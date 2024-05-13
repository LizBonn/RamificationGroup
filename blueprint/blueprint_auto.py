import argparse
import re
import os
import jinja2
import json

keywords = [
    "theorem",
    "def",
    "lemma",
    "/--",
    "class",
    "structure",
    #"instance",
    "inductive"
]


type_tex_dict = {
    "theorem": "theorem",
    "def": "definition",
    "lemma": "lemma",
    "class": "definition",
    "structure": "definition",
    #"instance": "lemma",
    "inductive": "definition",
    "/--": "documentation"
}

def find_lean_files(folder_path):
    '''
    Find all .lean files under the given path.
    '''
    lean_files = []

    for root, _, files in os.walk(folder_path):
        for file in files:
            if file.endswith('.lean'):
                relative_path = os.path.join(root, file)
                lean_files.append(relative_path)

    return lean_files

class LeanFile:
    def __init__(self, path) -> None:
        self.path = path
        self.namespaces = {}
        self.statements = []
        self.slices = []
        self.statement2slice = {}
        self.full_name = {}
        self.docs = {}
        with open(self.path, "r", encoding="utf8") as f:
            self.content = f.read()
        self.find_namespace()
        self.find_statements()
        self.get_slices()
        self.get_full_name()
        self.find_sorry()
        self.find_docs()

    def find_namespace(self):
        # 构建正则表达式，匹配 "namespace xxx" 和 "end xxx" 模式
        namespace_pattern = r"namespace\s+(\w+)"
        # 查找所有 "namespace xxx" 的模式的起始位置和对应的名称
        namespace_matches = [(m.start(), m.group(1)) for m in re.finditer(namespace_pattern, self.content)]

        # 对于每个找到的 "namespace xxx"，查找其对应的 "end xxx"
        for start_index, namespace_name in namespace_matches:
            namespace_end_pattern = r"end\s+{}".format(re.escape(namespace_name))
            end_match = re.search(namespace_end_pattern, self.content[start_index:])

            if end_match:
                end_index = start_index + end_match.start() + len(end_match.group())
            else:
                # 如果找不到对应的 "end xxx"，将其索引设为字符串的长度
                end_index = len(self.content)
            self.namespaces[namespace_name] = (start_index, end_index)

    def find_statements(self):
        count = 0
        for keyword in keywords:
            pattern = r"\n{}".format(re.escape(keyword))
            matches = re.finditer(pattern, self.content)
            for match in matches:
                if keyword != "/--":
                    temp = self.content[match.start():].split(" ")
                    name = temp[1]
                    if ":" in name:
                        name = name[:name.find(":")]
                else:
                    name = f"doc{count}"
                    count += 1
                self.statements.append([match.start(), keyword, name])
        # 根据关键词出现的位置进行排序
        self.statements.sort(key=lambda x: x[0])


    def get_slices(self):
        start = 0
        for i, statement in enumerate(self.statements):
            self.slices.append((start, statement[0]))
            self.statement2slice[statement[2]] = i + 1
            start = statement[0]
        self.slices.append((start, len(self.content)))

    def get_full_name(self):
        for statement in self.statements:
            namespace = []
            for name, idx in self.namespaces.items():
                if statement[1] == "/--":
                    break
                if statement[0] > idx[0] and statement[0] < idx[1]:
                    namespace.append(name)
            namespace = sorted(namespace, key=lambda name: self.namespaces[name][0])
            self.full_name[statement[2]] = '.'.join(namespace + [statement[2]])

    def find_sorry(self):
        for i, statement in enumerate(self.statements):
            if "sorry" in self.__getitem__(self.statement2slice[statement[2]]):
                self.statements[i].append(False)
            else:
                self.statements[i].append(True)

    def find_docs(self):
        try:
            for i, statement in enumerate(self.statements):
                if statement[1] == "/--" and i < len(self.statements) - 1:
                    docstring = self.__getitem__(self.statement2slice[statement[2]])
                    end_index = docstring.find("-/")
                    docstring = docstring[4:end_index].strip()
                    self.docs[self.full_name[self.statements[i+1][2]]] = docstring
        except:
            print(self.path)
            print(self.statements)
    def __len__(self):
        return len(self.slices)

    def __getitem__(self, idx):
        return self.content[self.slices[idx][0]: self.slices[idx][1]]

class LeanProject:
    def __init__(self, root) -> None:
        self.root = root
        self.files = find_lean_files(root)
        self.leanfiles = [LeanFile(file) for file in self.files]
        self.names = {}
        self.statements = {} # full_name : [slice_content, type, solved]
        self.dependencies = {}
        self.docs = {}
        for file in self.leanfiles:
            self.names.update(file.full_name)
            self.docs.update(file.docs)
            for statement in file.statements:
                if statement[1] != '/--':
                    self.statements[self.names[statement[2]]] = [
                        file[file.statement2slice[statement[2]]],
                        type_tex_dict[statement[1]],
                        statement[3]
                    ]
        self.find_dependency()

    def find_dependency(self):
        for name, features in self.statements.items():
            dependency = []
            for lemma in self.names.keys():
                if lemma in features[0] and self.names[lemma] != name:
                    dependency.append(self.names[lemma])
            self.dependencies[name] = dependency

        for statement in self.statements.keys():
            for lemma in self.dependencies[statement]:
                if not self.statements[lemma][2]:
                    self.statements[statement][2] = False
                    break


def generate_Tex(structure_dict : dict):
    env = jinja2.Environment(
        block_start_string="((*",
        block_end_string="*))",
        variable_start_string="(((",
        variable_end_string=")))",
        comment_start_string="((#",
        comment_end_string="#))",
        trim_blocks=True,
        autoescape=False,
        loader=jinja2.FileSystemLoader(os.path.abspath(".")),
    )

    template = env.get_template(os.path.join("blueprint", "template.tex"))
    output = template.render(structure_dict=structure_dict)
    with open(os.path.join("blueprint", "src", "demo.tex"), "w") as f:
        f.write(output)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("-p", "--project", type=str)
    arg = parser.parse_args()
    project = LeanProject(arg.project)
    structure_dict = {
        "statements" : project.statements,
        "dependencies": project.dependencies,
        "docs": project.docs,
    }
    generate_Tex(structure_dict)

