import Mathlib.Tactic
--文件最后的Judge函数是一个例子，展示了各个定义的使用方法，并写了一个简单的例子来展示定罪的流程的写法


-- 定义了有期徒刑的时间，分别代表无罪，三年以下（Less than three）,七年以下以及七年以上有期徒刑，使用的方法是使用点方法，例如Crime.Innocent。
inductive Crime
  | Innocent : Crime
  | LeThree : Crime
  | LeSeven : Crime
  | GeSeven : Crime
deriving Repr

--定义了过失，分为过于自信的过失与粗疏大意的过失两类。
inductive Fault
  | Confidence : Fault
  | Carelessness : Fault
deriving Repr, BEq, DecidableEq

--定义了一般主体，包括年龄，刑事责任能力以及自然人属性，并要求年龄大于十六周岁。
class GeneralSubject where
  Age : Nat
  CriminalCapacity : Prop
  NaturalPerson : Prop
  Adult : 16 ≤ Age

--定义了责任，分为全部责任，主要责任，同等责任，次要责任以及无责任。
inductive Responsibility
  | Full : Responsibility
  | Primiry : Responsibility
  | Equal : Responsibility
  | Secondary : Responsibility
  | None : Responsibility
deriving Repr, BEq, DecidableEq

--定义了各种危险驾驶行为，包括《交通案件解释》中的各种行为，以及逃逸。
inductive Drive
  | Drunk : Drive
  | NoLicense : Drive
  | NoSafetyFacilities : Drive
  | Overloading : Drive
  | RunAway : Drive
deriving Repr, BEq, DecidableEq

--定义了事故，包含重伤人数以及死亡人数。
class Accident where
  SeriousInjury : Nat
  Death : Nat

--定义了交通肇事罪，包含一般主体，过失，事故以及危险驾驶行为。
class TrafficCrime where
  generalsubject : GeneralSubject
  fault : Fault
  accident : Accident
  drive : Drive

--定义了判刑，包含有期徒刑以及责任判定。
class Sentence where
  crime : Crime
  responsibility : Responsibility
deriving Repr

--简单的定罪流程例子，说明若酒后或吸食毒品后驾驶车辆，且死亡人数大于五人且过于自信则判七年以上有期徒刑，否则无罪。
def Judge (t : TrafficCrime) : Sentence :=
  if t.drive = Drive.Drunk ∧ 5 < t.accident.Death ∧ t.fault = Fault.Confidence then ⟨Crime.GeSeven, Responsibility.Full⟩
  else ⟨Crime.Innocent, Responsibility.None⟩

--第一个例子，一般主体17周岁，具有刑事责任能力与自然人属性，属于过于自信的过失，造成重伤与死亡人数都为10人，并且酒后驾驶
def Example_one : TrafficCrime where
  generalsubject := {
    Age := 17
    CriminalCapacity := True
    NaturalPerson := True
    Adult := by linarith
  }
  fault := Fault.Confidence
  accident := ⟨10, 10⟩
  drive := Drive.Drunk

def Example_two : TrafficCrime where
  generalsubject := {
    Age := 17
    CriminalCapacity := True
    NaturalPerson := True
    Adult := by linarith
  }
  fault := Fault.Carelessness
  accident := ⟨1, 0⟩
  drive := Drive.Overloading

--计算第一个例子的判刑
#eval Judge Example_one

--计算第二个例子的判刑
#eval Judge Example_two
