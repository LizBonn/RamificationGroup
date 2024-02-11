# Valued or Valuation?

The choice here is made based on quality of life.

The main difference between `Valued` and `Valuation` is that there are several valuations on a given ring, but only one `Valued` instance. More precisely, only one `Valued R G` instance if `G` is given.

A motivating example similar to `Valuation` and `Valued` in my mind is `RingHom` and `Algebra`. One should develop general theory based on `RingHom`, but `Algebra` makes life so much easier, especially when you are trying to write `L →ₐ[K] L' `, i.e. `AlgHom`. It relieves the burden of mentioning the explicit algebra map. Something like `f →ₐ g` is just too rebellion from everyday mathematical notations.

The same logic applies here when you are trying to write `ValRingHom` (or even `ValAlgHom`). A notation like `K →+*ᵥ L` (or `L →ᵥₐ[K] L'`) would be nice. And topology instance only defines for `Valued` for a similar reason (of course it needs canonicalness).

That's why I prefer to build the whole theory of ramification on `Valued` instance, more concretely, on `DiscreteValued` or `CompleteDiscreteValued`. Pros: This will enable the scoped notation of `G(L/K)_[v]` and `G(L/K)^[v]`

One thing I am not certain about is whether I should state a theorem in `→+*ᵥ` or in `→+*` (in the case of finite extention local fields, `→+*` would be automatically `→+*ᵥ`). Currently I plan to write in `→+*ᵥ`, and write a `instance Coe RingHom ValRingHom` in the case of local fields.

Another issue is the ideal given be elements whose valuation is smaller than a certain value. I plan to define them for `Valuation`.

More things I am not certain about (luckily we don't need them for present):

1. Whether an instance `Valued` for DVR should exist? It is quite cannoinical, but only up to equivalence. The answer to this question may involve a total rewrite of whole valuation theory that makes everything defines/holds up to equivalence.
2. 

### Todo

1. Check Valued.v
