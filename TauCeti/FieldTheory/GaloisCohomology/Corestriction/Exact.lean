/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.Corestriction.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.IndexTwo.Exact

/-!
# Restriction–corestriction exactness for quadratic extensions

For a quadratic extension `L/K`, an embedding of `L` into the separable closure of `K` determines
an open subgroup of index two in `G_K`, whose cohomology is identified with that of `G_L` by
`TauCeti.galoisF2Iso`. The subgroup index-two exact sequence therefore says, in every degree, that
a class over `L` has zero corestriction precisely when it is the restriction of a class over `K`:

```text
Hⁿ(G_K, 𝔽₂) --res--> Hⁿ(G_L, 𝔽₂) --cor--> Hⁿ(G_K, 𝔽₂).
```

This file transports the existing subgroup theorem through
`TauCeti.galoisF2Iso`, so the statement uses the field-extension operations `TauCeti.galoisRes`
and `TauCeti.galoisCor` rather than rebuilding either operation.

## Main result

* `TauCeti.exact_galoisRes_galoisCor_of_finrank_eq_two`: restriction followed by corestriction
  is exact for a quadratic extension, in every degree.

## References

* J. Kr. Arason, *Cohomologische Invarianten quadratischer Formen*, J. Algebra **36** (1975),
  448–491.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.3.2).
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory

universe u

variable (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]
  (σ : L →ₐ[K] SeparableClosure K) [FiniteDimensional K L]

/-- **Exactness of restriction followed by corestriction for a quadratic extension.** In every
degree, a class in `Hⁿ(G_L, 𝔽₂)` has zero corestriction if and only if it is the restriction of
a class in `Hⁿ(G_K, 𝔽₂)`. -/
theorem exact_galoisRes_galoisCor_of_finrank_eq_two (hL : Module.finrank K L = 2) (n : ℕ) :
    Function.Exact (galoisRes K L σ n) (galoisCor K L σ n) := by
  rw [galoisRes_def, galoisCor_def]
  let hU : (galoisSubgroup K L σ).toSubgroup.index = 2 :=
    (galoisSubgroup_index K L σ).trans hL
  let e := (galoisF2Iso K L σ n).toContinuousLinearEquiv.toLinearEquiv
  exact (LinearEquiv.conj_exact_iff_exact _ _ e).2
    (exact_trivialF2ResMap_trivialF2CorMap_of_index_two
      (AbsoluteGaloisGroup K) (galoisSubgroup K L σ).toSubgroup
      (galoisSubgroup K L σ).isOpen hU n)

end TauCeti
