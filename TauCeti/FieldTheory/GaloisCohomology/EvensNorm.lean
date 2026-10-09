/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.Restriction
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.IndexTwoNorm

/-!
# The Evens norm of a quadratic field extension

A quadratic extension `L/K` and an embedding `σ : L →ₐ[K] Kˢ` identify `G_L` with the open
subgroup `galoisSubgroup K L σ` of `G_K`, which has index two. This file defines the index-two
Evens norm `H¹(G_L, 𝔽₂) → H²(G_K, 𝔽₂)` along `L/K`, with trivial `𝔽₂` coefficients, as the
transport along `galoisF2Iso K L σ` followed by the norm
`TauCeti.ContCohomology.evensNormIndexTwo` of that index-two subgroup. It is the companion of
`TauCeti.galoisRes` and `TauCeti.galoisCor`, and like them it is a reading of the subgroup
operation, not a second construction of it.

The norm multiplies the degree by the index, so the signature is the index-two case only: for a
cubic extension the target would be `H³`. Like the subgroup norm, `galoisEvens` is a function and
not an additive map.

## Main definitions

* `TauCeti.galoisEvens`: the Evens norm from `G_L` to `G_K` on `𝔽₂`-cohomology, for a quadratic
  extension.

## Main results

* `TauCeti.galoisEvens_galoisF2Iso_hom`: read on the open subgroup, `galoisEvens` is the
  index-two norm `evensNormIndexTwo` of `galoisSubgroup K L σ`.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer.
  Math. Soc. **108** (1963), 54–65.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  Chapter I, §5, for the open subgroup associated to a finite extension.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory ContCohomology

universe u

variable (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]
  (σ : L →ₐ[K] SeparableClosure K) [FiniteDimensional K L]

/-- The Evens norm `H¹(G_L, 𝔽₂) → H²(G_K, 𝔽₂)` of the quadratic extension `L/K`, relative to `σ`.
It is the canonical identification of `G_L` with the index-two open subgroup
`galoisSubgroup K L σ`, followed by the index-two Evens norm of that subgroup. -/
def galoisEvens (hL : Module.finrank K L = 2)
    (x : continuousCohomology 1 (trivialF2 (AbsoluteGaloisGroup L))) :
    continuousCohomology 2 (trivialF2 (AbsoluteGaloisGroup K)) :=
  evensNormIndexTwo (galoisSubgroup K L σ) ((galoisSubgroup_index K L σ).trans hL)
    ((galoisF2Iso K L σ 1).inv x)

/-- The definition of the field-extension Evens norm as transport to the open subgroup followed by
the index-two Evens norm of that subgroup. -/
theorem galoisEvens_def (hL : Module.finrank K L = 2)
    (x : continuousCohomology 1 (trivialF2 (AbsoluteGaloisGroup L))) :
    galoisEvens K L σ hL x =
      evensNormIndexTwo (galoisSubgroup K L σ) ((galoisSubgroup_index K L σ).trans hL)
        ((galoisF2Iso K L σ 1).inv x) :=
  (rfl)

/-- Read on the open subgroup, the field-extension Evens norm is the index-two Evens norm of
`galoisSubgroup K L σ`: the norm of the transport of a class `y ∈ H¹(galoisSubgroup K L σ, 𝔽₂)` to
`G_L` is `evensNormIndexTwo y`. -/
theorem galoisEvens_galoisF2Iso_hom (hL : Module.finrank K L = 2)
    (y : continuousCohomology 1 (trivialF2 ↥(galoisSubgroup K L σ).toSubgroup)) :
    galoisEvens K L σ hL ((galoisF2Iso K L σ 1).hom y) =
      evensNormIndexTwo (galoisSubgroup K L σ) ((galoisSubgroup_index K L σ).trans hL) y := by
  rw [galoisEvens_def, Iso.hom_inv_id_apply]

end TauCeti
