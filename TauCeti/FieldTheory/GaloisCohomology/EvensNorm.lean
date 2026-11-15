/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.Character
public import TauCeti.FieldTheory.GaloisCohomology.Corestriction.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Identities
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Naturality

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

The index-two Evens identities are then read on the `L/K` side, with restriction `galoisRes`,
corestriction `galoisCor`, the conjugate class `galoisConj` and the quadratic character
`χ_{L/K} = galoisCharacter`:

```text
res N^{Ev}(x)       = x ⌣ galoisConj x,
N^{Ev}(x + y)       = N^{Ev}(x) + N^{Ev}(y) + cor (x ⌣ galoisConj y),
N^{Ev}(res y)       = y ⌣ y + χ_{L/K} ⌣ y.
```

Each is the transport through `galoisF2Iso` of the corresponding identity for
`evensNormIndexTwo`, using that `galoisConj` is the transport of `OpenSubgroup.evensConj`
(`TauCeti.galoisConj_evensConj`). Finally, `galoisEvens` does not depend on the embedding `σ`:
two embeddings identify `G_L` with the fixing subgroup by maps differing by an inner automorphism
of `G_K`, under which the index-two norm is invariant.

## Main definitions

* `TauCeti.galoisEvens`: the Evens norm from `G_L` to `G_K` on `𝔽₂`-cohomology, for a quadratic
  extension.

## Main results

* `TauCeti.galoisEvens_galoisF2Iso_hom`: read on the open subgroup, `galoisEvens` is the
  index-two norm `evensNormIndexTwo` of `galoisSubgroup K L σ`.
* `TauCeti.galoisRes_galoisEvens`: `res N^{Ev}(x) = x ⌣ galoisConj x`.
* `TauCeti.galoisEvens_add`: `N^{Ev}(x + y) = N^{Ev}(x) + N^{Ev}(y) + cor (x ⌣ galoisConj y)`.
* `TauCeti.galoisEvens_galoisRes`: `N^{Ev}(res y) = y ⌣ y + χ_{L/K} ⌣ y`.
* `TauCeti.galoisEvens_embedding_independent`: `galoisEvens` does not depend on the embedding.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer.
  Math. Soc. **108** (1963), 54–65.
* A. Kozlowski, *The Evens–Kahn formula for the total Stiefel–Whitney class*, Proc. Amer. Math.
  Soc. **91** (1984), 309–313, Lemma 2.4, for the index-two identities.
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

/-! ### The index-two identities -/

/-- **Restriction of the Evens norm of a quadratic extension**:
`res N^{Ev}(x) = x ⌣ galoisConj x` in `H²(G_L, 𝔽₂)`, for `x ∈ H¹(G_L, 𝔽₂)`. -/
theorem galoisRes_galoisEvens (hL : Module.finrank K L = 2)
    (x : continuousCohomology 1 (trivialF2 (AbsoluteGaloisGroup L))) :
    galoisRes K L σ 2 (galoisEvens K L σ hL x) =
      (trivialF2TopPairing (AbsoluteGaloisGroup L)).cup 1 1 x (galoisConj K L σ 1 x) := by
  rw [galoisRes_def, galoisEvens_def, ConcreteCategory.comp_apply,
    trivialF2ResMap_evensNormIndexTwo, galoisConj_evensConj K L σ hL,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  exact (galoisF2Iso_hom_cup K L σ 1 1 _ _).trans (by rw [Iso.inv_hom_id_apply])

/-- **Polarization of the Evens norm of a quadratic extension**:
`N^{Ev}(x + y) = N^{Ev}(x) + N^{Ev}(y) + cor (x ⌣ galoisConj y)` in `H²(G_K, 𝔽₂)`, for
`x, y ∈ H¹(G_L, 𝔽₂)`. The cross term involves the **conjugate** of `y`. -/
theorem galoisEvens_add (hL : Module.finrank K L = 2)
    (x y : continuousCohomology 1 (trivialF2 (AbsoluteGaloisGroup L))) :
    galoisEvens K L σ hL (x + y) =
      galoisEvens K L σ hL x + galoisEvens K L σ hL y +
        galoisCor K L σ 2
          ((trivialF2TopPairing (AbsoluteGaloisGroup L)).cup 1 1 x (galoisConj K L σ 1 y)) := by
  have h := evensNormIndexTwo_polarization (galoisSubgroup K L σ)
    ((galoisSubgroup_index K L σ).trans hL) ((galoisF2Iso K L σ 1).inv x)
    ((galoisF2Iso K L σ 1).inv y)
  rw [sub_sub, sub_eq_iff_eq_add'] at h
  rw [galoisEvens_def, galoisEvens_def, galoisEvens_def, map_add, h, galoisCor_def,
    ConcreteCategory.comp_apply, galoisConj_evensConj K L σ hL,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  congr 2
  exact ((galoisF2Iso_inv_cup K L σ 1 1 _ _).trans (by rw [Iso.hom_inv_id_apply])).symm

/-- **The Evens norm of a restricted class**: for a quadratic extension `L/K` and
`y ∈ H¹(G_K, 𝔽₂)`, `N^{Ev}(res y) = y ⌣ y + χ_{L/K} ⌣ y` in `H²(G_K, 𝔽₂)`, where `χ_{L/K}` is the
quadratic character `galoisCharacter`. -/
theorem galoisEvens_galoisRes (hL : Module.finrank K L = 2)
    (y : continuousCohomology 1 (trivialF2 (AbsoluteGaloisGroup K))) :
    galoisEvens K L σ hL (galoisRes K L σ 1 y) =
      (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 y y +
        (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (galoisCharacter K L σ hL) y := by
  rw [galoisRes_def, ConcreteCategory.comp_apply, galoisEvens_galoisF2Iso_hom,
    evensNormIndexTwo_trivialF2ResMap, galoisCharacter_def]

/-! ### Independence of the embedding -/

/-- **The Evens norm of a quadratic extension does not depend on the embedding**: two
`K`-embeddings `σ τ : L →ₐ[K] Kˢ` induce the same norm `H¹(G_L, 𝔽₂) → H²(G_K, 𝔽₂)`. The two
identifications of `G_L` with its fixing subgroup differ by an inner automorphism of `G_K`, and
the index-two norm is invariant under conjugation. -/
theorem galoisEvens_embedding_independent (τ : L →ₐ[K] SeparableClosure K)
    (hL : Module.finrank K L = 2) :
    galoisEvens K L σ hL = galoisEvens K L τ hL := by
  obtain ⟨γ, hγ⟩ := exists_galoisSubgroupComparison_eq_conj K L σ τ
  let κ : (galoisSubgroup K L τ).toSubgroup →ₜ* (galoisSubgroup K L σ).toSubgroup :=
    galoisSubgroupComparison K L σ τ
  have hinv : (galoisF2Iso K L τ 1).inv = (galoisF2Iso K L σ 1).inv ≫ trivialF2Map κ 1 := by
    rw [galoisF2Iso_inv, galoisF2Iso_inv, ← trivialF2Map_comp]
    congr 1
    ext v
    simp [κ]
  ext x
  rw [galoisEvens_def, galoisEvens_def, hinv, ConcreteCategory.comp_apply,
    evensNormIndexTwo_comp_of_conj _ _ _ _ γ κ hγ]

end TauCeti
