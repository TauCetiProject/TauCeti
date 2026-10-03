/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.ConjugateSubgroups
public import TauCeti.FieldTheory.GaloisCohomology.Restriction
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Conjugation

/-!
# Corestriction across a finite extension of fields

A finite extension `L/K` and an embedding `σ : L →ₐ[K] Kˢ` identify `G_L` with the open
subgroup `galoisSubgroup K L σ` of `G_K`, of index `[L : K]`. This file defines corestriction
`Hⁿ(G_L, 𝔽₂) ⟶ Hⁿ(G_K, 𝔽₂)` along `L/K`, with trivial `𝔽₂` coefficients and in every degree, as
the transport along `galoisF2Iso K L σ` followed by all-degree corestriction at
`galoisSubgroup K L σ`. It is the companion of `TauCeti.galoisRes`, and the two satisfy
`cor ∘ res = [L : K]`.

The composite the other way round, `res ∘ cor`, is the identity plus the endomorphism
`galoisConj`. For a quadratic extension the double-coset formula makes `galoisConj` conjugation by
the nontrivial coset of `G_L` in `G_K`; it is written through `res ∘ cor` rather than through an
element of that coset, so no such element is chosen.

Neither map depends on `σ`: another embedding changes the open subgroup and its identification
with `G_L` by conjugation by an element of `G_K`, and corestriction is invariant under conjugation
(`TauCeti.ContinuousCohomology.map_comp_corestriction_of_conj`). So `galoisCor` and `galoisConj`
are attached to `L/K` alone.

## Main definitions

* `TauCeti.galoisCor`: corestriction from `G_L` to `G_K` on `𝔽₂`-cohomology.
* `TauCeti.galoisConj`: the endomorphism `res ∘ cor - id` of the `𝔽₂`-cohomology of `G_L`.

## Main results

* `TauCeti.galoisRes_comp_galoisCor`, `TauCeti.galoisCor_galoisRes`: restriction followed by
  corestriction is multiplication by the degree `[L : K]`.
* `TauCeti.galoisCor_comp_galoisRes`, `TauCeti.galoisRes_galoisCor`: corestriction followed by
  restriction is `y ↦ y + galoisConj y`.
* `TauCeti.galoisConj_galoisRes`: on a restricted class, `galoisConj` is multiplication by
  `[L : K] - 1`.
* `TauCeti.galoisCor_embedding_independent`, `TauCeti.galoisConj_embedding_independent`:
  corestriction and `galoisConj` do not depend on the embedding of `L` into `Kˢ`.

## Reference

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  Chapter I, §5, and (1.5.7), for corestriction through the open subgroup associated to a finite
  extension.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory

universe u

variable (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]
  (σ : L →ₐ[K] SeparableClosure K) [FiniteDimensional K L]

/-- Corestriction on `𝔽₂`-cohomology for the finite extension `L/K`, relative to `σ`.
It is the canonical identification of `G_L` with `galoisSubgroup K L σ`, followed by
corestriction from that open subgroup to `G_K`. -/
def galoisCor (n : ℕ) :
    continuousCohomology n (trivialF2 (AbsoluteGaloisGroup L)) ⟶
      continuousCohomology n (trivialF2 (AbsoluteGaloisGroup K)) :=
  (galoisF2Iso K L σ n).inv ≫
    trivialF2CorMap (AbsoluteGaloisGroup K) (galoisSubgroup K L σ).toSubgroup
      (galoisSubgroup K L σ).isOpen n

/-- The definition of field-extension corestriction as transport to the open subgroup followed by
subgroup corestriction. -/
theorem galoisCor_def (n : ℕ) :
    galoisCor K L σ n =
      (galoisF2Iso K L σ n).inv ≫
        trivialF2CorMap (AbsoluteGaloisGroup K) (galoisSubgroup K L σ).toSubgroup
          (galoisSubgroup K L σ).isOpen n :=
  (rfl)

/-- Read on the open subgroup, field-extension corestriction is subgroup corestriction. -/
@[reassoc]
theorem galoisF2Iso_hom_comp_galoisCor (n : ℕ) :
    (galoisF2Iso K L σ n).hom ≫ galoisCor K L σ n =
      trivialF2CorMap (AbsoluteGaloisGroup K) (galoisSubgroup K L σ).toSubgroup
        (galoisSubgroup K L σ).isOpen n := by
  rw [galoisCor_def, Iso.hom_inv_id_assoc]

/-- **`cor ∘ res = [L : K]`** on `𝔽₂`-cohomology, in every degree (NSW (1.5.7)). -/
theorem galoisRes_comp_galoisCor (n : ℕ) :
    galoisRes K L σ n ≫ galoisCor K L σ n =
      Module.finrank K L • 𝟙 (continuousCohomology n (trivialF2 (AbsoluteGaloisGroup K))) := by
  rw [galoisRes_def, Category.assoc, galoisF2Iso_hom_comp_galoisCor,
    trivialF2ResMap_comp_trivialF2CorMap, galoisSubgroup_index]

/-- **`cor (res x) = [L : K] • x`** for every class `x ∈ Hⁿ(G_K, 𝔽₂)`. -/
@[simp]
theorem galoisCor_galoisRes (n : ℕ)
    (x : continuousCohomology n (trivialF2 (AbsoluteGaloisGroup K))) :
    galoisCor K L σ n (galoisRes K L σ n x) = Module.finrank K L • x := by
  have h := ConcreteCategory.congr_hom (galoisRes_comp_galoisCor K L σ n) x
  simp only [ConcreteCategory.comp_apply] at h
  exact h

/-- The endomorphism `res ∘ cor - id` of `Hⁿ(G_L, 𝔽₂)` for the finite extension `L/K`, relative
to `σ`. For a quadratic extension the double-coset formula identifies `res ∘ cor` with the sum of a
class and its conjugate under the nontrivial coset of `G_L` in `G_K`, so this is the conjugate
class; it is written through restriction and corestriction so that no element of that coset is
chosen. -/
def galoisConj (n : ℕ) :
    continuousCohomology n (trivialF2 (AbsoluteGaloisGroup L)) ⟶
      continuousCohomology n (trivialF2 (AbsoluteGaloisGroup L)) :=
  galoisCor K L σ n ≫ galoisRes K L σ n - 𝟙 _

/-- The definition of `galoisConj` as corestriction followed by restriction, minus the
identity. -/
theorem galoisConj_def (n : ℕ) :
    galoisConj K L σ n = galoisCor K L σ n ≫ galoisRes K L σ n - 𝟙 _ :=
  (rfl)

/-- **`res ∘ cor = id + galoisConj`** on `Hⁿ(G_L, 𝔽₂)`, the definition of `galoisConj` solved for
`res ∘ cor`. -/
theorem galoisCor_comp_galoisRes (n : ℕ) :
    galoisCor K L σ n ≫ galoisRes K L σ n = 𝟙 _ + galoisConj K L σ n := by
  rw [galoisConj_def, add_sub_cancel]

/-- **`res (cor y) = y + galoisConj y`** for every class `y ∈ Hⁿ(G_L, 𝔽₂)`. -/
theorem galoisRes_galoisCor (n : ℕ)
    (y : continuousCohomology n (trivialF2 (AbsoluteGaloisGroup L))) :
    galoisRes K L σ n (galoisCor K L σ n y) = y + galoisConj K L σ n y := by
  have h := ConcreteCategory.congr_hom (galoisCor_comp_galoisRes K L σ n) y
  simp only [ConcreteCategory.comp_apply] at h
  exact h

/-- On a restricted class, `galoisConj` is multiplication by `[L : K] - 1`. For a quadratic
extension a restricted class is its own conjugate. -/
theorem galoisConj_galoisRes (n : ℕ)
    (x : continuousCohomology n (trivialF2 (AbsoluteGaloisGroup K))) :
    galoisConj K L σ n (galoisRes K L σ n x) =
      (Module.finrank K L - 1) • galoisRes K L σ n x := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt (Module.finrank_pos (R := K) (M := L))
  have h := galoisRes_galoisCor K L σ n (galoisRes K L σ n x)
  rw [galoisCor_galoisRes, map_nsmul, hd, zero_add, succ_nsmul'] at h
  rw [hd, zero_add, Nat.add_sub_cancel]
  exact (add_left_cancel h).symm

/-! ### Independence of the embedding -/

/-- **Field-extension corestriction does not depend on the embedding**: two `K`-embeddings
`σ τ : L →ₐ[K] Kˢ` induce the same corestriction `Hⁿ(G_L, 𝔽₂) ⟶ Hⁿ(G_K, 𝔽₂)`, in every degree.
The automorphism `γ` of `Kˢ` carrying the identification of separable closures attached to `σ` to
the one attached to `τ` conjugates `galoisSubgroup K L σ` onto `galoisSubgroup K L τ`, compatibly
with the two identifications with `G_L`, and corestriction is invariant under conjugation. -/
theorem galoisCor_embedding_independent (τ : L →ₐ[K] SeparableClosure K) (n : ℕ) :
    galoisCor K L σ n = galoisCor K L τ n := by
  obtain ⟨γ, hγ⟩ := exists_galoisSubgroupEquiv_eq_conj K L σ τ
  -- The identification of `galoisSubgroup K L τ` with `galoisSubgroup K L σ` through `G_L`, which
  -- is conjugation by `γ⁻¹`.
  let κ : (galoisSubgroup K L τ).toSubgroup →ₜ* (galoisSubgroup K L σ).toSubgroup :=
    (ContinuousMonoidHom.toContinuousMonoidHom (galoisSubgroupEquiv K L σ)).comp
      (ContinuousMonoidHom.toContinuousMonoidHom (galoisSubgroupEquiv K L τ).symm)
  have hκ (v : (galoisSubgroup K L τ).toSubgroup) :
      (κ v : AbsoluteGaloisGroup K) = γ⁻¹ * v * γ := by
    have h := hγ ((galoisSubgroupEquiv K L τ).symm v)
    rw [ContinuousMulEquiv.apply_symm_apply] at h
    simp [κ, h, mul_assoc]
  have hVU : (galoisSubgroup K L τ).toSubgroup =
      (galoisSubgroup K L σ).toSubgroup.map (MulAut.conj γ).toMonoidHom := by
    ext x
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    refine ⟨fun hx => hκ ⟨x, hx⟩ ▸ (κ ⟨x, hx⟩).2, fun hx => ?_⟩
    -- `κ` is onto: `γ⁻¹ x γ` is the image of `v`, so `x = v` lies in `galoisSubgroup K L τ`.
    let v := galoisSubgroupEquiv K L τ ((galoisSubgroupEquiv K L σ).symm ⟨_, hx⟩)
    have hv : (κ v : AbsoluteGaloisGroup K) = γ⁻¹ * x * γ := by simp [κ, v]
    rw [hκ, mul_left_inj, mul_right_inj] at hv
    exact hv ▸ v.2
  rw [galoisCor_def, galoisCor_def, galoisF2Iso_inv, galoisF2Iso_inv,
    ← trivialF2Map_comp_trivialF2CorMap_of_conj (galoisSubgroup K L σ).isOpen
      (galoisSubgroup K L τ).isOpen γ hVU κ hκ n, ← Category.assoc, ← trivialF2Map_comp]
  congr 2
  ext v : 1
  simp [κ]

/-- **The endomorphism `galoisConj = res ∘ cor - id` does not depend on the embedding**: two
`K`-embeddings `σ τ : L →ₐ[K] Kˢ` induce the same endomorphism `galoisConj` of `Hⁿ(G_L, 𝔽₂)`.
For a quadratic extension it is conjugation by the nontrivial coset of `G_L` in `G_K`. -/
theorem galoisConj_embedding_independent (τ : L →ₐ[K] SeparableClosure K) (n : ℕ) :
    galoisConj K L σ n = galoisConj K L τ n := by
  rw [galoisConj_def, galoisConj_def, galoisCor_embedding_independent K L σ τ,
    galoisRes_embedding_independent K L σ τ]

end TauCeti
