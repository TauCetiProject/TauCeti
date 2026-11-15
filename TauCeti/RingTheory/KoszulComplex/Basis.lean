/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import TauCeti.RingTheory.KoszulComplex.Basic
import TauCeti.RingTheory.Ideal.Operations

/-!
# The Koszul differential in a basis

Let `M` be a free module with basis `(bᵢ)` and let `φ : M → R` be a linear functional. In the
exterior-power basis, the contraction by the coordinate `bᵢ*` deletes the index `i`, so the Koszul
differential of `φ` is `d(z) = ∑ᵢ φ(bᵢ) ιᵢ(z)` with `ιᵢ` the contraction by `bᵢ*`. The family of
all contractions `z ↦ (ιᵢ(z))ᵢ` is the linearized Koszul differential `⋀ⁿ⁺¹ M → ⋀ⁿ M ⊗ M`, and it
is split injective coordinatewise: the coordinate of `z` at an index set `s ∋ i` is, up to sign,
the coordinate of `ιᵢ(z)` at `s \ {i}`. Hence for every ideal `I`, an element `z` of positive
degree lies in `I • ⋀ M` exactly when all its contractions `ιᵢ(z)` do.

## Main results

* `Module.Basis.koszulDifferential_eq_sum`: the Koszul differential of `φ` is `∑ᵢ φ(bᵢ) ιᵢ`.
* `Module.Basis.koszulDifferential_coord_exteriorPower_basis_of_mem` and
  `Module.Basis.koszulDifferential_coord_exteriorPower_basis_of_notMem`: contraction by a
  coordinate on the exterior-power basis.
* `Module.Basis.exteriorPower_basis_repr_koszulDifferential_coord`: the coordinates of a
  contraction.
* `Module.Basis.mem_smul_top_iff_forall_koszulDifferential_coord_mem`: an element of positive
  degree lies in `I • ⋀ M` exactly when all its coordinate contractions do.

## References

* [The Stacks Project, Lemma 10.110.3](https://stacks.math.columbia.edu/tag/00OA)
-/

public section

noncomputable section

universe u v

open CliffordAlgebra TauCeti

namespace Module.Basis

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {ι : Type*}

/-- The Koszul differential of `φ` is the combination of the contractions by the coordinates of a
finite basis, with coefficients `φ(bᵢ)`: `d(z) = ∑ᵢ φ(bᵢ) ιᵢ(z)`. -/
theorem koszulDifferential_eq_sum [Fintype ι] (b : Module.Basis ι R M) (φ : Module.Dual R M)
    (n : ℕ) (z : ⋀[R]^(n + 1) M) :
    koszulDifferential φ n z = ∑ i, φ (b i) • koszulDifferential (b.coord i) n z := by
  apply Subtype.ext
  rw [coe_koszulDifferential_apply, Submodule.coe_sum]
  conv_lhs => rw [← b.sum_dual_apply_smul_coord φ]
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, LinearMap.smul_apply, Submodule.coe_smul, coe_koszulDifferential_apply]

section Basis

variable [LinearOrder ι] (b : Module.Basis ι R M) {n : ℕ}

/-- Contraction by the coordinate `bᵢ*` erases `i` from an exterior-basis vector whose index set
contains it, with the shuffle sign that moves `i` to the front. -/
theorem koszulDifferential_coord_exteriorPower_basis_of_mem {i : ι}
    {s : Set.powersetCard ι (n + 1)} (h : i ∈ s.val) :
    koszulDifferential (b.coord i) n (b.exteriorPower (n + 1) s) =
      ExteriorAlgebra.basisEraseSign i s.val •
        b.exteriorPower n (Set.powersetCard.ofCard (s := s.val.erase i)
          (by simp [Finset.card_erase_of_mem h, Set.powersetCard.card_eq])) := by
  apply Subtype.ext
  rw [coe_koszulDifferential_apply, ← _root_.ExteriorAlgebra.basis_eq_coe_basis,
    ExteriorAlgebra.contractLeft_coord_basis]
  simp only [h, ↓reduceIte, Submodule.coe_smul_of_tower]
  rw [← _root_.ExteriorAlgebra.basis_eq_coe_basis, Set.powersetCard.val_ofCard]

/-- Contraction by the coordinate `bᵢ*` kills an exterior-basis vector whose index set does not
contain `i`. -/
theorem koszulDifferential_coord_exteriorPower_basis_of_notMem {i : ι}
    {s : Set.powersetCard ι (n + 1)} (h : i ∉ s.val) :
    koszulDifferential (b.coord i) n (b.exteriorPower (n + 1) s) = 0 := by
  apply Subtype.ext
  rw [coe_koszulDifferential_apply, ← _root_.ExteriorAlgebra.basis_eq_coe_basis,
    ExteriorAlgebra.contractLeft_coord_basis]
  simp [h]

/-- The coordinates of a contraction: for `i ∈ s`, the coordinate of `ιᵢ(z)` at `s \ {i}` is the
coordinate of `z` at `s`, up to the shuffle sign moving `i` to the front of `s`. -/
theorem exteriorPower_basis_repr_koszulDifferential_coord (z : ⋀[R]^(n + 1) M)
    {i : ι} {s : Set.powersetCard ι (n + 1)} (h : i ∈ s.val) :
    (b.exteriorPower n).repr (koszulDifferential (b.coord i) n z)
        (Set.powersetCard.ofCard (s := s.val.erase i)
          (by simp [Finset.card_erase_of_mem h, Set.powersetCard.card_eq])) =
      ExteriorAlgebra.basisEraseSign i s.val • (b.exteriorPower (n + 1)).repr z s := by
  -- Both sides are linear in `z`; compare them on the exterior basis.
  let t' : Set.powersetCard ι n := Set.powersetCard.ofCard (s := s.val.erase i)
    (by simp [Finset.card_erase_of_mem h, Set.powersetCard.card_eq])
  suffices hcoord : (b.exteriorPower n).coord t' ∘ₗ koszulDifferential (b.coord i) n =
      ExteriorAlgebra.basisEraseSign i s.val • (b.exteriorPower (n + 1)).coord s by
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply, Module.Basis.coord_apply] using
      LinearMap.congr_fun hcoord z
  refine (b.exteriorPower (n + 1)).ext fun t ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]
  by_cases hit : i ∈ t.val
  · rw [koszulDifferential_coord_exteriorPower_basis_of_mem b hit, map_zsmul_unit,
      Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
    -- Erasing `i` is injective on the index sets containing `i`.
    have heq : (Set.powersetCard.ofCard (s := t.val.erase i)
        (by simp [Finset.card_erase_of_mem hit, Set.powersetCard.card_eq]) = t') ↔ t = s := by
      simp only [Subtype.ext_iff, t', Set.powersetCard.val_ofCard]
      exact ⟨fun he ↦ Finset.erase_injOn' i hit h he, fun he ↦ by rw [he]⟩
    by_cases hts : t = s
    · subst hts
      simp [t']
    · simp [heq.not.mpr hts, hts]
  · have hts : t ≠ s := fun hts ↦ hit (hts ▸ h)
    rw [koszulDifferential_coord_exteriorPower_basis_of_notMem b hit]
    simp [hts]

end Basis

/-- **The linearized Koszul differential is injective modulo every ideal.** For a module with a
basis `(bᵢ)`, an element `z` of positive exterior degree lies in `I • ⋀ M` exactly when its
contractions by all coordinates `bᵢ*` do. -/
theorem mem_smul_top_iff_forall_koszulDifferential_coord_mem (b : Module.Basis ι R M)
    (I : Ideal R) {n : ℕ} (z : ⋀[R]^(n + 1) M) :
    z ∈ I • (⊤ : Submodule R (⋀[R]^(n + 1) M)) ↔
      ∀ i, koszulDifferential (b.coord i) n z ∈ I • (⊤ : Submodule R (⋀[R]^n M)) := by
  refine ⟨fun hz i ↦ Submodule.smul_top_le_comap_smul_top I _ hz, fun h ↦ ?_⟩
  -- The exterior-power basis needs an order on the indices; any one will do.
  let : LinearOrder ι := IsWellOrder.linearOrder WellOrderingRel
  rw [(b.exteriorPower (n + 1)).mem_smul_top_iff]
  intro s
  obtain ⟨i, hi⟩ : s.val.Nonempty := Finset.card_pos.mp (by simp [Set.powersetCard.card_eq])
  have hmem := (b.exteriorPower n).mem_smul_top_iff.mp (h i)
    (Set.powersetCard.ofCard (s := s.val.erase i) (by simp [Finset.card_erase_of_mem hi,
      Set.powersetCard.card_eq]))
  rw [b.exteriorPower_basis_repr_koszulDifferential_coord z hi] at hmem
  -- The sign is a unit of `ℤ`, so it can be cancelled.
  have hsign := I.toAddSubgroup.zsmul_mem hmem (ExteriorAlgebra.basisEraseSign i s.val : ℤ)
  rwa [← Units.smul_def, smul_smul, Int.units_mul_self, one_smul] at hsign

end Module.Basis
