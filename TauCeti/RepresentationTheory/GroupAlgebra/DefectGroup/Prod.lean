/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Center
public import TauCeti.Algebra.Group.Subgroup.Prod
public import TauCeti.Algebra.MonoidAlgebra.TensorProduct
public import TauCeti.GroupTheory.PGroup
public import TauCeti.RepresentationTheory.GroupAlgebra.DefectGroup.Basic

/-!
# Defect groups of direct products

For groups `G₁`, `G₂` and a commutative semiring `R`, Mathlib's
`MonoidAlgebra.tensorEquiv R : R[G₁] ⊗[R] R[G₂] ≃ₗ[R] R[G₁ × G₂]` sends `x ⊗ y` to the element
`x ⊗ y` of `R[G₁ × G₂]` with coefficient `x(g₁) y(g₂)` at `(g₁, g₂)`
(`MonoidAlgebra.coeff_tensorEquiv_tmul`).

A subgroup `Q ≤ G₁ × G₂` with projections `Q₁ ≤ G₁` and `Q₂ ≤ G₂` has centralizer
`C(Q) = C(Q₁) × C(Q₂)` (`Set.mem_centralizer_iff_fst_snd`). Hence, over a semiring without zero
divisors, `Br_Q(x ⊗ y) ≠ 0` exactly when `Br_{Q₁}(x) ≠ 0` and `Br_{Q₂}(y) ≠ 0`, and the defect
groups of `x ⊗ y` are exactly the products `D₁ × D₂` of a defect group `D₁` of `x` and a defect
group `D₂` of `y`. Applied to block idempotents, this computes the defect groups of the products
`e₁ ⊗ e₂` of block idempotents of `k[G₁]` and `k[G₂]` inside `k[G₁ × G₂]`.

## Main results

* `TauCeti.brauerProjection_tensorEquiv_tmul_ne_zero_iff`: `Br_Q(x ⊗ y) ≠ 0` exactly when
  `Br_{Q₁}(x) ≠ 0` and `Br_{Q₂}(y) ≠ 0`.
* `TauCeti.isDefectGroup_tensorEquiv_tmul_iff`: the defect groups of `x ⊗ y` are the
  `D₁ × D₂`.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, §12.5, p. 243.
-/

public section

open MonoidAlgebra TensorProduct

namespace TauCeti

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂] {R : Type*} [CommSemiring R] [NoZeroDivisors R]

/-- **The Brauer projection of `x ⊗ y`.** Over a semiring without zero divisors,
`Br_Q(x ⊗ y) ≠ 0` exactly when `Br_{Q₁}(x) ≠ 0` and `Br_{Q₂}(y) ≠ 0`, for the projections
`Q₁`, `Q₂` of `Q`. -/
theorem brauerProjection_tensorEquiv_tmul_ne_zero_iff {Q : Subgroup (G₁ × G₂)}
    {x : MonoidAlgebra R G₁} {y : MonoidAlgebra R G₂} :
    brauerProjection Q (tensorEquiv R (x ⊗ₜ y)) ≠ 0 ↔
      brauerProjection (Q.map (MonoidHom.fst G₁ G₂)) x ≠ 0 ∧
        brauerProjection (Q.map (MonoidHom.snd G₁ G₂)) y ≠ 0 := by
  simp only [ne_eq, brauerProjection_eq_zero_iff, not_forall, exists_prop,
    coeff_tensorEquiv_tmul, mul_eq_zero, not_or]
  have hC {c : G₁ × G₂} := Set.mem_centralizer_iff_fst_snd (S := (Q : Set (G₁ × G₂))) (c := c)
  exact ⟨fun ⟨c, hc, hx, hy⟩ ↦ ⟨⟨c.1, (hC.1 hc).1, hx⟩, ⟨c.2, (hC.1 hc).2, hy⟩⟩,
    fun ⟨⟨a, ha, hx⟩, ⟨b, hb, hy⟩⟩ ↦ ⟨(a, b), hC.2 ⟨ha, hb⟩, hx, hy⟩⟩

/-- `Br_{D₁ × D₂}(x ⊗ y) ≠ 0` exactly when `Br_{D₁}(x) ≠ 0` and `Br_{D₂}(y) ≠ 0`. -/
theorem brauerProjection_prod_tensorEquiv_tmul_ne_zero_iff {D₁ : Subgroup G₁}
    {D₂ : Subgroup G₂} {x : MonoidAlgebra R G₁} {y : MonoidAlgebra R G₂} :
    brauerProjection (D₁.prod D₂) (tensorEquiv R (x ⊗ₜ y)) ≠ 0 ↔
      brauerProjection D₁ x ≠ 0 ∧ brauerProjection D₂ y ≠ 0 := by
  rw [brauerProjection_tensorEquiv_tmul_ne_zero_iff, Subgroup.prod_map_fst, Subgroup.prod_map_snd]

/-- **Defect groups of a direct product.** Over a semiring without zero divisors, the defect
groups of `x ⊗ y ∈ R[G₁ × G₂]` are exactly the products `D₁ × D₂` of a defect group `D₁` of `x`
and a defect group `D₂` of `y`. -/
theorem isDefectGroup_tensorEquiv_tmul_iff {p : ℕ} {x : MonoidAlgebra R G₁}
    {y : MonoidAlgebra R G₂} {Q : Subgroup (G₁ × G₂)} :
    IsDefectGroup R p (tensorEquiv R (x ⊗ₜ y)) Q ↔
      ∃ D₁ D₂, IsDefectGroup R p x D₁ ∧ IsDefectGroup R p y D₂ ∧ Q = D₁.prod D₂ := by
  constructor
  · intro h
    obtain ⟨hQ, hBr, hmax⟩ := isDefectGroup_iff.1 h
    set Q₁ := Q.map (MonoidHom.fst G₁ G₂)
    set Q₂ := Q.map (MonoidHom.snd G₁ G₂)
    obtain ⟨hBr₁, hBr₂⟩ := brauerProjection_tensorEquiv_tmul_ne_zero_iff.1 hBr
    have key : ∀ (R₁ : Subgroup G₁) (R₂ : Subgroup G₂), IsPGroup p R₁ → IsPGroup p R₂ →
        brauerProjection R₁ x ≠ 0 → brauerProjection R₂ y ≠ 0 → Q ≤ R₁.prod R₂ →
          R₁.prod R₂ = Q := fun R₁ R₂ hp₁ hp₂ hb₁ hb₂ hle ↦
      hmax _ ((hp₁.prod hp₂).of_equiv (Subgroup.prodEquiv R₁ R₂).symm)
        (brauerProjection_prod_tensorEquiv_tmul_ne_zero_iff.2 ⟨hb₁, hb₂⟩) hle
    have hp₁ : IsPGroup p Q₁ := hQ.map _
    have hp₂ : IsPGroup p Q₂ := hQ.map _
    have hQeq : Q₁.prod Q₂ = Q :=
      key Q₁ Q₂ hp₁ hp₂ hBr₁ hBr₂ (Subgroup.le_prod_iff.2 ⟨le_rfl, le_rfl⟩)
    refine ⟨Q₁, Q₂, isDefectGroup_iff.2 ⟨hp₁, hBr₁, fun R₁ hR₁ hb₁ hle ↦ ?_⟩,
      isDefectGroup_iff.2 ⟨hp₂, hBr₂, fun R₂ hR₂ hb₂ hle ↦ ?_⟩, hQeq.symm⟩
    · have := key R₁ Q₂ hR₁ hp₂ hb₁ hBr₂ (hQeq ▸ Subgroup.prod_mono hle le_rfl)
      rw [← Subgroup.prod_map_fst R₁ Q₂, this]
    · have := key Q₁ R₂ hp₁ hR₂ hBr₁ hb₂ (hQeq ▸ Subgroup.prod_mono le_rfl hle)
      rw [← Subgroup.prod_map_snd Q₁ R₂, this]
  · rintro ⟨D₁, D₂, h₁, h₂, rfl⟩
    obtain ⟨hp₁, hBr₁, hmax₁⟩ := isDefectGroup_iff.1 h₁
    obtain ⟨hp₂, hBr₂, hmax₂⟩ := isDefectGroup_iff.1 h₂
    refine isDefectGroup_iff.2 ⟨(hp₁.prod hp₂).of_equiv (Subgroup.prodEquiv D₁ D₂).symm,
      brauerProjection_prod_tensorEquiv_tmul_ne_zero_iff.2 ⟨hBr₁, hBr₂⟩, fun Q hQ hBr hle ↦ ?_⟩
    obtain ⟨hb₁, hb₂⟩ := brauerProjection_tensorEquiv_tmul_ne_zero_iff.1 hBr
    have hle₁ : D₁ ≤ Q.map (MonoidHom.fst G₁ G₂) :=
      Subgroup.prod_map_fst D₁ D₂ ▸ Subgroup.map_mono hle
    have hle₂ : D₂ ≤ Q.map (MonoidHom.snd G₁ G₂) :=
      Subgroup.prod_map_snd D₁ D₂ ▸ Subgroup.map_mono hle
    have he₁ := hmax₁ _ (hQ.map _) hb₁ hle₁
    have he₂ := hmax₂ _ (hQ.map _) hb₂ hle₂
    exact le_antisymm (Subgroup.le_prod_iff.2 ⟨he₁.le, he₂.le⟩) hle

end TauCeti
