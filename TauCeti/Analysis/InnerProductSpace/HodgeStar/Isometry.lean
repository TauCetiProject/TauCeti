/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Metric and functorial properties of the Hodge star

The Hodge star preserves the inner product and hence defines a linear isometric equivalence
between complementary exterior powers. Combined with the defining identity
`⟪⋆x, y⟫ = vol (x ∧ y)`, this gives the wedge characterization `α ∧ ⋆β = ⟪α, β⟫ vol`.
Reversing the orientation negates the Hodge star, and transporting the orientation along a
linear isometric equivalence commutes with it. These statements hold also in dimension zero, for
either orientation.

## References

* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer (1983), §6.1.
-/

public section

noncomputable section

open Module exteriorPower Set
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)]

namespace Orientation

variable (o : Orientation ℝ V (Fin n))

private theorem orthonormal_hodgeStar_basis (b : OrthonormalBasis (Fin n) ℝ V) {k l : ℕ}
    (hkl : k + l = finrank ℝ V) :
    Orthonormal ℝ (o.hodgeStar hkl ∘ b.toBasis.exteriorPower k) := by
  classical
  have hvol := o.abs_volumeForm_apply_of_orthonormal b
  have hb := (b.exteriorPower l).orthonormal
  refine ⟨?_, ?_⟩
  · intro s
    rw [Function.comp_apply, hodgeStar_orthonormalBasis]
    rcases Int.units_eq_one_or (powersetCard.sign s) with hs | hs <;>
      simp [hs, norm_smul, Real.norm_eq_abs, ← OrthonormalBasis.toBasis_exteriorPower, hvol]
  · intro s t hst
    rw [Function.comp_apply, Function.comp_apply, hodgeStar_orthonormalBasis,
      hodgeStar_orthonormalBasis]
    have hcard : l + k = Fintype.card (Fin n) := by
      rw [Fintype.card_fin, ← (Fact.out : finrank ℝ V = n)]
      omega
    have hc := (powersetCard.compl hcard).injective.ne hst
    simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left,
      real_inner_smul_right, ← OrthonormalBasis.toBasis_exteriorPower,
      OrthonormalBasis.coe_toBasis, hb.inner_eq_zero hc, mul_zero]

/-- The Hodge star as a linear isometric equivalence between complementary exterior powers. -/
def hodgeStarIsometry {k l : ℕ} (hkl : k + l = finrank ℝ V) :
    ⋀[ℝ]^k V ≃ₗᵢ[ℝ] ⋀[ℝ]^l V :=
  let b := (stdOrthonormalBasis ℝ V).reindex (finCongr (Fact.out : finrank ℝ V = n))
  (o.hodgeStar hkl).isometryOfOrthonormal
    (v := b.toBasis.exteriorPower k)
    (by
      rw [← OrthonormalBasis.toBasis_exteriorPower, OrthonormalBasis.coe_toBasis]
      exact (b.exteriorPower k).orthonormal)
    (o.orthonormal_hodgeStar_basis b hkl)

/-- The metric refinement of the Hodge star has the original underlying linear equivalence. -/
@[simp]
theorem hodgeStarIsometry_toLinearEquiv {k l : ℕ} (hkl : k + l = finrank ℝ V) :
    (o.hodgeStarIsometry hkl).toLinearEquiv = o.hodgeStar hkl := by
  rw [hodgeStarIsometry, LinearEquiv.isometryOfOrthonormal_toLinearEquiv]

/-- The metric refinement evaluates as the original Hodge star. This equation is kept as a
named rewrite so that the bundled inverse laws remain available to the simplifier. -/
theorem hodgeStarIsometry_apply {k l : ℕ} (hkl : k + l = finrank ℝ V)
    (x : ⋀[ℝ]^k V) : o.hodgeStarIsometry hkl x = o.hodgeStar hkl x :=
  (rfl)

/-- The Hodge star preserves inner products. -/
@[simp]
theorem inner_hodgeStar_hodgeStar {k l : ℕ} (hkl : k + l = finrank ℝ V)
    (x y : ⋀[ℝ]^k V) : ⟪o.hodgeStar hkl x, o.hodgeStar hkl y⟫ = ⟪x, y⟫ := by
  simpa only [← o.hodgeStarIsometry_toLinearEquiv hkl, LinearIsometryEquiv.coe_toLinearEquiv]
    using (o.hodgeStarIsometry hkl).inner_map_map x y

/-- **The wedge characterization of the Hodge star**: `α ∧ ⋆β = ⟪α, β⟫ vol`, that is, the
volume of `α ∧ ⋆β` is the inner product of `α` and `β`, for `α β ∈ ⋀ᵏ V`. -/
theorem wedgePairing_hodgeStar {k l : ℕ} (hkl : k + l = finrank ℝ V) (x y : ⋀[ℝ]^k V) :
    wedgePairing o.volumeEquiv hkl x (o.hodgeStar hkl y) = ⟪x, y⟫ := by
  rw [← inner_hodgeStar_apply, inner_hodgeStar_hodgeStar]

/-- The Hodge star preserves norms. -/
@[simp]
theorem norm_hodgeStar {k l : ℕ} (hkl : k + l = finrank ℝ V) (x : ⋀[ℝ]^k V) :
    ‖o.hodgeStar hkl x‖ = ‖x‖ := by
  simpa only [← o.hodgeStarIsometry_toLinearEquiv hkl, LinearIsometryEquiv.coe_toLinearEquiv]
    using (o.hodgeStarIsometry hkl).norm_map x

/-- Reversing the orientation negates the Hodge star. -/
@[simp]
theorem hodgeStar_neg_orientation {k l : ℕ} (hkl : k + l = finrank ℝ V)
    (x : ⋀[ℝ]^k V) : (-o).hodgeStar hkl x = -(o.hodgeStar hkl x) := by
  let b := (stdOrthonormalBasis ℝ V).reindex (finCongr (Fact.out : finrank ℝ V = n))
  refine LinearMap.congr_fun ((b.toBasis.exteriorPower k).ext
    (f₁ := ((-o).hodgeStar hkl).toLinearMap)
    (f₂ := -(o.hodgeStar hkl).toLinearMap) fun s ↦ ?_) x
  simp only [LinearEquiv.coe_coe, LinearMap.neg_apply]
  rw [hodgeStar_orthonormalBasis, hodgeStar_orthonormalBasis]
  simp [volumeForm_neg_orientation]

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [Fact (finrank ℝ W = n)]

/-- The Hodge star commutes with a linear isometric equivalence when the target has the
transported orientation. -/
theorem hodgeStar_map (φ : V ≃ₗᵢ[ℝ] W) {k l : ℕ}
    (hV : k + l = finrank ℝ V) (hW : k + l = finrank ℝ W) (x : ⋀[ℝ]^k V) :
    (Orientation.map (Fin n) φ.toLinearEquiv o).hodgeStar hW
        (exteriorPower.map k φ.toLinearMap x) =
      exteriorPower.map l φ.toLinearMap (o.hodgeStar hV x) := by
  let b := (stdOrthonormalBasis ℝ V).reindex (finCongr (Fact.out : finrank ℝ V = n))
  have hb (d : ℕ) (s : powersetCard (Fin n) d) :
      exteriorPower.map d φ.toLinearMap (b.toBasis.exteriorPower d s) =
        (b.map φ).toBasis.exteriorPower d s := by
    simp [exteriorPower.coe_basis, OrthonormalBasis.coe_toBasis,
      Module.Basis.coe_map, Function.comp_def]
  have hvol : (Orientation.map (Fin n) φ.toLinearEquiv o).volumeForm (b.map φ) =
      o.volumeForm b := by
    rw [o.volumeForm_map]
    congr 1
    ext i
    simp
  refine LinearMap.congr_fun ((b.toBasis.exteriorPower k).ext
    (f₁ := ((Orientation.map (Fin n) φ.toLinearEquiv o).hodgeStar hW).toLinearMap ∘ₗ
      exteriorPower.map k φ.toLinearMap)
    (f₂ := exteriorPower.map l φ.toLinearMap ∘ₗ (o.hodgeStar hV).toLinearMap) fun s ↦ ?_) x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [hb, hodgeStar_orthonormalBasis, hodgeStar_orthonormalBasis, hvol,
    map_smul, map_zsmul_unit, hb]

end Orientation
