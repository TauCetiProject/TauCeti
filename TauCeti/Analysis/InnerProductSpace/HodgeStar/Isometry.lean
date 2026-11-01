/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ExteriorPower
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Basic
import TauCeti.LinearAlgebra.ExteriorPower.WedgePairing
import TauCeti.LinearAlgebra.Matrix.Determinant.FinFour
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Metric and functorial properties of the Hodge star

The Hodge star preserves the inner product and hence defines a linear isometric equivalence
between complementary exterior powers. Combined with the defining identity
`⟪⋆x, y⟫ = vol (x ∧ y)`, this gives the wedge characterization `α ∧ ⋆β = ⟪α, β⟫ vol`.
On the top exterior power the inner product is the product of the volumes,
`⟪x, y⟫ = vol x * vol y`, since `⋆1` is a unit vector representing the volume. In an even
middle degree the Hodge star is an isometric involution, hence symmetric.
Reversing the orientation negates the Hodge star, and transporting the orientation along a
linear isometric equivalence commutes with it. These statements hold also in dimension zero, for
either orientation.

In dimension four, the Hodge star of a wedge of two vectors pairs with another such wedge to the
volume of the four vectors, `⟪⋆(a ∧ b), u ∧ w⟫ = vol(a, b, u, w)`
(`Orientation.inner_hodgeStar_ιMulti_two`), and the derivation action
`D_A (u ∧ w) = A u ∧ w + u ∧ A w` of a skew-adjoint endomorphism `A` commutes with the Hodge star
on two-forms (`Orientation.hodgeStar_lieMap_two`).

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

/-- In an even middle degree, `k + k = finrank ℝ V` with `k` even, the Hodge star is symmetric,
`⟪⋆x, y⟫ = ⟪x, ⋆y⟫`, being an isometric involution. This covers two-forms in dimension four. -/
theorem isSymmetric_hodgeStar_of_even {k : ℕ} (hk : Even k) (hkk : k + k = finrank ℝ V) :
    (o.hodgeStar hkk : ⋀[ℝ]^k V →ₗ[ℝ] ⋀[ℝ]^k V).IsSymmetric := fun x y ↦ by
  conv_lhs => rw [← o.hodgeStar_hodgeStar_of_even hk hkk y]
  exact o.inner_hodgeStar_hodgeStar hkk x (o.hodgeStar hkk y)

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

/-- On the top exterior power, a line, the inner product is the product of the volumes:
`⟪x, y⟫ = vol x * vol y`. Equivalently, the unit volume element `vol⁻¹ 1` has norm one. -/
theorem inner_eq_volumeEquiv_mul_volumeEquiv (x y : ⋀[ℝ]^(finrank ℝ V) V) :
    ⟪x, y⟫ = o.volumeEquiv x * o.volumeEquiv y := by
  -- The star `ω = ⋆1` of the unit `1 ∈ ⋀⁰ V` is a unit vector representing the volume.
  have h₀ : 0 + finrank ℝ V = finrank ℝ V := zero_add _
  set ω := o.hodgeStar h₀ (ιMulti ℝ 0 ![])
  have hvol (z : ⋀[ℝ]^(finrank ℝ V) V) : o.volumeEquiv z = ⟪ω, z⟫ := by
    rw [inner_hodgeStar_apply, wedgePairing_apply_eq_of_coe_mul_eq _ h₀ _ _ z
      (by simp [ExteriorAlgebra.ιMulti_zero_apply])]
  have hω : ⟪ω, ω⟫ = 1 := by
    rw [inner_hodgeStar_hodgeStar, inner_ιMulti_self]
    simp
  have hz (z : ⋀[ℝ]^(finrank ℝ V) V) : z = o.volumeEquiv z • ω := by
    apply o.volumeEquiv.injective
    rw [map_smul, hvol ω, hω, smul_eq_mul, mul_one]
  conv_lhs => rw [hz x, hz y]
  rw [real_inner_smul_left, real_inner_smul_right, hω, mul_one]

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

/-! ### Two-forms in dimension four -/

namespace Orientation

variable [Fact (finrank ℝ V = 4)] (o : Orientation ℝ V (Fin 4))

/-- In dimension four, the Hodge star of a wedge of two vectors pairs with another such wedge to
the volume of the four vectors: `⟪⋆(a ∧ b), u ∧ w⟫ = vol(a, b, u, w)`. -/
theorem inner_hodgeStar_ιMulti_two (hkl : 2 + 2 = finrank ℝ V) (a b u w : V) :
    ⟪o.hodgeStar hkl (ιMulti ℝ 2 ![a, b]), ιMulti ℝ 2 ![u, w]⟫ = o.volumeForm ![a, b, u, w] := by
  -- Read the wedge of the four vectors in the degree `finrank ℝ V`.
  have key : ∀ {d : ℕ} (hd : d = 4) (f : Fin 4 → V),
      ExteriorAlgebra.ιMulti ℝ d (f ∘ finCongr hd) = ExteriorAlgebra.ιMulti ℝ 4 f := by
    rintro d rfl f
    rfl
  rw [inner_hodgeStar_apply, wedgePairing_apply_eq_of_coe_mul_eq _ hkl _ _
    (ιMulti ℝ _ (![a, b, u, w] ∘ finCongr (Fact.out : finrank ℝ V = 4))), volumeEquiv_ιMulti]
  · congr 1
  · simp only [ιMulti_apply_coe, key, ExteriorAlgebra.ιMulti_mul_ιMulti]
    congr 1
    ext i
    fin_cases i <;> rfl

/-- **Skew-adjoint endomorphisms commute with the Hodge star on two-forms** in dimension four:
`⋆ (D_A x) = D_A (⋆ x)` for the derivation action `D_A` of a skew-adjoint `A`. This is the
infinitesimal form of the invariance of `⋆` under rotations; it holds because `D_A` acts on
`⋀⁴ V` by `tr A = 0`. -/
theorem hodgeStar_lieMap_two (hkl : 2 + 2 = finrank ℝ V) {A : V →ₗ[ℝ] V}
    (hA : ∀ u w, ⟪A u, w⟫ = -⟪u, A w⟫) (x : ⋀[ℝ]^2 V) :
    o.hodgeStar hkl (exteriorPower.lieMap 2 A x) =
      exteriorPower.lieMap 2 A (o.hodgeStar hkl x) := by
  set e := (stdOrthonormalBasis ℝ V).reindex (finCongr (Fact.out : finrank ℝ V = 4))
    |>.adjustToOrientation o
  have he : e.toBasis.orientation = o := OrthonormalBasis.orientation_adjustToOrientation _ _
  -- The coordinates of `A v` in terms of the six entries `⟪eᵢ, A eⱼ⟫`, `i < j`, of its matrix.
  have hm (i j : Fin 4) : ⟪e i, A (e j)⟫ = -⟪e j, A (e i)⟫ := by
    rw [← hA, real_inner_comm]
  have hd (i : Fin 4) : ⟪e i, A (e i)⟫ = 0 := by linarith [hm i i]
  have hAe (v : V) (i : Fin 4) : e.repr (A v) i =
      ![⟪e 0, A (e 1)⟫ * e.repr v 1 + ⟪e 0, A (e 2)⟫ * e.repr v 2 + ⟪e 0, A (e 3)⟫ * e.repr v 3,
        -⟪e 0, A (e 1)⟫ * e.repr v 0 + ⟪e 1, A (e 2)⟫ * e.repr v 2 + ⟪e 1, A (e 3)⟫ * e.repr v 3,
        -⟪e 0, A (e 2)⟫ * e.repr v 0 - ⟪e 1, A (e 2)⟫ * e.repr v 1 + ⟪e 2, A (e 3)⟫ * e.repr v 3,
        -⟪e 0, A (e 3)⟫ * e.repr v 0 - ⟪e 1, A (e 3)⟫ * e.repr v 1 -
          ⟪e 2, A (e 3)⟫ * e.repr v 2] i := by
    have hv : e.repr (A v) i = ∑ j, e.repr v j * ⟪e i, A (e j)⟫ := by
      conv_lhs => rw [← e.sum_repr v]
      simp [OrthonormalBasis.repr_apply_apply]
    rw [hv, Fin.sum_univ_four]
    fin_cases i <;>
      simp [hd, hm 1 0, hm 2 0, hm 3 0, hm 2 1, hm 3 1, hm 3 2] <;> ring
  refine LinearMap.congr_fun (linearMap_ext_inner_ιMulti_two (f := (o.hodgeStar hkl).toLinearMap ∘ₗ
    exteriorPower.lieMap 2 A) (g := exteriorPower.lieMap 2 A ∘ₗ
    (o.hodgeStar hkl).toLinearMap) fun a b u w ↦ ?_) x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, inner_lieMap_two_left hA,
    exteriorPower.lieMap_two_apply_ιMulti, map_add, inner_add_left, inner_add_right,
    o.inner_hodgeStar_ιMulti_two hkl, o.volumeForm_robust e he, Basis.det_apply,
    Matrix.det_fin_four]
  simp only [Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, hAe]
  ring

end Orientation
