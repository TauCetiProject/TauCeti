/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Basic
import TauCeti.LinearAlgebra.ExteriorPower.WedgePairing
import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.InnerProductSpace.Trace.Free
import TauCeti.LinearAlgebra.Matrix.Determinant.FinFour

/-!
# Metric and functorial properties of the Hodge star

The Hodge star preserves the inner product and hence defines a linear isometric equivalence
between complementary exterior powers. Combined with the defining identity
`⟪⋆x, y⟫ = vol (x ∧ y)`, this gives the wedge characterization `α ∧ ⋆β = ⟪α, β⟫ vol`.
On the top exterior power the inner product is the product of the volumes,
`⟪x, y⟫ = vol x * vol y`, since `⋆1` is a unit vector representing the volume. Since `⋆⋆` is
`(-1) ^ (k l)` on `⋀ᵏ V`, the adjoint of the star `⋀ᵏ V → ⋀ˡ V` is `(-1) ^ (k l)` times the star
`⋀ˡ V → ⋀ᵏ V` (`Orientation.inner_hodgeStar_left`), and the adjoint composed with the star is
the identity (`Orientation.adjoint_hodgeStar_comp_hodgeStar`). In an even middle degree the Hodge
star is therefore symmetric, so a self-dual or anti-self-dual form pairs with `⋆y` as with `±y`.
Reversing the orientation negates the Hodge star, and transporting the orientation along a
linear isometric equivalence commutes with it. These statements hold also in dimension zero, for
either orientation.

The derivation action `D_A` of a skew-adjoint endomorphism `A`, which applies `A` to one factor of
a wedge at a time, commutes with the Hodge star in every degree (`Orientation.hodgeStar_lieMap`):
`D_A` is skew-adjoint and acts on the top exterior power by `tr A = 0`, so it preserves the
characterization `⟪⋆x, y⟫ = vol (x ∧ y)`. This is the infinitesimal form of the invariance of the
star under rotations.

In dimension four, the Hodge star of a wedge of two vectors pairs with another such wedge to the
volume of the four vectors, `⟪⋆(a ∧ b), u ∧ w⟫ = vol(a, b, u, w)`
(`Orientation.inner_hodgeStar_ιMulti_two`). For a positively oriented orthonormal basis `e`, this
gives `⋆(e₀ ∧ e₁) = e₂ ∧ e₃`, `⋆(e₀ ∧ e₂) = -(e₁ ∧ e₃)` and `⋆(e₀ ∧ e₃) = e₁ ∧ e₂`
(`Orientation.hodgeStar_ιMulti_zero_one` and its companions). Consequently a self-dual or
anti-self-dual two-vector is determined by its coordinates along `e₀ ∧ e₁`, `e₀ ∧ e₂` and `e₀ ∧ e₃`,
and its squared norm is twice the sum of their squares
(`Orientation.inner_ιMulti_two_of_hodgeStar_eq_self`, `Orientation.norm_sq_of_hodgeStar_eq_self`,
`Orientation.inner_ιMulti_two_of_hodgeStar_eq_neg`, `Orientation.norm_sq_of_hodgeStar_eq_neg`).

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

/-- **The adjoint of the Hodge star**: `⟪⋆x, y⟫ = (-1) ^ (k l) ⟪x, ⋆y⟫` for `x ∈ ⋀ᵏ V` and
`y ∈ ⋀ˡ V`, where `k + l = finrank ℝ V`. -/
theorem inner_hodgeStar_left {k l : ℕ} (hkl : k + l = finrank ℝ V) (hlk : l + k = finrank ℝ V)
    (x : ⋀[ℝ]^k V) (y : ⋀[ℝ]^l V) :
    ⟪o.hodgeStar hkl x, y⟫ = (-1) ^ (k * l) * ⟪x, o.hodgeStar hlk y⟫ := by
  -- Pair `⋆x` with `y = (-1) ^ (l k) ⋆⋆y` and use that the star preserves inner products.
  have h := o.inner_hodgeStar_hodgeStar hkl x (o.hodgeStar hlk y)
  rw [o.hodgeStar_hodgeStar hlk hkl, real_inner_smul_right] at h
  rw [← h, ← mul_assoc, ← pow_add, mul_comm l k, ← two_mul, pow_mul]
  simp

/-- In an even middle degree, `k + k = finrank ℝ V` with `k` even, the Hodge star is symmetric,
`⟪⋆x, y⟫ = ⟪x, ⋆y⟫`, being an isometric involution. This covers two-forms in dimension four. -/
theorem isSymmetric_hodgeStar_of_even {k : ℕ} (hk : Even k) (hkk : k + k = finrank ℝ V) :
    (o.hodgeStar hkk : ⋀[ℝ]^k V →ₗ[ℝ] ⋀[ℝ]^k V).IsSymmetric := fun x y ↦ by
  rw [LinearEquiv.coe_coe, o.inner_hodgeStar_left hkk hkk,
    (hk.mul_right k).neg_one_pow, one_mul]

/-- A self-dual `η`, with `⋆η = η`, in an even middle degree pairs with `⋆y` as with `y`:
`⟪η, ⋆y⟫ = ⟪η, y⟫`. -/
theorem inner_hodgeStar_right_of_hodgeStar_eq_self {k : ℕ} (hk : Even k)
    (hkk : k + k = finrank ℝ V) {η : ⋀[ℝ]^k V} (hη : o.hodgeStar hkk η = η) (y : ⋀[ℝ]^k V) :
    ⟪η, o.hodgeStar hkk y⟫ = ⟪η, y⟫ := by
  have h := o.isSymmetric_hodgeStar_of_even hk hkk η y
  simp only [LinearEquiv.coe_coe, hη] at h
  exact h.symm

/-- An anti-self-dual `μ`, with `⋆μ = -μ`, in an even middle degree pairs with `⋆y` as with
`-y`: `⟪μ, ⋆y⟫ = -⟪μ, y⟫`. -/
theorem inner_hodgeStar_right_of_hodgeStar_eq_neg {k : ℕ} (hk : Even k)
    (hkk : k + k = finrank ℝ V) {μ : ⋀[ℝ]^k V} (hμ : o.hodgeStar hkk μ = -μ) (y : ⋀[ℝ]^k V) :
    ⟪μ, o.hodgeStar hkk y⟫ = -⟪μ, y⟫ := by
  have h := o.isSymmetric_hodgeStar_of_even hk hkk μ y
  simp only [LinearEquiv.coe_coe, hμ, inner_neg_left] at h
  exact h.symm

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

/-- The Hodge star `⋀ᵏ V → ⋀ˡ V`, an isometry, composed with its adjoint is the identity. -/
theorem adjoint_hodgeStar_comp_hodgeStar {k l : ℕ} (hkl : k + l = finrank ℝ V) :
    ContinuousLinearMap.adjoint
        (LinearMap.toContinuousLinearMap (o.hodgeStar hkl : ⋀[ℝ]^k V →ₗ[ℝ] ⋀[ℝ]^l V)) ∘L
      LinearMap.toContinuousLinearMap (o.hodgeStar hkl : ⋀[ℝ]^k V →ₗ[ℝ] ⋀[ℝ]^l V) = 1 :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).1 (o.norm_hodgeStar hkl)

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

/-- **Skew-adjoint endomorphisms commute with the Hodge star**: `⋆ (D_A x) = D_A (⋆ x)` for the
derivation action `D_A` of a skew-adjoint endomorphism `A` on forms of every degree. This is the
infinitesimal form of the invariance of `⋆` under rotations. -/
theorem hodgeStar_lieMap {k l : ℕ} (hkl : k + l = finrank ℝ V) {A : V →ₗ[ℝ] V}
    (hA : ∀ u w, ⟪A u, w⟫ = -⟪u, A w⟫) (x : ⋀[ℝ]^k V) :
    o.hodgeStar hkl (lieMap k A x) = lieMap l A (o.hodgeStar hkl x) := by
  -- `D_A` is skew-adjoint, and it acts on the top exterior power by `tr A = 0`.
  refine ext_inner_right ℝ fun y ↦ ?_
  rw [inner_hodgeStar_apply, inner_lieMap_left hA, inner_hodgeStar_apply, eq_neg_iff_add_eq_zero,
    wedgePairing_lieMap_add_wedgePairing_lieMap, LinearMap.trace_eq_zero_of_inner_left_eq_neg hA,
    zero_mul]

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

variable {o} (hkl : 2 + 2 = finrank ℝ V) {e : OrthonormalBasis (Fin 4) ℝ V}
  (he : e.toBasis.orientation = o)
include he

/-- For a positively oriented orthonormal basis `e` in dimension four, `⋆(e₀ ∧ e₁) = e₂ ∧ e₃`. -/
theorem hodgeStar_ιMulti_zero_one :
    o.hodgeStar hkl (ιMulti ℝ 2 ![e 0, e 1]) = ιMulti ℝ 2 ![e 2, e 3] := by
  refine ext_inner_ιMulti_two fun u w ↦ ?_
  rw [o.inner_hodgeStar_ιMulti_two hkl, inner_ιMulti_two]
  simp [o.volumeForm_robust e he, Basis.det_apply, Matrix.det_fin_four, Basis.toMatrix_apply,
    ← e.repr_apply_apply, OrthonormalBasis.repr_self]

/-- For a positively oriented orthonormal basis `e` in dimension four, `⋆(e₂ ∧ e₃) = e₀ ∧ e₁`. -/
theorem hodgeStar_ιMulti_two_three :
    o.hodgeStar hkl (ιMulti ℝ 2 ![e 2, e 3]) = ιMulti ℝ 2 ![e 0, e 1] := by
  rw [← o.hodgeStar_ιMulti_zero_one hkl he, o.hodgeStar_hodgeStar hkl hkl]
  norm_num

/-- For a positively oriented orthonormal basis `e` in dimension four,
`⋆(e₀ ∧ e₂) = -(e₁ ∧ e₃)`. -/
theorem hodgeStar_ιMulti_zero_two :
    o.hodgeStar hkl (ιMulti ℝ 2 ![e 0, e 2]) = -ιMulti ℝ 2 ![e 1, e 3] := by
  refine ext_inner_ιMulti_two fun u w ↦ ?_
  rw [o.inner_hodgeStar_ιMulti_two hkl, inner_neg_left, inner_ιMulti_two]
  simp [o.volumeForm_robust e he, Basis.det_apply, Matrix.det_fin_four, Basis.toMatrix_apply,
    ← e.repr_apply_apply, OrthonormalBasis.repr_self]
  ring

/-- For a positively oriented orthonormal basis `e` in dimension four, `⋆(e₀ ∧ e₃) = e₁ ∧ e₂`. -/
theorem hodgeStar_ιMulti_zero_three :
    o.hodgeStar hkl (ιMulti ℝ 2 ![e 0, e 3]) = ιMulti ℝ 2 ![e 1, e 2] := by
  refine ext_inner_ιMulti_two fun u w ↦ ?_
  rw [o.inner_hodgeStar_ιMulti_two hkl, inner_ιMulti_two]
  simp [o.volumeForm_robust e he, Basis.det_apply, Matrix.det_fin_four, Basis.toMatrix_apply,
    ← e.repr_apply_apply, OrthonormalBasis.repr_self]
  ring

/-- For a positively oriented orthonormal basis `e` in dimension four, the coordinates of an
anti-self-dual `μ`, with `⋆μ = -μ`, in the basis `eᵢ ∧ eⱼ` are determined by its three coordinates
along `e₀ ∧ e₁`, `e₀ ∧ e₂` and `e₀ ∧ e₃`. -/
theorem inner_ιMulti_two_of_hodgeStar_eq_neg {μ : ⋀[ℝ]^2 V}
    (hμ : o.hodgeStar hkl μ = -μ) :
    ⟪μ, ιMulti ℝ 2 ![e 2, e 3]⟫ = -⟪μ, ιMulti ℝ 2 ![e 0, e 1]⟫ ∧
      ⟪μ, ιMulti ℝ 2 ![e 1, e 3]⟫ = ⟪μ, ιMulti ℝ 2 ![e 0, e 2]⟫ ∧
      ⟪μ, ιMulti ℝ 2 ![e 1, e 2]⟫ = -⟪μ, ιMulti ℝ 2 ![e 0, e 3]⟫ := by
  have hneg := o.inner_hodgeStar_right_of_hodgeStar_eq_neg even_two hkl hμ
  refine ⟨?_, ?_, ?_⟩
  · rw [← o.hodgeStar_ιMulti_zero_one hkl he, hneg]
  · rw [← neg_neg (ιMulti ℝ 2 ![e 1, e 3]), ← o.hodgeStar_ιMulti_zero_two hkl he,
      inner_neg_right, hneg, neg_neg]
  · rw [← o.hodgeStar_ιMulti_zero_three hkl he, hneg]

/-- For a positively oriented orthonormal basis `e` in dimension four, the squared norm of an
anti-self-dual `μ`, with `⋆μ = -μ`, is twice the sum of the squares of its coordinates along
`e₀ ∧ e₁`, `e₀ ∧ e₂` and `e₀ ∧ e₃`. -/
theorem norm_sq_of_hodgeStar_eq_neg {μ : ⋀[ℝ]^2 V} (hμ : o.hodgeStar hkl μ = -μ) :
    ‖μ‖ ^ 2 = 2 * (⟪μ, ιMulti ℝ 2 ![e 0, e 1]⟫ ^ 2 + ⟪μ, ιMulti ℝ 2 ![e 0, e 2]⟫ ^ 2 +
      ⟪μ, ιMulti ℝ 2 ![e 0, e 3]⟫ ^ 2) := by
  obtain ⟨h23, h13, h12⟩ := o.inner_ιMulti_two_of_hodgeStar_eq_neg hkl he hμ
  rw [e.norm_sq_eq_sum_sq_inner_ιMulti_two, h23, h13, h12]
  ring

/-- For a positively oriented orthonormal basis `e` in dimension four, the coordinates of a
self-dual `F`, with `⋆F = F`, in the basis `eᵢ ∧ eⱼ` are determined by its three coordinates along
`e₀ ∧ e₁`, `e₀ ∧ e₂` and `e₀ ∧ e₃`. -/
theorem inner_ιMulti_two_of_hodgeStar_eq_self {F : ⋀[ℝ]^2 V}
    (hF : o.hodgeStar hkl F = F) :
    ⟪F, ιMulti ℝ 2 ![e 2, e 3]⟫ = ⟪F, ιMulti ℝ 2 ![e 0, e 1]⟫ ∧
      ⟪F, ιMulti ℝ 2 ![e 1, e 3]⟫ = -⟪F, ιMulti ℝ 2 ![e 0, e 2]⟫ ∧
      ⟪F, ιMulti ℝ 2 ![e 1, e 2]⟫ = ⟪F, ιMulti ℝ 2 ![e 0, e 3]⟫ := by
  have hself := o.inner_hodgeStar_right_of_hodgeStar_eq_self even_two hkl hF
  refine ⟨?_, ?_, ?_⟩
  · rw [← o.hodgeStar_ιMulti_zero_one hkl he, hself]
  · rw [← neg_neg (ιMulti ℝ 2 ![e 1, e 3]), ← o.hodgeStar_ιMulti_zero_two hkl he,
      inner_neg_right, hself]
  · rw [← o.hodgeStar_ιMulti_zero_three hkl he, hself]

/-- For a positively oriented orthonormal basis `e` in dimension four, the squared norm of a
self-dual `F`, with `⋆F = F`, is twice the sum of the squares of its coordinates along `e₀ ∧ e₁`,
`e₀ ∧ e₂` and `e₀ ∧ e₃`. -/
theorem norm_sq_of_hodgeStar_eq_self {F : ⋀[ℝ]^2 V} (hF : o.hodgeStar hkl F = F) :
    ‖F‖ ^ 2 = 2 * (⟪F, ιMulti ℝ 2 ![e 0, e 1]⟫ ^ 2 + ⟪F, ιMulti ℝ 2 ![e 0, e 2]⟫ ^ 2 +
      ⟪F, ιMulti ℝ 2 ![e 0, e 3]⟫ ^ 2) := by
  obtain ⟨h23, h13, h12⟩ := o.inner_ιMulti_two_of_hodgeStar_eq_self hkl he hF
  rw [e.norm_sq_eq_sum_sq_inner_ιMulti_two, h23, h13, h12]
  ring

end Orientation
