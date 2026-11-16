/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.ParityKernel
public import TauCeti.LinearAlgebra.IntegralLattice.Orthogonal.Sum
public import TauCeti.LinearAlgebra.IntegralLattice.RankOne.Basic

/-!
# The indefinite odd unimodular plane and its hyperbolic two-neighbors

The rank-two lattice `indefiniteUnitPlane` on `ℚ²` has Gram matrix `diag(1, -1)` in the standard
coordinate basis, so it is canonically isometric to `⟨1⟩ ⊕ ⟨-1⟩`. It is unimodular, odd, and
indefinite of signature `(1, 0, 1)`.

Its vector `![1, 1]` is characteristic of norm zero, so `8 ∣ 0`. By the norm-parity kernel theory
of `TauCeti.LinearAlgebra.IntegralLattice.Characteristic.ParityKernel`, its canonical even
sublattice consists of integer pairs `(x₀, x₁)` with `x₀ + x₁` even, and adjoining either
`![1 / 2, 1 / 2]` or `![1, 0] + ![1 / 2, 1 / 2]` produces the two even unimodular Kneser
two-neighbors of `indefiniteUnitPlane`. Both two-neighbors are explicitly isometric to the
hyperbolic plane `U`.

For any even lattice `Y`, forming the orthogonal sum with `indefiniteUnitPlane` commutes with taking
the even sublattice, `(Y ⊕ M)_even = Y ⊕ M_even`, and Kneser `p`-neighbors are preserved under
orthogonal direct sums with an arbitrary lattice. Consequently `Y ⊕ U` is isometric to an explicit
even Kneser two-neighbor of `Y ⊕ indefiniteUnitPlane`.

## Main definitions

* `TauCeti.IntegralLattice.indefiniteUnitPlane`: the odd unimodular plane `⟨1⟩ ⊕ ⟨-1⟩` on `ℚ²`.
* `TauCeti.IntegralLattice.rankOneOrthogonalSumIsometryIndefiniteUnitPlane`: the canonical isometry
  `⟨1⟩ ⊕ ⟨-1⟩ ≅ indefiniteUnitPlane`.
* `TauCeti.IntegralLattice.indefiniteUnitPlaneFirstNeighbor` and
  `TauCeti.IntegralLattice.indefiniteUnitPlaneSecondNeighbor`: the two even unimodular Kneser
  two-neighbors of `indefiniteUnitPlane`.
* `TauCeti.IntegralLattice.hyperbolicPlaneIsometryIndefiniteUnitPlaneFirstNeighbor` and
  `TauCeti.IntegralLattice.hyperbolicPlaneIsometryIndefiniteUnitPlaneSecondNeighbor`: explicit
  isometries from `hyperbolicPlane` onto each two-neighbor.

## Main results

* `TauCeti.IntegralLattice.indefiniteUnitPlane_signature`: `indefiniteUnitPlane` has signature
  `(1, 0, 1)`.
* `TauCeti.IntegralLattice.evenSublattice_orthogonalSum_of_isEven_left`:
  `(Y ⊕ M).evenSublattice = Y ⊕ M.evenSublattice` when `Y` is even.
* `TauCeti.IntegralLattice.IsNeighbor.orthogonalSum_left`: Kneser `p`-neighbors are preserved by
  orthogonal direct sums.
* `TauCeti.IntegralLattice.exists_isNeighbor_orthogonalSum_indefiniteUnitPlane`: for an even
  lattice `Y`, `Y ⊕ hyperbolicPlane` is isometric to an even Kneser two-neighbor of
  `Y ⊕ indefiniteUnitPlane`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter V, §2.2.
* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Chapter II, §2.
-/

public section

open Module

namespace TauCeti.IntegralLattice

/-! ## The lattice `⟨1⟩ ⊕ ⟨-1⟩` on `ℚ²` -/

private def indefiniteUnitPlaneMatrix : Matrix (Fin 2) (Fin 2) ℤ :=
  Matrix.diagonal ![1, -1]

private theorem isSymm_indefiniteUnitPlaneMatrix : indefiniteUnitPlaneMatrix.IsSymm :=
  Matrix.isSymm_diagonal _

/-- The indefinite odd unimodular plane on `ℚ²`, with Gram matrix `diag(1, -1)`. -/
noncomputable def indefiniteUnitPlane : IntegralLattice (Fin 2 → ℚ) :=
  ofGramMatrix (Pi.basisFun ℚ (Fin 2)) indefiniteUnitPlaneMatrix isSymm_indefiniteUnitPlaneMatrix

/-- The standard coordinate integral basis of `indefiniteUnitPlane`. -/
noncomputable def indefiniteUnitPlaneBasis : Basis (Fin 2) ℤ indefiniteUnitPlane :=
  ofGramMatrix.basis (Pi.basisFun ℚ (Fin 2)) indefiniteUnitPlaneMatrix
    isSymm_indefiniteUnitPlaneMatrix

/-- Ambient coercion of `indefiniteUnitPlaneBasis`. -/
@[simp]
theorem coe_indefiniteUnitPlaneBasis (i : Fin 2) :
    (indefiniteUnitPlaneBasis i : Fin 2 → ℚ) = Pi.single i 1 := by
  have h := ofGramMatrix.coe_basis (Pi.basisFun ℚ (Fin 2)) indefiniteUnitPlaneMatrix
    isSymm_indefiniteUnitPlaneMatrix i
  exact h.trans (Pi.basisFun_apply ℚ (Fin 2) i)

/-- The Gram matrix of `indefiniteUnitPlane` in `indefiniteUnitPlaneBasis` is `diag(1, -1)`. -/
@[simp]
theorem gramMatrix_indefiniteUnitPlaneBasis :
    indefiniteUnitPlane.gramMatrix indefiniteUnitPlaneBasis = !![1, 0; 0, -1] := by
  have h := gramMatrix_ofGramMatrix (Pi.basisFun ℚ (Fin 2)) indefiniteUnitPlaneMatrix
    isSymm_indefiniteUnitPlaneMatrix
  have hg : indefiniteUnitPlane.gramMatrix indefiniteUnitPlaneBasis =
      indefiniteUnitPlaneMatrix := by
    simpa only [indefiniteUnitPlane, indefiniteUnitPlaneBasis] using h
  rw [hg]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [indefiniteUnitPlaneMatrix]

/-- A vector belongs to `indefiniteUnitPlane` precisely when both coordinates are integers. -/
@[simp]
theorem mem_indefiniteUnitPlane_carrier_iff (x : Fin 2 → ℚ) :
    x ∈ indefiniteUnitPlane.carrier ↔ ∀ i, ∃ z : ℤ, (z : ℚ) = x i := by
  classical
  rw [indefiniteUnitPlane, ofGramMatrix_carrier, Module.Basis.mem_span_iff_repr_mem]
  simp [Pi.basisFun_repr]

/-- The bilinear form of `indefiniteUnitPlane` is `x₀ y₀ - x₁ y₁`. -/
@[simp]
theorem indefiniteUnitPlane_form_apply (x y : Fin 2 → ℚ) :
    indefiniteUnitPlane.form x y = x 0 * y 0 - x 1 * y 1 := by
  let _ : DecidableEq (Fin 2) := Classical.decEq _
  rw [indefiniteUnitPlane, ofGramMatrix_form, Matrix.toBilin_apply]
  simp [Fin.sum_univ_two, indefiniteUnitPlaneMatrix]
  ring

/-- The quadratic norm on `indefiniteUnitPlane` is `x₀² - x₁²`. -/
@[simp]
theorem indefiniteUnitPlane_norm_apply (x : Fin 2 → ℚ) :
    indefiniteUnitPlane.norm x = x 0 ^ 2 - x 1 ^ 2 := by
  rw [norm_apply, indefiniteUnitPlane_form_apply]
  ring

/-- `indefiniteUnitPlane` has rank two. -/
@[simp]
theorem finrank_indefiniteUnitPlane : Module.finrank ℤ indefiniteUnitPlane = 2 := by
  rw [indefiniteUnitPlane.finrank_carrier]
  simp

/-- `indefiniteUnitPlane` has signed determinant `-1`. -/
@[simp]
theorem indefiniteUnitPlane_determinant : indefiniteUnitPlane.determinant = -1 := by
  rw [indefiniteUnitPlane, determinant_ofGramMatrix]
  simp [indefiniteUnitPlaneMatrix]

/-- `indefiniteUnitPlane` has discriminant `1`. -/
@[simp]
theorem indefiniteUnitPlane_discriminant : indefiniteUnitPlane.discriminant = 1 := by
  rw [indefiniteUnitPlane, discriminant_ofGramMatrix]
  simp [indefiniteUnitPlaneMatrix]

/-- `indefiniteUnitPlane` is nondegenerate. -/
instance instIsNondegenerateIndefiniteUnitPlane : indefiniteUnitPlane.IsNondegenerate :=
  ⟨indefiniteUnitPlane.determinant_ne_zero_iff.mp (by simp)⟩

/-- `indefiniteUnitPlane` is unimodular. -/
theorem isUnimodular_indefiniteUnitPlane : indefiniteUnitPlane.IsUnimodular := by
  rw [indefiniteUnitPlane.isUnimodular_iff_discriminant_eq_one]
  exact indefiniteUnitPlane_discriminant

/-- `indefiniteUnitPlane` is an odd integral lattice. -/
theorem not_isEven_indefiniteUnitPlane : ¬ indefiniteUnitPlane.IsEven := by
  rw [indefiniteUnitPlane, isEven_ofGramMatrix_iff]
  intro h
  obtain ⟨k, hk⟩ := h 0
  have h1 : (1 : ℤ) = k + k := by simpa [indefiniteUnitPlaneMatrix] using hk
  omega

/-- The canonical isometry `(rankOne 1).orthogonalSum (rankOne (-1)) ≅ indefiniteUnitPlane`. -/
noncomputable def rankOneOrthogonalSumIsometryIndefiniteUnitPlane :
    Isometry ((rankOne 1).orthogonalSum (rankOne (-1))) indefiniteUnitPlane where
  toLinearEquiv := (LinearEquiv.finTwoArrow ℚ ℚ).symm
  map_app' p q := by
    have hp : (LinearEquiv.finTwoArrow ℚ ℚ).symm p = ![p.1, p.2] := rfl
    have hq : (LinearEquiv.finTwoArrow ℚ ℚ).symm q = ![q.1, q.2] := rfl
    simp only [LinearEquiv.coe_toLinearMap, LinearMap.toFun_eq_coe]
    rw [hp, hq, indefiniteUnitPlane_form_apply, orthogonalSum_form, LinearMap.BilinForm.prod_apply,
      rankOne_form_apply, rankOne_form_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_one, Int.cast_neg]
    ring
  map_carrier := by
    ext x
    rw [Submodule.mem_map_equiv, orthogonalSum_carrier, Submodule.mem_prod,
      mem_rankOne_carrier_iff, mem_rankOne_carrier_iff, mem_indefiniteUnitPlane_carrier_iff,
      Fin.forall_fin_two]
    rfl

/-- `rankOneOrthogonalSumIsometryIndefiniteUnitPlane` sends `(a, b)` to `![a, b]`. -/
@[simp]
theorem rankOneOrthogonalSumIsometryIndefiniteUnitPlane_apply (p : ℚ × ℚ) :
    rankOneOrthogonalSumIsometryIndefiniteUnitPlane p = ![p.1, p.2] :=
  (rfl)

/-- `indefiniteUnitPlane` has signature `(1, 0, 1)`. -/
@[simp]
theorem indefiniteUnitPlane_signature : indefiniteUnitPlane.signature = (1, 0, 1) := by
  have hp := rankOne_signature_of_pos zero_lt_one
  have hn := rankOne_signature_of_neg (neg_lt_zero.mpr zero_lt_one)
  simp only [signature, Prod.mk.injEq] at hp hn
  rw [← rankOneOrthogonalSumIsometryIndefiniteUnitPlane.signature_eq, signature_orthogonalSum,
    hp.1, hp.2.1, hp.2.2, hn.1, hn.2.1, hn.2.2]

/-! ## Characteristic vector, even sublattice, and the two hyperbolic neighbors -/

/-- The isotropic characteristic vector `![1, 1]` of `indefiniteUnitPlane`. -/
def indefiniteUnitPlaneCharacteristicVector : indefiniteUnitPlane :=
  ⟨![1, 1], (mem_indefiniteUnitPlane_carrier_iff _).mpr fun i ↦ by
    fin_cases i <;> exact ⟨1, rfl⟩⟩

/-- Ambient coercion of `indefiniteUnitPlaneCharacteristicVector`. -/
@[simp]
theorem coe_indefiniteUnitPlaneCharacteristicVector :
    (indefiniteUnitPlaneCharacteristicVector : Fin 2 → ℚ) = ![1, 1] :=
  (rfl)

/-- `![1, 1]` is a characteristic vector of `indefiniteUnitPlane`. -/
theorem isCharacteristicVector_indefiniteUnitPlaneCharacteristicVector :
    indefiniteUnitPlane.IsCharacteristicVector indefiniteUnitPlaneCharacteristicVector := by
  rw [indefiniteUnitPlane.isCharacteristicVector_iff]
  intro y
  obtain ⟨⟨z₀, hz₀⟩, ⟨z₁, hz₁⟩⟩ :=
    (Fin.forall_fin_two.mp ((mem_indefiniteUnitPlane_carrier_iff y).mp y.2))
  have hform : indefiniteUnitPlane.integralForm indefiniteUnitPlaneCharacteristicVector y =
      z₀ - z₁ := by
    apply Int.cast_injective (α := ℚ)
    rw [integralForm_cast, indefiniteUnitPlane_form_apply,
      coe_indefiniteUnitPlaneCharacteristicVector, ← hz₀, ← hz₁]
    simp
  have hnorm : indefiniteUnitPlane.integralNorm y = z₀ ^ 2 - z₁ ^ 2 := by
    apply Int.cast_injective (α := ℚ)
    rw [integralNorm_cast, indefiniteUnitPlane_norm_apply, ← hz₀, ← hz₁]
    push_cast
    ring
  rw [hform, hnorm, Int.modEq_iff_dvd]
  rcases Int.even_or_odd (z₀ - z₁) with ⟨k, hk⟩ | ⟨k, hk⟩
  · refine ⟨k * (z₀ + z₁ - 1), ?_⟩
    calc
      z₀ ^ 2 - z₁ ^ 2 - (z₀ - z₁) = (z₀ - z₁) * (z₀ + z₁ - 1) := by ring
      _ = 2 * (k * (z₀ + z₁ - 1)) := by rw [hk]; ring
  · have hsum : Even (z₀ + z₁ - 1) := by
      refine ⟨z₁ + k, ?_⟩
      linarith
    obtain ⟨m, hm⟩ := hsum
    refine ⟨(z₀ - z₁) * m, ?_⟩
    calc
      z₀ ^ 2 - z₁ ^ 2 - (z₀ - z₁) = (z₀ - z₁) * (z₀ + z₁ - 1) := by ring
      _ = 2 * ((z₀ - z₁) * m) := by rw [hm]; ring

/-- `indefiniteUnitPlaneCharacteristicVector` has integral norm zero. -/
@[simp]
theorem integralNorm_indefiniteUnitPlaneCharacteristicVector :
    indefiniteUnitPlane.integralNorm indefiniteUnitPlaneCharacteristicVector = 0 := by
  apply Int.cast_injective (α := ℚ)
  rw [integralNorm_cast, indefiniteUnitPlane_norm_apply,
    coe_indefiniteUnitPlaneCharacteristicVector]
  simp

/-- The standard unit-norm vector `![1, 0]` of `indefiniteUnitPlane`. -/
def indefiniteUnitPlaneOddVector : indefiniteUnitPlane :=
  ⟨![1, 0], (mem_indefiniteUnitPlane_carrier_iff _).mpr fun i ↦ by
    fin_cases i
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩⟩

/-- Ambient coercion of `indefiniteUnitPlaneOddVector`. -/
@[simp]
theorem coe_indefiniteUnitPlaneOddVector :
    (indefiniteUnitPlaneOddVector : Fin 2 → ℚ) = ![1, 0] :=
  (rfl)

/-- `indefiniteUnitPlaneOddVector` has integral norm `1`. -/
@[simp]
theorem integralNorm_indefiniteUnitPlaneOddVector :
    indefiniteUnitPlane.integralNorm indefiniteUnitPlaneOddVector = 1 := by
  apply Int.cast_injective (α := ℚ)
  rw [integralNorm_cast, indefiniteUnitPlane_norm_apply, coe_indefiniteUnitPlaneOddVector]
  simp

/-- `indefiniteUnitPlaneOddVector` has odd integral norm. -/
theorem odd_integralNorm_indefiniteUnitPlaneOddVector :
    Odd (indefiniteUnitPlane.integralNorm indefiniteUnitPlaneOddVector) := by
  rw [integralNorm_indefiniteUnitPlaneOddVector]
  exact odd_one

/-- Membership in `indefiniteUnitPlane.evenSublattice` means integral coordinates of equal parity
(equivalently, even coordinate sum). -/
theorem mem_evenSublattice_indefiniteUnitPlane_carrier_iff (x : Fin 2 → ℚ) :
    x ∈ indefiniteUnitPlane.evenSublattice.carrier ↔
      (∀ i, ∃ z : ℤ, (z : ℚ) = x i) ∧ ∃ k : ℤ, x 0 + x 1 = 2 * k := by
  constructor
  · intro hx
    have hxL := indefiniteUnitPlane.evenSublattice_carrier_le hx
    obtain ⟨⟨z₀, hz₀⟩, ⟨z₁, hz₁⟩⟩ :=
      Fin.forall_fin_two.mp ((mem_indefiniteUnitPlane_carrier_iff x).mp hxL)
    obtain ⟨m, hm⟩ := (indefiniteUnitPlane.even_integralNorm_iff ⟨x, hxL⟩).mp
      ((indefiniteUnitPlane.mem_evenSublattice_carrier_iff ⟨x, hxL⟩).mp hx)
    rw [indefiniteUnitPlane_norm_apply] at hm
    dsimp only at hm
    rw [← hz₀, ← hz₁] at hm
    have hdiff : Even (z₀ ^ 2 - z₁ ^ 2) :=
      ⟨m, Int.cast_injective (α := ℚ) (by push_cast; linarith)⟩
    have hsum : Even (z₀ + z₁) := by
      rcases Int.even_or_odd (z₀ + z₁) with he | ho
      · exact he
      · exfalso
        have ho_sub : Odd (z₀ - z₁) := by
          obtain ⟨c, hc⟩ := ho
          exact ⟨c - z₁, by omega⟩
        exact Int.not_odd_iff_even.mpr hdiff (by
          simpa [sq_sub_sq] using ho.mul ho_sub)
    obtain ⟨k, hk⟩ := hsum
    refine ⟨Fin.forall_fin_two.mpr ⟨⟨z₀, hz₀⟩, ⟨z₁, hz₁⟩⟩, k, ?_⟩
    have hzk : z₀ + z₁ = 2 * k := by omega
    rw [← hz₀, ← hz₁]
    exact_mod_cast hzk
  · rintro ⟨hxZ, k, hk⟩
    have hxL : x ∈ indefiniteUnitPlane.carrier := (mem_indefiniteUnitPlane_carrier_iff x).mpr hxZ
    obtain ⟨⟨z₀, hz₀⟩, ⟨z₁, hz₁⟩⟩ := Fin.forall_fin_two.mp hxZ
    rw [indefiniteUnitPlane.mem_evenSublattice_carrier_iff ⟨x, hxL⟩,
      indefiniteUnitPlane.even_integralNorm_iff]
    refine ⟨k * (z₀ - z₁), ?_⟩
    rw [indefiniteUnitPlane_norm_apply]
    dsimp only
    rw [← hz₀, ← hz₁]
    have hzk : (z₀ : ℚ) + z₁ = 2 * k := by rwa [hz₀, hz₁]
    push_cast
    calc
      (z₀ : ℚ) ^ 2 - z₁ ^ 2 = (z₀ + z₁) * (z₀ - z₁) := by ring
      _ = 2 * (k * (z₀ - z₁)) := by rw [hzk]; ring

private theorem eight_dvd_integralNorm_indefiniteUnitPlaneCharacteristicVector :
    8 ∣ indefiniteUnitPlane.integralNorm indefiniteUnitPlaneCharacteristicVector := by
  rw [integralNorm_indefiniteUnitPlaneCharacteristicVector]
  exact dvd_zero 8

/-- The first even unimodular Kneser two-neighbor of `indefiniteUnitPlane`, obtained by adjoining
`![1 / 2, 1 / 2]` to `indefiniteUnitPlane.evenSublattice`. -/
noncomputable def indefiniteUnitPlaneFirstNeighbor : IntegralLattice (Fin 2 → ℚ) :=
  indefiniteUnitPlane.halfCharacteristicOverlattice isUnimodular_indefiniteUnitPlane
    isCharacteristicVector_indefiniteUnitPlaneCharacteristicVector
    eight_dvd_integralNorm_indefiniteUnitPlaneCharacteristicVector

/-- The second even unimodular Kneser two-neighbor of `indefiniteUnitPlane`, obtained by adjoining
`![1, 0] + ![1 / 2, 1 / 2]` to `indefiniteUnitPlane.evenSublattice`. -/
noncomputable def indefiniteUnitPlaneSecondNeighbor : IntegralLattice (Fin 2 → ℚ) :=
  indefiniteUnitPlane.shiftedHalfCharacteristicOverlattice isUnimodular_indefiniteUnitPlane
    isCharacteristicVector_indefiniteUnitPlaneCharacteristicVector
    eight_dvd_integralNorm_indefiniteUnitPlaneCharacteristicVector
    indefiniteUnitPlaneOddVector

/-- `indefiniteUnitPlaneFirstNeighbor` is even. -/
theorem isEven_indefiniteUnitPlaneFirstNeighbor : indefiniteUnitPlaneFirstNeighbor.IsEven :=
  indefiniteUnitPlane.isEven_halfCharacteristicOverlattice _ _ _

/-- `indefiniteUnitPlaneFirstNeighbor` is unimodular. -/
theorem isUnimodular_indefiniteUnitPlaneFirstNeighbor :
    indefiniteUnitPlaneFirstNeighbor.IsUnimodular :=
  indefiniteUnitPlane.isUnimodular_halfCharacteristicOverlattice isUnimodular_indefiniteUnitPlane
    _ _

/-- `indefiniteUnitPlaneFirstNeighbor` is a Kneser two-neighbor of `indefiniteUnitPlane`. -/
theorem isNeighbor_indefiniteUnitPlaneFirstNeighbor :
    indefiniteUnitPlane.IsNeighbor indefiniteUnitPlaneFirstNeighbor 2 :=
  indefiniteUnitPlane.isNeighbor_halfCharacteristicOverlattice isUnimodular_indefiniteUnitPlane
    not_isEven_indefiniteUnitPlane _ _

/-- `indefiniteUnitPlaneSecondNeighbor` is even. -/
theorem isEven_indefiniteUnitPlaneSecondNeighbor : indefiniteUnitPlaneSecondNeighbor.IsEven :=
  indefiniteUnitPlane.isEven_shiftedHalfCharacteristicOverlattice _ _ _ _

/-- `indefiniteUnitPlaneSecondNeighbor` is unimodular. -/
theorem isUnimodular_indefiniteUnitPlaneSecondNeighbor :
    indefiniteUnitPlaneSecondNeighbor.IsUnimodular :=
  indefiniteUnitPlane.isUnimodular_shiftedHalfCharacteristicOverlattice
    isUnimodular_indefiniteUnitPlane _ _ _

/-- `indefiniteUnitPlaneSecondNeighbor` is a Kneser two-neighbor of `indefiniteUnitPlane`. -/
theorem isNeighbor_indefiniteUnitPlaneSecondNeighbor :
    indefiniteUnitPlane.IsNeighbor indefiniteUnitPlaneSecondNeighbor 2 :=
  indefiniteUnitPlane.isNeighbor_shiftedHalfCharacteristicOverlattice
    isUnimodular_indefiniteUnitPlane not_isEven_indefiniteUnitPlane _ _ _

private def hyperbolicToFirstNeighborEquiv : (Fin 2 → ℚ) ≃ₗ[ℚ] (Fin 2 → ℚ) where
  toFun u := ![u 0 / 2 + u 1, u 0 / 2 - u 1]
  invFun x := ![x 0 + x 1, (x 0 - x 1) / 2]
  map_add' u v := by
    rw [funext_iff, Fin.forall_fin_two]
    exact ⟨by simp; ring, by simp; ring⟩
  map_smul' c u := by
    rw [funext_iff, Fin.forall_fin_two]
    exact ⟨by simp; ring, by simp; ring⟩
  left_inv u := by
    rw [funext_iff, Fin.forall_fin_two]
    exact ⟨by simp, by simp⟩
  right_inv x := by
    rw [funext_iff, Fin.forall_fin_two]
    exact ⟨by simp; ring, by simp; ring⟩

@[simp]
private theorem hyperbolicToFirstNeighborEquiv_apply (u : Fin 2 → ℚ) :
    hyperbolicToFirstNeighborEquiv u = ![u 0 / 2 + u 1, u 0 / 2 - u 1] :=
  rfl

private theorem hyperbolicToFirstNeighborEquiv_mem_iff (u : Fin 2 → ℚ) :
    hyperbolicToFirstNeighborEquiv u ∈ indefiniteUnitPlaneFirstNeighbor.carrier ↔
      u ∈ hyperbolicPlane.carrier := by
  rw [indefiniteUnitPlaneFirstNeighbor,
    indefiniteUnitPlane.mem_halfCharacteristicOverlattice_carrier_iff,
    mem_evenSublattice_indefiniteUnitPlane_carrier_iff,
    mem_evenSublattice_indefiniteUnitPlane_carrier_iff,
    mem_hyperbolicPlane_carrier_iff]
  simp only [Fin.forall_fin_two]
  constructor
  · rintro (⟨⟨⟨z₀, hz₀⟩, ⟨z₁, hz₁⟩⟩, k, hk⟩ | ⟨⟨⟨z₀, hz₀⟩, ⟨z₁, hz₁⟩⟩, k, hk⟩)
    · simp only [hyperbolicToFirstNeighborEquiv_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one] at hz₀ hz₁ hk
      exact ⟨⟨z₀ + z₁, by push_cast; linarith⟩, ⟨z₀ - k, by push_cast; linarith⟩⟩
    · simp only [hyperbolicToFirstNeighborEquiv_apply,
        coe_indefiniteUnitPlaneCharacteristicVector, Pi.sub_apply, Pi.smul_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul] at hz₀ hz₁ hk
      exact ⟨⟨z₀ + z₁ + 1, by push_cast; linarith⟩, ⟨z₀ - k, by push_cast; linarith⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    rcases Int.even_or_odd a with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      simp only [hyperbolicToFirstNeighborEquiv_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        ← ha, ← hb]
      exact ⟨⟨⟨m + b, by push_cast; ring⟩, ⟨m - b, by push_cast; ring⟩⟩, m, by push_cast; ring⟩
    · right
      simp only [hyperbolicToFirstNeighborEquiv_apply,
        coe_indefiniteUnitPlaneCharacteristicVector, Pi.sub_apply, Pi.smul_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul, ← ha, ← hb]
      exact ⟨⟨⟨m + b, by push_cast; ring⟩, ⟨m - b, by push_cast; ring⟩⟩, m, by push_cast; ring⟩

/-- Explicit isometry from `hyperbolicPlane` onto `indefiniteUnitPlaneFirstNeighbor`, sending the
hyperbolic basis vectors `![1, 0], ![0, 1]` to `![1 / 2, 1 / 2], ![1, -1]`. -/
noncomputable def hyperbolicPlaneIsometryIndefiniteUnitPlaneFirstNeighbor :
    Isometry hyperbolicPlane indefiniteUnitPlaneFirstNeighbor where
  toLinearEquiv := hyperbolicToFirstNeighborEquiv
  map_app' u v := by
    have hform : indefiniteUnitPlaneFirstNeighbor.form = indefiniteUnitPlane.form :=
      isNeighbor_indefiniteUnitPlaneFirstNeighbor.form_eq.symm
    rw [hform, indefiniteUnitPlane_form_apply, hyperbolicPlane_form_apply]
    simp only [hyperbolicToFirstNeighborEquiv, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  map_carrier := by
    ext x
    rw [Submodule.mem_map_equiv]
    have h := hyperbolicToFirstNeighborEquiv_mem_iff (hyperbolicToFirstNeighborEquiv.symm x)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

/-- `hyperbolicPlaneIsometryIndefiniteUnitPlaneFirstNeighbor` sends `u` to
`![u 0 / 2 + u 1, u 0 / 2 - u 1]`. -/
@[simp]
theorem hyperbolicPlaneIsometryIndefiniteUnitPlaneFirstNeighbor_apply (u : Fin 2 → ℚ) :
    hyperbolicPlaneIsometryIndefiniteUnitPlaneFirstNeighbor u =
      ![u 0 / 2 + u 1, u 0 / 2 - u 1] :=
  (rfl)

private def hyperbolicToSecondNeighborEquiv : (Fin 2 → ℚ) ≃ₗ[ℚ] (Fin 2 → ℚ) where
  toFun u := ![u 0 / 2 + u 1, -u 0 / 2 + u 1]
  invFun x := ![x 0 - x 1, (x 0 + x 1) / 2]
  map_add' u v := by
    rw [funext_iff, Fin.forall_fin_two]
    exact ⟨by simp; ring, by simp; ring⟩
  map_smul' c u := by
    rw [funext_iff, Fin.forall_fin_two]
    exact ⟨by simp; ring, by simp; ring⟩
  left_inv u := by
    rw [funext_iff, Fin.forall_fin_two]
    exact ⟨by simp; ring, by simp; ring⟩
  right_inv x := by
    rw [funext_iff, Fin.forall_fin_two]
    exact ⟨by simp; ring, by simp; ring⟩

@[simp]
private theorem hyperbolicToSecondNeighborEquiv_apply (u : Fin 2 → ℚ) :
    hyperbolicToSecondNeighborEquiv u = ![u 0 / 2 + u 1, -u 0 / 2 + u 1] :=
  rfl

private theorem hyperbolicToSecondNeighborEquiv_mem_iff (u : Fin 2 → ℚ) :
    hyperbolicToSecondNeighborEquiv u ∈ indefiniteUnitPlaneSecondNeighbor.carrier ↔
      u ∈ hyperbolicPlane.carrier := by
  rw [indefiniteUnitPlaneSecondNeighbor,
    indefiniteUnitPlane.mem_shiftedHalfCharacteristicOverlattice_carrier_iff,
    mem_evenSublattice_indefiniteUnitPlane_carrier_iff,
    mem_evenSublattice_indefiniteUnitPlane_carrier_iff,
    mem_hyperbolicPlane_carrier_iff]
  simp only [Fin.forall_fin_two]
  constructor
  · rintro (⟨⟨⟨z₀, hz₀⟩, ⟨z₁, hz₁⟩⟩, k, hk⟩ | ⟨⟨⟨z₀, hz₀⟩, ⟨z₁, hz₁⟩⟩, k, hk⟩)
    · simp only [hyperbolicToSecondNeighborEquiv_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one] at hz₀ hz₁ hk
      exact ⟨⟨z₀ - z₁, by push_cast; linarith⟩, ⟨k, by linarith⟩⟩
    · simp only [hyperbolicToSecondNeighborEquiv_apply, coe_indefiniteUnitPlaneOddVector,
        coe_indefiniteUnitPlaneCharacteristicVector, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul] at hz₀ hz₁ hk
      exact ⟨⟨z₀ - z₁ + 1, by push_cast; linarith⟩, ⟨k + 1, by push_cast; linarith⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    rcases Int.even_or_odd a with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      simp only [hyperbolicToSecondNeighborEquiv_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        ← ha, ← hb]
      exact ⟨⟨⟨m + b, by push_cast; ring⟩, ⟨-m + b, by push_cast; ring⟩⟩, b, by ring⟩
    · right
      simp only [hyperbolicToSecondNeighborEquiv_apply, coe_indefiniteUnitPlaneOddVector,
        coe_indefiniteUnitPlaneCharacteristicVector, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul, ← ha, ← hb]
      exact ⟨⟨⟨m + b - 1, by push_cast; ring⟩, ⟨-m + b - 1, by push_cast; ring⟩⟩,
        b - 1, by push_cast; ring⟩

/-- Explicit isometry from `hyperbolicPlane` onto `indefiniteUnitPlaneSecondNeighbor`, sending the
hyperbolic basis vectors `![1, 0], ![0, 1]` to `![1 / 2, -1 / 2], ![1, 1]`. -/
noncomputable def hyperbolicPlaneIsometryIndefiniteUnitPlaneSecondNeighbor :
    Isometry hyperbolicPlane indefiniteUnitPlaneSecondNeighbor where
  toLinearEquiv := hyperbolicToSecondNeighborEquiv
  map_app' u v := by
    have hform : indefiniteUnitPlaneSecondNeighbor.form = indefiniteUnitPlane.form :=
      isNeighbor_indefiniteUnitPlaneSecondNeighbor.form_eq.symm
    rw [hform, indefiniteUnitPlane_form_apply, hyperbolicPlane_form_apply]
    simp only [hyperbolicToSecondNeighborEquiv, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  map_carrier := by
    ext x
    rw [Submodule.mem_map_equiv]
    have h := hyperbolicToSecondNeighborEquiv_mem_iff (hyperbolicToSecondNeighborEquiv.symm x)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

/-- `hyperbolicPlaneIsometryIndefiniteUnitPlaneSecondNeighbor` sends `u` to
`![u 0 / 2 + u 1, -u 0 / 2 + u 1]`. -/
@[simp]
theorem hyperbolicPlaneIsometryIndefiniteUnitPlaneSecondNeighbor_apply (u : Fin 2 → ℚ) :
    hyperbolicPlaneIsometryIndefiniteUnitPlaneSecondNeighbor u =
      ![u 0 / 2 + u 1, -u 0 / 2 + u 1] :=
  (rfl)

/-! ## Orthogonal sums with an even lattice and Kneser neighbors -/

section OrthogonalSum

universe u v

variable {V : Type u} {W : Type v} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

private theorem orthogonalSum_transport_prodComm (A : IntegralLattice V) (B : IntegralLattice W) :
    (B.orthogonalSum A).transport (LinearEquiv.prodComm ℚ W V) = A.orthogonalSum B := by
  refine IntegralLattice.ext (Submodule.ext fun x ↦ ?_) (LinearMap.BilinForm.ext fun x y ↦ ?_)
  · rw [transport_carrier, Submodule.mem_map_equiv]
    simp [orthogonalSum_carrier, Submodule.mem_prod, and_comm]
  · simp [transport_form, orthogonalSum_form, LinearMap.BilinForm.prod_apply, add_comm]

/-- `evenSublattice` commutes with transporting an integral lattice along a linear equivalence. -/
@[simp]
theorem evenSublattice_transport (L : IntegralLattice V) (e : V ≃ₗ[ℚ] W) :
    (L.transport e).evenSublattice = L.evenSublattice.transport e := by
  refine IntegralLattice.ext (Submodule.ext fun y ↦ ?_)
    (by rw [evenSublattice_form, transport_form, transport_form, evenSublattice_form])
  rw [transport_carrier, Submodule.mem_map_equiv, LinearEquiv.restrictScalars_symm_apply]
  refine ⟨fun hy ↦ ?_, fun hy ↦ ?_⟩
  · have hyT : y ∈ (L.transport e).carrier := (L.transport e).evenSublattice_carrier_le hy
    have hxL : e.symm y ∈ L.carrier := by rwa [transport_carrier, Submodule.mem_map_equiv] at hyT
    rw [L.mem_evenSublattice_carrier_iff ⟨e.symm y, hxL⟩, L.even_integralNorm_iff]
    simpa [norm_apply, transport_form] using
      ((L.transport e).even_integralNorm_iff ⟨y, hyT⟩).mp
        (((L.transport e).mem_evenSublattice_carrier_iff ⟨y, hyT⟩).mp hy)
  · have hyT : y ∈ (L.transport e).carrier := by
      rw [transport_carrier, Submodule.mem_map_equiv]
      exact L.evenSublattice_carrier_le hy
    rw [(L.transport e).mem_evenSublattice_carrier_iff ⟨y, hyT⟩,
      (L.transport e).even_integralNorm_iff]
    simpa [norm_apply, transport_form] using
      (L.even_integralNorm_iff ⟨e.symm y, L.evenSublattice_carrier_le hy⟩).mp
        ((L.mem_evenSublattice_carrier_iff _).mp hy)

/-- **Orthogonal sum with an even lattice commutes with `evenSublattice`.** No nondegeneracy or
unimodularity hypothesis on either summand is needed. -/
theorem evenSublattice_orthogonalSum_of_isEven_left {Y : IntegralLattice V} (hY : Y.IsEven)
    (M : IntegralLattice W) :
    (Y.orthogonalSum M).evenSublattice = Y.orthogonalSum M.evenSublattice := by
  refine IntegralLattice.ext (Submodule.ext fun p ↦ ?_)
    (by rw [evenSublattice_form, orthogonalSum_form, orthogonalSum_form, evenSublattice_form])
  constructor
  · intro hp
    have hpYM : p ∈ (Y.orthogonalSum M).carrier := (Y.orthogonalSum M).evenSublattice_carrier_le hp
    have hp_prod : p.1 ∈ Y.carrier ∧ p.2 ∈ M.carrier := by
      rwa [orthogonalSum_carrier, Submodule.mem_prod] at hpYM
    rw [orthogonalSum_carrier, Submodule.mem_prod]
    refine ⟨hp_prod.1, (M.mem_evenSublattice_carrier_iff ⟨p.2, hp_prod.2⟩).mpr ?_⟩
    rw [M.even_integralNorm_iff]
    obtain ⟨k, hk⟩ := ((Y.orthogonalSum M).even_integralNorm_iff ⟨p, hpYM⟩).mp
      (((Y.orthogonalSum M).mem_evenSublattice_carrier_iff ⟨p, hpYM⟩).mp hp)
    obtain ⟨m, hm⟩ := Y.isEven_iff_forall_norm.mp hY ⟨p.1, hp_prod.1⟩
    rw [norm_apply, orthogonalSum_form, LinearMap.BilinForm.prod_apply, ← Y.norm_apply,
      ← M.norm_apply, hm] at hk
    exact ⟨k - m, by push_cast; linarith⟩
  · intro hp
    rw [orthogonalSum_carrier, Submodule.mem_prod] at hp
    have hpYM : p ∈ (Y.orthogonalSum M).carrier := by
      rw [orthogonalSum_carrier, Submodule.mem_prod]
      exact ⟨hp.1, M.evenSublattice_carrier_le hp.2⟩
    rw [(Y.orthogonalSum M).mem_evenSublattice_carrier_iff ⟨p, hpYM⟩,
      (Y.orthogonalSum M).even_integralNorm_iff]
    obtain ⟨m, hm⟩ := Y.isEven_iff_forall_norm.mp hY ⟨p.1, hp.1⟩
    obtain ⟨k, hk⟩ := (M.even_integralNorm_iff ⟨p.2, M.evenSublattice_carrier_le hp.2⟩).mp
      ((M.mem_evenSublattice_carrier_iff _).mp hp.2)
    refine ⟨m + k, ?_⟩
    rw [norm_apply, orthogonalSum_form, LinearMap.BilinForm.prod_apply, ← Y.norm_apply,
      ← M.norm_apply, hm, hk]
    push_cast
    ring

/-- Right-hand companion to `evenSublattice_orthogonalSum_of_isEven_left`. -/
theorem evenSublattice_orthogonalSum_of_isEven_right (M : IntegralLattice V)
    {Y : IntegralLattice W} (hY : Y.IsEven) :
    (M.orthogonalSum Y).evenSublattice = M.evenSublattice.orthogonalSum Y := by
  rw [← orthogonalSum_transport_prodComm M Y, evenSublattice_transport,
    evenSublattice_orthogonalSum_of_isEven_left hY M, orthogonalSum_transport_prodComm]

/-- **Kneser `p`-neighbors are preserved by left orthogonal direct sums.** -/
theorem IsNeighbor.orthogonalSum_left (Y : IntegralLattice V) {M N : IntegralLattice W} {p : ℕ}
    (h : M.IsNeighbor N p) :
    (Y.orthogonalSum M).IsNeighbor (Y.orthogonalSum N) p := by
  have hrel (B : Submodule ℤ W) :
      (Y.carrier.prod (M.carrier ⊓ N.carrier)).toAddSubgroup.relIndex
          (Y.carrier.prod B).toAddSubgroup =
        (M.carrier ⊓ N.carrier).toAddSubgroup.relIndex B.toAddSubgroup := by
    let proj : (Y.carrier.prod B).toAddSubgroup →+ B.toAddSubgroup :=
      { toFun := fun q ↦ ⟨q.1.2, q.2.2⟩
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
    have hsurj : Function.Surjective proj := fun b ↦
      ⟨⟨(0, b.1), ⟨Y.carrier.zero_mem, b.2⟩⟩, rfl⟩
    have hcomap : ((M.carrier ⊓ N.carrier).toAddSubgroup.addSubgroupOf B.toAddSubgroup).comap proj =
        (Y.carrier.prod (M.carrier ⊓ N.carrier)).toAddSubgroup.addSubgroupOf
          (Y.carrier.prod B).toAddSubgroup := by
      ext q
      exact ⟨fun hq ↦ ⟨q.2.1, hq⟩, fun hq ↦ hq.2⟩
    rw [AddSubgroup.relIndex, ← hcomap, AddSubgroup.index_comap_of_surjective _ hsurj,
      ← AddSubgroup.relIndex]
  have hinf : (Y.orthogonalSum M).carrier ⊓ (Y.orthogonalSum N).carrier =
      Y.carrier.prod (M.carrier ⊓ N.carrier) := by
    ext x
    simp only [Submodule.mem_inf, orthogonalSum_carrier, Submodule.mem_prod]
    exact ⟨fun ⟨⟨h1, h2⟩, ⟨_, h3⟩⟩ ↦ ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ ↦ ⟨⟨h1, h2⟩, ⟨h1, h3⟩⟩⟩
  refine ⟨by rw [orthogonalSum_form, orthogonalSum_form, h.form_eq], ?_, ?_⟩
  · rw [hinf, orthogonalSum_carrier, hrel]
    exact h.relIndex_inf_left
  · rw [hinf, orthogonalSum_carrier, hrel]
    exact h.relIndex_inf_right

/-- **Kneser `p`-neighbors are preserved by right orthogonal direct sums.** -/
theorem IsNeighbor.orthogonalSum_right {M N : IntegralLattice V} {p : ℕ}
    (h : M.IsNeighbor N p) (Y : IntegralLattice W) :
    (M.orthogonalSum Y).IsNeighbor (N.orthogonalSum Y) p := by
  have hswap := (h.orthogonalSum_left Y).transport (LinearEquiv.prodComm ℚ W V)
  rwa [orthogonalSum_transport_prodComm, orthogonalSum_transport_prodComm] at hswap

/-- **For any even lattice `Y`, `Y ⊕ hyperbolicPlane` is isometric to an explicit even Kneser
two-neighbor of `Y ⊕ indefiniteUnitPlane`.** When `Y` is unimodular, so is the neighbor. -/
theorem exists_isNeighbor_orthogonalSum_indefiniteUnitPlane {Y : IntegralLattice V}
    (hY : Y.IsEven) :
    ∃ K : IntegralLattice (V × (Fin 2 → ℚ)),
      (Y.orthogonalSum indefiniteUnitPlane).IsNeighbor K 2 ∧
        K.IsEven ∧ Nonempty (Isometry (Y.orthogonalSum hyperbolicPlane) K) :=
  ⟨Y.orthogonalSum indefiniteUnitPlaneFirstNeighbor,
    isNeighbor_indefiniteUnitPlaneFirstNeighbor.orthogonalSum_left Y,
    (isEven_orthogonalSum_iff Y indefiniteUnitPlaneFirstNeighbor).mpr
      ⟨hY, isEven_indefiniteUnitPlaneFirstNeighbor⟩,
    ⟨(Isometry.refl Y).orthogonalSum hyperbolicPlaneIsometryIndefiniteUnitPlaneFirstNeighbor⟩⟩

end OrthogonalSum

end TauCeti.IntegralLattice
