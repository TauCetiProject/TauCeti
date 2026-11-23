/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import TauCeti.Analysis.Matrix.Cartan.Realify
public import TauCeti.Analysis.Matrix.L2OpNorm
public import TauCeti.Analysis.Matrix.SymplecticGroup.Maslov
public import TauCeti.Analysis.Matrix.UnitaryGroup.Torus
public import TauCeti.Analysis.Normed.Algebra.Exponential

/-!
# Polar coordinates on `Sp(2, ℝ)`: an open disc times a circle

A real symplectic `2 × 2` matrix `A` factors as `A = P U`, with `P = √(A Aᵀ)` positive definite
and symplectic and `U` orthogonal and symplectic, that is, a rotation. This file writes both
factors in explicit coordinates, for `Sp(2, ℝ) = TauCeti.GLSymplectic ι ℝ` with a one-element
index type `ι`.

* **The positive factor.** The symmetric matrices in the symplectic Lie algebra `𝔰𝔭(2, ℝ)` are
  exactly the matrices `[[a, b], [b, -a]]` (`TauCeti.GLSymplectic.spSymmMatrix`,
  `TauCeti.GLSymplectic.eq_spSymmMatrix`), so `P = exp [[a, b], [b, -a]]` for a unique
  `(a, b) ∈ ℝ²`. The point `(a, b)` is recorded through the disc coordinate
  `(a, b) / √(1 + a² + b²)` of the open unit disc, whose inverse is `v / √(1 - ‖v‖²)`. This is
  Mathlib's `Homeomorph.unitBall`; it is a diffeomorphism of the open disc onto the plane
  (`TauCeti.unitBallDiffeomorph`).
* **The orthogonal factor.** The rotation `U` is the realification of a `1 × 1` unitary matrix
  `(z)`, `|z| = 1`, which has the entries `Re z, -Im z; Im z, Re z`
  (`Matrix.realify_apply_inl_inl` and its siblings). The point `z` of the circle is the
  determinant of `(z)` (`Matrix.UnitaryGroup.detCircleEquivOfUnique`), so it is the value
  `ρ(A)` of the map `TauCeti.GLSymplectic.maslovPhase` whose winding along a loop of symplectic
  matrices is its Maslov index (`TauCeti.GLSymplectic.polarDiscHomeomorph_apply_snd`).

Together, `A ↦ ((a, b) / √(1 + a² + b²), z)` is a homeomorphism from `Sp(2, ℝ)` onto the product
of the open unit disc and the circle (`TauCeti.GLSymplectic.polarDiscHomeomorph`), with inverse
`(v, z) ↦ exp [[a, b], [b, -a]] * realify (z)`, `(a, b) = v / √(1 - ‖v‖²)`
(`TauCeti.GLSymplectic.val_polarDiscHomeomorph_symm_apply`). It is the case `n = 1` of the
Cartan decomposition `TauCeti.GLSymplectic.leftCartanHomeomorph` in the factor order `A = P U`.

The parametrization `((a, b), z) ↦ exp [[a, b], [b, -a]] * realify (z)` is smooth on the plane
times the complex numbers (`TauCeti.GLSymplectic.contDiff_exp_spSymmMatrix_mul_realify`). Since
the circle coordinate is `ρ(A)`, the Maslov index of a loop in `Sp(2, ℝ)` is the winding number of
its circle coordinate (`TauCeti.GLSymplectic.maslovIndex_eq_degree_polarDiscHomeomorph_snd`).

## Main definitions

* `TauCeti.GLSymplectic.spSymmMatrix`: the matrix `[[a, b], [b, -a]]`, with scalar blocks.
* `TauCeti.GLSymplectic.spSymmHomeomorph`: the coordinates `(a, b)` on the symmetric elements of
  `𝔰𝔭(2, ℝ)`.
* `TauCeti.GLSymplectic.polarDiscHomeomorph`: the homeomorphism
  `Sp(2, ℝ) ≃ₜ ball (0 : ℝ²) 1 × Circle`.

## Main results

* `TauCeti.GLSymplectic.polarDiscHomeomorph_apply_snd`: the circle coordinate is `ρ(A)`.
* `TauCeti.GLSymplectic.coe_polarDiscHomeomorph_apply_fst`: the disc coordinate is
  `(a, b) / √(1 + a² + b²)`, with `[[a, b], [b, -a]] = log √(A Aᵀ)`.
* `TauCeti.GLSymplectic.val_polarDiscHomeomorph_symm_apply`: the inverse map.
* `TauCeti.GLSymplectic.sqrt_mul_star_eq_exp_spSymmMatrix` and
  `TauCeti.GLSymplectic.coe_polarUnitary_eq_realify_diagonal_maslovPhase`: the two polar factors
  of `A` in these coordinates.
* `TauCeti.GLSymplectic.contDiff_exp_spSymmMatrix_mul_realify`: the inverse map, extended to the
  plane times the complex numbers, is smooth.
* `TauCeti.GLSymplectic.maslovIndex_eq_degree_polarDiscHomeomorph_snd`: the Maslov index of a loop
  is the winding number of its circle coordinate.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  Graduate Texts in Mathematics 27, Oxford University Press, 2017, Section 2.2 (the polar
  decomposition of symplectic matrices and the map `ρ`).
-/

public section

noncomputable section

open Matrix Metric
open scoped MatrixOrder

namespace TauCeti.GLSymplectic

variable {ι : Type*} [DecidableEq ι]

/-! ### Symmetric elements of `𝔰𝔭(2, ℝ)` -/

variable (ι) in
/-- The matrix `[[a, b], [b, -a]]`, with scalar `ι × ι` blocks. For a one-element index type every
symmetric element of the symplectic Lie algebra `𝔰𝔭(2, ℝ)` has this form
(`TauCeti.GLSymplectic.eq_spSymmMatrix`). -/
def spSymmMatrix (a b : ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  fromBlocks (diagonal fun _ ↦ a) (diagonal fun _ ↦ b) (diagonal fun _ ↦ b) (diagonal fun _ ↦ -a)

/-- `TauCeti.GLSymplectic.spSymmMatrix` in block form. -/
theorem spSymmMatrix_def (a b : ℝ) :
    spSymmMatrix ι a b =
      fromBlocks (diagonal fun _ ↦ a) (diagonal fun _ ↦ b) (diagonal fun _ ↦ b)
        (diagonal fun _ ↦ -a) :=
  (rfl)

@[simp]
theorem spSymmMatrix_apply_inl_inl (a b : ℝ) (i j : ι) :
    spSymmMatrix ι a b (.inl i) (.inl j) = if i = j then a else 0 := by
  simp [spSymmMatrix_def, diagonal_apply]

@[simp]
theorem spSymmMatrix_apply_inl_inr (a b : ℝ) (i j : ι) :
    spSymmMatrix ι a b (.inl i) (.inr j) = if i = j then b else 0 := by
  simp [spSymmMatrix_def, diagonal_apply]

@[simp]
theorem spSymmMatrix_apply_inr_inl (a b : ℝ) (i j : ι) :
    spSymmMatrix ι a b (.inr i) (.inl j) = if i = j then b else 0 := by
  simp [spSymmMatrix_def, diagonal_apply]

@[simp]
theorem spSymmMatrix_apply_inr_inr (a b : ℝ) (i j : ι) :
    spSymmMatrix ι a b (.inr i) (.inr j) = if i = j then -a else 0 := by
  simp [spSymmMatrix_def, diagonal_apply]

variable (ι) in
@[simp]
theorem spSymmMatrix_zero : spSymmMatrix ι 0 0 = 0 := by
  ext (i | i) (j | j) <;> simp

theorem isSelfAdjoint_spSymmMatrix (a b : ℝ) : IsSelfAdjoint (spSymmMatrix ι a b) := by
  ext (i | i) (j | j) <;> simp [eq_comm]

theorem continuous_spSymmMatrix : Continuous fun p : ℝ × ℝ ↦ spSymmMatrix ι p.1 p.2 := by
  simp only [spSymmMatrix_def]
  fun_prop

variable [Fintype ι]

theorem spSymmMatrix_mem_sp (a b : ℝ) : spSymmMatrix ι a b ∈ LieAlgebra.Symplectic.sp ι ℝ := by
  rw [mem_symplecticLieAlgebra_iff]
  refine ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i j ↦ ?_⟩ <;>
    by_cases h : i = j <;> simp [h, eq_comm]

variable [Unique ι]

/-- **The symmetric elements of `𝔰𝔭(2, ℝ)`**: a symmetric `2 × 2` matrix in the symplectic Lie
algebra is `[[a, b], [b, -a]]`. -/
theorem eq_spSymmMatrix {X : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ} (hX : IsSelfAdjoint X)
    (hXsp : X ∈ LieAlgebra.Symplectic.sp ι ℝ) :
    X = spSymmMatrix ι (X (.inl default) (.inl default)) (X (.inl default) (.inr default)) := by
  obtain ⟨-, -, h⟩ := (mem_symplecticLieAlgebra_iff X).1 hXsp
  have hs : ∀ i j, X j i = X i j := fun i j ↦ by
    simpa using congrFun (congrFun hX i) j
  ext (i | i) (j | j) <;> simp [Subsingleton.elim i default,
    Subsingleton.elim j default, h, hs (.inl default) (.inr default)]

variable (ι) in
/-- The coordinates `(a, b)` of the symmetric elements `[[a, b], [b, -a]]` of the symplectic Lie
algebra `𝔰𝔭(2, ℝ)`, a homeomorphism onto the Euclidean plane. -/
def spSymmHomeomorph : {X : selfAdjoint (Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) //
      (X : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) ∈ LieAlgebra.Symplectic.sp ι ℝ} ≃ₜ
    EuclideanSpace ℝ (Fin 2) where
  toFun X := !₂[(X : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (.inl default) (.inl default),
    (X : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (.inl default) (.inr default)]
  invFun v := ⟨⟨spSymmMatrix ι (v 0) (v 1), isSelfAdjoint_spSymmMatrix _ _⟩,
    spSymmMatrix_mem_sp _ _⟩
  left_inv X := Subtype.ext (Subtype.ext (eq_spSymmMatrix X.val.property X.property).symm)
  right_inv v := by
    ext i
    fin_cases i <;> simp
  continuous_toFun := (PiLp.continuous_toLp 2 _).comp <| continuous_pi fun i ↦ by
    fin_cases i <;> exact (continuous_subtypeVal.comp continuous_subtypeVal).matrix_elem _ _
  continuous_invFun := (((continuous_spSymmMatrix (ι := ι)).comp
    (f := fun v : EuclideanSpace ℝ (Fin 2) ↦ (v 0, v 1)) (((continuous_apply 0).comp
    (PiLp.continuous_ofLp 2 _)).prodMk ((continuous_apply 1).comp
      (PiLp.continuous_ofLp 2 _)))).subtype_mk _).subtype_mk _

@[simp]
theorem spSymmHomeomorph_apply (X : {X : selfAdjoint (Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) //
      (X : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) ∈ LieAlgebra.Symplectic.sp ι ℝ}) :
    spSymmHomeomorph ι X = !₂[(X : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (.inl default) (.inl default),
      (X : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (.inl default) (.inr default)] :=
  (rfl)

@[simp]
theorem coe_spSymmHomeomorph_symm_apply (v : EuclideanSpace ℝ (Fin 2)) :
    (((spSymmHomeomorph ι).symm v : selfAdjoint (Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)) :
      Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) = spSymmMatrix ι (v 0) (v 1) :=
  (rfl)

/-! ### Polar coordinates -/

variable (ι) in
/-- **Polar coordinates on `Sp(2, ℝ)`**: writing `A = P U` with `P = exp [[a, b], [b, -a]]` and
`U = realify (z)` the rotation by a point `z` of the circle, the map
`A ↦ ((a, b) / √(1 + a² + b²), z)` is a homeomorphism from `Sp(2, ℝ)` onto the product of the open
unit disc and the circle. The circle coordinate is `ρ(A)`
(`TauCeti.GLSymplectic.polarDiscHomeomorph_apply_snd`). -/
def polarDiscHomeomorph : GLSymplectic ι ℝ ≃ₜ ball (0 : EuclideanSpace ℝ (Fin 2)) 1 × Circle :=
  (leftCartanHomeomorph ι).symm.trans
    (((spSymmHomeomorph ι).trans Homeomorph.unitBall).prodCongr
      (UnitaryGroup.detCircleEquivOfUnique ι).toHomeomorph)

/-- The circle coordinate of `A ∈ Sp(2, ℝ)` is `ρ(A)`, the map
`TauCeti.GLSymplectic.maslovPhase` that defines the Maslov index. -/
@[simp]
theorem polarDiscHomeomorph_apply_snd (A : GLSymplectic ι ℝ) :
    (polarDiscHomeomorph ι A).2 = maslovPhase A := by
  rw [← maslovPhase_inclusion_polarUnitary, maslovPhase_inclusion,
    ← unitaryGroupEquivSymplecticInfOrthogonal_leftCartanHomeomorph_symm_apply_snd,
    ContinuousMulEquiv.symm_apply_apply]
  exact UnitaryGroup.detCircleEquivOfUnique_apply _

/-- The disc coordinate of `A ∈ Sp(2, ℝ)` is `x / √(1 + ‖x‖²)`, where `x = (a, b)` are the
entries of the logarithm `[[a, b], [b, -a]]` of the positive polar factor `√(A Aᵀ)`. -/
theorem coe_polarDiscHomeomorph_apply_fst (A : GLSymplectic ι ℝ) :
    ((polarDiscHomeomorph ι A).1 : EuclideanSpace ℝ (Fin 2)) =
      let L := cfc Real.log (CFC.sqrt (((A : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) *
        star ((A : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)))
      let x : EuclideanSpace ℝ (Fin 2) := !₂[L (.inl default) (.inl default),
        L (.inl default) (.inr default)]
      (√(1 + ‖x‖ ^ 2))⁻¹ • x := by
  rw [← coe_leftCartanHomeomorph_symm_apply_fst]
  simp [polarDiscHomeomorph, Homeomorph.unitBall_apply_coe,
    OpenPartialHomeomorph.univUnitBall_apply]

/-- The inverse of the polar coordinates on `Sp(2, ℝ)` sends `(v, z)` to
`exp [[a, b], [b, -a]] * realify (z)`, where `(a, b) = v / √(1 - ‖v‖²)`. -/
theorem val_polarDiscHomeomorph_symm_apply (p : ball (0 : EuclideanSpace ℝ (Fin 2)) 1 × Circle) :
    (((polarDiscHomeomorph ι).symm p : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) =
      let y : EuclideanSpace ℝ (Fin 2) := (√(1 - ‖(p.1 : EuclideanSpace ℝ (Fin 2))‖ ^ 2))⁻¹ •
        (p.1 : EuclideanSpace ℝ (Fin 2))
      NormedSpace.exp (spSymmMatrix ι (y 0) (y 1)) *
        (diagonal fun _ : ι ↦ (p.2 : ℂ)).realify := by
  -- `simp` cannot use these lemmas: `Homeomorph.unitBall` types the ball as `ball 0 1`, not as
  -- `univUnitBall.target`, so they only match up to unfolding.
  have hy : (Homeomorph.unitBall.symm p.1 : EuclideanSpace ℝ (Fin 2)) =
      (√(1 - ‖(p.1 : EuclideanSpace ℝ (Fin 2))‖ ^ 2))⁻¹ • (p.1 : EuclideanSpace ℝ (Fin 2)) :=
    (OpenPartialHomeomorph.toHomeomorphSourceTarget_symm_apply_coe
      OpenPartialHomeomorph.univUnitBall p.1).trans
      (OpenPartialHomeomorph.univUnitBall_symm_apply _)
  simp [polarDiscHomeomorph, ContinuousMulEquiv.toHomeomorph_eq_coe, hy]

/-- The identity has disc coordinate `0` and circle coordinate `1`. -/
@[simp]
theorem polarDiscHomeomorph_one :
    polarDiscHomeomorph ι 1 = (⟨0, mem_ball_self one_pos⟩, 1) := by
  rw [← Homeomorph.eq_symm_apply]
  refine Subtype.ext (Units.ext ?_)
  simp [val_polarDiscHomeomorph_symm_apply]

/-- The two polar factors of `A ∈ Sp(2, ℝ)` in polar coordinates. -/
private theorem polar_eq_polarDiscHomeomorph (A : GLSymplectic ι ℝ) :
    CFC.sqrt (((A : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) *
        star ((A : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)) =
      (let v : EuclideanSpace ℝ (Fin 2) := (polarDiscHomeomorph ι A).1
      let y : EuclideanSpace ℝ (Fin 2) := (√(1 - ‖v‖ ^ 2))⁻¹ • v
      NormedSpace.exp (spSymmMatrix ι (y 0) (y 1))) ∧
    ((A : GL (ι ⊕ ι) ℝ).polarUnitary : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) =
      (diagonal fun _ : ι ↦ ((polarDiscHomeomorph ι A).2 : ℂ)).realify := by
  have h := val_polarDiscHomeomorph_symm_apply (ι := ι) (polarDiscHomeomorph ι A)
  rw [Homeomorph.symm_apply_apply,
    ← UnitaryGroup.coe_detCircleEquivOfUnique_symm_apply (n := ι)] at h
  rw [← UnitaryGroup.coe_detCircleEquivOfUnique_symm_apply (n := ι)]
  exact GeneralLinearGroup.sqrt_mul_star_eq_exp_and_polarUnitary_eq_realify
    (isSelfAdjoint_spSymmMatrix _ _) _ h

/-- **The positive polar factor in polar coordinates**: `√(A Aᵀ) = exp [[a, b], [b, -a]]`, where
`(a, b) = v / √(1 - ‖v‖²)` for the disc coordinate `v` of `A`. -/
theorem sqrt_mul_star_eq_exp_spSymmMatrix (A : GLSymplectic ι ℝ) :
    CFC.sqrt (((A : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) *
        star ((A : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)) =
      let v : EuclideanSpace ℝ (Fin 2) := (polarDiscHomeomorph ι A).1
      let y : EuclideanSpace ℝ (Fin 2) := (√(1 - ‖v‖ ^ 2))⁻¹ • v
      NormedSpace.exp (spSymmMatrix ι (y 0) (y 1)) :=
  (polar_eq_polarDiscHomeomorph A).1

/-- **The orthogonal polar factor in polar coordinates**: the orthogonal polar factor of
`A ∈ Sp(2, ℝ)` is the rotation `realify (ρ(A))`, with entries `Re ρ(A), -Im ρ(A); Im ρ(A), Re ρ(A)`.
-/
theorem coe_polarUnitary_eq_realify_diagonal_maslovPhase (A : GLSymplectic ι ℝ) :
    ((A : GL (ι ⊕ ι) ℝ).polarUnitary : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) =
      (diagonal fun _ : ι ↦ (maslovPhase A : ℂ)).realify := by
  rw [← polarDiscHomeomorph_apply_snd]
  exact (polar_eq_polarDiscHomeomorph A).2

/-! ### Smoothness and the Maslov index -/

section Smooth

open scoped ContDiff Matrix.Norms.L2Operator

attribute [local instance] Matrix.l2OpNormedAlgebraReal

omit [Unique ι] in
/-- **The polar parametrization is smooth.** The map `((a, b), z) ↦ exp [[a, b], [b, -a]] *
realify (z)` from the plane and the complex numbers to the `2 × 2` real matrices is smooth. On the
unit circle in the second factor, read through the diffeomorphism `TauCeti.unitBallDiffeomorph` of
the open disc onto the plane, it is the inverse of `TauCeti.GLSymplectic.polarDiscHomeomorph`
(`TauCeti.GLSymplectic.val_polarDiscHomeomorph_symm_apply`). -/
theorem contDiff_exp_spSymmMatrix_mul_realify {k : ℕ∞ω} :
    ContDiff ℝ k fun p : EuclideanSpace ℝ (Fin 2) × ℂ ↦
      NormedSpace.exp (spSymmMatrix ι (p.1 0) (p.1 1)) * (diagonal fun _ : ι ↦ p.2).realify := by
  have hS (a b : ℝ) : spSymmMatrix ι a b =
      a • (fromBlocks 1 0 0 (-1) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) + b • fromBlocks 0 1 1 0 := by
    ext (i | i) (j | j) <;> by_cases h : i = j <;> simp [h]
  simp only [hS, ← smul_one_eq_diagonal, realify_smul_one, RCLike.re_to_complex,
    RCLike.im_to_complex]
  have hv : ContDiff ℝ k fun v : EuclideanSpace ℝ (Fin 2) ↦
      v 0 • (fromBlocks 1 0 0 (-1) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) + v 1 • fromBlocks 0 1 1 0 := by
    have h₀ : ContDiff ℝ k fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0 := contDiff_piLp_apply 2
    have h₁ : ContDiff ℝ k fun v : EuclideanSpace ℝ (Fin 2) ↦ v 1 := contDiff_piLp_apply 2
    exact (h₀.smul contDiff_const).add (h₁.smul contDiff_const)
  have hz : ContDiff ℝ k fun z : ℂ ↦ z.re • (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) + z.im • J ι ℝ :=
    (Complex.reCLM.contDiff.smul contDiff_const).add (Complex.imCLM.contDiff.smul contDiff_const)
  exact ((NormedSpace.contDiff_exp ℝ).comp (hv.comp contDiff_fst)).mul (hz.comp contDiff_snd)

end Smooth

/-- **The Maslov index is the winding number of the circle coordinate.** For a loop `γ` in
`Sp(2, ℝ)`, the Maslov index is the degree of the loop traced by the circle coordinate of `γ` in
the polar coordinates `TauCeti.GLSymplectic.polarDiscHomeomorph`. -/
theorem maslovIndex_eq_degree_polarDiscHomeomorph_snd {A : GLSymplectic ι ℝ} (γ : Path A A) :
    maslovIndex γ =
      Circle.degree (γ.map (continuous_snd.comp (polarDiscHomeomorph ι).continuous)) := by
  rw [maslovIndex_def]
  exact Circle.degree_congr _ _ fun t ↦ (polarDiscHomeomorph_apply_snd (γ t)).symm

end TauCeti.GLSymplectic
