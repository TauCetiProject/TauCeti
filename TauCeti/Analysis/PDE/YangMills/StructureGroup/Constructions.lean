/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.YangMills.StructureGroup.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import TauCeti.Analysis.Matrix.Frobenius
import TauCeti.Geometry.Lie.Subgroup.SpecialUnitary

/-!
# Canonical compact matrix structure groups and restriction

This file equips any closed subgroup `H ≤ Matrix.unitaryGroup n ℂ` with the canonical
`Ad(H)`-invariant trace inner product `⟨X, Y⟩ = -Re tr(X Y)` and constructs the standard
structure groups `U(n)`, `SU(n)`, and restriction to a closed subgroup. It also shows that every
finite subgroup of `U(n)` has trivial Lie algebra. Functorial reindexing and block-diagonal
products live in `TauCeti.Analysis.PDE.YangMills.StructureGroup.Product`.

## Main definitions

* `TauCeti.YangMills.traceBilinForm`: the real bilinear form `(X, Y) ↦ -Re tr(X Y)` on
  `unitaryLieSubalgebra H`.
* `TauCeti.YangMills.StructureGroup.ofClosedSubgroup`: equips a closed unitary subgroup with the
  canonical trace inner product `⟨X, Y⟩ = -Re tr(X Y)`.
* `TauCeti.YangMills.StructureGroup.unitary`: the unitary group `U(n)` with the trace inner
  product.
* `TauCeti.YangMills.specialUnitarySubgroup`: `SU(n)` as a subgroup of `Matrix.unitaryGroup n ℂ`.
* `TauCeti.YangMills.StructureGroup.specialUnitary`: the special unitary group `SU(n)` with the
  trace inner product and Lie algebra `𝔰𝔲(n) = {X : Xᴴ = -X ∧ tr X = 0}`.
* `TauCeti.YangMills.StructureGroup.restrict`: restricts a structure group to a closed subgroup,
  inheriting the `Ad`-invariant inner product isometrically.
* `TauCeti.YangMills.StructureGroup.restrictLieIncl`: the isometric Lie-algebra inclusion
  `(G.restrict H hHG hH).LieAlgebra →ₗᵢ[ℝ] G.LieAlgebra`.

## Main results

* `TauCeti.YangMills.trace_mul_im_eq_zero_of_skewHermitian`: for skew-Hermitian matrices `X, Y`,
  `tr(X Y)` is real, so `-tr(X Y) = ⟨X, Y⟩`.
* `TauCeti.YangMills.StructureGroup.mem_lieSubalgebra_unitary_iff` and
  `TauCeti.YangMills.StructureGroup.mem_lieSubalgebra_specialUnitary_iff`: explicit descriptions
  of `𝔲(n)` and `𝔰𝔲(n)`.
* `TauCeti.YangMills.unitaryLieSubalgebra_eq_bot_of_finite`: every finite subgroup of `U(n)` has
  trivial Lie algebra `⊥`.

## References

* S.-J. Oh and D. Tataru, *The Yang–Mills heat flow and the caloric gauge*, Astérisque 436 (2022),
  §1.1.
* S.-J. Oh and D. Tataru, *The hyperbolic Yang–Mills equation for connections in an arbitrary
  topological class*, Comm. Math. Phys. 365 (2019), §1.1.
-/

public section

open NormedSpace Set
open scoped ComplexConjugate InnerProductSpace Matrix

noncomputable section

namespace TauCeti.YangMills

universe u

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### Canonical trace bilinear form, `U(n)`, and `SU(n)` -/

section SkewTrace

variable {n : Type u} [Fintype n]

/-- For skew-Hermitian complex matrices `X, Y`, the complex trace `tr(X * Y)` is real. -/
theorem trace_mul_im_eq_zero_of_skewHermitian {X Y : Matrix n n ℂ}
    (hX : Xᴴ = -X) (hY : Yᴴ = -Y) : ((X * Y).trace).im = 0 := by
  have hconj : star (X * Y).trace = (X * Y).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hX, hY, neg_mul_neg,
      Matrix.trace_mul_comm]
  have him := congrArg Complex.im hconj
  simp only [Complex.star_def, Complex.conj_im] at him
  linarith

end SkewTrace

section TraceForm

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The canonical real bilinear form `(X, Y) ↦ -Re tr(X * Y)` on the Lie algebra of any
unitary subgroup `H ≤ U(n)`. -/
def traceBilinForm (H : Subgroup (Matrix.unitaryGroup n ℂ)) :
    LinearMap.BilinForm ℝ (unitaryLieSubalgebra H) :=
  LinearMap.mk₂ ℝ (fun X Y ↦ -((X.1 * Y.1).trace).re)
    (fun X Y Z ↦ by
      change -(((X.1 + Y.1) * Z.1).trace).re = _
      rw [add_mul, Matrix.trace_add, Complex.add_re, neg_add])
    (fun r X Y ↦ by
      change -(((r • X.1) * Y.1).trace).re = _
      rw [Algebra.smul_mul_assoc, Matrix.trace_smul]
      simp [Complex.real_smul])
    (fun X Y Z ↦ by
      change -((X.1 * (Y.1 + Z.1)).trace).re = _
      rw [mul_add, Matrix.trace_add, Complex.add_re, neg_add])
    (fun r X Y ↦ by
      change -((X.1 * (r • Y.1)).trace).re = _
      rw [Algebra.mul_smul_comm, Matrix.trace_smul]
      simp [Complex.real_smul])

@[simp]
theorem traceBilinForm_apply (H : Subgroup (Matrix.unitaryGroup n ℂ))
    (X Y : unitaryLieSubalgebra H) :
    traceBilinForm H X Y = -((X.1 * Y.1).trace).re :=
  (rfl)

/-- On skew-Hermitian matrices, `-Re tr(X * Y)` equals `Re tr(X * Yᴴ)`. -/
theorem traceBilinForm_eq_re_trace_mul_conjTranspose (H : Subgroup (Matrix.unitaryGroup n ℂ))
    (X Y : unitaryLieSubalgebra H) :
    traceBilinForm H X Y = ((X.1 * Y.1ᴴ).trace).re := by
  rw [traceBilinForm_apply, conjTranspose_eq_neg_of_mem_unitaryLieSubalgebra Y.2,
    Matrix.mul_neg, Matrix.trace_neg, Complex.neg_re]

/-- On skew-Hermitian matrices, the quadratic form of `traceBilinForm` is the squared Frobenius
norm `∑ i, ∑ j, ‖X i j‖ ^ 2`. -/
theorem traceBilinForm_self_eq_sum_norm_sq (H : Subgroup (Matrix.unitaryGroup n ℂ))
    (X : unitaryLieSubalgebra H) :
    traceBilinForm H X X = ∑ i : n, ∑ j : n, ‖X.1 i j‖ ^ 2 := by
  rw [traceBilinForm_eq_re_trace_mul_conjTranspose]
  simpa only [RCLike.re_to_complex] using Matrix.re_trace_mul_conjTranspose_self X.1

theorem traceBilinForm_isSymm (H : Subgroup (Matrix.unitaryGroup n ℂ)) :
    (traceBilinForm H).IsSymm :=
  LinearMap.BilinForm.isSymm_def.2 fun X Y ↦ by
    rw [traceBilinForm_apply, traceBilinForm_apply, Matrix.trace_mul_comm]

theorem traceBilinForm_pos (H : Subgroup (Matrix.unitaryGroup n ℂ))
    (X : unitaryLieSubalgebra H) (hX : X ≠ 0) :
    0 < traceBilinForm H X X := by
  rw [traceBilinForm_self_eq_sum_norm_sq]
  have hne : ∃ i j : n, X.1 i j ≠ 0 := by
    by_contra h
    push Not at h
    apply hX
    apply Subtype.ext
    ext i j
    exact h i j
  obtain ⟨i₀, j₀, hij⟩ := hne
  refine Finset.sum_pos' (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg _)
    ⟨i₀, Finset.mem_univ _, ?_⟩
  exact Finset.sum_pos' (fun j _ ↦ sq_nonneg _)
    ⟨j₀, Finset.mem_univ _, sq_pos_of_pos (norm_pos_iff.2 hij)⟩

theorem traceBilinForm_conj (H : Subgroup (Matrix.unitaryGroup n ℂ))
    (g : H) (X Y : unitaryLieSubalgebra H) :
    traceBilinForm H
      ⟨(g.1 : Matrix n n ℂ) * X.1 * (g.1 : Matrix n n ℂ)ᴴ,
        conj_mem_unitaryLieSubalgebra g.2 X.2⟩
      ⟨(g.1 : Matrix n n ℂ) * Y.1 * (g.1 : Matrix n n ℂ)ᴴ,
        conj_mem_unitaryLieSubalgebra g.2 Y.2⟩ =
    traceBilinForm H X Y := by
  have h1 : (g.1 : Matrix n n ℂ)ᴴ * (g.1 : Matrix n n ℂ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.1 g.1.2
  rw [traceBilinForm_apply, traceBilinForm_apply]
  congr 2
  calc (((g.1 : Matrix n n ℂ) * X.1 * (g.1 : Matrix n n ℂ)ᴴ) *
        ((g.1 : Matrix n n ℂ) * Y.1 * (g.1 : Matrix n n ℂ)ᴴ)).trace
      = ((g.1 : Matrix n n ℂ) * X.1 * ((g.1 : Matrix n n ℂ)ᴴ * (g.1 : Matrix n n ℂ)) *
        Y.1 * (g.1 : Matrix n n ℂ)ᴴ).trace := by simp [mul_assoc]
    _ = (((g.1 : Matrix n n ℂ) * (X.1 * Y.1)) * (g.1 : Matrix n n ℂ)ᴴ).trace := by
        rw [h1, mul_one]; simp [mul_assoc]
    _ = ((g.1 : Matrix n n ℂ)ᴴ * ((g.1 : Matrix n n ℂ) * (X.1 * Y.1))).trace :=
        Matrix.trace_mul_comm _ _
    _ = (X.1 * Y.1).trace := by rw [← mul_assoc, h1, one_mul]

namespace StructureGroup

/-- Equip any closed subgroup `H ≤ Matrix.unitaryGroup n ℂ` with the canonical `Ad(H)`-invariant
trace inner product `⟨X, Y⟩ = -Re tr(X * Y)`. -/
def ofClosedSubgroup (H : Subgroup (Matrix.unitaryGroup n ℂ))
    (hH : IsClosed (H : Set (Matrix.unitaryGroup n ℂ))) : StructureGroup n where
  subgroup := H
  isClosed := hH
  bilinForm := traceBilinForm H
  bilinForm_symm := traceBilinForm_isSymm H
  bilinForm_pos := traceBilinForm_pos H
  bilinForm_conj := traceBilinForm_conj H

@[simp]
theorem ofClosedSubgroup_subgroup (H : Subgroup (Matrix.unitaryGroup n ℂ))
    (hH : IsClosed (H : Set (Matrix.unitaryGroup n ℂ))) :
    (ofClosedSubgroup H hH).subgroup = H :=
  (rfl)

@[simp]
theorem ofClosedSubgroup_inner {H : Subgroup (Matrix.unitaryGroup n ℂ)}
    {hH : IsClosed (H : Set (Matrix.unitaryGroup n ℂ))}
    (X Y : (ofClosedSubgroup H hH).LieAlgebra) :
    ⟪X, Y⟫_ℝ = -((X.val * Y.val).trace).re := by
  rw [LieAlgebra.inner_eq_bilinForm]
  rfl

theorem ofClosedSubgroup_norm_sq {H : Subgroup (Matrix.unitaryGroup n ℂ)}
    {hH : IsClosed (H : Set (Matrix.unitaryGroup n ℂ))}
    (X : (ofClosedSubgroup H hH).LieAlgebra) :
    ‖X‖ ^ 2 = ∑ i : n, ∑ j : n, ‖X.val i j‖ ^ 2 := by
  rw [LieAlgebra.norm_sq_eq_bilinForm]
  exact traceBilinForm_self_eq_sum_norm_sq H X.toSubalgebra

/-- For the trace inner product, `-tr(X * Y)` is already real and coincides with `⟪X, Y⟫_ℝ` as a
complex number. -/
theorem ofClosedSubgroup_neg_trace_mul {H : Subgroup (Matrix.unitaryGroup n ℂ)}
    {hH : IsClosed (H : Set (Matrix.unitaryGroup n ℂ))}
    (X Y : (ofClosedSubgroup H hH).LieAlgebra) :
    -(X.val * Y.val).trace = (⟪X, Y⟫_ℝ : ℂ) := by
  apply Complex.ext
  · rw [ofClosedSubgroup_inner]
    simp
  · simp [trace_mul_im_eq_zero_of_skewHermitian X.conjTranspose_val Y.conjTranspose_val]

/-- The full unitary group `U(n)` as a compact matrix structure group with its canonical trace
inner product `⟨X, Y⟩ = -Re tr(X * Y)`. -/
def unitary (n : Type u) [Fintype n] [DecidableEq n] : StructureGroup n :=
  ofClosedSubgroup ⊤ isClosed_univ

@[simp]
theorem unitary_subgroup (n : Type u) [Fintype n] [DecidableEq n] :
    (unitary n).subgroup = ⊤ :=
  (rfl)

theorem mem_lieSubalgebra_unitary_iff (X : Matrix n n ℂ) :
    X ∈ (unitary n).lieSubalgebra ↔ Xᴴ = -X :=
  mem_unitaryLieSubalgebra_top_iff X

@[simp]
theorem unitary_inner (X Y : (unitary n).LieAlgebra) :
    ⟪X, Y⟫_ℝ = -((X.val * Y.val).trace).re :=
  ofClosedSubgroup_inner X Y

theorem unitary_norm_sq (X : (unitary n).LieAlgebra) :
    ‖X‖ ^ 2 = ∑ i : n, ∑ j : n, ‖X.val i j‖ ^ 2 :=
  ofClosedSubgroup_norm_sq X

theorem unitary_neg_trace_mul (X Y : (unitary n).LieAlgebra) :
    -(X.val * Y.val).trace = (⟪X, Y⟫_ℝ : ℂ) :=
  ofClosedSubgroup_neg_trace_mul X Y

end StructureGroup

/-- The special unitary group `SU(n)` viewed as a subgroup of `Matrix.unitaryGroup n ℂ`. -/
def specialUnitarySubgroup (n : Type u) [Fintype n] [DecidableEq n] :
    Subgroup (Matrix.unitaryGroup n ℂ) where
  carrier := {U | (U : Matrix n n ℂ).det = 1}
  mul_mem' {A B} hA hB := by
    change ((A : Matrix n n ℂ) * (B : Matrix n n ℂ)).det = 1
    rw [Matrix.det_mul, hA, hB, mul_one]
  one_mem' := Matrix.det_one
  inv_mem' {A} hA := by
    have hmul : (A : Matrix n n ℂ) * ((A⁻¹ : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ) = 1 := by
      have h := mul_inv_cancel A
      simpa only [Submonoid.coe_mul, OneMemClass.coe_one] using congrArg Subtype.val h
    have hdet := congrArg Matrix.det hmul
    rw [Matrix.det_mul, hA, one_mul, Matrix.det_one] at hdet
    exact hdet

@[simp]
theorem mem_specialUnitarySubgroup_iff {U : Matrix.unitaryGroup n ℂ} :
    U ∈ specialUnitarySubgroup n ↔ (U : Matrix n n ℂ).det = 1 :=
  Iff.rfl

theorem isClosed_specialUnitarySubgroup (n : Type u) [Fintype n] [DecidableEq n] :
    IsClosed (specialUnitarySubgroup n : Set (Matrix.unitaryGroup n ℂ)) :=
  isClosed_singleton.preimage (Continuous.matrix_det continuous_subtype_val)

theorem toGLSubgroup_specialUnitarySubgroup (n : Type u) [Fintype n] [DecidableEq n] :
    toGLSubgroup (specialUnitarySubgroup n) = TauCeti.GLSpecialUnitary n ℂ := by
  ext g
  simp only [mem_toGLSubgroup_iff, mem_specialUnitarySubgroup_iff,
    TauCeti.GLSpecialUnitary.mem_iff_mem_specialUnitaryGroup, Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u.2, hu⟩
  · rintro ⟨hU, hdet⟩
    exact ⟨⟨(g : Matrix n n ℂ), hU⟩, hdet, Units.ext rfl⟩

namespace StructureGroup

/-- The special unitary group `SU(n)` as a compact matrix structure group with its canonical trace
inner product `⟨X, Y⟩ = -Re tr(X * Y)`. -/
def specialUnitary (n : Type u) [Fintype n] [DecidableEq n] : StructureGroup n :=
  ofClosedSubgroup (specialUnitarySubgroup n) (isClosed_specialUnitarySubgroup n)

@[simp]
theorem specialUnitary_subgroup (n : Type u) [Fintype n] [DecidableEq n] :
    (specialUnitary n).subgroup = specialUnitarySubgroup n :=
  (rfl)

open TauCeti.Lie in
open scoped Matrix.Norms.Operator in
/-- The Lie algebra of `SU(n)` consists of the trace-free skew-Hermitian matrices. -/
theorem mem_lieSubalgebra_specialUnitary_iff (X : Matrix n n ℂ) :
    X ∈ (specialUnitary n).lieSubalgebra ↔ Xᴴ = -X ∧ X.trace = 0 := by
  rw [lieSubalgebra, specialUnitary_subgroup, unitaryLieSubalgebra_eq_unitsLieSubalgebra,
    toGLSubgroup_specialUnitarySubgroup, mem_unitsLieSubalgebra_iff]
  exact unitsLieAlgebraLieEquiv_symm_mem_GLSpecialUnitary_lieSubalgebra_iff X

@[simp]
theorem specialUnitary_inner (X Y : (specialUnitary n).LieAlgebra) :
    ⟪X, Y⟫_ℝ = -((X.val * Y.val).trace).re :=
  ofClosedSubgroup_inner X Y

theorem specialUnitary_norm_sq (X : (specialUnitary n).LieAlgebra) :
    ‖X‖ ^ 2 = ∑ i : n, ∑ j : n, ‖X.val i j‖ ^ 2 :=
  ofClosedSubgroup_norm_sq X

theorem specialUnitary_neg_trace_mul (X Y : (specialUnitary n).LieAlgebra) :
    -(X.val * Y.val).trace = (⟪X, Y⟫_ℝ : ℂ) :=
  ofClosedSubgroup_neg_trace_mul X Y

end StructureGroup

end TraceForm

/-! ### Restriction to a closed subgroup -/

namespace StructureGroup

section Restrict

variable {n : Type u} [Fintype n] [DecidableEq n]

private def lieSubalgebraInclusion {H K : Subgroup (Matrix.unitaryGroup n ℂ)} (hHK : H ≤ K) :
    unitaryLieSubalgebra H →ₗ[ℝ] unitaryLieSubalgebra K where
  toFun X := ⟨X.1, unitaryLieSubalgebra_mono hHK X.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restrict a structure group `G` to a closed subgroup `H ≤ G.subgroup`, keeping the induced
`Ad(H)`-invariant inner product on `unitaryLieSubalgebra H ≤ G.lieSubalgebra`. -/
def restrict (G : StructureGroup n) (H : Subgroup (Matrix.unitaryGroup n ℂ))
    (hHG : H ≤ G.subgroup) (hH : IsClosed (H : Set (Matrix.unitaryGroup n ℂ))) :
    StructureGroup n where
  subgroup := H
  isClosed := hH
  bilinForm := G.bilinForm.comp (lieSubalgebraInclusion hHG) (lieSubalgebraInclusion hHG)
  bilinForm_symm := LinearMap.BilinForm.isSymm_def.2 fun X Y ↦ by
    simp only [LinearMap.BilinForm.comp_apply]
    exact G.bilinForm_symm.eq _ _
  bilinForm_pos X hX := by
    rw [LinearMap.BilinForm.comp_apply]
    apply G.bilinForm_pos
    intro h
    exact hX (Subtype.ext (congrArg (Subtype.val : G.lieSubalgebra → Matrix n n ℂ) h))
  bilinForm_conj g X Y := by
    simp only [LinearMap.BilinForm.comp_apply]
    exact G.bilinForm_conj ⟨g.1, hHG g.2⟩ (lieSubalgebraInclusion hHG X)
      (lieSubalgebraInclusion hHG Y)

@[simp]
theorem restrict_subgroup (G : StructureGroup n) (H : Subgroup (Matrix.unitaryGroup n ℂ))
    (hHG : H ≤ G.subgroup) (hH : IsClosed (H : Set (Matrix.unitaryGroup n ℂ))) :
    (G.restrict H hHG hH).subgroup = H :=
  (rfl)

/-- The canonical isometric Lie-algebra inclusion `(G.restrict H hHG hH).LieAlgebra →ₗᵢ[ℝ]
G.LieAlgebra`. -/
def restrictLieIncl (G : StructureGroup n) {H : Subgroup (Matrix.unitaryGroup n ℂ)}
    (hHG : H ≤ G.subgroup) (hH : IsClosed (H : Set (Matrix.unitaryGroup n ℂ))) :
    (G.restrict H hHG hH).LieAlgebra →ₗᵢ[ℝ] G.LieAlgebra where
  toFun X := ⟨X.val, unitaryLieSubalgebra_mono hHG X.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' X := by
    let Y : G.LieAlgebra := ⟨X.val, unitaryLieSubalgebra_mono hHG X.property⟩
    change ‖Y‖ = ‖X‖
    have hsq : ‖Y‖ ^ 2 = ‖X‖ ^ 2 := by
      rw [LieAlgebra.norm_sq_eq_bilinForm, LieAlgebra.norm_sq_eq_bilinForm]
      rfl
    nlinarith [norm_nonneg X, norm_nonneg Y]

@[simp]
theorem restrictLieIncl_val (G : StructureGroup n) {H : Subgroup (Matrix.unitaryGroup n ℂ)}
    (hHG : H ≤ G.subgroup) (hH : IsClosed (H : Set (Matrix.unitaryGroup n ℂ)))
    (X : (G.restrict H hHG hH).LieAlgebra) :
    (G.restrictLieIncl hHG hH X).val = X.val :=
  (rfl)

@[simp]
theorem restrictLieIncl_lie (G : StructureGroup n) {H : Subgroup (Matrix.unitaryGroup n ℂ)}
    (hHG : H ≤ G.subgroup) (hH : IsClosed (H : Set (Matrix.unitaryGroup n ℂ)))
    (X Y : (G.restrict H hHG hH).LieAlgebra) :
    G.restrictLieIncl hHG hH ⁅X, Y⁆ =
      ⁅G.restrictLieIncl hHG hH X, G.restrictLieIncl hHG hH Y⁆ :=
  (rfl)

theorem restrict_inner (G : StructureGroup n) {H : Subgroup (Matrix.unitaryGroup n ℂ)}
    (hHG : H ≤ G.subgroup) (hH : IsClosed (H : Set (Matrix.unitaryGroup n ℂ)))
    (X Y : (G.restrict H hHG hH).LieAlgebra) :
    ⟪X, Y⟫_ℝ = ⟪G.restrictLieIncl hHG hH X, G.restrictLieIncl hHG hH Y⟫_ℝ := by
  rw [LieAlgebra.inner_eq_bilinForm, LieAlgebra.inner_eq_bilinForm]
  rfl

end Restrict

end StructureGroup

/-! ### Finite unitary subgroups have trivial Lie algebra -/

section FiniteSubgroup

variable {n : Type u} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.Operator in
private theorem eq_zero_of_exp_smul_eq_one_op {X : Matrix n n ℂ}
    (h : ∀ t : ℝ, NormedSpace.exp (t • X) = 1) : X = 0 := by
  let _ : NormedAlgebra ℚ (Matrix n n ℂ) := TauCeti.normedAlgebraRatOfReal
  have hderiv := hasDerivAt_exp_smul_const X (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at hderiv
  refine hderiv.unique ?_
  exact (hasDerivAt_const (0 : ℝ) (1 : Matrix n n ℂ)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall h)

open scoped Matrix.Norms.Operator in
private theorem continuous_exp_smul_op (X : Matrix n n ℂ) :
    Continuous (fun t : ℝ ↦ NormedSpace.exp (t • X)) := by
  let _ : NormedAlgebra ℚ (Matrix n n ℂ) := TauCeti.normedAlgebraRatOfReal
  exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)

/-- Every finite subgroup of `Matrix.unitaryGroup n ℂ` has trivial Lie algebra `⊥`. -/
theorem unitaryLieSubalgebra_eq_bot_of_finite {H : Subgroup (Matrix.unitaryGroup n ℂ)}
    (hH : (H : Set (Matrix.unitaryGroup n ℂ)).Finite) :
    unitaryLieSubalgebra H = ⊥ := by
  rw [eq_bot_iff]
  intro X hX
  rw [LieSubalgebra.mem_bot]
  have hS : (Subtype.val '' (H : Set (Matrix.unitaryGroup n ℂ))).Finite := hH.image _
  have hmem : ∀ t : ℝ, NormedSpace.exp (t • X) ∈
      Subtype.val '' (H : Set (Matrix.unitaryGroup n ℂ)) :=
    (mem_unitaryLieSubalgebra_iff hH.isClosed X).1 hX
  let f : ℝ → Matrix n n ℂ := fun t ↦ NormedSpace.exp (t • X)
  have hf : Continuous f := continuous_exp_smul_op X
  let U : Set ℝ := f ⁻¹' {(1 : Matrix n n ℂ)}
  let V : Set ℝ := f ⁻¹' ((Subtype.val '' (H : Set (Matrix.unitaryGroup n ℂ))) \ {1})
  have hU_closed : IsClosed U := isClosed_singleton.preimage hf
  have hV_closed : IsClosed V := (hS.subset Set.sdiff_subset).isClosed.preimage hf
  have hcov : (Set.univ : Set ℝ) ⊆ U ∪ V := by
    intro t _
    by_cases h1 : f t = 1
    · exact Or.inl h1
    · exact Or.inr ⟨hmem t, h1⟩
  have hdisj : Disjoint U V := Set.disjoint_left.2 fun t htU htV ↦ htV.2 htU
  have hU_open : IsOpen U := by
    have : U = Vᶜ := Set.Subset.antisymm (hdisj.subset_compl_right) fun t ht ↦
      (hcov (Set.mem_univ t)).resolve_right ht
    rw [this]
    exact hV_closed.isOpen_compl
  have hV_open : IsOpen V := by
    have : V = Uᶜ := Set.Subset.antisymm (hdisj.symm.subset_compl_right) fun t ht ↦
      (hcov (Set.mem_univ t)).resolve_left ht
    rw [this]
    exact hU_closed.isOpen_compl
  have h0 : (0 : ℝ) ∈ U := by
    change NormedSpace.exp ((0 : ℝ) • X) = 1
    simp
  have hsub : (Set.univ : Set ℝ) ⊆ U :=
    isPreconnected_univ.subset_left_of_subset_union hU_open hV_open hdisj hcov ⟨0, trivial, h0⟩
  exact eq_zero_of_exp_smul_eq_one_op fun t ↦ hsub (Set.mem_univ t)

namespace StructureGroup

/-- A structure group with finite underlying subgroup has trivial Lie algebra `⊥`. -/
theorem lieSubalgebra_eq_bot_of_finite (G : StructureGroup n)
    (hG : (G.subgroup : Set (Matrix.unitaryGroup n ℂ)).Finite) :
    G.lieSubalgebra = ⊥ :=
  unitaryLieSubalgebra_eq_bot_of_finite hG

/-- A structure group with finite underlying subgroup has subsingleton (zero-dimensional)
`G.LieAlgebra`. -/
theorem subsingleton_lieAlgebra_of_finite (G : StructureGroup n)
    (hG : (G.subgroup : Set (Matrix.unitaryGroup n ℂ)).Finite) :
    Subsingleton G.LieAlgebra := by
  refine ⟨fun X Y ↦ LieAlgebra.ext ?_⟩
  have hbot := G.lieSubalgebra_eq_bot_of_finite hG
  have hX : X.val = 0 := (LieSubalgebra.mem_bot _).1 (hbot ▸ X.property)
  have hY : Y.val = 0 := (LieSubalgebra.mem_bot _).1 (hbot ▸ Y.property)
  rw [hX, hY]

end StructureGroup

end FiniteSubgroup

end TauCeti.YangMills
