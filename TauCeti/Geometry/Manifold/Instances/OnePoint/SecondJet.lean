/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import TauCeti.Geometry.Manifold.Instances.OnePoint.FirstJet
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.ZPow
import TauCeti.Analysis.Calculus.Deriv.Second
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Second jets of Möbius transformations

Let `𝕜` be a proper nontrivially normed field, such as `ℂ`. Read a Möbius transformation `g` of
the projective line `OnePoint 𝕜` near `0` in the affine chart at `0` and in the preferred chart at
`g • 0`, the affine chart when `g • 0` is finite and the inverted chart `w = 1 / z` when
`g • 0 = ∞`. This local expression is Mathlib's
`writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) 0 (g • ·)`, a scalar function defined near `0`, and its value,
first derivative and second derivative at `0` are the **second jet** of `g` at `0`.

* **Second-jet coordinates.** When `2 ≠ 0` in `𝕜`, for every point `p`, every nonzero `v` and every
  `w`, exactly one element of `PGL(2, 𝕜)` sends `0` to `p` with first derivative `v` and second
  derivative `w` at `0` (`OnePoint.existsUnique_pgl_smul_zero_deriv_iteratedDeriv_eq`). So
  `g ↦ (g • 0, g'(0), g''(0))` identifies `PGL(2, 𝕜)` with `OnePoint 𝕜 × 𝕜ˣ × 𝕜`
  (`OnePoint.pglSecondJetEquiv`). This is the normalization of the reparametrizations of a
  genus-zero domain by the second jet at one marked point, complementing the normalization by
  three marked points (`OnePoint.existsUnique_pgl_smul_zero_one_infty_eq`) and by two marked points
  and a tangent direction (`OnePoint.existsUnique_pgl_smul_zero_infty_mfderiv_eq`). The derivative
  coordinate `g'(0)` is the first-jet coordinate `mfderiv (g • ·) 0 1` of
  `TauCeti.Geometry.Manifold.Instances.OnePoint.FirstJet`
  (`OnePoint.mfderiv_pgl_smul_zero_one_eq_deriv`).
* **The stabilizer of `0`.** Precomposing with an element `h` fixing `0` acts on second jets by the
  chain rule: `(g h)'(0) = g'(0) h'(0)` and `(g h)''(0) = g''(0) h'(0)² + g'(0) h''(0)`
  (`OnePoint.deriv_writtenInExtChartAt_pgl_mul_smul_zero`, in
  `TauCeti.Geometry.Manifold.Instances.OnePoint.FirstJet`, and
  `OnePoint.iteratedDeriv_two_writtenInExtChartAt_pgl_mul_smul_zero`). With `p = 0` the
  coordinates identify the stabilizer `𝕜 ⋊ 𝕜ˣ` of `0` with the second jets `(v, w)`, `v ≠ 0`, under
  this composition law.
* **Change of target chart.** When `g • 0 = p` is finite and nonzero, both charts at `p` apply.
  In the inverted chart the first and second derivatives at `0` become `-v / p²` and
  `2 v² / p³ - w / p²` (`OnePoint.deriv_invChart_pgl_smul_coe`, in
  `TauCeti.Geometry.Manifold.Instances.OnePoint.FirstJet`, and
  `OnePoint.iteratedDeriv_two_invChart_pgl_smul_coe`).

The computation behind all of this: for a representative `!![a, b; c, d]` of `g` with `d ≠ 0`, the
local expression is `z ↦ (a z + b) / (c z + d)` near `0`, with derivatives `(a d - b c) / d²` and
`-2 c (a d - b c) / d³` there; when `d = 0`, so that `g • 0 = ∞`, it is the reciprocal
`z ↦ (c z + d) / (a z + b)` read in the inverted chart. In characteristic two every second
derivative of a Möbius transformation vanishes at `0`, which is why `2 ≠ 0` is assumed for the
coordinates.

## Main definitions

* `OnePoint.pglSecondJetEquiv`: the second-jet coordinates `PGL(2, 𝕜) ≃ OnePoint 𝕜 × 𝕜ˣ × 𝕜`.

## Main results

* `OnePoint.existsUnique_pgl_smul_zero_deriv_iteratedDeriv_eq`: the second-jet coordinates of
  `PGL(2, 𝕜)`.
* `OnePoint.pglSecondJetEquiv_symm_smul_zero`,
  `OnePoint.deriv_writtenInExtChartAt_pglSecondJetEquiv_symm` and
  `OnePoint.iteratedDeriv_two_writtenInExtChartAt_pglSecondJetEquiv_symm`: the Möbius
  transformation with second jet `(p, v, w)` has value `p`, first derivative `v` and second
  derivative `w` at `0`.
* `OnePoint.iteratedDeriv_two_writtenInExtChartAt_pgl_mul_smul_zero`: the action of the stabilizer
  of `0` on second derivatives.
* `OnePoint.iteratedDeriv_two_invChart_pgl_smul_coe`: the change from the affine to the inverted
  chart at the target, for second derivatives.

The first-order results that the second-jet coordinates build on (the local expression at `0`, its
smoothness and nonzero derivative, and the first-order stabilizer and chart-change laws) are in
`TauCeti.Geometry.Manifold.Instances.OnePoint.FirstJet`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §§1–2.
* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, §§3.2 and 4.3.
-/

public section

open Filter Matrix MulAction Set Topology

open scoped Manifold MatrixGroups

namespace OnePoint

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [DecidableEq 𝕜] [ProperSpace 𝕜]

/-! ### The local expression of a representative at `0` -/

/-- For a representative `!![a, b; c, d]` with `d ≠ 0`, the local expression at `0` is
`z ↦ (a z + b) / (c z + d)` near `0`. -/
private theorem writtenInExtChartAt_pglMk_eventuallyEq_of_ne_zero (A : GL (Fin 2) 𝕜)
    (hA : A 1 1 ≠ 0) :
    writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜) (fun x ↦ ProjGenLinGroup.mk A • x)
      =ᶠ[𝓝 0] fun z ↦ (A 0 0 * z + A 0 1) / (A 1 0 * z + A 1 1) := by
  have hq : Continuous fun z : 𝕜 ↦ A 1 0 * z + A 1 1 := by fun_prop
  have h0 : ProjGenLinGroup.mk A • ((0 : 𝕜) : OnePoint 𝕜) = ((A 0 1 / A 1 1 : 𝕜) : OnePoint 𝕜) := by
    simp [smul_some_eq_ite, hA]
  filter_upwards [hq.continuousAt.eventually_ne (by simpa using hA)] with z hz
  rw [writtenInExtChartAt_pgl_smul_zero_apply, h0, chartAt_coe, pglMk_smul, smul_some_eq_ite,
    ite_eq_right_iff.2 fun h ↦ absurd h hz, affineChart_coe]

/-- For a representative `!![a, b; c, 0]`, which sends `0` to `∞`, the local expression at `0`,
read in the inverted chart at `∞`, is `z ↦ (c z + 0) / (a z + b)` near `0`. -/
private theorem writtenInExtChartAt_pglMk_eventuallyEq_of_eq_zero (A : GL (Fin 2) 𝕜)
    (hA : A 1 1 = 0) :
    writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜) (fun x ↦ ProjGenLinGroup.mk A • x)
      =ᶠ[𝓝 0] fun z ↦ (A 1 0 * z + A 1 1) / (A 0 0 * z + A 0 1) := by
  have h0 : ProjGenLinGroup.mk A • ((0 : 𝕜) : OnePoint 𝕜) = ∞ := by
    simp [smul_some_eq_ite, hA]
  filter_upwards with z
  rw [writtenInExtChartAt_pgl_smul_zero_apply, h0, chartAt_infty, pglMk_smul, smul_some_eq_ite]
  split_ifs with hd
  · rw [hd, zero_div, invChart_infty]
  · rw [invChart_coe, inv_div]

/-! ### Jets of a representative -/

/-- For a representative `!![a, b; c, d]` with `d ≠ 0`, the first derivative of the local
expression at `0` is `(a d - b c) / d ^ 2`. -/
private theorem deriv_writtenInExtChartAt_pglMk_of_ne_zero (A : GL (Fin 2) 𝕜) (hA : A 1 1 ≠ 0) :
    deriv (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜)
      (fun x ↦ ProjGenLinGroup.mk A • x)) 0 = (A 0 0 * A 1 1 - A 0 1 * A 1 0) / A 1 1 ^ 2 := by
  rw [(writtenInExtChartAt_pglMk_eventuallyEq_of_ne_zero A hA).deriv_eq,
    (TauCeti.hasDerivAt_linearFractional (by simpa using hA)).deriv, mul_zero, zero_add]

/-- For a representative `!![a, b; c, d]` with `d ≠ 0`, the second derivative of the local
expression at `0` is `-2 c (a d - b c) / d ^ 3`. -/
private theorem iteratedDeriv_two_writtenInExtChartAt_pglMk_of_ne_zero (A : GL (Fin 2) 𝕜)
    (hA : A 1 1 ≠ 0) :
    iteratedDeriv 2 (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜)
      (fun x ↦ ProjGenLinGroup.mk A • x)) 0 =
        -2 * A 1 0 * (A 0 0 * A 1 1 - A 0 1 * A 1 0) / A 1 1 ^ 3 := by
  rw [(writtenInExtChartAt_pglMk_eventuallyEq_of_ne_zero A hA).iteratedDeriv_eq, iteratedDeriv_succ,
    iteratedDeriv_one, TauCeti.deriv_deriv_linearFractional (by simpa using hA), mul_zero, zero_add]

/-- For a representative `!![a, b; c, 0]`, the first derivative of the local expression at `0`,
read in the inverted chart, is `c / b`. -/
private theorem deriv_writtenInExtChartAt_pglMk_of_eq_zero (A : GL (Fin 2) 𝕜) (hA : A 1 1 = 0) :
    deriv (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜)
      (fun x ↦ ProjGenLinGroup.mk A • x)) 0 = A 1 0 / A 0 1 := by
  have hb := GeneralLinearGroup.zero_one_ne_zero_of_one_one_eq_zero hA
  rw [(writtenInExtChartAt_pglMk_eventuallyEq_of_eq_zero A hA).deriv_eq,
    (TauCeti.hasDerivAt_linearFractional (by simpa using hb)).deriv, mul_zero, zero_add, hA]
  field_simp
  ring

/-- For a representative `!![a, b; c, 0]`, the second derivative of the local expression at `0`,
read in the inverted chart, is `-2 a c / b ^ 2`. -/
private theorem iteratedDeriv_two_writtenInExtChartAt_pglMk_of_eq_zero (A : GL (Fin 2) 𝕜)
    (hA : A 1 1 = 0) :
    iteratedDeriv 2 (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜)
      (fun x ↦ ProjGenLinGroup.mk A • x)) 0 = -2 * A 0 0 * A 1 0 / A 0 1 ^ 2 := by
  have hb := GeneralLinearGroup.zero_one_ne_zero_of_one_one_eq_zero hA
  rw [(writtenInExtChartAt_pglMk_eventuallyEq_of_eq_zero A hA).iteratedDeriv_eq, iteratedDeriv_succ,
    iteratedDeriv_one, TauCeti.deriv_deriv_linearFractional (by simpa using hb), mul_zero, zero_add,
    hA]
  field_simp
  ring

/-! ### Second-jet coordinates -/

section Coordinates

variable [NeZero (2 : 𝕜)]

/-- The representative `!![v - z w / (2 v), z; -w / (2 v), 1]`, whose class sends `0` to the finite
point `z` with second jet `(v, w)` there. -/
private def finiteSecondJetGL (z : 𝕜) {v : 𝕜} (hv : v ≠ 0) (w : 𝕜) : GL (Fin 2) 𝕜 :=
  GeneralLinearGroup.mkOfDetNeZero !![v + z * -(w / (2 * v)), z; -(w / (2 * v)), 1] (by
    rw [det_fin_two_of]
    convert hv using 1
    ring)

/-- The representative `!![-w / (2 v), 1; v, 0]`, whose class sends `0` to `∞` with second jet
`(v, w)` there, read in the inverted chart. -/
private def inftySecondJetGL {v : 𝕜} (hv : v ≠ 0) (w : 𝕜) : GL (Fin 2) 𝕜 :=
  GeneralLinearGroup.mkOfDetNeZero !![-(w / (2 * v)), 1; v, 0] (by
    rw [det_fin_two_of]
    simpa using hv)

/-- A Möbius transformation with second jet `(z, v, w)` at `0`, for a finite point `z`. -/
private theorem finiteSecondJetGL_spec (z : 𝕜) {v : 𝕜} (hv : v ≠ 0) (w : 𝕜) :
    ProjGenLinGroup.mk (finiteSecondJetGL z hv w) • ((0 : 𝕜) : OnePoint 𝕜) = z ∧
      deriv (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜)
        (fun x ↦ ProjGenLinGroup.mk (finiteSecondJetGL z hv w) • x)) 0 = v ∧
      iteratedDeriv 2 (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜)
        (fun x ↦ ProjGenLinGroup.mk (finiteSecondJetGL z hv w) • x)) 0 = w := by
  have h11 : finiteSecondJetGL z hv w 1 1 ≠ 0 := by simp [finiteSecondJetGL]
  refine ⟨?_, ?_, ?_⟩
  · simp [finiteSecondJetGL, smul_some_eq_ite]
  · rw [deriv_writtenInExtChartAt_pglMk_of_ne_zero _ h11]
    simp only [finiteSecondJetGL, GeneralLinearGroup.val_mkOfDetNeZero, of_apply, cons_val',
      cons_val_zero, cons_val_one, cons_val_fin_one, empty_val']
    ring
  · rw [iteratedDeriv_two_writtenInExtChartAt_pglMk_of_ne_zero _ h11]
    simp only [finiteSecondJetGL, GeneralLinearGroup.val_mkOfDetNeZero, of_apply, cons_val',
      cons_val_zero, cons_val_one, cons_val_fin_one, empty_val']
    field_simp
    ring

/-- A Möbius transformation with second jet `(∞, v, w)` at `0`. -/
private theorem inftySecondJetGL_spec {v : 𝕜} (hv : v ≠ 0) (w : 𝕜) :
    ProjGenLinGroup.mk (inftySecondJetGL hv w) • ((0 : 𝕜) : OnePoint 𝕜) = ∞ ∧
      deriv (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜)
        (fun x ↦ ProjGenLinGroup.mk (inftySecondJetGL hv w) • x)) 0 = v ∧
      iteratedDeriv 2 (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜)
        (fun x ↦ ProjGenLinGroup.mk (inftySecondJetGL hv w) • x)) 0 = w := by
  have h11 : inftySecondJetGL hv w 1 1 = 0 := by simp [inftySecondJetGL]
  refine ⟨?_, ?_, ?_⟩
  · simp [inftySecondJetGL, smul_some_eq_ite]
  · rw [deriv_writtenInExtChartAt_pglMk_of_eq_zero _ h11]
    simp [inftySecondJetGL]
  · rw [iteratedDeriv_two_writtenInExtChartAt_pglMk_of_eq_zero _ h11]
    simp only [inftySecondJetGL, GeneralLinearGroup.val_mkOfDetNeZero, of_apply, cons_val',
      cons_val_zero, cons_val_one, cons_val_fin_one, empty_val']
    field_simp

/-- A Möbius transformation is determined by its second jet at `0`. -/
private theorem pgl_eq_of_secondJet_eq {g h : PGL(2, 𝕜)}
    (h0 : g • ((0 : 𝕜) : OnePoint 𝕜) = h • ((0 : 𝕜) : OnePoint 𝕜))
    (h1 : deriv (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜) (fun x ↦ g • x)) 0 =
      deriv (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜) (fun x ↦ h • x)) 0)
    (h2 : iteratedDeriv 2 (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜)
        (fun x ↦ g • x)) 0 =
      iteratedDeriv 2 (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜)
        (fun x ↦ h • x)) 0) :
    g = h := by
  obtain ⟨A, rfl⟩ := ProjGenLinGroup.mk_surjective g
  obtain ⟨B, rfl⟩ := ProjGenLinGroup.mk_surjective h
  -- Representatives whose entries have the same ratios to a common nonzero entry are
  -- proportional, so they define the same element of `PGL(2, 𝕜)`.
  have key {k l : Fin 2} (hA : A k l ≠ 0) (hB : B k l ≠ 0)
      (hratio : ∀ i j, A i j / A k l = B i j / B k l) :
      ProjGenLinGroup.mk A = ProjGenLinGroup.mk B := by
    refine ProjGenLinGroup.mk_eq_mk_iff.2 ⟨Units.mk0 (B k l / A k l) (div_ne_zero hB hA),
      GeneralLinearGroup.ext fun i j ↦ ?_⟩
    have hij := hratio i j
    field_simp at hij
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, Units.val_mk0, scalar_apply,
      mul_diagonal]
    field_simp
    linear_combination hij
  have hdetA := A.det_ne_zero
  have hdetB := B.det_ne_zero
  rw [det_fin_two] at hdetA hdetB
  by_cases hA : A 1 1 = 0 <;> by_cases hB : B 1 1 = 0
  · -- Both send `0` to `∞`: compare the ratios to the entry `b`.
    have hbA := GeneralLinearGroup.zero_one_ne_zero_of_one_one_eq_zero hA
    have hbB := GeneralLinearGroup.zero_one_ne_zero_of_one_one_eq_zero hB
    have hcA : A 1 0 ≠ 0 := fun hc ↦ hdetA (by simp [hA, hc])
    rw [deriv_writtenInExtChartAt_pglMk_of_eq_zero _ hA,
      deriv_writtenInExtChartAt_pglMk_of_eq_zero _ hB] at h1
    rw [iteratedDeriv_two_writtenInExtChartAt_pglMk_of_eq_zero _ hA,
      iteratedDeriv_two_writtenInExtChartAt_pglMk_of_eq_zero _ hB] at h2
    have h2' : -2 * (A 0 0 / A 0 1) * (A 1 0 / A 0 1) =
        -2 * (B 0 0 / B 0 1) * (B 1 0 / B 0 1) := by
      convert h2 using 1 <;> field_simp
    rw [← h1] at h2'
    have h00 : A 0 0 / A 0 1 = B 0 0 / B 0 1 :=
      mul_left_cancel₀ (neg_ne_zero.2 two_ne_zero) (mul_right_cancel₀ (div_ne_zero hcA hbA) h2')
    refine key hbA hbB fun i j ↦ ?_
    fin_cases i <;> fin_cases j
    · exact h00
    · simp [hbA, hbB]
    · exact h1
    · simp [hA, hB]
  · simp [smul_some_eq_ite, hA, hB] at h0
  · simp [smul_some_eq_ite, hA, hB] at h0
  · -- Both send `0` to a finite point: compare the ratios to the entry `d`.
    rw [deriv_writtenInExtChartAt_pglMk_of_ne_zero _ hA,
      deriv_writtenInExtChartAt_pglMk_of_ne_zero _ hB] at h1
    rw [iteratedDeriv_two_writtenInExtChartAt_pglMk_of_ne_zero _ hA,
      iteratedDeriv_two_writtenInExtChartAt_pglMk_of_ne_zero _ hB] at h2
    have h01 : A 0 1 / A 1 1 = B 0 1 / B 1 1 := by
      simpa [smul_some_eq_ite, hA, hB] using h0
    have hv : (A 0 0 * A 1 1 - A 0 1 * A 1 0) / A 1 1 ^ 2 ≠ 0 :=
      div_ne_zero hdetA (pow_ne_zero 2 hA)
    have h2' : -2 * (A 1 0 / A 1 1) * ((A 0 0 * A 1 1 - A 0 1 * A 1 0) / A 1 1 ^ 2) =
        -2 * (B 1 0 / B 1 1) * ((B 0 0 * B 1 1 - B 0 1 * B 1 0) / B 1 1 ^ 2) := by
      convert h2 using 1 <;> field_simp
    rw [← h1] at h2'
    have h10 : A 1 0 / A 1 1 = B 1 0 / B 1 1 :=
      mul_left_cancel₀ (neg_ne_zero.2 two_ne_zero) (mul_right_cancel₀ hv h2')
    have h00 : A 0 0 / A 1 1 = B 0 0 / B 1 1 := by
      have hA' : A 0 0 / A 1 1 =
          (A 0 0 * A 1 1 - A 0 1 * A 1 0) / A 1 1 ^ 2 + A 0 1 / A 1 1 * (A 1 0 / A 1 1) := by
        field_simp
        ring
      have hB' : B 0 0 / B 1 1 =
          (B 0 0 * B 1 1 - B 0 1 * B 1 0) / B 1 1 ^ 2 + B 0 1 / B 1 1 * (B 1 0 / B 1 1) := by
        field_simp
        ring
      rw [hA', hB', h1, h01, h10]
    refine key hA hB fun i j ↦ ?_
    fin_cases i <;> fin_cases j
    · exact h00
    · exact h01
    · exact h10
    · simp [hA, hB]

/-- **Second-jet coordinates.** For a point `p` of the projective line, a nonzero `v` and any `w`,
exactly one Möbius transformation sends `0` to `p` with first derivative `v` and second derivative
`w` at `0`, read in the affine chart at `0` and the preferred chart at `p`. -/
theorem existsUnique_pgl_smul_zero_deriv_iteratedDeriv_eq (p : OnePoint 𝕜) {v : 𝕜} (hv : v ≠ 0)
    (w : 𝕜) :
    ∃! g : PGL(2, 𝕜), g • ((0 : 𝕜) : OnePoint 𝕜) = p ∧
      deriv (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜) (fun x ↦ g • x)) 0 = v ∧
      iteratedDeriv 2 (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜)
        (fun x ↦ g • x)) 0 = w := by
  have hex : ∃ g : PGL(2, 𝕜), g • ((0 : 𝕜) : OnePoint 𝕜) = p ∧
      deriv (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜) (fun x ↦ g • x)) 0 = v ∧
      iteratedDeriv 2 (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜)
        (fun x ↦ g • x)) 0 = w := by
    induction p using OnePoint.rec with
    | infty => exact ⟨_, inftySecondJetGL_spec hv w⟩
    | coe z => exact ⟨_, finiteSecondJetGL_spec z hv w⟩
  obtain ⟨g, hg⟩ := hex
  refine ⟨g, hg, fun h hh ↦ pgl_eq_of_secondJet_eq ?_ ?_ ?_⟩
  · rw [hh.1, hg.1]
  · rw [hh.2.1, hg.2.1]
  · rw [hh.2.2, hg.2.2]

/-- **The second-jet coordinates of `PGL(2, 𝕜)`**: a Möbius transformation `g` corresponds to the
image `g • 0`, the first derivative and the second derivative at `0` of its local expression, read
in the affine chart at `0` and the preferred chart at `g • 0`. -/
noncomputable def pglSecondJetEquiv : PGL(2, 𝕜) ≃ OnePoint 𝕜 × 𝕜ˣ × 𝕜 :=
  Equiv.ofBijective
    (fun g ↦ (g • ((0 : 𝕜) : OnePoint 𝕜),
      Units.mk0 _ (deriv_writtenInExtChartAt_pgl_smul_zero_ne_zero g),
      iteratedDeriv 2 (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜)
        (fun x ↦ g • x)) 0))
    ⟨fun g h hgh ↦ by
      simp only [Prod.mk.injEq, Units.ext_iff, Units.val_mk0] at hgh
      exact pgl_eq_of_secondJet_eq hgh.1 hgh.2.1 hgh.2.2,
    fun ⟨p, v, w⟩ ↦ by
      obtain ⟨g, hg0, hg1, hg2⟩ :=
        (existsUnique_pgl_smul_zero_deriv_iteratedDeriv_eq p v.ne_zero w).exists
      exact ⟨g, Prod.ext hg0 (Prod.ext (Units.ext hg1) hg2)⟩⟩

@[simp]
theorem pglSecondJetEquiv_apply (g : PGL(2, 𝕜)) :
    pglSecondJetEquiv g = (g • ((0 : 𝕜) : OnePoint 𝕜),
      Units.mk0 _ (deriv_writtenInExtChartAt_pgl_smul_zero_ne_zero g),
      iteratedDeriv 2 (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜)
        (fun x ↦ g • x)) 0) :=
  (rfl)

/-- The Möbius transformation with second jet `(p, v, w)` at `0` sends `0` to `p`. -/
@[simp]
theorem pglSecondJetEquiv_symm_smul_zero (p : OnePoint 𝕜) (v : 𝕜ˣ) (w : 𝕜) :
    pglSecondJetEquiv.symm (p, v, w) • ((0 : 𝕜) : OnePoint 𝕜) = p :=
  congrArg Prod.fst (pglSecondJetEquiv.apply_symm_apply (p, v, w))

/-- The Möbius transformation with second jet `(p, v, w)` at `0` has first derivative `v` at `0`. -/
theorem deriv_writtenInExtChartAt_pglSecondJetEquiv_symm (p : OnePoint 𝕜) (v : 𝕜ˣ) (w : 𝕜) :
    deriv (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜)
      (fun x ↦ pglSecondJetEquiv.symm (p, v, w) • x)) 0 = v :=
  congrArg (fun x ↦ (x.2.1 : 𝕜)) (pglSecondJetEquiv.apply_symm_apply (p, v, w))

/-- The Möbius transformation with second jet `(p, v, w)` at `0` has second derivative `w` at
`0`. -/
theorem iteratedDeriv_two_writtenInExtChartAt_pglSecondJetEquiv_symm (p : OnePoint 𝕜) (v : 𝕜ˣ)
    (w : 𝕜) :
    iteratedDeriv 2 (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜)
      (fun x ↦ pglSecondJetEquiv.symm (p, v, w) • x)) 0 = w :=
  congrArg (fun x ↦ x.2.2) (pglSecondJetEquiv.apply_symm_apply (p, v, w))

end Coordinates

/-! ### The action of the stabilizer of `0` -/

section Stabilizer

/-- **Second jets under the stabilizer of `0`**: precomposing with `h` fixing `0` transforms the
second derivative at `0` by the chain rule, `(g h)''(0) = g''(0) h'(0)² + g'(0) h''(0)`. -/
theorem iteratedDeriv_two_writtenInExtChartAt_pgl_mul_smul_zero (g : PGL(2, 𝕜)) {h : PGL(2, 𝕜)}
    (hh : h • ((0 : 𝕜) : OnePoint 𝕜) = ((0 : 𝕜) : OnePoint 𝕜)) :
    iteratedDeriv 2 (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜)
        (fun x ↦ (g * h) • x)) 0 =
      iteratedDeriv 2 (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜)
          (fun x ↦ g • x)) 0 *
          deriv (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜) (fun x ↦ h • x)) 0 ^ 2 +
        deriv (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜) (fun x ↦ g • x)) 0 *
          iteratedDeriv 2 (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜)
            (fun x ↦ h • x)) 0 := by
  have hg : ContDiffAt 𝕜 2
      (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜) (fun x ↦ g • x))
      (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜) (fun x ↦ h • x) 0) := by
    rw [writtenInExtChartAt_pgl_smul_zero_zero hh]
    exact contDiffAt_writtenInExtChartAt_pgl_smul_zero g
  rw [(writtenInExtChartAt_pgl_mul_eventuallyEq_comp g hh).iteratedDeriv_eq,
    iteratedDeriv_comp_two hg (contDiffAt_writtenInExtChartAt_pgl_smul_zero h),
    writtenInExtChartAt_pgl_smul_zero_zero hh]

end Stabilizer

/-! ### Changing the chart at the target -/

section TargetChart

/-- **Second jets in the inverted chart.** When `g • 0 = p` is finite and nonzero, reading `g` in
the inverted chart at `p` instead of the affine chart changes its second derivative at `0` from `w`
to `2 v² / p³ - w / p²`, where `v` is its first derivative. -/
theorem iteratedDeriv_two_invChart_pgl_smul_coe (g : PGL(2, 𝕜)) {p : 𝕜} (hp0 : p ≠ 0)
    (hp : g • ((0 : 𝕜) : OnePoint 𝕜) = p) :
    iteratedDeriv 2 (fun z : 𝕜 ↦ invChart (g • (z : OnePoint 𝕜))) 0 =
      2 * deriv (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜)
          (fun x ↦ g • x)) 0 ^ 2 / p ^ 3 -
        iteratedDeriv 2 (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜)
          (fun x ↦ g • x)) 0 / p ^ 2 := by
  have h0 := writtenInExtChartAt_pgl_smul_zero_zero hp
  have hinv : ContDiffAt 𝕜 2 (fun x : 𝕜 ↦ x⁻¹)
      (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜) (fun x ↦ g • x) 0) := by
    rw [h0]
    exact contDiffAt_inv 𝕜 hp0
  have hcomp := iteratedDeriv_comp_two hinv (contDiffAt_writtenInExtChartAt_pgl_smul_zero g)
  rw [h0] at hcomp
  have hd2 : iteratedDeriv 2 (fun x : 𝕜 ↦ x⁻¹) p = 2 / p ^ 3 := by
    rw [iteratedDeriv_eq_iterate, iter_deriv_inv]
    simp only [even_two, Even.neg_pow, one_pow, Nat.factorial_two, Nat.cast_ofNat, one_mul,
      Int.reduceNeg, Int.reduceSub, _root_.zpow_neg, zpow_ofNat]
    ring
  have hfun : (fun z : 𝕜 ↦ invChart (g • (z : OnePoint 𝕜))) =
      (fun x : 𝕜 ↦ x⁻¹) ∘
        writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜) (fun x ↦ g • x) := by
    funext z
    rw [congrFun (invChart_pgl_smul_coe_eq_inv g hp) z, Pi.inv_apply, Function.comp_apply]
  rw [hfun, hcomp, hd2, deriv_inv]
  field_simp
  ring

end TargetChart

end OnePoint
