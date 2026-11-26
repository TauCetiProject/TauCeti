/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import TauCeti.Geometry.Manifold.Algebra.Quotient
public import TauCeti.Geometry.Manifold.Instances.SpecialLinearGroup
public import TauCeti.Geometry.Manifold.Instances.OnePoint.DistinctTriples
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import Mathlib.Geometry.Manifold.Algebra.Structures
import TauCeti.Analysis.Calculus.FDeriv.Det.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.Geometry.Manifold.Instances.OnePoint.Projectivization

/-!
# The Möbius transformation through three moving points

The center of `SL(n, 𝕜)` is finite (`Matrix.SpecialLinearGroup.finite_center`), hence a discrete
normal subgroup, so the projective special linear group `PSL(n, 𝕜) = SL(n, 𝕜) ⧸ Z(SL(n, 𝕜))` over
`𝕜 = ℝ` or `ℂ` is an analytic Lie group, with the charts of `SL(n, 𝕜)` pushed forward along the
projection (`Subgroup.instLieGroupDiscreteQuotient`); the projection is a local diffeomorphism
(`Subgroup.isLocalDiffeomorph_quotientMk`). For `𝕜 = ℂ` and `n = 2` this makes `PSL(2, ℂ)`, the
automorphism group of the Riemann sphere `OnePoint ℂ`, a complex Lie group of dimension three.

For an ordered triple `b` of distinct points of the Riemann sphere,
`OnePoint.pslHomeomorphDistinctTriples b` identifies `PSL(2, ℂ)` with the ordered triples of
distinct points; its inverse sends a triple `p` to the unique Möbius transformation carrying `b`
to `p`. This file shows that this transformation depends holomorphically on `p`: if three
pairwise distinct points `p x 0`, `p x 1`, `p x 2` depend `C^n` (for instance holomorphically) on a
parameter `x` in a complex manifold, then so does the Möbius transformation carrying `b` to them
(`OnePoint.contMDiffAt_pslHomeomorphDistinctTriples_symm`,
`OnePoint.contMDiff_pslHomeomorphDistinctTriples_symm`). This is how the automorphisms of a
genus-zero domain are normalized by three marked points in families.

The transformation carrying `0`, `1`, `∞` to `[P]`, `[Q]`, `[R]`, for nonzero homogeneous
coordinates `P`, `Q`, `R` of three distinct points, is the class of the matrix with columns
`det(Q, P) R` and `det(R, Q) P`: it sends `[1 : 0]` to `[R]`, `[0 : 1]` to `[P]`, and, by the
three-term identity `det(Q, P) R + det(R, Q) P = det(R, P) Q`, `[1 : 1]` to `[Q]`. Its
determinant `det(Q, P) det(R, Q) det(R, P)` does not vanish, where `det(v, w)` is the determinant
of the matrix with rows `v` and `w` (`Projectivization.mk_eq_mk_iff_det_eq_zero`). Near a parameter
`x₀`, the points have `C^n` homogeneous coordinates
(`OnePoint.exists_contMDiffAt_eventually_equivProjectivization_eq_mk`), and the determinant has a
square root that is analytic in it (`TauCeti.exists_analyticAt_pow_eq`).
Dividing by it gives a family of matrices of determinant one, `C^n` at `x₀`, hence a `C^n` family
in `SL(2, ℂ)` (`Matrix.SpecialLinearGroup.contMDiffAt_iff`), whose class in `PSL(2, ℂ)` is the
transformation sought.

## Main results

* `OnePoint.contMDiffAt_pslHomeomorphDistinctTriples_symm`: the Möbius transformation carrying a
  fixed triple to three distinct points depending `C^n` on a parameter at `x₀` is `C^n` at `x₀`.
* `OnePoint.contMDiff_pslHomeomorphDistinctTriples_symm`: the global version.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §2 (the Möbius transformations of the Riemann sphere).
-/

public section

noncomputable section

open Filter Function Matrix Topology
open scoped ContDiff Manifold MatrixGroups Matrix.Norms.Operator LinearAlgebra.Projectivization
attribute [local instance] Matrix.linftyOpTopologicalSpace

namespace OnePoint

/-- The matrix with columns `det(Q, P) R` and `det(R, Q) P`, which carries `[1 : 0]`, `[0 : 1]`
and `[1 : 1]` to `[R]`, `[P]` and `[Q]`. -/
private def tripleMatrix (P Q R : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(of ![Q, P]).det * R 0, (of ![R, Q]).det * P 0;
    (of ![Q, P]).det * R 1, (of ![R, Q]).det * P 1]

private theorem det_tripleMatrix (P Q R : Fin 2 → ℂ) :
    (tripleMatrix P Q R).det = (of ![Q, P]).det * (of ![R, Q]).det * (of ![R, P]).det := by
  simp only [tripleMatrix, det_fin_two, of_apply, cons_val_zero, cons_val_one]
  ring

private theorem tripleMatrix_mulVec_zero_one (P Q R : Fin 2 → ℂ) :
    tripleMatrix P Q R *ᵥ ![0, 1] = (of ![R, Q]).det • P := by
  ext i; fin_cases i <;> simp [tripleMatrix]

private theorem tripleMatrix_mulVec_one_zero (P Q R : Fin 2 → ℂ) :
    tripleMatrix P Q R *ᵥ ![1, 0] = (of ![Q, P]).det • R := by
  ext i; fin_cases i <;> simp [tripleMatrix]

private theorem tripleMatrix_mulVec_one_one (P Q R : Fin 2 → ℂ) :
    tripleMatrix P Q R *ᵥ ![1, 1] = (of ![R, P]).det • Q := by
  ext i; fin_cases i <;> simp [tripleMatrix, det_fin_two] <;> ring

/-- If a matrix `A` of `SL(2, ℂ)` sends the homogeneous coordinates `v` of a point `x` to a multiple
of `w`, then its class in `PSL(2, ℂ)` moves `x` to the point with homogeneous coordinates `w`. -/
private theorem equivProjectivization_smul_eq (A : SL(2, ℂ)) {v w : Fin 2 → ℂ} (hv : v ≠ 0)
    (hw : w ≠ 0) {x : OnePoint ℂ} (hx : equivProjectivization ℂ x = .mk ℂ v hv) {a : ℂ}
    (hA : (A : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v = a • w) :
    equivProjectivization ℂ ((A : PSL(2, ℂ)) • x) = .mk ℂ w hw := by
  rw [pslMk_smul, equivProjectivization_smul, hx, Projectivization.smul_mk,
    Projectivization.mk_eq_mk_iff']
  -- The action of `SL(2, ℂ)` on vectors is multiplication by the underlying matrix.
  exact ⟨a, hA.symm⟩

/-- Homogeneous coordinates of two distinct points of the Riemann sphere have nonzero
determinant. -/
private theorem det_of_ne_zero {x y : OnePoint ℂ} (hxy : x ≠ y) {v w : Fin 2 → ℂ} {hv : v ≠ 0}
    {hw : w ≠ 0} (hx : equivProjectivization ℂ x = .mk ℂ v hv)
    (hy : equivProjectivization ℂ y = .mk ℂ w hw) : (of ![v, w]).det ≠ 0 := fun h ↦
  hxy ((equivProjectivization ℂ).injective
    (hx.trans (((Projectivization.mk_eq_mk_iff_det_eq_zero hv hw).2 h).trans hy.symm)))

/-- For homogeneous coordinates `P`, `Q`, `R` of an ordered triple `q` of distinct points, the
class of any matrix of `SL(2, ℂ)` proportional to the matrix with columns `det(Q, P) R` and
`det(R, Q) P` is the Möbius transformation carrying `0`, `1`, `∞` to `q`. -/
private theorem pslHomeomorphDistinctTriples_symm_eq_of_coe_eq_smul
    (q : {p : Fin 3 → OnePoint ℂ // Injective p}) {P Q R : Fin 2 → ℂ} {hP : P ≠ 0} {hQ : Q ≠ 0}
    {hR : R ≠ 0} (hPq : equivProjectivization ℂ (q.val 0) = .mk ℂ P hP)
    (hQq : equivProjectivization ℂ (q.val 1) = .mk ℂ Q hQ)
    (hRq : equivProjectivization ℂ (q.val 2) = .mk ℂ R hR) (A : SL(2, ℂ)) {a : ℂ}
    (hA : (A : Matrix (Fin 2) (Fin 2) ℂ) = a • tripleMatrix P Q R) :
    (pslHomeomorphDistinctTriples (zeroOneInftyTriple ℂ)).symm q = A := by
  have h₀ : (A : PSL(2, ℂ)) • ((0 : ℂ) : OnePoint ℂ) = q.val 0 :=
    (equivProjectivization ℂ).injective ((equivProjectivization_smul_eq A _ hP
      (equivProjectivization_apply_coe ℂ 0) (a := a * (of ![R, Q]).det)
      (by rw [hA, smul_mulVec, tripleMatrix_mulVec_zero_one, smul_smul])).trans hPq.symm)
  have h₁ : (A : PSL(2, ℂ)) • ((1 : ℂ) : OnePoint ℂ) = q.val 1 :=
    (equivProjectivization ℂ).injective ((equivProjectivization_smul_eq A _ hQ
      (equivProjectivization_apply_coe ℂ 1) (a := a * (of ![R, P]).det)
      (by rw [hA, smul_mulVec, tripleMatrix_mulVec_one_one, smul_smul])).trans hQq.symm)
  have h₂ : (A : PSL(2, ℂ)) • (∞ : OnePoint ℂ) = q.val 2 :=
    (equivProjectivization ℂ).injective ((equivProjectivization_smul_eq A _ hR
      (equivProjectivization_apply_infinity ℂ) (a := a * (of ![Q, P]).det)
      (by rw [hA, smul_mulVec, tripleMatrix_mulVec_one_zero, smul_smul])).trans hRq.symm)
  rw [pslHomeomorphDistinctTriples_symm_eq_iff, coe_zeroOneInftyTriple]
  intro i
  fin_cases i
  exacts [h₀, h₁, h₂]

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  {I : ModelWithCorners ℂ E H} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

/-- The matrix with columns `det(Q, P) R` and `det(R, Q) P` depends `C^n` on vectors `P`, `Q`,
`R` that depend `C^n` on a parameter. -/
private theorem contMDiffAt_tripleMatrix {P Q R : M → Fin 2 → ℂ} {x₀ : M}
    (hP : ContMDiffAt I 𝓘(ℂ, Fin 2 → ℂ) n P x₀) (hQ : ContMDiffAt I 𝓘(ℂ, Fin 2 → ℂ) n Q x₀)
    (hR : ContMDiffAt I 𝓘(ℂ, Fin 2 → ℂ) n R x₀) :
    ContMDiffAt I 𝓘(ℂ, Matrix (Fin 2) (Fin 2) ℂ) n
      (fun x ↦ tripleMatrix (P x) (Q x) (R x)) x₀ := by
  have h : ContDiff ℂ ω fun T : (Fin 2 → ℂ) × (Fin 2 → ℂ) × (Fin 2 → ℂ) ↦
      fun i j : Fin 2 ↦ tripleMatrix T.1 T.2.1 T.2.2 i j := by
    refine contDiff_pi.2 fun i ↦ contDiff_pi.2 fun j ↦ ?_
    fin_cases i <;> fin_cases j <;>
      simp only [tripleMatrix, det_fin_two, Fin.isValue, Fin.zero_eta, Fin.mk_one, of_apply,
        cons_val', cons_val_zero, cons_val_one, cons_val_fin_one] <;> fun_prop
  -- `Matrix.of` identifies entry functions with matrices.
  convert (((Matrix.ofContinuousLinearEquiv ℂ).contDiff.comp h).of_le le_top).contDiffAt
    |>.comp_contMDiffAt (hP.prodMk_space (hQ.prodMk_space hR)) using 1
  ext x i j
  simp

/-- **The Möbius transformation through three moving points depends holomorphically on them.**
Let `b` be an ordered triple of distinct points of the Riemann sphere, and let `p x` be an ordered
triple of distinct points depending on a parameter `x` in a complex manifold. If each point
`p x i` is `C^n` at `x₀`, then so is the Möbius transformation carrying `b` to `p x`, as a map into
the complex Lie group `PSL(2, ℂ)`; for `n = ω` it is holomorphic at `x₀`. -/
theorem contMDiffAt_pslHomeomorphDistinctTriples_symm {p : M → Fin 3 → OnePoint ℂ}
    (hp : ∀ x, Injective (p x)) {x₀ : M} (hpx : ∀ i, ContMDiffAt I 𝓘(ℂ) n (fun x ↦ p x i) x₀)
    (b : {p : Fin 3 → OnePoint ℂ // Injective p}) :
    ContMDiffAt I 𝓘(ℂ, SpecialLinearGroup.Model (Fin 2) ℂ) n
      (fun x ↦ (pslHomeomorphDistinctTriples b).symm ⟨p x, hp x⟩) x₀ := by
  -- It suffices to treat the base triple `(0, 1, ∞)`, since changing the base triple multiplies
  -- on the right by a fixed element.
  suffices h : ContMDiffAt I 𝓘(ℂ, SpecialLinearGroup.Model (Fin 2) ℂ) n
      (fun x ↦ (pslHomeomorphDistinctTriples (zeroOneInftyTriple ℂ)).symm ⟨p x, hp x⟩) x₀ by
    simp_rw [pslHomeomorphDistinctTriples_symm_eq_mul_inv b (zeroOneInftyTriple ℂ)]
    exact h.mul contMDiffAt_const
  -- Homogeneous coordinates `P`, `Q`, `R` of the three points, `C^n` at `x₀`.
  obtain ⟨P, hP, hPev⟩ := exists_contMDiffAt_eventually_equivProjectivization_eq_mk (hpx 0)
  obtain ⟨Q, hQ, hQev⟩ := exists_contMDiffAt_eventually_equivProjectivization_eq_mk (hpx 1)
  obtain ⟨R, hR, hRev⟩ := exists_contMDiffAt_eventually_equivProjectivization_eq_mk (hpx 2)
  -- The determinant `d` of the matrix with columns `det(Q, P) R` and `det(R, Q) P` does not
  -- vanish at `x₀`, since the three points are distinct.
  have hT := contMDiffAt_tripleMatrix hP hQ hR
  set d : M → ℂ := fun x ↦ (tripleMatrix (P x) (Q x) (R x)).det
  -- Here and in `hc`, naming the inner map spares the unifier from unfolding the determinants.
  have hd : ContMDiffAt I 𝓘(ℂ) n d x₀ :=
    contDiff_det.contDiffAt.comp_contMDiffAt (f := fun x ↦ tripleMatrix (P x) (Q x) (R x)) hT
  obtain ⟨_, hPx₀⟩ := hPev.self_of_nhds
  obtain ⟨_, hQx₀⟩ := hQev.self_of_nhds
  obtain ⟨_, hRx₀⟩ := hRev.self_of_nhds
  have hd₀ : d x₀ ≠ 0 := by
    simp only [d, det_tripleMatrix]
    exact mul_ne_zero (mul_ne_zero (det_of_ne_zero ((hp x₀).ne (by decide)) hQx₀ hPx₀)
      (det_of_ne_zero ((hp x₀).ne (by decide)) hRx₀ hQx₀))
      (det_of_ne_zero ((hp x₀).ne (by decide)) hRx₀ hPx₀)
  -- A square root `c` of `d` near `x₀`, analytic in `d`, and the normalized matrix `B`.
  obtain ⟨root, hroot, -, hroot_sq⟩ :=
    TauCeti.exists_analyticAt_pow_eq two_ne_zero hd₀ (Complex.cpow_nat_inv_pow (d x₀) two_ne_zero)
  have hc : ContMDiffAt I 𝓘(ℂ) n (fun x ↦ root (d x)) x₀ :=
    hroot.contDiffAt.comp_contMDiffAt (f := d) hd
  have hc₀ : root (d x₀) ≠ 0 := fun h ↦ hd₀ (by rw [← hroot_sq (d x₀), h, zero_pow two_ne_zero])
  set B : M → Matrix (Fin 2) (Fin 2) ℂ :=
    fun x ↦ (root (d x))⁻¹ • tripleMatrix (P x) (Q x) (R x) with hB_def
  have hB : ContMDiffAt I 𝓘(ℂ, Matrix (Fin 2) (Fin 2) ℂ) n B x₀ :=
    (hc.inv₀ hc₀).smul hT
  have hBdet {x : M} (hx : d x ≠ 0) : (B x).det = 1 := by
    rw [hB_def, det_smul, Fintype.card_fin, inv_pow, hroot_sq]
    exact inv_mul_cancel₀ hx
  have hev : ∀ᶠ x in 𝓝 x₀, d x ≠ 0 := hd.continuousAt.eventually_ne hd₀
  -- The corresponding map `L` into `SL(2, ℂ)` is `C^n` at `x₀`, since its matrix is.
  let L : M → SL(2, ℂ) := fun x ↦ if h : (B x).det = 1 then ⟨B x, h⟩ else 1
  have hLB {x : M} (hx : d x ≠ 0) : (L x : Matrix (Fin 2) (Fin 2) ℂ) = B x :=
    congrArg Subtype.val (dite_eq_left (hBdet hx))
  have hL : ContMDiffAt I 𝓘(ℂ, SpecialLinearGroup.Model (Fin 2) ℂ) n L x₀ :=
    SpecialLinearGroup.contMDiffAt_iff.2 (hB.congr_of_eventuallyEq (hev.mono fun _ ↦ hLB))
  -- Near `x₀`, the class of `L x` is the transformation carrying `0`, `1`, `∞` to `p x`.
  have hkey : (fun x ↦ (pslHomeomorphDistinctTriples (zeroOneInftyTriple ℂ)).symm ⟨p x, hp x⟩)
      =ᶠ[𝓝 x₀] fun x ↦ ((L x : SL(2, ℂ)) : PSL(2, ℂ)) := by
    filter_upwards [hPev, hQev, hRev, hev] with x ⟨_, hPx⟩ ⟨_, hQx⟩ ⟨_, hRx⟩ hx
    exact pslHomeomorphDistinctTriples_symm_eq_of_coe_eq_smul ⟨p x, hp x⟩ hPx hQx hRx (L x)
      (hLB hx)
  have hmk := (Subgroup.isLocalDiffeomorph_quotientMk
    (I := 𝓘(ℂ, SpecialLinearGroup.Model (Fin 2) ℂ)) (n := ω) (Subgroup.center SL(2, ℂ))).contMDiff
  exact ((hmk.of_le le_top).contMDiffAt.comp x₀ hL).congr_of_eventuallyEq hkey

/-- **The Möbius transformation through three moving points depends holomorphically on them.**
If three pairwise distinct points of the Riemann sphere depend `C^n` on a parameter in a complex
manifold, then so does the Möbius transformation carrying a fixed ordered triple of distinct points
to them, as a map into the complex Lie group `PSL(2, ℂ)`; for `n = ω` it is holomorphic. -/
theorem contMDiff_pslHomeomorphDistinctTriples_symm {p : M → Fin 3 → OnePoint ℂ}
    (hp : ∀ x, Injective (p x)) (hpx : ∀ i, ContMDiff I 𝓘(ℂ) n fun x ↦ p x i)
    (b : {p : Fin 3 → OnePoint ℂ // Injective p}) :
    ContMDiff I 𝓘(ℂ, SpecialLinearGroup.Model (Fin 2) ℂ) n
      fun x ↦ (pslHomeomorphDistinctTriples b).symm ⟨p x, hp x⟩ :=
  fun x₀ ↦ contMDiffAt_pslHomeomorphDistinctTriples_symm hp (fun i ↦ hpx i x₀) b

end OnePoint
