/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import TauCeti.Analysis.MvPolynomial.Jacobian
public import TauCeti.Geometry.Manifold.Instances.Projectivization
public import TauCeti.LinearAlgebra.Projectivization.ZeroLocus

import Mathlib.Analysis.Calculus.FDeriv.Pow
import TauCeti.Geometry.Manifold.RegularValue

/-!
# Differentials of homogeneous equations in projective charts

A homogeneous polynomial family defines polynomial equations in each standard ratio chart of
native projective space. Their analytic derivative is the cone Jacobian with the normalized
coordinate column omitted. At common zeros its surjectivity agrees with that of the cone
Jacobian, so the full-rank condition can be tested by the actual chart equations, also when they
are read as functions on projective space and differentiated as maps of manifolds.

On an overlap, a degree-`d` equation changes by the inverse `d`-th power of the new homogeneous
coordinate. At a zero, differentiating this identity gives the corresponding scaling law for
the chart derivatives, composed with the derivative of the native chart transition. These are
local formulas for the differential of homogeneous equations; no global bundle is constructed
here.

## References

* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Chapter 0, §1, for homogeneous
  coordinate charts and the transition factors of homogeneous equations.
-/

public section

open MvPolynomial
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] {n : ℕ}

/-- The actual analytic derivative of the equations in a standard ratio chart is the cone
Jacobian at the normalized representative with the chart coordinate column deleted. -/
theorem fderiv_eval_dehomogenize (i : Fin (n + 1))
    (p : ι → MvPolynomial (Fin (n + 1)) 𝕜) (a : Fin n → 𝕜) :
    (fderiv 𝕜 (fun z ↦ fun k ↦ eval z (dehomogenize i (p k))) a).toLinearMap =
      ((jacobiMatrixAt p (i.insertNth 1 a)).submatrix id i.succAbove).mulVecLin := by
  rw [fderiv_eval_family, jacobiMatrixAt_dehomogenize]

/-- At a common zero, the derivative of the actual ratio-chart equations is surjective exactly
when the cone Jacobian is surjective. -/
theorem surjective_fderiv_eval_dehomogenize_div_iff [Finite ι] (i : Fin (n + 1))
    {p : ι → MvPolynomial (Fin (n + 1)) 𝕜} {d : ι → ℕ}
    (hp : ∀ k, (p k).IsHomogeneous (d k)) {b : Fin (n + 1) → 𝕜}
    (hi : b i ≠ 0) (hb : ∀ k, eval b (p k) = 0) :
    Function.Surjective (fderiv 𝕜 (fun z ↦ fun k ↦ eval z (dehomogenize i (p k)))
      (fun j ↦ b (i.succAbove j) / b i)) ↔
      Function.Surjective (jacobiMatrixAt p b).mulVec := by
  classical
  cases nonempty_fintype ι
  have h := congrArg (fun f : (Fin n → 𝕜) →ₗ[𝕜] (ι → 𝕜) ↦ ⇑f)
    (fderiv_eval_family (fun k ↦ dehomogenize i (p k))
      (fun j ↦ b (i.succAbove j) / b i))
  simp only [ContinuousLinearMap.coe_coe, Matrix.coe_mulVecLin] at h
  rw [h, Matrix.mulVec_surjective_iff_rank_eq_card,
    rank_jacobiMatrixAt_dehomogenize_div i hp hi hb,
    Matrix.mulVec_surjective_iff_rank_eq_card]

/-- On the native complex projective zero locus, full rank of the cone Jacobian is exactly
surjectivity of the derivative of the actual equations in any chart containing the point. -/
theorem surjective_fderiv_eval_dehomogenize_affineChart_iff [Finite ι]
    (i : Fin (n + 1)) {p : ι → MvPolynomial (Fin (n + 1)) ℂ} {d : ι → ℕ}
    (hp : ∀ k, (p k).IsHomogeneous (d k))
    {L : Projectivization ℂ (Fin (n + 1) → ℂ)} (hL : L ∈ complexProjectiveZeroLocus p)
    (hi : L ∈ Projectivization.affineOpen i) :
    Function.Surjective (fderiv ℂ (fun z ↦ fun k ↦ eval z (dehomogenize i (p k)))
      (Projectivization.affineChart i L)) ↔
      Function.Surjective (jacobiMatrixAt p L.rep).mulVec := by
  have hi' : L.rep i ≠ 0 := by
    exact (Projectivization.mk_mem_affineOpen_iff i L.rep L.rep_nonzero).mp
      (L.mk_rep.symm ▸ hi)
  have hb := (mem_complexProjectiveZeroLocus_iff_eval_rep hp L).mp hL
  have hchart := Projectivization.affineChart_mk i L.rep L.rep_nonzero
  rw [L.mk_rep] at hchart
  rw [hchart]
  exact surjective_fderiv_eval_dehomogenize_div_iff i hp hi' hb

/-- **Full rank on projective space.** At a point `L` of the native complex projective zero locus
of a homogeneous family `p` in the standard affine open `U_i`, the manifold differential of the
chart equations at `L` is surjective exactly when the cone Jacobian of `p` is surjective. -/
theorem surjective_mfderiv_eval_dehomogenize_affineChart_iff [Fintype ι]
    (i : Fin (n + 1)) {p : ι → MvPolynomial (Fin (n + 1)) ℂ} {d : ι → ℕ}
    (hp : ∀ k, (p k).IsHomogeneous (d k))
    {L : Projectivization ℂ (Fin (n + 1) → ℂ)} (hL : L ∈ complexProjectiveZeroLocus p)
    (hi : L ∈ Projectivization.affineOpen i) :
    Function.Surjective (mfderiv 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ι → ℂ)
      (fun w ↦ fun k ↦ eval (Projectivization.affineChart i w) (dehomogenize i (p k))) L) ↔
      Function.Surjective (jacobiMatrixAt p L.rep).mulVec := by
  have hchart : MDifferentiableAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ)
      (Projectivization.affineChart i) L :=
    ((Projectivization.contMDiffOn_affineChart i 1).contMDiffAt
      ((Projectivization.isOpen_affineOpen i).mem_nhds hi)).mdifferentiableAt one_ne_zero
  -- The differential of the chart `affineChart i` itself is bijective.
  have hbij := (mdifferentiable_of_mem_atlas (I := 𝓘(ℂ, Fin n → ℂ))
    (Projectivization.affineOpenPartialHomeomorph_mem_atlas i)).mfderiv_bijective
    (by simpa using hi)
  rw [Projectivization.coe_affineOpenPartialHomeomorph] at hbij
  -- The chain rule through the chart `affineChart i`.
  have hcomp := mfderiv_comp L
    (hasFDerivAt_eval_family (fun k ↦ dehomogenize i (p k)) _).differentiableAt.mdifferentiableAt
    hchart
  -- The chart equations are the polynomial equations composed with the chart. Surjectivity is
  -- unchanged by the bijective chart differential, and for the polynomial equations on
  -- `Fin n → ℂ` it is surjectivity of their Fréchet derivative.
  change Function.Surjective (mfderiv _ _
    ((fun z : Fin n → ℂ ↦ fun k ↦ eval z (dehomogenize i (p k))) ∘
      Projectivization.affineChart i) L) ↔ _
  rw [hcomp, ContinuousLinearMap.coe_comp, Function.Surjective.of_comp_iff _ hbij.surjective,
    ← isRegularPoint_iff, isRegularPoint_iff_surjective_fderiv]
  exact surjective_fderiv_eval_dehomogenize_affineChart_iff i hp hL hi

/-- At a common zero, derivatives of homogeneous chart equations transform by the homogeneous
transition factor, after precomposition with the derivative of the native chart transition.
The formula permits different degrees in different rows, including degree zero. -/
theorem fderiv_eval_dehomogenize_transition (i j : Fin (n + 1))
    {p : ι → MvPolynomial (Fin (n + 1)) 𝕜} {d : ι → ℕ}
    (hp : ∀ k, (p k).IsHomogeneous (d k)) {a : Fin n → 𝕜}
    (hj : i.insertNth (α := fun _ ↦ 𝕜) 1 a j ≠ 0) (ha : ∀ k, eval a (dehomogenize i (p k)) = 0) :
    (fderiv 𝕜 (fun z ↦ fun k ↦ eval z (dehomogenize j (p k)))
        ((Projectivization.affineChart i).symm.trans (Projectivization.affineChart j) a)).comp
      (fderiv 𝕜 ((Projectivization.affineChart i).symm.trans
        (Projectivization.affineChart j)) a) =
      ContinuousLinearMap.pi (fun k ↦ (i.insertNth (α := fun _ ↦ 𝕜) 1 a j)⁻¹ ^ d k •
        (ContinuousLinearMap.proj k).comp
          (fderiv 𝕜 (fun z ↦ fun k ↦ eval z (dehomogenize i (p k))) a)) := by
  let T := (Projectivization.affineChart (K := 𝕜) i).symm.trans
    (Projectivization.affineChart j)
  have hw : ContDiff 𝕜 1 (fun z : Fin n → 𝕜 ↦ i.insertNth (α := fun _ ↦ 𝕜) 1 z) :=
    (contDiff_const (c := (1 : 𝕜))).finInsertNth (F := fun _ ↦ 𝕜) i contDiff_id
  have hwj := (contDiff_pi.mp hw j).differentiable (by simp)
  have hne : ∀ᶠ z in 𝓝 a, i.insertNth (α := fun _ ↦ 𝕜) 1 z j ≠ 0 :=
    hwj.continuous.continuousAt.eventually_ne hj
  have ht : DifferentiableAt 𝕜 T a :=
    ((Projectivization.contDiffOn_affineChart_symm_trans i j 1).contDiffAt
      (by rwa [Projectivization.affineChart_symm_trans_source])).differentiableAt_one
  have hs := (hasFDerivAt_eval_family (fun k ↦ dehomogenize i (p k)) a).differentiableAt
  have htgt := (hasFDerivAt_eval_family (fun k ↦ dehomogenize j (p k)) (T a)).differentiableAt
  have hproduct : HasFDerivAt
      (fun z ↦ fun k ↦ (i.insertNth (α := fun _ ↦ 𝕜) 1 z j)⁻¹ ^ d k * eval z (dehomogenize i (p k)))
      (ContinuousLinearMap.pi fun k ↦ (i.insertNth (α := fun _ ↦ 𝕜) 1 a j)⁻¹ ^ d k •
        (ContinuousLinearMap.proj k).comp
          (fderiv 𝕜 (fun z ↦ fun k ↦ eval z (dehomogenize i (p k))) a)) a := by
    apply hasFDerivAt_pi.mpr
    intro k
    have hk := ((hwj a).inv hj).pow (d k)
    convert! hk.hasFDerivAt.mul (hasFDerivAt_pi'.mp hs.hasFDerivAt k) using 1
    ext u
    simp [ha k]
  have heq : (fun z ↦ fun k ↦ eval (T z) (dehomogenize j (p k))) =ᶠ[𝓝 a]
      (fun z ↦ fun k ↦ (i.insertNth (α := fun _ ↦ 𝕜) 1 z j)⁻¹ ^ d k *
        eval z (dehomogenize i (p k))) := by
    filter_upwards [hne] with z hz
    funext k
    simpa only [T, Projectivization.affineChart_symm_trans_apply, eval_dehomogenize] using
      eval_dehomogenize_div j (hp k) (i.insertNth (α := fun _ ↦ 𝕜) 1 z) hz
  exact (htgt.hasFDerivAt.comp a ht.hasFDerivAt).unique
    (hproduct.congr_of_eventuallyEq heq)

end TauCeti
