/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.LocalNormalForm
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# The Morse–Bott lemma in product coordinates

Let `f (b, v)` be a function on a product `P × F` of finite-dimensional spaces whose zero section
`P × {0}` consists of critical points near `a`. Differentiating `b ↦ Df(b, 0) = 0` shows that the
base directions `P × {0}` lie in the kernel of the Hessian at `(a, 0)`
(`TauCeti.fderiv_fderiv_apply_inl_eq_zero`). The zero section is a **nondegenerate**, or
**Morse–Bott**, critical submanifold at `(a, 0)` when this kernel is no larger. Then the
restriction of the Hessian to the fibre `{a} × F`, the vertical Hessian, is invertible
(`TauCeti.isInvertible_fderiv_fderiv_slice_right_of_ker_le`): a vector of the fibre in its kernel
pairs to zero with the fibre directions, and with the base directions by symmetry, so it lies in
the kernel of the Hessian, which meets the fibre only in `0`.

With the parametric Morse lemma this gives the **Morse–Bott lemma** in product coordinates
(`TauCeti.exists_morseBott_chart_of_contDiffOn`): if `f` is `C^{n+2}` near `(a, 0)`, with
`1 ≤ n ≤ ∞`, there is a `C^n` change of fibre coordinates `ψ` preserving the base parameter and
fixing the zero section in which `f` is its constant critical value plus half the vertical Hessian,
`f z = f (a, 0) + ½ D²(f (z.1, ·))(0) ((ψ z).2, (ψ z).2)`, and the vertical Hessian is invertible
along the whole zero section of the chart. Diagonalizing the vertical Hessians as quadratic
forms is not part of this statement: they vary with the base point.

## Main declarations

* `TauCeti.isInvertible_fderiv_fderiv_slice_right_of_ker_le`: the vertical Hessian at a
  Morse–Bott point of the zero section is invertible.
* `TauCeti.exists_morseBott_chart_of_contDiffOn`: the Morse–Bott lemma in product coordinates.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* A. Banyaga and D. E. Hurtubise, *A proof of the Morse–Bott lemma*, Expositiones Mathematicae 22
  (2004), 365–373.
-/

public section

open Filter Metric Set Topology
open scoped ContDiff

namespace TauCeti

variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f : P × F → ℝ} {a : P}

/-- **The vertical Hessian at a Morse–Bott point is invertible.** If `f` is `C²` at `(a, 0)`, every
point `(b, 0)` with `b` near `a` is critical, and the kernel of the Hessian at `(a, 0)` consists of
base directions, then the Hessian at `0` of the fibre restriction `v ↦ f (a, v)` is invertible. -/
theorem isInvertible_fderiv_fderiv_slice_right_of_ker_le [FiniteDimensional ℝ F]
    (hf : ContDiffAt ℝ 2 f (a, 0)) (hcrit : ∀ᶠ b in 𝓝 a, fderiv ℝ f (b, 0) = 0)
    (hker : (fderiv ℝ (fderiv ℝ f) (a, 0)).ker ≤ LinearMap.range (LinearMap.inl ℝ P F)) :
    (fderiv ℝ (fderiv ℝ (fun v ↦ f (a, v))) 0).IsInvertible := by
  refine ContinuousLinearMap.isInvertible_of_injective <|
    (injective_iff_map_eq_zero _).mpr fun v hv ↦ ?_
  -- The vector `(0, v)` pairs to zero with every direction, so it lies in the kernel.
  have hD : fderiv ℝ (fderiv ℝ f) (a, 0) (0, v) = 0 := by
    refine ContinuousLinearMap.ext fun z ↦ ?_
    obtain ⟨u, w⟩ := z
    have hw : fderiv ℝ (fderiv ℝ f) (a, 0) (0, v) (0, w) = 0 := by
      simpa [hv] using (fderiv_fderiv_slice_right_apply hf v w).symm
    have hu : fderiv ℝ (fderiv ℝ f) (a, 0) (0, v) (u, 0) = 0 := by
      simp [hf.isSymmSndFDerivAt (by simp) (0, v) (u, 0),
        fderiv_fderiv_apply_inl_eq_zero hf hcrit u]
    have hsplit : ((u, w) : P × F) = (u, 0) + (0, w) := by simp
    rw [hsplit, map_add, hu, hw]
    simp
  have hmem : ((0 : P), v) ∈ (fderiv ℝ (fderiv ℝ f) (a, 0)).ker := LinearMap.mem_ker.mpr hD
  obtain ⟨u, hu⟩ := hker hmem
  simpa using (congrArg Prod.snd hu).symm

variable [FiniteDimensional ℝ P] [FiniteDimensional ℝ F] {W : Set (P × F)} {n : ℕ∞}

/-- **The Morse–Bott lemma in product coordinates.** Let `f` be `C^{n+2}` on a neighbourhood `W`
of `(a, 0)`, with `1 ≤ n ≤ ∞`, such that every point `(b, 0)` with `b` near `a` is critical and the
kernel of the Hessian at `(a, 0)` consists of base directions. Then there is a `C^n` chart `ψ`
with product source `U ×ˢ V` in `W`, preserving the base parameter in both directions and fixing
the zero section, such that on `U` the vertical Hessian is invertible and the critical value is
constant, and on the source of `ψ` the function `f` is that critical value plus half the vertical
Hessian read in the chart. -/
theorem exists_morseBott_chart_of_contDiffOn (hW : W ∈ 𝓝 (a, 0))
    (hf : ContDiffOn ℝ (n + 2) f W) (hcrit : ∀ᶠ b in 𝓝 a, fderiv ℝ f (b, 0) = 0)
    (hker : (fderiv ℝ (fderiv ℝ f) (a, 0)).ker ≤ LinearMap.range (LinearMap.inl ℝ P F))
    (hn : n ≠ 0) :
    ∃ (ψ : OpenPartialHomeomorph (P × F) (P × F)) (U : Set P) (V : Set F),
      IsOpen U ∧ IsOpen V ∧ a ∈ U ∧ (0 : F) ∈ V ∧ ψ.source = U ×ˢ V ∧ U ×ˢ V ⊆ W ∧
      (∀ z, (ψ z).1 = z.1) ∧ (∀ b, ψ (b, 0) = (b, 0)) ∧
      (∀ z ∈ ψ.target, (ψ.symm z).1 = z.1) ∧
      ContDiffOn ℝ n ψ ψ.source ∧ ContDiffOn ℝ n ψ.symm ψ.target ∧
      (∀ b ∈ U, f (b, 0) = f (a, 0)) ∧
      (∀ b ∈ U, (fderiv ℝ (fderiv ℝ (fun v ↦ f (b, v))) 0).IsInvertible) ∧
      ∀ z ∈ ψ.source,
        f z = f (a, 0) + (2 : ℝ)⁻¹ *
          fderiv ℝ (fderiv ℝ (fun v ↦ f (z.1, v))) 0 (ψ z).2 (ψ z).2 := by
  have h2 : (2 : ℕ∞ω) ≤ n + 2 := le_add_self
  -- `f` is `C²` at every point of a neighbourhood of `(a, 0)`.
  have hC2 : ∀ᶠ z in 𝓝 (a, (0 : F)), ContDiffAt ℝ 2 f z := by
    filter_upwards [eventually_mem_nhds_iff.mpr hW] with z hz
    exact (hf.contDiffAt hz).of_le h2
  have hC2a : ContDiffAt ℝ 2 f (a, 0) := hC2.self_of_nhds
  have hC2b : ∀ᶠ b in 𝓝 a, ContDiffAt ℝ 2 f (b, 0) :=
    (continuous_id.prodMk continuous_const).continuousAt.eventually hC2
  -- The vertical Hessian is invertible at `a`, hence at every base point near `a`: it is the
  -- restriction of the Hessian, which is continuous, and invertible maps form an open set.
  have hHa := isInvertible_fderiv_fderiv_slice_right_of_ker_le hC2a hcrit hker
  have hHb : ∀ᶠ b in 𝓝 a, (fderiv ℝ (fderiv ℝ (fun v ↦ f (b, v))) 0).IsInvertible := by
    -- Restriction of a bilinear form on `P × F` to the fibre directions.
    let K : (P × F →L[ℝ] ℝ) →L[ℝ] F →L[ℝ] ℝ :=
      (ContinuousLinearMap.compL ℝ F (P × F) ℝ).flip (ContinuousLinearMap.inr ℝ P F)
    let D : P → F →L[ℝ] F →L[ℝ] ℝ := fun b ↦
      K.comp ((fderiv ℝ (fderiv ℝ f) (b, 0)).comp (ContinuousLinearMap.inr ℝ P F))
    have hD : ∀ᶠ b in 𝓝 a, D b = fderiv ℝ (fderiv ℝ (fun v ↦ f (b, v))) 0 := by
      filter_upwards [hC2b] with b hb
      ext v w
      exact (fderiv_fderiv_slice_right_apply hb v w).symm
    have hcont : ContinuousAt D a := by
      have hpair : ContinuousAt (fun b : P ↦ (b, (0 : F))) a :=
        continuousAt_id.prodMk continuousAt_const
      have h := ContinuousAt.comp (g := fderiv ℝ (fderiv ℝ f)) (f := fun b : P ↦ (b, (0 : F)))
        (x := a) ((hC2a.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0)
          (by norm_num)).continuousAt hpair
      exact continuousAt_const.clm_comp (h.clm_comp continuousAt_const)
    have hopen : ∀ᶠ b in 𝓝 a, (D b).IsInvertible := by
      rw [← hD.self_of_nhds] at hHa
      obtain ⟨e, he⟩ := hHa
      exact hcont.eventually ((ContinuousLinearEquiv.isOpen).mem_nhds ⟨e, he⟩)
    filter_upwards [hD, hopen] with b hb hb'
    rwa [← hb]
  -- The vertical critical points of the fibre restrictions.
  have hcrit' : ∀ᶠ b in 𝓝 a, fderiv ℝ (fun v ↦ f (b, v)) 0 = 0 := by
    filter_upwards [hcrit, hC2b] with b hb hb2
    rw [fderiv_slice_right (hb2.differentiableAt (by norm_num)), hb,
      ContinuousLinearMap.zero_comp]
  obtain ⟨ψ, U, V, hU, hV, haU, h0V, hsource, hUV, hψfst, hψ0, hψsymm, hψ, hψinv, hψf⟩ :=
    exists_parametric_morse_chart_of_contDiffOn hW hf hcrit' hHa hn
  -- Shrink the base to a ball on which the zero section is critical and the vertical Hessian
  -- invertible; the critical value is constant on that ball.
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    ((hU.eventually_mem haU).and ((hcrit.and hC2b).and hHb))
  let ψ' := ψ.restrOpen (ball a r ×ˢ V) (isOpen_ball.prod hV)
  have hsource' : ψ'.source = ball a r ×ˢ V := by
    rw [OpenPartialHomeomorph.restrOpen_source, hsource, prod_inter_prod,
      inter_eq_right.mpr fun b hb ↦ (hball b hb).1, inter_self]
  have hconst : ∀ b ∈ ball a r, f (b, 0) = f (a, 0) := by
    have hdiff : ∀ b ∈ ball a r, HasFDerivAt (fun b ↦ f (b, 0)) 0 b := fun b hb ↦ by
      have hd := ((hball b hb).2.1.2.differentiableAt (by norm_num)).hasFDerivAt.comp b
        (hasFDerivAt_prodMk_left (𝕜 := ℝ) b (0 : F))
      rwa [(hball b hb).2.1.1, ContinuousLinearMap.zero_comp] at hd
    exact fun b hb ↦ (convex_ball a r).is_const_of_fderivWithin_eq_zero
      (fun b hb ↦ (hdiff b hb).differentiableAt.differentiableWithinAt)
      (fun b hb ↦ by rw [fderivWithin_of_isOpen isOpen_ball hb, (hdiff b hb).fderiv])
      hb (mem_ball_self hr)
  refine ⟨ψ', ball a r, V, isOpen_ball, hV, mem_ball_self hr, h0V, hsource',
    fun z hz ↦ hUV ⟨(hball z.1 hz.1).1, hz.2⟩, hψfst, hψ0, fun z hz ↦ hψsymm z hz.1,
    hψ.mono (by simp [ψ']), hψinv.mono fun z hz ↦ hz.1, hconst,
    fun b hb ↦ (hball b hb).2.2, fun z hz ↦ ?_⟩
  rw [hsource'] at hz
  rw [← hconst z.1 hz.1]
  exact hψf z (hsource ▸ ⟨(hball z.1 hz.1).1, hz.2⟩)

end TauCeti
