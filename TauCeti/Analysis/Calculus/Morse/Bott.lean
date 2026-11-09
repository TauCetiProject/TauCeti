/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Index
public import TauCeti.Analysis.Calculus.Morse.LocalNormalForm
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
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
along the whole zero section of the chart.

The vertical Hessians vary with the base point, but near `a` they are all congruent to the one at
`a`, by a `C^n` family of invertible operators
(`TauCeti.exists_congruence_fderiv_fderiv_slice_right`). Following these operators by
Sylvester coordinates of the vertical Hessian at `a` normalizes the fibre form
(`OpenPartialHomeomorph.exists_normalized_morseBott_chart`). This is the **normalized Morse–Bott
lemma** (`TauCeti.exists_normalized_morseBott_chart_of_contDiffOn`): in a `C^n` chart onto an
open subset of `P × ℝᵐ`, `m = dim F`, preserving the base parameter and fixing the zero section,

`f z = f (a, 0) - Σ_{i < λ} (ψ z).2ᵢ² + Σ_{i ≥ λ} (ψ z).2ᵢ²`,

where `λ` is the Morse index of `f` at `(a, 0)`. That index is the index of the vertical Hessian
(`TauCeti.morseIndex_slice_right`), since the base directions are null for the Hessian and
orthogonal to the fibre.

## Main declarations

* `TauCeti.isInvertible_fderiv_fderiv_slice_right_of_ker_le`: the vertical Hessian at a
  Morse–Bott point of the zero section is invertible.
* `TauCeti.exists_morseBott_chart_of_contDiffOn`: the Morse–Bott lemma in product coordinates.
* `TauCeti.exists_congruence_fderiv_fderiv_slice_right`: nearby vertical Hessians are congruent
  by a `C^n` family of invertible operators.
* `OpenPartialHomeomorph.exists_normalized_morseBott_chart`: normalizing the fibre form of a
  chart in which a function is a constant plus half its vertical Hessian.
* `TauCeti.exists_normalized_morseBott_chart_of_contDiffOn`: the normalized Morse–Bott lemma in
  product coordinates.

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

/-- **The vertical Hessians are locally congruent.** If `g` is `C^{n+2}` near `(a, 0)` and its
vertical Hessian `D²(g (a, ·))(0)` is invertible, then near `a` every vertical Hessian
`D²(g (b, ·))(0)` is congruent to the one at `a` by a `C^n` family of invertible operators `R b`,
equal to the identity at `a` and with `C^n` inverses. -/
theorem exists_congruence_fderiv_fderiv_slice_right {g : P × F → ℝ}
    (hg : ∀ᶠ z in 𝓝 (a, 0), ContDiffAt ℝ (n + 2) g z)
    (hHa : (fderiv ℝ (fderiv ℝ (fun v ↦ g (a, v))) 0).IsInvertible) :
    ∃ (R : P → F →L[ℝ] F) (U : Set P), IsOpen U ∧ a ∈ U ∧ R a = 1 ∧
      (∀ b ∈ U, (R b).IsInvertible) ∧ ContDiffOn ℝ n R U ∧
      ContDiffOn ℝ n (fun b ↦ (R b).inverse) U ∧
      ∀ b ∈ U, ∀ w w', fderiv ℝ (fderiv ℝ (fun v ↦ g (a, v))) 0 (R b w) (R b w') =
        fderiv ℝ (fderiv ℝ (fun v ↦ g (b, v))) 0 w w' := by
  -- Extend `g` from a neighbourhood of `(a, 0)` to a globally `C^{n+2}` function `G`. The
  -- vertical Hessians of `G` form a globally `C^n` family of symmetric forms.
  obtain ⟨O, hOsub, hO, haO⟩ := _root_.mem_nhds_iff.mp hg
  have hgO : ContDiffOn ℝ (n + 2) g O := fun z hz ↦ (hOsub hz).contDiffWithinAt
  obtain ⟨G, hG, -, hGg⟩ := hgO.exists_contDiff_eventuallyEq_of_finiteDimensional (hO.mem_nhds haO)
  have hG2 : ContDiff ℝ (n + 2) G := hG
  let B : P → F →L[ℝ] F →L[ℝ] ℝ := fun b ↦ fderiv ℝ (fderiv ℝ (fun v ↦ G (b, v))) 0
  have hB : ContDiff ℝ n B :=
    contDiff_iff_contDiffAt.mpr fun _ ↦ contDiffAt_fderiv_fderiv_slice_right hG2.contDiffAt
  have hBsymm (b : P) (w w' : F) : B b w w' = B b w' w :=
    (((hG2.comp (contDiff_const.prodMk contDiff_id)).contDiffAt).of_le
      le_add_self).isSymmSndFDerivAt (by simp) w w'
  -- Near `a`, they are the vertical Hessians of `g`.
  have hBg : ∀ᶠ b in 𝓝 a, B b = fderiv ℝ (fderiv ℝ (fun v ↦ g (b, v))) 0 := by
    obtain ⟨U₀, V₀, hU₀, haU₀, hV₀, h0V₀, hUV₀⟩ := mem_nhds_prod_iff'.mp hGg
    filter_upwards [hU₀.mem_nhds haU₀] with b hb
    have hslice : (fun v ↦ G (b, v)) =ᶠ[𝓝 0] fun v ↦ g (b, v) :=
      Filter.mem_of_superset (hV₀.mem_nhds h0V₀) fun v hv ↦ hUV₀ (mk_mem_prod hb hv)
    exact hslice.fderiv.fderiv_eq
  obtain ⟨A, hA⟩ := hHa
  obtain ⟨R, W, hW, haW, hRa, hR, hRB⟩ :=
    exists_congruence_of_symmetric_family hB hBsymm A (hA.trans hBg.self_of_nhds.symm)
  -- The operators are invertible near `a`, where they are close to the identity.
  have hRinv : ∀ᶠ b in 𝓝 a, (R b).IsInvertible :=
    (hR.continuousOn.continuousAt (hW.mem_nhds haW)).eventually
      (hRa ▸ ⟨ContinuousLinearEquiv.refl ℝ F, rfl⟩ : (R a).IsInvertible).eventually_nhds
  obtain ⟨U, hUsub, hU, haU⟩ :=
    _root_.mem_nhds_iff.mp (Filter.inter_mem (hW.mem_nhds haW) (hBg.and hRinv))
  refine ⟨R, U, hU, haU, hRa, fun b hb ↦ (hUsub hb).2.2, hR.mono fun b hb ↦ (hUsub hb).1,
    fun b hb ↦ ((hUsub hb).2.2.contDiffAt_map_inverse.comp b
      (hR.contDiffAt (hW.mem_nhds (hUsub hb).1))).contDiffWithinAt, fun b hb w w' ↦ ?_⟩
  rw [← hA, ContinuousLinearEquiv.coe_coe, hRB b (hUsub hb).1, (hUsub hb).2.1]

/-- **Normalizing the fibre form of a Morse–Bott chart.** Let `ψ` be a `C^n` chart of `P × F` with
product source `U ×ˢ V`, preserving the base coordinate in both directions and fixing the zero
section, in which `g z = c + ½ D²(g (z.1, ·))(0) ((ψ z).2, (ψ z).2)`, where `g` is `C^{n+2}` near
`(a, 0)` and its vertical Hessian at `a` is invertible. Then a base-dependent linear change of the
fibre coordinates turns `ψ` into a `C^n` chart `ψ'` onto an open subset of `P × ℝᵐ`, `m = dim F`,
with the same properties over a smaller base `U' ∋ a`, in which

`g z = c - Σ_{i < λ} (ψ' z).2ᵢ² + Σ_{i ≥ λ} (ψ' z).2ᵢ²`,

where `λ` is the Morse index at `0` of the fibre restriction `v ↦ g (a, v)`. -/
theorem _root_.OpenPartialHomeomorph.exists_normalized_morseBott_chart
    (ψ : OpenPartialHomeomorph (P × F) (P × F)) {U : Set P} {V : Set F} (hU : IsOpen U)
    (haU : a ∈ U) (hsource : ψ.source = U ×ˢ V) (hψfst : ∀ z, (ψ z).1 = z.1)
    (hψ0 : ∀ b, ψ (b, 0) = (b, 0)) (hψsymm : ∀ z ∈ ψ.target, (ψ.symm z).1 = z.1)
    (hψ : ContDiffOn ℝ n ψ ψ.source) (hψinv : ContDiffOn ℝ n ψ.symm ψ.target)
    {g : P × F → ℝ} {c : ℝ} (hg : ∀ᶠ z in 𝓝 (a, 0), ContDiffAt ℝ (n + 2) g z)
    (hHa : (fderiv ℝ (fderiv ℝ (fun v ↦ g (a, v))) 0).IsInvertible)
    (hψg : ∀ z ∈ ψ.source,
      g z = c + (2 : ℝ)⁻¹ * fderiv ℝ (fderiv ℝ (fun v ↦ g (z.1, v))) 0 (ψ z).2 (ψ z).2) :
    ∃ (ψ' : OpenPartialHomeomorph (P × F) (P × EuclideanSpace ℝ (Fin (Module.finrank ℝ F))))
      (U' : Set P), IsOpen U' ∧ a ∈ U' ∧ U' ⊆ U ∧ ψ'.source = U' ×ˢ V ∧
      (∀ z, (ψ' z).1 = z.1) ∧ (∀ b, ψ' (b, 0) = (b, 0)) ∧
      (∀ z ∈ ψ'.target, (ψ'.symm z).1 = z.1) ∧
      ContDiffOn ℝ n ψ' ψ'.source ∧ ContDiffOn ℝ n ψ'.symm ψ'.target ∧
      ∀ z ∈ ψ'.source, g z = c + ∑ i,
        (if i.val < morseIndex (fun v ↦ g (a, v)) 0 then -1 else 1) * (ψ' z).2 i ^ 2 := by
  set m := Module.finrank ℝ F
  -- Step 1: the vertical Hessians near `a` are congruent to the one at `a`.
  obtain ⟨R, U₁, hU₁, haU₁, -, hRinv, hR, hRi, hRH⟩ :=
    exists_congruence_fderiv_fderiv_slice_right hg hHa
  set U' := U ∩ U₁ with hU'_def
  have hU' : IsOpen U' := hU.inter hU₁
  -- Step 2: Sylvester coordinates `T` for the vertical Hessian at `a`.
  obtain ⟨T, hT⟩ := exists_continuousLinearEquiv_inv_two_mul_fderiv_fderiv_eq_sum
    (f := fun v ↦ g (a, v))
    ((hg.self_of_nhds.of_le le_add_self).comp 0 (contDiffAt_const.prodMk contDiffAt_id)) hHa
  -- Step 3: the fibrewise linear chart `(b, v) ↦ (b, T (R b v))` over `U'`.
  have hΦ : ContDiffOn ℝ n (fun z : P × F ↦ (z.1, T (R z.1 z.2))) (U' ×ˢ univ) :=
    contDiffOn_fst.prodMk (T.contDiff.comp_contDiffOn
      (((hR.mono inter_subset_right).comp (contDiffOn_fst (s := U' ×ˢ univ))
        fun _ hz ↦ hz.1).clm_apply contDiffOn_snd))
  have hΦinv : ContDiffOn ℝ n
      (fun y : P × EuclideanSpace ℝ (Fin m) ↦ (y.1, (R y.1).inverse (T.symm y.2)))
      (U' ×ˢ univ) :=
    contDiffOn_fst.prodMk (((hRi.mono inter_subset_right).comp
      (contDiffOn_fst (s := U' ×ˢ (univ : Set (EuclideanSpace ℝ (Fin m)))))
      fun _ hy ↦ hy.1).clm_apply (T.symm.contDiff.comp_contDiffOn contDiffOn_snd))
  let Φ : OpenPartialHomeomorph (P × F) (P × EuclideanSpace ℝ (Fin m)) :=
    { toFun := fun z ↦ (z.1, T (R z.1 z.2))
      invFun := fun y ↦ (y.1, (R y.1).inverse (T.symm y.2))
      source := U' ×ˢ univ
      target := U' ×ˢ univ
      map_source' := fun _ hz ↦ ⟨hz.1, mem_univ _⟩
      map_target' := fun _ hy ↦ ⟨hy.1, mem_univ _⟩
      left_inv' := fun z hz ↦ by simp [(hRinv z.1 hz.1.2).inverse_apply_self]
      right_inv' := fun y hy ↦ by simp [(hRinv y.1 hy.1.2).self_apply_inverse]
      open_source := hU'.prod isOpen_univ
      open_target := hU'.prod isOpen_univ
      continuousOn_toFun := hΦ.continuousOn
      continuousOn_invFun := hΦinv.continuousOn }
  -- Step 4: the normalized chart is `ψ` followed by `Φ`.
  refine ⟨ψ.trans Φ, U', hU', ⟨haU, haU₁⟩, inter_subset_left, ?_, fun z ↦ hψfst z,
    fun b ↦ ?_, fun y hy ↦ hψsymm _ hy.2, ?_, ?_, ?_⟩
  · ext z
    simp only [OpenPartialHomeomorph.trans_source, hsource, mem_inter_iff, mem_preimage,
      mem_prod, mem_univ, and_true, Φ, hψfst, hU'_def]
    tauto
  · simp [Φ, hψ0]
  · exact hΦ.comp (hψ.mono fun _ hz ↦ hz.1) fun _ hz ↦ hz.2
  · exact hψinv.comp (hΦinv.mono fun _ hy ↦ hy.1) fun _ hy ↦ hy.2
  · intro z hz
    have hz₁ : z.1 ∈ U' := hψfst z ▸ (hz.2 : ψ z ∈ U' ×ˢ univ).1
    have hψ'z : ((ψ.trans Φ) z).2 = T (R z.1 (ψ z).2) := by
      simp [Φ, hψfst]
    rw [hψg z hz.1, ← hRH z.1 hz₁.2, hT, hψ'z]

/-- **The normalized Morse–Bott lemma in product coordinates.** Under the hypotheses of
`TauCeti.exists_morseBott_chart_of_contDiffOn`, there is a `C^n` chart `ψ` from a product
neighbourhood `U ×ˢ V ⊆ W` of `(a, 0)` onto an open subset of `P × ℝᵐ`, `m = dim F`, preserving
the base parameter in both directions and fixing the zero section, in which

`f z = f (a, 0) - Σ_{i < λ} (ψ z).2ᵢ² + Σ_{i ≥ λ} (ψ z).2ᵢ²`

on the whole source, where `λ` is the Morse index of `f` at `(a, 0)`. -/
theorem exists_normalized_morseBott_chart_of_contDiffOn (hW : W ∈ 𝓝 (a, 0))
    (hf : ContDiffOn ℝ (n + 2) f W) (hcrit : ∀ᶠ b in 𝓝 a, fderiv ℝ f (b, 0) = 0)
    (hker : (fderiv ℝ (fderiv ℝ f) (a, 0)).ker ≤ LinearMap.range (LinearMap.inl ℝ P F))
    (hn : n ≠ 0) :
    ∃ (ψ : OpenPartialHomeomorph (P × F) (P × EuclideanSpace ℝ (Fin (Module.finrank ℝ F))))
      (U : Set P) (V : Set F),
      IsOpen U ∧ IsOpen V ∧ a ∈ U ∧ (0 : F) ∈ V ∧ ψ.source = U ×ˢ V ∧ U ×ˢ V ⊆ W ∧
      (∀ z, (ψ z).1 = z.1) ∧ (∀ b, ψ (b, 0) = (b, 0)) ∧
      (∀ z ∈ ψ.target, (ψ.symm z).1 = z.1) ∧
      ContDiffOn ℝ n ψ ψ.source ∧ ContDiffOn ℝ n ψ.symm ψ.target ∧
      ∀ z ∈ ψ.source, f z = f (a, 0) + ∑ i,
        (if i.val < morseIndex f (a, 0) then -1 else 1) * (ψ z).2 i ^ 2 := by
  obtain ⟨ψ, U, V, hU, hV, haU, h0V, hsource, hUVW, hψfst, hψ0, hψsymm, hψ, hψinv, -, hinv,
    hψf⟩ := exists_morseBott_chart_of_contDiffOn hW hf hcrit hker hn
  -- `f` is `C^{n+2}` at every point of the open set `U ×ˢ V ⊆ W`.
  have hfUV : ∀ z ∈ U ×ˢ V, ContDiffAt ℝ (n + 2) f z := fun z hz ↦
    hf.contDiffAt (Filter.mem_of_superset ((hU.prod hV).mem_nhds hz) hUVW)
  have ha0 : ((a, 0) : P × F) ∈ U ×ˢ V := mk_mem_prod haU h0V
  obtain ⟨ψ', U', hU', haU', hU'U, hsource', hψ'fst, hψ'0, hψ'symm, hψ', hψ'inv, hψ'f⟩ :=
    ψ.exists_normalized_morseBott_chart hU haU hsource hψfst hψ0 hψsymm hψ hψinv
      (Filter.mem_of_superset ((hU.prod hV).mem_nhds ha0) hfUV) (hinv a haU) hψf
  rw [morseIndex_slice_right ((hfUV _ ha0).of_le le_add_self) hcrit] at hψ'f
  exact ⟨ψ', U', V, hU', hV, haU', h0V, hsource', (prod_mono hU'U subset_rfl).trans hUVW,
    hψ'fst, hψ'0, hψ'symm, hψ', hψ'inv, hψ'f⟩

end TauCeti
