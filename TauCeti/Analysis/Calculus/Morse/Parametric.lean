/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.NormalForm
import TauCeti.Analysis.Calculus.Bilinear
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.InverseFunctionTheorem

/-!
# The parametric Morse lemma in a trivial bundle

A smooth family of functions with a critical zero section and a strongly nondegenerate vertical
Hessian admits local coordinates preserving the base parameter. The coordinate change fixes the
zero section and transforms the function into its vertical Hessian quadratic form. Both the
coordinate change and its local inverse are jointly smooth in base and fiber.

The construction follows the operator-square-root proof of the Morse--Palais lemma, as formalized
in `TauCeti.Analysis.Calculus.Morse.NormalForm`: apply its varying-reference congruence theorem to
the integral average of the vertical Hessian, then invert the map `(b, v) ↦ (b, R (b, v) v)`.
The Hessian convention is the second derivative itself, so the quadratic formula has a factor
`1 / 2`. This is a local theorem on a product of Banach spaces; no bundle gluing is asserted.

In finite dimensions the function need only be defined near the zero section:
`TauCeti.exists_parametric_morse_chart_of_contDiffOn` assumes smoothness on an open set `W`, and
criticality and nondegeneracy of the fibres at the points of the zero section in `W`. It cuts the
function off to a globally smooth one and restricts the chart to a ball where the two agree. Its
normal form is stated through the new chart alone: the function read in the chart is, on each
fibre, its own vertical Hessian quadratic form, and these vertical Hessians are invertible.

## References

* R. S. Palais, *The Morse lemma for Banach spaces*, Bull. Amer. Math. Soc. **75** (1969),
  968--971.
* R. S. Palais, *Morse theory on Hilbert manifolds*, Topology **2** (1963), 299--340, Section 2.
-/

public section

noncomputable section

open Filter Set Topology
open scoped ContDiff

namespace TauCeti

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : P × E → ℝ} {a : P} {n : ℕ∞}

/-- **Parametric Morse normal form.** A jointly `C^{n+2}` family with a critical zero section
near `a` and invertible vertical Hessian at `(a, 0)` has a jointly `C^n` fiber coordinate change
on a product neighborhood. It fixes the zero section, preserves the parameter, and has identity
derivative at `(a, 0)`. The reference quadratic form is the vertical Hessian at each `(b, 0)`.
The base space need not be complete for this forward coordinate construction. -/
theorem exists_parametric_morse_normal_form (hf : ContDiff ℝ (n + 2) f)
    (hcrit : ∀ᶠ b in 𝓝 a, fderiv ℝ (fun v ↦ f (b, v)) 0 = 0)
    (hH : (fderiv ℝ (fderiv ℝ (fun v ↦ f (a, v))) 0).IsInvertible) (hn : n ≠ 0) :
    ∃ (Φ : P × E → P × E) (U : Set P) (V : Set E),
      IsOpen U ∧ IsOpen V ∧ a ∈ U ∧ (0 : E) ∈ V ∧
      (∀ z, (Φ z).1 = z.1) ∧ (∀ b, Φ (b, 0) = (b, 0)) ∧
      ContDiffOn ℝ n Φ (U ×ˢ V) ∧
      HasFDerivAt Φ (ContinuousLinearMap.id ℝ (P × E)) (a, 0) ∧
      ∀ z ∈ U ×ˢ V,
        f z = f (z.1, 0) + (2 : ℝ)⁻¹ *
          fderiv ℝ (fderiv ℝ (fun v ↦ f (z.1, v))) 0 (Φ z).2 (Φ z).2 := by
  have hf₂ : ContDiff ℝ 2 f := hf.of_le le_add_self
  have hslice (b : P) : ContDiff ℝ 2 (fun v ↦ f (b, v)) :=
    hf₂.comp (contDiff_const.prodMk contDiff_id)
  let B : P × E → E →L[ℝ] E →L[ℝ] ℝ :=
    fun z ↦ hessianAverage (fun v ↦ f (z.1, v)) 0 z.2
  obtain ⟨R, U, V, hU, hV, haU, h0V, hR0, hR, _, _, hReq⟩ :=
    exists_parametric_congruence_of_symmetric_family
      (B := B) (a := a) (contDiff_hessianAverage_param hf 0)
      (fun z w w' ↦ hessianAverage_symm (hslice z.1) 0 z.2 w w')
      (by simpa only [B, hessianAverage_zero] using hH)
  obtain ⟨W, hWsub, hW, haW⟩ := mem_nhds_iff.mp hcrit
  let Φ : P × E → P × E := fun z ↦ (z.1, R z z.2)
  have hΦ : ContDiffOn ℝ n Φ (U ×ˢ V) :=
    contDiffOn_fst.prodMk (hR.clm_apply contDiffOn_snd)
  have hRa : ContDiffAt ℝ n R (a, 0) :=
    (hR (a, 0) ⟨haU, h0V⟩).contDiffAt ((hU.prod hV).mem_nhds ⟨haU, h0V⟩)
  have hd : HasFDerivAt (fun z : P × E ↦ R z z.2)
      ((R (a, 0)).comp (ContinuousLinearMap.snd ℝ P E) +
        (fderiv ℝ R (a, 0)).flip 0) (a, 0) :=
    (hRa.differentiableAt (by simpa using hn)).hasFDerivAt.clm_apply
      hasFDerivAt_snd
  have hΦd : HasFDerivAt Φ (ContinuousLinearMap.id ℝ (P × E)) (a, 0) := by
    convert hasFDerivAt_fst.prodMk hd using 1
    ext z <;> simp [hR0 a haU]
  refine ⟨Φ, U ∩ W, V, hU.inter hW, hV, ⟨haU, haW⟩, h0V,
    fun _ ↦ rfl, fun _ ↦ by simp [Φ], hΦ.mono (by intro z hz; exact ⟨hz.1.1, hz.2⟩),
    hΦd, ?_⟩
  intro z hz
  have ht := map_add_eq_add_hessianAverage (hslice z.1) 0 z.2
  have hc := hReq z ⟨hz.1.1, hz.2⟩ z.2 z.2
  simp only [B, hessianAverage_zero] at hc
  have hzcrit : fderiv ℝ (fun v ↦ f (z.1, v)) 0 = 0 := hWsub hz.1.2
  simpa only [zero_add, hzcrit, zero_apply, add_zero, smul_eq_mul, ← hc, Φ,
    Prod.mk.eta] using ht

/-- **The parametric Morse lemma, as a local chart.** The chart has a product source containing
`(a, 0)`, preserves the base parameter in both directions, and fixes the zero section. Its
quadratic equation uses the vertical Hessian on that same zero section. The base and the fiber
are Banach spaces, so the ordinary inverse function theorem applies to their product. -/
theorem exists_parametric_morse_chart [CompleteSpace P] (hf : ContDiff ℝ (n + 2) f)
    (hcrit : ∀ᶠ b in 𝓝 a, fderiv ℝ (fun v ↦ f (b, v)) 0 = 0)
    (hH : (fderiv ℝ (fderiv ℝ (fun v ↦ f (a, v))) 0).IsInvertible) (hn : n ≠ 0) :
    ∃ (ψ : OpenPartialHomeomorph (P × E) (P × E)) (U : Set P) (V : Set E),
      IsOpen U ∧ IsOpen V ∧ a ∈ U ∧ (0 : E) ∈ V ∧ ψ.source = U ×ˢ V ∧
      (∀ z, (ψ z).1 = z.1) ∧ (∀ b, ψ (b, 0) = (b, 0)) ∧
      (∀ z ∈ ψ.target, (ψ.symm z).1 = z.1) ∧
      ContDiffOn ℝ n ψ ψ.source ∧ ContDiffOn ℝ n ψ.symm ψ.target ∧
      ∀ z ∈ ψ.source,
        f z = f (z.1, 0) + (2 : ℝ)⁻¹ *
          fderiv ℝ (fderiv ℝ (fun v ↦ f (z.1, v))) 0 (ψ z).2 (ψ z).2 := by
  obtain ⟨Φ, U, V, hU, hV, haU, h0V, hΦfst, hΦ0, hΦ, hΦd, hΦeq⟩ :=
    exists_parametric_morse_normal_form hf hcrit hH hn
  have haUV : (a, (0 : E)) ∈ U ×ˢ V := ⟨haU, h0V⟩
  have hUV : IsOpen (U ×ˢ V) := hU.prod hV
  have hn' : 1 ≤ (n : ℕ∞ω) :=
    ENat.one_le_iff_ne_zero_withTop.2 (by simpa using hn)
  obtain ⟨Θ, hΘ, haΘ, hΘsub, hΘsymm⟩ :=
    ContDiffOn.exists_openPartialHomeomorph hΦ hUV haUV hn'
      (e := ContinuousLinearEquiv.refl ℝ (P × E)) hΦd.fderiv.symm
  -- Choose a product source to retain a common fiber neighborhood.
  obtain ⟨W, Z, hW, haW, hZ, h0Z, hWZ⟩ :=
    mem_nhds_prod_iff'.mp (Θ.open_source.mem_nhds haΘ)
  let ψ := Θ.restrOpen (W ×ˢ Z) (hW.prod hZ)
  have hsource : ψ.source = W ×ˢ Z := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    apply inter_eq_right.mpr
    exact hWZ
  have hψ : (ψ : P × E → P × E) = Φ := by
    simpa only [ψ, OpenPartialHomeomorph.coe_restrOpen] using hΘ
  refine ⟨ψ, W, Z, hW, hZ, haW, h0Z, hsource, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hψ] using hΦfst
  · simpa only [hψ] using hΦ0
  · intro z hz
    have hi := congrArg Prod.fst (ψ.right_inv hz)
    rwa [hψ, hΦfst] at hi
  · rw [hψ]
    exact hΦ.mono (fun z hz ↦ hΘsub (hWZ (hsource ▸ hz)))
  · exact hΘsymm.mono inter_subset_left
  · intro z hz
    simpa only [hψ] using hΦeq z (hΘsub (hWZ (hsource ▸ hz)))

section Local

variable [FiniteDimensional ℝ P]

omit [NormedSpace ℝ P] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ P] in
/-- Projecting to the zero section does not leave a ball about a point of the zero section. -/
private theorem mk_fst_zero_mem_ball {z : P × E} {r : ℝ} (hz : z ∈ Metric.ball (a, 0) r) :
    (z.1, (0 : E)) ∈ Metric.ball (a, 0) r := by
  simp only [Metric.mem_ball, Prod.dist_eq, dist_self] at hz ⊢
  exact (max_le_max le_rfl dist_nonneg).trans_lt hz

omit [CompleteSpace E] in
/-- The cutoff step of `TauCeti.exists_parametric_morse_chart_of_contDiffOn`: for `f` defined
near the zero section, the parametric Morse chart of a cut-off copy of `f` gives the normal form
of `f` itself on a ball about `(a, 0)`, with the vertical Hessians of `f`. -/
private theorem exists_parametric_morse_chart_ball [FiniteDimensional ℝ E] {W : Set (P × E)}
    (hW : IsOpen W) (haW : (a, 0) ∈ W) (hf : ContDiffOn ℝ (n + 2) f W)
    (hcrit : ∀ b, (b, 0) ∈ W → fderiv ℝ (fun v ↦ f (b, v)) 0 = 0)
    (hH : (fderiv ℝ (fderiv ℝ fun v ↦ f (a, v)) 0).IsInvertible) (hn : n ≠ 0) :
    ∃ (θ : OpenPartialHomeomorph (P × E) (P × E)) (U : Set P) (V : Set E) (r : ℝ),
      0 < r ∧ Metric.ball (a, 0) r ⊆ W ∧ a ∈ U ∧ (0 : E) ∈ V ∧ θ.source = U ×ˢ V ∧
      (∀ z, (θ z).1 = z.1) ∧ (∀ b, θ (b, 0) = (b, 0)) ∧
      ContDiffOn ℝ n θ θ.source ∧ ContDiffOn ℝ n θ.symm θ.target ∧
      ∀ z ∈ θ.source, z ∈ Metric.ball (a, 0) r → f z = f (z.1, 0) + (2 : ℝ)⁻¹ *
        fderiv ℝ (fderiv ℝ (fun v ↦ f (z.1, v))) 0 (θ z).2 (θ z).2 := by
  -- Cut `f` off to a globally `C^{n+2}` function `g`, equal to `f` on a ball `B` about `(a, 0)`.
  obtain ⟨χ, hχ, -, hχ1, -, hχW⟩ :=
    isCompact_singleton.exists_contDiff_cutoff_eventuallyEq_one hW (singleton_subset_iff.2 haW)
  set g : P × E → ℝ := fun z ↦ χ z • f z
  have hg : ContDiff ℝ (n + 2) g :=
    hf.contDiff_smul_of_tsupport_subset hW (hχ.of_le (WithTop.coe_le_coe.2 le_top)).contDiffOn hχW
  obtain ⟨r, hr, hrW⟩ := Metric.eventually_nhds_iff_ball.1
    ((hχ1 (a, 0) rfl).and (hW.mem_nhds haW))
  set B := Metric.ball ((a, 0) : P × E) r
  have hgf : ∀ z ∈ B, g z = f z := fun z hz ↦ by simp [g, (hrW z hz).1]
  have hBW : B ⊆ W := fun z hz ↦ (hrW z hz).2
  -- Near a point `(b, 0)` of `B` the fibres of `g` and `f` agree, with their vertical Hessians.
  have hloc : ∀ b, (b, (0 : E)) ∈ B → (fun v ↦ g (b, v)) =ᶠ[𝓝 0] fun v ↦ f (b, v) := by
    intro b hb
    have hcont : Continuous fun v : E ↦ (b, v) := continuous_const.prodMk continuous_id
    filter_upwards [hcont.continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hb)]
      with v hv using hgf _ hv
  have hcrit' : ∀ᶠ b in 𝓝 a, fderiv ℝ (fun v ↦ g (b, v)) 0 = 0 := by
    have hcont : Continuous fun b : P ↦ (b, (0 : E)) := continuous_id.prodMk continuous_const
    filter_upwards [hcont.continuousAt.preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))] with b hb
    rw [(hloc b hb).fderiv_eq]
    exact hcrit b (hBW hb)
  obtain ⟨θ, U, V, -, -, haU, h0V, hθs, hθfst, hθ0, -, hθ, hθsymm, hθeq⟩ :=
    exists_parametric_morse_chart hg hcrit'
      (by rw [(hloc a (Metric.mem_ball_self hr)).fderiv.fderiv_eq]; exact hH) hn
  refine ⟨θ, U, V, r, hr, hBW, haU, h0V, hθs, hθfst, hθ0, hθ, hθsymm, fun z hz hzB ↦ ?_⟩
  have hz0 : (z.1, (0 : E)) ∈ B := mk_fst_zero_mem_ball hzB
  rw [← hgf z hzB, ← hgf _ hz0, ← (hloc z.1 hz0).fderiv.fderiv_eq]
  exact hθeq z hz

omit [CompleteSpace E] in
/-- **The parametric Morse lemma for a function defined near the zero section.** Let `f` be
`C^{n+2}` on an open set `W` of `P × E` containing `(a, 0)`, such that at every point `(b, 0)` of
`W` the function `v ↦ f (b, v)` has a critical point at `0` with invertible Hessian. Then there is
a `C^n` chart `ψ` near `(a, 0)`, inside `W`, which preserves the first coordinate and fixes the
zero section, and in which `f` is its vertical Hessian quadratic form: at every point `z` of the
target, `f (ψ.symm z)` is the value at `(z.1, 0)` plus half the vertical Hessian of `f ∘ ψ.symm`
at `(z.1, 0)` evaluated on `z.2`. These vertical Hessians are invertible. -/
theorem exists_parametric_morse_chart_of_contDiffOn [FiniteDimensional ℝ E] {W : Set (P × E)}
    (hW : IsOpen W) (haW : (a, 0) ∈ W) (hf : ContDiffOn ℝ (n + 2) f W)
    (hcrit : ∀ b, (b, 0) ∈ W → fderiv ℝ (fun v ↦ f (b, v)) 0 = 0)
    (hH : ∀ b, (b, 0) ∈ W → (fderiv ℝ (fderiv ℝ fun v ↦ f (b, v)) 0).IsInvertible)
    (hn : n ≠ 0) :
    ∃ ψ : OpenPartialHomeomorph (P × E) (P × E),
      (a, 0) ∈ ψ.source ∧ ψ.source ⊆ W ∧ (∀ z ∈ ψ.source, (ψ z).1 = z.1) ∧
      (∀ z ∈ ψ.source, (z.1, 0) ∈ ψ.source ∧ ψ (z.1, 0) = (z.1, 0)) ∧
      ContDiffOn ℝ n ψ ψ.source ∧ ContDiffOn ℝ n ψ.symm ψ.target ∧
      (∀ z ∈ ψ.target, f (ψ.symm z) = f (z.1, 0) + 2⁻¹ *
        fderiv ℝ (fderiv ℝ fun v ↦ f (ψ.symm (z.1, v))) 0 z.2 z.2) ∧
      ∀ z ∈ ψ.target, (fderiv ℝ (fderiv ℝ fun v ↦ f (ψ.symm (z.1, v))) 0).IsInvertible := by
  obtain ⟨θ, U, V, r, hr, hBW, haU, h0V, hθs, hθfst, hθ0, hθ, hθsymm, hθeq⟩ :=
    exists_parametric_morse_chart_ball hW haW hf hcrit (hH a haW) hn
  set B := Metric.ball ((a, 0) : P × E) r
  set Q : P → E →L[ℝ] E →L[ℝ] ℝ := fun b ↦ fderiv ℝ (fderiv ℝ fun v ↦ f (b, v)) 0
  -- Restrict the chart to the ball on which it is a normal form for `f`.
  set ψ := θ.restrOpen B Metric.isOpen_ball
  have hψs : ψ.source = U ×ˢ V ∩ B := by simp [ψ, hθs]
  have hzero : ∀ z ∈ ψ.source, (z.1, (0 : E)) ∈ ψ.source ∧ ψ (z.1, 0) = (z.1, 0) := by
    intro z hz
    rw [hψs] at hz ⊢
    exact ⟨⟨⟨hz.1.1, h0V⟩, mk_fst_zero_mem_ball hz.2⟩, by simpa [ψ] using hθ0 z.1⟩
  -- A point of the target comes from a point of the source with the same first coordinate.
  have htarget : ∀ z ∈ ψ.target, z ∈ θ.target ∧ ψ.symm z ∈ ψ.source ∧ (ψ.symm z).1 = z.1 := by
    intro z hz
    have hzt : z ∈ θ.target := by simpa [ψ] using hz.1
    refine ⟨hzt, ψ.map_target hz, ?_⟩
    have h := hθfst (θ.symm z)
    rw [θ.right_inv hzt] at h
    simpa [ψ] using h.symm
  -- The normal form, with the vertical Hessians `Q` of `f` before the change of coordinates.
  have hpre : ∀ z ∈ ψ.target, f (ψ.symm z) = f (z.1, 0) + 2⁻¹ * Q z.1 z.2 z.2 := by
    intro z hz
    obtain ⟨hzt, hy, hfst⟩ := htarget z hz
    rw [hψs] at hy
    have h := hθeq (ψ.symm z) (hθs ▸ hy.1) hy.2
    rw [hfst] at h
    simpa [ψ, θ.right_inv hzt] using h
  -- On each fibre, `f ∘ ψ.symm` is the quadratic form of `Q`, so `Q` is its vertical Hessian.
  have hquad : ∀ z ∈ ψ.target, fderiv ℝ (fderiv ℝ fun v ↦ f (ψ.symm (z.1, v))) 0 = Q z.1 := by
    intro z hz
    obtain ⟨-, hy, hfst⟩ := htarget z hz
    have h0 := hzero _ hy
    rw [hfst] at h0
    have h0t : (z.1, (0 : E)) ∈ ψ.target := h0.2 ▸ ψ.map_source h0.1
    have hcont : Continuous fun v : E ↦ (z.1, v) := continuous_const.prodMk continuous_id
    have hev : (fun v ↦ f (ψ.symm (z.1, v))) =ᶠ[𝓝 0]
        fun v ↦ f (z.1, 0) + ((2⁻¹ : ℝ) • Q z.1) v v := by
      filter_upwards [hcont.continuousAt.preimage_mem_nhds (ψ.open_target.mem_nhds h0t)]
        with v hv
      simpa using hpre _ hv
    -- `Q z.1` is symmetric, being the Hessian of a function `C²` near `0`.
    have hsymm : IsSymmSndFDerivAt ℝ (fun v ↦ f (z.1, v)) 0 :=
      ((hf.contDiffAt (hW.mem_nhds (hBW (hψs ▸ h0.1).2))).comp _
        (contDiffAt_const.prodMk contDiffAt_id)).isSymmSndFDerivAt (by simp)
    rw [hev.fderiv.fderiv_eq, ContinuousLinearMap.fderiv_fderiv_const_add_apply_self]
    ext w w'
    simp only [add_apply, ContinuousLinearMap.flip_apply, smul_apply, smul_eq_mul, Q, hsymm w' w]
    ring
  refine ⟨ψ, by rw [hψs]; exact ⟨⟨haU, h0V⟩, Metric.mem_ball_self hr⟩,
    fun z hz ↦ hBW (hψs ▸ hz).2, fun z _ ↦ hθfst z, hzero,
    hθ.mono fun z hz ↦ by simpa [hθs] using (hψs ▸ hz).1, hθsymm.mono fun z hz ↦ hz.1,
    fun z hz ↦ by rw [hquad z hz]; exact hpre z hz, fun z hz ↦ ?_⟩
  obtain ⟨-, hy, hfst⟩ := htarget z hz
  rw [hquad z hz]
  exact hH _ (hBW (hfst ▸ (hψs ▸ (hzero _ hy).1).2))

end Local

end TauCeti
