/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.NormalForm
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
  have hΦa : ContDiffAt ℝ n Φ (a, 0) :=
    (hΦ (a, 0) haUV).contDiffAt (hUV.mem_nhds haUV)
  have hΦd' : HasFDerivAt Φ
      (ContinuousLinearEquiv.refl ℝ (P × E) : (P × E) →L[ℝ] (P × E)) (a, 0) := by
    simpa using hΦd
  have hn' : (n : ℕ∞ω) ≠ 0 := by simpa using hn
  have hstrict := hΦa.hasStrictFDerivAt' hΦd' hn'
  let p := hΦa.toOpenPartialHomeomorph Φ hΦd' hn'
  -- Choose a product source to retain a common fiber neighborhood.
  have hgood : U ×ˢ V ∩ p.source ∈ 𝓝 (a, (0 : E)) :=
    Filter.inter_mem (hUV.mem_nhds haUV)
      (p.open_source.mem_nhds (hΦa.mem_toOpenPartialHomeomorph_source hΦd' hn'))
  obtain ⟨W, Z, hW, haW, hZ, h0Z, hWZ⟩ := mem_nhds_prod_iff'.mp hgood
  let ψ := p.restrOpen (W ×ˢ Z) (hW.prod hZ)
  have hsource : ψ.source = W ×ˢ Z := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    apply inter_eq_right.mpr
    exact fun z hz ↦ (hWZ hz).2
  have hψ : (ψ : P × E → P × E) = Φ := by
    simp only [ψ, OpenPartialHomeomorph.coe_restrOpen, p,
      ContDiffAt.toOpenPartialHomeomorph_coe]
  refine ⟨ψ, W, Z, hW, hZ, haW, h0Z, hsource, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hψ] using hΦfst
  · simpa only [hψ] using hΦ0
  · intro z hz
    have hi := congrArg Prod.fst (ψ.right_inv hz)
    rwa [hψ, hΦfst] at hi
  · rw [hψ]
    exact hΦ.mono (fun z hz ↦ (hWZ (hsource ▸ hz)).1)
  · intro z hz
    have hy : ψ.symm z ∈ W ×ˢ Z := hsource ▸ ψ.map_target hz
    have hforward : ContDiffAt ℝ n Φ (ψ.symm z) :=
      (hΦ (ψ.symm z) (hWZ hy).1).contDiffAt (hUV.mem_nhds (hWZ hy).1)
    exact (hstrict.contDiffAt_toOpenPartialHomeomorph_symm hz.1 hforward).contDiffWithinAt
  · intro z hz
    simpa only [hψ] using hΦeq z (hWZ (hsource ▸ hz)).1

end TauCeti
