/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.AsymptoticSum
public import TauCeti.Analysis.Pseudodifferential.Composition.Expansion
public import TauCeti.Analysis.Pseudodifferential.Sobolev
import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import TauCeti.Analysis.Sobolev.BesselPotential.Multiplication

/-!
# Local left parametrices and local elliptic regularity

Let `a` be a symbol of order `m` with values in `V →L[ℂ] W`, and let `b` be a symbol of order `-m`
with values in `W →L[ℂ] V` that is a *formal left inverse* of `a`: the terms
`sharpTerm b a k` of the composition expansion of `b # a` (`TauCeti.Symbol.sharpTerm`) have the
identity as asymptotic sum,

`1 ∼ ∑ₖ sharpTerm b a k`,

so that `1 - ∑_{k < N} sharpTerm b a k` has order `-N` for every `N`. For an elliptic symbol such a
`b` is obtained by solving the composition expansion for an inverse term by term and summing
the terms asymptotically.

The composition symbol `b # a` of `TauCeti.Symbol.sharp` is defined when the right factor has
compact spatial support, so `a` itself is localized: let `a'` be a symbol with compact spatial
support which agrees with `a` near the positions where a cutoff `f` is nonzero, for instance
`a' = χ a` with `χ = 1` near the support of `f`. This file shows that `f b` is then a left
parametrix of `a'` over the support of `f`, and deduces local elliptic regularity.

## Main results

* `TauCeti.Symbol.isSmoothing_ofSpatial_comp_sharp_sub`: **the local left parametrix**. For a
  smooth `f` depending only on the position, `(f b) # a' - f` is a smoothing symbol. The proof
  compares the composition expansion of `(f b) # a'` with that of `b # a`: the expansion terms
  are local in the right factor over the support of `f` (`TauCeti.Symbol.sharpTerm_congr_right`),
  and `f` passes through them (`TauCeti.Symbol.coefficient_sharpTerm_ofSpatial_comp`).
* `TauCeti.Symbol.exists_isSmoothing_quantizeSchwartzValue_ofSpatial_comp_eq`: the same statement
  for operators. If `f` has compact support, there is a smoothing symbol `r` with compact spatial
  support such that `Op(f b) (Op(a') u) = f u + Op(r) u` for every Schwartz function `u`.
* `TauCeti.Symbol.memSobolev_smulLeftCLM_of_memSobolev_quantizeSobolev`: **local elliptic
  regularity**. For a compactly supported smooth scalar cutoff `ψ`, a distribution `u ∈ H^t` with
  `Op(a') u ∈ H^s` satisfies `ψ u ∈ H^{s + m}`: near the support of `ψ`, `u` has `m` more
  derivatives than `Op(a') u`, whatever its initial finite Sobolev order `t`.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (4.1)–(4.11).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open MeasureTheory TemperedDistribution
open scoped ContDiff SchwartzMap BesselPotentialSpace Topology

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}

/-! ### The local left parametrix on symbols and on Schwartz functions -/

section Parametrix

variable {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] [CompleteSpace W] [NormedAddCommGroup U] [NormedSpace ℂ U] [CompleteSpace U]
  {a a' : Symbol n V W m} {b : Symbol n W V (-m)} {f : CoordinateSpace n → V →L[ℂ] U}

/-- **The local left parametrix.** Let `b` be a formal left inverse of the symbol `a`,
`1 ∼ ∑ₖ sharpTerm b a k`, and let `a'` be a symbol with compact spatial support that agrees with
`a` near every position where the smooth spatial factor `f` is nonzero. Then the composition
symbol `(f b) # a'` of `Op(f b) ∘ Op(a')` differs from `f` by a smoothing symbol. -/
theorem isSmoothing_ofSpatial_comp_sharp_sub
    (hb : IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k) (inclusion (by simp) (const (.id ℂ V)))
      (b.sharpTerm a))
    (hf : ContDiff ℝ ∞ f) (ha' : a'.HasCompactSpatialSupport)
    (h : ∀ x ∈ Function.support f, ∀ ξ, a'.coefficient =ᶠ[𝓝 (x, ξ)] a.coefficient) :
    (((ofSpatial f hf).comp b).sharp a' ha' -
      inclusion (by simp) (ofSpatial f hf)).IsSmoothing := by
  have hc : ∀ x ∉ Function.support f, ∀ ξ, ((ofSpatial f hf).comp b).coefficient (x, ξ) = 0 :=
    fun x hx ξ ↦ by simp [Function.notMem_support.1 hx]
  refine isSmoothing_iff.2 fun m'' ↦ ?_
  obtain ⟨N, hN⟩ : ∃ N : ℕ, -(N : ℝ) ≤ m'' := ⟨⌈-m''⌉₊, by linarith [Nat.le_ceil (-m'')]⟩
  obtain ⟨r, hr⟩ := isAsymptoticSum_iff.1 hb N
  -- The first `N` terms of the expansion of `(f b) # a'` sum to `f (∑_{k < N} sharpTerm b a k)`,
  -- which is `f - f r` with `r` of order `-N`.
  refine ⟨inclusion (by linarith) (((ofSpatial f hf).comp b).sharpRemainder a' ha' N) -
    inclusion (by linarith) ((ofSpatial f hf).comp r), ?_⟩
  funext ⟨x, ξ⟩
  have hr' := congrFun hr (x, ξ)
  simp only [Pi.sub_apply, Finset.sum_apply, coefficient_inclusion, coefficient_const] at hr'
  ext v
  simp only [coefficient_sub, coefficient_inclusion, coefficient_sharpRemainder, Pi.sub_apply,
    Finset.sum_apply, coefficient_comp, coefficient_ofSpatial, ← hr', sharpTerm_congr_right hc h,
    coefficient_sharpTerm_ofSpatial_comp, sub_apply, sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, map_sub, map_sum]
  abel

/-- **The local left parametrix on Schwartz functions.** Under the hypotheses of
`TauCeti.Symbol.isSmoothing_ofSpatial_comp_sharp_sub`, if moreover `f` has compact support, there
is a smoothing symbol `r` with compact spatial support such that
`Op(f b) (Op(a') u) = f u + Op(r) u` for every Schwartz function `u`. -/
theorem exists_isSmoothing_quantizeSchwartzValue_ofSpatial_comp_eq [CompleteSpace V]
    (hb : IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k) (inclusion (by simp) (const (.id ℂ V)))
      (b.sharpTerm a))
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (ha' : a'.HasCompactSpatialSupport)
    (h : ∀ x ∈ Function.support f, ∀ ξ, a'.coefficient =ᶠ[𝓝 (x, ξ)] a.coefficient) :
    ∃ r : Symbol n V U 0, r.IsSmoothing ∧ r.HasCompactSpatialSupport ∧
      ∀ (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n),
        quantizeSchwartzValue ((ofSpatial f hf).comp b).coefficient
          ((ha'.hasCompactSupport_quantizeSchwartzValue u).toSchwartzMap
            (a'.contDiff_quantizeSchwartzValue u)) x =
          f x (u x) + quantizeSchwartzValue r.coefficient u x := by
  have hfs : (ofSpatial f hf).HasCompactSpatialSupport :=
    (hasCompactSpatialSupport_ofSpatial_iff hf).2 hfc
  have hd := isSmoothing_ofSpatial_comp_sharp_sub hb hf ha' h
  have hds : (((ofSpatial f hf).comp b).sharp a' ha' -
      inclusion (by simp) (ofSpatial f hf)).HasCompactSpatialSupport :=
    ((hfs.comp_right b).sharp ha').sub (hfs.inclusion _)
  obtain ⟨r, hr⟩ := isSmoothing_iff.1 hd 0
  refine ⟨r, isSmoothing_iff.2 fun m'' ↦ (isSmoothing_iff.1 hd m'').imp fun _ h' ↦ h'.trans hr.symm,
    hds.of_coefficient_eq hr, fun u x ↦ ?_⟩
  have hcoef : (((ofSpatial f hf).comp b).sharp a' ha').coefficient =
      (ofSpatial f hf).coefficient + r.coefficient := by
    rw [hr, coefficient_sub, coefficient_inclusion]
    abel
  have hfx : (ofSpatial f hf).coefficient = fun p ↦ f p.1 := funext (coefficient_ofSpatial f hf)
  obtain ⟨C, -, hC⟩ := (ofSpatial f hf).exists_bound_coefficient_slice x
  obtain ⟨C', -, hC'⟩ := r.exists_bound_coefficient_slice x
  rw [← quantizeSchwartzValue_sharp_eq_quantizeSchwartzValue ha', hcoef,
    quantizeSchwartzValue_add_left
      ((ofSpatial f hf).continuous_coefficient_slice x).aestronglyMeasurable hC
      (r.continuous_coefficient_slice x).aestronglyMeasurable hC', hfx,
    quantizeSchwartzValue_comp_fst]

end Parametrix

/-! ### Local elliptic regularity -/

section Regularity

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  {a a' : Symbol n V W m} {b : Symbol n W V (-m)}

/-- An identity `Op(c) (Op(a') u) = ψ u + Op(r) u` on Schwartz functions `u` persists, as an
identity of tempered distributions, for the extensions of the quantizations to `u ∈ H^t`. -/
private theorem smulLeftCLM_toDistr_eq_of_forall {μ : ℝ} {c : Symbol n W V μ} {r : Symbol n V V 0}
    (ha' : a'.HasCompactSpatialSupport) (hc : c.HasCompactSpatialSupport)
    (hr : r.HasCompactSpatialSupport) {ψ : CoordinateSpace n → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ)
    (hid : ∀ (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n),
      quantizeSchwartzValue c.coefficient
          ((ha'.hasCompactSupport_quantizeSchwartzValue u).toSchwartzMap
            (a'.contDiff_quantizeSchwartzValue u)) x =
        ψ x • u x + quantizeSchwartzValue r.coefficient u x)
    {t : ℝ} (u : H^{t}(CoordinateSpace n, V)) :
    smulLeftCLM V ψ u.toDistr =
      (c.quantizeSobolev hc (t - m) (a'.quantizeSobolev ha' t u)).toDistr -
        (r.quantizeSobolev hr t u).toDistr := by
  have hψ' : ⇑(hψc.toSchwartzMap hψ) = ψ := funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  -- Both sides, followed by inclusions into `H^{t₀}`, `t₀ = min t (t - m - μ)`, are continuous
  -- linear maps on `H^t` which agree on Schwartz functions.
  have hT : (BesselPotentialSpace.inclusion (min_le_left t (t - m - μ))).comp
      (BesselPotentialSpace.smulLeftCLM t (hψc.toSchwartzMap hψ)) =
      (BesselPotentialSpace.inclusion (min_le_right t (t - m - μ))).comp
          ((c.quantizeSobolev hc (t - m)).comp (a'.quantizeSobolev ha' t)) -
        (BesselPotentialSpace.inclusion (by simp : min t (t - m - μ) ≤ t - 0)).comp
          (r.quantizeSobolev hr t) := by
    refine BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u₀ ↦
      BesselPotentialSpace.ext ?_
    set w := (ha'.hasCompactSupport_quantizeSchwartzValue u₀).toSchwartzMap
      (a'.contDiff_quantizeSchwartzValue u₀)
    have hw : (a'.quantizeSobolev ha' t (SchwartzMap.toBesselPotentialSpaceCLM t 2 u₀)).toDistr =
        (SchwartzMap.toBesselPotentialSpaceCLM (t - m) 2 w).toDistr := by
      ext φ
      simp [w]
    ext φ
    have hi₁ : Integrable fun x ↦ φ x • quantizeSchwartzValue c.coefficient w x :=
      (hc.integrable_quantizeSchwartzValue w).smul_of_top_right (φ.memLp ⊤)
    have hi₂ : Integrable fun x ↦ φ x • quantizeSchwartzValue r.coefficient u₀ x :=
      (hr.integrable_quantizeSchwartzValue u₀).smul_of_top_right (φ.memLp ⊤)
    simp only [sub_apply, ContinuousLinearMap.comp_apply, BesselPotentialSpace.toDistr_sub,
      BesselPotentialSpace.toDistr_inclusion, toDistr_quantizeSobolev_eq hc hc rfl hw,
      toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply,
      BesselPotentialSpace.toDistr_smulLeftCLM, hψ', smulLeftCLM_apply_apply,
      SchwartzMap.toDistr_toBesselPotentialSpaceCLM, SchwartzMap.coe_apply]
    rw [← integral_sub hi₁ hi₂]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    have hx : quantizeSchwartzValue c.coefficient w x =
        ψ x • u₀ x + quantizeSchwartzValue r.coefficient u₀ x := hid u₀ x
    simp [hx, SchwartzMap.smulLeftCLM_apply_apply (hψc.hasTemperateGrowth hψ), smul_smul,
      mul_comm]
  simpa [hψ'] using congrArg (fun T ↦ (T u).toDistr) hT

/-- **Local elliptic regularity.** Let `b` be a formal left inverse of the symbol `a` of order
`m`, `1 ∼ ∑ₖ sharpTerm b a k`, let `ψ` be a smooth compactly supported cutoff and let `a'` be a
symbol with compact spatial support that agrees with `a` near every position where `ψ` is nonzero.
If `u ∈ H^t` and `Op(a') u ∈ H^s`, then `ψ u ∈ H^{s + m}`. -/
theorem memSobolev_smulLeftCLM_of_memSobolev_quantizeSobolev
    (hb : IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k) (inclusion (by simp) (const (.id ℂ V)))
      (b.sharpTerm a))
    {ψ : CoordinateSpace n → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (ha' : a'.HasCompactSpatialSupport)
    (h : ∀ x ∈ Function.support ψ, ∀ ξ, a'.coefficient =ᶠ[𝓝 (x, ξ)] a.coefficient)
    {s t : ℝ} (u : H^{t}(CoordinateSpace n, V))
    (hu : (a'.quantizeSobolev ha' t u).toDistr.MemSobolev s 2) :
    (smulLeftCLM V ψ u.toDistr).MemSobolev (s + m) 2 := by
  set f : CoordinateSpace n → V →L[ℂ] V := fun x ↦ ψ x • ContinuousLinearMap.id ℂ V
  have hf : ContDiff ℝ ∞ f := hψ.smul contDiff_const
  have hsupp : Function.support f ⊆ Function.support ψ := fun x hx hψx ↦ hx (by simp [f, hψx])
  obtain ⟨r, hrs, hrc, hid⟩ := exists_isSmoothing_quantizeSchwartzValue_ofSpatial_comp_eq hb hf
    hψc.smul_right ha' fun x hx ↦ h x (hsupp hx)
  have hc : ((ofSpatial f hf).comp b).HasCompactSpatialSupport :=
    ((hasCompactSpatialSupport_ofSpatial_iff hf).2 hψc.smul_right).comp_right b
  -- `ψ u = Op(f b) (Op(a') u) - Op(r) u`. Here `Op(a') u ∈ H^{s₀}` with `s₀ = max s (t - m)`, so
  -- `Op(f b)` maps it to `H^{s₀ + m}`, and the smoothing symbol `r` maps `u` there too.
  have hv := smulLeftCLM_toDistr_eq_of_forall ha' hc hrc hψ hψc
    (fun u x ↦ by simpa [f] using hid u x) u
  have hv₀ : (a'.quantizeSobolev ha' t u).toDistr.MemSobolev (max s (t - m)) 2 := by
    rcases le_total s (t - m) with hst | hst
    · rw [max_eq_right hst]
      exact BesselPotentialSpace.memSobolev_toDistr _
    · rwa [max_eq_left hst]
  obtain ⟨r', hr'⟩ := isSmoothing_iff.1 hrs (t - max s (t - m) - m)
  have hrc' := hrc.of_coefficient_eq hr'
  rw [hv, toDistr_quantizeSobolev_eq hc hc rfl (hv₀.toBesselPotentialSpace_toDistr).symm,
    toDistr_quantizeSobolev_eq hrc hrc' hr'.symm rfl]
  refine (MemSobolev.sub ?_ ?_).mono (by linarith [le_max_left s (t - m)] :
    s + m ≤ max s (t - m) + m)
  · exact (BesselPotentialSpace.memSobolev_toDistr _).mono (by linarith)
  · exact (BesselPotentialSpace.memSobolev_toDistr _).mono (by linarith)

end Regularity

end Symbol

end TauCeti
