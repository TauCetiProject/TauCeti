/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Parametrix

/-!
# Interior elliptic regularity on Bessel-potential spaces

Let `a` be a symbol of order `m` on `ℝⁿ` with a *formal left parametrix*: a symbol `b` of order
`-m` whose formal composition with `a` is the identity,

`1 ∼ ∑ₖ sharpTerm b a k`,

meaning that `1 - ∑_{k < N} sharpTerm b a k` is a symbol of order `-N` for every `N`. This is a
left parametrix of `Op(a)` on the level of symbols, and ellipticity of `a` is what makes it exist:
every symbol elliptic above some radius has one
(`TauCeti.Symbol.IsEllipticAbove.exists_isAsymptoticSum_sharpTerm`). These symbol-level results
are in `TauCeti.Analysis.Pseudodifferential.Composition.Parametrix`.

To apply `Op(a)` to distributions of finite Sobolev order, localize: let `ψ` be a compactly
supported Schwartz function and `p` a symbol of order `m` with compact spatial support which
agrees with `a` at all positions near the support of `ψ`, for instance `φ(x) a(x, ξ)` for a
cutoff `φ` equal to `1` near the support of `ψ`. This file proves the **interior regularity**
of `Op(a)`:

* `TauCeti.Symbol.memSobolev_smulLeftCLM_of_memSobolev_quantizeSobolev`: if `u ∈ H^r` and
  `Op(p) u ∈ H^s`, then `ψ u ∈ H^{s + m}`. A distribution gains back near the support of `ψ` the
  `m` derivatives that `Op(a)` takes away.
* `TauCeti.Symbol.exists_norm_smulLeftCLM_le`: the **interior estimate**
  `‖ψ u‖_{H^{s + m}} ≤ C (‖Op(p) u‖_{H^s} + ‖u‖_{H^r})` on `H^{s + m}`, for every `r ≤ s + m`,
  with a constant `C` independent of `u`.

## The local parametrix

Let `q(x, ξ) = ψ(x) b(x, ξ)`. Each term of the formal composition `q # p` is `ψ` times the
corresponding term of `b # a`
(`TauCeti.Symbol.coefficient_sharpTerm_of_eq_smul_of_eventuallyEq`): the frequency derivatives of
`q` carry the factor `ψ(x)`, and near the support of `ψ` the position derivatives of `p` are those
of `a`. With the asymptotic expansion of the composition symbol, `q # p` therefore agrees with
`ψ(x)` up to symbols of every order (`TauCeti.Symbol.isSmoothing_sharp_sub_ofSpatial`):

`q # p = ψ + R` with `R` smoothing.

On Bessel-potential spaces `Op(q # p) = Op(q) ∘ Op(p)` (`TauCeti.Symbol.quantizeSobolev_sharp`)
and `Op(ψ)` is the multiplication by `ψ` (`TauCeti.Symbol.quantizeSobolev_ofSpatial_smul`), so

`ψ u = Op(q) (Op(p) u) - Op(R) u`.

The operator `Op(q)` maps `H^s` to `H^{s + m}`, and `Op(R)` maps `H^r` to `H^{s + m}` since `R`
has order `r - (s + m)`. Both statements follow.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (4.6)–(4.11).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Filter Finset Set TemperedDistribution
open scoped Topology BesselPotentialSpace SchwartzMap ContDiff

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}

/-! ### Interior regularity -/

section Regularity

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- The localized parametrix symbol `ψ(x) b(x, ξ)`. -/
private def localize (ψ : 𝓢(CoordinateSpace n, ℂ)) (b : Symbol n W V (-m)) : Symbol n W V (-m) :=
  inclusion (zero_add (-m)).le
    ((ofSpatial (fun x ↦ ψ x • ContinuousLinearMap.id ℂ V) ((ψ.smooth ⊤).smul contDiff_const)).comp
      b)

omit [CompleteSpace V] [CompleteSpace W] in
private theorem coefficient_localize (ψ : 𝓢(CoordinateSpace n, ℂ)) (b : Symbol n W V (-m))
    (x ξ : CoordinateSpace n) :
    (localize ψ b).coefficient (x, ξ) = ψ x • b.coefficient (x, ξ) := by
  simp [localize, coefficient_inclusion, ContinuousLinearMap.smul_comp]

omit [CompleteSpace V] [CompleteSpace W] in
private theorem hasCompactSpatialSupport_localize {ψ : 𝓢(CoordinateSpace n, ℂ)}
    (hψ : HasCompactSupport ψ) (b : Symbol n W V (-m)) :
    (localize ψ b).HasCompactSpatialSupport :=
  hasCompactSpatialSupport_iff.2 ⟨tsupport ψ, hψ, fun x hx ξ ↦ by
    simp [coefficient_localize, image_eq_zero_of_notMem_tsupport hx]⟩

variable {a : Symbol n V W m} {b : Symbol n W V (-m)} {ψ : 𝓢(CoordinateSpace n, ℂ)}
  {p : Symbol n V W m}

/-- The parametrix identity `ψ u = Op(ψ b) (Op(p) u) - Op(R) u` on `H^r`, with a symbol `R`
of every order, of which `Op(R)` is taken at the order `μ`. -/
private theorem exists_toDistr_quantizeSobolev_localize
    (hab : IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k)
      (inclusion (by simp) (const (.id ℂ V))) (b.sharpTerm a))
    (hψ : HasCompactSupport ψ) (hp : p.HasCompactSpatialSupport)
    (hpa : ∀ᶠ x in 𝓝ˢ (tsupport ψ), ∀ ξ, p.coefficient (x, ξ) = a.coefficient (x, ξ))
    (μ : ℝ) :
    ∃ (R : Symbol n V V μ) (hR : R.HasCompactSpatialSupport), ∀ (r : ℝ)
      (u : H^{r}(CoordinateSpace n, V)),
        smulLeftCLM V (ψ : CoordinateSpace n → ℂ) u.toDistr =
          ((localize ψ b).quantizeSobolev (hasCompactSpatialSupport_localize hψ b) (r - m)
            (p.quantizeSobolev hp r u)).toDistr - (R.quantizeSobolev hR r u).toDistr := by
  have hψ' : ContDiff ℝ ∞ (ψ : CoordinateSpace n → ℂ) := ψ.smooth ⊤
  set ψs := ofSpatial (fun x ↦ ψ x • ContinuousLinearMap.id ℂ V) (hψ'.smul contDiff_const)
  have hψs : ψs.HasCompactSpatialSupport :=
    (hasCompactSpatialSupport_ofSpatial_iff _).2 hψ.smul_right
  have hq := hasCompactSpatialSupport_localize hψ b
  have hqp := hq.sharp hp
  have hsmooth := isSmoothing_sharp_sub_ofSpatial hab hψ' (coefficient_localize ψ b) hp hpa
  obtain ⟨R, hR⟩ := isSmoothing_iff.1 hsmooth μ
  have hRc : R.HasCompactSpatialSupport :=
    (hqp.sub (hψs.inclusion _)).of_coefficient_eq hR
  refine ⟨R, hRc, fun r u ↦ ?_⟩
  have hcomp := congrArg (fun T ↦ (T u).toDistr) (quantizeSobolev_sharp hq hp hqp r)
  have hsub := congrArg (fun T ↦ (T u).toDistr)
    (quantizeSobolev_sub hqp (hψs.inclusion (neg_add_cancel m).ge) (hqp.sub (hψs.inclusion _)) r)
  -- `Op(ψ) u` is the multiplication `ψ u`.
  have hmul : (((ψs.inclusion (neg_add_cancel m).ge).quantizeSobolev
      (hψs.inclusion _) r) u).toDistr = smulLeftCLM V (ψ : CoordinateSpace n → ℂ) u.toDistr := by
    simp only [quantizeSobolev_inclusion _ hψs, ψs, quantizeSobolev_ofSpatial_smul,
      ContinuousLinearMap.comp_apply, BesselPotentialSpace.toDistr_inclusion,
      BesselPotentialSpace.toDistr_smulLeftCLM]
  simp only [ContinuousLinearMap.comp_apply, BesselPotentialSpace.toDistr_inclusion,
    sub_apply, BesselPotentialSpace.toDistr_sub, hmul] at hcomp hsub
  rw [toDistr_quantizeSobolev_congr hR hRc (hqp.sub (hψs.inclusion _)) rfl, hsub,
    ← hcomp]
  abel

/-- **Interior elliptic regularity.** Let `b` be a formal left parametrix of the symbol `a` of
order `m`, `1 ∼ ∑ₖ sharpTerm b a k`, let `ψ` be a compactly supported Schwartz function, and `p`
a symbol with compact spatial support which agrees with `a` at all positions near the support of
`ψ`. If `u ∈ H^r` and `Op(p) u ∈ H^s`, then `ψ u ∈ H^{s + m}`. -/
theorem memSobolev_smulLeftCLM_of_memSobolev_quantizeSobolev
    (hab : IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k)
      (inclusion (by simp) (const (.id ℂ V))) (b.sharpTerm a))
    (hψ : HasCompactSupport ψ) (hp : p.HasCompactSpatialSupport)
    (hpa : ∀ᶠ x in 𝓝ˢ (tsupport ψ), ∀ ξ, p.coefficient (x, ξ) = a.coefficient (x, ξ))
    {r s : ℝ} (u : H^{r}(CoordinateSpace n, V))
    (hu : MemSobolev s 2 (p.quantizeSobolev hp r u).toDistr) :
    MemSobolev (s + m) 2 (smulLeftCLM V (ψ : CoordinateSpace n → ℂ) u.toDistr) := by
  obtain ⟨R, hR, hψu⟩ := exists_toDistr_quantizeSobolev_localize hab hψ hp hpa (r - (s + m))
  rw [hψu r u, toDistr_quantizeSobolev_congr rfl
    (hasCompactSpatialSupport_localize hψ b) (hasCompactSpatialSupport_localize hψ b)
    (MemSobolev.toBesselPotentialSpace_toDistr hu).symm]
  have hmem {t : ℝ} (f : H^{t}(CoordinateSpace n, V)) (ht : t = s + m) :
      MemSobolev (s + m) 2 f.toDistr :=
    ht ▸ f.memSobolev_toDistr
  exact (hmem _ (by ring)).sub (hmem _ (by ring))

/-- **Interior elliptic estimate.** Let `b` be a formal left parametrix of the symbol `a` of order
`m`, `1 ∼ ∑ₖ sharpTerm b a k`, let `ψ` be a compactly supported Schwartz function, and `p` a
symbol with compact spatial support which agrees with `a` at all positions near the support of
`ψ`. For all real `s` and `r ≤ s + m` there is a constant `C` with

`‖ψ u‖_{H^{s + m}} ≤ C (‖Op(p) u‖_{H^s} + ‖u‖_{H^r})`

for every `u ∈ H^{s + m}`. -/
theorem exists_norm_smulLeftCLM_le
    (hab : IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k)
      (inclusion (by simp) (const (.id ℂ V))) (b.sharpTerm a))
    (hψ : HasCompactSupport ψ) (hp : p.HasCompactSpatialSupport)
    (hpa : ∀ᶠ x in 𝓝ˢ (tsupport ψ), ∀ ξ, p.coefficient (x, ξ) = a.coefficient (x, ξ))
    (s : ℝ) {r : ℝ} (hr : r ≤ s + m) :
    ∃ C, ∀ u : H^{s + m}(CoordinateSpace n, V),
      ‖BesselPotentialSpace.smulLeftCLM (s + m) ψ u‖ ≤
        C * (‖p.quantizeSobolev hp (s + m) u‖ + ‖BesselPotentialSpace.inclusion hr u‖) := by
  obtain ⟨R, hR, hψu⟩ := exists_toDistr_quantizeSobolev_localize hab hψ hp hpa (r - (s + m))
  set Q := (localize ψ b).quantizeSobolev (hasCompactSpatialSupport_localize hψ b) (s + m - m)
  set T := R.quantizeSobolev hR r
  refine ⟨max ‖Q‖ ‖T‖, fun u ↦ ?_⟩
  -- `ψ u = Q (Op(p) u) - T u`, compared in `H^{s + m}`.
  have hnorm {t : ℝ} (f : H^{t}(CoordinateSpace n, V)) (ht : t = s + m) :
      ‖f.copy (s + m) ht‖ = ‖f‖ := by
    rw [← BesselPotentialSpace.norm_toLp_eq, BesselPotentialSpace.toLp_copy _ ht,
      BesselPotentialSpace.norm_toLp_eq]
  set X := BesselPotentialSpace.copy (s + m) (Q (p.quantizeSobolev hp (s + m) u)) (by ring)
  set Y := BesselPotentialSpace.copy (s + m) (T (BesselPotentialSpace.inclusion hr u)) (by ring)
  have hXY : BesselPotentialSpace.smulLeftCLM (s + m) ψ u = X - Y := by
    refine BesselPotentialSpace.ext ?_
    rw [BesselPotentialSpace.toDistr_smulLeftCLM, BesselPotentialSpace.toDistr_sub,
      BesselPotentialSpace.toDistr_copy _ (by ring), BesselPotentialSpace.toDistr_copy _ (by ring),
      hψu (s + m) u]
    congr 1
    exact toDistr_quantizeSobolev_congr rfl hR hR (by simp)
  calc ‖BesselPotentialSpace.smulLeftCLM (s + m) ψ u‖ ≤ ‖X‖ + ‖Y‖ := hXY ▸ norm_sub_le X Y
    _ ≤ ‖Q‖ * ‖p.quantizeSobolev hp (s + m) u‖ + ‖T‖ * ‖BesselPotentialSpace.inclusion hr u‖ := by
      rw [hnorm, hnorm]
      exact add_le_add (Q.le_opNorm _) (T.le_opNorm _)
    _ ≤ _ := by
      rw [mul_add]
      gcongr
      exacts [le_max_left _ _, le_max_right _ _]

end Regularity

end Symbol

end TauCeti
