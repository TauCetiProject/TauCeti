/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.BesselPotentialSpace
public import TauCeti.Analysis.Pseudodifferential.Composition.Parametrix
import TauCeti.Analysis.Sobolev.BesselPotential.Distribution

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

The same holds on the `Lᵖ` Bessel-potential spaces `H^{s,p}`, `1 < p < ∞`, for finite-dimensional
`V` and `W`, with the operators `TauCeti.Symbol.quantizeBesselPotentialSpace` in place of
`TauCeti.Symbol.quantizeSobolev`; there the localized symbol is called `c`, since `p` is the
exponent:

* `TauCeti.Symbol.memSobolev_smulLeftCLM_of_memSobolev_quantizeBesselPotentialSpace`: if
  `u ∈ H^{r,p}` and `Op(c) u ∈ H^{s,p}`, then `ψ u ∈ H^{s + m,p}`, and
  `TauCeti.Symbol.IsEllipticAbove.memSobolev_smulLeftCLM_of_memSobolev_quantizeBesselPotentialSpace`
  for a symbol `a` elliptic above some radius.
* `TauCeti.Symbol.exists_norm_le_of_toDistr_eq_smulLeftCLM`: the interior estimate
  `‖ψ u‖_{H^{s + m,p}} ≤ C (‖Op(c) u‖_{H^{s,p}} + ‖u‖_{H^{r,p}})` for `u ∈ H^{s + m,p}`. It bounds
  every element of `H^{s + m,p}` with the tempered distribution `ψ u`; such an element exists,
  since `ψ u` is the quantization of the symbol `ψ(x)`
  (`TauCeti.Symbol.toDistr_quantizeBesselPotentialSpace_ofSpatial_smul_id`).

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
has order `r - (s + m)`. Both statements follow, and the same identity on `H^{r,p}`
(`TauCeti.Symbol.toDistr_quantizeBesselPotentialSpace_sharp`,
`TauCeti.Symbol.toDistr_quantizeBesselPotentialSpace_ofSpatial_smul_id`) gives the `Lᵖ` versions.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (4.6)–(4.11), and Lecture II, (3.1)–(3.8) (the `Lᵖ` estimates by the same parametrix
  argument).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Filter Finset Set TemperedDistribution
open scoped Topology BesselPotentialSpace SchwartzMap ContDiff ENNReal

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}

/-! ### The norm bound of the estimates -/

section Localize

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W]

/-- The norm bound behind both interior estimates: `‖Q x - T y‖ ≤ max ‖Q‖ ‖T‖ (‖x‖ + ‖y‖)`, with
`Q x` and `T y` moved to a common Bessel-potential space `H^{s,p}`. -/
private theorem norm_copy_sub_copy_le [CompleteSpace V] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ F] {s t t' : ℝ} (Q : E →L[ℂ] H^{t, p}(CoordinateSpace n, V))
    (T : F →L[ℂ] H^{t', p}(CoordinateSpace n, V)) (x : E) (y : F) (ht : t = s) (ht' : t' = s) :
    ‖(Q x).copy s ht - (T y).copy s ht'‖ ≤ max ‖Q‖ ‖T‖ * (‖x‖ + ‖y‖) :=
  calc _ ≤ ‖Q x‖ + ‖T y‖ := by
        simpa only [BesselPotentialSpace.norm_copy] using
          norm_sub_le ((Q x).copy s ht) ((T y).copy s ht')
    _ ≤ ‖Q‖ * ‖x‖ + ‖T‖ * ‖y‖ := add_le_add (Q.le_opNorm x) (T.le_opNorm y)
    _ ≤ _ := by
      rw [mul_add]
      gcongr
      exacts [le_max_left _ _, le_max_right _ _]

end Localize

/-! ### Interior regularity -/

section Regularity

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

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
          ((smulLeft (ψ.smooth ⊤) b).quantizeSobolev
            (hasCompactSpatialSupport_smulLeft (ψ.smooth ⊤) hψ b) (r - m)
            (p.quantizeSobolev hp r u)).toDistr - (R.quantizeSobolev hR r u).toDistr := by
  have hψ' : ContDiff ℝ ∞ (ψ : CoordinateSpace n → ℂ) := ψ.smooth ⊤
  set ψs := ofSpatial (fun x ↦ ψ x • ContinuousLinearMap.id ℂ V) (hψ'.smul contDiff_const)
  have hψs : ψs.HasCompactSpatialSupport :=
    (hasCompactSpatialSupport_ofSpatial_iff _).2 hψ.smul_right
  have hq := hasCompactSpatialSupport_smulLeft (ψ.smooth ⊤) hψ b
  have hqp := hq.sharp hp
  have hsmooth := isSmoothing_sharp_sub_ofSpatial hab hψ'
    (fun x ξ ↦ coefficient_smulLeft hψ' b (x, ξ)) hp hpa
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
    (hasCompactSpatialSupport_smulLeft (ψ.smooth ⊤) hψ b)
    (hasCompactSpatialSupport_smulLeft (ψ.smooth ⊤) hψ b)
    (MemSobolev.toBesselPotentialSpace_toDistr hu).symm]
  exact (BesselPotentialSpace.memSobolev_toDistr_of_eq _ (by ring)).sub
    (BesselPotentialSpace.memSobolev_toDistr_of_eq _ (by ring))

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
  set Q := (smulLeft (ψ.smooth ⊤) b).quantizeSobolev
    (hasCompactSpatialSupport_smulLeft (ψ.smooth ⊤) hψ b) (s + m - m)
  set T := R.quantizeSobolev hR r
  refine ⟨max ‖Q‖ ‖T‖, fun u ↦ ?_⟩
  -- `ψ u = Q (Op(p) u) - T u`, compared in `H^{s + m}`.
  set X := BesselPotentialSpace.copy (s + m) (Q (p.quantizeSobolev hp (s + m) u)) (by ring)
  set Y := BesselPotentialSpace.copy (s + m) (T (BesselPotentialSpace.inclusion hr u)) (by ring)
  have hXY : BesselPotentialSpace.smulLeftCLM (s + m) ψ u = X - Y := by
    refine BesselPotentialSpace.ext ?_
    rw [BesselPotentialSpace.toDistr_smulLeftCLM, BesselPotentialSpace.toDistr_sub,
      BesselPotentialSpace.toDistr_copy _ (by ring), BesselPotentialSpace.toDistr_copy _ (by ring),
      hψu (s + m) u]
    congr 1
    exact toDistr_quantizeSobolev_congr rfl hR hR (by simp)
  exact hXY ▸ norm_copy_sub_copy_le Q T _ _ _ _

end Regularity

/-! ### Interior regularity on `H^{s,p}` -/

section BesselPotentialSpace

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [CompleteSpace V] [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  [CompleteSpace W] {a : Symbol n V W m} {b : Symbol n W V (-m)} {ψ : 𝓢(CoordinateSpace n, ℂ)}
  {c : Symbol n V W m} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The parametrix identity `ψ u = Op(ψ b) (Op(c) u) - Op(R) u` on `H^{r,p}`, with a symbol `R`
of every order, of which `Op(R)` is taken at the order `μ`. -/
private theorem exists_toDistr_quantizeBesselPotentialSpace_localize
    (hab : IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k)
      (inclusion (by simp) (const (.id ℂ V))) (b.sharpTerm a))
    (hψ : HasCompactSupport ψ) (hc : c.HasCompactSpatialSupport)
    (hca : ∀ᶠ x in 𝓝ˢ (tsupport ψ), ∀ ξ, c.coefficient (x, ξ) = a.coefficient (x, ξ))
    (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) (μ : ℝ) :
    ∃ (R : Symbol n V V μ) (hR : R.HasCompactSpatialSupport), ∀ (r : ℝ)
      (u : H^{r, p}(CoordinateSpace n, V)),
        smulLeftCLM V (ψ : CoordinateSpace n → ℂ) u.toDistr =
          ((smulLeft (ψ.smooth ⊤) b).quantizeBesselPotentialSpace
            (hasCompactSpatialSupport_smulLeft (ψ.smooth ⊤) hψ b) (r - m) p
            (c.quantizeBesselPotentialSpace hc r p u)).toDistr -
          (R.quantizeBesselPotentialSpace hR r p u).toDistr := by
  have hψ' : ContDiff ℝ ∞ (ψ : CoordinateSpace n → ℂ) := ψ.smooth ⊤
  set ψs := ofSpatial (fun x ↦ ψ x • ContinuousLinearMap.id ℂ V) (hψ'.smul contDiff_const)
  have hψs : ψs.HasCompactSpatialSupport :=
    (hasCompactSpatialSupport_ofSpatial_iff _).2 hψ.smul_right
  have hq := hasCompactSpatialSupport_smulLeft (ψ.smooth ⊤) hψ b
  have hqc := hq.sharp hc
  have hψs' := hψs.inclusion (neg_add_cancel m).ge
  -- `q # c - ψ` is smoothing, so it has a representative `R` of order `μ`.
  obtain ⟨R, hR⟩ := isSmoothing_iff.1
    (isSmoothing_sharp_sub_ofSpatial hab hψ' (fun x ξ ↦ coefficient_smulLeft hψ' b (x, ξ))
      hc hca) μ
  have hRc : R.HasCompactSpatialSupport := (hqc.sub hψs').of_coefficient_eq hR
  refine ⟨R, hRc, fun r u ↦ ?_⟩
  -- `Op(R) u = Op(q # c) u - ψ u = Op(q) (Op(c) u) - ψ u`.
  have hRu : (R.quantizeBesselPotentialSpace hRc r p u).toDistr =
      ((smulLeft (ψ.smooth ⊤) b).quantizeBesselPotentialSpace hq (r - m) p
        (c.quantizeBesselPotentialSpace hc r p u)).toDistr -
        smulLeftCLM V (ψ : CoordinateSpace n → ℂ) u.toDistr := by
    rw [toDistr_quantizeBesselPotentialSpace_congr hR hRc (hqc.sub hψs') hp hp_top rfl,
      quantizeBesselPotentialSpace_sub hqc hψs' _ r hp hp_top, _root_.sub_apply,
      BesselPotentialSpace.toDistr_sub,
      toDistr_quantizeBesselPotentialSpace_sharp hq hc r hp hp_top,
      toDistr_quantizeBesselPotentialSpace_congr (by simp [coefficient_inclusion]) hψs' hψs hp
        hp_top rfl, toDistr_quantizeBesselPotentialSpace_ofSpatial_smul_id ψ hψs r hp hp_top]
  rw [hRu, sub_sub_cancel]

/-- **Interior elliptic regularity on `H^{s,p}`.** Let `1 < p < ∞`, let `V` and `W` be
finite-dimensional, let `b` be a formal left parametrix of the symbol `a` of order `m`,
`1 ∼ ∑ₖ sharpTerm b a k`, let `ψ` be a compactly supported Schwartz function, and `c` a symbol with
compact spatial support which agrees with `a` at all positions near the support of `ψ`. If
`u ∈ H^{r,p}` and `Op(c) u ∈ H^{s,p}`, then `ψ u ∈ H^{s + m,p}`. Every symbol elliptic above some
radius has such a parametrix (`TauCeti.Symbol.IsEllipticAbove.exists_isAsymptoticSum_sharpTerm`). -/
theorem memSobolev_smulLeftCLM_of_memSobolev_quantizeBesselPotentialSpace
    (hab : IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k)
      (inclusion (by simp) (const (.id ℂ V))) (b.sharpTerm a))
    (hψ : HasCompactSupport ψ) (hc : c.HasCompactSpatialSupport)
    (hca : ∀ᶠ x in 𝓝ˢ (tsupport ψ), ∀ ξ, c.coefficient (x, ξ) = a.coefficient (x, ξ))
    (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) {r s : ℝ} (u : H^{r, p}(CoordinateSpace n, V))
    (hu : MemSobolev s p (c.quantizeBesselPotentialSpace hc r p u).toDistr) :
    MemSobolev (s + m) p (smulLeftCLM V (ψ : CoordinateSpace n → ℂ) u.toDistr) := by
  obtain ⟨R, hR, hψu⟩ :=
    exists_toDistr_quantizeBesselPotentialSpace_localize hab hψ hc hca hp hp_top (r - (s + m))
  rw [hψu r u, toDistr_quantizeBesselPotentialSpace_congr rfl
    (hasCompactSpatialSupport_smulLeft (ψ.smooth ⊤) hψ b)
    (hasCompactSpatialSupport_smulLeft (ψ.smooth ⊤) hψ b) hp hp_top
    (MemSobolev.toBesselPotentialSpace_toDistr hu).symm]
  exact (BesselPotentialSpace.memSobolev_toDistr_of_eq _ (by ring)).sub
    (BesselPotentialSpace.memSobolev_toDistr_of_eq _ (by ring))

/-- **Interior elliptic regularity on `H^{s,p}` for elliptic symbols.** Let `1 < p < ∞`, let `V`
and `W` be finite-dimensional, let `a` be a symbol of order `m` elliptic above some radius, let `ψ`
be a compactly supported Schwartz function, and `c` a symbol with compact spatial support which
agrees with `a` at all positions near the support of `ψ`. If `u ∈ H^{r,p}` and
`Op(c) u ∈ H^{s,p}`, then `ψ u ∈ H^{s + m,p}`. -/
theorem IsEllipticAbove.memSobolev_smulLeftCLM_of_memSobolev_quantizeBesselPotentialSpace
    {R : ℝ} (ha : a.IsEllipticAbove R) (hψ : HasCompactSupport ψ)
    (hc : c.HasCompactSpatialSupport)
    (hca : ∀ᶠ x in 𝓝ˢ (tsupport ψ), ∀ ξ, c.coefficient (x, ξ) = a.coefficient (x, ξ))
    (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) {r s : ℝ} (u : H^{r, p}(CoordinateSpace n, V))
    (hu : MemSobolev s p (c.quantizeBesselPotentialSpace hc r p u).toDistr) :
    MemSobolev (s + m) p (smulLeftCLM V (ψ : CoordinateSpace n → ℂ) u.toDistr) :=
  have ⟨_, hab, _⟩ := ha.exists_isAsymptoticSum_sharpTerm
  Symbol.memSobolev_smulLeftCLM_of_memSobolev_quantizeBesselPotentialSpace hab hψ hc hca hp hp_top
    u hu

/-- **Interior elliptic estimate on `H^{s,p}`.** Let `1 < p < ∞`, let `V` and `W` be
finite-dimensional, let `b` be a formal left parametrix of the symbol `a` of order `m`,
`1 ∼ ∑ₖ sharpTerm b a k`, let `ψ` be a compactly supported Schwartz function, and `c` a symbol with
compact spatial support which agrees with `a` at all positions near the support of `ψ`. For all
real `s` and `r ≤ s + m` there is a constant `C` with

`‖ψ u‖_{H^{s + m,p}} ≤ C (‖Op(c) u‖_{H^{s,p}} + ‖u‖_{H^{r,p}})`

for every `u ∈ H^{s + m,p}`, where `ψ u` is any element `v` of `H^{s + m,p}` with the tempered
distribution `ψ u`. -/
theorem exists_norm_le_of_toDistr_eq_smulLeftCLM
    (hab : IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k)
      (inclusion (by simp) (const (.id ℂ V))) (b.sharpTerm a))
    (hψ : HasCompactSupport ψ) (hc : c.HasCompactSpatialSupport)
    (hca : ∀ᶠ x in 𝓝ˢ (tsupport ψ), ∀ ξ, c.coefficient (x, ξ) = a.coefficient (x, ξ))
    (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) (s : ℝ) {r : ℝ} (hr : r ≤ s + m) :
    ∃ C, ∀ u v : H^{s + m, p}(CoordinateSpace n, V),
      v.toDistr = smulLeftCLM V (ψ : CoordinateSpace n → ℂ) u.toDistr →
        ‖v‖ ≤ C * (‖c.quantizeBesselPotentialSpace hc (s + m) p u‖ +
          ‖BesselPotentialSpace.inclusion hr u‖) := by
  obtain ⟨R, hR, hψu⟩ :=
    exists_toDistr_quantizeBesselPotentialSpace_localize hab hψ hc hca hp hp_top (r - (s + m))
  set Q := (smulLeft (ψ.smooth ⊤) b).quantizeBesselPotentialSpace
    (hasCompactSpatialSupport_smulLeft (ψ.smooth ⊤) hψ b) (s + m - m) p
  set T := R.quantizeBesselPotentialSpace hR r p
  refine ⟨max ‖Q‖ ‖T‖, fun u v hv ↦ ?_⟩
  -- `v = ψ u = Q (Op(c) u) - T u`, compared in `H^{s + m,p}`.
  set X := BesselPotentialSpace.copy (s + m)
    (Q (c.quantizeBesselPotentialSpace hc (s + m) p u)) (by ring)
  set Y := BesselPotentialSpace.copy (s + m) (T (BesselPotentialSpace.inclusion hr u)) (by ring)
  have hXY : v = X - Y := by
    refine BesselPotentialSpace.ext ?_
    rw [hv, BesselPotentialSpace.toDistr_sub, BesselPotentialSpace.toDistr_copy _ (by ring),
      BesselPotentialSpace.toDistr_copy _ (by ring), hψu (s + m) u]
    congr 1
    exact toDistr_quantizeBesselPotentialSpace_congr rfl hR hR hp hp_top (by simp)
  exact hXY ▸ norm_copy_sub_copy_le Q T _ _ _ _

end BesselPotentialSpace

end Symbol

end TauCeti
