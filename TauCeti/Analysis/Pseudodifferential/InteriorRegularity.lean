/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Parametrix
public import TauCeti.Analysis.Pseudodifferential.Composition.Sobolev

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
agrees with `a` at all positions where `ψ` does not vanish, for instance `φ(x) a(x, ξ)` for a
cutoff `φ` equal to `1` on the support of `ψ`. This file proves the **interior regularity**
of `Op(a)`:

* `TauCeti.Symbol.memSobolev_smulLeftCLM_of_isAsymptoticSum_sharpTerm`: if `u ∈ H^r` and
  `Op(p) u ∈ H^s`, then `ψ u ∈ H^{s + m}`. A distribution gains back near the support of `ψ` the
  `m` derivatives that `Op(a)` takes away. For symbols elliptic above some radius this is
  `TauCeti.Symbol.IsEllipticAbove.memSobolev_smulLeftCLM_of_memSobolev_quantizeSobolev`.
* `TauCeti.Symbol.exists_norm_smulLeftCLM_le_of_isAsymptoticSum_sharpTerm`: the **interior
  estimate** `‖ψ u‖_{H^s} ≤ C (‖Op(p) u‖_{H^{s - m}} + ‖u‖_{H^r})` on `H^s`, for every `r ≤ s`,
  with a constant `C` independent of `u`. For symbols with a left inverse at large frequencies
  near the support of `ψ`, the same estimate is
  `TauCeti.Symbol.exists_norm_smulLeftCLM_le_of_eventually_comp_eq_id`.

Both only use a *local parametrix*: a symbol `q` of order `-m` with compact spatial support such
that `q # p - ψ` is smoothing. In this form they are
`TauCeti.Symbol.memSobolev_smulLeftCLM_of_isSmoothing_sharp_sub` and
`TauCeti.Symbol.exists_norm_smulLeftCLM_le_of_isSmoothing_sharp_sub`, which follow from the
parametrix identity `TauCeti.Symbol.exists_continuousLinearMap_smulLeftCLM_toDistr_eq_sub`.

## The local parametrix

Let `q(x, ξ) = ψ(x) b(x, ξ)`. Each term of the formal composition `q # p` is `ψ` times the
corresponding term of `b # a`
(`TauCeti.Symbol.coefficient_sharpTerm_eq_smul_of_eventuallyEq`): the frequency derivatives of
`q` carry the factor `ψ(x)`, and where `ψ` does not vanish, an open set, the position derivatives
of `p` are those of `a`. With the asymptotic expansion of the composition symbol, `q # p`
therefore agrees with `ψ(x)` up to symbols of every order
(`TauCeti.Symbol.isSmoothing_sharp_sub_ofSpatial`):

`q # p = ψ + R` with `R` smoothing.

On Bessel-potential spaces `Op(q # p) = Op(q) ∘ Op(p)`
(`TauCeti.Symbol.toDistr_quantizeSobolev_sharp`) and `Op(ψ)` is the multiplication by `ψ`
(`TauCeti.Symbol.toDistr_quantizeSobolev_ofSpatial_smul_id`), so

`ψ u = Op(q) (Op(p) u) - Op(R) u`.

The operator `Op(q)` gains `m` derivatives, and `Op(R)` maps `H^r` to every Sobolev space
(`TauCeti.Symbol.IsSmoothing.exists_continuousLinearMap_toDistr_quantizeSobolev_eq`). Both
statements follow.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (4.6)–(4.11).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open TemperedDistribution
open scoped BesselPotentialSpace SchwartzMap ContDiff

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}

/-! ### Interior regularity -/

section Regularity

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-! #### From a local parametrix -/

variable {q : Symbol n W V (-m)} {ψ : 𝓢(CoordinateSpace n, ℂ)} {p : Symbol n V W m}

/-- **The local parametrix identity.** Let `q` and `p` be symbols of orders `-m` and `m` with
compact spatial support, and `ψ` a compactly supported Schwartz function such that `q # p - ψ` is
smoothing. Then for all real `r` and `s` there is a bounded operator `T : H^r → H^s` with
`ψ v = Op(q) (Op(p) v) - T u` for every `v` of any Sobolev order that agrees with `u ∈ H^r` as a
distribution. -/
theorem exists_continuousLinearMap_smulLeftCLM_toDistr_eq_sub (hq : q.HasCompactSpatialSupport)
    (hψ : HasCompactSupport ψ) (hp : p.HasCompactSpatialSupport)
    (hqp : (q.sharp p hp - inclusion (neg_add_cancel m).ge
      (ofSpatial (fun x ↦ ψ x • ContinuousLinearMap.id ℂ V)
        ((ψ.smooth ⊤).smul contDiff_const))).IsSmoothing)
    (r s : ℝ) :
    ∃ T : H^{r}(CoordinateSpace n, V) →L[ℂ] H^{s}(CoordinateSpace n, V),
      ∀ {t : ℝ} {v : H^{t}(CoordinateSpace n, V)} {u : H^{r}(CoordinateSpace n, V)},
        v.toDistr = u.toDistr →
          smulLeftCLM V (ψ : CoordinateSpace n → ℂ) v.toDistr =
            (q.quantizeSobolev hq (t - m) (p.quantizeSobolev hp t v)).toDistr - (T u).toDistr := by
  have hψs := hasCompactSpatialSupport_ofSpatial_smul_id (V := V) hψ
  have hS := (hq.sharp hp).sub (hψs.inclusion (neg_add_cancel m).ge)
  obtain ⟨T, hT⟩ := hqp.exists_continuousLinearMap_toDistr_quantizeSobolev_eq hS r s
  refine ⟨T, fun {t v u} huv ↦ ?_⟩
  -- `Op(ψ) v` is the multiplication `ψ v`.
  have hmul : (((ofSpatial _ _).inclusion (neg_add_cancel m).ge).quantizeSobolev
      (hψs.inclusion _) t v).toDistr = smulLeftCLM V (ψ : CoordinateSpace n → ℂ) v.toDistr := by
    rw [toDistr_quantizeSobolev_congr (coefficient_inclusion _ _) _ hψs rfl,
      toDistr_quantizeSobolev_ofSpatial_smul_id, BesselPotentialSpace.toDistr_smulLeftCLM]
  rw [← hT huv, toDistr_quantizeSobolev_sub_apply (hq.sharp hp) (hψs.inclusion _) hS, hmul,
    toDistr_quantizeSobolev_sharp hq hp]
  abel

/-- **Interior regularity from a local parametrix.** Let `q` and `p` be symbols of orders `-m`
and `m` with compact spatial support, and `ψ` a compactly supported Schwartz function such that
`q # p - ψ` is smoothing. If `u ∈ H^r` and `Op(p) u ∈ H^s`, then `ψ u ∈ H^{s + m}`. -/
theorem memSobolev_smulLeftCLM_of_isSmoothing_sharp_sub (hq : q.HasCompactSpatialSupport)
    (hψ : HasCompactSupport ψ) (hp : p.HasCompactSpatialSupport)
    (hqp : (q.sharp p hp - inclusion (neg_add_cancel m).ge
      (ofSpatial (fun x ↦ ψ x • ContinuousLinearMap.id ℂ V)
        ((ψ.smooth ⊤).smul contDiff_const))).IsSmoothing)
    {r s : ℝ} (u : H^{r}(CoordinateSpace n, V))
    (hu : MemSobolev s 2 (p.quantizeSobolev hp r u).toDistr) :
    MemSobolev (s + m) 2 (smulLeftCLM V (ψ : CoordinateSpace n → ℂ) u.toDistr) := by
  obtain ⟨T, hT⟩ := exists_continuousLinearMap_smulLeftCLM_toDistr_eq_sub hq hψ hp hqp r (s + m)
  rw [hT rfl, toDistr_quantizeSobolev_congr rfl hq hq
    (MemSobolev.toBesselPotentialSpace_toDistr hu).symm]
  have hmem {t : ℝ} (f : H^{t}(CoordinateSpace n, V)) (ht : t = s + m) :
      MemSobolev (s + m) 2 f.toDistr :=
    ht ▸ f.memSobolev_toDistr
  exact (hmem _ (sub_neg_eq_add s m)).sub (T u).memSobolev_toDistr

/-- **Interior estimate from a local parametrix.** Let `q` and `p` be symbols of orders `-m` and
`m` with compact spatial support, and `ψ` a compactly supported Schwartz function such that
`q # p - ψ` is smoothing. For all real `r ≤ s` there is a constant `C` with

`‖ψ u‖_{H^s} ≤ C (‖Op(p) u‖_{H^{s - m}} + ‖u‖_{H^r})`

for every `u ∈ H^s`. -/
theorem exists_norm_smulLeftCLM_le_of_isSmoothing_sharp_sub (hq : q.HasCompactSpatialSupport)
    (hψ : HasCompactSupport ψ) (hp : p.HasCompactSpatialSupport)
    (hqp : (q.sharp p hp - inclusion (neg_add_cancel m).ge
      (ofSpatial (fun x ↦ ψ x • ContinuousLinearMap.id ℂ V)
        ((ψ.smooth ⊤).smul contDiff_const))).IsSmoothing)
    {r s : ℝ} (hrs : r ≤ s) :
    ∃ C, ∀ u : H^{s}(CoordinateSpace n, V),
      ‖BesselPotentialSpace.smulLeftCLM s ψ u‖ ≤
        C * (‖p.quantizeSobolev hp s u‖ + ‖BesselPotentialSpace.inclusion hrs u‖) := by
  obtain ⟨T, hT⟩ := exists_continuousLinearMap_smulLeftCLM_toDistr_eq_sub hq hψ hp hqp r s
  set Q := BesselPotentialSpace.inclusion (le_of_eq (by ring) : s ≤ s - m - -m) ∘L
    q.quantizeSobolev hq (s - m)
  refine ⟨max ‖Q‖ ‖T‖, fun u ↦ ?_⟩
  -- `ψ u = Q (Op(p) u) - T u` in `H^s`.
  have h : BesselPotentialSpace.smulLeftCLM s ψ u =
      Q (p.quantizeSobolev hp s u) - T (BesselPotentialSpace.inclusion hrs u) := by
    refine BesselPotentialSpace.ext ?_
    rw [BesselPotentialSpace.toDistr_smulLeftCLM, BesselPotentialSpace.toDistr_sub,
      ContinuousLinearMap.comp_apply, BesselPotentialSpace.toDistr_inclusion,
      hT (BesselPotentialSpace.toDistr_inclusion hrs u).symm]
  calc ‖BesselPotentialSpace.smulLeftCLM s ψ u‖
      ≤ ‖Q (p.quantizeSobolev hp s u)‖ + ‖T (BesselPotentialSpace.inclusion hrs u)‖ :=
        h ▸ norm_sub_le _ _
    _ ≤ ‖Q‖ * ‖p.quantizeSobolev hp s u‖ + ‖T‖ * ‖BesselPotentialSpace.inclusion hrs u‖ :=
      add_le_add (Q.le_opNorm _) (T.le_opNorm _)
    _ ≤ _ := by
      rw [mul_add]
      gcongr
      exacts [le_max_left _ _, le_max_right _ _]

/-! #### From a formal left parametrix -/

variable {a : Symbol n V W m} {b : Symbol n W V (-m)}

/-- **Interior elliptic regularity.** Let `b` be a formal left parametrix of the symbol `a` of
order `m`, `1 ∼ ∑ₖ sharpTerm b a k`, let `ψ` be a compactly supported Schwartz function, and `p`
a symbol with compact spatial support which agrees with `a` at all positions where `ψ` does not
vanish. If `u ∈ H^r` and `Op(p) u ∈ H^s`, then `ψ u ∈ H^{s + m}`. -/
theorem memSobolev_smulLeftCLM_of_isAsymptoticSum_sharpTerm
    (hab : IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k)
      (inclusion (by simp) (const (.id ℂ V))) (b.sharpTerm a))
    (hψ : HasCompactSupport ψ) (hp : p.HasCompactSpatialSupport)
    (hpa : ∀ x, ψ x ≠ 0 → ∀ ξ, p.coefficient (x, ξ) = a.coefficient (x, ξ))
    {r s : ℝ} (u : H^{r}(CoordinateSpace n, V))
    (hu : MemSobolev s 2 (p.quantizeSobolev hp r u).toDistr) :
    MemSobolev (s + m) 2 (smulLeftCLM V (ψ : CoordinateSpace n → ℂ) u.toDistr) :=
  -- The local parametrix `q(x, ξ) = ψ(x) b(x, ξ)`.
  memSobolev_smulLeftCLM_of_isSmoothing_sharp_sub
    (((hasCompactSpatialSupport_ofSpatial_smul_id hψ).comp_right b).inclusion (zero_add (-m)).le)
    hψ hp (isSmoothing_sharp_sub_ofSpatial hab (ψ.smooth ⊤)
      (fun x ξ ↦ by simp [coefficient_inclusion, ContinuousLinearMap.smul_comp]) hp hpa) u hu

/-- **Interior elliptic estimate.** Let `b` be a formal left parametrix of the symbol `a` of order
`m`, `1 ∼ ∑ₖ sharpTerm b a k`, let `ψ` be a compactly supported Schwartz function, and `p` a
symbol with compact spatial support which agrees with `a` at all positions where `ψ` does not
vanish. For all real `r ≤ s` there is a constant `C` with

`‖ψ u‖_{H^s} ≤ C (‖Op(p) u‖_{H^{s - m}} + ‖u‖_{H^r})`

for every `u ∈ H^s`. -/
theorem exists_norm_smulLeftCLM_le_of_isAsymptoticSum_sharpTerm
    (hab : IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k)
      (inclusion (by simp) (const (.id ℂ V))) (b.sharpTerm a))
    (hψ : HasCompactSupport ψ) (hp : p.HasCompactSpatialSupport)
    (hpa : ∀ x, ψ x ≠ 0 → ∀ ξ, p.coefficient (x, ξ) = a.coefficient (x, ξ))
    {r s : ℝ} (hrs : r ≤ s) :
    ∃ C, ∀ u : H^{s}(CoordinateSpace n, V),
      ‖BesselPotentialSpace.smulLeftCLM s ψ u‖ ≤
        C * (‖p.quantizeSobolev hp s u‖ + ‖BesselPotentialSpace.inclusion hrs u‖) :=
  -- The local parametrix `q(x, ξ) = ψ(x) b(x, ξ)`.
  exists_norm_smulLeftCLM_le_of_isSmoothing_sharp_sub
    (((hasCompactSpatialSupport_ofSpatial_smul_id hψ).comp_right b).inclusion (zero_add (-m)).le)
    hψ hp (isSmoothing_sharp_sub_ofSpatial hab (ψ.smooth ⊤)
      (fun x ξ ↦ by simp [coefficient_inclusion, ContinuousLinearMap.smul_comp]) hp hpa) hrs

/-- **Interior elliptic regularity for elliptic symbols.** Let `a` be a symbol of order `m`
elliptic above some radius, `ψ` a compactly supported Schwartz function, and `p` a symbol with
compact spatial support which agrees with `a` at all positions where `ψ` does not vanish. If
`u ∈ H^r` and `Op(p) u ∈ H^s`, then `ψ u ∈ H^{s + m}`. -/
theorem IsEllipticAbove.memSobolev_smulLeftCLM_of_memSobolev_quantizeSobolev {R : ℝ}
    (ha : a.IsEllipticAbove R) (hψ : HasCompactSupport ψ) (hp : p.HasCompactSpatialSupport)
    (hpa : ∀ x, ψ x ≠ 0 → ∀ ξ, p.coefficient (x, ξ) = a.coefficient (x, ξ))
    {r s : ℝ} (u : H^{r}(CoordinateSpace n, V))
    (hu : MemSobolev s 2 (p.quantizeSobolev hp r u).toDistr) :
    MemSobolev (s + m) 2 (smulLeftCLM V (ψ : CoordinateSpace n → ℂ) u.toDistr) := by
  obtain ⟨b, hab, -⟩ := ha.exists_isAsymptoticSum_sharpTerm
  exact memSobolev_smulLeftCLM_of_isAsymptoticSum_sharpTerm hab hψ hp hpa u hu

end Regularity

end Symbol

end TauCeti
