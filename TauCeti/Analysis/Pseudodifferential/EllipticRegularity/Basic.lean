/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Parametrix
public import TauCeti.Analysis.Pseudodifferential.Composition.Sobolev
public import TauCeti.Analysis.Pseudodifferential.TemperedDistribution
import TauCeti.Analysis.Pseudodifferential.Smoothing
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff

/-!
# Interior elliptic regularity

Let `p` be a symbol of order `m` on `ℝⁿ` with values in `V →L[ℂ] W`, elliptic above some radius
(`TauCeti.Symbol.IsEllipticAbove`), and let `b` be a left parametrix symbol of `p`, a symbol of
order `-m` with `1 ∼ ∑ₖ sharpTerm b p k`
(`TauCeti.Symbol.IsEllipticAbove.exists_isAsymptoticSum_sharpTerm`).
The composition symbol `b # a` is only available when the right factor `a` has compact spatial
support, so the parametrix is applied to a localization of `Op(p)`: a symbol `a` with compact
spatial support that agrees with `p` near the support of a compactly supported Schwartz function
`φ`, for instance `ψ(x) p(x, ξ)` for a cutoff `ψ` equal to `1` near `tsupport φ`. The local left
parametrix identity `(φ b) # a = φ + r` with `r` smoothing
(`TauCeti.Symbol.isSmoothing_sharp_sub_ofSpatial`) gives `Op(φ b) Op(a) = φ + Op(r)` on
the Bessel-potential spaces `H^s = H^{s,2}(ℝⁿ; V)`. This file proves this operator identity and
the regularity of solutions of elliptic equations:

* `TauCeti.Symbol.IsEllipticAbove.exists_isSmoothing_sharp_sub_ofSpatial` is the symbol identity:
  a symbol `q` of order `-m` with compact spatial support, vanishing at positions outside
  `tsupport φ`, such that `q # a - φ` is smoothing, again with compact spatial support.
* `Symbol.IsAsymptoticSum.exists_isSmoothing_and_toDistr_quantizeSobolev_eq_quantizeSobolev_add`
  is the operator identity for a target symbol: if `c ∼ ∑ₖ sharpTerm b p k` for a symbol `c` of
  order `0`, then `Op(φ b) Op(a) u = Op(φ c) u + Op(r) u` with `r` smoothing.
* `TauCeti.Symbol.IsEllipticAbove.exists_isSmoothing_and_toDistr_quantizeSobolev_eq_smulLeftCLM_add`
  is the operator identity: for an elliptic `p`, there are a symbol `q` of order `-m`, vanishing
  at positions outside `tsupport φ`, and a smoothing symbol `r`, both with compact spatial
  support, with `Op(q) Op(a) u = φ u + Op(r) u` for every `u ∈ H^s` and every real `s`.
* `TauCeti.Symbol.memSobolev_smulLeftCLM_of_eventually_comp_eq_id`: **interior elliptic
  regularity** for symbols `a` that are only elliptic near `tsupport φ`, in the sense that a symbol
  `e` of order `-m` is a left inverse of `a(x, ξ)` at all large frequencies and all positions near
  `tsupport φ`. If `u ∈ H^t` and `χ Op(a) u ∈ H^{s - m}` for a function `χ` of temperate growth
  equal to `1` near `tsupport φ`, then `φ u ∈ H^s`, whatever the real numbers `s` and `t`. Unlike
  the interior estimate, this does not assume that `u` already lies in `H^s`, and it only uses
  `Op(a) u` near `tsupport φ`: this is the Euclidean form of `Pu ∈ H^{s - m}_loc ⇒ u ∈ H^s_loc`.
  `TauCeti.Symbol.IsEllipticAbove.memSobolev_smulLeftCLM` is the case of a symbol `a` that agrees
  near `tsupport φ` with an elliptic `p`; for `χ = 1` its hypothesis is `Op(a) u ∈ H^{s - m}`.
* `TauCeti.Symbol.exists_contDiff_smulLeftCLM_of_eventually_comp_eq_id` and
  `TauCeti.Symbol.IsEllipticAbove.exists_contDiff_smulLeftCLM`: **hypoellipticity**. If `u ∈ H^t`
  and `χ Op(a) u` lies in every `H^σ`, for instance if `Op(a) u = 0`, then `φ u` is a smooth
  function. By the Sobolev embedding `H^s ⊆ C^k` for `s > k + n / 2`
  (`TemperedDistribution.exists_contDiff_eq_integral_of_forall_memSobolev`), this follows from
  regularity at every order `s`. Since `t` may be negative, this applies to distributions that are
  not functions.

The same holds for scalar symbols acting on arbitrary tempered distributions, with no a priori
Sobolev regularity, since the smoothing remainder `Op(r)` maps every tempered distribution into
every `H^s` (`TauCeti.Symbol.IsSmoothing.memSobolev_quantizeTempered`):

* `TauCeti.Symbol.IsEllipticAbove.exists_isSmoothing_and_quantizeTempered_eq_smulLeftCLM_add`:
  the operator identity `Op(q) Op(a) T = φ T + Op(r) T` for every tempered distribution `T`.
* `TauCeti.Symbol.IsEllipticAbove.memSobolev_smulLeftCLM_of_memSobolev_quantizeTempered`: if `T`
  is a tempered distribution with `Op(a) T ∈ H^{s - m}`, then `φ T ∈ H^s`.
* `TauCeti.Symbol.IsEllipticAbove.exists_contDiff_smulLeftCLM_eq_integral_of_forall_memSobolev`:
  **hypoellipticity**. If `Op(a) T` lies in every `H^s`, for instance `Op(a) T = 0`, then `φ T`
  is a smooth function.

The corresponding interior estimate
`‖φ u‖_{H^s} ≤ C (‖Op(a) u‖_{H^{s - m}} + ‖u‖_{H^r})` is
`TauCeti.Symbol.IsEllipticAbove.exists_norm_smulLeftCLM_le`.

## Proof outline

Write `(φ b) # a = φ (b # a)` (`TauCeti.Symbol.coefficient_sharp_of_coefficient_eq_smul`) and
expand `b # a = ∑_{k < N} sharpTerm b a k + R_N` with `R_N` of order `-N`. At a position `x` near
`tsupport φ` the terms `sharpTerm b a k` only involve the derivatives of `a` at `x`, which are
those of `p` (`TauCeti.Symbol.coefficient_sharpTerm_of_eq_smul_of_eventuallyEq`), while
`1 - ∑_{k < N} sharpTerm b p k` has order `-N` since `b` is a left parametrix symbol. Hence
`φ ((b # a) - 1)` is `φ` times a symbol of order `-N` at every position, for every `N`. On
Bessel-potential spaces, the composition theorem `TauCeti.Symbol.toDistr_quantizeSobolev_sharp`
turns this into the operator identity.

Regularity uses instead the local parametrix `q = φ e` of a symbol `a` with a left inverse `e` near
`tsupport φ`: `φ u = Op(q) (Op(a) u) - Op(sm) u - Op(rem) u` with `sm` smoothing and `rem` of
order `-1` vanishing outside `tsupport φ`
(`TauCeti.Symbol.exists_isSmoothing_toDistr_smulLeftCLM_eq_quantizeSobolev_sub_sub`). Replace `χ`
by a compactly supported cutoff `χ'` equal to `1` near `tsupport φ` with `χ' = χ' χ`, so that
`χ' Op(a) u ∈ H^{s - m}`. By locality modulo smoothing operators
(`Symbol.exists_isSmoothing_and_toDistr_quantizeSobolev_eq_quantizeSobolev_smulLeftCLM_add`),
`Op(q) (Op(a) u)` is `Op(q) (χ' Op(a) u) ∈ H^s` up to a smoothing term, and `Op(rem) u` is
`Op(rem) (ψ u)` up to a smoothing term, for a cutoff `ψ` equal to `1` near `tsupport φ`; the
latter gains one derivative on `ψ u`. Hence, for cutoffs `ψ` and `φ` supported where `e` inverts
`a` and `χ' = 1`, if `ψ u ∈ H^σ` for every such `ψ`, then `φ u ∈ H^{min s (σ + 1)}` for every such
`φ`, and `⌈s - t⌉` steps starting from `u ∈ H^t` reach `H^s`.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (4.6)–(4.11).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open scoped SchwartzMap BesselPotentialSpace ContDiff Topology

namespace TauCeti

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {m R : ℝ}
  {p a : Symbol n V W m}

/-- **The local parametrix symbol of an elliptic symbol.** Let `p` be elliptic of order `m`, let
`φ` be a compactly supported Schwartz function, and let `a` be a symbol with compact spatial support
that agrees with `p` on a neighbourhood of `tsupport φ`. There is a symbol `q` of order `-m` with
compact spatial support, vanishing at positions outside `tsupport φ`, such that `q # a - φ` is
smoothing and has compact spatial support. -/
theorem IsEllipticAbove.exists_isSmoothing_sharp_sub_ofSpatial (hp : p.IsEllipticAbove R)
    (ha : a.HasCompactSpatialSupport) {φ : 𝓢(CoordinateSpace n, ℂ)} (hφ : HasCompactSupport φ)
    (hap : ∀ᶠ x in 𝓝ˢ (tsupport φ), ∀ ξ, a.coefficient (x, ξ) = p.coefficient (x, ξ)) :
    ∃ q : Symbol n W V (-m), q.HasCompactSpatialSupport ∧
      (∀ x ∉ tsupport φ, ∀ ξ, q.coefficient (x, ξ) = 0) ∧
      let r := q.sharp a ha - inclusion (neg_add_cancel m).ge
        (ofSpatial (fun x ↦ φ x • ContinuousLinearMap.id ℂ V) ((φ.smooth ⊤).smul contDiff_const))
      r.HasCompactSpatialSupport ∧ r.IsSmoothing := by
  obtain ⟨b, hL, -⟩ := hp.exists_isAsymptoticSum_sharpTerm
  have hF := hasCompactSpatialSupport_ofSpatial_smul_id (V := V) hφ
  set F := ofSpatial (fun x ↦ φ x • ContinuousLinearMap.id ℂ V) ((φ.smooth ⊤).smul contDiff_const)
  set q := smulLeft (φ.smooth ⊤) b
  have hqb : ∀ x ξ, q.coefficient (x, ξ) = φ x • b.coefficient (x, ξ) := fun x ξ ↦
    coefficient_smulLeft _ b (x, ξ)
  have hq : q.HasCompactSpatialSupport := hasCompactSpatialSupport_smulLeft (φ.smooth ⊤) hφ b
  exact ⟨q, hq, fun x hx ξ ↦ by rw [hqb, image_eq_zero_of_notMem_tsupport hx, zero_smul],
    (hq.sharp ha).sub (hF.inclusion _), isSmoothing_sharp_sub_ofSpatial hL (φ.smooth ⊤) hqb ha hap⟩

/-- **The local parametrix identity for a target symbol.** Let `b` be a symbol of order `-m`
whose formal composition with the symbol `p` of order `m` is a symbol `c` of order `0`,
`c ∼ ∑ₖ sharpTerm b p k`, let `φ` be a compactly supported Schwartz function, and let `a` be a
symbol with compact spatial support that agrees with `p` on a neighbourhood of `tsupport φ`. There
are symbols `q(x, ξ) = φ(x) b(x, ξ)` of order `-m` and `e(x, ξ) = φ(x) c(x, ξ)` of order `0`, and a
smoothing symbol `r`, all with compact spatial support, such that
`Op(q) Op(a) u = Op(e) u + Op(r) u` for every `u ∈ H^s` and every real `s`. -/
theorem IsAsymptoticSum.exists_isSmoothing_and_toDistr_quantizeSobolev_eq_quantizeSobolev_add
    {b : Symbol n W V (-m)} {c : Symbol n V V 0}
    (hpc : IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k) (inclusion (by simp) c) (b.sharpTerm p))
    (ha : a.HasCompactSpatialSupport) {φ : 𝓢(CoordinateSpace n, ℂ)} (hφ : HasCompactSupport φ)
    (hap : ∀ᶠ x in 𝓝ˢ (tsupport φ), ∀ ξ, a.coefficient (x, ξ) = p.coefficient (x, ξ)) :
    ∃ (q : Symbol n W V (-m)) (hq : q.HasCompactSpatialSupport),
      (∀ x ξ, q.coefficient (x, ξ) = φ x • b.coefficient (x, ξ)) ∧
      ∃ (e : Symbol n V V 0) (he : e.HasCompactSpatialSupport),
        (∀ x ξ, e.coefficient (x, ξ) = φ x • c.coefficient (x, ξ)) ∧
        ∃ (r : Symbol n V V (-m + m)) (hr : r.HasCompactSpatialSupport), r.IsSmoothing ∧
          ∀ (s : ℝ) (u : H^{s}(CoordinateSpace n, V)),
            (q.quantizeSobolev hq (s - m) (a.quantizeSobolev ha s u)).toDistr =
              (e.quantizeSobolev he s u).toDistr + (r.quantizeSobolev hr s u).toDistr := by
  have hF := hasCompactSpatialSupport_ofSpatial_smul_id (V := V) hφ
  set F := ofSpatial (fun x ↦ φ x • ContinuousLinearMap.id ℂ V) ((φ.smooth ⊤).smul contDiff_const)
  set q := inclusion (zero_add (-m)).le (F.comp b)
  have hq : q.HasCompactSpatialSupport := (hF.comp_right b).inclusion _
  have hqb : ∀ x ξ, q.coefficient (x, ξ) = φ x • b.coefficient (x, ξ) := fun x ξ ↦ by
    simp [q, F]
  set e : Symbol n V V 0 := inclusion (by norm_num) (F.comp c)
  have he : e.HasCompactSpatialSupport := (hF.comp_right c).inclusion _
  have hec : ∀ x ξ, e.coefficient (x, ξ) = φ x • c.coefficient (x, ξ) := fun x ξ ↦ by
    simp [e, F]
  have he' := he.inclusion (neg_add_cancel m).ge
  have hr := (hq.sharp ha).sub he'
  refine ⟨q, hq, hqb, e, he, hec, _, hr,
    isSmoothing_sharp_sub_of_isAsymptoticSum hpc (φ.smooth ⊤) hqb ha hap hec, fun s u ↦ ?_⟩
  rw [← toDistr_quantizeSobolev_sharp hq ha,
    toDistr_quantizeSobolev_congr
      (b := inclusion (neg_add_cancel m).ge e + (q.sharp a ha - inclusion (neg_add_cancel m).ge e))
      (by simp) (hq.sharp ha) (he'.add hr) rfl,
    quantizeSobolev_add he' hr, add_apply, BesselPotentialSpace.toDistr_add,
    toDistr_quantizeSobolev_congr (by simp) he' he rfl]

/-- **The local parametrix of an elliptic operator.** Let `p` be elliptic of order `m`, let `φ`
be a compactly supported Schwartz function, and let `a` be a symbol with compact spatial support
that agrees with `p` on a neighbourhood of `tsupport φ`. There are a symbol `q` of order `-m`,
vanishing at positions outside `tsupport φ`, and a smoothing symbol `r`, both with compact spatial
support, such that `Op(q) Op(a) u = φ u + Op(r) u` for every `u ∈ H^s` and every real `s`. -/
theorem IsEllipticAbove.exists_isSmoothing_and_toDistr_quantizeSobolev_eq_smulLeftCLM_add
    (hp : p.IsEllipticAbove R) (ha : a.HasCompactSpatialSupport) {φ : 𝓢(CoordinateSpace n, ℂ)}
    (hφ : HasCompactSupport φ)
    (hap : ∀ᶠ x in 𝓝ˢ (tsupport φ), ∀ ξ, a.coefficient (x, ξ) = p.coefficient (x, ξ)) :
    ∃ (q : Symbol n W V (-m)) (hq : q.HasCompactSpatialSupport),
      (∀ x ∉ tsupport φ, ∀ ξ, q.coefficient (x, ξ) = 0) ∧
      ∃ (r : Symbol n V V (-m + m)) (hr : r.HasCompactSpatialSupport), r.IsSmoothing ∧
        ∀ (s : ℝ) (u : H^{s}(CoordinateSpace n, V)),
          (q.quantizeSobolev hq (s - m) (a.quantizeSobolev ha s u)).toDistr =
            (BesselPotentialSpace.smulLeftCLM s φ u).toDistr +
              (r.quantizeSobolev hr s u).toDistr := by
  obtain ⟨b, hL, -⟩ := hp.exists_isAsymptoticSum_sharpTerm
  obtain ⟨q, hq, hqb, e, he, hec, r, hr, hsm, hid⟩ :=
    hL.exists_isSmoothing_and_toDistr_quantizeSobolev_eq_quantizeSobolev_add ha hφ hap
  refine ⟨q, hq, fun x hx ξ ↦ by rw [hqb, image_eq_zero_of_notMem_tsupport hx, zero_smul], r, hr,
    hsm, fun s u ↦ ?_⟩
  rw [hid, toDistr_quantizeSobolev_congr (by ext ⟨x, ξ⟩; simp [hec]) he
    (hasCompactSpatialSupport_ofSpatial_smul_id hφ) rfl, toDistr_quantizeSobolev_ofSpatial_smul_id]

/-! ### Interior regularity -/

/-- Interior regularity, by induction on the number `k` of derivatives recovered: if `e` is a left
inverse of `a` at large frequencies on the open set `U`, on which `χ = 1`, and
`χ Op(a) u ∈ H^{s - m}` for `u ∈ H^t`, then `φ u ∈ H^{min s (t + k)}` for every compactly
supported Schwartz function `φ` with `tsupport φ ⊆ U`. -/
private theorem memSobolev_smulLeftCLM_min {e : Symbol n W V (-m)}
    (ha : a.HasCompactSpatialSupport) {U : Set (CoordinateSpace n)} (hU : IsOpen U)
    (he : ∀ x ∈ U, ∀ ξ, R ≤ ‖ξ‖ → e.coefficient (x, ξ) ∘L a.coefficient (x, ξ) = .id ℂ V)
    {χ : 𝓢(CoordinateSpace n, ℂ)} (hχ : HasCompactSupport χ) (hχU : ∀ x ∈ U, χ x = 1)
    {s t : ℝ} {u : H^{t}(CoordinateSpace n, V)}
    (hu : (BesselPotentialSpace.smulLeftCLM (t - m) χ
      (a.quantizeSobolev ha t u)).toDistr.MemSobolev (s - m) 2)
    (k : ℕ) : ∀ {φ : 𝓢(CoordinateSpace n, ℂ)}, HasCompactSupport φ → tsupport φ ⊆ U →
      (BesselPotentialSpace.smulLeftCLM t φ u).toDistr.MemSobolev (min s (t + k)) 2 := by
  induction k with
  | zero =>
    intro φ _ _
    exact (BesselPotentialSpace.memSobolev_toDistr _).mono (by simp)
  | succ k ih =>
    intro φ hφ hφU
    obtain ⟨ψ, hψ, hψU, hψφ⟩ := hφ.isCompact.exists_schwartzMap_cutoff hU hφU
    obtain ⟨q, hq, sm, hsmK, rem, hremK, hsm, hq0, hrem0, hid⟩ :=
      exists_isSmoothing_toDistr_smulLeftCLM_eq_quantizeSobolev_sub_sub ha he hφU
    have hχφ : ∀ᶠ x in 𝓝ˢ (tsupport φ), χ x = 1 :=
      Filter.eventually_of_mem (hU.mem_nhdsSet.2 hφU) hχU
    -- `Op(q) (Op(a) u)` only depends on `χ Op(a) u ∈ H^{s - m}`, up to a smoothing operator.
    obtain ⟨r₁, hr₁, hr₁S, hloc₁⟩ :=
      exists_isSmoothing_and_toDistr_quantizeSobolev_eq_quantizeSobolev_smulLeftCLM_add hq hq0 hχ
        hχφ
    have h₁ : (q.quantizeSobolev hq (t - m) (a.quantizeSobolev ha t u)).toDistr.MemSobolev
        (min s (t + (k + 1 : ℕ))) 2 := by
      rw [hloc₁ (t - m) (a.quantizeSobolev ha t u)]
      refine TemperedDistribution.MemSobolev.add
        ((memSobolev_toDistr_quantizeSobolev hq hu).mono ?_)
        (hr₁S.memSobolev_toDistr_quantizeSobolev hr₁ _ _ _)
      linarith [min_le_left s (t + (k + 1 : ℕ))]
    -- `Op(rem) u` only depends on `ψ u`, which lies in `H^{min s (t + k)}` by induction, up to a
    -- smoothing operator, and `rem` has order `-1`.
    obtain ⟨r₂, hr₂, hr₂S, hloc₂⟩ :=
      exists_isSmoothing_and_toDistr_quantizeSobolev_eq_quantizeSobolev_smulLeftCLM_add hremK
        hrem0 hψ hψφ
    have h₂ : (rem.quantizeSobolev hremK t u).toDistr.MemSobolev (min s (t + (k + 1 : ℕ))) 2 := by
      rw [hloc₂ t u]
      refine TemperedDistribution.MemSobolev.add
        ((memSobolev_toDistr_quantizeSobolev hremK (ih hψ hψU)).mono ?_)
        (hr₂S.memSobolev_toDistr_quantizeSobolev hr₂ _ _ _)
      have hmin : min s (t + (k + 1 : ℕ)) ≤ min s (t + k) + 1 := by
        rw [← min_add_add_right]
        push_cast
        exact min_le_min (by linarith) (by linarith)
      push_cast at hmin ⊢
      linarith
    rw [hid t u]
    exact (h₁.sub (hsm.memSobolev_toDistr_quantizeSobolev hsmK _ _ _)).sub h₂

/-- **Interior elliptic regularity for locally elliptic symbols.** Let `a` be a symbol of order `m`
with compact spatial support and `φ` a Schwartz function, and suppose that a symbol `e` of order
`-m` is a left inverse of `a(x, ξ)` at all frequencies `‖ξ‖ ≥ R` and all positions `x` near
`tsupport φ` (unless `V` is trivial, this forces `φ` to have compact support). Let `χ` be a
function of temperate growth equal to `1` near `tsupport φ`, for instance `χ = 1`. If `u ∈ H^t` and
`χ Op(a) u ∈ H^{s - m}`, then `φ u ∈ H^s`, for all real `s` and `t`. -/
theorem memSobolev_smulLeftCLM_of_eventually_comp_eq_id {e : Symbol n W V (-m)}
    (ha : a.HasCompactSpatialSupport) {φ : 𝓢(CoordinateSpace n, ℂ)}
    (he : ∀ᶠ x in 𝓝ˢ (tsupport φ), ∀ ξ, R ≤ ‖ξ‖ →
      e.coefficient (x, ξ) ∘L a.coefficient (x, ξ) = .id ℂ V)
    {χ : CoordinateSpace n → ℂ} (hχ : χ.HasTemperateGrowth)
    (hχφ : ∀ᶠ x in 𝓝ˢ (tsupport φ), χ x = 1) {s t : ℝ} {u : H^{t}(CoordinateSpace n, V)}
    (hu : (TemperedDistribution.smulLeftCLM W χ (a.quantizeSobolev ha t u).toDistr).MemSobolev
      (s - m) 2) :
    (BesselPotentialSpace.smulLeftCLM t φ u).toDistr.MemSobolev s 2 := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · have h0 : (BesselPotentialSpace.smulLeftCLM t φ u).toDistr =
        (0 : H^{s}(CoordinateSpace n, V)).toDistr := by
      ext ψ
      exact Subsingleton.elim _ _
    rw [h0]
    exact BesselPotentialSpace.memSobolev_toDistr _
  obtain ⟨U, hU, hφU, hUe⟩ := eventually_nhdsSet_iff_exists.1 (he.and hχφ)
  -- For nontrivial `V`, `a` is only invertible at positions in a compact set.
  have hφ : HasCompactSupport φ :=
    (ha.isCompact_closure_of_comp_eq_id fun x hx ↦ (hUe x hx).1).of_isClosed_subset
      (isClosed_tsupport φ) (hφU.trans subset_closure)
  -- Replace `χ` by a compactly supported cutoff `χ'` with `χ' = χ' χ`.
  obtain ⟨χ', hχ', hχ'U, hχ'φ⟩ := hφ.isCompact.exists_schwartzMap_cutoff hU hφU
  obtain ⟨U', hU', hφU', hU'χ'⟩ := eventually_nhdsSet_iff_exists.1 hχ'φ
  have hχχ' : χ * χ' = χ' := funext fun x ↦ by
    by_cases hx : x ∈ tsupport χ'
    · simp [(hUe x (hχ'U hx)).2]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hu' : (BesselPotentialSpace.smulLeftCLM (t - m) χ'
      (a.quantizeSobolev ha t u)).toDistr.MemSobolev (s - m) 2 := by
    have h := hu.smulLeftCLM χ'
    rwa [TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hχ χ'.hasTemperateGrowth, hχχ',
      ← BesselPotentialSpace.toDistr_smulLeftCLM] at h
  have h := memSobolev_smulLeftCLM_min ha (hU.inter hU') (fun x hx ↦ (hUe x hx.1).1) hχ'
    (fun x hx ↦ hU'χ' x hx.2) hu' ⌈s - t⌉₊ hφ (Set.subset_inter hφU hφU')
  rwa [min_eq_left (by linarith [Nat.le_ceil (s - t)])] at h

/-- **Interior elliptic regularity.** Let `p` be elliptic of order `m`, let `φ` be a Schwartz
function, and let `a` be a symbol with compact spatial support that agrees with `p` on a
neighbourhood of `tsupport φ`. Let `χ` be a function of temperate growth equal to `1` near
`tsupport φ`, for instance `χ = 1`. If `u ∈ H^t` and `χ Op(a) u ∈ H^{s - m}`, then `φ u ∈ H^s`,
for all real `s` and `t`. -/
theorem IsEllipticAbove.memSobolev_smulLeftCLM (hp : p.IsEllipticAbove R)
    (ha : a.HasCompactSpatialSupport) {φ : 𝓢(CoordinateSpace n, ℂ)}
    (hap : ∀ᶠ x in 𝓝ˢ (tsupport φ), ∀ ξ, a.coefficient (x, ξ) = p.coefficient (x, ξ))
    {χ : CoordinateSpace n → ℂ} (hχ : χ.HasTemperateGrowth)
    (hχφ : ∀ᶠ x in 𝓝ˢ (tsupport φ), χ x = 1) {s t : ℝ} {u : H^{t}(CoordinateSpace n, V)}
    (hu : (TemperedDistribution.smulLeftCLM W χ (a.quantizeSobolev ha t u).toDistr).MemSobolev
      (s - m) 2) :
    (BesselPotentialSpace.smulLeftCLM t φ u).toDistr.MemSobolev s 2 := by
  obtain ⟨e, R', he⟩ := exists_isEllipticAbove_iff.1 ⟨R, hp⟩
  exact memSobolev_smulLeftCLM_of_eventually_comp_eq_id (e := e) (R := R') ha
    (hap.mono fun x hx ξ hξ ↦ by rw [hx]; exact (he x ξ hξ).1) hχ hχφ hu

/-- **Hypoellipticity of locally elliptic symbols.** Let `a` be a symbol of order `m` with compact
spatial support and `φ` a Schwartz function, and suppose that a symbol `e` of order `-m` is a left
inverse of `a(x, ξ)` at all frequencies `‖ξ‖ ≥ R` and all positions `x` near `tsupport φ`. Let `χ`
be a function of temperate growth equal to `1` near `tsupport φ`. If `u ∈ H^t` and `χ Op(a) u` lies
in every `H^σ`, then `φ u` is a smooth function `g`: it pairs with every Schwartz function `ψ` as
`∫ ψ • g`. -/
theorem exists_contDiff_smulLeftCLM_of_eventually_comp_eq_id {e : Symbol n W V (-m)}
    (ha : a.HasCompactSpatialSupport) {φ : 𝓢(CoordinateSpace n, ℂ)}
    (he : ∀ᶠ x in 𝓝ˢ (tsupport φ), ∀ ξ, R ≤ ‖ξ‖ →
      e.coefficient (x, ξ) ∘L a.coefficient (x, ξ) = .id ℂ V)
    {χ : CoordinateSpace n → ℂ} (hχ : χ.HasTemperateGrowth)
    (hχφ : ∀ᶠ x in 𝓝ˢ (tsupport φ), χ x = 1) {t : ℝ} {u : H^{t}(CoordinateSpace n, V)}
    (hu : ∀ σ : ℝ,
      (TemperedDistribution.smulLeftCLM W χ (a.quantizeSobolev ha t u).toDistr).MemSobolev σ 2) :
    ∃ g : CoordinateSpace n → V, ContDiff ℝ ∞ g ∧ ∀ ψ : 𝓢(CoordinateSpace n, ℂ),
      (BesselPotentialSpace.smulLeftCLM t φ u).toDistr ψ = ∫ x, ψ x • g x :=
  TemperedDistribution.exists_contDiff_eq_integral_of_forall_memSobolev fun s ↦
    memSobolev_smulLeftCLM_of_eventually_comp_eq_id ha he hχ hχφ (hu (s - m))

/-- **Hypoellipticity of elliptic symbols.** Let `p` be elliptic of order `m`, let `φ` be a
Schwartz function, and let `a` be a symbol with compact spatial support that agrees with `p` on a
neighbourhood of `tsupport φ`. Let `χ` be a function of temperate growth equal to `1` near
`tsupport φ`, for instance `χ = 1`. If `u ∈ H^t` and `χ Op(a) u` lies in every `H^σ`, for instance
if `Op(a) u = 0`, then `φ u` is a smooth function `g`: it pairs with every Schwartz function `ψ` as
`∫ ψ • g`. -/
theorem IsEllipticAbove.exists_contDiff_smulLeftCLM (hp : p.IsEllipticAbove R)
    (ha : a.HasCompactSpatialSupport) {φ : 𝓢(CoordinateSpace n, ℂ)}
    (hap : ∀ᶠ x in 𝓝ˢ (tsupport φ), ∀ ξ, a.coefficient (x, ξ) = p.coefficient (x, ξ))
    {χ : CoordinateSpace n → ℂ} (hχ : χ.HasTemperateGrowth)
    (hχφ : ∀ᶠ x in 𝓝ˢ (tsupport φ), χ x = 1) {t : ℝ} {u : H^{t}(CoordinateSpace n, V)}
    (hu : ∀ σ : ℝ,
      (TemperedDistribution.smulLeftCLM W χ (a.quantizeSobolev ha t u).toDistr).MemSobolev σ 2) :
    ∃ g : CoordinateSpace n → V, ContDiff ℝ ∞ g ∧ ∀ ψ : 𝓢(CoordinateSpace n, ℂ),
      (BesselPotentialSpace.smulLeftCLM t φ u).toDistr ψ = ∫ x, ψ x • g x :=
  TemperedDistribution.exists_contDiff_eq_integral_of_forall_memSobolev fun s ↦
    hp.memSobolev_smulLeftCLM ha hap hχ hχφ (hu (s - m))

/-! ### Tempered distributions -/

section Tempered

variable {p a : Symbol n ℂ ℂ m}

/-- **The local parametrix on tempered distributions.** Let `p` be a scalar symbol elliptic of
order `m`, let `φ` be a compactly supported Schwartz function, and let `a` be a symbol with compact
spatial support that agrees with `p` on a neighbourhood of `tsupport φ`. There are a symbol `q` of
order `-m` and a smoothing symbol `r`, both with compact spatial support, such that
`Op(q) Op(a) T = φ T + Op(r) T` for every tempered distribution `T`. -/
theorem IsEllipticAbove.exists_isSmoothing_and_quantizeTempered_eq_smulLeftCLM_add
    (F : Type*) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousConstSMul ℂ F] (hp : p.IsEllipticAbove R) (ha : a.HasCompactSpatialSupport)
    {φ : 𝓢(CoordinateSpace n, ℂ)} (hφ : HasCompactSupport φ)
    (hap : ∀ᶠ x in 𝓝ˢ (tsupport φ), ∀ ξ, a.coefficient (x, ξ) = p.coefficient (x, ξ)) :
    ∃ (q : Symbol n ℂ ℂ (-m)) (hq : q.HasCompactSpatialSupport) (r : Symbol n ℂ ℂ (-m + m))
      (hr : r.HasCompactSpatialSupport), r.IsSmoothing ∧
        ∀ T : 𝓢'(CoordinateSpace n, F),
          quantizeTempered F q hq.isUniform (quantizeTempered F a ha.isUniform T) =
            TemperedDistribution.smulLeftCLM F φ T + quantizeTempered F r hr.isUniform T := by
  obtain ⟨q, hq, -, hr, hrS⟩ := hp.exists_isSmoothing_sharp_sub_ofSpatial ha hφ hap
  have hF := hasCompactSpatialSupport_ofSpatial_smul_id (V := ℂ) hφ
  set M := ofSpatial (fun x ↦ φ x • ContinuousLinearMap.id ℂ ℂ) ((φ.smooth ⊤).smul contDiff_const)
  have hF' := hF.inclusion (neg_add_cancel m).ge
  refine ⟨q, hq, _, hr, hrS, fun T ↦ ?_⟩
  rw [← ContinuousLinearMap.comp_apply, ← quantizeTempered_sharp hq.isUniform ha,
    quantizeTempered_congr (hq.sharp ha).isUniform (hF'.add hr).isUniform
      (b := inclusion (neg_add_cancel m).ge M + (q.sharp a ha - inclusion (neg_add_cancel m).ge M))
      (by simp),
    quantizeTempered_add hF'.isUniform hr.isUniform, add_apply,
    quantizeTempered_inclusion hF.isUniform, quantizeTempered_ofSpatial_smul_id]

/-- **Interior elliptic regularity for tempered distributions.** Let `p` be a scalar symbol
elliptic of order `m`, let `φ` be a compactly supported Schwartz function, and let `a` be a symbol
with compact spatial support that agrees with `p` on a neighbourhood of `tsupport φ`. If
`Op(a) T ∈ H^{s - m}` for a tempered distribution `T`, then `φ T ∈ H^s`. Unlike
`TauCeti.Symbol.IsEllipticAbove.memSobolev_smulLeftCLM`, `T` is not assumed to lie in any
Bessel-potential space: the smoothing remainder of the local parametrix maps every tempered
distribution into every `H^s` (`TauCeti.Symbol.IsSmoothing.memSobolev_quantizeTempered`). -/
theorem IsEllipticAbove.memSobolev_smulLeftCLM_of_memSobolev_quantizeTempered
    (hp : p.IsEllipticAbove R) (ha : a.HasCompactSpatialSupport) {φ : 𝓢(CoordinateSpace n, ℂ)}
    (hφ : HasCompactSupport φ)
    (hap : ∀ᶠ x in 𝓝ˢ (tsupport φ), ∀ ξ, a.coefficient (x, ξ) = p.coefficient (x, ξ))
    {s : ℝ} {T : 𝓢'(CoordinateSpace n, ℂ)}
    (hT : (quantizeTempered ℂ a ha.isUniform T).MemSobolev (s - m) 2) :
    (TemperedDistribution.smulLeftCLM ℂ φ T).MemSobolev s 2 := by
  obtain ⟨q, hq, r, hr, hrS, h⟩ :=
    hp.exists_isSmoothing_and_quantizeTempered_eq_smulLeftCLM_add ℂ ha hφ hap
  have h₁ := memSobolev_quantizeTempered hq hT
  rw [h, sub_neg_eq_add, sub_add_cancel] at h₁
  convert h₁.sub (hrS.memSobolev_quantizeTempered hr T s) using 1
  exact (add_sub_cancel_right _ _).symm

/-- **Hypoellipticity on tempered distributions.** Let `p` be a scalar symbol elliptic of order
`m`, let `φ` be a compactly supported Schwartz function, and let `a` be a symbol with compact
spatial support that agrees with `p` on a neighbourhood of `tsupport φ`. If `Op(a) T` lies in
every `H^s` for a tempered distribution `T`, for instance if `Op(a) T = 0`, then `φ T` is a smooth
function `g`: it pairs with every Schwartz function `ψ` as `∫ ψ • g`. -/
theorem IsEllipticAbove.exists_contDiff_smulLeftCLM_eq_integral_of_forall_memSobolev
    (hp : p.IsEllipticAbove R) (ha : a.HasCompactSpatialSupport) {φ : 𝓢(CoordinateSpace n, ℂ)}
    (hφ : HasCompactSupport φ)
    (hap : ∀ᶠ x in 𝓝ˢ (tsupport φ), ∀ ξ, a.coefficient (x, ξ) = p.coefficient (x, ξ))
    {T : 𝓢'(CoordinateSpace n, ℂ)}
    (hT : ∀ s, (quantizeTempered ℂ a ha.isUniform T).MemSobolev s 2) :
    ∃ g : CoordinateSpace n → ℂ, ContDiff ℝ ∞ g ∧
      ∀ ψ : 𝓢(CoordinateSpace n, ℂ), TemperedDistribution.smulLeftCLM ℂ φ T ψ = ∫ x, ψ x • g x :=
  TemperedDistribution.exists_contDiff_eq_integral_of_forall_memSobolev fun s ↦
    hp.memSobolev_smulLeftCLM_of_memSobolev_quantizeTempered ha hφ hap (hT (s - m))

end Tempered

end Symbol

end TauCeti
