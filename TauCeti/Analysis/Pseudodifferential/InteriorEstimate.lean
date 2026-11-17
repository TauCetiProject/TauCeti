/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Sobolev
public import TauCeti.Analysis.Pseudodifferential.Symbol.Elliptic
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff

/-!
# Interior estimates for elliptic pseudodifferential operators

Let `a` be a symbol of order `m` on `ℝⁿ` with compact spatial support, with values in operators
`V →L[ℂ] W` between complex Hilbert spaces, and let `φ` be a compactly supported Schwartz
function. Suppose that `a` is elliptic near the support of `φ`, in the sense that a symbol `e` of
order `-m` is a left inverse of `a(x, ξ)` at all large frequencies `‖ξ‖ ≥ R` and all positions `x`
near `tsupport φ`. Then for all real `r ≤ s` there is a constant `C` with

`‖φ u‖_{H^s} ≤ C (‖Op(a) u‖_{H^{s - m}} + ‖u‖_{H^r})` for all `u ∈ H^s(ℝⁿ; V)`

(`TauCeti.Symbol.exists_norm_smulLeftCLM_le_of_eventually_comp_eq_id`). The norm of `φ u` in
`H^s` is controlled by the norm of `Op(a) u` in `H^{s - m}`: near `tsupport φ`, the `m`
derivatives that `Op(a)` loses are recovered, up to an arbitrarily weak norm of `u`. This is the
estimate behind local elliptic regularity. The typical case is a symbol `a` agreeing near
`tsupport φ` with a symbol `p` elliptic above some radius (`TauCeti.Symbol.IsEllipticAbove`),
such as the localization `a = ψ p` by a function `ψ` equal to `1` near `tsupport φ`, so that
`Op(a) u = ψ Op(p) u` (`TauCeti.Symbol.IsEllipticAbove.exists_norm_smulLeftCLM_le`). Only a left
inverse of the symbol is needed: the estimate holds for injectively elliptic symbols, between
fibres of different dimensions.

## Proof outline

The symbol `q = φ e` of order `-m` is a parametrix of `a` near `tsupport φ`: by the composition
expansion, `q # a = φ + (q ∘ a - φ) + (q # a - q ∘ a)`, where `q ∘ a - φ` vanishes at large
frequencies, hence is smoothing, and `q # a - q ∘ a` has order `-1`
(`TauCeti.Symbol.sharp_eq_comp_add_sharpRemainder_one`). Since `Op(q # a) = Op(q) ∘ Op(a)`
(`TauCeti.Symbol.toDistr_quantizeSobolev_sharp`), this gives
`‖φ u‖_{H^s} ≤ C (‖Op(a) u‖_{H^{s - m}} + ‖Op(q # a - q ∘ a) u‖_{H^s} + ‖u‖_{H^r})`. The symbol
`q # a - q ∘ a` vanishes outside `tsupport φ`, so by locality modulo smoothing operators
(`TauCeti.Symbol.exists_norm_quantizeSobolev_le_smulLeftCLM`) its term is bounded by `‖χ u‖` in
`H^{s - 1}` for a cutoff `χ` equal to `1` near `tsupport φ`, plus `‖u‖_{H^r}`. The same estimate
for `χ` in place of `φ`, at the order `s - 1`, closes an induction on the number of derivatives
`s - r` to recover.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (4.6)–(4.11).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open BesselPotentialSpace
open scoped SchwartzMap BesselPotentialSpace ContDiff Topology

namespace TauCeti

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {m R : ℝ}
  {a : Symbol n V W m} {e : Symbol n W V (-m)}

/-- The decomposition `F = q # a - (q ∘ a - F) - (q # a - q ∘ a)` behind the parametrix
estimate, on `H^s`, with `Op(q # a) = Op(q) ∘ Op(a)`. -/
private theorem toDistr_quantizeSobolev_eq_sub_sub (ha : a.HasCompactSpatialSupport)
    {q : Symbol n W V (0 + -m)} (hq : q.HasCompactSpatialSupport) {F : Symbol n V V 0}
    (hF : F.HasCompactSpatialSupport)
    (hsmK : (q.comp a - Symbol.inclusion (le_of_eq (by ring)) F).HasCompactSpatialSupport) (s : ℝ)
    (u : H^{s}(CoordinateSpace n, V)) :
    (F.quantizeSobolev hF s u).toDistr =
      (q.quantizeSobolev hq (s - m) (a.quantizeSobolev ha s u)).toDistr -
        ((q.comp a - Symbol.inclusion (le_of_eq (by ring)) F).quantizeSobolev hsmK s u).toDistr -
          ((q.sharp a ha - q.comp a).quantizeSobolev ((hq.sharp ha).sub (hq.comp_right a))
            s u).toDistr := by
  rw [← toDistr_quantizeSobolev_sharp hq ha,
    ← toDistr_quantizeSobolev_sub_apply _ _ ((hq.sharp ha).sub hsmK),
    ← toDistr_quantizeSobolev_sub_apply _ _
      (((hq.sharp ha).sub hsmK).sub ((hq.sharp ha).sub (hq.comp_right a)))]
  refine toDistr_quantizeSobolev_congr ?_ hF _ rfl
  funext p
  simp

/-- One step of the interior estimate: the parametrix `q = φ e` of `a` gives
`‖φ u‖_{H^s} ≤ C (‖Op(a) u‖_{H^{s - m}} + ‖χ u‖_{H^{s - 1}} + ‖u‖_{H^r})` for a cutoff `χ` equal
to `1` near `tsupport φ`. -/
private theorem exists_norm_smulLeftCLM_le_step (ha : a.HasCompactSpatialSupport)
    {U : Set (CoordinateSpace n)}
    (he : ∀ x ∈ U, ∀ ξ, R ≤ ‖ξ‖ → e.coefficient (x, ξ) ∘L a.coefficient (x, ξ) = .id ℂ V)
    {φ χ : 𝓢(CoordinateSpace n, ℂ)} (hφ : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
    (hχ : HasCompactSupport χ) (hχφ : ∀ᶠ x in 𝓝ˢ (tsupport φ), χ x = 1) {r s : ℝ}
    (hrs : r ≤ s) :
    ∃ C, ∀ u : H^{s}(CoordinateSpace n, V), ‖smulLeftCLM s φ u‖ ≤
      C * (‖a.quantizeSobolev ha s u‖ +
        ‖smulLeftCLM (s - 1) χ (BesselPotentialSpace.inclusion (sub_le_self s zero_le_one) u)‖ +
          ‖BesselPotentialSpace.inclusion hrs u‖) := by
  have hF := hasCompactSpatialSupport_ofSpatial_smul_id (V := V) hφ
  set F := ofSpatial (fun x ↦ φ x • ContinuousLinearMap.id ℂ V) ((φ.smooth ⊤).smul contDiff_const)
  have hφ0 : ∀ x ∉ tsupport φ, φ x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
  -- The parametrix symbol `q = φ e`: `q ∘ a - φ` vanishes at large frequencies, and
  -- `q # a - q ∘ a` is a symbol `rem` of order `-1` vanishing outside `tsupport φ`.
  set q := F.comp e
  have hq : q.HasCompactSpatialSupport := hF.comp_right e
  set sm := q.comp a - Symbol.inclusion (le_of_eq (by ring)) F
  have hsm : sm.IsSmoothing := isSmoothing_of_coefficient_eq_zero R fun x ξ hξ ↦ by
    by_cases hx : x ∈ tsupport φ
    · simp only [sm, q, F, coefficient_sub, coefficient_comp, coefficient_inclusion,
        coefficient_ofSpatial, Pi.sub_apply, he x (hφU hx) ξ hξ, ContinuousLinearMap.smul_comp,
        ContinuousLinearMap.id_comp, sub_self]
    · simp [sm, q, F, hφ0 x hx]
  have hsmK : sm.HasCompactSpatialSupport := (hq.comp_right a).sub (hF.inclusion _)
  set rem := q.sharpRemainder a ha 1
  have hrem : (q.sharp a ha - q.comp a).coefficient = rem.coefficient := by
    rw [sharp_eq_comp_add_sharpRemainder_one ha, add_sub_cancel_left, coefficient_inclusion]
  have hremK : rem.HasCompactSpatialSupport :=
    ((hq.sharp ha).sub (hq.comp_right a)).of_coefficient_eq hrem.symm
  have hrem0 : ∀ x ∉ tsupport φ, ∀ ξ, rem.coefficient (x, ξ) = 0 := fun x hx ξ ↦ by
    rw [← hrem]
    simp [q, F, hφ0 x hx]
  obtain ⟨C₁, hC₁⟩ := exists_norm_quantizeSobolev_le_smulLeftCLM hremK hrem0 hχ hχφ
    (min_le_right r (s - 1))
  obtain ⟨T, hT⟩ := hsm.exists_continuousLinearMap_toDistr_quantizeSobolev_eq hsmK r s
  refine ⟨‖q.quantizeSobolev hq (s - m)‖ + ‖T‖ + max C₁ 0, fun u ↦ ?_⟩
  set v := BesselPotentialSpace.inclusion (sub_le_self s zero_le_one) u
  set w := T (BesselPotentialSpace.inclusion hrs u)
  have hw := hT (toDistr_inclusion hrs u).symm
  have hwle : ‖w‖ ≤ ‖T‖ * ‖BesselPotentialSpace.inclusion hrs u‖ := T.le_opNorm _
  -- `φ u = Op(q) (Op(a) u) - w - Op(rem) u`, where `w = Op(sm) u`.
  have hφu : smulLeftCLM s φ u =
      BesselPotentialSpace.inclusion (le_of_eq (by ring))
          (q.quantizeSobolev hq (s - m) (a.quantizeSobolev ha s u)) - w -
        BesselPotentialSpace.inclusion (le_of_eq (by push_cast; ring))
          (rem.quantizeSobolev hremK (s - 1) v) := by
    refine BesselPotentialSpace.ext ?_
    rw [← toDistr_quantizeSobolev_ofSpatial_smul_id φ hF,
      toDistr_quantizeSobolev_eq_sub_sub ha hq hF hsmK, toDistr_sub, toDistr_sub,
      toDistr_inclusion, toDistr_inclusion, ← hw,
      toDistr_quantizeSobolev_congr hrem _ hremK (toDistr_inclusion _ u).symm]
  have hZ : ‖rem.quantizeSobolev hremK (s - 1) v‖ ≤
      max C₁ 0 * (‖smulLeftCLM (s - 1) χ v‖ + ‖BesselPotentialSpace.inclusion hrs u‖) := by
    refine (hC₁ v).trans ?_
    have h : ‖BesselPotentialSpace.inclusion (min_le_right r (s - 1)) v‖ ≤
        ‖BesselPotentialSpace.inclusion hrs u‖ :=
      norm_le_of_toDistr_eq (min_le_left r (s - 1)) (by simp [v])
    gcongr
    exact le_max_left _ _
  have hX := (q.quantizeSobolev hq (s - m)).le_opNorm (a.quantizeSobolev ha s u)
  rw [hφu]
  refine (norm_sub_le _ _).trans ((add_le_add ((norm_sub_le _ _).trans
    (add_le_add ((norm_inclusion_apply_le _ _).trans hX) hwle))
      ((norm_inclusion_apply_le _ _).trans hZ)).trans ?_)
  nlinarith [le_max_right C₁ 0, norm_nonneg (q.quantizeSobolev hq (s - m)), norm_nonneg T,
    norm_nonneg (a.quantizeSobolev ha s u), norm_nonneg (smulLeftCLM (s - 1) χ v),
    norm_nonneg (BesselPotentialSpace.inclusion hrs u)]

/-- The interior estimate, by induction on the number `k ≥ s - r` of derivatives to recover. -/
private theorem exists_norm_smulLeftCLM_le_of_sub_le (ha : a.HasCompactSpatialSupport)
    {U : Set (CoordinateSpace n)} (hU : IsOpen U)
    (he : ∀ x ∈ U, ∀ ξ, R ≤ ‖ξ‖ → e.coefficient (x, ξ) ∘L a.coefficient (x, ξ) = .id ℂ V)
    (r : ℝ) (k : ℕ) :
    ∀ (s : ℝ) (hrs : r ≤ s), s - r ≤ k → ∀ {φ : 𝓢(CoordinateSpace n, ℂ)},
      HasCompactSupport φ → tsupport φ ⊆ U → ∃ C, ∀ u : H^{s}(CoordinateSpace n, V),
        ‖smulLeftCLM s φ u‖ ≤
          C * (‖a.quantizeSobolev ha s u‖ + ‖BesselPotentialSpace.inclusion hrs u‖) := by
  induction k with
  | zero =>
    intro s hrs hsr φ _ _
    refine ⟨‖(smulLeftCLM s φ : H^{s}(CoordinateSpace n, V) →L[ℂ] _)‖, fun u ↦ ?_⟩
    have h : ‖u‖ ≤ ‖BesselPotentialSpace.inclusion hrs u‖ :=
      norm_le_of_toDistr_eq (by push_cast at hsr; linarith) (toDistr_inclusion hrs u)
    calc ‖smulLeftCLM s φ u‖ ≤ ‖(smulLeftCLM s φ : H^{s}(CoordinateSpace n, V) →L[ℂ] _)‖ * ‖u‖ :=
          (smulLeftCLM s φ).le_opNorm u
      _ ≤ _ := by gcongr; exact le_add_of_nonneg_left (norm_nonneg _) |>.trans' h
  | succ k ih =>
    intro s hrs hsr φ hφ hφU
    obtain ⟨χ, hχ, hχU, hχφ⟩ := hφ.isCompact.exists_schwartzMap_cutoff hU hφU
    obtain ⟨C₁, hC₁⟩ := exists_norm_smulLeftCLM_le_step ha he hφ hφU hχ hχφ hrs
    -- It remains to bound `χ u` in `H^{s - 1}`.
    obtain ⟨C₂, hC₂⟩ : ∃ C₂, ∀ u : H^{s}(CoordinateSpace n, V),
        ‖smulLeftCLM (s - 1) χ (BesselPotentialSpace.inclusion (sub_le_self s zero_le_one) u)‖ ≤
          C₂ * (‖a.quantizeSobolev ha s u‖ + ‖BesselPotentialSpace.inclusion hrs u‖) := by
      rcases le_or_gt r (s - 1) with hr | hr
      · obtain ⟨C, hC⟩ := ih (s - 1) hr (by push_cast at hsr; linarith) hχ hχU
        refine ⟨max C 0, fun u ↦ (hC _).trans ?_⟩
        have hP : ‖a.quantizeSobolev ha (s - 1)
            (BesselPotentialSpace.inclusion (sub_le_self s zero_le_one) u)‖ ≤
              ‖a.quantizeSobolev ha s u‖ :=
          norm_le_of_toDistr_eq (by linarith)
            (toDistr_quantizeSobolev_congr rfl ha ha (toDistr_inclusion _ u).symm)
        rw [BesselPotentialSpace.inclusion_inclusion]
        gcongr
        · exact le_max_left _ _
      · refine ⟨‖(smulLeftCLM (s - 1) χ : H^{s - 1}(CoordinateSpace n, V) →L[ℂ] _)‖,
          fun u ↦ ((smulLeftCLM (s - 1) χ).le_opNorm _).trans ?_⟩
        have h : ‖BesselPotentialSpace.inclusion (sub_le_self s zero_le_one) u‖ ≤
            ‖BesselPotentialSpace.inclusion hrs u‖ :=
          norm_le_of_toDistr_eq hr.le (by simp)
        gcongr
        exact le_add_of_nonneg_left (norm_nonneg _) |>.trans' h
    refine ⟨max C₁ 0 * (1 + max C₂ 0), fun u ↦ (hC₁ u).trans ?_⟩
    have hB := (hC₂ u).trans (mul_le_mul_of_nonneg_right (le_max_left C₂ 0)
      (add_nonneg (norm_nonneg _) (norm_nonneg _)))
    nlinarith [le_max_left C₁ 0, le_max_right C₁ 0, le_max_right C₂ 0,
      norm_nonneg (a.quantizeSobolev ha s u), norm_nonneg (BesselPotentialSpace.inclusion hrs u),
      norm_nonneg
        (smulLeftCLM (s - 1) χ (BesselPotentialSpace.inclusion (sub_le_self s zero_le_one) u))]

/-- **Interior elliptic estimate.** Let `a` be a symbol of order `m` with compact spatial support,
and `φ` a compactly supported Schwartz function. If a symbol `e` of order `-m` is a left inverse of
`a(x, ξ)` at all frequencies `‖ξ‖ ≥ R` and all positions `x` in a neighbourhood of `tsupport φ`,
then for all real `r ≤ s` there is `C` with

`‖φ u‖_{H^s} ≤ C (‖Op(a) u‖_{H^{s - m}} + ‖u‖_{H^r})` for every `u ∈ H^s(ℝⁿ; V)`. -/
theorem exists_norm_smulLeftCLM_le_of_eventually_comp_eq_id (ha : a.HasCompactSpatialSupport)
    {φ : 𝓢(CoordinateSpace n, ℂ)} (hφ : HasCompactSupport φ)
    (he : ∀ᶠ x in 𝓝ˢ (tsupport φ), ∀ ξ, R ≤ ‖ξ‖ →
      e.coefficient (x, ξ) ∘L a.coefficient (x, ξ) = .id ℂ V)
    {r s : ℝ} (hrs : r ≤ s) :
    ∃ C, ∀ u : H^{s}(CoordinateSpace n, V),
      ‖smulLeftCLM s φ u‖ ≤
        C * (‖a.quantizeSobolev ha s u‖ + ‖BesselPotentialSpace.inclusion hrs u‖) := by
  obtain ⟨U, hU, hφU, heU⟩ := eventually_nhdsSet_iff_exists.1 he
  exact exists_norm_smulLeftCLM_le_of_sub_le ha hU heU r ⌈s - r⌉₊ s hrs (Nat.le_ceil _) hφ hφU

/-- **Interior estimate for elliptic operators.** Let `p` be a symbol of order `m` elliptic above
some radius, `φ` a compactly supported Schwartz function, and `a` a symbol with compact spatial
support that agrees with `p` on a neighbourhood of `tsupport φ`, for instance the localization
`a = ψ p` by a function `ψ` equal to `1` near `tsupport φ`, so that `Op(a) = ψ Op(p)`. Then for all
real `r ≤ s` there is `C` with

`‖φ u‖_{H^s} ≤ C (‖Op(a) u‖_{H^{s - m}} + ‖u‖_{H^r})` for every `u ∈ H^s(ℝⁿ; V)`. -/
theorem IsEllipticAbove.exists_norm_smulLeftCLM_le {p : Symbol n V W m} (hp : p.IsEllipticAbove R)
    (ha : a.HasCompactSpatialSupport) {φ : 𝓢(CoordinateSpace n, ℂ)} (hφ : HasCompactSupport φ)
    (hap : ∀ᶠ x in 𝓝ˢ (tsupport φ), ∀ ξ, a.coefficient (x, ξ) = p.coefficient (x, ξ))
    {r s : ℝ} (hrs : r ≤ s) :
    ∃ C, ∀ u : H^{s}(CoordinateSpace n, V),
      ‖smulLeftCLM s φ u‖ ≤
        C * (‖a.quantizeSobolev ha s u‖ + ‖BesselPotentialSpace.inclusion hrs u‖) := by
  obtain ⟨e, R', he⟩ := exists_isEllipticAbove_iff.1 ⟨R, hp⟩
  refine exists_norm_smulLeftCLM_le_of_eventually_comp_eq_id (e := e) (R := R') ha hφ
    (hap.mono fun x hx ξ hξ ↦ ?_) hrs
  rw [hx]
  exact (he x ξ hξ).1

end Symbol

end TauCeti
