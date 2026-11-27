/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.DiscCharge.Continuous
public import TauCeti.Geometry.Symplectic.Manifold.LimitZeroCharge
public import TauCeti.Analysis.PDE.SeibergWitten.ZeroSet.Limit
import TauCeti.Topology.Circle.Normalize
import TauCeti.Topology.Compactness.Compact

/-!
# The limit of the framed charges along a sequence of abelian Higgs pairs

Let `(bₖ, αₖ)` be a family of abelian Higgs pairs on a finite-dimensional real vector space `E`,
along a filter `l`, with cutoff currents `Θₖ = i F_{bₖ} + d(χ(|αₖ|²) τₖ)`
(`TauCeti.SeibergWitten.cutoffCurrent`). Suppose that

* the coefficients of the `Θₖ` converge as distributions, and
* every point off a set `Z ⊆ E` has a neighbourhood that eventually lies in the vacuum region
  `{χ(|αₖ|²) = 1}`.

Then the family of framing sections `αₖ` is a zero-charge limit with support `Z`
(`TauCeti.SeibergWitten.isZeroChargeLimit_of_tendsto`, see `TauCeti.IsZeroChargeLimit`). Off `Z`
the sections are eventually nonvanishing on compact sets. The framed charge of a disc `σ` cut off at
radius `ρ < 1` stabilizes whenever the whole preimage `σ⁻¹(Z)` lies in the open disc of some radius
`ρ₀ < ρ`: the zeros then eventually lie inside a circle of radius between `ρ₀` and `ρ`, which avoids
`σ⁻¹(Z)`. The framed charge is the winding number of `αₖ` along that circle
(`TauCeti.SeibergWitten.integral_cutoffCurrent_comp_closedBall_eq_two_pi_mul_degree`),
equivalently the zero charge of the disc (`ContinuousMap.zeroCharge_eq_degree_toBasedLoop`). Its
stabilization is `TauCeti.SeibergWitten.exists_int_eventually_degree_toBasedLoop_eq`.

The limit zero charges `TauCeti.limitZeroCharge l α Z` therefore obey the vacuum, homotopy,
degree and additivity laws of a positive cohomology assignment to `Z`
(`TauCeti.IsZeroChargeLimit.limitZeroCharge_eq_zero`,
`TauCeti.IsZeroChargeLimit.limitZeroCharge_eq_of_homotopy`,
`TauCeti.IsZeroChargeLimit.limitZeroCharge_comp`,
`TauCeti.IsZeroChargeLimit.limitZeroCharge_eq_sum`). Only the vacuum region and the convergence
of the currents enter: positivity of the charges of pseudoholomorphic discs is neither used nor
asserted. For Seiberg–Witten solutions at large parameter it is the separate input that makes the
limit zero charges a positive cohomology assignment
(`TauCeti.PositiveCohomologyAssignment.ofIsZeroChargeLimit`). No density bound on `Z` enters
anywhere.

For large-parameter fields the vacuum hypothesis comes from Taubes's off-zero bound
`w₊ ≤ (C / r) w₊ + C / r + C exp (-c R / h)`, `w₊ = max (1 - |α|²) 0`: when the zero sets of the
`αₖ` converge to `Z` in the sense of Kuratowski (`TauCeti.IsKuratowskiLimit`), every point off `Z`
has a neighbourhood on which eventually `|αₖ|² > σ`, which lies in the vacuum region when `χ = 1`
above `σ`. So the framing sections form a zero-charge limit with support the Kuratowski limit of
their zero sets (`TauCeti.SeibergWitten.isZeroChargeLimit_of_isKuratowskiLimit`). Since `E` has a
countable basis, every sequence of such fields has a subsequence whose zero sets have a Kuratowski
limit, a closed set `Z`, and along which the framing sections form a zero-charge limit with
support `Z` (`TauCeti.SeibergWitten.exists_strictMono_isKuratowskiLimit_and_isZeroChargeLimit`).
No compactness of the domain enters.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Proposition 5.6 and Lemma 6.2.
-/

public section

noncomputable section

open Complex Filter Set MeasureTheory Metric
open scoped Topology Real ContDiff Complex.UnitDisc
open TauCeti.Complex.UnitDisc

namespace TauCeti.SeibergWitten

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {χ : ℝ → ℝ} {l : Filter ι}
  {α : ι → C(E, ℂ)} {Z : Set E}

/-- **The framed charges of a family of abelian Higgs pairs have a limit.** Let `(bₖ, αₖ)` be
abelian Higgs pairs along a filter `l` whose cutoff currents `Θₖ` have coefficients converging as
distributions, and let every point off `Z` have a neighbourhood that eventually lies in the vacuum
region `{χ(|αₖ|²) = 1}`. Then the framing sections `αₖ` form a zero-charge limit with support `Z`:
they are eventually nonvanishing on every compact set missing `Z`, and the zero charges, that is
the framed charges, of every disc `σ` cut off at radius `ρ < 1` are eventually constant, when `σ`
sends no point of norm at least `ρ₀ < ρ` into `Z`. -/
theorem isZeroChargeLimit_of_tendsto [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] [l.NeBot] {b : ι → E → E [⋀^Fin 1]→L[ℝ] ℝ}
    (hα : ∀ k, ContDiff ℝ 2 (α k)) (hb : ∀ k, ContDiff ℝ 1 (b k)) (hχ : ContDiff ℝ 1 χ)
    (hχ₀ : χ =ᶠ[𝓝 0] 0)
    (hvac : ∀ y ∉ Z, ∃ U ∈ 𝓝 y, ∀ᶠ k in l, ∀ x ∈ U, χ (normSq (α k x)) = 1)
    (hlim : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ m : Fin 2 → E,
      ∃ L, Tendsto (fun k ↦ ∫ y, φ y * cutoffCurrent χ (b k) (α k) y m ∂μ) l (𝓝 L)) :
    IsZeroChargeLimit l α Z := by
  have hne : ∀ ⦃K : Set E⦄, IsCompact K → Disjoint K Z → ∀ᶠ k in l, ∀ y ∈ K, α k y ≠ 0 :=
    fun K hK hKZ ↦ by
      obtain ⟨U, -, hKU, hU⟩ :=
        hK.exists_isOpen_eventually_forall fun y hy ↦ hvac y (Set.disjoint_left.1 hKZ hy)
      filter_upwards [hU] with k hk y hy using ne_zero_of_cutoff_eq_one hχ₀ (hk y (hKU hy))
  refine ⟨hne, fun σ ρ₀ ρ hρ hρ₁ hρ₀ hσ ↦ ?_⟩
  -- Eventually the zeros of `αₖ ∘ σ ∘ D_ρ` have norm less than `ρ₀`.
  have hconf := eventually_forall_mem_of_apply_discRetraction_eq_zero hne hρ hρ₁
    (N := {z : 𝔻 | ‖(z : ℂ)‖ < ρ₀}) (Complex.UnitDisc.isOpen_setOf_norm_lt ρ₀)
    (fun z hz ↦ hz.trans hρ₀) hσ
  rcases le_or_gt ρ₀ 0 with hρ₀₀ | hρ₀₀
  · -- If `ρ₀ ≤ 0` there are eventually no zeros at all.
    refine ⟨0, ?_⟩
    filter_upwards [hconf] with k hk
    exact ContinuousMap.zeroCharge_eq_zero_of_forall_ne_zero fun z hz ↦
      (norm_nonneg _).not_gt ((hk z hz).trans_le hρ₀₀)
  -- The circle of radius `r` between `ρ₀` and `ρ`, and the disc `σ ∘ D_ρ` read on the plane.
  obtain ⟨r, hρ₀r, hrρ⟩ := exists_between hρ₀
  have hr : 0 < r := hρ₀₀.trans hρ₀r
  set σ' : C(ℂ, E) := σ.comp (radialRetractionToUnitDisc ρ hρ hρ₁)
  have hsph (ζ : Circle) : (0 : ℂ) + r * ζ ∈ sphere (0 : ℂ) r := by simp [abs_of_pos hr]
  -- The image of the circle misses `Z`, so it has an open neighbourhood eventually in the vacuum.
  have hKZ : Disjoint (σ' '' sphere 0 r) Z := by
    rw [Set.disjoint_left]
    rintro _ ⟨w, hw, rfl⟩ hwZ
    have h' := hσ _ hwZ
    rw [norm_coe_radialRetractionToUnitDisc_apply, mem_sphere_zero_iff_norm.1 hw,
      min_eq_left hrρ.le] at h'
    exact hρ₀r.not_gt h'
  obtain ⟨U, hUo, hKU, hU⟩ :=
    ((isCompact_sphere 0 r).image σ'.continuous).exists_isOpen_eventually_forall fun y hy ↦
      hvac y (Set.disjoint_left.1 hKZ hy)
  obtain ⟨n, hn⟩ := exists_int_eventually_degree_toBasedLoop_eq (μ := μ) (α := fun k ↦ α k)
    (σ := σ') (z₀ := 0) hr.le hα hb hχ hχ₀ σ'.continuous.continuousOn hUo
    (fun w hw ↦ hKU ⟨w, hw, rfl⟩) hU hlim
  refine ⟨n, ?_⟩
  filter_upwards [hn, hconf, hU] with k hk hkc hkU
  -- The boundary direction map of `αₖ ∘ σ'` along the circle of radius `r`.
  have hne' (ζ : Circle) : α k (σ' (0 + r * ζ)) ≠ 0 :=
    ne_zero_of_cutoff_eq_one hχ₀ (hkU _ (hKU ⟨_, hsph ζ, rfl⟩))
  let f' : C(Circle, ℂ) := ⟨fun ζ ↦ α k (σ' (0 + r * ζ)), by fun_prop⟩
  have hu (ζ : Circle) : (f'.normalizeToCircle hne' ζ : ℂ) =
      α k (σ' (0 + r * ζ)) / ‖α k (σ' (0 + r * ζ))‖ :=
    f'.coe_normalizeToCircle_apply _ ζ
  rw [ContinuousMap.zeroCharge_eq_degree_toBasedLoop (u := f'.normalizeToCircle hne') hr
    (closedBall_subset_ball (by linarith))
    (fun z hz ↦ mem_ball_zero_iff.2 ((hkc z hz).trans hρ₀r)) fun ζ hζ ↦ by
      rw [ContinuousMap.comp_apply, discRetraction_apply, Complex.UnitDisc.coe_mk]
      exact hu ζ]
  exact hk _ hu

/-- **The framed charges of large-parameter fields have a limit supported on the limit of the zero
sets.** Let `(bₖ, αₖ)` be abelian Higgs pairs along a nontrivial filter `l` whose cutoff currents
`Θₖ` have coefficients converging as distributions, built with a cutoff `χ` equal to one above
`σ < 1`. Let the sets `Zₖ` converge in the sense of Kuratowski to `Z`, while `rₖ → ∞` and
`hₖ → 0⁺`, and suppose that eventually Taubes's off-zero bound
`max (1 - |αₖ|²) 0 ≤ (C / rₖ) max (1 - |αₖ|²) 0 + C / rₖ + C exp (-c R / hₖ)` holds at every point
where `|αₖ|² ≤ σ`, for every radius `R ≥ c₀ hₖ` of an open ball about that point missing `Zₖ`.
Then the framing sections `αₖ` form a zero-charge limit with support `Z`. -/
theorem isZeroChargeLimit_of_isKuratowskiLimit [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] [l.NeBot]
    {b : ι → E → E [⋀^Fin 1]→L[ℝ] ℝ} (hα : ∀ k, ContDiff ℝ 2 (α k)) (hb : ∀ k, ContDiff ℝ 1 (b k))
    (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0) {σ : ℝ} (hσ : σ < 1) (hχσ : EqOn χ 1 (Ioi σ))
    {Zs : ι → Set E} {r h : ι → ℝ} (C c c₀ : ℝ) (hc : 0 < c) (hr : Tendsto r l atTop)
    (hh : Tendsto h l (𝓝 0)) (hh₀ : ∀ᶠ k in l, 0 < h k) (hZ : IsKuratowskiLimit l Zs Z)
    (hbound : ∀ᶠ k in l, ∀ x, normSq (α k x) ≤ σ → ∀ R, c₀ * h k ≤ R →
      (∀ z ∈ Zs k, R ≤ dist x z) → max (1 - normSq (α k x)) 0 ≤
        C / r k * max (1 - normSq (α k x)) 0 + C / r k + C * Real.exp (-(c * R / h k)))
    (hlim : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ m : Fin 2 → E,
      ∃ L, Tendsto (fun k ↦ ∫ y, φ y * cutoffCurrent χ (b k) (α k) y m ∂μ) l (𝓝 L)) :
    IsZeroChargeLimit l α Z := by
  refine isZeroChargeLimit_of_tendsto hα hb hχ hχ₀ (fun y hy ↦ ?_) hlim
  obtain ⟨U, hU, hUσ⟩ := exists_mem_nhds_eventually_forall_lt_of_isKuratowskiLimit
    (s := fun k x ↦ normSq (α k x)) C c c₀ hc hσ hr hh hZ hh₀ hbound hy
  exact ⟨U, hU, hUσ.mono fun k hk x hx ↦ hχσ (hk x hx)⟩

/-- **Extraction of a limit of the zero sets and of the framed charges.** Let `(bₖ, αₖ)` be a
sequence of abelian Higgs pairs whose cutoff currents `Θₖ` have coefficients converging as
distributions, built with a cutoff `χ` equal to one above `σ < 1`, while `rₖ → ∞` and `hₖ → 0⁺`.
Suppose that eventually Taubes's off-zero bound holds at every point where `|αₖ|² ≤ σ`, relative to
the zero set of `αₖ`. Then there are a subsequence `φ` and a set `Z`, closed by
`TauCeti.IsKuratowskiLimit.isClosed`, such that the zero sets of the `α (φ k)` converge to `Z` in
the sense of Kuratowski and the framing sections `α (φ k)` form a zero-charge limit with
support `Z`. -/
theorem exists_strictMono_isKuratowskiLimit_and_isZeroChargeLimit [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {α : ℕ → C(E, ℂ)}
    {b : ℕ → E → E [⋀^Fin 1]→L[ℝ] ℝ} (hα : ∀ k, ContDiff ℝ 2 (α k))
    (hb : ∀ k, ContDiff ℝ 1 (b k)) (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0) {σ : ℝ}
    (hσ : σ < 1) (hχσ : EqOn χ 1 (Ioi σ)) {r h : ℕ → ℝ} (C c c₀ : ℝ) (hc : 0 < c)
    (hr : Tendsto r atTop atTop) (hh : Tendsto h atTop (𝓝 0)) (hh₀ : ∀ᶠ k in atTop, 0 < h k)
    (hbound : ∀ᶠ k in atTop, ∀ x, normSq (α k x) ≤ σ → ∀ R, c₀ * h k ≤ R →
      (∀ z ∈ α k ⁻¹' {0}, R ≤ dist x z) → max (1 - normSq (α k x)) 0 ≤
        C / r k * max (1 - normSq (α k x)) 0 + C / r k + C * Real.exp (-(c * R / h k)))
    (hlim : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ m : Fin 2 → E,
      ∃ L, Tendsto (fun k ↦ ∫ y, φ y * cutoffCurrent χ (b k) (α k) y m ∂μ) atTop (𝓝 L)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Z : Set E,
      IsKuratowskiLimit atTop (fun k ↦ α (φ k) ⁻¹' {0}) Z ∧ IsZeroChargeLimit atTop (α ∘ φ) Z := by
  obtain ⟨φ, hφ, Z, hZ⟩ := exists_strictMono_isKuratowskiLimit fun k ↦ α k ⁻¹' {0}
  have hφt := hφ.tendsto_atTop
  refine ⟨φ, hφ, Z, hZ, isZeroChargeLimit_of_isKuratowskiLimit (μ := μ) (b := b ∘ φ)
    (fun k ↦ hα (φ k)) (fun k ↦ hb (φ k)) hχ hχ₀ hσ hχσ C c c₀ hc (hr.comp hφt) (hh.comp hφt)
    (hφt.eventually hh₀) hZ (hφt.eventually hbound) fun ψ hψ hψc m ↦ ?_⟩
  obtain ⟨L, hL⟩ := hlim ψ hψ hψc m
  exact ⟨L, hL.comp hφt⟩

end TauCeti.SeibergWitten
