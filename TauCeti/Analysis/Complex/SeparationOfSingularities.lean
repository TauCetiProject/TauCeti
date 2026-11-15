/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Cycle.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
import TauCeti.Analysis.Contour.Cycle.Grid
import TauCeti.Analysis.Contour.Cycle.HomologyCauchy
import TauCeti.Analysis.Contour.Cycle.Residue
import Mathlib.Analysis.Complex.Liouville

/-!
# Separation of singularities along a compact set

Let `K` be a compact subset of an open set `V ⊆ ℂ` and let `f` be holomorphic on `V ∖ K`. Then
`f` splits as `f = g + h` on `V ∖ K`, where `g` is holomorphic on all of `V` and `h` is holomorphic
on `ℂ ∖ K` and tends to `0` at infinity, and the two parts are unique: `g` on `V` and `h` on
`ℂ ∖ K`. Thus the quotient `O(V ∖ K) / O(V)` is identified with the space of holomorphic functions
on `ℂ ∖ K` vanishing at infinity, independently of `V`. This is the form in which a holomorphic
function near a compact set `K` determines its singular part along `K`, as the classical Laurent
decomposition does on an annulus around a point.

Both parts are Cauchy integrals. Choose a cycle `Γ` in `V ∖ K`, null-homologous in `V`, winding
once around every point of `K`. Then

* `g(w) = (2πi)⁻¹ ∮_Γ f(z)/(z - w) dz` when `Γ` winds once around `w`, and
* `h(w) = -(2πi)⁻¹ ∮_Γ f(z)/(z - w) dz` when `Γ` winds zero times around `w`.

In the language of analytic functionals, the second formula says that `h(w)` is the pairing of the
class of `f` in `O(V ∖ K) / O(V)` with the germ along `K` of the Cauchy kernel `z ↦ (w - z)⁻¹`.

## Main results

* `IsCompact.exists_eqOn_add_tendsto_cocompact`: existence of the decomposition `f = g + h`.
* `IsCompact.eqOn_zero_of_eqOn_of_tendsto_cocompact`: uniqueness. If `g` is holomorphic on `V`,
  `h` is holomorphic on `ℂ ∖ K` and tends to `0` at infinity, and `g = h` on `V ∖ K`, then `g = 0`
  on `V` and `h = 0` on `ℂ ∖ K`.
* `IsCompact.integral_div_sub_eq_of_windingNumber_eq_one` and
  `IsCompact.integral_div_sub_eq_of_windingNumber_eq_zero`: the Cauchy integral formulas for the
  two parts of every such decomposition.

## Implementation notes

The cycles are those of `IsCompact.exists_cycle_windingNumber_eq_one`. The Cauchy integral over
such a cycle depends only on the winding number of the cycle about the point `w`, by the homology
form of Cauchy's theorem applied off `K ∪ {w}`; it is holomorphic in `w` off the trace and vanishes
at infinity (`TauCeti.Contour.Cycle.differentiableOn_integral_div_sub`,
`TauCeti.Contour.Cycle.tendsto_integral_div_sub_cocompact`). Near a point of `V`, a single cycle
winding once around a closed disc about the point computes `g`; near a point off `K`, a single
cycle avoiding a closed disc about the point computes `h`. Uniqueness is Liouville's theorem for
the entire function equal to `g` on `V` and to `h` off `K`.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, third edition,
  Theorem 1.2.2 and its proof (the decomposition along a compact set by Cauchy integrals).
* H. Komatsu, *An introduction to the theory of hyperfunctions*, in *Hyperfunctions and
  pseudo-differential equations*, Lecture Notes in Mathematics 287 (1973), 3–40, §1 (the
  identification of `O(V ∖ K) / O(V)` with holomorphic functions on `ℂ ∖ K` vanishing at
  infinity).
-/

public section

noncomputable section

open Complex Filter Set TauCeti.Contour

open scoped Real Topology

namespace TauCeti

variable {K V : Set ℂ} {f : ℂ → ℂ}

/-- Over two cycles in `V ∖ K`, null-homologous in `V` and winding once around every point of
`K`, the Cauchy integral of `f` at a point `w` off both traces agrees when both cycles have the
same winding number about `w`: Cauchy's theorem applies off the closed set `K ∪ {w}`. -/
private theorem integral_div_sub_eq_of_windingNumber_eq (hV : IsOpen V) (hK : IsClosed K)
    (hf : DifferentiableOn ℂ f (V \ K)) {Γ Γ' : Cycle} (hΓ : Γ.IsIn (V \ K))
    (hΓ' : Γ'.IsIn (V \ K)) (hΓV : Γ.IsNullHomologous V) (hΓ'V : Γ'.IsNullHomologous V)
    (hΓK : ∀ z ∈ K, Cycle.windingNumber z Γ = 1) (hΓ'K : ∀ z ∈ K, Cycle.windingNumber z Γ' = 1)
    {w : ℂ} (hw : w ∉ Cycle.trace Γ) (hw' : w ∉ Cycle.trace Γ')
    (hww : Cycle.windingNumber w Γ = Cycle.windingNumber w Γ') :
    Cycle.integral (fun z ↦ f z / (z - w)) Γ = Cycle.integral (fun z ↦ f z / (z - w)) Γ' := by
  have hin : ∀ {C : Cycle}, C.IsIn (V \ K) → w ∉ Cycle.trace C → C.IsIn (V \ (K ∪ {w})) :=
    fun hC hwC ↦ Cycle.isIn_iff.mpr fun z hz ↦
      ⟨(Cycle.isIn_iff.mp hC hz).1, by
        rintro (hzK | rfl)
        exacts [(Cycle.isIn_iff.mp hC hz).2 hzK, hwC hz]⟩
  refine Cycle.integral_eq_of_windingNumber_eq hV (hK.union isClosed_singleton)
    (fun z hz ↦ ?_) (hin hΓ hw) (hin hΓ' hw') hΓV hΓ'V ?_
  · have hzw : z - w ≠ 0 := sub_ne_zero.mpr fun h ↦ hz.2 (Or.inr h)
    exact ((hf z ⟨hz.1, fun h ↦ hz.2 (Or.inl h)⟩).mono
      (sdiff_subset_sdiff_right subset_union_left)).div
        (differentiableWithinAt_id.sub_const w) hzw
  · rintro z (hz | rfl)
    exacts [(hΓK z hz).trans (hΓ'K z hz).symm, hww]

open Classical in
/-- The Cauchy integral `(2πi)⁻¹ ∮_Γ f(z)/(z - w) dz` over a cycle `Γ` in `V ∖ K`, null-homologous
in `V`, winding once around every point of `K` and `n` times around `w`, or `0` when there is no
such cycle. It does not depend on the choice of `Γ` (`cauchyPart_eq`). -/
private def cauchyPart (V K : Set ℂ) (f : ℂ → ℂ) (n : ℂ) (w : ℂ) : ℂ :=
  if h : ∃ Γ : Cycle, Γ.IsIn (V \ K) ∧ Γ.IsNullHomologous V ∧
      (∀ z ∈ K, Cycle.windingNumber z Γ = 1) ∧ w ∉ Cycle.trace Γ ∧ Cycle.windingNumber w Γ = n
  then (2 * π * I)⁻¹ * Cycle.integral (fun z ↦ f z / (z - w)) h.choose
  else 0

/-- `cauchyPart` is computed by every admissible cycle. -/
private theorem cauchyPart_eq (hV : IsOpen V) (hK : IsClosed K)
    (hf : DifferentiableOn ℂ f (V \ K)) {Γ : Cycle} (hΓ : Γ.IsIn (V \ K))
    (hΓV : Γ.IsNullHomologous V) (hΓK : ∀ z ∈ K, Cycle.windingNumber z Γ = 1) {w : ℂ}
    (hw : w ∉ Cycle.trace Γ) :
    cauchyPart V K f (Cycle.windingNumber w Γ) w =
      (2 * π * I)⁻¹ * Cycle.integral (fun z ↦ f z / (z - w)) Γ := by
  have h : ∃ Γ' : Cycle, Γ'.IsIn (V \ K) ∧ Γ'.IsNullHomologous V ∧
      (∀ z ∈ K, Cycle.windingNumber z Γ' = 1) ∧ w ∉ Cycle.trace Γ' ∧
        Cycle.windingNumber w Γ' = Cycle.windingNumber w Γ := ⟨Γ, hΓ, hΓV, hΓK, hw, rfl⟩
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h.choose_spec
  rw [cauchyPart, dite_eq_left h,
    integral_div_sub_eq_of_windingNumber_eq hV hK hf h₁ hΓ h₂ hΓV h₃ hΓK h₄ hw h₅]

/-- A cycle in `V ∖ L`, null-homologous in `V`, winding once around the compact set `L ⊆ V`. When
`K ⊆ L`, it computes `cauchyPart V K f 1` at every point of `L`. -/
private theorem cauchyPart_one_eq (hV : IsOpen V) (hK : IsClosed K)
    (hf : DifferentiableOn ℂ f (V \ K)) {L : Set ℂ} (hKL : K ⊆ L) {Γ : Cycle}
    (hΓ : Γ.IsIn (V \ L)) (hΓV : Γ.IsNullHomologous V)
    (hΓL : ∀ z ∈ L, Cycle.windingNumber z Γ = 1) {w : ℂ} (hw : w ∈ L) :
    cauchyPart V K f 1 w = (2 * π * I)⁻¹ * Cycle.integral (fun z ↦ f z / (z - w)) Γ := by
  have hwΓ : w ∉ Cycle.trace Γ := fun h ↦ (Cycle.isIn_iff.mp hΓ h).2 hw
  rw [← hΓL w hw, cauchyPart_eq hV hK hf
    (Cycle.isIn_iff.mpr fun z hz ↦ sdiff_subset_sdiff_right hKL (Cycle.isIn_iff.mp hΓ hz)) hΓV
    (fun z hz ↦ hΓL z (hKL hz)) hwΓ]

/-- A cycle in `V' ∖ K`, null-homologous in an open `V' ⊆ V`, winding once around `K`. It computes
`cauchyPart V K f 0` at every point outside `V'`. -/
private theorem cauchyPart_zero_eq (hV : IsOpen V) (hK : IsClosed K)
    (hf : DifferentiableOn ℂ f (V \ K)) {V' : Set ℂ} (hV'V : V' ⊆ V) {Γ : Cycle}
    (hΓ : Γ.IsIn (V' \ K)) (hΓV' : Γ.IsNullHomologous V')
    (hΓK : ∀ z ∈ K, Cycle.windingNumber z Γ = 1) {w : ℂ} (hw : w ∉ V') :
    cauchyPart V K f 0 w = (2 * π * I)⁻¹ * Cycle.integral (fun z ↦ f z / (z - w)) Γ := by
  have hwΓ : w ∉ Cycle.trace Γ := fun h ↦ hw (Cycle.isIn_iff.mp hΓ h).1
  rw [← Cycle.isNullHomologous_iff.mp hΓV' w hw, cauchyPart_eq hV hK hf
    (Cycle.isIn_iff.mpr fun z hz ↦ sdiff_subset_sdiff_left hV'V (Cycle.isIn_iff.mp hΓ hz))
    (hΓV'.mono hV'V) hΓK hwΓ]

/-- A point of an open set has a closed disc of positive radius inside it. -/
private theorem exists_closedBall_subset {U : Set ℂ} (hU : IsOpen U) {w : ℂ} (hw : w ∈ U) :
    ∃ r > 0, Metric.closedBall w r ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU w hw
  exact ⟨ε / 2, half_pos hε, (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball⟩

/-- The part of `f` holomorphic on `V` is holomorphic there. -/
private theorem differentiableOn_cauchyPart_one (hK : IsCompact K) (hV : IsOpen V)
    (hKV : K ⊆ V) (hf : DifferentiableOn ℂ f (V \ K)) :
    DifferentiableOn ℂ (cauchyPart V K f 1) V := by
  intro w₀ hw₀
  obtain ⟨r, hr, hrV⟩ := exists_closedBall_subset hV hw₀
  -- One cycle winding once around `K ∪ closedBall w₀ r` computes the part near `w₀`.
  obtain ⟨Γ, hΓ, hΓV, hΓL⟩ :=
    (hK.union (isCompact_closedBall w₀ r)).exists_cycle_windingNumber_eq_one hV
      (union_subset hKV hrV)
  have hw₀Γ : w₀ ∉ Cycle.trace Γ := fun h ↦
    (Cycle.isIn_iff.mp hΓ h).2 (Or.inr (Metric.mem_closedBall_self hr.le))
  refine (((Cycle.differentiableOn_integral_div_sub f Γ).differentiableAt
    ((Cycle.isCompact_trace Γ).isClosed.isOpen_compl.mem_nhds hw₀Γ)).const_mul
      (2 * π * I)⁻¹).congr_of_eventuallyEq ?_ |>.differentiableWithinAt
  filter_upwards [Metric.ball_mem_nhds w₀ hr] with w hw
  exact cauchyPart_one_eq hV hK.isClosed hf subset_union_left hΓ hΓV hΓL
    (Or.inr (Metric.ball_subset_closedBall hw))

/-- The part of `f` holomorphic off `K` is holomorphic there. -/
private theorem differentiableOn_cauchyPart_zero (hK : IsCompact K) (hV : IsOpen V)
    (hKV : K ⊆ V) (hf : DifferentiableOn ℂ f (V \ K)) :
    DifferentiableOn ℂ (cauchyPart V K f 0) Kᶜ := by
  intro w₀ hw₀
  obtain ⟨r, hr, hrK⟩ := exists_closedBall_subset hK.isClosed.isOpen_compl hw₀
  -- One cycle around `K` avoiding `closedBall w₀ r` computes the part near `w₀`.
  have hV' : IsOpen (V \ Metric.closedBall w₀ r) := hV.sdiff Metric.isClosed_closedBall
  have hKV' : K ⊆ V \ Metric.closedBall w₀ r := fun z hz ↦ ⟨hKV hz, fun h ↦ hrK h hz⟩
  obtain ⟨Γ, hΓ, hΓV, hΓK⟩ := hK.exists_cycle_windingNumber_eq_one hV' hKV'
  have hw₀Γ : w₀ ∉ Cycle.trace Γ := fun h ↦
    (Cycle.isIn_iff.mp hΓ h).1.2 (Metric.mem_closedBall_self hr.le)
  refine (((Cycle.differentiableOn_integral_div_sub f Γ).differentiableAt
    ((Cycle.isCompact_trace Γ).isClosed.isOpen_compl.mem_nhds hw₀Γ)).const_mul
      (2 * π * I)⁻¹).congr_of_eventuallyEq ?_ |>.differentiableWithinAt
  filter_upwards [Metric.ball_mem_nhds w₀ hr] with w hw
  exact cauchyPart_zero_eq hV hK.isClosed hf sdiff_subset hΓ hΓV hΓK
    fun h ↦ h.2 (Metric.ball_subset_closedBall hw)

/-- The part of `f` holomorphic off `K` tends to `0` at infinity. -/
private theorem tendsto_cauchyPart_zero (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    (hf : DifferentiableOn ℂ f (V \ K)) :
    Tendsto (cauchyPart V K f 0) (cocompact ℂ) (𝓝 0) := by
  obtain ⟨Γ, hΓ, hΓV, hΓK⟩ := hK.exists_cycle_windingNumber_eq_one hV hKV
  have hlim := (Cycle.tendsto_integral_div_sub_cocompact f Γ).const_mul (2 * π * I)⁻¹
  rw [mul_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [Cycle.windingNumber_eventually_zero_cocompact Γ] with w hw
  rw [← hw.2, cauchyPart_eq hV hK.isClosed hf hΓ hΓV hΓK hw.1]

/-- On `V ∖ K`, the function `f` is the sum of its two Cauchy parts. -/
private theorem eqOn_cauchyPart_one_sub_cauchyPart_zero (hK : IsCompact K) (hV : IsOpen V)
    (hKV : K ⊆ V) (hf : DifferentiableOn ℂ f (V \ K)) :
    EqOn f (fun w ↦ cauchyPart V K f 1 w - cauchyPart V K f 0 w) (V \ K) := by
  intro w hw
  dsimp only
  -- A cycle winding once around `w` and one winding zero times around `w`.
  obtain ⟨Γ₁, hΓ₁, hΓ₁V, hΓ₁L⟩ :=
    (hK.union isCompact_singleton).exists_cycle_windingNumber_eq_one hV
      (union_subset hKV (singleton_subset_iff.mpr hw.1))
  have hKV' : K ⊆ V \ {w} := fun z hz ↦ ⟨hKV hz, fun h ↦ hw.2 (h ▸ hz)⟩
  obtain ⟨Γ₀, hΓ₀, hΓ₀V, hΓ₀K⟩ :=
    hK.exists_cycle_windingNumber_eq_one (hV.sdiff isClosed_singleton) hKV'
  have hw₁ : w ∉ Cycle.trace Γ₁ := fun h ↦ (Cycle.isIn_iff.mp hΓ₁ h).2 (Or.inr rfl)
  have hw₀ : w ∉ Cycle.trace Γ₀ := fun h ↦ (Cycle.isIn_iff.mp hΓ₀ h).1.2 rfl
  have hn₁ : Cycle.windingNumber w Γ₁ = 1 := hΓ₁L w (Or.inr rfl)
  have hn₀ : Cycle.windingNumber w Γ₀ = 0 :=
    Cycle.isNullHomologous_iff.mp hΓ₀V w fun h ↦ h.2 rfl
  rw [cauchyPart_one_eq hV hK.isClosed hf subset_union_left hΓ₁ hΓ₁V hΓ₁L (Or.inr rfl),
    cauchyPart_zero_eq hV hK.isClosed hf sdiff_subset hΓ₀ hΓ₀V hΓ₀K fun h ↦ h.2 rfl,
    ← mul_sub, ← map_sub]
  -- The difference `Γ₁ - Γ₀` is null-homologous in `V ∖ K` and winds once around `w`.
  have hin : (Γ₁ - Γ₀).IsIn (V \ K) := by
    rw [sub_eq_add_neg]
    exact (Cycle.isIn_iff.mpr fun z hz ↦ sdiff_subset_sdiff_right subset_union_left
      (Cycle.isIn_iff.mp hΓ₁ hz)).add (Cycle.isIn_neg_iff.mpr (Cycle.isIn_iff.mpr fun z hz ↦
        sdiff_subset_sdiff_left sdiff_subset (Cycle.isIn_iff.mp hΓ₀ hz)))
  have hnull : (Γ₁ - Γ₀).IsNullHomologous (V \ K) := by
    refine Cycle.isNullHomologous_iff.mpr fun z hz ↦ ?_
    rw [map_sub, sub_eq_zero]
    by_cases hzV : z ∈ V
    · have hzK : z ∈ K := not_not.mp fun h ↦ hz ⟨hzV, h⟩
      rw [hΓ₁L z (Or.inl hzK), hΓ₀K z hzK]
    · rw [Cycle.isNullHomologous_iff.mp hΓ₁V z hzV,
        Cycle.isNullHomologous_iff.mp hΓ₀V z fun h ↦ hzV h.1]
  have hwtr : w ∉ Cycle.trace (Γ₁ - Γ₀) := by
    rw [sub_eq_add_neg]
    intro h
    rcases Cycle.trace_add_subset _ _ h with h | h
    exacts [hw₁ h, hw₀ (Cycle.trace_neg Γ₀ ▸ h)]
  rw [Cycle.cauchyIntegralFormula_nullHomologous (hV.sdiff hK.isClosed) hf hin hnull hwtr,
    map_sub, hn₁, hn₀]
  field_simp [Real.pi_ne_zero, I_ne_zero]
  ring

/-- **Uniqueness of the separation of singularities.** Let `K` be a compact subset of an open set
`V ⊆ ℂ`. If `g` is holomorphic on `V`, `h` is holomorphic on `ℂ ∖ K` and tends to `0` at
infinity, and `g = h` on `V ∖ K`, then `g = 0` on `V` and `h = 0` on `ℂ ∖ K`. -/
theorem _root_.IsCompact.eqOn_zero_of_eqOn_of_tendsto_cocompact (hK : IsCompact K) (hV : IsOpen V)
    (hKV : K ⊆ V) {g h : ℂ → ℂ} (hg : DifferentiableOn ℂ g V) (hh : DifferentiableOn ℂ h Kᶜ)
    (hlim : Tendsto h (cocompact ℂ) (𝓝 0)) (hgh : EqOn g h (V \ K)) :
    EqOn g 0 V ∧ EqOn h 0 Kᶜ := by
  classical
  -- The function equal to `g` on `V` and to `h` off `K` is entire and vanishes at infinity.
  set F := V.piecewise g h
  have hFg : EqOn F g V := fun z hz ↦ piecewise_eq_of_mem _ _ _ hz
  have hFh : EqOn F h Kᶜ := fun z hz ↦ by
    by_cases hzV : z ∈ V
    · rw [hFg hzV, hgh ⟨hzV, hz⟩]
    · exact piecewise_eq_of_notMem _ _ _ hzV
  have hF : Differentiable ℂ F := fun z ↦ by
    by_cases hzV : z ∈ V
    · exact (hg.differentiableAt (hV.mem_nhds hzV)).congr_of_eventuallyEq
        (eventuallyEq_of_mem (hV.mem_nhds hzV) hFg)
    · have hzK : z ∈ Kᶜ := fun h ↦ hzV (hKV h)
      have hnhds := hK.isClosed.isOpen_compl.mem_nhds hzK
      exact (hh.differentiableAt hnhds).congr_of_eventuallyEq (eventuallyEq_of_mem hnhds hFh)
  have hF0 : ∀ z, F z = 0 := fun z ↦ hF.apply_eq_of_tendsto_cocompact z
    (hlim.congr' (eventuallyEq_of_mem hK.compl_mem_cocompact hFh).symm)
  exact ⟨fun z hz ↦ (hFg hz).symm.trans (hF0 z), fun z hz ↦ (hFh hz).symm.trans (hF0 z)⟩

/-- **Separation of singularities along a compact set.** Let `K` be a compact subset of an open
set `V ⊆ ℂ` and let `f` be holomorphic on `V ∖ K`. Then `f = g + h` on `V ∖ K` for a function `g`
holomorphic on `V` and a function `h` holomorphic on `ℂ ∖ K` that tends to `0` at infinity. The
two parts are unique by `IsCompact.eqOn_zero_of_eqOn_of_tendsto_cocompact`, and are given by
Cauchy integrals (`IsCompact.integral_div_sub_eq_of_windingNumber_eq_one`,
`IsCompact.integral_div_sub_eq_of_windingNumber_eq_zero`). -/
theorem _root_.IsCompact.exists_eqOn_add_tendsto_cocompact (hK : IsCompact K) (hV : IsOpen V)
    (hKV : K ⊆ V) (hf : DifferentiableOn ℂ f (V \ K)) :
    ∃ g h : ℂ → ℂ, DifferentiableOn ℂ g V ∧ DifferentiableOn ℂ h Kᶜ ∧
      Tendsto h (cocompact ℂ) (𝓝 0) ∧ EqOn f (g + h) (V \ K) :=
  ⟨cauchyPart V K f 1, fun w ↦ -cauchyPart V K f 0 w,
    differentiableOn_cauchyPart_one hK hV hKV hf,
    (differentiableOn_cauchyPart_zero hK hV hKV hf).neg,
    by simpa using (tendsto_cauchyPart_zero hK hV hKV hf).neg,
    fun w hw ↦ by
      simpa [sub_eq_add_neg] using eqOn_cauchyPart_one_sub_cauchyPart_zero hK hV hKV hf hw⟩

/-- A function that is the sum on `V ∖ K` of a function holomorphic on `V` and a function
holomorphic off `K` is holomorphic on `V ∖ K`. -/
private theorem differentiableOn_of_eqOn_add {g h : ℂ → ℂ} (hg : DifferentiableOn ℂ g V)
    (hh : DifferentiableOn ℂ h Kᶜ) (hfgh : EqOn f (g + h) (V \ K)) :
    DifferentiableOn ℂ f (V \ K) :=
  ((hg.mono sdiff_subset).add (hh.mono fun _ hz ↦ hz.2)).congr hfgh

/-- In a decomposition `f = g + h` of a function holomorphic on `V ∖ K` as in
`IsCompact.exists_eqOn_add_tendsto_cocompact`, the parts agree with the Cauchy parts. -/
private theorem eqOn_cauchyPart (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    {g h : ℂ → ℂ} (hg : DifferentiableOn ℂ g V) (hh : DifferentiableOn ℂ h Kᶜ)
    (hlim : Tendsto h (cocompact ℂ) (𝓝 0)) (hfgh : EqOn f (g + h) (V \ K)) :
    EqOn g (cauchyPart V K f 1) V ∧ EqOn h (fun w ↦ -cauchyPart V K f 0 w) Kᶜ := by
  have hf := differentiableOn_of_eqOn_add hg hh hfgh
  have key := hK.eqOn_zero_of_eqOn_of_tendsto_cocompact hV hKV
    (g := fun w ↦ g w - cauchyPart V K f 1 w) (h := fun w ↦ -cauchyPart V K f 0 w - h w)
    (hg.sub (differentiableOn_cauchyPart_one hK hV hKV hf))
    ((differentiableOn_cauchyPart_zero hK hV hKV hf).neg.sub hh)
    (by simpa using (tendsto_cauchyPart_zero hK hV hKV hf).neg.sub hlim) fun w hw ↦ by
      have h₁ := hfgh hw
      have h₂ := eqOn_cauchyPart_one_sub_cauchyPart_zero hK hV hKV hf hw
      simp only [Pi.add_apply] at h₁ h₂ ⊢
      linear_combination h₂ - h₁
  exact ⟨fun w hw ↦ sub_eq_zero.mp (key.1 hw), fun w hw ↦ (sub_eq_zero.mp (key.2 hw)).symm⟩

/-- **The Cauchy integral formula for the regular part.** Let `f = g + h` on `V ∖ K` be the
separation of singularities of `f` along the compact set `K ⊆ V`, with `g` holomorphic on `V` and
`h` holomorphic on `ℂ ∖ K` and vanishing at infinity. For a cycle `Γ` in `V ∖ K`, null-homologous
in `V` and winding once around every point of `K`, and a point `w` off `Γ` around which `Γ` winds
once, `∮_Γ f(z)/(z - w) dz = 2πi g(w)`. -/
theorem _root_.IsCompact.integral_div_sub_eq_of_windingNumber_eq_one (hK : IsCompact K)
    (hV : IsOpen V) (hKV : K ⊆ V) {g h : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g V) (hh : DifferentiableOn ℂ h Kᶜ)
    (hlim : Tendsto h (cocompact ℂ) (𝓝 0)) (hfgh : EqOn f (g + h) (V \ K)) {Γ : Cycle}
    (hΓ : Γ.IsIn (V \ K)) (hΓV : Γ.IsNullHomologous V)
    (hΓK : ∀ z ∈ K, Cycle.windingNumber z Γ = 1) {w : ℂ} (hw : w ∉ Cycle.trace Γ)
    (hw₁ : Cycle.windingNumber w Γ = 1) :
    Cycle.integral (fun z ↦ f z / (z - w)) Γ = 2 * π * I * g w := by
  have hf := differentiableOn_of_eqOn_add hg hh hfgh
  have hwV : w ∈ V := not_not.mp fun h ↦ by
    simp [Cycle.isNullHomologous_iff.mp hΓV w h] at hw₁
  have := cauchyPart_eq hV hK.isClosed hf hΓ hΓV hΓK hw
  rw [hw₁, ← (eqOn_cauchyPart hK hV hKV hg hh hlim hfgh).1 hwV] at this
  rw [this]
  field_simp [Real.pi_ne_zero, I_ne_zero]

/-- **The Cauchy integral formula for the singular part.** Let `f = g + h` on `V ∖ K` be the
separation of singularities of `f` along the compact set `K ⊆ V`, with `g` holomorphic on `V` and
`h` holomorphic on `ℂ ∖ K` and vanishing at infinity. For a cycle `Γ` in `V ∖ K`, null-homologous
in `V` and winding once around every point of `K`, and a point `w` off `Γ` around which `Γ` winds
zero times, `∮_Γ f(z)/(z - w) dz = -2πi h(w)`. -/
theorem _root_.IsCompact.integral_div_sub_eq_of_windingNumber_eq_zero (hK : IsCompact K)
    (hV : IsOpen V) (hKV : K ⊆ V) {g h : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g V) (hh : DifferentiableOn ℂ h Kᶜ)
    (hlim : Tendsto h (cocompact ℂ) (𝓝 0)) (hfgh : EqOn f (g + h) (V \ K)) {Γ : Cycle}
    (hΓ : Γ.IsIn (V \ K)) (hΓV : Γ.IsNullHomologous V)
    (hΓK : ∀ z ∈ K, Cycle.windingNumber z Γ = 1) {w : ℂ} (hw : w ∉ Cycle.trace Γ)
    (hw₀ : Cycle.windingNumber w Γ = 0) :
    Cycle.integral (fun z ↦ f z / (z - w)) Γ = -(2 * π * I * h w) := by
  have hf := differentiableOn_of_eqOn_add hg hh hfgh
  have hwK : w ∉ K := fun h ↦ by simp [hΓK w h] at hw₀
  have := cauchyPart_eq hV hK.isClosed hf hΓ hΓV hΓK hw
  rw [hw₀, show cauchyPart V K f 0 w = -h w from
    neg_eq_iff_eq_neg.mp ((eqOn_cauchyPart hK hV hKV hg hh hlim hfgh).2 hwK).symm] at this
  rw [← neg_eq_iff_eq_neg.mpr this.symm]
  field_simp [Real.pi_ne_zero, I_ne_zero]

end TauCeti
