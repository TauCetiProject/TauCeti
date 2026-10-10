/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Duality.CyclicalMonotonicity
import TauCeti.MeasureTheory.OptimalTransport.CTransform.Analytic
import TauCeti.MeasureTheory.OptimalTransport.Existence.Basic

/-!
# Dual attainment for costs with an integrable split upper bound

Let `c : X × Y → ℝ≥0∞` be a lower semicontinuous cost on a product of Polish spaces, and suppose
it has an integrable split upper bound: `c (x, y) ≤ ENNReal.ofReal (cX x + cY y)` (the positive
part of `cX x + cY y`) with `cX ∈ L¹(μ)` and `cY ∈ L¹(ν)`. Then the Kantorovich dual problem
between the probability measures `μ` and `ν` is attained by integrable potentials, and every
optimal plan is concentrated on their contact set. In particular the cost is finite everywhere and
the optimal cost is finite.

The potentials are feasible on a product `A ×ˢ B` of sets of full measure, not on all of
`X × Y`. Nothing stronger holds in general: take `X = {0, 1}`, `μ = δ₀`, `Y = ℕ` with a law `ν`
of full support and finite mean, `c (0, y) = y` and `c (1, y) = 0`. An optimal pair must have
`ψ y = y - φ 0` for every `y`, and then no real value of `φ 1` satisfies `φ 1 + ψ y ≤ 0` for all
`y`. Feasibility on `A ×ˢ B` is still enough for weak duality, because every coupling of `μ` and
`ν` gives `A ×ˢ B` full measure.

The proof follows Villani's. Fix an optimal plan `π`. By
`TauCeti.IsOptimalCoupling.exists_isCyclicallyMonotone_of_lowerSemicontinuous` it is concentrated
on a Borel `c`-cyclically monotone set `S`. Rüschendorf's potential `φ₀` of `S` puts `S` inside
its `c`-superdifferential, and `TauCeti.nullMeasurable_rockafellarPotential` makes it
universally measurable. A Borel modification of `φ₀` on a full-measure set `A` and the
`c`-transform of its restriction to `A` give the two potentials
(`TauCeti.IsCoupling.exists_ae_add_eq_of_isCyclicallyMonotone`). Feasibility at fixed points
`x₁ ∈ A` and `y₁ ∈ B` bounds them above by `c (x, y₁) - ψ y₁` and `c (x₁, y) - φ x₁`. Along `π` the
two potentials add up to the cost, so each is also bounded below by minus the upper bound of the
other. The split upper bound turns these two-sided estimates into integrability.

## Main statements

* `TauCeti.ofReal_kantorovichDualValue_le_transportCost_of_null_compl` — weak duality for
  potentials feasible on a product of full-measure sets;
* `TauCeti.IsCoupling.exists_ae_add_eq_of_isCyclicallyMonotone` — a coupling concentrated on a
  Borel cyclically monotone set is certified by real potentials feasible on a product of
  full-measure sets;
* `TauCeti.IsOptimalCoupling.exists_ae_mem_dualContactSet_of_le_add` — every optimal plan is
  concentrated on the contact set of an integrable pair of potentials feasible on a product of
  full-measure sets;
* `TauCeti.exists_kantorovichDualValue_eq_of_le_add` — **dual attainment**: such a pair exists
  whose dual value is the optimal transport cost.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Theorem 5.10 (iii).
* L. Ambrosio and A. Pratelli, *Existence and stability results in the `L¹` theory of optimal
  transportation*, in *Optimal Transportation and Applications*, Lecture Notes in Math. 1813,
  Springer 2003, Theorem 3.2.
* L. Rüschendorf, *On c-optimal random variables*, Statist. Probab. Lett. 27 (1996), 267--270.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace TauCeti

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
  {c : X × Y → ℝ≥0∞}

/-- **Weak duality for potentials feasible on a product of full-measure sets.** If integrable
potentials satisfy `φ x + ψ y ≤ c (x, y)` for `x ∈ A` and `y ∈ B`, where `Aᶜ` is `μ`-null and
`Bᶜ` is `ν`-null, then the positive part of their dual value is at most the transport cost:
every coupling of `μ` and `ν` gives `A ×ˢ B` full measure. -/
theorem ofReal_kantorovichDualValue_le_transportCost_of_null_compl {φ : X → ℝ} {ψ : Y → ℝ}
    {A : Set X} {B : Set Y} (hA : μ Aᶜ = 0) (hB : ν Bᶜ = 0) (hφ : Integrable φ μ)
    (hψ : Integrable ψ ν) (hfeas : ∀ x ∈ A, ∀ y ∈ B, ENNReal.ofReal (φ x + ψ y) ≤ c (x, y)) :
    ENNReal.ofReal (kantorovichDualValue μ ν φ ψ) ≤ transportCost c μ ν := by
  refine le_transportCost fun π hπ ↦ ?_
  have hAπ : ∀ᵐ z ∂π, z.1 ∈ A := hπ.measurePreserving_fst.quasiMeasurePreserving.ae <|
    measure_eq_zero_iff_ae_notMem.1 hA |>.mono fun _ h ↦ by simpa using h
  have hBπ : ∀ᵐ z ∂π, z.2 ∈ B := hπ.measurePreserving_snd.quasiMeasurePreserving.ae <|
    measure_eq_zero_iff_ae_notMem.1 hB |>.mono fun _ h ↦ by simpa using h
  rw [kantorovichDualValue_eq_integral hπ hφ hψ]
  exact (TauCeti.MeasureTheory.ofReal_integral_le_lintegral_ofReal
    (μ := π) (f := fun z : X × Y ↦ φ z.1 + ψ z.2)).trans <| lintegral_mono_ae <| by
      filter_upwards [hAπ, hBπ] with z hzA hzB
      exact hfeas z.1 hzA z.2 hzB

variable [TopologicalSpace X] [PolishSpace X] [BorelSpace X] [TopologicalSpace Y] [PolishSpace Y]
  [BorelSpace Y] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {π : Measure (X × Y)}

/-- **Real contact potentials of a cyclically monotone set.** Let `r` be a measurable real cost
on a product of Polish spaces, and let a coupling `π` of two probability measures be concentrated
on a Borel `r`-cyclically monotone set `S`. Then there are potentials `φ` (Borel) and `ψ`
(a.e.-measurable) and measurable sets `A`, `B` of full measure such that `φ x + ψ y ≤ r (x, y)`
on `A ×ˢ B` and `φ x + ψ y = r (x, y)` for `π`-a.e. `(x, y)`. The potential `φ` is a Borel
modification of Rüschendorf's potential `TauCeti.rockafellarPotential r S p`, and `ψ` is the
`r`-transform of its restriction to `A`. -/
theorem IsCoupling.exists_ae_add_eq_of_isCyclicallyMonotone (hπ : IsCoupling π μ ν)
    {r : X × Y → ℝ} (hr : Measurable r) {S : Set (X × Y)} (hSmeas : MeasurableSet S)
    (hS : IsCyclicallyMonotone r S) (haeS : ∀ᵐ z ∂π, z ∈ S) :
    ∃ (φ : X → ℝ) (ψ : Y → ℝ) (A : Set X) (B : Set Y), MeasurableSet A ∧ MeasurableSet B ∧
      μ Aᶜ = 0 ∧ ν Bᶜ = 0 ∧ Measurable φ ∧ AEMeasurable ψ ν ∧
      (∀ x ∈ A, ∀ y ∈ B, φ x + ψ y ≤ r (x, y)) ∧ ∀ᵐ z ∂π, φ z.1 + ψ z.2 = r z := by
  classical
  have hfst := hπ.measurePreserving_fst.quasiMeasurePreserving
  have hsnd := hπ.measurePreserving_snd
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact IsProbabilityMeasure.ne_zero μ (by simpa using hπ.measurePreserving_fst.map_eq.symm)
  have : (ae π).NeBot := ae_neBot.2 hπ0
  obtain ⟨p, hp⟩ := haeS.exists
  -- Rüschendorf's potential `φ₀` of `S`, and a Borel function `g` equal to it `μ`-a.e.
  set φ₀ := rockafellarPotential r S p
  have hsub : S ⊆ cSuperdifferential r φ₀ :=
    hS.subset_cSuperdifferential_rockafellarPotential hp
  have hφ₀meas : AEMeasurable φ₀ μ :=
    (nullMeasurable_rockafellarPotential μ hr hSmeas p).aemeasurable
  set g := hφ₀meas.mk φ₀
  have hg : Measurable g := hφ₀meas.measurable_mk
  have hφ₀g : ∀ᵐ z ∂π, φ₀ z.1 = g z.1 := hfst.ae hφ₀meas.ae_eq_mk
  have hgbot : ∀ᵐ x ∂μ, g x ≠ ⊥ := by
    rw [← hπ.measurePreserving_fst.map_eq]
    refine (ae_map_iff measurable_fst.aemeasurable (hg (measurableSet_singleton ⊥).compl)).2 ?_
    filter_upwards [haeS, hφ₀g] with z hzS hz
    have hz' : (z.1, z.2) ∈ contactSet r φ₀ (cTransform r φ₀) := by
      rw [← cSuperdifferential_def]
      exact hsub hzS
    exact hz ▸ ne_bot_left_of_mem_contactSet hz'
  -- The first potential `φ` is the real part of `g` on a measurable full-measure set `A`.
  set A : Set X := (toMeasurable μ {x | ¬(φ₀ x = g x ∧ g x ≠ ⊥)})ᶜ with hA
  have hAmeas : MeasurableSet A := (measurableSet_toMeasurable _ _).compl
  have hμA : μ Aᶜ = 0 := by
    rw [hA, compl_compl, measure_toMeasurable]
    exact ae_iff.1 (hφ₀meas.ae_eq_mk.and hgbot)
  have haeA : ∀ᵐ x ∂μ, x ∈ A := measure_eq_zero_iff_ae_notMem.1 hμA |>.mono fun _ h ↦ by
    simpa using h
  set φ : X → ℝ := fun x ↦ (g x).toReal with hφ
  have hφA : ∀ x ∈ A, φ₀ x = (φ x : EReal) := by
    intro x hx
    have hx' : φ₀ x = g x ∧ g x ≠ ⊥ := by
      by_contra hn
      exact hx (subset_toMeasurable _ _ hn)
    have htop : g x ≠ ⊤ :=
      hx'.1 ▸ ne_top_of_le_ne_top (EReal.coe_ne_top _) (rockafellarPotential_le_sub hp x)
    rw [hx'.1, hφ, EReal.coe_toReal htop hx'.2]
  obtain ⟨x₁, hx₁⟩ := haeA.exists
  -- The second potential is the `c`-transform of `φ` restricted to `A`.
  set g' : X → EReal := fun x ↦ if x ∈ A then (φ x : EReal) else ⊥ with hg'
  set ψ₀ := cTransform r g' with hψ₀
  have hint : Measurable fun z : X × Y ↦ (r z : EReal) - g' z.1 := by
    have heq : (fun z : X × Y ↦ (r z : EReal) - g' z.1) =
        fun z ↦ if z.1 ∈ A then ((r z - φ z.1 : ℝ) : EReal) else ⊤ := by
      funext z
      by_cases hz : z.1 ∈ A <;> simp [hg', hz, EReal.coe_sub]
    rw [heq]
    exact Measurable.ite (hAmeas.preimage measurable_fst)
      (measurable_coe_real_ereal.comp (hr.sub (hg.ereal_toReal.comp measurable_fst)))
      measurable_const
  have hψ₀meas : NullMeasurable ψ₀ ν := nullMeasurable_cTransform ν hint
  have hψ₀le y : ψ₀ y ≤ ((r (x₁, y) - φ x₁ : ℝ) : EReal) := by
    simpa [hg', hx₁, EReal.coe_sub] using cTransform_le r g' x₁ y
  have hcontact : ∀ z ∈ S, z.1 ∈ A → ψ₀ z.2 = ((r z - φ z.1 : ℝ) : EReal) := by
    intro z hzS hzA
    refine le_antisymm (by simpa [hg', hzA, EReal.coe_sub] using cTransform_le r g' z.1 z.2) ?_
    have hle : g' ≤ φ₀ := fun x ↦ by
      by_cases hx : x ∈ A
      · simp [hg', hx, hφA x hx]
      · simp [hg', hx]
    calc ((r z - φ z.1 : ℝ) : EReal) = cTransform r φ₀ z.2 := by
          rw [cTransform_eq_of_mem_cSuperdifferential (hsub hzS), hφA z.1 hzA, EReal.coe_sub]
      _ ≤ ψ₀ z.2 := cTransform_antitone r hle z.2
  -- The second potential `ψ` is the real part of `ψ₀` on the full-measure set `B` where `ψ₀` is
  -- not `⊥`. Along `π` the two potentials add up to the cost.
  have haeAπ : ∀ᵐ z ∂π, z.1 ∈ A := hfst.ae haeA
  have hψ₀bot : ν (ψ₀ ⁻¹' {⊥}) = 0 := by
    rw [← hsnd.measure_preimage (hψ₀meas (measurableSet_singleton ⊥))]
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    filter_upwards [haeS, haeAπ] with z hzS hzA
    simp only [mem_preimage, mem_singleton_iff, hcontact z hzS hzA]
    exact EReal.coe_ne_bot _
  set B : Set Y := (toMeasurable ν (ψ₀ ⁻¹' {⊥}))ᶜ with hB
  have hBmeas : MeasurableSet B := (measurableSet_toMeasurable _ _).compl
  have hνB : ν Bᶜ = 0 := by rw [hB, compl_compl, measure_toMeasurable, hψ₀bot]
  set ψ : Y → ℝ := fun y ↦ (ψ₀ y).toReal with hψ
  have hψB : ∀ y ∈ B, ψ₀ y = (ψ y : EReal) := by
    intro y hy
    have hbot : ψ₀ y ≠ ⊥ := fun hb ↦ hy (subset_toMeasurable _ _ hb)
    exact (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) (hψ₀le y)) hbot).symm
  have hsum : ∀ᵐ z ∂π, φ z.1 + ψ z.2 = r z := by
    filter_upwards [haeS, haeAπ] with z hzS hzA
    simp only [hψ, hcontact z hzS hzA, EReal.toReal_coe]
    ring
  refine ⟨φ, ψ, A, B, hAmeas, hBmeas, hμA, hνB, hg.ereal_toReal,
    hψ₀meas.aemeasurable.ereal_toReal, fun x hx y hy ↦ ?_, hsum⟩
  -- Feasibility on `A ×ˢ B` is the `r`-transform inequality.
  have hle := add_cTransform_le r g' x y
  rwa [← hψ₀, hψB y hy, show g' x = φ x by simp [hg', hx], ← EReal.coe_add,
    EReal.coe_le_coe_iff] at hle

/-- **Optimal plans are certified by integrable potentials.** Let `c` be a lower semicontinuous
cost on a product of Polish spaces with an integrable split upper bound
`c (x, y) ≤ ENNReal.ofReal (cX x + cY y)`, and let `π` be an optimal coupling of two probability
measures. Then there are integrable potentials `φ`, `ψ` and sets `A`, `B` of full measure such
that the dual constraint `φ x + ψ y ≤ c (x, y)` holds on `A ×ˢ B` and `π` is concentrated on the
contact set of `(φ, ψ)`. Feasibility cannot be required on all of `X × Y`; see the module
docstring. -/
theorem IsOptimalCoupling.exists_ae_mem_dualContactSet_of_le_add (h : IsOptimalCoupling c π μ ν)
    (hc : LowerSemicontinuous c) {cX : X → ℝ} {cY : Y → ℝ} (hcX : Integrable cX μ)
    (hcY : Integrable cY ν) (hle : ∀ x y, c (x, y) ≤ ENNReal.ofReal (cX x + cY y)) :
    ∃ (φ : X → ℝ) (ψ : Y → ℝ) (A : Set X) (B : Set Y), MeasurableSet A ∧ MeasurableSet B ∧
      μ Aᶜ = 0 ∧ ν Bᶜ = 0 ∧ Integrable φ μ ∧ Integrable ψ ν ∧
      (∀ x ∈ A, ∀ y ∈ B, ENNReal.ofReal (φ x + ψ y) ≤ c (x, y)) ∧
      ∀ᵐ z ∂π, z ∈ dualContactSet c φ ψ := by
  have hπ := h.toIsCoupling
  -- The real cost `r`, dominated by the nonnegative split bound `|cX| + |cY|`.
  set r : X × Y → ℝ := fun z ↦ (c z).toReal
  have hctop z : c z ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hle z.1 z.2)
  have hcr : (fun z ↦ ENNReal.ofReal (r z)) = c := funext fun z ↦ ENNReal.ofReal_toReal (hctop z)
  have hrmeas : Measurable r := hc.measurable.ennreal_toReal
  have hrle x y : r (x, y) ≤ |cX x| + |cY y| :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) ((hle x y).trans
      (ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (abs_add_le _ _))))
  have hrnn z : 0 ≤ r z := ENNReal.toReal_nonneg
  -- The optimal cost is finite, so `π` is concentrated on a cyclically monotone Borel set `S`.
  have hfinπ : ∫⁻ z, c z ∂π ≠ ∞ := by
    refine ne_top_of_le_ne_top (hπ.integrable_add_split hcX.abs hcY.abs).lintegral_lt_top.ne
      (lintegral_mono fun z ↦ ?_)
    rw [← hcr]
    exact ENNReal.ofReal_le_ofReal (hrle z.1 z.2)
  obtain ⟨S, hSmeas, hSmono, hπS⟩ :=
    h.exists_isCyclicallyMonotone_of_lowerSemicontinuous hc (h.lintegral_eq ▸ hfinπ)
  rw [← hcr, isCyclicallyMonotone_ofReal_iff hrnn] at hSmono
  have haeS : ∀ᵐ z ∂π, z ∈ S := measure_eq_zero_iff_ae_notMem.1 hπS |>.mono fun _ h ↦ by
    simpa using h
  -- Real potentials feasible on `A ×ˢ B` that add up to the cost along `π`.
  obtain ⟨φ, ψ, A, B, hAmeas, hBmeas, hμA, hνB, hφmeas, hψmeas, hfeas, hsum⟩ :=
    hπ.exists_ae_add_eq_of_isCyclicallyMonotone hrmeas hSmeas hSmono haeS
  obtain ⟨x₁, hx₁⟩ := (measure_eq_zero_iff_ae_notMem.1 hμA).exists
  obtain ⟨y₁, hy₁⟩ := (measure_eq_zero_iff_ae_notMem.1 hνB).exists
  rw [notMem_compl_iff] at hx₁ hy₁
  -- Integrability: `φ ≤ c (·, y₁) - ψ y₁` on `A` and `ψ ≤ c (x₁, ·) - φ x₁` on `B`.
  obtain ⟨hφint, hψint⟩ := hπ.integrable_and_integrable_of_ae_add_nonneg (f := φ) (g := ψ)
    (U := fun x ↦ |cX x| + (|cY y₁| - ψ y₁)) (V := fun y ↦ |cY y| + (|cX x₁| - φ x₁))
    hφmeas.aestronglyMeasurable hψmeas.aestronglyMeasurable
    (hcX.abs.add (integrable_const _)) (hcY.abs.add (integrable_const _))
    ((measure_eq_zero_iff_ae_notMem.1 hμA).mono fun x hx ↦ by
      linarith [hfeas x (notMem_compl_iff.1 hx) y₁ hy₁, hrle x y₁])
    ((measure_eq_zero_iff_ae_notMem.1 hνB).mono fun y hy ↦ by
      linarith [hfeas x₁ hx₁ y (notMem_compl_iff.1 hy), hrle x₁ y])
    (hsum.mono fun z hz ↦ hz ▸ hrnn z)
  refine ⟨φ, ψ, A, B, hAmeas, hBmeas, hμA, hνB, hφint, hψint, fun x hx y hy ↦ ?_,
    hsum.mono fun z hz ↦ mem_dualContactSet_of_toReal_eq (hctop z) hz.symm⟩
  exact (ENNReal.ofReal_le_ofReal (hfeas x hx y hy)).trans_eq (ENNReal.ofReal_toReal (hctop _))

/-- **Kantorovich dual attainment for costs with an integrable split upper bound.** Let `c` be a
lower semicontinuous cost on a product of Polish spaces with
`c (x, y) ≤ ENNReal.ofReal (cX x + cY y)` for integrable `cX` and `cY`. Then there are integrable
potentials `φ`, `ψ`, feasible on a product `A ×ˢ B` of sets of full measure, whose dual value is
the optimal transport cost. By `TauCeti.ofReal_kantorovichDualValue_le_transportCost_of_null_compl`
no such pair has a larger value, so the dual problem over this class is attained. -/
theorem exists_kantorovichDualValue_eq_of_le_add (hc : LowerSemicontinuous c) {cX : X → ℝ}
    {cY : Y → ℝ} (hcX : Integrable cX μ) (hcY : Integrable cY ν)
    (hle : ∀ x y, c (x, y) ≤ ENNReal.ofReal (cX x + cY y)) :
    ∃ (φ : X → ℝ) (ψ : Y → ℝ) (A : Set X) (B : Set Y), MeasurableSet A ∧ MeasurableSet B ∧
      μ Aᶜ = 0 ∧ ν Bᶜ = 0 ∧ Integrable φ μ ∧ Integrable ψ ν ∧
      (∀ x ∈ A, ∀ y ∈ B, ENNReal.ofReal (φ x + ψ y) ≤ c (x, y)) ∧
      kantorovichDualValue μ ν φ ψ = (transportCost c μ ν).toReal := by
  obtain ⟨π, hπ⟩ := exists_isOptimalCoupling μ ν hc
  obtain ⟨φ, ψ, A, B, hA, hB, hμA, hνB, hφ, hψ, hfeas, hae⟩ :=
    hπ.exists_ae_mem_dualContactSet_of_le_add hc hcX hcY hle
  refine ⟨φ, ψ, A, B, hA, hB, hμA, hνB, hφ, hψ, hfeas, ?_⟩
  rw [← hπ.lintegral_eq, lintegral_eq_ofReal_kantorovichDualValue hπ.toIsCoupling hφ hψ hae,
    ENNReal.toReal_ofReal
      (kantorovichDualValue_nonneg_of_ae_mem_dualContactSet hπ.toIsCoupling hφ hψ hae)]

end TauCeti
