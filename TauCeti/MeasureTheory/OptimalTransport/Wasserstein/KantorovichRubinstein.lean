/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Duality.Compact
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.FiniteSupport
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Pushforward

/-!
# Kantorovich–Rubinstein duality

For probability measures `μ` and `ν` with finite first moments on a separable metric space whose
measurable structure is standard Borel, the `1`-Wasserstein distance is the largest difference of
expectations of a `1`-Lipschitz real function:

`W₁ (μ, ν) = ⨆ (f : X → ℝ) (_ : LipschitzWith 1 f), ENNReal.ofReal (∫ f ∂μ - ∫ f ∂ν)`.

This is the Kantorovich duality for the cost `edist`, in the special form that a distance cost
allows: a single potential `f` replaces the pair `(φ, ψ)`, with `ψ = -f`. It turns `W₁` estimates
into estimates on the expectations of Lipschitz test functions, and conversely. Since only the
differences of expectations enter, the supremum may be restricted to the functions vanishing at a
prescribed basepoint.

The inequality bounding a difference of expectations by `W₁` (weak duality) holds on an arbitrary
extended pseudometric space, for arbitrary measures, as soon as the test function is integrable.
On a compact pseudometric space the full formula holds for all probability measures, with no
moment hypothesis. In general, the finite-moment hypotheses make every `1`-Lipschitz function
integrable (`TauCeti.HasFiniteMoment.integrable_of_lipschitzWith`), so that the Bochner integrals on
the right are the honest expectations; under them both sides are finite.

## Main statements

* `TauCeti.ofReal_integral_sub_integral_le_wassersteinEDist_one` — the difference of expectations
  of an integrable `1`-Lipschitz function is at most `W₁`, on an arbitrary extended pseudometric
  space;
* `TauCeti.wassersteinEDist_one_eq_iSup_of_compactSpace` — Kantorovich–Rubinstein duality for
  probability measures on a compact pseudometric space;
* `TauCeti.wassersteinEDist_one_eq_iSup` — Kantorovich–Rubinstein duality for probability measures
  with finite first moments on a second-countable pseudometric space with a standard Borel
  measurable structure, in particular on a Polish metric space;
* `TauCeti.wassersteinEDist_one_eq_iSup_apply_eq_zero` — the same formula with the test functions
  normalized to vanish at a basepoint.

## References

* L. V. Kantorovich and G. S. Rubinstein, *On a space of completely additive functions*, Vestnik
  Leningrad. Univ. 13 (1958), no. 7, 52--59.
* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, AMS 2003,
  Theorem 1.14.
* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Particular
  Case 5.16.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

universe u

variable {X : Type u} [MeasurableSpace X] {μ ν : Measure X}

section WeakDuality

variable [PseudoEMetricSpace X]

/-- **Kantorovich–Rubinstein weak duality.** The difference of the expectations of an integrable
`1`-Lipschitz real function under two measures is at most their `1`-Wasserstein distance. No
measurability of the ground distance and no finiteness of the measures is needed. -/
theorem ofReal_integral_sub_integral_le_wassersteinEDist_one {f : X → ℝ}
    (hf : LipschitzWith 1 f) (hμ : Integrable f μ) (hν : Integrable f ν) :
    ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν) ≤ wassersteinEDist 1 μ ν := by
  -- `(f, -f)` is a feasible dual pair for the cost `edist`, so Kantorovich weak duality applies
  have hfeas : DualFeasible (fun z : X × X ↦ edist z.1 z.2) f (fun y ↦ -f y) := by
    refine dualFeasible_iff_ofReal_add_le.2 fun x y ↦ ?_
    calc ENNReal.ofReal (f x + -f y) ≤ edist (f x) (f y) := by
          rw [edist_dist, Real.dist_eq, ← sub_eq_add_neg]
          exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ edist x y := by simpa using hf.edist_le_mul x y
  have hdual := hfeas.ofReal_kantorovichDualValue_le_transportCost hμ hν.neg
  rwa [kantorovichDualValue_def, integral_neg, ← sub_eq_add_neg,
    ← wassersteinEDist_one_eq_transportCost] at hdual

end WeakDuality

section Compact

variable [PseudoMetricSpace X] [CompactSpace X] [OpensMeasurableSpace X]

/-- The approximate form of Kantorovich–Rubinstein duality on a compact space: `W₁` is within any
`ε > 0` of the difference of expectations of some `1`-Lipschitz function. -/
private theorem exists_lipschitzWith_wassersteinEDist_one_le [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {ε : ℝ} (hε : 0 < ε) :
    ∃ f : X → ℝ, LipschitzWith 1 f ∧
      wassersteinEDist 1 μ ν ≤ ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν + ε) := by
  have : Nonempty X := μ.nonempty_of_neZero
  -- strong Kantorovich duality for the continuous cost `dist` gives a continuous feasible pair
  -- `(φ, ψ)` whose value is within `ε` of `W₁`
  obtain ⟨φ, ψ, hφc, hψc, hfeas, hle⟩ :=
    exists_continuous_forall_add_le_transportCost_le (μ := μ) (ν := ν)
      (c := fun z : X × X ↦ dist z.1 z.2) continuous_dist (fun _ ↦ dist_nonneg) hε
  -- the transform `f x = ⨅ y, (dist x y - ψ y)` is `1`-Lipschitz and satisfies `φ ≤ f` and
  -- `ψ ≤ -f`, so `f` alone does at least as well as the pair
  obtain ⟨M, hM⟩ := (isCompact_range hψc).bddAbove
  have hbdd : ∀ x, BddBelow (range fun y ↦ dist x y - ψ y) := fun x ↦
    ⟨-M, by rintro _ ⟨y, rfl⟩; linarith [dist_nonneg (x := x) (y := y), hM ⟨y, rfl⟩]⟩
  set f : X → ℝ := fun x ↦ ⨅ y, (dist x y - ψ y)
  have hf : LipschitzWith 1 f := LipschitzWith.of_le_add fun x x' ↦ by
    rw [← sub_le_iff_le_add]
    refine le_ciInf fun y ↦ ?_
    linarith [ciInf_le (hbdd x) y, dist_triangle x x' y]
  have hφf : ∀ x, φ x ≤ f x := fun x ↦ le_ciInf fun y ↦ by linarith [hfeas x y]
  have hψf : ∀ y, ψ y ≤ -f y := fun y ↦ by
    linarith [ciInf_le (hbdd y) y, dist_self y]
  refine ⟨f, hf, ?_⟩
  have hcost : wassersteinEDist 1 μ ν
      = transportCost (fun z : X × X ↦ ENNReal.ofReal (dist z.1 z.2)) μ ν := by
    simp only [wassersteinEDist_one_eq_transportCost, edist_dist]
  refine hcost.trans_le (hle.trans (ENNReal.ofReal_le_ofReal ?_))
  have hfc := hf.continuous
  have hφ : ∫ x, φ x ∂μ ≤ ∫ x, f x ∂μ :=
    integral_mono (hφc.integrable_of_hasCompactSupport (.of_compactSpace _))
      (hfc.integrable_of_hasCompactSupport (.of_compactSpace _)) hφf
  have hψ : ∫ y, ψ y ∂ν ≤ ∫ y, -f y ∂ν :=
    integral_mono (hψc.integrable_of_hasCompactSupport (.of_compactSpace _))
      (hfc.neg.integrable_of_hasCompactSupport (.of_compactSpace _)) hψf
  rw [kantorovichDualValue_def]
  rw [integral_neg] at hψ
  linarith

/-- **Kantorovich–Rubinstein duality on a compact space.** For probability measures on a compact
pseudometric space whose open sets are measurable, the `1`-Wasserstein distance is the supremum
of the differences of expectations of the `1`-Lipschitz real functions. -/
theorem wassersteinEDist_one_eq_iSup_of_compactSpace [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    wassersteinEDist 1 μ ν =
      ⨆ (f : X → ℝ) (_ : LipschitzWith 1 f), ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν) := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_) (iSup₂_le fun f hf ↦ ?_)
  · obtain ⟨f, hf, hle⟩ :=
      exists_lipschitzWith_wassersteinEDist_one_le (μ := μ) (ν := ν) (NNReal.coe_pos.2 hε)
    calc wassersteinEDist 1 μ ν
        ≤ ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν) + ENNReal.ofReal ε :=
          hle.trans ENNReal.ofReal_add_le
      _ ≤ _ := by
          rw [ENNReal.ofReal_coe_nnreal]
          gcongr
          exact le_iSup₂ (f := fun (f : X → ℝ) (_ : LipschitzWith 1 f) ↦
            ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν)) f hf
  · exact ofReal_integral_sub_integral_le_wassersteinEDist_one hf
      (hf.continuous.integrable_of_hasCompactSupport (.of_compactSpace _))
      (hf.continuous.integrable_of_hasCompactSupport (.of_compactSpace _))

end Compact

section StandardBorel

variable [PseudoMetricSpace X] [OpensMeasurableSpace X] [SecondCountableTopology X]
  [StandardBorelSpace X]

omit [StandardBorelSpace X] in
/-- Kantorovich–Rubinstein duality for laws pushed onto a finite set, in the direction not given by
weak duality: the `1`-Wasserstein distance of two laws supported on a common finite set is at most
the supremum of the differences of expectations of the `1`-Lipschitz real functions on `X`. -/
private theorem wassersteinEDist_one_map_le_iSup [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {T T' : X → X} (hT : Measurable T) (hT' : Measurable T')
    {t : Finset X} (hTt : ∀ x, T x ∈ t) (hT't : ∀ x, T' x ∈ t) :
    wassersteinEDist 1 (μ.map T) (ν.map T') ≤ ⨆ (G : X → ℝ) (_ : LipschitzWith 1 G),
      ENNReal.ofReal (∫ x, G x ∂(μ.map T) - ∫ x, G x ∂(ν.map T')) := by
  classical
  -- the finite subspace `t` is compact, so the compact case applies on it; every `1`-Lipschitz
  -- function on `t` then extends to one on `X` by McShane's theorem, `LipschitzOnWith.extend_real`
  -- the two laws, read on the finite subspace `t`
  let U : X → (t : Set X) := fun x ↦ ⟨T x, Finset.mem_coe.2 (hTt x)⟩
  let U' : X → (t : Set X) := fun x ↦ ⟨T' x, Finset.mem_coe.2 (hT't x)⟩
  have hμU : (μ.map U).map (↑) = μ.map T :=
    Measure.map_map measurable_subtype_coe hT.subtype_mk
  have hνU : (ν.map U').map (↑) = ν.map T' :=
    Measure.map_map measurable_subtype_coe hT'.subtype_mk
  have hpush : wassersteinEDist 1 (μ.map T) (ν.map T') ≤
      wassersteinEDist 1 (μ.map U) (ν.map U') := by
    rw [← hμU, ← hνU]
    simpa using wassersteinEDist_map_le_mul measurable_edist measurable_subtype_coe
      isometry_subtype_coe.lipschitzWith (μ.map U) (ν.map U') (p := 1)
  refine hpush.trans ?_
  rw [wassersteinEDist_one_eq_iSup_of_compactSpace]
  refine iSup₂_le fun g hg ↦ ?_
  -- extend the test function from `t` to `X`
  have hrestrict : (t : Set X).domRestrict (fun x ↦ if h : x ∈ (t : Set X) then g ⟨x, h⟩ else 0)
      = g :=
    funext fun y ↦ dite_eq_left y.2
  obtain ⟨G, hG, hGg⟩ := LipschitzOnWith.extend_real
    (lipschitzOnWith_iff_restrict.2 (hrestrict ▸ hg))
  have hGt : ∀ y : (t : Set X), G y = g y := fun y ↦ by
    simpa [y.2] using (hGg y.2).symm
  have hint (ρ : Measure (t : Set X)) : ∫ y, g y ∂ρ = ∫ x, G x ∂(ρ.map (↑)) := by
    rw [integral_map measurable_subtype_coe.aemeasurable hG.continuous.aestronglyMeasurable]
    simp only [hGt]
  refine le_iSup₂_of_le G hG (le_of_eq ?_)
  rw [hint, hint, hμU, hνU]

/-- **Kantorovich–Rubinstein duality.** For probability measures with finite first moments on a
second-countable pseudometric space whose measurable structure is standard Borel and contains the
open sets — in particular on a Polish metric space with its Borel σ-algebra — the
`1`-Wasserstein distance is the supremum of the differences of expectations of the `1`-Lipschitz
real functions. -/
theorem wassersteinEDist_one_eq_iSup [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : HasFiniteMoment 1 μ) (hν : HasFiniteMoment 1 ν) :
    wassersteinEDist 1 μ ν =
      ⨆ (f : X → ℝ) (_ : LipschitzWith 1 f), ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν) := by
  refine le_antisymm ?_ (iSup₂_le fun f hf ↦
    ofReal_integral_sub_integral_le_wassersteinEDist_one hf
      (hμ.integrable_of_lipschitzWith hf) (hν.integrable_of_lipschitzWith hf))
  -- reduce to the compact case by quantization: push both laws, within `W₁` distance `δ`, onto a
  -- common finite set, where the formula holds; replacing the quantized laws by the original ones
  -- changes both sides by a small amount, by the triangle inequality for `W₁` on the left and by
  -- weak duality on the right
  set R := ⨆ (f : X → ℝ) (_ : LipschitzWith 1 f), ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  set δ : ℝ≥0∞ := (ε : ℝ≥0∞) / 2 / 2 with hδ
  have hδ0 : δ ≠ 0 :=
    (ENNReal.half_pos (ENNReal.half_pos (by exact_mod_cast hε.ne')).ne').ne'
  have hδtop : δ ≠ ∞ := by simp [hδ, ENNReal.div_eq_top]
  have hδε : δ + δ + (δ + δ) = ε := by rw [hδ, ENNReal.add_halves, ENNReal.add_halves]
  -- quantize both laws onto a common finite set, within `W₁` distance `δ`
  obtain ⟨s, T, hT, hTs, hμT⟩ := exists_map_wassersteinEDist_le le_rfl ENNReal.one_ne_top hμ hδ0
  obtain ⟨s', T', hT', hT's, hνT⟩ :=
    exists_map_wassersteinEDist_le le_rfl ENNReal.one_ne_top hν hδ0
  have hμT' : HasFiniteMoment 1 (μ.map T) :=
    (hasFiniteMoment_iff_wassersteinEDist_ne_top_of_hasFiniteMoment measurable_edist hμ).2
      (ne_top_of_le_ne_top hδtop hμT)
  have hνT' : HasFiniteMoment 1 (ν.map T') :=
    (hasFiniteMoment_iff_wassersteinEDist_ne_top_of_hasFiniteMoment measurable_edist hν).2
      (ne_top_of_le_ne_top hδtop hνT)
  -- the quantized laws satisfy the formula, and quantizing moves each expectation by at most `δ`
  have hquant : wassersteinEDist 1 (μ.map T) (ν.map T') ≤ R + (δ + δ) := by
    classical
    refine (wassersteinEDist_one_map_le_iSup hT hT' (t := s ∪ s')
      (fun x ↦ Finset.mem_union_left _ (hTs x)) (fun x ↦ Finset.mem_union_right _ (hT's x))).trans
      (iSup₂_le fun G hG ↦ ?_)
    have h₀ : ENNReal.ofReal (∫ x, G x ∂μ - ∫ x, G x ∂ν) ≤ R :=
      le_iSup₂ (f := fun (f : X → ℝ) (_ : LipschitzWith 1 f) ↦
        ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν)) G hG
    have h₁ := ofReal_integral_sub_integral_le_wassersteinEDist_one hG
      (hμT'.integrable_of_lipschitzWith hG) (hμ.integrable_of_lipschitzWith hG)
    have h₂ := ofReal_integral_sub_integral_le_wassersteinEDist_one hG
      (hν.integrable_of_lipschitzWith hG) (hνT'.integrable_of_lipschitzWith hG)
    rw [wassersteinEDist_comm measurable_edist] at h₁
    calc ENNReal.ofReal (∫ x, G x ∂(μ.map T) - ∫ x, G x ∂(ν.map T'))
        = ENNReal.ofReal ((∫ x, G x ∂μ - ∫ x, G x ∂ν) +
            ((∫ x, G x ∂(μ.map T) - ∫ x, G x ∂μ) + (∫ x, G x ∂ν - ∫ x, G x ∂(ν.map T')))) := by
          congr 1
          ring
      _ ≤ ENNReal.ofReal (∫ x, G x ∂μ - ∫ x, G x ∂ν) +
            (ENNReal.ofReal (∫ x, G x ∂(μ.map T) - ∫ x, G x ∂μ) +
              ENNReal.ofReal (∫ x, G x ∂ν - ∫ x, G x ∂(ν.map T'))) :=
          ENNReal.ofReal_add_le.trans (by gcongr; exact ENNReal.ofReal_add_le)
      _ ≤ R + (δ + δ) := by
          gcongr
          exacts [h₁.trans hμT, h₂.trans hνT]
  -- pass from the quantized laws back to `μ` and `ν` by the triangle inequality
  calc wassersteinEDist 1 μ ν
      ≤ wassersteinEDist 1 μ (μ.map T) + (wassersteinEDist 1 (μ.map T) (ν.map T') +
          wassersteinEDist 1 (ν.map T') ν) :=
        (wassersteinEDist_triangle measurable_edist le_rfl _ (μ.map T) _).trans
          (by gcongr; exact wassersteinEDist_triangle measurable_edist le_rfl _ (ν.map T') _)
    _ ≤ δ + ((R + (δ + δ)) + δ) := by
        rw [wassersteinEDist_comm measurable_edist 1 (ν.map T')]
        gcongr
    _ = R + ε := by
        rw [← hδε]
        ring

/-- **Kantorovich–Rubinstein duality, normalized at a basepoint.** Under the hypotheses of
`TauCeti.wassersteinEDist_one_eq_iSup`, the supremum may be taken over the `1`-Lipschitz real
functions vanishing at any prescribed point `x₀`: subtracting a constant does not change a
difference of expectations under two probability measures. -/
theorem wassersteinEDist_one_eq_iSup_apply_eq_zero [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : HasFiniteMoment 1 μ) (hν : HasFiniteMoment 1 ν) (x₀ : X) :
    wassersteinEDist 1 μ ν = ⨆ (f : X → ℝ) (_ : LipschitzWith 1 f) (_ : f x₀ = 0),
      ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν) := by
  rw [wassersteinEDist_one_eq_iSup hμ hν]
  refine le_antisymm (iSup₂_le fun f hf ↦ ?_) (iSup₂_mono fun f hf ↦ iSup_le fun _ ↦ le_rfl)
  have hg : LipschitzWith 1 fun x ↦ f x - f x₀ := LipschitzWith.of_le_add fun x y ↦ by
    have hxy := hf.le_add_mul x y
    rw [NNReal.coe_one, one_mul] at hxy
    linarith
  refine le_iSup₂_of_le (fun x ↦ f x - f x₀) hg (le_iSup_of_le (sub_self _) (le_of_eq ?_))
  rw [integral_sub (hμ.integrable_of_lipschitzWith hf) (integrable_const _),
    integral_sub (hν.integrable_of_lipschitzWith hf) (integrable_const _)]
  simp only [integral_const, probReal_univ, one_smul, sub_sub_sub_cancel_right]

end StandardBorel

end TauCeti
