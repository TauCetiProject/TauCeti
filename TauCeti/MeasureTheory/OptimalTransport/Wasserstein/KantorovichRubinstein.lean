/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Cost.Mixture
public import TauCeti.MeasureTheory.OptimalTransport.Duality.Attainment
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

For finite measures of equal mass on a Polish pseudometric space and `R ≥ 0`, transport with
cost `min (dist x y) (2 * R)` is the greatest difference of integrals over `1`-Lipschitz real
functions bounded in absolute value by `R`. No moment assumption is needed. For probability
measures and `R = 1`, this gives the bounded-Lipschitz (Fortet–Mourier) convention with separate
Lipschitz and supremum-norm bounds of one, corresponding to a primal cap of **two**.
The bounded variant uses dual attainment and centers a conjugate potential whose oscillation
is at most `2 * R`; finite measures reduce to probability measures by normalization.

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
  normalized to vanish at a basepoint;
* `TauCeti.exists_lipschitzWith_norm_le_integral_sub_integral_eq_transportCost_truncated_dist` —
  bounded-Lipschitz dual attainment for finite measures of equal mass on a Polish space;
* `TauCeti.transportCost_truncated_dist_eq_iSup` and
  `TauCeti.transportCost_truncated_dist_eq_iSup_abs` — the signed and absolute supremum formulas
  for the distance truncated at `2 * R`.

## References

* L. V. Kantorovich and G. S. Rubinstein, *On a space of completely additive functions*, Vestnik
  Leningrad. Univ. 13 (1958), no. 7, 52--59.
* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, AMS 2003,
  Theorem 1.14.
* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Particular
  Case 5.16. For the bounded-Lipschitz variant, the ground distance is truncated at `2 * R`.
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
  rw [kantorovichDualValue_def, integral_neg, ← sub_eq_add_neg] at hdual
  -- The identification of `W₁` with the transport cost of `edist` needs a jointly measurable
  -- ground distance, but the inequality this direction does not: coupling by coupling,
  -- `∫⁻ edist ≤ eLpNorm edist 1`, with the right-hand side `∞` when `edist` is not measurable.
  refine le_wassersteinEDist fun π hπ ↦ hdual.trans
    ((transportCost_le_lintegral hπ _).trans ?_)
  simpa using lintegral_enorm_le_eLpNorm_one (μ := π) (f := fun z : X × X ↦ edist z.1 z.2)

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
    simp only [wassersteinEDist_one_eq_transportCost measurable_edist, edist_dist]
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

section BoundedLipschitz

variable [PseudoMetricSpace X] {R : ℝ}

/-- Bounded-Lipschitz weak duality for the truncated distance cost. The bound `R` on each
potential produces the cap `2 * R` on the cost. -/
theorem ofReal_integral_sub_integral_le_transportCost_truncated_dist
    [OpensMeasurableSpace X] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : X → ℝ} (hf : LipschitzWith 1 f) (hfb : ∀ x, ‖f x‖ ≤ R) :
    ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν) ≤
      transportCost (fun z : X × X ↦ ENNReal.ofReal (min (dist z.1 z.2) (2 * R))) μ ν := by
  have hi (ρ : Measure X) [IsFiniteMeasure ρ] : Integrable f ρ :=
    .of_bound hf.continuous.aestronglyMeasurable R (ae_of_all _ hfb)
  have hfeas : DualFeasible
      (fun z : X × X ↦ ENNReal.ofReal (min (dist z.1 z.2) (2 * R))) f (fun y ↦ -f y) := by
    refine dualFeasible_iff_ofReal_add_le.2 fun x y ↦ ENNReal.ofReal_le_ofReal ?_
    have hdist := hf.le_add_mul x y
    have hx := (abs_le.1 (hfb x)).2
    have hy := (abs_le.1 (hfb y)).1
    simp only [NNReal.coe_one, one_mul] at hdist
    exact le_min (by linarith) (by linarith)
  simpa only [kantorovichDualValue_def, integral_neg, sub_eq_add_neg] using
    hfeas.ofReal_kantorovichDualValue_le_transportCost (hi μ) (hi ν).neg

omit [MeasurableSpace X] in
/-- Center the range of a conjugate potential of the truncated distance cost. -/
private theorem exists_boundedLipschitz_shift [Nonempty X] (hR : 0 ≤ R)
    {φ ψ : X → ℝ}
    (hfeas : ∀ x y, φ x + ψ y ≤ min (dist x y) (2 * R))
    (hφ : ∀ x, φ x = ⨅ y, (min (dist x y) (2 * R) - ψ y)) :
    ∃ (f : X → ℝ) (a : ℝ), LipschitzWith 1 f ∧ (∀ x, ‖f x‖ ≤ R) ∧
      ∀ x, f x = φ x - a := by
  have hbdd (x : X) : BddBelow (range fun y ↦ min (dist x y) (2 * R) - ψ y) :=
    ⟨φ x, forall_mem_range.2 fun y ↦ by linarith [hfeas x y]⟩
  have hosc (x x' : X) : φ x ≤ φ x' + 2 * R := by
    rw [← sub_le_iff_le_add, hφ x']
    refine le_ciInf fun y ↦ ?_
    have h := ciInf_le (hbdd x) y
    rw [← hφ x] at h
    linarith [min_le_right (dist x y) (2 * R),
      le_min (dist_nonneg (x := x') (y := y)) (by positivity : 0 ≤ 2 * R)]
  have hφlip : LipschitzWith 1 φ := LipschitzWith.of_le_add fun x x' ↦ by
    rw [← sub_le_iff_le_add, hφ x']
    refine le_ciInf fun y ↦ ?_
    have h := ciInf_le (hbdd x) y
    rw [← hφ x] at h
    have hlip := ((LipschitzWith.dist_left y).min_const (2 * R)).le_add_mul x x'
    simp only [NNReal.coe_one, one_mul] at hlip
    linarith
  obtain ⟨x₀⟩ := ‹Nonempty X›
  have hφbdd : BddBelow (range φ) :=
    ⟨φ x₀ - 2 * R, forall_mem_range.2 fun x ↦ by linarith [hosc x₀ x]⟩
  let m : ℝ := ⨅ x, φ x
  have hm (x : X) : m ≤ φ x := ciInf_le hφbdd x
  have hupper (x : X) : φ x ≤ m + 2 * R := by
    rw [← sub_le_iff_le_add]
    exact le_ciInf fun y ↦ by linarith [hosc x y]
  let f : X → ℝ := fun x ↦ φ x - (m + R)
  have hflip : LipschitzWith 1 f := LipschitzWith.of_le_add fun x y ↦ by
    have h := hφlip.le_add_mul x y
    simp only [NNReal.coe_one, one_mul] at h
    dsimp only [f]
    linarith
  refine ⟨f, m + R, hflip, fun x ↦ ?_, fun _ ↦ rfl⟩
  rw [Real.norm_eq_abs, abs_le]
  dsimp only [f]
  constructor <;> linarith [hm x, hupper x]

section Polish

variable [PolishSpace X] [BorelSpace X] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Transport with truncated distance admits a maximizing `1`-Lipschitz test function bounded
by half the cap. This holds for every pair of probability measures, including laws with infinite
first moment and the zero-cap case. -/
private theorem exists_boundedLipschitz_maximizer_probability
    (hR : 0 ≤ R) :
    ∃ f : X → ℝ, LipschitzWith 1 f ∧ (∀ x, ‖f x‖ ≤ R) ∧
      ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν) =
        transportCost (fun z : X × X ↦ ENNReal.ofReal (min (dist z.1 z.2) (2 * R))) μ ν := by
  have : Nonempty X := μ.nonempty_of_neZero
  let c : X × X → ℝ := fun z ↦ min (dist z.1 z.2) (2 * R)
  have hc : Continuous c := continuous_dist.min continuous_const
  have hc0 : ∀ z, 0 ≤ c z := fun z ↦ le_min dist_nonneg (by positivity)
  obtain ⟨π, φ, ψ, hcert, hφ, -⟩ := exists_isDualCertificate_of_continuous
    (μ := μ) (ν := ν) hc hc0 ⟨2 * R, forall_mem_range.2 fun _ ↦ min_le_right _ _⟩
  have hfeas := (dualFeasible_ofReal_iff hc0 φ ψ).1 hcert.dualFeasible
  obtain ⟨f, a, hf, hfb, hshift⟩ := exists_boundedLipschitz_shift hR hfeas hφ
  -- The shift makes the potential bounded, hence integrable against either marginal.
  have hfi (ρ : Measure X) [IsFiniteMeasure ρ] : Integrable f ρ :=
    .of_bound hf.continuous.aestronglyMeasurable R (ae_of_all _ hfb)
  have hφν : Integrable φ ν := by
    convert (hfi ν).add (integrable_const a) using 1
    ext x
    simp [hshift]
  have hψ : ∀ y, ψ y ≤ -φ y := fun y ↦ by
    have h := hfeas y y
    have hcy : c (y, y) = 0 := by simp [c, hR]
    rw [hcy] at h
    linarith
  -- Replacing the second potential by `-φ` improves the dual value.
  have hvalue : kantorovichDualValue μ ν φ ψ ≤ ∫ x, φ x ∂μ - ∫ x, φ x ∂ν := by
    have h := integral_mono hcert.integrable_right hφν.neg hψ
    simp only [Pi.neg_apply, integral_neg] at h
    rw [kantorovichDualValue_def]
    linarith
  have hint : ∫ x, f x ∂μ - ∫ x, f x ∂ν = ∫ x, φ x ∂μ - ∫ x, φ x ∂ν := by
    simp only [hshift, integral_sub hcert.integrable_left (integrable_const _),
      integral_sub hφν (integrable_const _), integral_const, probReal_univ, one_smul,
      sub_sub_sub_cancel_right]
  refine ⟨f, hf, hfb, le_antisymm
    (ofReal_integral_sub_integral_le_transportCost_truncated_dist hf hfb) ?_⟩
  rw [hint, hcert.transportCost_eq]
  exact ENNReal.ofReal_le_ofReal hvalue

end Polish

section PolishFinite

variable [PolishSpace X] [BorelSpace X] [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- Transport with truncated distance admits a maximizing `1`-Lipschitz test function bounded
by half the cap, for finite measures of equal mass. No first-moment assumption is needed, and
zero mass and the zero-cap case are included. -/
theorem exists_lipschitzWith_norm_le_integral_sub_integral_eq_transportCost_truncated_dist
    (hR : 0 ≤ R) (hmass : μ univ = ν univ) :
    ∃ f : X → ℝ, LipschitzWith 1 f ∧ (∀ x, ‖f x‖ ≤ R) ∧
      ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν) =
        transportCost (fun z : X × X ↦ ENNReal.ofReal (min (dist z.1 z.2) (2 * R))) μ ν := by
  by_cases hμ : μ = 0
  · have hν : ν = 0 := Measure.measure_univ_eq_zero.1 (hmass ▸ Measure.measure_univ_eq_zero.2 hμ)
    subst μ
    subst ν
    refine ⟨fun _ ↦ 0, (LipschitzWith.const _).weaken (by simp), fun _ ↦ by simpa using hR, ?_⟩
    have h := transportCost_le_lintegral isCoupling_zero
      (fun z : X × X ↦ ENNReal.ofReal (min (dist z.1 z.2) (2 * R)))
    have hcost : transportCost
        (fun z : X × X ↦ ENNReal.ofReal (min (dist z.1 z.2) (2 * R))) 0 0 = 0 :=
      le_antisymm (by simpa using h) zero_le
    simpa using hcost.symm
  have hμ0 : μ univ ≠ 0 := mt Measure.measure_univ_eq_zero.1 hμ
  have hμtop : μ univ ≠ ∞ := measure_ne_top _ _
  let μ' := (μ univ)⁻¹ • μ
  let ν' := (μ univ)⁻¹ • ν
  have : NeZero μ := ⟨hμ⟩
  have : IsProbabilityMeasure μ' := inferInstance
  have : IsProbabilityMeasure ν' := ⟨by
    simp only [ν', Measure.smul_apply, smul_eq_mul, ← hmass,
      ENNReal.inv_mul_cancel hμ0 hμtop]⟩
  obtain ⟨f, hf, hfb, heq⟩ :=
    exists_boundedLipschitz_maximizer_probability
      (μ := μ') (ν := ν') hR
  have hscale (ρ : Measure X) : μ univ • ((μ univ)⁻¹ • ρ) = ρ := by
    rw [smul_smul, ENNReal.mul_inv_cancel hμ0 hμtop, one_smul]
  have hint (ρ : Measure X) :
      ∫ x, f x ∂ρ = (μ univ).toReal * ∫ x, f x ∂((μ univ)⁻¹ • ρ) := by
    calc ∫ x, f x ∂ρ = ∫ x, f x ∂(μ univ • ((μ univ)⁻¹ • ρ)) :=
          congrArg (fun ρ ↦ ∫ x, f x ∂ρ) (hscale ρ).symm
      _ = _ := integral_smul_measure _ _
  refine ⟨f, hf, hfb, ?_⟩
  calc ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν)
      = μ univ * ENNReal.ofReal (∫ x, f x ∂μ' - ∫ x, f x ∂ν') := by
        rw [hint μ, hint ν, ← mul_sub, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal hμtop]
    _ = μ univ * transportCost
        (fun z : X × X ↦ ENNReal.ofReal (min (dist z.1 z.2) (2 * R))) μ' ν' := by rw [heq]
    _ = _ := by rw [← transportCost_smul hμtop, hscale μ, hscale ν]

/-- **Bounded-Lipschitz Kantorovich–Rubinstein duality with attainment.** The cost capped at
`2 * R` is the greatest difference of integrals of a `1`-Lipschitz function bounded by `R`,
for finite measures of equal mass. Both constraints are separate; this is the maximum-norm
convention, not their sum. -/
theorem isGreatest_ofReal_integral_sub_integral_boundedLipschitz (hR : 0 ≤ R)
    (hmass : μ univ = ν univ) :
    IsGreatest {r : ℝ≥0∞ | ∃ f : X → ℝ, LipschitzWith 1 f ∧ (∀ x, ‖f x‖ ≤ R) ∧
      ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν) = r}
      (transportCost (fun z : X × X ↦ ENNReal.ofReal (min (dist z.1 z.2) (2 * R))) μ ν) := by
  refine ⟨exists_lipschitzWith_norm_le_integral_sub_integral_eq_transportCost_truncated_dist
    hR hmass, ?_⟩
  rintro r ⟨f, hf, hfb, rfl⟩
  exact ofReal_integral_sub_integral_le_transportCost_truncated_dist hf hfb

/-- **Bounded-Lipschitz duality in supremum form.** A uniform bound `R` on the test functions
corresponds to truncation of the ground distance at `2 * R`, for finite measures of equal mass. -/
theorem transportCost_truncated_dist_eq_iSup (hR : 0 ≤ R) (hmass : μ univ = ν univ) :
    transportCost (fun z : X × X ↦ ENNReal.ofReal (min (dist z.1 z.2) (2 * R))) μ ν =
      ⨆ (f : X → ℝ) (_ : LipschitzWith 1 f) (_ : ∀ x, ‖f x‖ ≤ R),
        ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν) := by
  obtain ⟨f, hf, hfb, heq⟩ :=
    exists_lipschitzWith_norm_le_integral_sub_integral_eq_transportCost_truncated_dist
      (μ := μ) (ν := ν) hR hmass
  refine le_antisymm ?_ (iSup_le fun g ↦ iSup_le fun hg ↦ iSup_le fun hgb ↦
    ofReal_integral_sub_integral_le_transportCost_truncated_dist hg hgb)
  rw [← heq]
  exact le_iSup_of_le f (le_iSup_of_le hf (le_iSup_of_le hfb le_rfl))

/-- The absolute-difference form of bounded-Lipschitz duality for finite measures of equal mass.
The test class is closed under negation, so its signed and absolute suprema coincide. -/
theorem transportCost_truncated_dist_eq_iSup_abs (hR : 0 ≤ R) (hmass : μ univ = ν univ) :
    transportCost (fun z : X × X ↦ ENNReal.ofReal (min (dist z.1 z.2) (2 * R))) μ ν =
      ⨆ (f : X → ℝ) (_ : LipschitzWith 1 f) (_ : ∀ x, ‖f x‖ ≤ R),
        ENNReal.ofReal |∫ x, f x ∂μ - ∫ x, f x ∂ν| := by
  refine le_antisymm ?_ ?_
  · rw [transportCost_truncated_dist_eq_iSup hR hmass]
    exact iSup_mono fun f ↦ iSup_mono fun _ ↦ iSup_mono fun _ ↦
      ENNReal.ofReal_le_ofReal (le_abs_self _)
  · refine iSup_le fun f ↦ iSup_le fun hf ↦ iSup_le fun hfb ↦ ?_
    have hpos := ofReal_integral_sub_integral_le_transportCost_truncated_dist
      (μ := μ) (ν := ν) hf hfb
    have hneg := ofReal_integral_sub_integral_le_transportCost_truncated_dist
      (μ := μ) (ν := ν) hf.neg (fun x ↦ by simpa using hfb x)
    simp only [Pi.neg_apply, integral_neg] at hneg
    rw [abs_sub_comm]
    rcases le_total (∫ x, f x ∂μ) (∫ x, f x ∂ν) with h | h
    · rw [abs_of_nonneg (sub_nonneg.2 h)]
      convert hneg using 1
      congr 1
      ring
    · rw [abs_of_nonpos (sub_nonpos.2 h)]
      convert hpos using 1
      congr 1
      ring

end PolishFinite

end BoundedLipschitz

end TauCeti
