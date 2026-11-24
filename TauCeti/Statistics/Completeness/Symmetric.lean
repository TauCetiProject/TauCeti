/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import TauCeti.Statistics.Completeness.Basic
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import TauCeti.GroupTheory.Perm.Fin
import TauCeti.MeasureTheory.Constructions.Pi
import TauCeti.MeasureTheory.Integral.Pi
import TauCeti.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Convex

/-!
# Completeness of symmetric statistics

Let `C` be a set of probability laws on `X` that is closed under binary mixtures and for which the
identity statistic is complete. In the `n`-sample model `{Pⁿ | P ∈ C}`, the order of the
observations carries no information, and the symmetric statistics are complete: a measurable
function `g` of `n` observations that is invariant under every permutation of the observations and
is integrable with mean `0` under every `Pⁿ`, `P ∈ C`, vanishes `Pⁿ`-almost everywhere for every
`P ∈ C`. This is the nonparametric completeness behind the optimality of U-statistics: two
symmetric unbiased estimators of the same quantity agree almost everywhere in such a model.

The hypothesis of closure under mixtures cannot be dropped: for the Gaussian location family
`{N(θ, 1)}` the symmetric function `(x₀ - x₁)² - 2` has mean `0` under every `N(θ, 1)²` without
vanishing.

## Main results

* `TauCeti.ae_eq_zero_pi_of_isCompleteStatistic_of_convex`: completeness of symmetric statistics.

## Implementation notes

The proof follows Pfanzagl.

* For laws `Q₀, …, Qₙ₋₁ ∈ C` and a nonempty set `s` of indices, the uniform mixture of the `Qᵢ`,
  `i ∈ s`, lies in `C`. Expanding the `n`-th power of this mixture multilinearly
  (`MeasureTheory.Measure.pi_finsetSum`) shows that the integrals of `g` against the products
  `Q_{f 0} ⊗ ⋯ ⊗ Q_{f (n - 1)}` sum to `0` over the maps `f` with values in `s`.
* Inclusion–exclusion over `s` (`Finset.inclusion_exclusion_sum_inf_compl`) isolates the
  surjective maps `f`, which are permutations; by symmetry each of them contributes the integral of
  `g` against `Q₀ ⊗ ⋯ ⊗ Qₙ₋₁`, which therefore vanishes.
* Completeness is then applied one coordinate at a time, by induction on `n`: integrating out all
  coordinates but the first shows that the integral of `g` over `A ×ˢ (Fin n → X)` against
  `P ⊗ Qⁿ` vanishes, so the function of the other coordinates obtained by integrating the first
  over `A` against `P` is symmetric of mean `0`, hence `0` by induction. The integrals of `g` over
  all rectangles then vanish, and so does `g`.

## References

* J. Pfanzagl, *Parametric Statistical Theory*, de Gruyter (1994), Definition 1.5.4 and
  Theorem 1.5.10.
-/

public section

open MeasureTheory Finset

open scoped ENNReal NNReal

namespace TauCeti

variable {X : Type*} [MeasurableSpace X] {C : Set (ProbabilityMeasure X)} {n : ℕ}

/-- **Expansion step.** If the uniform mixture of the `Q i`, `i ∈ s`, is in `C`, then `g` is
integrable against each product `Q_{f 0} ⊗ ⋯ ⊗ Q_{f (n - 1)}` with `f` taking values in `s`, and
these integrals sum to `0`. -/
private lemma integrable_and_sum_integral_eq_zero {g : (Fin n → X) → ℝ}
    (hint : ∀ P ∈ C, Integrable g (Measure.pi fun _ : Fin n ↦ (P : Measure X)) ∧
      ∫ x, g x ∂(Measure.pi fun _ : Fin n ↦ (P : Measure X)) = 0)
    {Q : Fin n → ProbabilityMeasure X} {s : Finset (Fin n)} (hs : s.Nonempty)
    {R : ProbabilityMeasure X} (hRC : R ∈ C)
    (hR : (R : Measure X) = (#s : ℝ≥0)⁻¹ • ∑ i ∈ s, (Q i : Measure X)) :
    (∀ f ∈ Fintype.piFinset fun _ ↦ s,
      Integrable g (Measure.pi fun k ↦ (Q (f k) : Measure X))) ∧
    ∑ f ∈ Fintype.piFinset (fun _ ↦ s), ∫ x, g x ∂Measure.pi (fun k ↦ (Q (f k) : Measure X)) =
      0 := by
  have hc : (#s : ℝ≥0)⁻¹ ^ n ≠ 0 := by simp [hs.ne_empty]
  -- Expand the `n`-th power of the uniform mixture `R` multilinearly.
  have hpi : Measure.pi (fun _ : Fin n ↦ (R : Measure X)) =
      ((#s : ℝ≥0)⁻¹ ^ n) • ∑ f ∈ Fintype.piFinset fun _ ↦ s,
        Measure.pi fun k ↦ (Q (f k) : Measure X) := by
    simp_rw [hR]
    rw [Measure.pi_smul (fun _ ↦ (#s : ℝ≥0)⁻¹) (fun _ ↦ ∑ i ∈ s, (Q i : Measure X)), prod_const,
      card_univ, Fintype.card_fin, Measure.pi_finsetSum (fun _ ↦ s) fun _ i ↦ (Q i : Measure X)]
  obtain ⟨hgi, hg0⟩ := hint R hRC
  rw [hpi] at hgi hg0
  rw [ENNReal.smul_def, integrable_smul_measure (by simpa using hc) ENNReal.coe_ne_top,
    integrable_finsetSum_measure] at hgi
  refine ⟨hgi, ?_⟩
  rw [integral_smul_nnreal_measure, integral_finsetSum_measure hgi] at hg0
  exact (smul_eq_zero.mp hg0).resolve_left hc

/-- **Distinct factors.** For laws `Q₀, …, Qₙ₋₁ ∈ C`, a symmetric `g` with mean `0` under every
`Pⁿ`, `P ∈ C`, is integrable with mean `0` under `Q₀ ⊗ ⋯ ⊗ Qₙ₋₁`. -/
private lemma integrable_and_integral_pi_eq_zero [NeZero n]
    (hconv : ∀ P ∈ C, ∀ Q ∈ C, ∀ a : ℝ≥0, a ≤ 1 →
      ∃ R ∈ C, (R : Measure X) = (a : ℝ≥0∞) • (P : Measure X) +
        ((1 - a : ℝ≥0) : ℝ≥0∞) • (Q : Measure X))
    {g : (Fin n → X) → ℝ} (hsym : ∀ (σ : Equiv.Perm (Fin n)) x, g (x ∘ σ) = g x)
    (hint : ∀ P ∈ C, Integrable g (Measure.pi fun _ : Fin n ↦ (P : Measure X)) ∧
      ∫ x, g x ∂(Measure.pi fun _ : Fin n ↦ (P : Measure X)) = 0)
    {Q : Fin n → ProbabilityMeasure X} (hQ : ∀ i, Q i ∈ C) :
    Integrable g (Measure.pi fun k ↦ (Q k : Measure X)) ∧
      ∫ x, g x ∂Measure.pi (fun k ↦ (Q k : Measure X)) = 0 := by
  classical
  have hexp (s : Finset (Fin n)) (hs : s.Nonempty) :
      (∀ f ∈ Fintype.piFinset fun _ ↦ s,
        Integrable g (Measure.pi fun k ↦ (Q (f k) : Measure X))) ∧
      ∑ f ∈ Fintype.piFinset (fun _ ↦ s),
        ∫ x, g x ∂Measure.pi (fun k ↦ (Q (f k) : Measure X)) = 0 := by
    obtain ⟨R, hRC, hR⟩ := MeasureTheory.exists_mem_eq_smul_sum hconv (fun i _ ↦ hQ i) hs
    exact integrable_and_sum_integral_eq_zero hint hs hRC hR
  set I : (Fin n → Fin n) → ℝ := fun f ↦ ∫ x, g x ∂Measure.pi (fun k ↦ (Q (f k) : Measure X))
  refine ⟨(hexp univ univ_nonempty).1 id (by simp), ?_⟩
  -- By symmetry, every surjective, hence bijective, `f` contributes `I id`.
  have hperm (f : Fin n → Fin n) (hf : f.Surjective) : I f = I id :=
    integral_pi_comp_perm (fun k ↦ (Q k : Measure X))
      (Equiv.ofBijective f ⟨Finite.injective_iff_surjective.mpr hf, hf⟩) (hsym _)
  -- Inclusion–exclusion over the sets of values that `f` avoids.
  let S (i : Fin n) : Finset (Fin n → Fin n) := univ.filter fun f ↦ ∀ k, f k ≠ i
  have hie := inclusion_exclusion_sum_inf_compl univ S I
  have hinf : univ.inf (fun i ↦ (S i)ᶜ) = univ.filter Function.Surjective := by
    ext f
    simp [S, Function.Surjective, mem_inf]
  have hterm (t : Finset (Fin n)) : ∑ f ∈ t.inf S, I f = 0 := by
    have ht : t.inf S = Fintype.piFinset fun _ ↦ tᶜ := by
      ext f
      simp only [S, mem_inf, mem_filter, mem_univ, true_and, Fintype.mem_piFinset, mem_compl]
      grind
    rw [ht]
    rcases tᶜ.eq_empty_or_nonempty with h | h
    · simp [h]
    · exact (hexp _ h).2
  rw [hinf, sum_congr rfl fun f hf ↦ hperm f (mem_filter.mp hf).2, sum_const] at hie
  simp only [hterm, smul_zero, sum_const_zero] at hie
  refine (smul_eq_zero.mp hie).resolve_left ?_
  exact card_ne_zero.mpr ⟨id, by simp [Function.surjective_id]⟩

/-- **Two laws.** For `R, Q ∈ C`, a symmetric `g` of `n + 1` observations with mean `0` under every
`Pⁿ⁺¹`, `P ∈ C`, composed with `Fin.cons`, is integrable with mean `0` under `R ⊗ Qⁿ`. -/
private lemma integrable_and_integral_prod_eq_zero
    (hconv : ∀ P ∈ C, ∀ Q ∈ C, ∀ a : ℝ≥0, a ≤ 1 →
      ∃ R ∈ C, (R : Measure X) = (a : ℝ≥0∞) • (P : Measure X) +
        ((1 - a : ℝ≥0) : ℝ≥0∞) • (Q : Measure X))
    {g : (Fin (n + 1) → X) → ℝ} (hgm : Measurable g)
    (hsym : ∀ (σ : Equiv.Perm (Fin (n + 1))) x, g (x ∘ σ) = g x)
    (hint : ∀ P ∈ C, Integrable g (Measure.pi fun _ : Fin (n + 1) ↦ (P : Measure X)) ∧
      ∫ x, g x ∂(Measure.pi fun _ : Fin (n + 1) ↦ (P : Measure X)) = 0)
    {R Q : ProbabilityMeasure X} (hR : R ∈ C) (hQ : Q ∈ C) :
    Integrable (fun p : X × (Fin n → X) ↦ g (Fin.cons p.1 p.2))
        ((R : Measure X).prod (Measure.pi fun _ ↦ (Q : Measure X))) ∧
      ∫ p : X × (Fin n → X), g (Fin.cons p.1 p.2)
        ∂(R : Measure X).prod (Measure.pi fun _ ↦ (Q : Measure X)) = 0 := by
  have hmp := Measure.measurePreserving_finCons (R : Measure X) fun _ : Fin n ↦ (Q : Measure X)
  have hT : (Fin.cons (R : Measure X) fun _ ↦ (Q : Measure X) : Fin (n + 1) → Measure X) =
      fun k ↦ ((Fin.cons R fun _ ↦ Q : Fin (n + 1) → ProbabilityMeasure X) k : Measure X) := by
    funext k
    cases k using Fin.cases <;> simp
  rw [hT] at hmp
  obtain ⟨hi, h0⟩ := integrable_and_integral_pi_eq_zero hconv hsym hint
    (Q := Fin.cons R fun _ ↦ Q) fun k ↦ by cases k using Fin.cases <;> simp [hR, hQ]
  refine ⟨hmp.integrable_comp_of_integrable hi, ?_⟩
  rw [← h0, ← hmp.map_eq, integral_map hmp.measurable.aemeasurable hgm.aestronglyMeasurable]

/-- **Induction step.** Completeness of symmetric statistics of `n` observations gives it for
`n + 1` observations: completeness of the identity removes the first coordinate. -/
private lemma ae_eq_zero_pi_succ
    (hc : IsCompleteStatistic (fun P : C ↦ ((P : ProbabilityMeasure X) : Measure X)) id)
    (hconv : ∀ P ∈ C, ∀ Q ∈ C, ∀ a : ℝ≥0, a ≤ 1 →
      ∃ R ∈ C, (R : Measure X) = (a : ℝ≥0∞) • (P : Measure X) +
        ((1 - a : ℝ≥0) : ℝ≥0∞) • (Q : Measure X))
    {g : (Fin (n + 1) → X) → ℝ} (hgm : Measurable g)
    (hsym : ∀ (σ : Equiv.Perm (Fin (n + 1))) x, g (x ∘ σ) = g x)
    (hint : ∀ P ∈ C, Integrable g (Measure.pi fun _ : Fin (n + 1) ↦ (P : Measure X)) ∧
      ∫ x, g x ∂(Measure.pi fun _ : Fin (n + 1) ↦ (P : Measure X)) = 0)
    {P : ProbabilityMeasure X} (hP : P ∈ C)
    (ih : ∀ g' : (Fin n → X) → ℝ, Measurable g' →
      (∀ (σ : Equiv.Perm (Fin n)) x, g' (x ∘ σ) = g' x) →
      (∀ Q ∈ C, Integrable g' (Measure.pi fun _ : Fin n ↦ (Q : Measure X)) ∧
        ∫ x, g' x ∂(Measure.pi fun _ : Fin n ↦ (Q : Measure X)) = 0) →
      g' =ᵐ[Measure.pi fun _ : Fin n ↦ (P : Measure X)] 0) :
    g =ᵐ[Measure.pi fun _ : Fin (n + 1) ↦ (P : Measure X)] 0 := by
  set G : X × (Fin n → X) → ℝ := fun p ↦ g (Fin.cons p.1 p.2)
  have hGm : Measurable G := hgm.comp_finCons
  have hprod {R Q : ProbabilityMeasure X} (hR : R ∈ C) (hQ : Q ∈ C) :=
    integrable_and_integral_prod_eq_zero hconv hgm hsym hint hR hQ
  -- For a set `A`, integrating the first coordinate over `A` against `P` gives a
  -- symmetric function of the other `n` coordinates, which vanishes by the induction hypothesis.
  have hsection (A : Set X) :
      (fun y ↦ ∫ x in A, G (x, y) ∂(P : Measure X)) =ᵐ[Measure.pi fun _ ↦ (P : Measure X)] 0 := by
    refine ih _
      (hGm.stronglyMeasurable.integral_prod_left' (μ := (P : Measure X).restrict A)).measurable
      (fun σ y ↦ ?_) fun Q hQ ↦ ?_
    · simp only [G, Fin.cons_comp_perm, hsym]
    have hGA :
        Integrable G (((P : Measure X).restrict A).prod (Measure.pi fun _ ↦ (Q : Measure X))) := by
      rw [← Measure.restrict_univ (μ := Measure.pi fun _ ↦ (Q : Measure X)), Measure.prod_restrict]
      exact (hprod hP hQ).1.restrict
    refine ⟨hGA.integral_prod_right, ?_⟩
    rw [← integral_prod_symm G hGA, integral_prod G hGA]
    -- The integral over the last `n` coordinates has mean `0` under every `R ∈ C`, hence vanishes.
    have hzero : ∀ᵐ x ∂(P : Measure X), ∫ y, G (x, y) ∂(Measure.pi fun _ ↦ (Q : Measure X)) = 0 :=
      hc.ae_eq_zero (g := fun x ↦ ∫ y, G (x, y) ∂(Measure.pi fun _ ↦ (Q : Measure X)))
        (hGm.stronglyMeasurable.integral_prod_right'
          (ν := Measure.pi fun _ ↦ (Q : Measure X))).measurable
        (fun R ↦ (hprod R.property hQ).1.integral_prod_left)
        (fun R ↦ (integral_prod G (hprod R.property hQ).1).symm.trans (hprod R.property hQ).2)
        ⟨P, hP⟩
    exact integral_eq_zero_of_ae (ae_restrict_of_ae hzero)
  -- Hence `G` has integral `0` over every measurable rectangle, so it vanishes almost everywhere.
  have hGi := (hprod hP hP).1
  have hG0 : G =ᵐ[(P : Measure X).prod (Measure.pi fun _ ↦ (P : Measure X))] 0 := by
    refine hGi.ae_eq_zero_of_forall_setIntegral_eq_zero fun u hu _ ↦
      setIntegral_eq_zero_of_forall_prod hGi (fun A _ B _ ↦ ?_) u hu
    have hAB := Measure.prod_restrict (μ := (P : Measure X))
      (ν := Measure.pi fun _ : Fin n ↦ (P : Measure X)) A B
    rw [← hAB, integral_prod_symm G (hGi.mono_measure (hAB ▸ Measure.restrict_le_self))]
    exact integral_eq_zero_of_ae (ae_restrict_of_ae (hsection A))
  have hmp := Measure.measurePreserving_finCons (P : Measure X) fun _ : Fin n ↦ (P : Measure X)
  have hT : (Fin.cons (P : Measure X) fun _ ↦ (P : Measure X) : Fin (n + 1) → Measure X) =
      fun _ ↦ (P : Measure X) := by
    funext k
    cases k using Fin.cases <;> simp
  rw [hT] at hmp
  rw [← hmp.map_eq, Filter.EventuallyEq,
    ae_map_iff hmp.measurable.aemeasurable (measurableSet_eq_fun hgm measurable_zero)]
  exact hG0

/-- **Completeness of symmetric statistics.** Let `C` be a set of probability laws on `X` that is
closed under binary mixtures and for which the identity statistic is complete. If a measurable
function `g` of `n` observations is invariant under every permutation of the observations and is
integrable with mean `0` under the product law `Pⁿ` of every `P ∈ C`, then `g` vanishes
`Pⁿ`-almost everywhere for every `P ∈ C`. -/
theorem ae_eq_zero_pi_of_isCompleteStatistic_of_convex
    (hc : IsCompleteStatistic (fun P : C ↦ ((P : ProbabilityMeasure X) : Measure X)) id)
    (hconv : ∀ P ∈ C, ∀ Q ∈ C, ∀ a : ℝ≥0, a ≤ 1 →
      ∃ R ∈ C, (R : Measure X) = (a : ℝ≥0∞) • (P : Measure X) +
        ((1 - a : ℝ≥0) : ℝ≥0∞) • (Q : Measure X))
    {g : (Fin n → X) → ℝ} (hgm : Measurable g)
    (hsym : ∀ (σ : Equiv.Perm (Fin n)) x, g (x ∘ σ) = g x)
    (hint : ∀ P ∈ C, Integrable g (Measure.pi fun _ : Fin n ↦ (P : Measure X)) ∧
      ∫ x, g x ∂(Measure.pi fun _ : Fin n ↦ (P : Measure X)) = 0)
    {P : ProbabilityMeasure X} (hP : P ∈ C) :
    g =ᵐ[Measure.pi fun _ : Fin n ↦ (P : Measure X)] 0 := by
  induction n with
  | zero =>
    -- With no observations, `g` is a constant, which is its own mean.
    refine ae_of_all _ fun x ↦ ?_
    have h0 := (hint P hP).2
    rwa [show g = fun _ ↦ g x from funext fun y ↦ congrArg g (Subsingleton.elim y x),
      integral_const, probReal_univ, one_smul] at h0
  | succ n ih => exact ae_eq_zero_pi_succ hc hconv hgm hsym hint hP fun g' hg' ↦ ih hg'

end TauCeti
