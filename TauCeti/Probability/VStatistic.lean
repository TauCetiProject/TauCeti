/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5

Staged for Tau Ceti, roadmap topic T14.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track — additions to `Mathlib/Probability/`.

Formalized by Claude Opus 5 (claude-opus-5[1m]).
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.ProductMeasure

/-! # Two-coordinate marginals of a product measure, and the mean of a V-statistic

Under a product measure the pair of two *distinct* coordinates has the product law.  That is
`map_evalPair_pi`, and it is the reason the expectation of a double average splits into its
off-diagonal and diagonal parts:

  `∫ ∑ᵢ ∑ⱼ f (ω i) (ω j) = n (n - 1) ∫∫ f + n ∫ f x x`.

A double average of this shape — a *V-statistic of order two* — is not covered by the law of
large numbers, since the summands share coordinates, and the classical routes (Hoeffding's
decomposition, or Varadarajan's theorem on almost-sure weak convergence of empirical measures)
are both absent from Mathlib.  The identity above is where an elementary second-moment proof of
the weak law would start.

Both statements are ordinary facts about product measures and are stated for their own sake;
neither is currently consumed by a paper-facing theorem in this repository.
-/

public section

namespace TauCeti

open MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι] {α : Type*} [MeasurableSpace α]

/-- Under a product of probability measures, two **distinct** coordinates are jointly
distributed as the product measure. -/
theorem map_evalPair_pi (P : Measure α) [IsProbabilityMeasure P] {i j : ι} (hij : i ≠ j) :
    (Measure.pi (fun _ : ι => P)).map (fun ω : ι → α => (ω i, ω j)) = P.prod P := by
  have hindep : IndepFun (fun ω : ι → α => ω i) (fun ω : ι → α => ω j)
      (Measure.pi (fun _ : ι => P)) :=
    (iIndepFun_pi (X := fun _ : ι => (id : α → α)) fun _ => aemeasurable_id).indepFun hij
  have hmap : ∀ k : ι,
      (Measure.pi (fun _ : ι => P)).map (fun ω : ι → α => ω k) = P :=
    fun k => (measurePreserving_eval (fun _ : ι => P) k).map_eq
  rw [(indepFun_iff_map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable).mp hindep,
    hmap i, hmap j]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [Fintype ι] in
/-- Integrating a function of two distinct coordinates is integrating against the product
measure. -/
theorem integral_evalPair_pi [Fintype ι] (P : Measure α) [IsProbabilityMeasure P]
    {i j : ι} (hij : i ≠ j) {f : α × α → E} (hf : AEStronglyMeasurable f (P.prod P)) :
    ∫ ω, f (ω i, ω j) ∂(Measure.pi (fun _ : ι => P)) = ∫ q, f q ∂(P.prod P) := by
  rw [← map_evalPair_pi (ι := ι) P hij,
    integral_map ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
      (by rwa [map_evalPair_pi (ι := ι) P hij])]

omit [Fintype ι] [NormedSpace ℝ E] in
/-- A function of two distinct coordinates is integrable exactly when it is integrable against
the product measure. -/
theorem integrable_evalPair_pi [Fintype ι] (P : Measure α) [IsProbabilityMeasure P]
    {i j : ι} (hij : i ≠ j) {f : α × α → E} (hf : Integrable f (P.prod P)) :
    Integrable (fun ω : ι → α => f (ω i, ω j)) (Measure.pi (fun _ : ι => P)) := by
  have hf' : Integrable f
      ((Measure.pi (fun _ : ι => P)).map (fun ω : ι → α => (ω i, ω j))) := by
    rwa [map_evalPair_pi (ι := ι) P hij]
  exact (integrable_map_measure hf'.aestronglyMeasurable
    ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable).mp hf'

/-- Integrating a function of a single coordinate is integrating against the base measure. -/
theorem integral_eval_pi (P : Measure α) [IsProbabilityMeasure P] (i : ι) {g : α → E}
    (hg : AEStronglyMeasurable g P) :
    ∫ ω, g (ω i) ∂(Measure.pi (fun _ : ι => P)) = ∫ x, g x ∂P := by
  have hmap := (measurePreserving_eval (fun _ : ι => P) i).map_eq
  have hg' : AEStronglyMeasurable g
      ((Measure.pi (fun _ : ι => P)).map (fun ω : ι → α => ω i)) := by rwa [hmap]
  conv_rhs => rw [← hmap]
  rw [integral_map (measurable_pi_apply i).aemeasurable hg']

omit [Fintype ι] [NormedSpace ℝ E] in
/-- A function of a single coordinate is integrable exactly when it is integrable against the
base measure. -/
theorem integrable_eval_pi [Fintype ι] (P : Measure α) [IsProbabilityMeasure P] (i : ι) {g : α → E}
    (hg : Integrable g P) :
    Integrable (fun ω : ι → α => g (ω i)) (Measure.pi (fun _ : ι => P)) := by
  have hmap := (measurePreserving_eval (fun _ : ι => P) i).map_eq
  have hg' : Integrable g ((Measure.pi (fun _ : ι => P)).map (fun ω : ι → α => ω i)) := by
    rwa [hmap]
  exact (integrable_map_measure hg'.aestronglyMeasurable
    (measurable_pi_apply i).aemeasurable).mp hg'

/--
**The mean of a V-statistic of order two.**

Under a product of `n` copies of `P`, the double sum splits into `n (n - 1)` off-diagonal terms,
each distributed as the product measure, and `n` diagonal terms, each distributed as `P`.
-/
theorem integral_doubleSum_pi {n : ℕ} (P : Measure α) [IsProbabilityMeasure P]
    {f : α → α → ℝ} (hf : Integrable (Function.uncurry f) (P.prod P))
    (hdiag : Integrable (fun x => f x x) P) :
    ∫ ω, (∑ i : Fin n, ∑ j : Fin n, f (ω i) (ω j))
        ∂(Measure.pi (fun _ : Fin n => P))
      = ((n : ℝ) * ((n : ℝ) - 1)) * (∫ q, Function.uncurry f q ∂(P.prod P))
        + (n : ℝ) * ∫ x, f x x ∂P := by
  classical
  set A : ℝ := ∫ x, f x x ∂P with hA
  set B : ℝ := ∫ q, Function.uncurry f q ∂(P.prod P) with hB
  have hterm : ∀ i j : Fin n,
      Integrable (fun ω : Fin n → α => f (ω i) (ω j)) (Measure.pi (fun _ : Fin n => P)) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      exact integrable_eval_pi (ι := Fin n) P i hdiag
    · exact integrable_evalPair_pi (ι := Fin n) P hij hf
  have hval : ∀ i j : Fin n,
      ∫ ω, f (ω i) (ω j) ∂(Measure.pi (fun _ : Fin n => P))
        = if i = j then A else B := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [hA]
      exact integral_eval_pi (ι := Fin n) P i hdiag.aestronglyMeasurable
    · simp only [hij, reduceIte, hB]
      exact integral_evalPair_pi (ι := Fin n) P hij hf.aestronglyMeasurable
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hterm i j)]
  have hstep : ∀ i : Fin n,
      ∫ ω, (∑ j : Fin n, f (ω i) (ω j)) ∂(Measure.pi (fun _ : Fin n => P))
        = ((n : ℝ) - 1) * B + A := by
    intro i
    rw [integral_finsetSum _ (fun j _ => hterm i j)]
    have hsplit : ∀ j : Fin n,
        (∫ ω, f (ω i) (ω j) ∂(Measure.pi (fun _ : Fin n => P)))
          = B + (if i = j then A - B else 0) := by
      intro j
      rw [hval i j]
      by_cases h : i = j <;> simp [h]
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Finset.sum_ite_eq Finset.univ i (fun _ => A - B)]
    simp only [Finset.mem_univ, reduceIte, nsmul_eq_mul]
    ring
  simp_rw [hstep]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-! ### Exchanging an almost-everywhere quantifier with a parameter

A limit theorem proved "for each parameter, almost surely" gives a null set that depends on the
parameter.  A conclusion phrased "almost surely, for almost every parameter" needs the opposite
order, and the exchange is Fubini: the failure set has null sections in one direction, hence null
product measure, hence null sections in the other.

The exchange needs the failure set to be measurable in the product, which is a genuine
obligation, not bookkeeping -- for a non-measurable set the two orders can disagree. -/

/--
**Exchanging an almost-everywhere quantifier with a parameter.**

If for every parameter the property holds almost surely, and the set where it holds is
measurable in the product, then almost surely it holds for almost every parameter.
-/
theorem ae_ae_of_forall_ae {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [SFinite μ] (P : Measure X) [SFinite P]
    {s : Set (Ω × X)} (hs : MeasurableSet s)
    (h : ∀ x : X, ∀ᵐ ω ∂μ, (ω, x) ∈ s) :
    ∀ᵐ ω ∂μ, ∀ᵐ x ∂P, (ω, x) ∈ s := by
  classical
  -- the failure set has null sections in the parameter direction
  have hswap : MeasurableSet (Prod.swap ⁻¹' sᶜ : Set (X × Ω)) :=
    (hs.compl).preimage measurable_swap
  have hsect : ∀ x : X, μ (Prod.mk x ⁻¹' (Prod.swap ⁻¹' sᶜ : Set (X × Ω))) = 0 := by
    intro x
    have := h x
    rw [Filter.Eventually, mem_ae_iff] at this
    refine measure_mono_null (fun ω hω => ?_) this
    simpa using hω
  have hnull : (P.prod μ) (Prod.swap ⁻¹' sᶜ : Set (X × Ω)) = 0 :=
    Measure.measure_prod_null_of_ae_null hswap
      (Filter.Eventually.of_forall fun x => hsect x)
  -- transport across the swap and read the sections in the other direction
  have hmapnull : (μ.prod P) (sᶜ) = 0 := by
    have hmap : (P.prod μ).map Prod.swap = μ.prod P := Measure.prod_swap
    rw [← hmap, Measure.map_apply measurable_swap hs.compl]
    exact hnull
  have hae : ∀ᵐ z ∂(μ.prod P), z ∈ s := by
    rw [Filter.Eventually, mem_ae_iff]
    simpa using hmapnull
  exact Measure.ae_ae_of_ae_prod hae

/-! ### One coordinate of an infinite product, alongside an independent parameter

The finite-product statements above have an infinite-product counterpart that is what a growing
reference collection actually needs: the collection is a point of `ι → β` drawn from a product
measure, a query is an independent point of `α`, and a statistic evaluated at the `i`-th member
of the collection sees only the pair `(query, i-th member)`.  That pair has the same law for
every `i`, which is why a per-member expectation cannot depend on the member.
-/

/--
**A query and one member of an independently drawn collection have the product law.**

The map `(x, φ) ↦ (x, φ i)` pushes `μ ⊗ ⨂ P` forward to `μ ⊗ P`, for every index `i`.
-/
theorem map_prodMk_eval_infinitePi {ι α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (P : Measure β) [IsProbabilityMeasure P] (i : ι) :
    (μ.prod (Measure.infinitePi fun _ : ι => P)).map (fun z : α × (ι → β) => (z.1, z.2 i))
      = μ.prod P :=
  ((MeasurePreserving.id μ).prod (measurePreserving_eval_infinitePi (fun _ : ι => P) i)).map_eq

/--
**A statistic of a query and one member of the collection integrates against the product
measure**, with the same value for every member.
-/
theorem integral_prodMk_eval_infinitePi {ι α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (P : Measure β) [IsProbabilityMeasure P] (i : ι)
    {f : α × β → E} (hf : AEStronglyMeasurable f (μ.prod P)) :
    ∫ z, f (z.1, z.2 i) ∂(μ.prod (Measure.infinitePi fun _ : ι => P)) = ∫ q, f q ∂(μ.prod P) := by
  have hg : Measurable fun z : α × (ι → β) => (z.1, z.2 i) :=
    measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)
  rw [← map_prodMk_eval_infinitePi (ι := ι) μ P i,
    integral_map hg.aemeasurable (by rwa [map_prodMk_eval_infinitePi (ι := ι) μ P i])]

end TauCeti
