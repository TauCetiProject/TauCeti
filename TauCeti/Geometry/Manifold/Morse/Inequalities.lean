/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Ring.Finset
public import TauCeti.AlgebraicTopology.Singular.Empty
public import TauCeti.AlgebraicTopology.Singular.Sublevel
public import TauCeti.AlgebraicTopology.Singular.Triple.Finrank
public import TauCeti.Geometry.Manifold.Morse.Cell.Homology
public import TauCeti.Geometry.Manifold.Morse.Deformation.Homology
import TauCeti.Algebra.BigOperators.AlternatingSum

/-!
# The Morse inequalities

Let `f` be a Morse function on a boundaryless finite-dimensional manifold `M`, let `V` be a
finite-dimensional module over a division ring `k`, and write `M_a = {f ≤ a}`. Let `a ≤ b` be
values of `f` at no critical point, with compact band `f⁻¹[a, b]`. Write
`bᵢ = dim Hᵢ(M_b, M_a; V)` for the dimensions of relative singular homology, and `cᵢ` for the
number of critical points of index `i` with value in `(a, b]`. Then, for every `n`:

* `Hₙ(M_b, M_a; V)` is finite-dimensional, and `bₙ ≤ cₙ dim V` (the weak Morse inequalities);
* `bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ (cₙ - cₙ₋₁ + ⋯ ± c₀) dim V` (the strong Morse inequalities);
* if `n ≥ dim M`, then `∑ᵢ₌₀ⁿ (-1)ⁱ bᵢ = (∑ᵢ₌₀ⁿ (-1)ⁱ cᵢ) dim V` (Euler's equality);
* if `n ≥ dim M`, then `∑ᵢ₌₀ⁿ cᵢ dim V · tⁱ = ∑ᵢ₌₀ⁿ bᵢ tⁱ + (1 + t) Q(t)` for a polynomial `Q` with
  natural number coefficients, the coefficient of `tⁱ` being the gap in the `i`-th strong
  inequality (the Morse polynomial identity);
* `b₀ + ⋯ + bₙ` is at most `dim V` times the number of critical points with values in `(a, b]`;
* if no two of these critical points have indices differing by one, then `bₙ = cₙ dim V` (the
  lacunary principle).

The band `W = f⁻¹[a, b]` is then a compact cobordism from the level `f⁻¹(a)` to the level
`f⁻¹(b)`, and the inclusion of pairs `(W, f⁻¹(a)) ⟶ (M_b, M_a)` induces isomorphisms on relative
homology (`TauCeti.isIso_singularHomologyMap_bandPairInclusion`). So the finiteness, the weak and
strong inequalities, Euler's equality and the polynomial identity hold as well for the numbers
`bᵢ = dim Hᵢ(W, f⁻¹(a); V)` of the cobordism relative to its incoming boundary.

For compact `M` all of `M` is such a band, with `M_a = ∅`, and the same statements hold for the
singular homology `Hᵢ(M; V)` and the numbers `cᵢ` of critical points of index `i` on `M`. In
particular the singular homology of a compact manifold admitting a Morse function is
finite-dimensional in every degree.

The proof is Milnor's. Across a single critical level the sublevel pair has the relative homology
of a finite CW pair with one `i`-cell for each critical point of index `i`
(`TauCeti.IsMorse.exists_relCWComplex_isIso_singularHomologyMap_sublevelPair`), where the
three statements are the Morse inequalities for CW pairs. Across a band without critical points
the relative homology vanishes, by the deformation retraction of `M_b` onto `M_a`
(`TauCeti.isZero_singularHomology_sublevelPair_of_mfderiv_ne_zero`).
A band is cut at the critical values it contains into finitely many such pieces
(`TauCeti.IsMorse.band_induction`), and the long exact sequence of the triple
`M_a ⊆ M_m ⊆ M_b` shows that dimensions and the alternating sums `Sₙ` are subadditive
(`TauCeti.TopTriple.finrank_singularHomology_totalPair_le` and
`TauCeti.TopTriple.sum_range_neg_one_pow_mul_finrank_singularHomology_totalPair_le`), while the
critical counts are additive. Above the dimension of `M` the connecting map in degree `n + 1`
vanishes, since its source is zero by the weak inequalities, which turns the strong inequality
into the equality. The polynomial identity and the lacunary principle are then the numerical
consequences `TauCeti.exists_sum_range_monomial_eq_add_mul` and
`TauCeti.eq_of_forall_sum_range_neg_one_pow_mul_le` of the strong inequalities and Euler's
equality.

## Main results

* `TauCeti.IsMorse.finrank_singularHomology_sublevelPair_le`,
  `TauCeti.IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_sublevelPair_le` and
  `TauCeti.IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_sublevelPair_eq`: the weak
  and strong Morse inequalities and Euler's equality for a compact band between regular values.
* `TauCeti.IsMorse.exists_sum_range_monomial_sublevelPair_eq_add_mul`,
  `TauCeti.IsMorse.sum_range_finrank_singularHomology_sublevelPair_le` and
  `TauCeti.IsMorse.finrank_singularHomology_sublevelPair_eq_of_forall_ne_add_one`: the Morse
  polynomial identity, the bound on the total Betti number and the lacunary principle for such a
  band.
* `TauCeti.IsMorse.finite_singularHomology_bandPair`,
  `TauCeti.IsMorse.finrank_singularHomology_bandPair_le`,
  `TauCeti.IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_bandPair_le`,
  `TauCeti.IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_bandPair_eq` and
  `TauCeti.IsMorse.exists_sum_range_monomial_bandPair_eq_add_mul`: the same statements for the
  cobordism `f⁻¹[a, b]` relative to its incoming boundary `f⁻¹(a)`.
* `TauCeti.IsMorse.finrank_singularHomology_le`,
  `TauCeti.IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_le`,
  `TauCeti.IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_eq`,
  `TauCeti.IsMorse.exists_sum_range_monomial_eq_add_mul`,
  `TauCeti.IsMorse.sum_range_finrank_singularHomology_le` and
  `TauCeti.IsMorse.finrank_singularHomology_eq_of_forall_ne_add_one`: the same for a compact
  manifold, with the numbers `TauCeti.criticalCount` of critical points of each index and their
  total `TauCeti.totalCriticalCount`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 5.
* R. Bott, *Lectures on Morse theory, old and new*, Bulletin of the American Mathematical
  Society 7 (1982), 331--358, Section 1.
-/

public section

noncomputable section

open CategoryTheory Limits Module Set Topology Topology.RelCWComplex
open Polynomial (monomial X)
open scoped ContDiff Manifold Polynomial

universe u

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] {f : M → ℝ}
  {k : Type u} [DivisionRing k] (V : ModuleCat.{u} k) [Module.Finite k V]

section Band

variable (I f) in
/-- The number of critical points of `f` of index `i` with value in `(a, b]`. -/
private abbrev bandCount (a b : ℝ) (i : ℕ) : ℕ :=
  {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = i}.ncard

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- Critical counts are additive along `a ≤ m ≤ b`, when there are finitely many critical points
with values in `(a, b]`. -/
private theorem bandCount_add {a m b : ℝ} (ham : a ≤ m) (hmb : m ≤ b)
    (hfin : (criticalPoints I f ∩ f ⁻¹' Ioc a b).Finite) (i : ℕ) :
    bandCount I f a b i = bandCount I f a m i + bandCount I f m b i := by
  have hsub {s : Set ℝ} (hs : s ⊆ Ioc a b) :
      {x ∈ criticalPoints I f ∩ f ⁻¹' s | manifoldMorseIndex I f x = i}.Finite :=
    hfin.subset fun x hx ↦ ⟨hx.1.1, hs hx.1.2⟩
  have hdisj : Disjoint
      {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a m | manifoldMorseIndex I f x = i}
      {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc m b | manifoldMorseIndex I f x = i} :=
    disjoint_left.2 fun x hx hx' ↦ (not_lt.2 hx.1.2.2) hx'.1.2.1
  rw [bandCount, bandCount, bandCount, ← ncard_union_eq hdisj (hsub (Ioc_subset_Ioc_right hmb))
    (hsub (Ioc_subset_Ioc_left ham)), ← Ioc_union_Ioc_eq_Ioc ham hmb]
  congr 1
  ext x
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_union]
  tauto

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- The count vanishes if no critical point with value in `(a, b]` has index `i`. -/
private theorem bandCount_eq_zero_of_forall {a b : ℝ} {i : ℕ}
    (h : ∀ x ∈ criticalPoints I f, f x ∈ Ioc a b → manifoldMorseIndex I f x ≠ i) :
    bandCount I f a b i = 0 := by
  have : {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = i} = ∅ :=
    eq_empty_iff_forall_notMem.2 fun x hx ↦ h x hx.1.1 hx.1.2 hx.2
  rw [bandCount, this, ncard_empty]

omit [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- There is no critical point of index larger than the dimension of `M`. -/
private theorem bandCount_eq_zero {a b : ℝ} {i : ℕ} (hi : finrank ℝ E < i) :
    bandCount I f a b i = 0 :=
  bandCount_eq_zero_of_forall fun _ _ _ ↦ (manifoldMorseIndex_le_finrank.trans_lt hi).ne

variable (I f) in
/-- The Morse inequalities for the sublevel pair `({f ≤ b}, {f ≤ a})` with coefficients `V`, in
every degree `n`: the relative homology is finite-dimensional, the weak and strong Morse
inequalities hold, and from the dimension of `M` on Euler's equality holds. -/
private def MorseInequalities (a b : ℝ) (hab : a ≤ b) : Prop :=
  ∀ n : ℕ, Module.Finite k ((sublevelPair f hab).singularHomology V n : ModuleCat k) ∧
    finrank k ((sublevelPair f hab).singularHomology V n : ModuleCat k) ≤
      bandCount I f a b n * finrank k V ∧
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) *
        finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k) ≤
      finrank k V * ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) * bandCount I f a b i ∧
    (finrank ℝ E ≤ n → ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k) =
      finrank k V * ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * bandCount I f a b i)

omit [Module.Finite k V] in
/-- The Morse inequalities hold trivially across a compact band without critical points. -/
private theorem morseInequalities_of_forall_notMem (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (hcrit : ∀ x ∈ criticalPoints I f, f x ∉ Icc a b) :
    MorseInequalities I f V a b hab := by
  have hzero (n : ℕ) := isZero_singularHomology_sublevelPair_of_mfderiv_ne_zero hf.contMDiff hab
    hcompact (fun x hax hxb hx ↦ hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 hx) ⟨hax, hxb⟩)
    V n
  have hfin (n : ℕ) : Module.Finite k ((sublevelPair f hab).singularHomology V n : ModuleCat k) :=
    have := (ModuleCat.isZero_iff_subsingleton.1 (hzero n))
    inferInstance
  have hrank (n : ℕ) :
      finrank k ((sublevelPair f hab).singularHomology V n : ModuleCat k) = 0 :=
    have := (ModuleCat.isZero_iff_subsingleton.1 (hzero n))
    finrank_zero_of_subsingleton
  have hcount (i : ℕ) : bandCount I f a b i = 0 :=
    bandCount_eq_zero_of_forall fun x hx hxab ↦ (hcrit x hx (Ioc_subset_Icc_self hxab)).elim
  intro n
  simp [hfin, hrank, hcount]

/-- **The Morse inequalities across one critical level.** If the band `f⁻¹[c - δ, c + δ]` is
compact and its critical points all lie on the level `c`, then for some `0 < ε ≤ δ` the Morse
inequalities hold for `({f ≤ c + ε}, {f ≤ c - ε})`. -/
private theorem IsMorse.exists_morseInequalities_level (hf : IsMorse I f) {c δ : ℝ} (hδ : 0 < δ)
    (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ)))
    (hsub : criticalPoints I f ∩ f ⁻¹' Icc (c - δ) (c + δ) ⊆ f ⁻¹' {c}) :
    ∃ ε, ∃ hε : 0 < ε, ε ≤ δ ∧ MorseInequalities I f V (c - ε) (c + ε) (by linarith) := by
  obtain ⟨ε, hε, hεδ, C, _, _, hC, hcell, hiso⟩ :=
    hf.exists_relCWComplex_isIso_singularHomologyMap_sublevelPair hδ hcompact
  have hsubε : criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ f ⁻¹' {c} :=
    fun x hx ↦ hsub ⟨hx.1, Icc_subset_Icc (by linarith) (by linarith) hx.2⟩
  refine ⟨ε, hε, hεδ, fun n ↦ ?_⟩
  -- The cells of `C` are counted by the critical points on the level `c`, which are those with
  -- values in `(c - ε, c + ε]`.
  have hcount (i : ℕ) : Nat.card (cell C i) = bandCount I f (c - ε) (c + ε) i := by
    rw [Nat.card_congr (hcell i).some, bandCount, ← Nat.card_coe_set_eq]
    refine Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter
      (· ∈ criticalPoints I f ∩ f ⁻¹' {c}) (manifoldMorseIndex I f · = i)).trans
      (Equiv.subtypeEquivRight fun x ↦ ?_))
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_ofPred_eq, mem_Ioc]
    constructor
    · rintro ⟨⟨hx, rfl⟩, hi⟩
      exact ⟨⟨hx, by linarith, by linarith⟩, hi⟩
    · rintro ⟨⟨hx, h₁, h₂⟩, hi⟩
      exact ⟨⟨hx, hsubε ⟨hx, h₁.le, h₂⟩⟩, hi⟩
  -- The relative homology of the sublevel pair is that of the CW pair `(C, {f ≤ c - ε})`.
  have hrank (i : ℕ) : finrank k ((complexBasePair C).singularHomology V i : ModuleCat k) =
      finrank k ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology V i :
        ModuleCat k) := by
    rw [complexBasePair_eq_ofInclusion]
    exact (@asIso _ _ _ _ _ (hiso V i)).toLinearEquiv.finrank_eq
  have hfinite (i : ℕ) : _root_.Finite (cell C i) := FiniteType.finite_cell i
  refine ⟨?_, ?_, ?_, fun hn ↦ ?_⟩
  · have h := finite_singularHomology_complexBasePair C V n
    rw [complexBasePair_eq_ofInclusion] at h
    exact Module.Finite.equiv (@asIso _ _ _ _ _ (hiso V n)).toLinearEquiv
  · rw [← hrank, ← hcount]
    exact finrank_singularHomology_complexBasePair_le C V n
  · have h := sum_range_neg_one_pow_mul_finrank_singularHomology_complexBasePair_le C V
      (n := n) fun i _ ↦ hfinite i
    simpa only [hrank, hcount] using h
  · -- There are no cells above the dimension of `M`.
    have hempty : IsEmpty (cell C (n + 1)) := by
      rw [← Finite.card_eq_zero_iff, hcount]
      exact bandCount_eq_zero (by lia)
    have h := sum_range_finrank_singularHomology_complexBasePair C V (n := n)
      (fun i _ ↦ hfinite i) hempty
    simpa only [hrank, hcount] using h

omit [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [Module.Finite k V] in
/-- **The Morse inequalities along a triple of sublevels.** If they hold for
`({f ≤ m}, {f ≤ a})` and for `({f ≤ b}, {f ≤ m})`, and only finitely many critical points have
values in `(a, b]`, they hold for `({f ≤ b}, {f ≤ a})`. -/
private theorem MorseInequalities.trans {a m b : ℝ} {ham : a ≤ m} {hmb : m ≤ b}
    (hfin : (criticalPoints I f ∩ f ⁻¹' Ioc a b).Finite) (h₁ : MorseInequalities I f V a m ham)
    (h₂ : MorseInequalities I f V m b hmb) : MorseInequalities I f V a b (ham.trans hmb) := by
  let T := TopTriple.ofInclusions (X := TopCat.of M) (sublevel_mono f ham) (sublevel_mono f hmb)
  have : ∀ n, Module.Finite k ((TopTriple.innerPair.obj T).singularHomology V n : ModuleCat k) :=
    fun n ↦ (h₁ n).1
  have : ∀ n, Module.Finite k ((TopTriple.outerPair.obj T).singularHomology V n : ModuleCat k) :=
    fun n ↦ (h₂ n).1
  have hcount := bandCount_add (I := I) ham hmb hfin
  -- The counts in degree `i` add up, and so do their alternating sums.
  have hsum (n : ℕ) (s : ℕ → ℤ) : ∑ i ∈ Finset.range (n + 1), s i * (bandCount I f a b i : ℤ) =
      ∑ i ∈ Finset.range (n + 1), s i * (bandCount I f a m i : ℤ) +
        ∑ i ∈ Finset.range (n + 1), s i * (bandCount I f m b i : ℤ) := by
    simp only [hcount, Nat.cast_add, mul_add, Finset.sum_add_distrib]
  intro n
  obtain ⟨-, hw₁, hs₁, he₁⟩ := h₁ n
  obtain ⟨-, hw₂, hs₂, he₂⟩ := h₂ n
  refine ⟨T.finite_singularHomology_totalPair V n, ?_, ?_, fun hn ↦ ?_⟩
  · refine (T.finrank_singularHomology_totalPair_le V n).trans ?_
    rw [hcount, add_mul]
    exact add_le_add hw₁ hw₂
  · refine (T.sum_range_neg_one_pow_mul_finrank_singularHomology_totalPair_le V n).trans ?_
    rw [hsum, mul_add]
    exact add_le_add hs₁ hs₂
  · -- Above the dimension of `M`, `Hₙ₊₁({f ≤ b}, {f ≤ m})` vanishes by the weak inequality.
    obtain ⟨hfin₂, hw₂', -, -⟩ := h₂ (n + 1)
    have hzero : IsZero ((TopTriple.outerPair.obj T).singularHomology V (n + 1)) := by
      rw [bandCount_eq_zero (by lia), zero_mul, Nat.le_zero,
        finrank_eq_zero_iff_of_free] at hw₂'
      exact @ModuleCat.isZero_of_subsingleton _ _ _ hw₂'
    have h : ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
          finrank k ((sublevelPair f (ham.trans hmb)).singularHomology V i : ModuleCat k) =
        ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
            finrank k ((sublevelPair f ham).singularHomology V i : ModuleCat k) +
          ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
            finrank k ((sublevelPair f hmb).singularHomology V i : ModuleCat k) :=
      T.sum_range_neg_one_pow_mul_finrank_singularHomology_totalPair_eq V n hzero
    rw [h, he₁ hn, he₂ hn, hsum, mul_add]

/-- **The Morse inequalities across a compact band between regular values**, by induction over its
critical levels. -/
private theorem IsMorse.morseInequalities (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) : MorseInequalities I f V a b hab :=
  hf.band_induction hab hcompact ha hb
    (fun _ _ hst hcompact hcrit ↦ morseInequalities_of_forall_notMem V hf hst hcompact hcrit)
    (fun _ _ _ _ _ hδ hcompact hsub ↦ hf.exists_morseInequalities_level V hδ hcompact hsub)
    fun _ _ _ _ _ hcompact h₁ h₂ ↦ h₁.trans V
      ((hf.finite_criticalPoints_inter hcompact).subset
        (inter_subset_inter_right _ (preimage_mono Ioc_subset_Icc_self))) h₂

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- Finitely many critical points with values in `(a, b]` bound the critical counts in total. -/
private theorem sum_range_bandCount_le {a b : ℝ}
    (hfin : (criticalPoints I f ∩ f ⁻¹' Ioc a b).Finite) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), bandCount I f a b i ≤
      (criticalPoints I f ∩ f ⁻¹' Ioc a b).ncard := by
  classical
  have hcount (i : ℕ) : bandCount I f a b i =
      (hfin.toFinset.filter (manifoldMorseIndex I f · = i)).card := by
    rw [bandCount, ← ncard_coe_finset]
    congr 1
    ext x
    simp
  simp only [hcount]
  rw [Finset.sum_card_fiberwise_eq_card_filter, ncard_eq_toFinset_card _ hfin]
  exact Finset.card_filter_le _ _

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- If no two critical points with values in `(a, b]` have indices differing by one, then of two
consecutive critical counts one vanishes. -/
private theorem bandCount_eq_zero_or {a b : ℝ}
    (h : ∀ x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b, ∀ y ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b,
      manifoldMorseIndex I f x ≠ manifoldMorseIndex I f y + 1) (i : ℕ) :
    bandCount I f a b i = 0 ∨ bandCount I f a b (i + 1) = 0 := by
  by_contra! hne
  obtain ⟨y, hy, hyi⟩ := nonempty_of_ncard_ne_zero hne.1
  obtain ⟨x, hx, hxi⟩ := nonempty_of_ncard_ne_zero hne.2
  exact h x hx y hy (by rw [hxi, hyi])

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [Module.Finite k V] in
/-- The Morse inequalities in the form of the Morse polynomial identity. -/
private theorem MorseInequalities.exists_sum_range_monomial_eq_add_mul {a b : ℝ} {hab : a ≤ b}
    (h : MorseInequalities I f V a b hab) {n : ℕ} (hn : finrank ℝ E ≤ n) :
    ∃ Q : ℕ[X], ∑ i ∈ Finset.range (n + 1), monomial i (bandCount I f a b i * finrank k V) =
        ∑ i ∈ Finset.range (n + 1),
          monomial i (finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k)) +
          (1 + X) * Q ∧
      (∀ i < n, (Q.coeff i : ℤ) =
        finrank k V * ∑ j ∈ Finset.range (i + 1), (-1 : ℤ) ^ (i - j) * bandCount I f a b j -
          ∑ j ∈ Finset.range (i + 1), (-1 : ℤ) ^ (i - j) *
            finrank k ((sublevelPair f hab).singularHomology V j : ModuleCat k)) ∧
      ∀ i, n ≤ i → Q.coeff i = 0 := by
  obtain ⟨Q, hQ, hcoeff, hzero⟩ := TauCeti.exists_sum_range_monomial_eq_add_mul
    (b := fun i ↦ finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k))
    (c := fun i ↦ bandCount I f a b i * finrank k V) (n := n)
    (fun m _ ↦ (h m).2.2.1.trans_eq (natCast_mul_sum_mul_natCast _ _ _ _))
    ((h n).2.2.2 hn |>.trans (natCast_mul_sum_mul_natCast _ _ _ _))
  refine ⟨Q, hQ, fun i hi ↦ ?_, hzero⟩
  rw [hcoeff i hi, natCast_mul_sum_mul_natCast]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [Module.Finite k V] in
/-- The Morse inequalities bound the total dimension of homology by the number of critical
points. -/
private theorem MorseInequalities.sum_range_finrank_le {a b : ℝ} {hab : a ≤ b}
    (h : MorseInequalities I f V a b hab) (hfin : (criticalPoints I f ∩ f ⁻¹' Ioc a b).Finite)
    (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1),
        finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k) ≤
      (criticalPoints I f ∩ f ⁻¹' Ioc a b).ncard * finrank k V :=
  calc _ ≤ ∑ i ∈ Finset.range (n + 1), bandCount I f a b i * finrank k V :=
        Finset.sum_le_sum fun i _ ↦ (h i).2.1
    _ = (∑ i ∈ Finset.range (n + 1), bandCount I f a b i) * finrank k V := Finset.sum_mul .. |>.symm
    _ ≤ _ := Nat.mul_le_mul_right _ (sum_range_bandCount_le hfin n)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [Module.Finite k V] in
/-- The lacunary principle for a sublevel pair satisfying the Morse inequalities. -/
private theorem MorseInequalities.finrank_eq_of_eq_zero_or {a b : ℝ} {hab : a ≤ b}
    (h : MorseInequalities I f V a b hab)
    (hc : ∀ i, bandCount I f a b i = 0 ∨ bandCount I f a b (i + 1) = 0) (n : ℕ) :
    finrank k ((sublevelPair f hab).singularHomology V n : ModuleCat k) =
      bandCount I f a b n * finrank k V :=
  congrFun (eq_of_forall_sum_range_neg_one_pow_mul_le
    (b := fun i ↦ finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k))
    (c := fun i ↦ bandCount I f a b i * finrank k V)
    (fun m ↦ (h m).2.2.1.trans_eq (natCast_mul_sum_mul_natCast _ _ _ _))
    fun i ↦ (hc i).imp (fun h ↦ by rw [h, zero_mul]) fun h ↦ by rw [h, zero_mul]) n

/-- **Finiteness of relative homology for a band.** Let `f` be a Morse function, and `a ≤ b`
regular values with compact band `f⁻¹[a, b]`. Then the relative singular homology
`Hₙ({f ≤ b}, {f ≤ a}; V)` is finite-dimensional. -/
theorem IsMorse.finite_singularHomology_sublevelPair (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) (n : ℕ) :
    Module.Finite k ((sublevelPair f hab).singularHomology V n : ModuleCat k) :=
  (hf.morseInequalities V hab hcompact ha hb n).1

/-- **The weak Morse inequalities for a band.** Let `f` be a Morse function, and `a ≤ b` regular
values with compact band `f⁻¹[a, b]`. Then `Hₙ({f ≤ b}, {f ≤ a}; V)` has dimension at most `dim V`
times the number of critical points of index `n` with values in `(a, b]`. -/
theorem IsMorse.finrank_singularHomology_sublevelPair_le (hf : IsMorse I f) {a b : ℝ}
    (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) (n : ℕ) :
    finrank k ((sublevelPair f hab).singularHomology V n : ModuleCat k) ≤
      {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = n}.ncard *
        finrank k V :=
  (hf.morseInequalities V hab hcompact ha hb n).2.1

/-- **The strong Morse inequalities for a band.** Let `f` be a Morse function, and `a ≤ b` regular
values with compact band `f⁻¹[a, b]`. Write `bᵢ` for the dimension of `Hᵢ({f ≤ b}, {f ≤ a}; V)` and
`cᵢ` for the number of critical points of index `i` with values in `(a, b]`. Then
`bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ (cₙ - cₙ₋₁ + ⋯ ± c₀) dim V`. -/
theorem IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_sublevelPair_le
    (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) *
        finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k) ≤
      finrank k V * ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) *
        {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = i}.ncard :=
  (hf.morseInequalities V hab hcompact ha hb n).2.2.1

/-- **Euler's equality for a band.** Let `f` be a Morse function, and `a ≤ b` regular values with
compact band `f⁻¹[a, b]`. Write `bᵢ` for the dimension of `Hᵢ({f ≤ b}, {f ≤ a}; V)` and `cᵢ` for
the number of critical points of index `i` with values in `(a, b]`. Then
`∑ᵢ₌₀ⁿ (-1)ⁱ bᵢ = (∑ᵢ₌₀ⁿ (-1)ⁱ cᵢ) dim V` for every `n ≥ dim M`. -/
theorem IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_sublevelPair_eq
    (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) {n : ℕ}
    (hn : finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k) =
      finrank k V * ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = i}.ncard :=
  (hf.morseInequalities V hab hcompact ha hb n).2.2.2 hn

/-- **The Morse polynomial identity for a band.** Let `f` be a Morse function, and `a ≤ b` regular
values with compact band `f⁻¹[a, b]`. Write `bᵢ` for the dimension of `Hᵢ({f ≤ b}, {f ≤ a}; V)`
and `cᵢ` for the number of critical points of index `i` with values in `(a, b]`. Then for every
`n ≥ dim M`, `∑ᵢ₌₀ⁿ cᵢ dim V · tⁱ = ∑ᵢ₌₀ⁿ bᵢ tⁱ + (1 + t) Q(t)` for a polynomial `Q` with natural
number coefficients. The coefficient of `tⁱ` in `Q` is the gap
`(cᵢ - cᵢ₋₁ + ⋯ ± c₀) dim V - (bᵢ - bᵢ₋₁ + ⋯ ± b₀)` in the `i`-th strong Morse inequality for
`i < n`, and zero for `i ≥ n`. -/
theorem IsMorse.exists_sum_range_monomial_sublevelPair_eq_add_mul (hf : IsMorse I f) {a b : ℝ}
    (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) {n : ℕ} (hn : finrank ℝ E ≤ n) :
    ∃ Q : ℕ[X], ∑ i ∈ Finset.range (n + 1), monomial i
          ({x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = i}.ncard *
            finrank k V) =
        ∑ i ∈ Finset.range (n + 1),
          monomial i (finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k)) +
          (1 + X) * Q ∧
      (∀ i < n, (Q.coeff i : ℤ) =
        finrank k V * ∑ j ∈ Finset.range (i + 1), (-1 : ℤ) ^ (i - j) *
            {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = j}.ncard -
          ∑ j ∈ Finset.range (i + 1), (-1 : ℤ) ^ (i - j) *
            finrank k ((sublevelPair f hab).singularHomology V j : ModuleCat k)) ∧
      ∀ i, n ≤ i → Q.coeff i = 0 :=
  (hf.morseInequalities V hab hcompact ha hb).exists_sum_range_monomial_eq_add_mul V hn

/-- **The total Betti number of a band is at most `dim V` times its number of critical points.**
Let `f` be a Morse function, and `a ≤ b` regular values with compact band `f⁻¹[a, b]`. Then for
every `n`, `∑ᵢ₌₀ⁿ dim Hᵢ({f ≤ b}, {f ≤ a}; V)` is at most `dim V` times the number of critical
points with values in `(a, b]`. -/
theorem IsMorse.sum_range_finrank_singularHomology_sublevelPair_le (hf : IsMorse I f) {a b : ℝ}
    (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1),
        finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k) ≤
      (criticalPoints I f ∩ f ⁻¹' Ioc a b).ncard * finrank k V :=
  (hf.morseInequalities V hab hcompact ha hb).sum_range_finrank_le V
    ((hf.finite_criticalPoints_inter hcompact).subset fun _ hx ↦ ⟨hx.1, Ioc_subset_Icc_self hx.2⟩)
    n

/-- **The lacunary principle for a band.** Let `f` be a Morse function, and `a ≤ b` regular values
with compact band `f⁻¹[a, b]`. If no two critical points with values in `(a, b]` have indices
differing by one, then for every `n` the dimension of `Hₙ({f ≤ b}, {f ≤ a}; V)` is `dim V` times the
number of critical points of index `n` with values in `(a, b]`. -/
theorem IsMorse.finrank_singularHomology_sublevelPair_eq_of_forall_ne_add_one (hf : IsMorse I f)
    {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b)
    (hind : ∀ x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b, ∀ y ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b,
      manifoldMorseIndex I f x ≠ manifoldMorseIndex I f y + 1) (n : ℕ) :
    finrank k ((sublevelPair f hab).singularHomology V n : ModuleCat k) =
      {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = n}.ncard *
        finrank k V :=
  (hf.morseInequalities V hab hcompact ha hb).finrank_eq_of_eq_zero_or V
    (bandCount_eq_zero_or hind) n

omit [Module.Finite k V] in
/-- Above a regular value `a`, the band pair `(f⁻¹[a, b], f⁻¹(a))` has the relative homology of the
sublevel pair `({f ≤ b}, {f ≤ a})`, through the inclusion of pairs. -/
private theorem nonempty_linearEquiv_singularHomology_bandPair (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (n : ℕ) :
    Nonempty (((bandPair f hab).singularHomology V n : ModuleCat k) ≃ₗ[k]
      ((sublevelPair f hab).singularHomology V n : ModuleCat k)) :=
  have := isIso_singularHomologyMap_bandPairInclusion hf hab hcompact ha V n
  ⟨(asIso (TopPair.singularHomologyMap (bandPairInclusion f hab) V n)).toLinearEquiv⟩

/-- **Finiteness of relative homology for a cobordism.** Let `f` be a Morse function, and `a ≤ b`
regular values with compact band `f⁻¹[a, b]`. Then the relative singular homology
`Hₙ(f⁻¹[a, b], f⁻¹(a); V)` of the band relative to its lower level is finite-dimensional. -/
theorem IsMorse.finite_singularHomology_bandPair (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) (n : ℕ) :
    Module.Finite k ((bandPair f hab).singularHomology V n : ModuleCat k) :=
  have := hf.finite_singularHomology_sublevelPair V hab hcompact ha hb n
  Module.Finite.equiv
    (nonempty_linearEquiv_singularHomology_bandPair V hf.contMDiff hab hcompact ha n).some.symm

omit [Module.Finite k V] in
private theorem finrank_singularHomology_bandPair (hf : ContMDiff I 𝓘(ℝ) ∞ f) {a b : ℝ}
    (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (n : ℕ) :
    finrank k ((bandPair f hab).singularHomology V n : ModuleCat k) =
      finrank k ((sublevelPair f hab).singularHomology V n : ModuleCat k) :=
  (nonempty_linearEquiv_singularHomology_bandPair V hf hab hcompact ha n).some.finrank_eq

/-- **The weak Morse inequalities for a cobordism.** Let `f` be a Morse function, and `a ≤ b`
regular values with compact band `f⁻¹[a, b]`. Then `Hₙ(f⁻¹[a, b], f⁻¹(a); V)` has dimension at
most `dim V` times the number of critical points of index `n` with values in `(a, b]`. -/
theorem IsMorse.finrank_singularHomology_bandPair_le (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) (n : ℕ) :
    finrank k ((bandPair f hab).singularHomology V n : ModuleCat k) ≤
      {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = n}.ncard *
        finrank k V := by
  rw [finrank_singularHomology_bandPair V hf.contMDiff hab hcompact ha]
  exact hf.finrank_singularHomology_sublevelPair_le V hab hcompact ha hb n

/-- **The strong Morse inequalities for a cobordism.** Let `f` be a Morse function, and `a ≤ b`
regular values with compact band `f⁻¹[a, b]`. Write `bᵢ` for the dimension of
`Hᵢ(f⁻¹[a, b], f⁻¹(a); V)` and `cᵢ` for the number of critical points of index `i` with values in
`(a, b]`. Then `bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ (cₙ - cₙ₋₁ + ⋯ ± c₀) dim V`. -/
theorem IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_bandPair_le
    (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) *
        finrank k ((bandPair f hab).singularHomology V i : ModuleCat k) ≤
      finrank k V * ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) *
        {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = i}.ncard := by
  simpa only [finrank_singularHomology_bandPair V hf.contMDiff hab hcompact ha] using
    hf.sum_range_neg_one_pow_mul_finrank_singularHomology_sublevelPair_le V hab hcompact ha hb n

/-- **Euler's equality for a cobordism.** Let `f` be a Morse function, and `a ≤ b` regular values
with compact band `f⁻¹[a, b]`. Write `bᵢ` for the dimension of `Hᵢ(f⁻¹[a, b], f⁻¹(a); V)` and `cᵢ`
for the number of critical points of index `i` with values in `(a, b]`. Then
`∑ᵢ₌₀ⁿ (-1)ⁱ bᵢ = (∑ᵢ₌₀ⁿ (-1)ⁱ cᵢ) dim V` for every `n ≥ dim M`. -/
theorem IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_bandPair_eq
    (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) {n : ℕ}
    (hn : finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        finrank k ((bandPair f hab).singularHomology V i : ModuleCat k) =
      finrank k V * ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = i}.ncard := by
  simpa only [finrank_singularHomology_bandPair V hf.contMDiff hab hcompact ha] using
    hf.sum_range_neg_one_pow_mul_finrank_singularHomology_sublevelPair_eq V hab hcompact ha hb hn

/-- **The Morse polynomial identity for a cobordism.** Let `f` be a Morse function, and `a ≤ b`
regular values with compact band `f⁻¹[a, b]`. Write `bᵢ` for the dimension of
`Hᵢ(f⁻¹[a, b], f⁻¹(a); V)` and `cᵢ` for the number of critical points of index `i` with values in
`(a, b]`. Then for every `n ≥ dim M`, `∑ᵢ₌₀ⁿ cᵢ dim V · tⁱ = ∑ᵢ₌₀ⁿ bᵢ tⁱ + (1 + t) Q(t)` for a
polynomial `Q` with natural number coefficients. The coefficient of `tⁱ` in `Q` is the gap
`(cᵢ - cᵢ₋₁ + ⋯ ± c₀) dim V - (bᵢ - bᵢ₋₁ + ⋯ ± b₀)` in the `i`-th strong Morse inequality for
`i < n`, and zero for `i ≥ n`. -/
theorem IsMorse.exists_sum_range_monomial_bandPair_eq_add_mul (hf : IsMorse I f) {a b : ℝ}
    (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) {n : ℕ} (hn : finrank ℝ E ≤ n) :
    ∃ Q : ℕ[X], ∑ i ∈ Finset.range (n + 1), monomial i
          ({x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = i}.ncard *
            finrank k V) =
        ∑ i ∈ Finset.range (n + 1),
          monomial i (finrank k ((bandPair f hab).singularHomology V i : ModuleCat k)) +
          (1 + X) * Q ∧
      (∀ i < n, (Q.coeff i : ℤ) =
        finrank k V * ∑ j ∈ Finset.range (i + 1), (-1 : ℤ) ^ (i - j) *
            {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = j}.ncard -
          ∑ j ∈ Finset.range (i + 1), (-1 : ℤ) ^ (i - j) *
            finrank k ((bandPair f hab).singularHomology V j : ModuleCat k)) ∧
      ∀ i, n ≤ i → Q.coeff i = 0 := by
  simpa only [finrank_singularHomology_bandPair V hf.contMDiff hab hcompact ha] using
    hf.exists_sum_range_monomial_sublevelPair_eq_add_mul V hab hcompact ha hb hn

end Band

section Compact

variable [CompactSpace M]

/-- On a compact manifold, take `a < f < b`. The Morse inequalities hold for the sublevel pair
`({f ≤ b}, {f ≤ a}) = (M, ∅)`, whose relative homology is the singular homology of `M` and whose
critical counts are those of `f`. -/
private theorem IsMorse.exists_morseInequalities_univ (hf : IsMorse I f) :
    ∃ a b : ℝ, ∃ hab : a ≤ b, MorseInequalities I f V a b hab ∧
      (∀ n, Nonempty (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj V).obj
        (TopCat.of M) ≅ (sublevelPair f hab).singularHomology V n)) ∧
      (∀ i, bandCount I f a b i = (criticalCount I f i).toNat) ∧ ∀ x, f x ∈ Ioc a b := by
  obtain ⟨a, b, hab, hcompact, ha, hb, hf'⟩ :=
    exists_isRegularValue_forall_mem_Ioc (I := I) hf.contMDiff.continuous
  refine ⟨a, b, hab, hf.morseInequalities V hab hcompact ha hb,
    fun n ↦ ⟨singularHomologyIsoSublevelPair hab (fun x ↦ (hf' x).1)
      (fun x ↦ (hf' x).2) V n⟩, fun i ↦ ?_, hf'⟩
  rw [bandCount, criticalCount_def, ← ncard_def]
  congr 1
  ext x
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
  have := hf' x
  tauto

/-- **Finiteness of homology.** The singular homology of a compact boundaryless manifold carrying
a Morse function, with coefficients in a finite-dimensional module `V`, is finite-dimensional in
every degree. -/
theorem IsMorse.finite_singularHomology (hf : IsMorse I f) (n : ℕ) :
    Module.Finite k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj V).obj
      (TopCat.of M)) := by
  obtain ⟨a, b, hab, h, he, -, -⟩ := hf.exists_morseInequalities_univ V
  have := (h n).1
  exact Module.Finite.equiv (he n).some.symm.toLinearEquiv

/-- **The weak Morse inequalities.** For a Morse function `f` on a compact boundaryless manifold
`M`, the singular homology `Hₙ(M; V)` has dimension at most `dim V` times the number of critical
points of index `n`. -/
theorem IsMorse.finrank_singularHomology_le (hf : IsMorse I f) (n : ℕ) :
    finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj V).obj
        (TopCat.of M)) ≤
      (criticalCount I f n).toNat * finrank k V := by
  obtain ⟨a, b, hab, h, he, hc, -⟩ := hf.exists_morseInequalities_univ V
  rw [(he n).some.toLinearEquiv.finrank_eq, ← hc]
  exact (h n).2.1

/-- **The strong Morse inequalities.** For a Morse function `f` on a compact boundaryless manifold
`M`, write `bᵢ` for the dimension of `Hᵢ(M; V)` and `cᵢ` for the number of critical points of
index `i`. Then `bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ (cₙ - cₙ₋₁ + ⋯ ± c₀) dim V`. -/
theorem IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_le (hf : IsMorse I f)
    (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) *
        finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj V).obj
          (TopCat.of M)) ≤
      finrank k V * ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) *
        (criticalCount I f i).toNat := by
  obtain ⟨a, b, hab, h, he, hc, -⟩ := hf.exists_morseInequalities_univ V
  have hr (i : ℕ) := (he i).some.toLinearEquiv.finrank_eq
  simp only [hr, ← hc]
  exact (h n).2.2.1

/-- **Euler's equality.** For a Morse function `f` on a compact boundaryless manifold `M`, write
`bᵢ` for the dimension of `Hᵢ(M; V)` and `cᵢ` for the number of critical points of index `i`.
Then `∑ᵢ₌₀ⁿ (-1)ⁱ bᵢ = (∑ᵢ₌₀ⁿ (-1)ⁱ cᵢ) dim V` for every `n ≥ dim M`. -/
theorem IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_eq (hf : IsMorse I f)
    {n : ℕ} (hn : finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj V).obj
          (TopCat.of M)) =
      finrank k V * ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat := by
  obtain ⟨a, b, hab, h, he, hc, -⟩ := hf.exists_morseInequalities_univ V
  have hr (i : ℕ) := (he i).some.toLinearEquiv.finrank_eq
  simp only [hr, ← hc]
  exact (h n).2.2.2 hn

/-- **The Morse polynomial identity.** For a Morse function `f` on a compact boundaryless manifold
`M`, write `bᵢ` for the dimension of `Hᵢ(M; V)` and `cᵢ` for the number of critical points of index
`i`. Then for every `n ≥ dim M`, `∑ᵢ₌₀ⁿ cᵢ dim V · tⁱ = ∑ᵢ₌₀ⁿ bᵢ tⁱ + (1 + t) Q(t)` for a polynomial
`Q` with natural number coefficients. The coefficient of `tⁱ` in `Q` is the gap
`(cᵢ - cᵢ₋₁ + ⋯ ± c₀) dim V - (bᵢ - bᵢ₋₁ + ⋯ ± b₀)` in the `i`-th strong Morse inequality for
`i < n`, and zero for `i ≥ n`. -/
theorem IsMorse.exists_sum_range_monomial_eq_add_mul (hf : IsMorse I f) {n : ℕ}
    (hn : finrank ℝ E ≤ n) :
    ∃ Q : ℕ[X], ∑ i ∈ Finset.range (n + 1),
          monomial i ((criticalCount I f i).toNat * finrank k V) =
        ∑ i ∈ Finset.range (n + 1), monomial i
          (finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj V).obj
            (TopCat.of M))) + (1 + X) * Q ∧
      (∀ i < n, (Q.coeff i : ℤ) =
        finrank k V * ∑ j ∈ Finset.range (i + 1), (-1 : ℤ) ^ (i - j) *
            (criticalCount I f j).toNat -
          ∑ j ∈ Finset.range (i + 1), (-1 : ℤ) ^ (i - j) *
            finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) j).obj V).obj
              (TopCat.of M))) ∧
      ∀ i, n ≤ i → Q.coeff i = 0 := by
  obtain ⟨a, b, hab, h, he, hc, -⟩ := hf.exists_morseInequalities_univ V
  have hr (i : ℕ) := (he i).some.toLinearEquiv.finrank_eq
  simp only [hr, ← hc]
  exact h.exists_sum_range_monomial_eq_add_mul V hn

/-- **The total Betti number is at most `dim V` times the number of critical points.** For a Morse
function `f` on a compact boundaryless manifold `M` and every `n`, `∑ᵢ₌₀ⁿ dim Hᵢ(M; V)` is at most
`dim V` times the number of critical points of `f`. -/
theorem IsMorse.sum_range_finrank_singularHomology_le (hf : IsMorse I f) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1),
        finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj V).obj
          (TopCat.of M)) ≤
      (totalCriticalCount I f).toNat * finrank k V := by
  obtain ⟨a, b, hab, h, he, -, hfab⟩ := hf.exists_morseInequalities_univ V
  have hr (i : ℕ) := (he i).some.toLinearEquiv.finrank_eq
  have hS : criticalPoints I f ∩ f ⁻¹' Ioc a b = criticalPoints I f :=
    inter_eq_left.2 fun x _ ↦ hfab x
  simp only [hr]
  rw [totalCriticalCount_def, ← ncard_def, ← hS]
  exact h.sum_range_finrank_le V (by rw [hS]; exact hf.finite_criticalPoints) n

/-- **The lacunary principle.** Let `f` be a Morse function on a compact boundaryless manifold `M`
such that no two critical points have indices differing by one. Then for every `n` the dimension
of `Hₙ(M; V)` is `dim V` times the number of critical points of index `n`. -/
theorem IsMorse.finrank_singularHomology_eq_of_forall_ne_add_one (hf : IsMorse I f)
    (hind : ∀ x ∈ criticalPoints I f, ∀ y ∈ criticalPoints I f,
      manifoldMorseIndex I f x ≠ manifoldMorseIndex I f y + 1) (n : ℕ) :
    finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj V).obj
        (TopCat.of M)) =
      (criticalCount I f n).toNat * finrank k V := by
  obtain ⟨a, b, hab, h, he, hc, -⟩ := hf.exists_morseInequalities_univ V
  rw [(he n).some.toLinearEquiv.finrank_eq, ← hc]
  exact h.finrank_eq_of_eq_zero_or V (bandCount_eq_zero_or fun x hx y hy ↦ hind x hx.1 y hy.1) n

end Compact

end TauCeti
