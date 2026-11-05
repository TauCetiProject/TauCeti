/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Empty
public import TauCeti.AlgebraicTopology.Singular.Triple.Finrank
public import TauCeti.Geometry.Manifold.Morse.Cell.Homology
public import TauCeti.Geometry.Manifold.Morse.Deformation.Homology

/-!
# The Morse inequalities

Let `f` be a Morse function on a boundaryless finite-dimensional manifold `M`, let `V` be a
finite-dimensional module over a division ring `k`, and write `M_a = {f ≤ a}`. Let `a ≤ b` be
values of `f` at no critical point, with compact band `f⁻¹[a, b]`. Write
`bᵢ = dim Hᵢ(M_b, M_a; V)` for the dimensions of relative singular homology, and `cᵢ` for the
number of critical points of index `i` with value in `(a, b]`. Then, for every `n`:

* `Hₙ(M_b, M_a; V)` is finite-dimensional, and `bₙ ≤ cₙ dim V` (the weak Morse inequalities);
* `bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ (cₙ - cₙ₋₁ + ⋯ ± c₀) dim V` (the strong Morse inequalities);
* if `n ≥ dim M`, then `∑ᵢ₌₀ⁿ (-1)ⁱ bᵢ = (∑ᵢ₌₀ⁿ (-1)ⁱ cᵢ) dim V` (Euler's equality).

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
A band is cut at the critical values it contains into finitely many such pieces, and the long exact
sequence of the triple `M_a ⊆ M_m ⊆ M_b` shows that dimensions and the alternating sums `Sₙ` are
subadditive (`TauCeti.TopTriple.finrank_singularHomology_totalPair_le` and
`TauCeti.TopTriple.sum_range_neg_one_pow_mul_finrank_singularHomology_totalPair_le`), while the
critical counts are additive. Above the dimension of `M` the connecting map in degree `n + 1`
vanishes, since its source is zero by the weak inequalities, which turns the strong inequality
into the equality.

## Main results

* `TauCeti.IsMorse.finrank_singularHomology_sublevelPair_le`,
  `TauCeti.IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_sublevelPair_le` and
  `TauCeti.IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_sublevelPair_eq`: the weak
  and strong Morse inequalities and Euler's equality for a compact band between regular values.
* `TauCeti.IsMorse.finrank_singularHomology_le`,
  `TauCeti.IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_le` and
  `TauCeti.IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_eq`: the same for a compact
  manifold, with the numbers `TauCeti.criticalCount` of critical points of each index.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 5.
-/

public section

noncomputable section

open CategoryTheory Limits Module Set Topology Topology.RelCWComplex
open scoped ContDiff Manifold

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
compact, then for some `0 < ε ≤ δ` the Morse inequalities hold for
`({f ≤ c + ε}, {f ≤ c - ε})`. -/
private theorem IsMorse.exists_morseInequalities_level (hf : IsMorse I f) {c δ : ℝ} (hδ : 0 < δ)
    (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ))) :
    ∃ ε, ∃ hε : 0 < ε, ε ≤ δ ∧ MorseInequalities I f V (c - ε) (c + ε) (by linarith) := by
  obtain ⟨δ', hδ', hδ'δ, hsub⟩ := hf.exists_criticalPoints_inter_preimage_Icc_subset hδ hcompact
  have hcompact' : IsCompact (f ⁻¹' Icc (c - δ') (c + δ')) :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.contMDiff.continuous)
      (preimage_mono (Icc_subset_Icc (by linarith) (by linarith)))
  obtain ⟨ε, hε, hεδ', C, _, _, hC, hcell, hiso⟩ :=
    hf.exists_relCWComplex_isIso_singularHomologyMap_sublevelPair hδ' hcompact'
  have hsubε : criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ f ⁻¹' {c} :=
    fun x hx ↦ hsub ⟨hx.1, Icc_subset_Icc (by linarith) (by linarith) hx.2⟩
  refine ⟨ε, hε, hεδ'.trans hδ'δ, fun n ↦ ?_⟩
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
    (fun _ _ _ _ _ hδ hcompact ↦ hf.exists_morseInequalities_level V hδ hcompact)
    fun _ _ _ _ _ hcompact h₁ h₂ ↦ h₁.trans V
      ((hf.finite_criticalPoints_inter hcompact).subset
        (inter_subset_inter_right _ (preimage_mono Ioc_subset_Icc_self))) h₂

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
      ∀ i, bandCount I f a b i = (criticalCount I f i).toNat := by
  have hfc : Continuous f := hf.contMDiff.continuous
  obtain ⟨l, hl⟩ := (isCompact_range hfc).bddBelow
  obtain ⟨t, ht⟩ := (isCompact_range hfc).bddAbove
  have ha (x : M) : l - 1 < f x := by linarith [hl (mem_range_self x)]
  have hb (x : M) : f x < max (t + 1) (l - 1) :=
    lt_max_of_lt_left (by linarith [ht (mem_range_self x)])
  have hab : l - 1 ≤ max (t + 1) (l - 1) := le_max_right _ _
  have hcrit {c : ℝ} (hc : ∀ x, f x ≠ c) : IsRegularValue I 𝓘(ℝ) f c :=
    isRegularValue_iff_notMem_image_criticalPoints.2 fun ⟨x, _, hx⟩ ↦ hc x hx
  refine ⟨l - 1, max (t + 1) (l - 1), hab,
    hf.morseInequalities V hab (isClosed_Icc.preimage hfc).isCompact
      (hcrit fun x ↦ (ha x).ne') (hcrit fun x ↦ (hb x).ne), fun n ↦ ?_, fun i ↦ ?_⟩
  · -- `{f ≤ a}` is empty and `{f ≤ b}` is all of `M`.
    have : IsEmpty (sublevelPair f hab).snd :=
      ⟨fun (x : {x : M | f x ≤ l - 1}) ↦ (ha x).not_ge x.2⟩
    have hπ : IsIso ((sublevelPair f hab).singularHomologyπ V n) := inferInstance
    exact ⟨((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj V).mapIso
      (TopCat.isoOfHomeo (sublevelHomeomorphUniv fun x ↦ (hb x).le)).symm ≪≫
        @asIso _ _ _ _ _ hπ⟩
  · rw [bandCount, criticalCount_def, ← ncard_def]
    congr 1
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
    have : f x ∈ Ioc (l - 1) (max (t + 1) (l - 1)) := ⟨ha x, (hb x).le⟩
    tauto

/-- **Finiteness of homology.** The singular homology of a compact boundaryless manifold carrying
a Morse function, with coefficients in a finite-dimensional module `V`, is finite-dimensional in
every degree. -/
theorem IsMorse.finite_singularHomology (hf : IsMorse I f) (n : ℕ) :
    Module.Finite k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj V).obj
      (TopCat.of M)) := by
  obtain ⟨a, b, hab, h, he, -⟩ := hf.exists_morseInequalities_univ V
  have := (h n).1
  exact Module.Finite.equiv (he n).some.symm.toLinearEquiv

/-- **The weak Morse inequalities.** For a Morse function `f` on a compact boundaryless manifold
`M`, the singular homology `Hₙ(M; V)` has dimension at most `dim V` times the number of critical
points of index `n`. -/
theorem IsMorse.finrank_singularHomology_le (hf : IsMorse I f) (n : ℕ) :
    finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj V).obj
        (TopCat.of M)) ≤
      (criticalCount I f n).toNat * finrank k V := by
  obtain ⟨a, b, hab, h, he, hc⟩ := hf.exists_morseInequalities_univ V
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
  obtain ⟨a, b, hab, h, he, hc⟩ := hf.exists_morseInequalities_univ V
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
  obtain ⟨a, b, hab, h, he, hc⟩ := hf.exists_morseInequalities_univ V
  have hr (i : ℕ) := (he i).some.toLinearEquiv.finrank_eq
  simp only [hr, ← hc]
  exact (h n).2.2.2 hn

end Compact

end TauCeti
