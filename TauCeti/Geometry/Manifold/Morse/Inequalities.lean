/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Sublevel
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import TauCeti.Algebra.BigOperators.Ring.Finset
import TauCeti.Algebra.Homology.EulerCharacteristic.MorseInequalities
import TauCeti.Algebra.Polynomial.AlternatingSum
import TauCeti.Geometry.Manifold.Morse.Cell.Homology
import TauCeti.Geometry.Manifold.Morse.Deformation.Homology

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

Read from the other end, `W` is the band of `-f` between `-b` and `-a`, relative to its incoming
boundary `f⁻¹(b)` (`TauCeti.bandPair_neg`). A critical point of index `λ` of `f` has index
`dim M - λ` for `-f`. So the same statements hold for the numbers `bᵢ = dim Hᵢ(W, f⁻¹(b); V)` of
the cobordism relative to its outgoing boundary, with `cᵢ` the number of critical points of index
`dim M - i` with values in `[a, b)`. Comparing the two Euler equalities, the Euler characteristics
of `(W, f⁻¹(b))` and `(W, f⁻¹(a))` agree up to the sign `(-1)^(dim M)`.

For compact `M` all of `M` is such a band, with `M_a = ∅`, and the same statements hold for the
singular homology `Hᵢ(M; V)` and the numbers `cᵢ` of critical points of index `i` on `M`. In
particular the singular homology of a compact manifold admitting a Morse function is
finite-dimensional in every degree.

The finiteness needs no division ring: for a finitely generated module `V` over a noetherian ring
`k`, such as `ℤ`, the relative homology `Hₙ(M_b, M_a; V)` is finitely generated
(`TauCeti.IsMorse.finite_singularHomology_sublevelPair`), and so is the homology of the cobordism
relative to either boundary. For compact `M`, finite generation of `Hₙ(M; V)` over a noetherian
ring follows from the finite CW type of `M` (`TauCeti.IsMorse.finiteCWType` and
`TauCeti.finite_singularHomology_of_finiteCWType`).

The proof is Milnor's. Across a single critical level the sublevel pair has the relative homology
of a finite CW pair with one `i`-cell for each critical point of index `i`
(`TauCeti.IsMorse.exists_relCWComplex_isIso_singularHomologyMap_sublevelPair`), where finiteness
over a noetherian ring and the strong Morse inequalities hold for CW pairs. Across a band without
critical points the relative homology vanishes, by the deformation retraction of `M_b` onto `M_a`
(`TauCeti.isZero_singularHomology_sublevelPair_of_mfderiv_ne_zero`).
A band is cut at the critical values it contains into finitely many such pieces
(`TauCeti.IsMorse.band_induction`), and the long exact sequence of the triple
`M_a ⊆ M_m ⊆ M_b` shows that the alternating sums `Sₙ` are subadditive
(`TauCeti.TopTriple.sum_range_neg_one_pow_mul_finrank_singularHomology_totalPair_le`), while the
critical counts are additive. The weak inequalities follow from
`TauCeti.le_of_forall_sum_range_neg_one_pow_mul_le`, and Euler’s equality follows from
`TauCeti.sum_range_neg_one_pow_mul_eq_of_le_succ`. The polynomial identity follows from
`TauCeti.exists_sum_range_monomial_eq_add_mul`, and the lacunary principle follows from
`TauCeti.eq_of_forall_sum_range_neg_one_pow_mul_le`.

The coefficients of `Q` are ranks of boundary maps. Cut the band at regular values
`a = s 0 ≤ s 1 ≤ ⋯ ≤ s (N + 1) = b` so that each piece `f⁻¹[s j, s (j + 1)]` contains at most one
critical value; on a compact manifold such values exist, since a Morse function has finitely many
critical values (`TauCeti.exists_monotone_isCriticalBand_of_finite_image_criticalPoints`). Each
piece then has `bᵢ = cᵢ dim V`, and summing the defects of subadditivity of `Sₙ` over the triples
`(M_{s (j + 2)}, M_{s (j + 1)}, M_{s 0})` (`Monotone.sum_range_finrank_range_singularHomologyδ_eq`)
shows that the coefficient of `tⁿ` in `Q` is the sum over `j < N` of the ranks of the connecting
maps `Hₙ₊₁(M_{s (j + 2)}, M_{s (j + 1)}) ⟶ Hₙ(M_{s (j + 1)}, M_{s 0})`
(`TauCeti.IsMorse.coeff_eq_sum_range_finrank_range_singularHomologyδ_sublevelPair`).

## Main results

* `TauCeti.IsMorse.finite_singularHomology_sublevelPair`,
  `TauCeti.IsMorse.finite_singularHomology_bandPair`,
  `TauCeti.IsMorse.finite_singularHomology_upperBandPair`: finite generation of the relative
  homology of a compact band and of the cobordism relative to either boundary, with coefficients
  in a finitely generated module over a noetherian ring.
* `TauCeti.IsMorse.finrank_singularHomology_sublevelPair_le`,
  `TauCeti.IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_sublevelPair_le`,
  `TauCeti.IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_sublevelPair_eq` and
  `sum_range_neg_one_pow_mul_finrank_singularHomology_sublevelPair_eq_of_manifoldMorseIndex_ne`:
  the weak and strong Morse inequalities and Euler's equality for a compact band between regular
  values (for `n ≥ dim M`, or whenever no critical point in `(a, b]` has index `n + 1`).
* `TauCeti.IsMorse.exists_sum_range_monomial_sublevelPair_eq_add_mul`,
  `TauCeti.IsMorse.sum_range_finrank_singularHomology_sublevelPair_le` and
  `TauCeti.IsMorse.finrank_singularHomology_sublevelPair_eq_of_forall_ne_add_one`: the Morse
  polynomial identity, the bound on the total Betti number and the lacunary principle for such a
  band.
* `TauCeti.IsMorse.finrank_singularHomology_bandPair_le`,
  `TauCeti.IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_bandPair_le`,
  `TauCeti.IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_bandPair_eq` and
  `TauCeti.IsMorse.exists_sum_range_monomial_bandPair_eq_add_mul`: the same statements for the
  cobordism `f⁻¹[a, b]` relative to its incoming boundary `f⁻¹(a)`.
* `TauCeti.IsMorse.finrank_singularHomology_upperBandPair_le`,
  `TauCeti.IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_upperBandPair_le`,
  `TauCeti.IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_upperBandPair_eq` and
  `TauCeti.IsMorse.exists_sum_range_monomial_upperBandPair_eq_add_mul`: the same statements for
  the cobordism relative to its outgoing boundary `f⁻¹(b)`, with critical points counted by their
  complementary index.
* `IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_upperBandPair_eq_neg_one_pow_mul`:
  the Euler characteristics of the cobordism relative to its two boundaries agree up to the sign
  `(-1)^(dim M)`.
* `TauCeti.IsMorse.sum_range_finrank_range_singularHomologyδ_sublevelPair_eq` and
  `TauCeti.IsMorse.coeff_eq_sum_range_finrank_range_singularHomologyδ_sublevelPair`: for a band
  cut at regular values into pieces with at most one critical value each, the gap in the `n`-th
  strong inequality, which is the coefficient of `tⁿ` in `Q`, is a sum of ranks of connecting maps
  of triples of sublevels.
* `TauCeti.IsMorse.finrank_singularHomology_le`,
  `TauCeti.IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_le`,
  `TauCeti.IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_eq`,
  `TauCeti.IsMorse.exists_sum_range_monomial_eq_add_mul`,
  `TauCeti.IsMorse.sum_range_finrank_singularHomology_le` and
  `TauCeti.IsMorse.finrank_singularHomology_eq_of_forall_ne_add_one`: the same for a compact
  manifold, with the numbers `TauCeti.criticalCount` of critical points of each index and their
  total `TauCeti.totalCriticalCount`.
* `TauCeti.IsMorse.sum_range_finrank_range_singularHomologyδ_eq` and
  `TauCeti.IsMorse.coeff_eq_sum_range_finrank_range_singularHomologyδ`: on a compact manifold, the
  coefficients of `Q` as sums of ranks of connecting maps along a cut of the values of `f` into
  pieces with at most one critical value each, which exists by
  `TauCeti.exists_monotone_isCriticalBand_of_finite_image_criticalPoints`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 5.
* R. Bott, *Lectures on Morse theory, old and new*, Bulletin of the American Mathematical
  Society 7 (1982), 331--358, Section 1.
-/

public section

noncomputable section

open CategoryTheory Module Set Topology.RelCWComplex
open Polynomial (monomial X)
open scoped ContDiff Manifold Polynomial

universe u

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {f : M → ℝ}

section BandCount

variable (I f) in
/-- The number of critical points of `f` of index `i` with value in `(a, b]`. -/
private abbrev bandCount (a b : ℝ) (i : ℕ) : ℕ :=
  {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = i}.ncard

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

/-- The count vanishes if no critical point with value in `(a, b]` has index `i`. -/
private theorem bandCount_eq_zero_of_forall {a b : ℝ} {i : ℕ}
    (h : ∀ x ∈ criticalPoints I f, f x ∈ Ioc a b → manifoldMorseIndex I f x ≠ i) :
    bandCount I f a b i = 0 := by
  have : {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = i} = ∅ :=
    eq_empty_iff_forall_notMem.2 fun x hx ↦ h x hx.1.1 hx.1.2 hx.2
  rw [bandCount, this, ncard_empty]

/-- There is no critical point of index larger than the dimension of `M`. -/
private theorem bandCount_eq_zero {a b : ℝ} {i : ℕ} (hi : finrank ℝ E < i) :
    bandCount I f a b i = 0 :=
  bandCount_eq_zero_of_forall fun _ _ _ ↦ (manifoldMorseIndex_le_finrank.trans_lt hi).ne

/-- If `c ∈ (a, b]` is the only critical value in `[a, b]`, the critical points of index `i` on the
level `c` are counted by `bandCount I f a b i`. -/
private theorem natCard_eq_bandCount {a b c : ℝ} (hac : a < c) (hcb : c ≤ b)
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c) (i : ℕ) :
    Nat.card {p : ↥(criticalPoints I f ∩ f ⁻¹' {c}) // manifoldMorseIndex I f p = i} =
      bandCount I f a b i := by
  rw [bandCount, ← Nat.card_coe_set_eq]
  refine Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter
    (· ∈ criticalPoints I f ∩ f ⁻¹' {c}) (manifoldMorseIndex I f · = i)).trans
    (Equiv.subtypeEquivRight fun x ↦ ?_))
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_ofPred_eq, mem_Ioc]
  constructor
  · rintro ⟨⟨hx, rfl⟩, hi⟩
    exact ⟨⟨hx, hac, hcb⟩, hi⟩
  · rintro ⟨⟨hx, h₁, h₂⟩, hi⟩
    exact ⟨⟨hx, hcrit x hx ⟨h₁.le, h₂⟩⟩, hi⟩

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

/-- Critical counts are additive along `s 0 ≤ s 1 ≤ ⋯ ≤ s N`, when there are finitely many critical
points with values in `(s 0, s N]`. -/
private theorem sum_range_bandCount {s : ℕ → ℝ} (hs : Monotone s) {N : ℕ}
    (hfin : (criticalPoints I f ∩ f ⁻¹' Ioc (s 0) (s N)).Finite) (i : ℕ) :
    ∑ j ∈ Finset.range N, bandCount I f (s j) (s (j + 1)) i = bandCount I f (s 0) (s N) i := by
  induction N with
  | zero => simp [bandCount]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih (hfin.subset (inter_subset_inter_right _
      (preimage_mono (Ioc_subset_Ioc_right (hs N.le_succ))))),
      bandCount_add (hs (Nat.zero_le N)) (hs N.le_succ) hfin]

/-- If all values of `f` lie in `(a, b]`, the critical points with values in `(a, b]` are all
critical points. -/
private theorem ncard_eq_toNat_criticalCount {a b : ℝ} (h : ∀ x, f x ∈ Ioc a b) (i : ℕ) :
    bandCount I f a b i = (criticalCount I f i).toNat := by
  rw [bandCount, criticalCount_def, ← ncard_def]
  congr 1
  ext x
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
  have := h x
  tauto

end BandCount

section MorseInequalities

variable {k : Type u} [Ring k] (V : ModuleCat.{u} k)

variable (I f) in
/-- Finiteness and the strong Morse inequalities for the sublevel pair `({f ≤ b}, {f ≤ a})` with
coefficients `V`, in every degree `n`. The weak inequalities, Euler's equality, the polynomial
identity and the lacunary principle are all numerical consequences of this predicate. -/
private def MorseInequalities (a b : ℝ) (hab : a ≤ b) : Prop :=
  ∀ n : ℕ, Module.Finite k ((sublevelPair f hab).singularHomology V n : ModuleCat k) ∧
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) *
        finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k) ≤
      finrank k V * ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) * bandCount I f a b i

/-- The weak Morse inequality follows by adding consecutive strong Morse inequalities. -/
private theorem MorseInequalities.finrank_le {a b : ℝ} {hab : a ≤ b}
    (h : MorseInequalities I f V a b hab) (n : ℕ) :
    finrank k ((sublevelPair f hab).singularHomology V n : ModuleCat k) ≤
      bandCount I f a b n * finrank k V :=
  le_of_forall_sum_range_neg_one_pow_mul_le
    (b := fun i ↦ finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k))
    (c := fun i ↦ bandCount I f a b i * finrank k V)
    (fun m ↦ (h m).2.trans_eq (natCast_mul_sum_mul_natCast _ _ _ _)) n

/-- Euler's equality at any degree `n` with no critical point of index `n + 1` follows from the
strong Morse inequalities in degrees `n` and `n + 1`. -/
private theorem MorseInequalities.sum_range_neg_one_pow_mul_eq {a b : ℝ} {hab : a ≤ b}
    (h : MorseInequalities I f V a b hab) {n : ℕ} (hno : bandCount I f a b (n + 1) = 0) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k) =
      finrank k V * ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * bandCount I f a b i := by
  rw [natCast_mul_sum_mul_natCast]
  exact sum_range_neg_one_pow_mul_eq_of_le_succ
    (b := fun i ↦ finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k))
    (c := fun i ↦ bandCount I f a b i * finrank k V)
    (fun m _ ↦ (h m).2.trans_eq (natCast_mul_sum_mul_natCast _ _ _ _)) (by simp [hno])

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
    (fun m _ ↦ (h m).2.trans_eq (natCast_mul_sum_mul_natCast _ _ _ _))
    ((h.sum_range_neg_one_pow_mul_eq V (bandCount_eq_zero (by lia))).trans
      (natCast_mul_sum_mul_natCast _ _ _ _))
  refine ⟨Q, hQ, fun i hi ↦ ?_, hzero⟩
  rw [hcoeff i hi, natCast_mul_sum_mul_natCast]

/-- The Morse inequalities bound the total dimension of homology by the number of critical
points. -/
private theorem MorseInequalities.sum_range_finrank_le {a b : ℝ} {hab : a ≤ b}
    (h : MorseInequalities I f V a b hab) (hfin : (criticalPoints I f ∩ f ⁻¹' Ioc a b).Finite)
    (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1),
        finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k) ≤
      (criticalPoints I f ∩ f ⁻¹' Ioc a b).ncard * finrank k V :=
  calc _ ≤ ∑ i ∈ Finset.range (n + 1), bandCount I f a b i * finrank k V :=
        Finset.sum_le_sum fun i _ ↦ h.finrank_le V i
    _ = (∑ i ∈ Finset.range (n + 1), bandCount I f a b i) * finrank k V := Finset.sum_mul .. |>.symm
    _ ≤ _ := Nat.mul_le_mul_right _ (sum_range_bandCount_le hfin n)

/-- The lacunary principle for a sublevel pair satisfying the Morse inequalities. -/
private theorem MorseInequalities.finrank_eq_of_eq_zero_or {a b : ℝ} {hab : a ≤ b}
    (h : MorseInequalities I f V a b hab)
    (hc : ∀ i, bandCount I f a b i = 0 ∨ bandCount I f a b (i + 1) = 0) (n : ℕ) :
    finrank k ((sublevelPair f hab).singularHomology V n : ModuleCat k) =
      bandCount I f a b n * finrank k V :=
  congrFun (eq_of_forall_sum_range_neg_one_pow_mul_le
    (b := fun i ↦ finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k))
    (c := fun i ↦ bandCount I f a b i * finrank k V)
    (fun m ↦ (h m).2.trans_eq (natCast_mul_sum_mul_natCast _ _ _ _))
    fun i ↦ (hc i).imp (fun h ↦ by rw [h, zero_mul]) fun h ↦ by rw [h, zero_mul]) n

end MorseInequalities

variable {k : Type u} [DivisionRing k] (V : ModuleCat.{u} k) in
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
  intro n
  refine ⟨T.finite_singularHomology_totalPair V n, ?_⟩
  refine (T.sum_range_neg_one_pow_mul_finrank_singularHomology_totalPair_le V n
    (fun i _ ↦ (h₁ i).1) (fun i _ ↦ (h₂ i).1)).trans ?_
  have hsum : ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) * (bandCount I f a b i : ℤ) =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) * (bandCount I f a m i : ℤ) +
        ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) * (bandCount I f m b i : ℤ) := by
    simp only [bandCount_add (I := I) ham hmb hfin, Nat.cast_add, mul_add, Finset.sum_add_distrib]
  rw [hsum, mul_add]
  exact add_le_add (h₁ n).2 (h₂ n).2

section Manifold

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]

section RingCoeff

variable {k : Type u} [Ring k] (V : ModuleCat.{u} k)

/-- The Morse inequalities hold trivially across a compact band without critical points. -/
private theorem morseInequalities_of_forall_notMem [Nontrivial k] (hf : IsMorse I f) {a b : ℝ}
    (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∉ Icc a b) :
    MorseInequalities I f V a b hab := by
  have hzero (n : ℕ) := isZero_singularHomology_sublevelPair_of_mfderiv_ne_zero hf.contMDiff hab
    hcompact (fun x hax hxb hx ↦ hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 hx) ⟨hax, hxb⟩)
    V n
  have hfin (n : ℕ) : Module.Finite k ((sublevelPair f hab).singularHomology V n : ModuleCat k) :=
    have := ModuleCat.isZero_iff_subsingleton.1 (hzero n)
    inferInstance
  have hrank (n : ℕ) :
      finrank k ((sublevelPair f hab).singularHomology V n : ModuleCat k) = 0 :=
    have := ModuleCat.isZero_iff_subsingleton.1 (hzero n)
    finrank_zero_of_subsingleton
  have hcount (i : ℕ) : bandCount I f a b i = 0 :=
    bandCount_eq_zero_of_forall fun x hx hxab ↦ (hcrit x hx (Ioc_subset_Icc_self hxab)).elim
  intro n
  simp [hfin, hrank, hcount]

/-- Above a regular value `a`, the band pair `(f⁻¹[a, b], f⁻¹(a))` has the relative homology of the
sublevel pair `({f ≤ b}, {f ≤ a})`, through the inclusion of pairs. -/
private theorem nonempty_linearEquiv_singularHomology_bandPair (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (n : ℕ) :
    Nonempty (((bandPair f hab).singularHomology V n : ModuleCat k) ≃ₗ[k]
      ((sublevelPair f hab).singularHomology V n : ModuleCat k)) :=
  have := isIso_singularHomologyMap_bandPairInclusion hf hab hcompact ha V n
  ⟨(asIso (TopPair.singularHomologyMap (bandPairInclusion f hab) V n)).toLinearEquiv⟩

private theorem finrank_singularHomology_bandPair (hf : ContMDiff I 𝓘(ℝ) ∞ f) {a b : ℝ}
    (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (n : ℕ) :
    finrank k ((bandPair f hab).singularHomology V n : ModuleCat k) =
      finrank k ((sublevelPair f hab).singularHomology V n : ModuleCat k) :=
  (nonempty_linearEquiv_singularHomology_bandPair V hf hab hcompact ha n).some.finrank_eq

end RingCoeff

section Noetherian

/-! ### Finiteness over a noetherian ring -/

variable {k : Type u} [Ring k] [IsNoetherianRing k] (V : ModuleCat.{u} k) [Module.Finite k V]

/-- Over a noetherian ring, a pair whose homology receives an isomorphism from the homology of a
finite relative CW complex `(C, D)` has finitely generated homology. -/
private theorem finite_singularHomology_of_isIso_complexBasePair {C D : Set M}
    [Topology.RelCWComplex C D] [Topology.RelCWComplex.Finite C] {P : TopPair.{u}}
    {φ : TopPair.ofInclusion (X := TopCat.of M) (base_subset_complex (C := C)) ⟶ P} {n : ℕ}
    (hiso : IsIso (TopPair.singularHomologyMap φ V n)) :
    Module.Finite k (P.singularHomology V n : ModuleCat k) := by
  have : _root_.Finite (cell C n) := FiniteType.finite_cell n
  have h := finite_singularHomology_complexBasePair C V n
  rw [complexBasePair_eq_ofInclusion] at h
  exact Module.Finite.equiv (asIso (TopPair.singularHomologyMap φ V n)).toLinearEquiv

namespace IsMorse

/-- **Finiteness of relative homology for a band.** Let `f` be a Morse function, and `a ≤ b`
regular values with compact band `f⁻¹[a, b]`. Then the relative singular homology
`Hₙ({f ≤ b}, {f ≤ a}; V)` with coefficients in a finitely generated module `V` over a noetherian
ring is finitely generated. -/
theorem finite_singularHomology_sublevelPair (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) (n : ℕ) :
    Module.Finite k ((sublevelPair f hab).singularHomology V n : ModuleCat k) := by
  refine hf.band_induction (P := fun s t hst ↦ ∀ n,
      Module.Finite k ((sublevelPair f hst).singularHomology V n : ModuleCat k)) hab hcompact ha hb
    (fun s t hst hcompact hcrit n ↦ ?_) (fun p _ _ _ δ hδ hcompact ↦ ?_)
    (fun s m t hsm hmt _ h₁ h₂ n ↦ ?_) n
  · -- Across a band without critical points the relative homology vanishes.
    have := ModuleCat.isZero_iff_subsingleton.1
      (isZero_singularHomology_sublevelPair_of_mfderiv_ne_zero hf.contMDiff hst hcompact
        (fun x hsx hxt hx ↦ hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 hx) ⟨hsx, hxt⟩) V n)
    infer_instance
  · -- Across one critical level it is the relative homology of a finite CW pair.
    obtain ⟨ε, hε, hεδ, C, _, _, hC, -, hiso⟩ :=
      hf.exists_relCWComplex_isIso_singularHomologyMap_sublevelPair hδ hcompact
    exact ⟨ε, hε, hεδ, fun n ↦ finite_singularHomology_of_isIso_complexBasePair V (hiso V n)⟩
  · -- Along a triple of sublevels, finiteness passes through the long exact sequence.
    let T := TopTriple.ofInclusions (X := TopCat.of M) (sublevel_mono f hsm) (sublevel_mono f hmt)
    have : Module.Finite k ((TopTriple.innerPair.obj T).singularHomology V n : ModuleCat k) :=
      h₁ n
    have : Module.Finite k ((TopTriple.outerPair.obj T).singularHomology V n : ModuleCat k) :=
      h₂ n
    exact T.finite_singularHomology_totalPair V n

/-- **Finiteness of relative homology for a cobordism.** Let `f` be a Morse function, and `a ≤ b`
regular values with compact band `f⁻¹[a, b]`. Then the relative singular homology
`Hₙ(f⁻¹[a, b], f⁻¹(a); V)` of the band relative to its lower level, with coefficients in a
finitely generated module `V` over a noetherian ring, is finitely generated. -/
theorem finite_singularHomology_bandPair (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) (n : ℕ) :
    Module.Finite k ((bandPair f hab).singularHomology V n : ModuleCat k) :=
  have := hf.finite_singularHomology_sublevelPair V hab hcompact ha hb n
  Module.Finite.equiv
    (nonempty_linearEquiv_singularHomology_bandPair V hf.contMDiff hab hcompact ha n).some.symm

/-- **Finiteness of relative homology for a cobordism relative to its outgoing boundary.** Let `f`
be a Morse function, and `a ≤ b` regular values with compact band `f⁻¹[a, b]`. Then the relative
singular homology `Hₙ(f⁻¹[a, b], f⁻¹(b); V)` of the band relative to its upper level, with
coefficients in a finitely generated module `V` over a noetherian ring, is finitely generated. -/
theorem finite_singularHomology_upperBandPair (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) (n : ℕ) :
    Module.Finite k ((upperBandPair f hab).singularHomology V n : ModuleCat k) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hf.neg_band hcompact ha hb
  rw [← bandPair_neg]
  exact h₁.finite_singularHomology_bandPair V (neg_le_neg hab) h₂ h₃ h₄ n

end IsMorse

end Noetherian

variable {k : Type u} [DivisionRing k] (V : ModuleCat.{u} k) [Module.Finite k V]

namespace IsMorse

section Sublevel

/-- **The Morse inequalities across one critical level.** If the band `f⁻¹[c - δ, c + δ]` is
compact, then for some `0 < ε ≤ δ` the Morse inequalities hold for
`({f ≤ c + ε}, {f ≤ c - ε})`. -/
private theorem exists_morseInequalities_level (hf : IsMorse I f) {c δ : ℝ} (hδ : 0 < δ)
    (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ))) :
    ∃ ε, ∃ hε : 0 < ε, ε ≤ δ ∧ MorseInequalities I f V (c - ε) (c + ε) (by linarith) := by
  obtain ⟨δ', hδ', hδ'δ, hsub⟩ := hf.exists_criticalPoints_inter_preimage_Icc_subset hδ hcompact
  have hcompact' : IsCompact (f ⁻¹' Icc (c - δ') (c + δ')) :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.contMDiff.continuous)
      (preimage_mono (Icc_subset_Icc (by linarith) (by linarith)))
  obtain ⟨ε, hε, hεδ', C, _, _, hC, hcell, hiso⟩ :=
    hf.exists_relCWComplex_isIso_singularHomologyMap_sublevelPair hδ' hcompact'
  refine ⟨ε, hε, hεδ'.trans hδ'δ, fun n ↦ ?_⟩
  -- The cells of `C` are counted by the critical points on the level `c`, which are those with
  -- values in `(c - ε, c + ε]`.
  have hcount (i : ℕ) : Nat.card (cell C i) = bandCount I f (c - ε) (c + ε) i := by
    rw [Nat.card_congr (hcell i).some]
    exact natCard_eq_bandCount (by linarith) (by linarith)
      (fun x hx hxε ↦ hsub ⟨hx, Icc_subset_Icc (by linarith) (by linarith) hxε⟩) i
  -- The relative homology of the sublevel pair is that of the CW pair `(C, {f ≤ c - ε})`.
  have hrank (i : ℕ) : finrank k ((complexBasePair C).singularHomology V i : ModuleCat k) =
      finrank k ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology V i :
        ModuleCat k) := by
    rw [complexBasePair_eq_ofInclusion]
    exact (@asIso _ _ _ _ _ (hiso V i)).toLinearEquiv.finrank_eq
  refine ⟨finite_singularHomology_of_isIso_complexBasePair V (hiso V n), ?_⟩
  have h := sum_range_neg_one_pow_mul_finrank_singularHomology_complexBasePair_le C V
    (n := n) fun i _ ↦ FiniteType.finite_cell i
  simpa only [hrank, hcount] using h

/-- **The Morse inequalities across a compact band between regular values**, by induction over its
critical levels. -/
private theorem morseInequalities (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) : MorseInequalities I f V a b hab :=
  hf.band_induction hab hcompact ha hb
    (fun _ _ hst hcompact hcrit ↦ morseInequalities_of_forall_notMem V hf hst hcompact hcrit)
    (fun _ _ _ _ _ hδ hcompact ↦ hf.exists_morseInequalities_level V hδ hcompact)
    fun _ _ _ _ _ hcompact h₁ h₂ ↦ h₁.trans V
      ((hf.finite_criticalPoints_inter hcompact).subset
        (inter_subset_inter_right _ (preimage_mono Ioc_subset_Icc_self))) h₂

/-! ### Sublevel pairs -/

/-- **The weak Morse inequalities for a band.** Let `f` be a Morse function, and `a ≤ b` regular
values with compact band `f⁻¹[a, b]`. Then `Hₙ({f ≤ b}, {f ≤ a}; V)` has dimension at most `dim V`
times the number of critical points of index `n` with values in `(a, b]`. -/
theorem finrank_singularHomology_sublevelPair_le (hf : IsMorse I f) {a b : ℝ}
    (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) (n : ℕ) :
    finrank k ((sublevelPair f hab).singularHomology V n : ModuleCat k) ≤
      {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = n}.ncard *
        finrank k V :=
  (hf.morseInequalities V hab hcompact ha hb).finrank_le V n

/-- **The strong Morse inequalities for a band.** Let `f` be a Morse function, and `a ≤ b` regular
values with compact band `f⁻¹[a, b]`. Write `bᵢ` for the dimension of `Hᵢ({f ≤ b}, {f ≤ a}; V)` and
`cᵢ` for the number of critical points of index `i` with values in `(a, b]`. Then
`bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ (cₙ - cₙ₋₁ + ⋯ ± c₀) dim V`. -/
theorem sum_range_neg_one_pow_mul_finrank_singularHomology_sublevelPair_le
    (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) *
        finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k) ≤
      finrank k V * ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) *
        {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = i}.ncard :=
  (hf.morseInequalities V hab hcompact ha hb n).2

/-- **Euler's equality for a band at a degree with no critical point of index `n + 1`.** Let `f` be
a Morse function, and `a ≤ b` regular values with compact band `f⁻¹[a, b]`. If no critical point of
`f` with value in `(a, b]` has Morse index `n + 1`, then
`∑ᵢ₌₀ⁿ (-1)ⁱ bᵢ = (∑ᵢ₌₀ⁿ (-1)ⁱ cᵢ) dim V`, generalizing
`IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_sublevelPair_eq` beyond `n ≥ dim M`.
-/
theorem sum_range_neg_one_pow_mul_finrank_singularHomology_sublevelPair_eq_of_manifoldMorseIndex_ne
    (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) {n : ℕ}
    (hno : ∀ x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b, manifoldMorseIndex I f x ≠ n + 1) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k) =
      finrank k V * ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = i}.ncard :=
  (hf.morseInequalities V hab hcompact ha hb).sum_range_neg_one_pow_mul_eq V
    (bandCount_eq_zero_of_forall fun x hx hIoc ↦ hno x ⟨hx, hIoc⟩)

/-- **Euler's equality for a band.** Let `f` be a Morse function, and `a ≤ b` regular values with
compact band `f⁻¹[a, b]`. Write `bᵢ` for the dimension of `Hᵢ({f ≤ b}, {f ≤ a}; V)` and `cᵢ` for
the number of critical points of index `i` with values in `(a, b]`. Then
`∑ᵢ₌₀ⁿ (-1)ⁱ bᵢ = (∑ᵢ₌₀ⁿ (-1)ⁱ cᵢ) dim V` for every `n ≥ dim M`. -/
theorem sum_range_neg_one_pow_mul_finrank_singularHomology_sublevelPair_eq
    (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) {n : ℕ}
    (hn : finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k) =
      finrank k V * ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = i}.ncard :=
  (hf.morseInequalities V hab hcompact ha hb).sum_range_neg_one_pow_mul_eq V
    (bandCount_eq_zero (by lia))

/-- **The Morse polynomial identity for a band.** Let `f` be a Morse function, and `a ≤ b` regular
values with compact band `f⁻¹[a, b]`. Write `bᵢ` for the dimension of `Hᵢ({f ≤ b}, {f ≤ a}; V)`
and `cᵢ` for the number of critical points of index `i` with values in `(a, b]`. Then for every
`n ≥ dim M`, `∑ᵢ₌₀ⁿ cᵢ dim V · tⁱ = ∑ᵢ₌₀ⁿ bᵢ tⁱ + (1 + t) Q(t)` for a polynomial `Q` with natural
number coefficients. The coefficient of `tⁱ` in `Q` is the gap
`(cᵢ - cᵢ₋₁ + ⋯ ± c₀) dim V - (bᵢ - bᵢ₋₁ + ⋯ ± b₀)` in the `i`-th strong Morse inequality for
`i < n`, and zero for `i ≥ n`. -/
theorem exists_sum_range_monomial_sublevelPair_eq_add_mul (hf : IsMorse I f) {a b : ℝ}
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
theorem sum_range_finrank_singularHomology_sublevelPair_le (hf : IsMorse I f) {a b : ℝ}
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
theorem finrank_singularHomology_sublevelPair_eq_of_forall_ne_add_one (hf : IsMorse I f)
    {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b)
    (hind : ∀ x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b, ∀ y ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b,
      manifoldMorseIndex I f x ≠ manifoldMorseIndex I f y + 1) (n : ℕ) :
    finrank k ((sublevelPair f hab).singularHomology V n : ModuleCat k) =
      {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = n}.ncard *
        finrank k V :=
  (hf.morseInequalities V hab hcompact ha hb).finrank_eq_of_eq_zero_or V
    (bandCount_eq_zero_or hind) n

/-! ### The quotient polynomial as a sum of ranks -/

/-- Across a compact band between regular values containing at most one critical value, the
relative homology has dimension `dim V` times the number of critical points of each index. -/
private theorem finrank_singularHomology_sublevelPair_eq_bandCount (hf : IsMorse I f)
    {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b)
    (hcrit : ∀ x ∈ criticalPoints I f, ∀ y ∈ criticalPoints I f, f x ∈ Icc a b →
      f y ∈ Icc a b → f x = f y) (n : ℕ) :
    finrank k ((sublevelPair f hab).singularHomology V n : ModuleCat k) =
      bandCount I f a b n * finrank k V := by
  rw [isRegularValue_iff_notMem_image_criticalPoints] at ha hb
  by_cases h : ∃ x ∈ criticalPoints I f, f x ∈ Icc a b
  · -- The band contains exactly one critical value `f x`, in its interior.
    obtain ⟨x, hx, hxab⟩ := h
    have hac : a < f x := hxab.1.lt_of_ne fun h ↦ ha ⟨x, hx, h.symm⟩
    have hcb : f x < b := hxab.2.lt_of_ne fun h ↦ hb ⟨x, hx, h⟩
    have hcrit' (y) (hy : y ∈ criticalPoints I f) (hyab : f y ∈ Icc a b) : f y = f x :=
      hcrit y hy x hx hyab hxab
    rw [hf.finrank_singularHomology_sublevelPair_eq hac hcb hcompact hcrit' V n,
      natCard_eq_bandCount hac hcb.le hcrit' n]
  · -- The band contains no critical point, so its relative homology vanishes.
    push Not at h
    have := ModuleCat.isZero_iff_subsingleton.1
      (isZero_singularHomology_sublevelPair_of_mfderiv_ne_zero hf.contMDiff hab hcompact
        (fun x hax hxb hx ↦ h x (mem_criticalPoints_iff_mfderiv_eq_zero.2 hx) ⟨hax, hxb⟩) V n)
    rw [finrank_zero_of_subsingleton, bandCount_eq_zero_of_forall
      fun x hx hxab ↦ (h x hx (Ioc_subset_Icc_self hxab)).elim, zero_mul]

/-- **The gaps in the strong Morse inequalities are ranks of connecting maps.** Let `f` be a Morse
function and `s 0 ≤ s 1 ≤ ⋯ ≤ s (N + 1)` regular values with compact band `f⁻¹[s 0, s (N + 1)]`,
such that each band `f⁻¹[s j, s (j + 1)]` contains at most one critical value. Write `M_t` for the
sublevel `{f ≤ t}`, `bᵢ = dim Hᵢ(M_{s (N + 1)}, M_{s 0}; V)` and `cᵢ` for the number of critical
points of index `i` with values in `(s 0, s (N + 1)]`. Then the gap
`(cₙ - cₙ₋₁ + ⋯ ± c₀) dim V - (bₙ - bₙ₋₁ + ⋯ ± b₀)` in the `n`-th strong Morse inequality is the
sum over `j < N` of the ranks of the connecting maps
`Hₙ₊₁(M_{s (j + 2)}, M_{s (j + 1)}) ⟶ Hₙ(M_{s (j + 1)}, M_{s 0})` of the triples of sublevels
`(M_{s (j + 2)}, M_{s (j + 1)}, M_{s 0})`. -/
theorem sum_range_finrank_range_singularHomologyδ_sublevelPair_eq (hf : IsMorse I f)
    {s : ℕ → ℝ} (hs : Monotone s) {N : ℕ} (hcompact : IsCompact (f ⁻¹' Icc (s 0) (s (N + 1))))
    (hreg : ∀ j ≤ N + 1, IsRegularValue I 𝓘(ℝ) f (s j))
    (hcrit : ∀ j ≤ N, ∀ x ∈ criticalPoints I f, ∀ y ∈ criticalPoints I f,
      f x ∈ Icc (s j) (s (j + 1)) → f y ∈ Icc (s j) (s (j + 1)) → f x = f y) (n : ℕ) :
    (∑ j ∈ Finset.range N, finrank k (LinearMap.range
        ((TopTriple.ofInclusions (X := TopCat.of M) (sublevel_mono f (hs (Nat.zero_le (j + 1))))
          (sublevel_mono f (hs (j + 1).le_succ))).singularHomologyδ V (n + 1) n rfl).hom) : ℤ) =
      finrank k V * ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) *
          {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc (s 0) (s (N + 1)) |
            manifoldMorseIndex I f x = i}.ncard -
        ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) *
          finrank k ((sublevelPair f (hs (Nat.zero_le (N + 1)))).singularHomology V i :
            ModuleCat k) := by
  have hcompact' (j : ℕ) (hj : j ≤ N) : IsCompact (f ⁻¹' Icc (s j) (s (j + 1))) :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.contMDiff.continuous)
      (preimage_mono (Icc_subset_Icc (hs (Nat.zero_le j)) (hs (by lia))))
  have hA : Monotone fun j ↦ ({x | f x ≤ s j} : Set (TopCat.of M)) :=
    fun _ _ h ↦ sublevel_mono f (hs h)
  have hfin (j : ℕ) (hj : j ≤ N) (i : ℕ) := hf.finite_singularHomology_sublevelPair V
    (hs j.le_succ) (hcompact' j hj) (hreg j (by lia)) (hreg (j + 1) (by lia)) i
  -- Each band `f⁻¹[s j, s (j + 1)]` contributes its critical points, which add up to `cᵢ`.
  have hpieces : ∑ j ∈ Finset.range (N + 1), ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) *
      finrank k ((sublevelPair f (hs j.le_succ)).singularHomology V i : ModuleCat k) =
      finrank k V * ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) *
        bandCount I f (s 0) (s (N + 1)) i := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← sum_range_bandCount hs ((hf.finite_criticalPoints_inter hcompact).subset
      (inter_subset_inter_right _ (preimage_mono Ioc_subset_Icc_self))) i, Nat.cast_sum,
      Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj : j ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    rw [hf.finrank_singularHomology_sublevelPair_eq_bandCount V (hs j.le_succ) (hcompact' j hj)
      (hreg j (by lia)) (hreg (j + 1) (by lia)) (hcrit j hj) i]
    push_cast
    ring
  have h := hA.sum_range_finrank_range_singularHomologyδ_eq V n fun j hj i _ ↦ hfin j hj i
  linarith

/-- **The coefficients of the quotient polynomial are ranks of connecting maps.** Let `f` be a
Morse function and `s 0 ≤ s 1 ≤ ⋯ ≤ s (N + 1)` regular values with compact band
`f⁻¹[s 0, s (N + 1)]`, such that each band `f⁻¹[s j, s (j + 1)]` contains at most one critical
value. Write `M_t` for the sublevel `{f ≤ t}`, `bᵢ = dim Hᵢ(M_{s (N + 1)}, M_{s 0}; V)` and `cᵢ` for
the number of critical points of index `i` with values in `(s 0, s (N + 1)]`. If `m ≥ dim M` and
`∑ᵢ₌₀ᵐ cᵢ dim V · tⁱ = ∑ᵢ₌₀ᵐ bᵢ tⁱ + (1 + t) Q(t)`, then the coefficient of `tⁿ` in `Q` is the sum
over `j < N` of the ranks of the connecting maps
`Hₙ₊₁(M_{s (j + 2)}, M_{s (j + 1)}) ⟶ Hₙ(M_{s (j + 1)}, M_{s 0})`. Such a `Q` exists by
`TauCeti.IsMorse.exists_sum_range_monomial_sublevelPair_eq_add_mul`. -/
theorem coeff_eq_sum_range_finrank_range_singularHomologyδ_sublevelPair
    (hf : IsMorse I f) {s : ℕ → ℝ} (hs : Monotone s) {N : ℕ}
    (hcompact : IsCompact (f ⁻¹' Icc (s 0) (s (N + 1))))
    (hreg : ∀ j ≤ N + 1, IsRegularValue I 𝓘(ℝ) f (s j))
    (hcrit : ∀ j ≤ N, ∀ x ∈ criticalPoints I f, ∀ y ∈ criticalPoints I f,
      f x ∈ Icc (s j) (s (j + 1)) → f y ∈ Icc (s j) (s (j + 1)) → f x = f y)
    {m : ℕ} (hm : finrank ℝ E ≤ m) {Q : ℕ[X]}
    (hQ : ∑ i ∈ Finset.range (m + 1), monomial i
          ({x ∈ criticalPoints I f ∩ f ⁻¹' Ioc (s 0) (s (N + 1)) |
            manifoldMorseIndex I f x = i}.ncard * finrank k V) =
        ∑ i ∈ Finset.range (m + 1), monomial i
          (finrank k ((sublevelPair f (hs (Nat.zero_le (N + 1)))).singularHomology V i :
            ModuleCat k)) + (1 + X) * Q) (n : ℕ) :
    Q.coeff n = ∑ j ∈ Finset.range N, finrank k (LinearMap.range
      ((TopTriple.ofInclusions (X := TopCat.of M) (sublevel_mono f (hs (Nat.zero_le (j + 1))))
        (sublevel_mono f (hs (j + 1).le_succ))).singularHomologyδ V (n + 1) n rfl).hom) := by
  -- Above the dimension of `M` there are no critical points, and hence no homology.
  have hbc (i : ℕ) (hi : m < i) :
      finrank k ((sublevelPair f (hs (Nat.zero_le (N + 1)))).singularHomology V i :
        ModuleCat k) =
      {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc (s 0) (s (N + 1)) |
        manifoldMorseIndex I f x = i}.ncard * finrank k V := by
    have hc : bandCount I f (s 0) (s (N + 1)) i = 0 := bandCount_eq_zero (by lia)
    have hb := hf.finrank_singularHomology_sublevelPair_le V (hs (Nat.zero_le (N + 1))) hcompact
      (hreg 0 (Nat.zero_le _)) (hreg (N + 1) le_rfl) i
    simp only [bandCount] at hc
    rw [hc, zero_mul] at hb ⊢
    exact Nat.le_zero.1 hb
  have h := Polynomial.coeff_eq_sum_range_neg_one_pow_mul_sub hQ hbc n
  rw [← natCast_mul_sum_mul_natCast,
    ← hf.sum_range_finrank_range_singularHomologyδ_sublevelPair_eq V hs hcompact hreg hcrit n] at h
  exact_mod_cast h

end Sublevel

section BandPair

/-! ### The cobordism relative to its incoming boundary -/

/-- **The weak Morse inequalities for a cobordism.** Let `f` be a Morse function, and `a ≤ b`
regular values with compact band `f⁻¹[a, b]`. Then `Hₙ(f⁻¹[a, b], f⁻¹(a); V)` has dimension at
most `dim V` times the number of critical points of index `n` with values in `(a, b]`. -/
theorem finrank_singularHomology_bandPair_le (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b)
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
theorem sum_range_neg_one_pow_mul_finrank_singularHomology_bandPair_le
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
theorem sum_range_neg_one_pow_mul_finrank_singularHomology_bandPair_eq
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
theorem exists_sum_range_monomial_bandPair_eq_add_mul (hf : IsMorse I f) {a b : ℝ}
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

end BandPair

section UpperBand

/-! ### The cobordism relative to its outgoing boundary

The band of `-f` between `-b` and `-a` is the band of `f` relative to its upper level
(`TauCeti.bandPair_neg`), and the critical points of index `i` of `-f` are those of index
`dim M - i` of `f`. So the statements for the band pair of `-f` give the Morse inequalities for the
upper band pair `(f⁻¹[a, b], f⁻¹(b))`, with the critical points counted by their complementary
index. -/

/-- **The weak Morse inequalities for a cobordism relative to its outgoing boundary.** Let `f` be
a Morse function on a manifold of dimension `m`, and `a ≤ b` regular values with compact band
`f⁻¹[a, b]`. Then `Hₙ(f⁻¹[a, b], f⁻¹(b); V)` has dimension at most `dim V` times the number of
critical points of index `m - n` with values in `[a, b)`. -/
theorem finrank_singularHomology_upperBandPair_le (hf : IsMorse I f) {a b : ℝ}
    (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) (n : ℕ) :
    finrank k ((upperBandPair f hab).singularHomology V n : ModuleCat k) ≤
      {x ∈ criticalPoints I f ∩ f ⁻¹' Ico a b |
        manifoldMorseIndex I f x + n = finrank ℝ E}.ncard * finrank k V := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hf.neg_band hcompact ha hb
  rw [← bandPair_neg, ← hf.setOf_neg_band_eq]
  exact h₁.finrank_singularHomology_bandPair_le V (neg_le_neg hab) h₂ h₃ h₄ n

/-- **The strong Morse inequalities for a cobordism relative to its outgoing boundary.** Let `f`
be a Morse function on a manifold of dimension `m`, and `a ≤ b` regular values with compact band
`f⁻¹[a, b]`. Write `bᵢ` for the dimension of `Hᵢ(f⁻¹[a, b], f⁻¹(b); V)` and `cᵢ` for the number of
critical points of index `m - i` with values in `[a, b)`. Then
`bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ (cₙ - cₙ₋₁ + ⋯ ± c₀) dim V`. -/
theorem sum_range_neg_one_pow_mul_finrank_singularHomology_upperBandPair_le
    (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) *
        finrank k ((upperBandPair f hab).singularHomology V i : ModuleCat k) ≤
      finrank k V * ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) *
        {x ∈ criticalPoints I f ∩ f ⁻¹' Ico a b |
          manifoldMorseIndex I f x + i = finrank ℝ E}.ncard := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hf.neg_band hcompact ha hb
  rw [← bandPair_neg]
  simpa only [hf.setOf_neg_band_eq] using
    h₁.sum_range_neg_one_pow_mul_finrank_singularHomology_bandPair_le V (neg_le_neg hab) h₂ h₃ h₄ n

/-- **Euler's equality for a cobordism relative to its outgoing boundary.** Let `f` be a Morse
function on a manifold of dimension `m`, and `a ≤ b` regular values with compact band `f⁻¹[a, b]`.
Write `bᵢ` for the dimension of `Hᵢ(f⁻¹[a, b], f⁻¹(b); V)` and `cᵢ` for the number of critical
points of index `m - i` with values in `[a, b)`. Then `∑ᵢ₌₀ⁿ (-1)ⁱ bᵢ = (∑ᵢ₌₀ⁿ (-1)ⁱ cᵢ) dim V` for
every `n ≥ m`. -/
theorem sum_range_neg_one_pow_mul_finrank_singularHomology_upperBandPair_eq
    (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) {n : ℕ}
    (hn : finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        finrank k ((upperBandPair f hab).singularHomology V i : ModuleCat k) =
      finrank k V * ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        {x ∈ criticalPoints I f ∩ f ⁻¹' Ico a b |
          manifoldMorseIndex I f x + i = finrank ℝ E}.ncard := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hf.neg_band hcompact ha hb
  rw [← bandPair_neg]
  simpa only [hf.setOf_neg_band_eq] using
    h₁.sum_range_neg_one_pow_mul_finrank_singularHomology_bandPair_eq V (neg_le_neg hab) h₂ h₃ h₄
      hn

/-- **The Morse polynomial identity for a cobordism relative to its outgoing boundary.** Let `f`
be a Morse function on a manifold of dimension `m`, and `a ≤ b` regular values with compact band
`f⁻¹[a, b]`. Write `bᵢ` for the dimension of `Hᵢ(f⁻¹[a, b], f⁻¹(b); V)` and `cᵢ` for the number of
critical points of index `m - i` with values in `[a, b)`. Then for every `n ≥ m`,
`∑ᵢ₌₀ⁿ cᵢ dim V · tⁱ = ∑ᵢ₌₀ⁿ bᵢ tⁱ + (1 + t) Q(t)` for a polynomial `Q` with natural number
coefficients. The coefficient of `tⁱ` in `Q` is the gap
`(cᵢ - cᵢ₋₁ + ⋯ ± c₀) dim V - (bᵢ - bᵢ₋₁ + ⋯ ± b₀)` in the `i`-th strong Morse inequality for
`i < n`, and zero for `i ≥ n`. -/
theorem exists_sum_range_monomial_upperBandPair_eq_add_mul (hf : IsMorse I f) {a b : ℝ}
    (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) {n : ℕ} (hn : finrank ℝ E ≤ n) :
    ∃ Q : ℕ[X], ∑ i ∈ Finset.range (n + 1), monomial i
          ({x ∈ criticalPoints I f ∩ f ⁻¹' Ico a b |
            manifoldMorseIndex I f x + i = finrank ℝ E}.ncard * finrank k V) =
        ∑ i ∈ Finset.range (n + 1),
          monomial i (finrank k ((upperBandPair f hab).singularHomology V i : ModuleCat k)) +
          (1 + X) * Q ∧
      (∀ i < n, (Q.coeff i : ℤ) =
        finrank k V * ∑ j ∈ Finset.range (i + 1), (-1 : ℤ) ^ (i - j) *
            {x ∈ criticalPoints I f ∩ f ⁻¹' Ico a b |
              manifoldMorseIndex I f x + j = finrank ℝ E}.ncard -
          ∑ j ∈ Finset.range (i + 1), (-1 : ℤ) ^ (i - j) *
            finrank k ((upperBandPair f hab).singularHomology V j : ModuleCat k)) ∧
      ∀ i, n ≤ i → Q.coeff i = 0 := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hf.neg_band hcompact ha hb
  rw [← bandPair_neg]
  simpa only [hf.setOf_neg_band_eq] using
    h₁.exists_sum_range_monomial_bandPair_eq_add_mul V (neg_le_neg hab) h₂ h₃ h₄ hn

/-- **Euler characteristics of a cobordism relative to its two boundaries.** Let `f` be a Morse
function on a manifold of dimension `m`, and `a ≤ b` regular values with compact band
`W = f⁻¹[a, b]`, with incoming boundary `∂₋W = f⁻¹(a)` and outgoing boundary `∂₊W = f⁻¹(b)`. Then
for every `n ≥ m`, `∑ᵢ₌₀ⁿ (-1)ⁱ dim Hᵢ(W, ∂₊W; V) = (-1)ᵐ ∑ᵢ₌₀ⁿ (-1)ⁱ dim Hᵢ(W, ∂₋W; V)`: the
Euler characteristics of `(W, ∂₊W)` and `(W, ∂₋W)` agree up to the sign `(-1)ᵐ`. -/
theorem sum_range_neg_one_pow_mul_finrank_singularHomology_upperBandPair_eq_neg_one_pow_mul
    (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) {n : ℕ}
    (hn : finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        finrank k ((upperBandPair f hab).singularHomology V i : ModuleCat k) =
      (-1) ^ finrank ℝ E * ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        finrank k ((bandPair f hab).singularHomology V i : ModuleCat k) := by
  rw [hf.sum_range_neg_one_pow_mul_finrank_singularHomology_upperBandPair_eq V hab hcompact ha hb
      hn, hf.sum_range_neg_one_pow_mul_finrank_singularHomology_bandPair_eq V hab hcompact ha hb hn,
    mul_left_comm]
  congr 1
  rw [criticalPoints_inter_preimage_Ioc_eq_Icc ha, criticalPoints_inter_preimage_Ico_eq_Icc hb]
  -- Both sums vanish above `dim M`, and reversing the index range pairs `m - i` with `i`.
  have htrunc (p : M → ℕ → Prop) (hp : ∀ x i, finrank ℝ E < i → ¬ p x i) :
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
          {x ∈ criticalPoints I f ∩ f ⁻¹' Icc a b | p x i}.ncard =
        ∑ i ∈ Finset.range (finrank ℝ E + 1), (-1 : ℤ) ^ i *
          {x ∈ criticalPoints I f ∩ f ⁻¹' Icc a b | p x i}.ncard := by
    symm
    refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hn)) fun i _ hi ↦ ?_
    have hempty : {x ∈ criticalPoints I f ∩ f ⁻¹' Icc a b | p x i} = ∅ :=
      eq_empty_iff_forall_notMem.2 fun x hx ↦ hp x i (by simpa using hi) hx.2
    rw [hempty, ncard_empty, Nat.cast_zero, mul_zero]
  rw [htrunc _ fun _ _ hlt h ↦ by omega,
    htrunc _ fun _ _ hlt ↦ (manifoldMorseIndex_le_finrank.trans_lt hlt).ne,
    Finset.mul_sum, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi : i ≤ finrank ℝ E := Nat.le_of_lt_succ (Finset.mem_range.1 hi)
  have hset : {x ∈ criticalPoints I f ∩ f ⁻¹' Icc a b |
        manifoldMorseIndex I f x + (finrank ℝ E + 1 - 1 - i) = finrank ℝ E} =
      {x ∈ criticalPoints I f ∩ f ⁻¹' Icc a b | manifoldMorseIndex I f x = i} := by
    ext x
    simp only [mem_ofPred_eq, add_tsub_cancel_right]
    exact and_congr_right fun _ ↦ by omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' hi
  have hsign : (-1 : ℤ) ^ (d + i) * (-1) ^ i = (-1) ^ d := by
    rw [← pow_add, Nat.add_assoc, pow_add, Even.neg_one_pow ⟨i, rfl⟩, mul_one]
  rw [hset, hd]
  simp only [add_tsub_cancel_right, ← mul_assoc, hsign]

end UpperBand

section Compact

/-! ### Compact manifolds -/

variable [CompactSpace M]

/-- On a compact manifold, take `a < f < b`. The Morse inequalities hold for the sublevel pair
`({f ≤ b}, {f ≤ a}) = (M, ∅)`, whose relative homology is the singular homology of `M` and whose
critical counts are those of `f`. -/
private theorem exists_morseInequalities_univ (hf : IsMorse I f) :
    ∃ a b : ℝ, ∃ hab : a ≤ b, MorseInequalities I f V a b hab ∧
      (∀ n, Nonempty (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj V).obj
        (TopCat.of M) ≅ (sublevelPair f hab).singularHomology V n)) ∧
      (∀ i, bandCount I f a b i = (criticalCount I f i).toNat) ∧ ∀ x, f x ∈ Ioc a b := by
  obtain ⟨a, b, hab, hcompact, ha, hb, hf'⟩ :=
    exists_isRegularValue_forall_mem_Ioc (I := I) hf.contMDiff.continuous
  refine ⟨a, b, hab, hf.morseInequalities V hab hcompact ha hb,
    fun n ↦ ⟨singularHomologyIsoSublevelPair hab (fun x ↦ (hf' x).1)
      (fun x ↦ (hf' x).2) V n⟩, ncard_eq_toNat_criticalCount hf', hf'⟩

/-- **Finiteness of homology.** The singular homology of a compact boundaryless manifold carrying
a Morse function, with coefficients in a finite-dimensional module `V`, is finite-dimensional in
every degree. -/
theorem finite_singularHomology (hf : IsMorse I f) (n : ℕ) :
    Module.Finite k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj V).obj
      (TopCat.of M)) := by
  obtain ⟨a, b, hab, h, he, -, -⟩ := hf.exists_morseInequalities_univ V
  have := (h n).1
  exact Module.Finite.equiv (he n).some.symm.toLinearEquiv

/-- On a compact boundaryless manifold carrying a Morse function, the singular homology with
coefficients in a finite-dimensional module `V` has rank in `ℕ∞` equal to its `finrank`. -/
theorem toENat_rank_singularHomology (hf : IsMorse I f) (n : ℕ) :
    (Module.rank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj V).obj
      (TopCat.of M))).toENat =
    finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj V).obj
      (TopCat.of M)) := by
  have := hf.finite_singularHomology V n
  rw [← finrank_eq_rank, Cardinal.toENat_nat]

/-- **The weak Morse inequalities.** For a Morse function `f` on a compact boundaryless manifold
`M`, the singular homology `Hₙ(M; V)` has dimension at most `dim V` times the number of critical
points of index `n`. -/
theorem finrank_singularHomology_le (hf : IsMorse I f) (n : ℕ) :
    finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj V).obj
        (TopCat.of M)) ≤
      (criticalCount I f n).toNat * finrank k V := by
  obtain ⟨a, b, hab, h, he, hc, -⟩ := hf.exists_morseInequalities_univ V
  rw [(he n).some.toLinearEquiv.finrank_eq, ← hc]
  exact h.finrank_le V n

/-- The singular homology of a compact boundaryless manifold carrying a Morse function has
zero finrank in degrees above the dimension of the manifold. -/
theorem finrank_singularHomology_eq_zero_of_finrank_lt (hf : IsMorse I f)
    {j : ℕ} (hj : finrank ℝ E < j) :
    finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) j).obj V).obj
      (TopCat.of M)) = 0 := by
  have h := hf.finrank_singularHomology_le V j
  simpa [criticalCount_eq_zero_of_finrank_lt hj] using h

/-- **The strong Morse inequalities.** For a Morse function `f` on a compact boundaryless manifold
`M`, write `bᵢ` for the dimension of `Hᵢ(M; V)` and `cᵢ` for the number of critical points of
index `i`. Then `bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ (cₙ - cₙ₋₁ + ⋯ ± c₀) dim V`. -/
theorem sum_range_neg_one_pow_mul_finrank_singularHomology_le (hf : IsMorse I f)
    (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) *
        finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj V).obj
          (TopCat.of M)) ≤
      finrank k V * ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) *
        (criticalCount I f i).toNat := by
  obtain ⟨a, b, hab, h, he, hc, -⟩ := hf.exists_morseInequalities_univ V
  have hr (i : ℕ) := (he i).some.toLinearEquiv.finrank_eq
  simp only [hr, ← hc]
  exact (h n).2

/-- **Euler's equality.** For a Morse function `f` on a compact boundaryless manifold `M`, write
`bᵢ` for the dimension of `Hᵢ(M; V)` and `cᵢ` for the number of critical points of index `i`.
Then `∑ᵢ₌₀ⁿ (-1)ⁱ bᵢ = (∑ᵢ₌₀ⁿ (-1)ⁱ cᵢ) dim V` for every `n ≥ dim M`. -/
theorem sum_range_neg_one_pow_mul_finrank_singularHomology_eq (hf : IsMorse I f)
    {n : ℕ} (hn : finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj V).obj
          (TopCat.of M)) =
      finrank k V * ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat := by
  obtain ⟨a, b, hab, h, he, hc, -⟩ := hf.exists_morseInequalities_univ V
  have hr (i : ℕ) := (he i).some.toLinearEquiv.finrank_eq
  simp only [hr, ← hc]
  exact h.sum_range_neg_one_pow_mul_eq V (bandCount_eq_zero (by lia))

/-- **The Morse polynomial identity.** For a Morse function `f` on a compact boundaryless manifold
`M`, write `bᵢ` for the dimension of `Hᵢ(M; V)` and `cᵢ` for the number of critical points of index
`i`. Then for every `n ≥ dim M`, `∑ᵢ₌₀ⁿ cᵢ dim V · tⁱ = ∑ᵢ₌₀ⁿ bᵢ tⁱ + (1 + t) Q(t)` for a polynomial
`Q` with natural number coefficients. The coefficient of `tⁱ` in `Q` is the gap
`(cᵢ - cᵢ₋₁ + ⋯ ± c₀) dim V - (bᵢ - bᵢ₋₁ + ⋯ ± b₀)` in the `i`-th strong Morse inequality for
`i < n`, and zero for `i ≥ n`. -/
theorem exists_sum_range_monomial_eq_add_mul (hf : IsMorse I f) {n : ℕ}
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

/-- **The gaps in the strong Morse inequalities are ranks of connecting maps.** Let `f` be a Morse
function on a compact boundaryless manifold `M`, and `s 0 ≤ s 1 ≤ ⋯ ≤ s (N + 1)` regular values with
`s 0 < f ≤ s (N + 1)` on `M`, such that each band `f⁻¹[s j, s (j + 1)]` contains at most one
critical value. Write `M_t` for the sublevel `{f ≤ t}`, so that `M_{s 0}` is empty, `bᵢ` for the
dimension of `Hᵢ(M; V)` and `cᵢ` for the number of critical points of index `i`. Then the gap
`(cₙ - cₙ₋₁ + ⋯ ± c₀) dim V - (bₙ - bₙ₋₁ + ⋯ ± b₀)` in the `n`-th strong Morse inequality is the
sum over `j < N` of the ranks of the connecting maps
`Hₙ₊₁(M_{s (j + 2)}, M_{s (j + 1)}) ⟶ Hₙ(M_{s (j + 1)}, M_{s 0})`. -/
theorem sum_range_finrank_range_singularHomologyδ_eq (hf : IsMorse I f) {s : ℕ → ℝ}
    (hs : Monotone s) {N : ℕ} (hlow : ∀ x, s 0 < f x) (hup : ∀ x, f x ≤ s (N + 1))
    (hreg : ∀ j ≤ N + 1, IsRegularValue I 𝓘(ℝ) f (s j))
    (hcrit : ∀ j ≤ N, ∀ x ∈ criticalPoints I f, ∀ y ∈ criticalPoints I f,
      f x ∈ Icc (s j) (s (j + 1)) → f y ∈ Icc (s j) (s (j + 1)) → f x = f y) (n : ℕ) :
    (∑ j ∈ Finset.range N, finrank k (LinearMap.range
        ((TopTriple.ofInclusions (X := TopCat.of M) (sublevel_mono f (hs (Nat.zero_le (j + 1))))
          (sublevel_mono f (hs (j + 1).le_succ))).singularHomologyδ V (n + 1) n rfl).hom) : ℤ) =
      finrank k V * ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) * (criticalCount I f i).toNat -
        ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) *
          finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj V).obj
            (TopCat.of M)) := by
  have hc := ncard_eq_toNat_criticalCount (I := I) fun x ↦ ⟨hlow x, hup x⟩
  have hb (i : ℕ) := (singularHomologyIsoSublevelPair (hs (Nat.zero_le (N + 1))) hlow hup V
    i).toLinearEquiv.finrank_eq
  simp only [← hc, hb]
  exact hf.sum_range_finrank_range_singularHomologyδ_sublevelPair_eq V hs
    (isClosed_Icc.preimage hf.contMDiff.continuous).isCompact hreg hcrit n

/-- **The coefficients of the quotient polynomial are ranks of connecting maps.** Let `f` be a
Morse function on a compact boundaryless manifold `M`, and `s 0 ≤ s 1 ≤ ⋯ ≤ s (N + 1)` regular
values with `s 0 < f ≤ s (N + 1)` on `M`, such that each band `f⁻¹[s j, s (j + 1)]` contains at
most one critical value. Write `M_t` for the sublevel `{f ≤ t}`, so that `M_{s 0}` is empty, `bᵢ`
for the dimension of `Hᵢ(M; V)` and `cᵢ` for the number of critical points of index `i`. If
`m ≥ dim M` and `∑ᵢ₌₀ᵐ cᵢ dim V · tⁱ = ∑ᵢ₌₀ᵐ bᵢ tⁱ + (1 + t) Q(t)`, then the coefficient of `tⁿ`
in `Q` is the sum over `j < N` of the ranks of the connecting maps
`Hₙ₊₁(M_{s (j + 2)}, M_{s (j + 1)}) ⟶ Hₙ(M_{s (j + 1)}, M_{s 0})`. Such a `Q` exists by
`TauCeti.IsMorse.exists_sum_range_monomial_eq_add_mul`. -/
theorem coeff_eq_sum_range_finrank_range_singularHomologyδ (hf : IsMorse I f)
    {s : ℕ → ℝ} (hs : Monotone s) {N : ℕ} (hlow : ∀ x, s 0 < f x) (hup : ∀ x, f x ≤ s (N + 1))
    (hreg : ∀ j ≤ N + 1, IsRegularValue I 𝓘(ℝ) f (s j))
    (hcrit : ∀ j ≤ N, ∀ x ∈ criticalPoints I f, ∀ y ∈ criticalPoints I f,
      f x ∈ Icc (s j) (s (j + 1)) → f y ∈ Icc (s j) (s (j + 1)) → f x = f y)
    {m : ℕ} (hm : finrank ℝ E ≤ m) {Q : ℕ[X]}
    (hQ : ∑ i ∈ Finset.range (m + 1), monomial i ((criticalCount I f i).toNat * finrank k V) =
        ∑ i ∈ Finset.range (m + 1), monomial i
          (finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj V).obj
            (TopCat.of M))) + (1 + X) * Q) (n : ℕ) :
    Q.coeff n = ∑ j ∈ Finset.range N, finrank k (LinearMap.range
      ((TopTriple.ofInclusions (X := TopCat.of M) (sublevel_mono f (hs (Nat.zero_le (j + 1))))
        (sublevel_mono f (hs (j + 1).le_succ))).singularHomologyδ V (n + 1) n rfl).hom) := by
  have hc := ncard_eq_toNat_criticalCount (I := I) fun x ↦ ⟨hlow x, hup x⟩
  have hb (i : ℕ) := (singularHomologyIsoSublevelPair (hs (Nat.zero_le (N + 1))) hlow hup V
    i).toLinearEquiv.finrank_eq
  simp only [← hc, hb] at hQ
  exact hf.coeff_eq_sum_range_finrank_range_singularHomologyδ_sublevelPair V hs
    (isClosed_Icc.preimage hf.contMDiff.continuous).isCompact hreg hcrit hm hQ n

/-- **The total Betti number is at most `dim V` times the number of critical points.** For a Morse
function `f` on a compact boundaryless manifold `M` and every `n`, `∑ᵢ₌₀ⁿ dim Hᵢ(M; V)` is at most
`dim V` times the number of critical points of `f`. -/
theorem sum_range_finrank_singularHomology_le (hf : IsMorse I f) (n : ℕ) :
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
theorem finrank_singularHomology_eq_of_forall_ne_add_one (hf : IsMorse I f)
    (hind : ∀ x ∈ criticalPoints I f, ∀ y ∈ criticalPoints I f,
      manifoldMorseIndex I f x ≠ manifoldMorseIndex I f y + 1) (n : ℕ) :
    finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj V).obj
        (TopCat.of M)) =
      (criticalCount I f n).toNat * finrank k V := by
  obtain ⟨a, b, hab, h, he, hc, -⟩ := hf.exists_morseInequalities_univ V
  rw [(he n).some.toLinearEquiv.finrank_eq, ← hc]
  exact h.finrank_eq_of_eq_zero_or V (bandCount_eq_zero_or fun x hx y hy ↦ hind x hx.1 y hy.1) n

end Compact

end IsMorse

end Manifold

end TauCeti
