/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.MorseInequalities
public import TauCeti.Geometry.Manifold.Morse.CWModel.Cobordism

/-!
# Relative CW models of sublevel pairs and cobordisms

Let `f` be a Morse function and `a ≤ b` regular values with compact band `f⁻¹[a, b]`, and write
`M_t = {f ≤ t}`. The relative CW model of the regular band
(`TauCeti.IsMorse.exists_relCWComplex_homotopyEquiv_sublevel`) is a space `X` with a closed
embedding `j : M_a → X`, a CW structure relative to the image of `j` with one `λ`-cell for each
critical point of index `λ` with value in `(a, b]`, and a homotopy equivalence `h : X ≃ₕ M_b` with
`h ∘ j` the inclusion `M_a ⊆ M_b`. Since `h` restricts on the base to the homeomorphism `j⁻¹`, it
identifies the relative singular homology of the CW pair `(X, j M_a)` with that of the sublevel pair
`(M_b, M_a)` (`TopPair.nonempty_singularHomology_ofInclusion_iso_of_homotopyEquiv`), and the model
is finite since the compact band has finitely many critical points
(`TauCeti.IsMorse.exists_relCWComplex_singularHomology_iso_sublevelPair`).

The same holds for the cobordism `W = f⁻¹[a, b]` relative to either of its boundary levels. Its
relative CW model over the incoming boundary `f⁻¹(a)`
(`TauCeti.IsMorse.exists_relCWComplex_homotopyEquiv_band`) has one `λ`-cell for each critical point
of index `λ` in the band and the relative homology of the band pair `(W, f⁻¹(a))`
(`TauCeti.IsMorse.exists_relCWComplex_singularHomology_iso_bandPair`). Its model over the outgoing
boundary `f⁻¹(b)` (`TauCeti.IsMorse.exists_relCWComplex_homotopyEquiv_upperBand`) has one
`(m - λ)`-cell for each such critical point, where `m` is the dimension of the manifold, and the
relative homology of the upper band pair `(W, f⁻¹(b))`
(`TauCeti.IsMorse.exists_relCWComplex_singularHomology_iso_upperBandPair`).

Applying the Morse polynomial identity for CW pairs
(`TauCeti.sum_range_monomial_natCard_cell_mul_finrank_eq`) to these models identifies the
coefficients of the quotient polynomial in `∑ᵢ cᵢ dim V · tⁱ = ∑ᵢ bᵢ tⁱ + (1 + t) Q(t)`: the
coefficient of `tⁱ` in `Q` is the rank of the relative cellular differential from degree `i + 1` to
degree `i` of the model. For the sublevel pair and the band pair, `cᵢ` counts the critical points of
index `i` with values in `(a, b]`, and `bᵢ` is the dimension of `Hᵢ(M_b, M_a; V)`, respectively of
`Hᵢ(W, f⁻¹(a); V)`
(`TauCeti.IsMorse.exists_relCWComplex_sum_range_monomial_sublevelPair_eq_add_mul` and
`TauCeti.IsMorse.exists_relCWComplex_sum_range_monomial_bandPair_eq_add_mul`). For the upper band
pair, `cᵢ` counts the critical points of index `m - i` with values in `[a, b)`, and `bᵢ` is the
dimension of `Hᵢ(W, f⁻¹(b); V)`
(`TauCeti.IsMorse.exists_relCWComplex_sum_range_monomial_upperBandPair_eq_add_mul`). These refine
the identities of `TauCeti.Geometry.Manifold.Morse.Inequalities`, where the coefficients of `Q` are
the gaps in the strong Morse inequalities.

## Main results

* `TauCeti.IsMorse.exists_relCWComplex_singularHomology_iso_sublevelPair`: the relative CW model of
  a regular band is finite and has the relative singular homology of the sublevel pair
  `(M_b, M_a)`.
* `TauCeti.IsMorse.exists_relCWComplex_singularHomology_iso_bandPair` and
  `TauCeti.IsMorse.exists_relCWComplex_singularHomology_iso_upperBandPair`: the relative CW models
  of a regular cobordism over its two boundary levels are finite and have the relative singular
  homology of the cobordism relative to that level.
* `TauCeti.IsMorse.exists_relCWComplex_sum_range_monomial_sublevelPair_eq_add_mul` and
  `IsMorse.exists_relCWComplex_sum_range_monomial_sublevelPair_eq_add_mul_of_manifoldMorseIndex_le`:
  the Morse polynomial identity of a sublevel pair with compact band (at any degree `n` with no
  critical point of index `n + 1` in `(a, b]`, and in particular for `n ≥ d` when critical indices
  are bounded by `d`), with the coefficients of the quotient polynomial the ranks of the cellular
  differentials of a relative CW model.
* `TauCeti.IsMorse.exists_relCWComplex_sum_range_monomial_bandPair_eq_add_mul` and
  `TauCeti.IsMorse.exists_relCWComplex_sum_range_monomial_upperBandPair_eq_add_mul`: the Morse
  polynomial identities of a cobordism relative to either boundary level, with the coefficients of
  the quotient polynomial the ranks of the cellular differentials of a relative CW model.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5 and Section 5.
* J. Milnor, *Lectures on the h-cobordism theorem*, Princeton University Press, 1965, Theorem 3.4.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse Theory*, lecture notes,
  Theorem 5.7 and Corollary 5.11.
-/

public section

noncomputable section

open CategoryTheory Limits Module Set Topology Topology.RelCWComplex
open Polynomial (monomial X)
open scoped ContDiff ContinuousMap Manifold Polynomial

universe u v w

namespace TauCeti.IsMorse

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] {f : M → ℝ}

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- The Morse polynomial identity read off a finite relative CW model: if the relative `m`-cells of
`(W, B)` correspond to the points of index `m` of a set `S`, and the pair has the relative
homology of `P` with coefficients in `V`, then
`∑ᵢ₌₀ⁿ cᵢ dim V · tⁱ = ∑ᵢ₌₀ⁿ dim Hᵢ(P; V) tⁱ + (1 + t) Q(t)` for every `n` such that no point of
`S` has index `n + 1`, where `cᵢ` counts the points of index `i` of `S` and the coefficient of `tⁱ`
in `Q` is the rank of the cellular differential of `(W, B)` from degree `i + 1` to degree `i`. -/
private theorem sum_range_monomial_eq_add_mul_of_relCWComplex {W : Type u} [TopologicalSpace W]
    [T2Space W] {B : Set W} [RelCWComplex (univ : Set W) B] [RelCWComplex.Finite (univ : Set W)]
    {S : Set M} (c : ∀ m, cell (univ : Set W) m ≃ ↥{x ∈ S | manifoldMorseIndex I f x = m})
    {P : TopPair.{u}} {k : Type u} [DivisionRing k] (V : ModuleCat.{u} k) [Module.Finite k V]
    (hH : ∀ i, Nonempty ((complexBasePair (univ : Set W)).singularHomology V i ≅
      P.singularHomology V i))
    {n : ℕ} (hn : ∀ x ∈ S, manifoldMorseIndex I f x ≠ n + 1) :
    ∑ i ∈ Finset.range (n + 1), monomial i
        ({x ∈ S | manifoldMorseIndex I f x = i}.ncard * finrank k V) =
      ∑ i ∈ Finset.range (n + 1), monomial i (finrank k (P.singularHomology V i : ModuleCat k)) +
        (1 + X) * ∑ i ∈ Finset.range n, monomial i (finrank k
          (LinearMap.range ((cellularChainComplex (univ : Set W) V).d (i + 1) i).hom)) := by
  -- There are finitely many relative cells, and none in degree `n + 1`.
  have hcell (i : ℕ) : Finite (cell (univ : Set W) i) := FiniteType.finite_cell i
  have hn' : IsEmpty (cell (univ : Set W) (n + 1)) :=
    (c (n + 1)).isEmpty_congr.2 ⟨fun x ↦ hn x.val x.property.1 x.property.2⟩
  have h := sum_range_monomial_natCard_cell_mul_finrank_eq (univ : Set W) V (fun i _ ↦ hcell i) hn'
  simp only [Nat.card_congr (c _), Nat.card_coe_set_eq] at h
  rw [h]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by rw [(hH i).some.toLinearEquiv.finrank_eq]

/-- **The relative CW model of a regular band computes its relative homology.** Let `f` be a Morse
function and `a ≤ b` regular values with compact band `f⁻¹[a, b]`. Then there are a space `X`, a
closed embedding `j : M_a → X` of the sublevel `M_a = {f ≤ a}`, and a finite CW structure on `X`
relative to the image of `j`, whose `m`-cells correspond to the critical points of index `m` with
values in `(a, b]`, such that the relative singular homology of this CW pair is that of the
sublevel pair `(M_b, M_a)`, for coefficients in any abelian category with coproducts. -/
theorem exists_relCWComplex_singularHomology_iso_sublevelPair (hf : IsMorse I f)
    {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (j : C({x | f x ≤ a}, X))
      (_ : RelCWComplex (univ : Set X) (range j)),
      IsClosedEmbedding j ∧ RelCWComplex.Finite (univ : Set X) ∧
      (∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = m})) ∧
      ∀ {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A) (n : ℕ),
        Nonempty ((complexBasePair (univ : Set X)).singularHomology R n ≅
          (sublevelPair f hab).singularHomology R n) := by
  obtain ⟨X, _, _, j, _, h, hj, hh, ⟨c⟩⟩ :=
    hf.exists_relCWComplex_homotopyEquiv_sublevel hab hcompact ha hb
  -- Only finitely many critical points lie in the compact band.
  have := finite_sigma_criticalPoints_inter ((hf.finite_criticalPoints_inter hcompact).subset
    (inter_subset_inter_right _ (preimage_mono Ioc_subset_Icc_self)))
  refine ⟨X, _, ‹_›, j, ‹_›, hj,
    RelCWComplex.finite_of_finite_cells (.of_equiv _ (Equiv.sigmaCongrRight c).symm),
    fun m ↦ ⟨c m⟩, fun R n ↦ ?_⟩
  rw [complexBasePair_eq_ofInclusion]
  exact TopPair.nonempty_singularHomology_ofInclusion_iso_of_homotopyEquiv _ hj.isEmbedding h hh R n

/-- **The Morse polynomial identity of a sublevel pair, with cellular coefficients.** Let `f` be a
Morse function and `a ≤ b` regular values with compact band `f⁻¹[a, b]`. Then there is a finite
relative CW complex `(W, B)` whose relative `m`-cells correspond to the critical points of index
`m` with values in `(a, b]`, such that for every finite-dimensional module `V` over a division ring
`k` and every `n` for which no critical point in `(a, b]` has index `n + 1` (in particular, every
`n ≥ dim M`), writing `cᵢ` for the number of these critical points of index `i` and
`bᵢ = dim Hᵢ(M_b, M_a; V)`, `∑ᵢ₌₀ⁿ cᵢ dim V · tⁱ = ∑ᵢ₌₀ⁿ bᵢ tⁱ + (1 + t) Q(t)`, where the
coefficient of `tⁱ` in `Q` is the rank of the cellular differential of `(W, B)` with coefficients in
`V` from degree `i + 1` to degree `i`. -/
theorem exists_relCWComplex_sum_range_monomial_sublevelPair_eq_add_mul (hf : IsMorse I f)
    {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : T2Space W) (B : Set W)
      (_ : RelCWComplex (univ : Set W) B),
      RelCWComplex.Finite (univ : Set W) ∧
      (∀ m, Nonempty (cell (univ : Set W) m ≃
        ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = m})) ∧
      ∀ {k : Type u} [DivisionRing k] (V : ModuleCat.{u} k) [Module.Finite k V] {n : ℕ},
        (∀ x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b, manifoldMorseIndex I f x ≠ n + 1) →
        ∑ i ∈ Finset.range (n + 1), monomial i
            ({x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = i}.ncard *
              finrank k V) =
          ∑ i ∈ Finset.range (n + 1),
            monomial i (finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k)) +
            (1 + X) * ∑ i ∈ Finset.range n, monomial i (finrank k
              (LinearMap.range ((cellularChainComplex (univ : Set W) V).d (i + 1) i).hom)) := by
  obtain ⟨W, instTop, instT2, j, instCW, -, hfin, c, hH⟩ :=
    hf.exists_relCWComplex_singularHomology_iso_sublevelPair hab hcompact ha hb
  refine ⟨W, _, ‹_›, range j, ‹_›, hfin, c, fun V _ n hno ↦ ?_⟩
  exact sum_range_monomial_eq_add_mul_of_relCWComplex (S := criticalPoints I f ∩ f ⁻¹' Ioc a b)
    (P := sublevelPair f hab) (fun m ↦ (c m).some) V (hH V) hno

/-- **The relative CW model of a regular cobordism computes its relative homology.** Let `f` be a
Morse function and `a ≤ b` regular values with compact band `f⁻¹[a, b]`. Then there are a space
`X`, a closed embedding `j : f⁻¹(a) → X` of the incoming boundary, and a finite CW structure on
`X` relative to the image of `j`, whose `m`-cells correspond to the critical points of index `m`
with values in `(a, b]`, such that the relative singular homology of this CW pair is that of the
band pair `(f⁻¹[a, b], f⁻¹(a))`, for coefficients in any abelian category with coproducts. -/
theorem exists_relCWComplex_singularHomology_iso_bandPair (hf : IsMorse I f)
    {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (j : C(f ⁻¹' {a}, X))
      (_ : RelCWComplex (univ : Set X) (range j)),
      IsClosedEmbedding j ∧ RelCWComplex.Finite (univ : Set X) ∧
      (∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = m})) ∧
      ∀ {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A) (n : ℕ),
        Nonempty ((complexBasePair (univ : Set X)).singularHomology R n ≅
          (bandPair f hab).singularHomology R n) := by
  obtain ⟨X, _, _, j, _, h, hj, hfin, hh, ⟨c⟩⟩ :=
    hf.exists_relCWComplex_homotopyEquiv_band hab hcompact ha hb
  refine ⟨X, _, ‹_›, j, ‹_›, hj, hfin, fun m ↦ ⟨c m⟩, fun R n ↦ ?_⟩
  rw [complexBasePair_eq_ofInclusion]
  exact TopPair.nonempty_singularHomology_ofInclusion_iso_of_homotopyEquiv _ hj.isEmbedding h hh R n

/-- **The relative CW model of a regular cobordism over its outgoing boundary computes its
relative homology.** Let `f` be a Morse function on a manifold of dimension `m`, and `a ≤ b`
regular values with compact band `f⁻¹[a, b]`. Then there are a space `X`, a closed embedding
`j : f⁻¹(b) → X` of the outgoing boundary, and a finite CW structure on `X` relative to the image of
`j`, whose `i`-cells correspond to the critical points of index `m - i` with values in `[a, b)`,
such that the relative singular homology of this CW pair is that of the upper band pair
`(f⁻¹[a, b], f⁻¹(b))`, for coefficients in any abelian category with coproducts. -/
theorem exists_relCWComplex_singularHomology_iso_upperBandPair (hf : IsMorse I f)
    {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (j : C(f ⁻¹' {b}, X))
      (_ : RelCWComplex (univ : Set X) (range j)),
      IsClosedEmbedding j ∧ RelCWComplex.Finite (univ : Set X) ∧
      (∀ i, Nonempty (cell (univ : Set X) i ≃ ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ico a b |
        manifoldMorseIndex I f x + i = finrank ℝ E})) ∧
      ∀ {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A) (n : ℕ),
        Nonempty ((complexBasePair (univ : Set X)).singularHomology R n ≅
          (upperBandPair f hab).singularHomology R n) := by
  obtain ⟨X, _, _, j, _, h, hj, hfin, hh, ⟨c⟩⟩ :=
    hf.exists_relCWComplex_homotopyEquiv_upperBand hab hcompact ha hb
  refine ⟨X, _, ‹_›, j, ‹_›, hj, hfin, fun i ↦ ⟨c i⟩, fun R n ↦ ?_⟩
  rw [complexBasePair_eq_ofInclusion]
  exact TopPair.nonempty_singularHomology_ofInclusion_iso_of_homotopyEquiv _ hj.isEmbedding h hh R n

/-- **The Morse polynomial identity of a cobordism, with cellular coefficients.** Let `f` be a
Morse function and `a ≤ b` regular values with compact band `f⁻¹[a, b]`. Then there is a finite
relative CW complex `(W, B)` whose relative `m`-cells correspond to the critical points of index `m`
with values in `(a, b]`, such that for every finite-dimensional module `V` over a division ring `k`
and every `n ≥ dim M`, writing `cᵢ` for the number of these critical points of index `i` and
`bᵢ = dim Hᵢ(f⁻¹[a, b], f⁻¹(a); V)`, `∑ᵢ₌₀ⁿ cᵢ dim V · tⁱ = ∑ᵢ₌₀ⁿ bᵢ tⁱ + (1 + t) Q(t)`, where the
coefficient of `tⁱ` in `Q` is the rank of the cellular differential of `(W, B)` with coefficients
in `V` from degree `i + 1` to degree `i`. -/
theorem exists_relCWComplex_sum_range_monomial_bandPair_eq_add_mul (hf : IsMorse I f)
    {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : T2Space W) (B : Set W)
      (_ : RelCWComplex (univ : Set W) B),
      RelCWComplex.Finite (univ : Set W) ∧
      (∀ m, Nonempty (cell (univ : Set W) m ≃
        ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = m})) ∧
      ∀ {k : Type u} [DivisionRing k] (V : ModuleCat.{u} k) [Module.Finite k V] {n : ℕ},
        finrank ℝ E ≤ n →
        ∑ i ∈ Finset.range (n + 1), monomial i
            ({x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = i}.ncard *
              finrank k V) =
          ∑ i ∈ Finset.range (n + 1),
            monomial i (finrank k ((bandPair f hab).singularHomology V i : ModuleCat k)) +
            (1 + X) * ∑ i ∈ Finset.range n, monomial i (finrank k
              (LinearMap.range ((cellularChainComplex (univ : Set W) V).d (i + 1) i).hom)) := by
  obtain ⟨W, _, _, j, _, -, hfin, c, hH⟩ :=
    hf.exists_relCWComplex_singularHomology_iso_bandPair hab hcompact ha hb
  refine ⟨W, _, ‹_›, range j, ‹_›, hfin, c, fun V _ n hn ↦ ?_⟩
  exact sum_range_monomial_eq_add_mul_of_relCWComplex (S := criticalPoints I f ∩ f ⁻¹' Ioc a b)
    (P := bandPair f hab) (fun m ↦ (c m).some) V (hH V) fun x _ ↦ by
      have := manifoldMorseIndex_le_finrank (I := I) (f := f) (x := x)
      lia

/-- **The Morse polynomial identity of a cobordism relative to its outgoing boundary, with
cellular coefficients.** Let `f` be a Morse function on a manifold of dimension `m`, and `a ≤ b`
regular values with compact band `f⁻¹[a, b]`. Then there is a finite relative CW complex `(W, B)`
whose relative `i`-cells correspond to the critical points of index `m - i` with values in
`[a, b)`, such that for every finite-dimensional module `V` over a division ring `k` and every
`n ≥ m`, writing `cᵢ` for the number of these critical points of index `m - i` and
`bᵢ = dim Hᵢ(f⁻¹[a, b], f⁻¹(b); V)`, `∑ᵢ₌₀ⁿ cᵢ dim V · tⁱ = ∑ᵢ₌₀ⁿ bᵢ tⁱ + (1 + t) Q(t)`, where the
coefficient of `tⁱ` in `Q` is the rank of the cellular differential of `(W, B)` with coefficients
in `V` from degree `i + 1` to degree `i`. -/
theorem exists_relCWComplex_sum_range_monomial_upperBandPair_eq_add_mul
    (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : T2Space W) (B : Set W)
      (_ : RelCWComplex (univ : Set W) B),
      RelCWComplex.Finite (univ : Set W) ∧
      (∀ i, Nonempty (cell (univ : Set W) i ≃ ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ico a b |
        manifoldMorseIndex I f x + i = finrank ℝ E})) ∧
      ∀ {k : Type u} [DivisionRing k] (V : ModuleCat.{u} k) [Module.Finite k V] {n : ℕ},
        finrank ℝ E ≤ n →
        ∑ i ∈ Finset.range (n + 1), monomial i
            ({x ∈ criticalPoints I f ∩ f ⁻¹' Ico a b |
              manifoldMorseIndex I f x + i = finrank ℝ E}.ncard * finrank k V) =
          ∑ i ∈ Finset.range (n + 1),
            monomial i (finrank k ((upperBandPair f hab).singularHomology V i : ModuleCat k)) +
            (1 + X) * ∑ i ∈ Finset.range n, monomial i (finrank k
              (LinearMap.range ((cellularChainComplex (univ : Set W) V).d (i + 1) i).hom)) := by
  -- This is the identity of the band pair of `-f` over `[-b, -a]`, which is the upper band pair of
  -- `f`, and whose critical points of index `i` are those of `f` of index `m - i`.
  obtain ⟨W, _, _, B, _, hfin, c, hQ⟩ :=
    hf.neg.exists_relCWComplex_sum_range_monomial_bandPair_eq_add_mul (neg_le_neg hab)
      (by rwa [preimage_neg_Icc_neg]) (isRegularValue_neg_iff.2 (by rwa [neg_neg]))
      (isRegularValue_neg_iff.2 (by rwa [neg_neg]))
  refine ⟨W, _, ‹_›, B, ‹_›, hfin,
    fun i ↦ ⟨(c i).some.trans (Set.equivOfEq (hf.setOf_neg_band_eq a b i))⟩, fun V _ n hn ↦ ?_⟩
  rw [← bandPair_neg]
  simpa only [hf.setOf_neg_band_eq] using hQ V hn

/-- **Index-bounded Morse polynomial identity of a sublevel pair, with cellular coefficients.** Let
`f` be a Morse function and `a ≤ b` regular values with compact band `f⁻¹[a, b]`, such that every
critical point of `f` with value in `(a, b]` has Morse index at most `d`. Then there is a finite
relative CW complex `(W, B)` with no relative cells above dimension `d`, whose relative `m`-cells
correspond to the critical points of index `m` in `(a, b]`, such that for every finite-dimensional
module `V` over a division ring `k` and every `n ≥ d`, writing `cᵢ` for the number of these critical
points of index `i` and `bᵢ = dim Hᵢ(M_b, M_a; V)`,
`∑ᵢ₌₀ⁿ cᵢ dim V · tⁱ = ∑ᵢ₌₀ⁿ bᵢ tⁱ + (1 + t) Q(t)`, where the coefficient of `tⁱ` in `Q` is the
rank of the cellular differential of `(W, B)` with coefficients in `V` from degree `i + 1` to
degree `i`. -/
theorem exists_relCWComplex_sum_range_monomial_sublevelPair_eq_add_mul_of_manifoldMorseIndex_le
    (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) {d : ℕ}
    (hidx : ∀ x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b, manifoldMorseIndex I f x ≤ d) :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : T2Space W) (B : Set W)
      (_ : RelCWComplex (univ : Set W) B),
      RelCWComplex.Finite (univ : Set W) ∧
      (∀ m, Nonempty (cell (univ : Set W) m ≃
        ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = m})) ∧
      (∀ m, d < m → IsEmpty (cell (univ : Set W) m)) ∧
      ∀ {k : Type u} [DivisionRing k] (V : ModuleCat.{u} k) [Module.Finite k V] {n : ℕ},
        d ≤ n →
        ∑ i ∈ Finset.range (n + 1), monomial i
            ({x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = i}.ncard *
              finrank k V) =
          ∑ i ∈ Finset.range (n + 1),
            monomial i (finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k)) +
            (1 + X) * ∑ i ∈ Finset.range n, monomial i (finrank k
              (LinearMap.range ((cellularChainComplex (univ : Set W) V).d (i + 1) i).hom)) := by
  obtain ⟨W, instTop, instT2, B, instCW, hfin, c, hpoly⟩ :=
    hf.exists_relCWComplex_sum_range_monomial_sublevelPair_eq_add_mul hab hcompact ha hb
  exact ⟨W, instTop, instT2, B, instCW, hfin, c,
    fun m hm ↦ (c m).some.isEmpty_congr.2 ⟨fun x ↦
        ((x.property.2 ▸ hidx x.val x.property.1).trans_lt hm).false⟩,
    fun {k} _ V _ {n} hn ↦ hpoly V fun x hx ↦ ((hidx x hx).trans_lt (Nat.lt_succ_of_le hn)).ne⟩

end TauCeti.IsMorse
