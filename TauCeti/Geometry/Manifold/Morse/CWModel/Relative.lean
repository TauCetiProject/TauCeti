/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.MorseInequalities
public import TauCeti.Geometry.Manifold.Morse.CWModel

/-!
# Relative CW models of sublevel pairs

Let `f` be a Morse function and `a ≤ b` regular values with compact band `f⁻¹[a, b]`, and write
`M_t = {f ≤ t}`. The relative CW model of the regular band
(`TauCeti.IsMorse.exists_relCWComplex_homotopyEquiv_sublevel`) is a space `X` with a closed
embedding `j : M_a → X`, a CW structure relative to the image of `j` with one `λ`-cell for each
critical point of index `λ` with value in `(a, b]`, and a homotopy equivalence `h : X ≃ₕ M_b` with
`h ∘ j` the inclusion `M_a ⊆ M_b`. Since `h` restricts on the base to the homeomorphism `j⁻¹`, it
identifies the relative singular homology of the CW pair `(X, j M_a)` with that of the sublevel pair
`(M_b, M_a)`, and the model is finite since the compact band has finitely many critical points
(`TauCeti.IsMorse.exists_relCWComplex_singularHomology_iso_sublevelPair`).

Applying the Morse polynomial identity for CW pairs
(`TauCeti.sum_range_monomial_natCard_cell_mul_finrank_eq`) to this model identifies the coefficients
of the quotient polynomial in `∑ᵢ cᵢ dim V · tⁱ = ∑ᵢ bᵢ tⁱ + (1 + t) Q(t)`, where `cᵢ` counts the
critical points of index `i` with values in `(a, b]` and `bᵢ = dim Hᵢ(M_b, M_a; V)`: the coefficient
of `tⁱ` in `Q` is the rank of the relative cellular differential from degree `i + 1` to degree `i`
of the model (`TauCeti.IsMorse.exists_relCWComplex_sum_range_monomial_sublevelPair_eq_add_mul`).

## Main results

* `TauCeti.IsMorse.exists_relCWComplex_singularHomology_iso_sublevelPair`: the relative CW model of
  a regular band is finite and has the relative singular homology of the sublevel pair
  `(M_b, M_a)`.
* `TauCeti.IsMorse.exists_relCWComplex_sum_range_monomial_sublevelPair_eq_add_mul`: the Morse
  polynomial identity of a sublevel pair with compact band, with the coefficients of the quotient
  polynomial the ranks of the cellular differentials of a relative CW model.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5 and Section 5.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse Theory*, lecture notes,
  Theorem 5.7 and Corollary 5.11.
-/

public section

noncomputable section

open CategoryTheory Limits Module Set Topology Topology.RelCWComplex
open Polynomial (monomial X)
open scoped ContDiff ContinuousMap Manifold Polynomial

universe u v w

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] {f : M → ℝ}

/-- **The relative CW model of a regular band computes its relative homology.** Let `f` be a Morse
function and `a ≤ b` regular values with compact band `f⁻¹[a, b]`. Then there are a space `X`, a
closed embedding `j : M_a → X` of the sublevel `M_a = {f ≤ a}`, and a finite CW structure on `X`
relative to the image of `j`, whose `m`-cells correspond to the critical points of index `m` with
values in `(a, b]`, such that the relative singular homology of this CW pair is that of the
sublevel pair `(M_b, M_a)`, for coefficients in any abelian category with coproducts. -/
theorem IsMorse.exists_relCWComplex_singularHomology_iso_sublevelPair (hf : IsMorse I f)
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
  -- On the total spaces the map of pairs is `h`, and on the subspaces it is `j⁻¹`.
  let φ := TopPair.ofInclusionMap (X := TopCat.of X) (Y := TopCat.of M) (subset_univ (range j))
    (sublevel_mono f hab) (h.toFun.restrict univ) fun x ⟨w, hw⟩ ↦ by
      simp [← hw, hh]
  have := TopPair.isIso_singularHomologyMap_of_homotopyEquiv φ
    ((Homeomorph.Set.univ X).toHomotopyEquiv.trans h)
    hj.isEmbedding.toHomeomorph.symm.toHomotopyEquiv
    (by ext x; exact TopPair.ofInclusionMap_fst_apply _ _ x)
    (by
      ext ⟨_, w, rfl⟩
      refine Subtype.ext ((TopPair.ofInclusionMap_snd_apply _ _ _).trans ((hh w).trans ?_))
      exact congrArg Subtype.val (hj.isEmbedding.toHomeomorph_symm_apply w).symm) R n
  exact ⟨asIso (TopPair.singularHomologyMap φ R n)⟩

/-- **The Morse polynomial identity of a sublevel pair, with cellular coefficients.** Let `f` be a
Morse function and `a ≤ b` regular values with compact band `f⁻¹[a, b]`. Then there is a
finite relative CW complex `(W, B)` whose relative `m`-cells correspond to the critical points of
index `m` with values in `(a, b]`, such that for every finite-dimensional module `V` over a division
ring `k` and every `n ≥ dim M`, writing `cᵢ` for the number of these critical points of index `i`
and `bᵢ = dim Hᵢ(M_b, M_a; V)`,
`∑ᵢ₌₀ⁿ cᵢ dim V · tⁱ = ∑ᵢ₌₀ⁿ bᵢ tⁱ + (1 + t) Q(t)`, where the coefficient of `tⁱ` in `Q` is the rank
of the cellular differential of `(W, B)` with coefficients in `V` from degree `i + 1` to degree `i`.
-/
theorem IsMorse.exists_relCWComplex_sum_range_monomial_sublevelPair_eq_add_mul (hf : IsMorse I f)
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
            monomial i (finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k)) +
            (1 + X) * ∑ i ∈ Finset.range n, monomial i (finrank k
              (LinearMap.range ((cellularChainComplex (univ : Set W) V).d (i + 1) i).hom)) := by
  obtain ⟨W, _, _, j, _, -, hfin, c, hH⟩ :=
    hf.exists_relCWComplex_singularHomology_iso_sublevelPair hab hcompact ha hb
  refine ⟨W, _, ‹_›, range j, ‹_›, hfin, c, fun V _ n hn ↦ ?_⟩
  -- There are finitely many relative cells, and none above the dimension of `M`.
  have hcell (i : ℕ) : Finite (cell (univ : Set W) i) := FiniteType.finite_cell i
  have hn' : IsEmpty (cell (univ : Set W) (n + 1)) :=
    (c (n + 1)).some.isEmpty_congr.2 ⟨fun x ↦ by
      have := x.2.2 ▸ manifoldMorseIndex_le_finrank (I := I) (f := f) (x := x.1)
      lia⟩
  have h := sum_range_monomial_natCard_cell_mul_finrank_eq (univ : Set W) V (fun i _ ↦ hcell i) hn'
  simp only [Nat.card_congr (c _).some, Nat.card_coe_set_eq] at h
  rw [h]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by rw [(hH V i).some.toLinearEquiv.finrank_eq]

end TauCeti
