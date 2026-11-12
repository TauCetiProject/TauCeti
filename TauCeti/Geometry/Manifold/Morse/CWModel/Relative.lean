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

A compact sublevel `M_a` at a regular value has a finite CW model, with one `λ`-cell for each
critical point of index `λ` in it
(`TauCeti.IsMorse.exists_cwComplex_homotopyEquiv_sublevel_of_isCompact`):
below the minimum of `f` on `M_a` the sublevel is empty. This applies on a compact manifold and for
a proper function.

## Main results

* `TauCeti.IsMorse.exists_relCWComplex_singularHomology_iso_sublevelPair`: the relative CW model of
  a regular band is finite and has the relative singular homology of the sublevel pair
  `(M_b, M_a)`.
* `TauCeti.IsMorse.exists_relCWComplex_sum_range_monomial_sublevelPair_eq_add_mul`: the Morse
  polynomial identity of a sublevel pair with compact band, with the coefficients of the quotient
  polynomial the ranks of the cellular differentials of a relative CW model.
* `TauCeti.IsMorse.exists_cwComplex_homotopyEquiv_sublevel_of_isCompact`: a compact regular
  sublevel has a finite CW model with one cell for each critical point.

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

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- If only finitely many critical points lie in `S`, then only finitely many pairs of an index `m`
and a critical point of index `m` in `S` exist. -/
private theorem finite_sigma_criticalPoints_inter {S : Set M}
    (hS : (criticalPoints I f ∩ S).Finite) :
    Finite (Σ m, ↥{x ∈ criticalPoints I f ∩ S | manifoldMorseIndex I f x = m}) :=
  have := hS.to_subtype
  .of_injective (fun x ↦ (⟨x.2, x.2.2.1⟩ : ↥(criticalPoints I f ∩ S)))
    fun ⟨_, _, hx⟩ ⟨_, _, hy⟩ hxy ↦ by
      cases Subtype.ext_iff.1 hxy
      cases hx.2.symm.trans hy.2
      rfl

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- Homotopy equivalences `h : W ≃ₕ M_a` and `h' : W' ≃ₕ M_b` with `h' ∘ ι = h`, for a closed
embedding `ι : W → W'`, induce isomorphisms `Hₙ(W', ι W) ≅ Hₙ(M_b, M_a)`. -/
private theorem nonempty_singularHomology_ofInclusion_iso_sublevelPair {a b : ℝ} (hab : a ≤ b)
    {W W' : Type u} [TopologicalSpace W] [TopologicalSpace W'] {ι : C(W, W')}
    (hι : IsClosedEmbedding ι) {S : Set W'} (hS : range ι = S) (h : W ≃ₕ {x | f x ≤ a})
    (h' : W' ≃ₕ {x | f x ≤ b}) (hh : ∀ w, (h' (ι w) : M) = h w) {A : Type v} [Category.{w} A]
    [HasCoproducts.{u} A] [Abelian A] (R : A) (n : ℕ) :
    Nonempty ((TopPair.ofInclusion (X := TopCat.of W') (subset_univ S)).singularHomology R n ≅
      (sublevelPair f hab).singularHomology R n) := by
  subst hS
  let φ := TopPair.ofInclusionMap (X := TopCat.of W') (Y := TopCat.of M) (subset_univ (range ι))
    (sublevel_mono f hab) (h'.toFun.restrict univ) fun x ⟨w, hw⟩ ↦ by
      simp [← hw, hh]
  -- On the total spaces `φ` is `h'`, and on the subspaces it is `h` read through `ι`.
  let e₁ : ↥(univ : Set W') ≃ₕ {x | f x ≤ b} := (Homeomorph.Set.univ W').toHomotopyEquiv.trans h'
  let e₂ : ↥(range ι) ≃ₕ {x | f x ≤ a} := hι.isEmbedding.toHomeomorph.symm.toHomotopyEquiv.trans h
  have hfst (m : ℕ) : IsIso (SSet.homologyMap (TopCat.toSSet.map (TopPair.Hom.fst φ)) R m) := by
    have hφ : TopPair.Hom.fst φ = TopCat.ofHom e₁.toFun := by
      ext x
      exact TopPair.ofInclusionMap_fst_apply _ _ x
    have := (e₁.singularHomologyIso R m).isIso_hom
    rw [ContinuousMap.HomotopyEquiv.singularHomologyIso_hom, ← hφ] at this
    exact this
  have hsnd (m : ℕ) : IsIso (SSet.homologyMap (TopCat.toSSet.map (TopPair.Hom.snd φ)) R m) := by
    have hφ : TopPair.Hom.snd φ = TopCat.ofHom e₂.toFun := by
      ext ⟨_, w, rfl⟩
      refine Subtype.ext ((TopPair.ofInclusionMap_snd_apply _ _ _).trans ((hh w).trans ?_))
      -- Unfolding `TopCat.ofHom` and `HomotopyEquiv.trans`, `e₂` sends `ι w` to `h (ι⁻¹ (ι w))`.
      exact congrArg (fun x ↦ (h.toFun x : M)) (hι.isEmbedding.toHomeomorph_symm_apply w).symm
    have := (e₂.singularHomologyIso R m).isIso_hom
    rw [ContinuousMap.HomotopyEquiv.singularHomologyIso_hom, ← hφ] at this
    exact this
  have := TopPair.isIso_singularHomologyMap_of_isIso R φ n (hfst n) (hsnd n) (fun m _ ↦ hfst m)
    fun m _ ↦ hsnd m
  exact ⟨asIso (TopPair.singularHomologyMap φ R n)⟩

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
      RelCWComplex.Finite (univ : Set X) ∧
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
  refine ⟨X, _, ‹_›, j, ‹_›,
    RelCWComplex.finite_of_finite_cells (.of_equiv _ (Equiv.sigmaCongrRight c).symm),
    fun m ↦ ⟨c m⟩, fun R n ↦ ?_⟩
  rw [complexBasePair_eq_ofInclusion]
  exact nonempty_singularHomology_ofInclusion_iso_sublevelPair hab hj rfl
    (.refl _) h hh R n

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
  obtain ⟨W, _, _, j, _, hfin, c, hH⟩ :=
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

/-- **CW models of compact sublevels.** Let `f` be a Morse function and `a` a regular value with
compact sublevel `M_a = {f ≤ a}`. Then `M_a` is homotopy equivalent to a finite CW complex whose
`m`-cells correspond to the critical points of index `m` in `M_a`. The hypotheses hold for every
regular value on a compact manifold, and for every regular value of a proper function. -/
theorem IsMorse.exists_cwComplex_homotopyEquiv_sublevel_of_isCompact (hf : IsMorse I f) {a : ℝ}
    (hcompact : IsCompact {x | f x ≤ a}) (ha : IsRegularValue I 𝓘(ℝ) f a) :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : T2Space W) (_ : CWComplex (univ : Set W)),
      RelCWComplex.Finite (univ : Set W) ∧ Nonempty (W ≃ₕ {x | f x ≤ a}) ∧
      ∀ m, Nonempty (cell (univ : Set W) m ≃
        ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Iic a | manifoldMorseIndex I f x = m}) := by
  -- Below the minimum of `f` on the compact set `M_a` the sublevel is empty.
  obtain ⟨l, hl⟩ := hcompact.bddBelow_image hf.contMDiff.continuous.continuousOn
  have ha₀ (x : M) : min l a - 1 < f x := by
    rcases le_or_gt (f x) a with hx | hx
    · linarith [min_le_left l a, hl (mem_image_of_mem f (show x ∈ {x | f x ≤ a} from hx))]
    · linarith [min_le_right l a]
  have hband : IsCompact (f ⁻¹' Icc (min l a - 1) a) :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.contMDiff.continuous) fun _ hx ↦ hx.2
  have : IsEmpty {x | f x ≤ min l a - 1} := ⟨fun x ↦ (not_le.2 (ha₀ x)) x.2⟩
  obtain ⟨W, _, _, _, -, h, -, -, -, e, -⟩ := hf.exists_cwComplex_extension_homotopyEquiv_sublevel
    (by linarith [min_le_right l a]) hband
    (isRegularValue_of_notMem_range fun ⟨x, hx⟩ ↦ (ha₀ x).ne' hx) ha PEmpty.{u + 1}
    Homeomorph.empty.toHomotopyEquiv
  -- The empty CW complex has no cells, and every critical point in `M_a` lies above `min l a - 1`.
  have (m : ℕ) : IsEmpty (cell (univ : Set PEmpty.{u + 1}) m) := ⟨fun j ↦ (map m j 0).elim⟩
  have hS (m : ℕ) : {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc (min l a - 1) a |
      manifoldMorseIndex I f x = m} =
      {x ∈ criticalPoints I f ∩ f ⁻¹' Iic a | manifoldMorseIndex I f x = m} := by
    ext x
    simp [ha₀ x]
  have := finite_sigma_criticalPoints_inter (hf.finite_criticalPoints_inter (K := f ⁻¹' Iic a)
    hcompact)
  let c (m : ℕ) : cell (univ : Set W) m ≃
      ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Iic a | manifoldMorseIndex I f x = m} :=
    (e m).trans ((Equiv.emptySum _ _).trans (Set.equivOfEq (hS m)))
  exact ⟨W, _, ‹_›, ‹_›,
    RelCWComplex.finite_of_finite_cells (.of_equiv _ (Equiv.sigmaCongrRight c).symm), ⟨h⟩,
    fun m ↦ ⟨c m⟩⟩

end TauCeti
