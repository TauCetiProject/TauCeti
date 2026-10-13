/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import TauCeti.AlgebraicTopology.Cellular.Homology
public import TauCeti.AlgebraicTopology.Singular.DirectedUnion
public import TauCeti.Topology.CWComplex.Classical.CompactSupport

/-!
# Cellular and singular homology of CW pairs

The inclusions `(Xᵐ, A) ⟶ (Xᵐ⁺¹, A)` induce isomorphisms in degree `k < m`: the two
adjacent homology groups of `(Xᵐ⁺¹, Xᵐ)` vanish. Hence all inclusions of skeleta above
degree `k` induce isomorphisms in that degree, and so does the inclusion `(Xᵐ, A) ⟶ (X, A)`
into the whole complex. There are two reasons for the last statement.

* For a finite-dimensional relative CW complex, a sufficiently large skeleton is the whole
  complex.
* For an arbitrary relative CW complex, a compact subset lies in a finite skeleton
  (`TauCeti.exists_subset_skeletonLT_of_isCompact`), so singular homology of `X` is the colimit
  of the singular homology of its skeleta (`TauCeti.isColimitMapCoconeSingularHomology`),
  provided sequential colimits are exact in the coefficient category, as they are for modules.
  The skeleta from `Xᵐ` on all have the same homology in degree `k < m`, so the colimit is
  attained at `Xᵐ`. This gives the statement first for absolute homology, and then for the
  pairs relative to the base through their long exact sequences.

Composing the inclusion-induced isomorphism `Hₙ(Xⁿ⁺¹, A) ≅ Hₙ(X, A)` with
`TauCeti.cellularHomologyIso` identifies cellular homology with relative singular homology.
The formula on cellular cycles specifies the comparison using the inclusion of pairs, without
choosing singular-chain representatives. No finiteness of the set of cells is required.
Coefficients lie in any abelian category with coproducts exact for the cell indexing types; for
an infinite-dimensional complex, sequential colimits must be exact as well.

The source is A. Hatcher, *Algebraic Topology*, Section 2.2, Lemma 2.34 and Theorem 2.35, and
Proposition A.1 of the Appendix for compact subsets of CW complexes.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex

universe w v u

namespace TauCeti

variable {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X}
  (C : Set X) [RelCWComplex C D]
  {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- Attaching cells of dimension `m + 1` leaves homology in degree `k < m` unchanged. -/
lemma isIso_singularHomologyMap_skeletonBasePairToSucc {m k : ℕ}
    [HasExactColimitsOfShape (Discrete (cell C (m + 1))) A] (hk : k < m) :
    IsIso ((skeletonBasePair C m).singularHomologyMap (skeletonBasePairToSucc C m) R k) := by
  have : Mono ((skeletonBasePair C m).singularHomologyMap
      (skeletonBasePairToSucc C m) R k) := by
    rw [skeletonBasePairToSucc_def]
    exact ((skeletonBaseTriple C m).singularHomology_exact_inner R (k + 1) k).mono_g
      ((isZero_singularHomology_skeletonPair_of_ne C R (by lia)).eq_of_src _ _)
  have : Epi ((skeletonBasePair C m).singularHomologyMap
      (skeletonBasePairToSucc C m) R k) := by
    rw [skeletonBasePairToSucc_def]
    exact ((skeletonBaseTriple C m).singularHomology_exact_total R k).epi_f
      ((isZero_singularHomology_skeletonPair_of_ne C R (by lia)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- Homology in degree `k` is stable under inclusions of skeleta of dimension greater than `k`.
The isomorphism is induced by the actual inclusion of pairs. Exactness of coproducts is needed
only for cell dimensions `n < j ≤ m`. -/
lemma isIso_singularHomologyMap_skeletonBasePairInclusion {n m k : ℕ}
    (h : n ≤ m) (hk : k < n)
    (hExact : ∀ j, n < j → j ≤ m → HasExactColimitsOfShape (Discrete (cell C j)) A) :
    IsIso ((skeletonBasePair C n).singularHomologyMap
      (skeletonBasePairInclusion C h) R k) := by
  induction m, h using Nat.le_induction with
  | base =>
    simp only [skeletonBasePairInclusion_refl, TopPair.singularHomologyMap_id]
    infer_instance
  | succ m h ih =>
    have := ih (fun j hj hjm ↦ hExact j hj (by lia))
    have := hExact (m + 1) (by lia) (le_refl _)
    have := isIso_singularHomologyMap_skeletonBasePairToSucc C R (m := m) (by lia : k < m)
    have : IsIso ((skeletonBasePair C m).singularHomologyMap
        (skeletonBasePairInclusion C m.le_succ) R k) := by
      rw [skeletonBasePairInclusion_succ]
      infer_instance
    rw [← skeletonBasePairInclusion_comp C h m.le_succ, TopPair.singularHomologyMap_comp]
    infer_instance

/-- Attaching the cells of dimension `j` leaves the singular homology of the skeleta unchanged
in every degree `k` with `k ≠ j` and `k + 1 ≠ j`: the inclusion `Xʲ⁻¹ ⟶ Xʲ` induces an
isomorphism on `Hₖ`, since `Hₖ₊₁(Xʲ, Xʲ⁻¹)` and `Hₖ(Xʲ, Xʲ⁻¹)` vanish. -/
lemma isIso_homologyMap_skeletonPair_map {j k : ℕ}
    [HasExactColimitsOfShape (Discrete (cell C j)) A] (hk : k ≠ j) (hk' : k + 1 ≠ j) :
    IsIso (SSet.homologyMap (TopCat.toSSet.map (skeletonPair C j).map) R k) := by
  have : Mono (SSet.homologyMap (TopCat.toSSet.map (skeletonPair C j).map) R k) :=
    ((skeletonPair C j).singularHomology_exact_subspace R (k + 1) k).mono_g
      ((isZero_singularHomology_skeletonPair_of_ne C R hk').eq_of_src _ _)
  have : Epi (SSet.homologyMap (TopCat.toSSet.map (skeletonPair C j).map) R k) :=
    ((skeletonPair C j).singularHomology_exact_space R k).epi_f
      ((isZero_singularHomology_skeletonPair_of_ne C R hk).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- The skeleta `skeletonLT C j` and their inclusions, as a sequential diagram of spaces. -/
private def skeletonFunctor : ℕ ⥤ TopCat.{w} where
  obj j := skeletonObj C j
  map f := TopCat.ofHom (ContinuousMap.inclusion (skeletonLT_mono (mod_cast f.le)))

/-- The inclusions of the skeleta into the whole complex. -/
private def skeletonCocone : Cocone (skeletonFunctor C) where
  pt := TopCat.of C
  ι := { app j := TopCat.ofHom (ContinuousMap.inclusion (skeletonLT C (j : ℕ∞)).subset_complex) }

section Colimit

variable [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A]

/-- **The singular homology of a relative CW complex is that of its skeleta in low degrees.**
When sequential colimits are exact in the coefficient category, the inclusion `Xᵐ ⟶ X` of the
`m`-skeleton induces an isomorphism on `Hₖ` for `k < m`, with no dimension bound on the complex.
Exactness of coproducts is needed only for cell dimensions above `m`. -/
lemma isIso_homologyMap_skeletonBasePairToComplex_fst {m k : ℕ} (hk : k < m)
    (hExact : ∀ j, m < j → HasExactColimitsOfShape (Discrete (cell C j)) A) :
    IsIso (SSet.homologyMap
      (TopCat.toSSet.map (TopPair.Hom.fst (skeletonBasePairToComplex C m))) R k) := by
  -- A compact subset of the complex lies in a skeleton, so singular homology of the complex is
  -- the colimit of the singular homology of its skeleta.
  have hc := isColimitMapCoconeSingularHomology R k (skeletonCocone C)
    (fun j ↦ IsEmbedding.inclusion (skeletonLT C (j : ℕ∞)).subset_complex) fun K hK ↦ by
      obtain ⟨n, hn⟩ := exists_subset_skeletonLT_of_isCompact (C := C)
        (hK.image continuous_subtype_val) (by rintro _ ⟨x, -, rfl⟩; exact x.2)
      exact ⟨n, fun x hx ↦ ⟨⟨x.1, hn ⟨x, hx, rfl⟩⟩, rfl⟩⟩
  -- From the `m`-skeleton on, the diagram of homology objects in degree `k` is constant.
  have hconst : (skeletonFunctor C ⋙
      (AlgebraicTopology.singularHomologyFunctor A k).obj R).IsEventuallyConstantFrom (m + 1) := by
    intro j φ
    induction j, φ.le using Nat.le_induction with
    | base => rw [Subsingleton.elim φ (𝟙 _), CategoryTheory.Functor.map_id]; infer_instance
    | succ j hj ih =>
      rw [Subsingleton.elim φ (homOfLE hj ≫ homOfLE j.le_succ), Functor.map_comp]
      have := ih (homOfLE hj)
      have := hExact j (by lia)
      -- The diagram sends `j ≤ j + 1` to the inclusion of the pair of consecutive skeleta.
      have hmap : (skeletonFunctor C).map (homOfLE j.le_succ) = (skeletonPair C j).map := rfl
      have : IsIso ((skeletonFunctor C ⋙
          (AlgebraicTopology.singularHomologyFunctor A k).obj R).map (homOfLE j.le_succ)) := by
        rw [Functor.comp_map, hmap]
        exact isIso_homologyMap_skeletonPair_map C R (by lia) (by lia)
      infer_instance
  rw [skeletonBasePairToComplex_fst]
  -- The leg of the colimit cocone at `m + 1` is by definition the homology map of the inclusion.
  exact hconst.isIso_ι_of_isColimit hc

/-- **Homology of the whole pair from a skeleton, without a dimension bound.** When sequential
colimits are exact in the coefficient category, inclusion of the `m`-skeleton relative to the
base into the whole relative CW complex induces an isomorphism on degree-`k` relative singular
homology for `k < m`. Exactness of coproducts is needed only for cell dimensions above `m`. -/
lemma isIso_singularHomologyMap_skeletonBasePairToComplex_of_hasExactColimitsOfShape
    {m k : ℕ} (hk : k < m)
    (hExact : ∀ j, m < j → HasExactColimitsOfShape (Discrete (cell C j)) A) :
    IsIso ((skeletonBasePair C m).singularHomologyMap (skeletonBasePairToComplex C m) R k) := by
  -- Compare the long exact sequences of the two pairs: the map is the identity on the base and
  -- an isomorphism on the homology of the ambient spaces in degrees `k` and below.
  let φ := SSetPair.chainComplexShortComplexMap
    (TopPair.toSSetPair.map (skeletonBasePairToComplex C m)) R
  have : IsIso φ.τ₁ := by
    have : IsIso (TopPair.Hom.snd (skeletonBasePairToComplex C m)) := by
      rw [skeletonBasePairToComplex_snd]
      exact IsIso.id _
    rw [SSetPair.chainComplexShortComplexMap_τ₁, TopPair.toSSetPair_map_left]
    exact Functor.map_isIso (F := (SSet.chainComplexFunctor A).obj R)
      (TopCat.toSSet.map (TopPair.Hom.snd (skeletonBasePairToComplex C m)))
  have h₂ (i : ℕ) (hi : i ≤ k) : IsIso (HomologicalComplex.homologyMap φ.τ₂ i) := by
    rw [SSetPair.chainComplexShortComplexMap_τ₂, TopPair.toSSetPair_map_right]
    exact isIso_homologyMap_skeletonBasePairToComplex_fst C R (by lia) hExact
  have := HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃ φ
    ((skeletonBasePair C m).shortExact_singularChainComplexShortComplex R)
    ((complexBasePair C).shortExact_singularChainComplexShortComplex R) k inferInstance
    (h₂ k le_rfl) (fun _ _ ↦ inferInstance) fun i hi ↦ by
      have := h₂ i (by simp at hi; lia)
      infer_instance
  rwa [SSetPair.chainComplexShortComplexMap_τ₃] at this

end Colimit

section FiniteDimensional

variable [FiniteDimensional C]

/-- For a finite-dimensional relative CW complex, inclusion of any skeleton of dimension
greater than `k` induces an isomorphism on degree-`k` relative singular homology. Exactness of
coproducts is needed only for cell dimensions above `m`. -/
lemma isIso_singularHomologyMap_skeletonBasePairToComplex {m k : ℕ} (hk : k < m)
    (hExact : ∀ j, m < j → HasExactColimitsOfShape (Discrete (cell C j)) A) :
    IsIso ((skeletonBasePair C m).singularHomologyMap (skeletonBasePairToComplex C m) R k) := by
  have h : ∀ᶠ j in Filter.atTop, IsEmpty (cell C j) :=
    FiniteDimensional.eventually_isEmpty_cell
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h
  let M := max m N
  have hM : (skeletonLT C ((M + 1 : ℕ) : ℕ∞) : Set X) = C :=
    skeletonLT_eq_complex_of_isEmpty_cell C (M + 1) fun j hj ↦ hN j (by dsimp [M] at hj; lia)
  have := isIso_skeletonBasePairToComplex_of_eq C M hM
  have := isIso_singularHomologyMap_skeletonBasePairInclusion C R (le_max_left m N) hk
    (fun j hj _ ↦ hExact j hj)
  have hfac := TopPair.singularHomologyMap_comp
    (skeletonBasePairInclusion C (le_max_left m N)) R (skeletonBasePairToComplex C M) k
  rw [skeletonBasePairInclusion_comp_toComplex] at hfac
  rw [hfac]
  infer_instance

end FiniteDimensional

variable [∀ m, HasExactColimitsOfShape (Discrete (cell C m)) A]

/-- For a finite-dimensional relative CW complex, `(Xⁿ⁺¹, X⁻¹) ⟶ (X, X⁻¹)` induces an
isomorphism on `Hₙ`. -/
instance isIso_singularHomologyMap_skeletonBasePairToComplex_succ_of_finiteDimensional
    [FiniteDimensional C] (n : ℕ) :
    IsIso ((skeletonBasePair C (n + 1)).singularHomologyMap
      (skeletonBasePairToComplex C (n + 1)) R n) :=
  isIso_singularHomologyMap_skeletonBasePairToComplex C R (by lia) fun _ _ ↦ inferInstance

/-- For any relative CW complex, `(Xⁿ⁺¹, X⁻¹) ⟶ (X, X⁻¹)` induces an isomorphism on `Hₙ` when
sequential colimits are exact in the coefficient category, for instance for modules. -/
instance isIso_singularHomologyMap_skeletonBasePairToComplex_succ_of_hasExactColimitsOfShape
    [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A] (n : ℕ) :
    IsIso ((skeletonBasePair C (n + 1)).singularHomologyMap
      (skeletonBasePairToComplex C (n + 1)) R n) :=
  isIso_singularHomologyMap_skeletonBasePairToComplex_of_hasExactColimitsOfShape C R (by lia)
    fun _ _ ↦ inferInstance

variable (n : ℕ) [IsIso ((skeletonBasePair C (n + 1)).singularHomologyMap
  (skeletonBasePairToComplex C (n + 1)) R n)]

/-- **Cellular homology is singular homology**: cellular homology of a relative CW complex is its
relative singular homology. The second map is induced by inclusion of the `(n + 1)`-skeleton into
the complex, an isomorphism on `Hₙ` for every finite-dimensional complex
(`TauCeti.isIso_singularHomologyMap_skeletonBasePairToComplex_succ_of_finiteDimensional`) and,
when sequential colimits are exact in the coefficient category, for every complex
(`TauCeti.isIso_singularHomologyMap_skeletonBasePairToComplex_succ_of_hasExactColimitsOfShape`).
-/
def cellularSingularHomologyIso :
    (cellularChainComplex C R).homology n ≅ (complexBasePair C).singularHomology R n :=
  cellularHomologyIso C R n ≪≫
    asIso ((skeletonBasePair C (n + 1)).singularHomologyMap
      (skeletonBasePairToComplex C (n + 1)) R n)

/-- The cellular–singular comparison on cycles is the homology map induced by inclusion
of the `n`-skeleton into the whole pair. -/
@[reassoc (attr := simp)]
lemma homologyπ_comp_cellularSingularHomologyIso_hom :
    (cellularChainComplex C R).homologyπ n ≫ (cellularSingularHomologyIso C R n).hom =
      (cellularCyclesIso C R n).hom ≫
        (skeletonBasePair C n).singularHomologyMap (skeletonBasePairToComplex C n) R n := by
  simp only [cellularSingularHomologyIso, Iso.trans_hom, asIso_hom, ← Category.assoc,
    homologyπ_comp_cellularHomologyIso_hom]
  rw [Category.assoc, ← TopPair.singularHomologyMap_comp, ← skeletonBasePairInclusion_succ,
    skeletonBasePairInclusion_comp_toComplex]

end TauCeti
