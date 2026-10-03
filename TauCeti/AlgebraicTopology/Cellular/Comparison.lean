/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Homology

/-!
# Cellular and singular homology of finite-dimensional CW pairs

The inclusions `(Xᵐ, A) ⟶ (Xᵐ⁺¹, A)` induce isomorphisms in degree `k < m`: the two
adjacent homology groups of `(Xᵐ⁺¹, Xᵐ)` vanish. Hence all inclusions of skeleta above
degree `k` induce isomorphisms in that degree. For a finite-dimensional relative CW complex,
a sufficiently large skeleton is the whole complex, so the inclusion
`(Xᵏ⁺¹, A) ⟶ (X, A)` induces an isomorphism in degree `k`.

Composing this inclusion-induced isomorphism with `TauCeti.cellularHomologyIso` identifies
cellular homology with relative singular homology. The formula on cellular cycles specifies
the comparison using the inclusion of pairs, without choosing singular-chain representatives.
Finite dimensionality bounds cell dimensions; no finiteness of the set of cells is required.
Coefficients lie in any abelian category with coproducts exact for the cell indexing types.

The source is A. Hatcher, *Algebraic Topology*, Section 2.2, Lemma 2.34 and Theorem 2.35.
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

variable [∀ m, HasExactColimitsOfShape (Discrete (cell C m)) A]

/-- Cellular homology of a finite-dimensional relative CW complex is its relative singular
homology. The second map is induced by inclusion of the `(n + 1)`-skeleton into the complex. -/
def cellularSingularHomologyIso (n : ℕ) :
    (cellularChainComplex C R).homology n ≅ (complexBasePair C).singularHomology R n :=
  have := isIso_singularHomologyMap_skeletonBasePairToComplex C R (m := n + 1) (k := n) (by lia)
    (fun _ _ ↦ inferInstance)
  cellularHomologyIso C R n ≪≫
    asIso ((skeletonBasePair C (n + 1)).singularHomologyMap
      (skeletonBasePairToComplex C (n + 1)) R n)

/-- The cellular–singular comparison on cycles is the homology map induced by inclusion
of the `n`-skeleton into the whole pair. -/
@[reassoc (attr := simp)]
lemma homologyπ_comp_cellularSingularHomologyIso_hom (n : ℕ) :
    (cellularChainComplex C R).homologyπ n ≫ (cellularSingularHomologyIso C R n).hom =
      (cellularCyclesIso C R n).hom ≫
        (skeletonBasePair C n).singularHomologyMap (skeletonBasePairToComplex C n) R n := by
  simp only [cellularSingularHomologyIso, Iso.trans_hom, asIso_hom, ← Category.assoc,
    homologyπ_comp_cellularHomologyIso_hom]
  rw [Category.assoc, ← TopPair.singularHomologyMap_comp, ← skeletonBasePairInclusion_succ,
    skeletonBasePairInclusion_comp_toComplex]

end TauCeti
