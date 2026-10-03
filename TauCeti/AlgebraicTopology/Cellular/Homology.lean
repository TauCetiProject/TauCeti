/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Coproduct

/-!
# The homology of the cellular chain complex

For a relative CW complex `(X, A)` write `Xⁿ` for its `n`-skeleton, so that `X⁻¹ = A`.  This
file proves the vanishing results on the relative singular homology of skeleta that drive the
comparison of cellular and singular homology, and the first half of that comparison: the
homology of the cellular chain complex in degree `n` is the relative singular homology
`Hₙ(Xⁿ⁺¹, X⁻¹)` of the `(n + 1)`-skeleton.

* `Hₖ(Xⁿ, Xⁿ⁻¹) = 0` for `k ≠ n` (`TauCeti.isZero_singularHomology_skeletonPair_of_ne`): the
  characteristic maps identify this group with the relative homology of a disjoint union of
  disk pairs `(Dⁿ, Sⁿ⁻¹)`, which vanishes outside degree `n`.
* `Hₖ(Xⁿ, X⁻¹) = 0` for `n < k` (`TauCeti.isZero_singularHomology_skeletonBasePair_of_lt`), by
  induction on `n` along the long exact sequences of the triples `(Xⁿ⁺¹, Xⁿ, X⁻¹)`.
* The cellular differential `Hₙ₊₁(Xⁿ⁺¹, Xⁿ) ⟶ Hₙ(Xⁿ, Xⁿ⁻¹)` factors as the connecting morphism
  `TauCeti.skeletonBaseTripleδ` of the triple `(Xⁿ⁺¹, Xⁿ, X⁻¹)` followed by the map
  `Hₙ(Xⁿ, X⁻¹) ⟶ Hₙ(Xⁿ, Xⁿ⁻¹)` induced by the identity of `Xⁿ`
  (`TauCeti.cellularDifferential_eq_skeletonBaseTripleδ_comp_singularHomologyMap`).  The second
  map is a monomorphism, because `Hₙ(Xⁿ⁻¹, X⁻¹) = 0`.
* Hence the cellular cycles in degree `n` are `Hₙ(Xⁿ, X⁻¹)` (`TauCeti.cellularCyclesIso`) and the
  cellular boundaries are the image of `TauCeti.skeletonBaseTripleδ`.  Since `Hₙ(Xⁿ⁺¹, Xⁿ) = 0`, the
  exact sequence of the triple (`TauCeti.skeletonBaseTriple_singularHomology_exact_inner`)
  identifies the cellular homology in degree `n` with `Hₙ(Xⁿ⁺¹, X⁻¹)`
  (`TauCeti.cellularHomologyIso`).  Both identifications come from a left homology datum of the
  short complex of the cellular chain complex in degree `n`.

The base `X⁻¹` is `skeletonLT C 0`, which is the base of the complex by
`TauCeti.range_skeletonBasePair_snd`; using it keeps the pair `(X⁰, X⁻¹)` identical to
the skeletal pair `TauCeti.skeletonPair C 0`.

Coefficients are an object `R` of an abelian category with coproducts in which coproducts indexed
by the cells of each dimension are exact, as for modules over a ring, or for any abelian category
when the complex has finitely many cells in each dimension.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Lemma 2.34 and the proof of Theorem 2.35.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex

universe w v u

namespace TauCeti

variable {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X} (C : Set X) [RelCWComplex C D]
  {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- **The relative homology of consecutive skeleta vanishes outside the degree of their cells**:
`Hₖ(Xⁿ, Xⁿ⁻¹) = 0` for `k ≠ n`, when coproducts indexed by the `n`-cells are exact. -/
theorem isZero_singularHomology_skeletonPair_of_ne {n k : ℕ}
    [HasExactColimitsOfShape (Discrete (cell C n)) A] (hk : k ≠ n) :
    IsZero ((skeletonPair C n).singularHomology R k) :=
  (isZero_singularHomology_sigmaDiskPair_of_ne R (cell C n) hk).of_iso
    (asIso ((sigmaDiskPair (cell C n) n).singularHomologyMap (characteristicPairMap C n) R k)).symm

/-- In degree `0` the map `Hₖ(X⁰, X⁻¹) ⟶ Hₖ(X⁰, X⁻¹)` induced by
`TauCeti.skeletonBasePairToSkeletonPair` is an isomorphism, being the identity. -/
instance isIso_singularHomologyMap_skeletonBasePairToSkeletonPair_zero (k : ℕ) :
    IsIso ((skeletonBasePair C 0).singularHomologyMap
      (skeletonBasePairToSkeletonPair C 0) R k) := by
  rw [skeletonBasePairToSkeletonPair_zero, TopPair.singularHomologyMap_id]
  infer_instance

/-- The map of triples `(Xⁿ⁺¹, Xⁿ, X⁻¹) ⟶ (Xⁿ⁺¹, Xⁿ, Xⁿ⁻¹)`, the identity on the two larger
skeleta. -/
private def skeletonBaseTripleToSkeletonTriple (n : ℕ) :
    skeletonBaseTriple C n ⟶ skeletonTriple C n :=
  ⟨ComposableArrows.homMk₂
    (TopCat.ofHom (ContinuousMap.inclusion (skeletonLT_zero_subset_skeletonLT C n)))
    (𝟙 _) (𝟙 _) rfl rfl⟩

/-- The connecting morphism `Hₙ₊₁(Xⁿ⁺¹, Xⁿ) ⟶ Hₙ(Xⁿ, X⁻¹)` of the triple `(Xⁿ⁺¹, Xⁿ, X⁻¹)`. -/
def skeletonBaseTripleδ (n : ℕ) :
    cellularChainGroup C R (n + 1) ⟶ (skeletonBasePair C n).singularHomology R n :=
  (skeletonBaseTriple C n).singularHomologyδ R (n + 1) n

/-- `TauCeti.skeletonBaseTripleδ` is the connecting morphism of the triple
`TauCeti.skeletonBaseTriple C n`. -/
lemma skeletonBaseTripleδ_def (n : ℕ) :
    skeletonBaseTripleδ C R n = (skeletonBaseTriple C n).singularHomologyδ R (n + 1) n := (rfl)

/-- The connecting morphism `Hₙ₊₁(Xⁿ⁺¹, Xⁿ) ⟶ Hₙ(Xⁿ, X⁻¹)` followed by the map
`Hₙ(Xⁿ, X⁻¹) ⟶ Hₙ(Xⁿ⁺¹, X⁻¹)` is zero. -/
@[reassoc (attr := simp)]
lemma skeletonBaseTripleδ_comp_singularHomologyMap_skeletonBasePairToSucc (n : ℕ) :
    skeletonBaseTripleδ C R n ≫
      (skeletonBasePair C n).singularHomologyMap (skeletonBasePairToSucc C n) R n = 0 := by
  rw [skeletonBasePairToSucc_def]
  exact (skeletonBaseTriple C n).singularHomologyδ_comp R (n + 1) n

/-- The map `Hₙ₊₁(Xⁿ⁺¹, X⁻¹) ⟶ Hₙ₊₁(Xⁿ⁺¹, Xⁿ)` followed by the connecting morphism
`Hₙ₊₁(Xⁿ⁺¹, Xⁿ) ⟶ Hₙ(Xⁿ, X⁻¹)` is zero. -/
@[reassoc (attr := simp)]
lemma singularHomologyMap_skeletonBasePairToSkeletonPair_comp_skeletonBaseTripleδ (n : ℕ) :
    (skeletonBasePair C (n + 1)).singularHomologyMap (skeletonBasePairToSkeletonPair C (n + 1))
      R (n + 1) ≫ skeletonBaseTripleδ C R n = 0 := by
  rw [skeletonBasePairToSkeletonPair_succ]
  exact (skeletonBaseTriple C n).comp_singularHomologyδ R (n + 1) n

/-- The cellular differential `Hₙ₊₁(Xⁿ⁺¹, Xⁿ) ⟶ Hₙ(Xⁿ, Xⁿ⁻¹)` is the connecting morphism
`Hₙ₊₁(Xⁿ⁺¹, Xⁿ) ⟶ Hₙ(Xⁿ, X⁻¹)` of the triple `(Xⁿ⁺¹, Xⁿ, X⁻¹)` followed by the map
`Hₙ(Xⁿ, X⁻¹) ⟶ Hₙ(Xⁿ, Xⁿ⁻¹)`. -/
@[reassoc]
lemma cellularDifferential_eq_skeletonBaseTripleδ_comp_singularHomologyMap (n : ℕ) :
    cellularDifferential C R n = skeletonBaseTripleδ C R n ≫
      (skeletonBasePair C n).singularHomologyMap (skeletonBasePairToSkeletonPair C n) R n := by
  have h₁ : TopTriple.innerPair.map (skeletonBaseTripleToSkeletonTriple C n) =
      skeletonBasePairToSkeletonPair C n := by
    refine MorphismProperty.Arrow.Hom.ext ?_ ?_
    · ext x
      exact Subtype.ext (coe_skeletonBasePairToSkeletonPair_snd_apply C n x).symm
    · ext x
      exact (skeletonBasePairToSkeletonPair_fst_apply C n x).symm
  have h₂ : TopTriple.outerPair.map (skeletonBaseTripleToSkeletonTriple C n) = 𝟙 _ := by
    ext : 2 <;> rfl
  -- Naturality of the connecting morphism along the map of triples
  -- `(Xⁿ⁺¹, Xⁿ, X⁻¹) ⟶ (Xⁿ⁺¹, Xⁿ, Xⁿ⁻¹)`, which is the identity on the outer pair.
  have key := TopTriple.singularHomologyδ_naturality (skeletonBaseTripleToSkeletonTriple C n) R
    (n + 1) n
  rw [h₁, h₂, TopPair.singularHomologyMap_id, Category.id_comp] at key
  rw [cellularDifferential_eq_singularHomologyδ, skeletonBaseTripleδ_def]
  exact key.symm

/-- The map `Hₙ(Xⁿ, X⁻¹) ⟶ Hₙ(Xⁿ, Xⁿ⁻¹)`, read in the cellular chain complex. -/
private def cellularCyclesι (n : ℕ) :
    (skeletonBasePair C n).singularHomology R n ⟶ (cellularChainComplex C R).X n :=
  (skeletonBasePair C n).singularHomologyMap (skeletonBasePairToSkeletonPair C n) R n ≫
    eqToHom (cellularChainComplex_X C R n).symm

/-- The differential of the cellular chain complex out of degree `n + 1` factors through the
connecting morphism of the triple `(Xⁿ⁺¹, Xⁿ, X⁻¹)`. -/
private lemma cellularChainComplex_d_eq (n : ℕ) :
    (cellularChainComplex C R).d (n + 1) n =
      eqToHom (cellularChainComplex_X C R (n + 1)) ≫ skeletonBaseTripleδ C R n ≫
        cellularCyclesι C R n := by
  rw [cellularChainComplex_d, cellularDifferential_eq_skeletonBaseTripleδ_comp_singularHomologyMap]
  simp only [cellularCyclesι, Category.assoc]

/-- The map `Hₙ(Xⁿ, X⁻¹) ⟶ Hₙ(Xⁿ, Xⁿ⁻¹)` followed by the outgoing cellular differential is zero. -/
private lemma cellularCyclesι_comp_d (n : ℕ) :
    cellularCyclesι C R n ≫ (cellularChainComplex C R).d n (n - 1) = 0 := by
  cases n with
  | zero => simp
  | succ n =>
    simp [cellularCyclesι, cellularDifferential_eq_skeletonBaseTripleδ_comp_singularHomologyMap]

/-- Exactness at `Hₙ₊₁(Xⁿ⁺¹, Xⁿ)` in the long exact sequence of the triple `(Xⁿ⁺¹, Xⁿ, X⁻¹)`,
stated with the maps of `TauCeti.skeletonBasePair`. -/
lemma skeletonBaseTriple_singularHomology_exact_outer (n : ℕ) :
    (ShortComplex.mk _ _
      (singularHomologyMap_skeletonBasePairToSkeletonPair_comp_skeletonBaseTripleδ C R n)).Exact :=
  ShortComplex.exact_of_iso
    (S₁ := ShortComplex.mk _ _ ((skeletonBaseTriple C n).comp_singularHomologyδ R (n + 1) n))
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [skeletonBasePairToSkeletonPair_succ])
      ((Category.id_comp _).trans (Category.comp_id _).symm))
    ((skeletonBaseTriple C n).singularHomology_exact_outer R (n + 1) n)

/-- Exactness at `Hₙ(Xⁿ, X⁻¹)` in the long exact sequence of the triple `(Xⁿ⁺¹, Xⁿ, X⁻¹)`,
stated with the maps of `TauCeti.skeletonBasePair`. -/
lemma skeletonBaseTriple_singularHomology_exact_inner (n : ℕ) :
    (ShortComplex.mk _ _
      (skeletonBaseTripleδ_comp_singularHomologyMap_skeletonBasePairToSucc C R n)).Exact :=
  ShortComplex.exact_of_iso
    (S₁ := ShortComplex.mk _ _ ((skeletonBaseTriple C n).singularHomologyδ_comp R (n + 1) n))
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ((Category.id_comp _).trans (Category.comp_id _).symm)
      (by simp [skeletonBasePairToSucc_def]))
    ((skeletonBaseTriple C n).singularHomology_exact_inner R (n + 1) n)

/-- The map `Hₙ(Xⁿ, X⁻¹) ⟶ Hₙ(Xⁿ⁺¹, X⁻¹)` is an epimorphism: its cokernel embeds in
`Hₙ(Xⁿ⁺¹, Xⁿ) = 0`. -/
instance epi_singularHomologyMap_skeletonBasePairToSucc (n : ℕ)
    [HasExactColimitsOfShape (Discrete (cell C (n + 1))) A] :
    Epi ((skeletonBasePair C n).singularHomologyMap (skeletonBasePairToSucc C n) R n) := by
  rw [skeletonBasePairToSucc_def]
  exact ((skeletonBaseTriple C n).singularHomology_exact_total R n).epi_f
    ((isZero_singularHomology_skeletonPair_of_ne C R (by lia)).eq_of_tgt _ _)

section Base

variable [∀ m, HasExactColimitsOfShape (Discrete (cell C m)) A]

/-- **The homology of a skeleton relative to the base vanishes above its dimension**:
`Hₖ(Xⁿ, X⁻¹) = 0` for `n < k`. -/
theorem isZero_singularHomology_skeletonBasePair_of_lt {n k : ℕ} (hk : n < k) :
    IsZero ((skeletonBasePair C n).singularHomology R k) := by
  induction n with
  | zero => exact isZero_singularHomology_skeletonPair_of_ne C R hk.ne'
  | succ n ih =>
    exact ((skeletonBaseTriple C n).singularHomology_exact_total R k).isZero_X₂
      ((ih (by lia)).eq_of_src _ _)
      ((isZero_singularHomology_skeletonPair_of_ne C R (by lia)).eq_of_tgt _ _)

/-- The map `Hₙ(Xⁿ, X⁻¹) ⟶ Hₙ(Xⁿ, Xⁿ⁻¹)` is a monomorphism: its kernel is a quotient of
`Hₙ(Xⁿ⁻¹, X⁻¹) = 0`. -/
instance mono_singularHomologyMap_skeletonBasePairToSkeletonPair (n : ℕ) :
    Mono ((skeletonBasePair C n).singularHomologyMap
      (skeletonBasePairToSkeletonPair C n) R n) := by
  cases n with
  | zero => infer_instance
  | succ n =>
    rw [skeletonBasePairToSkeletonPair_succ]
    exact ((skeletonBaseTriple C n).singularHomology_exact_total R (n + 1)).mono_g
      ((isZero_singularHomology_skeletonBasePair_of_lt C R (by lia)).eq_of_src _ _)

end Base

section Homology

variable [∀ m, HasExactColimitsOfShape (Discrete (cell C m)) A]

private instance (n : ℕ) : Mono (cellularCyclesι C R n) := by
  unfold cellularCyclesι
  infer_instance

/-- The sequence `Hₙ(Xⁿ, X⁻¹) ⟶ Hₙ(Xⁿ, Xⁿ⁻¹) ⟶ Hₙ₋₁(Xⁿ⁻¹, Xⁿ⁻²)` is exact. -/
private lemma cellularCycles_exact (n : ℕ) :
    (ShortComplex.mk _ _ (cellularCyclesι_comp_d C R n)).Exact := by
  cases n with
  | zero =>
    rw [ShortComplex.exact_iff_epi _ ((cellularChainComplex C R).shape 0 0 (by simp))]
    exact inferInstanceAs (Epi (_ ≫ _))
  | succ n =>
    refine (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      (S₁ := ShortComplex.mk _ _
        (singularHomologyMap_skeletonBasePairToSkeletonPair_comp_skeletonBaseTripleδ C R n))
      (S₂ := ShortComplex.mk _ _ (cellularCyclesι_comp_d C R (n + 1)))
      { τ₁ := 𝟙 _
        τ₂ := eqToHom (cellularChainComplex_X C R (n + 1)).symm
        τ₃ := cellularCyclesι C R n
        comm₁₂ := by simp [cellularCyclesι]
        comm₂₃ := by
          simp [cellularCyclesι,
            cellularDifferential_eq_skeletonBaseTripleδ_comp_singularHomologyMap] }).1
      (skeletonBaseTriple_singularHomology_exact_outer C R n)

/-- The kernel lift of the incoming cellular differential through `Hₙ(Xⁿ, X⁻¹)` is the
connecting morphism of the triple `(Xⁿ⁺¹, Xⁿ, X⁻¹)`. -/
private lemma cellularCycles_lift_eq (n : ℕ) :
    (cellularCycles_exact C R n).fIsKernel.lift
        (KernelFork.ofι ((cellularChainComplex C R).d (n + 1) n)
          ((cellularChainComplex C R).d_comp_d (n + 1) n (n - 1))) =
      eqToHom (cellularChainComplex_X C R (n + 1)) ≫ skeletonBaseTripleδ C R n := by
  rw [← cancel_mono (cellularCyclesι C R n), Category.assoc, ← cellularChainComplex_d_eq]
  exact Fork.IsLimit.lift_ι _

/-- **The cellular homology as a left homology datum**: in degree `n` the cellular cycles are
`Hₙ(Xⁿ, X⁻¹)`, included in `Hₙ(Xⁿ, Xⁿ⁻¹)` by the map that is the identity on `Xⁿ`, and the
cellular homology is `Hₙ(Xⁿ⁺¹, X⁻¹)`, the quotient of the cycles by the image of the connecting
morphism `Hₙ₊₁(Xⁿ⁺¹, Xⁿ) ⟶ Hₙ(Xⁿ, X⁻¹)` of the triple `(Xⁿ⁺¹, Xⁿ, X⁻¹)`. -/
private def cellularLeftHomologyData (n : ℕ) :
    ((cellularChainComplex C R).sc' (n + 1) n (n - 1)).LeftHomologyData where
  K := (skeletonBasePair C n).singularHomology R n
  H := (skeletonBasePair C (n + 1)).singularHomology R n
  i := cellularCyclesι C R n
  wi := cellularCyclesι_comp_d C R n
  hi := (cellularCycles_exact C R n).fIsKernel
  π := (skeletonBasePair C n).singularHomologyMap (skeletonBasePairToSucc C n) R n
  wπ := by
    refine (congrArg (· ≫ _) (cellularCycles_lift_eq C R n)).trans ?_
    rw [Category.assoc, skeletonBaseTripleδ_comp_singularHomologyMap_skeletonBasePairToSucc]
    exact comp_zero
  hπ := isCokernelEpiComp (skeletonBaseTriple_singularHomology_exact_inner C R n).gIsCokernel
    (eqToHom (cellularChainComplex_X C R (n + 1))) (cellularCycles_lift_eq C R n)

/-- The cycles of the cellular chain complex in degree `n` are `Hₙ(Xⁿ, X⁻¹)`. -/
def cellularCyclesIso (n : ℕ) :
    (cellularChainComplex C R).cycles n ≅ (skeletonBasePair C n).singularHomology R n :=
  (cellularChainComplex C R).cyclesIsoSc' (n + 1) n (n - 1) (by simp) (by cases n <;> simp) ≪≫
    (cellularLeftHomologyData C R n).cyclesIso

/-- Under `TauCeti.cellularCyclesIso`, the inclusion of the cellular cycles into the cellular
chain group `Hₙ(Xⁿ, Xⁿ⁻¹)` is induced by the map of pairs `(Xⁿ, X⁻¹) ⟶ (Xⁿ, Xⁿ⁻¹)`. -/
@[reassoc (attr := simp)]
lemma cellularCyclesIso_inv_comp_iCycles (n : ℕ) :
    (cellularCyclesIso C R n).inv ≫ (cellularChainComplex C R).iCycles n =
      (skeletonBasePair C n).singularHomologyMap (skeletonBasePairToSkeletonPair C n) R n ≫
        eqToHom (cellularChainComplex_X C R n).symm :=
  -- The cycles of the left homology datum are `Hₙ(Xⁿ, X⁻¹)` only up to unfolding, so
  -- `Iso.trans_inv` does not rewrite here; the two inclusion lemmas are chained instead.
  (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) ((cellularChainComplex C R).cyclesIsoSc'_inv_iCycles _ _ _ _ _)).trans
      (cellularLeftHomologyData C R n).cyclesIso_inv_comp_iCycles

/-- **The homology of the cellular chain complex** in degree `n` is the relative singular homology
`Hₙ(Xⁿ⁺¹, X⁻¹)` of the `(n + 1)`-skeleton relative to the base. -/
def cellularHomologyIso (n : ℕ) :
    (cellularChainComplex C R).homology n ≅ (skeletonBasePair C (n + 1)).singularHomology R n :=
  (cellularChainComplex C R).homologyIsoSc' (n + 1) n (n - 1) (by simp) (by cases n <;> simp) ≪≫
    (cellularLeftHomologyData C R n).homologyIso

/-- Under `TauCeti.cellularCyclesIso` and `TauCeti.cellularHomologyIso`, the projection from the
cellular cycles to the cellular homology is induced by the inclusion `(Xⁿ, X⁻¹) ⟶ (Xⁿ⁺¹, X⁻¹)`. -/
@[reassoc (attr := simp)]
lemma homologyπ_comp_cellularHomologyIso_hom (n : ℕ) :
    (cellularChainComplex C R).homologyπ n ≫ (cellularHomologyIso C R n).hom =
      (cellularCyclesIso C R n).hom ≫
        (skeletonBasePair C n).singularHomologyMap (skeletonBasePairToSucc C n) R n := by
  have h := (cellularChainComplex C R).π_homologyIsoSc'_hom_assoc (n + 1) n (n - 1) (by simp)
    (by cases n <;> simp) (cellularLeftHomologyData C R n).homologyIso.hom
  rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom] at h
  exact h.trans (Category.assoc _ _ _).symm

end Homology

end TauCeti
