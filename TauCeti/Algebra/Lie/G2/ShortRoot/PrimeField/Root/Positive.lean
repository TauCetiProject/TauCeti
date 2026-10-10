/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Pinning.Basic
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Root.Space
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Positive.BorelCandidate

/-!
# The numbered positive simple roots of the short-root G₂ carrier

The two numbered raising roots are intrinsically simple for the chosen split maximal torus
and positive subgroup of the short-root carrier over `𝔽₃`. Their root spaces lie in the
positive subgroup's tangent Lie algebra. Every intrinsic positive root has strictly positive
height, whereas each numbered raising root has height one, so neither is a sum of two positive
roots.

The height functional is `3a + 5b` in fundamental-weight coordinates. On the seven ordered
weights of the short-root module its values are `3, 2, 1, 0, -1, -2, -3`. Upper triangularity
therefore detects positivity without a classification of all adjoint weights. The results do
not assert that the two roots exhaust the intrinsic simple roots, or that the positive subgroup
is a Borel. No identification with an independently pinned group scheme is made.

## Main results

* `TauCeti.G2ShortRoot.PrimeField.isPositiveRoot_simpleRootCharacter`: the numbered raising
  characters are intrinsic positive roots.
* `TauCeti.G2ShortRoot.PrimeField.isSimpleRoot_simpleRootCharacter`: they are intrinsic simple
  roots, relative to the same positive subgroup.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.1.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.

The intrinsic definitions and proof organization follow
`TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Pinning.Basic`.
-/

public section

open CategoryTheory

namespace TauCeti.G2ShortRoot.PrimeField

open DynkinType

noncomputable section

/-- The numbered positive simple-root character in the lifted coordinates of the chosen split
maximal torus. Its underlying root is the corresponding Bourbaki root of the simply connected
`G₂` datum. -/
def simpleRootCharacter (i : Fin 2) : ULift.{0} (Fin 2) →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm fun j =>
    (G2.simplyConnectedRootDatum valid_G2).root (G2.simpleIndex valid_G2 i) j.down

/-- The numbered root character evaluates as the corresponding root of the named datum. -/
@[simp]
theorem simpleRootCharacter_apply (i : Fin 2) (j : ULift.{0} (Fin 2)) :
    simpleRootCharacter i j =
      (G2.simplyConnectedRootDatum valid_G2).root (G2.simpleIndex valid_G2 i) j.down := by
  simp [simpleRootCharacter]

private theorem ofAdd_simpleRootCharacter (i : Fin 2) :
    Multiplicative.ofAdd (simpleRootCharacter i) =
      SplitTorus.weightCharacter (fun j : ULift.{0} (Fin 2) =>
        G2.rootGeneratorWeight valid_G2 (.inl i) j.down) := by
  have hroot : G2.rootGeneratorWeight valid_G2 (.inl i) =
      (G2.simplyConnectedRootDatum valid_G2).root (G2.simpleIndex valid_G2 i) := by
    simpa only [rank_G2] using G2.rootGeneratorWeight_inl_eq_root_simpleIndex valid_G2 i
  apply Multiplicative.toAdd.injective
  ext j
  simp only [toAdd_ofAdd, simpleRootCharacter_apply, SplitTorus.toAdd_weightCharacter, hroot]

private theorem simpleRootCharacter_height (i : Fin 2) :
    3 * simpleRootCharacter i (ULift.up 0) +
      5 * simpleRootCharacter i (ULift.up 1) = 1 := by
  have hrow : (G2.simplyConnectedRootDatum valid_G2).root (G2.simpleIndex valid_G2 i) =
      fun j : Fin 2 => (!![2, -1; -3, 2] : Matrix (Fin 2) (Fin 2) ℤ) i j := by
    simpa only [rank_G2, cartanMatrix_G2_eq] using root_simpleIndex G2 valid_G2 i
  simp only [simpleRootCharacter_apply, hrow]
  fin_cases i <;> norm_num

/-- The differential of a numbered raising subgroup belongs to the tangent Lie algebra of the
positive subgroup. -/
theorem rootVector_inl_mem_positiveDefiningIdeal_lieSubalgebra (i : Fin 2) :
    Derivation.cotangentLinearEquiv (B := ZMod 3) (rootVector (.inl i)) ∈
      positiveDefiningIdeal.lieSubalgebra := by
  have hcomp : positiveRestriction ≫
      CommHopfAlgCat.commonKernelLift Positive.generator (.inl i) =
        CommHopfAlgCat.commonKernelLift generator (.inl (.inl i)) := by
    apply (cancel_epi (CommHopfAlgCat.mkQuotient _ _)).1
    rw [CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe_assoc,
      CommHopfAlgCat.mkQuotient_comp_commonKernelLift,
      CommHopfAlgCat.mkQuotient_comp_commonKernelLift, Positive.generator_inl]
  rw [cotangentLinearEquiv_rootVector, HopfIdeal.mem_lieSubalgebra_iff]
  intro x hx
  have hz : (CommHopfAlgCat.commonKernelLift generator (.inl (.inl i))).hom x = 0 := by
    rw [← hcomp, CommHopfAlgCat.comp_apply,
      (mem_positiveDefiningIdeal x).mp hx, map_zero]
  simp [derivationComp_apply, hz]
  rfl

private theorem adjointWeightSpace_simpleRootCharacter_eq_span (i : Fin 2) :
    Derivation.adjointWeightSpace splitMaximalTorus.coordinateMap.hom
        (Multiplicative.ofAdd (simpleRootCharacter i)) = (ZMod 3) ∙ rootVector (.inl i) := by
  calc
    _ = Derivation.adjointWeightSpace splitMaximalTorus.coordinateMap.hom
        (SplitTorus.weightCharacter (fun j : ULift.{0} (Fin 2) =>
          G2.rootGeneratorWeight valid_G2 (.inl i) j.down)) :=
      congrArg (Derivation.adjointWeightSpace splitMaximalTorus.coordinateMap.hom)
        (ofAdd_simpleRootCharacter i)
    _ = Derivation.adjointWeightSpace weightTorusCoordinateMap.hom
        (SplitTorus.weightCharacter (G2.rootGeneratorWeight valid_G2 (.inl i))) :=
      adjointWeightSpace_splitMaximalTorus_weightCharacter_eq_weightTorus _
    _ = _ := adjointWeightSpace_rootGeneratorWeight_eq_span (.inl i)

/-- Each numbered raising root is an intrinsic positive root for the chosen torus and positive
subgroup. -/
theorem isPositiveRoot_simpleRootCharacter (i : Fin 2) :
    splitMaximalTorus.IsPositiveRoot positiveDefiningIdeal (simpleRootCharacter i) := by
  rw [SplitMaximalTorus.isPositiveRoot_iff, Derivation.mem_nontrivialAdjointWeights,
    adjointWeightSpace_simpleRootCharacter_eq_span]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro h
    have hz : simpleRootCharacter i = 0 := Multiplicative.ofAdd.injective h
    have hh := simpleRootCharacter_height i
    simp [hz] at hh
  · intro h
    have hmem : rootVector (.inl i) ∈ Derivation.adjointWeightSpace
        splitMaximalTorus.coordinateMap.hom (Multiplicative.ofAdd (simpleRootCharacter i)) :=
      (adjointWeightSpace_simpleRootCharacter_eq_span i).symm ▸
        Submodule.mem_span_singleton_self _
    exact rootVector_ne_zero (.inl i) ((Submodule.mem_bot (ZMod 3)).mp (h ▸ hmem))
  · intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul]
    exact positiveDefiningIdeal.lieSubalgebra.smul_mem c
      (rootVector_inl_mem_positiveDefiningIdeal_lieSubalgebra i)

private theorem tangentMatrix_lower_eq_zero
    (x : Module.Dual (ZMod 3) (Bialgebra.CotangentSpace (ZMod 3) carrierAlgebra))
    (hx : Derivation.cotangentLinearEquiv (B := ZMod 3) x ∈ positiveDefiningIdeal.lieSubalgebra)
    (i j : Fin 7) (hji : j < i) : tangentMatrix x i j = 0 := by
  let y := GeneralLinear.coordinateHopfAlgebraAlgEquiv (ZMod 3) 7
    (GeneralLinear.coordinateRingMap (ZMod 3) 7 (MvPolynomial.X (i, j)))
  have hy : y ∈ Positive.definingIdeal := by
    apply Positive.upperTriangular_le_definingIdeal
    rw [← HopfIdeal.mem_toIdeal, GeneralLinear.UpperTriangular.definingHopfIdeal_toIdeal]
    exact Ideal.subset_span
      ((GeneralLinear.UpperTriangular.mem_definingRelationSet_iff _ _ y).mpr
        ⟨i, j, hji, rfl⟩)
  have hq : Ideal.Quotient.mkₐ (ZMod 3)
      (CommHopfAlgCat.commonKernelHopfIdeal generator).toIdeal y ∈ positiveDefiningIdeal := by
    rw [mem_positiveDefiningIdeal]
    rw [← CommHopfAlgCat.mkQuotient_apply,
      ← CommHopfAlgCat.comp_apply, CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hy
  have hz := (HopfIdeal.mem_lieSubalgebra_iff _ _).mp hx _ hq
  rw [tangentMatrix_apply, GeneralLinear.tangentMatrix_apply,
    HopfIdeal.quotientLieHom_apply_apply, hz]
  rw [Bialgebra.CounitAlgebra.algEquivSelf_apply]
  exact Bialgebra.CounitAlgebra.algEquivSelf_apply (ZMod 3)
    (GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7) (ZMod 3) (0 : ZMod 3)

/-- Every intrinsic positive root for the chosen torus and positive subgroup has strictly
positive integral height under the functional `3a + 5b` in fundamental-weight coordinates. -/
theorem height_pos_of_isPositiveRoot (α : ULift.{0} (Fin 2) →₀ ℤ)
    (hα : splitMaximalTorus.IsPositiveRoot positiveDefiningIdeal α) :
    0 < 3 * α (ULift.up 0) + 5 * α (ULift.up 1) := by
  rw [SplitMaximalTorus.isPositiveRoot_iff] at hα
  obtain ⟨hαne, hspace⟩ := Derivation.mem_nontrivialAdjointWeights.mp hα.1
  obtain ⟨x, hx, hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hspace
  have hm : tangentMatrix x ≠ 0 := fun h => hxne
    (tangentMatrix_injective (h.trans (map_zero tangentMatrix).symm))
  obtain ⟨i, j, hij⟩ : ∃ i j, tangentMatrix x i j ≠ 0 := by
    contrapose! hm
    ext i j
    exact hm i j
  have heq : SplitTorus.weightCharacter
      (fun b : ULift.{0} (Fin 2) => weight i b.down - weight j b.down) =
        Multiplicative.ofAdd α := by
    by_contra h
    exact hij ((mem_adjointWeightSpace_splitMaximalTorus_iff _ x).mp hx i j h)
  have hijlt : i < j := by
    have hnot : ¬ j < i := fun h => hij (tangentMatrix_lower_eq_zero x (hα.2 x hx) i j h)
    have hne : i ≠ j := by
      intro hij
      subst j
      apply hαne
      rw [← heq]
      apply Multiplicative.toAdd.injective
      ext l
      simp [SplitTorus.toAdd_weightCharacter]
    exact lt_of_le_of_ne (le_of_not_gt hnot) hne
  have hzero := congrArg (fun χ : Multiplicative (ULift.{0} (Fin 2) →₀ ℤ) =>
    Multiplicative.toAdd χ (ULift.up 0)) heq
  have hone := congrArg (fun χ : Multiplicative (ULift.{0} (Fin 2) →₀ ℤ) =>
    Multiplicative.toAdd χ (ULift.up 1)) heq
  simp only [SplitTorus.toAdd_weightCharacter, toAdd_ofAdd] at hzero hone
  have hw (a : Fin 7) : 3 * weight a 0 + 5 * weight a 1 = 3 - (a : ℤ) := by
    fin_cases a <;> decide
  have hlt : (i : ℤ) < j := by exact_mod_cast hijlt
  have hwi := hw i
  have hwj := hw j
  omega

/-- Each numbered raising root is intrinsically simple: its height is one, while every intrinsic
positive root has strictly positive integral height. This does not assert exhaustion of the
intrinsic simple roots. -/
theorem isSimpleRoot_simpleRootCharacter (i : Fin 2) :
    splitMaximalTorus.IsSimpleRoot positiveDefiningIdeal (simpleRootCharacter i) := by
  rw [SplitMaximalTorus.isSimpleRoot_iff]
  refine ⟨isPositiveRoot_simpleRootCharacter i, ?_⟩
  intro β γ hβ hγ heq
  have hβh := height_pos_of_isPositiveRoot β hβ
  have hγh := height_pos_of_isPositiveRoot γ hγ
  have hh := simpleRootCharacter_height i
  rw [heq] at hh
  simp only [Finsupp.add_apply] at hh
  omega

end

end TauCeti.G2ShortRoot.PrimeField
