/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.BifunctorHomotopy
public import TauCeti.Algebra.Homology.Monoidal.Homology.Cross
public import TauCeti.Algebra.Homology.Semisimple

/-!
# The Künneth map on the homology of a tensor product of complexes

Let `K` and `L` be homological complexes in a preadditive monoidal category `C`, with a shape
`c` carrying tensor signs.  The cross products `Hₚ(K) ⊗ H_q(L) ⟶ Hₙ(K ⊗ L)` for `p + q = n`
(`HomologicalComplex.homologyCross`) assemble into the **Künneth map**

`⨁_{p + q = n} Hₚ(K) ⊗ H_q(L) ⟶ Hₙ(K ⊗ L)`,

whose source is the degree `n` part of the tensor product of the graded objects `H(K)` and `H(L)`.
It is natural in both complexes.  The Künneth theorem for chain complexes of vector spaces over a
field asserts that it is an isomorphism.  This file proves the two formal steps of that theorem
which hold in any such category:

* when `K` and `L` have zero differentials, the Künneth map is an isomorphism, since then each
  homology object is the corresponding term of the complex and `Hₙ(K ⊗ L)` is the coproduct of
  the `K.X p ⊗ L.X q` with `p + q = n`;
* the Künneth map of `K` and `L` is an isomorphism exactly when that of homotopy equivalent
  complexes `K'` and `L'` is, because homotopy equivalences induce isomorphisms on homology and
  their tensor product is again a homotopy equivalence (`HomotopyEquiv.mapBifunctor`).

Combining the two, the Künneth map is an isomorphism whenever `K` and `L` are homotopy equivalent
to complexes with zero differential.  A complex of modules is of this kind when its cycles split
off its terms and its homology splits off its cycles
(`HomologicalComplex.exists_homotopyEquiv_d_eq_zero`).  Every complex of semisimple modules, in
particular every complex of vector spaces over a field, satisfies this, which gives the
**Künneth theorem over a field**.  So does a complex whose cycles split off and whose homology is
projective, for instance a complex of free modules over a principal ideal domain with free
homology.

## Main definitions and results

* `HomologicalComplex.homologyKunneth`: the Künneth map, characterized on summands by
  `HomologicalComplex.ι_homologyKunneth`.
* `HomologicalComplex.homologyKunneth_naturality`: naturality in both complexes.
* `HomologicalComplex.isIso_homologyKunneth_of_d_eq_zero`: the Künneth map is an isomorphism
  for complexes with zero differentials.
* `HomologicalComplex.isIso_homologyKunneth_iff_of_homotopyEquiv`: invariance of this property
  under homotopy equivalences.
* `HomologicalComplex.isIso_homologyKunneth_of_homotopyEquiv_of_d_eq_zero`: the Künneth map is
  an isomorphism for complexes homotopy equivalent to complexes with zero differentials.
* `HomologicalComplex.isIso_homologyKunneth_of_isSplitMono_of_isSplitEpi`: the Künneth theorem
  for complexes of modules over a commutative ring whose cycles and homology split off, for
  instance complexes of vector spaces over a field.

## References

* C. Weibel, *An Introduction to Homological Algebra*, Section 3.6, the Künneth formula.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

namespace HomologicalComplex

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  {I : Type*} [AddMonoid I] {c : ComplexShape I} [c.TensorSigns] [DecidableEq I]

section Kunneth

variable (K L : HomologicalComplex C c) [HasTensor K L] (n : I)
  [∀ p, K.HasHomology p] [∀ q, L.HasHomology q] [(tensorObj K L).HasHomology n]
  [∀ p, PreservesColimitsOfShape WalkingParallelPair (tensorLeft (K.homology p))]
  [∀ q, PreservesColimitsOfShape WalkingParallelPair (tensorRight (L.cycles q))]
  [∀ q, PreservesColimitsOfShape WalkingParallelPair (tensorRight (L.X (c.prev q)))]
  [GradedObject.HasTensor (fun p ↦ K.homology p) (fun q ↦ L.homology q)]

/-- **The Künneth map** `⨁_{p + q = n} Hₚ(K) ⊗ H_q(L) ⟶ Hₙ(K ⊗ L)`, whose restriction to the
summand `Hₚ(K) ⊗ H_q(L)` is the cross product `HomologicalComplex.homologyCross`. -/
def homologyKunneth :
    GradedObject.Monoidal.tensorObj (fun p ↦ K.homology p) (fun q ↦ L.homology q) n ⟶
      (tensorObj K L).homology n :=
  GradedObject.Monoidal.tensorObjDesc fun p q h ↦ homologyCross K L p q n h

/-- The Künneth map restricts to the cross product on each summand. -/
@[reassoc (attr := simp)]
lemma ι_homologyKunneth (p q : I) (h : p + q = n) :
    GradedObject.Monoidal.ιTensorObj (fun p ↦ K.homology p) (fun q ↦ L.homology q) p q n h ≫
      homologyKunneth K L n = homologyCross K L p q n h :=
  GradedObject.Monoidal.ι_tensorObjDesc _ _ _ _

end Kunneth

section Naturality

variable {K L K' L' : HomologicalComplex C c} [HasTensor K L] [HasTensor K' L']
  (φ : K ⟶ K') (ψ : L ⟶ L') (n : I)
  [∀ p, K.HasHomology p] [∀ q, L.HasHomology q] [(tensorObj K L).HasHomology n]
  [∀ p, PreservesColimitsOfShape WalkingParallelPair (tensorLeft (K.homology p))]
  [∀ q, PreservesColimitsOfShape WalkingParallelPair (tensorRight (L.cycles q))]
  [∀ q, PreservesColimitsOfShape WalkingParallelPair (tensorRight (L.X (c.prev q)))]
  [GradedObject.HasTensor (fun p ↦ K.homology p) (fun q ↦ L.homology q)]
  [∀ p, K'.HasHomology p] [∀ q, L'.HasHomology q] [(tensorObj K' L').HasHomology n]
  [∀ p, PreservesColimitsOfShape WalkingParallelPair (tensorLeft (K'.homology p))]
  [∀ q, PreservesColimitsOfShape WalkingParallelPair (tensorRight (L'.cycles q))]
  [∀ q, PreservesColimitsOfShape WalkingParallelPair (tensorRight (L'.X (c.prev q)))]
  [GradedObject.HasTensor (fun p ↦ K'.homology p) (fun q ↦ L'.homology q)]

/-- **Naturality of the Künneth map** in both complexes. -/
@[reassoc]
lemma homologyKunneth_naturality :
    GradedObject.Monoidal.tensorHom (fun p ↦ homologyMap φ p) (fun q ↦ homologyMap ψ q) n ≫
        homologyKunneth K' L' n =
      homologyKunneth K L n ≫ homologyMap (tensorHom φ ψ) n := by
  ext p q h
  simp [homologyCross_naturality]

/-- The Künneth map of `K` and `L` is an isomorphism if and only if the Künneth map of homotopy
equivalent complexes `K'` and `L'` is. -/
theorem isIso_homologyKunneth_iff_of_homotopyEquiv (eK : HomotopyEquiv K K')
    (eL : HomotopyEquiv L L') :
    IsIso (homologyKunneth K L n) ↔ IsIso (homologyKunneth K' L' n) := by
  have e := homologyKunneth_naturality eK.hom eL.hom n
  have : IsIso (GradedObject.Monoidal.tensorHom (fun p ↦ homologyMap eK.hom p)
      (fun q ↦ homologyMap eL.hom q)) :=
    (GradedObject.Monoidal.tensorIso (GradedObject.isoMk _ _ fun p ↦ eK.toHomologyIso p)
      (GradedObject.isoMk _ _ fun q ↦ eL.toHomologyIso q)).isIso_hom
  have : IsIso (homologyMap (tensorHom eK.hom eL.hom) n) := by
    rw [tensorHom, ← HomotopyEquiv.mapBifunctor_hom (F := curriedTensor C) (c := c) eK eL]
    exact ((HomotopyEquiv.mapBifunctor (curriedTensor C) c eK eL).toHomologyIso n).isIso_hom
  rw [← isIso_comp_right_iff (homologyKunneth K L n) (homologyMap (tensorHom eK.hom eL.hom) n),
    ← e, isIso_comp_left_iff]

end Naturality

section ZeroDifferential

variable {K L : HomologicalComplex C c} [HasTensor K L]

/-- If `K` and `L` have zero differentials, so does `K ⊗ L`. -/
private lemma tensorObj_d_eq_zero (hK : ∀ i j, K.d i j = 0) (hL : ∀ i j, L.d i j = 0)
    (i j : I) : (tensorObj K L).d i j = 0 := by
  ext p q h
  rw [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂, comp_zero]
  by_cases h₁ : c.Rel p (c.next p)
  · by_cases h₂ : c.Rel q (c.next q)
    · simp [mapBifunctor.d₁_eq' _ _ _ _ h₁, mapBifunctor.d₂_eq' _ _ _ _ _ h₂, hK, hL]
    · simp [mapBifunctor.d₁_eq' _ _ _ _ h₁, mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ h₂, hK]
  · by_cases h₂ : c.Rel q (c.next q)
    · simp [mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ h₁, mapBifunctor.d₂_eq' _ _ _ _ _ h₂, hL]
    · simp [mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ h₁, mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ h₂]

/-- For a complex with zero differentials, the isomorphism `K.X i ≅ K.homology i`. -/
private def xIsoHomology (K : HomologicalComplex C c) (hK : ∀ i j, K.d i j = 0) (i : I)
    [K.HasHomology i] : K.X i ≅ K.homology i :=
  (K.iCyclesIso i _ rfl (hK _ _)).symm ≪≫ K.isoHomologyπ _ i rfl (hK _ _)

variable (n : I)
  [∀ p, K.HasHomology p] [∀ q, L.HasHomology q] [(tensorObj K L).HasHomology n]
  [∀ p, PreservesColimitsOfShape WalkingParallelPair (tensorLeft (K.homology p))]
  [∀ q, PreservesColimitsOfShape WalkingParallelPair (tensorRight (L.cycles q))]
  [∀ q, PreservesColimitsOfShape WalkingParallelPair (tensorRight (L.X (c.prev q)))]
  [GradedObject.HasTensor (fun p ↦ K.homology p) (fun q ↦ L.homology q)]

omit [GradedObject.HasTensor (fun p ↦ K.homology p) (fun q ↦ L.homology q)] in
/-- For complexes with zero differentials, the cross product of the classes of two chains is the
class of their tensor product. -/
private lemma xIsoHomology_tensorHom_homologyCross (hK : ∀ i j, K.d i j = 0)
    (hL : ∀ i j, L.d i j = 0) (p q : I) (h : p + q = n) :
    ((xIsoHomology K hK p).hom ⊗ₘ (xIsoHomology L hL q).hom) ≫ homologyCross K L p q n h =
      ιTensorObj K L p q n h ≫
        (xIsoHomology (tensorObj K L) (tensorObj_d_eq_zero hK hL) n).hom := by
  have hcross : ((K.iCyclesIso p _ rfl (hK _ _)).inv ⊗ₘ (L.iCyclesIso q _ rfl (hL _ _)).inv) ≫
      cyclesCross K L p q n h =
        ιTensorObj K L p q n h ≫
          ((tensorObj K L).iCyclesIso n _ rfl (tensorObj_d_eq_zero hK hL _ _)).inv := by
    simp [← cancel_mono ((tensorObj K L).iCycles n), tensorHom_comp_tensorHom_assoc]
  simp [xIsoHomology, ← tensorHom_comp_tensorHom_assoc, reassoc_of% hcross]

/-- **The Künneth map is an isomorphism for complexes with zero differentials**: then
`Hₙ(K ⊗ L) = (K ⊗ L)ₙ` is the direct sum of the `K.X p ⊗ L.X q = Hₚ(K) ⊗ H_q(L)` with
`p + q = n`. -/
theorem isIso_homologyKunneth_of_d_eq_zero (hK : ∀ i j, K.d i j = 0)
    (hL : ∀ i j, L.d i j = 0) : IsIso (homologyKunneth K L n) := by
  let e := xIsoHomology (tensorObj K L) (tensorObj_d_eq_zero hK hL) n
  refine ⟨e.inv ≫ mapBifunctorDesc fun p q h ↦
    ((xIsoHomology K hK p).hom ⊗ₘ (xIsoHomology L hL q).hom) ≫
      GradedObject.Monoidal.ιTensorObj (fun p ↦ K.homology p) (fun q ↦ L.homology q) p q n h,
    ?_, ?_⟩
  · refine GradedObject.Monoidal.tensorObj_ext _ _ fun p q h ↦ ?_
    rw [← cancel_epi ((xIsoHomology K hK p).hom ⊗ₘ (xIsoHomology L hL q).hom)]
    simp [reassoc_of% xIsoHomology_tensorHom_homologyCross n hK hL p q h]
  · rw [← cancel_epi e.hom, Category.assoc, e.hom_inv_id_assoc, Category.comp_id]
    ext p q h
    simp [xIsoHomology_tensorHom_homologyCross n hK hL p q h, e]

end ZeroDifferential

section HomotopyEquiv

variable {K L K' L' : HomologicalComplex C c} [HasTensor K L] [HasTensor K' L'] (n : I)
  [∀ p, K.HasHomology p] [∀ q, L.HasHomology q] [(tensorObj K L).HasHomology n]
  [∀ p, PreservesColimitsOfShape WalkingParallelPair (tensorLeft (K.homology p))]
  [∀ q, PreservesColimitsOfShape WalkingParallelPair (tensorRight (L.cycles q))]
  [∀ q, PreservesColimitsOfShape WalkingParallelPair (tensorRight (L.X (c.prev q)))]
  [GradedObject.HasTensor (fun p ↦ K.homology p) (fun q ↦ L.homology q)]
  [∀ p, K'.HasHomology p] [∀ q, L'.HasHomology q] [(tensorObj K' L').HasHomology n]
  [∀ p, PreservesColimitsOfShape WalkingParallelPair (tensorLeft (K'.homology p))]
  [∀ q, PreservesColimitsOfShape WalkingParallelPair (tensorRight (L'.cycles q))]
  [∀ q, PreservesColimitsOfShape WalkingParallelPair (tensorRight (L'.X (c.prev q)))]
  [GradedObject.HasTensor (fun p ↦ K'.homology p) (fun q ↦ L'.homology q)]

/-- **The Künneth map is an isomorphism for complexes homotopy equivalent to complexes with zero
differentials.**  Every chain complex of vector spaces over a field is of this kind, since its
cycles and boundaries split off as direct summands. -/
theorem isIso_homologyKunneth_of_homotopyEquiv_of_d_eq_zero (eK : HomotopyEquiv K K')
    (eL : HomotopyEquiv L L') (hK' : ∀ i j, K'.d i j = 0) (hL' : ∀ i j, L'.d i j = 0) :
    IsIso (homologyKunneth K L n) :=
  (isIso_homologyKunneth_iff_of_homotopyEquiv n eK eL).mpr
    (isIso_homologyKunneth_of_d_eq_zero n hK' hL')

end HomotopyEquiv

section Split

universe u

variable {R : Type u} [CommRing R] {I : Type*} [Small.{u} I] [AddMonoid I] {c : ComplexShape I}
  [c.TensorSigns] [DecidableEq I] (K L : HomologicalComplex (ModuleCat.{u} R) c) (n : I)
  [∀ i, IsSplitMono (K.iCycles i)] [∀ i, IsSplitEpi (K.homologyπ i)]
  [∀ i, IsSplitMono (L.iCycles i)] [∀ i, IsSplitEpi (L.homologyπ i)]

/-- **The Künneth theorem for split complexes**: for complexes `K` and `L` of modules over a
commutative ring `R` whose cycles split off their terms and whose homology splits off their cycles,
the Künneth map `⨁_{p + q = n} Hₚ(K) ⊗ H_q(L) ⟶ Hₙ(K ⊗ L)` is an isomorphism.  This applies to
complexes of semisimple modules, for instance of vector spaces over a field
(`HomologicalComplex.isSplitMono_iCycles_of_isSemisimpleModule`), and to complexes whose cycles
split off and whose homology is projective
(`HomologicalComplex.isSplitEpi_homologyπ_of_projective`). -/
instance isIso_homologyKunneth_of_isSplitMono_of_isSplitEpi : IsIso (homologyKunneth K L n) := by
  obtain ⟨K', hK', ⟨eK⟩⟩ := K.exists_homotopyEquiv_d_eq_zero
  obtain ⟨L', hL', ⟨eL⟩⟩ := L.exists_homotopyEquiv_d_eq_zero
  exact isIso_homologyKunneth_of_homotopyEquiv_of_d_eq_zero n eK eL hK' hL'

end Split

end HomologicalComplex
