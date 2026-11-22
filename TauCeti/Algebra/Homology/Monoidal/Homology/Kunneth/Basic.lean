/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import TauCeti.Algebra.Category.ModuleCat.AB
public import Mathlib.RingTheory.Flat.CategoryTheory
public import TauCeti.Algebra.Homology.Bifunctor.Homotopy
public import TauCeti.Algebra.Homology.CyclesComplex
public import TauCeti.Algebra.Homology.Monoidal.Homology.Connecting
public import TauCeti.Algebra.Homology.Monoidal.Homology.Cross
public import TauCeti.Algebra.Homology.Semisimple
public import TauCeti.CategoryTheory.GradedObject.Monoidal
public import TauCeti.CategoryTheory.Monoidal.Preadditive

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
projective.  In particular, a complex of free modules over a principal ideal domain with free
homology is of this kind, since its cycles split off
(`HomologicalComplex.isSplitMono_iCycles_of_isPrincipalIdealRing`).

When only the cycles of `K` and `L` split off, as for complexes of free modules over a principal
ideal domain, the Künneth map is still a split monomorphism
(`HomologicalComplex.isSplitMono_homologyKunneth`): by naturality it is split by the map induced
by the projections onto the complexes of homology objects, which induce isomorphisms on homology
(`HomologicalComplex.isIso_homologyMap_toHomologyComplex`).  This retraction need not be natural.

When only one factor has zero differentials, the Künneth map is still an isomorphism provided that
factor has flat terms (`HomologicalComplex.isIso_homologyKunneth_of_d_eq_zero_of_flat`), here
for chain complexes of modules indexed by any additive right cancellative monoid `I` carrying
tensor signs, such as `ℕ`, and an arbitrary second factor `L`.  Since the terms of `K` are flat,
tensoring with `K` preserves the short exact sequence `0 ⟶ Z(L) ⟶ L ⟶ L / Z(L) ⟶ 0` of
`HomologicalComplex.cyclesComplexShortComplex`, whose outer terms have zero differentials.  By
`HomologicalComplex.homologyCross_comp_δ`, the connecting morphisms of the tensored sequence are,
up to sign, the tensor products of the flat modules `Kₚ` with the connecting morphisms of the
cycle sequence of `L`, which are monomorphisms.  The long exact homology sequence therefore
identifies `Hₙ(K ⊗ L)` with a cokernel, which is `⨁ Kₚ ⊗ H_q(L)` by right exactness.  The same
argument, tensoring the cycle sequence of `K` on the right with `L` and using
`HomologicalComplex.homologyCross_comp_δ_right`, gives the theorem when the second factor has zero
differentials and flat terms, for indices which in addition commute
(`HomologicalComplex.isIso_homologyKunneth_of_d_eq_zero_of_flat_right`).

When the Künneth map is an isomorphism and the homology modules are free of finite rank, the ranks
of the homology of `K ⊗ L` follow from the ranks of the degree `n` part of a tensor product of
graded modules (`CategoryTheory.GradedObject.Monoidal.finrank_tensorObj`):
`rank Hₙ(K ⊗ L) = ∑_{p + q = n} rank Hₚ(K) · rank H_q(L)`.

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
* `HomologicalComplex.isSplitMono_homologyKunneth`: the Künneth map is a split monomorphism for
  complexes of modules whose cycles split off.
* `HomologicalComplex.isIso_homologyKunneth_of_d_eq_zero_of_flat` and
  `HomologicalComplex.isIso_homologyKunneth_of_d_eq_zero_of_flat_right`: the Künneth theorem when
  the first, respectively the second, complex of modules has zero differentials and flat terms.
* `CategoryTheory.GradedObject.Monoidal.finrank_tensorObj`: the rank of the degree `n` part of
  the tensor product of graded modules that are free of finite rank in each degree.

## References

* C. Weibel, *An Introduction to Homological Algebra*, Section 3.6, the Künneth formula, and the
  proof of Theorem 3.6.3 for the cycle sequence argument.
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
    ((K.iCyclesIso p _ rfl (hK _ _)).inv ≫ K.homologyπ p ⊗ₘ
      (L.iCyclesIso q _ rfl (hL _ _)).inv ≫ L.homologyπ q) ≫ homologyCross K L p q n h =
      ιTensorObj K L p q n h ≫
        ((tensorObj K L).iCyclesIso n _ rfl (tensorObj_d_eq_zero hK hL _ _)).inv ≫
          (tensorObj K L).homologyπ n := by
  have hcross : ((K.iCyclesIso p _ rfl (hK _ _)).inv ⊗ₘ (L.iCyclesIso q _ rfl (hL _ _)).inv) ≫
      cyclesCross K L p q n h =
        ιTensorObj K L p q n h ≫
          ((tensorObj K L).iCyclesIso n _ rfl (tensorObj_d_eq_zero hK hL _ _)).inv := by
    simp [← cancel_mono ((tensorObj K L).iCycles n), tensorHom_comp_tensorHom_assoc]
  simp [← tensorHom_comp_tensorHom_assoc, reassoc_of% hcross]

/-- **The Künneth map is an isomorphism for complexes with zero differentials**: then
`Hₙ(K ⊗ L) = (K ⊗ L)ₙ` is the direct sum of the `K.X p ⊗ L.X q = Hₚ(K) ⊗ H_q(L)` with
`p + q = n`. -/
theorem isIso_homologyKunneth_of_d_eq_zero (hK : ∀ i j, K.d i j = 0)
    (hL : ∀ i j, L.d i j = 0) : IsIso (homologyKunneth K L n) := by
  let e := (tensorObj K L).XIsoHomologyOfDEqZero n (tensorObj_d_eq_zero hK hL _ _)
    (tensorObj_d_eq_zero hK hL _ _)
  refine ⟨e.inv ≫ mapBifunctorDesc fun p q h ↦
    ((K.XIsoHomologyOfDEqZero p (hK _ _) (hK _ _)).hom ⊗ₘ
      (L.XIsoHomologyOfDEqZero q (hL _ _) (hL _ _)).hom) ≫
      GradedObject.Monoidal.ιTensorObj (fun p ↦ K.homology p) (fun q ↦ L.homology q) p q n h,
    ?_, ?_⟩
  · refine GradedObject.Monoidal.tensorObj_ext _ _ fun p q h ↦ ?_
    rw [← cancel_epi ((K.XIsoHomologyOfDEqZero p (hK _ _) (hK _ _)).hom ⊗ₘ
      (L.XIsoHomologyOfDEqZero q (hL _ _) (hL _ _)).hom)]
    simp [reassoc_of% xIsoHomology_tensorHom_homologyCross n hK hL p q h, e]
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
  [∀ p, K'.HasHomology p] [∀ q, L'.HasHomology q]
  [∀ p, PreservesColimitsOfShape WalkingParallelPair (tensorLeft (K'.homology p))]
  [∀ q, PreservesColimitsOfShape WalkingParallelPair (tensorRight (L'.cycles q))]
  [∀ q, PreservesColimitsOfShape WalkingParallelPair (tensorRight (L'.X (c.prev q)))]
  [GradedObject.HasTensor (fun p ↦ K'.homology p) (fun q ↦ L'.homology q)]

/-- **The Künneth map is an isomorphism for complexes homotopy equivalent to complexes with zero
differentials.**  Every chain complex of vector spaces over a field is of this kind, since its
cycles and boundaries split off as direct summands. -/
theorem isIso_homologyKunneth_of_homotopyEquiv_of_d_eq_zero (eK : HomotopyEquiv K K')
    (eL : HomotopyEquiv L L') (hK' : ∀ i j, K'.d i j = 0) (hL' : ∀ i j, L'.d i j = 0) :
    IsIso (homologyKunneth K L n) := by
  -- a complex with zero differentials has homology everywhere
  have : (tensorObj K' L').HasHomology n :=
    ShortComplex.HasHomology.mk' (ShortComplex.HomologyData.ofZeros _
      (tensorObj_d_eq_zero hK' hL' _ _) (tensorObj_d_eq_zero hK' hL' _ _))
  exact (isIso_homologyKunneth_iff_of_homotopyEquiv n eK eL).mpr
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

section SplitMono

universe u

variable {R : Type u} [CommRing R] {I : Type*} [Small.{u} I] [AddMonoid I] {c : ComplexShape I}
  [c.TensorSigns] [DecidableEq I] (K L : HomologicalComplex (ModuleCat.{u} R) c) (n : I)
  [∀ i, IsSplitMono (K.iCycles i)] [∀ i, IsSplitMono (L.iCycles i)]

/-- **The Künneth map is a split monomorphism** for complexes `K` and `L` of modules over a
commutative ring whose cycles split off their terms, for instance complexes of projective modules
over a principal ideal domain (`HomologicalComplex.isSplitMono_iCycles_of_isPrincipalIdealRing`).
A retraction is induced by the projections `K ⟶ H(K)` and `L ⟶ H(L)` onto the complexes of
homology objects (`HomologicalComplex.toHomologyComplex`), which depend on the chosen splittings of
the cycles, so it need not be natural in `K` and `L`. -/
theorem isSplitMono_homologyKunneth : IsSplitMono (homologyKunneth K L n) := by
  have := isIso_homologyKunneth_of_d_eq_zero n (K := K.homologyComplex) (L := L.homologyComplex)
    (by simp) (by simp)
  have : IsIso (GradedObject.Monoidal.tensorHom (fun p ↦ homologyMap K.toHomologyComplex p)
      (fun q ↦ homologyMap L.toHomologyComplex q)) :=
    (GradedObject.Monoidal.tensorIso
      (GradedObject.isoMk _ _ fun p ↦ asIso (homologyMap K.toHomologyComplex p))
      (GradedObject.isoMk _ _ fun q ↦ asIso (homologyMap L.toHomologyComplex q))).isIso_hom
  -- by naturality, the Künneth map of `K` and `L` followed by the map induced by the projections
  -- is the isomorphism induced on homology objects followed by the Künneth map of the complexes
  -- of homology objects, also an isomorphism
  exact .mk' ⟨homologyMap (tensorHom K.toHomologyComplex L.toHomologyComplex) n ≫
    inv (homologyKunneth K.homologyComplex L.homologyComplex n) ≫
      inv (GradedObject.Monoidal.tensorHom (fun p ↦ homologyMap K.toHomologyComplex p)
        (fun q ↦ homologyMap L.toHomologyComplex q) n), by
    rw [← homologyKunneth_naturality_assoc, IsIso.hom_inv_id_assoc, IsIso.hom_inv_id]⟩

end SplitMono

section EqToHom

universe u

variable {R : Type u} [CommRing R] {I : Type*} [Small.{u} I] [AddMonoid I] {c : ComplexShape I}
  [c.TensorSigns] [DecidableEq I] (K : HomologicalComplex (ModuleCat.{u} R) c)
  {L L' : HomologicalComplex (ModuleCat.{u} R) c}

/-- The Künneth map is compatible with replacing the second complex by an equal one. -/
@[reassoc]
lemma homologyKunneth_comp_eqToHom (e : L' = L) (n : I) :
    homologyKunneth K L' n ≫ eqToHom (congrArg (fun M ↦ (tensorObj K M).homology n) e) =
      GradedObject.Monoidal.tensorHom (𝟙 (fun p ↦ K.homology p))
        (fun q ↦ eqToHom (congrArg (fun M ↦ M.homology q) e)) n ≫ homologyKunneth K L n := by
  subst e
  refine GradedObject.Monoidal.tensorObj_ext _ _ fun p q h ↦ ?_
  simp

end EqToHom

section FlatZeroDifferential

/-! ### One factor with zero differentials and flat terms -/

universe u

variable {R : Type u} [CommRing R] {I : Type*} [Small.{u} I] [AddRightCancelMonoid I] [One I]
  [(ComplexShape.down I).TensorSigns] [DecidableEq I] (K L : ChainComplex (ModuleCat.{u} R) I)

/-- The automorphism of the graded object `H(K)` which is multiplication by the sign `ε(p)` of the
tensor product of chain complexes in degree `p`, for instance `(-1)ᵖ` for complexes indexed
by `ℕ`. -/
abbrev homologySign : (fun p ↦ K.homology p) ⟶ (fun p ↦ K.homology p) :=
  fun p ↦ ((ComplexShape.down I).ε p : ℤ) • 𝟙 (K.homology p)

omit [DecidableEq I] in
/-- On the summand `Hₚ(K) ⊗ H_{q + 1}(L / Z(L))`, the connecting morphism of
`Z(L) ⟶ L ⟶ L / Z(L)` followed by the map `H(Z(L)) ⟶ H(L)` vanishes, and hence so does the
composite of the corresponding maps of tensor products of graded objects. -/
private lemma tensorHom_δ_comp_tensorHom (n : I) :
    GradedObject.Monoidal.tensorHom (homologySign K)
        (fun q ↦ L.cyclesComplexShortComplex_shortExact.δ (q + 1) q (by simp)) n ≫
      GradedObject.Monoidal.tensorHom (𝟙 fun p ↦ K.homology p)
        (fun q ↦ homologyMap L.cyclesComplexShortComplex.f q) n = 0 := by
  refine GradedObject.Monoidal.tensorObj_ext _ _ fun p q h ↦ ?_
  simp only [GradedObject.Monoidal.ι_tensorHom_assoc, GradedObject.Monoidal.ι_tensorHom,
    zsmul_tensorHom, Pi.id_apply, id_tensorHom, Preadditive.zsmul_comp, ← whiskerLeft_comp_assoc,
    ShortComplex.ShortExact.δ_comp, MonoidalPreadditive.whiskerLeft_zero, zero_comp, smul_zero,
    comp_zero]

variable {K L} in
/-- The connecting morphisms of `K ⊗ Z(L) ⟶ K ⊗ L ⟶ K ⊗ (L / Z(L))`, read through the Künneth
maps, whenever this sequence is short exact: on the summand `Hₚ(K) ⊗ H_{q + 1}(L / Z(L))` it is
`ε(p)` times `Hₚ(K)` tensored with the connecting morphism of `Z(L) ⟶ L ⟶ L / Z(L)`.  The summands
`Hₚ(K) ⊗ H_q(L / Z(L))` with `q` not of the form `q' + 1` vanish. -/
lemma homologyKunneth_comp_δ
    (hKS : (tensorLeftShortComplex K L.cyclesComplexShortComplex).ShortExact) (m : I) :
    homologyKunneth K L.cyclesComplexShortComplex.X₃ (m + 1) ≫ hKS.δ (m + 1) m (by simp) =
      (GradedObject.Monoidal.tensorObjSuccIso (fun p ↦ K.homology p)
          (fun q ↦ L.cyclesComplexShortComplex.X₃.homology q)
          (fun _ ↦ L.isZero_homology_cyclesComplexShortComplex_X₃_of_forall_add_one_ne) m).inv ≫
        GradedObject.Monoidal.tensorHom (homologySign K)
          (fun q ↦ L.cyclesComplexShortComplex_shortExact.δ (q + 1) q (by simp)) m ≫
        homologyKunneth K L.cyclesComplexShortComplex.X₁ m := by
  refine GradedObject.Monoidal.tensorObj_ext _ _ fun p q h ↦ ?_
  by_cases hq : ∃ q', q' + 1 = q
  · obtain ⟨q, rfl⟩ := hq
    have h' : p + q = m := add_right_cancel (b := 1) (by rw [add_assoc, h])
    rw [ι_homologyKunneth_assoc, homologyCross_comp_δ K L.cyclesComplexShortComplex_shortExact
      _ (q' := q) (by simp) h h']
    simp [zsmul_tensorHom, id_tensorHom]
  · exact ((tensorLeft _).map_isZero
      (L.isZero_homology_cyclesComplexShortComplex_X₃_of_forall_add_one_ne
        (not_exists.1 hq))).eq_of_src _ _

variable [∀ p, Module.Flat R (K.X p)]

/-- If `K` has flat terms, tensoring with `K` preserves the short exact sequence
`0 ⟶ Z(L) ⟶ L ⟶ L / Z(L) ⟶ 0`. -/
private lemma shortExact_tensorLeft_cyclesComplexShortComplex :
    (tensorLeftShortComplex K L.cyclesComplexShortComplex).ShortExact :=
  shortExact_tensorLeftShortComplex_of_preservesFiniteLimits K
    L.cyclesComplexShortComplex_shortExact

variable (hK : ∀ i j, K.d i j = 0)
include hK

/-- If `K` has zero differentials and flat terms, the connecting morphisms of
`K ⊗ Z(L) ⟶ K ⊗ L ⟶ K ⊗ (L / Z(L))` are monomorphisms. -/
private lemma mono_δ (m : I) :
    Mono ((shortExact_tensorLeft_cyclesComplexShortComplex K L).δ
      (m + 1) m (by simp)) := by
  have (p : I) : Module.Flat R (K.homology p) :=
    .of_linearEquiv (K.XIsoHomologyOfDEqZero p (hK _ _) (hK _ _)).symm.toLinearEquiv
  -- each summand is `±` the flat module `Hₚ(K)` tensored with a monomorphism
  have (p q : I) : Mono (homologySign K p ⊗ₘ
      L.cyclesComplexShortComplex_shortExact.δ (q + 1) q (by simp)) := by
    have := L.mono_δ_cyclesComplexShortComplex (i := q + 1) (j := q) (by simp)
    have : Mono (K.homology p ◁ L.cyclesComplexShortComplex_shortExact.δ (q + 1) q (by simp)) :=
      (tensorLeft (K.homology p)).map_mono _
    rcases Int.units_eq_one_or ((ComplexShape.down I).ε p) with h | h <;>
      simp only [h, Units.val_one, Units.val_neg, one_smul, neg_smul, zsmul_tensorHom,
        id_tensorHom] <;> infer_instance
  have : Mono (GradedObject.Monoidal.tensorHom (homologySign K)
      (fun q ↦ L.cyclesComplexShortComplex_shortExact.δ (q + 1) q (by simp)) m) :=
    GradedObject.Monoidal.mono_tensorHom _ _ m
  have := isIso_homologyKunneth_of_d_eq_zero m hK (L := L.cyclesComplexShortComplex.X₁)
    L.cyclesComplexShortComplex_X₁_d
  have := isIso_homologyKunneth_of_d_eq_zero (m + 1) hK (L := L.cyclesComplexShortComplex.X₃)
    L.cyclesComplexShortComplex_X₃_d
  rw [← mono_comp_iff_of_isIso (homologyKunneth K L.cyclesComplexShortComplex.X₃ (m + 1)),
    homologyKunneth_comp_δ (shortExact_tensorLeft_cyclesComplexShortComplex K L)]
  infer_instance

/-- If `K` has zero differentials and flat terms, the map `K ⊗ L ⟶ K ⊗ (L / Z(L))` induces zero
on homology: in a degree `m + 1` it is followed by the monomorphism `δ`, and in a degree not of
this form, such as degree zero for complexes indexed by `ℕ`, the target `Hₘ(K ⊗ (L / Z(L)))`
vanishes. -/
private lemma homologyMap_tensorHom_g_eq_zero (m : I) :
    homologyMap (tensorHom (𝟙 K) L.cyclesComplexShortComplex.g) m = 0 := by
  by_cases hm : ∃ m', m' + 1 = m
  · obtain ⟨m, rfl⟩ := hm
    have := mono_δ K L hK m
    have hm : (ComplexShape.down I).Rel (m + 1) m := by simp
    rw [← cancel_mono ((shortExact_tensorLeft_cyclesComplexShortComplex K L).δ (m + 1) m hm),
      zero_comp]
    exact (shortExact_tensorLeft_cyclesComplexShortComplex K L).comp_δ _ _ _
  · have := isIso_homologyKunneth_of_d_eq_zero m hK (L := L.cyclesComplexShortComplex.X₃)
      L.cyclesComplexShortComplex_X₃_d
    refine IsZero.eq_of_tgt (IsZero.of_iso ?_
      (asIso (homologyKunneth K L.cyclesComplexShortComplex.X₃ m)).symm) _ _
    rw [IsZero.iff_id_eq_zero]
    refine GradedObject.Monoidal.tensorObj_ext _ _ fun p q h ↦ ?_
    -- each summand `Hₚ(K) ⊗ H_q(L / Z(L))` vanishes, since `q` is not of the form `q' + 1`
    have hq (q' : I) : q' + 1 ≠ q := fun hq ↦ hm ⟨p + q', by rw [add_assoc, hq, h]⟩
    exact ((tensorLeft _).map_isZero
      (L.isZero_homology_cyclesComplexShortComplex_X₃_of_forall_add_one_ne hq)).eq_of_src _ _

/-- **The Künneth theorem when one factor has zero differentials and flat terms.**  If `K` is a
complex of flat modules with zero differentials, so that `Hₚ(K) = Kₚ`, then for every complex `L`
the Künneth map `⨁_{p + q = n} Hₚ(K) ⊗ H_q(L) ⟶ Hₙ(K ⊗ L)` is an
isomorphism.  For instance, for a flat module `M` placed in degree zero this says that tensoring
`L` with `M` commutes with homology. -/
theorem isIso_homologyKunneth_of_d_eq_zero_of_flat (n : I) : IsIso (homologyKunneth K L n) := by
  -- `L` is the middle term of `S = L.cyclesComplexShortComplex`; we write it as such so that the
  -- three terms of `S` appear uniformly
  rw [← L.cyclesComplexShortComplex_X₂]
  have hKS := shortExact_tensorLeft_cyclesComplexShortComplex K L
  have := isIso_homologyKunneth_of_d_eq_zero n hK (L := L.cyclesComplexShortComplex.X₁)
    L.cyclesComplexShortComplex_X₁_d
  -- `Hₙ(K ⊗ L)` is the cokernel of `δ : Hₙ₊₁(K ⊗ (L / Z(L))) ⟶ Hₙ(K ⊗ Z(L))`, since the map
  -- `Hₙ(K ⊗ L) ⟶ Hₙ(K ⊗ (L / Z(L)))` vanishes
  have (m : I) : Epi (homologyMap (tensorHom (𝟙 K) L.cyclesComplexShortComplex.f) m) :=
    (hKS.homology_exact₂ m).epi_f (homologyMap_tensorHom_g_eq_zero K L hK m)
  have hn : (ComplexShape.down I).Rel (n + 1) n := by simp
  have hcoker := (hKS.homology_exact₁ (n + 1) n hn).gIsCokernel
  -- the inverse of the Künneth map is induced by `Z(L) ⟶ L` through this cokernel
  let T := GradedObject.Monoidal.tensorHom (𝟙 fun p ↦ K.homology p)
    (fun q ↦ homologyMap L.cyclesComplexShortComplex.f q) n
  have hT : hKS.δ (n + 1) n hn ≫ inv (homologyKunneth K L.cyclesComplexShortComplex.X₁ n) ≫ T =
      0 := by
    have := isIso_homologyKunneth_of_d_eq_zero (n + 1) hK (L := L.cyclesComplexShortComplex.X₃)
      L.cyclesComplexShortComplex_X₃_d
    rw [← cancel_epi (homologyKunneth K L.cyclesComplexShortComplex.X₃ (n + 1)),
      reassoc_of% (homologyKunneth_comp_δ (shortExact_tensorLeft_cyclesComplexShortComplex K L) n)]
    simp [T, tensorHom_δ_comp_tensorHom]
  let ψ : (tensorObj K L.cyclesComplexShortComplex.X₂).homology n ⟶
      GradedObject.Monoidal.tensorObj (fun p ↦ K.homology p)
        (fun q ↦ L.cyclesComplexShortComplex.X₂.homology q) n :=
    hcoker.desc (CokernelCofork.ofπ (inv (homologyKunneth K L.cyclesComplexShortComplex.X₁ n) ≫ T)
      hT)
  have hψ : homologyMap (tensorHom (𝟙 K) L.cyclesComplexShortComplex.f) n ≫ ψ =
      inv (homologyKunneth K L.cyclesComplexShortComplex.X₁ n) ≫ T :=
    hcoker.fac _ WalkingParallelPair.one
  refine ⟨ψ, GradedObject.Monoidal.tensorObj_ext _ _ fun p q h ↦ ?_, ?_⟩
  · -- check on the classes of cycles of `L`, which come from `Z(L)`
    have : Epi (K.homology p ◁ homologyMap L.cyclesComplexShortComplex.f q) :=
      (tensorLeft (K.homology p)).map_epi _
    -- the naturality of the cross product in `Z(L) ⟶ L`
    have hnat : (K.homology p ◁ homologyMap L.cyclesComplexShortComplex.f q) ≫
        homologyCross K L.cyclesComplexShortComplex.X₂ p q n h =
          homologyCross K L.cyclesComplexShortComplex.X₁ p q n h ≫
            homologyMap (tensorHom (𝟙 K) L.cyclesComplexShortComplex.f) n := by
      simpa using homologyCross_naturality (𝟙 K) L.cyclesComplexShortComplex.f p q n h
    rw [← cancel_epi (K.homology p ◁ homologyMap L.cyclesComplexShortComplex.f q),
      ι_homologyKunneth_assoc, reassoc_of% hnat, hψ, ← ι_homologyKunneth_assoc]
    simp [T]
  · -- `homologyKunneth_naturality` is stated for the graded map `p ↦ homologyMap (𝟙 K) p`
    have hid : (fun p ↦ homologyMap (𝟙 K) p) = 𝟙 fun p ↦ K.homology p :=
      funext fun p ↦ homologyMap_id K p
    have hnat := homologyKunneth_naturality (𝟙 K) L.cyclesComplexShortComplex.f n
    rw [hid] at hnat
    rw [← cancel_epi (homologyMap (tensorHom (𝟙 K) L.cyclesComplexShortComplex.f) n),
      reassoc_of% hψ, Category.comp_id, IsIso.inv_comp_eq, hnat]

end FlatZeroDifferential

section FlatZeroDifferentialRight

/-! ### The second factor with zero differentials and flat terms -/

universe u

variable {R : Type u} [CommRing R] {I : Type*} [Small.{u} I] [AddCancelCommMonoid I] [One I]
  [(ComplexShape.down I).TensorSigns] [DecidableEq I] (K L : ChainComplex (ModuleCat.{u} R) I)

omit [(ComplexShape.down I).TensorSigns] [DecidableEq I] in
/-- On the summand `H_{p + 1}(K / Z(K)) ⊗ H_q(L)`, the connecting morphism of
`Z(K) ⟶ K ⟶ K / Z(K)` followed by the map `H(Z(K)) ⟶ H(K)` vanishes, and hence so does the
composite of the corresponding maps of tensor products of graded objects. -/
private lemma tensorHom_δ_comp_tensorHom_right (n : I) :
    GradedObject.Monoidal.tensorHom
        (fun p ↦ K.cyclesComplexShortComplex_shortExact.δ (p + 1) p (by simp))
        (𝟙 fun q ↦ L.homology q) n ≫
      GradedObject.Monoidal.tensorHom (fun p ↦ homologyMap K.cyclesComplexShortComplex.f p)
        (𝟙 fun q ↦ L.homology q) n = 0 := by
  refine GradedObject.Monoidal.tensorObj_ext _ _ fun p q h ↦ ?_
  simp only [GradedObject.Monoidal.ι_tensorHom_assoc, GradedObject.Monoidal.ι_tensorHom,
    Pi.id_apply, tensorHom_id, ← comp_whiskerRight_assoc, ShortComplex.ShortExact.δ_comp,
    MonoidalPreadditive.zero_whiskerRight, zero_comp, comp_zero]

variable {K L} in
/-- The connecting morphisms of `Z(K) ⊗ L ⟶ K ⊗ L ⟶ (K / Z(K)) ⊗ L`, read through the Künneth
maps, whenever this sequence is short exact: on the summand `H_{p + 1}(K / Z(K)) ⊗ H_q(L)` it is
the connecting morphism of `Z(K) ⟶ K ⟶ K / Z(K)` tensored with `H_q(L)`.  The summands
`Hₚ(K / Z(K)) ⊗ H_q(L)` with `p` not of the form `p' + 1` vanish. -/
lemma homologyKunneth_comp_δ_right
    (hSL : (tensorRightShortComplex L K.cyclesComplexShortComplex).ShortExact) (m : I) :
    homologyKunneth K.cyclesComplexShortComplex.X₃ L (m + 1) ≫ hSL.δ (m + 1) m (by simp) =
      (GradedObject.Monoidal.succTensorObjIso
          (fun p ↦ K.cyclesComplexShortComplex.X₃.homology p) (fun q ↦ L.homology q)
          (fun _ ↦ K.isZero_homology_cyclesComplexShortComplex_X₃_of_forall_add_one_ne) m).inv ≫
        GradedObject.Monoidal.tensorHom
          (fun p ↦ K.cyclesComplexShortComplex_shortExact.δ (p + 1) p (by simp))
          (𝟙 fun q ↦ L.homology q) m ≫
        homologyKunneth K.cyclesComplexShortComplex.X₁ L m := by
  refine GradedObject.Monoidal.tensorObj_ext _ _ fun p q h ↦ ?_
  by_cases hp : ∃ p', p' + 1 = p
  · obtain ⟨p, rfl⟩ := hp
    have h' : p + q = m := add_right_cancel (b := 1) (by rw [← h, add_right_comm])
    rw [ι_homologyKunneth_assoc, homologyCross_comp_δ_right L
      K.cyclesComplexShortComplex_shortExact _ (p' := p) (by simp) h h']
    simp [tensorHom_id]
  · exact ((tensorRight _).map_isZero
      (K.isZero_homology_cyclesComplexShortComplex_X₃_of_forall_add_one_ne
        (not_exists.1 hp))).eq_of_src _ _

variable [∀ q, Module.Flat R (L.X q)]

/-- If `L` has flat terms, tensoring on the right with `L` preserves the short exact sequence
`0 ⟶ Z(K) ⟶ K ⟶ K / Z(K) ⟶ 0`. -/
private lemma shortExact_tensorRight_cyclesComplexShortComplex :
    (tensorRightShortComplex L K.cyclesComplexShortComplex).ShortExact :=
  shortExact_tensorRightShortComplex_of_preservesFiniteLimits L
    K.cyclesComplexShortComplex_shortExact

variable (hL : ∀ i j, L.d i j = 0)
include hL

/-- If `L` has zero differentials and flat terms, the connecting morphisms of
`Z(K) ⊗ L ⟶ K ⊗ L ⟶ (K / Z(K)) ⊗ L` are monomorphisms. -/
private lemma mono_δ_right (m : I) :
    Mono ((shortExact_tensorRight_cyclesComplexShortComplex K L).δ
      (m + 1) m (by simp)) := by
  have (q : I) : Module.Flat R (L.homology q) :=
    .of_linearEquiv (L.XIsoHomologyOfDEqZero q (hL _ _) (hL _ _)).symm.toLinearEquiv
  -- each summand is a monomorphism tensored with the flat module `H_q(L)`
  have (p q : I) : Mono (K.cyclesComplexShortComplex_shortExact.δ (p + 1) p (by simp) ⊗ₘ
      𝟙 (L.homology q)) := by
    have := K.mono_δ_cyclesComplexShortComplex (i := p + 1) (j := p) (by simp)
    rw [tensorHom_id]
    exact (tensorRight (L.homology q)).map_mono _
  have : Mono (GradedObject.Monoidal.tensorHom
      (fun p ↦ K.cyclesComplexShortComplex_shortExact.δ (p + 1) p (by simp))
      (𝟙 fun q ↦ L.homology q) m) :=
    GradedObject.Monoidal.mono_tensorHom _ _ m
  have := isIso_homologyKunneth_of_d_eq_zero m (K := K.cyclesComplexShortComplex.X₁)
    K.cyclesComplexShortComplex_X₁_d hL
  have := isIso_homologyKunneth_of_d_eq_zero (m + 1) (K := K.cyclesComplexShortComplex.X₃)
    K.cyclesComplexShortComplex_X₃_d hL
  rw [← mono_comp_iff_of_isIso (homologyKunneth K.cyclesComplexShortComplex.X₃ L (m + 1)),
    homologyKunneth_comp_δ_right (shortExact_tensorRight_cyclesComplexShortComplex K L)]
  infer_instance

/-- If `L` has zero differentials and flat terms, the map `K ⊗ L ⟶ (K / Z(K)) ⊗ L` induces zero
on homology: in a degree `m + 1` it is followed by the monomorphism `δ`, and in a degree not of
this form the target `Hₘ((K / Z(K)) ⊗ L)` vanishes. -/
private lemma homologyMap_tensorHom_g_eq_zero_right (m : I) :
    homologyMap (tensorHom K.cyclesComplexShortComplex.g (𝟙 L)) m = 0 := by
  by_cases hm : ∃ m', m' + 1 = m
  · obtain ⟨m, rfl⟩ := hm
    have := mono_δ_right K L hL m
    have hm : (ComplexShape.down I).Rel (m + 1) m := by simp
    rw [← cancel_mono ((shortExact_tensorRight_cyclesComplexShortComplex K L).δ (m + 1) m hm),
      zero_comp]
    exact (shortExact_tensorRight_cyclesComplexShortComplex K L).comp_δ _ _ _
  · have := isIso_homologyKunneth_of_d_eq_zero m (K := K.cyclesComplexShortComplex.X₃)
      K.cyclesComplexShortComplex_X₃_d hL
    refine IsZero.eq_of_tgt (IsZero.of_iso ?_
      (asIso (homologyKunneth K.cyclesComplexShortComplex.X₃ L m)).symm) _ _
    rw [IsZero.iff_id_eq_zero]
    refine GradedObject.Monoidal.tensorObj_ext _ _ fun p q h ↦ ?_
    -- each summand `Hₚ(K / Z(K)) ⊗ H_q(L)` vanishes, since `p` is not of the form `p' + 1`
    have hp (p' : I) : p' + 1 ≠ p := fun hp ↦ hm ⟨p' + q, by rw [add_right_comm, hp, h]⟩
    exact ((tensorRight _).map_isZero
      (K.isZero_homology_cyclesComplexShortComplex_X₃_of_forall_add_one_ne hp)).eq_of_src _ _

/-- The connecting morphism `Hₙ₊₁((K / Z(K)) ⊗ L) ⟶ Hₙ(Z(K) ⊗ L)`, read through the Künneth
isomorphism of `Z(K)` and `L`, is killed by the map induced by the inclusion `Z(K) ⟶ K`. -/
private lemma δ_comp_inv_homologyKunneth_comp_tensorHom_right (n : I) :
    (shortExact_tensorRight_cyclesComplexShortComplex K L).δ (n + 1) n (by simp) ≫
      (have := isIso_homologyKunneth_of_d_eq_zero n (K := K.cyclesComplexShortComplex.X₁)
        K.cyclesComplexShortComplex_X₁_d hL
      inv (homologyKunneth K.cyclesComplexShortComplex.X₁ L n)) ≫
      GradedObject.Monoidal.tensorHom (fun p ↦ homologyMap K.cyclesComplexShortComplex.f p)
        (𝟙 fun q ↦ L.homology q) n = 0 := by
  have := isIso_homologyKunneth_of_d_eq_zero (n + 1) (K := K.cyclesComplexShortComplex.X₃)
    K.cyclesComplexShortComplex_X₃_d hL
  rw [← cancel_epi (homologyKunneth K.cyclesComplexShortComplex.X₃ L (n + 1)),
    reassoc_of% (homologyKunneth_comp_δ_right
      (shortExact_tensorRight_cyclesComplexShortComplex K L) n)]
  simp [tensorHom_δ_comp_tensorHom_right]

/-- **The Künneth theorem when the second factor has zero differentials and flat terms.**  If `L`
is a complex of flat modules with zero differentials, so that `H_q(L) = L_q`, then for every
complex `K` the Künneth map `⨁_{p + q = n} Hₚ(K) ⊗ H_q(L) ⟶ Hₙ(K ⊗ L)` is an isomorphism.  This
is `HomologicalComplex.isIso_homologyKunneth_of_d_eq_zero_of_flat` with the factors interchanged,
proved by tensoring the cycle sequence of `K` on the right with `L`. -/
theorem isIso_homologyKunneth_of_d_eq_zero_of_flat_right (n : I) :
    IsIso (homologyKunneth K L n) := by
  -- `K` is the middle term of `S = K.cyclesComplexShortComplex`; we write it as such so that the
  -- three terms of `S` appear uniformly
  rw [← K.cyclesComplexShortComplex_X₂]
  have hSL := shortExact_tensorRight_cyclesComplexShortComplex K L
  have := isIso_homologyKunneth_of_d_eq_zero n (K := K.cyclesComplexShortComplex.X₁)
    K.cyclesComplexShortComplex_X₁_d hL
  -- `Hₙ(K ⊗ L)` is the cokernel of `δ : Hₙ₊₁((K / Z(K)) ⊗ L) ⟶ Hₙ(Z(K) ⊗ L)`, since the map
  -- `Hₙ(K ⊗ L) ⟶ Hₙ((K / Z(K)) ⊗ L)` vanishes
  have (m : I) : Epi (homologyMap (tensorHom K.cyclesComplexShortComplex.f (𝟙 L)) m) :=
    (hSL.homology_exact₂ m).epi_f (homologyMap_tensorHom_g_eq_zero_right K L hL m)
  have hn : (ComplexShape.down I).Rel (n + 1) n := by simp
  have hcoker := (hSL.homology_exact₁ (n + 1) n hn).gIsCokernel
  -- the inverse of the Künneth map is induced by `Z(K) ⟶ K` through this cokernel
  let T := GradedObject.Monoidal.tensorHom
    (fun p ↦ homologyMap K.cyclesComplexShortComplex.f p) (𝟙 fun q ↦ L.homology q) n
  have hT := δ_comp_inv_homologyKunneth_comp_tensorHom_right K L hL n
  let ψ : (tensorObj K.cyclesComplexShortComplex.X₂ L).homology n ⟶
      GradedObject.Monoidal.tensorObj (fun p ↦ K.cyclesComplexShortComplex.X₂.homology p)
        (fun q ↦ L.homology q) n :=
    hcoker.desc (CokernelCofork.ofπ (inv (homologyKunneth K.cyclesComplexShortComplex.X₁ L n) ≫ T)
      hT)
  have hψ : homologyMap (tensorHom K.cyclesComplexShortComplex.f (𝟙 L)) n ≫ ψ =
      inv (homologyKunneth K.cyclesComplexShortComplex.X₁ L n) ≫ T :=
    hcoker.fac _ WalkingParallelPair.one
  refine ⟨ψ, GradedObject.Monoidal.tensorObj_ext _ _ fun p q h ↦ ?_, ?_⟩
  · -- check on the classes of cycles of `K`, which come from `Z(K)`
    have : Epi (homologyMap K.cyclesComplexShortComplex.f p ▷ L.homology q) :=
      (tensorRight (L.homology q)).map_epi _
    -- the naturality of the cross product in `Z(K) ⟶ K`
    have hnat : (homologyMap K.cyclesComplexShortComplex.f p ▷ L.homology q) ≫
        homologyCross K.cyclesComplexShortComplex.X₂ L p q n h =
          homologyCross K.cyclesComplexShortComplex.X₁ L p q n h ≫
            homologyMap (tensorHom K.cyclesComplexShortComplex.f (𝟙 L)) n := by
      simpa using homologyCross_naturality K.cyclesComplexShortComplex.f (𝟙 L) p q n h
    rw [← cancel_epi (homologyMap K.cyclesComplexShortComplex.f p ▷ L.homology q),
      ι_homologyKunneth_assoc, reassoc_of% hnat, hψ, ← ι_homologyKunneth_assoc]
    simp [T]
  · -- `homologyKunneth_naturality` is stated for the graded map `q ↦ homologyMap (𝟙 L) q`
    have hid : (fun q ↦ homologyMap (𝟙 L) q) = 𝟙 fun q ↦ L.homology q :=
      funext fun q ↦ homologyMap_id L q
    have hnat := homologyKunneth_naturality K.cyclesComplexShortComplex.f (𝟙 L) n
    rw [hid] at hnat
    rw [← cancel_epi (homologyMap (tensorHom K.cyclesComplexShortComplex.f (𝟙 L)) n),
      reassoc_of% hψ, Category.comp_id, IsIso.inv_comp_eq, hnat]

end FlatZeroDifferentialRight

section ModuleCatCross

/-! ### The cross product on classes of cycles of complexes of modules -/

universe u

open scoped TensorProduct

variable {R : Type u} [CommRing R] {I : Type*} [AddMonoid I] {c : ComplexShape I}
  [c.TensorSigns] [DecidableEq I] (K L : HomologicalComplex (ModuleCat.{u} R) c)
  {M : HomologicalComplex (ModuleCat.{u} R) c} [HasTensor K L] (p q n : I) (h : p + q = n)
  [K.HasHomology p] [L.HasHomology q] [(tensorObj K L).HasHomology n] [M.HasHomology n]
  [PreservesColimitsOfShape WalkingParallelPair (tensorLeft (K.homology p))]
  [PreservesColimitsOfShape WalkingParallelPair (tensorRight (L.cycles q))]
  [PreservesColimitsOfShape WalkingParallelPair (tensorRight (L.X (c.prev q)))]

/-- Element-wise form of `HomologicalComplex.homologyπ_tensorHom_homologyCross`, followed by a
chain map `φ` out of the tensor product: `φ` sends the cross product of the classes of cycles `z`
and `w` to the class of the image under `φ` of the cycle `z ⊗ w`. -/
theorem moduleCat_homologyMap_homologyCross_tmul (φ : tensorObj K L ⟶ M) (z : K.cycles p)
    (w : L.cycles q) :
    (homologyMap φ n).hom
        ((homologyCross K L p q n h).hom (K.homologyπ p z ⊗ₜ L.homologyπ q w)) =
      M.homologyπ n ((cyclesMap φ n).hom ((cyclesCross K L p q n h).hom (z ⊗ₜ w))) := by
  have h' := congrArg (fun f ↦ f.hom (z ⊗ₜ w))
    (homologyπ_tensorHom_homologyCross_assoc K L p q n h (homologyMap φ n))
  rw [homologyπ_naturality] at h'
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul] at h'
  exact h'

end ModuleCatCross

end HomologicalComplex

namespace CategoryTheory.GradedObject.Monoidal

universe u v

variable {k : Type u} [CommRing k] {I : Type v} [AddMonoid I] [Finset.HasAntidiagonal I]
  (A B : GradedObject I (ModuleCat.{u} k)) [HasTensor A B]
  [∀ p, Module.Free k (A p)] [∀ p, Module.Finite k (A p)]
  [∀ q, Module.Free k (B q)] [∀ q, Module.Finite k (B q)]

/-- **The rank of a tensor product of graded modules.** Over a nontrivial commutative ring, if `A`
and `B` are free of finite rank in each degree, then the degree `n` part
`⨁_{p + q = n} Aₚ ⊗ B_q` of their tensor product has rank `∑_{p + q = n} rank Aₚ · rank B_q`.
Composed with a Künneth isomorphism, this computes the ranks of the homology of a tensor product
of complexes. -/
theorem finrank_tensorObj [Nontrivial k] (n : I) :
    Module.finrank k (tensorObj A B n : ModuleCat.{u} k) =
      ∑ x ∈ Finset.antidiagonal n, Module.finrank k (A x.1) * Module.finrank k (B x.2) := by
  classical
  let P := (fun x : I × I ↦ x.1 + x.2) ⁻¹' {n}
  let e : P ≃ Finset.antidiagonal n := Equiv.subtypeEquivRight fun x ↦ by simp [P]
  have := Fintype.ofEquiv _ e.symm
  let ε := (Fintype.equivFin P).symm
  -- The degree `n` part of the tensor product is by definition the coproduct of the summands.
  -- Reindexing it by `Fin _` keeps the index type in universe `0`, as `coprodIsoDirectSum`
  -- requires the index universe to be at most the module universe.
  have iso : (tensorObj A B n : ModuleCat.{u} k) ≅ ModuleCat.of k
      (DirectSum (Fin (Fintype.card P)) fun j ↦ TensorProduct k (A (ε j).val.1) (B (ε j).val.2)) :=
    (Sigma.reindex ε fun i : P ↦ A i.val.1 ⊗ B i.val.2).symm ≪≫
      ModuleCat.coprodIsoDirectSum fun j ↦ A (ε j).val.1 ⊗ B (ε j).val.2
  rw [iso.toLinearEquiv.finrank_eq, Module.finrank_directSum,
    ← Finset.sum_coe_sort (Finset.antidiagonal n)]
  exact Fintype.sum_equiv (ε.trans e) _ _ fun x ↦ Module.finrank_tensorProduct

end CategoryTheory.GradedObject.Monoidal
