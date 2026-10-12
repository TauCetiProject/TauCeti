/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
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
factor has flat terms (`HomologicalComplex.isIso_homologyKunneth_of_d_eq_zero_of_flat`), here for
complexes of modules indexed by `ℕ` and an arbitrary second factor `L`.  Since the terms of `K`
are flat, tensoring with `K` preserves the short exact sequence `0 ⟶ Z(L) ⟶ L ⟶ L / Z(L) ⟶ 0` of
`HomologicalComplex.cyclesComplexShortComplex`, whose outer terms have zero differentials.  By
`HomologicalComplex.homologyCross_comp_δ`, the connecting morphisms of the tensored sequence are,
up to sign, the tensor products of the flat modules `Kₚ` with the connecting morphisms of the
cycle sequence of `L`, which are monomorphisms.  The long exact homology sequence therefore
identifies `Hₙ(K ⊗ L)` with a cokernel, which is `⨁ Kₚ ⊗ H_q(L)` by right exactness.

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
* `HomologicalComplex.isIso_homologyKunneth_of_d_eq_zero_of_flat`: the Künneth theorem when one
  complex of modules has zero differentials and flat terms.

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

variable {R : Type u} [CommRing R] (K : ChainComplex (ModuleCat.{u} R) ℕ)
  {L L' : ChainComplex (ModuleCat.{u} R) ℕ}

/-- The Künneth map is compatible with replacing the second complex by an equal one. -/
@[reassoc]
lemma homologyKunneth_comp_eqToHom (e : L' = L) (n : ℕ) :
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

variable {R : Type u} [CommRing R] (K L : ChainComplex (ModuleCat.{u} R) ℕ)

/-- The automorphism of the graded object `H(K)` which is multiplication by the sign
`ε(p) = (-1)ᵖ` in degree `p`. -/
abbrev homologySign : (fun p ↦ K.homology p) ⟶ (fun p ↦ K.homology p) :=
  fun p ↦ ((ComplexShape.down ℕ).ε p : ℤ) • 𝟙 (K.homology p)

/-- On the summand `Hₚ(K) ⊗ H_{q + 1}(L / Z(L))`, the connecting morphism of
`Z(L) ⟶ L ⟶ L / Z(L)` followed by the map `H(Z(L)) ⟶ H(L)` vanishes, and hence so does the
composite of the corresponding maps of tensor products of graded objects. -/
private lemma tensorHom_δ_comp_tensorHom (n : ℕ) :
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
`ε(p)` times `Hₚ(K)` tensored with the connecting morphism of `Z(L) ⟶ L ⟶ L / Z(L)`. -/
lemma homologyKunneth_comp_δ
    (hKS : (tensorLeftShortComplex K L.cyclesComplexShortComplex).ShortExact) (m : ℕ) :
    homologyKunneth K L.cyclesComplexShortComplex.X₃ (m + 1) ≫ hKS.δ (m + 1) m (by simp) =
      (GradedObject.Monoidal.tensorObjSuccIso (fun p ↦ K.homology p)
          (fun q ↦ L.cyclesComplexShortComplex.X₃.homology q)
          L.isZero_homology_cyclesComplexShortComplex_X₃_zero m).inv ≫
        GradedObject.Monoidal.tensorHom (homologySign K)
          (fun q ↦ L.cyclesComplexShortComplex_shortExact.δ (q + 1) q (by simp)) m ≫
        homologyKunneth K L.cyclesComplexShortComplex.X₁ m := by
  refine GradedObject.Monoidal.tensorObj_ext _ _ fun p q h ↦ ?_
  obtain _ | q := q
  · exact ((tensorLeft _).map_isZero
      L.isZero_homology_cyclesComplexShortComplex_X₃_zero).eq_of_src _ _
  · rw [ι_homologyKunneth_assoc, homologyCross_comp_δ K L.cyclesComplexShortComplex_shortExact
      _ (q' := q) (by simp) h (by omega : p + q = m)]
    simp [zsmul_tensorHom, id_tensorHom]

variable [∀ p, Module.Flat R (K.X p)]

/-- If `K` has flat terms, tensoring with `K` preserves the short exact sequence
`0 ⟶ Z(L) ⟶ L ⟶ L / Z(L) ⟶ 0`. -/
private lemma shortExact_tensorLeft_cyclesComplexShortComplex :
    (tensorLeftShortComplex K L.cyclesComplexShortComplex).ShortExact :=
  shortExact_tensorLeftShortComplex_of_preservesFiniteLimits K
    L.cyclesComplexShortComplex_shortExact fun n ↦
      (Finset.antidiagonal n).finite_toSet.subset fun x hx ↦ by simpa using hx

variable (hK : ∀ i j, K.d i j = 0)
include hK

/-- If `K` has zero differentials and flat terms, the connecting morphisms of
`K ⊗ Z(L) ⟶ K ⊗ L ⟶ K ⊗ (L / Z(L))` are monomorphisms. -/
private lemma mono_δ (m : ℕ) :
    Mono ((shortExact_tensorLeft_cyclesComplexShortComplex K L).δ
      (m + 1) m (by simp)) := by
  have (p : ℕ) : Module.Flat R (K.homology p) :=
    .of_linearEquiv ((K.iCyclesIso p _ rfl (hK _ _)).symm ≪≫
      K.isoHomologyπ _ p rfl (hK _ _)).symm.toLinearEquiv
  -- each summand is `±` the flat module `Hₚ(K)` tensored with a monomorphism
  have (p q : ℕ) : Mono (homologySign K p ⊗ₘ
      L.cyclesComplexShortComplex_shortExact.δ (q + 1) q (by simp)) := by
    have := L.mono_δ_cyclesComplexShortComplex (i := q + 1) (j := q) (by simp)
    have : Mono (K.homology p ◁ L.cyclesComplexShortComplex_shortExact.δ (q + 1) q (by simp)) :=
      (tensorLeft (K.homology p)).map_mono _
    rcases Int.units_eq_one_or ((ComplexShape.down ℕ).ε p) with h | h <;>
      simp only [h, Units.val_one, Units.val_neg, one_smul, neg_smul, zsmul_tensorHom,
        id_tensorHom] <;> infer_instance
  have : Mono (GradedObject.Monoidal.tensorHom (homologySign K)
      (fun q ↦ L.cyclesComplexShortComplex_shortExact.δ (q + 1) q (by simp)) m) :=
    GradedObject.Monoidal.mono_tensorHom _ _ m ((Finset.antidiagonal m).finite_toSet.subset
      fun x hx ↦ by simpa using hx)
  have := isIso_homologyKunneth_of_d_eq_zero m hK (L := L.cyclesComplexShortComplex.X₁)
    L.cyclesComplexShortComplex_X₁_d
  have := isIso_homologyKunneth_of_d_eq_zero (m + 1) hK (L := L.cyclesComplexShortComplex.X₃)
    L.cyclesComplexShortComplex_X₃_d
  rw [← mono_comp_iff_of_isIso (homologyKunneth K L.cyclesComplexShortComplex.X₃ (m + 1)),
    homologyKunneth_comp_δ (shortExact_tensorLeft_cyclesComplexShortComplex K L)]
  infer_instance

/-- If `K` has zero differentials and flat terms, the map `K ⊗ L ⟶ K ⊗ (L / Z(L))` induces zero
on homology: in positive degrees it is followed by the monomorphism `δ`, and in degree zero the
target `H₀(K ⊗ (L / Z(L)))` vanishes. -/
private lemma homologyMap_tensorHom_g_eq_zero (m : ℕ) :
    homologyMap (tensorHom (𝟙 K) L.cyclesComplexShortComplex.g) m = 0 := by
  cases m with
  | zero =>
    have := isIso_homologyKunneth_of_d_eq_zero 0 hK (L := L.cyclesComplexShortComplex.X₃)
      L.cyclesComplexShortComplex_X₃_d
    refine IsZero.eq_of_tgt (IsZero.of_iso ?_
      (asIso (homologyKunneth K L.cyclesComplexShortComplex.X₃ 0)).symm) _ _
    rw [IsZero.iff_id_eq_zero]
    refine GradedObject.Monoidal.tensorObj_ext _ _ fun p q h ↦ ?_
    obtain rfl : q = 0 := by omega
    exact ((tensorLeft _).map_isZero
      L.isZero_homology_cyclesComplexShortComplex_X₃_zero).eq_of_src _ _
  | succ m =>
    have := mono_δ K L hK m
    have hm : (ComplexShape.down ℕ).Rel (m + 1) m := by simp
    rw [← cancel_mono ((shortExact_tensorLeft_cyclesComplexShortComplex K L).δ (m + 1) m hm),
      zero_comp]
    exact (shortExact_tensorLeft_cyclesComplexShortComplex K L).comp_δ _ _ _

/-- **The Künneth theorem when one factor has zero differentials and flat terms.**  If `K` is a
complex of flat modules with zero differentials, so that `Hₚ(K) = Kₚ`, then for every complex `L`
the Künneth map `⨁_{p + q = n} Hₚ(K) ⊗ H_q(L) ⟶ Hₙ(K ⊗ L)` is an
isomorphism.  For instance, for a flat module `M` placed in degree zero this says that tensoring
`L` with `M` commutes with homology. -/
theorem isIso_homologyKunneth_of_d_eq_zero_of_flat (n : ℕ) : IsIso (homologyKunneth K L n) := by
  -- `L` is the middle term of `S = L.cyclesComplexShortComplex`; we write it as such so that the
  -- three terms of `S` appear uniformly
  rw [← L.cyclesComplexShortComplex_X₂]
  have hKS := shortExact_tensorLeft_cyclesComplexShortComplex K L
  have := isIso_homologyKunneth_of_d_eq_zero n hK (L := L.cyclesComplexShortComplex.X₁)
    L.cyclesComplexShortComplex_X₁_d
  -- `Hₙ(K ⊗ L)` is the cokernel of `δ : Hₙ₊₁(K ⊗ (L / Z(L))) ⟶ Hₙ(K ⊗ Z(L))`, since the map
  -- `Hₙ(K ⊗ L) ⟶ Hₙ(K ⊗ (L / Z(L)))` vanishes
  have (m : ℕ) : Epi (homologyMap (tensorHom (𝟙 K) L.cyclesComplexShortComplex.f) m) :=
    (hKS.homology_exact₂ m).epi_f (homologyMap_tensorHom_g_eq_zero K L hK m)
  have hn : (ComplexShape.down ℕ).Rel (n + 1) n := by simp
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

end HomologicalComplex
