/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.RepresentationTheory.Rep.Iso
public import TauCeti.AlgebraicTopology.Cellular.Augmentation
public import TauCeti.AlgebraicTopology.Cellular.Equivariant
public import TauCeti.AlgebraicTopology.Cellular.LocalDegree
public import TauCeti.GroupTheory.GroupAction.Free
public import TauCeti.RepresentationTheory.FreeOfBasis
public import TauCeti.Topology.CWComplex.Classical.CellAction
public import TauCeti.Topology.CWComplex.Classical.OrbitSpace

/-!
# Cellular chains of free cellular group actions

Let a group `G` act continuously on a Hausdorff CW complex `C`, carrying each open `n`-cell onto
an open `n`-cell (`g • openCell n i = openCell n j`) with trivial cell stabilizers. Unlike the
lifted CW structure `TauCeti.cwComplexPreimage` studied in
`TauCeti.AlgebraicTopology.Cellular.Covering`, translations here need not carry the characteristic
map of a cell strictly onto the characteristic map of the translated cell: for example, a group
acting by simplicial automorphisms on the realization of a simplicial complex need not preserve the
chosen vertex ordering, so translations may reverse cell orientations.

This file shows that the cellular chains of `C` still form a complex of free `R[G]`-modules, with
an explicit `R[G]`-basis given by the cellular basis vectors of one chosen representative in each
cell orbit — or, along any compatible quotient covering map `p : E → B`, one chosen lift over each
cell of `B` — and therefore give a `ProjectiveResolution (Rep.trivial R G R)` whenever `C` is
contractible.

1. **Cellular maps preserving closed cells** (`section ClosedCellMap`): if a cellular map between
   relative CW complexes sends `closedCell n i` into `closedCell n i'`, then the image of the
   `i`-th summand of the `n`-th cellular chain group vanishes in the local homology
   `Hₙ(Yⁿ, Yⁿ ∖ {x})` at every point `x` of any open `n`-cell `j ≠ i'`. Over a ring `R`, reading
   off cellular coordinates via `TauCeti.cellularChainBasis_repr_apply_eq_inv_cellLocalClass` shows
   that `f` sends `cellularChainBasis C R n i` to a scalar multiple of
   `cellularChainBasis C' R n i'`
   (`TauCeti.cellularChainGroupMap_cellularChainBasis_of_mapsTo_closedCell`).
2. **Equivariant cellular chains and orientation units** (`section MonoidAction` and
   `section GroupBasis`): continuous translations preserving open cells are cellular
   (`TauCeti.isCellular_cellActionSMul`), assembling the cellular chains into a complex
   `TauCeti.cellActionChainComplex` in `Rep R G`. Each `g : G` sends the basis vector of `i` to
   `cellActionCoeff C hcell R n g i • cellularChainBasis C R n (g • i)`, where the scalars satisfy
   the cocycle law `c(g * h, i) = c(h, i) * c(g, h • i)`. When `G` is a group, `c(g, i)` has
   two-sided inverse `c(g⁻¹, g • i)` over any (not necessarily commutative) ring `R`, packaging
   into a unit `TauCeti.cellActionUnit`. Scaling the cellular basis along an orbit parametrization
   `e ⟨i, g⟩ = g • s i` yields an `R`-basis `TauCeti.cellActionBasis` on which `G` acts by pure
   left translation: `cellActionBasis (e ⟨i, g⟩) = ρ g (cellularChainBasis C R n (s i))`.
3. **Free `R[G]`-bases and projective resolutions** (`section FreeRep`, `section QuotientCover`,
   `section Augmentation`, and `section Resolution`): over a commutative ring `R`,
   `TauCeti.cellActionRepIsoFreeOfEquiv` identifies the `n`-th cellular chain representation with
   `Rep.free R G ι`. Specializing to orbits gives `TauCeti.cellActionRepIsoFreeOrbit`, and
   specializing to chosen lifts `s b` over the cells of `B` along a quotient covering map
   `p : E → B` gives `IsQuotientCoveringMap.cellActionRepIsoFree` and
   `IsQuotientCoveringMap.cellActionRepIsoFreeQuotient`. Naturality of
   `TauCeti.cellularAugmentation` equips the complex with an equivariant augmentation
   `TauCeti.cellActionChainComplexAugmentation`, which is a quasi-isomorphism when `C` is
   contractible (`TauCeti.quasiIso_cellActionChainComplexAugmentation`), assembling into
   `TauCeti.cellActionResolution`.

## Main definitions and results

* `TauCeti.cellularChainGroupMap_cellularChainBasis_of_mapsTo_closedCell`: a cellular map sending
  `closedCell n i` into `closedCell n i'` sends the basis vector of `i` to a scalar multiple of the
  basis vector of `i'`.
* `TauCeti.cellActionRepresentation`, `TauCeti.cellActionChainComplex`, and
  `TauCeti.cellActionChainComplexForget₂Iso`: the equivariant cellular chain complex of an action
  preserving open cells.
* `TauCeti.cellActionCoeff` and `TauCeti.cellActionUnit`: the orientation scalar and unit by which
  translation acts on a cellular basis vector.
* `TauCeti.cellActionBasis`: the rescaled cellular `R`-basis freely permuted by `G`.
* `TauCeti.cellActionRepIsoFreeOfEquiv`, `TauCeti.cellActionRepIsoFreeOrbit`,
  `IsQuotientCoveringMap.cellActionRepIsoFree`, and
  `IsQuotientCoveringMap.cellActionRepIsoFreeQuotient`: freeness of the cellular chains over `R[G]`,
  with basis one chosen representative per orbit or one chosen lift per base cell.
* `TauCeti.cellActionAugmentation`, `TauCeti.cellActionChainComplexAugmentation`,
  `TauCeti.quasiIso_cellActionChainComplexAugmentation`, and `TauCeti.cellActionResolution`: the
  equivariant cellular augmentation and projective resolution of `Rep.trivial R G R`.

## References

* T. tom Dieck, *Transformation Groups*, de Gruyter, 1987, Section II.1 and Section II.2 (free
  `G`-CW complexes and their cellular chain complexes).
* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section I.4.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Section 2.2.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex
open scoped Pointwise

universe w v u

namespace TauCeti

section ClosedCellMap

variable {X Y : Type w} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
  {D : Set X} {E : Set Y} (C : Set X) [RelCWComplex C D] (C' : Set Y) [RelCWComplex C' E]
  {f : TopCat.of C ⟶ TopCat.of C'} (hf : IsCellular C C' f)

/-- If a cellular map sends `closedCell n i` into `closedCell n i'`, then the summand of `i` in the
cellular chain group vanishes in the local homology at any point `x` of an open `n`-cell `j ≠ i'`.
-/
@[reassoc]
lemma ι_cellularChainGroupIso_inv_comp_cellularChainGroupMap_comp_local_of_ne
    {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
    {n : ℕ} [HasExactColimitsOfShape (Discrete (cell C n)) A]
    {i : cell C n} {i' j : cell C' n}
    (hclosed : ∀ z ∈ closedCell n i, ∀ hz : z ∈ C, (f ⟨z, hz⟩ : Y) ∈ closedCell n i')
    (x : skeletonObj C' (n + 1)) (hx : (x : Y) ∈ openCell n j) (hj : j ≠ i') :
    Sigma.ι (fun _ : cell C n ↦ R) i ≫ (cellularChainGroupIso C R n).inv ≫
        cellularChainGroupMap C C' hf R n ≫
        TopPair.singularHomologyMap
          (skeletonPairToComplSingleton C' x (notMem_skeletonLT_of_mem_openCell n hx)) R n =
      0 := by
  rw [ι_cellularChainGroupIso_inv_eq_singularHomologyMap_characteristicCellPairMap_assoc,
    cellularChainGroupMap_def, ← TopPair.singularHomologyMap_comp,
    ← TopPair.singularHomologyMap_comp]
  set φ := characteristicCellPairMap C i ≫ skeletonPairMap C C' hf n ≫
    skeletonPairToComplSingleton C' x (notMem_skeletonLT_of_mem_openCell n hx)
  have hmiss : ∀ z : TopCat.disk.{w} n, (TopPair.Hom.fst φ z : skeletonObj C' (n + 1)) ≠ x := by
    intro z hz
    let q := TopPair.Hom.fst (characteristicCellPairMap C i) z
    have h1 : TopPair.Hom.fst φ z =
        TopPair.Hom.fst (skeletonPairToComplSingleton C' x
          (notMem_skeletonLT_of_mem_openCell n hx))
          (TopPair.Hom.fst (skeletonPairMap C C' hf n) q) := by
      simp only [φ, TopPair.Hom.fst_comp]
      rfl
    have h2 : TopPair.Hom.fst (skeletonPairMap C C' hf n) q = x :=
      (ConcreteCategory.congr_hom (skeletonPairToComplSingleton_fst C' x _) _).symm.trans
        (h1.symm.trans hz)
    have h3 : skeletonMap C C' hf (n + 1) q = x :=
      (ConcreteCategory.congr_hom (skeletonPairMap_fst C C' hf n) q).symm.trans h2
    have h4 : (x : Y) = (f ⟨q.1, (skeletonLT C _).subset_complex q.2⟩ : Y) :=
      (congrArg Subtype.val h3).symm.trans
        (congrArg Subtype.val (skeletonMap_apply C C' hf (n + 1) q))
    have hmem : (x : Y) ∈ closedCell n i' := by
      rw [h4]
      refine hclosed _ ?_ _
      erw [coe_characteristicCellPairMap_fst_apply]
      exact ⟨_, (EuclideanSpace.equiv (Fin n) ℝ).image_unitBallHomeomorph_closedBall ▸
        mem_image_of_mem _ z.down.2, rfl⟩
    exact (disjoint_closedCell_openCell_of_ne n le_rfl
      (fun h ↦ hj.symm (eq_of_heq (Sigma.mk.inj_iff.1 h).2))).notMem_of_mem_left hmem hx
  rw [TopPair.singularHomologyMap_eq_zero_of_fac φ R
    (TopCat.ofHom ⟨fun z ↦ ⟨TopPair.Hom.fst φ z, hmiss z⟩,
      (TopPair.Hom.fst φ).hom.continuous.subtype_mk _⟩) rfl, Limits.comp_zero]

/-- If a cellular map sends `closedCell n i` into `closedCell n i'`, then the image of the cellular
basis vector of `i` has coordinate `0` on every `n`-cell `j ≠ i'`. -/
lemma cellularChainBasis_repr_cellularChainGroupMap_eq_zero_of_ne
    (R : Type w) [Ring R] {n : ℕ} {i : cell C n} {i' j : cell C' n}
    (hclosed : ∀ z ∈ closedCell n i, ∀ hz : z ∈ C, (f ⟨z, hz⟩ : Y) ∈ closedCell n i')
    (hj : j ≠ i') :
    (cellularChainBasis C' R n).repr
      (cellularChainGroupMap C C' hf (ModuleCat.of R R) n (cellularChainBasis C R n i)) j = 0 := by
  let x : skeletonObj C' (n + 1) :=
    ⟨map n j 0, openCell_subset_skeletonLT n j (map_zero_mem_openCell n j)⟩
  rw [cellularChainBasis_repr_apply_eq_inv_cellLocalClass C' R x (map_zero_mem_openCell n j),
    cellularChainBasis_apply, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
    ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
    ι_cellularChainGroupIso_inv_comp_cellularChainGroupMap_comp_local_of_ne_assoc C C' hf _
      hclosed x (map_zero_mem_openCell n j) hj,
    Limits.zero_comp]
  rfl

/-- **A cellular map sending `closedCell n i` into `closedCell n i'` sends the cellular basis vector
of `i` to a scalar multiple of the cellular basis vector of `i'`.** -/
theorem cellularChainGroupMap_cellularChainBasis_of_mapsTo_closedCell
    (R : Type w) [Ring R] {n : ℕ} {i : cell C n} {i' : cell C' n}
    (hclosed : ∀ z ∈ closedCell n i, ∀ hz : z ∈ C, (f ⟨z, hz⟩ : Y) ∈ closedCell n i') :
    cellularChainGroupMap C C' hf (ModuleCat.of R R) n (cellularChainBasis C R n i) =
      (cellularChainBasis C' R n).repr
        (cellularChainGroupMap C C' hf (ModuleCat.of R R) n (cellularChainBasis C R n i)) i' •
        cellularChainBasis C' R n i' := by
  set c := cellularChainGroupMap C C' hf (ModuleCat.of R R) n (cellularChainBasis C R n i)
  conv_lhs => rw [← (cellularChainBasis C' R n).linearCombination_repr c]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_eq_single i']
  · intro j _ hj
    rw [cellularChainBasis_repr_cellularChainGroupMap_eq_zero_of_ne C C' hf R hclosed hj,
      zero_smul]
  · intro hi'
    rw [Finsupp.notMem_support_iff.1 hi', zero_smul]

end ClosedCellMap

section MonoidAction

variable {X : Type w} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]
  {G : Type w} [Monoid G] [MulAction G X] [ContinuousConstSMul G X]
  (hcell : ∀ (g : G) (n : ℕ) (i : cell C n), ∃ j : cell C n, g • openCell n i = openCell n j)
  (R : Type w) [Ring R]

/-- The representation of `G` on the `n`-th cellular chain group of `C` induced by continuous
translations carrying open cells onto open cells of the same dimension. -/
def cellActionRepresentation (n : ℕ) :
    Representation R G (cellularChainGroup C (ModuleCat.of R R) n : ModuleCat R) :=
  cellularActionRepresentation C (cellActionSMul C hcell) (isCellular_cellActionSMul C hcell)
    (cellActionSMul_one C hcell) (cellActionSMul_mul C hcell) R n

/-- An element `g : G` acts on cellular chains by the chain map of `TauCeti.cellActionSMul`. -/
@[simp]
theorem cellActionRepresentation_apply (n : ℕ) (g : G) :
    cellActionRepresentation C hcell R n g =
      (cellularChainGroupMap C C (isCellular_cellActionSMul C hcell g)
        (ModuleCat.of R R) n).hom :=
  cellularActionRepresentation_apply _ _ _ _ _ _ _ _

/-- The `G`-equivariant cellular differential for a continuous action preserving open cells. -/
def cellActionDifferential (n : ℕ) :
    Rep.of (cellActionRepresentation C hcell R (n + 1)) ⟶
      Rep.of (cellActionRepresentation C hcell R n) :=
  cellularActionDifferential C (cellActionSMul C hcell) (isCellular_cellActionSMul C hcell)
    (cellActionSMul_one C hcell) (cellActionSMul_mul C hcell) R n

/-- The underlying linear map of `TauCeti.cellActionDifferential` is the cellular differential. -/
@[simp]
theorem cellActionDifferential_hom_toLinearMap (n : ℕ) :
    (cellActionDifferential C hcell R n).hom.toLinearMap =
      (cellularDifferential C (ModuleCat.of R R) n).hom :=
  cellularActionDifferential_hom_toLinearMap _ _ _ _ _ _ _

/-- **The equivariant cellular chain complex** in `Rep R G` of a CW complex carrying a continuous
monoid action preserving open cells of each dimension. -/
def cellActionChainComplex : ChainComplex (Rep.{w} R G) ℕ :=
  cellularActionComplex C (cellActionSMul C hcell) (isCellular_cellActionSMul C hcell)
    (cellActionSMul_one C hcell) (cellActionSMul_mul C hcell) R

/-- The `n`-th term of `TauCeti.cellActionChainComplex` is `TauCeti.cellActionRepresentation`. -/
@[simp]
theorem cellActionChainComplex_X (n : ℕ) :
    (cellActionChainComplex C hcell R).X n = Rep.of (cellActionRepresentation C hcell R n) :=
  cellularActionComplex_X _ _ _ _ _ _ _

/-- The differential of `TauCeti.cellActionChainComplex` is `TauCeti.cellActionDifferential`. -/
@[simp]
theorem cellActionChainComplex_d (n : ℕ) :
    (cellActionChainComplex C hcell R).d (n + 1) n =
      eqToHom (cellActionChainComplex_X C hcell R (n + 1)) ≫ cellActionDifferential C hcell R n ≫
        eqToHom (cellActionChainComplex_X C hcell R n).symm :=
  cellularActionComplex_d _ _ _ _ _ _ n

/-- Forgetting the `G`-action on `TauCeti.cellActionChainComplex` recovers the geometric cellular
chain complex of `C`. -/
def cellActionChainComplexForget₂Iso :
    ((forget₂ (Rep.{w} R G) (ModuleCat.{w} R)).mapHomologicalComplex _).obj
        (cellActionChainComplex C hcell R) ≅
      cellularChainComplex C (ModuleCat.of R R) :=
  (cellularActionComplexForget₂Iso C (cellActionSMul C hcell) (isCellular_cellActionSMul C hcell)
    (cellActionSMul_one C hcell) (cellActionSMul_mul C hcell) R).symm

/-- The components of `TauCeti.cellActionChainComplexForget₂Iso` are the canonical term transports.
-/
@[simp]
theorem cellActionChainComplexForget₂Iso_hom_f (n : ℕ) :
    (cellActionChainComplexForget₂Iso C hcell R).hom.f n = eqToHom (by
      rw [Functor.mapHomologicalComplex_obj_X, cellActionChainComplex_X, cellularChainComplex_X]
      rfl) :=
  cellularActionComplexForget₂Iso_inv_f _ _ _ _ _ _ _

/-- The scalar in `R` by which translation by `g` sends the cellular basis vector of `i` to the
cellular basis vector of `g • i`. Over `ℤ` and for a group action, this is the orientation sign
`±1` of the self-homeomorphism between open cells. -/
def cellActionCoeff (n : ℕ) (g : G) (i : cell C n) : R :=
  letI := cellMulAction hcell n
  (cellularChainBasis C R n).repr
    (cellActionRepresentation C hcell R n g (cellularChainBasis C R n i)) (g • i)

/-- **Translation sends each cellular basis vector to a scalar multiple of the translated cell's
basis vector.** -/
theorem cellActionRepresentation_cellularChainBasis {n : ℕ} (g : G) (i : cell C n) :
    letI := cellMulAction hcell n
    cellActionRepresentation C hcell R n g (cellularChainBasis C R n i) =
      cellActionCoeff C hcell R n g i • cellularChainBasis C R n (g • i) := by
  let := cellMulAction hcell n
  rw [cellActionCoeff, cellActionRepresentation_apply]
  exact cellularChainGroupMap_cellularChainBasis_of_mapsTo_closedCell C C
    (isCellular_cellActionSMul C hcell g) R fun z hz _ ↦ by
      rw [coe_cellActionSMul_apply, ← smul_closedCell hcell g i]
      exact smul_mem_smul_set hz

/-- Translation by `1` acts with scalar `1` on every cellular basis vector. -/
@[simp]
theorem cellActionCoeff_one {n : ℕ} (i : cell C n) :
    cellActionCoeff C hcell R n 1 i = 1 := by
  let := cellMulAction hcell n
  rw [cellActionCoeff, map_one, one_apply_eq_self, one_smul, Module.Basis.repr_self,
    Finsupp.single_eq_same]

/-- **Cocycle law for cellular translation coefficients**: translating first by `h` and then by `g`
multiplies the orientation scalars `c(h, i) * c(g, h • i)`. -/
theorem cellActionCoeff_mul {n : ℕ} (g h : G) (i : cell C n) :
    letI := cellMulAction hcell n
    cellActionCoeff C hcell R n (g * h) i =
      cellActionCoeff C hcell R n h i * cellActionCoeff C hcell R n g (h • i) := by
  let := cellMulAction hcell n
  have hmul : cellActionRepresentation C hcell R n (g * h) (cellularChainBasis C R n i) =
      (cellActionCoeff C hcell R n h i * cellActionCoeff C hcell R n g (h • i)) •
        cellularChainBasis C R n ((g * h) • i) := by
    rw [map_mul, mul_apply_eq_comp,
      cellActionRepresentation_cellularChainBasis, map_smul,
      cellActionRepresentation_cellularChainBasis, smul_smul, ← mul_smul]
  rw [cellActionCoeff, hmul, LinearEquiv.map_smul, Module.Basis.repr_self, Finsupp.smul_single_one,
    Finsupp.single_eq_same]

end MonoidAction

section GroupBasis

variable {X : Type w} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]
  {G : Type w} [Group G] [MulAction G X] [ContinuousConstSMul G X]
  (hcell : ∀ (g : G) (n : ℕ) (i : cell C n), ∃ j : cell C n, g • openCell n i = openCell n j)
  (R : Type w) [Ring R]

/-- For a group action preserving open cells, the scalar `TauCeti.cellActionCoeff` is a unit of `R`
(with inverse `cellActionCoeff C hcell R n g⁻¹ (g • i)`), even when `R` is noncommutative. -/
def cellActionUnit (n : ℕ) (g : G) (i : cell C n) : Rˣ :=
  letI := cellMulAction hcell n
  { val := cellActionCoeff C hcell R n g i
    inv := cellActionCoeff C hcell R n g⁻¹ (g • i)
    val_inv := by
      rw [← cellActionCoeff_mul C hcell R g⁻¹ g i, inv_mul_cancel, cellActionCoeff_one]
    inv_val := by
      have h := cellActionCoeff_mul C hcell R g g⁻¹ (g • i)
      rw [mul_inv_cancel, cellActionCoeff_one, inv_smul_smul] at h
      exact h.symm }

/-- The underlying scalar of `TauCeti.cellActionUnit` is `TauCeti.cellActionCoeff`. -/
@[simp]
theorem coe_cellActionUnit {n : ℕ} (g : G) (i : cell C n) :
    (cellActionUnit C hcell R n g i : R) = cellActionCoeff C hcell R n g i :=
  (rfl)

/-- At `g = 1`, the orientation unit is `1`. -/
@[simp]
theorem cellActionUnit_one {n : ℕ} (i : cell C n) :
    cellActionUnit C hcell R n 1 i = 1 :=
  Units.ext (cellActionCoeff_one C hcell R i)

section Equiv

variable {n : ℕ} {ι : Type*} (s : ι → cell C n) (e : (Σ _ : ι, G) ≃ cell C n)

/-- **The equivariantly rescaled cellular `R`-basis.** Given representatives `s : ι → cell C n` and
a parametrization `e : (Σ _ : ι, G) ≃ cell C n` with `e ⟨i, g⟩ = g • s i`, scaling the cellular
basis vector of `e ⟨i, g⟩` by `cellActionUnit C hcell R n g (s i)` produces an `R`-basis of the
`n`-th cellular chain group on which `G` acts freely without orientation signs. -/
def cellActionBasis :
    Module.Basis (cell C n) R (cellularChainGroup C (ModuleCat.of R R) n : ModuleCat R) :=
  (cellularChainBasis C R n).unitsSMul fun j ↦
    cellActionUnit C hcell R n (e.symm j).2 (s (e.symm j).1)

/-- At `e ⟨i, g⟩`, the rescaled basis vector is the `g`-translate of the cellular basis vector of
the chosen representative `s i`. -/
theorem cellActionBasis_apply_equiv
    (he : letI := cellMulAction hcell n; ∀ i g, e ⟨i, g⟩ = g • s i) (i : ι) (g : G) :
    cellActionBasis C hcell R s e (e ⟨i, g⟩) =
      cellActionRepresentation C hcell R n g (cellularChainBasis C R n (s i)) := by
  let := cellMulAction hcell n
  rw [cellActionBasis, Module.Basis.unitsSMul_apply, Equiv.symm_apply_apply, Units.smul_def,
    coe_cellActionUnit, he i g, ← cellActionRepresentation_cellularChainBasis]

/-- At the chosen representative `e ⟨i, 1⟩ = s i`, the rescaled basis vector agrees with the
geometric cellular basis vector of `s i`. -/
theorem cellActionBasis_apply_one
    (he : letI := cellMulAction hcell n; ∀ i g, e ⟨i, g⟩ = g • s i) (i : ι) :
    cellActionBasis C hcell R s e (e ⟨i, 1⟩) = cellularChainBasis C R n (s i) := by
  rw [cellActionBasis_apply_equiv C hcell R s e he, map_one, one_apply_eq_self]

/-- **Left translation permutes `TauCeti.cellActionBasis` without signs**: `g'` sends the basis
vector at `e ⟨i, g⟩` to the basis vector at `e ⟨i, g' * g⟩`. -/
theorem cellActionRepresentation_cellActionBasis
    (he : letI := cellMulAction hcell n; ∀ i g, e ⟨i, g⟩ = g • s i) (g' g : G) (i : ι) :
    cellActionRepresentation C hcell R n g' (cellActionBasis C hcell R s e (e ⟨i, g⟩)) =
      cellActionBasis C hcell R s e (e ⟨i, g' * g⟩) := by
  rw [cellActionBasis_apply_equiv C hcell R s e he, cellActionBasis_apply_equiv C hcell R s e he,
    map_mul, mul_apply_eq_comp]

end Equiv

end GroupBasis

section FreeRep

variable {X : Type w} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]
  {G : Type w} [Group G] [MulAction G X] [ContinuousConstSMul G X]
  (hcell : ∀ (g : G) (n : ℕ) (i : cell C n), ∃ j : cell C n, g • openCell n i = openCell n j)
  (R : Type w) [CommRing R]

section Equiv

variable {n : ℕ} {ι : Type w} (s : ι → cell C n) (e : (Σ _ : ι, G) ≃ cell C n)
  (he : letI := cellMulAction hcell n; ∀ i g, e ⟨i, g⟩ = g • s i)

/-- **A free cellular action makes each cellular chain group free over `R[G]`**: given orbit
representatives `s : ι → cell C n` and an orbit parametrization `e ⟨i, g⟩ = g • s i`, the `n`-th
cellular chain representation is isomorphic to `Rep.free R G ι`, with `single i (single 1 1)`
corresponding to `cellularChainBasis C R n (s i)`. -/
def cellActionRepIsoFreeOfEquiv :
    Rep.of (cellActionRepresentation C hcell R n) ≅ Rep.free R G ι :=
  (Rep.mkIso ((cellActionRepresentation C hcell R n).freeEquivOfBasis
    (cellActionBasis C hcell R s e) e
    (cellActionRepresentation_cellActionBasis C hcell R s e he))).symm

/-- Under `(cellActionRepIsoFreeOfEquiv ...).inv`, the generator `single i (single g r)` maps to
`r` times the `g`-translate of the cellular basis vector of `s i`. -/
@[simp]
theorem cellActionRepIsoFreeOfEquiv_inv_hom_single (i : ι) (g : G) (r : R) :
    (cellActionRepIsoFreeOfEquiv C hcell R s e he).inv.hom
        (Finsupp.single i (MonoidAlgebra.single g r)) =
      r • cellActionRepresentation C hcell R n g (cellularChainBasis C R n (s i)) := by
  rw [cellActionRepIsoFreeOfEquiv, Iso.symm_inv, Rep.mkIso_hom_hom_apply]
  exact (Representation.freeEquivOfBasis_single (cellActionRepresentation C hcell R n)
    (cellActionBasis C hcell R s e) e
    (cellActionRepresentation_cellActionBasis C hcell R s e he) i g r).trans
      (by rw [cellActionBasis_apply_equiv C hcell R s e he])

/-- The `g`-translate of the cellular basis vector of `s i` corresponds to `single i (single g 1)`
in `Rep.free R G ι`. -/
theorem cellActionRepIsoFreeOfEquiv_hom_hom_apply_cellularChainBasis (i : ι) (g : G) :
    (cellActionRepIsoFreeOfEquiv C hcell R s e he).hom.hom
        (cellActionRepresentation C hcell R n g (cellularChainBasis C R n (s i))) =
      Finsupp.single i (MonoidAlgebra.single g 1) := by
  rw [← one_smul R (cellActionRepresentation C hcell R n g _),
    ← cellActionRepIsoFreeOfEquiv_inv_hom_single C hcell R s e he, Rep.hom_inv_apply]

/-- The cellular basis vector of the chosen representative `s i` corresponds to the free `R[G]`
basis element `single i (single 1 1)`. This is not a `simp` lemma because `cellularChainBasis_apply`
unfolds its argument first. -/
theorem cellActionRepIsoFreeOfEquiv_hom_hom_cellularChainBasis (i : ι) :
    (cellActionRepIsoFreeOfEquiv C hcell R s e he).hom.hom (cellularChainBasis C R n (s i)) =
      Finsupp.single i (MonoidAlgebra.single 1 1) := by
  simpa only [map_one, one_apply_eq_self] using
    cellActionRepIsoFreeOfEquiv_hom_hom_apply_cellularChainBasis C hcell R s e he i 1

end Equiv

/-- **Intrinsic `R[G]`-freeness on cell orbits**: when `G` acts freely on the open cells of `C`,
the `n`-th cellular chain representation is isomorphic to the free representation on the `G`-orbits
of `n`-cells. -/
def cellActionRepIsoFreeOrbit
    (hfree : ∀ (g : G) (n : ℕ) (i : cell C n), g • openCell n i = openCell n i → g = 1) (n : ℕ) :
    letI := cellMulAction hcell n
    Rep.of (cellActionRepresentation C hcell R n) ≅
      Rep.free R G (MulAction.orbitRel.Quotient G (cell C n)) :=
  letI := cellMulAction hcell n
  haveI := isCancelSMul_cell hcell hfree n
  cellActionRepIsoFreeOfEquiv C hcell R Quotient.out
    ((Equiv.sigmaEquivProd (MulAction.orbitRel.Quotient G (cell C n)) G).trans
      (MulAction.selfEquivOrbitsQuotientProd (G := G) (X := cell C n)
        IsCancelSMul.stabilizer_eq_bot).symm)
    fun q g ↦ MulAction.selfEquivOrbitsQuotientProd_symm_apply IsCancelSMul.stabilizer_eq_bot q g

/-- Each term of `TauCeti.cellActionChainComplex` is projective in `Rep R G` when the action on
open cells is free. -/
theorem projective_cellActionChainComplex_X
    (hfree : ∀ (g : G) (n : ℕ) (i : cell C n), g • openCell n i = openCell n i → g = 1) (n : ℕ) :
    Projective ((cellActionChainComplex C hcell R).X n) := by
  let := cellMulAction hcell n
  rw [cellActionChainComplex_X]
  exact Projective.of_iso (cellActionRepIsoFreeOrbit C hcell R hfree n).symm inferInstance

end FreeRep

section QuotientCover

variable {E B : Type w} [TopologicalSpace E] [T2Space E] [TopologicalSpace B]
  [CWComplex (univ : Set E)] {G : Type w} [Group G] [MulAction G E] {p : E → B}
  (hp : IsQuotientCoveringMap p G)
  (hcell : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
    ∃ j : cell (univ : Set E) n, g • openCell n i = openCell n j)
  (hfree : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
    g • openCell n i = openCell n i → g = 1)
  (R : Type w) [CommRing R]

/-- **Cellular chains of a free `G`-CW cover are free over `R[G]` on chosen lifts of the base
cells.** Given any CW structure on `B` whose open cells are the images under `p` of the open cells
of `E`, and a chosen lift `s b` of each `n`-cell `b` of `B`, the `n`-th cellular chain
representation of `E` is isomorphic to `Rep.free R G (cell (univ : Set B) n)`. -/
def _root_.IsQuotientCoveringMap.cellActionRepIsoFree [CWComplex (univ : Set B)]
    (hp_cell : ∀ (n : ℕ) (i : cell (univ : Set E) n),
      ∃ b : cell (univ : Set B) n, p '' openCell n i = openCell n b)
    {n : ℕ} (s : cell (univ : Set B) n → cell (univ : Set E) n)
    (hs : ∀ b, p '' openCell n (s b) = openCell n b) :
    haveI := hp.toContinuousConstSMul
    Rep.of (cellActionRepresentation (univ : Set E) hcell R n) ≅
      Rep.free R G (cell (univ : Set B) n) :=
  haveI := hp.toContinuousConstSMul
  cellActionRepIsoFreeOfEquiv (univ : Set E) hcell R s
    (hp.sigmaSMulCellLiftEquiv hcell hfree hp_cell s hs)
    (hp.sigmaSMulCellLiftEquiv_apply hcell hfree hp_cell s hs)

/-- Under `(hp.cellActionRepIsoFree ...).inv`, `single b (single g r)` maps to `r` times the
`g`-translate of the cellular basis vector of the chosen lift `s b`. -/
@[simp]
theorem _root_.IsQuotientCoveringMap.cellActionRepIsoFree_inv_hom_single [CWComplex (univ : Set B)]
    (hp_cell : ∀ (n : ℕ) (i : cell (univ : Set E) n),
      ∃ b : cell (univ : Set B) n, p '' openCell n i = openCell n b)
    {n : ℕ} (s : cell (univ : Set B) n → cell (univ : Set E) n)
    (hs : ∀ b, p '' openCell n (s b) = openCell n b) (b : cell (univ : Set B) n) (g : G) (r : R) :
    haveI := hp.toContinuousConstSMul
    (hp.cellActionRepIsoFree hcell hfree R hp_cell s hs).inv.hom
        (Finsupp.single b (MonoidAlgebra.single g r)) =
      r • cellActionRepresentation (univ : Set E) hcell R n g
        (cellularChainBasis (univ : Set E) R n (s b)) :=
  haveI := hp.toContinuousConstSMul
  cellActionRepIsoFreeOfEquiv_inv_hom_single (univ : Set E) hcell R s _ _ b g r

/-- The cellular basis vector of the chosen lift `s b` maps to `single b (single 1 1)`. -/
theorem _root_.IsQuotientCoveringMap.cellActionRepIsoFree_hom_hom_cellularChainBasis
    [CWComplex (univ : Set B)]
    (hp_cell : ∀ (n : ℕ) (i : cell (univ : Set E) n),
      ∃ b : cell (univ : Set B) n, p '' openCell n i = openCell n b)
    {n : ℕ} (s : cell (univ : Set B) n → cell (univ : Set E) n)
    (hs : ∀ b, p '' openCell n (s b) = openCell n b) (b : cell (univ : Set B) n) :
    haveI := hp.toContinuousConstSMul
    (hp.cellActionRepIsoFree hcell hfree R hp_cell s hs).hom.hom
        (cellularChainBasis (univ : Set E) R n (s b)) =
      Finsupp.single b (MonoidAlgebra.single 1 1) :=
  haveI := hp.toContinuousConstSMul
  cellActionRepIsoFreeOfEquiv_hom_hom_cellularChainBasis (univ : Set E) hcell R s _ _ b

/-- **Cellular chains of `E` are free over `R[G]` on chosen lifts of the cells of the orbit CW
structure `IsQuotientCoveringMap.cwComplexQuotient`.** -/
def _root_.IsQuotientCoveringMap.cellActionRepIsoFreeQuotient {n : ℕ}
    (s : letI := hp.cwComplexQuotient hcell hfree
      cell (univ : Set B) n → cell (univ : Set E) n)
    (hs : letI := hp.cwComplexQuotient hcell hfree
      ∀ b, p '' openCell n (s b) = openCell n b) :
    letI := hp.cwComplexQuotient hcell hfree
    haveI := hp.toContinuousConstSMul
    Rep.of (cellActionRepresentation (univ : Set E) hcell R n) ≅
      Rep.free R G (cell (univ : Set B) n) :=
  letI := hp.cwComplexQuotient hcell hfree
  hp.cellActionRepIsoFree hcell hfree R
    (fun m i ↦ ⟨(hp.cellQuotientEquiv hcell hfree m).symm (Quotient.mk'' i),
      hp.image_openCell hcell hfree i⟩)
    s hs

/-- Under `(hp.cellActionRepIsoFreeQuotient ...).inv`, `single b (single g r)` maps to `r` times the
`g`-translate of the cellular basis vector of `s b`. -/
@[simp]
theorem _root_.IsQuotientCoveringMap.cellActionRepIsoFreeQuotient_inv_hom_single {n : ℕ}
    (s : letI := hp.cwComplexQuotient hcell hfree
      cell (univ : Set B) n → cell (univ : Set E) n)
    (hs : letI := hp.cwComplexQuotient hcell hfree
      ∀ b, p '' openCell n (s b) = openCell n b)
    (b : letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) (g : G) (r : R) :
    letI := hp.cwComplexQuotient hcell hfree
    haveI := hp.toContinuousConstSMul
    (hp.cellActionRepIsoFreeQuotient hcell hfree R s hs).inv.hom
        (Finsupp.single b (MonoidAlgebra.single g r)) =
      r • cellActionRepresentation (univ : Set E) hcell R n g
        (cellularChainBasis (univ : Set E) R n (s b)) :=
  letI := hp.cwComplexQuotient hcell hfree
  hp.cellActionRepIsoFree_inv_hom_single hcell hfree R _ s hs b g r

/-- Under `hp.cellActionRepIsoFreeQuotient`, the cellular basis vector of `s b` maps to
`single b (single 1 1)`. -/
theorem _root_.IsQuotientCoveringMap.cellActionRepIsoFreeQuotient_hom_hom_cellularChainBasis {n : ℕ}
    (s : letI := hp.cwComplexQuotient hcell hfree
      cell (univ : Set B) n → cell (univ : Set E) n)
    (hs : letI := hp.cwComplexQuotient hcell hfree
      ∀ b, p '' openCell n (s b) = openCell n b)
    (b : letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) :
    letI := hp.cwComplexQuotient hcell hfree
    haveI := hp.toContinuousConstSMul
    (hp.cellActionRepIsoFreeQuotient hcell hfree R s hs).hom.hom
        (cellularChainBasis (univ : Set E) R n (s b)) =
      Finsupp.single b (MonoidAlgebra.single 1 1) :=
  letI := hp.cwComplexQuotient hcell hfree
  hp.cellActionRepIsoFree_hom_hom_cellularChainBasis hcell hfree R _ s hs b

end QuotientCover

section Augmentation

variable {X : Type w} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]
  {G : Type w} [Monoid G] [MulAction G X] [ContinuousConstSMul G X]
  (hcell : ∀ (g : G) (n : ℕ) (i : cell C n), ∃ j : cell C n, g • openCell n i = openCell n j)
  (R : Type w) [CommRing R]

/-- The **equivariant cellular augmentation** in degree `0`, sending each `0`-cell to `1` in the
trivial representation `Rep.trivial R G R`. -/
def cellActionAugmentation :
    Rep.of (cellActionRepresentation C hcell R 0) ⟶ Rep.trivial R G R :=
  Rep.ofHom
    { toLinearMap := (cellularAugmentation C (ModuleCat.of R R)).hom
      isIntertwining' g := LinearMap.ext fun x ↦ by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, Representation.trivial_apply,
          cellActionRepresentation_apply]
        exact ConcreteCategory.congr_hom (cellularChainGroupMap_comp_cellularAugmentation C C
          (isCellular_cellActionSMul C hcell g) (ModuleCat.of R R)) x }

/-- The underlying linear map of `TauCeti.cellActionAugmentation` is `TauCeti.cellularAugmentation`.
-/
@[simp]
theorem cellActionAugmentation_hom_toLinearMap :
    (cellActionAugmentation C hcell R).hom.toLinearMap =
      (cellularAugmentation C (ModuleCat.of R R)).hom :=
  (rfl)

/-- The equivariant cellular augmentation vanishes on boundaries of `1`-cells. -/
@[reassoc (attr := simp)]
theorem cellActionDifferential_comp_cellActionAugmentation :
    cellActionDifferential C hcell R 0 ≫ cellActionAugmentation C hcell R = 0 := by
  refine Rep.hom_ext <| Representation.IntertwiningMap.ext <| LinearMap.ext fun x ↦ ?_
  have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (cellularDifferential_comp_cellularAugmentation C (ModuleCat.of R R))) x
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.comp_apply,
    LinearMap.zero_apply] at h
  simpa [Rep.hom_comp] using h

/-- The **equivariant augmentation of `TauCeti.cellActionChainComplex`** as a chain map in
`Rep R G` to `Rep.trivial R G R` placed in degree `0`. -/
def cellActionChainComplexAugmentation :
    cellActionChainComplex C hcell R ⟶
      (ChainComplex.single₀ (Rep.{w} R G)).obj (Rep.trivial R G R) :=
  ((cellActionChainComplex C hcell R).toSingle₀Equiv _).symm
    ⟨eqToHom (cellActionChainComplex_X C hcell R 0) ≫ cellActionAugmentation C hcell R, by
      simp [cellActionChainComplex_d]⟩

/-- In degree `0`, `TauCeti.cellActionChainComplexAugmentation` is `TauCeti.cellActionAugmentation`.
-/
@[simp]
theorem cellActionChainComplexAugmentation_f_zero :
    (cellActionChainComplexAugmentation C hcell R).f 0 =
      eqToHom (cellActionChainComplex_X C hcell R 0) ≫ cellActionAugmentation C hcell R :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- **When `C` is contractible, the equivariant cellular augmentation is a quasi-isomorphism.** -/
theorem quasiIso_cellActionChainComplexAugmentation [ContractibleSpace C] :
    QuasiIso (cellActionChainComplexAugmentation C hcell R) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ (forget₂ _ (ModuleCat R)),
    quasiIso_iff_of_arrow_mk_iso _
      (cellularChainComplexAugmentation C (ModuleCat.of R R)) ?_]
  · exact quasiIso_cellularChainComplexAugmentation C (ModuleCat.of R R)
  · refine Arrow.isoMk' _ _ (cellActionChainComplexForget₂Iso C hcell R)
      ((HomologicalComplex.singleMapHomologicalComplex _ _ 0).app _) ?_
    have h : (forget₂ (Rep R G) (ModuleCat R)).map (cellActionAugmentation C hcell R) =
        cellularAugmentation C (ModuleCat.of R R) := by
      rw [Rep.forget₂_moduleCat_map, cellActionAugmentation_hom_toLinearMap, ModuleCat.ofHom_hom]
    ext : 1
    simp [-Rep.forget₂_moduleCat_map, eqToHom_map, h]

end Augmentation

section Resolution

variable {X : Type w} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]
  {G : Type w} [Group G] [MulAction G X] [ContinuousConstSMul G X]
  (hcell : ∀ (g : G) (n : ℕ) (i : cell C n), ∃ j : cell C n, g • openCell n i = openCell n j)
  (hfree : ∀ (g : G) (n : ℕ) (i : cell C n), g • openCell n i = openCell n i → g = 1)
  (R : Type w) [CommRing R] [ContractibleSpace C]

/-- **A contractible CW complex carrying a free cellular `G`-action yields a projective resolution
of the trivial representation `Rep.trivial R G R`** by its equivariant cellular chain complex. -/
def cellActionResolution : ProjectiveResolution (Rep.trivial R G R) where
  complex := cellActionChainComplex C hcell R
  π := cellActionChainComplexAugmentation C hcell R
  projective n := projective_cellActionChainComplex_X C hcell R hfree n
  quasiIso := quasiIso_cellActionChainComplexAugmentation C hcell R

/-- The underlying complex of `TauCeti.cellActionResolution` is `TauCeti.cellActionChainComplex`. -/
@[simp]
theorem cellActionResolution_complex :
    (cellActionResolution C hcell hfree R).complex = cellActionChainComplex C hcell R :=
  (rfl)

-- A public statement cannot unfold the unexposed body of `TauCeti.cellActionResolution`, so the
-- source of its `π` is transported along `cellActionResolution_complex`.
/-- The augmentation of `TauCeti.cellActionResolution` is
`TauCeti.cellActionChainComplexAugmentation`. -/
@[simp]
theorem cellActionResolution_π :
    (cellActionResolution C hcell hfree R).π =
      eqToHom (cellActionResolution_complex C hcell hfree R) ≫
        cellActionChainComplexAugmentation C hcell R :=
  (Category.id_comp _).symm

end Resolution

end TauCeti
