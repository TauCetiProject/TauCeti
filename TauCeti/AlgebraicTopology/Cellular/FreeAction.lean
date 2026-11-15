/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.RepresentationTheory.Rep.Iso
public import TauCeti.AlgebraicTopology.Cellular.Equivariant
public import TauCeti.AlgebraicTopology.Cellular.Incidence
public import TauCeti.RepresentationTheory.FreeOfBasis
public import TauCeti.Topology.CWComplex.Classical.OrbitSpace
import Mathlib.LinearAlgebra.Basis.SMul
import TauCeti.AlgebraicTopology.Cellular.Permutation
import TauCeti.GroupTheory.GroupAction.Free

/-!
# Cellular chains of free cellular actions

Let a group `G` act continuously on a Hausdorff CW complex `C ⊆ E` so that every element carries
each open `n`-cell onto an open `n`-cell (`TauCeti.cellMulAction`). Unlike the lifted CW structure
of a covering map (`TauCeti.cwComplexPreimage`), translations need not preserve chosen
characteristic maps strictly: by `TauCeti.cellularChainGroupMap_cellularChainBasis_eq_smul`, a
translation carrying the open cell of `i` onto that of `g • i` sends the cellular basis vector of
`i` to a scalar multiple of the cellular basis vector of `g • i` (`TauCeti.cellActionBasisCoeff`).
For a group action, these scalars are units (`TauCeti.cellActionBasisUnit`), over `ℤ` the
orientation signs `±1` of the induced self-homeomorphisms of cells.

Given any equivariant parametrization `(Σ _ : ι, G) ≃ cell C n`, rescaling the cellular basis along
each fibre by the units from its identity representative produces a `G`-permuted basis, identifying
the `n`-th cellular chain group with `Rep.free R G ι` over a commutative ring `R`
(`TauCeti.cellActionChainRepIsoFreeOfEquiv`). When `G` acts freely on the cells, each cellular chain
group is therefore free over `R[G]` with one generator for each `G`-orbit of cells
(`TauCeti.cellActionChainRepIsoFreeOfOrbits`), and — when `p : E → B` is a quotient covering map
giving `B` the orbit CW structure `IsQuotientCoveringMap.cwComplexQuotient` — with basis one chosen
lift of each cell of `B` (`IsQuotientCoveringMap.cellActionChainRepIsoFree`).

When `C` is contractible, the equivariant cellular augmentation
(`TauCeti.cellActionChainComplexRepAugmentation`) is a quasi-isomorphism, packaging the cellular
chain complex of `C` as a projective resolution of the trivial representation `Rep.trivial R G R`
(`TauCeti.cellActionResolution`).

## Main definitions and results

* `TauCeti.cellActionChainRepresentation` and `TauCeti.cellActionChainComplexRep`: the cellular
  chain groups and chain complex of a CW complex carrying a continuous monoid action that sends open
  cells onto open cells of the same dimension, as representations and complexes in `Rep R G`.
* `TauCeti.cellActionBasisCoeff` and `TauCeti.cellActionBasisUnit`: the scalar (and unit, for a
  group action) by which `g` scales the cellular basis vector of `i` into that of `g • i`.
* `TauCeti.cellActionChainRepIsoFreeOfEquiv`, `TauCeti.cellActionChainRepIsoFreeOfOrbits`, and
  `IsQuotientCoveringMap.cellActionChainRepIsoFree`: for an equivariant cell parametrization or a
  free cellular action, each cellular chain group is free over `R[G]` on the parameter set, on the
  cell orbits, or on chosen lifts of the cells of the orbit space `B`.
* `TauCeti.cellActionResolution`: for a contractible CW complex with a free cellular group action,
  its cellular chains form a `ProjectiveResolution (Rep.trivial R G R)`.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section I.4 and Section II.4.
* T. tom Dieck, *Transformation Groups*, de Gruyter, 1987, Section II.1.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.2.
-/

public section

noncomputable section

open CategoryTheory Function Metric Set Topology Topology.RelCWComplex
open scoped Pointwise

universe w

namespace TauCeti

section Action

variable {E : Type w} [TopologicalSpace E] [T2Space E] (C : Set E) [CWComplex C]
  {G : Type w} [Monoid G] [MulAction G E] [ContinuousConstSMul G E]
  (hcell : ∀ (g : G) (n : ℕ) (i : cell C n), ∃ j : cell C n, g • openCell n i = openCell n j)
  (R : Type w) [Ring R]

/-- The representation of `G` on the `n`-th cellular chain group of a Hausdorff CW complex `C`
induced by a continuous action carrying open cells onto open cells of the same dimension. -/
def cellActionChainRepresentation (n : ℕ) :
    Representation R G (cellularChainGroup C (ModuleCat.of R R) n : ModuleCat R) :=
  cellularActionRepresentation C (fun g ↦ cellActionSMul C g (hcell g))
    (fun g ↦ isCellular_cellActionSMul C g (hcell g))
    (cellActionSMul_one C (hcell 1))
    (fun g h ↦ cellActionSMul_mul C g h (hcell g) (hcell h) (hcell (g * h))) R n

/-- An element `g` acts on the cellular chains of `C` by the cellular chain map of translation by
`g`. -/
@[simp]
theorem cellActionChainRepresentation_apply (n : ℕ) (g : G) :
    cellActionChainRepresentation C hcell R n g =
      (cellularChainGroupMap C C (isCellular_cellActionSMul C g (hcell g))
        (ModuleCat.of R R) n).hom := by
  unfold cellActionChainRepresentation
  exact cellularActionRepresentation_apply _ _ _ _ _ _ _ _

/-- The cellular differential of `C` as a morphism of representations of `G`. -/
def cellActionDifferentialRep (n : ℕ) :
    Rep.of (cellActionChainRepresentation C hcell R (n + 1)) ⟶
      Rep.of (cellActionChainRepresentation C hcell R n) :=
  cellularActionDifferential C (fun g ↦ cellActionSMul C g (hcell g))
    (fun g ↦ isCellular_cellActionSMul C g (hcell g))
    (cellActionSMul_one C (hcell 1))
    (fun g h ↦ cellActionSMul_mul C g h (hcell g) (hcell h) (hcell (g * h))) R n

/-- The underlying linear map of `TauCeti.cellActionDifferentialRep` is the cellular differential
of `C`. -/
@[simp]
theorem cellActionDifferentialRep_hom_toLinearMap (n : ℕ) :
    (cellActionDifferentialRep C hcell R n).hom.toLinearMap =
      (cellularDifferential C (ModuleCat.of R R) n).hom := by
  unfold cellActionDifferentialRep
  exact cellularActionDifferential_hom_toLinearMap _ _ _ _ _ _ _

/-- **The cellular chain complex of `C` as a chain complex in `Rep R G`** for a continuous action
carrying open cells onto open cells of the same dimension. -/
def cellActionChainComplexRep : ChainComplex (Rep.{w} R G) ℕ :=
  cellularActionComplex C (fun g ↦ cellActionSMul C g (hcell g))
    (fun g ↦ isCellular_cellActionSMul C g (hcell g))
    (cellActionSMul_one C (hcell 1))
    (fun g h ↦ cellActionSMul_mul C g h (hcell g) (hcell h) (hcell (g * h))) R

/-- The terms of `TauCeti.cellActionChainComplexRep` are `TauCeti.cellActionChainRepresentation`. -/
@[simp]
theorem cellActionChainComplexRep_X (n : ℕ) :
    (cellActionChainComplexRep C hcell R).X n =
      Rep.of (cellActionChainRepresentation C hcell R n) := by
  unfold cellActionChainComplexRep cellActionChainRepresentation
  exact cellularActionComplex_X _ _ _ _ _ _ _

/-- The differentials of `TauCeti.cellActionChainComplexRep` are the equivariant cellular
differentials. -/
@[simp]
theorem cellActionChainComplexRep_d (n : ℕ) :
    (cellActionChainComplexRep C hcell R).d (n + 1) n =
      eqToHom (cellActionChainComplexRep_X C hcell R (n + 1)) ≫
        cellActionDifferentialRep C hcell R n ≫
          eqToHom (cellActionChainComplexRep_X C hcell R n).symm := by
  unfold cellActionChainComplexRep cellActionDifferentialRep
  exact cellularActionComplex_d _ _ _ _ _ _ n

/-- Forgetting the `G`-action on `TauCeti.cellActionChainComplexRep` recovers the cellular chain
complex of `C`. -/
def cellActionChainComplexRepForget₂Iso :
    ((forget₂ (Rep.{w} R G) (ModuleCat.{w} R)).mapHomologicalComplex _).obj
        (cellActionChainComplexRep C hcell R) ≅
      cellularChainComplex C (ModuleCat.of R R) :=
  (cellularActionComplexForget₂Iso C (fun g ↦ cellActionSMul C g (hcell g))
    (fun g ↦ isCellular_cellActionSMul C g (hcell g))
    (cellActionSMul_one C (hcell 1))
    (fun g h ↦ cellActionSMul_mul C g h (hcell g) (hcell h) (hcell (g * h))) R).symm

/-- Components of `TauCeti.cellActionChainComplexRepForget₂Iso` are the canonical term
transports. -/
@[simp]
theorem cellActionChainComplexRepForget₂Iso_hom_f (n : ℕ) :
    (cellActionChainComplexRepForget₂Iso C hcell R).hom.f n =
      eqToHom (by
        rw [Functor.mapHomologicalComplex_obj_X, cellularChainComplex_X,
          cellActionChainComplexRep_X]
        rfl) := by
  unfold cellActionChainComplexRepForget₂Iso
  exact cellularActionComplexForget₂Iso_inv_f _ _ _ _ _ _ _

/-- Inverse components of `TauCeti.cellActionChainComplexRepForget₂Iso` are the reverse term
transports. -/
@[simp]
theorem cellActionChainComplexRepForget₂Iso_inv_f (n : ℕ) :
    (cellActionChainComplexRepForget₂Iso C hcell R).inv.f n =
      eqToHom (by
        rw [Functor.mapHomologicalComplex_obj_X, cellularChainComplex_X,
          cellActionChainComplexRep_X]
        rfl) := by
  unfold cellActionChainComplexRepForget₂Iso
  exact cellularActionComplexForget₂Iso_hom_f _ _ _ _ _ _ _

/-- The scalar in `R` by which `g` multiplies the cellular basis vector of `i` into the cellular
basis vector of `g • i`. -/
def cellActionBasisCoeff {n : ℕ} (g : G) (i : cell C n) : R :=
  letI := cellMulAction hcell n
  (cellularChainBasis C R n).repr
    (cellActionChainRepresentation C hcell R n g (cellularChainBasis C R n i)) (g • i)

/-- `TauCeti.cellActionBasisCoeff` is the `(g • i)`-coordinate in `TauCeti.cellularChainBasis` of
the `g`-translate of the cellular basis vector of `i`. -/
theorem cellActionBasisCoeff_def {n : ℕ} (g : G) (i : cell C n) :
    letI := cellMulAction hcell n
    cellActionBasisCoeff C hcell R g i =
      (cellularChainBasis C R n).repr
        (cellActionChainRepresentation C hcell R n g (cellularChainBasis C R n i)) (g • i) :=
  (rfl)

/-- **Translation by `g` sends the cellular basis vector of `i` to `cellActionBasisCoeff` times
that of `g • i`.** This is not a `simp` lemma because `simp` unfolds `TauCeti.cellularChainBasis`
first. -/
theorem cellActionChainRepresentation_cellularChainBasis {n : ℕ} (g : G) (i : cell C n) :
    letI := cellMulAction hcell n
    cellActionChainRepresentation C hcell R n g (cellularChainBasis C R n i) =
      cellActionBasisCoeff C hcell R g i • cellularChainBasis C R n (g • i) := by
  let := cellMulAction hcell n
  have hi : ∀ x ∈ closedCell n i, ∀ hx : x ∈ C,
      (cellActionSMul C g (hcell g) ⟨x, hx⟩).1 ∈ closedCell n (g • i) := by
    intro x hx _
    rw [coe_cellActionSMul_apply, ← smul_closedCell hcell g i]
    exact smul_mem_smul_set hx
  simpa only [cellActionChainRepresentation_apply, cellActionBasisCoeff] using
    cellularChainGroupMap_cellularChainBasis_eq_smul C C
      (isCellular_cellActionSMul C g (hcell g)) R hi

/-- The identity element scales every cellular basis vector by `1`. -/
@[simp]
theorem cellActionBasisCoeff_one {n : ℕ} (i : cell C n) :
    cellActionBasisCoeff C hcell R (1 : G) i = 1 := by
  let := cellMulAction hcell n
  have h := cellActionChainRepresentation_cellularChainBasis C hcell R (1 : G) i
  rw [map_one, one_apply_eq_self, one_smul] at h
  have hrepr := congrArg (fun x ↦ (cellularChainBasis C R n).repr x i) h
  simpa only [map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
    smul_eq_mul, mul_one] using hrepr.symm

/-- Cocycle law for `TauCeti.cellActionBasisCoeff` under composition of translations. -/
theorem cellActionBasisCoeff_mul {n : ℕ} (g h : G) (i : cell C n) :
    letI := cellMulAction hcell n
    cellActionBasisCoeff C hcell R (g * h) i =
      cellActionBasisCoeff C hcell R h i * cellActionBasisCoeff C hcell R g (h • i) := by
  let := cellMulAction hcell n
  have lhs := cellActionChainRepresentation_cellularChainBasis C hcell R (g * h) i
  rw [map_mul, mul_apply_eq_comp,
    cellActionChainRepresentation_cellularChainBasis C hcell R h i, map_smul,
    cellActionChainRepresentation_cellularChainBasis C hcell R g (h • i), smul_smul,
    ← mul_smul] at lhs
  have hrepr := congrArg (fun x ↦ (cellularChainBasis C R n).repr x ((g * h) • i)) lhs
  simpa only [map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
    smul_eq_mul, mul_one] using hrepr.symm

/-- When translation by `g` carries the characteristic map of `i` strictly onto that of `g • i`
(as for lifted CW structures along coverings, or simplicial actions preserving the vertex order on
each face via `PreAbstractSimplicialComplex.SimplicialMap.realizationMap_characteristicMap`), the
scaling coefficient `TauCeti.cellActionBasisCoeff` is `1`. -/
theorem cellActionBasisCoeff_eq_one_of_smul_map {n : ℕ} {g : G} {i : cell C n}
    (hmap : letI := cellMulAction hcell n
      ∀ x ∈ closedBall (0 : Fin n → ℝ) 1, g • map n i x = map n (g • i) x) :
    cellActionBasisCoeff C hcell R g i = 1 := by
  let := cellMulAction hcell n
  have hstrict : cellActionChainRepresentation C hcell R n g (cellularChainBasis C R n i) =
      cellularChainBasis C R n (g • i) := by
    rw [cellActionChainRepresentation_apply]
    exact cellularChainGroupMap_cellularChainBasis C C
      (isCellular_cellActionSMul C g (hcell g)) R fun x hx hxC ↦
        (coe_cellActionSMul_apply C g (hcell g) ⟨map n i x, hxC⟩).trans (hmap x hx)
  rw [cellActionBasisCoeff, hstrict, Module.Basis.repr_self, Finsupp.single_eq_same]

/-- The **augmentation** of `TauCeti.cellActionChainRepresentation` in degree `0` onto the trivial
representation. -/
def cellActionAugmentationRep :
    Rep.of (cellActionChainRepresentation C hcell R 0) ⟶ Rep.trivial R G R :=
  cellularActionAugmentation C (fun g ↦ cellActionSMul C g (hcell g))
    (fun g ↦ isCellular_cellActionSMul C g (hcell g))
    (cellActionSMul_one C (hcell 1))
    (fun g h ↦ cellActionSMul_mul C g h (hcell g) (hcell h) (hcell (g * h))) R

/-- The underlying linear map of `TauCeti.cellActionAugmentationRep` is the cellular augmentation
of `C`. -/
@[simp]
theorem cellActionAugmentationRep_hom_toLinearMap :
    (cellActionAugmentationRep C hcell R).hom.toLinearMap =
      (cellularAugmentation C (ModuleCat.of R R)).hom := by
  unfold cellActionAugmentationRep
  exact cellularActionAugmentation_hom_toLinearMap _ _ _ _ _ _

/-- The equivariant cellular augmentation vanishes on boundaries of `1`-cells. -/
@[reassoc (attr := simp)]
theorem cellActionDifferentialRep_comp_cellActionAugmentationRep :
    cellActionDifferentialRep C hcell R 0 ≫ cellActionAugmentationRep C hcell R = 0 := by
  unfold cellActionDifferentialRep cellActionAugmentationRep
  exact cellularActionDifferential_comp_cellularActionAugmentation _ _ _ _ _ _

/-- The **augmentation of `TauCeti.cellActionChainComplexRep`** as a chain map in `Rep R G` to the
trivial representation concentrated in degree `0`. -/
def cellActionChainComplexRepAugmentation :
    cellActionChainComplexRep C hcell R ⟶
      (ChainComplex.single₀ (Rep.{w} R G)).obj (Rep.trivial R G R) :=
  cellularActionComplexAugmentation C (fun g ↦ cellActionSMul C g (hcell g))
    (fun g ↦ isCellular_cellActionSMul C g (hcell g))
    (cellActionSMul_one C (hcell 1))
    (fun g h ↦ cellActionSMul_mul C g h (hcell g) (hcell h) (hcell (g * h))) R

/-- In degree `0`, `TauCeti.cellActionChainComplexRepAugmentation` is
`TauCeti.cellActionAugmentationRep`. -/
@[simp]
theorem cellActionChainComplexRepAugmentation_f_zero :
    (cellActionChainComplexRepAugmentation C hcell R).f 0 =
      eqToHom (cellActionChainComplexRep_X C hcell R 0) ≫ cellActionAugmentationRep C hcell R := by
  have hX : cellActionChainComplexRep_X C hcell R 0 =
      cellularActionComplex_X C (fun g ↦ cellActionSMul C g (hcell g))
        (fun g ↦ isCellular_cellActionSMul C g (hcell g))
        (cellActionSMul_one C (hcell 1))
        (fun g h ↦ cellActionSMul_mul C g h (hcell g) (hcell h) (hcell (g * h))) R 0 :=
    Subsingleton.elim _ _
  rw [hX]
  unfold cellActionChainComplexRepAugmentation cellActionAugmentationRep
  exact cellularActionComplexAugmentation_f_zero _ _ _ _ _ _

/-- **The augmented cellular chain complex of a contractible CW complex with a cellular action is
exact.** -/
theorem quasiIso_cellActionChainComplexRepAugmentation [ContractibleSpace C] :
    QuasiIso (cellActionChainComplexRepAugmentation C hcell R) := by
  unfold cellActionChainComplexRepAugmentation
  exact quasiIso_cellularActionComplexAugmentation _ _ _ _ _ _

end Action

section GroupAction

variable {E : Type w} [TopologicalSpace E] [T2Space E] (C : Set E) [CWComplex C]
  {G : Type w} [Group G] [MulAction G E] [ContinuousConstSMul G E]
  (hcell : ∀ (g : G) (n : ℕ) (i : cell C n), ∃ j : cell C n, g • openCell n i = openCell n j)

section Units

variable (R : Type w) [Ring R]

/-- For a group action carrying open cells onto open cells, the scalar
`TauCeti.cellActionBasisCoeff` by which `g` multiplies the cellular basis vector of `i` is a unit in
`Rˣ`, with inverse the scalar of `g⁻¹` at `g • i`. -/
def cellActionBasisUnit {n : ℕ} (g : G) (i : cell C n) : Rˣ :=
  letI := cellMulAction hcell n
  { val := cellActionBasisCoeff C hcell R g i
    inv := cellActionBasisCoeff C hcell R g⁻¹ (g • i)
    val_inv := by
      rw [← cellActionBasisCoeff_mul, inv_mul_cancel, cellActionBasisCoeff_one]
    inv_val := by
      have h := cellActionBasisCoeff_mul C hcell R g g⁻¹ (g • i)
      rw [mul_inv_cancel, cellActionBasisCoeff_one, inv_smul_smul] at h
      exact h.symm }

/-- The underlying ring element of `TauCeti.cellActionBasisUnit` is
`TauCeti.cellActionBasisCoeff`. -/
@[simp]
theorem val_cellActionBasisUnit {n : ℕ} (g : G) (i : cell C n) :
    (cellActionBasisUnit C hcell R g i : R) = cellActionBasisCoeff C hcell R g i :=
  (rfl)

/-- The unit attached to the identity group element is `1`. -/
@[simp]
theorem cellActionBasisUnit_one {n : ℕ} (i : cell C n) :
    cellActionBasisUnit C hcell R (1 : G) i = 1 :=
  Units.ext (cellActionBasisCoeff_one C hcell R i)

/-- Cocycle law for `TauCeti.cellActionBasisUnit` under group multiplication. -/
theorem cellActionBasisUnit_mul {n : ℕ} (g h : G) (i : cell C n) :
    letI := cellMulAction hcell n
    cellActionBasisUnit C hcell R (g * h) i =
      cellActionBasisUnit C hcell R h i * cellActionBasisUnit C hcell R g (h • i) :=
  Units.ext (cellActionBasisCoeff_mul C hcell R g h i)

/-- The inverse of `TauCeti.cellActionBasisUnit` at `(g, i)` is the unit of `g⁻¹` at `g • i`. -/
theorem cellActionBasisUnit_inv {n : ℕ} (g : G) (i : cell C n) :
    letI := cellMulAction hcell n
    (cellActionBasisUnit C hcell R g i)⁻¹ = cellActionBasisUnit C hcell R g⁻¹ (g • i) :=
  Units.ext rfl

/-- Translation by `g` acts on `cellularChainBasis` through the unit
`TauCeti.cellActionBasisUnit`. -/
theorem cellActionChainRepresentation_cellularChainBasis_unit {n : ℕ} (g : G) (i : cell C n) :
    letI := cellMulAction hcell n
    cellActionChainRepresentation C hcell R n g (cellularChainBasis C R n i) =
      cellActionBasisUnit C hcell R g i • cellularChainBasis C R n (g • i) :=
  cellActionChainRepresentation_cellularChainBasis C hcell R g i

/-- When translation by `g` carries the characteristic map of `i` strictly onto that of `g • i`,
the orientation unit `TauCeti.cellActionBasisUnit` is `1`. -/
theorem cellActionBasisUnit_eq_one_of_smul_map {n : ℕ} {g : G} {i : cell C n}
    (hmap : letI := cellMulAction hcell n
      ∀ x ∈ closedBall (0 : Fin n → ℝ) 1, g • map n i x = map n (g • i) x) :
    cellActionBasisUnit C hcell R g i = 1 :=
  Units.ext (cellActionBasisCoeff_eq_one_of_smul_map C hcell R hmap)

end Units

section EquivariantBasis

variable (R : Type w) [CommRing R]

/-- Given representatives `s : ι → cell C n` and an equivariant parametrization
`e : (Σ _ : ι, G) ≃ cell C n` of the `n`-cells of `C`, rescaling each cellular basis vector `j` by
the unit of `(e.symm j).2` at `s (e.symm j).1` yields an `R`-basis whose vectors are strictly
permuted by `G`. -/
private def rescaledCellularChainBasis {n : ℕ} {ι : Type w}
    (s : ι → cell C n) (e : (Σ _ : ι, G) ≃ cell C n) :
    Module.Basis (cell C n) R (cellularChainGroup C (ModuleCat.of R R) n : ModuleCat R) :=
  (cellularChainBasis C R n).unitsSMul fun j ↦
    cellActionBasisUnit C hcell R (e.symm j).2 (s (e.symm j).1)

/-- At `e ⟨o, g⟩`, the rescaled cellular basis vector is the `g`-translate in the cellular chain
representation of the cellular basis vector of the chosen representative `s o`. -/
private theorem rescaledCellularChainBasis_apply_equiv {n : ℕ} {ι : Type w}
    (s : ι → cell C n) (e : (Σ _ : ι, G) ≃ cell C n)
    (he : letI := cellMulAction hcell n; ∀ (g : G) (o : ι), e ⟨o, g⟩ = g • s o)
    (o : ι) (g : G) :
    rescaledCellularChainBasis C hcell R s e (e ⟨o, g⟩) =
      cellActionChainRepresentation C hcell R n g (cellularChainBasis C R n (s o)) := by
  let := cellMulAction hcell n
  rw [rescaledCellularChainBasis, Module.Basis.unitsSMul_apply, Equiv.symm_apply_apply,
    Units.smul_def, val_cellActionBasisUnit, he g o,
    ← cellActionChainRepresentation_cellularChainBasis]

/-- `G` permutes `rescaledCellularChainBasis` strictly along left multiplication in the second
component of `e`. -/
private theorem cellActionChainRepresentation_rescaledCellularChainBasis {n : ℕ} {ι : Type w}
    (s : ι → cell C n) (e : (Σ _ : ι, G) ≃ cell C n)
    (he : letI := cellMulAction hcell n; ∀ (g : G) (o : ι), e ⟨o, g⟩ = g • s o)
    (g h : G) (o : ι) :
    cellActionChainRepresentation C hcell R n g
        (rescaledCellularChainBasis C hcell R s e (e ⟨o, h⟩)) =
      rescaledCellularChainBasis C hcell R s e (e ⟨o, g * h⟩) := by
  rw [rescaledCellularChainBasis_apply_equiv C hcell R s e he,
    rescaledCellularChainBasis_apply_equiv C hcell R s e he, map_mul, mul_apply_eq_comp]

/-- Equivalence with the free representation associated to an equivariant parametrization of the
`n`-cells. -/
private def freeEquivCellActionChainRepresentation {n : ℕ} {ι : Type w}
    (s : ι → cell C n) (e : (Σ _ : ι, G) ≃ cell C n)
    (he : letI := cellMulAction hcell n; ∀ (g : G) (o : ι), e ⟨o, g⟩ = g • s o) :
    (Representation.free R G ι).Equiv (cellActionChainRepresentation C hcell R n) :=
  (cellActionChainRepresentation C hcell R n).freeEquivOfBasis
    (rescaledCellularChainBasis C hcell R s e) e
    (cellActionChainRepresentation_rescaledCellularChainBasis C hcell R s e he)

/-- **An equivariant parametrization `(Σ _ : ι, G) ≃ cell C n` of the `n`-cells identifies the
`n`-th cellular chain group in `Rep R G` with the free representation on `ι`**, with
`single o (single 1 1)` corresponding to the cellular basis vector of `s o` and
`single o (single g r)` to `r` times its `g`-translate. -/
def cellActionChainRepIsoFreeOfEquiv {n : ℕ} {ι : Type w}
    (s : ι → cell C n) (e : (Σ _ : ι, G) ≃ cell C n)
    (he : letI := cellMulAction hcell n; ∀ (g : G) (o : ι), e ⟨o, g⟩ = g • s o) :
    Rep.of (cellActionChainRepresentation C hcell R n) ≅ Rep.free R G ι :=
  (Rep.mkIso (freeEquivCellActionChainRepresentation C hcell R s e he)).symm

/-- Under `TauCeti.cellActionChainRepIsoFreeOfEquiv`, the generator `single o (single g r)` of the
free representation maps to `r` times the `g`-translate of the cellular basis vector of the chosen
representative `s o`. -/
@[simp]
theorem cellActionChainRepIsoFreeOfEquiv_inv_hom_single {n : ℕ} {ι : Type w}
    (s : ι → cell C n) (e : (Σ _ : ι, G) ≃ cell C n)
    (he : letI := cellMulAction hcell n; ∀ (g : G) (o : ι), e ⟨o, g⟩ = g • s o)
    (o : ι) (g : G) (r : R) :
    (cellActionChainRepIsoFreeOfEquiv C hcell R s e he).inv.hom
        (Finsupp.single o (MonoidAlgebra.single g r)) =
      r • cellActionChainRepresentation C hcell R n g (cellularChainBasis C R n (s o)) := by
  rw [cellActionChainRepIsoFreeOfEquiv, Iso.symm_inv, Rep.mkIso_hom_hom_apply]
  exact (Representation.freeEquivOfBasis_single (cellActionChainRepresentation C hcell R n)
    (rescaledCellularChainBasis C hcell R s e) e _ o g r).trans
      (by rw [rescaledCellularChainBasis_apply_equiv C hcell R s e he])

/-- Under `TauCeti.cellActionChainRepIsoFreeOfEquiv`, the cellular basis vector of `s o` corresponds
to the generator `single o (single 1 1)`. This is not a `simp` lemma because `simp` unfolds
`TauCeti.cellularChainBasis` first. -/
theorem cellActionChainRepIsoFreeOfEquiv_hom_hom_cellularChainBasis {n : ℕ} {ι : Type w}
    (s : ι → cell C n) (e : (Σ _ : ι, G) ≃ cell C n)
    (he : letI := cellMulAction hcell n; ∀ (g : G) (o : ι), e ⟨o, g⟩ = g • s o)
    (o : ι) :
    (cellActionChainRepIsoFreeOfEquiv C hcell R s e he).hom.hom
        (cellularChainBasis C R n (s o)) =
      Finsupp.single o (MonoidAlgebra.single 1 1) := by
  have h := cellActionChainRepIsoFreeOfEquiv_inv_hom_single C hcell R s e he o 1 1
  rw [map_one, one_apply_eq_self, one_smul] at h
  rw [← h, Rep.hom_inv_apply]

/-- Under `TauCeti.cellActionChainRepIsoFreeOfEquiv`, the cellular basis vector of a translated
representative `g • s o` maps to `single o` weighted at `g` by the inverse orientation unit
`(cellActionBasisUnit C hcell R g (s o))⁻¹`. -/
theorem cellActionChainRepIsoFreeOfEquiv_hom_hom_cellularChainBasis_smul {n : ℕ} {ι : Type w}
    (s : ι → cell C n) (e : (Σ _ : ι, G) ≃ cell C n)
    (he : letI := cellMulAction hcell n; ∀ (g : G) (o : ι), e ⟨o, g⟩ = g • s o)
    (o : ι) (g : G) :
    letI := cellMulAction hcell n
    (cellActionChainRepIsoFreeOfEquiv C hcell R s e he).hom.hom
        (cellularChainBasis C R n (g • s o)) =
      Finsupp.single o
        (MonoidAlgebra.single g (↑(cellActionBasisUnit C hcell R g (s o))⁻¹ : R)) := by
  let := cellMulAction hcell n
  have h := cellActionChainRepIsoFreeOfEquiv_inv_hom_single C hcell R s e he o g
    (↑(cellActionBasisUnit C hcell R g (s o))⁻¹ : R)
  rw [cellActionChainRepresentation_cellularChainBasis_unit, ← Units.smul_def, smul_smul,
    inv_mul_cancel, one_smul] at h
  rw [← h, Rep.hom_inv_apply]

end EquivariantBasis

section Free

variable (hfree : ∀ (g : G) (n : ℕ) (i : cell C n), g • openCell n i = openCell n i → g = 1)
  (R : Type w) [CommRing R]

/-- The orbit parametrization `(Σ _ : orbitRel.Quotient G (cell C n), G) ≃ cell C n` attached to a
section `φ` of the orbit quotient. -/
private def orbitSigmaEquiv {n : ℕ}
    (φ : (letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) → cell C n)
    (hφ : letI := cellMulAction hcell n; LeftInverse Quotient.mk'' φ) :
    (Σ _ : (letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)), G) ≃
      cell C n :=
  letI := cellMulAction hcell n
  haveI := isCancelSMul_cell hcell hfree n
  (Equiv.sigmaEquivProd _ G).trans
    (MulAction.selfEquivOrbitsQuotientProd' hφ IsCancelSMul.stabilizer_eq_bot).symm

/-- **The cellular chains of a free cellular action are free over the group ring on the cell
orbits.** Given a choice `φ o` of representative in each `G`-orbit of `n`-cells of `C`, the `n`-th
cellular chain group of `C` is isomorphic in `Rep R G` to the free representation on the `G`-orbits
of `n`-cells, with `single o (single 1 1)` corresponding to the cellular basis vector of `φ o` and
`single o (single g r)` to `r` times its `g`-translate. -/
def cellActionChainRepIsoFreeOfOrbits {n : ℕ}
    (φ : (letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) → cell C n)
    (hφ : letI := cellMulAction hcell n; LeftInverse Quotient.mk'' φ) :
    Rep.of (cellActionChainRepresentation C hcell R n) ≅
      Rep.free R G (letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) :=
  cellActionChainRepIsoFreeOfEquiv C hcell R φ
    (orbitSigmaEquiv C hcell hfree φ hφ) fun g o ↦ by
      let := cellMulAction hcell n
      have := isCancelSMul_cell hcell hfree n
      simp [orbitSigmaEquiv]

/-- Under `TauCeti.cellActionChainRepIsoFreeOfOrbits`, the generator `single o (single g r)` of the
free representation maps to `r` times the `g`-translate of the cellular basis vector of the chosen
orbit representative `φ o`. -/
@[simp]
theorem cellActionChainRepIsoFreeOfOrbits_inv_hom_single {n : ℕ}
    (φ : (letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) → cell C n)
    (hφ : letI := cellMulAction hcell n; LeftInverse Quotient.mk'' φ)
    (o : letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) (g : G) (r : R) :
    (cellActionChainRepIsoFreeOfOrbits C hcell hfree R φ hφ).inv.hom
        (Finsupp.single o (MonoidAlgebra.single g r)) =
      r • cellActionChainRepresentation C hcell R n g (cellularChainBasis C R n (φ o)) :=
  cellActionChainRepIsoFreeOfEquiv_inv_hom_single C hcell R φ _ _ o g r

/-- Under `TauCeti.cellActionChainRepIsoFreeOfOrbits`, the cellular basis vector of the chosen
representative `φ o` corresponds to the generator `single o (single 1 1)`. This is not a `simp`
lemma because `simp` unfolds `TauCeti.cellularChainBasis` first. -/
theorem cellActionChainRepIsoFreeOfOrbits_hom_hom_cellularChainBasis {n : ℕ}
    (φ : (letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) → cell C n)
    (hφ : letI := cellMulAction hcell n; LeftInverse Quotient.mk'' φ)
    (o : letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) :
    (cellActionChainRepIsoFreeOfOrbits C hcell hfree R φ hφ).hom.hom
        (cellularChainBasis C R n (φ o)) =
      Finsupp.single o (MonoidAlgebra.single 1 1) :=
  cellActionChainRepIsoFreeOfEquiv_hom_hom_cellularChainBasis C hcell R φ _ _ o

/-- Under `TauCeti.cellActionChainRepIsoFreeOfOrbits`, the cellular basis vector of a translated
orbit representative `g • φ o` maps to `single o` weighted at `g` by the inverse orientation unit
`(cellActionBasisUnit C hcell R g (φ o))⁻¹`. -/
theorem cellActionChainRepIsoFreeOfOrbits_hom_hom_cellularChainBasis_smul {n : ℕ}
    (φ : (letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) → cell C n)
    (hφ : letI := cellMulAction hcell n; LeftInverse Quotient.mk'' φ)
    (o : letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) (g : G) :
    letI := cellMulAction hcell n
    (cellActionChainRepIsoFreeOfOrbits C hcell hfree R φ hφ).hom.hom
        (cellularChainBasis C R n (g • φ o)) =
      Finsupp.single o
        (MonoidAlgebra.single g (↑(cellActionBasisUnit C hcell R g (φ o))⁻¹ : R)) :=
  cellActionChainRepIsoFreeOfEquiv_hom_hom_cellularChainBasis_smul C hcell R φ _ _ o g

include hfree in
/-- Every term of `TauCeti.cellActionChainComplexRep` for a free cellular group action is a
projective object of `Rep R G`. -/
theorem projective_cellActionChainComplexRep_X (n : ℕ) :
    Projective ((cellActionChainComplexRep C hcell R).X n) := by
  rw [cellActionChainComplexRep_X]
  exact Projective.of_iso
    (cellActionChainRepIsoFreeOfOrbits C hcell hfree R Quotient.out
      (letI := cellMulAction hcell n; Quotient.out_eq')).symm
    inferInstance

include hfree in
/-- **The cellular chains of a contractible CW complex with a free cellular group action form a
projective resolution** of the trivial representation `Rep.trivial R G R`. -/
def cellActionResolution [ContractibleSpace C] :
    ProjectiveResolution (Rep.trivial R G R) where
  complex := cellActionChainComplexRep C hcell R
  projective := projective_cellActionChainComplexRep_X C hcell hfree R
  π := cellActionChainComplexRepAugmentation C hcell R
  quasiIso := quasiIso_cellActionChainComplexRepAugmentation C hcell R

/-- The underlying chain complex of `TauCeti.cellActionResolution` is
`TauCeti.cellActionChainComplexRep`. -/
@[simp]
theorem cellActionResolution_complex [ContractibleSpace C] :
    (cellActionResolution C hcell hfree R).complex = cellActionChainComplexRep C hcell R :=
  (rfl)

-- Under `module`, the public statement cannot unfold the unexposed body of
-- `TauCeti.cellActionResolution`, so it transports along `cellActionResolution_complex`.
/-- The augmentation of `TauCeti.cellActionResolution` is
`TauCeti.cellActionChainComplexRepAugmentation`. -/
@[simp]
theorem cellActionResolution_π [ContractibleSpace C] :
    (cellActionResolution C hcell hfree R).π =
      eqToHom (cellActionResolution_complex C hcell hfree R) ≫
        cellActionChainComplexRepAugmentation C hcell R :=
  (Category.id_comp _).symm

end Free

end GroupAction

section QuotientCovering

variable {E B : Type w} [TopologicalSpace E] [T2Space E] [CWComplex (univ : Set E)]
  [TopologicalSpace B] {G : Type w} [Group G] [MulAction G E] {p : E → B}
  (hp : IsQuotientCoveringMap p G)
  (hcell : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
    ∃ j : cell (univ : Set E) n, g • openCell n i = openCell n j)
  (hfree : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
    g • openCell n i = openCell n i → g = 1)
  (R : Type w) [CommRing R]

/-- **The cellular chains of the total space of a free cellular quotient covering are free over the
group ring, with basis one chosen lift of each cell of the orbit space.** Given a lift `s b` of each
`n`-cell `b` of `B` (for the orbit CW structure `IsQuotientCoveringMap.cwComplexQuotient`), the
`n`-th cellular chain group of `E` is isomorphic in `Rep R G` to
`Rep.free R G (cell (univ : Set B) n)`, with `single b (single 1 1)` corresponding to the cellular
basis vector of `s b` and `single b (single g r)` to `r` times its `g`-translate. -/
def _root_.IsQuotientCoveringMap.cellActionChainRepIsoFree {n : ℕ}
    (s : (letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) → cell (univ : Set E) n)
    (hs : letI := hp.cwComplexQuotient hcell hfree; ∀ b, p '' openCell n (s b) = openCell n b) :
    haveI := hp.toContinuousConstSMul
    Rep.of (cellActionChainRepresentation (univ : Set E) hcell R n) ≅
      Rep.free R G (letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) :=
  haveI := hp.toContinuousConstSMul
  cellActionChainRepIsoFreeOfEquiv (univ : Set E) hcell R s
    (hp.sigmaSMulQuotientLiftEquiv hcell hfree s hs)
    fun g b ↦ hp.sigmaSMulQuotientLiftEquiv_apply hcell hfree s hs ⟨b, g⟩

/-- Under `IsQuotientCoveringMap.cellActionChainRepIsoFree`, the generator `single b (single g r)`
of the free representation on the `n`-cells of `B` maps to `r` times the `g`-translate of the
cellular basis vector of the lifted cell `s b`. -/
@[simp]
theorem _root_.IsQuotientCoveringMap.cellActionChainRepIsoFree_inv_hom_single {n : ℕ}
    (s : (letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) → cell (univ : Set E) n)
    (hs : letI := hp.cwComplexQuotient hcell hfree; ∀ b, p '' openCell n (s b) = openCell n b)
    (b : letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) (g : G) (r : R) :
    haveI := hp.toContinuousConstSMul
    (hp.cellActionChainRepIsoFree hcell hfree R s hs).inv.hom
        (Finsupp.single b (MonoidAlgebra.single g r)) =
      r • cellActionChainRepresentation (univ : Set E) hcell R n g
        (cellularChainBasis (univ : Set E) R n (s b)) :=
  haveI := hp.toContinuousConstSMul
  cellActionChainRepIsoFreeOfEquiv_inv_hom_single (univ : Set E) hcell R s _ _ b g r

/-- Under `IsQuotientCoveringMap.cellActionChainRepIsoFree`, the cellular basis vector of the chosen
lift `s b` corresponds to the generator `single b (single 1 1)`. This is not a `simp` lemma because
`simp` unfolds `TauCeti.cellularChainBasis` first. -/
theorem _root_.IsQuotientCoveringMap.cellActionChainRepIsoFree_hom_hom_cellularChainBasis {n : ℕ}
    (s : (letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) → cell (univ : Set E) n)
    (hs : letI := hp.cwComplexQuotient hcell hfree; ∀ b, p '' openCell n (s b) = openCell n b)
    (b : letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) :
    haveI := hp.toContinuousConstSMul
    (hp.cellActionChainRepIsoFree hcell hfree R s hs).hom.hom
        (cellularChainBasis (univ : Set E) R n (s b)) =
      Finsupp.single b (MonoidAlgebra.single 1 1) :=
  haveI := hp.toContinuousConstSMul
  cellActionChainRepIsoFreeOfEquiv_hom_hom_cellularChainBasis (univ : Set E) hcell R s _ _ b

/-- Under `IsQuotientCoveringMap.cellActionChainRepIsoFree`, the cellular basis vector of the
translated lift `g • s b` maps to `single b` weighted at `g` by the inverse orientation unit
`(cellActionBasisUnit (univ : Set E) hcell R g (s b))⁻¹`. -/
theorem _root_.IsQuotientCoveringMap.cellActionChainRepIsoFree_hom_hom_cellularChainBasis_smul
    {n : ℕ}
    (s : (letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) → cell (univ : Set E) n)
    (hs : letI := hp.cwComplexQuotient hcell hfree; ∀ b, p '' openCell n (s b) = openCell n b)
    (b : letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) (g : G) :
    letI := cellMulAction hcell n
    haveI := hp.toContinuousConstSMul
    (hp.cellActionChainRepIsoFree hcell hfree R s hs).hom.hom
        (cellularChainBasis (univ : Set E) R n (g • s b)) =
      Finsupp.single b (MonoidAlgebra.single g
        (↑(cellActionBasisUnit (univ : Set E) hcell R g (s b))⁻¹ : R)) :=
  haveI := hp.toContinuousConstSMul
  cellActionChainRepIsoFreeOfEquiv_hom_hom_cellularChainBasis_smul
    (univ : Set E) hcell R s _ _ b g

end QuotientCovering

end TauCeti
