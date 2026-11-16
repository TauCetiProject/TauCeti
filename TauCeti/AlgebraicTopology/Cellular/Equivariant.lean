/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Rep.Basic
public import TauCeti.AlgebraicTopology.Cellular.Augmentation
public import TauCeti.AlgebraicTopology.Cellular.Incidence
public import TauCeti.Topology.CWComplex.Classical.CellAction
import TauCeti.AlgebraicTopology.Cellular.Permutation

/-!
# Cellular chains with a monoid action

A family of cellular self-maps satisfying the action laws induces representations on cellular
chains (`TauCeti.cellularActionRepresentation`). Naturality of the cellular differential and
augmentation assembles these into a chain complex in `Rep R G` (`TauCeti.cellularActionComplex`)
with an equivariant augmentation onto `Rep.trivial R G R` (`TauCeti.cellularActionAugmentation` and
`TauCeti.cellularActionComplexAugmentation`). The forgetful isomorphism
(`TauCeti.cellularActionComplexForget₂Iso`) identifies the underlying complex of `R`-modules with
the geometric cellular chain complex, so when `C` is contractible the equivariant augmentation is a
quasi-isomorphism (`TauCeti.quasiIso_cellularActionComplexAugmentation`).

For a continuous monoid action on the ambient space carrying each open `n`-cell onto an open
`n`-cell (`TauCeti.cellMulAction`), restriction to `C` yields cellular self-maps
(`TauCeti.isCellular_cellActionSMul`), specializing the general construction to
`TauCeti.cellActionChainRepresentation`, `TauCeti.cellActionChainComplexRep`,
`TauCeti.cellActionAugmentationRep`, and `TauCeti.cellActionChainComplexRepAugmentation`.
Translations need not preserve chosen characteristic maps strictly: by
`TauCeti.cellularChainGroupMap_cellularChainBasis_eq_smul`, a translation carrying the open cell of
`i` onto that of `g • i` sends the cellular basis vector of `i` to a scalar multiple of the
cellular basis vector of `g • i` (`TauCeti.cellActionBasisCoeff`). For a group action, these
scalars are units (`TauCeti.cellActionBasisUnit`), over `ℤ` the orientation signs `±1` of the
induced self-homeomorphisms of cells.

## Main definitions and results

* `TauCeti.cellularActionRepresentation`, `TauCeti.cellularActionComplex`,
  `TauCeti.cellularActionAugmentation`, and `TauCeti.cellularActionComplexAugmentation`:
  equivariant cellular chains and augmentation for an arbitrary cellular monoid action.
* `TauCeti.cellActionChainRepresentation`, `TauCeti.cellActionChainComplexRep`,
  `TauCeti.cellActionAugmentationRep`, and `TauCeti.cellActionChainComplexRepAugmentation`:
  specialization to a continuous ambient monoid action carrying open cells onto open cells of the
  same dimension.
* `TauCeti.cellActionBasisCoeff` and `TauCeti.cellActionBasisUnit`: the scaling cocycle (and
  orientation unit, for a group action) relating `g` applied to the cellular basis vector of `i`
  and the cellular basis vector of `g • i`.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section I.4.
* T. tom Dieck, *Transformation Groups*, de Gruyter, 1987, Section II.1.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.2.
-/

public section

noncomputable section

open CategoryTheory Metric Set Topology Topology.RelCWComplex
open scoped Pointwise

namespace TauCeti

universe u

section CellularMaps

variable {X : Type u} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]
  {G : Type u} [Monoid G] (ρ : G → (TopCat.of C ⟶ TopCat.of C))
  (hcell : ∀ g, IsCellular C C (ρ g))
  (hone : ρ 1 = 𝟙 _) (hmul : ∀ g h, ρ (g * h) = ρ h ≫ ρ g)
  (R : Type u) [Ring R]

/-- The representation induced on cellular chains by a cellular action. -/
def cellularActionRepresentation (n : ℕ) :
    Representation R G (cellularChainGroup C (ModuleCat.of R R) n : ModuleCat R) where
  toFun g := (cellularChainGroupMap C C (hcell g) (ModuleCat.of R R) n).hom
  map_one' := by
    simp only [hone, cellularChainGroupMap_id, ModuleCat.hom_id]
    rfl
  map_mul' g h := by
    simpa only [hmul, ModuleCat.hom_comp, Module.End.mul_eq_comp] using
      congrArg ModuleCat.Hom.hom
        (cellularChainGroupMap_comp C C (hcell h) C (hcell g) (ModuleCat.of R R) n)

/-- The action is induced by the given cellular self-map. -/
@[simp]
theorem cellularActionRepresentation_apply (n : ℕ) (g : G) :
    cellularActionRepresentation C ρ hcell hone hmul R n g =
      (cellularChainGroupMap C C (hcell g) (ModuleCat.of R R) n).hom := (rfl)

/-- The cellular differential as a morphism of representations. -/
def cellularActionDifferential (n : ℕ) :
    Rep.of (cellularActionRepresentation C ρ hcell hone hmul R (n + 1)) ⟶
      Rep.of (cellularActionRepresentation C ρ hcell hone hmul R n) :=
  Rep.ofHom
    { toLinearMap := (cellularDifferential C (ModuleCat.of R R) n).hom
      isIntertwining' g := by
        simpa only [cellularActionRepresentation_apply, ModuleCat.hom_comp] using
          congrArg ModuleCat.Hom.hom
            (cellularChainGroupMap_comp_cellularDifferential C C (hcell g)
              (ModuleCat.of R R) n) }

/-- The underlying linear map is the cellular differential. -/
@[simp]
theorem cellularActionDifferential_hom_toLinearMap (n : ℕ) :
    (cellularActionDifferential C ρ hcell hone hmul R n).hom.toLinearMap =
      (cellularDifferential C (ModuleCat.of R R) n).hom := (rfl)

/-- Cellular chains retaining a cellular monoid action. -/
def cellularActionComplex : ChainComplex (Rep R G) ℕ :=
  ChainComplex.of (fun n ↦ Rep.of (cellularActionRepresentation C ρ hcell hone hmul R n))
    (cellularActionDifferential C ρ hcell hone hmul R) fun n ↦ by
      ext x
      exact ConcreteCategory.congr_hom
        (cellularDifferential_comp_cellularDifferential C (ModuleCat.of R R) n) x

/-- The terms of the equivariant cellular complex. -/
@[simp]
theorem cellularActionComplex_X (n : ℕ) :
    (cellularActionComplex C ρ hcell hone hmul R).X n =
      Rep.of (cellularActionRepresentation C ρ hcell hone hmul R n) := (rfl)

/-- Its differential is the equivariant cellular differential. -/
@[simp]
theorem cellularActionComplex_d (n : ℕ) :
    (cellularActionComplex C ρ hcell hone hmul R).d (n + 1) n =
      eqToHom (cellularActionComplex_X C ρ hcell hone hmul R (n + 1)) ≫
        cellularActionDifferential C ρ hcell hone hmul R n ≫
      eqToHom (cellularActionComplex_X C ρ hcell hone hmul R n).symm := by
  -- Proof irrelevance normalizes the reflexive transports without exposing the complex API.
  have h : ∀ m, cellularActionComplex_X C ρ hcell hone hmul R m = rfl :=
    fun _ ↦ Subsingleton.elim _ _
  rw [h (n + 1), h n]
  unfold cellularActionComplex
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact ChainComplex.of_d _ _ n

/-- Forgetting the action recovers the geometric cellular chain complex. -/
def cellularActionComplexForget₂Iso :
    cellularChainComplex C (ModuleCat.of R R) ≅
      ((forget₂ (Rep R G) (ModuleCat R)).mapHomologicalComplex _).obj
        (cellularActionComplex C ρ hcell hone hmul R) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ eqToIso (by
      rw [Functor.mapHomologicalComplex_obj_X, cellularActionComplex_X,
        cellularChainComplex_X]
      rfl))
    fun i j hij ↦ by
      subst i
      simp only [cellularChainComplex_d, Functor.mapHomologicalComplex_obj_d,
        cellularActionComplex_d, eqToIso.hom, Functor.map_comp, eqToHom_map,
        Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
      unfold cellularActionComplex
      simp only [eqToHom_refl, Category.comp_id,
        Rep.forget₂_moduleCat_map, cellularActionDifferential_hom_toLinearMap,
        ModuleCat.ofHom_hom]

/-- Components of the forgetful identification are the canonical cellular-term transports. -/
@[simp]
theorem cellularActionComplexForget₂Iso_hom_f (n : ℕ) :
    (cellularActionComplexForget₂Iso C ρ hcell hone hmul R).hom.f n =
      eqToHom (by
        rw [Functor.mapHomologicalComplex_obj_X, cellularActionComplex_X,
          cellularChainComplex_X]
        rfl) := (rfl)

/-- Inverse components of the forgetful identification are the reverse term transports. -/
@[simp]
theorem cellularActionComplexForget₂Iso_inv_f (n : ℕ) :
    (cellularActionComplexForget₂Iso C ρ hcell hone hmul R).inv.f n =
      eqToHom (by
        rw [Functor.mapHomologicalComplex_obj_X, cellularActionComplex_X,
          cellularChainComplex_X]
        rfl) := (rfl)

/-- The **augmentation** of `TauCeti.cellularActionRepresentation` in degree `0` onto the trivial
representation. -/
def cellularActionAugmentation :
    Rep.of (cellularActionRepresentation C ρ hcell hone hmul R 0) ⟶ Rep.trivial R G R :=
  Rep.ofHom
    { toLinearMap := (cellularAugmentation C (ModuleCat.of R R)).hom
      isIntertwining' g := LinearMap.ext fun x ↦ by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, Representation.trivial_apply,
          cellularActionRepresentation_apply]
        exact ConcreteCategory.congr_hom (cellularChainGroupMap_comp_cellularAugmentation C C
          (hcell g) (ModuleCat.of R R)) x }

/-- The underlying linear map of `TauCeti.cellularActionAugmentation` is the cellular augmentation
of `C`. -/
@[simp]
theorem cellularActionAugmentation_hom_toLinearMap :
    (cellularActionAugmentation C ρ hcell hone hmul R).hom.toLinearMap =
      (cellularAugmentation C (ModuleCat.of R R)).hom := (rfl)

/-- The equivariant cellular augmentation vanishes on boundaries of `1`-cells. -/
@[reassoc (attr := simp)]
theorem cellularActionDifferential_comp_cellularActionAugmentation :
    cellularActionDifferential C ρ hcell hone hmul R 0 ≫
      cellularActionAugmentation C ρ hcell hone hmul R = 0 := by
  refine Rep.hom_ext <| Representation.IntertwiningMap.ext <| LinearMap.ext fun x ↦ ?_
  have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (cellularDifferential_comp_cellularAugmentation C (ModuleCat.of R R))) x
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.comp_apply,
    LinearMap.zero_apply] at h
  simpa [Rep.hom_comp] using h

/-- The **augmentation of `TauCeti.cellularActionComplex`** as a chain map in `Rep R G` to the
trivial representation concentrated in degree `0`. -/
def cellularActionComplexAugmentation :
    cellularActionComplex C ρ hcell hone hmul R ⟶
      (ChainComplex.single₀ (Rep.{u} R G)).obj (Rep.trivial R G R) :=
  ((cellularActionComplex C ρ hcell hone hmul R).toSingle₀Equiv _).symm
    ⟨eqToHom (cellularActionComplex_X C ρ hcell hone hmul R 0) ≫
      cellularActionAugmentation C ρ hcell hone hmul R, by
        simp [cellularActionComplex_d]⟩

/-- In degree `0`, `TauCeti.cellularActionComplexAugmentation` is
`TauCeti.cellularActionAugmentation`. -/
@[simp]
theorem cellularActionComplexAugmentation_f_zero :
    (cellularActionComplexAugmentation C ρ hcell hone hmul R).f 0 =
      eqToHom (cellularActionComplex_X C ρ hcell hone hmul R 0) ≫
        cellularActionAugmentation C ρ hcell hone hmul R :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- **The augmented cellular chain complex of a contractible CW complex with a cellular monoid
action is exact.** -/
theorem quasiIso_cellularActionComplexAugmentation [ContractibleSpace C] :
    QuasiIso (cellularActionComplexAugmentation C ρ hcell hone hmul R) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ (forget₂ _ (ModuleCat R)),
    quasiIso_iff_of_arrow_mk_iso _
      (cellularChainComplexAugmentation C (ModuleCat.of R R)) ?_]
  · exact quasiIso_cellularChainComplexAugmentation _ _
  · refine Arrow.isoMk' _ _ (cellularActionComplexForget₂Iso C ρ hcell hone hmul R).symm
      ((HomologicalComplex.singleMapHomologicalComplex _ _ 0).app _) ?_
    -- Exclude `Rep.forget₂_moduleCat_map` so `forget₂` stays visible on `eqToHom` and on the
    -- augmentation map, where `eqToHom_map` and `h` apply.
    have h : (forget₂ (Rep R G) (ModuleCat R)).map
        (cellularActionAugmentation C ρ hcell hone hmul R) =
          cellularAugmentation C (ModuleCat.of R R) := by
      rw [Rep.forget₂_moduleCat_map, cellularActionAugmentation_hom_toLinearMap,
        ModuleCat.ofHom_hom]
    ext : 1
    simp [-Rep.forget₂_moduleCat_map, eqToHom_map, h]

end CellularMaps

section Action

variable {E : Type u} [TopologicalSpace E] [T2Space E] (C : Set E) [CWComplex C]
  {G : Type u} [Monoid G] [MulAction G E] [ContinuousConstSMul G E]
  (hcell : ∀ (g : G) (n : ℕ) (i : cell C n), ∃ j : cell C n, g • openCell n i = openCell n j)
  (R : Type u) [Ring R]

/-- The representation of `G` on the `n`-th cellular chain group of a Hausdorff CW complex `C`
induced by a continuous action carrying open cells onto open cells of the same dimension. -/
def cellActionChainRepresentation (n : ℕ) :
    Representation R G (cellularChainGroup C (ModuleCat.of R R) n : ModuleCat R) :=
  cellularActionRepresentation C (fun g ↦ cellActionSMul C g (hcell g))
    (fun g ↦ isCellular_cellActionSMul C g (hcell g))
    (cellActionSMul_one C (hcell 1))
    (fun g h ↦ cellActionSMul_mul C g h (hcell g) (hcell h) (hcell (g * h))) R n

/-- `TauCeti.cellActionChainRepresentation` is `TauCeti.cellularActionRepresentation` for the
restricted cellular translations `TauCeti.cellActionSMul`. -/
theorem cellActionChainRepresentation_def (n : ℕ) :
    cellActionChainRepresentation C hcell R n =
      cellularActionRepresentation C (fun g ↦ cellActionSMul C g (hcell g))
        (fun g ↦ isCellular_cellActionSMul C g (hcell g))
        (cellActionSMul_one C (hcell 1))
        (fun g h ↦ cellActionSMul_mul C g h (hcell g) (hcell h) (hcell (g * h))) R n :=
  (rfl)

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

/-- `TauCeti.cellActionDifferentialRep` is `TauCeti.cellularActionDifferential` for the restricted
cellular translations, transported across `TauCeti.cellActionChainRepresentation_def`. -/
theorem cellActionDifferentialRep_def (n : ℕ) :
    cellActionDifferentialRep C hcell R n =
      eqToHom (congrArg Rep.of (cellActionChainRepresentation_def C hcell R (n + 1))) ≫
        cellularActionDifferential C (fun g ↦ cellActionSMul C g (hcell g))
          (fun g ↦ isCellular_cellActionSMul C g (hcell g))
          (cellActionSMul_one C (hcell 1))
          (fun g h ↦ cellActionSMul_mul C g h (hcell g) (hcell h) (hcell (g * h))) R n ≫
        eqToHom (congrArg Rep.of (cellActionChainRepresentation_def C hcell R n)).symm := by
  unfold cellActionDifferentialRep cellActionChainRepresentation
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

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
def cellActionChainComplexRep : ChainComplex (Rep.{u} R G) ℕ :=
  cellularActionComplex C (fun g ↦ cellActionSMul C g (hcell g))
    (fun g ↦ isCellular_cellActionSMul C g (hcell g))
    (cellActionSMul_one C (hcell 1))
    (fun g h ↦ cellActionSMul_mul C g h (hcell g) (hcell h) (hcell (g * h))) R

/-- `TauCeti.cellActionChainComplexRep` is `TauCeti.cellularActionComplex` for the restricted
cellular translations `TauCeti.cellActionSMul`. -/
theorem cellActionChainComplexRep_def :
    cellActionChainComplexRep C hcell R =
      cellularActionComplex C (fun g ↦ cellActionSMul C g (hcell g))
        (fun g ↦ isCellular_cellActionSMul C g (hcell g))
        (cellActionSMul_one C (hcell 1))
        (fun g h ↦ cellActionSMul_mul C g h (hcell g) (hcell h) (hcell (g * h))) R :=
  (rfl)

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
    ((forget₂ (Rep.{u} R G) (ModuleCat.{u} R)).mapHomologicalComplex _).obj
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
  have hi : ∀ x ∈ openCell n i, ∀ hx : x ∈ C,
      (cellActionSMul C g (hcell g) ⟨x, hx⟩).1 ∈
        (skeletonLT C (n : ℕ∞) : Set E) ∪ openCell n (g • i) :=
    fun _ hx _ ↦
      Or.inr (coe_cellActionSMul_apply C g (hcell g) _ ▸ smul_mem_openCell_smul hcell g hx)
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

/-- When translation by `g` carries the characteristic map of `i` strictly onto that of an `n`-cell
`j` (as for lifted CW structures along coverings, or simplicial actions preserving the vertex order
on each face via `PreAbstractSimplicialComplex.SimplicialMap.realizationMap_characteristicMap`),
the scaling coefficient `TauCeti.cellActionBasisCoeff` is `1`. -/
theorem cellActionBasisCoeff_eq_one_of_smul_map {n : ℕ} {g : G} {i j : cell C n}
    (hmap : ∀ x ∈ closedBall (0 : Fin n → ℝ) 1, g • map n i x = map n j x) :
    cellActionBasisCoeff C hcell R g i = 1 := by
  let := cellMulAction hcell n
  have hj : j = g • i := by
    have hmem : map n j 0 ∈ openCell n j ∧ map n j 0 ∈ openCell n (g • i) :=
      ⟨map_zero_mem_openCell n j,
        hmap 0 (mem_closedBall_self zero_le_one) ▸
          smul_mem_openCell_smul hcell g (map_zero_mem_openCell n i)⟩
    exact eq_of_heq (Sigma.mk.inj_iff.1
      (eq_of_not_disjoint_openCell (not_disjoint_iff.2 ⟨_, hmem.1, hmem.2⟩))).2
  subst hj
  have hstrict : cellActionChainRepresentation C hcell R n g (cellularChainBasis C R n i) =
      cellularChainBasis C R n (g • i) := by
    rw [cellActionChainRepresentation_apply]
    exact cellularChainGroupMap_cellularChainBasis C C
      (isCellular_cellActionSMul C g (hcell g)) R fun x hx hxC ↦
        (coe_cellActionSMul_apply C g (hcell g) ⟨map n i x, hxC⟩).trans (hmap x hx)
  rw [cellActionBasisCoeff, hstrict, Module.Basis.repr_self, Finsupp.single_eq_same]

/-- Every element scales the cellular basis vector of a `0`-cell by `1`. -/
@[simp]
theorem cellActionBasisCoeff_zero (g : G) (i : cell C 0) :
    cellActionBasisCoeff C hcell R g i = 1 := by
  let := cellMulAction hcell 0
  refine cellActionBasisCoeff_eq_one_of_smul_map C hcell R (j := g • i) fun x _ ↦ ?_
  rw [Subsingleton.elim x 0]
  have hmem := smul_mem_openCell_smul hcell g (map_zero_mem_openCell 0 i)
  rw [openCell_zero_eq_singleton, mem_singleton_iff] at hmem
  exact hmem.trans (congrArg (map 0 (g • i)) (Subsingleton.elim _ _))

/-- The **augmentation** of `TauCeti.cellActionChainRepresentation` in degree `0` onto the trivial
representation. -/
def cellActionAugmentationRep :
    Rep.of (cellActionChainRepresentation C hcell R 0) ⟶ Rep.trivial R G R :=
  cellularActionAugmentation C (fun g ↦ cellActionSMul C g (hcell g))
    (fun g ↦ isCellular_cellActionSMul C g (hcell g))
    (cellActionSMul_one C (hcell 1))
    (fun g h ↦ cellActionSMul_mul C g h (hcell g) (hcell h) (hcell (g * h))) R

/-- `TauCeti.cellActionAugmentationRep` is `TauCeti.cellularActionAugmentation` for the restricted
cellular translations, transported across `TauCeti.cellActionChainRepresentation_def`. -/
theorem cellActionAugmentationRep_def :
    cellActionAugmentationRep C hcell R =
      eqToHom (congrArg Rep.of (cellActionChainRepresentation_def C hcell R 0)) ≫
        cellularActionAugmentation C (fun g ↦ cellActionSMul C g (hcell g))
          (fun g ↦ isCellular_cellActionSMul C g (hcell g))
          (cellActionSMul_one C (hcell 1))
          (fun g h ↦ cellActionSMul_mul C g h (hcell g) (hcell h) (hcell (g * h))) R :=
  (Category.id_comp _).symm

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
      (ChainComplex.single₀ (Rep.{u} R G)).obj (Rep.trivial R G R) :=
  cellularActionComplexAugmentation C (fun g ↦ cellActionSMul C g (hcell g))
    (fun g ↦ isCellular_cellActionSMul C g (hcell g))
    (cellActionSMul_one C (hcell 1))
    (fun g h ↦ cellActionSMul_mul C g h (hcell g) (hcell h) (hcell (g * h))) R

/-- `TauCeti.cellActionChainComplexRepAugmentation` is `TauCeti.cellularActionComplexAugmentation`
for the restricted cellular translations, transported across
`TauCeti.cellActionChainComplexRep_def`. -/
theorem cellActionChainComplexRepAugmentation_def :
    cellActionChainComplexRepAugmentation C hcell R =
      eqToHom (cellActionChainComplexRep_def C hcell R) ≫
        cellularActionComplexAugmentation C (fun g ↦ cellActionSMul C g (hcell g))
          (fun g ↦ isCellular_cellActionSMul C g (hcell g))
          (cellActionSMul_one C (hcell 1))
          (fun g h ↦ cellActionSMul_mul C g h (hcell g) (hcell h) (hcell (g * h))) R :=
  (Category.id_comp _).symm

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

section Units

variable {E : Type u} [TopologicalSpace E] [T2Space E] (C : Set E) [CWComplex C]
  {G : Type u} [Group G] [MulAction G E] [ContinuousConstSMul G E]
  (hcell : ∀ (g : G) (n : ℕ) (i : cell C n), ∃ j : cell C n, g • openCell n i = openCell n j)
  (R : Type u) [Ring R]

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

/-- When translation by `g` carries the characteristic map of `i` strictly onto that of an `n`-cell
`j`, the orientation unit `TauCeti.cellActionBasisUnit` is `1`. -/
theorem cellActionBasisUnit_eq_one_of_smul_map {n : ℕ} {g : G} {i j : cell C n}
    (hmap : ∀ x ∈ closedBall (0 : Fin n → ℝ) 1, g • map n i x = map n j x) :
    cellActionBasisUnit C hcell R g i = 1 :=
  Units.ext (cellActionBasisCoeff_eq_one_of_smul_map C hcell R hmap)

/-- The orientation unit attached to a `0`-cell is `1`. -/
@[simp]
theorem cellActionBasisUnit_zero (g : G) (i : cell C 0) :
    cellActionBasisUnit C hcell R g i = 1 :=
  Units.ext (cellActionBasisCoeff_zero C hcell R g i)

end Units

end TauCeti
