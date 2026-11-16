/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.RepresentationTheory.Rep.Iso
public import TauCeti.AlgebraicTopology.Cellular.Augmentation
public import TauCeti.AlgebraicTopology.Cellular.Equivariant
public import TauCeti.AlgebraicTopology.Cellular.LocalDegree
public import TauCeti.RepresentationTheory.FreeOfBasis
public import TauCeti.Topology.CWComplex.Classical.OrbitSpace

import TauCeti.GroupTheory.GroupAction.Free

/-!
# Cellular chains and projective resolutions for free cellular actions

Let `C` be a CW complex in a Hausdorff space `E`, and let a monoid `G` act continuously on `E`
carrying every open `n`-cell of `C` onto an open `n`-cell of `C`. Unlike a lifted CW structure on a
covering space, translation by `g : G` is not required to carry characteristic maps onto
characteristic maps; it only permutes the open cells, and hence the closed cells and skeleta. Each
translation is therefore a cellular self-map of `C` (`TauCeti.isCellular_cellActionSMul`), so the
cellular chain complex of `C` with coefficients in a ring `R` carries a representation of `G`
(`TauCeti.cellActionRepresentation`, `TauCeti.cellActionComplex`), together with an equivariant
augmentation to the trivial representation (`TauCeti.cellActionAugmentation`,
`TauCeti.cellActionComplexAugmentation`) which is a quasi-isomorphism whenever `C` is contractible
(`TauCeti.quasiIso_cellActionComplexAugmentation`).

Because translation by `g` maps the closed cell of an `n`-cell `i` onto the closed cell of `g • i`,
the local-homology coordinate readout (`TauCeti.cellularChainGroupMap_cellularChainBasis_eq_smul`)
shows that `g` acts monomially on the cellular basis: `g • eᵢ = c(g, i) • e_{g • i}` for a scalar
`c(g, i) : R` (`TauCeti.cellActionRepresentation_cellularChainBasis_eq_smul`). When `G` is a
group, these scalars are units in `R`
(`TauCeti.isUnit_repr_cellActionRepresentation_cellularChainBasis`).

When `G` is a group, `R` is a commutative ring, and `G` acts freely on the open cells of `C`, the
monomial-basis freeness theorem (`Representation.freeEquivOfMonomialBasis`) identifies each
cellular chain group as a free `R[G]`-module:

* given any equivariant bijection `(Σ _ : ι, G) ≃ cell C n`, the `n`-th cellular chain group is
  isomorphic to `Rep.free R G ι` (`TauCeti.cellActionRepIsoFreeOfEquiv`);
* given any choice of orbit representatives of the `n`-cells of `C`, it is isomorphic to the free
  representation on the `G`-orbits of `n`-cells (`TauCeti.cellActionRepIsoFree`), hence projective
  (`TauCeti.projective_cellActionComplex_X`);
* for a quotient covering map `p : E → B` (`IsQuotientCoveringMap p G`) with the orbit-space CW
  structure `IsQuotientCoveringMap.cwComplexQuotient` on `B`, any choice of lifts of the `n`-cells
  of `B` is an `R[G]`-basis of the `n`-th cellular chain group of `E`
  (`TauCeti.cellActionRepIsoFreeOfQuotientCovering`).

Consequently, whenever `C` is contractible, the augmented cellular chain complex of `C` is a free
resolution of `Rep.trivial R G R`, packaged as a projective resolution
`TauCeti.cellActionResolution`.

## Main definitions

* `TauCeti.cellActionRepresentation`: the representation of `G` on the `n`-th cellular chain group
  of `C`.
* `TauCeti.cellActionDifferential`: the cellular differential as a morphism of representations.
* `TauCeti.cellActionComplex`: the cellular chain complex of `C` in `Rep R G`.
* `TauCeti.cellActionComplexForget₂Iso`: forgetting the action recovers the cellular chain complex
  of `C`.
* `TauCeti.cellActionAugmentation` and `TauCeti.cellActionComplexAugmentation`: the equivariant
  augmentation to `Rep.trivial R G R`.
* `TauCeti.cellActionRepIsoFreeOfEquiv`, `TauCeti.cellActionRepIsoFree`, and
  `TauCeti.cellActionRepIsoFreeOfQuotientCovering`: freeness of the cellular chain groups over
  `R[G]`.
* `TauCeti.cellActionResolution`: for contractible `C` with a free cellular `G`-action, the
  projective resolution of `Rep.trivial R G R` by the cellular chain complex of `C`.

## Main results

* `TauCeti.cellActionRepresentation_cellularChainBasis_eq_smul`: a cellular action acts monomially
  on the cellular basis.
* `TauCeti.isUnit_repr_cellActionRepresentation_cellularChainBasis`: for a group action, the
  monomial scalars are units.
* `TauCeti.quasiIso_cellActionComplexAugmentation`: for contractible `C`, the equivariant
  augmentation is a quasi-isomorphism.
* `TauCeti.projective_cellActionComplex_X`: for a free cellular group action, each cellular chain
  group is a projective representation.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section I.4, Proposition 4.1, and
  Section II.4.
* T. tom Dieck, *Transformation Groups*, de Gruyter, 1987, Section II.1 (free `G`-CW complexes).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 1.B and Section 2.2.
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology Topology.RelCWComplex
open scoped Pointwise

universe w

namespace TauCeti

section Action

variable {E : Type w} [TopologicalSpace E] [T2Space E] (C : Set E) [CWComplex C]
  {G : Type w} [Monoid G] [MulAction G E] [ContinuousConstSMul G E]
  (hcell : ∀ (g : G) (n : ℕ) (i : cell C n),
    ∃ j : cell C n, g • openCell n i = openCell n j)
  (R : Type w) [Ring R]

/-- The representation of `G` on the `n`-th cellular chain group of `C` induced by a continuous
cellular action permuting open cells. -/
def cellActionRepresentation (n : ℕ) :
    Representation R G (cellularChainGroup C (ModuleCat.of R R) n : ModuleCat R) :=
  cellularActionRepresentation C (cellActionSMul C hcell) (isCellular_cellActionSMul C hcell)
    (cellActionSMul_one C hcell) (cellActionSMul_mul C hcell) R n

/-- On cellular chains, `g : G` acts by the chain-group map induced by translation by `g`. -/
@[simp]
theorem cellActionRepresentation_apply (n : ℕ) (g : G) :
    cellActionRepresentation C hcell R n g =
      (cellularChainGroupMap C C (isCellular_cellActionSMul C hcell g)
        (ModuleCat.of R R) n).hom :=
  cellularActionRepresentation_apply ..

/-- The cellular differential as a morphism of `G`-representations. -/
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
  cellularActionDifferential_hom_toLinearMap ..

/-- The cellular chain complex of `C`, equipped with the representation of `G` induced by a
continuous action permuting open cells. -/
def cellActionComplex : ChainComplex (Rep R G) ℕ :=
  cellularActionComplex C (cellActionSMul C hcell) (isCellular_cellActionSMul C hcell)
    (cellActionSMul_one C hcell) (cellActionSMul_mul C hcell) R

/-- The degree-`n` object of `TauCeti.cellActionComplex` is the `n`-th cellular chain group with
the induced action of `G`. -/
@[simp]
theorem cellActionComplex_X (n : ℕ) :
    (cellActionComplex C hcell R).X n = Rep.of (cellActionRepresentation C hcell R n) :=
  cellularActionComplex_X ..

/-- The differential of `TauCeti.cellActionComplex` is `TauCeti.cellActionDifferential`. -/
@[simp]
theorem cellActionComplex_d (n : ℕ) :
    (cellActionComplex C hcell R).d (n + 1) n =
      eqToHom (cellActionComplex_X C hcell R (n + 1)) ≫
        cellActionDifferential C hcell R n ≫
        eqToHom (cellActionComplex_X C hcell R n).symm :=
  cellularActionComplex_d ..

/-- Forgetting the `G`-action identifies `TauCeti.cellActionComplex` with the ordinary cellular
chain complex of `C`. -/
def cellActionComplexForget₂Iso :
    ((forget₂ (Rep.{w} R G) (ModuleCat.{w} R)).mapHomologicalComplex _).obj
        (cellActionComplex C hcell R) ≅
      cellularChainComplex C (ModuleCat.of R R) :=
  (cellularActionComplexForget₂Iso C (cellActionSMul C hcell) (isCellular_cellActionSMul C hcell)
    (cellActionSMul_one C hcell) (cellActionSMul_mul C hcell) R).symm

/-- The components of `TauCeti.cellActionComplexForget₂Iso` are the canonical object transports. -/
@[simp]
theorem cellActionComplexForget₂Iso_hom_f (n : ℕ) :
    (cellActionComplexForget₂Iso C hcell R).hom.f n =
      eqToHom (by
        rw [Functor.mapHomologicalComplex_obj_X, cellularChainComplex_X, cellActionComplex_X]
        rfl) := by
  unfold cellActionComplexForget₂Iso
  exact cellularActionComplexForget₂Iso_inv_f ..

/-- The inverse components of `TauCeti.cellActionComplexForget₂Iso` are the reverse object
transports. -/
@[simp]
theorem cellActionComplexForget₂Iso_inv_f (n : ℕ) :
    (cellActionComplexForget₂Iso C hcell R).inv.f n =
      eqToHom (by
        rw [Functor.mapHomologicalComplex_obj_X, cellularChainComplex_X, cellActionComplex_X]
        rfl) := by
  unfold cellActionComplexForget₂Iso
  exact cellularActionComplexForget₂Iso_hom_f ..

/-- **A cellular action acts monomially on the cellular basis.** If each element of `G` carries
every open `n`-cell of `C` onto an open `n`-cell, then `g` sends the cellular basis vector of an
`n`-cell `i` to a scalar multiple of the cellular basis vector of `g • i`. -/
theorem cellActionRepresentation_cellularChainBasis_eq_smul {n : ℕ} (g : G) (i : cell C n) :
    letI := cellMulAction hcell n
    cellActionRepresentation C hcell R n g (cellularChainBasis C R n i) =
      (cellularChainBasis C R n).repr
        (cellActionRepresentation C hcell R n g (cellularChainBasis C R n i)) (g • i) •
        cellularChainBasis C R n (g • i) := by
  let := cellMulAction hcell n
  rw [cellActionRepresentation_apply]
  exact cellularChainGroupMap_cellularChainBasis_eq_smul C C R
    (isCellular_cellActionSMul C hcell g) (i := i) (i' := g • i) fun y hy ↦ by
    rw [coe_cellActionSMul_apply]
    exact Or.inr (smul_closedCell hcell g i ▸ smul_mem_smul_set hy)

/-- The **augmentation** of the cellular chains of `C` in degree `0`, as a morphism of
representations to the trivial representation: translation by each element of `G` is cellular, and
the cellular augmentation is natural under cellular maps. -/
def cellActionAugmentation :
    Rep.of (cellActionRepresentation C hcell R 0) ⟶ Rep.trivial R G R :=
  Rep.ofHom
    { toLinearMap := (cellularAugmentation C (ModuleCat.of R R)).hom
      isIntertwining' g := LinearMap.ext fun x ↦ by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, Representation.trivial_apply,
          cellActionRepresentation_apply]
        exact ConcreteCategory.congr_hom (cellularChainGroupMap_comp_cellularAugmentation C C
          (isCellular_cellActionSMul C hcell g) (ModuleCat.of R R)) x }

/-- The underlying linear map of `TauCeti.cellActionAugmentation` is the cellular augmentation of
`C`. -/
@[simp]
theorem cellActionAugmentation_hom_toLinearMap :
    (cellActionAugmentation C hcell R).hom.toLinearMap =
      (cellularAugmentation C (ModuleCat.of R R)).hom :=
  (rfl)

/-- The equivariant augmentation vanishes on the boundaries of `1`-cells. -/
@[reassoc (attr := simp)]
theorem cellActionDifferential_comp_cellActionAugmentation :
    cellActionDifferential C hcell R 0 ≫ cellActionAugmentation C hcell R = 0 := by
  refine Rep.hom_ext <| Representation.IntertwiningMap.ext <| LinearMap.ext fun x ↦ ?_
  have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (cellularDifferential_comp_cellularAugmentation C (ModuleCat.of R R))) x
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.comp_apply,
    LinearMap.zero_apply] at h
  simpa [Rep.hom_comp] using h

/-- The **augmentation of the equivariant cellular chain complex**, as a chain map in `Rep R G`
to the trivial representation placed in degree `0`. -/
def cellActionComplexAugmentation :
    cellActionComplex C hcell R ⟶ (ChainComplex.single₀ (Rep.{w} R G)).obj (Rep.trivial R G R) :=
  ((cellActionComplex C hcell R).toSingle₀Equiv _).symm
    ⟨eqToHom (cellActionComplex_X C hcell R 0) ≫ cellActionAugmentation C hcell R, by
      simp [cellActionComplex_d]⟩

/-- In degree `0`, the augmentation of `TauCeti.cellActionComplex` is
`TauCeti.cellActionAugmentation`. -/
@[simp]
theorem cellActionComplexAugmentation_f_zero :
    (cellActionComplexAugmentation C hcell R).f 0 =
      eqToHom (cellActionComplex_X C hcell R 0) ≫ cellActionAugmentation C hcell R :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- **The augmented equivariant cellular chain complex of a contractible CW complex is exact**:
forgetting the action, the augmentation is that of the cellular chain complex of `C`. -/
theorem quasiIso_cellActionComplexAugmentation [ContractibleSpace C] :
    QuasiIso (cellActionComplexAugmentation C hcell R) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ (forget₂ _ (ModuleCat R)),
    quasiIso_iff_of_arrow_mk_iso _ (cellularChainComplexAugmentation C (ModuleCat.of R R)) ?_]
  · exact quasiIso_cellularChainComplexAugmentation C (ModuleCat.of R R)
  · refine Arrow.isoMk' _ _ (cellActionComplexForget₂Iso C hcell R)
      ((HomologicalComplex.singleMapHomologicalComplex _ _ 0).app _) ?_
    have h : (forget₂ (Rep R G) (ModuleCat R)).map (cellActionAugmentation C hcell R) =
        cellularAugmentation C (ModuleCat.of R R) := by
      rw [Rep.forget₂_moduleCat_map, cellActionAugmentation_hom_toLinearMap, ModuleCat.ofHom_hom]
    ext : 1
    simp [-Rep.forget₂_moduleCat_map, eqToHom_map, h]

end Action

section GroupAction

variable {E : Type w} [TopologicalSpace E] [T2Space E] (C : Set E) [CWComplex C]
  {G : Type w} [Group G] [MulAction G E] [ContinuousConstSMul G E]
  (hcell : ∀ (g : G) (n : ℕ) (i : cell C n),
    ∃ j : cell C n, g • openCell n i = openCell n j)
  (R : Type w) [Ring R]

/-- **The monomial scalars of a cellular group action are units.** For any `g : G` and any
`n`-cell `i`, the scalar relating `g • eᵢ` to `e_{g • i}` is a unit in `R`. -/
theorem isUnit_repr_cellActionRepresentation_cellularChainBasis {n : ℕ} (g : G) (i : cell C n) :
    letI := cellMulAction hcell n
    IsUnit ((cellularChainBasis C R n).repr
      (cellActionRepresentation C hcell R n g (cellularChainBasis C R n i)) (g • i)) := by
  let := cellMulAction hcell n
  have h1 := cellActionRepresentation_cellularChainBasis_eq_smul C hcell R g i
  have h2 := cellActionRepresentation_cellularChainBasis_eq_smul C hcell R g⁻¹ (g • i)
  rw [inv_smul_smul] at h2
  exact (cellActionRepresentation C hcell R n).isUnit_of_apply_basis_eq_smul
    (cellularChainBasis C R n) h1 h2

end GroupAction

section Free

variable {E : Type w} [TopologicalSpace E] [T2Space E] (C : Set E) [CWComplex C]
  {G : Type w} [Group G] [MulAction G E] [ContinuousConstSMul G E]
  (hcell : ∀ (g : G) (n : ℕ) (i : cell C n),
    ∃ j : cell C n, g • openCell n i = openCell n j)

section Equiv

variable (R : Type w) [CommRing R] {n : ℕ} {ι : Type w}

/-- The monomial action hypothesis for `Representation.freeEquivOfMonomialBasis`, deduced from
`TauCeti.cellActionRepresentation_cellularChainBasis_eq_smul`. -/
private lemma cellActionRepresentation_monomial (e : (Σ _ : ι, G) ≃ cell C n)
    (he : ∀ (g h : G) (i : ι), letI := cellMulAction hcell n; g • e ⟨i, h⟩ = e ⟨i, g * h⟩)
    (g h : G) (i : ι) :
    ∃ c : R, cellActionRepresentation C hcell R n g (cellularChainBasis C R n (e ⟨i, h⟩)) =
      c • cellularChainBasis C R n (e ⟨i, g * h⟩) := by
  let := cellMulAction hcell n
  exact ⟨_, by
    rw [← he g h i]
    exact cellActionRepresentation_cellularChainBasis_eq_smul C hcell R g (e ⟨i, h⟩)⟩

/-- **Freeness of a cellular chain group from an equivariant indexing of the cells.** If the
`n`-cells of `C` are indexed equivariantly by `Σ _ : ι, G`, then the `n`-th cellular chain group
of `C` is isomorphic in `Rep R G` to `Rep.free R G ι`, sending the generator
`single i (single g 1)` to `g • e_{e ⟨i, 1⟩}`. -/
def cellActionRepIsoFreeOfEquiv (e : (Σ _ : ι, G) ≃ cell C n)
    (he : ∀ (g h : G) (i : ι), letI := cellMulAction hcell n; g • e ⟨i, h⟩ = e ⟨i, g * h⟩) :
    Rep.of (cellActionRepresentation C hcell R n) ≅ Rep.free R G ι :=
  (Rep.mkIso ((cellActionRepresentation C hcell R n).freeEquivOfMonomialBasis
    (cellularChainBasis C R n) e (cellActionRepresentation_monomial C hcell R e he))).symm

/-- The generator `single i (single g r)` of the free representation corresponds to
`r • g • e_{e ⟨i, 1⟩}`. -/
@[simp]
theorem cellActionRepIsoFreeOfEquiv_inv_hom_single (e : (Σ _ : ι, G) ≃ cell C n)
    (he : ∀ (g h : G) (i : ι), letI := cellMulAction hcell n; g • e ⟨i, h⟩ = e ⟨i, g * h⟩)
    (i : ι) (g : G) (r : R) :
    (cellActionRepIsoFreeOfEquiv C hcell R e he).inv.hom
        (Finsupp.single i (MonoidAlgebra.single g r)) =
      r • cellActionRepresentation C hcell R n g (cellularChainBasis C R n (e ⟨i, 1⟩)) := by
  rw [cellActionRepIsoFreeOfEquiv, Iso.symm_inv, Rep.mkIso_hom_hom_apply]
  exact Representation.freeEquivOfMonomialBasis_single (cellActionRepresentation C hcell R n)
    (cellularChainBasis C R n) e (cellActionRepresentation_monomial C hcell R e he) i g r

/-- The translated basis vector `g • e_{e ⟨i, 1⟩}` corresponds to `single i (single g 1)`. This
is not a `simp` lemma: `simp` unfolds `TauCeti.cellularChainBasis` by
`TauCeti.cellularChainBasis_apply` first. -/
theorem cellActionRepIsoFreeOfEquiv_hom_hom_apply_cellularChainBasis (e : (Σ _ : ι, G) ≃ cell C n)
    (he : ∀ (g h : G) (i : ι), letI := cellMulAction hcell n; g • e ⟨i, h⟩ = e ⟨i, g * h⟩)
    (i : ι) (g : G) :
    (cellActionRepIsoFreeOfEquiv C hcell R e he).hom.hom
        (cellActionRepresentation C hcell R n g (cellularChainBasis C R n (e ⟨i, 1⟩))) =
      Finsupp.single i (MonoidAlgebra.single g 1) := by
  rw [← one_smul R (cellActionRepresentation C hcell R n g (cellularChainBasis C R n (e ⟨i, 1⟩))),
    ← cellActionRepIsoFreeOfEquiv_inv_hom_single C hcell R e he, Rep.hom_inv_apply]

/-- The basis vector `e_{e ⟨i, 1⟩}` corresponds to `single i (single 1 1)`. This is not a `simp`
lemma: `simp` unfolds `TauCeti.cellularChainBasis` by `TauCeti.cellularChainBasis_apply` first. -/
theorem cellActionRepIsoFreeOfEquiv_hom_hom_cellularChainBasis (e : (Σ _ : ι, G) ≃ cell C n)
    (he : ∀ (g h : G) (i : ι), letI := cellMulAction hcell n; g • e ⟨i, h⟩ = e ⟨i, g * h⟩)
    (i : ι) :
    (cellActionRepIsoFreeOfEquiv C hcell R e he).hom.hom
        (cellularChainBasis C R n (e ⟨i, 1⟩)) =
      Finsupp.single i (MonoidAlgebra.single 1 1) := by
  simpa only [map_one, one_apply_eq_self] using
    cellActionRepIsoFreeOfEquiv_hom_hom_apply_cellularChainBasis C hcell R e he i 1

end Equiv

/-- **The cellular chains of a free `G`-CW complex are free over `R[G]`**, with basis any choice of
one representative from each `G`-orbit of `n`-cells: given a section `s` of the orbit quotient on
`cell C n`, the `n`-th cellular chain group is isomorphic in `Rep R G` to the free representation
on the orbits of `n`-cells, sending `single o (single g 1)` to `g • e_{s o}`. -/
def cellActionRepIsoFree
    (hfree : ∀ (g : G) (n : ℕ) (i : cell C n), g • openCell n i = openCell n i → g = 1)
    (R : Type w) [CommRing R] {n : ℕ}
    (s : (letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) → cell C n)
    (hs : letI := cellMulAction hcell n; Function.LeftInverse Quotient.mk'' s) :
    letI := cellMulAction hcell n
    Rep.of (cellActionRepresentation C hcell R n) ≅
      Rep.free R G (MulAction.orbitRel.Quotient G (cell C n)) :=
  letI := cellMulAction hcell n
  haveI := isCancelSMul_cell hcell hfree n
  cellActionRepIsoFreeOfEquiv C hcell R
    ((Equiv.sigmaEquivProd _ G).trans
      (MulAction.selfEquivOrbitsQuotientProd' hs IsCancelSMul.stabilizer_eq_bot).symm)
    fun g h o ↦ by
      simp only [Equiv.trans_apply, Equiv.sigmaEquivProd_apply,
        MulAction.selfEquivOrbitsQuotientProd'_symm_apply, mul_smul]

/-- The generator `single o (single g r)` of the free representation corresponds to
`r • g • e_{s o}`. -/
@[simp]
theorem cellActionRepIsoFree_inv_hom_single
    (hfree : ∀ (g : G) (n : ℕ) (i : cell C n), g • openCell n i = openCell n i → g = 1)
    (R : Type w) [CommRing R] {n : ℕ}
    (s : (letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) → cell C n)
    (hs : letI := cellMulAction hcell n; Function.LeftInverse Quotient.mk'' s)
    (o : letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n))
    (g : G) (r : R) :
    (cellActionRepIsoFree C hcell hfree R s hs).inv.hom
        (Finsupp.single o (MonoidAlgebra.single g r)) =
      r • cellActionRepresentation C hcell R n g (cellularChainBasis C R n (s o)) := by
  let := cellMulAction hcell n
  have := isCancelSMul_cell hcell hfree n
  rw [cellActionRepIsoFree, cellActionRepIsoFreeOfEquiv_inv_hom_single]
  simp only [Equiv.trans_apply, Equiv.sigmaEquivProd_apply,
    MulAction.selfEquivOrbitsQuotientProd'_symm_apply, one_smul]

/-- The translated basis vector `g • e_{s o}` corresponds to `single o (single g 1)`. This is not
a `simp` lemma: `simp` unfolds `TauCeti.cellularChainBasis` by `TauCeti.cellularChainBasis_apply`
first. -/
theorem cellActionRepIsoFree_hom_hom_apply_cellularChainBasis
    (hfree : ∀ (g : G) (n : ℕ) (i : cell C n), g • openCell n i = openCell n i → g = 1)
    (R : Type w) [CommRing R] {n : ℕ}
    (s : (letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) → cell C n)
    (hs : letI := cellMulAction hcell n; Function.LeftInverse Quotient.mk'' s)
    (o : letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) (g : G) :
    (cellActionRepIsoFree C hcell hfree R s hs).hom.hom
        (cellActionRepresentation C hcell R n g (cellularChainBasis C R n (s o))) =
      Finsupp.single o (MonoidAlgebra.single g 1) := by
  rw [← one_smul R (cellActionRepresentation C hcell R n g (cellularChainBasis C R n (s o))),
    ← cellActionRepIsoFree_inv_hom_single C hcell hfree R s hs, Rep.hom_inv_apply]

/-- The basis vector `e_{s o}` of the chosen orbit representative corresponds to
`single o (single 1 1)`. This is not a `simp` lemma: `simp` unfolds `TauCeti.cellularChainBasis`
by `TauCeti.cellularChainBasis_apply` first. -/
theorem cellActionRepIsoFree_hom_hom_cellularChainBasis
    (hfree : ∀ (g : G) (n : ℕ) (i : cell C n), g • openCell n i = openCell n i → g = 1)
    (R : Type w) [CommRing R] {n : ℕ}
    (s : (letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) → cell C n)
    (hs : letI := cellMulAction hcell n; Function.LeftInverse Quotient.mk'' s)
    (o : letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) :
    (cellActionRepIsoFree C hcell hfree R s hs).hom.hom (cellularChainBasis C R n (s o)) =
      Finsupp.single o (MonoidAlgebra.single 1 1) := by
  simpa only [map_one, one_apply_eq_self] using
    cellActionRepIsoFree_hom_hom_apply_cellularChainBasis C hcell hfree R s hs o 1

/-- Every term of the cellular chain complex of a free `G`-CW complex is a projective
representation of `G`. -/
theorem projective_cellActionComplex_X
    (hfree : ∀ (g : G) (n : ℕ) (i : cell C n), g • openCell n i = openCell n i → g = 1)
    (R : Type w) [CommRing R] (n : ℕ) :
    Projective ((cellActionComplex C hcell R).X n) := by
  let := cellMulAction hcell n
  rw [cellActionComplex_X]
  exact Projective.of_iso
    (cellActionRepIsoFree C hcell hfree R Quotient.out Quotient.out_eq').symm inferInstance

/-- **The cellular chains of a contractible free `G`-CW complex form a projective resolution** of
the trivial representation of `G` over `R`. -/
def cellActionResolution
    (hfree : ∀ (g : G) (n : ℕ) (i : cell C n), g • openCell n i = openCell n i → g = 1)
    (R : Type w) [CommRing R] [ContractibleSpace C] :
    ProjectiveResolution (Rep.trivial R G R) where
  complex := cellActionComplex C hcell R
  π := cellActionComplexAugmentation C hcell R
  projective := projective_cellActionComplex_X C hcell hfree R
  quasiIso := quasiIso_cellActionComplexAugmentation C hcell R

/-- The complex of `TauCeti.cellActionResolution` is `TauCeti.cellActionComplex`. -/
@[simp]
theorem cellActionResolution_complex
    (hfree : ∀ (g : G) (n : ℕ) (i : cell C n), g • openCell n i = openCell n i → g = 1)
    (R : Type w) [CommRing R] [ContractibleSpace C] :
    (cellActionResolution C hcell hfree R).complex = cellActionComplex C hcell R :=
  (rfl)

-- A public statement cannot unfold the unexposed body of `TauCeti.cellActionResolution`, so the
-- source of its `π` is transported along `cellActionResolution_complex`. Inside the proof the
-- transport reduces to `eqToHom rfl`, which is definitionally the identity.
/-- The augmentation of `TauCeti.cellActionResolution` is
`TauCeti.cellActionComplexAugmentation`. -/
@[simp]
theorem cellActionResolution_π
    (hfree : ∀ (g : G) (n : ℕ) (i : cell C n), g • openCell n i = openCell n i → g = 1)
    (R : Type w) [CommRing R] [ContractibleSpace C] :
    (cellActionResolution C hcell hfree R).π =
      eqToHom (cellActionResolution_complex C hcell hfree R) ≫
        cellActionComplexAugmentation C hcell R :=
  (Category.id_comp _).symm

end Free

section QuotientCovering

variable {E B : Type w} [TopologicalSpace E] [TopologicalSpace B] [T2Space E]
  [CWComplex (univ : Set E)] {p : E → B} {G : Type w} [Group G] [MulAction G E]
  (hp : IsQuotientCoveringMap p G)
  (hcell : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
    ∃ j : cell (univ : Set E) n, g • openCell n i = openCell n j)
  (hfree : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
    g • openCell n i = openCell n i → g = 1)
  (R : Type w) [CommRing R] {n : ℕ}

/-- **The cellular chains of a free `G`-CW complex are free over `R[G]` on any chosen lifts of the
cells of the orbit space.** For a quotient covering map `p : E → B` with the orbit-space CW
structure `IsQuotientCoveringMap.cwComplexQuotient` on `B`, any choice `s b` of an `n`-cell of `E`
projecting onto each `n`-cell `b` of `B` yields an isomorphism in `Rep R G` from the `n`-th
cellular chain group of `E` to `Rep.free R G (cell (univ : Set B) n)`, sending
`single b (single g 1)` to `g • e_{s b}`. -/
def cellActionRepIsoFreeOfQuotientCovering
    (s : (letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) →
      cell (univ : Set E) n)
    (hs : letI := hp.cwComplexQuotient hcell hfree; ∀ b, p '' openCell n (s b) = openCell n b) :
    letI := hp.cwComplexQuotient hcell hfree
    haveI := hp.toContinuousConstSMul
    Rep.of (cellActionRepresentation (univ : Set E) hcell R n) ≅
      Rep.free R G (cell (univ : Set B) n) :=
  letI := hp.cwComplexQuotient hcell hfree
  haveI := hp.toContinuousConstSMul
  cellActionRepIsoFreeOfEquiv (univ : Set E) hcell R
    (hp.sigmaSMulCellEquiv hcell hfree s hs) fun g h b ↦ by
      let := cellMulAction hcell n
      rw [hp.sigmaSMulCellEquiv_apply, hp.sigmaSMulCellEquiv_apply, mul_smul]

/-- The generator `single b (single g r)` of the free representation corresponds to
`r • g • e_{s b}`. -/
@[simp]
theorem cellActionRepIsoFreeOfQuotientCovering_inv_hom_single
    (s : (letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) →
      cell (univ : Set E) n)
    (hs : letI := hp.cwComplexQuotient hcell hfree; ∀ b, p '' openCell n (s b) = openCell n b)
    (b : letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) (g : G) (r : R) :
    haveI := hp.toContinuousConstSMul
    (cellActionRepIsoFreeOfQuotientCovering hp hcell hfree R s hs).inv.hom
        (Finsupp.single b (MonoidAlgebra.single g r)) =
      r • cellActionRepresentation (univ : Set E) hcell R n g
        (cellularChainBasis (univ : Set E) R n (s b)) := by
  let := hp.cwComplexQuotient hcell hfree
  have := hp.toContinuousConstSMul
  let := cellMulAction hcell n
  rw [cellActionRepIsoFreeOfQuotientCovering, cellActionRepIsoFreeOfEquiv_inv_hom_single,
    hp.sigmaSMulCellEquiv_apply, one_smul]

/-- The translated basis vector `g • e_{s b}` corresponds to `single b (single g 1)`. This is not
a `simp` lemma: `simp` unfolds `TauCeti.cellularChainBasis` by `TauCeti.cellularChainBasis_apply`
first. -/
theorem cellActionRepIsoFreeOfQuotientCovering_hom_hom_apply_cellularChainBasis
    (s : (letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) →
      cell (univ : Set E) n)
    (hs : letI := hp.cwComplexQuotient hcell hfree; ∀ b, p '' openCell n (s b) = openCell n b)
    (b : letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) (g : G) :
    haveI := hp.toContinuousConstSMul
    (cellActionRepIsoFreeOfQuotientCovering hp hcell hfree R s hs).hom.hom
        (cellActionRepresentation (univ : Set E) hcell R n g
          (cellularChainBasis (univ : Set E) R n (s b))) =
      Finsupp.single b (MonoidAlgebra.single g 1) := by
  let := hp.cwComplexQuotient hcell hfree
  have := hp.toContinuousConstSMul
  rw [← one_smul R (cellActionRepresentation (univ : Set E) hcell R n g
      (cellularChainBasis (univ : Set E) R n (s b))),
    ← cellActionRepIsoFreeOfQuotientCovering_inv_hom_single hp hcell hfree R s hs,
    Rep.hom_inv_apply]

/-- The basis vector `e_{s b}` of the chosen lift of `b` corresponds to `single b (single 1 1)`.
This is not a `simp` lemma: `simp` unfolds `TauCeti.cellularChainBasis` by
`TauCeti.cellularChainBasis_apply` first. -/
theorem cellActionRepIsoFreeOfQuotientCovering_hom_hom_cellularChainBasis
    (s : (letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) →
      cell (univ : Set E) n)
    (hs : letI := hp.cwComplexQuotient hcell hfree; ∀ b, p '' openCell n (s b) = openCell n b)
    (b : letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) :
    haveI := hp.toContinuousConstSMul
    (cellActionRepIsoFreeOfQuotientCovering hp hcell hfree R s hs).hom.hom
        (cellularChainBasis (univ : Set E) R n (s b)) =
      Finsupp.single b (MonoidAlgebra.single 1 1) := by
  have := hp.toContinuousConstSMul
  simpa only [map_one, one_apply_eq_self] using
    cellActionRepIsoFreeOfQuotientCovering_hom_hom_apply_cellularChainBasis hp hcell hfree R s hs
      b 1

end QuotientCovering

end TauCeti
