/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Permutation
public import TauCeti.RepresentationTheory.FreeOfBasis
public import TauCeti.Topology.CWComplex.Classical.Covering
public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# The cellular chains of a lifted CW structure are free over the group ring

Let `p : E → B` be the quotient covering map of a free action of a group `G` on `E`
(`IsQuotientCoveringMap p G`), and let `C` be a CW complex in the Hausdorff space `B`. Then
`p ⁻¹' C` carries the lifted CW structure `TauCeti.cwComplexPreimage`, and `G` permutes its
cells freely, with one orbit over each cell of `C`, translating characteristic maps
(`TauCeti.map_smul_cellPreimage`).

Translation by `g` is therefore cellular (`TauCeti.isCellular_preimageSMul`) and sends the
cellular basis vector of a lifted cell to that of its translate. With coefficients in a commutative
ring `R`, this makes each cellular chain group of `p ⁻¹' C`, the relative homology of consecutive
skeleta of `p ⁻¹' C` with coefficients in `R`, a representation of `G`
(`TauCeti.cellularChainRepresentation`), on which `g` acts by the chain map of the translation.
The cellular differentials are `G`-equivariant, so the cellular chain complex of `p ⁻¹' C` is a
chain complex of representations (`TauCeti.cellularChainComplexRep`), whose underlying chain
complex of `R`-modules is the cellular chain complex of `p ⁻¹' C`
(`TauCeti.cellularChainComplexRepForget₂Iso`).

Each of its terms is free over `R[G]`, with basis one chosen lift of each cell of `C`
(`TauCeti.cellularChainRepIsoFree`): for a choice `s` of lifts, the basis vector of the lifted cell
`g • s i` corresponds to the generator `single i (single g 1)` of `Rep.free R G (cell C n)`.

## Main definitions

* `TauCeti.cellularChainRepresentation`: the action of `G` on a cellular chain group of the lift.
* `TauCeti.cellularChainComplexRep`: the cellular chain complex of the lift, as a chain complex
  of representations of `G`.
* `TauCeti.cellularChainComplexRepForget₂Iso`: forgetting the action, it is the cellular chain
  complex of the lift.
* `TauCeti.cellularChainRepIsoFree`: each of its terms is the free representation on the cells
  of `C`.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section I.4, free `G`-complexes
  and their cellular chains.
* T. tom Dieck, *Transformation Groups*, de Gruyter, 1987, Section II.1.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex

universe w

namespace TauCeti

variable {E B : Type w} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}
  (C : Set B) {G : Type w} [Group G] [MulAction G E] (hG : IsQuotientCoveringMap p G)

variable [T2Space B] [CWComplex C] (R : Type w) [CommRing R]

/-- Translation by `g` sends the cellular basis vector of a lifted cell to that of its translate;
this is `TauCeti.cellularChainRepresentation_cellularChainBasis` before the representation is
assembled. -/
private lemma cellularChainGroupMap_preimageSMul_cellularChainBasis (g : G) {n : ℕ}
    (c : letI := cwComplexPreimage C hG.isCoveringMap; cell (p ⁻¹' C) n) :
    letI := cwComplexPreimage C hG.isCoveringMap
    letI := cellPreimageMulAction C hG n
    haveI := hG.isCoveringMap.t2Space
    cellularChainGroupMap _ _ (isCellular_preimageSMul C hG g) (ModuleCat.of R R) n
        (cellularChainBasis (p ⁻¹' C) R n c) =
      cellularChainBasis (p ⁻¹' C) R n (g • c) := by
  let := cwComplexPreimage C hG.isCoveringMap
  let := cellPreimageMulAction C hG n
  have := hG.isCoveringMap.t2Space
  exact cellularChainGroupMap_cellularChainBasis _ _ _ R fun x _ _ ↦
    (coe_preimageSMul_apply C hG g _).trans (map_smul_cellPreimage C hG g c x).symm

/-- The action of `G` on the `n`-th cellular chain group of the lift `p ⁻¹' C` of `C`, in which
`g` acts by the chain map of translation by `g`. -/
def cellularChainRepresentation (n : ℕ) :
    letI := cwComplexPreimage C hG.isCoveringMap
    haveI := hG.isCoveringMap.t2Space
    Representation R G (cellularChainGroup (p ⁻¹' C) (ModuleCat.of R R) n : ModuleCat R) :=
  letI := cwComplexPreimage C hG.isCoveringMap
  letI := cellPreimageMulAction C hG n
  haveI := hG.isCoveringMap.t2Space
  { toFun g := (cellularChainGroupMap _ _ (isCellular_preimageSMul C hG g)
      (ModuleCat.of R R) n).hom
    map_one' := (cellularChainBasis (p ⁻¹' C) R n).ext fun c ↦ by
      simp only [cellularChainGroupMap_preimageSMul_cellularChainBasis, one_smul,
        Module.End.one_apply]
    map_mul' g h := (cellularChainBasis (p ⁻¹' C) R n).ext fun c ↦ by
      simp only [Module.End.mul_apply, cellularChainGroupMap_preimageSMul_cellularChainBasis,
        mul_smul] }

/-- An element `g` acts on the cellular chains of the lift by the chain map of translation by
`g`. -/
@[simp]
lemma cellularChainRepresentation_apply (n : ℕ) (g : G) :
    letI := cwComplexPreimage C hG.isCoveringMap
    haveI := hG.isCoveringMap.t2Space
    cellularChainRepresentation C hG R n g =
      (cellularChainGroupMap _ _ (isCellular_preimageSMul C hG g) (ModuleCat.of R R) n).hom :=
  (rfl)

/-- An element `g` sends the cellular basis vector of a lifted cell to that of its translate.
This is not a `simp` lemma: `simp` unfolds `TauCeti.cellularChainBasis` by
`TauCeti.cellularChainBasis_apply` first. -/
lemma cellularChainRepresentation_cellularChainBasis {n : ℕ} (g : G)
    (c : letI := cwComplexPreimage C hG.isCoveringMap; cell (p ⁻¹' C) n) :
    letI := cwComplexPreimage C hG.isCoveringMap
    letI := cellPreimageMulAction C hG n
    haveI := hG.isCoveringMap.t2Space
    cellularChainRepresentation C hG R n g (cellularChainBasis (p ⁻¹' C) R n c) =
      cellularChainBasis (p ⁻¹' C) R n (g • c) :=
  cellularChainGroupMap_preimageSMul_cellularChainBasis C hG R g c

/-- The cellular differential of the lift is `G`-equivariant, so it is a morphism of
representations. -/
def cellularDifferentialRep (n : ℕ) :
    Rep.of (cellularChainRepresentation C hG R (n + 1)) ⟶
      Rep.of (cellularChainRepresentation C hG R n) :=
  letI := cwComplexPreimage C hG.isCoveringMap
  haveI := hG.isCoveringMap.t2Space
  Rep.ofHom
    { toLinearMap := (cellularDifferential (p ⁻¹' C) (ModuleCat.of R R) n).hom
      isIntertwining' g := by
        rw [cellularChainRepresentation_apply, cellularChainRepresentation_apply]
        simpa only [ModuleCat.hom_comp] using congrArg ModuleCat.Hom.hom
          (cellularChainGroupMap_comp_cellularDifferential _ _ (isCellular_preimageSMul C hG g)
            (ModuleCat.of R R) n) }

/-- The underlying linear map of `TauCeti.cellularDifferentialRep` is the cellular
differential. -/
@[simp]
lemma cellularDifferentialRep_hom_toLinearMap (n : ℕ) :
    letI := cwComplexPreimage C hG.isCoveringMap
    haveI := hG.isCoveringMap.t2Space
    (cellularDifferentialRep C hG R n).hom.toLinearMap =
      (cellularDifferential (p ⁻¹' C) (ModuleCat.of R R) n).hom :=
  (rfl)

/-- **The cellular chain complex of the lift is a chain complex of representations of `G`**: its
terms are the representations `TauCeti.cellularChainRepresentation` and its differentials are the
cellular differentials. -/
def cellularChainComplexRep : ChainComplex (Rep.{w} R G) ℕ :=
  letI := cwComplexPreimage C hG.isCoveringMap
  haveI := hG.isCoveringMap.t2Space
  ChainComplex.of (fun n ↦ Rep.of (cellularChainRepresentation C hG R n))
    (cellularDifferentialRep C hG R) fun n ↦ by
      ext x
      exact ConcreteCategory.congr_hom
        (cellularDifferential_comp_cellularDifferential (p ⁻¹' C) (ModuleCat.of R R) n) x

/-- The objects of `TauCeti.cellularChainComplexRep` are the representations
`TauCeti.cellularChainRepresentation`. -/
@[simp]
lemma cellularChainComplexRep_X (n : ℕ) :
    (cellularChainComplexRep C hG R).X n = Rep.of (cellularChainRepresentation C hG R n) :=
  (rfl)

/-- The differentials of `TauCeti.cellularChainComplexRep` are the equivariant cellular
differentials, transported across `TauCeti.cellularChainComplexRep_X`. -/
@[simp]
lemma cellularChainComplexRep_d (n : ℕ) :
    (cellularChainComplexRep C hG R).d (n + 1) n =
      eqToHom (cellularChainComplexRep_X C hG R (n + 1)) ≫ cellularDifferentialRep C hG R n ≫
        eqToHom (cellularChainComplexRep_X C hG R n).symm := by
  -- The object equations hold by definition, so both transports are identities; the body of
  -- `cellularChainComplexRep` is not exposed, so reducing its differential needs an `unfold`.
  have h : ∀ m : ℕ, cellularChainComplexRep_X C hG R m = rfl := fun _ ↦ Subsingleton.elim _ _
  rw [h (n + 1), h n]
  unfold cellularChainComplexRep
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact ChainComplex.of_d _ _ n

/-- **Forgetting the action of `G`, `TauCeti.cellularChainComplexRep` is the cellular chain
complex of the lift**: the components of this isomorphism are transports along equalities of
objects that hold by definition. -/
def cellularChainComplexRepForget₂Iso :
    letI := cwComplexPreimage C hG.isCoveringMap
    haveI := hG.isCoveringMap.t2Space
    ((forget₂ (Rep.{w} R G) (ModuleCat.{w} R)).mapHomologicalComplex _).obj
        (cellularChainComplexRep C hG R) ≅
      cellularChainComplex (p ⁻¹' C) (ModuleCat.of R R) :=
  letI := cwComplexPreimage C hG.isCoveringMap
  haveI := hG.isCoveringMap.t2Space
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ eqToIso (by
      rw [Functor.mapHomologicalComplex_obj_X, cellularChainComplex_X, cellularChainComplexRep_X]
      rfl))
    fun i j (h : j + 1 = i) ↦ by
      subst h
      rw [Functor.mapHomologicalComplex_obj_d, cellularChainComplexRep_d, cellularChainComplex_d]
      simp only [eqToIso.hom, eqToHom_trans_assoc]
      -- The remaining transports are between objects that are the cellular chain groups by
      -- definition, so both sides are the cellular differential.
      rfl

section Free

variable {n : ℕ}
  (s : cell C n → letI := cwComplexPreimage C hG.isCoveringMap; cell (p ⁻¹' C) n)
  (hs : ∀ i, (cellPreimageEquiv C hG.isCoveringMap n (s i)).1 = i)

/-- Translation by `g` sends the cellular basis vector of the lifted cell `h • s i` to that of
`(g * h) • s i`. -/
private lemma cellularChainRepresentation_sigmaSMulLiftEquiv (g h : G) (i : cell C n) :
    letI := cwComplexPreimage C hG.isCoveringMap
    letI := cellPreimageMulAction C hG n
    haveI := hG.isCoveringMap.t2Space
    cellularChainRepresentation C hG R n g
        (cellularChainBasis (p ⁻¹' C) R n (sigmaSMulLiftEquiv C hG s hs ⟨i, h⟩)) =
      cellularChainBasis (p ⁻¹' C) R n (sigmaSMulLiftEquiv C hG s hs ⟨i, g * h⟩) := by
  let := cwComplexPreimage C hG.isCoveringMap
  have := hG.isCoveringMap.t2Space
  simp only [sigmaSMulLiftEquiv_apply, cellularChainRepresentation_cellularChainBasis, mul_smul]

/-- The isomorphism of `TauCeti.cellularChainRepIsoFree`, as an equivalence of
representations from the free representation. -/
private def freeEquivCellularChainRepresentation :
    (Representation.free R G (cell C n)).Equiv (cellularChainRepresentation C hG R n) :=
  letI := cwComplexPreimage C hG.isCoveringMap
  letI := cellPreimageMulAction C hG n
  haveI := hG.isCoveringMap.t2Space
  (cellularChainRepresentation C hG R n).freeEquivOfBasis (cellularChainBasis (p ⁻¹' C) R n)
    (sigmaSMulLiftEquiv C hG s hs) (cellularChainRepresentation_sigmaSMulLiftEquiv C hG R s hs)

/-- **The cellular chains of the lift are free over the group ring**, with basis one chosen lift
of each cell of `C`: given a lift `s i` of each `n`-cell `i` of `C`, the `n`-th cellular chain
group of `p ⁻¹' C` is isomorphic, as a representation of `G`, to the free representation on the
`n`-cells of `C`, the generator `single i (single g 1)` corresponding to the cellular basis vector
of the lifted cell `g • s i`. -/
def cellularChainRepIsoFree :
    Rep.of (cellularChainRepresentation C hG R n) ≅ Rep.free R G (cell C n) :=
  (Rep.mkIso (freeEquivCellularChainRepresentation C hG R s hs)).symm

/-- The generator `single i (single g 1)` of the free representation corresponds to the cellular
basis vector of the lifted cell `g • s i`. -/
@[simp]
lemma cellularChainRepIsoFree_inv_hom_single (i : cell C n) (g : G) :
    letI := cwComplexPreimage C hG.isCoveringMap
    letI := cellPreimageMulAction C hG n
    haveI := hG.isCoveringMap.t2Space
    (cellularChainRepIsoFree C hG R s hs).inv.hom (Finsupp.single i (MonoidAlgebra.single g 1)) =
      cellularChainBasis (p ⁻¹' C) R n (g • s i) := by
  let := cwComplexPreimage C hG.isCoveringMap
  have := hG.isCoveringMap.t2Space
  let := cellPreimageMulAction C hG n
  rw [cellularChainRepIsoFree, Iso.symm_inv, Rep.mkIso_hom_hom_apply]
  exact (Representation.freeEquivOfBasis_single (cellularChainRepresentation C hG R n)
    (cellularChainBasis (p ⁻¹' C) R n) (sigmaSMulLiftEquiv C hG s hs)
    (cellularChainRepresentation_sigmaSMulLiftEquiv C hG R s hs) i g 1).trans
      (by rw [one_smul, sigmaSMulLiftEquiv_apply])

/-- The cellular basis vector of the lifted cell `g • s i` corresponds to the generator
`single i (single g 1)` of the free representation. This is not a `simp` lemma: `simp` unfolds
`TauCeti.cellularChainBasis` by `TauCeti.cellularChainBasis_apply` first. -/
lemma cellularChainRepIsoFree_hom_hom_cellularChainBasis (i : cell C n) (g : G) :
    letI := cwComplexPreimage C hG.isCoveringMap
    letI := cellPreimageMulAction C hG n
    haveI := hG.isCoveringMap.t2Space
    (cellularChainRepIsoFree C hG R s hs).hom.hom (cellularChainBasis (p ⁻¹' C) R n (g • s i)) =
      Finsupp.single i (MonoidAlgebra.single g 1) := by
  rw [← cellularChainRepIsoFree_inv_hom_single C hG R s hs, Rep.hom_inv_apply]

end Free

end TauCeti
