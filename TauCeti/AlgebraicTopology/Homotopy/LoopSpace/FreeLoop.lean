/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MappingSpace.HomotopyGroup
public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace
public import TauCeti.Topology.Homotopy.HomotopyGroup.PathComponent
public import TauCeti.Topology.MappingSpace.Fibration

/-!
# Homotopy groups of free loop spaces

Evaluation `𝓛Q = C(S¹, Q) → Q` at `1 ∈ S¹` is a Hurewicz fibration
(`TauCeti.isHurewiczFibration_mappingSpaceEval_one`) with fibre the based loops
`Ω_x Q = Map_*(S¹, Q)` over `x`, and the constant loops are a section. So its exact homotopy
sequence splits (`TauCeti.injective_homotopyGroupMap_basedMap_val`,
`TauCeti.mem_range_homotopyGroupMap_basedMap_val_iff`): for `n ≥ 1` there are split short exact
sequences of groups

`1 → π_{n+1}(Q, x) → π_n(𝓛Q, x) → π_n(Q, x) → 1`,

where the first map is the inclusion of based loops after the loop-space shift
`π_n(Ω_x Q) ≅ π_{n+1}(Q, x)` (`TauCeti.basedMapCircleHomotopyGroupMulEquiv`), the second is
evaluation, and the splitting is given by the constant loops. The same holds for the contractible
free loops `𝓛₀Q`, which contain the path component of every constant loop and hence have the same
positive-dimensional homotopy groups at a constant loop
(`TauCeti.contractibleLoopsHomotopyGroupMulEquiv`).

In degree one this is the extension `1 → π₂(Q, x) → π₁(𝓛₀Q, x) → π₁(Q, x) → 1`, split by the
constant loops: the fundamental group of the contractible free loops keeps both the spherical
classes `π₂(Q)` of its based-loop fibre and the fundamental group of `Q`. This is the evaluation
sequence of the contractible loop space underlying the capped loop cover of Floer theory.

## Main declarations

* `TauCeti.basedMapCircleHomotopyGroupMulEquiv`: the loop-space shift `π_n(Ω_x Q) ≅ π_{n+1}(Q, x)`
  on the based-loop fibre.
* `TauCeti.freeLoopHomotopyGroupHom`: the injection `π_{n+1}(Q, x) → π_n(𝓛Q, x)`, with
  `TauCeti.injective_freeLoopHomotopyGroupHom` and `TauCeti.range_freeLoopHomotopyGroupHom`,
  split by `TauCeti.mapHom_mappingSpaceEval_comp_mapHom_const`, the general splitting of
  evaluation by the constant maps.
* `TauCeti.contractibleLoopsHomotopyGroupMulEquiv`: `π_n(𝓛₀Q, x) ≅ π_n(𝓛Q, x)` for `n ≥ 1`.
* `TauCeti.contractibleLoopHomotopyGroupHom`: the injection `π_{n+1}(Q, x) → π_n(𝓛₀Q, x)`, with
  `TauCeti.injective_contractibleLoopHomotopyGroupHom` and
  `TauCeti.range_contractibleLoopHomotopyGroupHom`, split by
  `TauCeti.mapHom_basepointContractibleLoop_comp_mapHom_constContractibleLoop`.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapters I and IV.8.
* A. Hatcher, *Algebraic Topology*, Section 4.2, the long exact sequence of a fibration.
-/

public section

noncomputable section

open CategoryTheory Topology

universe u

namespace TauCeti

variable {Q : Type u} [TopologicalSpace Q] (x : Q) {N : Type*}

/-! ### Based loops in free loops -/

/-- **The based-loop fibre computes the next homotopy group.** The loop-space shift
`π_{m+1}(Ω_x Q) ≅ π_{m+2}(Q, x)`, on the based loops `Map_*(S¹, Q)` at the constant loop. -/
def basedMapCircleHomotopyGroupMulEquiv (m : ℕ) :
    π_ (m + 1) (BasedMap Circle Q 1 x)
        ⟨ContinuousMap.const Circle x, ContinuousMap.const_apply x 1⟩ ≃*
      π_ (m + 2) Q x :=
  (HomotopyGroup.homeomorphMulEquivOfEq (basedMapCircleOneHomeomorphPath x)
    ((Homeomorph.symm_apply_eq _).1 (basedMapCircleOneHomeomorphPath_symm_refl x)).symm).trans
    (HomotopyGroup.pathLoopSpaceMulEquiv m)

/-- The loop-space shift on the based loops is the map induced by
`TauCeti.basedMapCircleOneHomeomorphPath`, followed by the path loop-space shift
`HomotopyGroup.pathLoopSpaceMulEquiv`. -/
@[simp]
theorem basedMapCircleHomotopyGroupMulEquiv_apply (m : ℕ)
    (a : π_ (m + 1) (BasedMap Circle Q 1 x)
      ⟨ContinuousMap.const Circle x, ContinuousMap.const_apply x 1⟩) :
    basedMapCircleHomotopyGroupMulEquiv x m a =
      HomotopyGroup.pathLoopSpaceMulEquiv m
        (HomotopyGroup.map ⟨basedMapCircleOneHomeomorphPath x,
            (basedMapCircleOneHomeomorphPath x).continuous⟩
          ((Homeomorph.symm_apply_eq _).1 (basedMapCircleOneHomeomorphPath_symm_refl x)).symm
          a) := by
  rw [basedMapCircleHomotopyGroupMulEquiv, MulEquiv.trans_apply,
    HomotopyGroup.homeomorphMulEquivOfEq_apply]

/-! ### Free loops -/

/-- The injection `π_{m+2}(Q, x) → π_{m+1}(𝓛Q, x)` at the constant loop: the inverse of the
loop-space shift `TauCeti.basedMapCircleHomotopyGroupMulEquiv`, followed by the inclusion of the
based loops (`TauCeti.basedMapHomotopyGroupHom`). -/
def freeLoopHomotopyGroupHom (m : ℕ) :
    π_ (m + 2) Q x →* π_ (m + 1) C(Circle, Q) (ContinuousMap.const Circle x) :=
  basedMapHomotopyGroupHom (basedMapCircleHomotopyGroupMulEquiv x m)

/-- On the loop-space shift of a class of based loops, `TauCeti.freeLoopHomotopyGroupHom` is the
map induced by the inclusion of the based loops. Not `@[simp]`: the simp normal form unfolds
the loop-space shift through `TauCeti.basedMapCircleHomotopyGroupMulEquiv_apply`. -/
theorem freeLoopHomotopyGroupHom_basedMapCircleHomotopyGroupMulEquiv (m : ℕ)
    (a : π_ (m + 1) (BasedMap Circle Q 1 x)
      ⟨ContinuousMap.const Circle x, ContinuousMap.const_apply x 1⟩) :
    freeLoopHomotopyGroupHom x m (basedMapCircleHomotopyGroupMulEquiv x m a) =
      HomotopyGroup.map ⟨Subtype.val, continuous_subtype_val⟩ rfl a :=
  basedMapHomotopyGroupHom_apply_mulEquiv _ a

/-- The injection `π_{m+2}(Q, x) → π_{m+1}(𝓛Q, x)` is injective. -/
theorem injective_freeLoopHomotopyGroupHom (m : ℕ) :
    Function.Injective (freeLoopHomotopyGroupHom x m) :=
  injective_basedMapHomotopyGroupHom
    isHurewiczFibration_mappingSpaceEval_one.{0}.mem_serreFibrations _

/-- **Exactness of the free-loop sequence.** The image of `π_{m+2}(Q, x) → π_{m+1}(𝓛Q, x)` is the
kernel of evaluation `π_{m+1}(𝓛Q, x) → π_{m+1}(Q, x)`. -/
theorem range_freeLoopHomotopyGroupHom (m : ℕ) :
    (freeLoopHomotopyGroupHom x m).range =
      (HomotopyGroup.mapHom (N := Fin (m + 1)) (mappingSpaceEval (X := Q) 1)
        (leftInverse_mappingSpaceEval_const 1 x)).ker :=
  range_basedMapHomotopyGroupHom
    isHurewiczFibration_mappingSpaceEval_one.{0}.mem_serreFibrations _

/-! ### Contractible free loops -/

/-- **The contractible free loops have the homotopy groups of the free loops.** In positive
dimension, the inclusion `𝓛₀Q → 𝓛Q` induces an isomorphism of homotopy groups at a constant
loop, since `𝓛₀Q` contains its path component. -/
def contractibleLoopsHomotopyGroupMulEquiv [DecidableEq N] [Nonempty N] :
    HomotopyGroup N (contractibleLoops Q) (constContractibleLoop x) ≃*
      HomotopyGroup N C(Circle, Q) (ContinuousMap.const Circle x) :=
  MulEquiv.ofBijective
    (HomotopyGroup.mapHom ⟨Subtype.val, continuous_subtype_val⟩ (coe_constContractibleLoop x)) <| by
      rw [HomotopyGroup.mapHom, MonoidHom.coe_mk, OneHom.coe_mk]
      refine HomotopyGroup.bijective_map_subtypeVal_of_pathComponent_subset ?_ _
      rw [coe_constContractibleLoop]
      exact pathComponent_const_subset_contractibleLoops x

@[simp]
theorem contractibleLoopsHomotopyGroupMulEquiv_apply [DecidableEq N] [Nonempty N]
    (a : HomotopyGroup N (contractibleLoops Q) (constContractibleLoop x)) :
    contractibleLoopsHomotopyGroupMulEquiv x a =
      HomotopyGroup.map ⟨Subtype.val, continuous_subtype_val⟩ (coe_constContractibleLoop x) a := by
  rw [contractibleLoopsHomotopyGroupMulEquiv, MulEquiv.ofBijective_apply,
    HomotopyGroup.mapHom_apply]

/-- The injection `π_{m+2}(Q, x) → π_{m+1}(𝓛₀Q, x)` at the constant loop: the injection into the
free loops, which lands in the contractible free loops. -/
def contractibleLoopHomotopyGroupHom (m : ℕ) :
    π_ (m + 2) Q x →* π_ (m + 1) (contractibleLoops Q) (constContractibleLoop x) :=
  (contractibleLoopsHomotopyGroupMulEquiv x).symm.toMonoidHom.comp (freeLoopHomotopyGroupHom x m)

/-- Included in the free loops, `TauCeti.contractibleLoopHomotopyGroupHom` is
`TauCeti.freeLoopHomotopyGroupHom`. -/
theorem contractibleLoopsHomotopyGroupMulEquiv_contractibleLoopHomotopyGroupHom (m : ℕ)
    (a : π_ (m + 2) Q x) :
    contractibleLoopsHomotopyGroupMulEquiv x (contractibleLoopHomotopyGroupHom x m a) =
      freeLoopHomotopyGroupHom x m a := by
  rw [contractibleLoopHomotopyGroupHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]

/-- The injection `π_{m+2}(Q, x) → π_{m+1}(𝓛₀Q, x)` is injective. -/
theorem injective_contractibleLoopHomotopyGroupHom (m : ℕ) :
    Function.Injective (contractibleLoopHomotopyGroupHom x m) := by
  rw [contractibleLoopHomotopyGroupHom, MonoidHom.coe_comp]
  exact (MulEquiv.injective _).comp (injective_freeLoopHomotopyGroupHom x m)

/-- On homotopy groups at a constant loop, evaluation of contractible free loops is evaluation of
free loops after the identification `TauCeti.contractibleLoopsHomotopyGroupMulEquiv`. -/
theorem mapHom_basepointContractibleLoop_eq [DecidableEq N] [Nonempty N] :
    HomotopyGroup.mapHom (N := N) (basepointContractibleLoop (Q := Q))
        (basepointContractibleLoop_constContractibleLoop x) =
      (HomotopyGroup.mapHom (mappingSpaceEval (X := Q) 1)
        (leftInverse_mappingSpaceEval_const 1 x)).comp
        (contractibleLoopsHomotopyGroupMulEquiv x).toMonoidHom := by
  ext a
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, contractibleLoopsHomotopyGroupMulEquiv_apply,
    HomotopyGroup.mapHom_apply, HomotopyGroup.mapHom_apply, HomotopyGroup.map_comp_apply]
  exact HomotopyGroup.map_congr (ContinuousMap.ext fun γ ↦ by simp) _ _ a

/-- **Exactness of the contractible free-loop sequence.** The image of
`π_{m+2}(Q, x) → π_{m+1}(𝓛₀Q, x)` is the kernel of evaluation
`π_{m+1}(𝓛₀Q, x) → π_{m+1}(Q, x)`. -/
theorem range_contractibleLoopHomotopyGroupHom (m : ℕ) :
    (contractibleLoopHomotopyGroupHom x m).range =
      (HomotopyGroup.mapHom (N := Fin (m + 1)) (basepointContractibleLoop (Q := Q))
        (basepointContractibleLoop_constContractibleLoop x)).ker := by
  rw [mapHom_basepointContractibleLoop_eq, ← MonoidHom.comap_ker, ← range_freeLoopHomotopyGroupHom,
    contractibleLoopHomotopyGroupHom, MonoidHom.range_comp]
  exact (Subgroup.comap_equiv_eq_map_symm' _ _).symm

/-- **The constant loops split the contractible free-loop sequence.** Evaluation undoes the
constant loops on homotopy groups. -/
theorem mapHom_basepointContractibleLoop_comp_mapHom_constContractibleLoop [DecidableEq N]
    [Nonempty N] :
    (HomotopyGroup.mapHom (basepointContractibleLoop (Q := Q))
        (basepointContractibleLoop_constContractibleLoop x)).comp
        (HomotopyGroup.mapHom (N := N) (x := x) constContractibleLoop rfl) =
      MonoidHom.id (HomotopyGroup N Q x) :=
  MonoidHom.ext fun a ↦ HomotopyGroup.map_map_of_comp_eq_id _ _ rfl _
    basepointContractibleLoop_comp_constContractibleLoop a

end TauCeti
