/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.Basic
public import TauCeti.Topology.MappingSpace.HomotopyGroup
public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace
public import TauCeti.Topology.Homotopy.HomotopyGroup.PathComponent
public import TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence
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

The splitting shows that the constant loops `i_Q : Q → 𝓛₀Q` are injective on every homotopy group,
and onto `π_{m+1}(𝓛₀Q, x)` exactly when `π_{m+2}(Q, x)` vanishes. Since every contractible loop is
joined to a constant loop, `i_Q` is a weak homotopy equivalence exactly when all the homotopy
groups of `Q` of dimension at least two vanish
(`TauCeti.isWeakHomotopyEquivalence_constContractibleLoop_iff`), and for a path-connected `Q`
exactly when `Q` is aspherical
(`TauCeti.isWeakHomotopyEquivalence_constContractibleLoop_iff_isAspherical`). The same holds for
evaluation `𝓛₀Q → Q`, its retraction. For a torus, for instance, the constant loops are a weak
homotopy equivalence; for `S²` they are not, since `π₁(𝓛₀S²)` contains `π₂(S²) = ℤ`.

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
* `TauCeti.isWeakHomotopyEquivalence_constContractibleLoop_iff`,
  `TauCeti.isWeakHomotopyEquivalence_basepointContractibleLoop_iff`: the constant loops
  `Q → 𝓛₀Q`, and evaluation `𝓛₀Q → Q`, are weak homotopy equivalences exactly when the homotopy
  groups of `Q` of dimension at least two vanish at every point.
* `TauCeti.isWeakHomotopyEquivalence_constContractibleLoop_iff_isAspherical`,
  `TauCeti.IsAspherical.isWeakHomotopyEquivalence_constContractibleLoop`: for a path-connected
  `Q`, exactly when `Q` is aspherical.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapters I and IV.8.
* A. Hatcher, *Algebraic Topology*, Section 4.2, the long exact sequence of a fibration.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §5 (the constant loops `i_Q`).
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
      HomotopyGroup.map ⟨Subtype.val, continuous_subtypeVal⟩ rfl a :=
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
  HomotopyGroup.subtypeValMulEquivOfPathComponentSubset
    (by rw [coe_constContractibleLoop]; exact pathComponent_const_subset_contractibleLoops x)
    (coe_constContractibleLoop x)

@[simp]
theorem contractibleLoopsHomotopyGroupMulEquiv_apply [DecidableEq N] [Nonempty N]
    (a : HomotopyGroup N (contractibleLoops Q) (constContractibleLoop x)) :
    contractibleLoopsHomotopyGroupMulEquiv x a =
      HomotopyGroup.map ⟨Subtype.val, continuous_subtypeVal⟩ (coe_constContractibleLoop x) a :=
  HomotopyGroup.subtypeValMulEquivOfPathComponentSubset_apply _ _ a

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

/-! ### When the constant loops are a weak homotopy equivalence -/

/-- **The constant loops are injective on homotopy groups.** Evaluation at the basepoint is a left
inverse of the map `π_N(Q, x) → π_N(𝓛₀Q, x)` induced by the constant loops. -/
theorem injective_map_constContractibleLoop :
    Function.Injective (HomotopyGroup.map (N := N) (constContractibleLoop (Q := Q))
      (rfl : constContractibleLoop x = constContractibleLoop x)) :=
  Function.LeftInverse.injective fun a ↦ HomotopyGroup.map_map_of_comp_eq_id _ _ rfl
    (basepointContractibleLoop_constContractibleLoop x)
    basepointContractibleLoop_comp_constContractibleLoop a

/-- **The constant loops are onto `π_{m+1}(𝓛₀Q, x)` exactly when `π_{m+2}(Q, x)` is trivial.** In
the split exact sequence `1 → π_{m+2}(Q, x) → π_{m+1}(𝓛₀Q, x) → π_{m+1}(Q, x) → 1`, the section
given by the constant loops is onto exactly when the kernel of evaluation, a copy of
`π_{m+2}(Q, x)`, is trivial. -/
theorem surjective_map_constContractibleLoop_iff (m : ℕ) :
    Function.Surjective (HomotopyGroup.map (N := Fin (m + 1)) (constContractibleLoop (Q := Q))
        (rfl : constContractibleLoop x = constContractibleLoop x)) ↔
      Subsingleton (π_ (m + 2) Q x) := by
  set ε := HomotopyGroup.mapHom (N := Fin (m + 1)) (basepointContractibleLoop (Q := Q))
    (basepointContractibleLoop_constContractibleLoop x)
  have hε : Function.LeftInverse ε (HomotopyGroup.map constContractibleLoop rfl) :=
    fun a ↦ DFunLike.congr_fun
      (mapHom_basepointContractibleLoop_comp_mapHom_constContractibleLoop (N := Fin (m + 1)) x) a
  -- A section is onto exactly when its retraction is injective, that is, when the kernel of
  -- evaluation, the image of the injection of `π_{m+2}(Q, x)`, is trivial.
  have hsurj : Function.Surjective (HomotopyGroup.map constContractibleLoop rfl) ↔
      Function.Injective ε :=
    ⟨fun hs ↦ (hε.rightInverse_of_surjective hs).injective,
      fun hi ↦ (hε.rightInverse_of_injective hi).surjective⟩
  rw [hsurj, ← MonoidHom.ker_eq_bot_iff,
    ← range_contractibleLoopHomotopyGroupHom, MonoidHom.range_eq_bot_iff]
  exact ⟨fun h ↦ ⟨fun a b ↦ injective_contractibleLoopHomotopyGroupHom x m <| by
      rw [h, MonoidHom.one_apply, MonoidHom.one_apply]⟩,
    fun _ ↦ MonoidHom.ext fun a ↦ by rw [Subsingleton.elim a 1, map_one, MonoidHom.one_apply]⟩

/-- **The constant loops `Q → 𝓛₀Q` are a weak homotopy equivalence exactly when every homotopy
group of `Q` of dimension at least two vanishes, at every point.** They are a bijection on path
components, since every contractible loop is joined to a constant loop and evaluation is a
retraction, and they are injective on homotopy groups
(`TauCeti.injective_map_constContractibleLoop`). They are onto `π_{m+1}(𝓛₀Q, x)` exactly when
`π_{m+2}(Q, x)` vanishes (`TauCeti.surjective_map_constContractibleLoop_iff`). -/
theorem isWeakHomotopyEquivalence_constContractibleLoop_iff :
    (constContractibleLoop (Q := Q)).IsWeakHomotopyEquivalence ↔
      ∀ (x : Q) (m : ℕ), Subsingleton (π_ (m + 2) Q x) := by
  rw [ContinuousMap.isWeakHomotopyEquivalence_iff_joined]
  refine ⟨fun h x m ↦ (surjective_map_constContractibleLoop_iff x m).1 (h.2.2 m x).2,
    fun h ↦ ⟨fun γ ↦ ?_, fun a b hab ↦ ?_, fun m x ↦
      ⟨injective_map_constContractibleLoop x, (surjective_map_constContractibleLoop_iff x m).2
        (h x m)⟩⟩⟩
  · -- A path from a contractible loop to a constant loop stays among the contractible loops.
    obtain ⟨q, hq⟩ := mem_contractibleLoops_iff.1 γ.property
    have hq' : constContractibleLoop q = ⟨_, const_mem_contractibleLoops q⟩ :=
      Subtype.ext (coe_constContractibleLoop q)
    refine ⟨q, hq' ▸ ?_⟩
    exact ((isPathConnected_pathComponent.joinedIn _ (mem_pathComponent_self _) _
      hq.symm).mono (pathComponent_const_subset_contractibleLoops q)).joined_subtype
  · simpa only [basepointContractibleLoop_constContractibleLoop] using
      hab.map basepointContractibleLoop.continuous

/-- **Evaluation `𝓛₀Q → Q` at the basepoint is a weak homotopy equivalence exactly when every
homotopy group of `Q` of dimension at least two vanishes, at every point.** It is a retraction of
the constant loops, so by two out of three it is a weak homotopy equivalence exactly when they are
(`TauCeti.isWeakHomotopyEquivalence_constContractibleLoop_iff`). -/
theorem isWeakHomotopyEquivalence_basepointContractibleLoop_iff :
    (basepointContractibleLoop (Q := Q)).IsWeakHomotopyEquivalence ↔
      ∀ (x : Q) (m : ℕ), Subsingleton (π_ (m + 2) Q x) := by
  have hid : ((basepointContractibleLoop (Q := Q)).comp
      constContractibleLoop).IsWeakHomotopyEquivalence := by
    rw [basepointContractibleLoop_comp_constContractibleLoop]
    exact .id
  rw [← isWeakHomotopyEquivalence_constContractibleLoop_iff]
  exact ⟨fun h ↦ h.of_postcomp hid, fun h ↦ h.of_precomp hid⟩

/-- **For a path-connected space, the constant loops `Q → 𝓛₀Q` are a weak homotopy equivalence
exactly when `Q` is aspherical.** On a path-connected space the vanishing of the higher homotopy
groups at one point gives it at every point. -/
theorem isWeakHomotopyEquivalence_constContractibleLoop_iff_isAspherical [PathConnectedSpace Q] :
    (constContractibleLoop (Q := Q)).IsWeakHomotopyEquivalence ↔ IsAspherical Q x := by
  rw [isWeakHomotopyEquivalence_constContractibleLoop_iff]
  exact ⟨fun h ↦ .mk inferInstance (h x), fun h y ↦ (h.of_basepoint y).subsingleton_homotopyGroup⟩

/-- **The constant loops of an aspherical space are a weak homotopy equivalence `Q → 𝓛₀Q`.** -/
theorem IsAspherical.isWeakHomotopyEquivalence_constContractibleLoop {x : Q}
    (h : IsAspherical Q x) : (constContractibleLoop (Q := Q)).IsWeakHomotopyEquivalence :=
  haveI := h.pathConnectedSpace
  (isWeakHomotopyEquivalence_constContractibleLoop_iff_isAspherical x).2 h

end TauCeti
