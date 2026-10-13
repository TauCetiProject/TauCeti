/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.FiberHomotopyEquiv
public import TauCeti.Topology.PathSpace.Moore.Comparison.Basic

/-!
# Comparing path spaces with constrained endpoints

The space of Moore paths starting in `A` and ending in `B` is fibre homotopy equivalent to the
corresponding space of paths on the unit interval, by restricting `MoorePath.toUnitPath`,
`MoorePath.ofUnitPath`, and `MoorePath.unitHomotopy`. Both comparison maps preserve endpoints,
and the homotopy of the Moore composite to the identity fixes each endpoint throughout.
The bundled `MoorePath.fiberHomotopyEquivPathsBetween` compares the endpoint evaluation maps
and restricts to a homotopy equivalence of each endpoint fibre, including when `A` or `B`
is a singleton. No closedness or separation assumptions on the subsets or space are needed.

Constant unit-interval paths become Moore paths of duration one, whereas the Moore constant
section has duration zero. The explicit `constantBetweenHomotopy` compares these sections by
shrinking the duration while keeping the path constant. This supplies compatibility with
constant sections when transporting constructions between the two path models.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter III.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1.
-/

public noncomputable section

open scoped unitInterval ContinuousMap
open Set unitInterval

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] (A B : Set X)

/-- Unit-interval paths starting in `A` and ending in `B`, with the compact-open subspace
topology. -/
def unitPathsBetween : Set C(I, X) := {p | p 0 ∈ A ∧ p 1 ∈ B}

@[simp]
theorem mem_unitPathsBetween {p : C(I, X)} :
    p ∈ unitPathsBetween A B ↔ p 0 ∈ A ∧ p 1 ∈ B :=
  Iff.rfl

namespace MoorePath

/-- Reparametrize an endpoint-constrained Moore path to the unit interval. -/
def toUnitPathBetween : C(pathsBetween A B, unitPathsBetween A B) where
  toFun γ := ⟨γ.val.toUnitPath, (mem_unitPathsBetween A B).mpr
    ⟨(toUnitPath_zero γ.val).symm ▸ (mem_pathsBetween.mp γ.property).1,
      (toUnitPath_one γ.val).symm ▸ (mem_pathsBetween.mp γ.property).2⟩⟩
  continuous_toFun := (continuous_toUnitPath.comp continuous_subtype_val).subtype_mk _

@[simp]
theorem coe_toUnitPathBetween (γ : pathsBetween A B) :
    (toUnitPathBetween A B γ : C(I, X)) = γ.val.toUnitPath :=
  (rfl)

/-- Regard an endpoint-constrained unit-interval path as a Moore path of duration one. -/
def ofUnitPathBetween : C(unitPathsBetween A B, pathsBetween A B) where
  toFun p := ⟨ofUnitPath p.val, mem_pathsBetween.mpr
    ⟨(source_ofUnitPath p.val).symm ▸ ((mem_unitPathsBetween A B).mp p.property).1,
      (target_ofUnitPath p.val).symm ▸ ((mem_unitPathsBetween A B).mp p.property).2⟩⟩
  continuous_toFun := (continuous_ofUnitPath.comp continuous_subtype_val).subtype_mk _

@[simp]
theorem coe_ofUnitPathBetween (p : unitPathsBetween A B) :
    (ofUnitPathBetween A B p : MoorePath X) = ofUnitPath p.val :=
  (rfl)

/-- Endpoint evaluation on the unit-interval path space, taking values in `A × B`. -/
def unitEndpointsBetween : C(unitPathsBetween A B, A × B) where
  toFun p := (⟨p.val 0, ((mem_unitPathsBetween A B).mp p.property).1⟩,
    ⟨p.val 1, ((mem_unitPathsBetween A B).mp p.property).2⟩)
  continuous_toFun :=
    (((continuous_eval_const 0).comp continuous_subtype_val).subtype_mk _).prodMk
      (((continuous_eval_const 1).comp continuous_subtype_val).subtype_mk _)

-- Unfolding this with `simp` would preempt the endpoint-preserving comparison lemmas below.
theorem unitEndpointsBetween_apply (p : unitPathsBetween A B) :
    unitEndpointsBetween A B p =
      (⟨p.val 0, ((mem_unitPathsBetween A B).mp p.property).1⟩,
        ⟨p.val 1, ((mem_unitPathsBetween A B).mp p.property).2⟩) :=
  (rfl)

/-- The forward comparison commutes with endpoint evaluation. -/
@[simp]
theorem unitEndpointsBetween_toUnitPathBetween (γ : pathsBetween A B) :
    unitEndpointsBetween A B (toUnitPathBetween A B γ) = endpointsBetween A B γ := by
  simp only [unitEndpointsBetween_apply, endpointsBetween_apply, coe_toUnitPathBetween]
  exact Prod.ext (Subtype.ext (toUnitPath_zero γ.val)) (Subtype.ext (toUnitPath_one γ.val))

/-- The reverse comparison commutes with endpoint evaluation. -/
@[simp]
theorem endpointsBetween_ofUnitPathBetween (p : unitPathsBetween A B) :
    endpointsBetween A B (ofUnitPathBetween A B p) = unitEndpointsBetween A B p := by
  simp only [endpointsBetween_apply, unitEndpointsBetween_apply, coe_ofUnitPathBetween]
  exact Prod.ext (Subtype.ext (source_ofUnitPath p.val)) (Subtype.ext (target_ofUnitPath p.val))

/-- The unit-interval composite of the comparison maps is the identity. -/
@[simp]
theorem toUnitPathBetween_ofUnitPathBetween (p : unitPathsBetween A B) :
    toUnitPathBetween A B (ofUnitPathBetween A B p) = p :=
  Subtype.ext (toUnitPath_ofUnitPath p.val)

/-- The Moore composite is homotopic to the identity through maps over `A × B`. -/
def unitHomotopyBetween :
    ContinuousMap.HomotopyWith ((ofUnitPathBetween A B).comp (toUnitPathBetween A B))
      (ContinuousMap.id (pathsBetween A B))
      (fun f ↦ ∀ γ, endpointsBetween A B (f γ) = endpointsBetween A B γ) where
  toFun p := ⟨unitHomotopy (p.1, p.2.val), mem_pathsBetween.mpr
    ⟨(unitHomotopy_source p.1 p.2.val).symm ▸ (mem_pathsBetween.mp p.2.property).1,
      (unitHomotopy_target p.1 p.2.val).symm ▸ (mem_pathsBetween.mp p.2.property).2⟩⟩
  continuous_toFun := ((unitHomotopy (X := X)).continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left γ := Subtype.ext (unitHomotopy_apply_zero γ.val)
  map_one_left γ := Subtype.ext (unitHomotopy_apply_one γ.val)
  prop' s γ := by
    simp only [endpointsBetween_apply]
    apply Prod.ext <;> apply Subtype.ext
    · exact unitHomotopy_source s γ.val
    · exact unitHomotopy_target s γ.val

@[simp]
theorem coe_unitHomotopyBetween (s : I) (γ : pathsBetween A B) :
    (unitHomotopyBetween A B (s, γ) : MoorePath X) = unitHomotopy (s, γ.val) :=
  (rfl)

/-- The homotopy fixes both endpoints at every time. -/
@[simp]
theorem endpointsBetween_unitHomotopyBetween (s : I) (γ : pathsBetween A B) :
    endpointsBetween A B (unitHomotopyBetween A B (s, γ)) = endpointsBetween A B γ :=
  (unitHomotopyBetween A B).prop s γ

/-- Moore paths and unit-interval paths between subsets are fibre homotopy equivalent over
endpoint evaluation. Restrict to any endpoint fibre with `FiberHomotopyEquiv.fiber`.
The comparison remains valid for arbitrary subsets, including empty subsets. -/
def fiberHomotopyEquivPathsBetween :
    FiberHomotopyEquiv (endpointsBetween A B) (unitEndpointsBetween A B) where
  toFun := toUnitPathBetween A B
  invFun := ofUnitPathBetween A B
  comp_toFun := ContinuousMap.ext (unitEndpointsBetween_toUnitPathBetween A B)
  comp_invFun := ContinuousMap.ext (endpointsBetween_ofUnitPathBetween A B)
  left_inv := ⟨{
    toHomotopy := (unitHomotopyBetween A B).toHomotopy
    prop' := fun s ↦ ContinuousMap.ext (endpointsBetween_unitHomotopyBetween A B s) }⟩
  right_inv := by
    have h : (toUnitPathBetween A B).comp (ofUnitPathBetween A B) =
        ContinuousMap.id (unitPathsBetween A B) :=
      ContinuousMap.ext (toUnitPathBetween_ofUnitPathBetween A B)
    rw [h]
    exact ContinuousMap.HomotopicWith.refl _ (ContinuousMap.comp_id _)

@[simp]
theorem fiberHomotopyEquivPathsBetween_toFun :
    (fiberHomotopyEquivPathsBetween A B).toFun = toUnitPathBetween A B :=
  (rfl)

@[simp]
theorem fiberHomotopyEquivPathsBetween_invFun :
    (fiberHomotopyEquivPathsBetween A B).invFun = ofUnitPathBetween A B :=
  (rfl)

/-! ### Compatibility with constant sections -/

/-- The constant unit-interval paths, parametrized by `A ∩ B`. -/
def unitConstantBetween : C(↥(A ∩ B), unitPathsBetween A B) where
  toFun x := ⟨ContinuousMap.const I x.val, (mem_unitPathsBetween A B).mpr x.property⟩
  continuous_toFun := (ContinuousMap.continuous_const'.comp continuous_subtype_val).subtype_mk _

@[simp]
theorem coe_unitConstantBetween (x : ↥(A ∩ B)) :
    (unitConstantBetween A B x : C(I, X)) = ContinuousMap.const I x.val :=
  (rfl)

/-- The forward comparison preserves the constant section exactly. -/
@[simp]
theorem toUnitPathBetween_constantBetween (x : ↥(A ∩ B)) :
    toUnitPathBetween A B (constantBetween A B x) = unitConstantBetween A B x := by
  apply Subtype.ext
  simp

/-- Compare the reverse image of the constant section with the Moore constant section by
shrinking its duration from one to zero. All intermediate paths remain constant. -/
def constantBetweenHomotopy :
    ContinuousMap.HomotopyWith ((ofUnitPathBetween A B).comp (unitConstantBetween A B))
      (constantBetween A B)
      (fun f ↦ ∀ x, endpointsBetween A B (f x) = endpointsBetween A B (constantBetween A B x))
    where
  toFun p := ⟨constOfLength p.2.val (1 - toNNReal p.1), mem_pathsBetween.mpr
    ⟨(source_constOfLength p.2.val (1 - toNNReal p.1)).symm ▸ p.2.property.1,
      (target_constOfLength p.2.val (1 - toNNReal p.1)).symm ▸ p.2.property.2⟩⟩
  continuous_toFun := ((continuous_subtype_val.comp continuous_snd).moorePath_constOfLength
    (continuous_const.sub (toNNReal_continuous.comp continuous_fst))).subtype_mk _
  map_zero_left x := Subtype.ext (by simp)
  map_one_left x := Subtype.ext (by simp)
  prop' s x := by
    simp only [endpointsBetween_apply]
    apply Prod.ext <;> apply Subtype.ext <;> simp

@[simp]
theorem coe_constantBetweenHomotopy (s : I) (x : ↥(A ∩ B)) :
    (constantBetweenHomotopy A B (s, x) : MoorePath X) =
      constOfLength x.val (1 - toNNReal s) :=
  (rfl)

end MoorePath

end TauCeti
