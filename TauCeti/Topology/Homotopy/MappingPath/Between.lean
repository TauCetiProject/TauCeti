/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.MappingPath.Fiber
public import TauCeti.Topology.PathSpace.Moore.Comparison.Between

/-!
# Endpoint-constrained mapping-path spaces and unit-interval path spaces

For a point `b : K`, the mapping-path space `MappingPathSpace (ContinuousMap.const Unit b)` of the
constant map at `b` is homeomorphic to the fixed-start unit-interval path space
`{p : C(I, K) // p 0 = b}` by forgetting the redundant `Unit` coordinate
(`TauCeti.mappingPathSpaceConstHomeomorph`), compatibly with final-endpoint evaluation, the
constant-path inclusion, and `TauCeti.mappingPathFiberConstHomeomorphPath` on each endpoint fibre.

More generally, for arbitrary start and endpoint subsets `A, B ⊆ K`, restricting the mapping-path
space `MappingPathSpace (ContinuousMap.subtypeVal A)` of the inclusion `A → K` to paths ending in
`B` defines `TauCeti.MappingPathBetween A B`, which is canonically homeomorphic to the
compact-open subspace `TauCeti.unitPathsBetween A B = {p : C(I, K) | p 0 ∈ A ∧ p 1 ∈ B}`
(`TauCeti.MappingPathBetween.homeomorphUnitPathsBetween`), compatibly with the endpoint projections
to `A × B` and the constant-path sections on `A ∩ B`. Composing with
`TauCeti.MoorePath.fiberHomotopyEquivPathsBetween` yields a fibre homotopy equivalence over `A × B`
between the Moore path space `pathsBetween A B` and `MappingPathBetween A B`
(`TauCeti.MoorePath.fiberHomotopyEquivMappingPathBetween`).

## Main declarations

* `TauCeti.mappingPathSpaceConstHomeomorph`:
  `MappingPathSpace (const Unit b) ≃ₜ {p : C(I, K) // p 0 = b}`.
* `TauCeti.MappingPathBetween A B`: `MappingPathSpace (Subtype.val : A → K)` restricted over `B`,
  with endpoint maps `source`, `target`, `endpoints` and `constantSection`.
* `TauCeti.MappingPathBetween.homeomorphUnitPathsBetween`:
  `MappingPathBetween A B ≃ₜ unitPathsBetween A B`.
* `TauCeti.MoorePath.fiberHomotopyEquivMappingPathBetween`: fibre homotopy equivalence over `A × B`
  from `MoorePath.pathsBetween A B` to `MappingPathBetween A B`.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter I.7 and Chapter III.
-/

public section

open Topology unitInterval

universe u

namespace TauCeti

variable {K : Type u} [TopologicalSpace K]

/-! ### Fixed-start unit-interval paths -/

/-- Forget the redundant `Unit` coordinate to identify `MappingPathSpace (const Unit b)` with the
space of unit-interval paths starting at `b`. -/
def mappingPathSpaceConstHomeomorph (b : K) :
    MappingPathSpace (ContinuousMap.const Unit b) ≃ₜ {p : C(I, K) // p 0 = b} where
  toFun p := ⟨p.val.2, p.property⟩
  invFun γ := ⟨((), γ.val), γ.property⟩
  left_inv _ := Subtype.ext <| Prod.ext (Subsingleton.elim _ _) rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.snd.subtype_mk _
  continuous_invFun := (continuous_const.prodMk continuous_subtype_val).subtype_mk _

@[simp]
theorem coe_mappingPathSpaceConstHomeomorph (b : K)
    (p : MappingPathSpace (ContinuousMap.const Unit b)) :
    (mappingPathSpaceConstHomeomorph b p : C(I, K)) = p.val.2 :=
  (rfl)

@[simp]
theorem mappingPathSpaceConstHomeomorph_symm_val (b : K) (γ : {p : C(I, K) // p 0 = b}) :
    ((mappingPathSpaceConstHomeomorph b).symm γ).val = ((), γ.val) :=
  (rfl)

theorem endpoint_mappingPathSpaceConstHomeomorph_symm (b : K) (γ : {p : C(I, K) // p 0 = b}) :
    MappingPathSpace.endpoint (ContinuousMap.const Unit b)
      ((mappingPathSpaceConstHomeomorph b).symm γ) = γ.val 1 := by
  simp

@[simp]
theorem mappingPathSpaceConstHomeomorph_incl (b : K) :
    mappingPathSpaceConstHomeomorph b
      (MappingPathSpace.incl (ContinuousMap.const Unit b) ()) =
      ⟨ContinuousMap.const I b, rfl⟩ :=
  Subtype.ext (by simp)

/-- On the fibre over a final endpoint `k`, `mappingPathSpaceConstHomeomorph` agrees with
`mappingPathFiberConstHomeomorphPath`. -/
theorem toContinuousMap_mappingPathFiberConstHomeomorphPath (b k : K)
    (p : MappingPathFiber (ContinuousMap.const Unit b) k) :
    (mappingPathFiberConstHomeomorphPath b k p).toContinuousMap =
      (mappingPathSpaceConstHomeomorph b
        (MappingPathFiber.endpointHomeomorph (ContinuousMap.const Unit b) k p).val).val := by
  ext t
  simp

/-! ### Free-start unit-interval paths between subsets -/

/-- The mapping-path space of the inclusion `A → K` restricted to paths whose final endpoint lies
in `B`, with the subspace compact-open topology. -/
abbrev MappingPathBetween (A B : Set K) :=
  {p : MappingPathSpace (ContinuousMap.subtypeVal A) //
    MappingPathSpace.endpoint (ContinuousMap.subtypeVal A) p ∈ B}

namespace MappingPathBetween

variable (A B : Set K)

/-- Starting-point projection `MappingPathBetween A B → A`. -/
def source : C(MappingPathBetween A B, A) :=
  ⟨fun p ↦ p.val.val.1, continuous_subtype_val.subtype_val.fst⟩

@[simp]
theorem source_apply (p : MappingPathBetween A B) : source A B p = p.val.val.1 :=
  (rfl)

/-- Final-endpoint projection `MappingPathBetween A B → B`. -/
def target : C(MappingPathBetween A B, B) :=
  ⟨fun p ↦ ⟨MappingPathSpace.endpoint (ContinuousMap.subtypeVal A) p.val, p.property⟩,
    ((MappingPathSpace.endpoint _).continuous.comp continuous_subtype_val).subtype_mk _⟩

@[simp]
theorem coe_target (p : MappingPathBetween A B) : (target A B p : K) = p.val.val.2 1 := by
  rw [target]
  exact MappingPathSpace.endpoint_apply _ p.val

/-- Combined endpoint map `MappingPathBetween A B → A × B`. -/
def endpoints : C(MappingPathBetween A B, A × B) :=
  (source A B).prodMk (target A B)

-- Keep `endpoints` bundled under `simp` so endpoint-preserving comparison lemmas apply cleanly.
theorem endpoints_apply (p : MappingPathBetween A B) :
    endpoints A B p = (source A B p, target A B p) :=
  (rfl)

/-- The constant-path section `A ∩ B → MappingPathBetween A B`. -/
def constantSection : C(↥(A ∩ B), MappingPathBetween A B) :=
  ⟨fun x ↦ ⟨MappingPathSpace.incl (ContinuousMap.subtypeVal A) ⟨x.val, x.property.1⟩,
      (DFunLike.congr_fun (MappingPathSpace.endpoint_comp_incl (ContinuousMap.subtypeVal A))
        ⟨x.val, x.property.1⟩).symm ▸ x.property.2⟩,
    ((MappingPathSpace.incl _).continuous.comp
      (continuous_subtype_val.subtype_mk _)).subtype_mk _⟩

@[simp]
theorem constantSection_path (x : ↥(A ∩ B)) :
    ((constantSection A B x).val.val.2 : C(I, K)) = ContinuousMap.const I x.val := by
  simp [constantSection]

@[simp]
theorem endpoints_constantSection (x : ↥(A ∩ B)) :
    endpoints A B (constantSection A B x) = (⟨x.val, x.property.1⟩, ⟨x.val, x.property.2⟩) := by
  rw [endpoints_apply]
  exact Prod.ext (Subtype.ext (by simp [constantSection])) (Subtype.ext (by simp))

/-- `MappingPathBetween A B` is canonically homeomorphic to `unitPathsBetween A B`: forgetting the
starting-point coordinate in `A` is a homeomorphism, with continuous inverse `q ↦ (q 0, q)`. -/
def homeomorphUnitPathsBetween : MappingPathBetween A B ≃ₜ unitPathsBetween A B where
  toFun p := ⟨p.val.val.2, (mem_unitPathsBetween A B).2
    ⟨p.val.property.symm ▸ p.val.val.1.property,
      (MappingPathSpace.endpoint_apply (ContinuousMap.subtypeVal A) p.val) ▸ p.property⟩⟩
  invFun q :=
    let hq := (mem_unitPathsBetween A B).1 q.property
    ⟨⟨(⟨q.val 0, hq.1⟩, q.val), rfl⟩,
      (MappingPathSpace.endpoint_apply (ContinuousMap.subtypeVal A)
        ⟨(⟨q.val 0, hq.1⟩, q.val), rfl⟩).symm ▸ hq.2⟩
  left_inv p := Subtype.ext <| Subtype.ext <| Prod.ext (Subtype.ext p.val.property) rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_val.snd.subtype_mk _
  continuous_invFun :=
    (((((continuous_eval_const (0 : I)).comp continuous_subtype_val).subtype_mk _).prodMk
      continuous_subtype_val).subtype_mk _).subtype_mk _

@[simp]
theorem coe_homeomorphUnitPathsBetween (p : MappingPathBetween A B) :
    (homeomorphUnitPathsBetween A B p : C(I, K)) = p.val.val.2 :=
  (rfl)

@[simp]
theorem homeomorphUnitPathsBetween_symm_path (q : unitPathsBetween A B) :
    (((homeomorphUnitPathsBetween A B).symm q).val.val.2 : C(I, K)) = q.val :=
  (rfl)

@[simp]
theorem unitEndpointsBetween_homeomorphUnitPathsBetween (p : MappingPathBetween A B) :
    MoorePath.unitEndpointsBetween A B (homeomorphUnitPathsBetween A B p) = endpoints A B p := by
  simp only [MoorePath.unitEndpointsBetween_apply, endpoints_apply, source_apply,
    coe_homeomorphUnitPathsBetween]
  exact Prod.ext (Subtype.ext p.val.property) (Subtype.ext (coe_target A B p).symm)

@[simp]
theorem endpoints_homeomorphUnitPathsBetween_symm (q : unitPathsBetween A B) :
    endpoints A B ((homeomorphUnitPathsBetween A B).symm q) =
      MoorePath.unitEndpointsBetween A B q := by
  rw [← unitEndpointsBetween_homeomorphUnitPathsBetween A B
    ((homeomorphUnitPathsBetween A B).symm q), Homeomorph.apply_symm_apply]

@[simp]
theorem homeomorphUnitPathsBetween_constantSection (x : ↥(A ∩ B)) :
    homeomorphUnitPathsBetween A B (constantSection A B x) =
      MoorePath.unitConstantBetween A B x :=
  Subtype.ext (by simp)

@[simp]
theorem homeomorphUnitPathsBetween_symm_unitConstantBetween (x : ↥(A ∩ B)) :
    (homeomorphUnitPathsBetween A B).symm (MoorePath.unitConstantBetween A B x) =
      constantSection A B x :=
  (homeomorphUnitPathsBetween A B).injective (by simp)

end MappingPathBetween

namespace MoorePath

/-- Moore paths starting in `A` and ending in `B` are fibre homotopy equivalent over `A × B` to
`MappingPathBetween A B`. -/
noncomputable def fiberHomotopyEquivMappingPathBetween (A B : Set K) :
    FiberHomotopyEquiv (endpointsBetween A B) (MappingPathBetween.endpoints A B) :=
  (fiberHomotopyEquivPathsBetween A B).trans
    (.ofHomeomorph (MappingPathBetween.homeomorphUnitPathsBetween A B).symm
      (ContinuousMap.ext (MappingPathBetween.endpoints_homeomorphUnitPathsBetween_symm A B)))

@[simp]
theorem fiberHomotopyEquivMappingPathBetween_toFun (A B : Set K) :
    (fiberHomotopyEquivMappingPathBetween A B).toFun =
      ((MappingPathBetween.homeomorphUnitPathsBetween A B).symm :
        C(unitPathsBetween A B, MappingPathBetween A B)).comp (toUnitPathBetween A B) := by
  simp [fiberHomotopyEquivMappingPathBetween]

@[simp]
theorem fiberHomotopyEquivMappingPathBetween_invFun (A B : Set K) :
    (fiberHomotopyEquivMappingPathBetween A B).invFun =
      (ofUnitPathBetween A B).comp
        (MappingPathBetween.homeomorphUnitPathsBetween A B :
          C(MappingPathBetween A B, unitPathsBetween A B)) := by
  simp [fiberHomotopyEquivMappingPathBetween]

end MoorePath

end TauCeti
