/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.MappingPath.Basic
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Fibres of mapping-path replacements

The mapping-path fibre over `k` retains the source point and a path ending at `k`.
Flattening the two endpoint constraints identifies it homeomorphically with the
literal fibre of the replacement's endpoint map. For a constant map from a point,
this is exactly the native compact-open path space, and hence at equal endpoints
the native loop space. In particular, this identification does not presume that
an endpoint fibre is nonempty.

The full based path space is contractible by the shrinking homotopy, whereas its
endpoint fibres generally are not. No fibration or homotopy exact-sequence theorem
is asserted here.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter I.7.
-/

public section

open unitInterval Topology.Homotopy

universe u v

namespace TauCeti

variable {B : Type u} {K : Type v} [TopologicalSpace B] [TopologicalSpace K]

/-- The mapping-path fibre, with the subspace topology from `B × C(I, K)`. -/
abbrev MappingPathFiber (f : C(B, K)) (k : K) :=
  {p : B × C(I, K) // p.2 0 = f p.1 ∧ p.2 1 = k}

namespace MappingPathFiber

variable (f : C(B, K)) (k : K)

/-- Flattening identifies the two-constraint path fibre with the literal endpoint fibre. -/
def endpointHomeomorph :
    MappingPathFiber f k ≃ₜ {p : MappingPathSpace f // MappingPathSpace.endpoint f p = k} where
  toFun p := ⟨⟨p.val, p.property.1⟩,
    (MappingPathSpace.endpoint_apply f ⟨p.val, p.property.1⟩).trans p.property.2⟩
  invFun p := ⟨p.val.val, p.val.property,
    (MappingPathSpace.endpoint_apply f p.val).symm.trans p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_val).subtype_mk _

@[simp]
theorem endpointHomeomorph_val (p : MappingPathFiber f k) :
    (endpointHomeomorph f k p).val.val = p.val := (rfl)

@[simp]
theorem endpointHomeomorph_symm_val
    (p : {p : MappingPathSpace f // MappingPathSpace.endpoint f p = k}) :
    ((endpointHomeomorph f k).symm p).val = p.val.val := (rfl)

end MappingPathFiber

/-- Forget the redundant source point to identify a constant-map fibre with native paths. -/
def mappingPathFiberConstHomeomorphPath (b k : K) :
    MappingPathFiber (ContinuousMap.const Unit b) k ≃ₜ Path b k where
  toFun p := ⟨p.val.2, p.property.1, p.property.2⟩
  invFun γ := ⟨((), γ.toContinuousMap), γ.source, γ.target⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_rng.2 continuous_subtype_val.snd
  continuous_invFun := (continuous_const.prodMk continuous_induced_dom).subtype_mk _

@[simp]
theorem mappingPathFiberConstHomeomorphPath_apply (b k : K)
    (p : MappingPathFiber (ContinuousMap.const Unit b) k) (t : I) :
    mappingPathFiberConstHomeomorphPath b k p t = p.val.2 t := (rfl)

@[simp]
theorem mappingPathFiberConstHomeomorphPath_symm_val (b k : K) (γ : Path b k) :
    ((mappingPathFiberConstHomeomorphPath b k).symm γ).val = ((), γ.toContinuousMap) :=
  (rfl)

/-- At equal endpoints the constant-map fibre is the native compact-open loop space. -/
abbrev mappingPathFiberConstHomeomorphLoopSpace (k : K) :
    MappingPathFiber (ContinuousMap.const Unit k) k ≃ₜ Ω K k :=
  mappingPathFiberConstHomeomorphPath k k

/-- The constant path in the fibre corresponds to the constant native loop. -/
@[simp]
theorem mappingPathFiberConstHomeomorphLoopSpace_refl (k : K) :
    mappingPathFiberConstHomeomorphLoopSpace k
      ⟨((), ContinuousMap.const I k), rfl, rfl⟩ = Path.refl k := by
  apply Path.ext
  rfl

/-- The based path space (without a fixed final endpoint) is contractible. -/
instance (k : K) : ContractibleSpace (MappingPathSpace (ContinuousMap.const Unit k)) :=
  (MappingPathSpace.homotopyEquiv (ContinuousMap.const Unit k)).symm.contractibleSpace

end TauCeti
