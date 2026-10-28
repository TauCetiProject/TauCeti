/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.MappingPath.Basic
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Homotopy.HomotopyGroup
public import TauCeti.Topology.PathSpace.Prepend

/-!
# Fibres of mapping-path replacements

The mapping-path fibre over `k` retains the source point and a path ending at `k`.
Flattening the two endpoint constraints identifies it homeomorphically with the
literal fibre of the replacement's endpoint map. For a constant map from a point,
this is exactly the native compact-open path space, and hence at equal endpoints
the native loop space. In particular, this identification does not presume that
an endpoint fibre is nonempty.

The fibre of the source projection over `b` is the space of paths from `f b` to `k`. It is
empty exactly when `f b` and `k` lie in different path components
(`MappingPathFiber.isEmpty_projFiber_iff`). A chosen reference path `α` from `f b` to `k`
makes it homotopy equivalent to the loop space `Ω K k`
(`MappingPathFiber.projFiberHomotopyEquivLoopSpace`): a path `γ` is sent to the loop
`α.symm.trans γ`, and a loop `ℓ` back to the path `α.trans ℓ`. This equivalence depends on `α`;
no identification independent of a reference path is asserted.

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

/-- The source projection of the mapping-path fibre. -/
def proj : C(MappingPathFiber f k, B) :=
  ⟨fun p ↦ p.val.1, by fun_prop⟩

@[simp]
theorem proj_apply (p : MappingPathFiber f k) : proj f k p = p.val.1 := (rfl)

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

/-- `MappingPathFiber f k` is the base change along `f` of the fixed-end path fibration
`proj (ContinuousMap.id K) k`. -/
def pullbackHomeomorph :
    MappingPathFiber f k ≃ₜ
      {x : B × MappingPathFiber (ContinuousMap.id K) k // f x.1 = proj (.id K) k x.2} where
  toFun p := ⟨(p.val.1, ⟨(f p.val.1, p.val.2), p.property⟩), rfl⟩
  invFun x := ⟨(x.val.1, x.val.2.val.2),
    x.val.2.property.1.trans x.property.symm, x.val.2.property.2⟩
  left_inv _ := rfl
  right_inv x := Subtype.ext (Prod.ext rfl (Subtype.ext (Prod.ext x.property rfl)))
  continuous_toFun := by
    refine (continuous_subtype_val.fst.prodMk ?_).subtype_mk _
    exact ((f.continuous.comp continuous_subtype_val.fst).prodMk
      continuous_subtype_val.snd).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.fst.prodMk
      (continuous_subtype_val.comp continuous_subtype_val.snd).snd).subtype_mk _

@[simp]
theorem pullbackHomeomorph_val_fst (p : MappingPathFiber f k) :
    (pullbackHomeomorph f k p).val.1 = p.val.1 := (rfl)

@[simp]
theorem pullbackHomeomorph_val_snd_val (p : MappingPathFiber f k) :
    (pullbackHomeomorph f k p).val.2.val = (f p.val.1, p.val.2) := (rfl)

@[simp]
theorem pullbackHomeomorph_symm_val
    (x : {x : B × MappingPathFiber (ContinuousMap.id K) k // f x.1 = proj (.id K) k x.2}) :
    ((pullbackHomeomorph f k).symm x).val = (x.val.1, x.val.2.val.2) := (rfl)

/-- The base-change identification lies over `B`. -/
theorem proj_eq_comp_pullbackHomeomorph :
    ⇑(proj f k) = (fun x ↦ x.val.1) ∘ pullbackHomeomorph f k :=
  (rfl)

/-- The fibre of the source projection over `b` is the native space of paths from `f b`
to `k`. -/
def projFiberHomeomorphPath (b : B) :
    {p : MappingPathFiber f k // proj f k p = b} ≃ₜ Path (f b) k where
  toFun p := ⟨p.val.val.2, p.val.property.1.trans (congrArg f p.property), p.val.property.2⟩
  invFun γ := ⟨⟨(b, γ.toContinuousMap), γ.source, γ.target⟩, rfl⟩
  left_inv p := Subtype.ext (Subtype.ext (Prod.ext p.property.symm rfl))
  right_inv _ := rfl
  continuous_toFun :=
    continuous_induced_rng.2 (continuous_subtype_val.comp continuous_subtype_val).snd
  continuous_invFun := ((continuous_const.prodMk continuous_induced_dom).subtype_mk _).subtype_mk _

@[simp]
theorem projFiberHomeomorphPath_apply (b : B) (p : {p : MappingPathFiber f k // proj f k p = b})
    (t : I) : projFiberHomeomorphPath f k b p t = p.val.val.2 t := (rfl)

@[simp]
theorem projFiberHomeomorphPath_symm_val_val (b : B) (γ : Path (f b) k) :
    ((projFiberHomeomorphPath f k b).symm γ).val.val = (b, γ.toContinuousMap) := (rfl)

/-- The fibre of the source projection over `b` is nonempty exactly when `f b` is joined to `k`
by a path. -/
theorem nonempty_projFiber_iff (b : B) :
    Nonempty {p : MappingPathFiber f k // proj f k p = b} ↔ Joined (f b) k :=
  (projFiberHomeomorphPath f k b).toEquiv.nonempty_congr

/-- The fibre of the source projection over `b` is empty exactly when `f b` and `k` lie in
different path components. -/
theorem isEmpty_projFiber_iff (b : B) :
    IsEmpty {p : MappingPathFiber f k // proj f k p = b} ↔ ¬Joined (f b) k := by
  rw [← nonempty_projFiber_iff, not_nonempty_iff]

/-- A reference path `α` from `f b` to `k` makes the fibre of the source projection over `b`
homotopy equivalent to the loop space `Ω K k`. A path `γ` from `f b` to `k` is sent to the loop
`α.symm.trans γ`, and the homotopy inverse sends a loop `ℓ` to the path `α.trans ℓ`. -/
noncomputable def projFiberHomotopyEquivLoopSpace (b : B) (α : Path (f b) k) :
    ContinuousMap.HomotopyEquiv {p : MappingPathFiber f k // proj f k p = b} (Ω K k) :=
  (projFiberHomeomorphPath f k b).toHomotopyEquiv.trans (Path.prependHomotopyEquiv α k).symm

@[simp]
theorem projFiberHomotopyEquivLoopSpace_apply (b : B) (α : Path (f b) k)
    (p : {p : MappingPathFiber f k // proj f k p = b}) :
    projFiberHomotopyEquivLoopSpace f k b α p = α.symm.trans (projFiberHomeomorphPath f k b p) :=
  Path.prependHomotopyEquiv_symm_apply α _

@[simp]
theorem projFiberHomotopyEquivLoopSpace_symm_apply (b : B) (α : Path (f b) k) (ℓ : Ω K k) :
    (projFiberHomotopyEquivLoopSpace f k b α).symm ℓ =
      (projFiberHomeomorphPath f k b).symm (α.trans ℓ) :=
  -- Mathlib's `HomotopyEquiv.trans` and `symm` unfold to the composite of the inverse maps.
  congrArg (projFiberHomeomorphPath f k b).symm (Path.prependHomotopyEquiv_apply α ℓ)

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
