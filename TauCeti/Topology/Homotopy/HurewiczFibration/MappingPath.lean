/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.FiberHomotopyEquiv
public import TauCeti.Topology.Homotopy.MappingPath.Functoriality
public import TauCeti.Topology.Homotopy.MappingPath.LiftingFunction

/-!
# Ordinary fibres and mapping-path fibres of Hurewicz fibrations

A lifting function for `p : E → B` gives a fibre homotopy inverse to the constant-path
inclusion `E → MappingPathSpace p`, over `B`: lift the path from its supplied starting
point and take its endpoint. Thus every ordinary fibre of a Hurewicz fibration is homotopy
equivalent to its mapping-path homotopy fibre, by the constant-path inclusion.

The inverse homotopies are explicit. On the replacement, move the starting point along
the lifted path while retaining the remaining tail of the original path. On `E`, lift
constant paths. The latter lifts need not be constant, so these are ordinary, not based,
homotopy equivalences; no regularity of the lifting function is assumed. All constructions
retain empty fibres and allow the source and base to lie in distinct universes.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter I.7.
-/

public section

open unitInterval

universe u v

namespace TauCeti
namespace LiftingFunction

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
variable {p : C(E, B)} (Λ : LiftingFunction p)

/-- Send a mapping-path replacement point to the endpoint of its lifted path. -/
def mappingPathLiftEndpoint : C(MappingPathSpace p, E) :=
  ⟨fun x ↦ Λ.toContinuousMap x 1, by fun_prop⟩

@[simp]
theorem mappingPathLiftEndpoint_apply (x : MappingPathSpace p) :
    Λ.mappingPathLiftEndpoint x = Λ.lift x.val.1 x.val.2 x.property 1 := by
  rw [lift_def]
  rfl

/-- Taking the endpoint of the lift lies over the endpoint of the original path. -/
@[simp]
theorem comp_mappingPathLiftEndpoint :
    p.comp Λ.mappingPathLiftEndpoint = MappingPathSpace.endpoint p := by
  ext x
  simpa only [ContinuousMap.comp_apply, mappingPathLiftEndpoint_apply,
    MappingPathSpace.endpoint_apply] using Λ.apply_lift x.val.1 x.val.2 x.property 1

/-- Lifting constant paths supplies the inverse homotopy on the original total space,
through maps over the base. The lifts themselves need not be constant. -/
def mappingPathLeftHomotopy :
    ContinuousMap.HomotopyWith (Λ.mappingPathLiftEndpoint.comp (MappingPathSpace.incl p))
      (.id E) (fun f ↦ p.comp f = p) where
  toFun q := Λ.toContinuousMap (MappingPathSpace.incl p q.2) (σ q.1)
  continuous_toFun := by fun_prop
  map_zero_left x := by
    simp [mappingPathLiftEndpoint, ContinuousMap.comp_apply]
  map_one_left x := by simpa using Λ.apply_zero' (MappingPathSpace.incl p x)
  prop' s := by
    ext x
    simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, MappingPathSpace.incl_val,
      ContinuousMap.const_apply] using
      ContinuousMap.congr_fun (Λ.comp_apply' (MappingPathSpace.incl p x)) (σ s)

@[simp]
theorem mappingPathLeftHomotopy_apply (s : I) (x : E) :
    Λ.mappingPathLeftHomotopy (s, x) =
      Λ.lift x (ContinuousMap.const I (p x)) (ContinuousMap.const_apply _ _) (σ s) := by
  rw [lift_def]
  exact congrArg (fun z : MappingPathSpace p ↦ Λ.toContinuousMap z (σ s))
    (Subtype.ext (MappingPathSpace.incl_val p x))

/-- Moving the starting point along its lifted path and retaining the remaining tail
contracts the mapping-path replacement to the endpoint-of-lift inverse, over the base. -/
def mappingPathRightHomotopy :
    ContinuousMap.HomotopyWith ((MappingPathSpace.incl p).comp Λ.mappingPathLiftEndpoint)
      (.id (MappingPathSpace p))
      (fun f ↦ (MappingPathSpace.endpoint p).comp f = MappingPathSpace.endpoint p) where
  toFun q := ⟨(Λ.toContinuousMap q.2 (σ q.1),
    ⟨fun t ↦ q.2.val.2 (Set.Icc.convexComb (σ q.1) 1 t),
      q.2.val.2.continuous.comp (Set.Icc.continuous_convexComb _ _)⟩), by
        simpa using (ContinuousMap.congr_fun (Λ.comp_apply' q.2) (σ q.1)).symm⟩
  continuous_toFun := by
    refine ((by fun_prop : Continuous fun q : I × MappingPathSpace p ↦
      Λ.toContinuousMap q.2 (σ q.1)).prodMk ?_).subtype_mk _
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact ((continuous_snd.comp continuous_fst).subtype_val.snd).eval
      (Set.Icc.continuous_convexComb_prod.comp
        (((continuous_symm.comp (continuous_fst.comp continuous_fst)).prodMk
          (continuous_const.prodMk continuous_snd))))
  map_zero_left x := by
    apply Subtype.ext
    apply Prod.ext
    · simp [mappingPathLiftEndpoint]
    · ext t
      simp [mappingPathLiftEndpoint, ← Λ.comp_apply' x]
  map_one_left x := by
    apply Subtype.ext
    apply Prod.ext
    · simpa using Λ.apply_zero' x
    · ext t
      simp
  prop' s := by
    ext x
    simp

@[simp]
theorem mappingPathRightHomotopy_point (s : I) (x : MappingPathSpace p) :
    (Λ.mappingPathRightHomotopy (s, x)).val.1 =
      Λ.lift x.val.1 x.val.2 x.property (σ s) := by
  rw [lift_def]
  rfl

@[simp]
theorem mappingPathRightHomotopy_path (s t : I) (x : MappingPathSpace p) :
    (Λ.mappingPathRightHomotopy (s, x)).val.2 t =
      x.val.2 (Set.Icc.convexComb (σ s) 1 t) := (rfl)

/-- The constant-path inclusion of a map with a lifting function is a fibre homotopy
equivalence to its mapping-path replacement, with its endpoint map to the same base. -/
def mappingPathFiberHomotopyEquiv :
    FiberHomotopyEquiv p (MappingPathSpace.endpoint p) where
  toFun := MappingPathSpace.incl p
  invFun := Λ.mappingPathLiftEndpoint
  comp_toFun := MappingPathSpace.endpoint_comp_incl p
  comp_invFun := Λ.comp_mappingPathLiftEndpoint
  left_inv := ⟨Λ.mappingPathLeftHomotopy⟩
  right_inv := ⟨Λ.mappingPathRightHomotopy⟩

@[simp]
theorem mappingPathFiberHomotopyEquiv_toFun :
    Λ.mappingPathFiberHomotopyEquiv.toFun = MappingPathSpace.incl p := (rfl)

@[simp]
theorem mappingPathFiberHomotopyEquiv_invFun :
    Λ.mappingPathFiberHomotopyEquiv.invFun = Λ.mappingPathLiftEndpoint := (rfl)

/-- The ordinary fibre of a map with a lifting function is homotopy equivalent to its
mapping-path fibre, by including constant paths and taking endpoints of lifted paths. -/
def fiberHomotopyEquiv (b : B) :
    ContinuousMap.HomotopyEquiv {e // p e = b} (MappingPathFiber p b) :=
  (Λ.mappingPathFiberHomotopyEquiv.fiber b).trans
    (MappingPathFiber.endpointHomeomorph p b).symm.toHomotopyEquiv

@[simp]
theorem fiberHomotopyEquiv_apply_val (b : B) (e : {e // p e = b}) :
    (Λ.fiberHomotopyEquiv b e).val = (e.val, ContinuousMap.const I (p e.val)) := by
  simp [fiberHomotopyEquiv, -Homeomorph.symm_toHomotopyEquiv]

@[simp]
theorem fiberHomotopyEquiv_symm_apply_coe (b : B) (x : MappingPathFiber p b) :
    ((Λ.fiberHomotopyEquiv b).symm x : E) =
      Λ.lift x.val.1 x.val.2 x.property.1 1 := by
  simp [fiberHomotopyEquiv, ← Homeomorph.symm_toHomotopyEquiv, mappingPathLiftEndpoint_apply]

/-- Changing the lifting function does not change the inverse fibre comparison up to
homotopy. The forward comparison is always the same constant-path inclusion. -/
theorem fiberHomotopyEquiv_symm_homotopic (Λ' : LiftingFunction p) (b : B) :
    (Λ.fiberHomotopyEquiv b).invFun.Homotopic (Λ'.fiberHomotopyEquiv b).invFun := by
  let e := Λ.fiberHomotopyEquiv b
  let e' := Λ'.fiberHomotopyEquiv b
  have hf : e.toFun = e'.toFun := by
    ext x : 1
    apply Subtype.ext
    simp [e, e']
  have h₀ := e'.left_inv.comp (ContinuousMap.Homotopic.refl e.invFun)
  have h₁ := (ContinuousMap.Homotopic.refl e'.invFun).comp e.right_inv
  rw [← hf] at h₀
  have h₁' : ((e'.invFun.comp e.toFun).comp e.invFun).Homotopic e'.invFun := by
    simpa only [ContinuousMap.comp_assoc, ContinuousMap.comp_id] using h₁
  simpa only [ContinuousMap.id_comp] using h₀.symm.trans h₁'

/-- The constant-path fibre comparison is natural under commutative squares, even when
the two fibrations have unrelated lifting functions. -/
theorem fiberHomotopyEquiv_natural {E' B' : Type*} [TopologicalSpace E']
    [TopologicalSpace B'] {p' : C(E', B')} (Λ' : LiftingFunction p')
    (a : C(E, E')) (c : C(B, B')) (h : c.comp p = p'.comp a) (b : B)
    (x : {e // p e = b}) :
    MappingPathFiber.map a c h rfl (Λ.fiberHomotopyEquiv b x) =
      Λ'.fiberHomotopyEquiv (c b)
        ⟨a x, (ContinuousMap.congr_fun h x).symm.trans (congrArg c x.property)⟩ := by
  apply Subtype.ext
  simp only [MappingPathFiber.map_val, fiberHomotopyEquiv_apply_val]
  refine Prod.ext rfl ?_
  ext t
  exact ContinuousMap.congr_fun h x

end LiftingFunction

namespace IsHurewiczFibration

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
variable {p : C(E, B)}

/-- A Hurewicz fibration's ordinary fibre is homotopy equivalent to its mapping-path fibre.
The forward map is the canonical constant-path inclusion, independently of the chosen lift. -/
noncomputable def fiberHomotopyEquiv (hp : IsHurewiczFibration.{max u v} p) (b : B) :
    ContinuousMap.HomotopyEquiv {e // p e = b} (MappingPathFiber p b) :=
  hp.nonempty_liftingFunction.some.fiberHomotopyEquiv b

@[simp]
theorem fiberHomotopyEquiv_apply_val (hp : IsHurewiczFibration.{max u v} p) (b : B)
    (e : {e // p e = b}) :
    (hp.fiberHomotopyEquiv b e).val = (e.val, ContinuousMap.const I (p e.val)) :=
  LiftingFunction.fiberHomotopyEquiv_apply_val _ b e

end IsHurewiczFibration
end TauCeti
