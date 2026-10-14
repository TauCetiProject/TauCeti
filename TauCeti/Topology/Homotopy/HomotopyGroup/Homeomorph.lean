/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyGroup.Map

/-!
# Higher homotopy groups are homeomorphism invariants

The functoriality API in `TauCeti.Topology.Homotopy.HomotopyGroup.Map` records the map
`HomotopyGroup.map` on homotopy classes induced by a based continuous map (a monoid
homomorphism `HomotopyGroup.mapHom` in positive dimensions), but it stops short of packaging a
homeomorphism as an *isomorphism* of homotopy groups. This file supplies that: a homeomorphism
`e : X ≃ₜ Y` induces an equivalence `π_N(X, x) ≃ π_N(Y, e x)` in every dimension, and a group
isomorphism `π_N(X, x) ≃* π_N(Y, e x)` in positive dimensions, and more generally the versions
sending `x` to any `y` with `e x = y`.

The forward and inverse application lemmas characterize these equivalences as
`HomotopyGroup.map` for `e` and `e.symm`, respectively.

The file also records a homeomorphism between spaces of generalized loops themselves:
Mathlib's bijection `genLoopEquivOfUnique` between the generalized loops indexed by a singleton
and the loop space `Ω X x` is continuous both ways for the compact-open topologies.

Transporting a homotopy-group computation across a homeomorphism is the dimension-`N` analogue of
`TauCeti.FundamentalGroup.homeomorphMulEquiv`.

## Main declarations

* `HomotopyGroup.homeomorphEquivOfEq`: `π_N(X, x) ≃ π_N(Y, y)` from `e : X ≃ₜ Y` with
  `e x = y`.
* `HomotopyGroup.homeomorphEquiv`: `π_N(X, x) ≃ π_N(Y, e x)`.
* `HomotopyGroup.homeomorphMulEquivOfEq`: the positive-dimensional group isomorphism
  `π_N(X, x) ≃* π_N(Y, y)`.
* `HomotopyGroup.homeomorphMulEquiv`: `π_N(X, x) ≃* π_N(Y, e x)`.
* `GenLoop.homeomorphOfUnique`: `Ω^ N X x ≃ₜ Ω X x` for `N` a singleton.
* `Homeomorph.genLoopHomeomorph`: `Ω^ N X x ≃ₜ Ω^ N Y y` from `e : X ≃ₜ Y` with `e x = y`.
-/

public section

open scoped unitInterval Topology Topology.Homotopy

namespace GenLoop

variable {N X : Type*} [TopologicalSpace X] {x : X}

/-- Mathlib's bijection `genLoopEquivOfUnique` between the one-dimensional generalized loops at
`x` and the loop space `Ω X x`, upgraded to a homeomorphism for the compact-open topologies. -/
def homeomorphOfUnique (N : Type*) [Unique N] : Ω^ N X x ≃ₜ Ω X x where
  toEquiv := genLoopEquivOfUnique N
  continuous_toFun := Path.continuous_uncurry_iff.1 <|
    continuous_eval.comp (continuous_fst.prodMk (continuous_pi fun _ => continuous_snd))
  continuous_invFun := by
    refine Continuous.subtype_mk (ContinuousMap.continuous_of_continuous_uncurry _ ?_) _
    exact continuous_eval.comp
      (continuous_fst.prodMk ((continuous_apply default).comp continuous_snd))

@[simp]
theorem homeomorphOfUnique_apply (N : Type*) [Unique N] (p : Ω^ N X x) (t : I) :
    homeomorphOfUnique N p t = p fun _ => t :=
  by rw [homeomorphOfUnique.eq_1]; rfl

@[simp]
theorem homeomorphOfUnique_symm_apply (N : Type*) [Unique N] (γ : Ω X x) (t : I^N) :
    (homeomorphOfUnique N).symm γ t = γ (t default) :=
  by rw [homeomorphOfUnique.eq_1]; rfl

/-- The homeomorphism of `GenLoop.homeomorphOfUnique` is based: it carries the constant
generalized loop to the constant path. -/
@[simp]
theorem homeomorphOfUnique_const (N : Type*) [Unique N] :
    homeomorphOfUnique N (_root_.GenLoop.const : Ω^ N X x) = Path.refl x :=
  Path.ext (funext fun _ => rfl)

section Map

variable {Y : Type*} [TopologicalSpace Y] {y : Y}

/-- A homeomorphism `e : X ≃ₜ Y` with `e x = y` induces, by postcomposition, a homeomorphism of
the spaces of generalized loops `Ω^ N X x ≃ₜ Ω^ N Y y`. -/
def _root_.Homeomorph.genLoopHomeomorph (e : X ≃ₜ Y) (h : e x = y) : Ω^ N X x ≃ₜ Ω^ N Y y where
  toFun := map ⟨e, e.continuous⟩ h
  invFun := map ⟨e.symm, e.symm.continuous⟩ (e.symm_apply_eq.mpr h.symm)
  left_inv p := _root_.GenLoop.ext _ _ fun t => by
    simp only [map_apply, ContinuousMap.coe_mk, Homeomorph.symm_apply_apply]
  right_inv p := _root_.GenLoop.ext _ _ fun t => by
    simp only [map_apply, ContinuousMap.coe_mk, Homeomorph.apply_symm_apply]
  continuous_toFun :=
    ((ContinuousMap.continuous_postcomp ⟨e, e.continuous⟩).comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((ContinuousMap.continuous_postcomp ⟨e.symm, e.symm.continuous⟩).comp
      continuous_subtype_val).subtype_mk _

/-- The inverse of `Homeomorph.genLoopHomeomorph e` is `Homeomorph.genLoopHomeomorph e.symm`. -/
theorem _root_.Homeomorph.genLoopHomeomorph_symm (e : X ≃ₜ Y) (h : e x = y) :
    (Homeomorph.genLoopHomeomorph e h : Ω^ N X x ≃ₜ Ω^ N Y y).symm =
      Homeomorph.genLoopHomeomorph e.symm (e.symm_apply_eq.mpr h.symm) := by
  rw [Homeomorph.genLoopHomeomorph, Homeomorph.genLoopHomeomorph]; rfl

@[simp]
theorem _root_.Homeomorph.genLoopHomeomorph_apply (e : X ≃ₜ Y) (h : e x = y) (p : Ω^ N X x)
    (t : I^N) :
    Homeomorph.genLoopHomeomorph e h p t = e (p t) :=
  map_apply ⟨e, e.continuous⟩ h p t

@[simp]
theorem _root_.Homeomorph.genLoopHomeomorph_symm_apply (e : X ≃ₜ Y) (h : e x = y)
    (p : Ω^ N Y y) (t : I^N) :
    (Homeomorph.genLoopHomeomorph e h).symm p t = e.symm (p t) :=
  map_apply ⟨e.symm, e.symm.continuous⟩ (e.symm_apply_eq.mpr h.symm) p t

end Map

end GenLoop

namespace HomotopyGroup

variable {N X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {x : X} {y : Y}

/-- A homeomorphism `e : X ≃ₜ Y` carrying `x` to `y` induces an equivalence of homotopy groups
`π_N(X, x) ≃ π_N(Y, y)`. The forward map is `HomotopyGroup.map` of `e`; the inverse is
`HomotopyGroup.map` of `e.symm`. This holds in every dimension `N`. -/
@[expose] noncomputable def homeomorphEquivOfEq (e : X ≃ₜ Y) (h : e x = y) :
    HomotopyGroup N X x ≃ HomotopyGroup N Y y where
  toFun := map ⟨e, e.continuous⟩ h
  invFun := map ⟨e.symm, e.symm.continuous⟩ (e.symm_apply_eq.mpr h.symm)
  left_inv a :=
    map_map_of_comp_eq_id ⟨e.symm, e.symm.continuous⟩ ⟨e, e.continuous⟩ h
      (e.symm_apply_eq.mpr h.symm)
      (ContinuousMap.ext fun t => e.symm_apply_apply t) a
  right_inv b :=
    map_map_of_comp_eq_id ⟨e, e.continuous⟩ ⟨e.symm, e.symm.continuous⟩
      (e.symm_apply_eq.mpr h.symm) h
      (ContinuousMap.ext fun t => e.apply_symm_apply t) b

@[simp]
theorem homeomorphEquivOfEq_apply (e : X ≃ₜ Y) (h : e x = y) (a : HomotopyGroup N X x) :
    homeomorphEquivOfEq e h a = map ⟨e, e.continuous⟩ h a :=
  rfl

@[simp]
theorem homeomorphEquivOfEq_symm_apply (e : X ≃ₜ Y) (h : e x = y) (b : HomotopyGroup N Y y) :
    (homeomorphEquivOfEq e h).symm b =
      map ⟨e.symm, e.symm.continuous⟩ (e.symm_apply_eq.mpr h.symm) b :=
  rfl

/-- A homeomorphism `e : X ≃ₜ Y` induces an equivalence of homotopy groups
`π_N(X, x) ≃ π_N(Y, e x)`, in every dimension `N`. -/
@[expose] noncomputable def homeomorphEquiv (e : X ≃ₜ Y) (x : X) :
    HomotopyGroup N X x ≃ HomotopyGroup N Y (e x) :=
  homeomorphEquivOfEq e rfl

@[simp]
theorem homeomorphEquiv_apply (e : X ≃ₜ Y) (x : X) (a : HomotopyGroup N X x) :
    homeomorphEquiv e x a = map ⟨e, e.continuous⟩ rfl a :=
  rfl

@[simp]
theorem homeomorphEquiv_symm_apply (e : X ≃ₜ Y) (x : X) (b : HomotopyGroup N Y (e x)) :
    (homeomorphEquiv e x).symm b =
      map ⟨e.symm, e.symm.continuous⟩ (e.symm_apply_apply x) b :=
  rfl

/-- A homeomorphism `e : X ≃ₜ Y` carrying `x` to `y` induces an isomorphism of homotopy groups
`π_N(X, x) ≃* π_N(Y, y)` in positive dimensions. -/
@[expose] noncomputable def homeomorphMulEquivOfEq [DecidableEq N] [Nonempty N]
    (e : X ≃ₜ Y) (h : e x = y) :
    HomotopyGroup N X x ≃* HomotopyGroup N Y y :=
  { homeomorphEquivOfEq e h with
    map_mul' := map_mul ⟨e, e.continuous⟩ h }

@[simp]
theorem homeomorphMulEquivOfEq_apply [DecidableEq N] [Nonempty N] (e : X ≃ₜ Y) (h : e x = y)
    (a : HomotopyGroup N X x) :
    homeomorphMulEquivOfEq e h a = map ⟨e, e.continuous⟩ h a :=
  rfl

@[simp]
theorem homeomorphMulEquivOfEq_symm_apply [DecidableEq N] [Nonempty N] (e : X ≃ₜ Y) (h : e x = y)
    (b : HomotopyGroup N Y y) : (homeomorphMulEquivOfEq e h).symm b =
      map ⟨e.symm, e.symm.continuous⟩ (e.symm_apply_eq.mpr h.symm) b :=
  rfl

/-- A homeomorphism `e : X ≃ₜ Y` induces an isomorphism of homotopy groups
`π_N(X, x) ≃* π_N(Y, e x)` in positive dimensions. -/
@[expose] noncomputable def homeomorphMulEquiv [DecidableEq N] [Nonempty N] (e : X ≃ₜ Y) (x : X) :
    HomotopyGroup N X x ≃* HomotopyGroup N Y (e x) :=
  homeomorphMulEquivOfEq e rfl

@[simp]
theorem homeomorphMulEquiv_apply [DecidableEq N] [Nonempty N] (e : X ≃ₜ Y) (x : X)
    (a : HomotopyGroup N X x) :
    homeomorphMulEquiv e x a = map ⟨e, e.continuous⟩ rfl a :=
  rfl

@[simp]
theorem homeomorphMulEquiv_symm_apply [DecidableEq N] [Nonempty N] (e : X ≃ₜ Y) (x : X)
    (b : HomotopyGroup N Y (e x)) : (homeomorphMulEquiv e x).symm b =
      map ⟨e.symm, e.symm.continuous⟩ (e.symm_apply_apply x) b :=
  rfl

end HomotopyGroup
