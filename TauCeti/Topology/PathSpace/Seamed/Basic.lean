/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.FixedPoints.Basic
public import TauCeti.Topology.MappingSpace.FreeLoop

/-!
# Seamed path spaces

For a self-map `φ : X → X`, a `φ`-seamed path is a path `γ : [0, 1] → X` whose end is the image
of its start under `φ`, `γ 1 = φ (γ 0)`. The `φ`-seamed paths, with the subspace topology of the
compact-open topology on `C(I, X)`, form the space `TauCeti.SeamedPath φ`. It is the
configuration space on which the Floer theory of a symplectomorphism is built, in place of the free
loop space of Hamiltonian Floer theory: its constant paths are the fixed points of `φ`, and for
`φ = id` it is the free loop space.

When `φ` is a homeomorphism the `φ`-seamed paths are the sections of the mapping torus of `φ` over
the circle (`TauCeti.SeamedPath.sectionHomeomorph`, in `TauCeti.Topology.MappingTorus.Section`).

## Main definitions

* `TauCeti.SeamedPath φ`: the paths `γ : C(I, X)` with `γ 1 = φ (γ 0)`.
* `TauCeti.SeamedPath.ofPath`, `TauCeti.SeamedPath.toPath`: a path from `x` to `φ x` is a
  `φ`-seamed path, and conversely.
* `TauCeti.SeamedPath.const`: the constant path at a fixed point of `φ`.
* `TauCeti.SeamedPath.map`: the map of seamed path spaces induced by a map `g` intertwining two
  seams, `g ∘ φ = ψ ∘ g`.

## Main results

* `TauCeti.SeamedPath.fixedPointsHomeomorph`: the constant `φ`-seamed paths are the fixed points
  of `φ`.
* `TauCeti.SeamedPath.idHomeomorph`: the `id`-seamed paths are the closed paths, that is, the free
  loops.
* `TauCeti.SeamedPath.symmHomeomorph`: reversing paths identifies the `φ`-seamed paths with the
  `φ⁻¹`-seamed paths, for a homeomorphism `φ`.

## References

* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. 120 (1989),
  575–611.
* S. Dostoglou and D. A. Salamon, *Self-dual instantons and holomorphic curves*, Ann. of Math. 139
  (1994), 581–640.
-/

public section

open unitInterval Function

namespace TauCeti

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The `φ`-seamed path space: the paths `γ : [0, 1] → X` whose end is the image of their start
under `φ`, `γ 1 = φ (γ 0)`, with the subspace topology of the compact-open topology. -/
abbrev SeamedPath (φ : X → X) : Type _ :=
  {γ : C(I, X) // γ 1 = φ (γ 0)}

namespace SeamedPath

variable {φ : X → X}

/-- The seam condition: the end of a `φ`-seamed path is the image of its start under `φ`. -/
@[simp]
theorem apply_one (γ : SeamedPath φ) : γ.val 1 = φ (γ.val 0) :=
  γ.property

/-- Two seamed paths are equal when they agree at every time. -/
@[ext]
theorem ext {γ δ : SeamedPath φ} (h : ∀ t, γ.val t = δ.val t) : γ = δ :=
  Subtype.ext (ContinuousMap.ext h)

/-! ### Seamed paths as paths -/

/-- A path from `x` to `φ x` is a `φ`-seamed path. -/
def ofPath {x : X} (p : Path x (φ x)) : SeamedPath φ :=
  ⟨p.toContinuousMap, by simp⟩

@[simp]
theorem val_ofPath {x : X} (p : Path x (φ x)) : (ofPath p).val = p.toContinuousMap :=
  (rfl)

theorem ofPath_apply {x : X} (p : Path x (φ x)) (t : I) : (ofPath p).val t = p t :=
  (rfl)

/-- A `φ`-seamed path, read as a path from its start to the image of its start under `φ`. -/
def toPath (γ : SeamedPath φ) : Path (γ.val 0) (φ (γ.val 0)) where
  toContinuousMap := γ.val
  source' := rfl
  target' := γ.property

@[simp]
theorem coe_toPath (γ : SeamedPath φ) : ⇑γ.toPath = ⇑γ.val :=
  (rfl)

theorem toPath_apply (γ : SeamedPath φ) (t : I) : γ.toPath t = γ.val t :=
  (rfl)

@[simp]
theorem ofPath_toPath (γ : SeamedPath φ) : ofPath γ.toPath = γ :=
  (rfl)

/-! ### Constant seamed paths and fixed points -/

/-- The constant path at a fixed point of `φ` is `φ`-seamed. -/
def const (x : X) (hx : IsFixedPt φ x) : SeamedPath φ :=
  ⟨ContinuousMap.const I x, hx.symm⟩

@[simp]
theorem const_apply (x : X) (hx : IsFixedPt φ x) (t : I) : (const x hx).val t = x :=
  (rfl)

/-- The start of a constant `φ`-seamed path is a fixed point of `φ`. -/
theorem isFixedPt_apply_zero {γ : SeamedPath φ} (hγ : ∀ t, γ.val t = γ.val 0) :
    IsFixedPt φ (γ.val 0) :=
  ((apply_one γ).symm.trans (hγ 1) :)

/-- A seamed path is constant exactly when it is the constant path at a fixed point. -/
theorem forall_apply_eq_apply_zero_iff {γ : SeamedPath φ} :
    (∀ t, γ.val t = γ.val 0) ↔ ∃ (x : X) (hx : IsFixedPt φ x), γ = const x hx where
  mp hγ := ⟨γ.val 0, isFixedPt_apply_zero hγ, ext hγ⟩
  mpr := by
    rintro ⟨x, hx, rfl⟩ t
    rfl

/-- **The constant `φ`-seamed paths are the fixed points of `φ`.** The constant path at a fixed
point and the start of a constant seamed path are mutually inverse homeomorphisms. -/
def fixedPointsHomeomorph (φ : X → X) :
    fixedPoints φ ≃ₜ {γ : SeamedPath φ // ∀ t, γ.val t = γ.val 0} where
  toFun x := ⟨const x.val x.property, fun _ ↦ rfl⟩
  invFun γ := ⟨γ.val.val 0, isFixedPt_apply_zero γ.property⟩
  left_inv _ := rfl
  right_inv γ := Subtype.ext (ext fun t ↦ (γ.property t).symm)
  continuous_toFun := ((ContinuousMap.continuous_const'.comp continuous_subtypeVal).subtype_mk
    _).subtype_mk _
  continuous_invFun := ((continuous_eval_const (0 : I)).comp
    (continuous_subtypeVal.comp continuous_subtypeVal)).subtype_mk _

@[simp]
theorem fixedPointsHomeomorph_apply (x : fixedPoints φ) :
    (fixedPointsHomeomorph φ x).val = const x.val x.property :=
  (rfl)

@[simp]
theorem fixedPointsHomeomorph_symm_apply (γ : {γ : SeamedPath φ // ∀ t, γ.val t = γ.val 0}) :
    ((fixedPointsHomeomorph φ).symm γ).val = γ.val.val 0 :=
  (rfl)

/-! ### The identity seam: free loops -/

variable (X) in
/-- **The `id`-seamed paths are the free loops**: they are exactly the closed paths
`TauCeti.ClosedUnitPath X`, which `TauCeti.circleMapHomeomorphClosedUnitPath` identifies with the
maps from the circle. -/
def idHomeomorph : SeamedPath (id : X → X) ≃ₜ ClosedUnitPath X where
  toFun γ := ⟨γ.val, γ.property.symm⟩
  invFun γ := ⟨γ.val, γ.property.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtypeVal.subtype_mk _
  continuous_invFun := continuous_subtypeVal.subtype_mk _

@[simp]
theorem coe_idHomeomorph (γ : SeamedPath (id : X → X)) : (idHomeomorph X γ).val = γ.val :=
  (rfl)

@[simp]
theorem coe_idHomeomorph_symm (γ : ClosedUnitPath X) : ((idHomeomorph X).symm γ).val = γ.val :=
  (rfl)

/-! ### Functoriality -/

/-- A map `g` intertwining the seams, `g ∘ φ = ψ ∘ g`, sends `φ`-seamed paths to `ψ`-seamed paths
by composition. -/
def map {ψ : Y → Y} (g : C(X, Y)) (hg : Semiconj g φ ψ) : C(SeamedPath φ, SeamedPath ψ) where
  toFun γ := ⟨g.comp γ.val, (congrArg g (apply_one γ)).trans (hg.eq _)⟩
  continuous_toFun :=
    ((ContinuousMap.continuous_postcomp g).comp continuous_subtypeVal).subtype_mk _

@[simp]
theorem map_apply {ψ : Y → Y} (g : C(X, Y)) (hg : Semiconj g φ ψ) (γ : SeamedPath φ) (t : I) :
    (map g hg γ).val t = g (γ.val t) :=
  (rfl)

@[simp]
theorem map_id : map (ContinuousMap.id X) (Semiconj.id_left : Semiconj id φ φ) =
    ContinuousMap.id (SeamedPath φ) :=
  (rfl)

theorem map_comp {ψ : Y → Y} {χ : Z → Z} (h : C(Y, Z)) (hh : Semiconj h ψ χ) (g : C(X, Y))
    (hg : Semiconj g φ ψ) : map (h.comp g) (hh.comp_left hg) = (map h hh).comp (map g hg) :=
  (rfl)

/-- The constant path at a fixed point is sent to the constant path at its image, which is a fixed
point of the target seam. -/
@[simp]
theorem map_const {ψ : Y → Y} (g : C(X, Y)) (hg : Semiconj g φ ψ) (x : X) (hx : IsFixedPt φ x) :
    map g hg (const x hx) = const (g x) (hx.map hg) :=
  (rfl)

/-! ### Reversal -/

/-- The reversal of a `φ`-seamed path is `φ⁻¹`-seamed. -/
private theorem apply_symm_one_eq {φ : X ≃ₜ X} (γ : SeamedPath φ) :
    γ.val (σ 1) = φ.symm (γ.val (σ 0)) := by
  simp

/-- The reversal of a `φ⁻¹`-seamed path is `φ`-seamed. -/
private theorem apply_symm_one_eq_of_symm {φ : X ≃ₜ X} (γ : SeamedPath φ.symm) :
    γ.val (σ 1) = φ (γ.val (σ 0)) := by
  simp

/-- **Reversal of seamed paths.** For a homeomorphism `φ`, reversing the time of a `φ`-seamed path
gives a `φ⁻¹`-seamed path, and this is a homeomorphism. -/
def symmHomeomorph (φ : X ≃ₜ X) : SeamedPath φ ≃ₜ SeamedPath φ.symm where
  toFun γ := ⟨γ.val.comp ⟨σ, continuous_symm⟩, apply_symm_one_eq γ⟩
  invFun γ := ⟨γ.val.comp ⟨σ, continuous_symm⟩, apply_symm_one_eq_of_symm γ⟩
  left_inv γ := ext fun t ↦ by simp
  right_inv γ := ext fun t ↦ by simp
  continuous_toFun :=
    ((ContinuousMap.continuous_precomp _).comp continuous_subtypeVal).subtype_mk _
  continuous_invFun :=
    ((ContinuousMap.continuous_precomp _).comp continuous_subtypeVal).subtype_mk _

@[simp]
theorem symmHomeomorph_apply (φ : X ≃ₜ X) (γ : SeamedPath φ) (t : I) :
    (symmHomeomorph φ γ).val t = γ.val (σ t) :=
  (rfl)

@[simp]
theorem symmHomeomorph_symm_apply (φ : X ≃ₜ X) (γ : SeamedPath φ.symm) (t : I) :
    ((symmHomeomorph φ).symm γ).val t = γ.val (σ t) :=
  (rfl)

end SeamedPath

end TauCeti
