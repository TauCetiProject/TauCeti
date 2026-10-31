/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.GroupTheory.SemidirectProduct
public import TauCeti.GroupTheory.SpecificGroups.Heisenberg

/-!
# The Heisenberg subgroup of Weierstrass coordinate changes

The changes of variables with scaling factor `u = 1` form a Heisenberg group, not an
additive three-dimensional group. We identify this subgroup with `TauCeti.HeisenbergGroup`
and express the full native coordinate-change group as its semidirect product with the
units of the coefficient ring. These identifications are natural under ring homomorphisms,
so they retain infinitesimal coordinate changes as well as field-valued ones.

We use Mathlib's multiplication convention for `WeierstrassCurve.VariableChange`:
`(u,r,s,t)(v,R,S,T) = (uv,rv²+R,vs+S,tv³+rSv²+T)`.
Consequently conjugation by `(u,0,0,0)` acts on the Heisenberg coordinates `(r,s,t)`
with inverse weights `(2,1,3)`. The cross term is `rS`, as in the existing Heisenberg
multiplication; it must not be discarded when forming the cubic presentation.

The coordinate-change group is the one used in Bauer, *Computation of the homotopy of
the spectrum tmf*, §3. The group-theoretic constructions here use the existing
`TauCeti.HeisenbergGroup` and Mathlib's `SemidirectProduct`.
-/

public section

namespace WeierstrassCurve.VariableChange

open TauCeti

variable (R : Type*) [CommRing R]

/-- The scaling factor as a group homomorphism. -/
def scalingHom : VariableChange R →* Rˣ where
  toFun C := C.u
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem scalingHom_apply (C : VariableChange R) : scalingHom R C = C.u := (rfl)

/-- Pure scalings split the scaling-factor homomorphism. -/
def scaling : Rˣ →* VariableChange R where
  toFun u := ⟨u, 0, 0, 0⟩
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp [mul_def]

@[simp] theorem scaling_apply (u : Rˣ) : scaling R u = ⟨u, 0, 0, 0⟩ := (rfl)

/-- The Heisenberg group embeds as the changes of variables with unit scaling factor. -/
def heisenbergHom : HeisenbergGroup R →* VariableChange R where
  toFun a := ⟨1, a.x, a.y, a.z⟩
  map_one' := rfl
  map_mul' a b := by ext <;> simp [mul_def, add_comm, add_left_comm, add_assoc]

@[simp] theorem heisenbergHom_apply (a : HeisenbergGroup R) :
    heisenbergHom R a = ⟨1, a.x, a.y, a.z⟩ := (rfl)

/-- No Heisenberg coordinate is lost by the embedding. -/
theorem heisenbergHom_injective : Function.Injective (heisenbergHom R) := by
  intro a b h
  exact HeisenbergGroup.ext (congrArg VariableChange.r h)
    (congrArg VariableChange.s h) (congrArg VariableChange.t h)

/-- The Heisenberg subgroup is precisely the kernel of the scaling factor. -/
theorem range_heisenbergHom : (heisenbergHom R).range = (scalingHom R).ker := by
  ext C
  constructor
  · rintro ⟨a, rfl⟩
    rfl
  · intro h
    exact ⟨⟨C.r, C.s, C.t⟩, VariableChange.ext h.symm rfl rfl rfl⟩

/-- The unit-scaling subgroup with its induced group structure is the Heisenberg group. -/
def heisenbergEquivKer : HeisenbergGroup R ≃* (scalingHom R).ker where
  toFun a := ⟨heisenbergHom R a, rfl⟩
  invFun C := ⟨C.val.r, C.val.s, C.val.t⟩
  left_inv _ := rfl
  right_inv C := Subtype.ext (VariableChange.ext C.property.symm rfl rfl rfl)
  map_mul' a b := Subtype.ext ((heisenbergHom R).map_mul a b)

@[simp] theorem heisenbergEquivKer_apply (a : HeisenbergGroup R) :
    (heisenbergEquivKer R a).val = heisenbergHom R a := (rfl)

@[simp] theorem heisenbergEquivKer_symm_apply (C : (scalingHom R).ker) :
    (heisenbergEquivKer R).symm C = ⟨C.val.r, C.val.s, C.val.t⟩ := (rfl)

/-- The action of pure scalings on Heisenberg coordinates, with inverse weights `(2,1,3)`.
The weights add in the cross term, so this is an action by group automorphisms. -/
def heisenbergAction : Rˣ →* MulAut (HeisenbergGroup R) where
  toFun u :=
    { toFun := fun a ↦ ⟨a.x * (↑u⁻¹ : R) ^ 2, a.y * ↑u⁻¹, a.z * (↑u⁻¹ : R) ^ 3⟩
      invFun := fun a ↦ ⟨a.x * (↑u : R) ^ 2, a.y * ↑u, a.z * (↑u : R) ^ 3⟩
      left_inv := by intro a; ext <;> simp [mul_assoc, ← mul_pow]
      right_inv := by intro a; ext <;> simp [mul_assoc, ← mul_pow]
      map_mul' := by intro a b; ext <;> simp <;> ring }
  map_one' := by ext a <;> simp
  map_mul' u v := by ext a <;> simp [mul_pow] <;> ring

@[simp] theorem heisenbergAction_apply (u : Rˣ) (a : HeisenbergGroup R) :
    heisenbergAction R u a =
      ⟨a.x * (↑u⁻¹ : R) ^ 2, a.y * ↑u⁻¹, a.z * (↑u⁻¹ : R) ^ 3⟩ := (rfl)

/-- The action is conjugation by the corresponding pure scaling in the native group. -/
theorem heisenbergHom_action (u : Rˣ) (a : HeisenbergGroup R) :
    heisenbergHom R (heisenbergAction R u a) =
      scaling R u * heisenbergHom R a * (scaling R u)⁻¹ := by
  ext <;> simp [mul_def, inv_def, mul_comm]

/-- The full coordinate-change group is the semidirect product of the Heisenberg group
and the units. This is an isomorphism over every commutative ring, including the zero ring. -/
noncomputable def semidirectProductEquiv :
    HeisenbergGroup R ⋊[heisenbergAction R] Rˣ ≃* VariableChange R :=
  MulEquiv.ofBijective
    (SemidirectProduct.lift (heisenbergHom R) (scaling R) (fun u ↦ by
      exact DFunLike.ext _ _ (heisenbergHom_action R u))) (by
    constructor
    · intro a b h
      have hu : a.right = b.right := by
        simpa [SemidirectProduct.lift, mul_def] using congrArg VariableChange.u h
      have hn : a.left = b.left := by
        apply heisenbergHom_injective R
        apply mul_right_cancel (b := scaling R a.right)
        simpa only [SemidirectProduct.lift, MonoidHom.coe_mk, OneHom.coe_mk, hu] using h
      exact SemidirectProduct.ext hn hu
    · intro C
      refine ⟨⟨⟨C.r * (↑C.u⁻¹ : R) ^ 2, C.s * ↑C.u⁻¹,
        C.t * (↑C.u⁻¹ : R) ^ 3⟩, C.u⟩, ?_⟩
      have hs : (↑C.u : R) * (C.s * ↑C.u⁻¹) = C.s := by
        rw [mul_left_comm, Units.mul_inv, mul_one]
      ext <;> simp [SemidirectProduct.lift, mul_def, mul_assoc, ← mul_pow, hs])

/-- The isomorphism multiplies the unipotent part by the pure scaling, in that order. -/
@[simp] theorem semidirectProductEquiv_apply
    (a : HeisenbergGroup R ⋊[heisenbergAction R] Rˣ) :
    semidirectProductEquiv R a = heisenbergHom R a.left * scaling R a.right := (rfl)

/-- Recovering the unipotent coordinates requires dividing by the scaling weights. -/
@[simp] theorem semidirectProductEquiv_symm_apply (C : VariableChange R) :
    (semidirectProductEquiv R).symm C =
      ⟨⟨C.r * (↑C.u⁻¹ : R) ^ 2, C.s * ↑C.u⁻¹, C.t * (↑C.u⁻¹ : R) ^ 3⟩, C.u⟩ := by
  apply (semidirectProductEquiv R).injective
  have hs : (↑C.u : R) * (C.s * ↑C.u⁻¹) = C.s := by
    rw [mul_left_comm, Units.mul_inv, mul_one]
  ext <;> simp [mul_def, mul_assoc, ← mul_pow, hs]

variable {R} {S : Type*} [CommRing S]

-- Naturality is stated without simp attributes: the coordinate formulas above are the
-- simp normal forms, whereas these statements retain the group homomorphisms.

/-- Pure scalings commute with base change. -/
theorem map_scaling (f : R →+* S) (u : Rˣ) :
    (scaling R u).map f = scaling S (Units.map f u) := by
  ext <;> simp [map]

/-- The Heisenberg embedding commutes with base change. -/
theorem map_heisenbergHom (f : R →+* S) (a : HeisenbergGroup R) :
    (heisenbergHom R a).map f = heisenbergHom S (HeisenbergGroup.map f a) := by
  ext <;> simp [map]

/-- Base change intertwines the two scaling actions. -/
theorem map_heisenbergAction (f : R →+* S) (u : Rˣ) (a : HeisenbergGroup R) :
    HeisenbergGroup.map f (heisenbergAction R u a) =
      heisenbergAction S (Units.map f u) (HeisenbergGroup.map f a) := by
  ext <;> simp

/-- The semidirect-product decomposition commutes with every ring homomorphism. -/
theorem map_semidirectProductEquiv (f : R →+* S)
    (a : HeisenbergGroup R ⋊[heisenbergAction R] Rˣ) :
    (semidirectProductEquiv R a).map f =
      semidirectProductEquiv S
        (SemidirectProduct.map (HeisenbergGroup.map f) (Units.map f)
          (fun u ↦ DFunLike.ext _ _ (map_heisenbergAction f u)) a) := by
  simp only [semidirectProductEquiv_apply, SemidirectProduct.map_left,
    SemidirectProduct.map_right]
  calc
    (heisenbergHom R a.left * scaling R a.right).map f =
        (heisenbergHom R a.left).map f * (scaling R a.right).map f :=
      (mapHom f).map_mul _ _
    _ = _ := by rw [map_heisenbergHom, map_scaling]

end WeierstrassCurve.VariableChange
