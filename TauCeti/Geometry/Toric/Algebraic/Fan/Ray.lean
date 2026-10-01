/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.Basic
public import TauCeti.Geometry.Toric.Algebraic.Ray.Generation

/-!
# Rays of a finite toric fan

A ray of a fan is a one-dimensional cone belonging to the fan. This intrinsic indexing type is
finite and agrees, below any cone of the fan, with the rays of that cone. Every nonzero cone of a
fan contains a ray; this follows from the generation of a toric cone by its rays.

The global ray type is the natural index for invariant boundary components of a toric variety.

## Main declarations

* `TauCeti.Toric.Fan.Ray`: the one-dimensional cones of a fan.
* `TauCeti.Toric.Fan.Ray.ofToricRay`: a ray of a cone of the fan, viewed as a fan ray.
* `TauCeti.Toric.Fan.Ray.toToricRay`: a fan ray contained in a cone, viewed as a ray of that cone.
* `TauCeti.Toric.Fan.rayEquiv`: the equivalence between rays below a cone and its toric rays.
* `TauCeti.Toric.Fan.exists_ray_le_of_ne_bot`: every nonzero cone of a fan contains a ray.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.2 and 3.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.2 and 3.2.
-/

public section

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Phi : Fan i)

/-- A ray of a fan is a one-dimensional cone belonging to the fan. -/
abbrev Ray : Type _ :=
  {rho : Phi.cones //
    Module.finrank ℝ (Submodule.span ℝ (rho.1 : Set V)) = 1}

namespace Ray

/-- The cone of the fan underlying a fan ray. -/
abbrev toCone (rho : Phi.Ray) : Phi.cones := rho.1

/-- The cone underlying a fan ray has one-dimensional linear span. -/
@[simp]
theorem finrank_span (rho : Phi.Ray) :
    Module.finrank ℝ (Submodule.span ℝ (rho.toCone.1 : Set V)) = 1 :=
  rho.2

/-- A fan ray is not the zero cone. -/
theorem toCone_ne_bot (rho : Phi.Ray) : rho.toCone.1 ≠ ⊥ := by
  intro h
  have hrank := rho.finrank_span
  -- Expose the zero cone as a singleton so `Submodule.span_zero_singleton` applies.
  rw [h, show ((⊥ : PointedCone ℝ V) : Set V) = ({0} : Set V) by ext; simp,
    Submodule.span_zero_singleton, finrank_bot] at hrank
  omega

/-- A ray of a cone belonging to a fan is a ray of the fan. -/
def ofToricRay (sigma : Phi.cones) (rho : ToricRay sigma.1) : Phi.Ray :=
  ⟨⟨rho.toPointedCone, Phi.mem_of_isFaceOf sigma.2 rho.1.isFaceOf⟩, rho.2⟩

@[simp]
theorem toCone_ofToricRay (sigma : Phi.cones) (rho : ToricRay sigma.1) :
    (ofToricRay Phi sigma rho).toCone.1 = rho.toPointedCone :=
  (rfl)

/-- A toric ray, viewed as a fan ray, is contained in its original cone. -/
theorem toCone_ofToricRay_le (sigma : Phi.cones) (rho : ToricRay sigma.1) :
    (ofToricRay Phi sigma rho).toCone ≤ sigma := by
  exact Subtype.coe_le_coe.1 (toCone_ofToricRay Phi sigma rho ▸ rho.1.isFaceOf.le)

/-- A fan ray contained in a cone is a ray of that cone. -/
def toToricRay (rho : Phi.Ray) (sigma : Phi.cones) (h : rho.toCone ≤ sigma) :
    ToricRay sigma.1 :=
  ⟨⟨rho.toCone.1, Phi.isFaceOf_of_le sigma.2 rho.toCone.2 h⟩, rho.2⟩

@[simp]
theorem toPointedCone_toToricRay (rho : Phi.Ray) (sigma : Phi.cones)
    (h : rho.toCone ≤ sigma) :
    (rho.toToricRay Phi sigma h).toPointedCone = rho.toCone.1 :=
  (rfl)

end Ray

/-- The fan rays contained in a cone are exactly the toric rays of that cone. -/
def rayEquiv (sigma : Phi.cones) :
    {rho : Phi.Ray // rho.toCone ≤ sigma} ≃ ToricRay sigma.1 where
  toFun rho := rho.1.toToricRay Phi sigma rho.2
  invFun rho := ⟨Ray.ofToricRay Phi sigma rho, rho.1.isFaceOf.le⟩
  left_inv rho := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv rho := by
    apply Subtype.ext
    apply PointedCone.Face.ext
    exact fun _ ↦ Iff.rfl

/-- The equivalence from fan rays below a cone to its toric rays uses the same underlying cone. -/
@[simp]
theorem rayEquiv_apply (sigma : Phi.cones)
    (rho : {rho : Phi.Ray // rho.toCone ≤ sigma}) :
    Phi.rayEquiv sigma rho = rho.1.toToricRay Phi sigma rho.2 :=
  (rfl)

/-- The inverse equivalence views a toric ray as a cone belonging to the fan. -/
@[simp]
theorem rayEquiv_symm_apply (sigma : Phi.cones) (rho : ToricRay sigma.1) :
    (Phi.rayEquiv sigma).symm rho =
      ⟨Ray.ofToricRay Phi sigma rho, Ray.toCone_ofToricRay_le Phi sigma rho⟩ :=
  (rfl)

/-- Every nonzero cone of a fan contains a ray of the fan. -/
theorem exists_ray_le_of_ne_bot (sigma : Phi.cones) (hσ : sigma.1 ≠ ⊥) :
    ∃ rho : Phi.Ray, rho.toCone ≤ sigma := by
  have hnonempty : Nonempty (ToricRay sigma.1) := by
    by_contra h
    let _ : IsEmpty (ToricRay sigma.1) := not_nonempty_iff.mp h
    have hgen := ToricRay.iSup_toPointedCone (Phi.isToricCone sigma.2).fg
      (Phi.isToricCone sigma.2).salient
    rw [iSup_of_empty] at hgen
    exact hσ hgen.symm
  let rho := Classical.choice hnonempty
  exact ⟨Ray.ofToricRay Phi sigma rho, rho.1.isFaceOf.le⟩

end TauCeti.Toric.Fan
