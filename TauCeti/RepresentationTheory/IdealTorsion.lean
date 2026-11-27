/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.Map
public import TauCeti.RepresentationTheory.Smooth.Basic

/-!
# The representation on ideal torsion

The vectors in an `A`-linear representation annihilated by an ideal `I` carry a representation
over `A ⧸ I`. Restriction to these vectors is functorial. For the maximal ideal of a local
coefficient ring this gives the representation on the socle over the residue field.
-/

public section

open Submodule

namespace Representation

variable {A G V W : Type*} [CommRing A] [Monoid G] [AddCommGroup V] [Module A V]
  [AddCommGroup W] [Module A W]

/-- The action on the vectors killed by `I`, as a representation over the quotient ring. -/
def torsionByIdeal (ρ : Representation A G V) (I : Ideal A) :
    Representation (A ⧸ I) G (torsionBySet A V I) where
  toFun g := (ρ g).torsionByIdeal I
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' g h := by simp [Module.End.mul_eq_comp]

@[simp]
theorem torsionByIdeal_apply (ρ : Representation A G V) (I : Ideal A) (g : G) :
    ρ.torsionByIdeal I g = (ρ g).torsionByIdeal I := (rfl)

/-- An intertwiner induces an intertwiner of the quotient-ring representations on ideal
torsion. -/
def IntertwiningMap.torsionByIdeal {ρ : Representation A G V} {σ : Representation A G W}
    (f : ρ.IntertwiningMap σ) (I : Ideal A) :
    (ρ.torsionByIdeal I).IntertwiningMap (σ.torsionByIdeal I) where
  toLinearMap := f.toLinearMap.torsionByIdeal I
  isIntertwining' g := by
    simp only [torsionByIdeal_apply, ← LinearMap.torsionByIdeal_comp, f.isIntertwining']

@[simp]
theorem IntertwiningMap.toLinearMap_torsionByIdeal {ρ : Representation A G V}
    {σ : Representation A G W} (f : ρ.IntertwiningMap σ) (I : Ideal A) :
    (f.torsionByIdeal I).toLinearMap = f.toLinearMap.torsionByIdeal I := (rfl)

@[simp]
theorem IntertwiningMap.coe_torsionByIdeal_apply {ρ : Representation A G V}
    {σ : Representation A G W} (f : ρ.IntertwiningMap σ) (I : Ideal A) (v : torsionBySet A V I) :
    (f.torsionByIdeal I v : W) = f v :=
  LinearMap.coe_torsionByIdeal_apply _ _ _

section Group

variable {G : Type*} [Group G] (ρ : Representation A G V) (I : Ideal A)

/-- Passing to ideal torsion preserves each vector's stabilizer. -/
@[simp]
theorem stabilizer_torsionByIdeal (v : torsionBySet A V I) :
    (ρ.torsionByIdeal I).stabilizer v = ρ.stabilizer (v : V) := by
  ext
  simp [Subtype.ext_iff]

/-- Ideal torsion of a smooth representation is smooth over the quotient ring. -/
instance [TopologicalSpace G] [IsSmooth ρ] : IsSmooth (ρ.torsionByIdeal I) :=
  ⟨fun v ↦ ρ.stabilizer_torsionByIdeal I v ▸ IsSmooth.isOpen_stabilizer (v : V)⟩

end Group

end Representation
