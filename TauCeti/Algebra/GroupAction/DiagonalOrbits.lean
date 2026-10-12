/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Prod
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.Transitive

/-!
# Diagonal orbits and stabilizer orbits

If `G` acts transitively on `Y`, fixing a point `y : Y` identifies the diagonal orbit space
of `X × Y` with the orbit space of `X` under the stabilizer of `y`. This is useful for replacing
an object with a moving marked point by an object whose mark is fixed once and for all.

The forward map is canonical: it sends the stabilizer orbit of `x` to the diagonal orbit of
`(x, y)`. Its injectivity does not require transitivity. Transitivity supplies surjectivity;
the inverse sends the orbit of `(x, g • y)` to the stabilizer orbit of `g⁻¹ • x`.
-/

public section

namespace TauCeti.MulAction

variable {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]

/-- Attach a fixed mark `y` to a stabilizer orbit, giving a diagonal orbit. -/
def orbitRelQuotientStabilizerMap (y : Y) :
    MulAction.orbitRel.Quotient (MulAction.stabilizer G y) X →
      MulAction.orbitRel.Quotient G (X × Y) :=
  Quotient.map' (fun x => (x, y)) fun x x' h => by
    obtain ⟨g, hg⟩ := h
    refine ⟨(g : G), Prod.ext ?_ ?_⟩
    · simpa only [Subgroup.smul_def, Prod.smul_def, Prod.fst] using hg
    · exact MulAction.mem_stabilizer_iff.mp g.2

@[simp]
theorem orbitRelQuotientStabilizerMap_mk (y : Y) (x : X) :
    orbitRelQuotientStabilizerMap (G := G) y (Quotient.mk'' x) = Quotient.mk'' (x, y) :=
  (rfl)

/-- Fixing the mark identifies stabilizer orbits faithfully with diagonal orbits. -/
theorem orbitRelQuotientStabilizerMap_injective (y : Y) :
    Function.Injective (orbitRelQuotientStabilizerMap (G := G) (X := X) y) := by
  intro q q'
  refine Quotient.inductionOn₂' q q' ?_
  intro x x' h
  obtain ⟨g, hg⟩ := Quotient.exact' h
  refine Quotient.sound' ⟨⟨g, MulAction.mem_stabilizer_iff.mpr (congrArg Prod.snd hg)⟩, ?_⟩
  simpa only [Subgroup.smul_def, Prod.smul_def, Prod.fst] using congrArg Prod.fst hg

/-- Every diagonal orbit admits a representative with mark `y` when the marking action is
transitive. -/
theorem orbitRelQuotientStabilizerMap_surjective [MulAction.IsPretransitive G Y] (y : Y) :
    Function.Surjective (orbitRelQuotientStabilizerMap (G := G) (X := X) y) := by
  intro q
  refine Quotient.inductionOn' q ?_
  rintro ⟨x, z⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G y z
  refine ⟨Quotient.mk'' (g⁻¹ • x), Quotient.sound' ⟨g⁻¹, ?_⟩⟩
  simp [← hg]

/-- Stabilizer orbits with a fixed mark are exactly diagonal orbits with a moving mark. -/
noncomputable def orbitRelQuotientStabilizerEquiv [MulAction.IsPretransitive G Y] (y : Y) :
    MulAction.orbitRel.Quotient (MulAction.stabilizer G y) X ≃
      MulAction.orbitRel.Quotient G (X × Y) :=
  Equiv.ofBijective (orbitRelQuotientStabilizerMap y)
    ⟨orbitRelQuotientStabilizerMap_injective y, orbitRelQuotientStabilizerMap_surjective y⟩

@[simp]
theorem orbitRelQuotientStabilizerEquiv_mk [MulAction.IsPretransitive G Y] (y : Y) (x : X) :
    orbitRelQuotientStabilizerEquiv (G := G) y (Quotient.mk'' x) = Quotient.mk'' (x, y) :=
  (rfl)

@[simp]
theorem orbitRelQuotientStabilizerEquiv_symm_mk [MulAction.IsPretransitive G Y]
    (y : Y) (x : X) :
    (orbitRelQuotientStabilizerEquiv (G := G) y).symm (Quotient.mk'' (x, y)) =
      Quotient.mk'' x := by
  exact (orbitRelQuotientStabilizerEquiv (G := G) y).symm_apply_apply (Quotient.mk'' x)

/-- Move the mark back to `y` by applying the inverse translator to the object as well. -/
@[simp]
theorem orbitRelQuotientStabilizerEquiv_symm_mk_smul [MulAction.IsPretransitive G Y]
    (y : Y) (x : X) (g : G) :
    (orbitRelQuotientStabilizerEquiv (G := G) y).symm (Quotient.mk'' (x, g • y)) =
      Quotient.mk'' (g⁻¹ • x) := by
  apply (orbitRelQuotientStabilizerEquiv (G := G) y).injective
  simp only [Equiv.apply_symm_apply, orbitRelQuotientStabilizerEquiv_mk]
  exact Quotient.sound' ⟨g, by simp⟩

end TauCeti.MulAction
