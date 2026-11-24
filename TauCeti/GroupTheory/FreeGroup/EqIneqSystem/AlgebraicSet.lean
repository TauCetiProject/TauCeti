/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.EqIneqSystem.Basic
public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet
import Mathlib.Data.Set.Finite.Basic

/-!
# The equations of a system over a free group as a system of algebraic geometry

Read through the coefficient letters `FreeGroup.of : A → F(A)`, the equations of a system `S` of
equations and inequations over `F(A)` form a finite set `S.eqSet` of elements of `F(A)[X]`: a
system of equations of algebraic geometry over `F(A)`. Its points in a group `H` over `F(A)` are
the solutions of the equations of `S`; the inequations of `S` do not enter. In particular every
solution of `S` is a point. The empty system has no equations, and the equations of a
concatenation of systems are those of both.

## Main definitions

* `TauCeti.EqIneqSystem.eqSet`: the equations of a system as elements of `F(A)[X]`.

## Main results

* `TauCeti.EqIneqSystem.mem_V_eqSet_iff`: the points of the equations of a system are the
  solutions of its equations.
* `TauCeti.EqIneqSystem.IsSolution.mem_V_eqSet`: a solution of a system is a point of its
  equations.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.3 (systems of equations and inequations) and §2.4 (algebraic sets and coordinate
  groups).
-/

public section

namespace TauCeti

namespace EqIneqSystem

open GroupAlgGeom

variable {X A : Type*} {S : EqIneqSystem X A}

/-- The equations of a system as elements of `F(A)[X]`: a system of equations of algebraic
geometry over `F(A)`. -/
def eqSet (S : EqIneqSystem X A) : Set (GX (FreeGroup A) X) :=
  toGX X FreeGroup.of '' {e | e ∈ S.eqs}

theorem eqSet_def (S : EqIneqSystem X A) :
    S.eqSet = toGX X FreeGroup.of '' {e | e ∈ S.eqs} :=
  (rfl)

/-- The elements of the set of equations of a system are the images in `F(A)[X]` of its
equations. -/
theorem mem_eqSet_iff {w : GX (FreeGroup A) X} :
    w ∈ S.eqSet ↔ ∃ e ∈ S.eqs, toGX X FreeGroup.of e = w :=
  Iff.rfl

/-- The image in `F(A)[X]` of an equation of a system lies in its set of equations. -/
theorem toGX_mem_eqSet {e : FreeGroup (X ⊕ A)} (he : e ∈ S.eqs) :
    toGX X FreeGroup.of e ∈ S.eqSet :=
  Set.mem_image_of_mem _ he

/-- A system has finitely many equations. -/
theorem finite_eqSet (S : EqIneqSystem X A) : S.eqSet.Finite :=
  S.eqs.finite_toSet.image _

/-- The empty system has no equations. -/
@[simp]
theorem eqSet_empty : (empty X A).eqSet = ∅ := by
  simp [eqSet]

/-- The equations of a concatenation of systems are those of both systems. -/
@[simp]
theorem eqSet_append (S T : EqIneqSystem X A) : (S.append T).eqSet = S.eqSet ∪ T.eqSet := by
  simp [eqSet, Set.ofPred_or, Set.image_union]

variable {H : Type*} [Group H] {ι : FreeGroup A →* H} {v : X → H}

/-- The points of the equations of a system in a group over `F(A)` are the solutions of its
equations. -/
theorem mem_V_eqSet_iff : v ∈ V ι S.eqSet ↔ ∀ e ∈ S.eqs, eval v (ι ∘ FreeGroup.of) e = 1 := by
  simp [eqSet, mem_V]

/-- A solution of a system in a group over `F(A)` is a point of its equations. -/
theorem IsSolution.mem_V_eqSet (h : S.IsSolution v (ι ∘ FreeGroup.of)) : v ∈ V ι S.eqSet :=
  mem_V_eqSet_iff.2 fun _ => h.eval_eq_one

/-- A solution of a system in `F(A)` is a point of its equations over `F(A)`. -/
theorem IsSolution.mem_V_id_eqSet {v : X → FreeGroup A} (h : S.IsSolution v FreeGroup.of) :
    v ∈ V (MonoidHom.id (FreeGroup A)) S.eqSet :=
  h.mem_V_eqSet

end EqIneqSystem

end TauCeti
