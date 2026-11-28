/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Determinant.Pencil
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Avoiding singular scalar translates

For a matrix over a field, only finitely many scalars `a` make `1 + a • g`
singular. Over a finite product of fields, one can therefore choose `a` in any infinite
subset of a common subfield so that every component of `1 + a • g` is invertible.
This permits moving a unitary matrix into the domain of the Cayley transform by a
scalar unitary matrix.
-/

public section

open Set

namespace Matrix

variable {n K L : Type*} [Fintype n] [DecidableEq n] [Field K] [Field L]

/-- Only finitely many scalars from a subfield make `1 + a • g` singular. -/
theorem finite_setOf_not_isUnit_one_add_smul (f : K →+* L) (g : Matrix n n L) :
    Set.Finite {a : K | ¬IsUnit (1 + f a • g)} := by
  refine ((finite_setOf_det_smul_add_eq_zero g 1 ⟨0, by simp⟩).preimage
    f.injective.injOn).subset fun a ha ↦ ?_
  simpa only [Set.mem_preimage, Set.mem_ofPred_eq, add_comm, isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero, not_not] using ha

/-- Over a finite product of fields, a matrix has a nonsingular scalar
translate `1 + a • g` with `a` in any infinite subset of a common subfield. The
identification with the product is algebraic; no topology is required. -/
theorem exists_isUnit_one_add_smul {S I : Type*} [CommRing S] [Finite I]
    {L : I → Type*} [∀ i, Field (L i)] (f : K →+* S)
    (e : S ≃+* ∀ i, L i) {s : Set K} (hs : s.Infinite) (g : Matrix n n S) :
    ∃ a ∈ s, IsUnit (1 + f a • g) := by
  classical
  let fi (i : I) : K →+* L i := (Pi.evalRingHom L i).comp (e.toRingHom.comp f)
  let gi (i : I) : Matrix n n (L i) :=
    g.map ((Pi.evalRingHom L i).comp e.toRingHom)
  have hbad : (⋃ i, {a : K | ¬IsUnit (1 + fi i a • gi i)}).Finite :=
    Set.finite_iUnion fun i ↦ finite_setOf_not_isUnit_one_add_smul (fi i) (gi i)
  obtain ⟨a, ha, hgood⟩ := hs.exists_notMem_finite hbad
  refine ⟨a, ha, (isUnit_iff_isUnit_det _).2 ?_⟩
  apply (MulEquiv.isUnit_map e).1
  rw [Pi.isUnit_iff]
  intro i
  have hi : IsUnit (1 + fi i a • gi i) := by
    exact not_not.mp (fun hi ↦ hgood (Set.mem_iUnion.2 ⟨i, hi⟩))
  have hmap := (isUnit_iff_isUnit_det _).1 hi
  let ei : S →+* L i := (Pi.evalRingHom L i).comp e.toRingHom
  have heval : (1 + fi i a • gi i) =
      (1 + f a • g).map ei := by
    ext j k
    by_cases h : j = k <;>
      simp [ei, fi, gi, Matrix.map_apply,
        smul_eq_mul, h]
  rw [heval] at hmap
  have hunit : IsUnit (ei (1 + f a • g).det) := by
    rw [ei.map_det]
    exact hmap
  exact hunit

end Matrix
