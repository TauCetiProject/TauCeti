/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.IsPrincipal
public import Mathlib.GroupTheory.Index

/-!
# Scalar indices on nonzero principal ideals

A nonzero principal ideal in a domain is a free module of rank one. Multiplication by `c`
on its additive group therefore has cokernel of order `Nat.card (R ⧸ Ideal.span {c})`.
This computes scalar indices on small principal neighbourhoods after linearisation.
-/

public section

namespace Ideal

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Multiplication by `c` on a nonzero principal ideal has the same cokernel index as
multiplication by `c` on the ring. No finiteness assumption is needed for this identity. -/
theorem index_range_smul (I : Ideal R) [I.IsPrincipal] (hI : I ≠ ⊥) (c : R) :
    (DistribSMul.toAddMonoidHom I c).range.index = Nat.card (R ⧸ span {c}) := by
  let e := (isoBaseOfIsPrincipal hI).symm
  have hr : (DistribSMul.toAddMonoidHom I c).range.map e.toAddEquiv.toAddMonoidHom =
      (span {c}).toAddSubgroup := by
    ext z
    constructor
    · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
      exact mem_span_singleton.mpr ⟨e x, by simp [map_smul, smul_eq_mul]⟩
    · intro hz
      obtain ⟨x, rfl⟩ := mem_span_singleton.mp hz
      refine ⟨c • e.symm x, ⟨e.symm x, rfl⟩, ?_⟩
      simp [map_smul, smul_eq_mul]
  have hidx := AddSubgroup.index_map_of_bijective
    (f := e.toAddEquiv.toAddMonoidHom) e.toAddEquiv.bijective
    (DistribSMul.toAddMonoidHom I c).range
  rw [hr, AddSubgroup.index_eq_card] at hidx
  exact hidx.symm

end Ideal
