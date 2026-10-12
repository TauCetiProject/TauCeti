/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Finite

/-!
# Shells and representation numbers of an integral lattice

The shell of norm `n` of an integral lattice `L` is the set `S_n(L)` of lattice vectors of norm
`n`, and the representation number `r_L(n)` is its cardinality:

```text
r_L(n) = #S_n(L) = #{x ∈ L | B(x, x) = n}.
```

The shells are the sets `TauCeti.IntegralLattice.vectorsOfNorm`, defined for every lattice and
every rational `n`. For a positive definite lattice every shell is finite, so its representation
numbers are genuine counts; the representation number is defined for every lattice, and takes the
value `0` on an infinite shell.

This file records the basic behaviour of these counts: the zero shell of an anisotropic lattice,
in particular of a positive definite one, is `{0}`, so `r_L(0) = 1`; negative norms are not
represented by a positive semidefinite lattice; in rank zero the zero shell is `{0}` and every
other shell is empty, so `r_L(0) = 1` and `r_L(n) = 0` for `n ≠ 0`; and an isometry carries shells
onto shells, so representation numbers are isometry invariants.

Representation numbers are the counts that the theta series of a positive definite lattice
expands; that identification is not made here.

## Main declarations

* `TauCeti.IntegralLattice.representationNumber`: the number `r_L(n)` of lattice vectors of
  norm `n`.
* `TauCeti.IntegralLattice.vectorsOfNorm_zero_of_anisotropic` and
  `TauCeti.IntegralLattice.representationNumber_zero_of_anisotropic`: the zero shell of an
  anisotropic lattice is `{0}`, so `r_L(0) = 1`.
* `TauCeti.IntegralLattice.IsPosDef.representationNumber_eq_zero_iff`: for a positive definite
  lattice, `r_L(n) = 0` exactly when the shell of norm `n` is empty.
* `TauCeti.IntegralLattice.IsPosSemidef.vectorsOfNorm_eq_empty_of_neg`: a positive semidefinite
  lattice represents no negative number.
* `TauCeti.IntegralLattice.representationNumber_zero_of_subsingleton` and
  `TauCeti.IntegralLattice.representationNumber_eq_zero_of_subsingleton`: in rank zero,
  `r_L(0) = 1` and `r_L(n) = 0` for `n ≠ 0`.
* `TauCeti.IntegralLattice.Isometry.carrierEquiv_image_vectorsOfNorm` and
  `TauCeti.IntegralLattice.Isometry.representationNumber_eq`: isometries carry shells onto shells
  and preserve representation numbers.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 2, §2.3.
* W. Ebeling, *Lattices and Codes*, Chapter 2.
-/

public section

namespace TauCeti

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℚ V]
variable {W : Type v} [AddCommGroup W] [Module ℚ W]

namespace IntegralLattice

/-- The representation number `r_L(n)` of an integral lattice: the number of lattice vectors of
norm `n`. For a positive definite lattice every shell is finite, so this is a genuine count; on an
infinite shell it is `0`. -/
noncomputable def representationNumber (L : IntegralLattice V) (n : ℚ) : ℕ :=
  (L.vectorsOfNorm n).ncard

/-- The representation number is the cardinality of the shell. -/
theorem representationNumber_def (L : IntegralLattice V) (n : ℚ) :
    L.representationNumber n = (L.vectorsOfNorm n).ncard :=
  (rfl)

/-! ## Shells of an anisotropic lattice -/

variable {L : IntegralLattice V}

/-- The norm-zero shell of an anisotropic lattice consists of the zero vector alone. For a positive
definite lattice `hL`, the hypothesis is `hL.anisotropic`. -/
theorem vectorsOfNorm_zero_of_anisotropic (hL : L.norm.Anisotropic) :
    L.vectorsOfNorm 0 = {0} := by
  ext x
  simp only [mem_vectorsOfNorm, Set.mem_singleton_iff]
  constructor
  · intro hx
    exact Submodule.coe_eq_zero.mp (hL (x : V) hx)
  · rintro rfl
    simp

/-- An anisotropic lattice represents `0` exactly once: `r_L(0) = 1`. -/
theorem representationNumber_zero_of_anisotropic (hL : L.norm.Anisotropic) :
    L.representationNumber 0 = 1 := by
  rw [representationNumber_def, vectorsOfNorm_zero_of_anisotropic hL, Set.ncard_singleton]

/-- For a positive definite lattice, whose shells are finite, the representation number of `n`
vanishes exactly when no lattice vector has norm `n`. -/
theorem IsPosDef.representationNumber_eq_zero_iff (hL : L.IsPosDef) {n : ℚ} :
    L.representationNumber n = 0 ↔ L.vectorsOfNorm n = ∅ := by
  rw [representationNumber_def, Set.ncard_eq_zero (hL.finite_vectorsOfNorm n)]

/-- A positive semidefinite lattice has no vector of negative norm. -/
theorem IsPosSemidef.vectorsOfNorm_eq_empty_of_neg (hL : L.IsPosSemidef) {n : ℚ} (hn : n < 0) :
    L.vectorsOfNorm n = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun x hx ↦ ?_
  rw [mem_vectorsOfNorm, norm_apply] at hx
  exact absurd (hx ▸ (L.isPosSemidef_iff.mp hL) (x : V)) (not_le.mpr hn)

/-- A positive semidefinite lattice represents no negative number. -/
theorem IsPosSemidef.representationNumber_eq_zero_of_neg (hL : L.IsPosSemidef) {n : ℚ}
    (hn : n < 0) : L.representationNumber n = 0 := by
  rw [representationNumber_def, hL.vectorsOfNorm_eq_empty_of_neg hn, Set.ncard_empty]

/-! ## Shells in rank zero -/

/-- In rank zero the norm-zero shell is `{0}`. -/
@[simp]
theorem vectorsOfNorm_zero_of_subsingleton [Subsingleton L] : L.vectorsOfNorm 0 = {0} := by
  ext x
  simp only [mem_vectorsOfNorm, Set.mem_singleton_iff]
  constructor
  · intro _
    exact Subsingleton.elim x 0
  · rintro rfl
    simp

/-- In rank zero every shell of nonzero norm is empty. -/
@[simp]
theorem vectorsOfNorm_eq_empty_of_subsingleton [Subsingleton L] {n : ℚ} (hn : n ≠ 0) :
    L.vectorsOfNorm n = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun x hx ↦ hn ?_
  rw [mem_vectorsOfNorm] at hx
  rw [← hx, Subsingleton.elim x 0]
  simp

/-- In rank zero `0` is represented exactly once: `r_L(0) = 1`. -/
@[simp]
theorem representationNumber_zero_of_subsingleton [Subsingleton L] :
    L.representationNumber 0 = 1 := by
  rw [representationNumber_def, vectorsOfNorm_zero_of_subsingleton, Set.ncard_singleton]

/-- In rank zero no nonzero number is represented: `r_L(n) = 0` for `n ≠ 0`. -/
@[simp]
theorem representationNumber_eq_zero_of_subsingleton [Subsingleton L] {n : ℚ} (hn : n ≠ 0) :
    L.representationNumber n = 0 := by
  rw [representationNumber_def, vectorsOfNorm_eq_empty_of_subsingleton hn, Set.ncard_empty]

/-! ## Isometry invariance -/

namespace Isometry

variable {M : IntegralLattice W}

/-- An isometry carries each shell of the source onto the shell of the same norm of the target. -/
theorem carrierEquiv_image_vectorsOfNorm (e : Isometry L M) (n : ℚ) :
    e.carrierEquiv '' L.vectorsOfNorm n = M.vectorsOfNorm n := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (e.carrierEquiv_mem_vectorsOfNorm_iff x n).mpr hx
  · intro hy
    refine ⟨e.carrierEquiv.symm y, ?_, e.carrierEquiv.apply_symm_apply y⟩
    rw [← e.carrierEquiv_mem_vectorsOfNorm_iff, e.carrierEquiv.apply_symm_apply]
    exact hy

/-- Representation numbers are isometry invariants. -/
theorem representationNumber_eq (e : Isometry L M) (n : ℚ) :
    L.representationNumber n = M.representationNumber n := by
  rw [representationNumber_def, representationNumber_def, ← e.carrierEquiv_image_vectorsOfNorm,
    Set.ncard_image_of_injective _ e.carrierEquiv.injective]

end Isometry

end IntegralLattice

end TauCeti
