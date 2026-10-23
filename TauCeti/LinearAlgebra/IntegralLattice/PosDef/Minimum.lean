/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Lattice.Nat
public import TauCeti.LinearAlgebra.IntegralLattice.Even
public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.RepresentationNumber

/-!
# The minimum and the kissing number of a positive definite lattice

The minimum of a positive definite integral lattice `L` of positive rank is the least norm of a
nonzero lattice vector,

```text
min L = min {B(x, x) | x ∈ L, x ≠ 0},
```

a positive integer, and the kissing number is the number of nonzero vectors attaining it, that is
the representation number `r_L(min L)`.

Both are defined for every integral lattice, as natural numbers: the minimum is the least natural
number that is the norm of a nonzero lattice vector, and it is `0` when there is none, which for a
positive definite lattice happens exactly in rank zero; the kissing number is the cardinality of
the set of nonzero vectors of norm `min L`, so that it is `0` in rank zero. For a positive definite
lattice that set is finite and the kissing number is a genuine count; for a lattice whose minimal
shell is infinite it is `0`, as for `representationNumber`. The attainment and order properties of
the minimum need only that norms are nonnegative, and are stated for positive semidefinite lattices:
the minimum of a nontrivial positive semidefinite lattice is attained and bounds every nonzero norm
from below, so it is the least element of the set of norms of nonzero vectors, which is the form in
which a stored minimum is certified. Positive definiteness enters where it is needed: the minimum
of a nontrivial positive definite lattice is positive, and its kissing number is a positive count
of a finite shell.

An even positive definite lattice has minimum at least `2`, and its minimum is exactly `2` as soon
as it has a root, a vector of norm `2`. Minimum and kissing number are isometry invariants.

## Main declarations

* `TauCeti.IntegralLattice.minimum`: the minimum `min L`.
* `TauCeti.IntegralLattice.IsPosSemidef.isLeast_minimum`: for a nontrivial positive semidefinite
  lattice the minimum is the least norm of a nonzero vector.
* `TauCeti.IntegralLattice.IsPosDef.minimum_pos` and
  `TauCeti.IntegralLattice.IsPosDef.minimum_eq_zero_iff`: the minimum of a positive definite
  lattice vanishes exactly in rank zero.
* `TauCeti.IntegralLattice.IsPosSemidef.vectorsOfNorm_eq_empty_of_lt_minimum`: no nonzero norm
  below the minimum is represented.
* `TauCeti.IntegralLattice.IsPosDef.two_le_minimum` and
  `TauCeti.IntegralLattice.IsPosDef.minimum_eq_two`: the minimum of an even positive definite
  lattice is at least `2`, and equals `2` when the lattice has a root.
* `TauCeti.IntegralLattice.kissingNumber`: the number of nonzero minimal vectors, with
  `TauCeti.IntegralLattice.kissingNumber_eq_representationNumber`,
  `TauCeti.IntegralLattice.kissingNumber_eq_zero_of_subsingleton` and
  `TauCeti.IntegralLattice.IsPosDef.kissingNumber_pos`.
* `TauCeti.IntegralLattice.Isometry.minimum_eq` and
  `TauCeti.IntegralLattice.Isometry.kissingNumber_eq`: isometry invariance.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 1, §§1.1–1.2.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section

namespace TauCeti

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℚ V]
variable {W : Type v} [AddCommGroup W] [Module ℚ W]

namespace IntegralLattice

/-- The minimum `min L` of an integral lattice: the least natural number that is the integral norm
of a nonzero lattice vector, and `0` if there is none. For a positive definite lattice of positive
rank this is the least norm of a nonzero vector, and it is positive. -/
noncomputable def minimum (L : IntegralLattice V) : ℕ :=
  sInf {k : ℕ | ∃ x : L, x ≠ 0 ∧ L.integralNorm x = k}

/-- The minimum is the infimum of the natural numbers that are norms of nonzero lattice
vectors. -/
theorem minimum_def (L : IntegralLattice V) :
    L.minimum = sInf {k : ℕ | ∃ x : L, x ≠ 0 ∧ L.integralNorm x = k} :=
  (rfl)

variable {L : IntegralLattice V}

/-- In rank zero there is no nonzero vector, so the minimum is `0`. -/
@[simp]
theorem minimum_eq_zero_of_subsingleton [Subsingleton L] : L.minimum = 0 := by
  refine Nat.sInf_eq_zero.mpr (Or.inr (Set.eq_empty_of_forall_notMem ?_))
  rintro k ⟨x, hx, -⟩
  exact hx (Subsingleton.elim x 0)

/-! ## Positive semidefinite lattices -/

/-- In a nontrivial positive semidefinite lattice the minimum is the norm of some nonzero
vector. -/
theorem IsPosSemidef.exists_ne_zero_integralNorm_eq_minimum (hL : L.IsPosSemidef) [Nontrivial L] :
    ∃ x : L, x ≠ 0 ∧ L.integralNorm x = L.minimum := by
  obtain ⟨x, hx⟩ := exists_ne (0 : L)
  have hmem : (L.integralNorm x).toNat ∈ {k : ℕ | ∃ x : L, x ≠ 0 ∧ L.integralNorm x = k} :=
    ⟨x, hx, (Int.toNat_of_nonneg (hL.integralNorm_nonneg x)).symm⟩
  exact Nat.sInf_mem ⟨_, hmem⟩

/-- In a positive semidefinite lattice the minimum bounds the norm of every nonzero vector from
below. -/
theorem IsPosSemidef.minimum_le_integralNorm (hL : L.IsPosSemidef) {x : L} (hx : x ≠ 0) :
    (L.minimum : ℤ) ≤ L.integralNorm x := by
  have hnonneg := hL.integralNorm_nonneg x
  have hmem : (L.integralNorm x).toNat ∈ {k : ℕ | ∃ x : L, x ≠ 0 ∧ L.integralNorm x = k} :=
    ⟨x, hx, (Int.toNat_of_nonneg hnonneg).symm⟩
  have := Nat.sInf_le hmem
  rw [← Int.toNat_of_nonneg hnonneg]
  exact_mod_cast this

/-- **The minimum of a nontrivial positive semidefinite lattice is the least norm of a nonzero
vector.** -/
theorem IsPosSemidef.isLeast_minimum (hL : L.IsPosSemidef) [Nontrivial L] :
    IsLeast {k : ℤ | ∃ x : L, x ≠ 0 ∧ L.integralNorm x = k} (L.minimum : ℤ) := by
  refine ⟨?_, fun k ⟨x, hx, hk⟩ ↦ hk ▸ hL.minimum_le_integralNorm hx⟩
  obtain ⟨x, hx, hmin⟩ := hL.exists_ne_zero_integralNorm_eq_minimum
  exact ⟨x, hx, hmin⟩

/-- In a nontrivial positive semidefinite lattice the shell of the minimum is nonempty. -/
theorem IsPosSemidef.nonempty_vectorsOfNorm_minimum (hL : L.IsPosSemidef) [Nontrivial L] :
    (L.vectorsOfNorm L.minimum).Nonempty := by
  obtain ⟨x, -, hmin⟩ := hL.exists_ne_zero_integralNorm_eq_minimum
  exact ⟨x, (L.mem_vectorsOfNorm_natCast).mpr hmin⟩

/-- A positive semidefinite lattice represents no nonzero number below its minimum. -/
theorem IsPosSemidef.vectorsOfNorm_eq_empty_of_lt_minimum (hL : L.IsPosSemidef) {n : ℚ}
    (hn₀ : n ≠ 0) (hn : n < L.minimum) : L.vectorsOfNorm n = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun x hx ↦ ?_
  rw [mem_vectorsOfNorm] at hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hn₀ (by simpa using hx.symm)
  have hle : ((L.minimum : ℤ) : ℚ) ≤ L.norm x := by
    rw [← L.integralNorm_cast x]
    exact_mod_cast hL.minimum_le_integralNorm hx0
  rw [hx, Int.cast_natCast] at hle
  exact absurd hn (not_lt.mpr hle)

/-! ## Positive definite lattices -/

/-- The minimum of a nontrivial positive definite lattice is positive. -/
theorem IsPosDef.minimum_pos (hL : L.IsPosDef) [Nontrivial L] : 0 < L.minimum := by
  obtain ⟨x, hx, hmin⟩ := hL.isPosSemidef.exists_ne_zero_integralNorm_eq_minimum
  have := hL.posDef_integralNorm x hx
  rw [hmin] at this
  exact_mod_cast this

/-- The minimum of a positive definite lattice vanishes exactly when the lattice has rank zero. -/
theorem IsPosDef.minimum_eq_zero_iff (hL : L.IsPosDef) : L.minimum = 0 ↔ Subsingleton L := by
  refine ⟨fun h ↦ ?_, fun _ ↦ minimum_eq_zero_of_subsingleton⟩
  by_contra hns
  have : Nontrivial L := not_subsingleton_iff_nontrivial.mp hns
  exact (hL.minimum_pos).ne' h

/-! ## Even lattices -/

/-- The minimum of a nontrivial even positive definite lattice is at least `2`. -/
theorem IsPosDef.two_le_minimum (hL : L.IsPosDef) (he : L.IsEven) [Nontrivial L] :
    2 ≤ L.minimum := by
  obtain ⟨x, hx, hmin⟩ := hL.isPosSemidef.exists_ne_zero_integralNorm_eq_minimum
  have hpos := hL.posDef_integralNorm x hx
  obtain ⟨r, hr⟩ := (L.even_integralNorm_iff x).mpr (he.exists_norm_eq_two_mul x)
  have h2 : (2 : ℤ) ≤ L.minimum := by
    rw [← hmin]
    omega
  exact_mod_cast h2

/-- **An even positive definite lattice with a root has minimum `2`.** A root is a lattice vector
of norm `2`. -/
theorem IsPosDef.minimum_eq_two (hL : L.IsPosDef) (he : L.IsEven) {x : L}
    (hx : L.integralNorm x = 2) : L.minimum = 2 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have : Nontrivial L := nontrivial_of_ne x 0 hx0
  have hle : (L.minimum : ℤ) ≤ 2 := hx ▸ hL.isPosSemidef.minimum_le_integralNorm hx0
  have hge := hL.two_le_minimum he
  omega

/-! ## The kissing number -/

/-- The kissing number of an integral lattice: the number of nonzero vectors of norm `min L`. For a
positive definite lattice the minimal shell is finite, so this is a genuine count; on an infinite
minimal shell it is `0`. When the minimum is nonzero, in particular for a positive definite lattice
of positive rank, this is the representation number `r_L(min L)`
(`kissingNumber_eq_representationNumber`); in rank zero it is `0`
(`kissingNumber_eq_zero_of_subsingleton`), the zero vector not being a minimal vector. -/
noncomputable def kissingNumber (L : IntegralLattice V) : ℕ :=
  (L.vectorsOfNorm L.minimum \ {0}).ncard

/-- The kissing number is the cardinality of the set of nonzero vectors in the shell of the
minimum, which is `0` when that set is infinite. -/
theorem kissingNumber_def (L : IntegralLattice V) :
    L.kissingNumber = (L.vectorsOfNorm L.minimum \ {0}).ncard :=
  (rfl)

/-- In rank zero there is no nonzero vector, so the kissing number is `0`. -/
@[simp]
theorem kissingNumber_eq_zero_of_subsingleton [Subsingleton L] : L.kissingNumber = 0 := by
  rw [kissingNumber_def, minimum_eq_zero_of_subsingleton, Nat.cast_zero,
    vectorsOfNorm_zero_of_subsingleton, sdiff_self, Set.bot_eq_empty, Set.ncard_empty]

/-- When the minimum is nonzero, the kissing number is the representation number of the
minimum. -/
theorem kissingNumber_eq_representationNumber (h : L.minimum ≠ 0) :
    L.kissingNumber = L.representationNumber L.minimum := by
  rw [kissingNumber_def, representationNumber_def, Set.sdiff_singleton_eq_self]
  simp only [mem_vectorsOfNorm, Submodule.coe_zero, norm_zero]
  exact_mod_cast h.symm

/-- A nontrivial positive definite lattice has a positive kissing number. -/
theorem IsPosDef.kissingNumber_pos (hL : L.IsPosDef) [Nontrivial L] : 0 < L.kissingNumber := by
  rw [kissingNumber_def, Set.ncard_pos (hL.finite_vectorsOfNorm _).sdiff]
  obtain ⟨x, hx, hmin⟩ := hL.isPosSemidef.exists_ne_zero_integralNorm_eq_minimum
  exact ⟨x, (L.mem_vectorsOfNorm_natCast).mpr hmin, hx⟩

/-! ## Isometry invariance -/

namespace Isometry

variable {M : IntegralLattice W}

/-- The minimum is an isometry invariant. -/
theorem minimum_eq (e : Isometry L M) : L.minimum = M.minimum := by
  rw [minimum_def, minimum_def]
  congr 1
  ext k
  constructor
  · rintro ⟨x, hx, hk⟩
    refine ⟨e.carrierEquiv x, e.carrierEquiv.map_ne_zero_iff.mpr hx, ?_⟩
    rw [e.integralNorm_carrierEquiv]
    exact hk
  · rintro ⟨y, hy, hk⟩
    refine ⟨e.carrierEquiv.symm y, e.carrierEquiv.symm.map_ne_zero_iff.mpr hy, ?_⟩
    rw [← e.integralNorm_carrierEquiv, e.carrierEquiv.apply_symm_apply]
    exact hk

/-- The kissing number is an isometry invariant. -/
theorem kissingNumber_eq (e : Isometry L M) : L.kissingNumber = M.kissingNumber := by
  rw [kissingNumber_def, kissingNumber_def, e.minimum_eq, ← e.carrierEquiv_image_vectorsOfNorm,
    ← Set.ncard_image_of_injective _ e.carrierEquiv.injective,
    Set.image_sdiff e.carrierEquiv.injective, Set.image_singleton, map_zero]

end Isometry

end IntegralLattice

end TauCeti
