/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.Transvection

/-!
# Rank-one symplectic endomorphisms and their brackets

For a bilinear form `B`, write `N(v)` for the endomorphism `z ↦ B z v • v`. The bracket
of a skew-adjoint endomorphism `X` with `N(v)` is the polarization of `N` at `v` and `X v`.
Consequently, when two is nonzero, this bracket detects whether `X` annihilates `v`.
For alternating `B`, the operators `N(v)` themselves belong to the symplectic Lie algebra.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)
attribute [local instance 100] LieRing.ofAssociativeRing

/-- The polarization of the quadratic family of transvection generators at `v` and `w`. -/
def transvectionPolar {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]
    (B : BilinForm R V) (v w : V) : Module.End R V :=
  (B.flip w).smulRight v + (B.flip v).smulRight w

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {B : BilinForm R V}

/-- The infinitesimal transvection `z ↦ B z v • v`, as an element of the symplectic Lie algebra. -/
abbrev transvectionGenerator (hB : B.IsAlt) (v : V) : skewAdjointLieSubalgebra B :=
  ⟨(B.flip v).smulRight v, smulRight_flip_mem_skewAdjointSubmodule hB v⟩

/-- Polarization is the difference of three transvection generators. -/
theorem transvectionPolar_eq_smulRight_flip_sub (B : BilinForm R V) (v w : V) :
    transvectionPolar B v w = (B.flip (v + w)).smulRight (v + w) -
      (B.flip v).smulRight v - (B.flip w).smulRight w := by
  rw [smulRight_flip_add]
  unfold transvectionPolar
  abel

private theorem lie_smulRight_mixed (X : Module.End R V) (hX : X ∈ B.skewAdjointSubmodule)
    (v w : V) :
    ⁅X, (B.flip v).smulRight w⁆ =
      (B.flip (X v)).smulRight w + (B.flip v).smulRight (X w) := by
  have hsk : ∀ z, B (X z) v = -(B z (X v)) := fun z ↦ by
    simpa using (mem_skewAdjointSubmodule (B := B) X).mp hX z v
  ext z
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, mul_apply_eq_comp,
    smulRight_apply, flip_apply, map_smul, LinearMap.add_apply, hsk, neg_smul]
  abel

/-- Bracketing a transvection generator with a skew-adjoint `X` polarizes at `v` and `X v`. -/
theorem lie_smulRight_flip_eq_transvectionPolar (B : BilinForm R V) (X : Module.End R V)
    (hX : X ∈ B.skewAdjointSubmodule) (v : V) :
    ⁅X, (B.flip v).smulRight v⁆ = transvectionPolar B v (X v) :=
  lie_smulRight_mixed X hX v v

/-- The double bracket acts by terms of total degree two in the skew-adjoint map `X`. -/
theorem lie_lie_smulRight_flip_apply (X : Module.End R V) (hX : X ∈ B.skewAdjointSubmodule)
    (v z : V) :
    ⁅X, ⁅X, (B.flip v).smulRight v⁆⁆ z =
      B z (X (X v)) • v + B z (X v) • X v + (B z (X v) • X v + B z v • X (X v)) := by
  simp only [lie_smulRight_mixed X hX, lie_add, LinearMap.add_apply, smulRight_apply, flip_apply]

/-- When `X²` annihilates `v`, the double bracket is twice the generator at `X v`. -/
theorem lie_lie_smulRight_flip_of_apply_apply_eq_zero (X : Module.End R V)
    (hX : X ∈ B.skewAdjointSubmodule) (v : V) (hv : X (X v) = 0) :
    ⁅X, ⁅X, (B.flip v).smulRight v⁆⁆ = (2 : R) • (B.flip (X v)).smulRight (X v) := by
  ext z
  simp [lie_lie_smulRight_flip_apply X hX, hv, two_smul]

/-- The double bracket with the infinitesimal transvection at `v` is a multiple of it. -/
theorem lie_lie_smulRight_flip_eq_smul {v : V} (hv : B v v = 0) (Y : Module.End R V) :
    ⁅(B.flip v).smulRight v, ⁅(B.flip v).smulRight v, Y⁆⁆ =
      (-(2 : R) * B (Y v) v) • (B.flip v).smulRight v := by
  ext z
  simp only [LieRing.of_associative_ring_bracket, mul_apply_eq_comp, LinearMap.sub_apply,
    smulRight_apply, flip_apply, map_sub, map_smul, hv, smul_zero, zero_smul,
    zero_sub, map_zero, sub_zero, LinearMap.smul_apply]
  module

variable [IsDomain R] [Module.IsTorsionFree R V] [NeZero (2 : R)]

/-- If pairing with `v` is nonzero, the polarized rank-one operator determines its other input. -/
theorem transvectionPolar_injective {v : V} (hv : B.flip v ≠ 0) :
    Function.Injective (transvectionPolar B v) := by
  obtain ⟨z, hz⟩ : ∃ z, B z v ≠ 0 := by
    by_contra! hall
    exact hv (LinearMap.ext hall)
  intro w w' hw
  have h : B z w • v + B z v • w = B z w' • v + B z v • w' := LinearMap.congr_fun hw z
  have hh := congrArg (B z) h
  simp only [map_add, map_smul, smul_eq_mul] at hh
  have he : B z w = B z w' := by
    apply mul_left_cancel₀ (mul_ne_zero (NeZero.ne (2 : R)) hz)
    linear_combination hh
  rw [he] at h
  exact smul_right_injective V hz (add_left_cancel h)

/-- A skew-adjoint operator commutes with the generator at `v` exactly when it annihilates `v`,
provided the functional `B(·,v)` is nonzero. -/
theorem lie_smulRight_flip_eq_zero_iff {v : V} (hv : B.flip v ≠ 0)
    (X : Module.End R V) (hX : X ∈ B.skewAdjointSubmodule) :
    ⁅X, (B.flip v).smulRight v⁆ = 0 ↔ X v = 0 := by
  rw [lie_smulRight_flip_eq_transvectionPolar B X hX]
  have hzero : transvectionPolar B v 0 = 0 := by ext z; simp [transvectionPolar]
  rw [← hzero]
  exact (transvectionPolar_injective hv).eq_iff

end LinearMap.BilinForm
