/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable

/-!
# Congruence representatives in the kernel of algebraic K₁

For a surjective ring homomorphism `f : A →+* B`, every class in the kernel of
`K₁(A) → K₁(B)` has a finite invertible matrix representative whose image is the identity.
One must first stabilize the original representative and then correct it by an elementary
matrix lifted from `B`. Neither the original matrix nor arbitrary invertible matrices over
`B` are asserted to lift.

This identifies the kernel as the supremum of the images of the finite congruence subgroups.
For a two-sided ideal, the representative is congruent to the identity entrywise modulo the
ideal. These are the representative and image statements used in the relative K₁ sequence;
they do not define the relative group as this image.

## References

* Charles Weibel, *The K-book*, Chapter III, Proposition 2.3: the elementary-lifting argument
  proving exactness at absolute K₁ in the relative sequence.
-/

public section

open Matrix

namespace RingHom

open TauCeti
open TauCeti.AlgebraicK1

variable {A B : Type*} [Ring A] [Ring B]

/-- If the image of a matrix has trivial K₁ class, an elementary correction after stabilization
makes its image the identity. The correction does not change its class over the source ring. -/
theorem exists_mem_elementarySubgroup_map_stabilizeGL_mul_inv_eq_one
    (f : A →+* B) (hf : Function.Surjective f) {n : ℕ} (u : GL (Fin n) A)
    (hu : AlgebraicK1.map f (AlgebraicK1.mk A n u) = 1) :
    ∃ k, ∃ h : n ≤ k, ∃ e ∈ elementarySubgroup (Fin k) A,
      Units.map (f.mapMatrix (m := Fin k)).toMonoidHom
        (stabilizeGL A h u * e⁻¹) = 1 := by
  rw [map_mk, mk_eq_one_iff] at hu
  obtain ⟨k, h, he⟩ := hu
  rw [stabilizeGL_map] at he
  obtain ⟨e, he, hfe⟩ :=
    f.exists_mem_elementarySubgroup_unitsMap_mapMatrix_eq hf he
  exact ⟨k, h, e, he, by rw [map_mul, map_inv, hfe, mul_inv_cancel]⟩

/-- A class killed by a surjective ring map has a finite matrix representative mapping to the
identity. Conversely, every such representative gives a class in the kernel. -/
theorem algebraicK1_map_eq_one_iff_exists_mk (f : A →+* B) (hf : Function.Surjective f)
    (x : AlgebraicK1 A) :
    AlgebraicK1.map f x = 1 ↔
      ∃ (n : ℕ) (u : GL (Fin n) A), AlgebraicK1.mk A n u = x ∧
        Units.map (f.mapMatrix (m := Fin n)).toMonoidHom u = 1 := by
  constructor
  · intro hx
    obtain ⟨n, u, rfl⟩ := exists_mk x
    obtain ⟨k, h, e, he, hfe⟩ :=
      f.exists_mem_elementarySubgroup_map_stabilizeGL_mul_inv_eq_one hf u hx
    refine ⟨k, stabilizeGL A h u * e⁻¹, ?_, hfe⟩
    have he' : AlgebraicK1.mk A k e = 1 := mk_eq_one_iff.mpr ⟨k, le_rfl, by simpa using he⟩
    simp [he']
  · rintro ⟨n, u, rfl, hu⟩
    rw [map_mk]
    exact (congrArg (AlgebraicK1.mk B n) hu).trans (map_one _)

/-- The kernel of K₁ along a surjection is the supremum of the images of the finite congruence
subgroups. This is an image description, not a definition of relative K₁. -/
theorem ker_algebraicK1_map_eq_iSup_map_ker (f : A →+* B) (hf : Function.Surjective f) :
    (AlgebraicK1.map f).ker = ⨆ n : ℕ,
      ((Units.map (f.mapMatrix (m := Fin n)).toMonoidHom).ker).map (AlgebraicK1.mk A n) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨n, u, rfl, hu⟩ := (f.algebraicK1_map_eq_one_iff_exists_mk hf x).mp hx
    exact le_iSup (fun n : ℕ ↦
      ((Units.map (f.mapMatrix (m := Fin n)).toMonoidHom).ker).map (AlgebraicK1.mk A n)) n
        ⟨u, hu, rfl⟩
  · refine iSup_le fun n ↦ ?_
    rintro x ⟨u, hu, rfl⟩
    rw [MonoidHom.mem_ker, map_mk]
    exact (congrArg (AlgebraicK1.mk B n) (MonoidHom.mem_ker.mp hu)).trans (map_one _)

end RingHom

namespace Ideal

open TauCeti
open TauCeti.AlgebraicK1

variable {A : Type*} [Ring A]

/-- Modulo a two-sided ideal, every class in the kernel has a representative congruent to the
identity entrywise. No commutativity, noetherianity, or lifting of arbitrary units is needed. -/
theorem algebraicK1_map_quotient_eq_one_iff_exists_mk (I : Ideal A) [I.IsTwoSided]
    (x : AlgebraicK1 A) :
    AlgebraicK1.map (Ideal.Quotient.mk I) x = 1 ↔
      ∃ (n : ℕ) (u : GL (Fin n) A), mk A n u = x ∧
        ∀ i j, (u : Matrix (Fin n) (Fin n) A) i j -
          (1 : Matrix (Fin n) (Fin n) A) i j ∈ I := by
  rw [RingHom.algebraicK1_map_eq_one_iff_exists_mk _ Ideal.Quotient.mk_surjective]
  refine exists_congr fun n ↦ exists_congr fun u ↦ and_congr_right fun _ ↦ ?_
  rw [Units.ext_iff, ← Matrix.ext_iff]
  refine forall₂_congr fun i j ↦ ?_
  simp only [Units.coe_map, Units.val_one, Matrix.one_apply]
  rw [← Ideal.Quotient.eq]
  simp [apply_ite (Ideal.Quotient.mk I)]

end Ideal
