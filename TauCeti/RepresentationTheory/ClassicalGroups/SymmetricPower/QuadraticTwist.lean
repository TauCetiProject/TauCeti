/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.Topology.Algebra.Group.Matrix
public import TauCeti.RepresentationTheory.ClassicalGroups.SymmetricPower.Basic
import TauCeti.LinearAlgebra.SymmetricPower.Kernel

/-!
# Quadratic ambiguity of the symmetric square

The symmetric square of the standard action has kernel the scalar square roots of unity.
Consequently, two continuous matrix representations with the same symmetric-square action
(in fixed coordinates) differ by a unique continuous character with values in the square roots
of unity. There is no unramifiedness requirement on the character.

The rank-two application to crystalline lifts is discussed in Christopher Skinner,
*A note on the p-adic Galois representations attached to Hilbert modular forms*, §2.4.1, p. 252.
The results here concern the group representations, not their period rings.
-/

public section

open Matrix Matrix.GeneralLinearGroup

namespace TauCeti

variable {R : Type} {n : ℕ}

/-- A scalar matrix acts on the standard representation by scalar multiplication. -/
theorem stdRep_scalar [CommSemiring R] (u : Rˣ) : stdRep R n (GeneralLinearGroup.scalar (Fin n) u) =
    (u : R) • LinearMap.id := by
  ext v i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal, smul_eq_mul]

variable [CommRing R]

/-- The symmetric square acts trivially exactly on scalar matrices of square one. -/
theorem symPowerRep_two_eq_one_iff (A : GL (Fin n) R) :
    symPowerRep R n 2 A = 1 ↔
      ∃ u : rootsOfUnity 2 R, A = GeneralLinearGroup.scalar (Fin n) u.val := by
  rw [Representation.symmetricPower_apply, Module.End.one_eq_id,
    SymmetricPower.map_fin_two_eq_id_iff (Pi.basisFun R (Fin n))]
  refine ⟨?_, ?_⟩
  · rintro ⟨a, ha, hA⟩
    let u := rootsOfUnity.mkOfPowEq a ha
    refine ⟨u, stdRep_injective R n ?_⟩
    rw [hA, stdRep_scalar]
    simp [u]
  · rintro ⟨u, rfl⟩
    exact ⟨(u.val : R), (mem_rootsOfUnity' _ _).1 u.property, stdRep_scalar u.val⟩

/-- Two matrices induce the same action on the symmetric square exactly when they differ by a
scalar square root of unity. -/
theorem symPowerRep_two_eq_iff (A B : GL (Fin n) R) :
    symPowerRep R n 2 A = symPowerRep R n 2 B ↔
      ∃ u : rootsOfUnity 2 R, A = GeneralLinearGroup.scalar (Fin n) u.val * B := by
  let s := symPowerRep R n 2
  -- The image of `B` is a unit even though the codomain is an endomorphism monoid.
  have h : s A = s B ↔ s (A * B⁻¹) = 1 := by
    calc
      s A = s B ↔ s (A * B⁻¹) * s B = 1 * s B := by
        rw [← map_mul, inv_mul_cancel_right, one_mul]
      _ ↔ _ := ((Group.isUnit B).map s).mul_left_inj
  rw [h, symPowerRep_two_eq_one_iff]
  exact exists_congr fun _ => mul_inv_eq_iff_eq_mul

/-- Extending coefficients takes the scalar difference of two lifts to the image scalar. -/
theorem symPowerRep_two_map_eq_of_eq {S : Type} [CommRing S]
    (f : R →+* S) {A B : GL (Fin n) R} (h : symPowerRep R n 2 A = symPowerRep R n 2 B) :
    symPowerRep S n 2 (GeneralLinearGroup.map f A) =
      symPowerRep S n 2 (GeneralLinearGroup.map f B) := by
  obtain ⟨u, rfl⟩ := (symPowerRep_two_eq_iff A B).1 h
  refine (symPowerRep_two_eq_iff _ _).2 ⟨restrictRootsOfUnity f 2 u, ?_⟩
  simp [GeneralLinearGroup.map_scalar, restrictRootsOfUnity]

/-- A twisting scalar can be read off from any diagonal entry of the ratio of the two matrices. -/
theorem coe_eq_apply_mul_inv_of_eq_scalar_mul {A B : GL (Fin n) R} {u : Rˣ}
    (h : A = GeneralLinearGroup.scalar (Fin n) u * B) (i : Fin n) :
    (u : R) = (A * B⁻¹) i i := by
  rw [h, mul_inv_cancel_right]
  simp [Matrix.scalar_apply]

section Continuous

variable [TopologicalSpace R] [IsTopologicalSemiring R]
variable {G : Type*} [Monoid G] [TopologicalSpace G] [NeZero n]

/-- For fixed matrix coordinates, two continuous representations with equal symmetric-square
actions differ by a unique continuous character valued in the square roots of unity. -/
theorem existsUnique_quadraticTwist_of_symPowerRep_two_eq (ρ σ : G →ₜ* GL (Fin n) R)
    (h : ∀ g, symPowerRep R n 2 (σ g) = symPowerRep R n 2 (ρ g)) :
    ∃! χ : G →ₜ* rootsOfUnity 2 R, ∀ g,
      σ g = GeneralLinearGroup.scalar (Fin n) (χ g).val * ρ g := by
  let i : Fin n := 0
  let δ (g : G) := σ g * (ρ g)⁻¹
  let s := (GeneralLinearGroup.scalar (Fin n)).comp (rootsOfUnity 2 R).subtype
  have hs : ∀ u : rootsOfUnity 2 R, s u i i = ((u.val : Rˣ) : R) := by
    intro u
    simp [s, Matrix.scalar_apply]
  have hinj : Function.Injective s := by
    intro u v huv
    apply rootsOfUnity.coe_injective
    simpa only [hs] using congrArg (fun A : GL (Fin n) R => A i i) huv
  have hδ (g : G) : ∃ u : rootsOfUnity 2 R, δ g = s u := by
    obtain ⟨u, hu⟩ := (symPowerRep_two_eq_iff _ _).1 (h g)
    exact ⟨u, mul_inv_eq_iff_eq_mul.mpr hu⟩
  let χ (g : G) : rootsOfUnity 2 R := rootsOfUnity.mkOfPowEq (δ g i i) (by
    obtain ⟨u, hu⟩ := hδ g
    rw [hu, hs]
    exact (mem_rootsOfUnity' _ _).1 u.property)
  have hχ (g : G) : s (χ g) = δ g := by
    obtain ⟨u, hu⟩ := hδ g
    rw [hu]
    apply congrArg s
    apply rootsOfUnity.coe_injective
    simp only [χ, rootsOfUnity.coe_mkOfPowEq, hu, hs]
  let χhom : G →* rootsOfUnity 2 R :=
    { toFun := χ
      map_one' := hinj (by simp [hχ, δ])
      map_mul' := fun g k => hinj (by
        have hcomm : Commute (δ k) (ρ g)⁻¹ := by
          rw [← hχ k]
          exact scalar_commute (χ k).val (ρ g)⁻¹
        simpa only [map_mul, hχ, δ, _root_.mul_inv_rev, mul_assoc] using
          congrArg (σ g * ·) hcomm.eq) }
  have hval : Continuous fun g => δ g i i :=
    (_root_.continuous_apply i).comp
      (GeneralLinearGroup.continuous_apply δ (by dsimp [δ]; fun_prop) i)
  refine ⟨⟨χhom, ?_⟩, ?_, ?_⟩
  · refine Continuous.subtype_mk (Units.continuous_iff.mpr ⟨hval, ?_⟩) _
    convert hval using 1
    funext g
    have hpow := (mem_rootsOfUnity 2 (χ g).val).1 (χ g).property
    exact congrArg Units.val (inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hpow))
  · exact fun g => mul_inv_eq_iff_eq_mul.mp (hχ g).symm
  · intro ψ hψ
    apply ContinuousMonoidHom.ext
    intro g
    apply rootsOfUnity.coe_injective
    exact (coe_eq_apply_mul_inv_of_eq_scalar_mul (hψ g) i).trans
      (rootsOfUnity.coe_mkOfPowEq _).symm

end Continuous

end TauCeti
