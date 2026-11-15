/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.NormTwoShell.FullCartan.Basic
public import Mathlib.Algebra.Lie.Solvable

/-!
# The derived algebra of the full-Cartan signed shell algebra

The full Cartan lattice need not split integrally into central and coroot summands.
Nevertheless every integral bracket lies in the image of the coroot-lattice shell algebra.
After scalar extension to a commutative ring in which two is invertible, that image is exactly
the derived algebra, provided the coordinate vectors are roots. This identifies the derived
part without choosing a central complement, and retains any additional toral directions.

The equality applies in particular over the rationals. It is not an integral equality:
in rank one, bracketing a coroot with a root vector gives twice that root vector.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§8 and 19.
* J. C. Jantzen, *Representations of Algebraic Groups*, Part II, Chapter 1.
-/

public section

open scoped TensorProduct

namespace Matrix.FullShellLieAlgebra

variable {I : Type*} [Fintype I] [LinearOrder I]
variable {B : Matrix I I ℤ} {Y : Type*} [AddCommGroup Y]
variable (D : ShellCartanDatum B Y)

/-- Every integral bracket lies in the image of the coroot-lattice shell algebra. -/
theorem lie_mem_range_toFull (x y : FullShellLieAlgebra D) :
    ⁅x, y⁆ ∈ LinearMap.range (toFull D) := by
  let S := LinearMap.range (toFull D)
  have hr (a : B.normTwoShell) : root D a ∈ S := ⟨_, toFull_root D a⟩
  have hb (a b : B.normTwoShell) : rootBracket D a b ∈ S :=
    ⟨ShellLieAlgebra.rootBracket B a b, toFull_rootBracket D a b⟩
  -- Vanishing in the quotient can be checked on the Cartan and root generators in each slot.
  have h : (bracketBilin D).compr₂ S.mkQ = 0 := by
    refine linearMap_ext (fun y ↦ linearMap_ext (fun z ↦ ?_) fun b ↦ ?_)
      fun a ↦ linearMap_ext (fun z ↦ ?_) fun b ↦ ?_ <;>
      simp only [LinearMap.compr₂_apply, bracketBilin_apply_apply, LinearMap.zero_apply]
    · simp
    · exact (Submodule.Quotient.mk_eq_zero S).2 (by
        simpa only [cartan_lie_root] using S.smul_mem _ (hr b))
    · exact (Submodule.Quotient.mk_eq_zero S).2 (by
        simpa only [root_lie_cartan] using S.neg_mem (S.smul_mem _ (hr a)))
    · exact (Submodule.Quotient.mk_eq_zero S).2 (by
        simpa only [root_lie_root] using hb a b)
  exact (Submodule.Quotient.mk_eq_zero S).1 (congr($h x y))

section ScalarExtension

variable (hB : B.PosDef) (heven : ∀ i, Even (B i i))

variable (R : Type*) [CommRing R]

/-- After any scalar extension, the derived algebra is contained in the image of the
coroot-lattice shell algebra. No flatness or invertibility assumption is needed. -/
theorem derivedSeries_one_le_range_toFull_baseChange :
    letI := lieRing D hB heven
    (LieAlgebra.derivedSeries R (R ⊗[ℤ] FullShellLieAlgebra D) 1).toSubmodule ≤
      LinearMap.range ((toFull D).baseChange R) := by
  let := lieRing D hB heven
  have h : (LieAlgebra.derivedSeries ℤ (FullShellLieAlgebra D) 1).toSubmodule ≤
      LinearMap.range (toFull D) := by
    rw [← LieIdeal.toLieSubalgebra_toSubmodule, LieAlgebra.coe_derivedSeries_one_eq]
    exact Submodule.span_le.mpr fun _ ⟨x, y, hxy⟩ ↦ hxy ▸ lie_mem_range_toFull D x y
  rw [LieAlgebra.derivedSeries_baseChange, LieSubmodule.coe_baseChange]
  refine (Submodule.baseChange_mono R h).trans ?_
  rw [Submodule.baseChange_eq_span]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
  exact ⟨(1 : R) ⊗ₜ[ℤ] z, by simp⟩

/-- Every root vector belongs to the derived algebra after extension to a ring in which two
is invertible: its bracket with its own coroot is twice itself. -/
theorem tmul_root_mem_derivedSeries_one [Invertible (2 : R)] (a : B.normTwoShell) :
    letI := lieRing D hB heven
    (1 : R) ⊗ₜ[ℤ] root D a ∈ LieAlgebra.derivedSeries R (R ⊗[ℤ] FullShellLieAlgebra D) 1 := by
  let := lieRing D hB heven
  have h := LieSubmodule.lie_mem_lie
    (I := (⊤ : LieIdeal R (R ⊗[ℤ] FullShellLieAlgebra D)))
    (N := (⊤ : LieIdeal R (R ⊗[ℤ] FullShellLieAlgebra D)))
    (x := (⅟ (2 : R)) ⊗ₜ[ℤ] cartan D (D.coroot a))
    (m := (1 : R) ⊗ₜ[ℤ] root D a) (by trivial) (by trivial)
  have heq : ⁅(⅟ (2 : R)) ⊗ₜ[ℤ] cartan D (D.coroot a), (1 : R) ⊗ₜ[ℤ] root D a⁆ =
      (1 : R) ⊗ₜ[ℤ] root D a := by
    simp only [LieAlgebra.ExtendScalars.bracket_tmul, mul_one, cartan_lie_root,
      D.weight_coroot, mem_normTwoShell.mp a.property, two_smul ℤ,
      TensorProduct.tmul_add, ← TensorProduct.add_tmul]
    congr 1
    simpa only [two_mul] using mul_invOf_self (2 : R)
  rw [heq] at h
  exact h

/-- For every root `a`, the coroot `1 ⊗ cartan (coroot a)` lies in the derived algebra after
any scalar extension; neither two invertible nor `B i i = 2` is needed. -/
theorem tmul_cartan_coroot_mem_derivedSeries_one (a : B.normTwoShell) :
    letI := lieRing D hB heven
    (1 : R) ⊗ₜ[ℤ] cartan D (D.coroot a) ∈
      LieAlgebra.derivedSeries R (R ⊗[ℤ] FullShellLieAlgebra D) 1 := by
  let := lieRing D hB heven
  let b : B.normTwoShell := ⟨-(a : I → ℤ), neg_mem_normTwoShell.mpr a.property⟩
  let u := (B.orderedSignForm a b).negOnePow
  have h := LieSubmodule.lie_mem_lie
    (I := (⊤ : LieIdeal R (R ⊗[ℤ] FullShellLieAlgebra D)))
    (N := (⊤ : LieIdeal R (R ⊗[ℤ] FullShellLieAlgebra D)))
    (x := (1 : R) ⊗ₜ[ℤ] root D a) (m := (1 : R) ⊗ₜ[ℤ] root D b)
    (by trivial) (by trivial)
  have heq : ⁅(1 : R) ⊗ₜ[ℤ] root D a, (1 : R) ⊗ₜ[ℤ] root D b⁆ =
      u • ((1 : R) ⊗ₜ[ℤ] cartan D (D.coroot a)) := by
    simp [rootBracket_of_add_eq_zero (a := a) (b := b) (by simp [b]), u,
      Units.smul_def, TensorProduct.tmul_smul]
  rw [heq] at h
  exact ((LieAlgebra.derivedSeries R (R ⊗[ℤ] FullShellLieAlgebra D) 1).toSubmodule.smul_mem_iff'
    u).mp h

/-- If every coordinate vector is a root, the derived algebra after scalar extension with two
invertible is exactly the image of the coroot-lattice shell algebra. No integral splitting of
the full Cartan lattice is assumed. -/
theorem derivedSeries_one_eq_range_toFull_baseChange [Invertible (2 : R)]
    (hdiag : ∀ i, B i i = 2) :
    letI := lieRing D hB heven
    (LieAlgebra.derivedSeries R (R ⊗[ℤ] FullShellLieAlgebra D) 1).toSubmodule =
      LinearMap.range ((toFull D).baseChange R) := by
  let := lieRing D hB heven
  apply le_antisymm (derivedSeries_one_le_range_toFull_baseChange D hB heven R)
  let P := (LieAlgebra.derivedSeries R (R ⊗[ℤ] FullShellLieAlgebra D) 1).toSubmodule
  -- The coroot-lattice basis consists of simple coroots and all root vectors.
  have h (x : ShellLieAlgebra B) : (1 : R) ⊗ₜ[ℤ] toFull D x ∈ P := by
    have hx : x ∈ Submodule.span ℤ (Set.range (ShellLieAlgebra.basis B)) := by
      rw [(ShellLieAlgebra.basis B).span_eq]
      trivial
    refine Submodule.span_induction (p := fun x _ ↦ (1 : R) ⊗ₜ[ℤ] toFull D x ∈ P)
      ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩
      rcases i with i | a
      · rw [ShellLieAlgebra.basis_inl, toFull_cartan]
        exact tmul_cartan_coroot_mem_derivedSeries_one D hB heven R
          ⟨_, single_mem_normTwoShell (hdiag i)⟩
      · rw [ShellLieAlgebra.basis_inr, toFull_root]
        exact tmul_root_mem_derivedSeries_one D hB heven R a
    · simp
    · intro x y _ _ hx hy
      simpa only [map_add, TensorProduct.tmul_add] using P.add_mem hx hy
    · intro n x _ hx
      simpa only [map_smul, TensorProduct.tmul_smul] using P.smul_of_tower_mem n hx
  rintro _ ⟨x, rfl⟩
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    rw [map_add]
    exact P.add_mem hx hy
  | tmul r x =>
    simpa only [LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      using P.smul_mem r (h x)

end ScalarExtension

end Matrix.FullShellLieAlgebra
