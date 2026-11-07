/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Elementary linear-equivalence transport

Transport of submodule stability through an intertwining linear equivalence.
Symmetry of a linear automorphism agrees with inversion in its group structure.
A ring isomorphism over a common target carries the kernel of one map to the kernel of the other.
-/

public section

namespace LinearEquiv

/-- Symmetry of a linear automorphism is its group inverse. -/
theorem symm_eq_inv {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (e : V ≃ₗ[R] V) : e.symm = e⁻¹ := rfl

/-- Transport stability of a mapped submodule through an intertwining linear equivalence. -/
theorem mem_of_preserves_map
    {R V W : Type*} [Semiring R]
    [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
    (e : V ≃ₗ[R] W) (p : Submodule R V) (q : Submodule R W)
    (hmap : p.map e.toLinearMap = q) (f : V → V) (g : W → W)
    (hcomm : ∀ x, e (f x) = g (e x))
    (hstable : ∀ {y}, y ∈ q → g y ∈ q)
    {x : V} (hx : x ∈ p) : f x ∈ p := by
  have hex : e x ∈ q := by
    rw [← hmap]
    exact Submodule.mem_map_of_mem hx
  have hfx := hstable hex
  rw [← hcomm x, ← hmap] at hfx
  simpa only [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply] using hfx

end LinearEquiv

namespace RingEquiv

/-- A ring isomorphism over a common target carries the kernel of one map to the kernel of the
other, as a semilinear image. -/
theorem map_ker_toSemilinearEquiv {A B S : Type*} [Semiring A] [Semiring B] [Semiring S]
    (Φ : A ≃+* B) (g : A →+* S) (h : B →+* S)
    (hΦ : ∀ x, h (Φ x) = g x) :
    Submodule.map (Φ.toSemilinearEquiv : A →ₛₗ[(Φ : A →+* B)] B) (RingHom.ker g) =
      RingHom.ker h := by
  have : RingHomInvPair (Φ : A →+* B) (Φ.symm : B →+* A) := .of_ringEquiv Φ
  have : RingHomInvPair (Φ.symm : B →+* A) (Φ : A →+* B) := .of_ringEquiv_symm Φ
  ext y
  rw [Submodule.mem_map_equiv, RingHom.mem_ker, RingHom.mem_ker, ← hΦ]
  exact Iff.of_eq (congrArg (· = 0) (congrArg _ (Φ.apply_symm_apply y)))

end RingEquiv
