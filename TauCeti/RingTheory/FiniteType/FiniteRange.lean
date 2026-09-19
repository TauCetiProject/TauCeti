/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.FiniteType.PointSeparation
public import TauCeti.RingTheory.Idempotents.Connected.Spectrum
import Mathlib.LinearAlgebra.Lagrange

/-!
# Regular functions with finite image

A regular function on a reduced connected affine scheme of finite type over an algebraically
closed field is constant if it takes only finitely many values on rational points. This permits
one to turn finiteness of an algebraic action into constancy, without constructing a morphism
to a finite constant scheme.

The argument uses Lagrange interpolation to separate one value from the others by an
idempotent, followed by point separation and connectedness.
-/

public section

namespace TauCeti

open Polynomial

variable {k A : Type*} [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
  [Algebra.FiniteType k A] [IsReduced A] [ConnectedSpace (PrimeSpectrum A)]

/-- A regular function with finite image on rational points of a reduced connected affine scheme
is the constant given by its value at any chosen rational point. -/
theorem eq_algebraMap_of_finite_range_eval (a : A)
    (hfinite : (Set.range fun f : A →ₐ[k] k ↦ f a).Finite) (f₀ : A →ₐ[k] k) :
    a = algebraMap k A (f₀ a) := by
  classical
  let s := hfinite.toFinset
  have hmem (f : A →ₐ[k] k) : f a ∈ s := hfinite.mem_toFinset.mpr ⟨f, rfl⟩
  let p := Lagrange.basis s id (f₀ a)
  have heval (f : A →ₐ[k] k) :
      f (aeval a p) = if f a = f₀ a then 1 else 0 := by
    rw [← aeval_algHom_apply, aeval_def, Algebra.algebraMap_self, eval₂_id]
    split_ifs with h
    · rw [h]
      exact Lagrange.eval_basis_self (fun _ _ _ _ h ↦ h) (hmem f₀)
    · exact Lagrange.eval_basis_of_ne (s := s) (v := id) (Ne.symm h) (hmem f)
  have hidem : IsIdempotentElem (aeval a p) := by
    apply eq_of_forall_algHom_apply_eq (k := k) (K := k)
    intro f
    simp only [map_mul, heval]
    split_ifs <;> simp
  have hone : aeval a p = 1 := by
    rcases eq_zero_or_eq_one_of_isIdempotentElem hidem with h | h
    · have h₀ := heval f₀
      simp [h] at h₀
    · exact h
  apply eq_of_forall_algHom_apply_eq (k := k) (K := k)
  intro f
  have h := heval f
  rw [hone, map_one] at h
  rw [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
  by_contra hne
  simp [hne] at h

end TauCeti
