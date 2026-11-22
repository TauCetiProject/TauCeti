/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Quotients of `ℝ[X]` by irreducible quadratics

If `g` is an irreducible real polynomial of degree two, then `ℝ[X]⧸(g)` is a field of
dimension two over `ℝ`, so sending its generator to a complex root of `g` identifies it with `ℂ`.
Since `ℂ` is algebraically closed, every element of `ℝ[X]⧸(g)` is a square
(`AdjoinRoot.isSquare_of_irreducible_of_natDegree_eq_two`).

This is the archimedean input of explicit descent on elliptic curves: when a real cubic has a
single real root, its quotient algebra is `ℝ` times such a field, and square classes are detected
by the sign at the real root alone.
-/

public section

open Polynomial

namespace AdjoinRoot

/-- **Every element of `ℝ[X]⧸(g)` is a square** when `g` is an irreducible real quadratic: the
quotient is isomorphic to `ℂ`, which is algebraically closed. -/
theorem isSquare_of_irreducible_of_natDegree_eq_two {g : ℝ[X]} (hg : Irreducible g)
    (h2 : g.natDegree = 2) (b : AdjoinRoot g) : IsSquare b := by
  have := Fact.mk hg
  obtain ⟨z, hz⟩ := Complex.exists_root (f := g.map (algebraMap ℝ ℂ)) <| by
    rw [degree_map]
    exact degree_pos_of_irreducible hg
  let φ : AdjoinRoot g →ₐ[ℝ] ℂ :=
    liftAlgHom g (Algebra.ofId ℝ ℂ) z (by rwa [IsRoot, eval_map] at hz)
  have hfin : Module.finrank ℝ (AdjoinRoot g) = Module.finrank ℝ ℂ := by
    rw [(powerBasis hg.ne_zero).finrank, powerBasis_dim, h2, Complex.finrank_real_complex]
  have := (powerBasis hg.ne_zero).finite
  have hbij : Function.Bijective φ :=
    ⟨φ.toRingHom.injective, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin
      (f := φ.toLinearMap)).mp φ.toRingHom.injective⟩
  let ψ := AlgEquiv.ofBijective φ hbij
  obtain ⟨w, hw⟩ := IsAlgClosed.isSquare (ψ b)
  exact ⟨ψ.symm w, by rw [← map_mul, ← hw, AlgEquiv.symm_apply_apply]⟩

end AdjoinRoot
