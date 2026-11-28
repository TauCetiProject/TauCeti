/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Spanning by polynomial evaluation vectors

For finitely many polynomials, their value vectors on a box with infinite sides span the
coordinate space exactly when the polynomials are linearly independent. One can remove the
zero locus of any nonzero polynomial without changing this criterion. In particular, for a
polynomial basis the evaluations determine every linear map out of the coordinate space.
-/

public section

namespace MvPolynomial

open Set

/-- On a box with infinite sides, even after removing the zeros of a nonzero polynomial `g`,
the value vectors of a finite family of polynomials span if and only if the family is linearly
independent. The variable type `σ` need not be finite. -/
theorem span_range_eval_eq_top_iff {K σ ι : Type*} [Field K] [Finite ι]
    (p : ι → MvPolynomial σ K) {s : σ → Set K} (hs : ∀ i, (s i).Infinite)
    {g : MvPolynomial σ K} (hg : g ≠ 0) :
    Submodule.span K (Set.range fun x : {x ∈ pi univ s | eval x g ≠ 0} ↦
      fun i ↦ eval x.val (p i)) = ⊤ ↔ LinearIndependent K p := by
  let A := {x ∈ pi univ s | eval x g ≠ 0}
  let E : MvPolynomial σ K →ₗ[K] (A → K) :=
    LinearMap.pi fun x ↦ (aeval x.val).toLinearMap
  have hE : Function.Injective E := by
    refine LinearMap.ker_eq_bot.mp (eq_bot_iff.mpr fun f hf ↦ ?_)
    have hf' : E f = 0 := LinearMap.mem_ker.mp hf
    -- Multiplication by `g` fills in the points omitted from the box.
    have hfg : f * g = 0 := funext_set s hs fun x hx ↦ by
      rw [map_mul, map_zero]
      by_cases hxg : eval x g = 0
      · simp [hxg]
      · have hfx : eval x f = 0 := by
          simpa only [E, LinearMap.pi_apply, AlgHom.toLinearMap_apply, aeval_eq_eval, Pi.zero_apply]
            using congrFun hf' (⟨x, hx, hxg⟩ : A)
        simp [hfx]
    exact (Submodule.mem_bot K).mpr ((mul_eq_zero.mp hfg).resolve_right hg)
  exact span_flip_eq_top_iff_linearIndependent.trans
    ⟨fun hp ↦ hp.of_comp E, fun hp ↦ hp.map' E (LinearMap.ker_eq_bot.mpr hE)⟩

end MvPolynomial
