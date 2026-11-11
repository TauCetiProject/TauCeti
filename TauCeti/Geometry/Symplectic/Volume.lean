/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Pow
import TauCeti.Geometry.Symplectic.ContinuousAlternatingMap
import TauCeti.Geometry.Symplectic.Darboux.Basis
import TauCeti.LinearAlgebra.Alternating.TopDegree
import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# The top power of a linear two-form

A real two-form `ω` on a vector space `E` of dimension `2 n` is nondegenerate exactly when its top
wedge power `ωⁿ` is nonzero (`ContinuousAlternatingMap.wedgePow_ne_zero_iff`). Nondegeneracy is
stated elementwise: the only vector `v` with `ω(v, w) = 0` for every `w` is zero.

If `ω` is nondegenerate, a Darboux basis `(q₁, p₁, …, qₙ, pₙ)` exists and `ωⁿ` takes the value
`n!` on it. Conversely, if `ι_v ω = 0` for a nonzero vector `v`, then the power rule
`ι_v (ωⁿ) = n (ι_v ω ∧ ωⁿ⁻¹)` gives `ι_v (ωⁿ) = 0`, and a top-degree form with a nonzero vector in
its kernel vanishes.

This is the linear volume criterion for symplectic forms. It is the pointwise statement behind
the nonvanishing of the symplectic volume form `σⁿ / n!` of a nondegenerate two-form on a
manifold, and the step from the symplectic to the contact volume criterion.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Section 2.1 and Chapter 3 (the volume form `ωⁿ / n!`).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Chapter 1.
-/

public section

open Module

namespace ContinuousAlternatingMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [FiniteDimensional ℝ E]
  {n : ℕ}

/-- **The volume criterion for linear symplectic forms.** On a real vector space of dimension
`2 n`, a two-form `ω` is nondegenerate, in the sense that the only vector `v` with `ω(v, w) = 0`
for every `w` is zero, exactly when its top wedge power `ωⁿ` is nonzero. -/
theorem wedgePow_ne_zero_iff (hn : finrank ℝ E = 2 * n) (ω : E [⋀^Fin 2]→L[ℝ] ℝ) :
    ω.wedgePow n ≠ 0 ↔ ∀ v, (∀ w, ω ![v, w] = 0) → v = 0 := by
  constructor
  · intro h v hv
    by_contra hv₀
    cases n with
    | zero =>
      have : Subsingleton E := finrank_zero_iff.1 hn
      exact hv₀ (Subsingleton.elim v 0)
    | succ m =>
      -- `v` is a nonzero vector in the kernel of the top-degree form `ω ^ (m + 1)`.
      refine h (toAlternatingMap_injective ?_)
      refine AlternatingMap.eq_zero_of_curryLeft_eq_zero (n := 2 * m + 1) hn _ hv₀ ?_
      ext w
      rw [AlternatingMap.curryLeft_apply_apply, coe_toAlternatingMap,
        ← curryLeftTopological_apply_apply, curryLeftTopological_wedgePow_succ_eq_zero ω m hv,
        coe_zero, Pi.zero_apply, _root_.zero_apply]
  · intro h
    -- A Darboux basis for the symplectic form `ω`, on which `ω ^ n` takes the value `n!`.
    set ωs := TauCeti.SymplecticForm.ofContinuousAlternatingMap ω h
    obtain ⟨b, hb⟩ := ωs.exists_isDarbouxBasis_of_finrank_eq (hn.trans (Nat.mul_comm 2 n))
    have hval := wedgePow_apply_finProdFinEquiv ω b
      (fun i j ↦ by simpa [ωs] using hb.apply_fst_fst i j)
      (fun i j ↦ by simpa [ωs] using hb.apply_fst_snd i j)
    have hb' : ⇑(b.reindex (finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2)))) =
        fun r ↦ b (finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 2 n) r)) := by
      funext r
      simp only [Basis.coe_reindex, Function.comp_apply, Equiv.symm_trans_apply, finCongr_symm,
        finCongr_apply]
    rw [← map_basis_ne_zero_iff _ (b.reindex (finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2)))),
      hb', hval]
    exact Nat.cast_ne_zero.2 n.factorial_ne_zero

end ContinuousAlternatingMap
