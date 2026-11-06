/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Darboux.Basis
public import TauCeti.LinearAlgebra.BilinearMap.Multilinear
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Pow
import TauCeti.LinearAlgebra.Basis.Fin
import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# The volume criterion for nondegeneracy of a two-form

Let `ω` be a real alternating two-form on a vector space `V` of dimension `2 * n`. Then `ω` is
nondegenerate exactly when its top wedge power `ωⁿ` is nonzero
(`ContinuousAlternatingMap.wedgePow_ne_zero_iff_nondegenerate`).

If `ω` is nondegenerate, a Darboux basis `(q₁, p₁, …, qₙ, pₙ)` exists, and `ωⁿ` takes the value
`n!` on it (`ContinuousAlternatingMap.wedgePow_apply_finProdFinEquiv`). Conversely, a nonzero
vector `v` with `ω (v, ·) = 0` is a kernel vector of `ωⁿ`
(`ContinuousAlternatingMap.wedgePow_succ_apply_vecCons_eq_zero`), so `ωⁿ` vanishes on every basis
beginning with `v`, and a top-degree form vanishing on one basis is zero.

This is the linear algebra behind the description of symplectic forms on a `2n`-dimensional
manifold as the closed two-forms `ω` with `ωⁿ` nowhere zero, and behind the analogous description
of contact forms `α` on a `(2n + 1)`-dimensional manifold by the nonvanishing of `α ∧ (dα)ⁿ`.

## Main results

* `ContinuousAlternatingMap.wedgePow_ne_zero_iff_nondegenerate`: in dimension `2 * n`, a two-form
  is nondegenerate exactly when its `n`-th wedge power is nonzero.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Chapter 1 (nondegeneracy of `ω` as nonvanishing of `ωⁿ`).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Chapter 3 (the volume form `ωⁿ / n!`).
-/

public section

open Module TauCeti

namespace ContinuousAlternatingMap

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [FiniteDimensional ℝ V]

/-- **The volume criterion for nondegeneracy.** On a real vector space of dimension `2 * n`, an
alternating two-form `ω` is nondegenerate exactly when its `n`-th wedge power `ωⁿ` is nonzero. -/
theorem wedgePow_ne_zero_iff_nondegenerate (ω : V [⋀^Fin 2]→L[ℝ] ℝ) {n : ℕ}
    (hn : finrank ℝ V = 2 * n) :
    wedgePow ω n ≠ 0 ↔ ω.toMultilinearMap.toBilinMap.Nondegenerate := by
  have hB : ω.toMultilinearMap.toBilinMap.IsAlt := ω.toAlternatingMap.isAlt_toBilinMap
  constructor
  · intro h
    rw [hB.isRefl.nondegenerate_iff_separatingLeft]
    intro v hv
    by_contra hv0
    refine h ?_
    cases n with
    | zero =>
      have : Subsingleton V := finrank_zero_iff.mp hn
      exact absurd (Subsingleton.elim v 0) hv0
    | succ m =>
      -- Complete `v` by a basis of a complementary hyperplane to a basis of `V`.
      obtain ⟨W, hW⟩ := (ℝ ∙ v).exists_isCompl
      have hvW : v ∉ W := fun hvW ↦
        hv0 (Submodule.disjoint_def.mp hW.disjoint v (Submodule.mem_span_singleton_self v) hvW)
      have hWrank : finrank ℝ W = 2 * m + 1 := by
        have := Submodule.finrank_add_eq_of_isCompl hW
        rw [finrank_span_singleton hv0] at this
        omega
      let c := Basis.mkFinConsOfNotMem v (finBasisOfFinrankEq ℝ W hWrank) hvW (by rw [hn]; ring)
      rw [← map_basis_eq_zero_iff (ι := Fin (2 * (m + 1))) _ c, Basis.coe_mkFinConsOfNotMem]
      exact wedgePow_succ_apply_vecCons_eq_zero ω m (fun w ↦ by simpa using hv w) _
  · intro h
    let σ : SymplecticForm V := ⟨_, hB, h⟩
    obtain ⟨b, hb⟩ := σ.exists_isDarbouxBasis_of_finrank_eq (n := n) (hn.trans (Nat.mul_comm 2 n))
    have hval := wedgePow_apply_finProdFinEquiv ω (m := n) b
      (fun i j ↦ by simpa [σ] using hb.apply_fst_fst i j)
      (fun i j ↦ by simpa [σ] using hb.apply_fst_snd i j)
    rw [← map_basis_ne_zero_iff _ (b.reindex (finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2))))]
    have hb' : ⇑(b.reindex (finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2)))) =
        fun r ↦ b (finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 2 n) r)) := by
      funext r
      simp only [Basis.coe_reindex, Function.comp_apply, Equiv.symm_trans_apply, finCongr_symm,
        finCongr_apply]
    rw [hb', hval]
    exact_mod_cast n.factorial_ne_zero

end ContinuousAlternatingMap
