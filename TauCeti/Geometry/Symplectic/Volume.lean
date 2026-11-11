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
import TauCeti.LinearAlgebra.Determinant.Prod
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

The top power of a direct sum `ω₁ ⊕ ω₂` on `E × F`, with `dim E = 2 n` and `dim F = 2 m`, takes
the value `C(n + m, n) ω₁ⁿ(v) ω₂ᵐ(w)` on a family `(vᵢ, 0)` followed by `(0, wⱼ)`
(`ContinuousAlternatingMap.wedgePow_prod_apply`). Equivalently the normalized volume forms satisfy
`(ω₁ ⊕ ω₂)ⁿ⁺ᵐ / (n + m)! = ω₁ⁿ / n! · ω₂ᵐ / m!` on such families: the symplectic volume of a
product is the product of the symplectic volumes. If both forms are nondegenerate, Darboux bases
of the summands concatenate to a Darboux basis of the sum; otherwise both sides vanish.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Section 2.1 and Chapter 3 (the volume form `ωⁿ / n!`).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Chapter 1.
-/

public section

open Module

namespace ContinuousAlternatingMap

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [FiniteDimensional ℝ F] {n m : ℕ}

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

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The direct sum `ω₁ ∘ pr₁ + ω₂ ∘ pr₂` of two two-forms evaluates componentwise. -/
private theorem add_compContinuousLinearMap_fst_snd_apply (ω₁ : E [⋀^Fin 2]→L[ℝ] ℝ)
    (ω₂ : F [⋀^Fin 2]→L[ℝ] ℝ) (x y : E × F) :
    (ω₁.compContinuousLinearMap (.fst ℝ E F) + ω₂.compContinuousLinearMap (.snd ℝ E F)) ![x, y] =
      ω₁ ![x.1, y.1] + ω₂ ![x.2, y.2] := by
  simp only [add_apply, compContinuousLinearMap_apply]
  congr 2 <;> funext i <;> fin_cases i <;> rfl

omit [FiniteDimensional ℝ E] in
/-- A two-form agreeing with a symplectic form `S` takes the value `n!` in its `n`-th power on a
Darboux basis of `S`, listed in the interleaved order `(q₁, p₁, …, qₙ, pₙ)`. -/
private theorem wedgePow_apply_reindex_of_isDarbouxBasis (ω : E [⋀^Fin 2]→L[ℝ] ℝ)
    {S : TauCeti.SymplecticForm E} (hS : ∀ x y, S x y = ω ![x, y])
    {b : Basis (Fin n × Fin 2) ℝ E} (hb : S.IsDarbouxBasis b) :
    ω.wedgePow n (b.reindex (finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2)))) =
      n.factorial := by
  convert wedgePow_apply_finProdFinEquiv ω b (fun i j ↦ (hS _ _).symm.trans (hb.apply_fst_fst i j))
    (fun i j ↦ (hS _ _).symm.trans (hb.apply_fst_snd i j)) using 2
  funext r
  simp only [Basis.coe_reindex, Function.comp_apply, Equiv.symm_trans_apply, finCongr_symm,
    finCongr_apply]

/-- If one summand of a direct sum of two-forms is degenerate, so is the sum, and its top power
vanishes. -/
private theorem wedgePow_add_compContinuousLinearMap_fst_snd_eq_zero (hn : finrank ℝ E = 2 * n)
    (hm : finrank ℝ F = 2 * m) {ω₁ : E [⋀^Fin 2]→L[ℝ] ℝ} {ω₂ : F [⋀^Fin 2]→L[ℝ] ℝ}
    (h : ¬ (∀ x, (∀ y, ω₁ ![x, y] = 0) → x = 0) ∨ ¬ (∀ x, (∀ y, ω₂ ![x, y] = 0) → x = 0)) :
    (ω₁.compContinuousLinearMap (.fst ℝ E F) + ω₂.compContinuousLinearMap (.snd ℝ E F)).wedgePow
      (n + m) = 0 := by
  have hEF : finrank ℝ (E × F) = 2 * (n + m) := by rw [finrank_prod, hn, hm, mul_add]
  refine not_not.1 fun hne ↦ ?_
  have hnd := (wedgePow_ne_zero_iff hEF _).1 hne
  rcases h with h | h <;> refine h fun x hx ↦ ?_
  · refine congr($(hnd (x, 0) fun y ↦ ?_).1)
    rw [add_compContinuousLinearMap_fst_snd_apply, hx, zero_add]
    exact ω₂.map_coord_zero 0 rfl
  · refine congr($(hnd (0, x) fun y ↦ ?_).2)
    rw [add_compContinuousLinearMap_fst_snd_apply, hx, add_zero]
    exact ω₁.map_coord_zero 0 rfl

omit [TopologicalSpace E] [FiniteDimensional ℝ E] [TopologicalSpace F] [FiniteDimensional ℝ F] in
/-- The concatenation of two interleaved Darboux-ordered bases, read in the interleaved order of
the direct sum, has block determinant on the family `(vᵢ, 0)`, `(0, wⱼ)`. -/
private theorem det_reindex_prod_sumElim (b : Basis (Fin n × Fin 2) ℝ E)
    (c : Basis (Fin m × Fin 2) ℝ F) (v : Fin (2 * n) → E) (w : Fin (2 * m) → F) :
    (((b.prod c).reindex
        ((Equiv.sumProdDistrib _ _ _).symm.trans (finSumFinEquiv.prodCongr (Equiv.refl _)))).reindex
        (finProdFinEquiv.trans (finCongr (Nat.mul_comm (n + m) 2)))).det
      (fun r ↦ Sum.elim (fun i ↦ (v i, 0)) (fun j ↦ (0, w j))
        (finSumFinEquiv.symm (Fin.cast (mul_add 2 n m) r))) =
      (b.reindex (finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2)))).det v *
        (c.reindex (finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2)))).det w := by
  rw [Basis.det_reindex, Basis.det_reindex, Basis.det_reindex, Basis.det_reindex,
    ← Basis.prod_det_sumElim]
  congr 1
  funext p
  -- Position `2 i + a` of the interleaved order lies in the first block exactly when `i < n`.
  rcases p with ⟨i, a⟩ | ⟨j, a⟩
  · have hi : Fin.cast (mul_add 2 n m) (finProdFinEquiv.trans (finCongr (Nat.mul_comm (n + m) 2))
        ((Equiv.sumProdDistrib _ _ _).symm.trans (finSumFinEquiv.prodCongr (Equiv.refl _))
          (Sum.inl (i, a)))) =
        Fin.castAdd (2 * m) (finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2)) (i, a)) := by
      ext
      simp [finProdFinEquiv]
    simp only [Function.comp_apply, hi, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
  · have hj : Fin.cast (mul_add 2 n m) (finProdFinEquiv.trans (finCongr (Nat.mul_comm (n + m) 2))
        ((Equiv.sumProdDistrib _ _ _).symm.trans (finSumFinEquiv.prodCongr (Equiv.refl _))
          (Sum.inr (j, a)))) =
        Fin.natAdd (2 * n) (finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2)) (j, a)) := by
      ext
      simp [finProdFinEquiv]
      ring
    simp only [Function.comp_apply, hj, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]

/-- **The top power of a direct sum of two-forms.** For two-forms `ω₁` on a space `E` of
dimension `2 n` and `ω₂` on a space `F` of dimension `2 m`, the top power of their direct sum
`ω₁ ⊕ ω₂ = ω₁ ∘ pr₁ + ω₂ ∘ pr₂` on `E × F` takes the value `C(n + m, n) ω₁ⁿ(v) ω₂ᵐ(w)` on the
family `(v₁, 0), …, (v₂ₙ, 0), (0, w₁), …, (0, w₂ₘ)`. -/
theorem wedgePow_prod_apply (hn : finrank ℝ E = 2 * n) (hm : finrank ℝ F = 2 * m)
    (ω₁ : E [⋀^Fin 2]→L[ℝ] ℝ) (ω₂ : F [⋀^Fin 2]→L[ℝ] ℝ) (v : Fin (2 * n) → E)
    (w : Fin (2 * m) → F) :
    (ω₁.compContinuousLinearMap (.fst ℝ E F) + ω₂.compContinuousLinearMap (.snd ℝ E F)).wedgePow
        (n + m) (fun r ↦ Sum.elim (fun i ↦ (v i, 0)) (fun j ↦ (0, w j))
          (finSumFinEquiv.symm (Fin.cast (mul_add 2 n m) r))) =
      ((n + m).choose n : ℝ) * (ω₁.wedgePow n v * ω₂.wedgePow m w) := by
  -- If a summand is degenerate, both sides vanish.
  by_cases h₁ : ∀ x, (∀ y, ω₁ ![x, y] = 0) → x = 0
  swap
  · rw [wedgePow_add_compContinuousLinearMap_fst_snd_eq_zero hn hm (.inl h₁),
      (not_ne_iff.1 (mt (wedgePow_ne_zero_iff hn ω₁).1 h₁))]
    simp
  by_cases h₂ : ∀ x, (∀ y, ω₂ ![x, y] = 0) → x = 0
  swap
  · rw [wedgePow_add_compContinuousLinearMap_fst_snd_eq_zero hn hm (.inr h₂),
      (not_ne_iff.1 (mt (wedgePow_ne_zero_iff hm ω₂).1 h₂))]
    simp
  -- Otherwise Darboux bases `b`, `c` of the summands concatenate to a Darboux basis of the sum,
  -- and each power is its value `k!` on such a basis times the determinant in that basis.
  set ω₁s := TauCeti.SymplecticForm.ofContinuousAlternatingMap ω₁ h₁
  set ω₂s := TauCeti.SymplecticForm.ofContinuousAlternatingMap ω₂ h₂
  obtain ⟨b, hb⟩ := ω₁s.exists_isDarbouxBasis_of_finrank_eq (hn.trans (Nat.mul_comm 2 n))
  obtain ⟨c, hc⟩ := ω₂s.exists_isDarbouxBasis_of_finrank_eq (hm.trans (Nat.mul_comm 2 m))
  rw [apply_eq_det_mul _ (((b.prod c).reindex _).reindex _), det_reindex_prod_sumElim,
    wedgePow_apply_reindex_of_isDarbouxBasis _ (fun x y ↦ ?_) (hb.prod hc),
    apply_eq_det_mul _ (b.reindex _) v, wedgePow_apply_reindex_of_isDarbouxBasis ω₁
      (TauCeti.SymplecticForm.ofContinuousAlternatingMap_apply ω₁ h₁) hb,
    apply_eq_det_mul _ (c.reindex _) w, wedgePow_apply_reindex_of_isDarbouxBasis ω₂
      (TauCeti.SymplecticForm.ofContinuousAlternatingMap_apply ω₂ h₂) hc,
    ← Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right n m), Nat.add_sub_cancel_left]
  · push_cast
    ring
  · rw [add_compContinuousLinearMap_fst_snd_apply, TauCeti.SymplecticForm.prod_apply,
      TauCeti.SymplecticForm.ofContinuousAlternatingMap_apply,
      TauCeti.SymplecticForm.ofContinuousAlternatingMap_apply]

end ContinuousAlternatingMap
