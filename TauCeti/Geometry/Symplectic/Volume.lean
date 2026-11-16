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
import TauCeti.LinearAlgebra.Basis.Fin
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

The normalized top power `ωⁿ / n!` is multiplicative on direct sums
(`ContinuousAlternatingMap.wedgePow_fst_add_snd_apply_append`). Let `ω₁` and `ω₂` be two-forms on
spaces `V` and `W` of dimensions `2 n` and `2 m`, and let `ω = pr₁^* ω₁ + pr₂^* ω₂` on `V × W`. On
the family `(u₁, 0), …, (u₂ₙ, 0), (0, w₁), …, (0, w₂ₘ)` the form `ω^(n + m) / (n + m)!` takes
the value `(ω₁ⁿ / n!)(u) · (ω₂ᵐ / m!)(w)`. If one of the forms is degenerate, both sides vanish.
Otherwise a Darboux basis of `ω` is the concatenation of Darboux bases of `ω₁` and `ω₂`, on which
all three normalized powers take the value `1`, and both sides transform by the same determinant
under the block-diagonal change of basis to `u` and `w`. This is the pointwise statement behind
the multiplicativity of the Liouville measure on products of symplectic manifolds.

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
    rw [← map_basis_ne_zero_iff _ (b.reindex (finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2)))),
      Basis.coe_reindex_finProdFinEquiv, hval]
    exact Nat.cast_ne_zero.2 n.factorial_ne_zero

section Prod

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W] [TopologicalSpace W] [FiniteDimensional ℝ W] {m : ℕ}

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
/-- The two-form `pr₁^* ω₁ + pr₂^* ω₂` on `V × W` pairs `p` with `q` to
`ω₁(p.1, q.1) + ω₂(p.2, q.2)`. -/
private theorem fst_add_snd_apply (ω₁ : V [⋀^Fin 2]→L[ℝ] ℝ) (ω₂ : W [⋀^Fin 2]→L[ℝ] ℝ)
    (p q : V × W) :
    (ω₁.compContinuousLinearMap (ContinuousLinearMap.fst ℝ V W) +
        ω₂.compContinuousLinearMap (ContinuousLinearMap.snd ℝ V W)) ![p, q] =
      ω₁ ![p.1, q.1] + ω₂ ![p.2, q.2] := by
  have h₁ : Prod.fst ∘ ![p, q] = ![p.1, q.1] := by ext i; fin_cases i <;> rfl
  have h₂ : Prod.snd ∘ ![p, q] = ![p.2, q.2] := by ext i; fin_cases i <;> rfl
  simp [h₁, h₂]

/-- If the top power of `pr₁^* ω₁ + pr₂^* ω₂` is nonzero, both `ω₁` and `ω₂` are nondegenerate: a
vector `v` in the kernel of `ω₁` or of `ω₂` gives the vector `(v, 0)` or `(0, v)` in the kernel of
the sum. -/
private theorem nondegenerate_of_wedgePow_fst_add_snd_ne_zero (hn : finrank ℝ V = 2 * n)
    (hm : finrank ℝ W = 2 * m) (ω₁ : V [⋀^Fin 2]→L[ℝ] ℝ) (ω₂ : W [⋀^Fin 2]→L[ℝ] ℝ)
    (h : (ω₁.compContinuousLinearMap (ContinuousLinearMap.fst ℝ V W) +
      ω₂.compContinuousLinearMap (ContinuousLinearMap.snd ℝ V W)).wedgePow (n + m) ≠ 0) :
    (∀ v, (∀ x, ω₁ ![v, x] = 0) → v = 0) ∧ ∀ v, (∀ x, ω₂ ![v, x] = 0) → v = 0 := by
  have hnm : finrank ℝ (V × W) = 2 * (n + m) := by rw [finrank_prod, hn, hm, Nat.mul_add]
  have h' := (wedgePow_ne_zero_iff hnm _).1 h
  refine ⟨fun v hv ↦ congrArg Prod.fst (h' (v, 0) fun q ↦ ?_),
    fun v hv ↦ congrArg Prod.snd (h' (0, v) fun q ↦ ?_)⟩
  · rw [fst_add_snd_apply, hv, ω₂.map_coord_zero 0 rfl, add_zero]
  · rw [fst_add_snd_apply, hv, ω₁.map_coord_zero 0 rfl, zero_add]

/-- **The normalized top power of a direct sum of two-forms.** For two-forms `ω₁` on a space `V`
of dimension `2 n` and `ω₂` on a space `W` of dimension `2 m`, the form
`ω = pr₁^* ω₁ + pr₂^* ω₂` on `V × W` satisfies

`(ω^(n + m) / (n + m)!)((u, 0), (0, w)) = (ω₁ⁿ / n!)(u) · (ω₂ᵐ / m!)(w)`,

where `((u, 0), (0, w))` lists the vectors `(uᵢ, 0)` and then the vectors `(0, wⱼ)`. No
nondegeneracy is assumed: for a degenerate `ω₁` or `ω₂` both sides vanish. -/
theorem wedgePow_fst_add_snd_apply_append (hn : finrank ℝ V = 2 * n) (hm : finrank ℝ W = 2 * m)
    (ω₁ : V [⋀^Fin 2]→L[ℝ] ℝ) (ω₂ : W [⋀^Fin 2]→L[ℝ] ℝ) (u : Fin (2 * n) → V)
    (w : Fin (2 * m) → W) :
    ((n + m).factorial : ℝ)⁻¹ *
        (ω₁.compContinuousLinearMap (ContinuousLinearMap.fst ℝ V W) +
          ω₂.compContinuousLinearMap (ContinuousLinearMap.snd ℝ V W)).wedgePow (n + m)
          (fun r ↦ Fin.append (fun i ↦ (u i, (0 : W))) (fun j ↦ ((0 : V), w j))
            (Fin.cast (Nat.mul_add 2 n m) r)) =
      ((n.factorial : ℝ)⁻¹ * ω₁.wedgePow n u) * ((m.factorial : ℝ)⁻¹ * ω₂.wedgePow m w) := by
  set ω := ω₁.compContinuousLinearMap (ContinuousLinearMap.fst ℝ V W) +
    ω₂.compContinuousLinearMap (ContinuousLinearMap.snd ℝ V W)
  by_cases h₁₂ : (∀ v, (∀ x, ω₁ ![v, x] = 0) → v = 0) ∧ ∀ v, (∀ x, ω₂ ![v, x] = 0) → v = 0
  swap
  · -- A degenerate factor: both sides vanish by the volume criterion.
    have h : ω.wedgePow (n + m) = 0 :=
      not_not.1 (mt (nondegenerate_of_wedgePow_fst_add_snd_ne_zero hn hm ω₁ ω₂) h₁₂)
    rcases not_and_or.1 h₁₂ with h₁ | h₂
    · simp [h, not_not.1 (mt (wedgePow_ne_zero_iff hn ω₁).1 h₁)]
    · simp [h, not_not.1 (mt (wedgePow_ne_zero_iff hm ω₂).1 h₂)]
  -- Both forms are nondegenerate: the concatenation of Darboux bases of `ω₁` and `ω₂` is a Darboux
  -- basis of `ω`, and all three powers take the value of a factorial on these bases.
  obtain ⟨h₁, h₂⟩ := h₁₂
  have hω (p q : V × W) : ω ![p, q] = ω₁ ![p.1, q.1] + ω₂ ![p.2, q.2] :=
    fst_add_snd_apply ω₁ ω₂ p q
  set s₁ := TauCeti.SymplecticForm.ofContinuousAlternatingMap ω₁ h₁
  set s₂ := TauCeti.SymplecticForm.ofContinuousAlternatingMap ω₂ h₂
  obtain ⟨d₁, hd₁⟩ := s₁.exists_isDarbouxBasis_of_finrank_eq (hn.trans (Nat.mul_comm 2 n))
  obtain ⟨d₂, hd₂⟩ := s₂.exists_isDarbouxBasis_of_finrank_eq (hm.trans (Nat.mul_comm 2 m))
  have hd := hd₁.prod hd₂
  set d := (d₁.prod d₂).reindex
    ((Equiv.sumProdDistrib _ _ _).symm.trans (finSumFinEquiv.prodCongr (Equiv.refl _)))
  have hv₁ := wedgePow_apply_finProdFinEquiv ω₁ d₁
    (fun i j ↦ by simpa [s₁] using hd₁.apply_fst_fst i j)
    (fun i j ↦ by simpa [s₁] using hd₁.apply_fst_snd i j)
  have hv₂ := wedgePow_apply_finProdFinEquiv ω₂ d₂
    (fun i j ↦ by simpa [s₂] using hd₂.apply_fst_fst i j)
    (fun i j ↦ by simpa [s₂] using hd₂.apply_fst_snd i j)
  have hv := wedgePow_apply_finProdFinEquiv ω d
    (fun i j ↦ by simpa [hω, s₁, s₂] using hd.apply_fst_fst i j)
    (fun i j ↦ by simpa [hω, s₁, s₂] using hd.apply_fst_snd i j)
  rw [← Basis.coe_reindex_finProdFinEquiv] at hv₁ hv₂ hv
  have hB : ⇑(d.reindex (finProdFinEquiv.trans (finCongr (Nat.mul_comm (n + m) 2)))) =
      fun r ↦ Fin.append
        (fun i ↦ (d₁.reindex (finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2))) i, (0 : W)))
        (fun j ↦ ((0 : V), d₂.reindex (finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) j))
        (Fin.cast (Nat.mul_add 2 n m) r) :=
    Basis.coe_reindex_prod_finProdFinEquiv d₁ d₂
  have key := apply_append_eq_mul_of_apply_basis (Nat.mul_add 2 n m)
    (((n + m).factorial : ℝ)⁻¹ • ω.wedgePow (n + m)) (((n.factorial : ℝ)⁻¹ • ω₁.wedgePow n))
    (((m.factorial : ℝ)⁻¹ • ω₂.wedgePow m)) _ _ _ hB
    (by
      simp only [ContinuousAlternatingMap.smul_apply, hv₁, hv₂, hv, smul_eq_mul]
      field_simp) u w
  simpa using key

end Prod

end ContinuousAlternatingMap
