/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.Padics.ContinuousMapLattice

/-!
# Checks: continuous maps into `V` land in a lattice

Checks that continuous maps from a compact space into `V` land in a lattice, for `T = ℤ_p` inside
`V = ℚ_p`, the `ℤ_p`-span of the basis `1` (Rubin, *Euler Systems*, Appendix B, §2,
Proposition 2.4).

* For `X = ℤ_p`, the map `x ↦ x / p` lands in `p⁻¹ ℤ_p` and not in `ℤ_p`.
* Compactness is needed: on the discrete noncompact space `ℕ`, the continuous map `n ↦ p^{-n}`
  lands in no `p^{-n} ℤ_p`.
* For empty `X`, both `C(X, ℤ_p)` and `C(X, ℚ_p)` are zero.
-/

variable (p : ℕ) [Fact p.Prime]

example : IsOpen ((Submodule.span ℤ_[p] (Set.range (Module.Basis.singleton Unit ℚ_[p])) :
    Submodule ℤ_[p] ℚ_[p]) : Set ℚ_[p]) :=
  Module.Basis.isOpen_span_padicInt _

/-- `x ↦ x / p` on `ℤ_p` lands in `p⁻¹ ℤ_p`. -/
example : ∀ x : ℤ_[p], (p : ℤ_[p]) ^ 1 • ((x : ℚ_[p]) / p) ∈
    Submodule.span ℤ_[p] (Set.range (Module.Basis.singleton Unit ℚ_[p])) := by
  intro x
  rw [Module.Basis.mem_span_padicInt_iff_norm_repr_le_one]
  simp [← algebraMap_smul ℚ_[p], mul_div_cancel₀, (Fact.out : p.Prime).ne_zero, x.norm_le_one]

/-- `x ↦ x / p` on `ℤ_p` does not land in `ℤ_p`: its value at `1` is `1 / p`. -/
example : ((1 : ℤ_[p]) : ℚ_[p]) / p ∉
    Submodule.span ℤ_[p] (Set.range (Module.Basis.singleton Unit ℚ_[p])) := by
  rw [Module.Basis.mem_span_padicInt_iff_norm_repr_le_one]
  simp [(Fact.out : p.Prime).one_lt]

/-- Compactness is needed: on the discrete space `ℕ`, `n ↦ p^{-n}` lands in no `p^{-n} ℤ_p`. -/
example : ¬ ∃ n : ℕ, ∀ m : ℕ, (p : ℤ_[p]) ^ n • ((p : ℚ_[p]) ^ m)⁻¹ ∈
    Submodule.span ℤ_[p] (Set.range (Module.Basis.singleton Unit ℚ_[p])) := by
  rintro ⟨n, hn⟩
  have h := (Module.Basis.mem_span_padicInt_iff_norm_repr_le_one _ _).1 (hn (n + 1))
  exact (Fact.out : p.Prime).one_lt.not_ge <| by
    simpa [← algebraMap_smul ℚ_[p], pow_succ', mul_inv_cancel_left₀, (Fact.out : p.Prime).ne_zero]
      using h

/-- For empty `X`, `C(X, ℚ_p)` is zero. -/
example {X : Type*} [TopologicalSpace X] [IsEmpty X] : Subsingleton C(X, ℚ_[p]) :=
  inferInstance

/-- For empty `X`, `C(X, ℤ_p)` is zero. -/
example {X : Type*} [TopologicalSpace X] [IsEmpty X] :
    Subsingleton C(X, Submodule.span ℤ_[p] (Set.range (Module.Basis.singleton Unit ℚ_[p]))) :=
  inferInstance
