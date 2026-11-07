/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Almost.Finiteness.Approximation
import TauCeti.RingTheory.Almost.ValuationRing
import TauCeti.NumberTheory.Padics.Complex.MaximalIdeal
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Examples of almost finitely generated and presented modules

These examples test `TauCeti.Almost.BasicSetup.AlmostFG`, `UniformlyAlmostFG` and `AlmostFP`:

* `Vⁿ` has uniform bound `n` and is almost finitely presented for every setup, while over `ℚ` in
  the classical setup `ℚ²` does not have uniform bound `1`;
* for every setup, a nonzero element of `m` prevents `ℕ →₀ V` from being almost finitely
  generated; in particular `ℕ →₀ ℤ` is not almost finitely generated classically, while for the
  zero setup it is almost finitely presented with uniform bound `0`;
* the uniform bound `0` holds for `V ⧸ m` in every setup but not for `ℤ ⧸ 2` classically;
* through the almost isomorphism `m → V`, the ideal `m` of every setup is almost finitely
  generated; for a valuation domain with non-finitely-generated maximal ideal, such as
  `𝓞_ℂ_[p]`, it has uniform bound `1` although it is not a finitely generated module;
* the epsilon criterion shows that the same maximal ideal is almost finitely presented,
  although it is not finitely presented. Multiplication by `ε` gives its finite approximation.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §2.3.
-/

open IsLocalRing TauCeti.Almost TauCeti.Almost.BasicSetup

variable {V : Type*} [CommRing V] (S : BasicSetup V)

/-! ### Finite free modules -/

-- `Vⁿ` has uniform bound `n` for every setup, including `n = 0`, and is almost finitely
-- presented.
example (n : ℕ) : S.UniformlyAlmostFG (Fin n → V) n :=
  uniformlyAlmostFG_of_surjective S LinearMap.id Function.surjective_id

example : S.UniformlyAlmostFG (Fin 0 → V) 0 :=
  uniformlyAlmostFG_of_surjective S LinearMap.id Function.surjective_id

example (n : ℕ) : S.AlmostFP (Fin n → V) :=
  almostFP_of_finitePresentation S

-- Over `ℚ` in the classical setup, `ℚ²` has uniform bound `2` but not `1`.
example : (classical ℚ).UniformlyAlmostFG (Fin 2 → ℚ) 2 :=
  uniformlyAlmostFG_of_surjective _ LinearMap.id Function.surjective_id

example : ¬ (classical ℚ).UniformlyAlmostFG (Fin 2 → ℚ) 1 := by
  rw [uniformlyAlmostFG_classical_iff]
  rintro ⟨φ, hφ⟩
  have := LinearMap.finrank_range_le φ
  rw [LinearMap.range_eq_top.mpr hφ, finrank_top] at this
  simp at this

/-! ### Infinite free modules -/

-- A nonzero element `ε ∈ m` prevents `ℕ →₀ V` from being almost finitely generated: a map
-- `Vⁿ → ℕ →₀ V` lands in the functions supported on a finite set `T`, and `ε • single k 1` does
-- not for `k ∉ T`.
example {ε : V} (hε : ε ∈ S.ideal) (hε₀ : ε ≠ 0) : ¬ S.AlmostFG (ℕ →₀ V) := by
  classical
  intro h
  obtain ⟨n, φ, hφ⟩ :=
    almostFG_iff.mp h (Ideal.span {ε}) (by simpa [Ideal.span_le]) (Submodule.fg_span_singleton ε)
  let T : Finset ℕ := Finset.univ.biUnion fun i ↦ (φ fun j ↦ if i = j then 1 else 0).support
  have hT : LinearMap.range φ ≤ Finsupp.supported V V (T : Set ℕ) := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.pi_apply_eq_sum_univ φ v]
    refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ ?_
    rw [Finsupp.mem_supported, Finset.coe_subset]
    exact Finset.subset_biUnion_of_mem (fun i ↦ (φ fun j ↦ if i = j then 1 else 0).support)
      (Finset.mem_univ i)
  obtain ⟨k, hk⟩ := Infinite.exists_notMem_finset T
  have hmem := hT (hφ (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self ε)
    (Submodule.mem_top (x := Finsupp.single k 1))))
  rw [Finsupp.smul_single_one, Finsupp.mem_supported'] at hmem
  exact hε₀ (by simpa using hmem k hk)

-- In the classical setup over `ℤ`, `ℤ` is almost finitely presented and `ℕ →₀ ℤ` is not almost
-- finitely generated.
example : (classical ℤ).AlmostFP ℤ :=
  almostFP_of_finitePresentation _

example : ¬ (classical ℤ).AlmostFG (ℕ →₀ ℤ) := by
  rw [almostFG_classical_iff]
  intro h
  have := Module.Finite.finite_basis (Finsupp.basisSingleOne (R := ℤ) (ι := ℕ))
  exact not_finite ℕ

-- For the zero setup `ℕ →₀ ℤ` is almost finitely presented, with uniform bound `0`.
example : (zero ℤ).AlmostFP (ℕ →₀ ℤ) :=
  almostFP_zero

example : (zero ℤ).UniformlyAlmostFG (ℕ →₀ ℤ) 0 :=
  uniformlyAlmostFG_bound_zero_iff.mpr isAlmostZero_zero

/-! ### The uniform bound `0` -/

-- `V ⧸ m` has uniform bound `0` for every setup, while `ℤ ⧸ 2` does not classically.
example : S.UniformlyAlmostFG (V ⧸ S.ideal) 0 :=
  uniformlyAlmostFG_bound_zero_iff.mpr S.isAlmostZero_quotient

example : ¬ (classical ℤ).UniformlyAlmostFG (ZMod 2) 0 := by
  rw [uniformlyAlmostFG_bound_zero_iff, isAlmostZero_classical_iff]
  exact fun h ↦ zero_ne_one (Subsingleton.elim (0 : ZMod 2) 1)

/-! ### The ideal `m` -/

-- The ideal `m` of every setup is almost finitely generated: `m → V` is an almost isomorphism.
example : S.AlmostFG S.ideal :=
  (S.isAlmostIso_subtype).almostFG_iff.mpr (almostFG_of_finite S)

section ValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [ValuationRing O] (h : ¬ (maximalIdeal O).FG)

-- Multiplication by `ε` maps `O` to its maximal ideal, with kernel and cokernel killed by `ε`.
-- Thus this non-finitely-generated module is nevertheless almost finitely presented.
example : (ofValuationRing h).AlmostFP (ofValuationRing h).ideal ∧
    ¬ Module.FinitePresentation O (ofValuationRing h).ideal := by
  constructor
  · rw [almostFP_iff_epsilon (isFilteredPrincipal_of_preValuationRing _)]
    intro ε hε
    let f := LinearMap.toSpanSingleton O (ofValuationRing h).ideal ⟨ε, hε⟩
    refine ⟨O, inferInstance, inferInstance, inferInstance, f, ?_, ?_⟩
    · apply Module.mem_annihilator.mpr
      rintro ⟨x, hx⟩
      apply Subtype.ext
      simpa [f, mul_comm] using congrArg Subtype.val (LinearMap.mem_ker.mp hx)
    · apply Module.mem_annihilator.mpr
      intro x
      obtain ⟨x, rfl⟩ := (LinearMap.range f).mkQ_surjective x
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      refine ⟨(x : O), ?_⟩
      apply Subtype.ext
      simp [f, mul_comm]
  · intro hfp
    have := hfp
    have hnot : ¬ Module.Finite O (ofValuationRing h).ideal := by
      rwa [Module.Finite.iff_fg, ofValuationRing_ideal]
    exact hnot inferInstance

-- For a valuation domain whose maximal ideal `m` is not finitely generated, `m` has uniform
-- bound `1`, like `O`, but it is not a finitely generated `O`-module.
example : (ofValuationRing h).UniformlyAlmostFG (ofValuationRing h).ideal 1 := by
  rw [UniformlyAlmostFG.iff_of_isAlmostIso (isFilteredPrincipal_of_preValuationRing _)
    (isAlmostIso_subtype _)]
  exact uniformlyAlmostFG_of_surjective _ (LinearEquiv.funUnique (Fin 1) O O).toLinearMap
    (LinearEquiv.funUnique (Fin 1) O O).surjective

example : ¬ Module.Finite O (ofValuationRing h).ideal := by
  rwa [Module.Finite.iff_fg, ofValuationRing_ideal]

-- The same for `𝓞_ℂ_[p]`.
example (p : ℕ) [Fact p.Prime] :
    (ofValuationRing (TauCeti.PadicComplexInt.not_fg_maximalIdeal p)).UniformlyAlmostFG
      (ofValuationRing (TauCeti.PadicComplexInt.not_fg_maximalIdeal p)).ideal 1 := by
  rw [UniformlyAlmostFG.iff_of_isAlmostIso (isFilteredPrincipal_of_preValuationRing _)
    (isAlmostIso_subtype _)]
  exact uniformlyAlmostFG_of_surjective _ (LinearEquiv.funUnique (Fin 1) _ _).toLinearMap
    (LinearEquiv.funUnique (Fin 1) _ _).surjective

end ValuationRing
