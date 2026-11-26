/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Linear independence in products

Over a domain `R`, the vectors `(1, c)` and `v` of `R × R` are linearly independent exactly when
the determinant `v.2 - c * v.1` is nonzero (`TauCeti.linearIndependent_pair_mk_one_iff`).

Over a semiring `K`, a family `u : Option J → V × W`, with `V` a cancellative semimodule, is
linearly independent when its values at `some i` are `(eᵢ, 0)` for a linearly independent
family `e`, and scalar multiplication on the second coordinate of its value at `none` is injective
(`LinearIndependent.option_prod`): adjoining a vector with a new coordinate keeps a family
independent.
-/

public section

namespace TauCeti

/-- Over a domain `R`, the vectors `(1, c)` and `v` of `R × R` are linearly independent exactly
when the determinant `v.2 - c * v.1` is nonzero: the case of
`LinearIndependent.pair_add_smul_add_smul_iff` for the standard basis. -/
theorem linearIndependent_pair_mk_one_iff {R : Type*} [CommRing R] [IsDomain R] {c : R}
    {v : R × R} : LinearIndependent R ![((1 : R), c), v] ↔ v.2 - c * v.1 ≠ 0 := by
  have hbasis : LinearIndependent R ![((1 : R), (0 : R)), ((0 : R), (1 : R))] :=
    LinearIndependent.pair_iff.2 fun s t hst ↦ by simpa [Prod.ext_iff] using hst
  have key := LinearIndependent.pair_add_smul_add_smul_iff (R := R)
    (x := ((1 : R), (0 : R))) (y := ((0 : R), (1 : R))) (1 : R) c v.1 v.2
  simp only [Prod.smul_mk, smul_eq_mul, mul_one, mul_zero, Prod.mk_add_mk, add_zero, zero_add,
    Prod.mk.eta, one_mul] at key
  rw [key]
  exact ⟨fun h ↦ sub_ne_zero.2 h.2, fun h ↦ ⟨hbasis, sub_ne_zero.1 h⟩⟩

end TauCeti

/-- Over a semiring `K`, a family `u : Option J → V × W`, with `V` a cancellative semimodule, is
linearly independent when its values at `some i` are `(eᵢ, 0)` for a linearly independent
family `e`, and scalar multiplication on the second coordinate of its value at `none` is
injective. -/
theorem LinearIndependent.option_prod {K V W J : Type*} [Semiring K] [AddCancelCommMonoid V]
    [Module K V] [AddCommMonoid W] [Module K W] {e : J → V} (he : LinearIndependent K e)
    {u : Option J → V × W} (hsome : ∀ i, u (some i) = (e i, 0))
    (hnone : Function.Injective (fun a : K ↦ a • (u none).2)) :
    LinearIndependent K u := by
  rw [linearIndependent_iffₛ]
  intro l m hlm
  have hcomp : u ∘ some = LinearMap.inl K V W ∘ e := funext hsome
  simp only [Finsupp.linearCombination_option, hcomp,
    ← Finsupp.apply_linearCombination] at hlm
  -- The second coordinate determines `none`; cancellation then isolates the other coefficients.
  have hnone' : l none = m none :=
    hnone (by simpa using congrArg Prod.snd hlm)
  have hsome' : l.some = m.some := he.finsuppLinearCombination_injective <| by
    simpa [hnone'] using congrArg Prod.fst hlm
  ext (_ | i)
  · exact hnone'
  · simpa using congrArg (· i) hsome'
