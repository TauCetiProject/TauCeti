/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Checks for smooth representations and smooth vectors

These examples exercise `Representation.IsSmooth` and `Representation.smoothVectors` on the
additive group `ℤ_[p]` of `p`-adic integers, written multiplicatively as
`Multiplicative ℤ_[p]`, and on discrete groups.

* The trivial representation of any topological group is smooth.
* The left regular representation of `ℤ_[p]` on `ℤ[ℤ_[p]]` is not smooth: the stabilizer of a
  basis vector is trivial, and `{0}` is not open in `ℤ_[p]`. In fact its only smooth vector is
  `0`, since a nonzero finitely supported function can only be fixed by a finite subgroup.
* For `U = p ^ n ℤ_[p]` the permutation representation `ℤ[ℤ_[p] ⧸ U]` is smooth, and `U` fixes
  every vector.
* Every vector of a representation of a discrete group is smooth.
-/

public section

open Representation
open scoped MonoidAlgebra

namespace TauCeti.Examples.RepresentationTheory.Smooth

/-! ### The trivial representation and discrete groups -/

/-- The trivial representation of any topological group is smooth. -/
example {A G V : Type*} [Semiring A] [Group G] [TopologicalSpace G] [AddCommMonoid V]
    [Module A V] : IsSmooth (trivial A G V) :=
  inferInstance

/-- For a discrete group every vector is smooth. -/
example {A G V : Type*} [Semiring A] [Group G] [TopologicalSpace G] [DiscreteTopology G]
    [AddCommMonoid V] [Module A V] (ρ : Representation A G V) : ρ.smoothVectors = ⊤ := by
  simp

/-! ### The left regular representation of a nondiscrete group -/

/-- In a `T₁` group in which `{1}` is not open, the left regular representation has no
nonzero smooth vector: the open stabilizer of a vector `f` would act freely on the finite support
of `f`, so it would be a finite open subgroup, and `{1}` would be open. -/
theorem smoothVectors_leftRegular_eq_bot {A G : Type*} [Semiring A] [Group G]
    [TopologicalSpace G] [SeparatelyContinuousMul G] [T1Space G] (hG : ¬IsOpen ({1} : Set G)) :
    (leftRegular A G).smoothVectors = ⊥ := by
  refine eq_bot_iff.mpr fun f hf ↦ ?_
  rcases eq_or_ne f 0 with rfl | hf0
  · exact Subrepresentation.mem_toSubmodule.mp (zero_mem _)
  exfalso
  obtain ⟨x, hx⟩ : f.coeff.support.Nonempty := by
    rwa [Finsupp.support_nonempty_iff, Ne, MonoidAlgebra.coeff_eq_zero]
  set H : Set G := ((leftRegular A G).stabilizer f : Set G)
  have hH : IsOpen H := mem_smoothVectors.mp hf
  -- Each `h ∈ H` fixes `f`, so it moves the point `x` of the support to `h * x` in the support.
  have hfin : H.Finite := by
    refine Set.Finite.of_finite_image (f := (· * x)) ?_ (mul_left_injective x).injOn
    refine f.coeff.support.finite_toSet.subset ?_
    rintro _ ⟨h, hh, rfl⟩
    have hfix : leftRegular A G h f = f := hh
    rw [Finset.mem_coe, Finsupp.mem_support_iff, ← hfix, coeff_ofMulAction, smul_eq_mul,
      inv_mul_cancel_left]
    exact Finsupp.mem_support_iff.mp hx
  refine hG ?_
  have hsingleton : ({1} : Set G) = H \ (H \ {1}) := by
    ext g
    by_cases hg : g = 1 <;> simp [hg, H]
  rw [hsingleton]
  exact hH.sdiff (hfin.sdiff).isClosed

variable (p : ℕ) [Fact p.Prime]

/-- The singleton `{0}` is not open in `ℤ_[p]`: the powers of `p` are nonzero and tend to `0`. -/
theorem not_isOpen_singleton_zero_padicInt : ¬IsOpen ({0} : Set ℤ_[p]) := by
  intro h
  have hp : ‖(p : ℤ_[p])‖ < 1 := by
    rw [PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (mod_cast (Fact.out : p.Prime).one_lt)
  obtain ⟨n, hn⟩ :=
    ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one hp).eventually (h.mem_nhds rfl)).exists
  exact pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hn

/-- The identity is not an isolated point of `Multiplicative ℤ_[p]`. -/
theorem not_isOpen_singleton_one_multiplicative_padicInt :
    ¬IsOpen ({1} : Set (Multiplicative ℤ_[p])) :=
  not_isOpen_singleton_zero_padicInt p

/-- The left regular representation of `ℤ_[p]` on `ℤ[ℤ_[p]]` is not smooth. -/
theorem not_isSmooth_leftRegular_padicInt :
    ¬IsSmooth (leftRegular ℤ (Multiplicative ℤ_[p])) := by
  rw [leftRegular, isSmooth_ofMulAction_iff]
  exact fun h ↦ not_isOpen_singleton_one_multiplicative_padicInt p (by simpa using h 1)

/-- The only smooth vector of the left regular representation of `ℤ_[p]` on `ℤ[ℤ_[p]]` is `0`. -/
theorem smoothVectors_leftRegular_padicInt :
    (leftRegular ℤ (Multiplicative ℤ_[p])).smoothVectors = ⊥ :=
  smoothVectors_leftRegular_eq_bot (not_isOpen_singleton_one_multiplicative_padicInt p)

/-! ### Permutation representations on `ℤ_[p] ⧸ p ^ n ℤ_[p]` -/

/-- The open subgroup `p ^ n ℤ_[p]` of `ℤ_[p]`, written multiplicatively: the closed ball of
radius `p ^ (-n)` about `0`. -/
noncomputable def padicIntPowSubgroup (n : ℕ) : OpenSubgroup (Multiplicative ℤ_[p]) where
  toSubgroup := AddSubgroup.toSubgroup (Ideal.span {(p : ℤ_[p]) ^ n}).toAddSubgroup
  isOpen' := by
    have : ((Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]) : Set ℤ_[p]) =
        Metric.closedBall 0 ((p : ℝ) ^ (-n : ℤ)) := by
      ext x
      simp [← PadicInt.norm_le_pow_iff_mem_span_pow]
    -- `Multiplicative ℤ_[p]` is a type synonym carrying the topology of `ℤ_[p]`, and the carrier
    -- of `AddSubgroup.toSubgroup` is that of the additive subgroup, so the goal is the openness
    -- of the ideal in `ℤ_[p]`.
    change IsOpen ((Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]) : Set ℤ_[p])
    rw [this]
    exact IsUltrametricDist.isOpen_closedBall _
      (zpow_ne_zero _ (mod_cast (Fact.out : p.Prime).ne_zero))

/-- The permutation representation `ℤ[ℤ_[p] ⧸ p ^ n ℤ_[p]]` is smooth. -/
example (n : ℕ) :
    IsSmooth (ofMulAction ℤ (Multiplicative ℤ_[p])
      (Multiplicative ℤ_[p] ⧸ (padicIntPowSubgroup p n : Subgroup (Multiplicative ℤ_[p])))) :=
  inferInstance

/-- Every vector of `ℤ[ℤ_[p] ⧸ p ^ n ℤ_[p]]` is fixed by `p ^ n ℤ_[p]`: the group is commutative,
so `p ^ n ℤ_[p]` fixes every coset. -/
example (n : ℕ)
    (f : ℤ[Multiplicative ℤ_[p] ⧸ (padicIntPowSubgroup p n : Subgroup (Multiplicative ℤ_[p]))])
    (u : Multiplicative ℤ_[p]) (hu : u ∈ padicIntPowSubgroup p n) :
    ofMulAction ℤ (Multiplicative ℤ_[p]) _ u f = f := by
  ext y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  rw [coeff_ofMulAction, MulAction.Quotient.smul_mk]
  congr 1
  rw [QuotientGroup.eq, smul_eq_mul, mul_inv_rev, inv_inv, mul_comm, mul_inv_cancel_left]
  exact hu

end TauCeti.Examples.RepresentationTheory.Smooth
