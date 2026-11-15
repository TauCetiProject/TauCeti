/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.LeftIdeal

/-!
# Currents in congruence quotients

The quotient `Q_N = U / I_N` of a level enveloping algebra is a left module. Over a field, its
degree-one current subspace is exactly `L((t)) / a_N` when `N ≥ 0`: the current-generator map
induces an injective linear map from this quotient. This is the first part of the PBW description
of the congruence-induced module, and detects currents acting nontrivially on its cyclic vector.

Over any field at nonnegative order, `I_N` is two-sided precisely when `L`
is abelian and the central term `a • Φ` vanishes. For a nonabelian coefficient Lie algebra
over any field it is never two-sided, even at level zero. Thus these completion stages
cannot be treated as quotient rings.
The obstructions are visible on pairs of Laurent modes.

The degree-one calculation uses the induced-module PBW theorem
`TauCeti.UniversalEnvelopingAlgebra.ι_sub_algebraMap_mem_span_range_ι_sub_algebraMap_iff`.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §2.1.2 and §3.2.1,
  for congruence-induced modules and the left-ideal completion.
* J. Dixmier, *Enveloping Algebras*, Chapter 5, for induced modules and their PBW filtration.
-/

public section

noncomputable section

open scoped TensorProduct LaurentSeries
open LieAlgebra TauCeti.UniversalEnvelopingAlgebra
open LieAlgebra.ofTwoCocycle (centralElement envelopingι envelopingι_mul_sub_mul
  adjoin_range_envelopingι)

-- Match the coefficientwise algebra structure used by formal currents.
attribute [local instance 1100] HahnSeries.instAlgebra

namespace TauCeti.CurrentAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (a : R)

local notation "C" => currentAlgebra R L
local notation "c" => twoCocycleOfBilinear R L Φ hΦ hΦs
local notation "U" => CentralQuotient R (centralElement c) a

/-- The linear map induced by the current generators on currents modulo the prescribed order
submodule. Over a field and at nonnegative order, it identifies the source with the current
subspace of the congruence quotient. -/
def orderQuotientCurrent (N : ℤ) :
    C ⧸ orderSubmodule R L N →ₗ[R] U ⧸ orderLeftIdeal Φ hΦ hΦs a N :=
  (orderSubmodule R L N).liftQ
    (((orderLeftIdeal Φ hΦ hΦs a N).mkQ.restrictScalars R).comp
      (envelopingι c a)) fun u hu ↦ by
    simpa using envelopingι_mem_orderLeftIdeal (Φ := Φ) (hΦ := hΦ) (hΦs := hΦs) (a := a) hu

/-- A current class maps to the class of its enveloping generator. -/
@[simp]
theorem orderQuotientCurrent_mk (N : ℤ) (u : C) :
    orderQuotientCurrent Φ hΦ hΦs a N (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (envelopingι c a u) :=
  (rfl)

/-- For an abelian coefficient Lie algebra with vanishing central term, every congruence
ideal is two-sided. No restriction on the order or the characteristic is needed. -/
theorem isTwoSided_orderLeftIdeal (hL : IsLieAbelian L) (hform : a • Φ = 0) (N : ℤ) :
    Ideal.IsTwoSided (orderLeftIdeal Φ hΦ hΦs a N) := by
  have hmem (u : U) : u ∈ Algebra.adjoin R (Set.range (envelopingι c a)) := by
    rw [adjoin_range_envelopingι]
    trivial
  have hcomm (u v : U) : Commute u v := by
    refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute (hmem v) ?_
    rintro _ ⟨y, rfl⟩
    apply Commute.symm
    refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute (hmem u) ?_
    rintro _ ⟨x, rfl⟩
    exact commute_envelopingι_of_isLieAbelian Φ hΦ hΦs a hL hform y x
  refine ⟨fun v hu ↦ ?_⟩
  rw [(hcomm _ v).eq]
  exact Ideal.mul_mem_left _ _ hu

section Field

variable {K : Type*} [Field K] [LieAlgebra K L]
  (Ψ : LinearMap.BilinForm K L) (hΨ : Ψ.lieInvariant L) (hΨs : Ψ.IsSymm) (b : K)

local notation "CK" => currentAlgebra K L
local notation "cK" => twoCocycleOfBilinear K L Ψ hΨ hΨs
/-- No currents below the cutoff are lost in the congruence quotient. This holds at every
central value and without any finiteness assumption on the coefficient Lie algebra. -/
theorem orderQuotientCurrent_injective {N : ℤ} (hN : 0 ≤ N) :
    Function.Injective (orderQuotientCurrent Ψ hΨ hΨs b N) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro u
  induction u using Submodule.Quotient.induction_on with
  | _ u =>
    simpa using (envelopingι_mem_orderLeftIdeal_iff Ψ hΨ hΨs b hN u).mp

private theorem commutator_relations_of_isTwoSided {N : ℤ} (hN : 0 ≤ N)
    (hI : Ideal.IsTwoSided (orderLeftIdeal Ψ hΨ hΨs b N)) {u : CK}
    (hu : u ∈ orderSubmodule K L N) (v : CK) :
    ⁅u, v⁆ ∈ orderSubmodule K L N ∧ b * residuePairing K L Ψ u v = 0 := by
  have hi := envelopingι_mem_orderLeftIdeal (Φ := Ψ) (hΦ := hΨ) (hΦs := hΨs) (a := b) hu
  have hc := (orderLeftIdeal Ψ hΨ hΨs b N).sub_mem
    (hI.mul_mem_of_left (envelopingι cK b v) hi)
    (Ideal.mul_mem_left _ (envelopingι cK b v) hi)
  rw [envelopingι_mul_sub_mul, twoCocycleOfBilinear_coe,
    twoCochainOfBilinear_apply_apply, LinearEquiv.apply_symm_apply] at hc
  have h := (envelopingι_sub_algebraMap_mem_orderLeftIdeal_iff Ψ hΨ hΨs b hN
    ⁅u, v⁆ (-(b * residuePairing K L Ψ u v))).mp (by simpa using hc)
  exact ⟨h.1, neg_eq_zero.mp h.2⟩

/-- A two-sided congruence ideal at nonnegative order forces the coefficient Lie algebra to
be abelian. The conclusion is independent of the central value and characteristic. -/
theorem isLieAbelian_of_isTwoSided_orderLeftIdeal {N : ℤ} (hN : 0 ≤ N)
    (hI : Ideal.IsTwoSided (orderLeftIdeal Ψ hΨ hΨs b N)) : IsLieAbelian L := by
  refine ⟨fun x y ↦ ?_⟩
  have hu : HahnSeries.single N (1 : K) ⊗ₜ[K] x ∈ orderSubmodule K L N :=
    tmul_mem_orderSubmodule K L N HahnSeries.orderTop_single_le x
  have hc := (commutator_relations_of_isTwoSided Ψ hΨ hΨs b hN hI hu
    (HahnSeries.single (-N - 1) 1 ⊗ₜ[K] y)).1
  have hsum : N + (-N - 1) = -1 := by omega
  have hn : (-1 : ℤ) < N := by omega
  simpa [LieAlgebra.ExtendScalars.bracket_tmul, HahnSeries.single_mul_single, hsum] using
    coeff_eq_zero_of_mem_orderSubmodule K L hc hn

/-- Two-sidedness also forces the level times the invariant form to vanish, in every
characteristic. This rules out two-sided congruence ideals for nonzero Heisenberg central terms. -/
theorem smul_form_eq_zero_of_isTwoSided_orderLeftIdeal {N : ℤ} (hN : 0 ≤ N)
    (hI : Ideal.IsTwoSided (orderLeftIdeal Ψ hΨ hΨs b N)) : b • Ψ = 0 := by
  ext x y
  have hmode (n : ℤ) (hn : N ≤ n) : b * (-(n : K) * Ψ x y) = 0 := by
    have hu : HahnSeries.single n (1 : K) ⊗ₜ[K] x ∈ orderSubmodule K L N :=
      tmul_mem_orderSubmodule K L N
        (le_trans (by exact_mod_cast hn) HahnSeries.orderTop_single_le) x
    have hc := (commutator_relations_of_isTwoSided Ψ hΨ hΨs b hN hI hu
      (HahnSeries.single (-n) 1 ⊗ₜ[K] y)).2
    simpa [residuePairing_tmul, LaurentSeries.residuePairing_single, zsmul_eq_mul] using hc
  -- Subtract consecutive mode relations to avoid dividing by a mode index.
  have h₀ := hmode N le_rfl
  have h₁ := hmode (N + 1) (by omega)
  simp only [Int.cast_add, Int.cast_one] at h₁
  simp only [LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul]
  linear_combination h₀ - h₁

/-- **Exactly when a congruence ideal is two-sided.** At nonnegative order over a field,
this happens precisely for abelian currents with zero central commutator term. -/
@[simp]
theorem isTwoSided_orderLeftIdeal_iff {N : ℤ} (hN : 0 ≤ N) :
    Ideal.IsTwoSided (orderLeftIdeal Ψ hΨ hΨs b N) ↔ IsLieAbelian L ∧ b • Ψ = 0 :=
  ⟨fun hI ↦ ⟨isLieAbelian_of_isTwoSided_orderLeftIdeal Ψ hΨ hΨs b hN hI,
    smul_form_eq_zero_of_isTwoSided_orderLeftIdeal Ψ hΨ hΨs b hN hI⟩,
    fun ⟨hL, hform⟩ ↦ isTwoSided_orderLeftIdeal Ψ hΨ hΨs b hL hform N⟩

/-- For nonabelian coefficient Lie algebras, congruence quotients of nonnegative order are
module quotients rather than quotient rings, including at central value zero. -/
theorem not_isTwoSided_orderLeftIdeal (hL : ¬ IsLieAbelian L) {N : ℤ} (hN : 0 ≤ N) :
    ¬ Ideal.IsTwoSided (orderLeftIdeal Ψ hΨ hΨs b N) :=
  fun hI ↦ hL (isLieAbelian_of_isTwoSided_orderLeftIdeal Ψ hΨ hΨs b hN hI)

end Field

end TauCeti.CurrentAlgebra
