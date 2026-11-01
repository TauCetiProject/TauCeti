/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Weights.IsSimple
public import TauCeti.Algebra.Lie.HighestWeight.Casimir
public import TauCeti.Algebra.Lie.Killing.InvariantForm
public import TauCeti.LinearAlgebra.RootSystem.DualCoxeterNumber

/-!
# The Killing form is `2 h^∨` times the normalized invariant form

Let `L` be a finite-dimensional simple Lie algebra over a field `K` of characteristic zero, `H` a
splitting Cartan subalgebra, and `b` a base of its root system
`LieAlgebra.IsKilling.rootSystem H`, with highest root `θ` and dual Coxeter number
`h^∨ = RootPairing.Base.dualCoxeterNumber b`. The **normalized invariant form** is

`κ₀ = (2 h^∨)⁻¹ κ`,

where `κ` is the Killing form (`TauCeti.normalizedInvariantForm`). This file proves that `κ₀` is
the invariant form in which the highest root, a long root, has squared length `2`, so that the
Killing form is `κ = 2 h^∨ κ₀`. These are the normalizations of the affine theory: a level `k`
means the invariant form `k κ₀`, and the critical level is the form `-½ κ = -h^∨ κ₀`
(`TauCeti.neg_inv_two_smul_killingForm_eq_neg_smul_normalizedInvariantForm`).

The computation is the root-system identity
`RootPairing.Base.corootForm_coroot_highestRoot`, `∑_α ⟨α, θ^∨⟩² = 4 h^∨`, read through Mathlib's
`LieAlgebra.IsKilling.corootForm_rootSystem_eq_killing`, which says that its left side is the
Killing form on the Cartan subalgebra. It gives `κ(θ^∨, θ^∨) = 4 h^∨`
(`TauCeti.killingForm_coroot_highestRoot`), hence `κ₀(θ^∨, θ^∨) = 2`. Dually, for the inverse
forms on the weights, `⟨θ, θ⟩ = 1 / h^∨` for the Killing form (`TauCeti.invForm_root_highestRoot`)
and `⟨θ, θ⟩ = 2` for `κ₀` (`TauCeti.root_highestRoot_apply_eq_two`). Over an algebraically
closed field every invariant form is a multiple of the Killing form, so `κ₀` is the only invariant
form with `κ₀(θ^∨, θ^∨) = 2` (`TauCeti.eq_normalizedInvariantForm`).

The dual Coxeter number is also read off the Casimir scalar `TauCeti.casimirScalar`, the scalar
`⟨λ + ρ, λ + ρ⟩ - ⟨ρ, ρ⟩` by which the Casimir element of the Killing form acts on a highest weight
module of highest weight `λ`. At the highest root, the highest weight of the adjoint
representation, it is `1` (`TauCeti.casimirScalar_root_highestRoot`), because the pairings of `θ`
with the positive roots add up to `⟨θ, θ⟩ (h^∨ - 1)` and `⟨θ, θ⟩ h^∨ = 1`. Rescaling the form to
`κ₀` multiplies the Casimir element by `2 h^∨`, so `h^∨` is half the Casimir scalar of the adjoint
representation for `κ₀`; the Casimir element of `κ₀` itself is not constructed here.

## Main definitions

* `TauCeti.normalizedInvariantForm`: the invariant form `κ₀ = (2 h^∨)⁻¹ κ`.

## Main results

* `TauCeti.killingForm_coroot_highestRoot`: `κ(θ^∨, θ^∨) = 4 h^∨`.
* `TauCeti.invForm_root_highestRoot`: `⟨θ, θ⟩ = 1 / h^∨` for the inverse Killing form.
* `TauCeti.killingForm_eq_smul_normalizedInvariantForm`: `κ = 2 h^∨ κ₀`.
* `TauCeti.normalizedInvariantForm_coroot_highestRoot`: `κ₀(θ^∨, θ^∨) = 2`.
* `TauCeti.root_highestRoot_apply_eq_two`: the inverse form of `κ₀` gives `θ` squared length `2`.
* `TauCeti.eq_normalizedInvariantForm`: over an algebraically closed field, `κ₀` is the unique
  invariant form with `κ₀(θ^∨, θ^∨) = 2`.
* `TauCeti.neg_inv_two_smul_killingForm_eq_neg_smul_normalizedInvariantForm`:
  `-½ κ = -h^∨ κ₀`.
* `TauCeti.casimirScalar_root_highestRoot`: the Casimir scalar of the highest root is `1`.

## Implementation notes

The dual Coxeter number is defined from a base, through its highest root, and that it does not
depend on the base is not proved here; so `κ₀` is defined for a fixed base `b`. Over an
algebraically closed field, `TauCeti.eq_normalizedInvariantForm` characterizes it by
`κ₀(θ^∨, θ^∨) = 2`, which involves `b` only through its highest root.

## References

* V. G. Kac, *Infinite-Dimensional Lie Algebras*, 3rd ed., Chapter 6, for the dual Coxeter
  number, the normalized invariant form and its comparison with the Killing form.
* E. Frenkel, *Langlands Correspondence for Loop Groups*, for the critical level
  `κ_c = -½ κ = -h^∨ κ₀`.
-/
public section

open LieAlgebra LieAlgebra.IsKilling LieModule Module

namespace TauCeti

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [IsSimple K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- The root system of a simple Lie algebra has a root. -/
instance nonempty_root : Nonempty H.root := by
  have := RootPairing.IsIrreducible.nontrivial (rootSystem H)
  by_contra h
  have htop := RootPairing.IsRootSystem.span_root_eq_top (P := rootSystem H)
  rw [Set.range_eq_empty_iff.mpr (not_nonempty_iff.mp h), Submodule.span_empty] at htop
  exact bot_ne_top htop

variable (b : (rootSystem H).Base)

/-- **The coroot of the highest root has Killing length `4 h^∨`**: `κ(θ^∨, θ^∨) = 4 h^∨`. -/
theorem killingForm_coroot_highestRoot :
    killingForm K L ((rootSystem H).coroot b.highestRoot)
        ((rootSystem H).coroot b.highestRoot) = 4 * (b.dualCoxeterNumber : K) := by
  have h := b.corootForm_coroot_highestRoot
  rw [corootForm_rootSystem_eq_killing] at h
  exact h

/-- **The highest root has squared length `1 / h^∨` for the inverse Killing form**:
`⟨θ, θ⟩ = (h^∨)⁻¹`, where `⟨·,·⟩` is `TauCeti.invForm`. -/
theorem invForm_root_highestRoot :
    invForm ((rootSystem H).root b.highestRoot) ((rootSystem H).root b.highestRoot) =
      (b.dualCoxeterNumber : K)⁻¹ := by
  have h4 := traceForm_coroot_self_mul_invForm_self_eq_four (H.isNonZero_coe_root b.highestRoot)
  have hκ := killingForm_coroot_highestRoot b
  rw [← restrict_killingForm, LinearMap.BilinForm.restrict_apply,
    LinearMap.domRestrict_apply] at h4
  simp only [rootSystem_coroot_apply, rootSystem_root_apply] at hκ ⊢
  rw [hκ] at h4
  have hh : (b.dualCoxeterNumber : K) ≠ 0 := Int.cast_ne_zero.mpr b.dualCoxeterNumber_pos.ne'
  field_simp
  linear_combination h4 / 4

/-- **The normalized invariant form** `κ₀ = (2 h^∨)⁻¹ κ` of a simple Lie algebra, for a base of
its root system with dual Coxeter number `h^∨`. It is the invariant form for which long roots have
squared length `2` (`TauCeti.root_highestRoot_apply_eq_two`), equivalently
`κ₀(θ^∨, θ^∨) = 2` (`TauCeti.normalizedInvariantForm_coroot_highestRoot`), and the Killing form
is `2 h^∨ κ₀` (`TauCeti.killingForm_eq_smul_normalizedInvariantForm`). -/
noncomputable def normalizedInvariantForm : LinearMap.BilinForm K L :=
  (2 * (b.dualCoxeterNumber : K))⁻¹ • killingForm K L

/-- The defining formula `κ₀ = (2 h^∨)⁻¹ κ` of the normalized invariant form. -/
theorem normalizedInvariantForm_def :
    normalizedInvariantForm b = (2 * (b.dualCoxeterNumber : K))⁻¹ • killingForm K L :=
  (rfl)

/-- **The Killing form is `2 h^∨` times the normalized invariant form**: `κ = 2 h^∨ κ₀`. -/
theorem killingForm_eq_smul_normalizedInvariantForm :
    killingForm K L = (2 * (b.dualCoxeterNumber : K)) • normalizedInvariantForm b := by
  have hh : (b.dualCoxeterNumber : K) ≠ 0 := Int.cast_ne_zero.mpr b.dualCoxeterNumber_pos.ne'
  rw [normalizedInvariantForm_def, smul_smul, mul_inv_cancel₀ (mul_ne_zero two_ne_zero hh),
    one_smul]

/-- The normalized invariant form is invariant. -/
theorem normalizedInvariantForm_lieInvariant : (normalizedInvariantForm b).lieInvariant L := by
  rw [normalizedInvariantForm_def, LinearMap.BilinForm.lieInvariant_iff]
  exact Submodule.smul_mem _ _
    ((LinearMap.BilinForm.lieInvariant_iff _).mp (traceForm_lieInvariant K L L))

/-- The normalized invariant form is symmetric. -/
theorem normalizedInvariantForm_isSymm : (normalizedInvariantForm b).IsSymm :=
  (LinearMap.BilinForm.isSymm_def.mpr fun x y ↦ traceForm_comm K L L x y).smul _

/-- The normalized invariant form is nondegenerate. -/
theorem normalizedInvariantForm_nondegenerate : (normalizedInvariantForm b).Nondegenerate := by
  have hh : (b.dualCoxeterNumber : K) ≠ 0 := Int.cast_ne_zero.mpr b.dualCoxeterNumber_pos.ne'
  obtain ⟨hl, hr⟩ := IsKilling.killingForm_nondegenerate K L
  refine ⟨fun x hx ↦ hl x fun y ↦ ?_, fun y hy ↦ hr y fun x ↦ ?_⟩
  · simpa [normalizedInvariantForm_def, hh] using hx y
  · simpa [normalizedInvariantForm_def, hh] using hy x

/-- **The coroot of the highest root has length `2` for the normalized invariant form**:
`κ₀(θ^∨, θ^∨) = 2`. -/
theorem normalizedInvariantForm_coroot_highestRoot :
    normalizedInvariantForm b ((rootSystem H).coroot b.highestRoot)
      ((rootSystem H).coroot b.highestRoot) = 2 := by
  have hh : (b.dualCoxeterNumber : K) ≠ 0 := Int.cast_ne_zero.mpr b.dualCoxeterNumber_pos.ne'
  rw [normalizedInvariantForm_def, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul,
    killingForm_coroot_highestRoot]
  field_simp
  ring

/-- **Long roots have squared length `2` for the inverse of the normalized invariant form.** If
`t ∈ H` represents the highest root `θ` under `κ₀`, that is `κ₀(t, x) = θ(x)` for every `x ∈ H`,
then `θ(t) = 2`; the number `θ(t)` is the squared length of `θ` for the form on the weights
induced by `κ₀`. -/
theorem root_highestRoot_apply_eq_two {t : H}
    (ht : ∀ x : H, normalizedInvariantForm b t x = (rootSystem H).root b.highestRoot x) :
    (rootSystem H).root b.highestRoot t = 2 := by
  set θ := (rootSystem H).root b.highestRoot
  have hh : (b.dualCoxeterNumber : K) ≠ 0 := Int.cast_ne_zero.mpr b.dualCoxeterNumber_pos.ne'
  have hdual : cartanEquivDual H t = (2 * (b.dualCoxeterNumber : K)) • θ := by
    ext x
    rw [cartanEquivDual_apply_apply_eq_killingForm, killingForm_eq_smul_normalizedInvariantForm b,
      LinearMap.smul_apply, LinearMap.smul_apply, ht, LinearMap.smul_apply]
  have ht' : t = (2 * (b.dualCoxeterNumber : K)) • (cartanEquivDual H).symm θ := by
    rw [← map_smul, ← hdual, LinearEquiv.symm_apply_apply]
  have hθ := invForm_root_highestRoot b
  rw [invForm_apply_apply] at hθ
  rw [ht', map_smul, hθ, smul_eq_mul]
  field_simp

/-- **Uniqueness of the normalized invariant form.** Over an algebraically closed field, an
invariant form `κ` with `κ(θ^∨, θ^∨) = 2` is the normalized invariant form, so the Killing form is
`2 h^∨ κ` by `TauCeti.killingForm_eq_smul_normalizedInvariantForm`. -/
theorem eq_normalizedInvariantForm [IsAlgClosed K] {κ : LinearMap.BilinForm K L}
    (hκ : κ.lieInvariant L)
    (hθ : κ ((rootSystem H).coroot b.highestRoot) ((rootSystem H).coroot b.highestRoot) = 2) :
    κ = normalizedInvariantForm b := by
  obtain ⟨c, rfl⟩ := LieAlgebra.exists_eq_smul_killingForm hκ
  have hh : (b.dualCoxeterNumber : K) ≠ 0 := Int.cast_ne_zero.mpr b.dualCoxeterNumber_pos.ne'
  rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul,
    killingForm_coroot_highestRoot] at hθ
  rw [normalizedInvariantForm_def]
  congr 1
  field_simp
  linear_combination hθ / 2

/-- **The critical form is `-h^∨` times the normalized invariant form**: `-½ κ = -h^∨ κ₀`. -/
theorem neg_inv_two_smul_killingForm_eq_neg_smul_normalizedInvariantForm :
    -(2⁻¹ : K) • killingForm K L = -(b.dualCoxeterNumber : K) • normalizedInvariantForm b := by
  rw [killingForm_eq_smul_normalizedInvariantForm b, smul_smul]
  congr 1
  ring

/-- **The Casimir scalar of the highest root is `1`**: `⟨θ + ρ, θ + ρ⟩ - ⟨ρ, ρ⟩ = 1`. This is the
scalar by which the Casimir element of the Killing form acts on a highest weight module of highest
weight `θ` (`TauCeti.casimir_smul_of_isHighestWeightVector_of_lieSpan_eq_top`). -/
theorem casimirScalar_root_highestRoot :
    casimirScalar b ((rootSystem H).root b.highestRoot) = 1 := by
  set θ := (rootSystem H).root b.highestRoot
  have hh : (b.dualCoxeterNumber : K) ≠ 0 := Int.cast_ne_zero.mpr b.dualCoxeterNumber_pos.ne'
  have hpair (i : H.root) : invForm θ ((rootSystem H).root i) =
      invForm θ θ / 2 * ((rootSystem H).pairingIn ℤ i b.highestRoot : K) := by
    have hp : (rootSystem H).root i ((rootSystem H).coroot b.highestRoot) =
        ((rootSystem H).pairingIn ℤ i b.highestRoot : K) := by
      rw [← eq_intCast (algebraMap ℤ K), (rootSystem H).algebraMap_pairingIn ℤ,
        rootSystem_pairing_apply, rootSystem_root_apply, rootSystem_coroot_apply,
        Weight.toLinear_apply]
    have h := invForm_coroot ((rootSystem H).root i) b.highestRoot
    rw [hp] at h
    linear_combination (invForm_isSymm (H := H)).eq θ ((rootSystem H).root i) - h / 2
  have hsum := congrArg (Int.cast : ℤ → K) b.sum_pairingIn_highestRoot_right_posRootsFinset
  push_cast at hsum
  rw [casimirScalar_eq_add_sum, Finset.sum_congr rfl fun i _ ↦ hpair i, ← Finset.mul_sum, hsum,
    invForm_root_highestRoot]
  field_simp
  ring

end TauCeti
