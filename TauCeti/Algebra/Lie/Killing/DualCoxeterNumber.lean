/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.Casimir
public import TauCeti.Algebra.Lie.Killing.InvariantForm
public import TauCeti.Algebra.Lie.Weights.InvariantForm
public import TauCeti.Algebra.Lie.Weights.IsSimple
public import TauCeti.LinearAlgebra.RootSystem.DualCoxeterNumber

/-!
# The Killing form and the dual Coxeter number

Let `L` be a finite-dimensional simple Lie algebra over a field `K` of characteristic zero, with a
splitting Cartan subalgebra `H`, and let `b` be a base of its root system
`LieAlgebra.IsKilling.rootSystem H`, with highest root `θ` and dual Coxeter number
`h^∨ = RootPairing.Base.dualCoxeterNumber b`. This file compares the Killing form `κ` of `L` with
the invariant form `κ₀` normalised by the highest root, and proves `κ = 2 h^∨ κ₀`.

For the root system of `L`, Mathlib's canonical coroot form is the restriction of the Killing form
to `H` (`LieAlgebra.IsKilling.corootForm_rootSystem_eq_killing`), so the root-system identity
`RootPairing.Base.corootForm_coroot_highestRoot` becomes

`κ(θ^∨, θ^∨) = 4 h^∨`

(`RootPairing.Base.killingForm_coroot_highestRoot`). Since `κ(α^∨, α^∨) ⟨α, α⟩ = 4` for every root,
where `⟨·,·⟩` is the form `TauCeti.invForm` on `H^*` dual to the Killing form, the highest root has
squared length `⟨θ, θ⟩ = 1 / h^∨` (`RootPairing.Base.invForm_root_highestRoot`).

The form `κ₀ = (2 h^∨)⁻¹ κ` is therefore normalised in both of the usual equivalent ways: it takes
the value `2` at the coroot of the highest root
(`RootPairing.Base.inv_smul_killingForm_coroot_highestRoot`), and the highest root has squared
length `2` for the form on `H^*` dual to it
(`RootPairing.Base.inv_smul_killingForm_apply_self_eq_two`). The second condition is phrased
without inverting `κ₀`: if `t ∈ H` represents `θ`, that is `κ₀(t, h) = θ(h)` for every `h ∈ H`,
then the dual squared length of `θ` is `κ₀(t, t)`.

Over an algebraically closed field every invariant form on `L` is a multiple of the Killing form
(`TauCeti.LieAlgebra.exists_eq_smul_killingForm`), so either normalisation characterises `κ₀`: an
invariant form `Φ` satisfies `κ = 2 h^∨ Φ` if and only if `Φ(θ^∨, θ^∨) = 2`
(`RootPairing.Base.killingForm_eq_smul_iff_apply_coroot_highestRoot_eq_two`), if and only if the
highest root has squared length `2` for the dual of `Φ`
(`RootPairing.Base.killingForm_eq_smul_iff_apply_self_eq_two`). Hence the form `κ_c = -½ κ`
defining the critical level is `-h^∨ κ₀`
(`RootPairing.Base.neg_inv_two_smul_killingForm_eq_neg_smul`).

The dual Coxeter number is also read off the Casimir scalar `TauCeti.casimirScalar`, the scalar
`⟨λ + ρ, λ + ρ⟩ - ⟨ρ, ρ⟩` by which the Casimir element of the Killing form acts on a highest weight
module of highest weight `λ`. At the highest root, the highest weight of the adjoint
representation, it is `1` (`RootPairing.Base.casimirScalar_root_highestRoot`), because the pairings
of `θ` with the positive roots add up to `⟨θ, θ⟩ (h^∨ - 1)` and `⟨θ, θ⟩ h^∨ = 1`. Rescaling the form
to `κ₀` multiplies the Casimir element by `2 h^∨`, so `h^∨` is half the Casimir scalar of the
adjoint representation for `κ₀`; the Casimir element of `κ₀` itself is not constructed here.

## Main results

* `RootPairing.Base.killingForm_coroot_highestRoot`: `κ(θ^∨, θ^∨) = 4 h^∨`.
* `RootPairing.Base.invForm_root_highestRoot`: `⟨θ, θ⟩ = 1 / h^∨` for the form dual to `κ`.
* `RootPairing.Base.killingForm_eq_smul_iff_apply_coroot_highestRoot_eq_two` and
  `RootPairing.Base.killingForm_eq_smul_iff_apply_self_eq_two`: `κ = 2 h^∨ κ₀` for the invariant
  form `κ₀` normalised by `κ₀(θ^∨, θ^∨) = 2`, or by squared length `2` of `θ` for its dual form.
* `RootPairing.Base.casimirScalar_root_highestRoot`: the Casimir scalar of the highest root is `1`.

## Implementation notes

The dual Coxeter number is defined from a base, through its highest root. The statements here hold
for every base; that `h^∨` does not depend on the base is not proved here.

## References

* V. G. Kac, *Infinite-Dimensional Lie Algebras*, 3rd ed., Chapter 6, for the normalised invariant
  form, the dual Coxeter number and the comparison `κ = 2 h^∨ κ₀`.
* E. Frenkel, *Langlands Correspondence for Loop Groups*, Chapters 1 and 2, for the normalisation of
  `κ₀` and the critical level `κ_c = -h^∨ κ₀ = -½ κ`.
-/

public section

open LieAlgebra LieAlgebra.IsKilling LieModule Module

namespace RootPairing.Base

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  [IsSimple K L] {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  (b : (rootSystem H).Base)

/-- **The coroot of the highest root has Killing length `4 h^∨`**, `κ(θ^∨, θ^∨) = 4 h^∨`. -/
theorem killingForm_coroot_highestRoot :
    killingForm K L ((rootSystem H).coroot b.highestRoot : L)
        ((rootSystem H).coroot b.highestRoot : L) =
      4 * (b.dualCoxeterNumber : K) := by
  have h := b.corootForm_coroot_highestRoot
  rwa [corootForm_rootSystem_eq_killing, LinearMap.BilinForm.restrict_apply,
    LinearMap.domRestrict_apply] at h

/-- **The highest root has squared length `1 / h^∨`** for the form `TauCeti.invForm` on `H^*` dual
to the Killing form, `⟨θ, θ⟩ = 1 / h^∨`. -/
theorem invForm_root_highestRoot :
    TauCeti.invForm ((rootSystem H).root b.highestRoot) ((rootSystem H).root b.highestRoot) =
      (b.dualCoxeterNumber : K)⁻¹ := by
  have h4 := TauCeti.traceForm_coroot_self_mul_invForm_self_eq_four
    (H.isNonZero_coe_root b.highestRoot)
  have hk := b.killingForm_coroot_highestRoot
  rw [rootSystem_coroot_apply, ← LinearMap.domRestrict_apply,
    ← LinearMap.BilinForm.restrict_apply, restrict_killingForm] at hk
  rw [hk] at h4
  rw [rootSystem_root_apply]
  exact eq_inv_of_mul_eq_one_left (by linear_combination h4 / 4)

/-- If `t ∈ H` represents the highest root for the form `e • κ`, then `e (e • κ)(t, t)` is the
squared length `1 / h^∨` of `θ` for the form dual to `κ`. -/
private theorem mul_smul_killingForm_apply_self (e : K) {t : H}
    (ht : ∀ h : H, (e • killingForm K L) t h = (rootSystem H).root b.highestRoot h) :
    e * (e • killingForm K L) t t = (b.dualCoxeterNumber : K)⁻¹ := by
  have hθ : cartanEquivDual H (e • t) = (rootSystem H).root b.highestRoot := by
    ext h
    rw [← ht, map_smul, LinearMap.smul_apply, TauCeti.cartanEquivDual_apply_apply_eq_killingForm,
      LinearMap.smul_apply, LinearMap.smul_apply]
  have h := TauCeti.invForm_cartanEquivDual_right ((rootSystem H).root b.highestRoot) (e • t)
  rw [hθ, b.invForm_root_highestRoot, map_smul, ← ht t, smul_eq_mul] at h
  exact h.symm

/-- **The normalised invariant form `κ₀ = (2 h^∨)⁻¹ κ` takes the value `2` at the coroot of the
highest root.** -/
theorem inv_smul_killingForm_coroot_highestRoot :
    ((2 * (b.dualCoxeterNumber : K))⁻¹ • killingForm K L) ((rootSystem H).coroot b.highestRoot : L)
        ((rootSystem H).coroot b.highestRoot : L) = 2 := by
  have := b.cast_dualCoxeterNumber_ne_zero
  rw [LinearMap.smul_apply, LinearMap.smul_apply, b.killingForm_coroot_highestRoot, smul_eq_mul]
  field_simp
  ring

/-- **The highest root has squared length `2` for the form on `H^*` dual to the normalised
invariant form `κ₀ = (2 h^∨)⁻¹ κ`**: if `t ∈ H` represents `θ` for `κ₀`, that is
`κ₀(t, h) = θ(h)` for every `h ∈ H`, then `κ₀(t, t) = 2`. -/
theorem inv_smul_killingForm_apply_self_eq_two {t : H}
    (ht : ∀ h : H, ((2 * (b.dualCoxeterNumber : K))⁻¹ • killingForm K L) t h =
      (rootSystem H).root b.highestRoot h) :
    ((2 * (b.dualCoxeterNumber : K))⁻¹ • killingForm K L) t t = 2 := by
  have hh := b.cast_dualCoxeterNumber_ne_zero
  have h := b.mul_smul_killingForm_apply_self _ ht
  generalize ((2 * (b.dualCoxeterNumber : K))⁻¹ • killingForm K L) t t = x at h ⊢
  field_simp at h
  linear_combination h

/-- **The Casimir scalar of the highest root is `1`**: `⟨θ + ρ, θ + ρ⟩ - ⟨ρ, ρ⟩ = 1`. This is the
scalar by which the Casimir element of the Killing form acts on a highest weight module of highest
weight `θ` (`TauCeti.casimir_smul_of_isHighestWeightVector_of_lieSpan_eq_top`). -/
theorem casimirScalar_root_highestRoot :
    TauCeti.casimirScalar b ((rootSystem H).root b.highestRoot) = 1 := by
  have := b.cast_dualCoxeterNumber_ne_zero (R := K)
  have hρ := TauCeti.invForm_coroot (TauCeti.weylVector (rootSystem H) b) b.highestRoot
  rw [← TauCeti.rootSystem_coroot'_apply, b.coroot'_highestRoot_weylVector,
    b.invForm_root_highestRoot] at hρ
  have hs := (TauCeti.invForm_isSymm (H := H)).eq ((rootSystem H).root b.highestRoot)
    (TauCeti.weylVector (rootSystem H) b)
  simp only [TauCeti.casimirScalar_def, map_add, LinearMap.add_apply, b.invForm_root_highestRoot,
    hs]
  field_simp at hρ ⊢
  linear_combination -hρ

variable [IsAlgClosed K]

/-- **The Killing form is `2 h^∨` times the invariant form normalised at the highest coroot**: an
invariant form `Φ` on a simple Lie algebra over an algebraically closed field of characteristic
zero satisfies `κ = 2 h^∨ Φ` if and only if `Φ(θ^∨, θ^∨) = 2`. -/
theorem killingForm_eq_smul_iff_apply_coroot_highestRoot_eq_two {Φ : LinearMap.BilinForm K L}
    (hΦ : Φ.lieInvariant L) :
    killingForm K L = (2 * (b.dualCoxeterNumber : K)) • Φ ↔
      Φ ((rootSystem H).coroot b.highestRoot : L) ((rootSystem H).coroot b.highestRoot : L) =
        2 := by
  have hh := b.cast_dualCoxeterNumber_ne_zero
  constructor
  · intro h
    rw [← inv_smul_eq_iff₀ (by simpa using hh)] at h
    rw [← h]
    exact b.inv_smul_killingForm_coroot_highestRoot
  · intro h
    obtain ⟨d, rfl⟩ := TauCeti.LieAlgebra.exists_eq_smul_killingForm hΦ
    rw [LinearMap.smul_apply, LinearMap.smul_apply, b.killingForm_coroot_highestRoot,
      smul_eq_mul] at h
    have hd : 2 * (b.dualCoxeterNumber : K) * d = 1 := by linear_combination h / 2
    rw [smul_smul, hd, one_smul]

/-- **The Killing form is `2 h^∨` times the invariant form for whose dual the highest root has
squared length `2`**: if `t ∈ H` represents `θ` for an invariant form `Φ` on a simple Lie algebra
over an algebraically closed field of characteristic zero, that is `Φ(t, h) = θ(h)` for every
`h ∈ H`, then `κ = 2 h^∨ Φ` if and only if `Φ(t, t) = 2`. -/
theorem killingForm_eq_smul_iff_apply_self_eq_two {Φ : LinearMap.BilinForm K L}
    (hΦ : Φ.lieInvariant L) {t : H} (ht : ∀ h : H, Φ t h = (rootSystem H).root b.highestRoot h) :
    killingForm K L = (2 * (b.dualCoxeterNumber : K)) • Φ ↔ Φ t t = 2 := by
  have hh := b.cast_dualCoxeterNumber_ne_zero
  constructor
  · intro h
    rw [← inv_smul_eq_iff₀ (by simpa using hh)] at h
    subst h
    exact b.inv_smul_killingForm_apply_self_eq_two ht
  · intro h
    obtain ⟨d, rfl⟩ := TauCeti.LieAlgebra.exists_eq_smul_killingForm hΦ
    have hd := b.mul_smul_killingForm_apply_self d ht
    rw [h] at hd
    field_simp at hd
    have hd' : 2 * (b.dualCoxeterNumber : K) * d = 1 := by linear_combination hd
    rw [smul_smul, hd', one_smul]

/-- **The critical level**: if the invariant form `Φ` is normalised by `Φ(θ^∨, θ^∨) = 2`, then
`κ_c = -½ κ` is `-h^∨ Φ`. -/
theorem neg_inv_two_smul_killingForm_eq_neg_smul {Φ : LinearMap.BilinForm K L}
    (hΦ : Φ.lieInvariant L)
    (h : Φ ((rootSystem H).coroot b.highestRoot : L) ((rootSystem H).coroot b.highestRoot : L) =
      2) :
    (-2⁻¹ : K) • killingForm K L = (-(b.dualCoxeterNumber : K)) • Φ := by
  rw [(b.killingForm_eq_smul_iff_apply_coroot_highestRoot_eq_two hΦ).mpr h, smul_smul]
  congr 1
  ring

end RootPairing.Base
