/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Tame.Quotient
public import TauCeti.RingTheory.RootsOfUnity.PadicTateTwist

/-!
# The `ℓ`-adic tame character

Let `K` be a nonarchimedean local field with residue characteristic `p` and residue field of order
`q`, and let `I_K` be its inertia group. The tame character
`I_K → ℤ̂^{(p')}(1) = lim_{p ∤ m} μ_m(K^{alg})`, `σ ↦ (σ(π^{1/m})/π^{1/m})_m`, identifies the tame
inertia group `I_K/P_K` with `ℤ̂^{(p')}(1)`, which as a profinite group is `∏_{ℓ ≠ p} ℤ_ℓ`. This
file specializes it at a single `ℓ` prime to `p`: keeping only the components at the powers
`ℓ ^ n` gives the **`ℓ`-adic tame character**

`t_ℓ : I_K →ₜ* ℤ_ℓ(1) = lim_n μ_{ℓ ^ n}(K^{alg})`, `σ ↦ (σ(π^{1/ℓ^n})/π^{1/ℓ^n})_n`.

It inherits from the tame character:

* its independence of the uniformizer `π` and of the chosen roots `π^{1/ℓ^n}`;
* surjectivity, since the tame character is onto at every finite level and `I_K` is compact;
* triviality on wild inertia; more precisely, `σ ∈ I_K` has trivial `ℓ`-adic tame character
  exactly when it fixes every `ℓ ^ n`-th root of `π`;
* the twist: conjugation by `g ∈ G_K` acts on `ℤ_ℓ(1)` through the action of `g` on the
  `ℓ`-power roots of unity, so that conjugation by an arithmetic Frobenius lift is `x ↦ x ^ q`.

## Main definitions

* `TauCeti.inertiaPadicTameCharacter K hℓ`: the `ℓ`-adic tame character
  `I_K →ₜ* ℤ_ℓ(1)`, written multiplicatively, for `ℓ` prime to `p`.

## Main results

* `TauCeti.coe_proj_inertiaPadicTameCharacter_apply`: its level-`n` component at `σ` is `σ(α)/α`
  for every root `α` of `X ^ (ℓ ^ n) − π`, for any uniformizer `π`.
* `TauCeti.inertiaPadicTameCharacter_surjective`: it is surjective.
* `TauCeti.inertiaPadicTameCharacter_eq_one_iff`: its kernel consists of the elements of inertia
  fixing every `ℓ ^ n`-th root of a uniformizer.
* `TauCeti.inertiaPadicTameCharacter_eq_one_of_mem_wildInertiaSubgroup`: it is trivial on wild
  inertia.
* `TauCeti.inertiaPadicTameCharacter_conj`: it is equivariant for conjugation by `G_K` and the
  Galois action on `ℤ_ℓ(1)`, for a prime `ℓ`.
* `TauCeti.IsArithFrobeniusLift.inertiaPadicTameCharacter_conj`: conjugation by an arithmetic
  Frobenius lift raises it to the `q`-th power.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, (7.5.2).
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2.
-/

public section

noncomputable section

namespace TauCeti

open PadicTateTwist ValuativeRel

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {ℓ : ℕ}

/-- **The `ℓ`-adic tame character** of `K`, for `ℓ` prime to the residue characteristic `p`: the
continuous homomorphism `I_K →ₜ* ℤ_ℓ(1)`, written multiplicatively, sending `σ` to
`(σ(π^{1/ℓ^n})/π^{1/ℓ^n})_n` for a uniformizer `π` and any `ℓ ^ n`-th roots `π^{1/ℓ^n}` of it
(`TauCeti.coe_proj_inertiaPadicTameCharacter_apply`). It is the specialization at `ℓ` of the tame
character `I_K →ₜ* ℤ̂^{(p')}(1)`. -/
def inertiaPadicTameCharacter (hℓ : ℓ.Coprime (ringChar 𝓀[K])) :
    inertiaSubgroup K →ₜ* Multiplicative (PadicTateTwist ℓ (AlgebraicClosure K)) :=
  have : NeZero ℓ := ⟨ne_zero_of_coprime_ringChar hℓ⟩
  (PrimeToPTateModule.toPadicTateTwist ℓ hℓ).comp (inertiaTameCharacter K)

variable {K} {hℓ : ℓ.Coprime (ringChar 𝓀[K])}

/-- The `ℓ`-adic tame character is the `ℓ`-adic component of the tame character. -/
theorem inertiaPadicTameCharacter_apply [NeZero ℓ] (σ : inertiaSubgroup K) :
    inertiaPadicTameCharacter K hℓ σ =
      PrimeToPTateModule.toPadicTateTwist ℓ hℓ (inertiaTameCharacter K σ) :=
  (rfl)

/-- **The `ℓ`-adic tame character at level `n`.** For a uniformizer `π` of `K` and any root `α` of
`X ^ (ℓ ^ n) − π`, the `ℓ ^ n`-th roots-of-unity component of the `ℓ`-adic tame character at
`σ ∈ I_K` is `σ(α)/α`. -/
theorem coe_proj_inertiaPadicTameCharacter_apply {σ : Gal(AlgebraicClosure K/K)}
    (hσ : σ ∈ inertiaSubgroup K) {π : Kˣ} (hπ : IsUniformizer K π) (n : ℕ)
    {α : AlgebraicClosure K} (hα : α ^ ℓ ^ n = algebraMap K (AlgebraicClosure K) π) :
    (((proj n (inertiaPadicTameCharacter K hℓ ⟨σ, hσ⟩).toAdd).toMul :
      (AlgebraicClosure K)ˣ) : AlgebraicClosure K) = σ α / α := by
  have : NeZero ℓ := ⟨ne_zero_of_coprime_ringChar hℓ⟩
  rw [inertiaPadicTameCharacter_apply, PrimeToPTateModule.proj_toPadicTateTwist, toMul_ofMul]
  exact coe_proj_inertiaTameCharacter_apply hσ hπ _ hα

variable (K hℓ) in
/-- **The `ℓ`-adic tame character is surjective**: it is onto at each finite level, because the
tame character is (`TauCeti.proj_inertiaTameCharacter_surjective`), and `I_K` is compact. -/
theorem inertiaPadicTameCharacter_surjective :
    Function.Surjective (inertiaPadicTameCharacter K hℓ) := by
  have : NeZero ℓ := ⟨ne_zero_of_coprime_ringChar hℓ⟩
  have : CompactSpace (inertiaSubgroup K) :=
    isCompact_iff_compactSpace.1 (isClosed_inertiaSubgroup K).isCompact
  have h := TateModule.surjective_of_forall_surjective_proj
    (f := fun σ ↦ (inertiaPadicTameCharacter K hℓ σ).toAdd)
    (continuous_toAdd.comp (map_continuous _)) fun n y ↦ by
      obtain ⟨σ, hσ⟩ := proj_inertiaTameCharacter_surjective K
        ⟨ℓ ^ n, pow_ne_zero n (NeZero.ne ℓ), hℓ.pow_left n⟩
        (levelAddEquivRootsOfUnity n y).toMul
      refine ⟨σ, (levelAddEquivRootsOfUnity n).injective ?_⟩
      rw [← proj_def, inertiaPadicTameCharacter_apply, PrimeToPTateModule.proj_toPadicTateTwist]
      exact congrArg Additive.ofMul hσ
  exact fun y ↦ (h y.toAdd).imp fun _ ↦ congrArg Multiplicative.ofAdd

/-- **The kernel of the `ℓ`-adic tame character**: `σ ∈ I_K` has trivial `ℓ`-adic tame character
exactly when it fixes every `ℓ ^ n`-th root of a uniformizer `π`, for every `n`. -/
theorem inertiaPadicTameCharacter_eq_one_iff {σ : Gal(AlgebraicClosure K/K)}
    (hσ : σ ∈ inertiaSubgroup K) {π : Kˣ} (hπ : IsUniformizer K π) :
    inertiaPadicTameCharacter K hℓ ⟨σ, hσ⟩ = 1 ↔
      ∀ (n : ℕ) (α : AlgebraicClosure K), α ^ ℓ ^ n = algebraMap K (AlgebraicClosure K) π →
        σ α = α := by
  have hne (n : ℕ) {α : AlgebraicClosure K}
      (hα : α ^ ℓ ^ n = algebraMap K (AlgebraicClosure K) π) : α ≠ 0 :=
    ne_zero_pow (pow_ne_zero n (ne_zero_of_coprime_ringChar hℓ)) (by simp [hα])
  constructor
  · intro h n α hα
    have h' := coe_proj_inertiaPadicTameCharacter_apply (hℓ := hℓ) hσ hπ n hα
    rwa [h, toAdd_one, map_zero, toMul_zero, OneMemClass.coe_one, Units.val_one, eq_comm,
      div_eq_one_iff_eq (hne n hα)] at h'
  · intro h
    refine Multiplicative.toAdd.injective <| PadicTateTwist.ext fun n ↦ ?_
    refine Additive.toMul.injective <| Subtype.ext <| Units.ext ?_
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) π)
      (pow_pos (Nat.pos_of_ne_zero (ne_zero_of_coprime_ringChar hℓ)) n)
    rw [coe_proj_inertiaPadicTameCharacter_apply hσ hπ n hα, h n α hα, div_self (hne n hα)]
    simp

/-- **The `ℓ`-adic tame character is trivial on wild inertia**, as the tame character is
(`TauCeti.inertiaTameCharacter_eq_one_iff`). -/
theorem inertiaPadicTameCharacter_eq_one_of_mem_wildInertiaSubgroup
    {σ : Gal(AlgebraicClosure K/K)} (hσ : σ ∈ inertiaSubgroup K)
    (hσ' : σ ∈ wildInertiaSubgroup K) : inertiaPadicTameCharacter K hℓ ⟨σ, hσ⟩ = 1 := by
  have : NeZero ℓ := ⟨ne_zero_of_coprime_ringChar hℓ⟩
  rw [inertiaPadicTameCharacter_apply, (inertiaTameCharacter_eq_one_iff hσ).2 hσ', map_one]

/-- **The `ℓ`-adic tame character is `G_K`-equivariant**, for a prime `ℓ`: conjugating an element
of inertia by `g ∈ G_K` applies to its `ℓ`-adic tame character the Galois representation of `g`
on `ℤ_ℓ(1)`, that is, `g` acting on the `ℓ`-power roots of unity. This is the twist `(1)` in
`ℤ_ℓ(1)`. -/
theorem inertiaPadicTameCharacter_conj [Fact ℓ.Prime] (g : Gal(AlgebraicClosure K/K))
    {σ : Gal(AlgebraicClosure K/K)} (hσ : σ ∈ inertiaSubgroup K) :
    inertiaPadicTameCharacter K hℓ ⟨g * σ * g⁻¹, (inertiaSubgroup_normal K).conj_mem σ hσ g⟩ =
      .ofAdd (galoisRepresentation g (inertiaPadicTameCharacter K hℓ ⟨σ, hσ⟩).toAdd) := by
  rw [inertiaPadicTameCharacter_apply, inertiaTameCharacter_conj,
    PrimeToPTateModule.toPadicTateTwist_smul, inertiaPadicTameCharacter_apply]

/-- **Conjugation by a Frobenius lift is the `q`-th power on the `ℓ`-adic tame character**: for an
arithmetic Frobenius lift `φ` and `σ ∈ I_K`, `t_ℓ(φ σ φ⁻¹) = t_ℓ(σ) ^ q`, since `φ` raises every
root of unity of order prime to `p` to the `q`-th power. -/
theorem IsArithFrobeniusLift.inertiaPadicTameCharacter_conj {φ : Gal(AlgebraicClosure K/K)}
    (hφ : IsArithFrobeniusLift K φ) {σ : Gal(AlgebraicClosure K/K)}
    (hσ : σ ∈ inertiaSubgroup K) :
    inertiaPadicTameCharacter K hℓ ⟨φ * σ * φ⁻¹, (inertiaSubgroup_normal K).conj_mem σ hσ φ⟩ =
      inertiaPadicTameCharacter K hℓ ⟨σ, hσ⟩ ^ Nat.card 𝓀[K] := by
  have : NeZero ℓ := ⟨ne_zero_of_coprime_ringChar hℓ⟩
  rw [inertiaPadicTameCharacter_apply, inertiaTameCharacter_conj, hφ.smul_eq_pow, map_pow,
    inertiaPadicTameCharacter_apply]

end TauCeti
