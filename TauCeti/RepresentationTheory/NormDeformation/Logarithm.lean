/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.GroupTheory.Transfer
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import TauCeti.RepresentationTheory.NormDeformation.Basic
public import TauCeti.GroupTheory.Transfer.Basic

/-!
# Logarithms and the coset derivative

Let `ρ : Γ →* R` be a multiplicative map from a finite group to a ring, and write `g` for `ρ g`.
For a homomorphism `c : Γ → ℤ/m` and a weight `f : ℤ/m → ℤ`, the *weighted norm*
`∑ f (c g) g` is additive in `f`. The constant weight `1` gives the norm `Nm = ∑ g`, and the
weight `valMinAbs`, which lifts `ℤ/m` to the representatives of least absolute value, gives the
*logarithm* of `c`. Multiplying by `g` shifts the weight by `c g`, so modulo `m` the logarithm
behaves like a derivative of the norm: `(γ - 1) L ≡ -Nm` when `c γ = 1`.

For a homomorphism `a : H → ℤ/m` on a subgroup `H`, the *coset derivative*
`∂ = -(∑ h) B(valMinAbs) (∑ h⁻¹)`, with `h` running over representatives of `Γ / H` and `B` the
weighted norm of `a` (or a multiple of it), is the first-order term at one auxiliary place. Its
defining property is that `n ∂ (g - 1)` is congruent to a multiple of the norm `Nm`, where
`∑ p⁻¹ Ψ p = n`.

A congruence `a ≡ b` is an equality `σ a = σ b` after a ring map `σ`. A ring map is a *reduction
modulo `m / k`* if it kills every `x` with `k x ∈ m R`.

## Main definitions

* `TauCeti.IsReductionMod σ m k`: `σ` kills every `x` with `k x ∈ m R`.
* `TauCeti.weightedNorm ρ c f`: the weighted norm `∑ f (c g) ρ g`.
* `TauCeti.cosetNorm ρ H`, `TauCeti.cosetNormInv ρ H`: the sums of `ρ h` and of `ρ h⁻¹` over the
  chosen representatives `h` of `Γ / H`.
* `TauCeti.cosetDerivative ρ H B`: the coset derivative `-(∑ h) B(valMinAbs) (∑ h⁻¹)`.

The components in `H` of the products `g h` are the cocycle `QuotientGroup.outCocycle`, and the
transfer is computed from it by `MonoidHom.transfer_eq_prod_out`.

## Main results

* `TauCeti.exists_isReductionMod`: if `R` has no `k`-torsion and `k μ = m`, there is a reduction
  modulo `m / k` whose kernel lies in `μ R`.
* `TauCeti.map_cosetNorm_mul_weightedNorm_mul_cosetNormInv`: `(∑ h) L(a) (∑ h⁻¹) ≡ L(Ver a)`,
  where `Ver a` is the transfer of `a` to `Γ`.
* `TauCeti.map_sub_one_mul_weightedNorm_valMinAbs`: `(γ - 1) L(c) ≡ -Nm` modulo `m` if `c γ = 1`.
* `TauCeti.map_valMinAbs_eq_zero_of_shift`: an additive map on weights that kills all
  differences `f (· - k) - f` kills the logarithm modulo `m / (2 k)`.
* `TauCeti.exists_map_nsmul_mul_sub_one_eq_sum_mul`: `n ∂ (g - 1) ≡ Nm Z` with `L Z = 0`, for
  every `L` that is right-invariant (`L g = L`) and kills `B 1`.

## References

The statements and their proofs are adapted from grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC), file `src/New/Congruences/FirstOrder/OnePrime.lean`
(`New.Patching.IsReductionMod`, `New.Patching.exists_isReductionMod`, `New.Patching.weightedSum`,
`New.Patching.cosetDerivative`, `New.Patching.map_cosetNorm_mul_weightedSum_mul_cosetNormInv`,
`New.Patching.map_sub_one_mul_weightedSum_valMinAbs`,
`New.Patching.map_valMinAbs_eq_zero_of_shift`,
`New.Patching.exists_map_nsmul_mul_sub_one_eq_sum_mul`). The use of a logarithm on the tame
inertia at an auxiliary prime as a first-order deformation goes back to Taylor and Wiles: R.
Taylor and A. Wiles, *Ring-theoretic properties of certain Hecke algebras*, Ann. of Math. 141
(1995).
-/

public section

open Finset ZMod

namespace TauCeti

universe u

section Reduction

variable {R S : Type*} [Ring R] [Ring S] {σ : R →+* S} {m k : ℕ}

/-- A ring map `σ` is a *reduction modulo `m / k`* if it kills every `x` with `k x ∈ m R`. Then a
congruence `a ≡ b` modulo `m / k` implies `σ a = σ b`; `exists_isReductionMod` gives a `σ` for
which the converse holds. -/
def IsReductionMod (σ : R →+* S) (m k : ℕ) : Prop :=
  ∀ x y : R, k • x = m • y → σ x = 0

theorem isReductionMod_iff : IsReductionMod σ m k ↔ ∀ x y : R, k • x = m • y → σ x = 0 :=
  Iff.rfl

/-- A reduction modulo `m / k` kills `m`. -/
theorem IsReductionMod.natCast_eq_zero (hσ : IsReductionMod σ m k) : (m : S) = 0 := by
  rw [← map_natCast σ]
  exact hσ m k (by rw [nsmul_eq_mul, nsmul_eq_mul, Nat.cast_comm])

/-- Let `R` be an `O`-algebra that has no `k`-torsion, and let `μ ∈ O` satisfy `k μ = m`. There
is a ring map `σ` on `R` that is a reduction modulo `m / k` (it kills `x` if `k x ∈ m R`) and
whose kernel lies in `μ R`. -/
theorem exists_isReductionMod {O : Type*} {R : Type u} [CommRing O] [Ring R] [Algebra O R]
    {μ : O} (hμ : (k : O) * μ = (m : O)) (hk : IsSMulRegular R k) :
    ∃ (S : Type u) (_ : Ring S) (σ : R →+* S),
      IsReductionMod σ m k ∧ ∀ a b : R, σ a = σ b → ∃ y : R, a - b = μ • y := by
  -- Take the quotient map `R → R / μ R`.
  let I : Ideal R := Ideal.span {algebraMap O R μ}
  have mem_I (x : R) : x ∈ I ↔ ∃ y : R, x = μ • y := by
    simp only [I, Ideal.mem_span_singleton', ← Algebra.commutes, ← Algebra.smul_def, eq_comm]
  have : I.IsTwoSided := ⟨fun {x} y hx ↦ by
    obtain ⟨x', rfl⟩ : ∃ x' : R, x = μ • x' := (mem_I x).1 hx
    exact (mem_I _).2 ⟨x' * y, smul_mul_assoc μ x' y⟩⟩
  refine ⟨R ⧸ I, inferInstance, Ideal.Quotient.mk I, fun x y hxy ↦ ?_,
    fun a b hab ↦ (mem_I _).1 (Ideal.Quotient.eq.1 hab)⟩
  have k_smul : k • x = k • μ • y := by
    rw [hxy, ← Nat.cast_smul_eq_nsmul O m, ← Nat.cast_smul_eq_nsmul O k, smul_smul, hμ]
  exact Ideal.Quotient.eq_zero_iff_mem.2 ((mem_I x).2 ⟨y, hk k_smul⟩)

/-- If `m = 0` in `S`, then only the weights modulo `m` matter: an additive map `B` on integer
weights takes weights that are congruent modulo `m` to elements with the same image under `σ`. -/
theorem map_eq_of_weights_modEq (hm : (m : S) = 0) {ι : Type*} (B : (ι → ℤ) →+ R)
    (f g : ι → ℤ) (h_congr : ∀ x : ι, (g x : ZMod m) = f x) : σ (B f) = σ (B g) := by
  choose d hd using fun x ↦ (intCast_eq_intCast_iff_dvd_sub (g x) (f x) m).1 (h_congr x)
  have h_sub : f = m • d + g := funext fun x ↦ by simp [← hd x]
  rw [h_sub, map_add, map_add, map_nsmul, map_nsmul, nsmul_eq_mul, hm, zero_mul, zero_add]

/-- **Shift-invariant maps kill the logarithm.** Let `σ` be a reduction modulo `m / (2 k)`, that is,
let it kill every `x` with `2 k x ∈ m R`. If an additive map `C` on weights `ℤ/m → ℤ` kills every `f
(· - k) - f`, then `σ` kills its value at the weight `valMinAbs`. -/
theorem map_valMinAbs_eq_zero_of_shift (hσ : IsReductionMod σ m (2 * k))
    (C : (ZMod m → ℤ) →+ R) (hC : ∀ f : ZMod m → ℤ, C ((fun x : ZMod m ↦ f (x - k)) - f) = 0) :
    σ (C valMinAbs) = 0 := by
  -- For `f x = x (x + k)` we have `f (x - k) - f x ≡ -2 k x` modulo `m`.
  let f (x : ZMod m) : ℤ := valMinAbs x * (valMinAbs x + k)
  have f_dvd (x : ZMod m) : ∃ d : ℤ, f (x - k) - f x + 2 * k * valMinAbs x = m * d :=
    (intCast_zmod_eq_zero_iff_dvd _ m).1 (by push_cast [f, coe_valMinAbs]; ring)
  choose d hd using f_dvd
  have f_diff : (fun x ↦ f (x - k)) - f + (2 * k) • valMinAbs = m • d :=
    funext fun x ↦ by simpa using hd x
  refine hσ (C valMinAbs) (C d) ?_
  rw [← map_nsmul, ← map_nsmul, ← f_diff, map_add, hC, zero_add]

end Reduction

variable {Γ R S : Type*} [Group Γ] [Fintype Γ] [Ring R] [Ring S] {m : ℕ} (ρ : Γ →* R)
  {σ : R →+* S}

section WeightedNorm

/-- The weighted norm `∑ f (c g) ρ g` of a homomorphism `c : Γ → ℤ/m`, as an additive function
of the weight `f : ℤ/m → ℤ`. The weight `1` gives the norm; the weight `valMinAbs`, which lifts
`ℤ/m` to `ℤ`, gives the logarithm of `c`. -/
def weightedNorm (c : Γ →* Multiplicative (ZMod m)) : (ZMod m → ℤ) →+ R :=
  .mk' (fun f ↦ ∑ g : Γ, f (c g).toAdd • ρ g) (by simp [add_smul, sum_add_distrib])

theorem weightedNorm_apply (c : Γ →* Multiplicative (ZMod m)) (f : ZMod m → ℤ) :
    weightedNorm ρ c f = ∑ g : Γ, f (c g).toAdd • ρ g :=
  (rfl)

/-- The weighted norm at the constant weight `1` is the norm `∑ ρ g`. -/
@[simp]
theorem weightedNorm_one (c : Γ →* Multiplicative (ZMod m)) :
    weightedNorm ρ c 1 = ∑ g : Γ, ρ g := by
  simp [weightedNorm_apply]

/-- Left multiplication by `ρ g` shifts the weight of the weighted norm `∑ f (c h) ρ h` by
`c g`. -/
theorem mul_weightedNorm (c : Γ →* Multiplicative (ZMod m)) (f : ZMod m → ℤ) (g : Γ) :
    ρ g * weightedNorm ρ c f = weightedNorm ρ c (fun x : ZMod m ↦ f (x - (c g).toAdd)) := by
  have shift (h : Γ) :
      ρ g * f (c h).toAdd • ρ h = f ((c (g * h)).toAdd - (c g).toAdd) • ρ (g * h) := by
    rw [map_mul c, map_mul ρ, toAdd_mul, add_sub_cancel_left, mul_smul_comm]
  rw [weightedNorm_apply, weightedNorm_apply, mul_sum]
  exact Fintype.sum_equiv (.mulLeft g) _ _ shift

/-- Right multiplication by `ρ g` shifts the weight of the weighted norm `∑ f (c h) ρ h` by
`c g`. -/
theorem weightedNorm_mul (c : Γ →* Multiplicative (ZMod m)) (f : ZMod m → ℤ) (g : Γ) :
    weightedNorm ρ c f * ρ g = weightedNorm ρ c (fun x : ZMod m ↦ f (x - (c g).toAdd)) := by
  have shift (h : Γ) :
      f (c h).toAdd • ρ h * ρ g = f ((c (h * g)).toAdd - (c g).toAdd) • ρ (h * g) := by
    rw [map_mul c, map_mul ρ, toAdd_mul, add_sub_cancel_right, smul_mul_assoc]
  rw [weightedNorm_apply, weightedNorm_apply, sum_mul]
  exact Fintype.sum_equiv (.mulRight g) _ _ shift

/-- **The logarithm is a derivative of the norm modulo `m`.** Let `σ : R → S` be a ring map with
`m = 0` in `S`, and let `L = ∑ valMinAbs (c g) ρ g` be the logarithm of a homomorphism
`c : Γ → ℤ/m` that sends `γ` to the generator `1`. Then `(ρ γ - 1) L ≡ -∑ ρ g`. -/
theorem map_sub_one_mul_weightedNorm_valMinAbs (hm : (m : S) = 0)
    (c : Γ →* Multiplicative (ZMod m)) {γ : Γ} (hγ : c γ = .ofAdd 1) :
    σ ((ρ γ - 1) * weightedNorm ρ c valMinAbs) = -σ (∑ g : Γ, ρ g) := by
  calc σ ((ρ γ - 1) * weightedNorm ρ c valMinAbs)
      = σ (weightedNorm ρ c ((fun x : ZMod m ↦ valMinAbs (x - 1)) - valMinAbs)) := by
        rw [sub_one_mul, mul_weightedNorm, ← map_sub, hγ, toAdd_ofAdd]
    _ = σ (weightedNorm ρ c (-1)) := map_eq_of_weights_modEq hm _ _ _ (by simp)
    _ = -σ (∑ g : Γ, ρ g) := by rw [map_neg, map_neg, weightedNorm_one]

end WeightedNorm

section Cosets

open scoped Classical in
/-- The sum `∑ ρ h` over the fixed representatives `h` of `Γ / H`, namely the elements `η.out`
that `Quotient.out` chooses in the cosets `η`. -/
noncomputable def cosetNorm (H : Subgroup Γ) : R := ∑ η : Γ ⧸ H, ρ η.out

open scoped Classical in
/-- The sum `∑ ρ h⁻¹` over the fixed representatives `h` of `Γ / H`. A sum `∑ f p ρ p` over `H`,
times this sum, is the sum over `Γ` in which `ρ (p h⁻¹)` has the weight `f p`. -/
noncomputable def cosetNormInv (H : Subgroup Γ) : R := ∑ η : Γ ⧸ H, ρ η.out⁻¹

/-- The coset derivative `∂ = -(∑ ρ h) B(valMinAbs) (∑ ρ h⁻¹)` attached to an additive map `B` on
weights `ℤ/m → ℤ`, where `h` runs over the fixed representatives of `Γ / H`. For the weighted norm
`B` of a homomorphism `a : H → ℤ/m`, the middle factor is the logarithm of `a`. -/
noncomputable def cosetDerivative (H : Subgroup Γ) (B : (ZMod m → ℤ) →+ R) : R :=
  -(cosetNorm ρ H * B valMinAbs * cosetNormInv ρ H)

open scoped Classical in
theorem cosetNorm_def (H : Subgroup Γ) : cosetNorm ρ H = ∑ η : Γ ⧸ H, ρ η.out :=
  (rfl)

open scoped Classical in
theorem cosetNormInv_def (H : Subgroup Γ) : cosetNormInv ρ H = ∑ η : Γ ⧸ H, ρ η.out⁻¹ :=
  (rfl)

theorem cosetDerivative_def (H : Subgroup Γ) (B : (ZMod m → ℤ) →+ R) :
    cosetDerivative ρ H B = -(cosetNorm ρ H * B valMinAbs * cosetNormInv ρ H) :=
  (rfl)

variable {H : Subgroup Γ}

/-- Let `h` run over the representatives `η.out` that `Quotient.out` chooses for the cosets
`η ∈ Γ / H`, so that `cosetNorm ρ H = ∑ ρ h`. For a weight `f : H → ℤ` and a coset `q`, the
product `(∑ ρ h) (∑_{p ∈ H} f p ρ p) ρ q.out⁻¹` is the sum over `g ∈ Γ` of `f p ρ g` with
`p = outCocycle g q`, the element of `H` in the unique factorisation `g q.out = h p`. -/
theorem cosetNorm_mul_sum_mul_out_inv [Fintype H] (f : H → ℤ) (q : Γ ⧸ H) :
    cosetNorm ρ H * (∑ p : H, f p • ρ p) * ρ q.out⁻¹ =
      ∑ g : Γ, f (QuotientGroup.outCocycle g q) • ρ g := by
  classical
  -- `g ↦ (g • q, outCocycle g q)` inverts `(η, p) ↦ η.out * p * q.out⁻¹`.
  have smul_eq (η : Γ ⧸ H) (p : H) : (η.out * p * q.out⁻¹) • q = η := by
    rw [← QuotientGroup.out_eq' (_ • q), QuotientGroup.mk_out_smul, inv_mul_cancel_right,
      QuotientGroup.mk_mul_of_mem _ p.property, QuotientGroup.out_eq']
  have cocycle_eq (η : Γ ⧸ H) (p : H) : QuotientGroup.outCocycle (η.out * p * q.out⁻¹) q = p :=
    Subtype.ext (by rw [QuotientGroup.coe_outCocycle, smul_eq]; simp [mul_assoc])
  rw [cosetNorm_def, sum_mul_sum, ← sum_product', sum_mul]
  refine sum_nbij' (fun (η, p) ↦ η.out * p * q.out⁻¹)
    (fun g ↦ (g • q, QuotientGroup.outCocycle g q)) (by simp) (by simp)
    (fun x _ ↦ by simp [smul_eq, cocycle_eq]) (fun g _ ↦ ?_) ?_
  · simp [mul_assoc]
  rintro ⟨η, p⟩ -
  simp only [cocycle_eq, map_mul, mul_smul_comm, smul_mul_assoc]

/-- The coset norm times the norm of `H` is the norm of `Γ`. -/
theorem cosetNorm_mul_norm [Fintype H] : cosetNorm ρ H * ∑ p : H, ρ p = ∑ g : Γ, ρ g := by
  -- Multiply the case `f = 1` of `cosetNorm_mul_sum_mul_out_inv` by `ρ q.out` on the right.
  let q : Γ ⧸ H := ↑(1 : Γ)
  have h := congrArg (· * ρ q.out) (cosetNorm_mul_sum_mul_out_inv ρ (H := H) 1 q)
  simp only [Pi.one_apply, one_smul, mul_assoc, ← map_mul, inv_mul_cancel, map_one,
    mul_one] at h
  rw [h, sum_mul]
  exact Fintype.sum_equiv (.mulRight q.out) _ _ fun g ↦ (map_mul ρ g q.out).symm

/-- **The coset norms carry a logarithm to the logarithm of its transfer.** Let `σ : R → S` be a
ring map with `m = 0` in `S`. For a homomorphism `c` to `ℤ/m` let `L c = ∑ valMinAbs (c g) ρ g`
be its logarithm. For `a : H → ℤ/m` on a subgroup `H`, the elements `(∑ ρ h) (L a) (∑ ρ h⁻¹)`
and `L a.transfer` have the same image under `σ`, where `h` runs over the fixed representatives
of `Γ / H` and `a.transfer` is the transfer of `a` from `H` to `Γ`. -/
theorem map_cosetNorm_mul_weightedNorm_mul_cosetNormInv [Fintype H] (hm : (m : S) = 0)
    (a : H →* Multiplicative (ZMod m)) :
    σ (cosetNorm ρ H * weightedNorm (ρ.comp H.subtype) a valMinAbs * cosetNormInv ρ H) =
      σ (weightedNorm ρ a.transfer valMinAbs) := by
  classical
  -- The coefficient of `g` on the left is the sum over the representatives `h` of the logarithms
  -- of the components of `g h`, which is congruent modulo `m` to the logarithm of the transfer.
  let C : (Γ → ℤ) →+ R := (Fintype.linearCombination ℤ ρ).toAddMonoidHom
  let weight (η : Γ ⧸ H) (g : Γ) : ℤ := valMinAbs (a (QuotientGroup.outCocycle g η)).toAdd
  have h_term (η : Γ ⧸ H) :
      cosetNorm ρ H * weightedNorm (ρ.comp H.subtype) a valMinAbs * ρ η.out⁻¹ = C (weight η) :=
    cosetNorm_mul_sum_mul_out_inv ρ (fun p ↦ valMinAbs (a p).toAdd) η
  have h_weights (g : Γ) :
      (valMinAbs (a.transfer g).toAdd : ZMod m) = (∑ η : Γ ⧸ H, weight η) g := by
    simp [weight, MonoidHom.transfer_eq_prod_out, toAdd_prod]
  calc σ (cosetNorm ρ H * weightedNorm (ρ.comp H.subtype) a valMinAbs * cosetNormInv ρ H)
      = σ (C (∑ η : Γ ⧸ H, weight η)) := by
        simp only [cosetNormInv_def, map_sum C, mul_sum, h_term]
    _ = σ (weightedNorm ρ a.transfer valMinAbs) := map_eq_of_weights_modEq hm C _ _ h_weights

/-- Let `σ : R → S` be a ring map with `m = 0` in `S`, let `a : H → ℤ/m` be a homomorphism on a
subgroup `H`, and let `B` be an additive map on weights `ℤ/m → ℤ` such that right multiplication
by `ρ p` shifts the weight by `a p`, as for the weighted norm over `H` or a fixed left multiple of
it. Then `B valMinAbs * (∑ ρ h⁻¹) * (ρ g - 1)` has the same image under `σ` as a right multiple
`B 1 * Q` of the value of `B` at the constant weight `1`. Here `h` runs over the fixed
representatives of `Γ / H`. -/
theorem exists_map_valMinAbs_mul_sub_one (hm : (m : S) = 0) (a : H →* Multiplicative (ZMod m))
    (B : (ZMod m → ℤ) →+ R)
    (hB : ∀ (f : ZMod m → ℤ) (p : H), B f * ρ p = B fun x : ZMod m ↦ f (x - (a p).toAdd))
    (g : Γ) :
    ∃ Q : R, σ (B valMinAbs * cosetNormInv ρ H * (ρ g - 1)) = σ (B 1 * Q) := by
  classical
  -- Right multiplication by `g` permutes the `h⁻¹` up to factors in `H`, which shift the weight
  -- by a constant.
  let k (η : Γ ⧸ H) : ZMod m := (a (QuotientGroup.outCocycle g η)).toAdd
  have permute : cosetNormInv ρ H * ρ g =
      ∑ η : Γ ⧸ H, ρ (QuotientGroup.outCocycle g η) * ρ η.out⁻¹ := by
    have term_eq (η : Γ ⧸ H) : ρ (QuotientGroup.outCocycle g η) * ρ η.out⁻¹ =
        ρ (MulAction.toPerm g η).out⁻¹ * ρ g := by
      simp [mul_assoc, ← map_mul]
    rw [cosetNormInv_def, sum_mul]
    exact (Fintype.sum_equiv (MulAction.toPerm g) _ _ term_eq).symm
  have shift (y : ZMod m) :
      σ (B fun x ↦ valMinAbs (x - y)) = σ (B valMinAbs - valMinAbs y • B 1) := by
    rw [← map_zsmul, ← map_sub]
    exact map_eq_of_weights_modEq hm B _ _ (by simp)
  have term_congr (η : Γ ⧸ H) :
      σ (B valMinAbs * (ρ (QuotientGroup.outCocycle g η) * ρ η.out⁻¹ - ρ η.out⁻¹)) =
        σ (B 1 * -(valMinAbs (k η) • ρ η.out⁻¹)) :=
    calc σ (B valMinAbs * (ρ (QuotientGroup.outCocycle g η) * ρ η.out⁻¹ - ρ η.out⁻¹))
        = (σ (B fun x ↦ valMinAbs (x - k η)) - σ (B valMinAbs)) * σ (ρ η.out⁻¹) := by
          rw [mul_sub, ← mul_assoc, hB, ← sub_mul, map_mul, map_sub]
      _ = σ (-(valMinAbs (k η) • B 1) * ρ η.out⁻¹) := by
          rw [shift, ← map_sub, sub_sub_cancel_left, map_mul]
      _ = σ (B 1 * -(valMinAbs (k η) • ρ η.out⁻¹)) := by
          rw [neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm]
  refine ⟨∑ η : Γ ⧸ H, -(valMinAbs (k η) • ρ η.out⁻¹), ?_⟩
  rw [mul_assoc, mul_sub_one, permute, cosetNormInv_def, ← sum_sub_distrib, mul_sum, mul_sum,
    map_sum, map_sum]
  exact sum_congr rfl fun η _ ↦ term_congr η

/-- **The coset derivative is a first-order deformation of the norm.** Let `σ : R → S` be a ring map
with `m = 0` in `S`. Let `a : H → ℤ/m` be a homomorphism on a subgroup `H`, let `B` be an additive
map on weights `ℤ/m → ℤ` such that right multiplication by `p ∈ H` shifts the weight by `a p`, and
let `∂ = cosetDerivative ρ H B` be `-(∑ h) B(valMinAbs) (∑ h⁻¹)`, with `h` running over the fixed
representatives of `Γ / H`. Let `H` fix `B 1` from the left, let `∑ p⁻¹ Ψ p = n` over `H`, and let
`L g = L` for all `g` and `L (B 1) = 0`. If `R` has no `#H`-torsion, then `n ∂ (g - 1) ≡ Nm Z` for
some `Z` with `L Z = 0`. -/
theorem exists_map_nsmul_mul_sub_one_eq_sum_mul [Fintype H] (hm : (m : S) = 0)
    (a : H →* Multiplicative (ZMod m)) (B : (ZMod m → ℤ) →+ R)
    (hB : ∀ (f : ZMod m → ℤ) (p : H), B f * ρ p = B fun x : ZMod m ↦ f (x - (a p).toAdd))
    (hB_fixed : ∀ p : H, ρ p * B 1 = B 1) {Ψ L : R} {n : ℕ}
    (hΨ : ∑ p : H, ρ ↑p⁻¹ * Ψ * ρ p = n) (hL : ∀ g : Γ, L * ρ g = L) (hLB : L * B 1 = 0)
    (h_regular : IsSMulRegular R (Fintype.card H)) (g : Γ) :
    ∃ Z : R,
      σ (n • (cosetDerivative ρ H B * (ρ g - 1))) = σ ((∑ k : Γ, ρ k) * Z) ∧ L * Z = 0 := by
  obtain ⟨Q, hQ⟩ : ∃ Q : R, σ (B valMinAbs * cosetNormInv ρ H * (ρ g - 1)) = σ (B 1 * Q) :=
    exists_map_valMinAbs_mul_sub_one ρ hm a B hB g
  have nsmul_B_one : n • B 1 = (∑ p : H, ρ p) * Ψ * B 1 :=
    nsmul_eq_norm_mul (ρ := ρ.comp H.subtype) hΨ hB_fixed
  refine ⟨-(Ψ * B 1 * Q), ?_, ?_⟩
  · calc σ (n • (cosetDerivative ρ H B * (ρ g - 1)))
        = -(σ (cosetNorm ρ H) * n • σ (B valMinAbs * cosetNormInv ρ H * (ρ g - 1))) := by
          simp only [cosetDerivative_def, neg_mul, smul_neg, map_neg, map_nsmul, map_mul,
            mul_smul_comm, mul_assoc]
      _ = σ (-(cosetNorm ρ H * (n • B 1 * Q))) := by
          simp only [hQ, map_neg, map_nsmul, map_mul, smul_mul_assoc]
      _ = σ ((∑ g, ρ g) * -(Ψ * B 1 * Q)) := by
          simp only [nsmul_B_one, ← cosetNorm_mul_norm ρ (H := H), mul_neg, mul_assoc]
  · have L_mul_eq_zero : L * (Ψ * B 1) = 0 := h_regular <|
      calc Fintype.card H • (L * (Ψ * B 1)) = L * ((∑ p : H, ρ p) * Ψ * B 1) := by
            simp only [sum_mul, mul_sum, ← mul_assoc, hL, sum_const, card_univ]
        _ = Fintype.card H • (0 : R) := by rw [← nsmul_B_one, mul_smul_comm, hLB, smul_zero,
            smul_zero]
    rw [mul_neg, ← mul_assoc, L_mul_eq_zero, zero_mul, neg_zero]

end Cosets

end TauCeti
