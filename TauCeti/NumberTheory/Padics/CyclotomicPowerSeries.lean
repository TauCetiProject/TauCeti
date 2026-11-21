/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Expand
public import TauCeti.NumberTheory.Padics.BinomialSeries
import TauCeti.RingTheory.PowerSeries.Binomial
import TauCeti.RingTheory.PowerSeries.OneAddXPow

/-!
# The cyclotomic operators `φ` and `γ_a` on `𝒪⟦π⟧`

Let `𝒪` be a `ℤ_p`-algebra, for instance the Witt vectors `W(k)` of a perfect field `k` of
characteristic `p`, an algebra over `ℤ_p = W(𝔽_p)`. The power series ring `𝒪⟦π⟧` is the ring
`A⁺` of `p`-adic Hodge theory and of the theory of `(φ, Γ)`-modules, the coordinate `π` standing
for `[ε] - 1`. It carries two families of operators, both defined by substitution into the
binomial series `(1 + π) ^ a = ∑ₙ (a choose n) πⁿ`, whose coefficients are integral since `ℤ_p`
is a binomial ring:

* for `a ∈ ℤ_p`, the `𝒪`-algebra endomorphism `γ_a : f(π) ↦ f((1 + π) ^ a - 1)`
  (`TauCeti.cyclotomicSubst`). The composition law `γ_a ∘ γ_b = γ_(a b)` makes `a ↦ γ_a` a
  monoid homomorphism from the multiplicative monoid of `ℤ_p`, so the units `ℤ_pˣ`, the image of
  the cyclotomic character, act by `𝒪`-algebra automorphisms (`TauCeti.cyclotomicGamma`). When
  `a` is not a unit of `𝒪`, for instance `a = p` with `𝒪 = W(k)`, `γ_a` is not surjective.
* for an `ℤ_p`-algebra endomorphism `σ` of `𝒪`, such as the Witt vector Frobenius, the Frobenius
  `φ_σ(f)(π) = f^σ((1 + π) ^ p - 1)`, where `f^σ` applies `σ` to the coefficients
  (`TauCeti.cyclotomicFrobenius p σ`). It is the composite `γ_p ∘ (f ↦ f^σ)`, so it commutes
  with every `γ_a`. When `σ` lifts the `p`-th power map of a ring `k` of characteristic `p`,
  `φ_σ` reduces to the `p`-th power map of `k⟦π⟧`.

The element `φ(π) = (1 + π) ^ p - 1` factors as `π q` with `q = ∑_{i < p} (1 + π) ^ i`, whose
constant coefficient is `p`; in particular `π` is not in the image of `φ` when `p` is not a unit
of `𝒪`.

## Main definitions

* `TauCeti.cyclotomicSubst 𝒪`: the monoid homomorphism `a ↦ γ_a` from `ℤ_p` to the
  `𝒪`-algebra endomorphisms of `𝒪⟦X⟧`.
* `TauCeti.cyclotomicGamma 𝒪`: its restriction `ℤ_pˣ →* (𝒪⟦X⟧ ≃ₐ[𝒪] 𝒪⟦X⟧)`.
* `TauCeti.cyclotomicFrobenius p σ`: the `σ`-semilinear Frobenius `f ↦ f^σ((1 + X) ^ p - 1)`.

## Main results

* `TauCeti.cyclotomicSubst_X`, `TauCeti.cyclotomicSubst_binomialSeries`: `γ_a(X) = (1 + X) ^ a - 1`
  and `γ_a((1 + X) ^ b) = (1 + X) ^ (a b)`.
* `TauCeti.exists_cyclotomicSubst_X_eq`: for a unit `a`, `γ_a(X) = a X (1 + h_a)` with
  `h_a ∈ X ℤ_p⟦X⟧`.
* `TauCeti.one_add_X_mul_cyclotomicSubst_neg_one_X`: `γ_(-1)(X) = -X / (1 + X)`.
* `TauCeti.coeff_one_cyclotomicSubst`: the linear coefficient of `γ_a(f)` is `a` times that of
  `f`.
* `TauCeti.X_notMem_range_cyclotomicSubst`: if `a` is not a unit of `𝒪`, then `X` is not in the
  image of `γ_a`.
* `TauCeti.cyclotomicSubst_injective`: `γ_a` is injective when `(1 + X) ^ a - 1 ≠ 0` and `𝒪` has
  no zero divisors.
* `TauCeti.continuous_cyclotomicSubst`: `(a, f) ↦ γ_a(f)` is jointly continuous.
* `TauCeti.map_cyclotomicSubst`: `γ_a` commutes with `ℤ_p`-algebra maps on coefficients.
* `TauCeti.cyclotomicFrobenius_X`, `TauCeti.cyclotomicFrobenius_C`,
  `TauCeti.cyclotomicFrobenius_X_eq_X_mul`: the values of `φ` on `X` and on constants, and the
  factorization `φ(X) = X q`.
* `TauCeti.cyclotomicFrobenius_cyclotomicSubst`: `φ ∘ γ_a = γ_a ∘ φ`.
* `TauCeti.cyclotomicFrobenius_injective`: `φ` is injective when `σ` is and `𝒪` has no zero
  divisors.
* `TauCeti.map_cyclotomicFrobenius`: `φ` reduces to the `p`-th power map modulo `p`.
* `TauCeti.X_notMem_range_cyclotomicFrobenius`: `X` is not in the image of `φ` when `p` is not a
  unit of `𝒪`.

## References

* J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois representations*, §4.3 (the operators
  `φ` and `γ` on `A⁺`, (4.10)).
* L. Berger, *Équations différentielles p-adiques et (φ, N)-modules filtrés*, Astérisque 319
  (2008), §I.2.
-/

public section

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace TauCeti

variable {p : ℕ} [Fact p.Prime] (O : Type*) [CommRing O] [Algebra ℤ_[p] O]

/-- The cyclotomic substitutions `γ_a : f(X) ↦ f((1 + X) ^ a - 1)` on `O⟦X⟧`, for `a ∈ ℤ_p`, as a
monoid homomorphism from the multiplicative monoid of `ℤ_p` to the `O`-algebra endomorphisms of
`O⟦X⟧`: `γ_1` is the identity and `γ_(a b) = γ_a ∘ γ_b`. -/
noncomputable def cyclotomicSubst : ℤ_[p] →* (O⟦X⟧ →ₐ[O] O⟦X⟧) where
  toFun a := substAlgHom (hasSubst_binomialSeries_sub_one a)
  map_one' := AlgHom.ext fun f ↦ by
    rw [coe_substAlgHom, binomialSeries_one, add_sub_cancel_left, X_subst, AlgHom.one_apply]
  map_mul' a b := AlgHom.ext fun f ↦ by
    rw [AlgHom.mul_apply, coe_substAlgHom, coe_substAlgHom, coe_substAlgHom,
      subst_comp_subst_apply (hasSubst_binomialSeries_sub_one b)
        (hasSubst_binomialSeries_sub_one a), subst_sub (hasSubst_binomialSeries_sub_one a),
      subst_one, subst_binomialSeries_sub_one]

variable {O}

theorem cyclotomicSubst_apply (a : ℤ_[p]) (f : O⟦X⟧) :
    cyclotomicSubst O a f = f.subst (binomialSeries O a - 1) := by
  simp [cyclotomicSubst, coe_substAlgHom]

@[simp]
theorem cyclotomicSubst_X (a : ℤ_[p]) : cyclotomicSubst O a X = binomialSeries O a - 1 := by
  rw [cyclotomicSubst_apply, subst_X (hasSubst_binomialSeries_sub_one a)]

@[simp]
theorem cyclotomicSubst_C (a : ℤ_[p]) (c : O) : cyclotomicSubst O a (C c) = C c :=
  (cyclotomicSubst O a).commutes c

/-- `γ_a` sends the binomial series `(1 + X) ^ b` to `(1 + X) ^ (a b)`. -/
@[simp]
theorem cyclotomicSubst_binomialSeries (a b : ℤ_[p]) :
    cyclotomicSubst O a (binomialSeries O b) = binomialSeries O (a * b) := by
  rw [cyclotomicSubst_apply, subst_binomialSeries_sub_one]

theorem cyclotomicSubst_one_add_X (a : ℤ_[p]) :
    cyclotomicSubst O a (1 + X) = binomialSeries O a := by
  simp

/-- For a natural number `n`, `γ_n` is the substitution `X ↦ (1 + X) ^ n - 1`. -/
theorem cyclotomicSubst_natCast_apply (n : ℕ) (f : O⟦X⟧) :
    cyclotomicSubst O (n : ℤ_[p]) f = f.subst ((1 + X) ^ n - 1 : O⟦X⟧) := by
  rw [cyclotomicSubst_apply, binomialSeries_nat]

/-- The linear coefficient of `γ_a(X)` is `a`. -/
theorem coeff_one_cyclotomicSubst_X (a : ℤ_[p]) :
    coeff 1 (cyclotomicSubst O a X) = algebraMap ℤ_[p] O a := by
  simp [Algebra.smul_def]

/-- The linear coefficient of `γ_a(f)` is `a` times that of `f`. -/
theorem coeff_one_cyclotomicSubst (a : ℤ_[p]) (f : O⟦X⟧) :
    coeff 1 (cyclotomicSubst O a f) = algebraMap ℤ_[p] O a * coeff 1 f := by
  rw [cyclotomicSubst_apply, coeff_one_subst (by simp)]
  simp [Algebra.smul_def, mul_comm]

/-- **The shape of `γ_a(X)` for a unit `a`.** For `a ∈ ℤ_pˣ`, `γ_a(X) = (1 + X) ^ a - 1` is
`a X (1 + h_a)` for a series `h_a ∈ X ℤ_p⟦X⟧` with `p`-adic integer coefficients. -/
theorem exists_cyclotomicSubst_X_eq (a : ℤ_[p]ˣ) :
    ∃ h : ℤ_[p]⟦X⟧, constantCoeff h = 0 ∧
      cyclotomicSubst O (a : ℤ_[p]) X =
        C (algebraMap ℤ_[p] O a) * X * (1 + map (algebraMap ℤ_[p] O) h) := by
  refine ⟨mk fun n ↦ if n = 0 then 0 else ↑a⁻¹ * Ring.choose (a : ℤ_[p]) (n + 1),
    by simp [← coeff_zero_eq_constantCoeff_apply], ?_⟩
  ext (_ | n)
  · simp
  rw [mul_assoc, coeff_C_mul, coeff_succ_X_mul, cyclotomicSubst_X, map_sub, binomialSeries_coeff]
  rcases n with _ | n
  · simp [Algebra.smul_def, ← coeff_zero_eq_constantCoeff_apply (map _ _), coeff_map]
  · simp [Algebra.smul_def, ← map_mul, ← mul_assoc]

/-- `γ_(-1)(X) = -X / (1 + X)`, stated without division as `(1 + X) γ_(-1)(X) = -X`. -/
theorem one_add_X_mul_cyclotomicSubst_neg_one_X :
    (1 + X) * cyclotomicSubst O (-1 : ℤ_[p]) X = -X := by
  have h : (1 + X : O⟦X⟧) * binomialSeries O (-1 : ℤ_[p]) = 1 := by
    rw [← binomialSeries_one (R := ℤ_[p]), ← binomialSeries_add, add_neg_cancel,
      binomialSeries_zero]
  rw [cyclotomicSubst_X, mul_sub, h]
  ring

/-- If `a` is not a unit of `O`, then `γ_a` is not surjective: `X` is not in its image, since the
linear coefficient of `γ_a(f)` is `a` times that of `f`. -/
theorem X_notMem_range_cyclotomicSubst {a : ℤ_[p]} (ha : ¬IsUnit (algebraMap ℤ_[p] O a)) :
    X ∉ Set.range (cyclotomicSubst O a) := by
  rintro ⟨f, hf⟩
  have h := congrArg (coeff 1) hf
  rw [coeff_one_cyclotomicSubst, coeff_one_X] at h
  exact ha (.of_mul_eq_one _ h)

/-- `γ_a` is injective when `O` has no zero divisors and `(1 + X) ^ a - 1 ≠ 0`. -/
theorem cyclotomicSubst_injective [NoZeroDivisors O] {a : ℤ_[p]}
    (ha : binomialSeries O a - 1 ≠ 0) : Function.Injective (cyclotomicSubst O a) :=
  substAlgHom_injective (hasSubst_binomialSeries_sub_one a) ha

variable (O) in
/-- The cyclotomic action of the units `ℤ_pˣ` on `O⟦X⟧` by the `O`-algebra automorphisms
`γ_a : f(X) ↦ f((1 + X) ^ a - 1)`. -/
noncomputable def cyclotomicGamma : ℤ_[p]ˣ →* (O⟦X⟧ ≃ₐ[O] O⟦X⟧) :=
  (AlgEquiv.algHomUnitsEquiv O O⟦X⟧).toMonoidHom.comp (Units.map (cyclotomicSubst O))

@[simp]
theorem cyclotomicGamma_apply (a : ℤ_[p]ˣ) (f : O⟦X⟧) :
    cyclotomicGamma O a f = cyclotomicSubst O (a : ℤ_[p]) f :=
  (rfl)

@[simp]
theorem cyclotomicGamma_symm_apply (a : ℤ_[p]ˣ) (f : O⟦X⟧) :
    (cyclotomicGamma O a).symm f = cyclotomicSubst O (↑a⁻¹ : ℤ_[p]) f := by
  rw [← cyclotomicGamma_apply, map_inv, AlgEquiv.aut_inv]

/-- The cyclotomic substitution `(a, f) ↦ γ_a(f)` is jointly continuous in the exponent
`a ∈ ℤ_p` and the series `f`, for the coefficientwise topology on `O⟦X⟧`. -/
theorem continuous_cyclotomicSubst [TopologicalSpace O] [IsTopologicalRing O]
    [ContinuousSMul ℤ_[p] O] :
    Continuous fun x : ℤ_[p] × O⟦X⟧ ↦ cyclotomicSubst O x.1 x.2 := by
  simp only [cyclotomicSubst_apply]
  exact continuous_snd.powerSeries_subst_binomialSeries_sub_one continuous_fst

/-- The cyclotomic substitutions commute with applying an `ℤ_p`-algebra map `σ : O → O'` to the
coefficients: `γ_a(f)^σ = γ_a(f^σ)`. -/
theorem map_cyclotomicSubst {O' : Type*} [CommRing O'] [Algebra ℤ_[p] O'] (σ : O →ₐ[ℤ_[p]] O')
    (a : ℤ_[p]) (f : O⟦X⟧) :
    map (σ : O →+* O') (cyclotomicSubst O a f) = cyclotomicSubst O' a (map (σ : O →+* O') f) := by
  have hs : map (σ : O →+* O') (f.subst (binomialSeries O a - 1)) =
      (map (σ : O →+* O') f).subst (map (σ : O →+* O') (binomialSeries O a - 1)) :=
    PowerSeries.map_subst (hasSubst_binomialSeries_sub_one a) _
  rw [cyclotomicSubst_apply, cyclotomicSubst_apply, hs, map_sub, map_one,
    map_algHom_binomialSeries]

section Frobenius

variable (p) in
/-- The cyclotomic Frobenius `φ_σ(f) = f^σ((1 + X) ^ p - 1)` on `O⟦X⟧`, for an `ℤ_p`-algebra
endomorphism `σ` of `O`: apply `σ` to the coefficients, then substitute `(1 + X) ^ p - 1`. It is
`σ`-semilinear: `φ_σ(C c) = C (σ c)`. -/
noncomputable def cyclotomicFrobenius (σ : O →ₐ[ℤ_[p]] O) : O⟦X⟧ →+* O⟦X⟧ :=
  (cyclotomicSubst O (p : ℤ_[p])).toRingHom.comp (map (σ : O →+* O))

variable (σ : O →ₐ[ℤ_[p]] O)

theorem cyclotomicFrobenius_eq_cyclotomicSubst (f : O⟦X⟧) :
    cyclotomicFrobenius p σ f = cyclotomicSubst O (p : ℤ_[p]) (map (σ : O →+* O) f) :=
  (rfl)

theorem cyclotomicFrobenius_apply (f : O⟦X⟧) :
    cyclotomicFrobenius p σ f = (map (σ : O →+* O) f).subst ((1 + X) ^ p - 1 : O⟦X⟧) := by
  rw [cyclotomicFrobenius_eq_cyclotomicSubst, cyclotomicSubst_natCast_apply]

@[simp]
theorem cyclotomicFrobenius_X : cyclotomicFrobenius p σ X = (1 + X) ^ p - 1 := by
  simp [cyclotomicFrobenius_eq_cyclotomicSubst, binomialSeries_nat]

@[simp]
theorem cyclotomicFrobenius_C (c : O) : cyclotomicFrobenius p σ (C c) = C (σ c) := by
  simp [cyclotomicFrobenius_eq_cyclotomicSubst]

/-- `φ(X) = X q` with `q = ∑_{i < p} (1 + X) ^ i`, a series with constant coefficient `p`. -/
theorem cyclotomicFrobenius_X_eq_X_mul :
    cyclotomicFrobenius p σ X = X * ∑ i ∈ Finset.range p, (1 + X) ^ i := by
  rw [cyclotomicFrobenius_X, ← mul_geom_sum, add_sub_cancel_left]

/-- **The Frobenius commutes with the cyclotomic substitutions**: `φ ∘ γ_a = γ_a ∘ φ`. -/
theorem cyclotomicFrobenius_cyclotomicSubst (a : ℤ_[p]) (f : O⟦X⟧) :
    cyclotomicFrobenius p σ (cyclotomicSubst O a f) =
      cyclotomicSubst O a (cyclotomicFrobenius p σ f) := by
  rw [cyclotomicFrobenius_eq_cyclotomicSubst, cyclotomicFrobenius_eq_cyclotomicSubst,
    map_cyclotomicSubst, ← AlgHom.mul_apply, ← map_mul, mul_comm, map_mul, AlgHom.mul_apply]

/-- The Frobenius `φ_σ` is injective when `σ` is injective and `O` has no zero divisors. -/
theorem cyclotomicFrobenius_injective [NoZeroDivisors O] (hσ : Function.Injective σ) :
    Function.Injective (cyclotomicFrobenius p σ) := by
  nontriviality O
  have hne : binomialSeries O (p : ℤ_[p]) - 1 ≠ 0 := by
    rw [binomialSeries_nat]
    exact one_add_X_pow_sub_one_ne_zero (Fact.out : p.Prime).ne_zero
  exact (cyclotomicSubst_injective hne).comp (map_injective _ hσ)

/-- **Reduction of the Frobenius.** If `σ` lifts the `p`-th power map along a ring homomorphism
`π : O → k` to a ring of characteristic `p`, then `φ_σ` reduces to the `p`-th power map:
`π(φ_σ f) = (π f) ^ p` coefficientwise. -/
theorem map_cyclotomicFrobenius {k : Type*} [CommRing k] [CharP k p] (π : O →+* k)
    (hσ : ∀ x, π (σ x) = π x ^ p) (f : O⟦X⟧) :
    map π (cyclotomicFrobenius p σ f) = map π f ^ p := by
  -- On coefficients, `π ∘ σ` is the Frobenius of `k` after `π`.
  have hπσ : map π (map (σ : O →+* O) f) = map (frobenius k p) (map π f) := by
    ext n
    simp [hσ, frobenius_def]
  -- In characteristic `p`, the substituted series `(1 + X) ^ p - 1` reduces to `X ^ p`, so the
  -- reduced substitution is `expand p`.
  have hX : map π (binomialSeries O (p : ℤ_[p]) - 1) = X ^ p := by
    simpa [binomialSeries_nat] using one_add_X_pow_sub_one_eq_X_pow p k 1
  have hs : map π (cyclotomicFrobenius p σ f) =
      (map π (map (σ : O →+* O) f)).subst (X ^ p : k⟦X⟧) := by
    rw [← hX, cyclotomicFrobenius_eq_cyclotomicSubst, cyclotomicSubst_apply]
    exact PowerSeries.map_subst (hasSubst_binomialSeries_sub_one _) _
  rw [hs, hπσ, ← expand_apply p (Fact.out : p.Prime).ne_zero, ← map_expand, map_frobenius_expand]

/-- `X` is not in the image of the Frobenius when `p` is not a unit of `O`: the linear coefficient
of `φ(f)` is `p σ(f₁)`. -/
theorem X_notMem_range_cyclotomicFrobenius (hp : ¬IsUnit (p : O)) :
    X ∉ Set.range (cyclotomicFrobenius p σ) := by
  rintro ⟨f, hf⟩
  exact X_notMem_range_cyclotomicSubst (a := (p : ℤ_[p])) (by simpa using hp)
    ⟨_, (cyclotomicFrobenius_eq_cyclotomicSubst σ f).symm.trans hf⟩

end Frobenius

/-! ### Examples -/

-- At `p = 2` the Frobenius sends `π` to `π ^ 2 + 2 π`.
example (σ : ℤ_[2] →ₐ[ℤ_[2]] ℤ_[2]) :
    cyclotomicFrobenius 2 σ X = X ^ 2 + 2 * X := by
  rw [cyclotomicFrobenius_X]
  ring

-- `γ_a(X) ≡ a X` modulo `X ^ 2`: the coefficient of `X` is `a`, here at `a = -1`.
example : coeff 1 (cyclotomicSubst ℤ_[3] (-1 : ℤ_[3]) X) = -1 := by
  simp

-- `γ_p` is not invertible on `ℤ_p⟦X⟧`.
example : X ∉ Set.range (cyclotomicSubst ℤ_[3] ((3 : ℕ) : ℤ_[3])) :=
  X_notMem_range_cyclotomicSubst PadicInt.prime_p.not_isUnit

end TauCeti
