/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Quadratic.Ramification
public import TauCeti.NumberTheory.NumberField.Inertia
import TauCeti.Algebra.Algebra.Equiv
import TauCeti.FieldTheory.Galois.FixedField
import TauCeti.FieldTheory.Galois.SquareRoot

/-!
# Ramified primes in a Galois extension unramified over a quadratic subfield

Let `M / ℚ` be a Galois number-field extension and let `F ⊆ M` be a quadratic intermediate field
such that `M / F` is unramified at every finite prime. This file computes which rational primes
ramify in the intermediate fields of `M`. Two statements come out, and together they say that the
quadratic subfields of `M` ramified at a fixed prime `p` form a coset of those unramified at `p`.

* **Ramification descends to `F`.** Every rational prime ramifying in an intermediate field of `M`
  already ramifies in `F`.
* **Two ramified square roots multiply to an unramified one.** If `√a ∈ M` and `p` ramifies in
  `ℚ(√a)`, then `p` is unramified in `ℚ(√(ab))`, where `ℚ(√b) = F`.

Both are read off the inertia subgroups of the primes `P` of `𝓞 M` above `p`: an intermediate
field is unramified at `p` exactly when every one of them fixes it pointwise
(`NumberField.notMem_ramifiedPrimes_iff_forall_inertia_le`). Unramifiedness of `M / F` makes such
an inertia subgroup `I` meet `Gal(M / F)` trivially
(`NumberField.disjoint_inertia_of_ramificationIdx_eq_one`), and `Gal(M / F)` has index two, so any
two nonidentity elements of `I` coincide: `I` is `{1}` at an unramified prime and `{1, σ}` at a
ramified one. Since `σ` sends a square root of a rational number to plus or minus itself,
`σ √a = -√a` and `σ √b = -√b` give `σ (√a √b) = √a √b`, which is the second statement; and
`σ ≠ 1` does not lie in `Gal(M / F)`, which is the first.

For the second statement, the element of `I` negating `√a` is supplied at every prime above `p`
by `TauCeti.NumberField.exists_mem_inertia_apply_eq_neg`.

The arithmetic form of both statements is stated with `fundamentalDiscriminant`, using that the
discriminant of `ℚ(√a)` for squarefree `a` is `fundamentalDiscriminant a`
(`TauCeti.Multiquadratic.discr_adjoin_singleton_eq_fundamentalDiscriminant`). It constrains the
prime discriminants of a quadratic subfield of `M` by those of `F`, which is the arithmetic half of
the maximality proof for the candidate genus field. The field-theoretic half is
`TauCeti.Multiquadratic.exists_squarefree_root_adjoin_range_eq_top_of_isUnramifiedIn_over_quadratic`
in `TauCeti/NumberTheory/Multiquadratic/Unramified/Basic.lean`, which presents such an `M` as a
multiquadratic field.

This is the classical argument in the genus-field construction; see D. A. Cox, *Primes of the Form
x² + ny²*, §6.A, and F. Lemmermeyer, *Reciprocity Laws: From Euler to Eisenstein*, §2.2.

## Main results

In the namespace `TauCeti.Multiquadratic`:

* `ramifiedPrimes_subset_of_isUnramifiedIn`: a prime ramifying in an intermediate field ramifies
  in the quadratic subfield.
* `notMem_ramifiedPrimes_adjoin_mul`: a prime ramifying in `ℚ(√a)` is unramified in `ℚ(√(ab))`.
* `dvd_fundamentalDiscriminant_base_of_dvd_subfield` and
  `not_dvd_fundamentalDiscriminant_mul_of_dvd_subfield`: the arithmetic forms.

## Provenance

Independently reconstructed. The multiquadratic roadmap designates
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance) (the formalization of
L. Alpöge's disproof of the uniform-constant Erdős unit-distance conjecture) as the migration
source for its Layer-0 square-class machinery — `sqrtTower`, `mem_sup_adjoin_sq`,
`squareClass_of_sqrt_mem`, `sqrtTower_finrank`, `exists_transversal_family` and
`units_sq_index_le` — and none of that is used here: this file is inertia theory over the Galois
group of `M / ℚ`, resting on Mathlib's `Ideal.inertia` and on
`TauCeti/NumberTheory/NumberField/Inertia.lean`.
-/

public section

open IntermediateField NumberField

open scoped NumberField

namespace TauCeti.Multiquadratic

variable {M : Type*} [Field M] [NumberField M] [IsGalois ℚ M]

/-- The inertia subgroup at a prime above `p` meets `Gal(M / F)` trivially when `M / F` is
unramified at every finite prime. -/
private theorem disjoint_inertia (F : IntermediateField ℚ M)
    (hunr : ∀ q : Ideal (𝓞 F), q.IsPrime → q ≠ ⊥ → Algebra.IsUnramifiedIn (𝓞 M) q)
    {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 M)) (hP : P.IsPrime)
    (hPp : P.LiesOver (Ideal.span {(p : ℤ)})) :
    Disjoint (P.inertia (M ≃ₐ[ℚ] M)) (fixingSubgroup (M ≃ₐ[ℚ] M) (F : Set M)) := by
  have : P.IsPrime := hP
  have : P.LiesOver (Ideal.span {(p : ℤ)}) := hPp
  let _ : NumberField F := NumberField.of_intermediateField F
  have hbot : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by simpa using hp.ne_zero
  have hq : (P.under (𝓞 F)) ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot (p := Ideal.span {(p : ℤ)}) hbot _
  exact NumberField.disjoint_inertia_of_ramificationIdx_eq_one (F := F)
    (fixingSubgroup (M ≃ₐ[ℚ] M) (F : Set M)) P hP
    ((hunr (P.under (𝓞 F)) inferInstance hq).ramificationIdx_eq_one inferInstance)

/-- **Ramification descends to the quadratic subfield.** Let `M / ℚ` be Galois, let `F ⊆ M` be an
intermediate field such that `M / F` is unramified at every finite prime, and let `E ⊆ M` be any
intermediate field. Then every rational prime ramifying in `E` ramifies in `F`.

Were such a prime unramified in `F`, the inertia subgroup of every prime `P` of `𝓞 M` above it
would be contained in `Gal(M / F)`; being also disjoint from `Gal(M / F)` it would be trivial,
hence contained in `Gal(M / E)`, and the prime would be unramified in `E`. -/
theorem ramifiedPrimes_subset_of_isUnramifiedIn (F E : IntermediateField ℚ M)
    (hunr : ∀ q : Ideal (𝓞 F), q.IsPrime → q ≠ ⊥ → Algebra.IsUnramifiedIn (𝓞 M) q) :
    ramifiedPrimes E ⊆ ramifiedPrimes F := by
  classical
  intro p hpE
  have hp : p.Prime := NumberField.prime_of_mem_ramifiedPrimes hpE
  let _ : NumberField E := NumberField.of_intermediateField E
  let _ : NumberField F := NumberField.of_intermediateField F
  by_contra hpF
  refine absurd hpE ((NumberField.notMem_ramifiedPrimes_iff_forall_inertia_le (K := M) (F := E)
    (fixingSubgroup (M ≃ₐ[ℚ] M) (E : Set M)) hp).mpr fun P hP hPp => ?_)
  have hle := (NumberField.notMem_ramifiedPrimes_iff_forall_inertia_le (K := M) (F := F)
    (fixingSubgroup (M ≃ₐ[ℚ] M) (F : Set M)) hp).mp hpF P hP hPp
  rw [(disjoint_inertia F hunr hp P hP hPp).eq_bot_of_le hle]
  exact bot_le

/-- **Two ramified square roots multiply to an unramified one.** Let `M / ℚ` be Galois, let
`y ∈ M` be a square root of a rational number generating a quadratic subfield `ℚ(y)`, and suppose
`M / ℚ(y)` is unramified at every finite prime. Let `x ∈ M` be a square root of a rational number.
If a rational prime `p` ramifies in `ℚ(x)`, then it is unramified in `ℚ(r x y)` for every
rational `r`.

Let `P` be a prime above `p`, with inertia subgroup `I`. Ramification in `ℚ(x)` gives some
`τ ∈ I` with `τ x = -x` (`TauCeti.NumberField.exists_mem_inertia_apply_eq_neg`). As `I` is
disjoint from `Gal(M / ℚ(y))`, which has index two, any two nonidentity elements of `I` coincide:
a nonidentity `σ ∈ I` satisfies `σ τ = 1`, so `σ x = -x`, while `σ ∉ Gal(M / ℚ(y))` forces
`σ y = -y`. Thus `σ` fixes `x y`, and `I` fixes `ℚ(r x y)` pointwise. -/
theorem notMem_ramifiedPrimes_adjoin_mul {x y : M} {a b : ℚ}
    (hx : x ^ 2 = algebraMap ℚ M a) (hy : y ^ 2 = algebraMap ℚ M b)
    (hdeg : Module.finrank ℚ (adjoin ℚ {y} : IntermediateField ℚ M) = 2)
    (hunr : ∀ q : Ideal (𝓞 (adjoin ℚ {y} : IntermediateField ℚ M)), q.IsPrime → q ≠ ⊥ →
      Algebra.IsUnramifiedIn (𝓞 M) q)
    (r : ℚ) {p : ℕ} (hpx : p ∈ ramifiedPrimes (adjoin ℚ {x} : IntermediateField ℚ M)) :
    p ∉ ramifiedPrimes (adjoin ℚ {algebraMap ℚ M r * (x * y)} : IntermediateField ℚ M) := by
  classical
  have hp : p.Prime := NumberField.prime_of_mem_ramifiedPrimes hpx
  let _ : NumberField (adjoin ℚ {y} : IntermediateField ℚ M) := NumberField.of_intermediateField _
  let _ : NumberField (adjoin ℚ {algebraMap ℚ M r * (x * y)} : IntermediateField ℚ M) :=
    NumberField.of_intermediateField _
  have hindex : (fixingSubgroup (M ≃ₐ[ℚ] M)
      ((adjoin ℚ {y} : IntermediateField ℚ M) : Set M)).index = 2 := by
    rw [IsGaloisGroup.index_eq_finrank _ ℚ (adjoin ℚ {y} : IntermediateField ℚ M) M, hdeg]
  refine (NumberField.notMem_ramifiedPrimes_iff_forall_inertia_le (K := M)
    (F := adjoin ℚ {algebraMap ℚ M r * (x * y)})
    (fixingSubgroup (M ≃ₐ[ℚ] M)
      ((adjoin ℚ {algebraMap ℚ M r * (x * y)} : IntermediateField ℚ M) : Set M)) hp).mpr
    fun P hP hPp => ?_
  have : P.IsPrime := hP
  have : P.LiesOver (Ideal.span {(p : ℤ)}) := hPp
  have hdisj := disjoint_inertia (adjoin ℚ {y}) hunr hp P hP hPp
  obtain ⟨τ, hτI, hτneg⟩ := TauCeti.NumberField.exists_mem_inertia_apply_eq_neg hx hpx P
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [IntermediateField.adjoin_zero, (IntermediateField.botEquiv ℚ M).ramifiedPrimes_eq,
      NumberField.ramifiedPrimes_rat] at hpx
    exact hpx
  intro σ hσ
  -- The inertia criterion uses the carrier-set fixing subgroup; expose its definitionally equal
  -- intermediate-field wrapper so that the adjoin API applies.
  change σ ∈ (adjoin ℚ {algebraMap ℚ M r * (x * y)}).fixingSubgroup
  rw [IntermediateField.fixingSubgroup_adjoin_simple, MulAction.mem_stabilizer_iff,
    AlgEquiv.smul_def]
  by_cases hσF : σ ∈ fixingSubgroup (M ≃ₐ[ℚ] M) ((adjoin ℚ {y} : IntermediateField ℚ M) : Set M)
  · rw [Subgroup.disjoint_def.mp hdisj hσ hσF]
    rfl
  by_cases hτF : τ ∈ fixingSubgroup (M ≃ₐ[ℚ] M) ((adjoin ℚ {y} : IntermediateField ℚ M) : Set M)
  · exact False.elim ((AlgEquiv.ne_one_of_apply_eq_neg τ
      (IsRegular.of_ne_zero two_ne_zero).left hx0 hτneg)
      (Subgroup.disjoint_def.mp hdisj hτI hτF))
  have hone : σ * τ = 1 := Subgroup.disjoint_def.mp hdisj (mul_mem hσ hτI)
    ((Subgroup.mul_mem_iff_of_index_two hindex).mpr (by simp only [hσF, hτF]))
  have hσx : σ x = -x := by
    have h1 : (σ * τ) x = x := by rw [hone]; rfl
    rw [AlgEquiv.mul_apply, hτneg, map_neg] at h1
    exact neg_eq_iff_eq_neg.mp h1
  have hσy : σ y = -y :=
    (AlgEquiv.apply_eq_or_eq_neg_of_sq_eq σ hy).resolve_left fun hfix =>
    hσF (by
      -- Convert the carrier-set fixing subgroup to the definitionally equal intermediate-field
      -- wrapper before applying the adjoin API.
      change σ ∈ (adjoin ℚ {y}).fixingSubgroup
      rw [IntermediateField.fixingSubgroup_adjoin_simple, MulAction.mem_stabilizer_iff,
        AlgEquiv.smul_def]
      exact hfix)
  rw [map_mul, map_mul, AlgEquiv.commutes, hσx, hσy, neg_mul_neg]

/-- **A ramified prime of a quadratic subfield ramifies in the quadratic base.** In a Galois
`M / ℚ` unramified over `ℚ(√d)` at every finite prime, every prime dividing the discriminant of a
quadratic subfield `ℚ(√a)` divides the discriminant of `ℚ(√d)`. -/
theorem dvd_fundamentalDiscriminant_base_of_dvd_subfield {x y : M} {a d : ℤ}
    (hsfa : Squarefree a) (hsfd : Squarefree d)
    (hx : x ^ 2 = algebraMap ℤ M a) (hy : y ^ 2 = algebraMap ℤ M d)
    (hunr : ∀ q : Ideal (𝓞 (adjoin ℚ {y} : IntermediateField ℚ M)), q.IsPrime → q ≠ ⊥ →
      Algebra.IsUnramifiedIn (𝓞 M) q)
    {p : ℕ} (hp : p.Prime) (hdvd : (p : ℤ) ∣ fundamentalDiscriminant a) :
    (p : ℤ) ∣ fundamentalDiscriminant d := by
  rw [← mem_ramifiedPrimes_adjoin_iff_dvd_fundamentalDiscriminant hsfd hy hp]
  exact ramifiedPrimes_subset_of_isUnramifiedIn _ _ hunr
    ((mem_ramifiedPrimes_adjoin_iff_dvd_fundamentalDiscriminant hsfa hx hp).mpr hdvd)

/-- **The product of two square roots is unramified where the first one ramifies.** In a Galois
`M / ℚ` unramified over the quadratic field `ℚ(√d)` at every finite prime, if `c` is a squarefree
integer in the square class of `a * d` then no prime dividing the discriminant of `ℚ(√a)` divides
the discriminant of `ℚ(√c)`. -/
theorem not_dvd_fundamentalDiscriminant_mul_of_dvd_subfield {x y : M} {a d c e : ℤ}
    (hsfa : Squarefree a) (hsfc : Squarefree c)
    (hx : x ^ 2 = algebraMap ℤ M a) (hy : y ^ 2 = algebraMap ℤ M d)
    (hdeg : Module.finrank ℚ (adjoin ℚ {y} : IntermediateField ℚ M) = 2)
    (hunr : ∀ q : Ideal (𝓞 (adjoin ℚ {y} : IntermediateField ℚ M)), q.IsPrime → q ≠ ⊥ →
      Algebra.IsUnramifiedIn (𝓞 M) q)
    (he : e ≠ 0) (hprod : a * d = c * e ^ 2)
    {p : ℕ} (hp : p.Prime) (hdvd : (p : ℤ) ∣ fundamentalDiscriminant a) :
    ¬ (p : ℤ) ∣ fundamentalDiscriminant c := by
  have hxq : x ^ 2 = algebraMap ℚ M (a : ℚ) := by
    rw [hx, IsScalarTower.algebraMap_apply ℤ ℚ M]; norm_num
  have hyq : y ^ 2 = algebraMap ℚ M (d : ℚ) := by
    rw [hy, IsScalarTower.algebraMap_apply ℤ ℚ M]; norm_num
  have heq : ((e : ℚ)) ≠ 0 := Int.cast_ne_zero.mpr he
  have hz : (algebraMap ℚ M ((e : ℚ)⁻¹) * (x * y)) ^ 2 = algebraMap ℤ M c := by
    have hrat : ((e : ℚ)⁻¹) ^ 2 * ((a : ℚ) * (d : ℚ)) = (c : ℚ) := by
      have hq : (a : ℚ) * (d : ℚ) = (c : ℚ) * (e : ℚ) ^ 2 := by exact_mod_cast hprod
      field_simp
      linear_combination hq
    calc (algebraMap ℚ M ((e : ℚ)⁻¹) * (x * y)) ^ 2
        = algebraMap ℚ M (((e : ℚ)⁻¹) ^ 2) * (x ^ 2 * y ^ 2) := by rw [map_pow]; ring
      _ = algebraMap ℚ M (((e : ℚ)⁻¹) ^ 2 * ((a : ℚ) * (d : ℚ))) := by
            rw [hxq, hyq, map_mul, map_mul]
      _ = algebraMap ℤ M c := by rw [hrat, IsScalarTower.algebraMap_apply ℤ ℚ M]; norm_num
  rw [← mem_ramifiedPrimes_adjoin_iff_dvd_fundamentalDiscriminant hsfc hz hp]
  exact notMem_ramifiedPrimes_adjoin_mul hxq hyq hdeg hunr ((e : ℚ)⁻¹)
    ((mem_ramifiedPrimes_adjoin_iff_dvd_fundamentalDiscriminant hsfa hx hp).mpr hdvd)

end TauCeti.Multiquadratic
