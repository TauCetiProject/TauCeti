/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

import Mathlib.Algebra.Group.Submonoid.Finsupp
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import TauCeti.FieldTheory.Kummer.Degree

/-!
# Linear independence of radical monomials

Let `K` be a field, `n ≠ 0`, and let `βᵢ` (`i ∈ ι`, a finite type) be elements of an extension
`E` of `K` with `βᵢ ^ n = αᵢ ∈ K`. The `n ^ #ι` **radical monomials**

```text
β ^ r = ∏ᵢ βᵢ ^ rᵢ,   r : ι → Fin n,
```

span `K(β)` over `K` (`TauCeti.span_range_prod_pow_eq_adjoin`), so `[K(β) : K] ≤ n ^ #ι`, with
equality exactly when they are linearly independent
(`TauCeti.finrank_adjoin_range_eq_pow_iff_linearIndependent`). When `K` contains the `n`-th roots
of unity, this happens exactly when the classes of the `αᵢ` in `Kˣ ⧸ (Kˣ)ⁿ` are independent: no
product `∏ᵢ αᵢ ^ rᵢ` with some `rᵢ` not divisible by `n` is an `n`-th power in `K`
(`TauCeti.linearIndependent_prod_pow_iff`, `TauCeti.finrank_adjoin_range_eq_pow_iff`).
For instance `(α₁, α₂) = (2, 4)` over `ℚ` with `n = 2` fails, since `α₂ = 2 ^ 2`.

The independence of the monomials is what separates a vanishing exponential sum into its classes
modulo `n`. If `∑_{l ∈ s} c_l β ^ l = 0` for a finite set `s` of exponent vectors `l : ι → ℕ` and
coefficients `c_l ∈ K`, then for every residue vector `r` the subsum over `l ≡ r (mod n)` vanishes
(`TauCeti.sum_filter_smul_prod_pow_eq_zero`). Writing `l = r + n m`, so that
`β ^ l = α ^ m β ^ r`, the refined sum `∑_{l ≡ r} c_l α ^ ((l - r) / n)` vanishes in `K`
(`TauCeti.sum_filter_mul_prod_pow_div_eq_zero`). In the `p`-adic method of linear forms in
logarithms, with `n` an auxiliary prime `q` and `βᵢ` the `q`-th roots of the `αᵢ`, this is the
step by which the Galois conjugates of the Kummer extension separate the support classes of the
auxiliary function, so that each class is a new auxiliary function with support refined by the
factor `q`.

The proof of independence is Kummer's: an automorphism `σ` of the Kummer field over `K` moves each
monomial by the root of unity `σ(β ^ r) / β ^ r`, and `σ ↦ σ(β ^ r) / β ^ r` is a character of the
Galois group. Elements with `n`-th powers in `K` and pairwise distinct characters are linearly
independent over `K`, by Dedekind's independence of characters (Mathlib's
`linearIndependent_monoidHom`; here `TauCeti.linearIndependent_of_injective_apply_div_self`).
Two exponents `r ≠ s` give distinct characters: otherwise `β ^ r / β ^ s` is fixed by the Galois
group, hence lies in `K` (`TauCeti.exists_eq_mul_pow_of_apply_div_self_eq`), and then
`∏ᵢ αᵢ ^ (rᵢ + (n - 1) sᵢ)` is an `n`-th power.

## Main results

* `TauCeti.span_range_prod_pow_eq_adjoin`: the monomials span `K(β)`.
* `TauCeti.finrank_adjoin_range_le_pow`: `[K(β) : K] ≤ n ^ #ι`.
* `TauCeti.finrank_adjoin_range_eq_pow_iff_linearIndependent`: equality holds iff the monomials
  are linearly independent.
* `TauCeti.linearIndependent_prod_pow_iff`: over a field containing the `n`-th roots of unity,
  the monomials are linearly independent iff the `αᵢ` are independent modulo `n`-th powers.
* `TauCeti.finrank_adjoin_range_eq_pow_iff`: hence `[K(β) : K] = n ^ #ι` iff the `αᵢ` are
  independent modulo `n`-th powers.
* `TauCeti.sum_filter_smul_prod_pow_eq_zero`, `TauCeti.sum_filter_mul_prod_pow_div_eq_zero`:
  a vanishing sum of monomials vanishes on each residue class of exponents.
* `TauCeti.linearIndependent_of_injective_apply_div_self`: nonzero elements with `n`-th powers in
  `K` and pairwise distinct Kummer characters are linearly independent over `K`.
* `TauCeti.exists_eq_mul_pow_of_apply_div_self_eq`: in a Galois extension, two `n`-th roots with
  the same Kummer character have radicands in the same class modulo `n`-th powers.

## References

* S. Lang, *Algebra*, Graduate Texts in Mathematics 211, Springer (2002), Chapter VI, §8.
* K. Yu, *Linear forms in p-adic logarithms. II*, Compositio Math. 74 (1990), 15–113, §2.
-/

public section

open IntermediateField Module

namespace TauCeti

variable {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ} {ι : Type*} [Fintype ι]
  {α : ι → K} {β : ι → E}

/-- A monomial in the `βᵢ` is a `K`-multiple of the monomial of its exponents reduced mod `n`. -/
private theorem prod_pow_eq_algebraMap_mul_prod_pow_mod (hβ : ∀ i, β i ^ n = algebraMap K E (α i))
    (l : ι → ℕ) :
    ∏ i, β i ^ l i = algebraMap K E (∏ i, α i ^ (l i / n)) * ∏ i, β i ^ (l i % n) := by
  rw [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [map_pow, ← hβ, ← pow_mul, ← pow_add, Nat.div_add_mod]

/-- **Equal Kummer characters have radicands in the same class.** In a Galois extension `F/K`,
if `y ^ n = a` and `y' ^ n = a'` with `a, a' ∈ K` and every automorphism moves `y` and `y'` by the
same factor `σ y / y = σ y' / y'`, then `a = a' c ^ n` for some `c ∈ K`. -/
theorem exists_eq_mul_pow_of_apply_div_self_eq {F : Type*} [Field F] [Algebra K F] [IsGalois K F]
    {y y' : F} {a a' : K} (hy : y ^ n = algebraMap K F a) (hy' : y' ^ n = algebraMap K F a')
    (h : ∀ σ : F ≃ₐ[K] F, σ y / y = σ y' / y') : ∃ c : K, a = a' * c ^ n := by
  rcases eq_or_ne y' 0 with rfl | hy'0
  · obtain rfl : y = 0 := by simpa using h 1
    exact ⟨1, (algebraMap K F).injective (by rw [one_pow, mul_one, ← hy, ← hy'])⟩
  obtain ⟨c, hc⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (y / y')).2 fun σ ↦ by
    rcases eq_or_ne y 0 with rfl | hy0
    · simp
    have hσ : σ y' ≠ 0 := by simpa using hy'0
    rw [map_div₀, div_eq_div_iff hσ hy'0, (div_eq_div_iff hy0 hy'0).1 (h σ), mul_comm]
  refine ⟨c, (algebraMap K F).injective ?_⟩
  rw [map_mul, map_pow, hc, ← hy, ← hy', ← mul_pow, mul_div_cancel₀ _ hy'0]

section NeZero

variable [NeZero n]

/-- **The radical monomials span `K(β)`.** If `βᵢ ^ n = αᵢ ∈ K` with `n ≠ 0`, the monomials
`∏ᵢ βᵢ ^ rᵢ` with `0 ≤ rᵢ < n` span `K(β)` over `K`. -/
theorem span_range_prod_pow_eq_adjoin (hβ : ∀ i, β i ^ n = algebraMap K E (α i)) :
    Submodule.span K (Set.range fun r : ι → Fin n ↦ ∏ i, β i ^ (r i : ℕ)) =
      Subalgebra.toSubmodule (adjoin K (Set.range β)).toSubalgebra := by
  have halg : ∀ x ∈ Set.range β, IsAlgebraic K x := by
    rintro _ ⟨i, rfl⟩
    exact ⟨Polynomial.X ^ n - Polynomial.C (α i),
      Polynomial.X_pow_sub_C_ne_zero (NeZero.pos n) _, by simp [hβ]⟩
  rw [adjoin_toSubalgebra_of_isAlgebraic halg, Algebra.adjoin_eq_span]
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨r, rfl⟩
    exact Submodule.subset_span
      (prod_mem fun i _ ↦ pow_mem (Submonoid.subset_closure (Set.mem_range_self i)) _)
  · intro x hx
    obtain ⟨l, rfl⟩ := Submonoid.exists_of_mem_closure_range β x hx
    rw [prod_pow_eq_algebraMap_mul_prod_pow_mod hβ, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨fun i ↦ ⟨l i % n, Nat.mod_lt _ (NeZero.pos n)⟩, rfl⟩)

/-- `[K(β) : K] ≤ n ^ #ι` when `βᵢ ^ n ∈ K` for every `i`. -/
theorem finrank_adjoin_range_le_pow (hβ : ∀ i, β i ^ n = algebraMap K E (α i)) :
    finrank K (adjoin K (Set.range β)) ≤ n ^ Fintype.card ι := by
  classical
  rw [← finrank_eq_finrank_subalgebra, ← Subalgebra.finrank_toSubmodule,
    ← span_range_prod_pow_eq_adjoin hβ]
  exact (finrank_range_le_card (R := K) fun r : ι → Fin n ↦ ∏ i, β i ^ (r i : ℕ)).trans_eq
    (by simp)

/-- **The degree of a multiple radical extension.** If `βᵢ ^ n = αᵢ ∈ K` with `n ≠ 0`, then
`[K(β) : K] = n ^ #ι` exactly when the monomials `∏ᵢ βᵢ ^ rᵢ`, `0 ≤ rᵢ < n`, are linearly
independent over `K`. -/
theorem finrank_adjoin_range_eq_pow_iff_linearIndependent
    (hβ : ∀ i, β i ^ n = algebraMap K E (α i)) :
    finrank K (adjoin K (Set.range β)) = n ^ Fintype.card ι ↔
      LinearIndependent K fun r : ι → Fin n ↦ ∏ i, β i ^ (r i : ℕ) := by
  classical
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, span_range_prod_pow_eq_adjoin hβ,
    Subalgebra.finrank_toSubmodule, finrank_eq_finrank_subalgebra, Fintype.card_fun,
    Fintype.card_fin, eq_comm]

/-- **A vanishing sum of radical monomials vanishes on each residue class.** Suppose that
`βᵢ ^ n = αᵢ ∈ K` and that the monomials `∏ᵢ βᵢ ^ rᵢ`, `0 ≤ rᵢ < n`, are linearly independent
over `K`. If `∑_{l ∈ s} c_l ∏ᵢ βᵢ ^ lᵢ = 0` for a finite set `s` of exponent vectors and
coefficients `c_l ∈ K`, then for every `r` the refined sum `∑_{l ∈ s, l ≡ r} c_l ∏ᵢ αᵢ ^ (lᵢ / n)`
over the exponents with `lᵢ % n = rᵢ` for all `i` vanishes. -/
theorem sum_filter_mul_prod_pow_div_eq_zero (hβ : ∀ i, β i ^ n = algebraMap K E (α i))
    (hli : LinearIndependent K fun r : ι → Fin n ↦ ∏ i, β i ^ (r i : ℕ))
    {s : Finset (ι → ℕ)} {c : (ι → ℕ) → K} (hs : ∑ l ∈ s, c l • ∏ i, β i ^ l i = 0)
    (r : ι → ℕ) : ∑ l ∈ s with ∀ i, l i % n = r i, c l * ∏ i, α i ^ (l i / n) = 0 := by
  classical
  by_cases hr : ∀ i, r i < n
  swap
  · push Not at hr
    obtain ⟨i, hi⟩ := hr
    refine Finset.sum_eq_zero fun l hl ↦ absurd hi (not_le.2 ?_)
    rw [← (Finset.mem_filter.1 hl).2 i]
    exact Nat.mod_lt _ (NeZero.pos n)
  let ρ (l : ι → ℕ) : ι → Fin n := fun i ↦ ⟨l i % n, Nat.mod_lt _ (NeZero.pos n)⟩
  have hsum : ∑ t : ι → Fin n,
      (∑ l ∈ s with ρ l = t, c l * ∏ i, α i ^ (l i / n)) • ∏ i, β i ^ (t i : ℕ) = 0 := by
    rw [← hs, ← Finset.sum_fiberwise s ρ]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    obtain rfl := (Finset.mem_filter.1 hl).2
    rw [prod_pow_eq_algebraMap_mul_prod_pow_mod hβ l, ← Algebra.smul_def, smul_smul]
  have := Fintype.linearIndependent_iff.1 hli _ hsum fun i ↦ ⟨r i, hr i⟩
  simpa [ρ, funext_iff, Fin.ext_iff] using this

/-- **A vanishing sum of radical monomials vanishes on each residue class**, read in `E`: under
the hypotheses of `TauCeti.sum_filter_mul_prod_pow_div_eq_zero`, the subsum of
`∑_{l ∈ s} c_l ∏ᵢ βᵢ ^ lᵢ` over the exponents with `lᵢ % n = rᵢ` for all `i` vanishes. -/
theorem sum_filter_smul_prod_pow_eq_zero (hβ : ∀ i, β i ^ n = algebraMap K E (α i))
    (hli : LinearIndependent K fun r : ι → Fin n ↦ ∏ i, β i ^ (r i : ℕ))
    {s : Finset (ι → ℕ)} {c : (ι → ℕ) → K} (hs : ∑ l ∈ s, c l • ∏ i, β i ^ l i = 0)
    (r : ι → ℕ) : ∑ l ∈ s with ∀ i, l i % n = r i, c l • ∏ i, β i ^ l i = 0 := by
  have h : ∀ l ∈ s.filter fun l ↦ ∀ i, l i % n = r i, c l • ∏ i, β i ^ l i =
      (c l * ∏ i, α i ^ (l i / n)) • ∏ i, β i ^ r i := by
    intro l hl
    have hlr := (Finset.mem_filter.1 hl).2
    rw [prod_pow_eq_algebraMap_mul_prod_pow_mod hβ l, mul_smul, Algebra.smul_def (∏ i, _)]
    simp only [hlr]
  rw [Finset.sum_congr rfl h, ← Finset.sum_smul,
    sum_filter_mul_prod_pow_div_eq_zero hβ hli hs r, zero_smul]

end NeZero

section RootsOfUnity

variable [NeZero n] [HasEnoughRootsOfUnity K n]

/-- **Dedekind's lemma for Kummer generators.** Let `K` contain the `n`-th roots of unity and let
`y_t` be nonzero elements of a field extension `F` of `K` with `y_t ^ n ∈ K`. If their Kummer
characters `σ ↦ σ(y_t) / y_t` on the automorphisms of `F/K` are pairwise distinct, the `y_t` are
linearly independent over `K`. -/
theorem linearIndependent_of_injective_apply_div_self {F κ : Type*} [Field F] [Algebra K F]
    {y : κ → F} {a : κ → K} (hy : ∀ t, y t ^ n = algebraMap K F (a t)) (hy0 : ∀ t, y t ≠ 0)
    (hinj : Function.Injective fun t (σ : F ≃ₐ[K] F) ↦ σ (y t) / y t) :
    LinearIndependent K y := by
  let χ (t : κ) : (F ≃ₐ[K] F) →* F :=
    { toFun σ := σ (y t) / y t
      map_one' := by simp [hy0 t]
      map_mul' σ τ := σ.mul_apply_div_self_of_pow_eq τ (hy t) }
  have hlin := (linearIndependent_monoidHom (F ≃ₐ[K] F) F).comp χ fun t t' h ↦
    hinj (congrArg DFunLike.coe h)
  rw [linearIndependent_iff'] at hlin ⊢
  intro s g hg t ht
  have := hlin s (fun t ↦ algebraMap K F (g t) * y t) (funext fun σ ↦ ?_) t ht
  · simpa [hy0 t] using this
  · simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, Pi.zero_apply, smul_eq_mul]
    calc ∑ t ∈ s, algebraMap K F (g t) * y t * χ t σ = σ (∑ t ∈ s, g t • y t) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun t _ ↦ ?_
          simp only [χ, MonoidHom.coe_mk, OneHom.coe_mk, Algebra.smul_def, map_mul,
            AlgEquiv.commutes]
          field_simp [hy0 t]
      _ = 0 := by rw [hg, map_zero]

/-- Kummer's argument: if no product `∏ᵢ αᵢ ^ rᵢ` with some `rᵢ` not divisible by `n` is an
`n`-th power in `K`, the Kummer characters `σ ↦ σ(β ^ r) / β ^ r` of the Galois group of the Kummer
field are pairwise distinct, so the monomials `β ^ r` are linearly independent. -/
private theorem linearIndependent_prod_pow_of_forall_dvd
    (hβ : ∀ i, β i ^ n = algebraMap K E (α i))
    (hα : ∀ r : ι → ℕ, (∃ c : K, ∏ i, α i ^ r i = c ^ n) → ∀ i, n ∣ r i) :
    LinearIndependent K fun r : ι → Fin n ↦ ∏ i, β i ^ (r i : ℕ) := by
  classical
  obtain rfl | hn := eq_or_ne n 1
  · exact linearIndependent_unique_iff.2 (by simp)
  have hα0 (i : ι) : α i ≠ 0 := fun h ↦ hn <| Nat.dvd_one.1 <| by
    simpa using hα (Pi.single i 1) ⟨0, by simp [h, zero_pow (NeZero.ne n), Pi.single_apply]⟩ i
  -- Work inside the Kummer field `M` of all `n`-th roots of elements of `Kˣ`, which is Galois.
  set M := kummerField E n (⊤ : Subgroup Kˣ)
  let b (i : ι) : M := ⟨β i, mem_kummerField_of_pow_eq (a := Units.mk0 (α i) (hα0 i))
    (Subgroup.mem_top _) (by simpa using hβ i)⟩
  have hb (i : ι) : b i ^ n = algebraMap K M (α i) := Subtype.ext (by simpa [b] using hβ i)
  let m (r : ι → Fin n) : M := ∏ i, b i ^ (r i : ℕ)
  have hm (r : ι → Fin n) : m r ^ n = algebraMap K M (∏ i, α i ^ (r i : ℕ)) := by
    simp_rw [m, ← Finset.prod_pow, ← pow_mul, mul_comm _ n, pow_mul, hb, map_prod, map_pow]
  have hm0 (r : ι → Fin n) : m r ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ ↦ pow_ne_zero _ fun h ↦ hα0 i <|
      (algebraMap K M).injective (by rw [← hb, h, zero_pow (NeZero.ne n), map_zero])
  -- Distinct exponents `r ≠ s` give distinct characters: otherwise `∏ αᵢ ^ rᵢ = c ^ n ∏ αᵢ ^ sᵢ`,
  -- and `∏ αᵢ ^ (rᵢ + (n - 1) sᵢ)` is an `n`-th power.
  have hli : LinearIndependent K m := by
    refine linearIndependent_of_injective_apply_div_self hm hm0 fun r s hrs ↦ ?_
    obtain ⟨c, hc⟩ := exists_eq_mul_pow_of_apply_div_self_eq (hm r) (hm s) (congrFun hrs)
    have hpow : ∏ i, α i ^ ((r i : ℕ) + (n - 1) * s i) = (c * ∏ i, α i ^ (s i : ℕ)) ^ n := by
      calc ∏ i, α i ^ ((r i : ℕ) + (n - 1) * s i) =
            (∏ i, α i ^ (r i : ℕ)) * (∏ i, α i ^ (s i : ℕ)) ^ (n - 1) := by
            rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
            exact Finset.prod_congr rfl fun i _ ↦ by rw [pow_add, ← pow_mul, mul_comm (n - 1)]
        _ = c ^ n * ((∏ i, α i ^ (s i : ℕ)) * (∏ i, α i ^ (s i : ℕ)) ^ (n - 1)) := by
            rw [hc]; ring
        _ = (c * ∏ i, α i ^ (s i : ℕ)) ^ n := by rw [mul_pow_sub_one (NeZero.ne n), mul_pow]
    funext i
    obtain ⟨k, hk⟩ := hα _ ⟨_, hpow⟩ i
    have hns : (n - 1) * s i + s i = n * s i := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel NeZero.one_le]
    have key : (r i : ℕ) + n * s i = n * k + s i := by linarith
    have := congrArg (· % n) key
    simp only [Nat.add_mul_mod_self_left, Nat.mul_add_mod, Nat.mod_eq_of_lt (r i).isLt,
      Nat.mod_eq_of_lt (s i).isLt] at this
    exact Fin.ext this
  -- Transport the independence from `M` to `E`.
  rw [Fintype.linearIndependent_iff] at hli ⊢
  exact fun g hg ↦ hli g (Subtype.ext (by simpa [m, b] using hg))

/-- If the monomials `β ^ r` are linearly independent, no product `∏ᵢ αᵢ ^ rᵢ` with some `rᵢ` not
divisible by `n` is an `n`-th power in `K`: otherwise the reduced monomial `β ^ (r mod n)` would
be a `K`-multiple of `β ^ 0 = 1`. -/
private theorem forall_dvd_of_linearIndependent_prod_pow
    (hβ : ∀ i, β i ^ n = algebraMap K E (α i))
    (hli : LinearIndependent K fun r : ι → Fin n ↦ ∏ i, β i ^ (r i : ℕ)) (r : ι → ℕ)
    (hr : ∃ c : K, ∏ i, α i ^ r i = c ^ n) (i : ι) : n ∣ r i := by
  classical
  obtain rfl | hn := eq_or_ne n 1
  · exact one_dvd _
  have h1n : 1 < n := by have := NeZero.pos n; omega
  have hα0 (j : ι) : α j ≠ 0 := by
    intro h
    have hβ0 : β j = 0 := pow_eq_zero_iff (NeZero.ne n) |>.1 (by rw [hβ, h, map_zero])
    refine hli.ne_zero (Pi.single j ⟨1, h1n⟩) ?_
    rw [Finset.prod_eq_single j (fun k _ hk ↦ by simp [Pi.single_eq_of_ne hk]) (by simp)]
    simp [hβ0]
  obtain ⟨c, hc⟩ := hr
  let ρ : ι → Fin n := fun i ↦ ⟨r i % n, Nat.mod_lt _ (NeZero.pos n)⟩
  -- `β ^ r` is an `n`-th root of `c ^ n`, so it is `z c` for some `z ∈ K`.
  obtain ⟨z, hz⟩ := exists_eq_algebraMap_mul_of_pow_eq (K := K) (n := n)
    (x := ∏ i, β i ^ r i) (y := algebraMap K E c) <| by
      simp_rw [← Finset.prod_pow, ← pow_mul, mul_comm _ n, pow_mul, hβ, ← map_pow, ← map_prod, hc]
  set A := ∏ i, α i ^ (r i / n)
  have hA : A ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ ↦ pow_ne_zero _ (hα0 i)
  have hrel : A • ∏ i, β i ^ ((ρ i : ℕ)) - (z * c) • ∏ i, β i ^ ((0 : ι → Fin n) i : ℕ) = 0 := by
    rw [Algebra.smul_def, Algebra.smul_def, ← prod_pow_eq_algebraMap_mul_prod_pow_mod hβ, hz]
    simp
  by_contra hdvd
  have hρ : ρ ≠ 0 := fun h ↦ hdvd (Nat.dvd_of_mod_eq_zero (congrArg Fin.val (congrFun h i)))
  have := Fintype.linearIndependent_iff.1 hli (Pi.single ρ A - Pi.single 0 (z * c)) (by
    simpa [sub_smul, Finset.sum_sub_distrib, Pi.single_apply, ite_smul] using hrel) ρ
  simp [Pi.single_eq_of_ne hρ, hA] at this

/-- **Kummer's independence of radical monomials.** Let `K` contain the `n`-th roots of unity and
let `βᵢ ^ n = αᵢ ∈ K`. The monomials `∏ᵢ βᵢ ^ rᵢ`, `0 ≤ rᵢ < n`, are linearly independent over `K`
if and only if the `αᵢ` are independent modulo `n`-th powers: whenever `∏ᵢ αᵢ ^ rᵢ` is an `n`-th
power in `K`, every `rᵢ` is divisible by `n`. -/
theorem linearIndependent_prod_pow_iff (hβ : ∀ i, β i ^ n = algebraMap K E (α i)) :
    (LinearIndependent K fun r : ι → Fin n ↦ ∏ i, β i ^ (r i : ℕ)) ↔
      ∀ r : ι → ℕ, (∃ c : K, ∏ i, α i ^ r i = c ^ n) → ∀ i, n ∣ r i :=
  ⟨forall_dvd_of_linearIndependent_prod_pow hβ, linearIndependent_prod_pow_of_forall_dvd hβ⟩

/-- **The Kummer condition.** Let `K` contain the `n`-th roots of unity and let `βᵢ ^ n = αᵢ ∈ K`.
Then `[K(β) : K] = n ^ #ι` if and only if the `αᵢ` are independent modulo `n`-th powers: whenever
`∏ᵢ αᵢ ^ rᵢ` is an `n`-th power in `K`, every `rᵢ` is divisible by `n`. -/
theorem finrank_adjoin_range_eq_pow_iff (hβ : ∀ i, β i ^ n = algebraMap K E (α i)) :
    finrank K (adjoin K (Set.range β)) = n ^ Fintype.card ι ↔
      ∀ r : ι → ℕ, (∃ c : K, ∏ i, α i ^ r i = c ^ n) → ∀ i, n ∣ r i := by
  rw [finrank_adjoin_range_eq_pow_iff_linearIndependent hβ, linearIndependent_prod_pow_iff hβ]

end RootsOfUnity

end TauCeti
