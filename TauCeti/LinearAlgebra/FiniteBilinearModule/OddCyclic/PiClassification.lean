/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.Basic
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Pi
import TauCeti.GroupTheory.Coset.Fiber
import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.Classification
import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.GaussSum
import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.Relations
import TauCeti.LinearAlgebra.QuadraticForm.Prod
import TauCeti.NumberTheory.LegendreSymbol.QuadraticCongruence

/-!
# Classification of orthogonal sums of odd cyclic generators

For an odd prime `p`, Nikulin's decomposition writes every nondegenerate finite quadratic module of
`p`-power order as an orthogonal sum of odd cyclic generators `q_θ^{(p)}(p^k)`
(`TauCeti.FiniteQuadraticModule.exists_isometry_pi_oddCyclic`). Such a decomposition is not
unique, and this file decides when two orthogonal sums of these generators with the same exponents
are isometric. For exponents `k_i` and coefficients `θ_i`, `η_i` prime to `p`,

```text
⊕ᵢ q_{θ_i}^{(p)}(p^{k_i}) ≅ ⊕ᵢ q_{η_i}^{(p)}(p^{k_i})
  ⟺  ∏_{k_i = m} (θ_i/p) = ∏_{k_i = m} (η_i/p)  for every m ≥ 1.
```

So, once the exponents are fixed, the isometry class of the sum only depends on the product of
the Legendre symbols of the coefficients of each order `p^m`; summands of order `p^0 = 1` are
trivial and impose nothing.

The invariance of the level products is a Gauss-sum computation. For `j ≥ 0` the scaled Gauss sum
`∑_x e^{2πi p^j q(x)}` is an isometry invariant and is multiplicative over orthogonal sums. On
`q_θ^{(p)}(p^k)` it is `(θ/p)^{k - j}` times its value at `θ = 1`, by Nikulin's values of the
Gauss-sum invariant on the generators (`TauCeti.FiniteQuadraticModule.gaussSign_oddCyclic`), so an
isometry gives `∏ᵢ ((θ_i/p)(η_i/p))^{k_i - j} = 1` for every `j`. Comparing `j = m - 1` with
`j = m` isolates the product over the summands with `k_i ≥ m`, and hence over those with
`k_i = m`.

Conversely, two odd cyclic generators of the same order with the same Legendre symbol are
isometric, and Nikulin's doubled relation `q_θ ⊕ q_θ ≅ q_η ⊕ q_η`
(`TauCeti.FiniteQuadraticModule.oddCyclicProdSelfIsometry`) shows that `q_a ⊕ q_b ≅ q_c ⊕ q_d`
whenever `(a/p)(b/p) = (c/p)(d/p)`. Equal level products therefore allow the coefficients to be
matched one summand at a time, moving a mismatched Legendre symbol onto another summand of the
same order.

## Main declarations

* `TauCeti.FiniteQuadraticModule.nonempty_isometry_pi_oddCyclic_iff`: two orthogonal sums of odd
  cyclic generators at `p` with the same exponents are isometric exactly when their level
  products of Legendre symbols agree.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Propositions 1.8.1, 1.8.2 and 1.11.2.
* C. T. C. Wall, *Quadratic forms on finite groups, and related topics*, Topology 2 (1963),
  281–298.
-/

public section

namespace TauCeti.FiniteQuadraticModule

variable {p : ℕ}

/-! ### Scaled Gauss sums -/

/-- The Gauss sum `∑_{a ∈ A} e^{2πi n q(a)}` of the scaled quadratic form `n • q`. -/
private noncomputable def scaledGaussSum (A : FiniteQuadraticModule) (n : ℕ) : ℂ :=
  ∑ᶠ a : A, expCircle (n • A.quadratic a)

private theorem scaledGaussSum_eq_sum (A : FiniteQuadraticModule) [Fintype A] (n : ℕ) :
    scaledGaussSum A n = ∑ a, expCircle (n • A.quadratic a) :=
  finsum_eq_sum_of_fintype _

private theorem Isometry.scaledGaussSum_eq {A B : FiniteQuadraticModule} (f : Isometry A B)
    (n : ℕ) : scaledGaussSum A n = scaledGaussSum B n := by
  obtain ⟨_⟩ := nonempty_fintype A
  obtain ⟨_⟩ := nonempty_fintype B
  rw [scaledGaussSum_eq_sum, scaledGaussSum_eq_sum]
  exact Fintype.sum_equiv f.toLinearEquiv.toEquiv _ _ fun x ↦
    congrArg (fun t ↦ expCircle (n • t)) (f.map_app x).symm

private theorem scaledGaussSum_pi {ι : Type*} [Fintype ι] (A : ι → FiniteQuadraticModule)
    (n : ℕ) : scaledGaussSum (pi A) n = ∏ i, scaledGaussSum (A i) n := by
  classical
  let _ : ∀ i, Fintype (A i) := fun i ↦ Fintype.ofFinite _
  rw [scaledGaussSum_eq_sum]
  simp_rw [scaledGaussSum_eq_sum]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  have h := map_prod expCircle.toMonoidHom
    (fun i ↦ Multiplicative.ofAdd (n • (A i).quadratic (x i))) Finset.univ
  rw [← ofAdd_sum] at h
  rw [QuadraticMap.pi_apply, Finset.smul_sum]
  exact h

/-- Scaling the form of `q_θ^{(p)}(p^{j+e})` by `p^j` is the form of `q_θ^{(p)}(p^e)` read
through the reduction modulo `p^e`. -/
private theorem pow_nsmul_oddCyclic_quadratic (hp : Odd p) (j e : ℕ) (θ : ℤ)
    (x : ZMod (p ^ (j + e))) :
    p ^ j • (oddCyclic (p ^ (j + e)) hp.pow θ).quadratic x =
      (oddCyclic (p ^ e) hp.pow θ).quadratic
        (ZMod.castHom (pow_dvd_pow p (Nat.le_add_left e j)) (ZMod (p ^ e)) x) := by
  obtain ⟨t, rfl⟩ := ZMod.intCast_surjective x
  rw [map_intCast, oddCyclic_quadratic_intCast, oddCyclic_quadratic_intCast, ← AddCircle.coe_nsmul,
    ← sub_eq_zero, ← AddCircle.coe_sub]
  -- The difference of the representatives is `θ t² (p^j - 1) / 2`, an integer since `p` is odd.
  obtain ⟨s, hs⟩ := hp.pow (n := j)
  refine (AddCircle.coe_eq_zero_iff (1 : ℚ)).2 ⟨θ * t ^ 2 * (s : ℤ), ?_⟩
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.pos.ne'
  have hsQ : (p : ℚ) ^ j = 2 * s + 1 := by exact_mod_cast hs
  rw [zsmul_eq_mul, nsmul_eq_mul, pow_add]
  push_cast
  rw [hsQ]
  field_simp
  ring

/-- **The `p^j`-scaled Gauss sum of `q_θ^{(p)}(p^{j+e})`** is `p^j` times the Gauss sum of
`q_θ^{(p)}(p^e)`: reduction modulo `p^e` is `p^j`-to-one. -/
private theorem scaledGaussSum_oddCyclic_pow_add (hp : Odd p) (j e : ℕ) (θ : ℤ) :
    scaledGaussSum (oddCyclic (p ^ (j + e)) hp.pow θ) (p ^ j) =
      p ^ j * (oddCyclic (p ^ e) hp.pow θ).gaussSum := by
  have : NeZero p := ⟨hp.pos.ne'⟩
  have hdvd : p ^ e ∣ p ^ (j + e) := pow_dvd_pow p (Nat.le_add_left e j)
  let r := (ZMod.castHom hdvd (ZMod (p ^ e))).toAddMonoidHom
  have hr : Function.Surjective r := ZMod.castHom_surjective hdvd
  have hker : Nat.card r.ker = p ^ j := by
    have h := AddSubgroup.card_ker_mul_card_range r
    rw [AddMonoidHom.range_eq_top.2 hr, AddSubgroup.card_top, Nat.card_zmod, Nat.card_zmod] at h
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos e) (h.trans (pow_add p j e))
  let _ : Fintype (oddCyclic (p ^ (j + e)) hp.pow θ) := inferInstanceAs (Fintype (ZMod _))
  let _ : Fintype (oddCyclic (p ^ e) hp.pow θ) := inferInstanceAs (Fintype (ZMod _))
  rw [scaledGaussSum_eq_sum, gaussSum_eq_sum]
  have hsum := AddMonoidHom.sum_comp_of_surjective r hr
    fun y ↦ expCircle ((oddCyclic (p ^ e) hp.pow θ).quadratic y)
  rw [hker, nsmul_eq_mul, Nat.cast_pow] at hsum
  refine Eq.trans ?_ hsum
  exact Finset.sum_congr rfl fun x _ ↦ congrArg expCircle (pow_nsmul_oddCyclic_quadratic hp j e θ x)

/-- Scaling by `p^j` with `k ≤ j` kills the form of `q_θ^{(p)}(p^k)`, so the scaled Gauss sum is
the order `p^k`. -/
private theorem scaledGaussSum_oddCyclic_of_le (hp : Odd p) {k j : ℕ} (hkj : k ≤ j) (θ : ℤ) :
    scaledGaussSum (oddCyclic (p ^ k) hp.pow θ) (p ^ j) = p ^ k := by
  have : NeZero p := ⟨hp.pos.ne'⟩
  let _ : Fintype (oddCyclic (p ^ k) hp.pow θ) := inferInstanceAs (Fintype (ZMod _))
  have hcard : Nat.card (oddCyclic (p ^ k) hp.pow θ) = p ^ k := Nat.card_zmod _
  have hzero (x : oddCyclic (p ^ k) hp.pow θ) :
      p ^ j • (oddCyclic (p ^ k) hp.pow θ).quadratic x = 0 := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkj
    have hodd : Odd (Nat.card (oddCyclic (p ^ k) hp.pow θ)) := by rw [hcard]; exact hp.pow
    have h := natCard_nsmul_quadratic_of_odd _ hodd x
    rw [hcard] at h
    rw [pow_add, mul_nsmul, h, nsmul_zero]
  rw [scaledGaussSum_eq_sum]
  simp only [hzero, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, ← Nat.card_eq_fintype_card, hcard, Nat.cast_pow]

/-- A Legendre symbol `(θ/p) = ±1` raised to the `e`-th power is `e^{2πi · 2e(1 - (θ/p))/8}`. -/
private theorem expCircle_toRatAddCircle_eight_legendreSym [Fact p.Prime] (e : ℕ) {θ : ℤ}
    (hθ : (θ : ZMod p) ≠ 0) :
    expCircle (ZMod.toRatAddCircle 8 ((2 * e * (1 - legendreSym p θ) : ℤ) : ZMod 8)) =
      (legendreSym p θ : ℂ) ^ e := by
  rcases legendreSym.eq_one_or_neg_one p hθ with h | h <;> rw [h]
  · simp
  · rw [ZMod.toRatAddCircle_intCast,
      show ((2 * e * (1 - -1) : ℤ) : ℚ) / ((8 : ℕ) : ℚ) = e • (1 / 2 : ℚ) by push_cast; ring,
      AddCircle.coe_nsmul, AddChar.map_nsmul_eq_pow, expCircle_one_div_two]
    simp

/-- **The Gauss sum of `q_θ^{(p)}(p^e)`** is `(θ/p)^e` times that of `q_1^{(p)}(p^e)`: by
Nikulin's values, the Gauss-sum invariants differ by `4eη`, where `(θ/p) = (-1)^η`. -/
private theorem gaussSum_oddCyclic_eq_legendreSym_pow_mul [Fact p.Prime] (hp : Odd p) (e : ℕ)
    {θ : ℤ} (hθ : IsCoprime (p : ℤ) θ) :
    (oddCyclic (p ^ e) hp.pow θ).gaussSum =
      legendreSym p θ ^ e * (oddCyclic (p ^ e) hp.pow 1).gaussSum := by
  have hθ0 : (θ : ZMod p) ≠ 0 := ((ZMod.coe_int_isUnit_iff_isCoprime θ p).2 hθ).ne_zero
  have hnd (t : ℤ) (ht : IsCoprime (p : ℤ) t) : (oddCyclic (p ^ e) hp.pow t).IsNondegenerate := by
    rw [isNondegenerate_oddCyclic_iff]
    simpa only [Nat.cast_pow] using ht.pow_left
  have hcard (t : ℤ) : Nat.card (oddCyclic (p ^ e) hp.pow t) = p ^ e := Nat.card_zmod _
  rw [(hnd θ hθ).gaussSum_eq, (hnd 1 isCoprime_one_right).gaussSum_eq, hcard, hcard,
    gaussSign_oddCyclic hp e hθ, gaussSign_oddCyclic hp e isCoprime_one_right, legendreSym.at_one,
    show (e : ℤ) ^ 2 * (1 - p) + 2 * e * (1 - legendreSym p θ) =
      (e ^ 2 * (1 - p) + 2 * e * (1 - 1)) + 2 * e * (1 - legendreSym p θ) by ring,
    Int.cast_add, map_add, AddChar.map_add_eq_mul, expCircle_toRatAddCircle_eight_legendreSym e hθ0]
  push_cast
  ring

/-- **The scaled Gauss sums of `q_θ^{(p)}(p^k)`**: scaling by `p^j` multiplies the scaled Gauss
sum of `q_1^{(p)}(p^k)` by `(θ/p)^{k - j}`, with truncated subtraction. -/
private theorem scaledGaussSum_oddCyclic [Fact p.Prime] (hp : Odd p) (k j : ℕ) {θ : ℤ}
    (hθ : IsCoprime (p : ℤ) θ) :
    scaledGaussSum (oddCyclic (p ^ k) hp.pow θ) (p ^ j) =
      legendreSym p θ ^ (k - j) * scaledGaussSum (oddCyclic (p ^ k) hp.pow 1) (p ^ j) := by
  rcases le_total k j with hkj | hjk
  · rw [scaledGaussSum_oddCyclic_of_le hp hkj, scaledGaussSum_oddCyclic_of_le hp hkj,
      Nat.sub_eq_zero_of_le hkj, pow_zero, one_mul]
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hjk
    rw [scaledGaussSum_oddCyclic_pow_add hp, scaledGaussSum_oddCyclic_pow_add hp,
      gaussSum_oddCyclic_eq_legendreSym_pow_mul hp e hθ, Nat.add_sub_cancel_left]
    ring

/-- The scaled Gauss sums of `q_1^{(p)}(p^k)` do not vanish. -/
private theorem scaledGaussSum_oddCyclic_one_ne_zero (hp : Odd p) (k j : ℕ) :
    scaledGaussSum (oddCyclic (p ^ k) hp.pow 1) (p ^ j) ≠ 0 := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.pos.ne'
  rcases le_total k j with hkj | hjk
  · rw [scaledGaussSum_oddCyclic_of_le hp hkj]
    exact pow_ne_zero _ hp0
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hjk
    rw [scaledGaussSum_oddCyclic_pow_add hp]
    refine mul_ne_zero (pow_ne_zero _ hp0) fun h ↦ ?_
    have hnd : (oddCyclic (p ^ e) hp.pow 1).IsNondegenerate := by
      rw [isNondegenerate_oddCyclic_iff]
      exact isCoprime_one_right
    have := hnd.norm_gaussSum
    rw [h, norm_zero] at this
    exact (Real.sqrt_pos.2 (Nat.cast_pos.2 Nat.card_pos)).ne this

/-! ### The level products are isometry invariants -/

/-- If `u i ^ 2 = 1` and `∏ i, u i ^ (k i - j) = 1` for every `j`, then the product of the `u i`
with `k i = m` is `1` for every `m ≥ 1`. Multiplying the identities at `j = m - 1` and `j = m`
isolates the product over `k i ≥ m`, and the product over `k i = m` is a quotient of two such. -/
private theorem prod_filter_eq_one_of_forall_prod_pow_tsub_eq_one {ι M : Type*} [Fintype ι]
    [CommMonoid M] (k : ι → ℕ) (u : ι → M) (hu : ∀ i, u i ^ 2 = 1)
    (h : ∀ j, ∏ i, u i ^ (k i - j) = 1) {m : ℕ} (hm : 0 < m) :
    ∏ i with k i = m, u i = 1 := by
  have hT (m : ℕ) (hm : 0 < m) : ∏ i with m ≤ k i, u i = 1 := by
    calc ∏ i with m ≤ k i, u i = ∏ i, u i ^ ((k i - (m - 1)) + (k i - m)) := by
          rw [Finset.prod_filter]
          refine Finset.prod_congr rfl fun i _ ↦ ?_
          split_ifs with hi
          · rw [show k i - (m - 1) + (k i - m) = 2 * (k i - m) + 1 by omega, pow_succ, pow_mul,
              hu, one_pow, one_mul]
          · rw [show k i - (m - 1) + (k i - m) = 0 by omega, pow_zero]
      _ = 1 := by simp only [pow_add, Finset.prod_mul_distrib, h, one_mul]
  have h₁ : (Finset.univ.filter (m ≤ k ·)).filter (k · = m) = Finset.univ.filter (k · = m) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have h₂ : (Finset.univ.filter (m ≤ k ·)).filter (fun i ↦ ¬k i = m) =
      Finset.univ.filter (m + 1 ≤ k ·) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hsplit := Finset.prod_filter_mul_prod_filter_not (Finset.univ.filter (m ≤ k ·))
    (k · = m) u
  rwa [h₁, h₂, hT m hm, hT (m + 1) m.succ_pos, mul_one] at hsplit

variable {ι : Type*} [Fintype ι] [Fact p.Prime]

/-- The scaled Gauss sums of an orthogonal sum of odd cyclic generators at `p`. -/
private theorem scaledGaussSum_pi_oddCyclic (hp : Odd p) (k : ι → ℕ) {θ : ι → ℤ}
    (hθ : ∀ i, IsCoprime (p : ℤ) (θ i)) (j : ℕ) :
    scaledGaussSum (pi fun i ↦ oddCyclic (p ^ k i) hp.pow (θ i)) (p ^ j) =
      ((∏ i, legendreSym p (θ i) ^ (k i - j) : ℤ) : ℂ) *
        ∏ i, scaledGaussSum (oddCyclic (p ^ k i) hp.pow 1) (p ^ j) := by
  rw [scaledGaussSum_pi]
  simp_rw [scaledGaussSum_oddCyclic hp _ j (hθ _)]
  push_cast
  exact Finset.prod_mul_distrib

/-- **The level products are isometry invariants.** If two orthogonal sums of odd cyclic
generators `q_{θ_i}^{(p)}(p^{k_i})` and `q_{η_i}^{(p)}(p^{k_i})` with the same exponents are
isometric, then for every `m ≥ 1` the Legendre symbols of the coefficients of the summands of order
`p^m` have the same product. The proof compares the Gauss sums of the forms scaled by `p^j`. -/
private theorem prod_legendreSym_eq_of_isometry_pi_oddCyclic (hp : Odd p) (k : ι → ℕ) {θ η : ι → ℤ}
    (hθ : ∀ i, IsCoprime (p : ℤ) (θ i)) (hη : ∀ i, IsCoprime (p : ℤ) (η i))
    (f : Isometry (pi fun i ↦ oddCyclic (p ^ k i) hp.pow (θ i))
      (pi fun i ↦ oddCyclic (p ^ k i) hp.pow (η i))) {m : ℕ} (hm : 0 < m) :
    ∏ i with k i = m, legendreSym p (θ i) = ∏ i with k i = m, legendreSym p (η i) := by
  have hsq (t : ℤ) (ht : IsCoprime (p : ℤ) t) : legendreSym p t ^ 2 = 1 :=
    legendreSym.sq_one p ((ZMod.coe_int_isUnit_iff_isCoprime t p).2 ht).ne_zero
  -- The scaled Gauss sums of the two sums agree, which gives the identities at every `j`.
  have hj (j : ℕ) : ∏ i, (legendreSym p (θ i) * legendreSym p (η i)) ^ (k i - j) = 1 := by
    have h := f.scaledGaussSum_eq (p ^ j)
    rw [scaledGaussSum_pi_oddCyclic hp k hθ, scaledGaussSum_pi_oddCyclic hp k hη] at h
    have hθη := Int.cast_injective (α := ℂ) (mul_right_cancel₀ (Finset.prod_ne_zero_iff.2
      fun i _ ↦ scaledGaussSum_oddCyclic_one_ne_zero hp (k i) j) h)
    simp_rw [mul_pow, Finset.prod_mul_distrib, hθη, ← Finset.prod_mul_distrib, ← mul_pow, ← sq,
      hsq _ (hη _), one_pow, Finset.prod_const_one]
  have h := prod_filter_eq_one_of_forall_prod_pow_tsub_eq_one k _
    (fun i ↦ by rw [mul_pow, hsq _ (hθ i), hsq _ (hη i), one_mul]) hj hm
  rw [Finset.prod_mul_distrib] at h
  calc ∏ i with k i = m, legendreSym p (θ i)
      = (∏ i with k i = m, legendreSym p (θ i)) *
          ((∏ i with k i = m, legendreSym p (η i)) * ∏ i with k i = m, legendreSym p (η i)) := by
        rw [← Finset.prod_mul_distrib]
        simp_rw [← sq, hsq _ (hη _), Finset.prod_const_one, mul_one]
    _ = ∏ i with k i = m, legendreSym p (η i) := by rw [← mul_assoc, h, one_mul]

/-! ### Isometries from the relations -/

omit [Fact p.Prime] in
/-- Two odd cyclic generators of order `p^0 = 1` are isometric: both are trivial. -/
private theorem nonempty_isometry_oddCyclic_of_eq_zero (hp : Odd p) {e : ℕ} (he : e = 0)
    (a b : ℤ) : Nonempty (Isometry (oddCyclic (p ^ e) hp.pow a) (oddCyclic (p ^ e) hp.pow b)) := by
  subst he
  have : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
  exact (nonempty_isometry_oddCyclic_iff _ _ a b).2 ⟨1, Subsingleton.elim _ _⟩

/-- Odd cyclic generators `q_a^{(p)}(p^e)` and `q_b^{(p)}(p^e)` with the same Legendre symbol are
isometric: `ab` is then a square modulo `p^e`. -/
private theorem nonempty_isometry_oddCyclic_of_legendreSym_eq (hp : Odd p) (e : ℕ) {a b : ℤ}
    (ha : IsCoprime (p : ℤ) a) (hb : IsCoprime (p : ℤ) b) (h : legendreSym p a = legendreSym p b) :
    Nonempty (Isometry (oddCyclic (p ^ e) hp.pow a) (oddCyclic (p ^ e) hp.pow b)) := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · exact nonempty_isometry_oddCyclic_of_eq_zero hp rfl a b
  have hp2 : p ≠ 2 := by rintro rfl; exact Nat.not_even_iff_odd.2 hp even_two
  have hab0 : ((a * b : ℤ) : ZMod p) ≠ 0 :=
    ((ZMod.coe_int_isUnit_iff_isCoprime _ p).2 (ha.mul_right hb)).ne_zero
  -- `ab` has `1 + (ab/p) = 2` square roots modulo `p^e`.
  have hcount := TauCeti.ZMod.natCard_sqrts_prime_pow_eq_legendreSym_add_one hp2 he.ne' hab0
  rw [legendreSym.mul, h, ← sq,
    legendreSym.sq_one p ((ZMod.coe_int_isUnit_iff_isCoprime b p).2 hb).ne_zero] at hcount
  obtain ⟨⟨x, hx⟩⟩ := (Nat.card_pos_iff.1 (by omega : 0 < Nat.card
    {x : ZMod (p ^ e) // x ^ 2 = ((a * b : ℤ) : ZMod (p ^ e))})).1
  have hbu : IsUnit (b : ZMod (p ^ e)) :=
    (ZMod.coe_int_isUnit_iff_isCoprime b (p ^ e)).2 (by simpa using hb.pow_left)
  have hxu : IsUnit x := by
    have hau : IsUnit (a : ZMod (p ^ e)) :=
      (ZMod.coe_int_isUnit_iff_isCoprime a (p ^ e)).2 (by simpa using ha.pow_left)
    have : IsUnit (x ^ 2) := by rw [hx]; push_cast; exact hau.mul hbu
    exact isUnit_pow_iff two_ne_zero |>.1 this
  refine (nonempty_isometry_oddCyclic_iff _ _ a b).2 ⟨hxu.unit * hbu.unit⁻¹, ?_⟩
  have hinv : (b : ZMod (p ^ e)) * ↑hbu.unit⁻¹ = 1 := by
    simpa only [IsUnit.unit_spec] using hbu.unit.mul_inv
  push_cast at hx ⊢
  rw [mul_pow, IsUnit.unit_spec, hx]
  linear_combination (-(a : ZMod (p ^ e)) * (b * ↑hbu.unit⁻¹ + 1)) * hinv

/-- **The binary relation at an odd prime.** Orthogonal sums `q_a ⊕ q_b` and `q_c ⊕ q_d` of odd
cyclic generators of the same order `p^e` are isometric as soon as `(a/p)(b/p) = (c/p)(d/p)`.
It follows from Nikulin's doubled relation `q_θ ⊕ q_θ ≅ q_η ⊕ q_η`. -/
private theorem nonempty_isometry_oddCyclic_prod (hp : Odd p) (e : ℕ) {a b c d : ℤ}
    (ha : IsCoprime (p : ℤ) a) (hb : IsCoprime (p : ℤ) b) (hc : IsCoprime (p : ℤ) c)
    (hd : IsCoprime (p : ℤ) d) (h : legendreSym p a * legendreSym p b =
      legendreSym p c * legendreSym p d) :
    Nonempty (Isometry ((oddCyclic (p ^ e) hp.pow a).prod (oddCyclic (p ^ e) hp.pow b))
      ((oddCyclic (p ^ e) hp.pow c).prod (oddCyclic (p ^ e) hp.pow d))) := by
  have hχ (t : ℤ) (ht : IsCoprime (p : ℤ) t) : legendreSym p t = 1 ∨ legendreSym p t = -1 :=
    legendreSym.eq_one_or_neg_one p ((ZMod.coe_int_isUnit_iff_isCoprime t p).2 ht).ne_zero
  have hcyc := fun {s t : ℤ} (hs : IsCoprime (p : ℤ) s) (ht : IsCoprime (p : ℤ) t)
    (hst : legendreSym p s = legendreSym p t) ↦
      nonempty_isometry_oddCyclic_of_legendreSym_eq hp e hs ht hst
  -- Every `q_s ⊕ q_t` is isometric to `q_1 ⊕ q_{st}`.
  have key (s t : ℤ) (hs : IsCoprime (p : ℤ) s) (ht : IsCoprime (p : ℤ) t) :
      Nonempty (Isometry ((oddCyclic (p ^ e) hp.pow s).prod (oddCyclic (p ^ e) hp.pow t))
        ((oddCyclic (p ^ e) hp.pow 1).prod (oddCyclic (p ^ e) hp.pow (s * t)))) := by
    have h1 : IsCoprime (p : ℤ) 1 := isCoprime_one_right
    have hst : IsCoprime (p : ℤ) (s * t) := hs.mul_right ht
    rcases hχ s hs with hs1 | hs1
    · obtain ⟨f⟩ := hcyc hs h1 (by rw [hs1, legendreSym.at_one])
      obtain ⟨g⟩ := hcyc ht hst (by rw [legendreSym.mul, hs1, one_mul])
      exact ⟨f.prod g⟩
    rcases hχ t ht with ht1 | ht1
    · obtain ⟨f⟩ := hcyc ht h1 (by rw [ht1, legendreSym.at_one])
      obtain ⟨g⟩ := hcyc hs hst (by rw [legendreSym.mul, ht1, mul_one])
      exact ⟨(QuadraticMap.IsometryEquiv.prodComm _ _).trans (f.prod g)⟩
    · obtain ⟨f⟩ := hcyc ht hs (by rw [hs1, ht1])
      obtain ⟨g⟩ := hcyc h1 hst (by rw [legendreSym.mul, hs1, ht1, legendreSym.at_one]; norm_num)
      have hpe (u : ℤ) (hu : IsCoprime (p : ℤ) u) : IsCoprime ((p ^ e : ℕ) : ℤ) u := by
        simpa using hu.pow_left
      exact ⟨((QuadraticMap.IsometryEquiv.refl _).prod f).trans
        ((oddCyclicProdSelfIsometry p e hp (hpe s hs) (hpe 1 h1)).trans
          ((QuadraticMap.IsometryEquiv.refl _).prod g))⟩
  obtain ⟨f⟩ := key a b ha hb
  obtain ⟨g⟩ := key c d hc hd
  obtain ⟨u⟩ := hcyc (ha.mul_right hb) (hc.mul_right hd)
    (by rw [legendreSym.mul, legendreSym.mul, h])
  exact ⟨f.trans (((QuadraticMap.IsometryEquiv.refl _).prod u).trans g.symm)⟩

omit [Fact p.Prime] in
/-- An orthogonal sum indexed by `Fin (n + 1)` with coefficients `Fin.cons x θ` is the
orthogonal product of `q_x^{(p)}(p^{k_0})` with the sum of the remaining summands. -/
private theorem nonempty_isometry_prod_pi_oddCyclic_cons (hp : Odd p) {n : ℕ}
    (k : Fin (n + 1) → ℕ) (x : ℤ) (θ : Fin n → ℤ) :
    Nonempty (Isometry
      ((oddCyclic (p ^ k 0) hp.pow x).prod
        (pi fun i : Fin n ↦ oddCyclic (p ^ k i.succ) hp.pow (θ i)))
      (pi fun i ↦ oddCyclic (p ^ k i) hp.pow ((Fin.cons x θ : Fin (n + 1) → ℤ) i))) :=
  ⟨(Isometry.ofEq (A' := (oddCyclic (p ^ k 0) hp.pow ((Fin.cons x θ : Fin (n + 1) → ℤ) 0)).prod
      (pi fun i : Fin n ↦
        oddCyclic (p ^ k i.succ) hp.pow ((Fin.cons x θ : Fin (n + 1) → ℤ) i.succ)))
      (by simp only [Fin.cons_zero, Fin.cons_succ])).trans
    (QuadraticMap.IsometryEquiv.consPi fun i ↦
      (oddCyclic (p ^ k i) hp.pow ((Fin.cons x θ : Fin (n + 1) → ℤ) i)).quadratic)⟩

/-- **Transferring a Legendre symbol into the tail.** If some summand of `⊕ q_{θ_i}^{(p)}(p^{k_i})`
has order `p^e`, then `q_a^{(p)}(p^e) ⊕ (⊕ q_{θ_i})` is isometric to `q_b^{(p)}(p^e) ⊕ (⊕ q_{θ'_i})`
for some coefficients `θ'` prime to `p`: apply the binary relation to `q_a` and that summand. -/
private theorem exists_isometry_oddCyclic_prod_pi (hp : Odd p) {n : ℕ} (k : Fin n → ℕ)
    {θ : Fin n → ℤ} (hθ : ∀ i, IsCoprime (p : ℤ) (θ i)) {e : ℕ} {a b : ℤ}
    (ha : IsCoprime (p : ℤ) a) (hb : IsCoprime (p : ℤ) b) (hk : ∃ i, k i = e) :
    ∃ θ' : Fin n → ℤ, (∀ i, IsCoprime (p : ℤ) (θ' i)) ∧
      Nonempty (Isometry
        ((oddCyclic (p ^ e) hp.pow a).prod (pi fun i ↦ oddCyclic (p ^ k i) hp.pow (θ i)))
        ((oddCyclic (p ^ e) hp.pow b).prod (pi fun i ↦ oddCyclic (p ^ k i) hp.pow (θ' i)))) := by
  induction n with
  | zero => exact (hk.choose.elim0)
  | succ n ih =>
    obtain ⟨i, hi⟩ := hk
    let split :=
      QuadraticMap.IsometryEquiv.consPi fun i ↦ (oddCyclic (p ^ k i) hp.pow (θ i)).quadratic
    cases i using Fin.cases with
    | zero =>
      -- Apply the binary relation to `q_a` and the first summand.
      subst hi
      obtain ⟨c, hc, ⟨g⟩⟩ : ∃ c : ℤ, IsCoprime (p : ℤ) c ∧ Nonempty (Isometry
          ((oddCyclic (p ^ k 0) hp.pow a).prod (oddCyclic (p ^ k 0) hp.pow (θ 0)))
          ((oddCyclic (p ^ k 0) hp.pow b).prod (oddCyclic (p ^ k 0) hp.pow c))) := by
        have hθ₀ : IsCoprime (p : ℤ) (θ 0 * a * b) := ((hθ 0).mul_right ha).mul_right hb
        refine ⟨θ 0 * a * b, hθ₀, nonempty_isometry_oddCyclic_prod hp (k 0) ha (hθ 0) hb hθ₀ ?_⟩
        rw [legendreSym.mul, legendreSym.mul]
        linear_combination -(legendreSym p a * legendreSym p (θ 0)) *
          legendreSym.sq_one p ((ZMod.coe_int_isUnit_iff_isCoprime b p).2 hb).ne_zero
      refine ⟨Fin.cons c fun i ↦ θ i.succ, by
        intro i; cases i using Fin.cases <;> simp [hc, hθ], ?_⟩
      obtain ⟨u⟩ := nonempty_isometry_prod_pi_oddCyclic_cons hp k c fun i ↦ θ i.succ
      exact ⟨((QuadraticMap.IsometryEquiv.refl _).prod split.symm).trans
        ((QuadraticMap.IsometryEquiv.prodAssoc _ _ _).symm.trans
          ((g.prod (QuadraticMap.IsometryEquiv.refl _)).trans
            ((QuadraticMap.IsometryEquiv.prodAssoc _ _ _).trans
              ((QuadraticMap.IsometryEquiv.refl _).prod u))))⟩
    | succ j =>
      -- Move `q_a` past the first summand and use the induction hypothesis.
      obtain ⟨θ', hθ', ⟨g⟩⟩ := ih (fun i ↦ k i.succ) (fun i ↦ hθ i.succ) ⟨j, hi⟩
      refine ⟨Fin.cons (θ 0) θ', by intro i; cases i using Fin.cases <;> simp [hθ, hθ'], ?_⟩
      obtain ⟨u⟩ := nonempty_isometry_prod_pi_oddCyclic_cons hp k (θ 0) θ'
      exact ⟨((QuadraticMap.IsometryEquiv.refl _).prod split.symm).trans
        ((QuadraticMap.IsometryEquiv.prodLeftComm _ _ _).trans
          (((QuadraticMap.IsometryEquiv.refl _).prod g).trans
            ((QuadraticMap.IsometryEquiv.prodLeftComm _ _ _).trans
              ((QuadraticMap.IsometryEquiv.refl _).prod u))))⟩

/-- The product of a function over the indices of `Fin (n + 1)` with a given level splits off the
first index. -/
private theorem prod_filter_fin_succ {M : Type*} [CommMonoid M] {n : ℕ} (k : Fin (n + 1) → ℕ)
    (f : Fin (n + 1) → M) (m : ℕ) :
    ∏ i with k i = m, f i =
      (if k 0 = m then f 0 else 1) * ∏ i : Fin n with k i.succ = m, f i.succ := by
  rw [Finset.prod_filter, Fin.prod_univ_succ, Finset.prod_filter]

/-- If the level products of Legendre symbols of two families indexed by `Fin (n + 1)` agree and
their first coefficients match (or the first summand is trivial), then the level products of the
remaining coefficients agree. -/
private theorem prod_legendreSym_succ_eq {n : ℕ} (k : Fin (n + 1) → ℕ) {θ η : Fin (n + 1) → ℤ}
    (hθ : IsCoprime (p : ℤ) (θ 0))
    (h : ∀ m, 0 < m → ∏ i with k i = m, legendreSym p (θ i) = ∏ i with k i = m, legendreSym p (η i))
    (h0 : k 0 = 0 ∨ legendreSym p (θ 0) = legendreSym p (η 0)) {m : ℕ} (hm : 0 < m) :
    ∏ i : Fin n with k i.succ = m, legendreSym p (θ i.succ) =
      ∏ i : Fin n with k i.succ = m, legendreSym p (η i.succ) := by
  have hm' := h m hm
  rw [prod_filter_fin_succ, prod_filter_fin_succ] at hm'
  refine mul_left_cancel₀ ?_ (hm'.trans ?_)
  · split_ifs
    · exact fun h0 ↦ ((ZMod.coe_int_isUnit_iff_isCoprime _ p).2 hθ).ne_zero
        ((legendreSym.eq_zero_iff p _).1 h0)
    · exact one_ne_zero
  · split_ifs with hkm
    · rcases h0 with h0 | h0
      · omega
      · rw [h0]
    · rfl

/-- **Equal level products give isometric sums.** If for every `m ≥ 1` the Legendre symbols of
the coefficients of the summands of order `p^m` have the same product, then the orthogonal sums
`⊕ q_{θ_i}^{(p)}(p^{k_i})` and `⊕ q_{η_i}^{(p)}(p^{k_i})` are isometric. -/
private theorem nonempty_isometry_pi_oddCyclic_of_prod_legendreSym_eq_fin (hp : Odd p) {n : ℕ}
    (k : Fin n → ℕ) {θ η : Fin n → ℤ} (hθ : ∀ i, IsCoprime (p : ℤ) (θ i))
    (hη : ∀ i, IsCoprime (p : ℤ) (η i))
    (h : ∀ m, 0 < m →
      ∏ i with k i = m, legendreSym p (θ i) = ∏ i with k i = m, legendreSym p (η i)) :
    Nonempty (Isometry (pi fun i ↦ oddCyclic (p ^ k i) hp.pow (θ i))
      (pi fun i ↦ oddCyclic (p ^ k i) hp.pow (η i))) := by
  induction n with
  | zero => exact ⟨Isometry.ofSubsingleton⟩
  | succ n ih =>
    -- If the first summands match, split them off and use the induction hypothesis.
    have step (θ' : Fin (n + 1) → ℤ) (hθ' : ∀ i, IsCoprime (p : ℤ) (θ' i))
        (h' : ∀ m, 0 < m → ∏ i with k i = m, legendreSym p (θ' i) =
          ∏ i with k i = m, legendreSym p (η i))
        (h0 : k 0 = 0 ∨ legendreSym p (θ' 0) = legendreSym p (η 0)) :
        Nonempty (Isometry (pi fun i ↦ oddCyclic (p ^ k i) hp.pow (θ' i))
          (pi fun i ↦ oddCyclic (p ^ k i) hp.pow (η i))) := by
      obtain ⟨g⟩ : Nonempty (Isometry (oddCyclic (p ^ k 0) hp.pow (θ' 0))
          (oddCyclic (p ^ k 0) hp.pow (η 0))) := by
        rcases h0 with h0 | h0
        · exact nonempty_isometry_oddCyclic_of_eq_zero hp h0 _ _
        · exact nonempty_isometry_oddCyclic_of_legendreSym_eq hp (k 0) (hθ' 0) (hη 0) h0
      obtain ⟨g'⟩ := ih (fun i ↦ k i.succ) (fun i ↦ hθ' i.succ) (fun i ↦ hη i.succ)
        fun _ hm ↦ prod_legendreSym_succ_eq k (hθ' 0) h' h0 hm
      exact ⟨(QuadraticMap.IsometryEquiv.consPi fun i ↦
          (oddCyclic (p ^ k i) hp.pow (θ' i)).quadratic).symm.trans
        ((g.prod g').trans (QuadraticMap.IsometryEquiv.consPi fun i ↦
          (oddCyclic (p ^ k i) hp.pow (η i)).quadratic))⟩
    by_cases h0 : k 0 = 0 ∨ legendreSym p (θ 0) = legendreSym p (η 0)
    · exact step θ hθ h h0
    push Not at h0
    obtain ⟨hk0, hχ⟩ := h0
    -- Otherwise the tail has a summand of order `p^{k 0}`, which can absorb the mismatch.
    have hk : ∃ j : Fin n, k j.succ = k 0 := by
      by_contra hne'
      push Not at hne'
      have hm := h (k 0) (Nat.pos_of_ne_zero hk0)
      simp only [prod_filter_fin_succ, hne', Finset.filter_false, Finset.prod_empty,
        mul_one, ↓reduceIte] at hm
      exact hχ hm
    obtain ⟨θ', hθ', ⟨g⟩⟩ :=
      exists_isometry_oddCyclic_prod_pi hp (fun i ↦ k i.succ) (fun i ↦ hθ i.succ) (hθ 0) (hη 0) hk
    have hθ'' : ∀ i, IsCoprime (p : ℤ) ((Fin.cons (η 0) θ' : Fin (n + 1) → ℤ) i) := by
      intro i; cases i using Fin.cases <;> simp [hη, hθ']
    obtain ⟨u⟩ := nonempty_isometry_prod_pi_oddCyclic_cons hp k (η 0) θ'
    let f : Isometry (pi fun i ↦ oddCyclic (p ^ k i) hp.pow (θ i))
        (pi fun i ↦ oddCyclic (p ^ k i) hp.pow ((Fin.cons (η 0) θ' : Fin (n + 1) → ℤ) i)) :=
      (QuadraticMap.IsometryEquiv.consPi fun i ↦
          (oddCyclic (p ^ k i) hp.pow (θ i)).quadratic).symm.trans (g.trans u)
    obtain ⟨f'⟩ := step _ hθ'' (fun m hm ↦
      (prod_legendreSym_eq_of_isometry_pi_oddCyclic hp k hθ hθ'' f hm).symm.trans (h m hm))
      (Or.inr (by rw [Fin.cons_zero]))
    exact ⟨f.trans f'⟩

/-- **Equal level products give isometric sums.** If for every `m ≥ 1` the Legendre symbols of
the coefficients of the summands of order `p^m` have the same product, then the orthogonal sums
`⊕ q_{θ_i}^{(p)}(p^{k_i})` and `⊕ q_{η_i}^{(p)}(p^{k_i})` are isometric. -/
private theorem nonempty_isometry_pi_oddCyclic_of_prod_legendreSym_eq (hp : Odd p) (k : ι → ℕ)
    {θ η : ι → ℤ} (hθ : ∀ i, IsCoprime (p : ℤ) (θ i)) (hη : ∀ i, IsCoprime (p : ℤ) (η i))
    (h : ∀ m, 0 < m →
      ∏ i with k i = m, legendreSym p (θ i) = ∏ i with k i = m, legendreSym p (η i)) :
    Nonempty (Isometry (pi fun i ↦ oddCyclic (p ^ k i) hp.pow (θ i))
      (pi fun i ↦ oddCyclic (p ^ k i) hp.pow (η i))) := by
  -- Reindex by `Fin n`.
  let e := (Fintype.equivFin ι).symm
  let u := QuadraticMap.IsometryEquiv.piCongrLeft
    (fun i ↦ (oddCyclic (p ^ k i) hp.pow (θ i)).quadratic) e
  let v := QuadraticMap.IsometryEquiv.piCongrLeft
    (fun i ↦ (oddCyclic (p ^ k i) hp.pow (η i)).quadratic) e
  obtain ⟨g⟩ := nonempty_isometry_pi_oddCyclic_of_prod_legendreSym_eq_fin hp (fun j ↦ k (e j))
    (fun j ↦ hθ (e j)) (fun j ↦ hη (e j)) fun m hm ↦ by
      have hm' := h m hm
      rw [Finset.prod_filter, Finset.prod_filter] at hm' ⊢
      rwa [← e.prod_comp, ← e.prod_comp] at hm'
  exact ⟨u.symm.trans (g.trans v)⟩

/-- **Classification of orthogonal sums of odd cyclic generators at an odd prime.** For an odd
prime `p`, exponents `k_i` and coefficients `θ_i`, `η_i` prime to `p`, the orthogonal sums
`⊕ q_{θ_i}^{(p)}(p^{k_i})` and `⊕ q_{η_i}^{(p)}(p^{k_i})` are isometric exactly when, for every
`m ≥ 1`, the Legendre symbols of the coefficients of the summands of order `p^m` have the same
product. -/
theorem nonempty_isometry_pi_oddCyclic_iff (hp : Odd p) (k : ι → ℕ) {θ η : ι → ℤ}
    (hθ : ∀ i, IsCoprime (p : ℤ) (θ i)) (hη : ∀ i, IsCoprime (p : ℤ) (η i)) :
    Nonempty (Isometry (pi fun i ↦ oddCyclic (p ^ k i) hp.pow (θ i))
      (pi fun i ↦ oddCyclic (p ^ k i) hp.pow (η i))) ↔
      ∀ m, 0 < m → ∏ i with k i = m, legendreSym p (θ i) = ∏ i with k i = m, legendreSym p (η i) :=
  ⟨fun ⟨f⟩ _ hm ↦ prod_legendreSym_eq_of_isometry_pi_oddCyclic hp k hθ hη f hm,
    nonempty_isometry_pi_oddCyclic_of_prod_legendreSym_eq hp k hθ hη⟩

end TauCeti.FiniteQuadraticModule
