/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.Basic
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Pi
import TauCeti.Algebra.BigOperators.Fin
import TauCeti.Algebra.BigOperators.Finset.Filter
import TauCeti.Data.Fintype.Fiber
import TauCeti.GroupTheory.SpecificGroups.Cyclic.ElementaryDivisors
import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.Classification
import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.GaussSum
import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.Relations
import TauCeti.LinearAlgebra.QuadraticForm.Prod

/-!
# Classification of orthogonal sums of odd cyclic generators

For an odd prime `p`, Nikulin's decomposition writes every nondegenerate finite quadratic module of
`p`-power order as an orthogonal sum of odd cyclic generators `q_θ^{(p)}(p^k)`
(`TauCeti.FiniteQuadraticModule.exists_isometry_pi_oddCyclic`). Such a decomposition is not
unique, and this file decides when two orthogonal sums of these generators are isometric. For
exponents `k_i`, `l_j` and coefficients `θ_i`, `η_j` prime to `p`,

```text
⊕ᵢ q_{θ_i}^{(p)}(p^{k_i}) ≅ ⊕ⱼ q_{η_j}^{(p)}(p^{l_j})
  ↔  #{i | k_i = m} = #{j | l_j = m}  and  ∏_{k_i = m} (θ_i/p) = ∏_{l_j = m} (η_j/p)
     for every m ≥ 1.
```

So the isometry class of the sum only depends on the number of summands of each order `p^m` and
on the product of the Legendre symbols of their coefficients; summands of order `p^0 = 1` are
trivial and impose nothing. Together with Nikulin's decomposition, this classifies the
nondegenerate finite quadratic modules of odd prime-power order up to isometry.

The numbers of summands of each order are invariants of the underlying group
(`ZMod.exists_equiv_exponents_of_pi_pow_addEquiv`). Once they agree, deleting the
trivial summands and matching the others by their orders reduces the classification to two sums
with the same exponents.

The invariance of the level products is a Gauss-sum computation. For `j ≥ 0` the scaled Gauss sum
`∑_x e^{2πi p^j q(x)}` (`TauCeti.FiniteQuadraticModule.scaledGaussSum`) is an isometry invariant
and is multiplicative over orthogonal sums. On `q_θ^{(p)}(p^k)` it is `(θ/p)^{k - j}` times its
value at `θ = 1`, by Nikulin's values of the Gauss-sum invariant on the generators
(`TauCeti.FiniteQuadraticModule.gaussSign_oddCyclic`), so an isometry gives
`∏ᵢ ((θ_i/p)(η_i/p))^{k_i - j} = 1` for every `j`. Comparing `j = m - 1` with `j = m` isolates the
product over the summands with `k_i ≥ m`, and hence over those with `k_i = m`.

Conversely, two odd cyclic generators of the same order with the same Legendre symbol are
isometric (`TauCeti.FiniteQuadraticModule.nonempty_isometry_oddCyclic_of_legendreSym_eq`), and
Nikulin's doubled relation `q_θ ⊕ q_θ ≅ q_η ⊕ q_η` shows that `q_a ⊕ q_b ≅ q_c ⊕ q_d` whenever
`(a/p)(b/p) = (c/p)(d/p)` (`TauCeti.FiniteQuadraticModule.nonempty_isometry_oddCyclic_prod`).
Equal level products therefore allow the coefficients to be matched one summand at a time, moving
a mismatched Legendre symbol onto another summand of the same order.

## Main declarations

* `TauCeti.FiniteQuadraticModule.nonempty_isometry_pi_oddCyclic_iff`: two orthogonal sums of odd
  cyclic generators at `p` are isometric exactly when they have the same number of summands of
  each order `p^m`, `m ≥ 1`, and the same level products of Legendre symbols.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Propositions 1.8.1, 1.8.2 and 1.11.2.
* C. T. C. Wall, *Quadratic forms on finite groups, and related topics*, Topology 2 (1963),
  281–298.
-/

public section

namespace TauCeti.FiniteQuadraticModule

variable {p : ℕ}

/-! ### The level products are isometry invariants -/

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
    legendreSym.sq_one p ((ZMod.isUnit_intCast_iff_isCoprime t p).2 ht).ne_zero
  -- The scaled Gauss sums of the two sums agree, which gives the identities at every `j`.
  have hj (j : ℕ) : ∏ i, (legendreSym p (θ i) * legendreSym p (η i)) ^ (k i - j) = 1 := by
    have h := f.scaledGaussSum_eq (p ^ j)
    rw [scaledGaussSum_pi_oddCyclic hp k hθ, scaledGaussSum_pi_oddCyclic hp k hη] at h
    have hθη := Int.cast_injective (α := ℂ) (mul_right_cancel₀ (Finset.prod_ne_zero_iff.2
      fun i _ ↦ scaledGaussSum_oddCyclic_one_ne_zero hp (k i) j) h)
    simp_rw [mul_pow, Finset.prod_mul_distrib, hθη, ← Finset.prod_mul_distrib, ← mul_pow, ← sq,
      hsq _ (hη _), one_pow, Finset.prod_const_one]
  have h := Finset.univ.prod_filter_eq_one_of_forall_prod_pow_tsub_eq_one k _
    (fun i _ _ ↦ by rw [mul_pow, hsq _ (hθ i), hsq _ (hη i), one_mul]) hj hm
  rw [Finset.prod_mul_distrib] at h
  calc ∏ i with k i = m, legendreSym p (θ i)
      = (∏ i with k i = m, legendreSym p (θ i)) *
          ((∏ i with k i = m, legendreSym p (η i)) * ∏ i with k i = m, legendreSym p (η i)) := by
        rw [← Finset.prod_mul_distrib]
        simp_rw [← sq, hsq _ (hη _), Finset.prod_const_one, mul_one]
    _ = ∏ i with k i = m, legendreSym p (η i) := by rw [← mul_assoc, h, one_mul]

/-! ### Isometries from the relations -/

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
          legendreSym.sq_one p ((ZMod.isUnit_intCast_iff_isCoprime b p).2 hb).ne_zero
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
        fun m hm ↦ Fin.prod_filter_succ_eq_of_prod_filter_eq (k · = m) (h' m hm)
          (fun _ h ↦ ((ZMod.isUnit_intCast_iff_isCoprime _ p).2 (hθ' 0)).ne_zero
            ((legendreSym.eq_zero_iff p _).1 h))
          fun hk ↦ h0.resolve_left (by omega)
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
      simp only [Fin.prod_filter_univ_succ, hne', Finset.filter_false, Finset.prod_empty,
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

/-! ### Sums with different exponents -/

open Finset Function

variable {κ : Type*} [Fintype κ]

omit [Fact p.Prime] in
/-- The summands of order `p^0 = 1` of an orthogonal sum of odd cyclic generators are trivial, so
deleting them is isometric. -/
private noncomputable def isometryPiOddCyclicNeZero (hp : Odd p) (k : ι → ℕ) (θ : ι → ℤ) :
    Isometry (pi fun i ↦ oddCyclic (p ^ k i) hp.pow (θ i))
      (pi fun i : {i // k i ≠ 0} ↦ oddCyclic (p ^ k i) hp.pow (θ i)) :=
  QuadraticMap.IsometryEquiv.piSubtype _ _ fun i hi ↦ by
    have h : Nat.card (oddCyclic (p ^ k i) hp.pow (θ i)) = 1 := by
      rw [natCard_oddCyclic, not_not.mp hi, pow_zero]
    exact (Nat.card_eq_one_iff_unique.mp h).1

omit [Fact p.Prime] in
/-- Matching the nontrivial summands of `⊕ⱼ q_{η_j}^{(p)}(p^{l_j})` with those of an exponent
family `k` along `σ` rewrites the sum with the exponents `k`. -/
private noncomputable def isometryPiOddCyclicOfEquiv (hp : Odd p) (k : ι → ℕ) (l : κ → ℕ)
    (η : κ → ℤ) (σ : {i // k i ≠ 0} ≃ {j // l j ≠ 0}) (hσ : ∀ i, l (σ i) = k i) :
    Isometry (pi fun j ↦ oddCyclic (p ^ l j) hp.pow (η j))
      (pi fun i : {i // k i ≠ 0} ↦ oddCyclic (p ^ k i) hp.pow (η (σ i))) :=
  (isometryPiOddCyclicNeZero hp l η).trans <|
    (QuadraticMap.IsometryEquiv.piCongrLeft
      (fun j : {j // l j ≠ 0} ↦ (oddCyclic (p ^ l j) hp.pow (η j)).quadratic) σ).symm.trans <|
    QuadraticMap.IsometryEquiv.pi fun i ↦ Isometry.ofEq (by rw [hσ i])

/-- **Classification of orthogonal sums of odd cyclic generators at an odd prime.** For an odd
prime `p`, exponents `k_i`, `l_j` and coefficients `θ_i`, `η_j` prime to `p`, the orthogonal sums
`⊕ᵢ q_{θ_i}^{(p)}(p^{k_i})` and `⊕ⱼ q_{η_j}^{(p)}(p^{l_j})` are isometric exactly when, for every
`m ≥ 1`, they have the same number of summands of order `p^m`, and the Legendre symbols of the
coefficients of these summands have the same product. Summands of order `p^0 = 1` are trivial and
impose nothing. -/
theorem nonempty_isometry_pi_oddCyclic_iff (hp : Odd p) (k : ι → ℕ) (l : κ → ℕ) {θ : ι → ℤ}
    {η : κ → ℤ} (hθ : ∀ i, IsCoprime (p : ℤ) (θ i)) (hη : ∀ j, IsCoprime (p : ℤ) (η j)) :
    Nonempty (Isometry (pi fun i ↦ oddCyclic (p ^ k i) hp.pow (θ i))
      (pi fun j ↦ oddCyclic (p ^ l j) hp.pow (η j))) ↔
      ∀ m, 0 < m → #{i | k i = m} = #{j | l j = m} ∧
        ∏ i with k i = m, legendreSym p (θ i) = ∏ j with l j = m, legendreSym p (η j) := by
  -- Once the numbers of summands of each order agree, both sides are sums over `{i // k i ≠ 0}`
  -- with the exponents `k`, and the classification with equal exponents applies.
  have key (hcard : ∀ m, 0 < m → #{i | k i = m} = #{j | l j = m}) :
      Nonempty (Isometry (pi fun i ↦ oddCyclic (p ^ k i) hp.pow (θ i))
        (pi fun j ↦ oddCyclic (p ^ l j) hp.pow (η j))) ↔
        ∀ m, 0 < m →
          ∏ i with k i = m, legendreSym p (θ i) = ∏ j with l j = m, legendreSym p (η j) := by
    obtain ⟨σ, hσ⟩ := exists_equiv_subtype_ne_of_occCount_eq (u := k) (v := l) (z := 0)
      fun m hm ↦ by
        rw [occCount_eq_card_filter, occCount_eq_card_filter]
        exact hcard m (Nat.pos_of_ne_zero hm)
    let D := isometryPiOddCyclicNeZero hp k θ
    let G := isometryPiOddCyclicOfEquiv hp k l η σ hσ
    have hprod (m : ℕ) (hm : 0 < m) :
        (∏ i ∈ ({i | k i = m} : Finset {i // k i ≠ 0}), legendreSym p (θ i) =
          ∏ i ∈ ({i | k i = m} : Finset {i // k i ≠ 0}), legendreSym p (η (σ i))) ↔
          ∏ i with k i = m, legendreSym p (θ i) = ∏ j with l j = m, legendreSym p (η j) := by
      rw [prod_filter_subtype_ne k (fun i ↦ legendreSym p (θ i)) hm.ne',
        prod_filter_subtype_ne_equiv k l (fun j ↦ legendreSym p (η j)) σ hσ hm.ne']
    constructor
    · rintro ⟨f⟩ m hm
      exact (hprod m hm).mp (prod_legendreSym_eq_of_isometry_pi_oddCyclic hp
        (fun i : {i // k i ≠ 0} ↦ k i) (fun i ↦ hθ i) (fun i ↦ hη (σ i))
        (D.symm.trans (f.trans G)) hm)
    · intro h
      obtain ⟨g⟩ := nonempty_isometry_pi_oddCyclic_of_prod_legendreSym_eq hp
        (fun i : {i // k i ≠ 0} ↦ k i) (fun i ↦ hθ i) (fun i ↦ hη (σ i))
        fun m hm ↦ (hprod m hm).mpr (h m hm)
      exact ⟨D.trans (g.trans G.symm)⟩
  constructor
  · intro hf
    -- The carrier of `oddCyclic (p ^ k) _ θ` is `ZMod (p ^ k)` by definition, so an isometry is in
    -- particular an additive equivalence of products of cyclic groups. After deleting the trivial
    -- summands, its exponents agree up to reindexing.
    obtain ⟨σ, hσ⟩ := ZMod.exists_equiv_exponents_of_pi_pow_addEquiv (Fact.out : p.Prime).one_lt
      (fun i : {i // k i ≠ 0} ↦ k i) (fun j : {j // l j ≠ 0} ↦ l j)
      (fun i ↦ Nat.pos_of_ne_zero i.2) (fun j ↦ Nat.pos_of_ne_zero j.2)
      ((isometryPiOddCyclicNeZero hp k θ).symm.trans
        (hf.some.trans (isometryPiOddCyclicNeZero hp l η))).toLinearEquiv.toAddEquiv
    have hcard (m : ℕ) (hm : 0 < m) : #{i | k i = m} = #{j | l j = m} := by
      rw [← occCount_eq_card_filter, ← occCount_eq_card_filter, ← occCount_subtype_ne k hm.ne',
        ← occCount_subtype_ne l hm.ne', occCount_def, occCount_def]
      exact Nat.card_congr (σ.subtypeEquiv fun i ↦ by rw [hσ i])
    exact fun m hm ↦ ⟨hcard m hm, (key hcard).mp hf m hm⟩
  · intro h
    exact (key fun m hm ↦ (h m hm).1).mpr fun m hm ↦ (h m hm).2

end TauCeti.FiniteQuadraticModule
