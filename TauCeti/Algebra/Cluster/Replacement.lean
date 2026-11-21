/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Subring.Basic
public import TauCeti.Algebra.Polynomial.DivX

import Mathlib.Algebra.Ring.Action.ConjAct
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import TauCeti.Algebra.Polynomial.Eval.Mem

/-!
# Finite polynomial replacement

Let `D` be a ring, `C` a subring, and `x`, `z` units of `D`. Suppose that an exchange in the
`z`-direction and its mutated exchange have the form
```
z* · z  = n₀ + Σ_a x^{n_a} c_a,
z** · z = (x*)^N m₀ + Σ_a (x*)^{N - n_a} d_a,
```
over a finite index set, with `n_a ≤ N`, `φ n₀ = m₀` for some `φ ∈ D`, and
`d_a = g_a x^{-n_a} φ x^{n_a} c_a`. The *replacement correction*
```
Σ_a (x*)^{N - n_a} ((x*)^{n_a} x^{n_a} - g_a) x^{-n_a} φ x^{n_a} c_a z⁻¹
```
expresses the mutated coordinate through the old one:
`z** = (x*)^N φ z* - correction` (`eq_pow_mul_mul_sub_replacementCorrection`). This identity
needs no subring. For membership, suppose moreover that `φ` and the `c_a` lie in `C`, that
`x⁻¹ C x ⊆ C` and `z C z⁻¹ ⊆ C`, and that each defect `(x*)^{n_a} x^{n_a} - g_a` lies in
`z C[z]`; then `z**` lies in the subring `C⟨x*, z*, z⟩` (`mem_closure_of_replacement`). The
identity specializes to the scalar case of an empty index set and to the singleton case
(`eq_pow_mul_mul_of_scalar_exchange`, `eq_pow_mul_mul_sub_of_singleton_exchange`); the
correction is invariant under reindexing and under insertion or removal of terms with zero
coefficient.

In a division ring the units are the nonzero elements, so the statements apply to nonzero
`x`, `z`; this is the algebraic replacement step for two interacting exchange directions in a
division ring. The singleton case with `n_a = N` is the binary replacement of
Berenstein–Fomin–Zelevinsky (classical) and of Berenstein–Zelevinsky (quantum).
For a commutative ring, `sum_mul_inv_mem_of_polynomial_exchange` applies the replacement to two
polynomial exchanges `x z = P(y)`, `y w = Q(x)` with `x`, `y` units: the defects are `y` times
the values of the quotients `(P ^ a).divX = (P(T)^a - P(0)^a) / T`, and for every
`e ≥ Q.natDegree` the element `(Σ_a Q_a P(0)^a z^{e-a}) / y` lies in every subring containing
the coefficients, `y`, `z` and `w`.

## References

* A. Berenstein, S. Fomin and A. Zelevinsky, *Cluster algebras III: Upper bounds and double
  Bruhat cells*, Duke Math. J. 126 (2005), Lemma 4.6.
* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Adv. Math. 195 (2005),
  Lemma 5.8.
-/

public section

open Finset Polynomial

namespace TauCeti

variable {D ι κ : Type*} [Ring D]

/-- The correction term of finite polynomial replacement,
`Σ_{a ∈ s} (x*)^{N - n_a} ((x*)^{n_a} x^{n_a} - g_a) x^{-n_a} φ x^{n_a} c_a z⁻¹`, for exponents
`n`, coefficients `c`, constant terms `g`, a bound `N`, an element `x* = xs`, a scalar `φ` and
units `x`, `z`. -/
def replacementCorrection (s : Finset ι) (n : ι → ℕ) (c g : ι → D) (N : ℕ) (xs φ : D)
    (x z : Dˣ) : D :=
  ∑ a ∈ s, xs ^ (N - n a) * (xs ^ n a * (x : D) ^ n a - g a) *
    (((x ^ n a)⁻¹ : Dˣ) * φ * (x : D) ^ n a) * c a * ((z⁻¹ : Dˣ) : D)

section Correction

variable (s : Finset ι) (n : ι → ℕ) (c g : ι → D) (N : ℕ) (xs φ : D) (x z : Dˣ)

theorem replacementCorrection_def :
    replacementCorrection s n c g N xs φ x z =
      ∑ a ∈ s, xs ^ (N - n a) * (xs ^ n a * (x : D) ^ n a - g a) *
        (((x ^ n a)⁻¹ : Dˣ) * φ * (x : D) ^ n a) * c a * ((z⁻¹ : Dˣ) : D) := (rfl)

@[simp]
theorem replacementCorrection_empty : replacementCorrection ∅ n c g N xs φ x z = 0 := by
  simp [replacementCorrection_def]

@[simp]
theorem replacementCorrection_singleton (a : ι) :
    replacementCorrection {a} n c g N xs φ x z =
      xs ^ (N - n a) * (xs ^ n a * (x : D) ^ n a - g a) *
        (((x ^ n a)⁻¹ : Dˣ) * φ * (x : D) ^ n a) * c a * ((z⁻¹ : Dˣ) : D) := by
  simp [replacementCorrection_def]

/-- Inserting an index whose exchange coefficient vanishes does not change the correction. -/
@[simp]
theorem replacementCorrection_insert_of_eq_zero [DecidableEq ι] {a : ι} (ha : c a = 0) :
    replacementCorrection (insert a s) n c g N xs φ x z =
      replacementCorrection s n c g N xs φ x z := by
  simp only [replacementCorrection_def]
  exact sum_insert_of_eq_zero_if_notMem fun _ ↦ by simp [ha]

/-- Removing an index whose exchange coefficient vanishes does not change the correction. -/
@[simp]
theorem replacementCorrection_erase_of_eq_zero [DecidableEq ι] {a : ι} (ha : c a = 0) :
    replacementCorrection (s.erase a) n c g N xs φ x z =
      replacementCorrection s n c g N xs φ x z := by
  simp only [replacementCorrection_def]
  exact sum_erase s (by simp [ha])

/-- Only the indices with nonzero exchange coefficient contribute to the correction. -/
@[simp]
theorem replacementCorrection_filter_ne_zero [DecidablePred fun a ↦ c a ≠ 0] :
    replacementCorrection (s.filter fun a ↦ c a ≠ 0) n c g N xs φ x z =
      replacementCorrection s n c g N xs φ x z := by
  simp only [replacementCorrection_def]
  exact sum_filter_of_ne fun a _ h hc ↦ h (by simp [hc])

/-- The correction depends only on the exponents, coefficients and constant terms at the indices
of `s`. -/
theorem replacementCorrection_congr {n n' : ι → ℕ} {c c' g g' : ι → D}
    (hn : ∀ a ∈ s, n a = n' a) (hc : ∀ a ∈ s, c a = c' a) (hg : ∀ a ∈ s, g a = g' a) :
    replacementCorrection s n c g N xs φ x z = replacementCorrection s n' c' g' N xs φ x z := by
  simp only [replacementCorrection_def]
  exact sum_congr rfl fun a ha ↦ by rw [hn a ha, hc a ha, hg a ha]

/-- Reindexing the correction along an embedding of index types. -/
@[simp]
theorem replacementCorrection_map (e : ι ↪ κ) (s : Finset ι) (n : κ → ℕ) (c g : κ → D) :
    replacementCorrection (s.map e) n c g N xs φ x z =
      replacementCorrection s (n ∘ e) (c ∘ e) (g ∘ e) N xs φ x z := by
  simp [replacementCorrection_def]

end Correction

section Identity

variable {s : Finset ι} {n : ι → ℕ} {c d g : ι → D} {N : ℕ} {xs zs zss φ n₀ m₀ : D}
  {x z : Dˣ}

/-- **Finite polynomial replacement.** If `z* z = n₀ + Σ_a x^{n_a} c_a` and
`z** z = (x*)^N m₀ + Σ_a (x*)^{N - n_a} d_a`, with `n_a ≤ N`, `φ n₀ = m₀` and
`d_a = g_a x^{-n_a} φ x^{n_a} c_a`, then `z** = (x*)^N φ z*` minus the replacement correction. -/
theorem eq_pow_mul_mul_sub_replacementCorrection (hn : ∀ a ∈ s, n a ≤ N) (hφ : φ * n₀ = m₀)
    (hzs : zs * z = n₀ + ∑ a ∈ s, (x : D) ^ n a * c a)
    (hzss : zss * z = xs ^ N * m₀ + ∑ a ∈ s, xs ^ (N - n a) * d a)
    (hd : ∀ a ∈ s, d a = g a * (((x ^ n a)⁻¹ : Dˣ) * φ * (x : D) ^ n a) * c a) :
    zss = xs ^ N * φ * zs - replacementCorrection s n c g N xs φ x z := by
  refine (Units.mul_left_inj z).mp ?_
  -- Each summand: `(x*)^N φ x^{n_a} c_a` minus the correction summand is `(x*)^{N - n_a} d_a`.
  have hterm : ∀ a ∈ s, xs ^ N * φ * ((x : D) ^ n a * c a) -
      xs ^ (N - n a) * (xs ^ n a * (x : D) ^ n a - g a) *
        (((x ^ n a)⁻¹ : Dˣ) * φ * (x : D) ^ n a) * c a = xs ^ (N - n a) * d a := by
    intro a ha
    set u := (((x ^ n a)⁻¹ : Dˣ) : D) * φ * (x : D) ^ n a with hu
    have hN : xs ^ N = xs ^ (N - n a) * xs ^ n a := by
      rw [← pow_add, Nat.sub_add_cancel (hn a ha)]
    -- The unit cancellation `x^{n_a} x^{-n_a} = 1` gives `φ x^{n_a} = x^{n_a} u`.
    have hφx : φ * (x : D) ^ n a = (x : D) ^ n a * u := by
      rw [hu, ← mul_assoc, ← mul_assoc, ← Units.val_pow_eq_pow_val, Units.mul_inv, one_mul]
    rw [hd a ha, hN]
    calc xs ^ (N - n a) * xs ^ n a * φ * ((x : D) ^ n a * c a) -
          xs ^ (N - n a) * (xs ^ n a * (x : D) ^ n a - g a) * u * c a
        = xs ^ (N - n a) * xs ^ n a * (φ * (x : D) ^ n a - (x : D) ^ n a * u) * c a +
            xs ^ (N - n a) * (g a * u * c a) := by noncomm_ring
      _ = xs ^ (N - n a) * (g a * u * c a) := by rw [hφx, sub_self, mul_zero, zero_mul, zero_add]
  have hcorr : replacementCorrection s n c g N xs φ x z * z =
      ∑ a ∈ s, xs ^ (N - n a) * (xs ^ n a * (x : D) ^ n a - g a) *
        (((x ^ n a)⁻¹ : Dˣ) * φ * (x : D) ^ n a) * c a := by
    simp only [replacementCorrection_def, sum_mul, Units.inv_mul_cancel_right]
  calc zss * z = xs ^ N * m₀ + ∑ a ∈ s, xs ^ (N - n a) * d a := hzss
    _ = xs ^ N * φ * n₀ + ∑ a ∈ s, (xs ^ N * φ * ((x : D) ^ n a * c a) -
          xs ^ (N - n a) * (xs ^ n a * (x : D) ^ n a - g a) *
            (((x ^ n a)⁻¹ : Dˣ) * φ * (x : D) ^ n a) * c a) := by
      rw [sum_congr rfl hterm, mul_assoc, hφ]
    _ = xs ^ N * φ * (n₀ + ∑ a ∈ s, (x : D) ^ n a * c a) -
          ∑ a ∈ s, xs ^ (N - n a) * (xs ^ n a * (x : D) ^ n a - g a) *
            (((x ^ n a)⁻¹ : Dˣ) * φ * (x : D) ^ n a) * c a := by
      rw [sum_sub_distrib, mul_add, mul_sum, add_sub_assoc]
    _ = (xs ^ N * φ * zs - replacementCorrection s n c g N xs φ x z) * z := by
      rw [sub_mul, hcorr, mul_assoc _ zs, hzs]

/-- **Scalar replacement**, the case of an empty index set: if `z* z = n₀`, `z** z = (x*)^N m₀`
and `φ n₀ = m₀`, then `z** = (x*)^N φ z*`. -/
theorem eq_pow_mul_mul_of_scalar_exchange (hφ : φ * n₀ = m₀) (hzs : zs * z = n₀)
    (hzss : zss * z = xs ^ N * m₀) : zss = xs ^ N * φ * zs := by
  simpa using eq_pow_mul_mul_sub_replacementCorrection (s := (∅ : Finset Empty)) (n := 0)
    (c := 0) (d := 0) (g := 0) (x := 1) (z := z) (by simp) hφ (by simpa using hzs)
    (by simpa using hzss) (by simp)

/-- **Singleton replacement**, the case of a one-term exchange: if `z* z = n₀ + x^r c`,
`z** z = (x*)^N m₀ + (x*)^{N - r} d`, `r ≤ N`, `φ n₀ = m₀` and `d = g x^{-r} φ x^r c`, then
`z** = (x*)^N φ z* - (x*)^{N - r} ((x*)^r x^r - g) x^{-r} φ x^r c z⁻¹`. -/
theorem eq_pow_mul_mul_sub_of_singleton_exchange {r : ℕ} {c' d' g' : D} (hr : r ≤ N)
    (hφ : φ * n₀ = m₀) (hzs : zs * z = n₀ + (x : D) ^ r * c')
    (hzss : zss * z = xs ^ N * m₀ + xs ^ (N - r) * d')
    (hd : d' = g' * (((x ^ r)⁻¹ : Dˣ) * φ * (x : D) ^ r) * c') :
    zss = xs ^ N * φ * zs - xs ^ (N - r) * (xs ^ r * (x : D) ^ r - g') *
      (((x ^ r)⁻¹ : Dˣ) * φ * (x : D) ^ r) * c' * ((z⁻¹ : Dˣ) : D) := by
  simpa using eq_pow_mul_mul_sub_replacementCorrection (s := {()}) (n := fun _ ↦ r)
    (c := fun _ ↦ c') (d := fun _ ↦ d') (g := fun _ ↦ g') (by simpa using hr) hφ
    (by simpa using hzs) (by simpa using hzss) (by simpa using hd)

end Identity

section Membership

variable {s : Finset ι} {n : ι → ℕ} {c d g : ι → D} {N : ℕ} {xs zs zss φ n₀ m₀ : D}
  {x z : Dˣ} {C : Subring D}

/-- **Finite polynomial replacement, membership.** Under the hypotheses of
`eq_pow_mul_mul_sub_replacementCorrection`, suppose that `φ` and the exchange coefficients `c_a`
lie in a subring `C` with `x⁻¹ C x ⊆ C` and `z C z⁻¹ ⊆ C`, and that each defect
`(x*)^{n_a} x^{n_a} - g_a` lies in `z C[z]`. Then `z**` lies in `C⟨x*, z*, z⟩`. -/
theorem mem_closure_of_replacement (hxC : ∀ c ∈ C, ((x⁻¹ : Dˣ) : D) * c * x ∈ C)
    (hzC : ∀ c ∈ C, (z : D) * c * ((z⁻¹ : Dˣ) : D) ∈ C) (hφC : φ ∈ C) (hc : ∀ a ∈ s, c a ∈ C)
    (hg : ∀ a ∈ s, ∃ p ∈ Subring.closure (insert (z : D) (C : Set D)),
      xs ^ n a * (x : D) ^ n a - g a = z * p)
    (hn : ∀ a ∈ s, n a ≤ N) (hφ : φ * n₀ = m₀)
    (hzs : zs * z = n₀ + ∑ a ∈ s, (x : D) ^ n a * c a)
    (hzss : zss * z = xs ^ N * m₀ + ∑ a ∈ s, xs ^ (N - n a) * d a)
    (hd : ∀ a ∈ s, d a = g a * (((x ^ n a)⁻¹ : Dˣ) * φ * (x : D) ^ n a) * c a) :
    zss ∈ Subring.closure (insert xs (insert zs (insert (z : D) (C : Set D)))) := by
  set Cz := Subring.closure (insert (z : D) (C : Set D))
  set H := Subring.closure (insert xs (insert zs (insert (z : D) (C : Set D))))
  -- Conjugation by `z` is a ring endomorphism of `D` mapping `C[z]` into itself.
  let f : D →+* D := MulSemiringAction.toRingHom (ConjAct Dˣ) D (ConjAct.toConjAct z)
  have hf (q : D) : f q = (z : D) * q * ((z⁻¹ : Dˣ) : D) := by
    simp [f, ConjAct.units_smul_def]
  have hfCz : Cz ≤ Cz.comap f := by
    refine Subring.closure_le.mpr ?_
    rintro q (rfl | hq)
    · rw [SetLike.mem_coe, Subring.mem_comap, hf, Units.mul_inv_cancel_right]
      exact Subring.subset_closure (Set.mem_insert _ _)
    · rw [SetLike.mem_coe, Subring.mem_comap, hf]
      exact Subring.subset_closure (Set.mem_insert_of_mem _ (hzC q hq))
  -- Conjugation by `x^{-m}` maps `C` into itself, as the `m`-th iterate of conjugation by `x⁻¹`.
  have hxpow (m : ℕ) (c : D) (hc : c ∈ C) : (((x ^ m)⁻¹ : Dˣ) : D) * c * (x : D) ^ m ∈ C := by
    have hmaps : Set.MapsTo (ConjAct.toConjAct x⁻¹ • · : D → D) C C := fun c hc ↦ by
      simpa [ConjAct.units_smul_def] using hxC c hc
    have h := hmaps.iterate m hc
    rwa [smul_iterate_apply, ← map_pow, inv_pow, ConjAct.units_smul_def,
      ConjAct.ofConjAct_toConjAct, inv_inv, Units.val_pow_eq_pow_val] at h
  have hCz : Cz ≤ H :=
    Subring.closure_mono fun _ h ↦ Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ h)
  have hC : (C : Set D) ⊆ H := fun _ h ↦ hCz (Subring.subset_closure (Set.mem_insert_of_mem _ h))
  have hxs : xs ∈ H := Subring.subset_closure (Set.mem_insert _ _)
  have hzs' : zs ∈ H := Subring.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  rw [eq_pow_mul_mul_sub_replacementCorrection hn hφ hzs hzss hd, replacementCorrection_def]
  refine H.sub_mem (H.mul_mem (H.mul_mem (H.pow_mem hxs _) (hC hφC)) hzs') (H.sum_mem ?_)
  intro a ha
  obtain ⟨p, hp, hpg⟩ := hg a ha
  have hq := C.mul_mem (hxpow (n a) φ hφC) (hc a ha)
  have hzp := hfCz (Cz.mul_mem hp (Subring.subset_closure (Set.mem_insert_of_mem _ hq)))
  rw [Subring.mem_comap, hf] at hzp
  have hmem : xs ^ (N - n a) * ((z : D) * (p * ((((x ^ n a)⁻¹ : Dˣ) * φ * (x : D) ^ n a) *
      c a)) * ((z⁻¹ : Dˣ) : D)) ∈ H := H.mul_mem (H.pow_mem hxs _) (hCz hzp)
  rw [hpg]
  simpa only [mul_assoc] using hmem

end Membership

section Polynomial

variable {R F : Type*} [Semiring R] [CommRing F]

/-- **Replacement for two polynomial exchanges.** Let `f : R →+* F` and let `x`, `y` be units of
the commutative ring `F` with polynomial exchanges `x z = P_f(y)` and `y w = Q_f(x)`. For every
`e` with `Q.natDegree ≤ e`, the quotient `(Σ_a f(Q_a) f(P(0))^a z^{e-a}) / y` lies in every
subring of `F` containing `f(R)`, `y`, `z` and `w`. -/
theorem sum_mul_inv_mem_of_polynomial_exchange (f : R →+* F) {P Q : R[X]} {e : ℕ}
    (he : Q.natDegree ≤ e) {x y : Fˣ} {z w : F} (hxz : x * z = P.eval₂ f y)
    (hyw : y * w = Q.eval₂ f x) {H : Subring F} (hf : Set.range f ⊆ H) (hy : (y : F) ∈ H)
    (hz : z ∈ H) (hw : w ∈ H) :
    (∑ a ∈ Q.support, f (Q.coeff a) * f (P.coeff 0) ^ a * z ^ (e - a)) * ((y⁻¹ : Fˣ) : F) ∈
      H := by
  have hmem := mem_closure_of_replacement (C := Subring.closure (Set.range f)) (s := Q.support)
    (n := id)
    (c := fun a ↦ f (Q.coeff a)) (d := fun a ↦ f (P.coeff 0) ^ a * f (Q.coeff a))
    (g := fun a ↦ f (P.coeff 0) ^ a) (N := e) (xs := z) (zs := w)
    (zss := (∑ a ∈ Q.support, f (Q.coeff a) * f (P.coeff 0) ^ a * z ^ (e - a)) *
      ((y⁻¹ : Fˣ) : F)) (φ := 1) (n₀ := 0) (m₀ := 0) (x := x) (z := y)
    (fun c hc ↦ by rwa [mul_comm _ c, Units.inv_mul_cancel_right])
    (fun c hc ↦ by rwa [mul_comm _ c, Units.mul_inv_cancel_right]) (one_mem _)
    (fun a _ ↦ Subring.subset_closure ⟨_, rfl⟩) ?_
    (fun a ha ↦ (le_natDegree_of_mem_supp a ha).trans he) (mul_zero _) ?_ ?_ ?_
  · refine Subring.closure_le.mpr ?_ hmem
    rintro q (rfl | rfl | rfl | hq)
    exacts [hz, hw, hy, Subring.closure_le.mpr hf hq]
  · intro a _
    refine ⟨((P ^ a).divX).eval₂ f y, eval₂_mem (fun i _ ↦ Subring.subset_closure
      (Set.mem_insert_of_mem _ (Subring.subset_closure (Set.mem_range_self _))))
      (Subring.subset_closure (Set.mem_insert _ _)), ?_⟩
    -- Evaluate `P ^ a = divX (P ^ a) * X + C (P(0) ^ a)` at `y`, where `P(y) = x z`.
    have h := eval₂_divX_mul_add f (y : F) (P ^ a)
    rw [← constantCoeff_apply, map_pow, constantCoeff_apply, eval₂_pow, ← hxz, map_pow] at h
    rw [id_eq]
    linear_combination -h
  · rw [mul_comm w, hyw, eval₂_eq_sum, Polynomial.sum_def]
    simp [mul_comm]
  · simp only [mul_assoc, Units.inv_mul, mul_one, mul_zero, zero_add, id_eq]
    exact sum_congr rfl fun a _ ↦ by ring
  · intro a _
    have hx : (((x ^ a)⁻¹ : Fˣ) : F) * 1 * (x : F) ^ a = 1 := by
      rw [mul_one, ← Units.val_pow_eq_pow_val, Units.inv_mul]
    rw [id_eq, hx, mul_one, mul_comm]

end Polynomial

end TauCeti
