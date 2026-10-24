/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Thom.Basic
public import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Preorder.Finite

/-!
# Thom encodings of the roots of a polynomial

A root of a nonzero polynomial over an ordered field with polynomial Rolle is determined by its
Thom encoding, the signs of its derivatives of orders `1, …, natDegree p`
(`Polynomial.thomEncoding_injOn`). This file turns that injectivity into an API for the finite
set of encodings realized by roots.

* `Polynomial.thomEncodings p` is the finite set of Thom encodings of the distinct roots of `p`.
  Its cardinality is the number of distinct roots (`Polynomial.card_thomEncodings`).
  Constant polynomials realize no encoding, and `-p`, `C c * p` with `c ≠ 0` and `p (a X + b)`
  with `a ≠ 0` realize the correspondingly negated or rescaled encodings of `p`
  (`Polynomial.thomEncodings_neg`, `Polynomial.thomEncodings_C_mul`,
  `Polynomial.thomEncodings_comp_C_mul_X_add_C`).
* `Polynomial.thomEncodingEquiv` identifies the distinct roots with their encodings, so that
  `(thomEncodingEquiv hrolle p).symm` reconstructs a root from its encoding
  (`Polynomial.existsUnique_eval_eq_zero_thomEncoding_eq` is the underlying uniqueness).
* `Polynomial.ThomLT` is the comparison of two sign words read off at the last coordinate where
  they differ. It is decidable and refers to no point of `R`. The order of two points with
  distinct encodings is this comparison of their encodings (`Polynomial.lt_iff_thomLT`), so the
  order of the roots of `p` is recovered from their encodings alone
  (`Polynomial.thomEncodingEquiv_lt_iff`). Negating both words preserves the comparison
  (`Polynomial.thomLT_neg_iff`), while the sign changes `(-1) ^ (i + 1)` produced by the
  reflection `X ↦ -X` reverse it (`Polynomial.thomLT_neg_one_pow_mul_iff`). Including the zeroth
  derivative compares any point with a root
  (`Polynomial.lt_iff_thomLT_cons_derivativeSign_of_eval_eq_zero_right`,
  `Polynomial.lt_iff_thomLT_cons_derivativeSign_of_eval_eq_zero_left`). The degree-bounded
  comparisons and `Polynomial.card_roots_lt_eq_card_filter_thomLT_of_natDegree_le` use sign words
  of a fixed length across specializations whose degrees may drop.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Proposition 2.28 (Thom encodings and the ordering of roots) and Chapter 10
(Thom encodings of real roots).
-/

public section

open TauCeti (PolynomialRolle)

namespace Polynomial

section Comparison

variable {d : ℕ}

/-- The Thom comparison of sign words: `ThomLT σ τ` holds when `σ` and `τ` first differ, reading
from the top, at coordinate `i`, the next coordinate `i + 1` exists, and either `σ (i + 1) = 1`
and `σ i < τ i`, or `σ (i + 1) = -1` and `τ i < σ i`. For Thom encodings of two points this
compares the points (`Polynomial.lt_iff_thomLT`). -/
def ThomLT (σ τ : Fin d → SignType) : Prop :=
  ∃ i : Fin d, σ i ≠ τ i ∧ (∀ j, i < j → σ j = τ j) ∧ ∃ h : i.val + 1 < d,
    (σ ⟨i.val + 1, h⟩ = 1 ∧ σ i < τ i) ∨ (σ ⟨i.val + 1, h⟩ = -1 ∧ τ i < σ i)

/-- `ThomLT`, unfolded. -/
theorem thomLT_iff {σ τ : Fin d → SignType} :
    ThomLT σ τ ↔ ∃ i : Fin d, σ i ≠ τ i ∧ (∀ j, i < j → σ j = τ j) ∧ ∃ h : i.val + 1 < d,
      (σ ⟨i.val + 1, h⟩ = 1 ∧ σ i < τ i) ∨ (σ ⟨i.val + 1, h⟩ = -1 ∧ τ i < σ i) :=
  Iff.rfl

instance : DecidableRel (ThomLT (d := d)) := fun _ _ ↦ decidable_of_iff _ thomLT_iff.symm

/-- At the last coordinate of disagreement, `ThomLT` is read off from the two differing signs and
the next coordinate. -/
theorem thomLT_iff_of_ne {σ τ : Fin d → SignType} {i : Fin d} (hi : σ i ≠ τ i)
    (ht : ∀ j, i < j → σ j = τ j) :
    ThomLT σ τ ↔ ∃ h : i.val + 1 < d,
      (σ ⟨i.val + 1, h⟩ = 1 ∧ σ i < τ i) ∨ (σ ⟨i.val + 1, h⟩ = -1 ∧ τ i < σ i) := by
  have hg {k : Fin d} (hk : σ k ≠ τ k) (ht : ∀ j, k < j → σ j = τ j) :
      IsGreatest {j | σ j ≠ τ j} k :=
    ⟨hk, fun j hj ↦ not_lt.1 fun h ↦ hj (ht j h)⟩
  constructor
  · rintro ⟨i', hi', ht', h⟩
    obtain rfl := (hg hi' ht').unique (hg hi ht)
    exact h
  · exact fun h ↦ ⟨i, hi, ht, h⟩

/-- Comparable words are distinct. -/
theorem ThomLT.ne {σ τ : Fin d → SignType} (h : ThomLT σ τ) : σ ≠ τ := by
  rintro rfl
  obtain ⟨i, hi, -⟩ := h
  exact hi rfl

/-- `ThomLT` is irreflexive. -/
theorem thomLT_irrefl (σ : Fin d → SignType) : ¬ThomLT σ σ := fun h ↦ h.ne rfl

/-- `ThomLT` is asymmetric on all words, realized or not. -/
theorem ThomLT.asymm {σ τ : Fin d → SignType} (h : ThomLT σ τ) : ¬ThomLT τ σ := by
  obtain ⟨i, hi, ht, hd, hστ⟩ := h
  rw [thomLT_iff_of_ne (Ne.symm hi) fun j hj ↦ (ht j hj).symm]
  rintro ⟨_, hτσ⟩
  rw [← ht _ (Fin.lt_def.2 (Nat.lt_succ_self i.val))] at hτσ
  rcases hστ with ⟨h1, hlt⟩ | ⟨h1, hlt⟩ <;> rcases hτσ with ⟨h2, hlt'⟩ | ⟨h2, hlt'⟩
  · exact lt_asymm hlt hlt'
  · rw [h1] at h2; cases h2
  · rw [h1] at h2; cases h2
  · exact lt_asymm hlt hlt'

/-- `ThomLT` is transitive on all words, realized or not. -/
theorem ThomLT.trans {σ τ υ : Fin d → SignType} (hστ : ThomLT σ τ) (hτυ : ThomLT τ υ) :
    ThomLT σ υ := by
  obtain ⟨i, hi, ht, hd, h⟩ := hστ
  obtain ⟨k, hk, hk', hd', h'⟩ := hτυ
  rcases lt_trichotomy i k with hik | rfl | hik
  · have hsucc : i < ⟨k.val + 1, hd'⟩ := Fin.lt_def.2 (Nat.lt_succ_of_lt hik)
    refine ⟨k, ht k hik ▸ hk, fun j hj ↦ (ht j (hik.trans hj)).trans (hk' j hj), hd', ?_⟩
    rwa [ht k hik, ht _ hsucc]
  · have htail : ∀ j, i < j → σ j = υ j := fun j hj ↦ (ht j hj).trans (hk' j hj)
    rw [← ht _ (Fin.lt_def.2 (Nat.lt_succ_self i.val))] at h'
    rcases h with ⟨h1, hlt⟩ | ⟨h1, hlt⟩ <;> rcases h' with ⟨h2, hlt'⟩ | ⟨h2, hlt'⟩
    · exact ⟨i, (hlt.trans hlt').ne, htail, hd, Or.inl ⟨h1, hlt.trans hlt'⟩⟩
    · rw [h1] at h2; cases h2
    · rw [h1] at h2; cases h2
    · exact ⟨i, (hlt'.trans hlt).ne', htail, hd, Or.inr ⟨h1, hlt'.trans hlt⟩⟩
  · have hsucc : k < ⟨i.val + 1, hd⟩ := Fin.lt_def.2 (Nat.lt_succ_of_lt hik)
    refine ⟨i, hk' i hik ▸ hi, fun j hj ↦ (ht j hj).trans (hk' j (hik.trans hj)), hd, ?_⟩
    rwa [← hk' i hik]

private theorem thomLT_cmp_neg (s a b : SignType) :
    (-s = 1 ∧ -a < -b) ∨ (-s = -1 ∧ -b < -a) ↔ (s = 1 ∧ a < b) ∨ (s = -1 ∧ b < a) := by
  revert s a b
  decide

/-- Negating both sign words preserves the Thom comparison. This is the comparison counterpart of
`Polynomial.thomEncoding_neg`: `p` and `-p` have the same roots, in the same order. -/
@[simp]
theorem thomLT_neg_iff {σ τ : Fin d → SignType} : ThomLT (-σ) (-τ) ↔ ThomLT σ τ := by
  simp only [thomLT_iff, Pi.neg_apply, thomLT_cmp_neg]
  simp only [ne_eq, neg_inj]

private theorem thomLT_cmp_mul {e : SignType} (he : e = 1 ∨ e = -1) (s a b : SignType) :
    (-e * s = 1 ∧ e * a < e * b) ∨ (-e * s = -1 ∧ e * b < e * a) ↔
      (s = 1 ∧ b < a) ∨ (s = -1 ∧ a < b) := by
  rcases he with rfl | rfl <;> revert s a b <;> decide

/-- Multiplying coordinate `i` of both sign words by `(-1) ^ (i + 1)` reverses the Thom
comparison. This is the comparison counterpart of the reflection `X ↦ -X`, under which the
derivative of order `i + 1` changes sign by `(-1) ^ (i + 1)`
(`Polynomial.thomEncoding_comp_C_mul_X_add_C`) and the order of the roots is reversed. -/
theorem thomLT_neg_one_pow_mul_iff {σ τ : Fin d → SignType} :
    ThomLT (fun i ↦ (-1) ^ (i.val + 1) * σ i) (fun i ↦ (-1) ^ (i.val + 1) * τ i) ↔
      ThomLT τ σ := by
  have hinj (n : ℕ) (a b : SignType) : (-1) ^ n * a = (-1) ^ n * b ↔ a = b :=
    (isUnit_neg_one.pow n).mul_right_inj
  simp only [thomLT_iff, ne_eq, hinj]
  refine exists_congr fun i ↦ ?_
  rw [eq_comm (a := τ i)]
  refine and_congr_right fun _ ↦ ⟨?_, ?_⟩ <;> rintro ⟨ht, h, hc⟩ <;>
    refine ⟨fun j hj ↦ (ht j hj).symm, h, ?_⟩
  · rwa [pow_succ, mul_neg_one, ht _ (Fin.lt_def.2 (Nat.lt_succ_self i.val)),
      thomLT_cmp_mul (neg_one_pow_eq_or SignType _)] at hc
  · rwa [pow_succ, mul_neg_one, ← ht _ (Fin.lt_def.2 (Nat.lt_succ_self i.val)),
      thomLT_cmp_mul (neg_one_pow_eq_or SignType _)]

end Comparison

section Realized

variable {R : Type*} [CommRing R] [IsDomain R] [LinearOrder R]

/-- The finite set of Thom encodings of the distinct roots of `p`. The zero polynomial has no
roots in `Polynomial.roots`, so it realizes no encoding. -/
noncomputable def thomEncodings (p : R[X]) : Finset (Fin p.natDegree → SignType) :=
  p.roots.toFinset.image (thomEncoding p)

/-- The realized Thom encodings are the images of the distinct roots under `thomEncoding`. -/
theorem thomEncodings_def (p : R[X]) : p.thomEncodings = p.roots.toFinset.image (thomEncoding p) :=
  (rfl)

/-- A word is a realized Thom encoding exactly when `p` is nonzero and some root of `p` has it as
its encoding. -/
@[simp]
theorem mem_thomEncodings {p : R[X]} {σ : Fin p.natDegree → SignType} :
    σ ∈ p.thomEncodings ↔ p ≠ 0 ∧ ∃ x, p.eval x = 0 ∧ thomEncoding p x = σ := by
  simp only [thomEncodings, Finset.mem_image, Multiset.mem_toFinset, mem_roots', IsRoot.def]
  constructor
  · rintro ⟨x, ⟨hp, hx⟩, rfl⟩
    exact ⟨hp, x, hx, rfl⟩
  · rintro ⟨hp, x, hx, rfl⟩
    exact ⟨x, ⟨hp, hx⟩, rfl⟩

/-- The Thom encoding of a root of a nonzero polynomial is realized. -/
theorem thomEncoding_mem_thomEncodings {p : R[X]} (hp : p ≠ 0) {x : R} (hx : p.eval x = 0) :
    thomEncoding p x ∈ p.thomEncodings :=
  mem_thomEncodings.2 ⟨hp, x, hx, rfl⟩

/-- The zero polynomial realizes no Thom encoding. -/
@[simp]
theorem thomEncodings_zero : (0 : R[X]).thomEncodings = ∅ := by
  rw [thomEncodings, roots_zero, Multiset.toFinset_zero]
  exact Finset.image_empty _

/-- A constant polynomial realizes no Thom encoding: it is zero or has no roots. -/
@[simp]
theorem thomEncodings_C (c : R) : (C c).thomEncodings = ∅ := by
  simp [thomEncodings_def]

end Realized

/-- The realized Thom encodings of `-p` are the negations of those of `p`. -/
theorem thomEncodings_neg {R : Type*} [CommRing R] [IsDomain R] [LinearOrder R] [IsOrderedRing R]
    (p : R[X]) :
    (-p).thomEncodings = p.thomEncodings.image fun σ ↦ -(σ ∘ Fin.cast (natDegree_neg p)) := by
  rw [thomEncodings_def, thomEncodings_def, roots_neg, Finset.image_image]
  exact Finset.image_congr fun x _ ↦ thomEncoding_neg p x

/-- The realized Thom encodings of `C c * p`, for `c ≠ 0`, are those of `p` multiplied by
`sign c`. -/
theorem thomEncodings_C_mul {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {c : R} (hc : c ≠ 0) (p : R[X]) :
    (C c * p).thomEncodings =
      p.thomEncodings.image fun σ i ↦ SignType.sign c * σ (Fin.cast (natDegree_C_mul hc) i) := by
  rw [thomEncodings_def, thomEncodings_def, roots_C_mul p hc, Finset.image_image]
  exact Finset.image_congr fun x _ ↦ thomEncoding_C_mul hc p x

/-- **Affine change of variable.** For a unit `a`, the realized Thom encodings of `p (a X + b)`
are those of `p` with coordinate `i` multiplied by `sign a ^ (i + 1)`. The root `a⁻¹ (x - b)` of
`p (a X + b)` corresponds to the root `x` of `p`. -/
theorem thomEncodings_comp_C_mul_X_add_C {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {a : R} (ha : IsUnit a) (b : R) (p : R[X]) :
    (p.comp (C a * X + C b)).thomEncodings = p.thomEncodings.image fun σ i ↦
      SignType.sign a ^ (i.val + 1) *
        σ (Fin.cast (natDegree_comp_C_mul_X_add_C ha.ne_zero b p) i) := by
  classical
  rw [thomEncodings_def, thomEncodings_def, roots_comp_C_mul_X_add_C p a b ha,
    Multiset.toFinset_map, Finset.image_image, Finset.image_image]
  refine Finset.image_congr fun x _ ↦ ?_
  simp only [Function.comp_apply, thomEncoding_comp_C_mul_X_add_C ha.ne_zero, ← mul_assoc,
    Ring.mul_inverse_cancel a ha, one_mul, sub_add_cancel]

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Distinct roots of `p` have distinct Thom encodings, so there are exactly as many realized
encodings as distinct roots. -/
theorem card_thomEncodings (hrolle : PolynomialRolle R) (p : R[X]) :
    p.thomEncodings.card = p.roots.toFinset.card := by
  by_cases hp : p = 0
  · subst hp
    rw [thomEncodings_zero, roots_zero, Multiset.toFinset_zero, Finset.card_empty,
      Finset.card_empty]
  refine Finset.card_image_of_injOn fun a ha b hb h ↦ ?_
  simp only [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hp, IsRoot.def] at ha hb
  exact thomEncoding_injOn p hrolle hp ha hb h

/-- **Reconstruction.** A realized Thom encoding is the encoding of exactly one root. -/
theorem existsUnique_eval_eq_zero_thomEncoding_eq (hrolle : PolynomialRolle R) {p : R[X]}
    {σ : Fin p.natDegree → SignType} (hσ : σ ∈ p.thomEncodings) :
    ∃! x, p.eval x = 0 ∧ thomEncoding p x = σ := by
  obtain ⟨hp, x, hx, rfl⟩ := mem_thomEncodings.1 hσ
  exact ⟨x, ⟨hx, rfl⟩, fun y hy ↦ thomEncoding_injOn p hrolle hp hy.1 hx hy.2⟩

/-- The distinct roots of `p` correspond to their Thom encodings. The inverse reconstructs a root
from its encoding. -/
noncomputable def thomEncodingEquiv (hrolle : PolynomialRolle R) (p : R[X]) :
    p.roots.toFinset ≃ p.thomEncodings :=
  Equiv.ofBijective
    (fun x ↦ ⟨thomEncoding p x, Finset.mem_image_of_mem _ x.2⟩)
    ⟨fun a b h ↦ by
      have hp : p ≠ 0 := ne_zero_of_mem_roots (Multiset.mem_toFinset.mp a.2)
      have ha := a.2
      have hb := b.2
      simp only [Multiset.mem_toFinset, mem_roots hp, IsRoot.def] at ha hb
      exact Subtype.ext (thomEncoding_injOn p hrolle hp ha hb (congrArg Subtype.val h)),
    fun σ ↦ by
      obtain ⟨x, hx, h⟩ := Finset.mem_image.1 σ.2
      exact ⟨⟨x, hx⟩, Subtype.ext h⟩⟩

/-- The correspondence sends a root to its Thom encoding. -/
@[simp]
theorem coe_thomEncodingEquiv_apply (hrolle : PolynomialRolle R) (p : R[X])
    (x : p.roots.toFinset) : (thomEncodingEquiv hrolle p x : Fin p.natDegree → SignType) =
      thomEncoding p x :=
  (rfl)

/-- The reconstructed point is a root. -/
@[simp]
theorem eval_thomEncodingEquiv_symm (hrolle : PolynomialRolle R) (p : R[X])
    (σ : p.thomEncodings) : p.eval ((thomEncodingEquiv hrolle p).symm σ : R) = 0 := by
  have h := ((thomEncodingEquiv hrolle p).symm σ).2
  have hp : p ≠ 0 := ne_zero_of_mem_roots (Multiset.mem_toFinset.mp h)
  simpa only [Multiset.mem_toFinset, mem_roots hp, IsRoot.def] using h

/-- The reconstructed root has the prescribed Thom encoding. -/
@[simp]
theorem thomEncoding_thomEncodingEquiv_symm (hrolle : PolynomialRolle R) (p : R[X])
    (σ : p.thomEncodings) :
    thomEncoding p ((thomEncodingEquiv hrolle p).symm σ : R) = σ := by
  simpa only [coe_thomEncodingEquiv_apply] using
    congrArg Subtype.val ((thomEncodingEquiv hrolle p).apply_symm_apply σ)

/-- **Extended comparison.** Any two points whose derivative signs of orders `0, …, d`
(with `p.natDegree ≤ d`) differ are ordered as those sign words are by `ThomLT`. -/
theorem lt_iff_thomLT_derivativeSign_of_natDegree_le {p : R[X]} {d : ℕ} (hd : p.natDegree ≤ d)
    (hrolle : PolynomialRolle R) {a b : R}
    (hne : (fun i : Fin (d + 1) => derivativeSign p a i.val) ≠
      fun i => derivativeSign p b i.val) :
    a < b ↔ ThomLT (fun i : Fin (d + 1) => derivativeSign p a i.val)
      (fun i => derivativeSign p b i.val) := by
  obtain ⟨i, hi, hmax⟩ := (Set.toFinite {i : Fin (d + 1) |
    derivativeSign p a i.val ≠ derivativeSign p b i.val}).exists_maximal
      (Function.ne_iff.mp hne)
  have ht (j : Fin (d + 1)) (hij : i < j) :
      derivativeSign p a j.val = derivativeSign p b j.val := by
    by_contra hne'
    exact hij.not_ge (hmax hne' hij.le)
  rw [thomLT_iff_of_ne hi ht]
  have hdeg : i.val + 1 < d + 1 := by
    by_contra h
    exact hi (derivativeSign_const p a b (by omega))
  have htail (k : ℕ) (hk : i.val < k) : derivativeSign p a k = derivativeSign p b k := by
    exact TauCeti.derivativeSign_eq_of_forall_le (n := i.val + 1) hd
      (fun j hj hjd => ht ⟨j, by omega⟩ hj) hk
  rw [lt_iff_derivativeSign p hrolle hi htail]
  exact ⟨fun h => ⟨hdeg, h⟩, fun ⟨_, h⟩ => h⟩

/-- Any two points whose derivative signs of orders `1, …, d` (with `p.natDegree ≤ d`) differ are
ordered as those sign words are by `ThomLT`. -/
theorem lt_iff_thomLT_derivativeSign_succ_of_natDegree_le {p : R[X]} {d : ℕ}
    (hd : p.natDegree ≤ d) (hrolle : PolynomialRolle R) {a b : R}
    (hne : (fun j : Fin d => derivativeSign p a (j.val + 1)) ≠
      fun j => derivativeSign p b (j.val + 1)) :
    a < b ↔ ThomLT (fun j : Fin d => derivativeSign p a (j.val + 1))
      (fun j => derivativeSign p b (j.val + 1)) := by
  cases d with
  | zero => exact False.elim (hne (Subsingleton.elim _ _))
  | succ d =>
    have hd' : p.derivative.natDegree ≤ d := by
      have := natDegree_derivative_le p
      omega
    simpa only [derivativeSign_derivative] using
      lt_iff_thomLT_derivativeSign_of_natDegree_le hd' hrolle
        (by simpa only [derivativeSign_derivative] using hne)

/-- **Comparison.** Two points with different Thom encodings are ordered as their encodings are
by `ThomLT`. -/
theorem lt_iff_thomLT (p : R[X]) (hrolle : PolynomialRolle R) {a b : R}
    (hne : thomEncoding p a ≠ thomEncoding p b) :
    a < b ↔ ThomLT (thomEncoding p a) (thomEncoding p b) := by
  simpa only [← thomEncoding_apply] using
    lt_iff_thomLT_derivativeSign_succ_of_natDegree_le le_rfl hrolle
      (by simpa only [← thomEncoding_apply] using hne)

/-- Two roots of a nonzero polynomial are ordered as their derivative signs of orders `1, …, d`
(with `p.natDegree ≤ d`) are by `ThomLT`. -/
theorem lt_iff_thomLT_derivativeSign_succ_of_eval_eq_zero {p : R[X]} {d : ℕ}
    (hd : p.natDegree ≤ d) (hrolle : PolynomialRolle R) (hp : p ≠ 0) {a b : R}
    (ha : p.eval a = 0) (hb : p.eval b = 0) :
    a < b ↔ ThomLT (fun j : Fin d => derivativeSign p a (j.val + 1))
      (fun j => derivativeSign p b (j.val + 1)) := by
  rcases eq_or_ne a b with rfl | hab
  · simp [thomLT_irrefl]
  · exact lt_iff_thomLT_derivativeSign_succ_of_natDegree_le hd hrolle fun h =>
      hab (eq_of_derivativeSign_succ_eq_of_natDegree_le hd hrolle hp ha hb h)

/-- For a root `b` of a nonzero polynomial `p` and any point `a`, `a < b` holds exactly when the
derivative signs of `p` at `a` of orders `0, …, d` (with `p.natDegree ≤ d`) precede `0` followed by
the derivative signs of `p` at `b` of orders `1, …, d` under `ThomLT`. -/
theorem lt_iff_thomLT_cons_derivativeSign_of_eval_eq_zero_right {p : R[X]} {d : ℕ}
    (hd : p.natDegree ≤ d) (hrolle : PolynomialRolle R) (hp : p ≠ 0) {a b : R}
    (hb : p.eval b = 0) :
    a < b ↔ ThomLT (fun i : Fin (d + 1) => derivativeSign p a i.val)
      (Fin.cons 0 (fun j : Fin d => derivativeSign p b (j.val + 1))) := by
  rw [cons_zero_derivativeSign_succ_eq d hb]
  rcases eq_or_ne a b with rfl | hab
  · simp [thomLT_irrefl]
  · exact lt_iff_thomLT_derivativeSign_of_natDegree_le hd hrolle
      (Polynomial.derivativeSign_ne_of_eval_eq_zero hd hrolle hp hab hb)

/-- For a root `a` of a nonzero polynomial `p` and any point `b`, `a < b` holds exactly when `0`
followed by the derivative signs of `p` at `a` of orders `1, …, d` (with `p.natDegree ≤ d`)
precedes the derivative signs of `p` at `b` of orders `0, …, d` under `ThomLT`. -/
theorem lt_iff_thomLT_cons_derivativeSign_of_eval_eq_zero_left {p : R[X]} {d : ℕ}
    (hd : p.natDegree ≤ d) (hrolle : PolynomialRolle R) (hp : p ≠ 0) {a b : R}
    (ha : p.eval a = 0) :
    a < b ↔ ThomLT (Fin.cons 0 (fun j : Fin d => derivativeSign p a (j.val + 1)))
      (fun i : Fin (d + 1) => derivativeSign p b i.val) := by
  rw [cons_zero_derivativeSign_succ_eq d ha]
  rcases eq_or_ne a b with rfl | hab
  · simp [thomLT_irrefl]
  · exact lt_iff_thomLT_derivativeSign_of_natDegree_le hd hrolle
      (Polynomial.derivativeSign_ne_of_eval_eq_zero hd hrolle hp hab.symm ha).symm

/-- Two roots of a nonzero polynomial are ordered as their Thom encodings are by `ThomLT`. -/
theorem lt_iff_thomLT_of_eval_eq_zero (hrolle : PolynomialRolle R) {p : R[X]} (hp : p ≠ 0)
    {a b : R} (ha : p.eval a = 0) (hb : p.eval b = 0) :
    a < b ↔ ThomLT (thomEncoding p a) (thomEncoding p b) := by
  simpa only [← thomEncoding_apply] using
    lt_iff_thomLT_derivativeSign_succ_of_eval_eq_zero le_rfl hrolle hp ha hb

/-- The correspondence between roots and their Thom encodings carries the order of the roots to
`ThomLT`. -/
theorem thomEncodingEquiv_lt_iff (hrolle : PolynomialRolle R) (p : R[X])
    (x y : p.roots.toFinset) :
    ThomLT (thomEncodingEquiv hrolle p x : Fin p.natDegree → SignType)
        (thomEncodingEquiv hrolle p y) ↔ (x : R) < y := by
  have hp : p ≠ 0 := ne_zero_of_mem_roots (Multiset.mem_toFinset.mp x.2)
  have hx := x.2
  have hy := y.2
  simp only [Multiset.mem_toFinset, mem_roots hp, IsRoot.def] at hx hy
  rw [coe_thomEncodingEquiv_apply, coe_thomEncodingEquiv_apply,
    lt_iff_thomLT_of_eval_eq_zero hrolle hp hx hy]

/-- For any root `r` of `p` with derivative signs `τ` of orders `1, …, d` (where `p.natDegree ≤ d`),
the number of distinct roots of `p` strictly below `r` is the number of words `σ : Fin d → SignType`
with `ThomLT σ τ` that are realized by a root in `p.roots.toFinset`. -/
theorem card_roots_lt_eq_card_filter_thomLT_of_natDegree_le {p : R[X]} {d : ℕ}
    (hd : p.natDegree ≤ d) (hrolle : PolynomialRolle R) {r : R} (hr : p.eval r = 0)
    {τ : Fin d → SignType} (hτ : (fun j : Fin d => derivativeSign p r (j.val + 1)) = τ) :
    {x ∈ p.roots.toFinset | x < r}.card =
      (Finset.univ.filter fun σ : Fin d → SignType =>
        ThomLT σ τ ∧ ∃ x ∈ p.roots.toFinset,
          (fun j : Fin d => derivativeSign p x (j.val + 1)) = σ).card := by
  classical
  refine Finset.card_bij (fun x _ j => derivativeSign p x (j.val + 1)) ?_ ?_ ?_
  · intro x hx
    obtain ⟨hx, hlt⟩ := Finset.mem_filter.mp hx
    have hp : p ≠ 0 := ne_zero_of_mem_roots (Multiset.mem_toFinset.mp hx)
    have hx0 : p.eval x = 0 := isRoot_of_mem_roots (Multiset.mem_toFinset.mp hx)
    rw [lt_iff_thomLT_derivativeSign_succ_of_eval_eq_zero hd hrolle hp hx0 hr, hτ] at hlt
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, x, hx, rfl⟩
  · intro a ha b hb h
    have ha' := (Finset.mem_filter.mp ha).1
    have hb' := (Finset.mem_filter.mp hb).1
    have hp : p ≠ 0 := ne_zero_of_mem_roots (Multiset.mem_toFinset.mp ha')
    exact eq_of_derivativeSign_succ_eq_of_natDegree_le hd hrolle hp
      (isRoot_of_mem_roots (Multiset.mem_toFinset.mp ha'))
      (isRoot_of_mem_roots (Multiset.mem_toFinset.mp hb')) h
  · intro σ hσ
    obtain ⟨-, hlt, x, hx, rfl⟩ := Finset.mem_filter.mp hσ
    have hp : p ≠ 0 := ne_zero_of_mem_roots (Multiset.mem_toFinset.mp hx)
    have hx0 : p.eval x = 0 := isRoot_of_mem_roots (Multiset.mem_toFinset.mp hx)
    rw [← hτ, ← lt_iff_thomLT_derivativeSign_succ_of_eval_eq_zero hd hrolle hp hx0 hr] at hlt
    exact ⟨x, Finset.mem_filter.mpr ⟨hx, hlt⟩, rfl⟩

/-- Distinct realized Thom encodings are comparable by `ThomLT`. -/
theorem thomLT_or_thomLT_of_mem_thomEncodings (hrolle : PolynomialRolle R) {p : R[X]}
    {σ τ : Fin p.natDegree → SignType} (hσ : σ ∈ p.thomEncodings) (hτ : τ ∈ p.thomEncodings)
    (hne : σ ≠ τ) : ThomLT σ τ ∨ ThomLT τ σ := by
  obtain ⟨hp, a, ha, rfl⟩ := mem_thomEncodings.1 hσ
  obtain ⟨-, b, hb, rfl⟩ := mem_thomEncodings.1 hτ
  rw [← lt_iff_thomLT p hrolle hne, ← lt_iff_thomLT p hrolle hne.symm]
  exact lt_or_gt_of_ne fun h ↦ hne (h ▸ rfl)

end Polynomial
