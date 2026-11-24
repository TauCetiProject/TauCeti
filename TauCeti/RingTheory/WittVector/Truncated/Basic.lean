/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Quotient
public import Mathlib.RingTheory.WittVector.Compare
public import Mathlib.RingTheory.WittVector.Complete
public import Mathlib.RingTheory.WittVector.Truncated
public import TauCeti.RingTheory.DeltaRing.Basic

import TauCeti.RingTheory.WittVector.Units

/-!
# Coefficient maps, reduction modulo `p` and length-two Witt arithmetic

A ring homomorphism `f : A →+* B` induces a ring homomorphism `W_n(A) →+* W_n(B)` acting on Witt
coordinates by `f`, compatibly with truncation from `W(A)`. For `A` of characteristic `p` the
Witt-vector Frobenius of `W_n(A)` is `TruncatedWittVector.map n (frobenius A p)`
(`TruncatedWittVector.map_frobenius_wittVector_truncate`), and for perfect `A` it is the
automorphism `TruncatedWittVector.mapEquiv n (frobeniusEquiv A p)`.

For `n ≠ 0` the zeroth coordinate is a ring homomorphism `W_n(A) →+* A`. When `A` has
characteristic `p`, the ring `W_n(A)` has characteristic `p ^ n`, and when moreover `A` is perfect,
the kernel of the zeroth coordinate is the ideal `(p)`, so that `W_n(A) ⧸ (p) ≃+* A`. These are the
truncated analogues of `WittVector.ker_constantCoeff` and `WittVector.quotientPEquiv`.

The length-two Witt ring has ghost components `x₀` and `x₀ ^ p + p * x₁`. The second coordinate
of a sum is the sum of the two second coordinates plus the integral δ-ring correction polynomial
evaluated at the zeroth coordinates.
The coordinate identities hold over arbitrary commutative rings, including rings with
`p`-torsion. Cancellation by `p` is used only over a universal polynomial ring over `ℤ`.

These are the length-two arithmetic and unit criterion used in Bhatt and Scholze,
*Prisms and prismatic cohomology*, Remark 2.4 and Lemma 2.15.
-/

public section

noncomputable section

namespace TruncatedWittVector

variable {p : ℕ} [hp : Fact p.Prime]
variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

/-- Change the coefficient ring of a truncated Witt vector. -/
def map (n : ℕ) (f : A →+* B) :
    TruncatedWittVector p n A →+* TruncatedWittVector p n B :=
  RingHom.liftOfRightInverse (WittVector.truncate n) out truncateFun_out
    ⟨(WittVector.truncate n).comp (WittVector.map f), by
      intro x hx
      rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker,
        WittVector.mem_ker_truncate]
      intro i hi
      rw [WittVector.map_coeff, (WittVector.mem_ker_truncate n x).mp hx i hi, map_zero]⟩

/-- Coefficient change commutes with truncation from full Witt vectors. -/
@[simp]
theorem map_wittVector_truncate (n : ℕ) (f : A →+* B) (x : WittVector p A) :
    map n f (WittVector.truncate n x) = WittVector.truncate n (WittVector.map f x) :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ _

/-- Coefficient change applies the coefficient homomorphism in every coordinate. -/
@[simp]
theorem map_coeff (n : ℕ) (f : A →+* B) (x : TruncatedWittVector p n A) (i : Fin n) :
    (map n f x).coeff i = f (x.coeff i) := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective (p := p) n A x
  simp only [map_wittVector_truncate, WittVector.coeff_truncate, WittVector.map_coeff]

/-- Changing coefficients by the identity is the identity. -/
@[simp]
theorem map_id (n : ℕ) : map (p := p) n (RingHom.id A) = RingHom.id _ := by
  ext x i
  simp only [map_coeff, RingHom.id_apply]

/-- Coefficient change respects composition. -/
theorem map_comp (n : ℕ) (f : A →+* B) (g : B →+* C) :
    map (p := p) n (g.comp f) = (map n g).comp (map n f) := by
  ext x i
  simp only [map_coeff, RingHom.comp_apply]

/-- The Witt vector Frobenius of `W(A)` descends to `TruncatedWittVector.map n (frobenius A p)` on
`W_n(A)` for `A` of characteristic `p`. -/
theorem map_frobenius_wittVector_truncate [CharP A p] (n : ℕ) (x : WittVector p A) :
    map n (frobenius A p) (WittVector.truncate n x) =
      WittVector.truncate n (WittVector.frobenius x) := by
  rw [map_wittVector_truncate, WittVector.frobenius_eq_map_frobenius]

/-- The ring isomorphism of truncated Witt vectors induced by a ring isomorphism `e`, acting on
Witt coordinates by `e`. -/
def mapEquiv (n : ℕ) (e : A ≃+* B) :
    TruncatedWittVector p n A ≃+* TruncatedWittVector p n B :=
  RingEquiv.ofRingHom (map n e) (map n e.symm)
    (RingHom.ext fun x ↦ ext fun i ↦ by simp) (RingHom.ext fun x ↦ ext fun i ↦ by simp)

@[simp]
theorem mapEquiv_apply (n : ℕ) (e : A ≃+* B) (x : TruncatedWittVector p n A) :
    mapEquiv n e x = map n e x :=
  (rfl)

@[simp]
theorem mapEquiv_symm (n : ℕ) (e : A ≃+* B) :
    (mapEquiv (p := p) n e).symm = mapEquiv n e.symm :=
  (rfl)

variable (p A) in
/-- Truncated Witt vectors of length `n` over a ring of characteristic `p` have characteristic
`p ^ n`. -/
instance charP (n : ℕ) [CharP A p] :
    CharP (TruncatedWittVector p n A) (p ^ n) := by
  have : Nontrivial A := CharP.nontrivial_of_char_ne_one hp.out.ne_one
  have := charP_zmod p n
  refine charP_of_injective_ringHom (f := map n (ZMod.castHom (dvd_refl p) A)) ?_ (p ^ n)
  intro x y hxy
  ext i
  have h := congr_arg (coeff i) hxy
  rw [map_coeff, map_coeff] at h
  exact (ZMod.castHom (dvd_refl p) A).injective h

section ConstantCoeff

variable {n : ℕ} [NeZero n]

/-- The zeroth Witt coordinate, as a ring homomorphism `W_n(A) →+* A` for `n ≠ 0`. In length two
it is the zeroth ghost component. -/
def constantCoeff : TruncatedWittVector p n A →+* A :=
  RingHom.liftOfRightInverse (WittVector.truncate n) out truncateFun_out
    ⟨WittVector.constantCoeff, by
      intro x hx
      exact (WittVector.mem_ker_truncate n x).mp hx 0 (Nat.pos_of_neZero n)⟩

/-- Truncation preserves the zeroth coordinate. -/
theorem constantCoeff_comp_wittVector_truncate :
    (constantCoeff (p := p) (n := n) (A := A)).comp (WittVector.truncate n) =
      WittVector.constantCoeff :=
  RingHom.liftOfRightInverse_comp _ _ _ _

/-- Truncation preserves the zeroth coordinate, applied to an element. -/
@[simp]
theorem constantCoeff_wittVector_truncate (x : WittVector p A) :
    constantCoeff (WittVector.truncate n x) = x.coeff 0 :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ _

/-- The zeroth coordinate map reads off the zeroth Witt coordinate.
Kept as a named equation so generic ring-homomorphism laws retain their bundled form. -/
theorem constantCoeff_apply (x : TruncatedWittVector p n A) :
    constantCoeff x = x.coeff 0 := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective (p := p) n A x
  rw [constantCoeff_wittVector_truncate, WittVector.coeff_truncate, Fin.val_zero]

@[simp]
theorem constantCoeff_map (f : A →+* B) (x : TruncatedWittVector p n A) :
    constantCoeff (map n f x) = f (constantCoeff x) := by
  simp [constantCoeff_apply]

theorem constantCoeff_surjective :
    Function.Surjective (constantCoeff : TruncatedWittVector p n A → A) := fun r ↦ by
  obtain ⟨x, rfl⟩ := WittVector.constantCoeff_surjective p r
  exact ⟨WittVector.truncate n x, constantCoeff_wittVector_truncate x⟩

variable [CharP A p]

/-- For `n ≠ 0`, the reduction modulo `p` of `W_n(A)` has characteristic `p`. -/
instance charP_quotient :
    CharP (TruncatedWittVector p n A ⧸ Ideal.span {(p : TruncatedWittVector p n A)}) p := by
  have : Nontrivial (TruncatedWittVector p n A) :=
    CharP.nontrivial_of_char_ne_one (v := p ^ n) (Nat.one_lt_pow (NeZero.ne n) hp.out.one_lt).ne'
  refine CharP.quotient _ p fun hu ↦ not_isUnit_zero (M₀ := TruncatedWittVector p n A) ?_
  simpa [← Nat.cast_pow, CharP.cast_eq_zero] using hu.pow n

variable [PerfectRing A p]

/-- For a perfect ring `A` of characteristic `p`, the kernel of the zeroth coordinate of `W_n(A)`
is the ideal `(p)`. -/
theorem ker_constantCoeff :
    RingHom.ker (constantCoeff : TruncatedWittVector p n A →+* A) =
      Ideal.span {(p : TruncatedWittVector p n A)} := by
  refine le_antisymm (fun x hx ↦ ?_) (Ideal.span_le.mpr ?_)
  · obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n A x
    rw [RingHom.mem_ker, constantCoeff_wittVector_truncate,
      ← WittVector.mem_span_p_iff_coeff_zero_eq_zero] at hx
    simpa [Ideal.map_span] using Ideal.mem_map_of_mem (WittVector.truncate n) hx
  · simp

/-- For a perfect ring `A` of characteristic `p` and `n ≠ 0`, the zeroth coordinate induces an
isomorphism `W_n(A) ⧸ (p) ≃+* A`. -/
def quotientPEquiv :
    TruncatedWittVector p n A ⧸ Ideal.span {(p : TruncatedWittVector p n A)} ≃+* A :=
  (Ideal.quotEquivOfEq ker_constantCoeff.symm).trans
    (RingHom.quotientKerEquivOfSurjective constantCoeff_surjective)

@[simp]
theorem quotientPEquiv_mk (x : TruncatedWittVector p n A) :
    quotientPEquiv (Ideal.Quotient.mk _ x) = constantCoeff x := by
  simp [quotientPEquiv, Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- For a perfect ring `A` of characteristic `p` and `n ≠ 0`, the reduction modulo `p` of `W_n(A)`
is perfect, being isomorphic to `A`. -/
instance perfectRing_quotient :
    PerfectRing (TruncatedWittVector p n A ⧸ Ideal.span {(p : TruncatedWittVector p n A)}) p := by
  let e := (quotientPEquiv (p := p) (n := n) (A := A))
  refine ⟨?_⟩
  have h : (fun x ↦ x ^ p) = e.symm ∘ (fun y : A ↦ y ^ p) ∘ e := funext fun x ↦ by simp
  rw [h]
  exact e.symm.bijective.comp (PerfectRing.bijective_frobenius.comp e.bijective)

end ConstantCoeff

/-- The first ghost component of the length-two Witt ring. -/
def ghostComponentOne : TruncatedWittVector p 2 A →+* A :=
  RingHom.liftOfRightInverse (WittVector.truncate 2) out truncateFun_out
    ⟨WittVector.ghostComponent 1, by
      intro x hx
      have h := (WittVector.mem_ker_truncate 2 x).mp hx
      rw [RingHom.mem_ker, WittVector.ghostComponent_apply, wittPolynomial_one]
      simp only [map_add, map_mul, map_pow,
        MvPolynomial.aeval_X, map_natCast, h 0 (by decide), h 1 (by decide),
        zero_pow hp.out.ne_zero, mul_zero, add_zero]⟩

/-- Truncation to length two preserves the first ghost component. -/
@[simp]
theorem ghostComponentOne_wittVector_truncate (x : WittVector p A) :
    ghostComponentOne (WittVector.truncate 2 x) = WittVector.ghostComponent 1 x :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ _

/-- The first ghost component is the polynomial `x₀ ^ p + p * x₁`.
Kept as a named equation so generic ring-homomorphism laws retain their bundled form. -/
theorem ghostComponentOne_apply (x : TruncatedWittVector p 2 A) :
    ghostComponentOne x = x.coeff 0 ^ p + p * x.coeff 1 := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective (p := p) 2 A x
  rw [ghostComponentOne_wittVector_truncate, WittVector.ghostComponent_apply,
    wittPolynomial_one]
  simp only [map_add, map_mul, map_pow, MvPolynomial.aeval_X,
    map_natCast, WittVector.coeff_truncate]
  exact add_comm _ _

/-- The zeroth coordinate of a sum in length two. -/
@[simp]
theorem add_coeff_zero (x y : TruncatedWittVector p 2 A) :
    (x + y).coeff 0 = x.coeff 0 + y.coeff 0 := by
  simpa only [constantCoeff_apply] using (map_add (constantCoeff (p := p)) x y)

/-- The zeroth coordinate of a product in length two. -/
@[simp]
theorem mul_coeff_zero (x y : TruncatedWittVector p 2 A) :
    (x * y).coeff 0 = x.coeff 0 * y.coeff 0 := by
  simpa only [constantCoeff_apply] using (map_mul (constantCoeff (p := p)) x y)

/-- The zeroth coordinate of the unit Witt vector is one. -/
@[simp]
theorem one_coeff_zero : (1 : TruncatedWittVector p 2 A).coeff 0 = 1 := by
  simpa only [constantCoeff_apply] using (map_one (constantCoeff (p := p) (n := 2) (A := A)))

/-- The second coordinate of the unit Witt vector is zero. -/
@[simp]
theorem one_coeff_one : (1 : TruncatedWittVector p 2 A).coeff 1 = 0 := by
  rw [← map_one (WittVector.truncate (p := p) (R := A) 2), WittVector.coeff_truncate]
  exact WittVector.one_coeff_eq_of_pos p A 1 (by decide)

/-- The second coordinate of `x + y` is `x₁ + y₁ + TauCeti.DeltaRing.addCorrection p x₀ y₀`. -/
theorem add_coeff_one (x y : TruncatedWittVector p 2 A) :
    (x + y).coeff 1 = x.coeff 1 + y.coeff 1 +
      TauCeti.DeltaRing.addCorrection p (x.coeff 0) (y.coeff 0) := by
  let X : TruncatedWittVector p 2 (MvPolynomial (Bool × Fin 2) ℤ) :=
    mk p fun i => MvPolynomial.X (false, i)
  let Y : TruncatedWittVector p 2 (MvPolynomial (Bool × Fin 2) ℤ) :=
    mk p fun i => MvPolynomial.X (true, i)
  have h : (X + Y).coeff 1 = X.coeff 1 + Y.coeff 1 +
      TauCeti.DeltaRing.addCorrection p (X.coeff 0) (Y.coeff 0) := by
    have hp_ne : (p : MvPolynomial (Bool × Fin 2) ℤ) ≠ 0 :=
      Nat.cast_ne_zero.mpr hp.out.ne_zero
    apply mul_left_cancel₀ hp_ne
    have hg := (ghostComponentOne (p := p)).map_add X Y
    simp only [ghostComponentOne_apply, add_coeff_zero] at hg
    have hc := TauCeti.DeltaRing.natCast_mul_addCorrection (p := p) (X.coeff 0) (Y.coeff 0)
    linear_combination hg - hc
  let f : MvPolynomial (Bool × Fin 2) ℤ →+* A :=
    MvPolynomial.eval₂Hom (Int.castRingHom A) fun i => if i.1 then y.coeff i.2 else x.coeff i.2
  have hX : map 2 f X = x := by ext i; simp [f, X]
  have hY : map 2 f Y = y := by ext i; simp [f, Y]
  have hf := congrArg f h
  simpa only [← map_coeff, map_add, hX, hY,
    TauCeti.DeltaRing.map_addCorrection] using hf

/-- The second multiplication coordinate over any commutative ring. -/
theorem mul_coeff_one (x y : TruncatedWittVector p 2 A) :
    (x * y).coeff 1 = x.coeff 0 ^ p * y.coeff 1 + y.coeff 0 ^ p * x.coeff 1 +
      p * x.coeff 1 * y.coeff 1 := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective (p := p) 2 A x
  obtain ⟨y, rfl⟩ := WittVector.truncate_surjective (p := p) 2 A y
  rw [← map_mul]
  simpa only [WittVector.coeff_truncate, Fin.val_zero, Fin.val_one] using
    WittVector.mul_coeff_one x y

/-- Over any commutative ring, a length-two Witt vector is invertible precisely when both ghost
components are units. -/
theorem isUnit_iff_isUnit_ghostComponents (x : TruncatedWittVector p 2 A) :
    IsUnit x ↔ IsUnit (x.coeff 0) ∧ IsUnit (ghostComponentOne x) := by
  refine ⟨fun hx => ⟨hx.map constantCoeff, hx.map ghostComponentOne⟩, ?_⟩
  rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
  let y : TruncatedWittVector p 2 A :=
    mk p ![↑u⁻¹, -x.coeff 1 * (↑u⁻¹ : A) ^ p * ↑v⁻¹]
  apply isUnit_iff_exists_inv.mpr
  refine ⟨y, ?_⟩
  ext i
  fin_cases i
  · simp [y, ← hu]
  · -- The case split produces a constructor index. The rewrite expects the numeral index.
    change (x * y).coeff 1 = (1 : TruncatedWittVector p 2 A).coeff 1
    rw [mul_coeff_one, one_coeff_one]
    simp only [y, coeff_mk, Matrix.cons_val_zero, Matrix.cons_val_one]
    calc
      _ = x.coeff 1 * (↑u⁻¹ : A) ^ p *
          (1 - (x.coeff 0 ^ p + p * x.coeff 1) * ↑v⁻¹) := by ring
      _ = 0 := by rw [← ghostComponentOne_apply, ← hv]; simp

end TruncatedWittVector
