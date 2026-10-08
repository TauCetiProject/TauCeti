/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import TauCeti.RingTheory.Polynomial.Cyclotomic.Computable

/-!
# Computable cyclotomic integers

This file defines `TauCeti.Cyclotomic e`, an exact, computable model of
`ℤ[X] / (Polynomial.cyclotomic e ℤ)`.  Its elements are the `e.totient` coefficients of the
canonical representative, in descending order; `TauCeti.Cyclotomic.coeff` reads off the coordinate
of a single power of `ζ`.  Addition, negation, multiplication, and equality are genuine
computations on finite lists of integers; multiplication convolves coefficient lists with
`TauCeti.Polynomial.mulCoeffList` and then applies the computable cyclotomic reduction from
`TauCeti.RingTheory.Polynomial.Cyclotomic.Computable`.

The coefficient accessor is additive (`TauCeti.Cyclotomic.coeffAddHom`), and integer scalar
multiplication scales each coordinate (`TauCeti.Cyclotomic.coeff_intCast_mul`).

The ring is identified with Mathlib's `AdjoinRoot (Polynomial.cyclotomic e ℤ)`.  For nonzero `e`,
evaluation at `exp (2 * π * I / e)` then gives the distinguished embedding into `ℂ` used to state
the correctness of exact character-table computations.

A ring homomorphism out of `Cyclotomic e` is determined by the image of `ζ`
(`TauCeti.Cyclotomic.ringHom_ext`).  Evaluating at a root of the cyclotomic polynomial gives a ring
homomorphism (`TauCeti.Cyclotomic.evalRingHom`); `TauCeti.Cyclotomic.evalCoeffs` evaluates a
coefficient list by Horner's rule.  Evaluation specialises to the reduction modulo a prime `p` at a
primitive `e`-th root in `ZMod p` (`TauCeti.Cyclotomic.reduce`, bundled as
`TauCeti.Cyclotomic.reduceRingHom`) and to the complex embedding
`TauCeti.Cyclotomic.complexEmbedding`, which is injective
(`TauCeti.Cyclotomic.complexEmbedding_injective`).
-/

public section

open Polynomial TauCeti.Polynomial

namespace TauCeti

/-! ## The exact ring -/

/-- Exact `e`-th cyclotomic integers, represented by the `e.totient` coefficients of the
canonical polynomial representative in descending order. -/
@[expose] def Cyclotomic (e : ℕ) : Type _ := {l : List ℤ // l.length = e.totient}
  deriving DecidableEq

namespace Cyclotomic

variable {e : ℕ}

/-- The descending list of coefficients representing an exact cyclotomic integer. -/
@[expose] def coeffs (x : Cyclotomic e) : List ℤ := x.1

@[simp]
theorem length_coeffs (x : Cyclotomic e) : x.coeffs.length = e.totient := x.2

/-- An exact cyclotomic integer is determined by its coefficient list. -/
theorem ext_coeffs {x y : Cyclotomic e} (h : x.coeffs = y.coeffs) : x = y := Subtype.ext h

/-- The coordinate of `ζ ^ j` on the power basis `ζ ^ (φ e - 1), …, ζ, 1`.  Since
`TauCeti.Cyclotomic.coeffs` is in descending order this reads it backwards, and it is `0` beyond
the `e.totient` slots the basis has. -/
@[expose] def coeff (x : Cyclotomic e) (j : ℕ) : ℤ := x.coeffs.reverse.getD j 0

/-- There is no coordinate beyond the `e.totient` elements of the power basis. -/
theorem coeff_eq_zero_of_totient_le (x : Cyclotomic e) {j : ℕ} (h : e.totient ≤ j) :
    x.coeff j = 0 := by
  rw [coeff, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using h),
    Option.getD_none]

/-- An exact cyclotomic integer is determined by its coordinates on the power basis.  Only the
`e.totient` coordinates the basis has are needed: the rest vanish by
`TauCeti.Cyclotomic.coeff_eq_zero_of_totient_le`. -/
@[ext]
theorem ext {x y : Cyclotomic e} (h : ∀ j : Fin e.totient, x.coeff j = y.coeff j) : x = y := by
  refine ext_coeffs (List.reverse_injective (List.ext_getElem (by simp) fun j hj hj' => ?_))
  have hj₁ := h ⟨j, by simpa using hj⟩
  rwa [coeff, coeff, List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj'] at hj₁

/-- Reduce a descending coefficient list modulo `Φ_e` and regard the result as an exact
cyclotomic integer. -/
@[expose] def ofCoeffList (e : ℕ) (l : List ℤ) : Cyclotomic e :=
  ⟨modByCyclotomic e l, length_modByCyclotomic e l⟩

@[simp]
theorem coeffs_ofCoeffList (e : ℕ) (l : List ℤ) :
    (ofCoeffList e l).coeffs = modByCyclotomic e l := rfl

/-- A coefficient list that already has the canonical length `φ e` is its own reduction modulo
`Φ_e`, the polynomial it presents having degree less than `φ e` already. -/
theorem coeffs_ofCoeffList_of_length_eq {l : List ℤ} (h : l.length = e.totient) :
    (ofCoeffList e l).coeffs = l :=
  eq_of_length_eq_of_ofCoeffList_eq (by simp [h])
    (by
      rw [coeffs_ofCoeffList, ofCoeffList_modByCyclotomic]
      exact (modByMonic_eq_self_iff (cyclotomic.monic e ℤ)).2
        (by rw [degree_cyclotomic]; simpa [h] using degree_ofCoeffList_lt l))

/-- An exact cyclotomic integer is rebuilt from its own coefficient list. -/
@[simp]
theorem ofCoeffList_coeffs (x : Cyclotomic e) : ofCoeffList e x.coeffs = x :=
  ext_coeffs (coeffs_ofCoeffList_of_length_eq x.length_coeffs)

/-- Zero in the coefficient-vector model. -/
@[expose] def zero (e : ℕ) : Cyclotomic e := ofCoeffList e []

/-- One in the coefficient-vector model. -/
@[expose] def one (e : ℕ) : Cyclotomic e := ofCoeffList e [1]

/-- Addition followed by canonical cyclotomic reduction. -/
@[expose] def add (x y : Cyclotomic e) : Cyclotomic e :=
  ofCoeffList e (List.zipWith (fun a b => a + b) x.coeffs y.coeffs)

/-- Negation followed by canonical cyclotomic reduction. -/
@[expose] def neg (x : Cyclotomic e) : Cyclotomic e :=
  ofCoeffList e (x.coeffs.map (-·))

/-- Polynomial convolution followed by canonical cyclotomic reduction. -/
@[expose] def mul (x y : Cyclotomic e) : Cyclotomic e :=
  ofCoeffList e (mulCoeffList x.coeffs y.coeffs)

instance : Zero (Cyclotomic e) := ⟨zero e⟩
instance : One (Cyclotomic e) := ⟨one e⟩
instance : Add (Cyclotomic e) := ⟨add⟩
instance : Neg (Cyclotomic e) := ⟨neg⟩
instance : Mul (Cyclotomic e) := ⟨mul⟩

instance : Sub (Cyclotomic e) := ⟨fun x y => x + -y⟩
instance : SMul ℕ (Cyclotomic e) := ⟨nsmulRec⟩
instance : SMul ℤ (Cyclotomic e) := ⟨zsmulRec⟩
instance : Pow (Cyclotomic e) ℕ := ⟨fun x n => npowRec n x⟩
instance : NatCast (Cyclotomic e) := ⟨fun n => ofCoeffList e [n]⟩
instance : IntCast (Cyclotomic e) := ⟨fun z => ofCoeffList e [z]⟩

/-! The notation of the classes above, and the fields of the `CommRing` structure assembled below,
are the standalone operations defined here.  The next few lemmas name that identification once, so
that the proofs which need it can rewrite rather than appeal to definitional unfolding.  None of
them is `simp`: they unfold arithmetic into coefficient lists, which is the opposite direction to
the normal form everything else is stated in. -/

/-- Zero is the reduction `ofCoeffList e []` of the empty coefficient list. -/
theorem zero_def : (0 : Cyclotomic e) = ofCoeffList e [] := rfl

/-- One is the reduction `ofCoeffList e [1]` of the coefficient list `[1]`. -/
theorem one_def : (1 : Cyclotomic e) = ofCoeffList e [1] := rfl

/-- An integer cast is the reduction `ofCoeffList e [z]` of its singleton coefficient list. -/
theorem intCast_def (z : ℤ) : (z : Cyclotomic e) = ofCoeffList e [z] := rfl

/-- Addition adds coefficient lists entrywise. -/
theorem add_def (x y : Cyclotomic e) :
    x + y = ofCoeffList e (List.zipWith (fun a b => a + b) x.coeffs y.coeffs) := rfl

/-- Negation negates every coefficient. -/
theorem neg_def (x : Cyclotomic e) : -x = ofCoeffList e (x.coeffs.map (-·)) := rfl

/-- `TauCeti.Cyclotomic.neg` is the negation of the `Neg` instance. -/
theorem neg_eq (x : Cyclotomic e) : neg x = -x := rfl

/-- Multiplication convolves coefficient lists and reduces modulo `Φ_e`. -/
theorem mul_def (x y : Cyclotomic e) :
    x * y = ofCoeffList e (mulCoeffList x.coeffs y.coeffs) := rfl

/-- The polynomial represented by an exact cyclotomic integer. -/
noncomputable def toPolynomial (x : Cyclotomic e) : ℤ[X] :=
  TauCeti.Polynomial.ofCoeffList x.coeffs

/-- The coordinates of an exact cyclotomic integer are the coefficients of its canonical
polynomial representative. -/
@[simp]
theorem coeff_toPolynomial (x : Cyclotomic e) (j : ℕ) : x.toPolynomial.coeff j = x.coeff j := by
  rw [toPolynomial, TauCeti.Polynomial.coeff_ofCoeffList, coeff]

/-- The comparison map from computable cyclotomic integers to Mathlib's quotient by `Φ_e`. -/
noncomputable def toAdjoinRoot (x : Cyclotomic e) : AdjoinRoot (cyclotomic e ℤ) :=
  AdjoinRoot.mk _ x.toPolynomial

/-- The canonical representative has degree strictly less than the cyclotomic polynomial. -/
theorem degree_toPolynomial_lt (x : Cyclotomic e) :
    x.toPolynomial.degree < (cyclotomic e ℤ).degree := by
  rw [degree_cyclotomic]
  simpa [toPolynomial] using degree_ofCoeffList_lt x.coeffs

/-- The canonical representative is already reduced modulo the cyclotomic polynomial. -/
@[simp]
theorem modByMonic_toPolynomial (x : Cyclotomic e) :
    x.toPolynomial %ₘ cyclotomic e ℤ = x.toPolynomial :=
  (modByMonic_eq_self_iff (cyclotomic.monic e ℤ)).2 x.degree_toPolynomial_lt

/-- The comparison with `AdjoinRoot` is injective. -/
theorem toAdjoinRoot_injective : Function.Injective (toAdjoinRoot : Cyclotomic e → _) := by
  intro x y h
  have h' := congrArg (AdjoinRoot.modByMonicHom (cyclotomic.monic e ℤ)) h
  simp only [toAdjoinRoot, AdjoinRoot.modByMonicHom_mk, modByMonic_toPolynomial] at h'
  exact ext_coeffs
    (eq_of_length_eq_of_ofCoeffList_eq (x.length_coeffs.trans y.length_coeffs.symm) h')

/-- The comparison map sends the exact cyclotomic integer built from a coefficient list to the
class of the polynomial with those coefficients: reduction modulo `Φ_e` is invisible in the
quotient. -/
@[simp]
theorem toAdjoinRoot_ofCoeffList (l : List ℤ) :
    toAdjoinRoot (ofCoeffList e l) = AdjoinRoot.mk _ (TauCeti.Polynomial.ofCoeffList l) := by
  rw [toAdjoinRoot, toPolynomial, coeffs_ofCoeffList, ofCoeffList_modByCyclotomic,
    ← AdjoinRoot.modByMonicHom_mk (cyclotomic.monic e ℤ)]
  exact AdjoinRoot.mk_leftInverse (cyclotomic.monic e ℤ) _

@[simp]
theorem toAdjoinRoot_zero : toAdjoinRoot (0 : Cyclotomic e) = 0 := by
  rw [zero_def, toAdjoinRoot_ofCoeffList]
  simp

@[simp]
theorem toAdjoinRoot_one : toAdjoinRoot (1 : Cyclotomic e) = 1 := by
  rw [one_def, toAdjoinRoot_ofCoeffList]
  simp [TauCeti.Polynomial.ofCoeffList_cons]

@[simp]
theorem toAdjoinRoot_add (x y : Cyclotomic e) :
    toAdjoinRoot (x + y) = toAdjoinRoot x + toAdjoinRoot y := by
  rw [add_def, toAdjoinRoot_ofCoeffList, toAdjoinRoot, toAdjoinRoot]
  rw [← map_add]
  congr 1
  simpa [sub_eq_add_neg, toPolynomial] using
    (ofCoeffList_zipWith_sub (-1 : ℤ) (x.length_coeffs.trans y.length_coeffs.symm))

@[simp]
theorem toAdjoinRoot_neg (x : Cyclotomic e) :
    toAdjoinRoot (-x) = -toAdjoinRoot x := by
  rw [neg_def, toAdjoinRoot_ofCoeffList, toAdjoinRoot, toPolynomial, ofCoeffList_map_neg, map_neg]

@[simp]
theorem toAdjoinRoot_mul (x y : Cyclotomic e) :
    toAdjoinRoot (x * y) = toAdjoinRoot x * toAdjoinRoot y := by
  rw [mul_def, toAdjoinRoot_ofCoeffList, toAdjoinRoot, toAdjoinRoot, ← map_mul,
    ofCoeffList_mulCoeffList]
  simp only [toPolynomial]

/-- The commutative ring structure on exact cyclotomic integers, with executable arithmetic on
canonical coefficient vectors. -/
instance : CommRing (Cyclotomic e) := fast_instance% by
  -- Transport the laws using `Function.Injective.commRing`; normalization keeps the operations
  -- computable.
  have hn (n : ℕ) (x : Cyclotomic e) :
      toAdjoinRoot (nsmulRec n x) = n • toAdjoinRoot x := by
    induction n with
    | zero => simpa only [nsmulRec, zero_nsmul] using toAdjoinRoot_zero (e := e)
    | succ n ih => simp only [nsmulRec, toAdjoinRoot_add, ih, succ_nsmul]
  refine Function.Injective.commRing toAdjoinRoot toAdjoinRoot_injective
    toAdjoinRoot_zero toAdjoinRoot_one toAdjoinRoot_add toAdjoinRoot_mul toAdjoinRoot_neg
    (fun x y => ?_) hn (fun n x => ?_) (fun x n => ?_) (fun n => ?_) (fun z => ?_)
  · exact (toAdjoinRoot_add x (-y)).trans (by rw [toAdjoinRoot_neg, sub_eq_add_neg])
  -- The ring laws are not available yet, so use the primitive recursion and cast instances.
  · change toAdjoinRoot (zsmulRec nsmulRec n x) = n • toAdjoinRoot x
    cases n <;> simp only [zsmulRec, hn, toAdjoinRoot_neg, Int.ofNat_eq_natCast, natCast_zsmul,
      negSucc_zsmul]
  · change toAdjoinRoot (npowRec n x) = toAdjoinRoot x ^ n
    induction n with
    | zero => simp [npowRec]
    | succ n ih => simp [npowRec, toAdjoinRoot_mul, ih, pow_succ]
  · change toAdjoinRoot (ofCoeffList e [(n : ℤ)]) = n
    simp [toAdjoinRoot_ofCoeffList, TauCeti.Polynomial.ofCoeffList_cons]
  · simp [intCast_def, toAdjoinRoot_ofCoeffList, TauCeti.Polynomial.ofCoeffList_cons]

/-- Every coordinate of `0` vanishes, its canonical representative being the zero polynomial. -/
@[simp]
theorem coeff_zero (j : ℕ) : (0 : Cyclotomic e).coeff j = 0 := by
  have hdvd : cyclotomic e ℤ ∣ (0 : Cyclotomic e).toPolynomial := by
    rw [← AdjoinRoot.mk_eq_zero, ← toAdjoinRoot]
    exact toAdjoinRoot_zero
  rw [← coeff_toPolynomial, eq_zero_of_dvd_of_degree_lt hdvd (degree_toPolynomial_lt _),
    Polynomial.coeff_zero]

/-- **Multiplication by an integer constant scales every coefficient.**  A constant multiple
raises no power of `ζ`, so no reduction modulo `Φ_e` takes place. -/
@[simp]
theorem coeffs_intCast_mul (z : ℤ) (x : Cyclotomic e) :
    ((z : Cyclotomic e) * x).coeffs = x.coeffs.map (z * ·) := by
  have hmul : (z : Cyclotomic e) * x = ofCoeffList e (x.coeffs.map (z * ·)) := by
    have hz : TauCeti.Polynomial.ofCoeffList [z] = Polynomial.C z := by
      simp [TauCeti.Polynomial.ofCoeffList_cons]
    refine toAdjoinRoot_injective ?_
    rw [toAdjoinRoot_mul, intCast_def,
      toAdjoinRoot_ofCoeffList, toAdjoinRoot_ofCoeffList, hz,
      TauCeti.Polynomial.ofCoeffList_map_mul_left, map_mul]
    rfl
  rw [hmul]
  exact coeffs_ofCoeffList_of_length_eq (by simp)

/-! ## Comparison with `AdjoinRoot` -/

/-- The ring homomorphism identifying exact cyclotomic integers with the polynomial quotient. -/
noncomputable def toAdjoinRootRingHom : Cyclotomic e →+* AdjoinRoot (cyclotomic e ℤ) where
  toFun := toAdjoinRoot
  map_zero' := toAdjoinRoot_zero
  map_one' := toAdjoinRoot_one
  map_add' := toAdjoinRoot_add
  map_mul' := toAdjoinRoot_mul

@[simp]
theorem toAdjoinRootRingHom_apply (x : Cyclotomic e) :
    toAdjoinRootRingHom x = toAdjoinRoot x := (rfl)

/-- The additive map reading a single power-basis coefficient. -/
noncomputable def coeffAddHom (e j : ℕ) : Cyclotomic e →+ ℤ :=
  ((Polynomial.lcoeff ℤ j).toAddMonoidHom.comp
    (AdjoinRoot.modByMonicHom (Polynomial.cyclotomic.monic e ℤ)).toAddMonoidHom).comp
      toAdjoinRootRingHom.toAddMonoidHom

/-- The coefficient map agrees with the coefficient-vector accessor. -/
@[simp]
theorem coeffAddHom_apply (x : Cyclotomic e) (j : ℕ) : coeffAddHom e j x = x.coeff j := by
  simp [coeffAddHom, toAdjoinRoot, coeff_toPolynomial]

/-- Addition adds power-basis coefficients. -/
@[simp]
theorem coeff_add (x y : Cyclotomic e) (j : ℕ) :
    (x + y).coeff j = x.coeff j + y.coeff j := by
  simpa only [coeffAddHom_apply] using (coeffAddHom e j).map_add x y

/-- Negation negates every power-basis coefficient. -/
@[simp]
theorem coeff_neg (x : Cyclotomic e) (j : ℕ) :
    (-x).coeff j = -x.coeff j := by
  simpa only [coeffAddHom_apply] using (coeffAddHom e j).map_neg x

/-- Subtraction subtracts power-basis coefficients. -/
@[simp]
theorem coeff_sub (x y : Cyclotomic e) (j : ℕ) :
    (x - y).coeff j = x.coeff j - y.coeff j := by
  simpa only [coeffAddHom_apply] using (coeffAddHom e j).map_sub x y

/-- Natural scalar multiplication scales every power-basis coefficient. -/
@[simp↓]
theorem coeff_nsmul (n : ℕ) (x : Cyclotomic e) (j : ℕ) :
    (n • x).coeff j = n • x.coeff j := by
  simpa only [coeffAddHom_apply] using (coeffAddHom e j).map_nsmul n x

/-- Integer scalar multiplication scales every power-basis coefficient. -/
@[simp↓]
theorem coeff_zsmul (z : ℤ) (x : Cyclotomic e) (j : ℕ) :
    (z • x).coeff j = z • x.coeff j := by
  simpa only [coeffAddHom_apply] using (coeffAddHom e j).map_zsmul z x

/-- Integer scalar multiplication scales every power-basis coefficient. -/
@[simp]
theorem coeff_intCast_mul (z : ℤ) (x : Cyclotomic e) (j : ℕ) :
    ((z : Cyclotomic e) * x).coeff j = z * x.coeff j := by
  simpa [zsmul_eq_mul] using (coeffAddHom e j).map_zsmul z x

/-- A finite sum adds power-basis coefficients. -/
@[simp]
theorem coeff_sum {ι : Type*} (s : Finset ι) (f : ι → Cyclotomic e) (j : ℕ) :
    (∑ i ∈ s, f i).coeff j = ∑ i ∈ s, (f i).coeff j := by
  simpa only [coeffAddHom_apply] using map_sum (coeffAddHom e j) f s

/-- Every class modulo `Φ_e` has an exact coefficient-vector representative. -/
theorem toAdjoinRoot_surjective : Function.Surjective (toAdjoinRoot : Cyclotomic e → _) := by
  intro z
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  refine ⟨ofCoeffList e p.coeffList, ?_⟩
  rw [toAdjoinRoot_ofCoeffList, TauCeti.Polynomial.ofCoeffList_coeffList]

private theorem toAdjoinRootRingHom_bijective :
    Function.Bijective (toAdjoinRootRingHom (e := e)) :=
  ⟨fun _ _ h => toAdjoinRoot_injective (by simpa using h),
    fun z => (toAdjoinRoot_surjective z).imp fun _ h => by simpa using h⟩

/-- Exact cyclotomic integers are the quotient `ℤ[X] / (Φ_e)`. -/
noncomputable def equivAdjoinRoot :
    Cyclotomic e ≃+* AdjoinRoot (cyclotomic e ℤ) :=
  RingEquiv.ofBijective toAdjoinRootRingHom toAdjoinRootRingHom_bijective

@[simp]
theorem equivAdjoinRoot_apply (x : Cyclotomic e) : equivAdjoinRoot x = toAdjoinRoot x := by
  rw [equivAdjoinRoot, RingEquiv.ofBijective_apply, toAdjoinRootRingHom_apply]

/-- The distinguished generator `ζ`, represented by the polynomial `X`. -/
@[expose] def zeta (e : ℕ) : Cyclotomic e := ofCoeffList e [1, 0]

@[simp]
theorem toAdjoinRoot_zeta : toAdjoinRoot (zeta e) = AdjoinRoot.root (cyclotomic e ℤ) := by
  have hX : TauCeti.Polynomial.ofCoeffList ([1, 0] : List ℤ) = X := by
    simp [TauCeti.Polynomial.ofCoeffList_cons]
  rw [zeta, toAdjoinRoot_ofCoeffList, hX, AdjoinRoot.mk_X]

@[simp]
theorem equivAdjoinRoot_symm_root :
    (equivAdjoinRoot (e := e)).symm (AdjoinRoot.root (cyclotomic e ℤ)) = zeta e :=
  equivAdjoinRoot.symm_apply_eq.2 (by rw [equivAdjoinRoot_apply, toAdjoinRoot_zeta])

/-- A ring homomorphism out of the exact cyclotomic integers is determined by the image of the
distinguished generator `ζ`: the integers admit a unique ring homomorphism, and `ζ` generates
everything else. -/
@[ext high]
theorem ringHom_ext {R : Type*} [Semiring R] {g₁ g₂ : Cyclotomic e →+* R}
    (h : g₁ (zeta e) = g₂ (zeta e)) : g₁ = g₂ := by
  have key : g₁.comp (equivAdjoinRoot (e := e)).symm.toRingHom
      = g₂.comp (equivAdjoinRoot (e := e)).symm.toRingHom :=
    AdjoinRoot.ringHom_ext (RingHom.ext_int _ _) (by simpa using h)
  refine RingHom.ext fun x => ?_
  obtain ⟨y, rfl⟩ := equivAdjoinRoot.symm.surjective x
  exact RingHom.congr_fun key y

/-! ## Evaluation and residue maps -/

/-- Evaluate exact cyclotomic integers at a root of the mapped cyclotomic polynomial. -/
noncomputable def evalRingHom {R : Type*} [CommRing R] (f : ℤ →+* R) (r : R)
    (hr : (cyclotomic e ℤ).eval₂ f r = 0) : Cyclotomic e →+* R :=
  (AdjoinRoot.lift f r hr).comp toAdjoinRootRingHom

/-- Evaluation at a root of `Φ_e` is evaluation of the canonical polynomial representative. -/
theorem evalRingHom_apply {R : Type*} [CommRing R] (f : ℤ →+* R) (r : R)
    (hr : (cyclotomic e ℤ).eval₂ f r = 0) (x : Cyclotomic e) :
    evalRingHom f r hr x = x.toPolynomial.eval₂ f r := by
  rw [evalRingHom, RingHom.comp_apply, toAdjoinRootRingHom_apply, toAdjoinRoot,
    AdjoinRoot.lift_mk]

@[simp]
theorem evalRingHom_ofCoeffList {R : Type*} [CommRing R] (f : ℤ →+* R) (r : R)
    (hr : (cyclotomic e ℤ).eval₂ f r = 0) (l : List ℤ) :
    evalRingHom f r hr (ofCoeffList e l) =
      (TauCeti.Polynomial.ofCoeffList l).eval₂ f r := by
  rw [evalRingHom, RingHom.comp_apply, toAdjoinRootRingHom_apply, toAdjoinRoot_ofCoeffList,
    AdjoinRoot.lift_mk]

/-- Evaluation at a root `r` of `Φ_e` sends the distinguished generator `ζ` to `r`. -/
@[simp]
theorem evalRingHom_zeta {R : Type*} [CommRing R] (f : ℤ →+* R) (r : R)
    (hr : (cyclotomic e ℤ).eval₂ f r = 0) : evalRingHom f r hr (zeta e) = r := by
  rw [evalRingHom, RingHom.comp_apply, toAdjoinRootRingHom_apply, toAdjoinRoot_zeta,
    AdjoinRoot.lift_root]

/-- `TauCeti.Cyclotomic.evalRingHom f r hr` is the *only* ring homomorphism sending the
distinguished generator `ζ` to `r`. -/
theorem eq_evalRingHom {R : Type*} [CommRing R] (f : ℤ →+* R) (r : R)
    (hr : (cyclotomic e ℤ).eval₂ f r = 0) (g : Cyclotomic e →+* R) (hg : g (zeta e) = r) :
    g = evalRingHom f r hr :=
  ringHom_ext (by rw [hg, evalRingHom_zeta])

/-- Evaluate a coefficient vector by Horner's rule.  Unlike `Polynomial.eval₂`, this is a genuine
computation because it works directly on the finite list. -/
@[expose] def evalCoeffs {R : Type*} [Semiring R] (f : ℤ →+* R) (r : R)
    (x : Cyclotomic e) : R :=
  x.coeffs.foldl (fun y a => y * r + f a) 0

/-- Direct coefficient-list evaluation agrees with polynomial evaluation. -/
theorem evalCoeffs_eq_eval₂ {R : Type*} [Semiring R] (f : ℤ →+* R) (r : R)
    (x : Cyclotomic e) :
    evalCoeffs f r x = x.toPolynomial.eval₂ f r := by
  rw [evalCoeffs, toPolynomial, TauCeti.Polynomial.eval₂_ofCoeffList]

/-- The bundled evaluation at a root of the cyclotomic polynomial is the Horner evaluation
`TauCeti.Cyclotomic.evalCoeffs`. -/
theorem evalRingHom_eq_evalCoeffs {R : Type*} [CommRing R] (f : ℤ →+* R) (r : R)
    (hr : (cyclotomic e ℤ).eval₂ f r = 0) (x : Cyclotomic e) :
    evalRingHom f r hr x = evalCoeffs f r x := by
  rw [evalRingHom_apply, evalCoeffs_eq_eval₂]

/-- Horner's rule in closed form: coefficient-list evaluation is the sum of the evaluated
coordinates against the powers of `r`, one term for each element of the power basis. -/
theorem evalCoeffs_eq_sum {R : Type*} [Semiring R] (f : ℤ →+* R) (r : R) (x : Cyclotomic e) :
    evalCoeffs f r x = ∑ j : Fin e.totient, f (x.coeff j) * r ^ (j : ℕ) := by
  rw [evalCoeffs_eq_eval₂, eval₂_eq_sum,
    Fin.sum_univ_eq_sum_range (fun j => f (x.coeff j) * r ^ j) e.totient]
  rw [Polynomial.sum_eq_of_subset (fun j a => f a * r ^ j) (by simp)
    (s := Finset.range e.totient)]
  · simp only [coeff_toPolynomial]
  · intro j hj
    exact Finset.mem_range.mpr (lt_of_not_ge fun h =>
      (mem_support_iff.mp hj) (by rw [coeff_toPolynomial]; exact x.coeff_eq_zero_of_totient_le h))

/-- Reduction of exact cyclotomic integers in `ZMod p`, evaluated at a chosen residue `r`.
When `p` is prime and `r` is a primitive `e`-th root, `TauCeti.Cyclotomic.reduceRingHom` packages
this as a ring homomorphism. -/
@[expose] def reduce (p : ℕ) (r : ZMod p) (x : Cyclotomic e) : ZMod p :=
  evalCoeffs (Int.castRingHom (ZMod p)) r x

/-- Reduction is the sum of the reduced coordinates against the powers of the residue. -/
theorem reduce_eq_sum (p : ℕ) (r : ZMod p) (x : Cyclotomic e) :
    reduce p r x = ∑ j : Fin e.totient, ((x.coeff j : ℤ) : ZMod p) * r ^ (j : ℕ) :=
  evalCoeffs_eq_sum _ _ _

/-- Reduction at an `e`-th primitive root in a prime field is a ring homomorphism. -/
noncomputable def reduceRingHom (p : ℕ) [Fact p.Prime] [NeZero e]
    (r : ZMod p) (hr : IsPrimitiveRoot r e) : Cyclotomic e →+* ZMod p :=
  evalRingHom (Int.castRingHom (ZMod p)) r <| by
    rw [← eval_map, map_cyclotomic]
    exact hr.isRoot_cyclotomic (NeZero.pos e)

-- Not `@[simp]`: `reduce p r` is multiplicative only when `r` is a root of the cyclotomic
-- polynomial, so it has no `simp` API of its own, and rewriting `reduceRingHom` to it would stop
-- `simp` from using `map_mul` and `map_add`.
theorem reduceRingHom_apply (p : ℕ) [Fact p.Prime] [NeZero e]
    (r : ZMod p) (hr : IsPrimitiveRoot r e) (x : Cyclotomic e) :
    reduceRingHom p r hr x = reduce p r x := by
  rw [reduceRingHom, evalRingHom_eq_evalCoeffs, reduce]

/-- For a prime `p`, reduction at a primitive `e`-th root in `ZMod p` sends the distinguished
generator `ζ` to that root. -/
@[simp]
theorem reduce_zeta (p : ℕ) [Fact p.Prime] [NeZero e] (r : ZMod p) (hr : IsPrimitiveRoot r e) :
    reduce p r (zeta e) = r := by
  rw [← reduceRingHom_apply p r hr, reduceRingHom, evalRingHom_zeta]

/-! ## The distinguished complex embedding -/

/-- The distinguished complex `e`-th root of unity `exp (2πi/e)`.  It is primitive for `e ≠ 0`
(`TauCeti.Cyclotomic.isPrimitiveRoot_complexRoot`); at `e = 0` it is `exp 0 = 1`. -/
noncomputable def complexRoot (e : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / e)

/-- For nonzero `e`, the distinguished root `TauCeti.Cyclotomic.complexRoot e` is a primitive
`e`-th root of unity.  Which primitive root it is, and hence which embedding
`TauCeti.Cyclotomic.complexEmbedding` is, is fixed by the definition `exp (2πi/e)`. -/
theorem isPrimitiveRoot_complexRoot [NeZero e] : IsPrimitiveRoot (complexRoot e) e :=
  Complex.isPrimitiveRoot_exp e (NeZero.ne e)

/-- Complex conjugation sends the distinguished root `complexRoot e` to its inverse.  The root is
primitive for `e ≠ 0` (`TauCeti.Cyclotomic.isPrimitiveRoot_complexRoot`), and `complexRoot 0 = 1`.
The `(e - 1)`-st power `TauCeti.Cyclotomic.conj_complexRoot_eq_pow_sub_one` is the simp normal
form, since it stays inside the subring generated by the root. -/
theorem conj_complexRoot :
    starRingEnd ℂ (complexRoot e) = (complexRoot e)⁻¹ := by
  rcases eq_or_ne e 0 with rfl | he
  · simp [complexRoot]
  have : NeZero e := ⟨he⟩
  exact (Complex.inv_eq_conj (isPrimitiveRoot_complexRoot.norm'_eq_one he)).symm

/-- Complex conjugation sends the distinguished root `complexRoot e` to its `(e - 1)`-st power.
For `e = 0` both sides are `1`. -/
@[simp]
theorem conj_complexRoot_eq_pow_sub_one :
    starRingEnd ℂ (complexRoot e) = complexRoot e ^ (e - 1) := by
  rcases eq_or_ne e 0 with rfl | he
  · simp [complexRoot]
  have : NeZero e := ⟨he⟩
  rw [conj_complexRoot]
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ', Nat.sub_add_cancel (NeZero.pos e)]
  exact isPrimitiveRoot_complexRoot.pow_eq_one

/-- The distinguished complex root annihilates the integral cyclotomic polynomial. -/
theorem eval₂_cyclotomic_complexRoot [NeZero e] :
    (cyclotomic e ℤ).eval₂ (Int.castRingHom ℂ) (complexRoot e) = 0 := by
  rw [← eval_map, map_cyclotomic]
  exact (isPrimitiveRoot_complexRoot (e := e)).isRoot_cyclotomic (NeZero.pos e)

/-- The pinned embedding of exact cyclotomic integers into `ℂ`, sending `ζ` to
`exp (2πi/e)`. -/
noncomputable def complexEmbedding [NeZero e] : Cyclotomic e →+* ℂ :=
  evalRingHom (Int.castRingHom ℂ) (complexRoot e) eval₂_cyclotomic_complexRoot

/-- The pinned embedding evaluates the canonical polynomial representative at `exp (2πi/e)`. -/
theorem complexEmbedding_apply [NeZero e] (x : Cyclotomic e) :
    complexEmbedding x = Polynomial.aeval (complexRoot e) x.toPolynomial := by
  rw [complexEmbedding, evalRingHom_apply, aeval_def, algebraMap_int_eq]

@[simp]
theorem complexEmbedding_zeta [NeZero e] : complexEmbedding (zeta e) = complexRoot e := by
  exact evalRingHom_zeta _ _ _

/-- The distinguished complex realization of exact cyclotomic integers is injective. -/
theorem complexEmbedding_injective [NeZero e] :
    Function.Injective (complexEmbedding : Cyclotomic e → ℂ) := by
  intro x y hxy
  have hzero : complexEmbedding (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have heval : Polynomial.aeval (complexRoot e) (x - y).toPolynomial = 0 := by
    rw [← complexEmbedding_apply]; exact hzero
  have hdiv : cyclotomic e ℤ ∣ (x - y).toPolynomial := by
    rw [cyclotomic_eq_minpoly isPrimitiveRoot_complexRoot (NeZero.pos e)]
    exact minpoly.isIntegrallyClosed_dvd
      (isPrimitiveRoot_complexRoot.isIntegral (NeZero.pos e)) heval
  have hp : (x - y).toPolynomial = 0 :=
    Polynomial.eq_zero_of_dvd_of_degree_lt hdiv (degree_toPolynomial_lt (x - y))
  apply sub_eq_zero.mp
  apply toAdjoinRoot_injective
  rw [toAdjoinRoot, hp, map_zero, toAdjoinRoot_zero]

/-! The exact arithmetic reduces in the kernel.  In `Cyclotomic 5`, `ζ₅⁵ = 1`; in `Cyclotomic 4`,
reduction at `2 : ZMod 5`, a primitive fourth root, sends `ζ₄ + 1` to `3`. -/

example : (zeta 5 ^ 5).coeffs = (1 : Cyclotomic 5).coeffs := by decide

example : reduce 5 2 (zeta 4 + 1) = 3 := by decide

end Cyclotomic

end TauCeti
