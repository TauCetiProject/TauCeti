/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Cotangent
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Pfister

/-!
# The signed discriminant on the Witt ring and `I/I² ≅ Kˣ/(Kˣ)²`

Adding a hyperbolic plane does not change the signed discriminant `d±`, so `d±` is a well-defined
function on the Witt ring `W(K)`. It need not be additive on all of `W(K)`: `d±(q ⊥ r)` picks up the
sign `(-1)^{mn}` in ranks `m` and `n`. That sign disappears as soon as one summand has even rank.
So `d±` restricts to an additive map on the fundamental ideal `I(K)`, and this is where the
*signed* discriminant, rather than the plain one, is forced.

On a one-fold Pfister class `d±⟨⟨a⟩⟩` is the square class of `a`. The two-fold Pfister classes lie
in its kernel, and they additively generate `I(K)²`, so `d±` vanishes on `I(K)²`. Conversely, the
identity `⟨⟨a⟩⟩ + ⟨⟨b⟩⟩ = ⟨⟨ab⟩⟩ + ⟨⟨a, b⟩⟩` shows that every element of `I(K)` is congruent
modulo `I(K)²` to a single one-fold Pfister class `⟨⟨a⟩⟩`, with `a` in the square class
`d±(x)`. Together these describe `I(K)²` as the classes of the even-dimensional forms of
trivial signed discriminant, and give the isomorphism
`I(K)/I(K)² ≅ Kˣ/(Kˣ)²`.

The quotient `I/I²` is Mathlib's `Ideal.Cotangent`. The square-class group is
`TauCeti.SquareClassGroup K`, written additively.

## Main definitions

* `TauCeti.WittRing.signedDiscr`: the signed discriminant of a Witt class.
* `TauCeti.signedDiscrHom`: its restriction to `I(K)`. This map is semilinear along the
  dimension-mod-two map `W(K) → ZMod 2`.
* `TauCeti.fundamentalIdealCotangentEquiv`: the isomorphism `I(K)/I(K)² ≃+ Kˣ/(Kˣ)²`.

## Main results

* `TauCeti.WittRing.signedDiscr_wittClass`: `d±` of the Witt class of a form is `d±` of the form.
* `TauCeti.WittRing.signedDiscr_add`: the correction term for `d±` of a sum of Witt classes.
* `TauCeti.WittRing.signedDiscr_add_of_mem_fundamentalIdeal`: the correction term vanishes once
  one summand lies in `I(K)`.
* `TauCeti.WittRing.signedDiscr_oneFoldPfisterClass`: `d±⟨⟨a⟩⟩` is the square class of `a`.
* `TauCeti.mem_fundamentalIdeal_sq_iff`: `I(K)²` consists of the classes in `I(K)` with trivial
  signed discriminant.
* `TauCeti.wittClass_mem_fundamentalIdeal_sq_iff`: a form has Witt class in `I(K)²` exactly when
  it has even rank and trivial signed discriminant.
* `TauCeti.oneFoldPfisterClass_eq_zero_iff`: `⟨⟨a⟩⟩ = 0` in `W(K)` exactly when `a` is a square.
* `TauCeti.signedDiscrHom_surjective` and `TauCeti.signedDiscrHom_eq_zero_iff`: `d±` maps `I(K)`
  onto the square-class group with kernel `I(K)²`.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter II, §2, where the
  signed discriminant is shown to induce `I/I² ≅ Kˣ/(Kˣ)²`.
-/

public section

open QuadraticMap QuadraticForm

namespace TauCeti

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-! ### The signed discriminant of a Witt class -/

namespace WittRing

/-- **The signed discriminant of a Witt class**: `d±` of any form representing it. This is well
defined because adding a hyperbolic plane does not change `d±`; see
`TauCeti.WittRing.signedDiscr_wittClass`. -/
noncomputable def signedDiscr (x : WittRing K) : SquareClassGroup K :=
  RegularFormClass.signedDiscr (Function.surjInv wittClass_surjective x)

/-- The signed discriminant of the Witt class of a form is the signed discriminant of the form. -/
@[simp]
theorem signedDiscr_wittClass (x : RegularFormClass K) :
    signedDiscr (wittClass x) = RegularFormClass.signedDiscr x := by
  obtain ⟨m, n, h⟩ := wittClass_eq_iff_exists_nsmul.mp
    (Function.surjInv_eq wittClass_surjective (wittClass x))
  rw [signedDiscr, ← RegularFormClass.signedDiscr_nsmul_hyperbolicClass_add m, h,
    RegularFormClass.signedDiscr_nsmul_hyperbolicClass_add]

/-- The zero Witt class has trivial signed discriminant. -/
@[simp]
theorem signedDiscr_zero : signedDiscr (0 : WittRing K) = 0 := by
  rw [← map_zero (wittClass (K := K)), signedDiscr_wittClass, RegularFormClass.signedDiscr_zero]

/-- The Witt class of `⟨1⟩` has trivial signed discriminant. -/
@[simp]
theorem signedDiscr_one : signedDiscr (1 : WittRing K) = 0 := by
  rw [← map_one (wittClass (K := K)), signedDiscr_wittClass, RegularFormClass.signedDiscr_one]

/-- **The signed discriminant of a sum of Witt classes**: the correction term is the product of
their dimensions modulo two, times the square class of `-1`. -/
theorem signedDiscr_add (x y : WittRing K) :
    signedDiscr (x + y) =
      (dimMod2 x * dimMod2 y) • squareClass (-1 : Kˣ) + signedDiscr x + signedDiscr y := by
  obtain ⟨q, rfl⟩ := wittClass_surjective x
  obtain ⟨r, rfl⟩ := wittClass_surjective y
  rw [← map_add, signedDiscr_wittClass, signedDiscr_wittClass, signedDiscr_wittClass,
    RegularFormClass.signedDiscr_add, dimMod2_wittClass, dimMod2_wittClass, ← Nat.cast_mul,
    Nat.cast_smul_eq_nsmul]

/-- **The signed discriminant is additive on the fundamental ideal**:
`d±(x + y) = d±(x) + d±(y)` as soon as `x` has even dimension. -/
@[simp]
theorem signedDiscr_add_of_mem_fundamentalIdeal {x : WittRing K} (hx : x ∈ fundamentalIdeal K)
    (y : WittRing K) : signedDiscr (x + y) = signedDiscr x + signedDiscr y := by
  rw [signedDiscr_add, mem_fundamentalIdeal_iff.mp hx, zero_mul, zero_smul,
    zero_add (M := SquareClassGroup K)]

/-- On the fundamental ideal the signed discriminant is invariant under negation. -/
@[simp]
theorem signedDiscr_neg_of_mem_fundamentalIdeal {x : WittRing K} (hx : x ∈ fundamentalIdeal K) :
    signedDiscr (-x) = signedDiscr x := by
  have h := signedDiscr_add_of_mem_fundamentalIdeal hx (-x)
  rw [add_neg_cancel, signedDiscr_zero] at h
  calc signedDiscr (-x) = signedDiscr x + (signedDiscr x + signedDiscr (-x)) := by
        rw [← add_assoc, ZModModule.add_self, zero_add (M := SquareClassGroup K)]
    _ = signedDiscr x := by rw [← h, add_zero (M := SquareClassGroup K)]

/-- On the fundamental ideal the signed discriminant commutes with natural multiples. -/
theorem signedDiscr_nsmul_of_mem_fundamentalIdeal (n : ℕ) {x : WittRing K}
    (hx : x ∈ fundamentalIdeal K) : signedDiscr (n • x) = n • signedDiscr x := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, signedDiscr_zero]
  | succ n ih =>
    rw [succ_nsmul, add_comm, signedDiscr_add_of_mem_fundamentalIdeal hx, ih, succ_nsmul,
      add_comm]

/-- **The signed discriminant of a one-fold Pfister class**: `d±⟨⟨a⟩⟩ = d±⟨1, -a⟩` is the square
class of `a`. -/
@[simp]
theorem signedDiscr_oneFoldPfisterClass (a : Kˣ) :
    signedDiscr (oneFoldPfisterClass a) = squareClass a := by
  rw [oneFoldPfisterClass_eq, ← map_one (wittClass (K := K)), ← map_add, signedDiscr_wittClass,
    RegularFormClass.signedDiscr_add,
    RegularFormClass.signedDiscr_one, RegularFormClass.signedDiscr_mk_rankOne,
    RegularFormClass.rank_one, RegularFormClass.rank_mk, one_mul, one_nsmul,
    add_zero (M := SquareClassGroup K),
    ← squareClass_mul, neg_one_mul, neg_neg]

/-- The signed discriminant of a two-fold Pfister class `⟨⟨a, b⟩⟩` is trivial. -/
theorem signedDiscr_oneFoldPfisterClass_mul (a b : Kˣ) :
    signedDiscr (oneFoldPfisterClass a * oneFoldPfisterClass b) = 0 := by
  have hab : oneFoldPfisterClass a * oneFoldPfisterClass b =
      oneFoldPfisterClass a + oneFoldPfisterClass b + -oneFoldPfisterClass (a * b) := by
    rw [oneFoldPfisterClass_mul]
    abel
  have hmem := oneFoldPfisterClass_mem_fundamentalIdeal (K := K)
  rw [hab, signedDiscr_add_of_mem_fundamentalIdeal (add_mem (hmem a) (hmem b)),
    signedDiscr_add_of_mem_fundamentalIdeal (hmem a),
    signedDiscr_neg_of_mem_fundamentalIdeal (hmem _), signedDiscr_oneFoldPfisterClass,
    signedDiscr_oneFoldPfisterClass, signedDiscr_oneFoldPfisterClass, squareClass_mul,
    ZModModule.add_self (squareClass a + squareClass b)]

/-- **The signed discriminant vanishes on `I(K)²`.** The two-fold Pfister classes additively
generate `I(K)²` and have trivial signed discriminant, and `d±` is additive on `I(K)`. -/
theorem signedDiscr_eq_zero_of_mem_fundamentalIdeal_sq {x : WittRing K}
    (hx : x ∈ fundamentalIdeal K ^ 2) : signedDiscr x = 0 := by
  have hI : ∀ z ∈ AddSubgroup.closure (Set.range (pfisterClass (K := K) (n := 2))),
      z ∈ fundamentalIdeal K := fun z hz => by
    rw [← fundamentalIdeal_sq_eq_addClosure, Submodule.mem_toAddSubgroup] at hz
    exact Ideal.pow_le_self two_ne_zero hz
  have hx' : x ∈ AddSubgroup.closure (Set.range (pfisterClass (K := K) (n := 2))) := by
    rw [← fundamentalIdeal_sq_eq_addClosure, Submodule.mem_toAddSubgroup]
    exact hx
  clear hx
  induction hx' using AddSubgroup.closure_induction with
  | mem _ h =>
    obtain ⟨a, rfl⟩ := h
    rw [pfisterClass_eq_prod, Fin.prod_univ_two, signedDiscr_oneFoldPfisterClass_mul]
  | zero => exact signedDiscr_zero
  | add x y hx hy ihx ihy =>
    rw [signedDiscr_add_of_mem_fundamentalIdeal (hI x hx), ihx, ihy,
      add_zero (M := SquareClassGroup K)]
  | neg x hx ih => rw [signedDiscr_neg_of_mem_fundamentalIdeal (hI x hx), ih]

/-- **The signed discriminant is semilinear on the fundamental ideal**: for `x ∈ I(K)`,
`d±(w x) = dim(w) • d±(x)`, with the dimension of `w` read modulo two. -/
@[simp]
theorem signedDiscr_mul_of_mem_fundamentalIdeal (w : WittRing K) {x : WittRing K}
    (hx : x ∈ fundamentalIdeal K) :
    signedDiscr (w * x) = dimMod2 w • signedDiscr x := by
  obtain ⟨q, rfl⟩ := wittClass_surjective w
  set m := RegularFormClass.rank q
  have hw : wittClass q - (m : WittRing K) ∈ fundamentalIdeal K := by
    rw [mem_fundamentalIdeal_iff, map_sub, dimMod2_wittClass, map_natCast, sub_self]
  have hsq : (wittClass q - (m : WittRing K)) * x ∈ fundamentalIdeal K ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hw hx
  have hdecomp : wittClass q * x = (wittClass q - (m : WittRing K)) * x + m • x := by
    rw [nsmul_eq_mul, ← add_mul, sub_add_cancel]
  rw [hdecomp, signedDiscr_add_of_mem_fundamentalIdeal (Ideal.pow_le_self two_ne_zero hsq),
    signedDiscr_eq_zero_of_mem_fundamentalIdeal_sq hsq,
    signedDiscr_nsmul_of_mem_fundamentalIdeal m hx, dimMod2_wittClass, Nat.cast_smul_eq_nsmul]
  exact zero_add (M := SquareClassGroup K) _

end WittRing

/-! ### `I(K)²` is the kernel of the signed discriminant -/

/-- **`⟨⟨a⟩⟩ = ⟨1, -a⟩` vanishes in the Witt ring exactly when `a` is a square.** -/
@[simp]
theorem oneFoldPfisterClass_eq_zero_iff {a : Kˣ} : oneFoldPfisterClass a = 0 ↔ IsSquare a := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← squareClass_eq_zero_iff, ← WittRing.signedDiscr_oneFoldPfisterClass, h,
      WittRing.signedDiscr_zero]
  · have hhyp : 1 + Quotient.mk (regularFormSetoid K) ⟨1, fun _ => -a⟩ = hyperbolicClass K := by
      refine RegularFormClass.eq_hyperbolicClass_of_rank_eq_two_of_discr_eq_neg_one ?_ ?_
      · simp
      · rw [RegularFormClass.discr_add, RegularFormClass.discr_one, RegularFormClass.discr_mk,
          Fin.prod_univ_one, zero_add (M := SquareClassGroup K), squareClass_eq_iff_isSquare_mul]
        dsimp only
        rwa [neg_mul_neg, mul_one]
    rw [oneFoldPfisterClass_eq, ← map_one (wittClass (K := K)), ← map_add, hhyp,
      wittClass_hyperbolicClass]

/-- Every element of `I(K)` is congruent modulo `I(K)²` to a one-fold Pfister class `⟨⟨a⟩⟩`, with
`a` in the square class of its signed discriminant. -/
private theorem exists_sub_oneFoldPfisterClass_mem_sq {x : WittRing K}
    (hx : x ∈ fundamentalIdeal K) :
    ∃ a : Kˣ, squareClass a = WittRing.signedDiscr x ∧
      x - oneFoldPfisterClass a ∈ fundamentalIdeal K ^ 2 := by
  have hmem := oneFoldPfisterClass_mem_fundamentalIdeal (K := K)
  have hprod : ∀ a b : Kˣ, oneFoldPfisterClass a * oneFoldPfisterClass b ∈ fundamentalIdeal K ^ 2 :=
    fun a b => by
      rw [pow_two]
      exact Ideal.mul_mem_mul (hmem a) (hmem b)
  have hI : ∀ z ∈ AddSubgroup.closure (Set.range (oneFoldPfisterClass (K := K))),
      z ∈ fundamentalIdeal K := fun z hz => by
    rwa [← fundamentalIdeal_toAddSubgroup_eq_closure_oneFoldPfisterClass,
      Submodule.mem_toAddSubgroup] at hz
  have hx' : x ∈ AddSubgroup.closure (Set.range (oneFoldPfisterClass (K := K))) := by
    rw [← fundamentalIdeal_toAddSubgroup_eq_closure_oneFoldPfisterClass,
      Submodule.mem_toAddSubgroup]
    exact hx
  clear hx
  induction hx' using AddSubgroup.closure_induction with
  | mem _ h =>
    obtain ⟨a, rfl⟩ := h
    exact ⟨a, (WittRing.signedDiscr_oneFoldPfisterClass a).symm, by
      rw [sub_self]
      exact zero_mem _⟩
  | zero =>
    exact ⟨1, by simp, by simp⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨a, ha, hxa⟩ := ihx
    obtain ⟨b, hb, hyb⟩ := ihy
    refine ⟨a * b, ?_, ?_⟩
    · rw [WittRing.signedDiscr_add_of_mem_fundamentalIdeal (hI x hx), squareClass_mul, ha, hb]
    · have hdecomp : x + y - oneFoldPfisterClass (a * b) =
          (x - oneFoldPfisterClass a) + (y - oneFoldPfisterClass b) +
            oneFoldPfisterClass a * oneFoldPfisterClass b := by
        rw [oneFoldPfisterClass_mul]
        abel
      rw [hdecomp]
      exact add_mem (add_mem hxa hyb) (hprod a b)
  | neg x hx ih =>
    obtain ⟨a, ha, hxa⟩ := ih
    refine ⟨a, by rw [WittRing.signedDiscr_neg_of_mem_fundamentalIdeal (hI x hx), ha], ?_⟩
    -- `2 • ⟨⟨a⟩⟩ = ⟨⟨-1⟩⟩ ⟨⟨a⟩⟩` lies in `I(K)²`, so `-⟨⟨a⟩⟩ ≡ ⟨⟨a⟩⟩`.
    have hdecomp : -x - oneFoldPfisterClass a =
        -(x - oneFoldPfisterClass a) - oneFoldPfisterClass (-1) * oneFoldPfisterClass a := by
      rw [oneFoldPfisterClass_neg_one, smul_mul_assoc, one_mul]
      abel
    rw [hdecomp]
    exact sub_mem (neg_mem hxa) (hprod (-1) a)

/-- **The description of `I(K)²` by the signed discriminant**: a Witt class lies in `I(K)²`
exactly when it lies in `I(K)` and has trivial signed discriminant. -/
@[simp]
theorem mem_fundamentalIdeal_sq_iff {x : WittRing K} :
    x ∈ fundamentalIdeal K ^ 2 ↔
      x ∈ fundamentalIdeal K ∧ WittRing.signedDiscr x = 0 := by
  refine ⟨fun hx => ⟨Ideal.pow_le_self two_ne_zero hx,
    WittRing.signedDiscr_eq_zero_of_mem_fundamentalIdeal_sq hx⟩, fun ⟨hx, hd⟩ => ?_⟩
  obtain ⟨a, ha, hxa⟩ := exists_sub_oneFoldPfisterClass_mem_sq hx
  rw [hd, squareClass_eq_zero_iff, ← oneFoldPfisterClass_eq_zero_iff] at ha
  rwa [ha, sub_zero] at hxa

/-- **A form has Witt class in `I(K)²` exactly when it has even rank and trivial signed
discriminant.** -/
theorem wittClass_mem_fundamentalIdeal_sq_iff (q : RegularFormClass K) :
    wittClass q ∈ fundamentalIdeal K ^ 2 ↔
      Even (RegularFormClass.rank q) ∧ RegularFormClass.signedDiscr q = 0 := by
  rw [mem_fundamentalIdeal_sq_iff, wittClass_mem_fundamentalIdeal_iff,
    WittRing.signedDiscr_wittClass]

/-- A one-fold Pfister class `⟨⟨a⟩⟩` lies in `I(K)²` exactly when `a` is a square, in which case
it is already zero. -/
theorem oneFoldPfisterClass_mem_fundamentalIdeal_sq_iff {a : Kˣ} :
    oneFoldPfisterClass a ∈ fundamentalIdeal K ^ 2 ↔ IsSquare a := by
  rw [mem_fundamentalIdeal_sq_iff, WittRing.signedDiscr_oneFoldPfisterClass,
    squareClass_eq_zero_iff, and_iff_right (oneFoldPfisterClass_mem_fundamentalIdeal a)]

/-! ### The isomorphism `I(K)/I(K)² ≅ Kˣ/(Kˣ)²` -/

/-- **The signed discriminant on the fundamental ideal**, as a map `I(K) → Kˣ/(Kˣ)²` that is
semilinear along the dimension-mod-two map `W(K) → ZMod 2`. Its kernel is `I(K)²`, by
`TauCeti.signedDiscrHom_eq_zero_iff`, and it is surjective, by
`TauCeti.signedDiscrHom_surjective`. -/
noncomputable def signedDiscrHom :
    fundamentalIdeal K →ₛₗ[WittRing.dimMod2 (K := K)] SquareClassGroup K where
  toFun x := WittRing.signedDiscr (x : WittRing K)
  map_add' x y := WittRing.signedDiscr_add_of_mem_fundamentalIdeal x.2 y
  map_smul' w x := WittRing.signedDiscr_mul_of_mem_fundamentalIdeal w x.2

/-- `signedDiscrHom` evaluates the signed discriminant. -/
@[simp]
theorem signedDiscrHom_apply (x : fundamentalIdeal K) :
    signedDiscrHom x = WittRing.signedDiscr (x : WittRing K) :=
  (rfl)

/-- The signed discriminant maps the one-fold Pfister class `⟨⟨a⟩⟩` to the square class of `a`;
in particular it maps `I(K)` onto the square-class group. -/
theorem signedDiscrHom_surjective : Function.Surjective (signedDiscrHom (K := K)) := by
  intro s
  induction s using QuotientAddGroup.induction_on with
  | H a =>
    refine ⟨⟨oneFoldPfisterClass (Additive.toMul a), oneFoldPfisterClass_mem_fundamentalIdeal _⟩,
      ?_⟩
    rw [signedDiscrHom_apply, WittRing.signedDiscr_oneFoldPfisterClass, squareClass_def,
      ofMul_toMul]

/-- **The kernel of the signed discriminant on `I(K)` is `I(K)²`.** -/
theorem signedDiscrHom_eq_zero_iff (x : fundamentalIdeal K) :
    signedDiscrHom x = 0 ↔ (x : WittRing K) ∈ fundamentalIdeal K ^ 2 := by
  rw [signedDiscrHom_apply, mem_fundamentalIdeal_sq_iff, and_iff_right x.2]

/-- The signed discriminant, descended to the cotangent space `I(K)/I(K)²`. -/
private noncomputable def cotangentSignedDiscr :
    (fundamentalIdeal K).Cotangent →ₛₗ[WittRing.dimMod2 (K := K)] SquareClassGroup K :=
  Submodule.liftQ _ signedDiscrHom fun x hx => by
    rw [LinearMap.mem_ker, signedDiscrHom_eq_zero_iff, ← Ideal.toCotangent_eq_zero,
      Ideal.toCotangent_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hx

private theorem cotangentSignedDiscr_toCotangent (x : fundamentalIdeal K) :
    cotangentSignedDiscr ((fundamentalIdeal K).toCotangent x) =
      WittRing.signedDiscr (x : WittRing K) := by
  -- `Ideal.Cotangent` is by definition the quotient `I ⧸ I • ⊤` that `Submodule.liftQ` descends
  -- to, so `rw` cannot see `Submodule.liftQ_apply` through the `Cotangent` type; `exact` can.
  rw [cotangentSignedDiscr, Ideal.toCotangent_apply]
  exact Submodule.liftQ_apply _ _ _

/-- **`I(K)/I(K)² ≅ Kˣ/(Kˣ)²`**: the signed discriminant induces an isomorphism from the cotangent
space `I(K)/I(K)²` of the fundamental ideal onto the square-class group. -/
noncomputable def fundamentalIdealCotangentEquiv :
    (fundamentalIdeal K).Cotangent ≃+ SquareClassGroup K :=
  AddEquiv.ofBijective (cotangentSignedDiscr (K := K)).toAddMonoidHom
    ⟨(injective_iff_map_eq_zero _).mpr fun x hx => by
      obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ x
      rw [LinearMap.toAddMonoidHom_coe, cotangentSignedDiscr_toCotangent, ← signedDiscrHom_apply,
        signedDiscrHom_eq_zero_iff] at hx
      rwa [Ideal.toCotangent_eq_zero],
    fun s => by
      obtain ⟨x, rfl⟩ := signedDiscrHom_surjective s
      exact ⟨(fundamentalIdeal K).toCotangent x, by
        rw [LinearMap.toAddMonoidHom_coe, cotangentSignedDiscr_toCotangent,
          signedDiscrHom_apply]⟩⟩

/-- The isomorphism `I(K)/I(K)² ≅ Kˣ/(Kˣ)²` sends the class of `x ∈ I(K)` to `d±(x)`. -/
@[simp]
theorem fundamentalIdealCotangentEquiv_toCotangent (x : fundamentalIdeal K) :
    fundamentalIdealCotangentEquiv ((fundamentalIdeal K).toCotangent x) =
      WittRing.signedDiscr (x : WittRing K) := by
  exact (AddEquiv.ofBijective_apply _ _ _).trans (cotangentSignedDiscr_toCotangent x)

/-- The inverse isomorphism `Kˣ/(Kˣ)² ≅ I(K)/I(K)²` sends the square class of `a` to the class
of the one-fold Pfister form `⟨⟨a⟩⟩`. -/
@[simp]
theorem fundamentalIdealCotangentEquiv_symm_squareClass (a : Kˣ) :
    fundamentalIdealCotangentEquiv.symm (squareClass a) =
      (fundamentalIdeal K).toCotangent
        ⟨oneFoldPfisterClass a, oneFoldPfisterClass_mem_fundamentalIdeal a⟩ := by
  rw [AddEquiv.symm_apply_eq, fundamentalIdealCotangentEquiv_toCotangent,
    WittRing.signedDiscr_oneFoldPfisterClass]

end TauCeti
