/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Pre-λ structures

A *pre-λ structure* on a commutative ring `R` is a sequence of operations `λⁿ : R → R` with
`λ⁰ x = 1`, `λ¹ x = x` and the sum law

```text
λⁿ (x + y) = ∑ i + j = n, λⁱ x * λʲ y.
```

Equivalently, the *total operation* `λ_t x = ∑ₙ λⁿ x tⁿ` is a homomorphism from the additive
group of `R` to the multiplicative monoid of `R⟦t⟧`, taking values in power series with constant
coefficient `1` and linear coefficient `x`. In Grothendieck's terminology these are
"λ-rings"; the stronger notion, with the universal product and iteration identities, is that of
a *special* λ-ring. Pre-λ structures are the common carrier of the binomial structure on a
binomial ring, of the exterior-power operations on `K₀`, and of the line-monomial structure on a
monoid algebra.

A ring can carry several pre-λ structures (for instance `ℤ` carries both the binomial structure
`λ_t m = (1 + t)ᵐ` and `λ_t m = (1 + t + t²)ᵐ`), so a pre-λ structure is a bundled structure
rather than a class.

## Main definitions

* `TauCeti.PreLambdaStructure R`: pre-λ structures on `R`.
* `TauCeti.PreLambdaStructure.totalSeries`: the total operation `λ_t x`.
* `TauCeti.PreLambdaStructure.totalHom`: the total operation as a monoid homomorphism
  `Multiplicative R →* R⟦X⟧`, and `TauCeti.PreLambdaStructure.ofTotalHom`, its inverse
  construction; `TauCeti.PreLambdaStructure.equivTotalHom` identifies the two descriptions.
* `TauCeti.PreLambdaStructure.IsLine`: line elements, those with `λ_t l = 1 + l t`.
* `TauCeti.PreLambdaHom`: ring homomorphisms commuting with every `λⁿ`.
* `TauCeti.PreLambdaStructure.IsLambdaIdeal`: ideals stable under the positive operations, and
  `TauCeti.PreLambdaStructure.quotient`, the induced structure on the quotient ring, with
  `TauCeti.PreLambdaStructure.quotientLift`, its universal property.
* `TauCeti.PreLambdaStructure.IsLambdaSubring`: subrings stable under every operation, and
  `TauCeti.PreLambdaStructure.restrict`, the induced structure on such a subring, with
  `TauCeti.PreLambdaHom.codRestrict`, its universal property.

## Main results

* `TauCeti.PreLambdaStructure.totalSeries_add`: the total operation turns sums into products.
* `TauCeti.PreLambdaStructure.lambda_apply_zero` and `TauCeti.PreLambdaStructure.totalSeries_neg`:
  the zero formula `λ_t 0 = 1` and the virtual-negative formula `λ_t (-x) = (λ_t x)⁻¹`.
* `TauCeti.PreLambdaHom.isLambdaIdeal_ker`: kernels of morphisms are λ-ideals.
* `TauCeti.PreLambdaStructure.eq_of_surjective` and
  `TauCeti.PreLambdaStructure.eq_of_injective`: uniqueness of the quotient and restricted
  structures.

## References

* C. A. Weibel, *The K-book*, §II.4.
* D. Yau, *Lambda-rings*, Chapter 1.
-/

public noncomputable section

open PowerSeries

namespace TauCeti

/-- A pre-λ structure on a commutative ring `R`: operations `λⁿ : R → R` with `λ⁰ x = 1`,
`λ¹ x = x` and `λⁿ (x + y) = ∑ i + j = n, λⁱ x * λʲ y`. -/
@[ext]
structure PreLambdaStructure (R : Type*) [CommRing R] where
  /-- The `n`th λ-operation `λⁿ`. -/
  lambda : ℕ → R → R
  lambda_zero (x : R) : lambda 0 x = 1
  lambda_one (x : R) : lambda 1 x = x
  lambda_add (n : ℕ) (x y : R) :
    lambda n (x + y) = ∑ p ∈ Finset.antidiagonal n, lambda p.1 x * lambda p.2 y

namespace PreLambdaStructure

attribute [simp] lambda_zero lambda_one

variable {R S : Type*} [CommRing R] [CommRing S]
variable (Λ : PreLambdaStructure R)

/-! ### The total operation -/

/-- The total operation `λ_t x = ∑ₙ λⁿ x tⁿ`. -/
def totalSeries (x : R) : R⟦X⟧ :=
  PowerSeries.mk fun n => Λ.lambda n x

@[simp]
theorem coeff_totalSeries (n : ℕ) (x : R) : coeff n (Λ.totalSeries x) = Λ.lambda n x :=
  coeff_mk _ _

@[simp]
theorem constantCoeff_totalSeries (x : R) : constantCoeff (Λ.totalSeries x) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_totalSeries, lambda_zero]

theorem coeff_one_totalSeries (x : R) : coeff 1 (Λ.totalSeries x) = x := by
  simp

theorem isUnit_totalSeries (x : R) : IsUnit (Λ.totalSeries x) :=
  isUnit_iff_constantCoeff.2 (by simp)

/-- The sum law: the total operation turns sums into products. -/
theorem totalSeries_add (x y : R) :
    Λ.totalSeries (x + y) = Λ.totalSeries x * Λ.totalSeries y := by
  ext n
  simp [coeff_mul, Λ.lambda_add]

/-- The zero formula, in series form. -/
@[simp]
theorem totalSeries_zero : Λ.totalSeries 0 = 1 := by
  have h := Λ.totalSeries_add 0 0
  rw [add_zero] at h
  exact (Λ.isUnit_totalSeries 0).mul_left_cancel (h.symm.trans (mul_one _).symm)

/-- The zero formula: `λ⁰ 0 = 1` and `λⁿ 0 = 0` for `n ≠ 0`. -/
@[simp]
theorem lambda_apply_zero (n : ℕ) : Λ.lambda n 0 = if n = 0 then 1 else 0 := by
  rw [← coeff_totalSeries, totalSeries_zero, coeff_one]

theorem lambda_apply_zero_of_ne_zero {n : ℕ} (hn : n ≠ 0) : Λ.lambda n 0 = 0 := by
  simp [lambda_apply_zero, hn]

theorem totalSeries_neg_mul (x : R) : Λ.totalSeries (-x) * Λ.totalSeries x = 1 := by
  rw [← totalSeries_add, neg_add_cancel, totalSeries_zero]

theorem totalSeries_mul_neg (x : R) : Λ.totalSeries x * Λ.totalSeries (-x) = 1 := by
  rw [mul_comm, totalSeries_neg_mul]

/-- The virtual-negative formula: `λ_t (-x)` is the inverse of `λ_t x`. -/
theorem totalSeries_neg (x : R) : Λ.totalSeries (-x) = invOfUnit (Λ.totalSeries x) 1 := by
  rw [← mul_one (Λ.totalSeries (-x)), ← mul_invOfUnit (Λ.totalSeries x) 1 (by simp), ← mul_assoc,
    totalSeries_neg_mul, one_mul]

/-- The sum law with the term `λⁿ x * λ⁰ y` separated from the others. -/
theorem lambda_add_eq_add_sum (n : ℕ) (x y : R) :
    Λ.lambda n (x + y) =
      Λ.lambda n x + ∑ p ∈ Finset.antidiagonal n with p.2 ≠ 0, Λ.lambda p.1 x * Λ.lambda p.2 y := by
  rw [Λ.lambda_add, ← Finset.sum_filter_not_add_sum_filter _ (fun p => p.2 ≠ 0), add_left_inj,
    Finset.sum_eq_single_of_mem ((n, 0) : ℕ × ℕ) (by simp)]
  · simp
  · rintro ⟨i, j⟩ hij hne
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, not_not] at hij
    obtain ⟨hij, rfl⟩ := hij
    simp_all

/-- The virtual-negative formula in coefficient form: for `n ≠ 0`, `λⁿ (-x)` is determined
recursively by the lower operations on `-x` and the operations on `x`. -/
theorem lambda_neg_of_ne_zero {n : ℕ} (hn : n ≠ 0) (x : R) :
    Λ.lambda n (-x) =
      -∑ p ∈ Finset.antidiagonal n with p.2 ≠ 0, Λ.lambda p.1 (-x) * Λ.lambda p.2 x := by
  have h := Λ.lambda_add_eq_add_sum n (-x) x
  rw [neg_add_cancel, Λ.lambda_apply_zero_of_ne_zero hn] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem totalSeries_sub (x y : R) :
    Λ.totalSeries (x - y) = Λ.totalSeries x * invOfUnit (Λ.totalSeries y) 1 := by
  rw [sub_eq_add_neg, totalSeries_add, totalSeries_neg]

/-- The total operation as a homomorphism from the additive group of `R`, written
multiplicatively, to the multiplicative monoid of `R⟦X⟧`. -/
def totalHom : Multiplicative R →* R⟦X⟧ where
  toFun x := Λ.totalSeries x.toAdd
  map_one' := Λ.totalSeries_zero
  map_mul' x y := Λ.totalSeries_add x.toAdd y.toAdd

@[simp]
theorem totalHom_apply (x : Multiplicative R) : Λ.totalHom x = Λ.totalSeries x.toAdd :=
  (rfl)

theorem totalSeries_sum {ι : Type*} (s : Finset ι) (f : ι → R) :
    Λ.totalSeries (∑ i ∈ s, f i) = ∏ i ∈ s, Λ.totalSeries (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.prod_cons, totalSeries_add, ih]

theorem totalSeries_nsmul (n : ℕ) (x : R) : Λ.totalSeries (n • x) = Λ.totalSeries x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, totalSeries_add, ih, pow_succ]

/-- The pre-λ structure with a prescribed total operation: a monoid homomorphism
`Multiplicative R →* R⟦X⟧` whose values have constant coefficient `1` and linear coefficient
the argument. -/
def ofTotalHom (f : Multiplicative R →* R⟦X⟧) (h₀ : ∀ x, constantCoeff (f x) = 1)
    (h₁ : ∀ x, coeff 1 (f x) = x.toAdd) : PreLambdaStructure R where
  lambda n x := coeff n (f (Multiplicative.ofAdd x))
  lambda_zero x := by rw [coeff_zero_eq_constantCoeff_apply, h₀]
  lambda_one x := h₁ _
  lambda_add n x y := by rw [ofAdd_add, map_mul, coeff_mul]

@[simp]
theorem ofTotalHom_lambda (f : Multiplicative R →* R⟦X⟧) (h₀ : ∀ x, constantCoeff (f x) = 1)
    (h₁ : ∀ x, coeff 1 (f x) = x.toAdd) (n : ℕ) (x : R) :
    (ofTotalHom f h₀ h₁).lambda n x = coeff n (f (Multiplicative.ofAdd x)) :=
  (rfl)

@[simp]
theorem totalHom_ofTotalHom (f : Multiplicative R →* R⟦X⟧) (h₀ : ∀ x, constantCoeff (f x) = 1)
    (h₁ : ∀ x, coeff 1 (f x) = x.toAdd) : (ofTotalHom f h₀ h₁).totalHom = f := by
  refine MonoidHom.ext fun x => ?_
  ext n
  simp

@[simp]
theorem ofTotalHom_totalHom :
    ofTotalHom Λ.totalHom (fun x => by simp) (fun x => by simp) = Λ := by
  ext n x
  simp

/-- Pre-λ structures on `R` are the same as their total operations: monoid homomorphisms
`Multiplicative R →* R⟦X⟧` with values of constant coefficient `1` and linear coefficient the
argument. -/
def equivTotalHom : PreLambdaStructure R ≃
    {f : Multiplicative R →* R⟦X⟧ // ∀ x, constantCoeff (f x) = 1 ∧ coeff 1 (f x) = x.toAdd} where
  toFun Λ := ⟨Λ.totalHom, fun x => by simp⟩
  invFun f := ofTotalHom f.val (fun x => (f.property x).1) (fun x => (f.property x).2)
  left_inv Λ := Λ.ofTotalHom_totalHom
  right_inv f := Subtype.ext (totalHom_ofTotalHom _ _ _)

@[simp]
theorem coe_equivTotalHom_apply : (equivTotalHom Λ : Multiplicative R →* R⟦X⟧) = Λ.totalHom :=
  (rfl)

@[simp]
theorem equivTotalHom_symm_apply
    (f : {f : Multiplicative R →* R⟦X⟧ // ∀ x, constantCoeff (f x) = 1 ∧ coeff 1 (f x) = x.toAdd}) :
    equivTotalHom.symm f =
      ofTotalHom f.val (fun x => (f.property x).1) (fun x => (f.property x).2) :=
  (rfl)

/-! ### Line elements -/

/-- A line element of a pre-λ structure: an element `l` with `λ_t l = 1 + l t`, that is
`λⁿ l = 0` for `n ≥ 2`. A line element need not be a unit. -/
def IsLine (l : R) : Prop :=
  ∀ n, 2 ≤ n → Λ.lambda n l = 0

theorem isLine_iff {l : R} : Λ.IsLine l ↔ ∀ n, 2 ≤ n → Λ.lambda n l = 0 :=
  Iff.rfl

variable {Λ} in
theorem IsLine.lambda_eq_zero {l : R} (h : Λ.IsLine l) {n : ℕ} (hn : 2 ≤ n) :
    Λ.lambda n l = 0 :=
  h n hn

theorem isLine_iff_totalSeries {l : R} : Λ.IsLine l ↔ Λ.totalSeries l = 1 + C l * X := by
  refine ⟨fun h => ?_, fun h n hn => ?_⟩
  · ext n
    rcases n with _ | _ | n
    · simp
    · simp
    · simp [coeff_one, h (n + 2) (by omega)]
  · have := congrArg (coeff n) h
    rw [coeff_totalSeries] at this
    rw [this, map_add, coeff_one, coeff_C_mul, coeff_X]
    simp [show n ≠ 0 by omega, show n ≠ 1 by omega]

variable {Λ} in
theorem IsLine.totalSeries_eq {l : R} (h : Λ.IsLine l) : Λ.totalSeries l = 1 + C l * X :=
  Λ.isLine_iff_totalSeries.1 h

/-- `0` is a line element. -/
@[simp]
theorem isLine_zero : Λ.IsLine 0 := fun _ hn => Λ.lambda_apply_zero_of_ne_zero (by omega)

/-! ### Uniqueness of induced structures -/

/-- A pre-λ structure on the target of a surjective ring homomorphism is determined by the
requirement that the homomorphism commute with every `λⁿ`. -/
theorem eq_of_surjective {Λ₁ Λ₂ : PreLambdaStructure S} (f : R →+* S)
    (hf : Function.Surjective f) (h₁ : ∀ n x, f (Λ.lambda n x) = Λ₁.lambda n (f x))
    (h₂ : ∀ n x, f (Λ.lambda n x) = Λ₂.lambda n (f x)) : Λ₁ = Λ₂ := by
  ext n y
  obtain ⟨x, rfl⟩ := hf y
  rw [← h₁, h₂]

/-- A pre-λ structure on the source of an injective ring homomorphism is determined by the
requirement that the homomorphism commute with every `λⁿ`. -/
theorem eq_of_injective {Λ₁ Λ₂ : PreLambdaStructure R} (Λ : PreLambdaStructure S) (f : R →+* S)
    (hf : Function.Injective f) (h₁ : ∀ n x, f (Λ₁.lambda n x) = Λ.lambda n (f x))
    (h₂ : ∀ n x, f (Λ₂.lambda n x) = Λ.lambda n (f x)) : Λ₁ = Λ₂ := by
  ext n x
  exact hf ((h₁ n x).trans (h₂ n x).symm)

/-! ### Structures and morphisms determined on additive generators -/

/-- If a ring homomorphism carries the total operation of `Λ` to that of `Λ'` on a set
generating `R` as an additive group, then it does so everywhere. -/
theorem map_totalSeries_eq_of_closure {Λ' : PreLambdaStructure S} (f : R →+* S) {s : Set R}
    (hs : AddSubgroup.closure s = ⊤)
    (h : ∀ x ∈ s, PowerSeries.map f (Λ.totalSeries x) = Λ'.totalSeries (f x)) (x : R) :
    PowerSeries.map f (Λ.totalSeries x) = Λ'.totalSeries (f x) := by
  have hx : x ∈ AddSubgroup.closure s := hs ▸ AddSubgroup.mem_top x
  induction hx using AddSubgroup.closure_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ hx hy => rw [totalSeries_add, map_mul, hx, hy, map_add, totalSeries_add]
  | neg x _ hx =>
    refine (Λ'.isUnit_totalSeries (f x)).mul_right_cancel ?_
    rw [map_neg, Λ'.totalSeries_neg_mul, ← hx, ← map_mul, totalSeries_neg_mul, map_one]

/-- Two pre-λ structures whose total operations agree on a set generating `R` as an additive
group are equal. -/
theorem ext_of_closure {Λ₁ Λ₂ : PreLambdaStructure R} {s : Set R}
    (hs : AddSubgroup.closure s = ⊤) (h : ∀ x ∈ s, Λ₁.totalSeries x = Λ₂.totalSeries x) :
    Λ₁ = Λ₂ := by
  ext n x
  have := congrArg (coeff n)
    (Λ₁.map_totalSeries_eq_of_closure (RingHom.id R) hs (by simpa [PowerSeries.map_id] using h) x)
  simpa using this

end PreLambdaStructure

/-! ### Morphisms -/

/-- A morphism of pre-λ structures: a ring homomorphism commuting with every `λⁿ`. -/
structure PreLambdaHom {R S : Type*} [CommRing R] [CommRing S] (Λ : PreLambdaStructure R)
    (Λ' : PreLambdaStructure S) extends R →+* S where
  map_lambda' (n : ℕ) (x : R) : toFun (Λ.lambda n x) = Λ'.lambda n (toFun x)

namespace PreLambdaHom

variable {R S T U : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
variable {Λ : PreLambdaStructure R} {Λ' : PreLambdaStructure S} {Λ'' : PreLambdaStructure T}
  {Λ''' : PreLambdaStructure U}

instance : FunLike (PreLambdaHom Λ Λ') R S where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨f, _⟩ := f
    obtain ⟨g, _⟩ := g
    congr
    exact DFunLike.coe_injective h

instance : RingHomClass (PreLambdaHom Λ Λ') R S where
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'

@[simp]
theorem toRingHom_eq_coe (f : PreLambdaHom Λ Λ') : f.toRingHom = (f : R →+* S) :=
  (rfl)

theorem coe_toRingHom (f : PreLambdaHom Λ Λ') : ⇑f.toRingHom = f :=
  (rfl)

@[simp]
theorem coe_mk (f : R →+* S) (h) : ⇑(⟨f, h⟩ : PreLambdaHom Λ Λ') = f :=
  (rfl)

@[ext]
theorem ext {f g : PreLambdaHom Λ Λ'} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

@[simp]
theorem map_lambda (f : PreLambdaHom Λ Λ') (n : ℕ) (x : R) :
    f (Λ.lambda n x) = Λ'.lambda n (f x) :=
  f.map_lambda' n x

theorem map_totalSeries (f : PreLambdaHom Λ Λ') (x : R) :
    PowerSeries.map (f : R →+* S) (Λ.totalSeries x) = Λ'.totalSeries (f x) := by
  ext n
  simp

/-- A ring homomorphism carrying the total operation of `Λ` to that of `Λ'` on a set generating
`R` as an additive group is a morphism of pre-λ structures. -/
def ofClosure (f : R →+* S) {s : Set R} (hs : AddSubgroup.closure s = ⊤)
    (h : ∀ x ∈ s, PowerSeries.map f (Λ.totalSeries x) = Λ'.totalSeries (f x)) :
    PreLambdaHom Λ Λ' where
  __ := f
  map_lambda' n x := by
    simpa using congrArg (coeff n) (Λ.map_totalSeries_eq_of_closure f hs h x)

@[simp]
theorem coe_ofClosure (f : R →+* S) {s : Set R} (hs : AddSubgroup.closure s = ⊤)
    (h : ∀ x ∈ s, PowerSeries.map f (Λ.totalSeries x) = Λ'.totalSeries (f x)) :
    ⇑(ofClosure f hs h) = f :=
  (rfl)

theorem map_isLine (f : PreLambdaHom Λ Λ') {l : R} (h : Λ.IsLine l) : Λ'.IsLine (f l) :=
  fun n hn => by rw [← map_lambda, h n hn, map_zero]

variable (Λ) in
/-- The identity morphism. -/
protected def id : PreLambdaHom Λ Λ where
  __ := RingHom.id R
  map_lambda' _ _ := rfl

@[simp]
theorem coe_id : ⇑(PreLambdaHom.id Λ) = id :=
  (rfl)

/-- The composite of two morphisms. -/
def comp (g : PreLambdaHom Λ' Λ'') (f : PreLambdaHom Λ Λ') : PreLambdaHom Λ Λ'' where
  __ := g.toRingHom.comp f.toRingHom
  map_lambda' n x := by simp

@[simp]
theorem coe_comp (g : PreLambdaHom Λ' Λ'') (f : PreLambdaHom Λ Λ') : ⇑(g.comp f) = g ∘ f :=
  (rfl)

theorem comp_apply (g : PreLambdaHom Λ' Λ'') (f : PreLambdaHom Λ Λ') (x : R) :
    g.comp f x = g (f x) :=
  (rfl)

@[simp]
theorem comp_id (f : PreLambdaHom Λ Λ') : f.comp (PreLambdaHom.id Λ) = f :=
  (rfl)

@[simp]
theorem id_comp (f : PreLambdaHom Λ Λ') : (PreLambdaHom.id Λ').comp f = f :=
  (rfl)

theorem comp_assoc (h : PreLambdaHom Λ'' Λ''') (g : PreLambdaHom Λ' Λ'') (f : PreLambdaHom Λ Λ') :
    (h.comp g).comp f = h.comp (g.comp f) :=
  (rfl)

end PreLambdaHom

namespace PreLambdaStructure

variable {R S : Type*} [CommRing R] [CommRing S]
variable (Λ : PreLambdaStructure R) {Λ' : PreLambdaStructure S}

/-! ### λ-ideals and quotients -/

/-- A λ-ideal: an ideal stable under every positive λ-operation. -/
def IsLambdaIdeal (I : Ideal R) : Prop :=
  ∀ ⦃n : ℕ⦄, n ≠ 0 → ∀ x ∈ I, Λ.lambda n x ∈ I

theorem isLambdaIdeal_iff {I : Ideal R} :
    Λ.IsLambdaIdeal I ↔ ∀ n, n ≠ 0 → ∀ x ∈ I, Λ.lambda n x ∈ I :=
  Iff.rfl

variable {Λ} in
theorem IsLambdaIdeal.lambda_mem {I : Ideal R} (hI : Λ.IsLambdaIdeal I) {n : ℕ} (hn : n ≠ 0)
    {x : R} (hx : x ∈ I) : Λ.lambda n x ∈ I :=
  hI hn x hx

theorem isLambdaIdeal_bot : Λ.IsLambdaIdeal ⊥ := by
  intro n hn x hx
  rw [Ideal.mem_bot.1 hx, Λ.lambda_apply_zero_of_ne_zero hn]
  exact Ideal.zero_mem _

theorem isLambdaIdeal_top : Λ.IsLambdaIdeal ⊤ :=
  fun _ _ _ _ => Submodule.mem_top

variable {Λ} in
/-- The preimage of a λ-ideal under a morphism is a λ-ideal. -/
theorem IsLambdaIdeal.comap {J : Ideal S} (hJ : Λ'.IsLambdaIdeal J) (f : PreLambdaHom Λ Λ') :
    Λ.IsLambdaIdeal (J.comap f) := by
  intro n hn x hx
  rw [Ideal.mem_comap, PreLambdaHom.map_lambda]
  exact hJ hn _ hx

variable {Λ} in
/-- The kernel of a morphism is a λ-ideal. -/
theorem _root_.TauCeti.PreLambdaHom.isLambdaIdeal_ker (f : PreLambdaHom Λ Λ') :
    Λ.IsLambdaIdeal (RingHom.ker f) := by
  rw [RingHom.ker_eq_comap_bot]
  exact Λ'.isLambdaIdeal_bot.comap f

variable {Λ} in
/-- Modulo a λ-ideal, each `λⁿ` respects congruence. -/
theorem IsLambdaIdeal.lambda_sub_mem {I : Ideal R} (hI : Λ.IsLambdaIdeal I) (n : ℕ) {x y : R}
    (h : x - y ∈ I) : Λ.lambda n x - Λ.lambda n y ∈ I := by
  have hx : x = y + (x - y) := by abel
  rw [hx, Λ.lambda_add_eq_add_sum, add_sub_cancel_left]
  refine Submodule.sum_mem _ fun p hp => Ideal.mul_mem_left _ _ (hI ?_ _ h)
  exact (Finset.mem_filter.1 hp).2

/-- The operation `λⁿ` induced on the quotient by a λ-ideal. -/
private def quotientLambda {I : Ideal R} (hI : Λ.IsLambdaIdeal I) (n : ℕ) : R ⧸ I → R ⧸ I :=
  Quotient.map' (Λ.lambda n) fun _ _ h =>
    (Submodule.quotientRel_def I).2 (hI.lambda_sub_mem n ((Submodule.quotientRel_def I).1 h))

private theorem quotientLambda_mk {I : Ideal R} (hI : Λ.IsLambdaIdeal I) (n : ℕ) (x : R) :
    quotientLambda Λ hI n (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (Λ.lambda n x) :=
  (rfl)

/-- The pre-λ structure induced on the quotient by a λ-ideal. -/
def quotient (I : Ideal R) (hI : Λ.IsLambdaIdeal I) : PreLambdaStructure (R ⧸ I) where
  lambda := quotientLambda Λ hI
  lambda_zero z := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [quotientLambda_mk, lambda_zero, map_one]
  lambda_one z := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [quotientLambda_mk, lambda_one]
  lambda_add n z w := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
    rw [← map_add, quotientLambda_mk, lambda_add, map_sum]
    simp only [map_mul, quotientLambda_mk]

@[simp]
theorem quotient_lambda_mk (I : Ideal R) (hI : Λ.IsLambdaIdeal I) (n : ℕ) (x : R) :
    (Λ.quotient I hI).lambda n (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (Λ.lambda n x) :=
  (rfl)

/-- The quotient map by a λ-ideal, as a morphism of pre-λ structures. -/
def quotientMk (I : Ideal R) (hI : Λ.IsLambdaIdeal I) : PreLambdaHom Λ (Λ.quotient I hI) where
  __ := Ideal.Quotient.mk I
  map_lambda' _ _ := rfl

@[simp]
theorem coe_quotientMk (I : Ideal R) (hI : Λ.IsLambdaIdeal I) :
    ⇑(Λ.quotientMk I hI) = Ideal.Quotient.mk I :=
  (rfl)

/-- A morphism vanishing on a λ-ideal factors through the quotient structure. -/
def quotientLift (I : Ideal R) (hI : Λ.IsLambdaIdeal I) (f : PreLambdaHom Λ Λ')
    (hf : ∀ x ∈ I, f x = 0) : PreLambdaHom (Λ.quotient I hI) Λ' where
  __ := Ideal.Quotient.lift I f.toRingHom hf
  map_lambda' n z := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    simp

@[simp]
theorem quotientLift_mk (I : Ideal R) (hI : Λ.IsLambdaIdeal I) (f : PreLambdaHom Λ Λ')
    (hf : ∀ x ∈ I, f x = 0) (x : R) :
    Λ.quotientLift I hI f hf (Ideal.Quotient.mk I x) = f x :=
  (rfl)

@[simp]
theorem quotientLift_comp_quotientMk (I : Ideal R) (hI : Λ.IsLambdaIdeal I)
    (f : PreLambdaHom Λ Λ') (hf : ∀ x ∈ I, f x = 0) :
    (Λ.quotientLift I hI f hf).comp (Λ.quotientMk I hI) = f :=
  (rfl)

variable {Λ} in
/-- Morphisms out of a quotient structure are determined by their composites with the quotient
map. -/
@[ext 1100]
theorem quotient_hom_ext {I : Ideal R} {hI : Λ.IsLambdaIdeal I}
    {f g : PreLambdaHom (Λ.quotient I hI) Λ'}
    (h : f.comp (Λ.quotientMk I hI) = g.comp (Λ.quotientMk I hI)) : f = g := by
  ext z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact congrArg (· x) h

/-- `quotientLift` is the unique morphism out of the quotient structure whose composite with the
quotient map is the given morphism. -/
theorem quotientLift_unique (I : Ideal R) (hI : Λ.IsLambdaIdeal I) (f : PreLambdaHom Λ Λ')
    (hf : ∀ x ∈ I, f x = 0) (g : PreLambdaHom (Λ.quotient I hI) Λ')
    (hg : g.comp (Λ.quotientMk I hI) = f) : g = Λ.quotientLift I hI f hf :=
  quotient_hom_ext (by rw [hg, quotientLift_comp_quotientMk])

/-- The quotient structure is the only pre-λ structure on `R ⧸ I` for which the quotient map
commutes with every `λⁿ`. -/
theorem eq_quotient {I : Ideal R} (hI : Λ.IsLambdaIdeal I) {Λ' : PreLambdaStructure (R ⧸ I)}
    (h : ∀ n x, Ideal.Quotient.mk I (Λ.lambda n x) = Λ'.lambda n (Ideal.Quotient.mk I x)) :
    Λ' = Λ.quotient I hI :=
  Λ.eq_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective h fun _ _ => rfl

/-- An ideal is a λ-ideal exactly when the quotient ring carries a pre-λ structure for which
the quotient map commutes with every `λⁿ`. -/
theorem isLambdaIdeal_iff_exists (I : Ideal R) :
    Λ.IsLambdaIdeal I ↔ ∃ Λ' : PreLambdaStructure (R ⧸ I),
      ∀ n x, Ideal.Quotient.mk I (Λ.lambda n x) = Λ'.lambda n (Ideal.Quotient.mk I x) := by
  refine ⟨fun hI => ⟨Λ.quotient I hI, fun _ _ => rfl⟩, fun ⟨Λ', h⟩ => ?_⟩
  convert PreLambdaHom.isLambdaIdeal_ker (Λ := Λ) ⟨Ideal.Quotient.mk I, h⟩
  ext x
  simp [Ideal.Quotient.eq_zero_iff_mem]

/-! ### λ-subrings -/

/-- A λ-subring: a subring stable under every λ-operation. -/
def IsLambdaSubring (A : Subring R) : Prop :=
  ∀ (n : ℕ), ∀ x ∈ A, Λ.lambda n x ∈ A

theorem isLambdaSubring_iff {A : Subring R} :
    Λ.IsLambdaSubring A ↔ ∀ (n : ℕ), ∀ x ∈ A, Λ.lambda n x ∈ A :=
  Iff.rfl

variable {Λ} in
theorem IsLambdaSubring.lambda_mem {A : Subring R} (hA : Λ.IsLambdaSubring A) (n : ℕ) {x : R}
    (hx : x ∈ A) : Λ.lambda n x ∈ A :=
  hA n x hx

theorem isLambdaSubring_top : Λ.IsLambdaSubring ⊤ :=
  fun _ _ _ => Subring.mem_top _

variable {Λ} in
/-- The range of a morphism is a λ-subring. -/
theorem _root_.TauCeti.PreLambdaHom.isLambdaSubring_range (f : PreLambdaHom Λ Λ') :
    Λ'.IsLambdaSubring (f : R →+* S).range := by
  rintro n _ ⟨x, rfl⟩
  exact ⟨Λ.lambda n x, f.map_lambda n x⟩

variable {Λ} in
/-- The preimage of a λ-subring under a morphism is a λ-subring. -/
theorem IsLambdaSubring.comap {B : Subring S} (hB : Λ'.IsLambdaSubring B)
    (f : PreLambdaHom Λ Λ') : Λ.IsLambdaSubring (B.comap (f : R →+* S)) := by
  intro n x hx
  simpa using hB n _ hx

/-- The pre-λ structure restricted to a λ-subring. -/
def restrict (A : Subring R) (hA : Λ.IsLambdaSubring A) : PreLambdaStructure A where
  lambda n x := ⟨Λ.lambda n x, hA n x x.property⟩
  lambda_zero x := Subtype.ext (Λ.lambda_zero x)
  lambda_one x := Subtype.ext (Λ.lambda_one x)
  lambda_add n x y := Subtype.ext <| by simp [Λ.lambda_add]

@[simp]
theorem coe_restrict_lambda (A : Subring R) (hA : Λ.IsLambdaSubring A) (n : ℕ) (x : A) :
    ((Λ.restrict A hA).lambda n x : R) = Λ.lambda n x :=
  (rfl)

/-- The inclusion of a λ-subring, as a morphism of pre-λ structures. -/
def subtype (A : Subring R) (hA : Λ.IsLambdaSubring A) : PreLambdaHom (Λ.restrict A hA) Λ where
  __ := A.subtype
  map_lambda' _ _ := rfl

@[simp]
theorem coe_subtype (A : Subring R) (hA : Λ.IsLambdaSubring A) :
    ⇑(Λ.subtype A hA) = ((↑) : A → R) :=
  (rfl)

variable {Λ} in
/-- A morphism with values in a λ-subring, as a morphism into the restricted structure. -/
def _root_.TauCeti.PreLambdaHom.codRestrict (f : PreLambdaHom Λ' Λ) (A : Subring R)
    (hA : Λ.IsLambdaSubring A) (hf : ∀ x, f x ∈ A) : PreLambdaHom Λ' (Λ.restrict A hA) where
  __ := f.toRingHom.codRestrict A hf
  map_lambda' n x := Subtype.ext (f.map_lambda n x)

variable {Λ} in
@[simp]
theorem _root_.TauCeti.PreLambdaHom.coe_codRestrict_apply (f : PreLambdaHom Λ' Λ)
    (A : Subring R) (hA : Λ.IsLambdaSubring A) (hf : ∀ x, f x ∈ A) (x : S) :
    (f.codRestrict A hA hf x : R) = f x :=
  (rfl)

@[simp]
theorem subtype_comp_codRestrict (f : PreLambdaHom Λ' Λ) (A : Subring R)
    (hA : Λ.IsLambdaSubring A) (hf : ∀ x, f x ∈ A) :
    (Λ.subtype A hA).comp (f.codRestrict A hA hf) = f :=
  (rfl)

/-- The restricted structure is the only pre-λ structure on a λ-subring for which the inclusion
commutes with every `λⁿ`. -/
theorem eq_restrict {A : Subring R} (hA : Λ.IsLambdaSubring A) {Λ' : PreLambdaStructure A}
    (h : ∀ n (x : A), (Λ'.lambda n x : R) = Λ.lambda n x) : Λ' = Λ.restrict A hA :=
  eq_of_injective Λ A.subtype Subtype.val_injective h fun _ _ => rfl

end PreLambdaStructure

end TauCeti
