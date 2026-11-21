/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Ring.Regular
public import Mathlib.FieldTheory.Finite.Basic

/-!
# δ-rings

Fix a prime `p`. A `δ`-ring is a commutative ring `A` with a map `δ : A → A` such that
`δ 0 = δ 1 = 0`, `δ (x * y) = x ^ p * δ y + y ^ p * δ x + p * δ x * δ y` and
`δ (x + y) = δ x + δ y + (x ^ p + y ^ p - (x + y) ^ p) / p`. The last quotient is the integral
polynomial `DeltaRing.addCorrection p x y`, a sum over the binomial coefficients `p.choose i`
with `0 < i < p`, each divided by `p`.

The map `φ x = x ^ p + p * δ x` is a ring endomorphism lifting Frobenius modulo `p`
(`DeltaRing.frobenius`). Conversely, on a ring in which `p` is a nonzerodivisor, a ring
endomorphism lifting Frobenius modulo `p` determines a unique `δ`-structure with that Frobenius
(`DeltaRing.ofFrobeniusLift` and `DeltaRing.ext_of_frobenius`), and a ring homomorphism into
such a ring commutes with `δ` exactly when it commutes with the Frobenius lifts. In particular
`ℤ` has a unique `δ`-structure (`DeltaRing.instInt` and `DeltaRing.instSubsingletonInt`), with
`δ n = (n - n ^ p) / p`.

## Main definitions

* `TauCeti.DeltaRing.addCorrection`: the polynomial `(x ^ p + y ^ p - (x + y) ^ p) / p`.
* `TauCeti.DeltaRing`: a `δ`-structure on a commutative ring.
* `TauCeti.DeltaRing.IsDeltaMap`: ring homomorphisms of `δ`-rings commuting with `δ`.
* `TauCeti.DeltaRing.IsFrobeniusLift`: ring endomorphisms lifting the `p`-th power map modulo `p`.
* `TauCeti.DeltaRing.frobenius`: the Frobenius lift `x ↦ x ^ p + p * δ x`.
* `TauCeti.DeltaRing.ofFrobeniusLift`: the `δ`-structure of a Frobenius lift on a ring in which
  `p` is a nonzerodivisor.
* `TauCeti.DeltaRing.equivFrobeniusLift`: on a ring in which `p` is a nonzerodivisor,
  `δ`-structures are equivalent to Frobenius lifts.

## Main results

* `TauCeti.DeltaRing.IsDeltaMap.comp_frobenius`: `δ`-maps intertwine the Frobenius lifts.
* `TauCeti.DeltaRing.isDeltaMap_iff_comp_frobenius`: if `p` is a nonzerodivisor on the target,
  the converse holds.

## References

* B. Bhatt and P. Scholze, *Prisms and prismatic cohomology*, Ann. of Math. 196 (2022),
  §2.1, Definition 2.1, Remarks 2.2 and 2.4.
-/

public section

namespace TauCeti

namespace DeltaRing

variable (p : ℕ) {A : Type*} [CommRing A]

/-- The integral polynomial `(x ^ p + y ^ p - (x + y) ^ p) / p`, written as
`-∑_{0 < i < p} x ^ i y ^ (p - i) (p.choose i / p)`. For prime `p` it satisfies
`p * addCorrection p x y = x ^ p + y ^ p - (x + y) ^ p` (`natCast_mul_addCorrection`). -/
def addCorrection (x y : A) : A :=
  -∑ i ∈ Finset.Ioo 0 p, x ^ i * y ^ (p - i) * ((p.choose i / p : ℕ) : A)

/-- The explicit binomial sum defining `addCorrection p x y`. -/
theorem addCorrection_def (x y : A) :
    addCorrection p x y = -∑ i ∈ Finset.Ioo 0 p, x ^ i * y ^ (p - i) * ((p.choose i / p : ℕ) : A) :=
  (rfl)

variable {p}

/-- For prime `p`, `p * addCorrection p x y = x ^ p + y ^ p - (x + y) ^ p`, so `addCorrection`
is the integral quotient `(x ^ p + y ^ p - (x + y) ^ p) / p` appearing in the sum rule of a
`δ`-ring. -/
theorem natCast_mul_addCorrection [hp : Fact p.Prime] (x y : A) :
    (p : A) * addCorrection p x y = x ^ p + y ^ p - (x + y) ^ p := by
  rw [addCorrection_def, add_pow_prime_eq' hp.out x y]
  ring

/-- Ring homomorphisms commute with `addCorrection`. -/
@[simp]
theorem map_addCorrection {B F : Type*} [CommRing B] [FunLike F A B] [RingHomClass F A B]
    (f : F) (x y : A) : f (addCorrection p x y) = addCorrection p (f x) (f y) := by
  simp [addCorrection_def]

/-- `addCorrection p 0 y = 0`. -/
@[simp]
theorem addCorrection_zero_left (y : A) : addCorrection p 0 y = 0 := by
  rw [addCorrection_def, neg_eq_zero]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [zero_pow (Finset.mem_Ioo.mp hi).1.ne', zero_mul, zero_mul]

/-- `addCorrection p x 0 = 0`. -/
@[simp]
theorem addCorrection_zero_right (x : A) : addCorrection p x 0 = 0 := by
  rw [addCorrection_def, neg_eq_zero]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [zero_pow (Nat.sub_ne_zero_of_lt (Finset.mem_Ioo.mp hi).2), mul_zero, zero_mul]

/-- `addCorrection` is symmetric in its two arguments. -/
theorem addCorrection_comm (x y : A) : addCorrection p x y = addCorrection p y x := by
  rw [addCorrection_def, addCorrection_def, neg_inj]
  refine Finset.sum_nbij' (p - ·) (p - ·) (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_)
    (fun i hi => ?_) fun i hi => ?_ <;> simp only [Finset.mem_Ioo] at hi ⊢ <;> try omega
  rw [Nat.sub_sub_self hi.2.le, Nat.choose_symm hi.2.le]
  ring

/-- For `p = 2` the addition correction is `-x * y`. -/
@[simp]
theorem addCorrection_two (x y : A) : addCorrection 2 x y = -(x * y) := by
  have h : Finset.Ioo 0 2 = ({1} : Finset ℕ) := by
    ext i
    simp only [Finset.mem_Ioo, Finset.mem_singleton]
    omega
  rw [addCorrection_def, h]
  simp

/-- For `p = 3` the addition correction is `-x * y * (x + y)`. -/
@[simp]
theorem addCorrection_three (x y : A) : addCorrection 3 x y = -(x * y * (x + y)) := by
  have h : Finset.Ioo 0 3 = ({1, 2} : Finset ℕ) := by
    ext i
    simp only [Finset.mem_Ioo, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [addCorrection_def, h]
  norm_num [Nat.choose]
  ring

/-- A ring endomorphism `f` of `A` is a Frobenius lift for `p` if `f x ≡ x ^ p` modulo `p` for
every `x` (Bhatt and Scholze, *Prisms and prismatic cohomology*, Remarks 2.2 and 2.5). This is a
proposition: the witnesses `y` with `f x = x ^ p + p * y` are not part of the data. -/
structure IsFrobeniusLift (p : ℕ) (f : A →+* A) : Prop where
  /-- `p` divides `f x - x ^ p`. -/
  dvd_sub_pow (x : A) : (p : A) ∣ f x - x ^ p

/-- The defining condition of `IsFrobeniusLift`. -/
theorem isFrobeniusLift_iff (f : A →+* A) :
    IsFrobeniusLift p f ↔ ∀ x, (p : A) ∣ f x - x ^ p :=
  ⟨fun h => h.dvd_sub_pow, fun h => ⟨h⟩⟩

/-- `f` is a Frobenius lift if and only if every `f x` has the form `x ^ p + p * y`. -/
theorem isFrobeniusLift_iff_exists (f : A →+* A) :
    IsFrobeniusLift p f ↔ ∀ x, ∃ y, f x = x ^ p + p * y := by
  simp only [isFrobeniusLift_iff, dvd_def, sub_eq_iff_eq_add']

/-- `f` is a Frobenius lift if and only if `f x` and `x ^ p` have the same image modulo `p`. -/
theorem isFrobeniusLift_iff_mk_eq (f : A →+* A) :
    IsFrobeniusLift p f ↔
      ∀ x, Ideal.Quotient.mk (Ideal.span {(p : A)}) (f x) =
        Ideal.Quotient.mk (Ideal.span {(p : A)}) (x ^ p) := by
  simp only [isFrobeniusLift_iff, Ideal.Quotient.eq, Ideal.mem_span_singleton]

/-- A Frobenius lift `f` satisfies `f x ≡ x ^ p` modulo `p`. -/
theorem IsFrobeniusLift.mk_eq {f : A →+* A} (hf : IsFrobeniusLift p f) (x : A) :
    Ideal.Quotient.mk (Ideal.span {(p : A)}) (f x) =
      Ideal.Quotient.mk (Ideal.span {(p : A)}) (x ^ p) :=
  (isFrobeniusLift_iff_mk_eq f).mp hf x

/-- If `x` lies in an ideal `I`, so does `addCorrection p x y`: each of its monomials
`x ^ i * y ^ (p - i)` has `0 < i`. -/
theorem addCorrection_mem_of_mem_left {I : Ideal A} {x : A} (y : A) (hx : x ∈ I) :
    addCorrection p x y ∈ I := by
  rw [addCorrection_def]
  refine I.neg_mem (I.sum_mem fun i hi => ?_)
  exact I.mul_mem_right _ (I.mul_mem_right _ (I.pow_mem_of_mem hx i (Finset.mem_Ioo.mp hi).1))

end DeltaRing

/-- A `δ`-structure on a commutative ring `A` for the prime `p` (Bhatt and Scholze, *Prisms and
prismatic cohomology*, Definition 2.1): a map
`delta` with `delta 0 = delta 1 = 0`, the product rule
`delta (x * y) = x ^ p * delta y + y ^ p * delta x + p * delta x * delta y` and the sum rule
`delta (x + y) = delta x + delta y + (x ^ p + y ^ p - (x + y) ^ p) / p`, where the last quotient
is the polynomial `DeltaRing.addCorrection p x y`.

The prime `p` is a parameter rather than a hypothesis of the class; the results that need its
primality assume `Fact p.Prime`. -/
@[ext]
class DeltaRing (p : ℕ) (A : Type*) [CommRing A] where
  /-- The `δ`-operation. -/
  delta : A → A
  delta_zero : delta 0 = 0
  delta_one : delta 1 = 0
  delta_add (x y : A) : delta (x + y) = delta x + delta y + DeltaRing.addCorrection p x y
  delta_mul (x y : A) :
    delta (x * y) = x ^ p * delta y + y ^ p * delta x + p * delta x * delta y

namespace DeltaRing

variable {p : ℕ} {A : Type*} [CommRing A]

attribute [simp] delta_zero delta_one

section Basic

variable [DeltaRing p A]

/-- `δ (-x) = -δ x - addCorrection p x (-x)`. -/
theorem delta_neg (x : A) : delta p (-x) = -delta p x - addCorrection p x (-x) := by
  have h := delta_add (p := p) x (-x)
  rw [add_neg_cancel, delta_zero] at h
  linear_combination -h

/-- `δ (1 + 1) = addCorrection p 1 1`. -/
theorem delta_one_add_one : delta p (1 + 1 : A) = addCorrection p 1 1 := by
  simp [delta_add]

end Basic

section Subsingleton

variable [Subsingleton A]

/-- The `δ`-structure on a zero ring. -/
instance instUniqueOfSubsingleton : Unique (DeltaRing p A) where
  default :=
    { delta := id
      delta_zero := Subsingleton.elim _ _
      delta_one := Subsingleton.elim _ _
      delta_add _ _ := Subsingleton.elim _ _
      delta_mul _ _ := Subsingleton.elim _ _ }
  uniq _ := DeltaRing.ext (funext fun _ => Subsingleton.elim _ _)

end Subsingleton

section IsDeltaMap

variable {B C : Type*} [CommRing B] [CommRing C] [DeltaRing p A] [DeltaRing p B] [DeltaRing p C]

variable (p) in
/-- A ring homomorphism between `δ`-rings is a `δ`-map if it commutes with `δ`. -/
structure IsDeltaMap (f : A →+* B) : Prop where
  /-- `f` commutes with `δ`. -/
  map_delta (x : A) : f (delta p x) = delta p (f x)

/-- The defining condition of `IsDeltaMap`. -/
theorem isDeltaMap_iff (f : A →+* B) :
    IsDeltaMap p f ↔ ∀ x, f (delta p x) = delta p (f x) :=
  ⟨fun h => h.map_delta, fun h => ⟨h⟩⟩

variable (p A) in
/-- The identity is a `δ`-map. -/
@[simp]
theorem isDeltaMap_id : IsDeltaMap p (RingHom.id A) :=
  ⟨fun _ => rfl⟩

/-- A composite of `δ`-maps is a `δ`-map. -/
theorem IsDeltaMap.comp {g : B →+* C} {f : A →+* B} (hg : IsDeltaMap p g)
    (hf : IsDeltaMap p f) : IsDeltaMap p (g.comp f) :=
  ⟨fun x => by rw [RingHom.comp_apply, hf.map_delta, hg.map_delta, RingHom.comp_apply]⟩

end IsDeltaMap

section Frobenius

variable [Fact p.Prime] [DeltaRing p A]

variable (p A) in
/-- The Frobenius lift `φ x = x ^ p + p * δ x` of a `δ`-ring, a ring endomorphism
(Bhatt and Scholze, *Prisms and prismatic cohomology*, Remark 2.2). -/
def frobenius : A →+* A where
  toFun x := x ^ p + p * delta p x
  map_one' := by simp
  map_mul' x y := by
    simp only [delta_mul, mul_pow]
    ring
  map_zero' := by simp [(Fact.out : p.Prime).ne_zero]
  map_add' x y := by
    simp only [delta_add, mul_add, natCast_mul_addCorrection]
    ring

theorem frobenius_apply (x : A) : frobenius p A x = x ^ p + p * delta p x := (rfl)

theorem frobenius_sub_pow (x : A) : frobenius p A x - x ^ p = p * delta p x := by
  rw [frobenius_apply]
  ring

/-- The Frobenius of a `δ`-ring lifts the `p`-th power map modulo `p`. -/
theorem natCast_dvd_frobenius_sub_pow (x : A) : (p : A) ∣ frobenius p A x - x ^ p :=
  ⟨delta p x, frobenius_sub_pow x⟩

variable (p A) in
/-- The Frobenius of a `δ`-ring is a Frobenius lift. -/
@[simp]
theorem isFrobeniusLift_frobenius : IsFrobeniusLift p (frobenius p A) :=
  ⟨natCast_dvd_frobenius_sub_pow⟩

/-- An element with `δ x = 0` has `φ x = x ^ p`. -/
theorem frobenius_apply_of_delta_eq_zero {x : A} (hx : delta p x = 0) :
    frobenius p A x = x ^ p := by
  rw [frobenius_apply, hx, mul_zero, add_zero]

/-- A ring homomorphism commuting with `δ` commutes with the Frobenius lifts. -/
theorem map_frobenius {B F : Type*} [CommRing B] [DeltaRing p B] [FunLike F A B]
    [RingHomClass F A B] (f : F) (hf : ∀ x, f (delta p x) = delta p (f x)) (x : A) :
    f (frobenius p A x) = frobenius p B (f x) := by
  simp [frobenius_apply, hf]

/-- A `δ`-map commutes with the Frobenius lifts. -/
theorem IsDeltaMap.map_frobenius {B : Type*} [CommRing B] [DeltaRing p B] {f : A →+* B}
    (hf : IsDeltaMap p f) (x : A) : f (frobenius p A x) = frobenius p B (f x) :=
  DeltaRing.map_frobenius f hf.map_delta x

/-- A `δ`-map intertwines the Frobenius lifts. -/
theorem IsDeltaMap.comp_frobenius {B : Type*} [CommRing B] [DeltaRing p B] {f : A →+* B}
    (hf : IsDeltaMap p f) : f.comp (frobenius p A) = (frobenius p B).comp f :=
  RingHom.ext hf.map_frobenius

/-- If `p` is a nonzerodivisor on `B`, a ring homomorphism `f : A →+* B` of `δ`-rings is a
`δ`-map if and only if it intertwines the Frobenius lifts (Bhatt and Scholze, *Prisms and
prismatic cohomology*, Remark 2.2). No hypothesis on `A` is needed. -/
theorem isDeltaMap_iff_comp_frobenius {B : Type*} [CommRing B] [DeltaRing p B]
    (hB : IsRegular (p : B)) (f : A →+* B) :
    IsDeltaMap p f ↔ f.comp (frobenius p A) = (frobenius p B).comp f := by
  refine ⟨IsDeltaMap.comp_frobenius, fun h => ⟨fun x => hB.left ?_⟩⟩
  have hx := congr(f $(frobenius_sub_pow (p := p) x))
  have hfx := frobenius_sub_pow (p := p) (f x)
  have h' := RingHom.congr_fun h x
  simp only [RingHom.comp_apply, map_sub, map_pow, map_mul, map_natCast] at hx h'
  dsimp only
  rw [← hx, ← hfx, h']

omit [DeltaRing p A] in
/-- On a ring in which `p` is a nonzerodivisor, a `δ`-structure is determined by its Frobenius
(Bhatt and Scholze, *Prisms and prismatic cohomology*, Remark 2.4). -/
theorem ext_of_frobenius (hA : IsRegular (p : A)) {δ₁ δ₂ : DeltaRing p A}
    (h : ∀ x, @frobenius p A _ _ δ₁ x = @frobenius p A _ _ δ₂ x) : δ₁ = δ₂ := by
  ext x
  apply hA.left
  dsimp only
  have h₁ := @frobenius_sub_pow p A _ _ δ₁ x
  have h₂ := @frobenius_sub_pow p A _ _ δ₂ x
  rw [← h₁, ← h₂, h x]

end Frobenius

section OfFrobeniusLift

variable [hp : Fact p.Prime]

/-- The `δ`-structure of a Frobenius lift `φ` on a ring in which `p` is a nonzerodivisor
(Bhatt and Scholze, *Prisms and prismatic cohomology*, Remark 2.4): `δ x` is the unique element
with `p * δ x = φ x - x ^ p`. -/
@[instance_reducible]
noncomputable def ofFrobeniusLift (hA : IsRegular (p : A)) (φ : A →+* A)
    (hφ : IsFrobeniusLift p φ) : DeltaRing p A where
  delta x := (hφ.dvd_sub_pow x).choose
  delta_zero := by
    rw [← hA.left.mul_left_eq_zero_iff, ← (hφ.dvd_sub_pow 0).choose_spec]
    simp [hp.out.ne_zero]
  delta_one := by
    rw [← hA.left.mul_left_eq_zero_iff, ← (hφ.dvd_sub_pow 1).choose_spec]
    simp
  delta_add x y := by
    apply hA.left
    have hx := (hφ.dvd_sub_pow x).choose_spec
    have hy := (hφ.dvd_sub_pow y).choose_spec
    have hxy : φ x + φ y - (x + y) ^ p = p * (hφ.dvd_sub_pow (x + y)).choose := by
      rw [← map_add]
      exact (hφ.dvd_sub_pow (x + y)).choose_spec
    have hc := natCast_mul_addCorrection (p := p) x y
    dsimp only
    linear_combination -hxy + hx + hy - hc
  delta_mul x y := by
    apply hA.left
    have hx := (hφ.dvd_sub_pow x).choose_spec
    have hy := (hφ.dvd_sub_pow y).choose_spec
    have hxy : φ x * φ y - (x * y) ^ p = p * (hφ.dvd_sub_pow (x * y)).choose := by
      rw [← map_mul]
      exact (hφ.dvd_sub_pow (x * y)).choose_spec
    dsimp only
    linear_combination -hxy + φ x * hy + (y ^ p + p * (hφ.dvd_sub_pow y).choose) * hx

/-- Under `ofFrobeniusLift hA φ hφ`, `δ x` is characterised by `p * δ x = φ x - x ^ p`. -/
theorem natCast_mul_delta_ofFrobeniusLift (hA : IsRegular (p : A)) (φ : A →+* A)
    (hφ : IsFrobeniusLift p φ) (x : A) :
    (p : A) * @delta p A _ (ofFrobeniusLift hA φ hφ) x = φ x - x ^ p :=
  ((hφ.dvd_sub_pow x).choose_spec).symm

/-- The Frobenius of `ofFrobeniusLift hA φ hφ` is `φ`. -/
@[simp]
theorem frobenius_ofFrobeniusLift (hA : IsRegular (p : A)) (φ : A →+* A)
    (hφ : IsFrobeniusLift p φ) :
    @frobenius p A _ _ (ofFrobeniusLift hA φ hφ) = φ := by
  ext x
  rw [@frobenius_apply, natCast_mul_delta_ofFrobeniusLift]
  ring

/-- If `p` is a nonzerodivisor on `A`, then `δ`-structures on `A` correspond to Frobenius lifts on
`A`, by `φ x = x ^ p + p * δ x` (Bhatt and Scholze, *Prisms and prismatic cohomology*,
Remark 2.2). -/
noncomputable def equivFrobeniusLift (hA : IsRegular (p : A)) :
    DeltaRing p A ≃ {φ : A →+* A // IsFrobeniusLift p φ} where
  toFun _ := ⟨frobenius p A, isFrobeniusLift_frobenius p A⟩
  invFun φ := ofFrobeniusLift hA φ.val φ.property
  left_inv _ := ext_of_frobenius hA fun x => by rw [frobenius_ofFrobeniusLift]
  right_inv φ := Subtype.ext (frobenius_ofFrobeniusLift hA φ.val φ.property)

/-- The Frobenius lift attached to a `δ`-structure by `equivFrobeniusLift` is its Frobenius. -/
@[simp]
theorem coe_equivFrobeniusLift_apply (hA : IsRegular (p : A)) (δ : DeltaRing p A) :
    (equivFrobeniusLift hA δ : A →+* A) = @frobenius p A _ _ δ :=
  (rfl)

/-- The `δ`-structure attached to a Frobenius lift by `equivFrobeniusLift` is
`ofFrobeniusLift`. -/
@[simp]
theorem equivFrobeniusLift_symm_apply (hA : IsRegular (p : A))
    (φ : {φ : A →+* A // IsFrobeniusLift p φ}) :
    (equivFrobeniusLift hA).symm φ = ofFrobeniusLift hA φ.val φ.property :=
  (rfl)

end OfFrobeniusLift

section Int

variable [hp : Fact p.Prime]

/-- The `δ`-structure on `ℤ` whose Frobenius is the identity (Bhatt and Scholze, *Prisms and
prismatic cohomology*, Remark 2.4); it is the only one (`instSubsingletonInt`). -/
noncomputable instance instInt : DeltaRing p ℤ :=
  ofFrobeniusLift (A := ℤ)
    (isRegular_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hp.out.ne_zero)) (RingHom.id ℤ)
      ⟨fun n => (Int.ModEq.pow_prime_eq_self hp.out n).dvd⟩

/-- `ℤ` has at most one `δ`-structure, since its Frobenius, a ring endomorphism of `ℤ`, must be
the identity. -/
instance instSubsingletonInt : Subsingleton (DeltaRing p ℤ) :=
  ⟨fun _ _ => ext_of_frobenius (isRegular_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hp.out.ne_zero))
    fun x => DFunLike.congr_fun (Subsingleton.elim _ _) x⟩

/-- The Frobenius of the `δ`-structure on `ℤ` is the identity. This is not `@[simp]`, since
`simp` already proves it by `frobenius_ofFrobeniusLift`. -/
theorem frobenius_int : frobenius p ℤ = RingHom.id ℤ :=
  frobenius_ofFrobeniusLift _ _ _

/-- The `δ`-operation on `ℤ` is `n ↦ (n - n ^ p) / p`; the division is exact since `p` divides
`n - n ^ p`. -/
theorem delta_int (n : ℤ) : delta p n = (n - n ^ p) / p := by
  have h := frobenius_sub_pow (p := p) n
  rw [frobenius_int, RingHom.id_apply] at h
  rw [h, Int.mul_ediv_cancel_left _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)]

/-- For `p = 2`, the `δ`-operation on `ℤ` sends `2` to `-1`. -/
@[simp]
theorem delta_int_two : delta 2 (2 : ℤ) = -1 := by
  rw [delta_int]
  norm_num

end Int

end DeltaRing

end TauCeti
