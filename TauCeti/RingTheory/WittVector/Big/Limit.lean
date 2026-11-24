/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WittVector.Big.NonUnital

/-!
# Big Witt vectors as an inverse limit

For every truncation set `S`, its big Witt ring is the inverse limit of the rings indexed by
finite subtruncations of `S`. The universal property is expressed by `BigWittVector.liftEquiv`:
compatible families of ring homomorphisms into the finite stages correspond to ring
homomorphisms into `BigWittVector S R`. The nonunital version is `NonUnitalBigWitt.liftEquiv`.

The homomorphism formulation follows the p-typical analogue `WittVector.liftEquiv` in
`Mathlib.RingTheory.WittVector.Truncated`. Both versions share the coordinate assembly: the
coordinate of index `n` is read from the finite stage `TruncationSet.divisors n`.
-/

public section

namespace TauCeti.BigWittVector

open BigWitt (TruncationSet)

variable {S : TruncationSet} {R A : Type*}

/-- The finite truncation sets contained in `S`. -/
abbrev FiniteSubtruncation (S : TruncationSet) :=
  {T : TruncationSet // T ≤ S ∧ (T : Set ℕ).Finite}

private abbrev divisorStage (n : S) : FiniteSubtruncation S :=
  ⟨TruncationSet.divisors n, (TruncationSet.divisors_le_iff
      (S.ne_zero_of_mem n.property)).2 n.property,
    by simpa only [TruncationSet.coe_divisors] using n.val.divisors.finite_toSet⟩

private def finiteGlue (f : ∀ T : FiniteSubtruncation S, A → T.val → R) (a : A) : S → R :=
  fun n ↦ f (divisorStage n) a
    ⟨n, TruncationSet.mem_divisors_self (S.ne_zero_of_mem n.property)⟩

private theorem finiteGlue_apply (f : ∀ T : FiniteSubtruncation S, A → T.val → R)
    (hf : ∀ (T U : FiniteSubtruncation S) (h : T.val ≤ U.val) (a : A) (n : T.val),
      f U a ⟨n, h n.property⟩ = f T a n)
    (T : FiniteSubtruncation S) (a : A) (n : T.val) :
    finiteGlue f a ⟨n, T.property.1 n.property⟩ = f T a n :=
  (hf (divisorStage ⟨n, T.property.1 n.property⟩) T
    ((TruncationSet.divisors_le_iff (T.val.ne_zero_of_mem n.property)).2 n.property) a
    ⟨n, TruncationSet.mem_divisors_self (T.val.ne_zero_of_mem n.property)⟩).symm

private theorem finiteCoordinate_ext {x y : S → R}
    (h : ∀ (T : FiniteSubtruncation S) (n : T.val),
      x ⟨n, T.property.1 n.property⟩ = y ⟨n, T.property.1 n.property⟩) (n : S) :
    x n = y n :=
  h (divisorStage n)
    ⟨n, TruncationSet.mem_divisors_self (S.ne_zero_of_mem n.property)⟩

variable [CommRing R]

/-- Finite restrictions determine a big Witt vector. -/
theorem eq_of_restrict_eq {x y : BigWittVector S R}
    (h : ∀ T : FiniteSubtruncation S, restrict T.property.1 x = restrict T.property.1 y) :
    x = y := by
  apply BigWittVector.ext
  intro n
  by_cases hn : n ∈ S
  · apply finiteCoordinate_ext (x := fun n : S ↦ x.coeff n)
      (y := fun n : S ↦ y.coeff n) (n := ⟨n, hn⟩)
    intro T n
    have he := congrArg (fun z : BigWittVector T.val R ↦ z.coeff n) (h T)
    simpa only [coeff_restrict_of_mem _ _ n.property] using he
  · exact (x.coeff_eq_zero_of_notMem n hn).trans (y.coeff_eq_zero_of_notMem n hn).symm

section Lift

variable [NonAssocSemiring A]
variable (f : ∀ T : FiniteSubtruncation S, A →+* BigWittVector T.val R)
variable (hf : ∀ (T U : FiniteSubtruncation S) (h : T.val ≤ U.val),
  (restrict h).comp (f U) = f T)

private noncomputable def liftFun (a : A) : BigWittVector S R := by
  classical
  exact mk' (fun n ↦ if hn : n ∈ S then
    finiteGlue (fun T a n ↦ (f T a).coeff n) a ⟨n, hn⟩ else 0)

include hf in
private theorem liftFun_restrict (T : FiniteSubtruncation S) (a : A) :
    restrict T.property.1 (liftFun f a) = f T a := by
  classical
  apply BigWittVector.ext
  intro n
  by_cases hn : n ∈ T.val
  · rw [coeff_restrict_of_mem _ _ hn]
    simp only [liftFun, coeff_mk'_of_mem _ (T.property.1 hn), dite_eq_left (T.property.1 hn)]
    apply finiteGlue_apply (fun T a n ↦ (f T a).coeff n) _ T a ⟨n, hn⟩
    intro T U h a n
    have he := congrArg (fun z : BigWittVector T.val R ↦ z.coeff n)
      (DFunLike.congr_fun (hf T U h) a)
    simpa only [RingHom.comp_apply, coeff_restrict_of_mem _ _ n.property] using he
  · exact (coeff_eq_zero_of_notMem _ n hn).trans
      ((f T a).coeff_eq_zero_of_notMem n hn).symm

/-- Lift a compatible family of ring homomorphisms to the big Witt ring. -/
noncomputable def lift : A →+* BigWittVector S R where
  toFun := liftFun f
  map_zero' := eq_of_restrict_eq fun T ↦ by
    rw [liftFun_restrict f hf, map_zero, map_zero]
  map_one' := eq_of_restrict_eq fun T ↦ by
    rw [liftFun_restrict f hf, map_one, map_one]
  map_add' a b := eq_of_restrict_eq fun T ↦ by
    rw [liftFun_restrict f hf, map_add, map_add,
      liftFun_restrict f hf, liftFun_restrict f hf]
  map_mul' a b := eq_of_restrict_eq fun T ↦ by
    rw [liftFun_restrict f hf, map_mul, map_mul,
      liftFun_restrict f hf, liftFun_restrict f hf]

@[simp]
theorem restrict_lift (T : FiniteSubtruncation S) (a : A) :
    restrict T.property.1 (lift f hf a) = f T a :=
  liftFun_restrict f hf T a

@[simp]
theorem restrict_comp_lift (T : FiniteSubtruncation S) :
    (restrict T.property.1).comp (lift f hf) = f T := by
  ext1 a
  exact restrict_lift f hf T a

/-- A lift is determined by its finite restrictions. -/
theorem lift_unique (g : A →+* BigWittVector S R)
    (hg : ∀ T : FiniteSubtruncation S, (restrict T.property.1).comp g = f T) :
    lift f hf = g := by
  ext1 a
  apply eq_of_restrict_eq
  intro T
  rw [restrict_lift]
  exact (DFunLike.congr_fun (hg T) a).symm

/-- The big Witt ring is the inverse limit of its finite subtruncations. -/
noncomputable def liftEquiv :
    {f : ∀ T : FiniteSubtruncation S, A →+* BigWittVector T.val R //
      ∀ (T U : FiniteSubtruncation S) (h : T.val ≤ U.val), (restrict h).comp (f U) = f T} ≃
      (A →+* BigWittVector S R) where
  toFun f := lift f.val f.property
  invFun g := ⟨fun T ↦ (restrict T.property.1).comp g, by
    intro T U h
    rw [← RingHom.comp_assoc, restrict_comp_restrict]⟩
  left_inv := by
    rintro ⟨f, hf⟩
    apply Subtype.ext
    funext T
    exact restrict_comp_lift f hf T
  right_inv g := lift_unique _ _ _ fun _ ↦ rfl

theorem liftEquiv_apply
    (f : {f : ∀ T : FiniteSubtruncation S, A →+* BigWittVector T.val R //
      ∀ (T U : FiniteSubtruncation S) (h : T.val ≤ U.val), (restrict h).comp (f U) = f T}) :
    liftEquiv f = lift f.val f.property := by
  rfl

@[simp]
theorem liftEquiv_symm_apply (g : A →+* BigWittVector S R) (T : FiniteSubtruncation S) :
    (liftEquiv.symm g).val T = (restrict T.property.1).comp g := by
  rfl

/-- Ring homomorphisms into a big Witt ring agree if their finite restrictions agree. -/
theorem hom_ext (g h : A →+* BigWittVector S R)
    (hgh : ∀ T : FiniteSubtruncation S,
      (restrict T.property.1).comp g = (restrict T.property.1).comp h) : g = h := by
  ext1 a
  apply eq_of_restrict_eq
  intro T
  exact DFunLike.congr_fun (hgh T) a

end Lift

end TauCeti.BigWittVector

namespace TauCeti.NonUnitalBigWitt

open BigWitt (TruncationSet)
open BigWittVector (FiniteSubtruncation)

variable {S : TruncationSet} {R A : Type*}

variable [NonUnitalCommRing R]

/-- Finite restrictions determine a nonunital big Witt vector. -/
theorem eq_of_restrict_eq {x y : NonUnitalBigWitt S R}
    (h : ∀ T : FiniteSubtruncation S, restrict T.property.1 x = restrict T.property.1 y) :
    x = y := by
  apply NonUnitalBigWitt.ext
  apply BigWittVector.finiteCoordinate_ext
  intro T n
  have he := congrArg (fun z : NonUnitalBigWitt T.val R ↦ z.coeff n) (h T)
  simpa only [restrict_coeff] using he

section Lift

variable [NonUnitalNonAssocSemiring A]
variable (f : ∀ T : FiniteSubtruncation S, A →ₙ+* NonUnitalBigWitt T.val R)
variable (hf : ∀ (T U : FiniteSubtruncation S) (h : T.val ≤ U.val),
  (restrict h).comp (f U) = f T)

private noncomputable def liftFun (a : A) : NonUnitalBigWitt S R :=
  mk (BigWittVector.finiteGlue (fun T a ↦ (f T a).coeff) a)

include hf in
private theorem liftFun_restrict (T : FiniteSubtruncation S) (a : A) :
    restrict T.property.1 (liftFun f a) = f T a := by
  apply NonUnitalBigWitt.ext
  intro n
  rw [restrict_coeff, liftFun, coeff_mk]
  apply BigWittVector.finiteGlue_apply
  intro T U h a n
  have he := congrArg (fun z : NonUnitalBigWitt T.val R ↦ z.coeff n)
    (DFunLike.congr_fun (hf T U h) a)
  simpa only [NonUnitalRingHom.comp_apply, restrict_coeff] using he

/-- Lift a compatible family of nonunital ring homomorphisms to `NonUnitalBigWitt S R`. -/
noncomputable def lift : A →ₙ+* NonUnitalBigWitt S R where
  toFun := liftFun f
  map_zero' := eq_of_restrict_eq fun T ↦ by
    rw [liftFun_restrict f hf, map_zero, map_zero]
  map_add' a b := eq_of_restrict_eq fun T ↦ by
    rw [liftFun_restrict f hf, map_add, map_add,
      liftFun_restrict f hf, liftFun_restrict f hf]
  map_mul' a b := eq_of_restrict_eq fun T ↦ by
    rw [liftFun_restrict f hf, map_mul, map_mul,
      liftFun_restrict f hf, liftFun_restrict f hf]

@[simp]
theorem restrict_lift (T : FiniteSubtruncation S) (a : A) :
    restrict T.property.1 (lift f hf a) = f T a :=
  liftFun_restrict f hf T a

@[simp]
theorem restrict_comp_lift (T : FiniteSubtruncation S) :
    (restrict T.property.1).comp (lift f hf) = f T := by
  ext1 a
  exact restrict_lift f hf T a

/-- A lift is determined by its finite restrictions. -/
theorem lift_unique (g : A →ₙ+* NonUnitalBigWitt S R)
    (hg : ∀ T : FiniteSubtruncation S, (restrict T.property.1).comp g = f T) :
    lift f hf = g := by
  ext1 a
  apply eq_of_restrict_eq
  intro T
  rw [restrict_lift]
  exact (DFunLike.congr_fun (hg T) a).symm

/-- The nonunital big Witt vectors are the inverse limit of their finite subtruncations. -/
noncomputable def liftEquiv :
    {f : ∀ T : FiniteSubtruncation S, A →ₙ+* NonUnitalBigWitt T.val R //
      ∀ (T U : FiniteSubtruncation S) (h : T.val ≤ U.val), (restrict h).comp (f U) = f T} ≃
      (A →ₙ+* NonUnitalBigWitt S R) where
  toFun f := lift f.val f.property
  invFun g := ⟨fun T ↦ (restrict T.property.1).comp g, by
    intro T U h
    rw [← NonUnitalRingHom.comp_assoc, restrict_comp]⟩
  left_inv := by
    rintro ⟨f, hf⟩
    apply Subtype.ext
    funext T
    exact restrict_comp_lift f hf T
  right_inv g := lift_unique _ _ _ fun _ ↦ rfl

theorem liftEquiv_apply
    (f : {f : ∀ T : FiniteSubtruncation S, A →ₙ+* NonUnitalBigWitt T.val R //
      ∀ (T U : FiniteSubtruncation S) (h : T.val ≤ U.val), (restrict h).comp (f U) = f T}) :
    liftEquiv f = lift f.val f.property := by
  rfl

@[simp]
theorem liftEquiv_symm_apply (g : A →ₙ+* NonUnitalBigWitt S R) (T : FiniteSubtruncation S) :
    (liftEquiv.symm g).val T = (restrict T.property.1).comp g := by
  rfl

/-- Nonunital ring homomorphisms into `NonUnitalBigWitt S R` agree if their finite
restrictions agree. -/
theorem hom_ext (g h : A →ₙ+* NonUnitalBigWitt S R)
    (hgh : ∀ T : FiniteSubtruncation S,
      (restrict T.property.1).comp g = (restrict T.property.1).comp h) : g = h := by
  ext1 a
  apply eq_of_restrict_eq
  intro T
  exact DFunLike.congr_fun (hgh T) a

end Lift

end TauCeti.NonUnitalBigWitt
