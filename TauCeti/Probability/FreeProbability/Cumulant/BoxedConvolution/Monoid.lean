/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Cumulant.BoxedConvolution.Associative
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# The boxed-convolution monoid of formal power series

Scalar boxed convolution `PowerSeries.boxedConvolution` is commutative, associative, and has the
two-sided identity `1 + X` over every commutative semiring. Because `R⟦X⟧` already carries
Cauchy multiplication with identity `1`, we package boxed convolution on the multiplicative type
wrapper `PowerSeries.BoxedConvolution R` (`toBoxed` / `ofBoxed`).

Both standard constant-coefficient conventions sit compatibly inside this monoid:

* the constant coefficient and the linear coefficient are monoid homomorphisms
  `BoxedConvolution.constantCoeffHom` and `BoxedConvolution.coeffOneHom` to `R`;
* the kernel `BoxedConvolution.normalizedSubmonoid R` of `constantCoeffHom` consists of the
  normalised series `1 + ∑_{n ≥ 1} aₙ Xⁿ`, which contains all one-variable free cumulant series
  and (for normalised functionals) moment series;
* on series with zero constant coefficient (Nica and Speicher's convention `∑_{n ≥ 1} aₙ Xⁿ`),
  `X` acts as a two-sided identity (`PowerSeries.boxedConvolution_X_of_constantCoeff_eq_zero`).

In addition, rescaling the variable commutes with boxed convolution in either factor:
`(rescale c f).boxedConvolution g = rescale c (f.boxedConvolution g) =
f.boxedConvolution (rescale c g)`, reflecting `(c a) b = c (a b) = a (c b)` for free variables.
Iterating `IsFreelyIndependent.freeCumulantSeries_mul` along `IsFreelyIndependent.biSup_disjoint`
expresses the free cumulant series of a product of variables from pairwise distinct members of a
freely independent family (over any semiring `A`) as the product in `BoxedConvolution R` of their
individual free cumulant series.

## Main definitions

* `PowerSeries.BoxedConvolution R`: multiplicative wrapper around `R⟦X⟧` whose product is boxed
  convolution and whose identity is `1 + X`.
* `PowerSeries.BoxedConvolution.constantCoeffHom`, `PowerSeries.BoxedConvolution.coeffOneHom`:
  the constant and linear coefficients as monoid homomorphisms `BoxedConvolution R →* R`.
* `PowerSeries.BoxedConvolution.map`: base change `BoxedConvolution R →* BoxedConvolution S`
  along a ring homomorphism `R →+* S`.
* `PowerSeries.BoxedConvolution.normalizedSubmonoid R`: the submonoid of series with constant
  coefficient `1`.

## Main results

* `PowerSeries.rescale_boxedConvolution`, `PowerSeries.boxedConvolution_rescale`: rescaling either
  factor rescales the boxed convolution.
* `PowerSeries.boxedConvolution_X_of_constantCoeff_eq_zero`,
  `PowerSeries.X_boxedConvolution_of_constantCoeff_eq_zero`: `X` is a two-sided boxed-convolution
  identity on series with zero constant coefficient.
* `TauCeti.IsFreelyIndependent.toBoxed_freeCumulantSeries_list_prod` and
  `TauCeti.IsFreelyIndependentElements.toBoxed_freeCumulantSeries_list_prod`: the free cumulant
  series of a finite product of free variables is the boxed-convolution product of their free
  cumulant series.
* `TauCeti.IsFreelyIndependent.apply_list_prod` and
  `TauCeti.IsFreelyIndependentElements.apply_list_prod`: expectations factorise along
  duplicate-free products of free variables over any semiring `A`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lectures 17 and 18.
* A. Nica, R. Speicher, *A "Fourier transform" for multiplicative functions on non-crossing
  partitions*, J. Algebraic Combin. 6 (1997), 141–160.
-/

public section

open Finset TauCeti TauCeti.NoncrossingPartition

namespace PowerSeries

section Operations

variable {R : Type*} [CommSemiring R]

/-- Rescaling the first factor of a boxed convolution rescales the result: for every partition
`π ∈ NC(n)`, the sizes of the parts of `π` sum to `n`. -/
theorem rescale_boxedConvolution (c : R) (f g : R⟦X⟧) :
    (rescale c f).boxedConvolution g = rescale c (f.boxedConvolution g) := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [← coeff_zero_eq_constantCoeff_apply (rescale _ _), coeff_rescale]
  rw [coeff_boxedConvolution hn, coeff_rescale, coeff_boxedConvolution hn, mul_sum]
  refine sum_congr rfl fun π _ => ?_
  simp only [coeff_rescale, prod_mul_distrib, prod_pow_eq_pow_sum, π.1.sum_card_parts,
    card_univ, Fintype.card_fin, mul_assoc]

/-- Rescaling the second factor of a boxed convolution rescales the result. -/
theorem boxedConvolution_rescale (c : R) (f g : R⟦X⟧) :
    f.boxedConvolution (rescale c g) = rescale c (f.boxedConvolution g) := by
  rw [boxedConvolution_comm, rescale_boxedConvolution, boxedConvolution_comm]

/-- On series with zero constant coefficient, `X` is a right identity for boxed convolution. -/
theorem boxedConvolution_X_of_constantCoeff_eq_zero {f : R⟦X⟧} (hf : constantCoeff f = 0) :
    f.boxedConvolution X = f := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hf]
  rw [coeff_boxedConvolution_congr hn (fun _ _ => rfl)
    (g' := 1 + X) (fun k hk => by simp [coeff_one, hk]), boxedConvolution_one_add_X]

/-- On series with zero constant coefficient, `X` is a left identity for boxed convolution. -/
theorem X_boxedConvolution_of_constantCoeff_eq_zero {f : R⟦X⟧} (hf : constantCoeff f = 0) :
    X.boxedConvolution f = f := by
  rw [boxedConvolution_comm, boxedConvolution_X_of_constantCoeff_eq_zero hf]

end Operations

/-- A multiplicative type wrapper around `R⟦X⟧` equipping formal power series with scalar boxed
convolution `PowerSeries.boxedConvolution` and identity `1 + X`. -/
@[ext]
structure BoxedConvolution (R : Type*) where
  /-- Wraps a power series in `BoxedConvolution R`. -/
  toBoxed ::
  /-- Unwraps an element of `BoxedConvolution R` to its underlying power series. -/
  ofBoxed : R⟦X⟧

namespace BoxedConvolution

section TypeWrapper

variable {R : Type*}

theorem ofBoxed_toBoxed (f : R⟦X⟧) : (toBoxed f).ofBoxed = f := (rfl)

@[simp]
theorem toBoxed_ofBoxed (x : BoxedConvolution R) : toBoxed x.ofBoxed = x := (rfl)

theorem ofBoxed_injective : Function.Injective (@ofBoxed R) :=
  fun _ _ => BoxedConvolution.ext

theorem toBoxed_injective : Function.Injective (@toBoxed R) :=
  Function.LeftInverse.injective ofBoxed_toBoxed

@[simp]
theorem ofBoxed_inj {x y : BoxedConvolution R} : x.ofBoxed = y.ofBoxed ↔ x = y :=
  ofBoxed_injective.eq_iff

theorem toBoxed_inj {f g : R⟦X⟧} : toBoxed f = toBoxed g ↔ f = g :=
  toBoxed_injective.eq_iff

variable (R) in
/-- `BoxedConvolution.ofBoxed` and `BoxedConvolution.toBoxed` as an equivalence of types. -/
def equiv : BoxedConvolution R ≃ R⟦X⟧ where
  toFun := ofBoxed
  invFun := toBoxed
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem equiv_apply (x : BoxedConvolution R) : equiv R x = x.ofBoxed := (rfl)

@[simp]
theorem equiv_symm_apply (f : R⟦X⟧) : (equiv R).symm f = toBoxed f := (rfl)

instance [Nontrivial R⟦X⟧] : Nontrivial (BoxedConvolution R) := (equiv R).nontrivial
instance [Subsingleton R⟦X⟧] : Subsingleton (BoxedConvolution R) := (equiv R).subsingleton
instance [DecidableEq R⟦X⟧] : DecidableEq (BoxedConvolution R) := (equiv R).decidableEq

end TypeWrapper

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- The identity of `BoxedConvolution R` is `1 + X`. -/
noncomputable instance : One (BoxedConvolution R) where
  one := toBoxed (1 + X)

/-- Multiplication in `BoxedConvolution R` is scalar boxed convolution. -/
noncomputable instance : Mul (BoxedConvolution R) where
  mul x y := toBoxed (x.ofBoxed.boxedConvolution y.ofBoxed)

@[simp]
theorem ofBoxed_one : (1 : BoxedConvolution R).ofBoxed = 1 + X := (rfl)

@[simp]
theorem toBoxed_one_add_X : toBoxed (1 + X : R⟦X⟧) = 1 := (rfl)

@[simp]
theorem ofBoxed_mul (x y : BoxedConvolution R) :
    (x * y).ofBoxed = x.ofBoxed.boxedConvolution y.ofBoxed := (rfl)

@[simp]
theorem toBoxed_boxedConvolution (f g : R⟦X⟧) :
    toBoxed (f.boxedConvolution g) = toBoxed f * toBoxed g := (rfl)

/-- Formal power series form a commutative monoid under boxed convolution, with identity `1 + X`. -/
noncomputable instance : CommMonoid (BoxedConvolution R) where
  mul_assoc x y z := BoxedConvolution.ext (boxedConvolution_assoc x.ofBoxed y.ofBoxed z.ofBoxed)
  one_mul x := BoxedConvolution.ext (one_add_X_boxedConvolution x.ofBoxed)
  mul_one x := BoxedConvolution.ext (boxedConvolution_one_add_X x.ofBoxed)
  mul_comm x y := BoxedConvolution.ext (boxedConvolution_comm x.ofBoxed y.ofBoxed)

/-- The constant coefficient as a monoid homomorphism `BoxedConvolution R →* R`. -/
noncomputable def constantCoeffHom : BoxedConvolution R →* R where
  toFun x := constantCoeff x.ofBoxed
  map_one' := by simp
  map_mul' x y := constantCoeff_boxedConvolution x.ofBoxed y.ofBoxed

@[simp]
theorem constantCoeffHom_apply (x : BoxedConvolution R) :
    constantCoeffHom x = constantCoeff x.ofBoxed := (rfl)

/-- The linear coefficient as a monoid homomorphism `BoxedConvolution R →* R`. -/
noncomputable def coeffOneHom : BoxedConvolution R →* R where
  toFun x := coeff 1 x.ofBoxed
  map_one' := by simp
  map_mul' x y := coeff_one_boxedConvolution x.ofBoxed y.ofBoxed

@[simp]
theorem coeffOneHom_apply (x : BoxedConvolution R) :
    coeffOneHom x = coeff 1 x.ofBoxed := (rfl)

@[simp]
theorem constantCoeff_ofBoxed_pow (x : BoxedConvolution R) (n : ℕ) :
    constantCoeff (x ^ n).ofBoxed = constantCoeff x.ofBoxed ^ n :=
  map_pow constantCoeffHom x n

@[simp]
theorem coeff_one_ofBoxed_pow (x : BoxedConvolution R) (n : ℕ) :
    coeff 1 (x ^ n).ofBoxed = coeff 1 x.ofBoxed ^ n :=
  map_pow coeffOneHom x n

/-- Base change of boxed-convolution elements along a ring homomorphism `f : R →+* S`. -/
noncomputable def map {S : Type*} [CommSemiring S] (f : R →+* S) :
    BoxedConvolution R →* BoxedConvolution S where
  toFun x := toBoxed (PowerSeries.map f x.ofBoxed)
  map_one' := BoxedConvolution.ext <| by simp
  map_mul' x y := BoxedConvolution.ext (map_boxedConvolution x.ofBoxed y.ofBoxed f)

@[simp]
theorem ofBoxed_map {S : Type*} [CommSemiring S] (f : R →+* S) (x : BoxedConvolution R) :
    (map f x).ofBoxed = PowerSeries.map f x.ofBoxed := (rfl)

@[simp]
theorem map_toBoxed {S : Type*} [CommSemiring S] (f : R →+* S) (p : R⟦X⟧) :
    map f (toBoxed p) = toBoxed (PowerSeries.map f p) := (rfl)

@[simp]
theorem map_id : map (RingHom.id R) = MonoidHom.id (BoxedConvolution R) :=
  MonoidHom.ext fun _ => BoxedConvolution.ext <| PowerSeries.ext fun _ => by simp

theorem map_comp {S T : Type*} [CommSemiring S] [CommSemiring T] (f : R →+* S) (g : S →+* T)
    (x : BoxedConvolution R) : map (g.comp f) x = map g (map f x) :=
  BoxedConvolution.ext <| PowerSeries.ext fun n => by simp

variable (R) in
/-- The submonoid of `BoxedConvolution R` consisting of normalised series `1 + ∑_{n ≥ 1} aₙ Xⁿ`,
those with constant coefficient `1`. -/
noncomputable def normalizedSubmonoid : Submonoid (BoxedConvolution R) :=
  MonoidHom.mker constantCoeffHom

@[simp]
theorem mem_normalizedSubmonoid_iff {x : BoxedConvolution R} :
    x ∈ normalizedSubmonoid R ↔ constantCoeff x.ofBoxed = 1 :=
  Iff.rfl

end CommSemiring

end BoxedConvolution

end PowerSeries

namespace TauCeti

open Function PowerSeries PowerSeries.BoxedConvolution

section Monoid

variable {R A : Type*} [CommRing R] [Monoid A]

/-- Every one-variable free cumulant series belongs to the normalised boxed-convolution
submonoid. -/
theorem toBoxed_freeCumulantSeries_mem_normalizedSubmonoid (φ : A → R) (a : A) :
    toBoxed (freeCumulantSeries φ a) ∈ normalizedSubmonoid R :=
  constantCoeff_freeCumulantSeries φ a

/-- For a normalised functional `φ`, every moment series belongs to the normalised
boxed-convolution submonoid. -/
theorem toBoxed_momentSeries_mem_normalizedSubmonoid {φ : A → R} (hφ : φ 1 = 1) (a : A) :
    toBoxed (momentSeries φ a) ∈ normalizedSubmonoid R := by
  simpa using hφ

/-- For a normalised functional `φ`, the free cumulant series of `1` is `1 + X`. -/
@[simp]
theorem freeCumulantSeries_one {φ : A → R} (hφ : φ 1 = 1) :
    freeCumulantSeries φ (1 : A) = 1 + X := by
  refine (eq_freeCumulantSeries_of_subst_eq (1 : A) hφ ?_).symm
  have hX : HasSubst (X * momentSeries φ (1 : A)) := .of_constantCoeff_zero' (by simp)
  rw [subst_add hX, subst_one, subst_X hX]
  ext (_ | n) <;> simp [hφ, coeff_succ_X_mul]

/-- For a normalised functional `φ`, the free cumulant series of `1` is the boxed-convolution
identity `1 + X`. -/
theorem toBoxed_freeCumulantSeries_one {φ : A → R} (hφ : φ 1 = 1) :
    toBoxed (freeCumulantSeries φ (1 : A)) = 1 := by
  simp [freeCumulantSeries_one hφ]

end Monoid

section FreeProduct

variable {R A ι : Type*} [CommRing R] [Semiring A] [Algebra R A] {φ : A →ₗ[R] R}

/-- *Free cumulants of a finite product of free variables*: if `l : List (ι × A)` has pairwise
distinct indices and each letter `p.2` belongs to `B p.1`, where `B` is freely independent for a
normalised `φ`, then the free cumulant series of `(l.map Prod.snd).prod` is the product in
`BoxedConvolution R` of the free cumulant series of the letters. No traciality or `[Ring A]`
hypothesis is needed. -/
theorem IsFreelyIndependent.toBoxed_freeCumulantSeries_list_prod {B : ι → Subalgebra R A}
    (h : IsFreelyIndependent φ B) (hφ : φ 1 = 1) {l : List (ι × A)}
    (hnodup : (l.map Prod.fst).Nodup) (hl : ∀ p ∈ l, p.2 ∈ B p.1) :
    toBoxed (freeCumulantSeries φ (l.map Prod.snd).prod) =
      (l.map fun p => toBoxed (freeCumulantSeries φ p.2)).prod := by
  induction l with
  | nil => simp [toBoxed_freeCumulantSeries_one hφ]
  | cons p l ih =>
    rw [List.map_cons, List.nodup_cons] at hnodup
    let S : Bool → Set ι := fun b => if b then {p.1} else {j | j ∈ l.map Prod.fst}
    have hdisj : Pairwise (Disjoint on S) := by
      intro b₁ b₂ hb
      cases b₁ <;> cases b₂
      · exact absurd rfl hb
      · exact Set.disjoint_singleton_right.mpr hnodup.1
      · exact Set.disjoint_singleton_left.mpr hnodup.1
      · exact absurd rfl hb
    have hB := h.biSup_disjoint hφ hdisj
    have hp : p.2 ∈ ⨆ i ∈ S true, B i :=
      (le_iSup₂ (f := fun i (_ : i ∈ S true) => B i) p.1 rfl) (hl p List.mem_cons_self)
    have htail : (l.map Prod.snd).prod ∈ ⨆ i ∈ S false, B i :=
      Subalgebra.list_prod_mem _ fun a ha => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
        have hqS : q.1 ∈ S false := List.mem_map.mpr ⟨q, hq, rfl⟩
        exact (le_iSup₂ (f := fun i (_ : i ∈ S false) => B i) q.1 hqS)
          (hl q (List.mem_cons_of_mem p hq))
    have hmul := hB.freeCumulantSeries_mul hφ (i := true) (j := false) (by decide) hp htail
    simp only [List.map_cons, List.prod_cons]
    rw [hmul, toBoxed_boxedConvolution, ih hnodup.2 fun q hq => hl q (List.mem_cons_of_mem p hq)]

/-- *Free cumulants of a finite product of free elements*: for a duplicate-free list `l` of
indices of a freely independent family `c` under a normalised `φ`, the free cumulant series of
`(l.map c).prod` is the boxed-convolution product of the free cumulant series of the factors. -/
theorem IsFreelyIndependentElements.toBoxed_freeCumulantSeries_list_prod {c : ι → A}
    (h : IsFreelyIndependentElements φ c) (hφ : φ 1 = 1) {l : List ι} (hnodup : l.Nodup) :
    toBoxed (freeCumulantSeries φ (l.map c).prod) =
      (l.map fun i => toBoxed (freeCumulantSeries φ (c i))).prod := by
  have hprod : l.map c = (l.map fun i => (i, c i)).map Prod.snd := by
    simp [List.map_map, Function.comp_def]
  have hfst : (l.map fun i => (i, c i)).map Prod.fst = l := by
    simp [List.map_map, Function.comp_def]
  rw [hprod, (isFreelyIndependentElements_iff.mp h).toBoxed_freeCumulantSeries_list_prod hφ
    (hfst.symm ▸ hnodup) fun p hp => by
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
      exact Algebra.self_mem_adjoin_singleton R (c i)]
  simp [List.map_map, Function.comp_def]

/-- *Factorisation of expectations along a duplicate-free product of free variables*: over any
semiring `A` (no `[Ring A]` needed), if `l : List (ι × A)` has pairwise distinct indices and each
`p.2 ∈ B p.1` for a freely independent family `B` under a normalised `φ`, then
`φ (l.map Prod.snd).prod = (l.map fun p => φ p.2).prod`. -/
theorem IsFreelyIndependent.apply_list_prod {B : ι → Subalgebra R A}
    (h : IsFreelyIndependent φ B) (hφ : φ 1 = 1) {l : List (ι × A)}
    (hnodup : (l.map Prod.fst).Nodup) (hl : ∀ p ∈ l, p.2 ∈ B p.1) :
    φ (l.map Prod.snd).prod = (l.map fun p => φ p.2).prod := by
  have h1 := congrArg coeffOneHom (h.toBoxed_freeCumulantSeries_list_prod hφ hnodup hl)
  simpa [map_list_prod, List.map_map, Function.comp_def, coeff_one_freeCumulantSeries] using h1

/-- *Factorisation of expectations along a duplicate-free product of free elements* over any
semiring `A`: for a duplicate-free list `l` of indices of a freely independent family `c` under a
normalised `φ`, `φ (l.map c).prod = (l.map fun i => φ (c i)).prod`. -/
theorem IsFreelyIndependentElements.apply_list_prod {c : ι → A}
    (h : IsFreelyIndependentElements φ c) (hφ : φ 1 = 1) {l : List ι} (hnodup : l.Nodup) :
    φ (l.map c).prod = (l.map fun i => φ (c i)).prod := by
  have h1 := congrArg coeffOneHom (h.toBoxed_freeCumulantSeries_list_prod hφ hnodup)
  simpa [map_list_prod, List.map_map, Function.comp_def, coeff_one_freeCumulantSeries] using h1

end FreeProduct

end TauCeti
