/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Pi
public import TauCeti.RingTheory.WittVector.Big.StructurePolynomial

public import Mathlib.Data.Fin.VecNotation

import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.MvPolynomial.Counit
import Mathlib.Algebra.Ring.InjSurj
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The big Witt ring

For a truncation set `S` and a commutative ring `R`, the big Witt ring `W_S(R)` is the set of
coordinate sequences `(x_n)_{n ∈ S}` in `R`, with the unique ring structure, natural in `R`, for
which every ghost component `w_n(x) = ∑_{d ∣ n} d * x_d ^ (n / d)`, `n ∈ S`, is a ring
homomorphism. Addition, multiplication and negation are given by the big Witt structure
polynomials `TauCeti.BigWitt.wittStructure` of `X 0 + X 1`, `X 0 * X 1` and `-X 0`, which have
integer coefficients, so the operations are defined over every commutative ring, including rings
with torsion where the ghost map is not injective. The unit has coordinates `1, 0, 0, …`.

A big Witt vector is stored as its sequence of coordinates indexed by all natural numbers,
required to vanish outside `S`; two big Witt vectors are equal exactly when all their coordinates
are. For a prime `p`, the truncation set of divisors of `p ^ (k - 1)` recovers the `p`-typical
Witt vectors of length `k`, and the truncation set of all positive integers gives the full big
Witt ring.

## Main definitions

* `TauCeti.BigWittVector S R`: the big Witt vectors of `R` indexed by the truncation set `S`, with
  its `CommRing` instance.
* `TauCeti.BigWittVector.mk' x`: the big Witt vector with coordinates `x_n`, `n ∈ S`.
* `TauCeti.BigWittVector.ghostMap`: the ghost map `W_S(R) →+* (S → R)`, `x ↦ (w_n(x))_{n ∈ S}`.
* `TauCeti.BigWittVector.map f`: the ring homomorphism `W_S(R) →+* W_S(R')` applying a ring
  homomorphism `f : R →+* R'` to every coordinate.
* `TauCeti.BigWittVector.restrict h`: for truncation sets `T ≤ S`, the ring homomorphism
  `W_S(R) →+* W_T(R)` forgetting the coordinates outside `T`.

## Main results

* `TauCeti.BigWittVector.ghostMap_injective`: the ghost map is injective when no prime in `S` is a
  zero-divisor of `R`.
* `TauCeti.BigWittVector.ghostMap_bijective_of_isUnit`: the ghost map is bijective when every
  element of `S` is a unit of `R`.
* `TauCeti.BigWittVector.ghostMap_map` and `TauCeti.BigWittVector.ghostMap_restrict`: ghost
  components commute with coefficient maps and with restriction.
* `TauCeti.BigWittVector.map_restrict`: coefficient maps commute with restriction.

## Implementation notes

The ring axioms are transported, as in Mathlib's construction of the `p`-typical Witt vectors
(`Mathlib/RingTheory/WittVector/Basic.lean`). Over an integral polynomial ring the ghost map is
injective and preserves the operations, which gives a commutative ring structure there; every
commutative ring `R` is a quotient of `ℤ[X_r : r ∈ R]` through `MvPolynomial.counit`, and the
coordinatewise map along it is surjective and preserves the operations. Natural-number and
integer multiples, powers and casts are defined recursively from the basic operations.

## References

* L. Hesselholt, *The big de Rham–Witt complex*, Acta Math. 214 (2015), §1, Proposition 1.2.
* J. Commelin and R. Y. Lewis, *Formalizing the ring of Witt vectors*, CPP 2021.
-/

public section

noncomputable section

namespace TauCeti

open BigWitt _root_.MvPolynomial Function

/-- The big Witt vectors `W_S(R)` of `R` indexed by the truncation set `S`: sequences of
coordinates `x_n`, `n ∈ S`, stored as functions on `ℕ` vanishing outside `S`. For a commutative
ring `R` it carries the ring structure making the ghost components ring homomorphisms. -/
structure BigWittVector (S : TruncationSet) (R : Type*) [Zero R] where
  /-- The Witt coordinates of a big Witt vector. They vanish outside the truncation set. -/
  coeff : ℕ → R
  /-- A big Witt vector has no coordinates outside its truncation set. -/
  coeff_eq_zero_of_notMem : ∀ n ∉ S, coeff n = 0

namespace BigWittVector

variable {S T U : TruncationSet} {R R' R'' : Type*}

section Zero

variable [Zero R]

theorem coeff_injective : Injective (coeff : BigWittVector S R → ℕ → R) := by
  rintro ⟨x, -⟩ ⟨y, -⟩ rfl
  rfl

/-- Big Witt vectors are equal when all their coordinates are. -/
@[ext]
theorem ext {x y : BigWittVector S R} (h : ∀ n, x.coeff n = y.coeff n) : x = y :=
  coeff_injective (funext h)

instance [Subsingleton R] : Subsingleton (BigWittVector S R) :=
  ⟨fun _ _ ↦ ext fun _ ↦ Subsingleton.elim _ _⟩

/-- The big Witt vectors indexed by the empty truncation set have no coordinates. -/
instance : Subsingleton (BigWittVector ⊥ R) :=
  ⟨fun x y ↦ ext fun n ↦ by
    rw [x.coeff_eq_zero_of_notMem n TruncationSet.notMem_bot,
      y.coeff_eq_zero_of_notMem n TruncationSet.notMem_bot]⟩

/-- The big Witt vector with coordinates `x_n`, `n ∈ S`: the coordinates of `x` outside `S` are
discarded. -/
def mk' (x : ℕ → R) : BigWittVector S R :=
  ⟨(S : Set ℕ).indicator x, fun _ hn ↦ Set.indicator_of_notMem hn _⟩

theorem coeff_mk' (x : ℕ → R) (n : ℕ) :
    (mk' x : BigWittVector S R).coeff n = (S : Set ℕ).indicator x n :=
  (rfl)

@[simp]
theorem coeff_mk'_of_mem (x : ℕ → R) {n : ℕ} (hn : n ∈ S) :
    (mk' x : BigWittVector S R).coeff n = x n :=
  Set.indicator_of_mem (SetLike.mem_coe.2 hn) _

/-- Every big Witt vector is constructed from its coordinates. -/
@[simp]
theorem mk'_coeff (x : BigWittVector S R) : mk' x.coeff = x := by
  ext n
  by_cases hn : n ∈ S
  · exact coeff_mk'_of_mem _ hn
  · rw [x.coeff_eq_zero_of_notMem n hn]
    exact Set.indicator_of_notMem hn _

end Zero

variable [CommRing R] [CommRing R'] [CommRing R'']

/-! ### The ring operations

The operations are first defined as local instances, from which the `CommRing` instance is
assembled; afterwards only the `CommRing` instance is in use. -/

section Construction

/-- Evaluation of the big Witt structure polynomials of `Φ` at a family of big Witt vectors. -/
private def peval {idx : Type*} (Φ : MvPolynomial idx ℤ) (x : idx → BigWittVector S R) :
    BigWittVector S R where
  coeff := (S : Set ℕ).indicator fun n ↦
    aeval (fun ik : idx × ℕ ↦ (x ik.fst).coeff ik.snd) (wittStructure Φ n)
  coeff_eq_zero_of_notMem _ hn := Set.indicator_of_notMem hn _

private abbrev instZeroAux : Zero (BigWittVector S R) :=
  ⟨⟨0, fun _ _ ↦ rfl⟩⟩

private abbrev instOneAux : One (BigWittVector S R) :=
  ⟨mk' (Pi.single 1 1)⟩

private abbrev instAddAux : Add (BigWittVector S R) :=
  ⟨fun x y ↦ peval (X 0 + X 1) ![x, y]⟩

private abbrev instMulAux : Mul (BigWittVector S R) :=
  ⟨fun x y ↦ peval (X 0 * X 1) ![x, y]⟩

private abbrev instNegAux : Neg (BigWittVector S R) :=
  ⟨fun x ↦ peval (-X 0) ![x]⟩

attribute [local instance] instZeroAux instOneAux instAddAux instMulAux instNegAux

private abbrev instSubAux : Sub (BigWittVector S R) :=
  ⟨fun x y ↦ x + -y⟩

private abbrev instNSMulAux : SMul ℕ (BigWittVector S R) :=
  ⟨nsmulRec⟩

private abbrev instZSMulAux : SMul ℤ (BigWittVector S R) :=
  ⟨zsmulRec⟩

private abbrev instPowAux : Pow (BigWittVector S R) ℕ :=
  ⟨fun x n ↦ npowRec n x⟩

private abbrev instNatCastAux : NatCast (BigWittVector S R) :=
  ⟨Nat.unaryCast⟩

private abbrev instIntCastAux : IntCast (BigWittVector S R) :=
  letI := instNatCastAux (S := S) (R := R)
  ⟨Int.castDef⟩

attribute [local instance] instSubAux instNSMulAux instZSMulAux instPowAux instNatCastAux
  instIntCastAux

private theorem coeff_one_aux (n : ℕ) :
    (1 : BigWittVector S R).coeff n = (S : Set ℕ).indicator (Pi.single 1 1) n :=
  rfl

private theorem add_def (x y : BigWittVector S R) : x + y = peval (X 0 + X 1) ![x, y] :=
  rfl

private theorem mul_def (x y : BigWittVector S R) : x * y = peval (X 0 * X 1) ![x, y] :=
  rfl

private theorem neg_def (x : BigWittVector S R) : -x = peval (-X 0) ![x] :=
  rfl

private theorem coeff_peval_of_mem {idx : Type*} (Φ : MvPolynomial idx ℤ)
    (x : idx → BigWittVector S R) {n : ℕ} (hn : n ∈ S) :
    (peval Φ x).coeff n =
      aeval (fun ik : idx × ℕ ↦ (x ik.fst).coeff ik.snd) (wittStructure Φ n) := by
  dsimp only [peval]
  exact Set.indicator_of_mem (SetLike.mem_coe.2 hn) _

/-! ### Ghost components of the operations -/

/-- The ghost components of a big Witt vector, before the ring structure is available. -/
private def ghostFun (x : BigWittVector S R) : S → R :=
  fun n ↦ ghostPolynomial n x.coeff

private theorem ghostFun_peval {idx : Type*} (Φ : MvPolynomial idx ℤ)
    (x : idx → BigWittVector S R) :
    ghostFun (peval Φ x) = fun n ↦ aeval (fun i ↦ ghostFun (x i) n) Φ := by
  funext n
  exact (ghostPolynomial_congr fun d hd ↦ coeff_peval_of_mem Φ x (S.mem_of_dvd n.prop hd)).trans
    (ghostPolynomial_aeval_wittStructure Φ _ (S.ne_zero_of_mem n.prop))

private theorem ghostFun_zero : ghostFun (0 : BigWittVector S R) = 0 :=
  funext fun n ↦ ghostPolynomial_zero_right n

private theorem ghostFun_one : ghostFun (1 : BigWittVector S R) = 1 :=
  funext fun n ↦
    (ghostPolynomial_congr fun _ hd ↦ coeff_mk'_of_mem _ (S.mem_of_dvd n.prop hd)).trans
      (ghostPolynomial_single_one (S.ne_zero_of_mem n.prop))

private theorem ghostFun_add (x y : BigWittVector S R) :
    ghostFun (x + y) = ghostFun x + ghostFun y := by
  rw [add_def, ghostFun_peval]
  funext n
  simp

private theorem ghostFun_mul (x y : BigWittVector S R) :
    ghostFun (x * y) = ghostFun x * ghostFun y := by
  rw [mul_def, ghostFun_peval]
  funext n
  simp

private theorem ghostFun_neg (x : BigWittVector S R) : ghostFun (-x) = -ghostFun x := by
  rw [neg_def, ghostFun_peval]
  funext n
  simp

private theorem ghostFun_sub (x y : BigWittVector S R) :
    ghostFun (x - y) = ghostFun x - ghostFun y := by
  rw [sub_eq_add_neg, ← ghostFun_neg, ← ghostFun_add]
  rfl

private theorem ghostFun_nsmul (n : ℕ) (x : BigWittVector S R) :
    ghostFun (n • x) = n • ghostFun x := by
  induction n with
  | zero => exact ghostFun_zero.trans (zero_nsmul _).symm
  | succ n ih => exact (ghostFun_add _ _).trans (by rw [succ_nsmul, ← ih]; rfl)

private theorem ghostFun_zsmul (n : ℤ) (x : BigWittVector S R) :
    ghostFun (n • x) = n • ghostFun x := by
  cases n with
  | ofNat n => exact (ghostFun_nsmul n x).trans (natCast_zsmul _ n).symm
  | negSucc n =>
    exact (ghostFun_neg _).trans (by rw [negSucc_zsmul, ← ghostFun_nsmul]; rfl)

private theorem ghostFun_pow (x : BigWittVector S R) (n : ℕ) :
    ghostFun (x ^ n) = ghostFun x ^ n := by
  induction n with
  | zero => exact ghostFun_one.trans (pow_zero _).symm
  | succ n ih => exact (ghostFun_mul _ _).trans (by rw [pow_succ, ← ih]; rfl)

private theorem ghostFun_natCast (n : ℕ) : ghostFun (n : BigWittVector S R) = n := by
  induction n with
  | zero => exact ghostFun_zero.trans Nat.cast_zero.symm
  | succ n ih =>
    exact (ghostFun_add _ _).trans (by rw [Nat.cast_succ, ← ih, ← ghostFun_one]; rfl)

private theorem ghostFun_intCast (n : ℤ) : ghostFun (n : BigWittVector S R) = n := by
  cases n with
  | ofNat n => exact (ghostFun_natCast n).trans (Int.cast_natCast n).symm
  | negSucc n =>
    exact (ghostFun_neg _).trans (by rw [Int.cast_negSucc, ← ghostFun_natCast])

private theorem ghostFun_injective (hS : ∀ p ∈ S, p.Prime → IsSMulRegular R (p : R)) :
    Injective (ghostFun : BigWittVector S R → S → R) := by
  intro x y h
  ext n
  by_cases hn : n ∈ S
  · exact (eqOn_ghostPolynomial_iff hS).1 (fun k hk ↦ congrFun h ⟨k, hk⟩) hn
  · rw [x.coeff_eq_zero_of_notMem n hn, y.coeff_eq_zero_of_notMem n hn]

/-! ### Coordinatewise maps -/

/-- Applying a ring homomorphism to every coordinate, before the ring structure is available. -/
private def mapFun (f : R →+* R') (x : BigWittVector S R) : BigWittVector S R' :=
  ⟨f ∘ x.coeff, fun n hn ↦ by simp [x.coeff_eq_zero_of_notMem n hn]⟩

private theorem mapFun_peval (f : R →+* R') {idx : Type*} (Φ : MvPolynomial idx ℤ)
    (x : idx → BigWittVector S R) : mapFun f (peval Φ x) = peval Φ (mapFun f ∘ x) := by
  ext n
  by_cases hn : n ∈ S
  · simp only [mapFun, comp_apply, coeff_peval_of_mem Φ _ hn]
    exact comp_aeval_apply _ f.toIntAlgHom (wittStructure Φ n)
  · rw [coeff_eq_zero_of_notMem _ n hn, coeff_eq_zero_of_notMem _ n hn]

private theorem mapFun_surjective (f : R →+* R') (hf : Surjective f) :
    Surjective (mapFun f : BigWittVector S R → BigWittVector S R') := by
  intro x
  refine ⟨mk' (surjInv hf ∘ x.coeff), ext fun n ↦ ?_⟩
  by_cases hn : n ∈ S
  · simp [mapFun, hn, surjInv_eq hf]
  · simp [coeff_eq_zero_of_notMem _ n hn]

private theorem mapFun_zero (f : R →+* R') : mapFun f (0 : BigWittVector S R) = 0 :=
  ext fun _ ↦ map_zero f

private theorem mapFun_one (f : R →+* R') : mapFun f (1 : BigWittVector S R) = 1 := by
  ext n
  simp only [mapFun, comp_apply, coeff_one_aux]
  rcases eq_or_ne n 1 with rfl | h1
  · by_cases h : 1 ∈ (S : Set ℕ) <;> simp [h]
  · by_cases h : n ∈ (S : Set ℕ) <;> simp [h, h1]

private theorem mapFun_add (f : R →+* R') (x y : BigWittVector S R) :
    mapFun f (x + y) = mapFun f x + mapFun f y := by
  rw [add_def, add_def, mapFun_peval]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem mapFun_mul (f : R →+* R') (x y : BigWittVector S R) :
    mapFun f (x * y) = mapFun f x * mapFun f y := by
  rw [mul_def, mul_def, mapFun_peval]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem mapFun_neg (f : R →+* R') (x : BigWittVector S R) :
    mapFun f (-x) = -mapFun f x := by
  rw [neg_def, neg_def, mapFun_peval]
  congr 1
  funext i
  fin_cases i
  rfl

private theorem mapFun_sub (f : R →+* R') (x y : BigWittVector S R) :
    mapFun f (x - y) = mapFun f x - mapFun f y :=
  (mapFun_add f x (-y)).trans (congrArg (mapFun f x + ·) (mapFun_neg f y))

private theorem mapFun_nsmul (f : R →+* R') (n : ℕ) (x : BigWittVector S R) :
    mapFun f (n • x) = n • mapFun f x := by
  induction n with
  | zero => exact mapFun_zero f
  | succ n ih => exact (mapFun_add f _ _).trans (congrArg (· + mapFun f x) ih)

private theorem mapFun_zsmul (f : R →+* R') (n : ℤ) (x : BigWittVector S R) :
    mapFun f (n • x) = n • mapFun f x := by
  cases n with
  | ofNat n => exact mapFun_nsmul f n x
  | negSucc n => exact (mapFun_neg f _).trans (congrArg (-·) (mapFun_nsmul f (n + 1) x))

private theorem mapFun_pow (f : R →+* R') (x : BigWittVector S R) (n : ℕ) :
    mapFun f (x ^ n) = mapFun f x ^ n := by
  induction n with
  | zero => exact mapFun_one f
  | succ n ih => exact (mapFun_mul f _ _).trans (congrArg (· * mapFun f x) ih)

private theorem mapFun_natCast (f : R →+* R') (n : ℕ) :
    mapFun f (n : BigWittVector S R) = n := by
  induction n with
  | zero => exact mapFun_zero f
  | succ n ih => exact (mapFun_add f _ _).trans (congrArg₂ (· + ·) ih (mapFun_one f))

private theorem mapFun_intCast (f : R →+* R') (n : ℤ) :
    mapFun f (n : BigWittVector S R) = n := by
  cases n with
  | ofNat n => exact mapFun_natCast f n
  | negSucc n => exact (mapFun_neg f _).trans (congrArg (-·) (mapFun_natCast f (n + 1)))

/-! ### The commutative ring structure -/

/-- Over an integral polynomial ring the ghost map is injective, so the ring axioms can be pulled
back from the product ring `S → MvPolynomial σ ℤ`. -/
private abbrev commRingAux (σ : Type*) : CommRing (BigWittVector S (MvPolynomial σ ℤ)) :=
  (ghostFun_injective fun _ _ hp ↦ .of_ne_zero (Nat.cast_ne_zero.2 hp.ne_zero)).commRing _
    ghostFun_zero ghostFun_one ghostFun_add ghostFun_mul ghostFun_neg ghostFun_sub
    ghostFun_nsmul ghostFun_zsmul ghostFun_pow ghostFun_natCast ghostFun_intCast

/-- The commutative ring structure on the big Witt vectors, pushed forward from the integral
polynomial ring `ℤ[X_r : r ∈ R]` along the surjection `MvPolynomial.counit R`. It is the
`CommRing` instance on `BigWittVector S R`; its operations are described by `coeff_zero`,
`coeff_one`, `coeff_add_of_mem`, `coeff_mul_of_mem` and `coeff_neg_of_mem`. -/
@[instance_reducible]
def commRing : CommRing (BigWittVector S R) :=
  letI := commRingAux (S := S) R
  (mapFun_surjective _ (counit_surjective R)).commRing _ (mapFun_zero _) (mapFun_one _)
    (mapFun_add _) (mapFun_mul _) (mapFun_neg _) (mapFun_sub _) (mapFun_nsmul _)
    (mapFun_zsmul _) (mapFun_pow _) (mapFun_natCast _) (mapFun_intCast _)

end Construction

instance : CommRing (BigWittVector S R) :=
  commRing

private theorem add_eq_peval (x y : BigWittVector S R) : x + y = peval (X 0 + X 1) ![x, y] :=
  rfl

private theorem mul_eq_peval (x y : BigWittVector S R) : x * y = peval (X 0 * X 1) ![x, y] :=
  rfl

@[simp]
theorem coeff_zero (n : ℕ) : (0 : BigWittVector S R).coeff n = 0 :=
  (rfl)

theorem coeff_one (n : ℕ) :
    (1 : BigWittVector S R).coeff n = (S : Set ℕ).indicator (Pi.single 1 1) n :=
  (rfl)

@[simp]
theorem coeff_one_one (h : 1 ∈ S) : (1 : BigWittVector S R).coeff 1 = 1 := by
  simp [coeff_one, Set.indicator_of_mem (SetLike.mem_coe.2 h)]

@[simp]
theorem coeff_one_of_ne_one {n : ℕ} (hn : n ≠ 1) : (1 : BigWittVector S R).coeff n = 0 := by
  rw [coeff_one]
  by_cases h : n ∈ (S : Set ℕ)
  · simp [Set.indicator_of_mem h, hn]
  · exact Set.indicator_of_notMem h _

/-- The coordinates of a sum are the big Witt structure polynomials of `X 0 + X 1` evaluated at the
coordinates of the summands. -/
theorem coeff_add_of_mem (x y : BigWittVector S R) {n : ℕ} (hn : n ∈ S) :
    (x + y).coeff n = aeval (fun ik : Fin 2 × ℕ ↦ (![x, y] ik.fst).coeff ik.snd)
      (wittStructure (X 0 + X 1) n) :=
  coeff_peval_of_mem _ _ hn

/-- The coordinates of a product are the big Witt structure polynomials of `X 0 * X 1` evaluated
at the coordinates of the factors. -/
theorem coeff_mul_of_mem (x y : BigWittVector S R) {n : ℕ} (hn : n ∈ S) :
    (x * y).coeff n = aeval (fun ik : Fin 2 × ℕ ↦ (![x, y] ik.fst).coeff ik.snd)
      (wittStructure (X 0 * X 1) n) :=
  coeff_peval_of_mem _ _ hn

/-- The coordinates of a negative are the big Witt structure polynomials of `-X 0` evaluated at the
coordinates of the vector. -/
theorem coeff_neg_of_mem (x : BigWittVector S R) {n : ℕ} (hn : n ∈ S) :
    (-x).coeff n = aeval (fun ik : Fin 1 × ℕ ↦ (![x] ik.fst).coeff ik.snd)
      (wittStructure (-X 0) n) :=
  coeff_peval_of_mem _ _ hn

/-! ### The ghost map -/

/-- The ghost map `W_S(R) →+* (S → R)`, sending a big Witt vector `x` to its ghost components
`w_n(x) = ∑_{d ∣ n} d * x_d ^ (n / d)`, `n ∈ S`. -/
def ghostMap : BigWittVector S R →+* (S → R) where
  toFun := ghostFun
  map_zero' := ghostFun_zero
  map_one' := ghostFun_one
  map_add' := ghostFun_add
  map_mul' := ghostFun_mul

theorem ghostMap_apply (x : BigWittVector S R) (n : S) :
    ghostMap x n = ghostPolynomial n x.coeff :=
  (rfl)

/-- **Injectivity of the ghost map.** If no prime in `S` is a zero-divisor of `R`, a big Witt
vector is determined by its ghost components. -/
theorem ghostMap_injective (hS : ∀ p ∈ S, p.Prime → IsSMulRegular R (p : R)) :
    Injective (ghostMap : BigWittVector S R →+* (S → R)) :=
  ghostFun_injective hS

/-- If every element of `S` is a unit of `R`, the ghost map is bijective: every sequence indexed
by `S` is the sequence of ghost components of exactly one big Witt vector. -/
theorem ghostMap_bijective_of_isUnit (hS : ∀ n ∈ S, IsUnit (n : R)) :
    Bijective (ghostMap : BigWittVector S R →+* (S → R)) := by
  classical
  refine ⟨ghostMap_injective fun p hp _ ↦ (hS p hp).isSMulRegular R, fun b ↦ ?_⟩
  obtain ⟨x, hx⟩ := exists_ghostPolynomial_eq_of_isUnit hS
    fun n ↦ if h : n ∈ S then b ⟨n, h⟩ else 0
  refine ⟨mk' x, funext fun n ↦ ?_⟩
  rw [ghostMap_apply]
  refine (ghostPolynomial_congr fun d hd ↦ coeff_mk'_of_mem x (S.mem_of_dvd n.prop hd)).trans ?_
  simp [hx n n.prop]

/-! ### Functoriality in the coefficients -/

/-- The ring homomorphism `W_S(R) →+* W_S(R')` induced by a ring homomorphism `f : R →+* R'`,
applying `f` to every coordinate. -/
def map (f : R →+* R') : BigWittVector S R →+* BigWittVector S R' where
  toFun := mapFun f
  map_zero' := mapFun_zero f
  map_one' := mapFun_one f
  map_add' := mapFun_add f
  map_mul' := mapFun_mul f

@[simp]
theorem coeff_map (f : R →+* R') (x : BigWittVector S R) (n : ℕ) :
    (map f x).coeff n = f (x.coeff n) :=
  (rfl)

variable (S R) in
@[simp]
theorem map_id : map (RingHom.id R) = RingHom.id (BigWittVector S R) := by
  ext
  simp

theorem map_comp (g : R' →+* R'') (f : R →+* R') :
    map (S := S) (g.comp f) = (map g).comp (map f) := by
  ext
  simp

theorem map_injective (f : R →+* R') (hf : Injective f) :
    Injective (map f : BigWittVector S R → BigWittVector S R') :=
  fun _ _ h ↦ ext fun n ↦ hf (by simpa using congrArg (coeff · n) h)

theorem map_surjective (f : R →+* R') (hf : Surjective f) :
    Surjective (map f : BigWittVector S R → BigWittVector S R') :=
  mapFun_surjective f hf

/-- Ghost components commute with coefficient maps. -/
@[simp]
theorem ghostMap_map (f : R →+* R') (x : BigWittVector S R) (n : S) :
    ghostMap (map f x) n = f (ghostMap x n) := by
  rw [ghostMap_apply, ghostMap_apply, map_ghostPolynomial]
  exact ghostPolynomial_congr fun d _ ↦ coeff_map f x d

/-! ### Restriction to a smaller truncation set -/

/-- Forgetting the coordinates outside a smaller truncation set, before the ring structure is
available. -/
private def restrictFun (_ : T ≤ S) (x : BigWittVector S R) : BigWittVector T R :=
  mk' x.coeff

private theorem restrictFun_peval (h : T ≤ S) {idx : Type*} (Φ : MvPolynomial idx ℤ)
    (x : idx → BigWittVector S R) :
    restrictFun h (peval Φ x) = peval Φ (restrictFun h ∘ x) := by
  ext n
  by_cases hn : n ∈ T
  · rw [coeff_peval_of_mem Φ _ hn]
    dsimp only [restrictFun]
    rw [coeff_mk'_of_mem _ hn, coeff_peval_of_mem Φ _ (h hn)]
    refine aeval_wittStructure_congr Φ fun i d hd ↦ ?_
    dsimp only [comp_apply, restrictFun]
    exact (coeff_mk'_of_mem _ (T.mem_of_dvd hn hd)).symm
  · rw [coeff_eq_zero_of_notMem _ n hn, coeff_eq_zero_of_notMem _ n hn]

/-- For truncation sets `T ≤ S`, the restriction `W_S(R) →+* W_T(R)`, which forgets the
coordinates outside `T`. -/
def restrict (h : T ≤ S) : BigWittVector S R →+* BigWittVector T R where
  toFun := restrictFun h
  map_zero' := ext fun n ↦ Set.indicator_apply_eq_zero.2 fun _ ↦ coeff_zero n
  map_one' := ext fun n ↦ by
    by_cases hn : n ∈ T
    · simp [restrictFun, coeff_one, hn, h hn]
    · simp [coeff_eq_zero_of_notMem _ n hn]
  map_add' x y := by
    rw [add_eq_peval, add_eq_peval, restrictFun_peval]
    congr 1
    funext i
    fin_cases i <;> rfl
  map_mul' x y := by
    rw [mul_eq_peval, mul_eq_peval, restrictFun_peval]
    congr 1
    funext i
    fin_cases i <;> rfl

theorem coeff_restrict (h : T ≤ S) (x : BigWittVector S R) (n : ℕ) :
    (restrict h x).coeff n = (T : Set ℕ).indicator x.coeff n :=
  (rfl)

@[simp]
theorem coeff_restrict_of_mem (h : T ≤ S) (x : BigWittVector S R) {n : ℕ} (hn : n ∈ T) :
    (restrict h x).coeff n = x.coeff n :=
  Set.indicator_of_mem (SetLike.mem_coe.2 hn) _

/-- Ghost components commute with restriction. -/
@[simp]
theorem ghostMap_restrict (h : T ≤ S) (x : BigWittVector S R) (n : T) :
    ghostMap (restrict h x) n = ghostMap x (Set.inclusion h n) := by
  rw [ghostMap_apply, ghostMap_apply]
  exact ghostPolynomial_congr fun d hd ↦ coeff_restrict_of_mem h x (T.mem_of_dvd n.prop hd)

@[simp]
theorem restrict_self : restrict (le_refl S) = RingHom.id (BigWittVector S R) := by
  ext x n
  by_cases hn : n ∈ S
  · simp [hn]
  · simp [coeff_eq_zero_of_notMem _ n hn]

theorem restrict_comp_restrict (hUT : U ≤ T) (hTS : T ≤ S) :
    (restrict hUT).comp (restrict hTS) = restrict (R := R) (hUT.trans hTS) := by
  ext x n
  by_cases hn : n ∈ U
  · simp [hn, hUT hn]
  · simp [coeff_eq_zero_of_notMem _ n hn]

/-- Restriction is natural in the coefficient ring. -/
theorem map_comp_restrict (h : T ≤ S) (f : R →+* R') :
    (map f).comp (restrict h) = (restrict h).comp (map f) := by
  ext x n
  by_cases hn : n ∈ T
  · simp [hn]
  · simp [coeff_eq_zero_of_notMem _ n hn]

/-- Coefficient maps commute with restriction to smaller truncation sets. -/
theorem map_restrict (h : T ≤ S) (f : R →+* R') (x : BigWittVector S R) :
    map f (restrict h x) = restrict h (map f x) :=
  DFunLike.congr_fun (map_comp_restrict h f) x

end BigWittVector

end TauCeti
