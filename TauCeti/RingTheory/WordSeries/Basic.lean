/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.FreeMonoid.Antidiagonal
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.Pi

/-!
# Noncommutative formal power series on words

`TauCeti.WordSeries ι R` consists of arbitrary coefficient functions on `FreeMonoid ι`.
Multiplication sums over concatenation factorizations of a word; it never permutes letters.
The empty word indexes the constant coefficient. Coefficients may lie in a noncommutative
semiring, and the alphabet need not be finite.

The coefficient, monomial, constant-series and variable APIs describe the resulting semiring.
This is the algebra in which joint free cumulant series can retain the order of their inputs.
No summability or analytic convergence is involved.

The construction of the semiring follows Mathlib's `MvPowerSeries` construction, replacing
commutative exponent addition by word concatenation and using the finite word antidiagonal.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 16.
-/

public section

noncomputable section

namespace TauCeti

/-- Formal series in noncommuting letters `ι`, with coefficients in `R`.
The carrier is exposed so the inherited pointwise additive and module instances remain
definitionally coherent with the semiring structure. -/
@[expose] def WordSeries (ι R : Type*) := FreeMonoid ι → R

namespace WordSeries

variable {ι R : Type*}

instance [Zero R] : Zero (WordSeries ι R) := inferInstanceAs (Zero (FreeMonoid ι → R))
instance [AddCommMonoid R] : AddCommMonoid (WordSeries ι R) :=
  inferInstanceAs (AddCommMonoid (FreeMonoid ι → R))
instance [AddCommGroup R] : AddCommGroup (WordSeries ι R) :=
  inferInstanceAs (AddCommGroup (FreeMonoid ι → R))
instance {S : Type*} [Semiring S] [AddCommMonoid R] [Module S R] :
    Module S (WordSeries ι R) := inferInstanceAs (Module S (FreeMonoid ι → R))
instance [Nontrivial R] : Nontrivial (WordSeries ι R) :=
  inferInstanceAs (Nontrivial (FreeMonoid ι → R))

/-- The coefficient of the word `w`. -/
def coeff (w : FreeMonoid ι) (f : WordSeries ι R) : R := f w

/-- Form a series from its word coefficients. -/
def mk (f : FreeMonoid ι → R) : WordSeries ι R := f

@[simp] theorem coeff_mk (f : FreeMonoid ι → R) (w : FreeMonoid ι) :
    coeff w (mk f) = f w := (rfl)

@[simp] theorem mk_coeff (f : WordSeries ι R) : mk (fun w => coeff w f) = f := (rfl)

@[ext] theorem ext {f g : WordSeries ι R} (h : ∀ w, coeff w f = coeff w g) : f = g :=
  funext h

@[simp] theorem coeff_zero [Zero R] (w : FreeMonoid ι) :
    coeff w (0 : WordSeries ι R) = 0 := (rfl)

@[simp] theorem coeff_add [AddCommMonoid R] (w : FreeMonoid ι) (f g : WordSeries ι R) :
    coeff w (f + g) = coeff w f + coeff w g := (rfl)

@[simp] theorem coeff_neg [AddCommGroup R] (w : FreeMonoid ι) (f : WordSeries ι R) :
    coeff w (-f) = -coeff w f := (rfl)

@[simp] theorem coeff_smul {S : Type*} [Semiring S] [AddCommMonoid R] [Module S R]
    (w : FreeMonoid ι) (r : S) (f : WordSeries ι R) : coeff w (r • f) = r • coeff w f := (rfl)

/-- A series supported on one word. -/
def monomial [Zero R] (w : FreeMonoid ι) (r : R) : WordSeries ι R := by
  classical
  exact mk (fun v => if v = w then r else 0)

open Classical in
@[simp] theorem coeff_monomial [Zero R] (v w : FreeMonoid ι) (r : R) :
    coeff v (monomial w r) = if v = w then r else 0 := by
  classical
  rfl

@[simp] theorem monomial_zero [Zero R] (w : FreeMonoid ι) : monomial w (0 : R) = 0 := by
  ext v
  simp

@[simp] theorem monomial_add [AddCommMonoid R] (w : FreeMonoid ι) (r s : R) :
    monomial w (r + s) = monomial w r + monomial w s := by
  classical
  ext v
  by_cases h : v = w <;> simp [h]

section Semiring

variable [Semiring R]

instance : One (WordSeries ι R) := ⟨monomial 1 1⟩

open Classical in
@[simp] theorem coeff_one (w : FreeMonoid ι) :
    coeff w (1 : WordSeries ι R) = if w = 1 then 1 else 0 := coeff_monomial ..

instance : AddMonoidWithOne (WordSeries ι R) where
  natCast n := monomial 1 n
  natCast_zero := by simp
  natCast_succ n := by simp [Nat.cast_add, monomial_add]; rfl

instance : Mul (WordSeries ι R) :=
  ⟨fun f g => mk fun w => ∑ p ∈ Finset.mulAntidiagonal w, coeff p.1 f * coeff p.2 g⟩

/-- Concatenation convolution: a coefficient sums over every ordered factorization. -/
theorem coeff_mul (w : FreeMonoid ι) (f g : WordSeries ι R) :
    coeff w (f * g) = ∑ p ∈ Finset.mulAntidiagonal w, coeff p.1 f * coeff p.2 g := (rfl)

private theorem zero_mul_aux (f : WordSeries ι R) : 0 * f = 0 := by
  ext w
  simp [coeff_mul]

private theorem mul_zero_aux (f : WordSeries ι R) : f * 0 = 0 := by
  ext w
  simp [coeff_mul]

private theorem one_mul_aux (f : WordSeries ι R) : 1 * f = f := by
  classical
  ext w
  rw [coeff_mul, Finset.sum_eq_single (1, w)]
  · simp
  · intro p hp hne
    have hp := Finset.mem_mulAntidiagonal.mp hp
    have : p.1 ≠ 1 := by
      intro h
      apply hne
      exact Prod.ext h (by simpa [h] using hp)
    simp [this]
  · simp

private theorem mul_one_aux (f : WordSeries ι R) : f * 1 = f := by
  classical
  ext w
  rw [coeff_mul, Finset.sum_eq_single (w, 1)]
  · simp
  · intro p hp hne
    have hp := Finset.mem_mulAntidiagonal.mp hp
    have : p.2 ≠ 1 := by
      intro h
      apply hne
      exact Prod.ext (by simpa [h] using hp) h
    simp [this]
  · simp

private theorem mul_add_aux (f g h : WordSeries ι R) : f * (g + h) = f * g + f * h := by
  ext w
  simp [coeff_mul, mul_add, Finset.sum_add_distrib]

private theorem add_mul_aux (f g h : WordSeries ι R) : (f + g) * h = f * h + g * h := by
  ext w
  simp [coeff_mul, add_mul, Finset.sum_add_distrib]

private theorem mul_assoc_aux (f g h : WordSeries ι R) : f * g * h = f * (g * h) := by
  ext w
  classical
  simp only [coeff_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_sigma']
  apply Finset.sum_nbij' (fun ⟨⟨_, j⟩, ⟨k, l⟩⟩ => ⟨(k, l * j), (l, j)⟩)
    (fun ⟨⟨i, _⟩, ⟨k, l⟩⟩ => ⟨(i * k, l), (i, k)⟩) <;>
    aesop (add simp [mul_assoc])

instance : Semiring (WordSeries ι R) where
  one_mul := by exact one_mul_aux
  mul_one := by exact mul_one_aux
  mul_zero := by exact mul_zero_aux
  zero_mul := by exact zero_mul_aux
  left_distrib := by exact mul_add_aux
  right_distrib := by exact add_mul_aux
  mul_assoc := by exact mul_assoc_aux

/-- Monomial multiplication concatenates the words, without commuting the coefficients. -/
@[simp] theorem monomial_mul_monomial (u v : FreeMonoid ι) (r s : R) :
    monomial u r * monomial v s = monomial (u * v) (r * s) := by
  classical
  ext w
  by_cases hw : w = u * v
  · subst w
    rw [coeff_mul, Finset.sum_eq_single (u, v)]
    · simp
    · intro p _ hne
      by_cases h₁ : p.1 = u <;> by_cases h₂ : p.2 = v <;> simp_all [Prod.ext_iff]
    · simp
  · rw [coeff_mul, coeff_monomial, ite_eq_right hw]
    apply Finset.sum_eq_zero
    intro p hp
    have hp := Finset.mem_mulAntidiagonal.mp hp
    by_cases h₁ : p.1 = u <;> by_cases h₂ : p.2 = v <;> simp_all

/-- Multiplying on the left by a monomial prefixes its word and multiplies the coefficient
on the left. -/
@[simp] theorem coeff_monomial_mul (u v : FreeMonoid ι) (r : R) (f : WordSeries ι R) :
    coeff (u * v) (monomial u r * f) = r * coeff v f := by
  classical
  rw [coeff_mul, Finset.sum_eq_single (u, v)]
  · simp
  · intro p hp hne
    have hp := Finset.mem_mulAntidiagonal.mp hp
    have : p.1 ≠ u := by
      intro h
      apply hne
      exact Prod.ext h (by simpa [h] using hp)
    simp [this]
  · simp

/-- Multiplying on the right by a monomial appends its word and multiplies the coefficient
on the right. -/
@[simp] theorem coeff_mul_monomial (u v : FreeMonoid ι) (f : WordSeries ι R) (r : R) :
    coeff (u * v) (f * monomial v r) = coeff u f * r := by
  classical
  rw [coeff_mul, Finset.sum_eq_single (u, v)]
  · simp
  · intro p hp hne
    have hp := Finset.mem_mulAntidiagonal.mp hp
    have : p.2 ≠ v := by
      intro h
      apply hne
      exact Prod.ext (by simpa [h] using hp) h
    simp [this]
  · simp

/-- Constant series, supported on the empty word. -/
def C : R →+* WordSeries ι R where
  toFun := monomial 1
  map_one' := rfl
  map_zero' := monomial_zero _
  map_add' := monomial_add _
  map_mul' r s := by simp

open Classical in
@[simp] theorem coeff_C (w : FreeMonoid ι) (r : R) :
    coeff w (C r) = if w = 1 then r else 0 := coeff_monomial ..

@[simp] theorem coeff_C_mul (w : FreeMonoid ι) (r : R) (f : WordSeries ι R) :
    coeff w (C r * f) = r * coeff w f := by
  simpa [C] using coeff_monomial_mul 1 w r f

@[simp] theorem coeff_mul_C (w : FreeMonoid ι) (f : WordSeries ι R) (r : R) :
    coeff w (f * C r) = coeff w f * r := by
  simpa [C] using coeff_mul_monomial w 1 f r

/-- The series consisting of a single letter with coefficient one. -/
def X (i : ι) : WordSeries ι R := monomial (FreeMonoid.of i) 1

open Classical in
@[simp] theorem coeff_X (w : FreeMonoid ι) (i : ι) :
    coeff w (X i : WordSeries ι R) = if w = FreeMonoid.of i then 1 else 0 := coeff_monomial ..

/-- A product of letter series is the monomial of the displayed word, in the same order. -/
theorem list_prod_X (w : List ι) :
    (w.map (X (R := R))).prod = monomial (FreeMonoid.ofList w) 1 := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [List.map_cons, List.prod_cons, ih, X, monomial_mul_monomial,
      one_mul, FreeMonoid.ofList_cons]

/-- The coefficient of the empty word, as a ring homomorphism. -/
def constantCoeff : WordSeries ι R →+* R where
  toFun := coeff 1
  map_zero' := coeff_zero _
  map_one' := by simp
  map_add' := coeff_add _
  map_mul' f g := by
    rw [coeff_mul]
    apply Finset.sum_eq_single_of_mem (1, 1) (by simp)
    intro p hp hne
    have hp := congrArg FreeMonoid.toList (Finset.mem_mulAntidiagonal.mp hp)
    have hp := List.append_eq_nil_iff.mp hp
    have : p = (1, 1) := Prod.ext (FreeMonoid.ext hp.1) (FreeMonoid.ext hp.2)
    exact (hne this).elim

theorem constantCoeff_apply (f : WordSeries ι R) : constantCoeff f = coeff 1 f := (rfl)

@[simp] theorem constantCoeff_C (r : R) : constantCoeff (C r : WordSeries ι R) = r := by
  simp [constantCoeff_apply]

@[simp] theorem constantCoeff_X (i : ι) : constantCoeff (X i : WordSeries ι R) = 0 := by
  simp [constantCoeff_apply]

end Semiring

instance [Ring R] : Ring (WordSeries ι R) :=
  { (inferInstance : AddCommGroup (WordSeries ι R)),
    (inferInstance : Semiring (WordSeries ι R)) with }

/-- Coefficientwise scalar multiplication makes word series an algebra over their
commutative coefficient semiring. -/
instance [CommSemiring R] : Algebra R (WordSeries ι R) where
  algebraMap := C
  commutes' r f := by
    ext w
    simp [mul_comm]
  smul_def' r f := by
    ext w
    simp

/-- The algebra map sends a scalar to its constant word series. -/
theorem algebraMap_eq_C [CommSemiring R] : algebraMap R (WordSeries ι R) = C := (rfl)

open Classical in
/-- Scalars have their given coefficient at the empty word and vanish at every other word. -/
@[simp] theorem coeff_algebraMap [CommSemiring R] (w : FreeMonoid ι) (r : R) :
    coeff w (algebraMap R (WordSeries ι R) r) = if w = 1 then r else 0 := by
  rw [algebraMap_eq_C, coeff_C]

end WordSeries
end TauCeti
