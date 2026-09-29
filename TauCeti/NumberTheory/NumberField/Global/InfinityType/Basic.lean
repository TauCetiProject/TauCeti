/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Infinity types of a number field

This file defines three carriers for the archimedean parameters of characters of a number field.
They deliberately record different kinds of data:

* `ContinuousInfinityType K` has a complex modulus exponent and a parity at every real place, and
  a complex modulus exponent and an integral angular frequency at every complex place.  These are
  the parameters in the classification of continuous characters of `ℝˣ` and `ℂˣ`.
* `AlgebraicInfinityType K` assigns an integer exponent to every embedding `K → ℂ`.
* `FiniteOrderInfinityType K` assigns only a parity to every real place.  There is no datum at a
  complex place because a finite-order continuous character of `ℂˣ` is trivial.

The map `AlgebraicInfinityType.toContinuous` performs the conjugation bookkeeping at a complex
place: exponents `a` and `b` at the chosen embedding and its conjugate give modulus exponent
`a + b` and angular frequency `a - b`.  This map is injective.  Finite-order infinity types also
embed in continuous infinity types, with all modulus exponents and complex angular frequencies
zero.

## References

* A. Weil, *Basic Number Theory*, Chapter VII.
* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, in J. W. S. Cassels and
  A. Fröhlich, eds., *Algebraic Number Theory*, §2.3.
-/

public section
noncomputable section

open NumberField

namespace TauCeti.GlobalNumberFields

/-- The archimedean parameters of a continuous character over `K`: a complex modulus exponent and
a parity at every real place, and a complex modulus exponent and integral angular frequency at
every complex place. -/
@[ext]
structure ContinuousInfinityType (K : Type*) [Field K] where
  /-- The exponent of the absolute value at each real place. -/
  realExponent : {w : InfinitePlace K // w.IsReal} → ℂ
  /-- The exponent of the sign character at each real place. -/
  realParity : {w : InfinitePlace K // w.IsReal} → ZMod 2
  /-- The exponent of the absolute value at each complex place. -/
  complexExponent : {w : InfinitePlace K // w.IsComplex} → ℂ
  /-- The exponent of the angular character at each complex place. -/
  complexAngularFrequency : {w : InfinitePlace K // w.IsComplex} → ℤ

namespace ContinuousInfinityType

variable {K : Type*} [Field K]

instance : Zero (ContinuousInfinityType K) :=
  ⟨⟨0, 0, 0, 0⟩⟩

instance : Add (ContinuousInfinityType K) :=
  ⟨fun t u ↦ ⟨t.realExponent + u.realExponent, t.realParity + u.realParity,
    t.complexExponent + u.complexExponent,
    t.complexAngularFrequency + u.complexAngularFrequency⟩⟩

instance : Neg (ContinuousInfinityType K) :=
  ⟨fun t ↦ ⟨-t.realExponent, -t.realParity, -t.complexExponent,
    -t.complexAngularFrequency⟩⟩

instance : Sub (ContinuousInfinityType K) :=
  ⟨fun t u ↦ ⟨t.realExponent - u.realExponent, t.realParity - u.realParity,
    t.complexExponent - u.complexExponent,
    t.complexAngularFrequency - u.complexAngularFrequency⟩⟩

instance : SMul ℕ (ContinuousInfinityType K) :=
  ⟨fun n t ↦ ⟨n • t.realExponent, n • t.realParity, n • t.complexExponent,
    n • t.complexAngularFrequency⟩⟩

instance : SMul ℤ (ContinuousInfinityType K) :=
  ⟨fun n t ↦ ⟨n • t.realExponent, n • t.realParity, n • t.complexExponent,
    n • t.complexAngularFrequency⟩⟩

/-- The zero continuous infinity type has zero real modulus exponents. -/
@[simp]
theorem zero_realExponent : (0 : ContinuousInfinityType K).realExponent = 0 :=
  rfl

/-- The zero continuous infinity type has zero real parities. -/
@[simp]
theorem zero_realParity : (0 : ContinuousInfinityType K).realParity = 0 :=
  rfl

/-- The zero continuous infinity type has zero complex modulus exponents. -/
@[simp]
theorem zero_complexExponent : (0 : ContinuousInfinityType K).complexExponent = 0 :=
  rfl

/-- The zero continuous infinity type has zero complex angular frequencies. -/
@[simp]
theorem zero_complexAngularFrequency : (0 : ContinuousInfinityType K).complexAngularFrequency = 0 :=
  rfl

/-- Real modulus exponents add pointwise. -/
@[simp]
theorem add_realExponent (t u : ContinuousInfinityType K) :
    (t + u).realExponent = t.realExponent + u.realExponent :=
  rfl

/-- Real parities add pointwise. -/
@[simp]
theorem add_realParity (t u : ContinuousInfinityType K) :
    (t + u).realParity = t.realParity + u.realParity :=
  rfl

/-- Complex modulus exponents add pointwise. -/
@[simp]
theorem add_complexExponent (t u : ContinuousInfinityType K) :
    (t + u).complexExponent = t.complexExponent + u.complexExponent :=
  rfl

/-- Complex angular frequencies add pointwise. -/
@[simp]
theorem add_complexAngularFrequency (t u : ContinuousInfinityType K) :
    (t + u).complexAngularFrequency = t.complexAngularFrequency + u.complexAngularFrequency :=
  rfl

/-- Negation negates real modulus exponents pointwise. -/
@[simp]
theorem neg_realExponent (t : ContinuousInfinityType K) :
    (-t).realExponent = -t.realExponent :=
  rfl

/-- Negation negates real parities pointwise. -/
@[simp]
theorem neg_realParity (t : ContinuousInfinityType K) :
    (-t).realParity = -t.realParity :=
  rfl

/-- Negation negates complex modulus exponents pointwise. -/
@[simp]
theorem neg_complexExponent (t : ContinuousInfinityType K) :
    (-t).complexExponent = -t.complexExponent :=
  rfl

/-- Negation negates complex angular frequencies pointwise. -/
@[simp]
theorem neg_complexAngularFrequency (t : ContinuousInfinityType K) :
    (-t).complexAngularFrequency = -t.complexAngularFrequency :=
  rfl

/-- Real modulus exponents subtract pointwise. -/
@[simp]
theorem sub_realExponent (t u : ContinuousInfinityType K) :
    (t - u).realExponent = t.realExponent - u.realExponent :=
  rfl

/-- Real parities subtract pointwise. -/
@[simp]
theorem sub_realParity (t u : ContinuousInfinityType K) :
    (t - u).realParity = t.realParity - u.realParity :=
  rfl

/-- Complex modulus exponents subtract pointwise. -/
@[simp]
theorem sub_complexExponent (t u : ContinuousInfinityType K) :
    (t - u).complexExponent = t.complexExponent - u.complexExponent :=
  rfl

/-- Complex angular frequencies subtract pointwise. -/
@[simp]
theorem sub_complexAngularFrequency (t u : ContinuousInfinityType K) :
    (t - u).complexAngularFrequency = t.complexAngularFrequency - u.complexAngularFrequency :=
  rfl

/-- Natural-number multiples scale real modulus exponents pointwise. -/
@[simp]
theorem nsmul_realExponent (n : ℕ) (t : ContinuousInfinityType K) :
    (n • t).realExponent = n • t.realExponent :=
  rfl

/-- Natural-number multiples scale real parities pointwise. -/
@[simp]
theorem nsmul_realParity (n : ℕ) (t : ContinuousInfinityType K) :
    (n • t).realParity = n • t.realParity :=
  rfl

/-- Natural-number multiples scale complex modulus exponents pointwise. -/
@[simp]
theorem nsmul_complexExponent (n : ℕ) (t : ContinuousInfinityType K) :
    (n • t).complexExponent = n • t.complexExponent :=
  rfl

/-- Natural-number multiples scale complex angular frequencies pointwise. -/
@[simp]
theorem nsmul_complexAngularFrequency (n : ℕ) (t : ContinuousInfinityType K) :
    (n • t).complexAngularFrequency = n • t.complexAngularFrequency :=
  rfl

/-- Integer multiples scale real modulus exponents pointwise. -/
@[simp]
theorem zsmul_realExponent (n : ℤ) (t : ContinuousInfinityType K) :
    (n • t).realExponent = n • t.realExponent :=
  rfl

/-- Integer multiples scale real parities pointwise. -/
@[simp]
theorem zsmul_realParity (n : ℤ) (t : ContinuousInfinityType K) :
    (n • t).realParity = n • t.realParity :=
  rfl

/-- Integer multiples scale complex modulus exponents pointwise. -/
@[simp]
theorem zsmul_complexExponent (n : ℤ) (t : ContinuousInfinityType K) :
    (n • t).complexExponent = n • t.complexExponent :=
  rfl

/-- Integer multiples scale complex angular frequencies pointwise. -/
@[simp]
theorem zsmul_complexAngularFrequency (n : ℤ) (t : ContinuousInfinityType K) :
    (n • t).complexAngularFrequency = n • t.complexAngularFrequency :=
  rfl

instance : AddCommGroup (ContinuousInfinityType K) :=
  Function.Injective.addCommGroup
    (fun t ↦ ((t.realExponent, t.realParity), (t.complexExponent, t.complexAngularFrequency)))
    (fun t u h ↦ by
      simp only [Prod.mk.injEq] at h
      exact ContinuousInfinityType.ext h.1.1 h.1.2 h.2.1 h.2.2)
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- A continuous infinity type is equivalently its four families of local parameters, as
additive groups. -/
@[expose, simps]
def equivProd : ContinuousInfinityType K ≃+
    (({w : InfinitePlace K // w.IsReal} → ℂ) ×
      ({w : InfinitePlace K // w.IsReal} → ZMod 2)) ×
    (({w : InfinitePlace K // w.IsComplex} → ℂ) ×
      ({w : InfinitePlace K // w.IsComplex} → ℤ)) where
  toFun t := ((t.realExponent, t.realParity),
    (t.complexExponent, t.complexAngularFrequency))
  invFun t := ⟨t.1.1, t.1.2, t.2.1, t.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

end ContinuousInfinityType

/-- An algebraic infinity type over `K`: an integer exponent at every complex embedding of `K`.

The two embeddings belonging to one complex place are retained separately.  Their sum and
difference become the modulus exponent and angular frequency of the associated continuous
infinity type. -/
abbrev AlgebraicInfinityType (K : Type*) [Field K] := (K →+* ℂ) → ℤ

/-- A finite-order infinity type over `K`: a sign parity at every real place.

There is no complex-place field: every finite-order continuous character of `ℂˣ` is trivial. -/
abbrev FiniteOrderInfinityType (K : Type*) [Field K] :=
  {w : InfinitePlace K // w.IsReal} → ZMod 2

namespace AlgebraicInfinityType

variable {K : Type*} [Field K]

/-- The continuous infinity type associated to an algebraic infinity type.  At a real place the
integer exponent gives both the modulus exponent and its parity.  At a complex place, exponents
`a` and `b` at the chosen embedding and its conjugate give modulus exponent `a + b` and angular
frequency `a - b`. -/
def toContinuous : AlgebraicInfinityType K →+ ContinuousInfinityType K where
  toFun n :=
    { realExponent := fun w ↦ n w.1.embedding
      realParity := fun w ↦ n w.1.embedding
      complexExponent := fun w ↦
        n w.1.embedding + n (ComplexEmbedding.conjugate w.1.embedding)
      complexAngularFrequency := fun w ↦
        n w.1.embedding - n (ComplexEmbedding.conjugate w.1.embedding) }
  map_zero' := by
    apply ContinuousInfinityType.ext <;> funext w <;> simp
  map_add' n m := by
    ext w
    · simp only [Pi.add_apply, Int.cast_add, ContinuousInfinityType.add_realExponent]
    · simp only [Pi.add_apply, Int.cast_add, ContinuousInfinityType.add_realParity]
    · simp only [Pi.add_apply, Int.cast_add, ContinuousInfinityType.add_complexExponent]
      ring
    · simp only [Pi.add_apply, ContinuousInfinityType.add_complexAngularFrequency]
      ring

/-- The real modulus exponent of an algebraic infinity type is its exponent at the real
embedding. -/
@[simp]
theorem toContinuous_realExponent (n : AlgebraicInfinityType K)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (toContinuous n).realExponent w = n w.1.embedding :=
  (rfl)

/-- The real parity of an algebraic infinity type is its embedding exponent modulo two. -/
@[simp]
theorem toContinuous_realParity (n : AlgebraicInfinityType K)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (toContinuous n).realParity w = n w.1.embedding :=
  (rfl)

/-- The complex modulus exponent of an algebraic infinity type is the sum of its two conjugate
embedding exponents. -/
@[simp]
theorem toContinuous_complexExponent (n : AlgebraicInfinityType K)
    (w : {w : InfinitePlace K // w.IsComplex}) :
    (toContinuous n).complexExponent w =
      n w.1.embedding + n (ComplexEmbedding.conjugate w.1.embedding) :=
  (rfl)

/-- The complex angular frequency of an algebraic infinity type is the difference of its two
conjugate embedding exponents. -/
@[simp]
theorem toContinuous_complexAngularFrequency (n : AlgebraicInfinityType K)
    (w : {w : InfinitePlace K // w.IsComplex}) :
    (toContinuous n).complexAngularFrequency w =
      n w.1.embedding - n (ComplexEmbedding.conjugate w.1.embedding) :=
  (rfl)

/-- Algebraic infinity types are determined by their associated continuous infinity types. -/
theorem toContinuous_injective : Function.Injective (toContinuous (K := K)) := by
  intro n m h
  funext φ
  by_cases hφ : ComplexEmbedding.IsReal φ
  · let w : {w : InfinitePlace K // w.IsReal} :=
      ⟨InfinitePlace.mk φ, InfinitePlace.isReal_mk_iff.mpr hφ⟩
    have hw := congrArg (fun t : ContinuousInfinityType K ↦ t.realExponent w) h
    simp only [toContinuous_realExponent] at hw
    rw [InfinitePlace.embedding_mk_eq_of_isReal hφ] at hw
    exact_mod_cast hw
  · let w : {w : InfinitePlace K // w.IsComplex} :=
      ⟨InfinitePlace.mk φ, InfinitePlace.isComplex_mk_iff.mpr hφ⟩
    have hsum := congrArg (fun t : ContinuousInfinityType K ↦ t.complexExponent w) h
    have hdiff := congrArg
      (fun t : ContinuousInfinityType K ↦ t.complexAngularFrequency w) h
    simp only [toContinuous_complexExponent] at hsum
    simp only [toContinuous_complexAngularFrequency] at hdiff
    have hsum' :
        n w.1.embedding + n (ComplexEmbedding.conjugate w.1.embedding) =
          m w.1.embedding + m (ComplexEmbedding.conjugate w.1.embedding) := by
      exact_mod_cast hsum
    have hemb : n w.1.embedding = m w.1.embedding := by omega
    have hconj : n (ComplexEmbedding.conjugate w.1.embedding) =
        m (ComplexEmbedding.conjugate w.1.embedding) := by omega
    dsimp [w] at hemb hconj
    rcases InfinitePlace.embedding_mk_eq φ with hφ | hφ
    · simpa only [hφ] using hemb
    · simpa only [hφ, star_star] using hconj

end AlgebraicInfinityType

namespace FiniteOrderInfinityType

variable {K : Type*} [Field K]

/-- A finite-order infinity type as a continuous infinity type: its real signs are retained, and
all modulus exponents and complex angular frequencies are zero. -/
def toContinuous : FiniteOrderInfinityType K →+ ContinuousInfinityType K where
  toFun ε :=
    { realExponent := 0
      realParity := ε
      complexExponent := 0
      complexAngularFrequency := 0 }
  map_zero' := by
    apply ContinuousInfinityType.ext <;> funext w <;> simp
  map_add' _ _ := by
    apply ContinuousInfinityType.ext <;> funext w <;> simp

/-- The continuous real exponent of a finite-order infinity type is zero. -/
@[simp]
theorem toContinuous_realExponent (ε : FiniteOrderInfinityType K)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (toContinuous ε).realExponent w = 0 :=
  by simp [toContinuous]

/-- Passing a finite-order infinity type to continuous parameters preserves its real parity. -/
@[simp]
theorem toContinuous_realParity (ε : FiniteOrderInfinityType K)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (toContinuous ε).realParity w = ε w :=
  by simp [toContinuous]

/-- The continuous complex exponent of a finite-order infinity type is zero. -/
@[simp]
theorem toContinuous_complexExponent (ε : FiniteOrderInfinityType K)
    (w : {w : InfinitePlace K // w.IsComplex}) :
    (toContinuous ε).complexExponent w = 0 :=
  by simp [toContinuous]

/-- The continuous complex angular frequency of a finite-order infinity type is zero. -/
@[simp]
theorem toContinuous_complexAngularFrequency (ε : FiniteOrderInfinityType K)
    (w : {w : InfinitePlace K // w.IsComplex}) :
    (toContinuous ε).complexAngularFrequency w = 0 :=
  by simp [toContinuous]

/-- Finite-order infinity types are determined by their continuous parameters. -/
theorem toContinuous_injective : Function.Injective (toContinuous (K := K)) := by
  intro ε η h
  funext w
  simpa using congrArg (fun t : ContinuousInfinityType K ↦ t.realParity w) h

end FiniteOrderInfinityType

end TauCeti.GlobalNumberFields
