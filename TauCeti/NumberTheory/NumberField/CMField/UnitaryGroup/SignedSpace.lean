/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.AdelicFrame
import TauCeti.NumberTheory.NumberField.CMField.IntegralAdeleNorm

/-!
# Hermitian spaces with an adelic frame of every sign vector

Let `E` be a CM field and `s ∈ {±1}^n` a sign vector. The diagonal hermitian form
`diag(s) = ⟨s_1, …, s_n⟩` on `E^n` has signature `s` at every infinite place, but at a finite
place it is isometric to the standard form `⟨1, …, 1⟩` only if `-1` is a norm there. A finite
adele `ν` with `conj ν * ν = -1` supplies such a norm at all finite places at once, and then
`V = (diag(s), x)` with `x_∞ = 1` and `x_f = diag(ν_1, …, ν_n)`, where `ν_i = 1` if `s_i = 1` and
`ν_i = ν` if `s_i = -1`, is a hermitian space with an adelic frame of signs `s`
(`TauCeti.FramedHermitianSpace.signed`): `x_f* diag(s) x_f = 1_n` because `conj ν * (-1) * ν = 1`.

When `E` contains a primitive fourth and a primitive seventh root of unity (for instance a
primitive `5040`-th root of unity), such a `ν` exists, and can be taken to be a unit of the
integral finite adeles `Ô` (`NumberField.IsCMField.exists_star_mul_self_eq_neg_one`). Hence there
is a hermitian space with an adelic frame of every sign vector
(`TauCeti.FramedHermitianSpace.nonempty_of_isPrimitiveRoot`).

## Main definitions

* `TauCeti.FramedHermitianSpace.signed ν hν s`: the space `(diag(s), (1, diag(ν_i)))` of signs
  `s`, for a finite adele `ν` with `conj ν * ν = -1`.

## Main results

* `TauCeti.FramedHermitianSpace.nonempty_of_isPrimitiveRoot`: if `E` contains a primitive fourth
  and a primitive seventh root of unity, there is a hermitian space with an adelic frame of every
  sign vector.

## References

* `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/Adelic/Unitary/ComponentsAndBlockSums.lean` (declarations `New.Weil.normNegOne`,
  `New.signedSpace`); Apache 2.0, Copyright 2026 Anthropic, PBC. The construction (an integral
  finite idele `ν` with `conj ν * ν = -1` turning `diag(s)` into `1_n` at every finite place)
  follows those declarations; the formalization here is independent of that code.
-/

public section
noncomputable section

open IsDedekindDomain Matrix NumberField NumberField.IsCMField
open scoped NumberField.AdeleRing

namespace TauCeti.FramedHermitianSpace

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {ι : Type*}

/-- The diagonal entries `ν_i` of the finite frame of `signed ν hν s`: `1` where `s_i = 1` and `ν`
where `s_i = -1`. -/
private def signedEntry (ν : 𝔸ᶠ[E]) (s : ι → ℤˣ) (i : ι) : 𝔸ᶠ[E] :=
  if s i = 1 then 1 else ν

/-- `conj ν_i * s_i * ν_i = 1`, for `conj ν * ν = -1`. -/
private theorem star_signedEntry_mul_mul_signedEntry {ν : 𝔸ᶠ[E]} (hν : star ν * ν = -1)
    (s : ι → ℤˣ) (i : ι) :
    star (signedEntry ν s i) * ((s i : ℤ) : 𝔸ᶠ[E]) * signedEntry ν s i = 1 := by
  rcases Int.units_eq_one_or (s i) with h | h
  · simp [signedEntry, h]
  · rw [signedEntry, h, ite_eq_right (by decide : ¬(-1 : ℤˣ) = 1), Units.val_neg,
      Units.val_one, Int.cast_neg, Int.cast_one]
    linear_combination -hν

/-- The entries `ν_i` are units: `ν_i * (conj ν_i * s_i) = 1`. -/
private theorem signedEntry_mul_star_signedEntry_mul {ν : 𝔸ᶠ[E]} (hν : star ν * ν = -1)
    (s : ι → ℤˣ) (i : ι) :
    signedEntry ν s i * (star (signedEntry ν s i) * ((s i : ℤ) : 𝔸ᶠ[E])) = 1 := by
  rw [mul_comm, star_signedEntry_mul_mul_signedEntry hν]

variable [Fintype ι] [DecidableEq ι]

/-- The finite frame `diag(ν_1, …, ν_n)` of `signed ν hν s`, invertible with inverse
`diag(conj ν_i * s_i)`. -/
private def signedFrame {ν : 𝔸ᶠ[E]} (hν : star ν * ν = -1) (s : ι → ℤˣ) : GL ι 𝔸ᶠ[E] where
  val := diagonal (signedEntry ν s)
  inv := diagonal fun i ↦ star (signedEntry ν s i) * ((s i : ℤ) : 𝔸ᶠ[E])
  val_inv := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg diagonal (funext (signedEntry_mul_star_signedEntry_mul hν s))
  inv_val := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg diagonal (funext fun i ↦ by
      rw [mul_comm, signedEntry_mul_star_signedEntry_mul hν s])

variable (E) in
/-- The **space of signs `s`** attached to a finite adele `ν` with `conj ν * ν = -1`: the diagonal
Gram matrix `diag(s)` with the adelic frame `x = (1, diag(ν_1, …, ν_n))`, where `ν_i = 1` if
`s_i = 1` and `ν_i = ν` if `s_i = -1`. At the finite places `x_f* diag(s) x_f = 1_n`, since
`conj ν * (-1) * ν = 1`. -/
def signed (ν : 𝔸ᶠ[E]) (hν : star ν * ν = -1) (s : ι → ℤˣ) : FramedHermitianSpace E s where
  gram := diagonal fun i ↦ ((s i : ℤ) : E)
  frame := (1, signedFrame hν s)
  star_mul_gram_mul_fst := by
    rw [Prod.fst, Units.val_one, star_one, one_mul, mul_one, diagonal_map (map_zero _)]
    simp_rw [map_intCast]
  star_mul_gram_mul_snd := by
    rw [diagonal_map (map_zero _)]
    simp_rw [map_intCast]
    rw [← diagonal_one, signedFrame, star_eq_conjTranspose, diagonal_conjTranspose,
      diagonal_mul_diagonal, diagonal_mul_diagonal]
    exact congrArg diagonal (funext fun i ↦ star_signedEntry_mul_mul_signedEntry hν s i)

/-- The Gram matrix of `signed E ν hν s` is `diag(s)`. -/
@[simp]
theorem gram_signed (ν : 𝔸ᶠ[E]) (hν : star ν * ν = -1) (s : ι → ℤˣ) :
    (signed E ν hν s).gram = diagonal fun i ↦ ((s i : ℤ) : E) :=
  (rfl)

/-- The archimedean frame of `signed E ν hν s` is `1`. -/
@[simp]
theorem frame_fst_signed (ν : 𝔸ᶠ[E]) (hν : star ν * ν = -1) (s : ι → ℤˣ) :
    (signed E ν hν s).frame.1 = 1 :=
  (rfl)

/-- The finite frame of `signed E ν hν s` is `diag(ν_1, …, ν_n)`, with `ν_i = 1` if `s_i = 1` and
`ν_i = ν` if `s_i = -1`. -/
@[simp]
theorem val_frame_snd_signed (ν : 𝔸ᶠ[E]) (hν : star ν * ν = -1) (s : ι → ℤˣ) :
    ((signed E ν hν s).frame.2 : Matrix ι ι 𝔸ᶠ[E]) =
      diagonal fun i ↦ if s i = 1 then 1 else ν :=
  (rfl)

/-- **There is a hermitian space with an adelic frame of every sign vector** over a CM field
containing a primitive fourth and a primitive seventh root of unity, for instance a primitive
`5040`-th root of unity. -/
theorem nonempty_of_isPrimitiveRoot {ζ₄ ζ₇ : E} (h₄ : IsPrimitiveRoot ζ₄ 4)
    (h₇ : IsPrimitiveRoot ζ₇ 7) (s : ι → ℤˣ) : Nonempty (FramedHermitianSpace E s) :=
  have ⟨ν, hν⟩ := exists_star_mul_self_eq_neg_one h₄ h₇
  ⟨signed E ((ν : FiniteAdeleRing.integralAdeles (𝓞 E) E) : 𝔸ᶠ[E])
    (by rw [← coe_star_integralAdeles, ← Units.coe_star, ← Subalgebra.coe_mul, ← Units.val_mul,
      hν, Units.val_neg, Units.val_one, Subalgebra.coe_neg, OneMemClass.coe_one]) s⟩

end TauCeti.FramedHermitianSpace
