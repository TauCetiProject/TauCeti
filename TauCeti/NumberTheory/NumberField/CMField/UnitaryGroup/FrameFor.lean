/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Congruence
public import TauCeti.NumberTheory.NumberField.CMField.AdeleStar.Matrix

/-!
# Frames for a matrix over a CM field, up to a scalar in `Ô_ℚ^×`

Let `E` be a CM field, `𝔸_f` its finite adeles, `Ô_ℚ` the integral finite adeles of `ℚ` and `n`
a finite type. Complex conjugation makes `𝔸_f` a star ring
(`NumberField.IsCMField.instStarRingFiniteAdeleRing`), and `x* = star x` is the conjugate
transpose of a matrix `x` over `𝔸_f`. The units `Ô_ℚ^×` map to `𝔸_f^×` along `ℚ ⊆ E`
(`NumberField.zhatUnitsMap`).

`x ∈ GL_n(𝔸_f)` is a *frame* for `β ∈ M_n(E)` if `x* β x = ε·1` for some `ε ∈ Ô_ℚ^×`. If
`c·g*g = ε'·1` with `c ∈ ℚ` and `ε' ∈ Ô_ℚ^×`, then `x g` is a frame for `c β`: this is the
composition of twisted similitudes (`Matrix.smul_transpose_map_mul_mul_mul_eq`) from the form of
`β` to the form `1` and then to `1`.

The relation with the hermitian spaces with an adelic frame of `TauCeti.FramedHermitianSpace` is
in `TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.FrameFor.FramedHermitianSpace`.

## Main definitions

* `TauCeti.IsFrameFor`: frames for a matrix over `E`.

## Main results

* `TauCeti.IsFrameFor.mul_of_smul_star_mul_self_eq`: if `x` is a frame for `β` and
  `c·g*g = ε'·1`, then `x g` is a frame for `c β`; `TauCeti.IsFrameFor.mul` is the case `c = 1`.

## References

* the folder `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207 (`New.Variety.IsFrameFor`).
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing Matrix NumberField NumberField.IsCMField
open scoped NumberField.AdeleRing

namespace TauCeti

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {n : Type*} [Fintype n]
  [DecidableEq n]

variable (E) in
/-- `x ∈ GL_n(𝔸_f)` is a **frame** for `β ∈ M_n(E)` if `x* β x = ε·1` for some `ε ∈ Ô_ℚ^×`. -/
def IsFrameFor (β : Matrix n n E) (x : GL n 𝔸ᶠ[E]) : Prop :=
  ∃ ε : (integralAdeles ℤ ℚ)ˣ, star (x : Matrix n n 𝔸ᶠ[E]) * β.map (algebraMap E 𝔸ᶠ[E]) * x =
    (zhatUnitsMap E ε : 𝔸ᶠ[E]) • 1

theorem isFrameFor_iff {β : Matrix n n E} {x : GL n 𝔸ᶠ[E]} :
    IsFrameFor E β x ↔ ∃ ε : (integralAdeles ℤ ℚ)ˣ, star (x : Matrix n n 𝔸ᶠ[E]) *
      β.map (algebraMap E 𝔸ᶠ[E]) * x = (zhatUnitsMap E ε : 𝔸ᶠ[E]) • 1 :=
  Iff.rfl

/-- The identity is a frame for the identity matrix. -/
theorem isFrameFor_one : IsFrameFor E (1 : Matrix n n E) 1 :=
  ⟨1, by simp⟩

/-- **Frames under similitudes**: if `x` is a frame for `β` and `c·g*g = ε'·1` with `c ∈ ℚ` and
`ε' ∈ Ô_ℚ^×`, then `x g` is a frame for `c β`. -/
theorem IsFrameFor.mul_of_smul_star_mul_self_eq {β : Matrix n n E} {x g : GL n 𝔸ᶠ[E]} {c : ℚ}
    {ε' : (integralAdeles ℤ ℚ)ˣ} (hx : IsFrameFor E β x)
    (hg : algebraMap E 𝔸ᶠ[E] c • (star (g : Matrix n n 𝔸ᶠ[E]) * g) =
      (zhatUnitsMap E ε' : 𝔸ᶠ[E]) • 1) :
    IsFrameFor E ((c : E) • β) (x * g) := by
  obtain ⟨ε, hε⟩ := hx
  refine ⟨ε * ε', ?_⟩
  rw [star_eq_transpose_map_finiteAdeleConj, ← one_smul 𝔸ᶠ[E] (_ * _)] at hε
  rw [star_eq_transpose_map_finiteAdeleConj, ← Matrix.mul_one (Matrix.transpose _)] at hg
  have h := smul_transpose_map_mul_mul_mul_eq _ hε hg
  rw [one_mul] at h
  calc star (↑(x * g) : Matrix n n 𝔸ᶠ[E]) * ((c : E) • β).map (algebraMap E 𝔸ᶠ[E]) * ↑(x * g)
      = algebraMap E 𝔸ᶠ[E] c • ((((x : Matrix n n 𝔸ᶠ[E]) * g).map
          (finiteAdeleConj E : 𝔸ᶠ[E] →+* 𝔸ᶠ[E]))ᵀ * β.map (algebraMap E 𝔸ᶠ[E]) *
            ((x : Matrix n n 𝔸ᶠ[E]) * g)) := by
        rw [GeneralLinearGroup.coe_mul, star_eq_transpose_map_finiteAdeleConj,
          Matrix.map_smul' _ _ _ (map_mul _), Matrix.mul_smul, Matrix.smul_mul]
    _ = _ := by rw [h, map_mul, Units.val_mul]

/-- **Frames are stable under unitary similitudes with factor in `Ô_ℚ^×`**: if `x` is a frame for
`β` and `g* g = ε'·1` with `ε' ∈ Ô_ℚ^×`, then `x g` is a frame for `β`. -/
theorem IsFrameFor.mul {β : Matrix n n E} {x g : GL n 𝔸ᶠ[E]} {ε' : (integralAdeles ℤ ℚ)ˣ}
    (hx : IsFrameFor E β x)
    (hg : star (g : Matrix n n 𝔸ᶠ[E]) * g = (zhatUnitsMap E ε' : 𝔸ᶠ[E]) • 1) :
    IsFrameFor E β (x * g) := by
  simpa using hx.mul_of_smul_star_mul_self_eq (c := 1) (by simpa using hg)

end TauCeti
