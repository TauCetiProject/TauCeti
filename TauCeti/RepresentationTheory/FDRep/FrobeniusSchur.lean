/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Limits
public import TauCeti.CategoryTheory.Monoidal.Pivotal.FrobeniusSchur.Simple
public import TauCeti.RepresentationTheory.Character.Basic
public import TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.Basic
public import TauCeti.RepresentationTheory.FDRep.Invariants
public import TauCeti.RepresentationTheory.FDRep.Pivotal
public import TauCeti.RepresentationTheory.Simple.Basic

/-!
# Frobenius–Schur indicators in `FDRep k G`

We compute the Ng–Schauenburg Frobenius–Schur indicators of a finite-dimensional representation
`V : FDRep k G` equipped with the standard spherical structure (`FDRep.Pivotal`) when `G` is finite
and `|G|` is invertible in `k`: for every `n : ℕ+`,

`TauCeti.frobeniusSchurIndicator k V n = (Nat.card G : k)⁻¹ * ∑ g : G, V.character (g ^ (n : ℕ))`
(`FDRep.frobeniusSchurIndicator_fdRep`).

Specializing to `n = 2` shows that the categorical second Frobenius–Schur indicator agrees with the
representation-theoretic indicator `FDRep.frobeniusSchurIndicator V = |G|⁻¹ ∑ g, χ_V(g²)`
(`FDRep.frobeniusSchurIndicator_fdRep_two`). Combining this identification with the categorical
trichotomy in `TauCeti.CategoryTheory.Monoidal.Pivotal.FrobeniusSchur.Simple` yields the
self-duality criterion `FDRep.frobeniusSchurIndicator V ≠ 0 ↔ Nonempty (V ≅ Vᘁ)` and the
`{1, 0, -1}` trichotomy for any simple `V : FDRep k G` over an algebraically closed field in which
`|G|` is invertible (including characteristic `2` when `|G|` is odd).

Note that invertibility of `|G|` in `k` is genuinely required to equate the categorical indicator
with the character average: for `G = C₂` and `k = 𝔽₂`, the trivial `1`-dimensional representation
has `dim_k Hom(𝟙_, V ⊗ V) = 1` and identity rotation, so its categorical indicator is `1`, whereas
`(Nat.card G : k)⁻¹` vanishes in `𝔽₂`.

## Main results

* `FDRep.frobeniusSchurIndicator_fdRep`: `ν_n(V) = (Nat.card G : k)⁻¹ * ∑ g : G,
  V.character (g ^ (n : ℕ))` for `[Invertible (Nat.card G : k)]` (and
  `FDRep.frobeniusSchurIndicator_fdRep_of_charZero` without an explicit invertibility hypothesis in
  characteristic zero).
* `FDRep.frobeniusSchurIndicator_fdRep_eq_zero_iff_of_coprime`: for a simple `V` and `n` coprime
  to `|G|`, the categorical `n`-th indicator is `0` exactly when the character of `V` is
  nontrivial.
* `FDRep.frobeniusSchurIndicator_fdRep_two`, `Representation.frobeniusSchurIndicator_fdRepOf_two`,
  and `Representation.frobeniusSchurIndicator_fdRep_ofShrink_two`: agreement of the categorical
  `n = 2` indicator with `FDRep.frobeniusSchurIndicator` and
  `TauCeti.Representation.frobeniusSchurIndicator`.
* `FDRep.frobeniusSchurIndicator_eq_one_or_eq_zero_or_eq_neg_one`,
  `FDRep.frobeniusSchurIndicator_ne_zero_iff`, and `FDRep.frobeniusSchurIndicator_eq_zero_iff`:
  categorical trichotomy and self-duality criterion for simple representations whenever `|G|` is
  invertible in an algebraically closed field `k`.

## References

* S.-H. Ng, P. Schauenburg, *Higher Frobenius–Schur indicators for pivotal categories*, in
  *Hopf algebras and generalizations*, Contemp. Math. **441** (2007), 63–90, §§4–5
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §4.7
-/

public section

open CategoryTheory MonoidalCategory TauCeti

universe u v w

namespace FDRep

section Indicator

variable {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G]

/-- In `FDRep k G` with its standard spherical structure, the `n`-th Frobenius–Schur indicator of
`V` equals `(Nat.card G : k)⁻¹ * ∑ g : G, V.character (g ^ (n : ℕ))` whenever `|G|` is invertible
in `k`. -/
theorem frobeniusSchurIndicator_fdRep [Invertible (Nat.card G : k)] (V : FDRep k G) (n : ℕ+) :
    TauCeti.frobeniusSchurIndicator k V n =
      (Nat.card G : k)⁻¹ * ∑ g : G, V.character (g ^ (n : ℕ)) := by
  rw [frobeniusSchurIndicator_eq_trace_rightComp, FDRep.trace_rightComp_tensorUnit]
  refine congrArg ((Nat.card G : k)⁻¹ * ·) (Finset.sum_congr rfl fun g _ ↦ ?_)
  have htr := congrArg (fun ψ : 𝟙_ (FGModuleCat k) ⟶ 𝟙_ (FGModuleCat k) ↦ ψ.hom.hom 1)
    (Action.trace_ρ_comp_tensorPowShiftIso_hom V g n.natPred)
  simp only [FGModuleCat.trace_hom_hom_one, FGModuleCat.hom_hom_comp, FDRep.hom_hom_action_ρ,
    PNat.natPred_add_one] at htr
  exact htr

/-- In characteristic zero, `|G|` is automatically invertible in `k`, so the `n`-th categorical
Frobenius–Schur indicator of `V : FDRep k G` is `|G|⁻¹ ∑ g : G, V.character (g ^ (n : ℕ))`. -/
theorem frobeniusSchurIndicator_fdRep_of_charZero [CharZero k] (V : FDRep k G) (n : ℕ+) :
    TauCeti.frobeniusSchurIndicator k V n =
      (Nat.card G : k)⁻¹ * ∑ g : G, V.character (g ^ (n : ℕ)) := by
  have : Invertible (Nat.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact frobeniusSchurIndicator_fdRep V n

end Indicator

section Coprime

variable {k : Type u} {G : Type v} [Field k] [Group G] [Invertible (Nat.card G : k)]

/-- **The categorical `n`-th Frobenius-Schur indicator of a simple object of `FDRep k G`, for `n`
coprime to `|G|`, is `0` exactly when its character is nontrivial.** For a group of odd order this
applies to the second indicator (`n = 2`, via `Odd.coprime_two_right`); for instance, each of the
two nontrivial one-dimensional representations of `C₃` has categorical second indicator `0`. -/
theorem frobeniusSchurIndicator_fdRep_eq_zero_iff_of_coprime (V : FDRep k G)
    [CategoryTheory.Simple V] {n : ℕ+} (hn : (Nat.card G).Coprime n) :
    TauCeti.frobeniusSchurIndicator k V n = 0 ↔ V.character ≠ fun _ => 1 := by
  have : Finite G := Nat.finite_of_card_ne_zero fun h =>
    Invertible.ne_zero (Nat.card G : k) (by rw [h, Nat.cast_zero])
  let _ : Fintype G := Fintype.ofFinite G
  have := isIrreducible_of_simple V
  rw [frobeniusSchurIndicator_fdRep V n]
  simpa only [character_ρ, funext (character_ρ V)] using
    Representation.card_inv_mul_sum_char_pow_eq_zero_iff_of_coprime V.ρ hn

end Coprime

section Two

variable {k : Type} {G : Type v} [Field k] [Group G] [Fintype G] [Invertible (Nat.card G : k)]

/-- The categorical second Frobenius–Schur indicator of `V : FDRep k G` agrees with the
character-average indicator `FDRep.frobeniusSchurIndicator V`. -/
theorem frobeniusSchurIndicator_fdRep_two (V : FDRep k G) :
    TauCeti.frobeniusSchurIndicator k V 2 = FDRep.frobeniusSchurIndicator V := by
  rw [frobeniusSchurIndicator_fdRep, FDRep.frobeniusSchurIndicator_def,
    TauCeti.Representation.frobeniusSchurIndicator_def]
  simp [FDRep.character_ρ]

end Two

end FDRep

namespace Representation

variable {k : Type} {G : Type v} [Field k] [Group G] [Fintype G] [Invertible (Nat.card G : k)]

/-- The categorical second Frobenius–Schur indicator of `FDRep.of ρ` agrees with
`TauCeti.Representation.frobeniusSchurIndicator ρ`. -/
theorem frobeniusSchurIndicator_fdRepOf_two {W : Type} [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] (ρ : Representation k G W) :
    TauCeti.frobeniusSchurIndicator k (FDRep.of ρ) 2 =
      TauCeti.Representation.frobeniusSchurIndicator ρ := by
  rw [FDRep.frobeniusSchurIndicator_fdRep_two, FDRep.frobeniusSchurIndicator_def, FDRep.of_ρ']

/-- The categorical second Frobenius–Schur indicator of `FDRep.ofShrink ρ` agrees with
`TauCeti.Representation.frobeniusSchurIndicator ρ` for representations in any universe. -/
theorem frobeniusSchurIndicator_fdRep_ofShrink_two {W : Type w} [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] (ρ : Representation k G W) :
    TauCeti.frobeniusSchurIndicator k (FDRep.ofShrink ρ) 2 =
      TauCeti.Representation.frobeniusSchurIndicator ρ := by
  rw [FDRep.frobeniusSchurIndicator_fdRep_two, FDRep.frobeniusSchurIndicator_def]
  exact TauCeti.Representation.frobeniusSchurIndicator_eq_of_equiv (FDRep.ofShrinkEquiv ρ)

end Representation

namespace FDRep

variable {k : Type} {G : Type v} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
  [Invertible (Nat.card G : k)] (V : FDRep k G) [Simple V]

/-- Over any algebraically closed field in which `|G|` is invertible (characteristic two included
when `|G|` is odd), the Frobenius–Schur indicator of a simple `V : FDRep k G` takes only the values
`1`, `0`, or `-1`. -/
theorem frobeniusSchurIndicator_eq_one_or_eq_zero_or_eq_neg_one :
    FDRep.frobeniusSchurIndicator V = 1 ∨ FDRep.frobeniusSchurIndicator V = 0 ∨
      FDRep.frobeniusSchurIndicator V = -1 := by
  rw [← FDRep.frobeniusSchurIndicator_fdRep_two]
  exact TauCeti.frobeniusSchurIndicator_two_eq_one_or_eq_zero_or_eq_neg_one k V

/-- Over an algebraically closed field in which `|G|` is invertible, the Frobenius–Schur indicator
of a simple representation `V : FDRep k G` is nonzero if and only if `V` is isomorphic to its dual
`Vᘁ`. -/
theorem frobeniusSchurIndicator_ne_zero_iff :
    FDRep.frobeniusSchurIndicator V ≠ 0 ↔ Nonempty (V ≅ Vᘁ) := by
  rw [← FDRep.frobeniusSchurIndicator_fdRep_two]
  exact TauCeti.frobeniusSchurIndicator_two_ne_zero_iff k V

/-- Over an algebraically closed field in which `|G|` is invertible, the Frobenius–Schur indicator
of a simple representation `V : FDRep k G` is zero if and only if `V` is not isomorphic to its dual
`Vᘁ`. -/
theorem frobeniusSchurIndicator_eq_zero_iff :
    FDRep.frobeniusSchurIndicator V = 0 ↔ IsEmpty (V ≅ Vᘁ) := by
  rw [← FDRep.frobeniusSchurIndicator_fdRep_two]
  exact TauCeti.frobeniusSchurIndicator_two_eq_zero_iff k V

end FDRep
