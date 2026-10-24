/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Distinguished
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Field
import TauCeti.RingTheory.KrullDimension.Basic
import TauCeti.RingTheory.KrullDimension.Integral
import TauCeti.RingTheory.KrullDimension.Quotient
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Groebner
import TauCeti.RingTheory.PowerSeries.TateAlgebra
import TauCeti.RingTheory.PowerSeries.Weierstrass.Quotient

/-!
# Krull dimension of Tate algebras

Over a complete nonarchimedean field `K`, the Tate algebra `K⟨X₁, …, Xₙ⟩` has Krull dimension
`n`. Consequently every ring that is integral over an injectively embedded Tate algebra
`K⟨X₁, …, X_d⟩` has Krull dimension `d`. Applied to the finite injective maps given by
Noether normalisation, this identifies the number of variables of a normalisation of an
affinoid algebra with its Krull dimension.

The proof is by induction on the number of variables, writing `K⟨X, Y⟩` as the univariate Tate
algebra `K⟨X⟩⟨Y⟩`.

* *Lower bound.* Setting `Y = 0` is a surjection `K⟨X⟩⟨Y⟩ → K⟨X⟩` killing the non-zero-divisor
  `Y`, so `dim K⟨X⟩ + 1 ≤ dim K⟨X, Y⟩`.
* *Upper bound.* For a nonzero `f`, an automorphism makes `f` distinguished in `Y`, and Weierstrass
  division makes `K⟨X, Y⟩ ⧸ (f)` finite over `K⟨X⟩`, so `dim K⟨X, Y⟩ ⧸ (f) ≤ dim K⟨X⟩`. A chain
  of primes of length `k + 1` gives a chain of length `k` above a nonzero element, so
  `dim K⟨X, Y⟩ ≤ dim K⟨X⟩ + 1`.

The same induction shows that every maximal ideal `M` of `K⟨X₁, …, Xₙ⟩` has height `n`. Choose a
nonzero `f ∈ M` and make it distinguished in `Y`. Then `K⟨X, Y⟩ ⧸ (f)` is finite free over `K⟨X⟩`,
so going down holds for it, as for every flat extension. The image of `M` lies over a maximal
ideal of `K⟨X⟩`, of height `n - 1`, so going down gives it height at least `n - 1`. Quotienting
by the non-zero-divisor `f` lowers heights by one, so `M` has height at least `n`.

The maximal-ideal height proof follows the finite-variable induction and transport under renaming
of `MvPolynomial.height_eq_natCard_of_isMaximal` in
`TauCeti.RingTheory.KrullDimension.FiniteType`. Its Jacobson-ring step is replaced here by
Weierstrass quotients and going down for finite free extensions.

## Main results

* `TauCeti.MvPowerSeries.ringKrullDim_isRestricted_subring`: the Tate algebra in the variables
  `σ`, for finite `σ`, has Krull dimension `Nat.card σ`.
* `TauCeti.MvPowerSeries.ringKrullDim_eq_natCard_of_isIntegral`: a ring that is integral over an
  injectively embedded Tate algebra in the variables `σ` has Krull dimension `Nat.card σ`.
* `Ideal.height_eq_natCard_of_isMaximal_isRestricted_subring`: every maximal ideal of the Tate
  algebra in the variables `σ` has height `Nat.card σ`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§5.2.2 and
  6.1.2.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "Tate " σ:max => IsRestricted.subring (R := K) (fun _ : σ ↦ 1)

/-- Without variables, the Tate algebra is the coefficient field, of Krull dimension zero. -/
private theorem ringKrullDim_isRestricted_subring_pEmpty : ringKrullDim (Tate PEmpty) = 0 := by
  rw [← ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective _
    ⟨(algebraMap K (Tate PEmpty)).injective, algebraMap_isRestrictedSubring_surjective⟩)]
  exact ringKrullDim_eq_zero_of_field K

variable [CompleteSpace K]

/-- Quotients of `K⟨X, Y⟩` by nonzero principal ideals are integral over `K⟨X⟩`, so their Krull
dimension is at most that of `K⟨X⟩`. -/
private theorem ringKrullDim_quotient_span_le_option {σ : Type*} [Finite σ] (f : Tate (Option σ))
    (hf : f ≠ 0) : ringKrullDim (Tate (Option σ) ⧸ Ideal.span {f}) ≤ ringKrullDim (Tate σ) := by
  let R := Tate σ
  let S := PowerSeries.IsRestricted.subring (R := R) 1
  let Φ : Tate (Option σ) ≃+* S := Huber.restrictedOptionEquiv
  obtain ⟨e, s, hd, hu⟩ := exists_algEquiv_isDistinguished_isUnit f hf
  have := hd.finite_quotient zero_lt_one hu
  have : Algebra.IsIntegral R (S ⧸ Ideal.span {Φ (e f)}) := Algebra.IsIntegral.of_finite R _
  let E : Tate (Option σ) ≃+* S := (e : Tate (Option σ) ≃+* Tate (Option σ)).trans Φ
  rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv (Ideal.span {f})
    (Ideal.span {Φ (e f)}) E (by simp [Ideal.map_span, E]))]
  exact ringKrullDim_le_of_isIntegral

/-- **Krull dimension of Tate algebras.** Over a complete nonarchimedean field `K`, the Tate
algebra `K⟨X₁, …, Xₙ⟩` in finitely many variables has Krull dimension `n`. -/
theorem ringKrullDim_isRestricted_subring {σ : Type*} [Finite σ] :
    ringKrullDim (Tate σ) = Nat.card σ := by
  refine Finite.induction_empty_option (P := fun σ ↦ ringKrullDim (Tate σ) = Nat.card σ)
    (fun {α β} e h ↦ ?_) ?_ (fun {σ} _ h ↦ ?_) σ
  · -- Renaming the variables along `e : α ≃ β` is a ring isomorphism of Tate algebras.
    rw [← Nat.card_congr e, ← h]
    exact (ringKrullDim_eq_of_ringEquiv
      (IsRestricted.renameAlgEquiv (R := K) e fun _ ↦ 1).toRingEquiv).symm
  · simpa using ringKrullDim_isRestricted_subring_pEmpty
  · rw [Finite.card_option, Nat.cast_add, Nat.cast_one]
    refine le_antisymm ?_ ?_
    · have hle (f : Tate (Option σ)) (hf : f ≠ 0) :
          ringKrullDim (Tate (Option σ) ⧸ Ideal.span {f}) ≤ ((Nat.card σ : ℕ∞) : WithBot ℕ∞) :=
        (ringKrullDim_quotient_span_le_option f hf).trans_eq (h.trans (WithBot.coe_natCast _).symm)
      exact ringKrullDim_le_add_one_of_forall_ringKrullDim_quotient_le hle
    · rw [← h, ringKrullDim_eq_of_ringEquiv (Huber.restrictedOptionEquiv (σ := σ) (R := K))]
      exact PowerSeries.ringKrullDim_succ_le_ringKrullDim_isRestricted_subring 1

/-- The Tate algebra in finitely many variables has finite Krull dimension. -/
instance finiteRingKrullDim {σ : Type*} [Finite σ] : FiniteRingKrullDim (Tate σ) :=
  .of_ringKrullDim_eq_natCast ringKrullDim_isRestricted_subring

/-- **The degree of a normalisation is the Krull dimension.** A ring that is integral over an
injectively embedded Tate algebra `K⟨X₁, …, X_d⟩` has Krull dimension `d`. This applies to the
finite injective maps from Tate algebras supplied by Noether normalisation,
`TauCeti.IsAffinoidAlgebra.exists_finite_injective`. -/
theorem ringKrullDim_eq_natCard_of_isIntegral {σ : Type*} [Finite σ] {A : Type*} [CommRing A]
    [Algebra (Tate σ) A] [Algebra.IsIntegral (Tate σ) A] [FaithfulSMul (Tate σ) A] :
    ringKrullDim A = Nat.card σ := by
  rw [ringKrullDim_eq_of_isIntegral_of_faithfulSMul (R := Tate σ),
    ringKrullDim_isRestricted_subring]

open scoped nonZeroDivisors in
/-- The inductive step for heights of maximal ideals: if every maximal ideal of `K⟨X⟩` has height
at least the number `n` of variables, then every maximal ideal of `K⟨X, Y⟩` has height at least
`n + 1`. -/
private theorem natCard_add_one_le_height_option {σ : Type*} [Finite σ]
    (IH : ∀ (p : Ideal (Tate σ)) [p.IsMaximal], Nat.card σ ≤ p.height)
    (M : Ideal (Tate (Option σ))) [M.IsMaximal] : Nat.card (Option σ) ≤ M.height := by
  -- `M ≠ 0`, since `K⟨X, Y⟩` has positive dimension and so is not a field.
  have hM : M ≠ ⊥ := by
    rintro rfl
    have := ringKrullDim_eq_zero_of_isField (Ring.isField_iff_maximal_bot.mpr ‹_›)
    rw [ringKrullDim_isRestricted_subring, Finite.card_option] at this
    exact Nat.succ_ne_zero (Nat.card σ) (by exact_mod_cast this)
  -- Transport `M` to `K⟨X⟩⟨Y⟩` along a change of variables making some `f ∈ M` distinguished.
  obtain ⟨f, hfM, hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM
  obtain ⟨e, s, hd, hu⟩ := exists_algEquiv_isDistinguished_isUnit f hf
  let R := Tate σ
  let S := PowerSeries.IsRestricted.subring (R := R) 1
  let E : Tate (Option σ) ≃+* S :=
    (e : Tate (Option σ) ≃+* Tate (Option σ)).trans Huber.restrictedOptionEquiv
  let g : S := E f
  let N : Ideal S := M.comap E.symm
  have hgN : g ∈ N := by simpa [N, g] using hfM
  -- `S ⧸ (g)` is finite free over `R`, so going down bounds the height of the image of `N`
  -- below by the height of its contraction to `R`, a maximal ideal.
  let B := S ⧸ Ideal.span {g}
  have : Module.Free R B := hd.free_quotient zero_lt_one hu
  have : Module.Finite R B := hd.finite_quotient zero_lt_one hu
  have : IsNoetherianRing R := isNoetherianRing_isRestricted_subring
  have : IsNoetherianRing B := IsNoetherianRing.of_finite R B
  have : Algebra.IsIntegral R B := Algebra.IsIntegral.of_finite R B
  let Nb : Ideal B := N.map (Ideal.Quotient.mk _)
  have : Nb.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    (by simpa [Ideal.mk_ker, Ideal.span_singleton_le_iff_mem] using hgN)
  let p := Nb.under R
  have : p.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal Nb
  have hNb : p.height ≤ Nb.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p Nb]
    exact le_self_add
  -- Quotienting by the non-zero-divisor `g` lowers the height of `N` by one.
  have hg : g ∈ S⁰ := mem_nonZeroDivisors_of_ne_zero (by simpa [g] using hf)
  rw [← RingEquiv.height_comap E.symm M]
  refine le_trans ?_ (Ideal.height_map_quotientMk_span_singleton_add_one_le hg N hgN)
  rw [Finite.card_option, Nat.cast_add, Nat.cast_one]
  gcongr
  exact (IH p).trans hNb

/-- **Heights of maximal ideals of Tate algebras.** Over a complete nonarchimedean field, every
maximal ideal of the Tate algebra `K⟨X₁, …, Xₙ⟩` has height `n`, its Krull dimension. -/
@[simp]
theorem _root_.Ideal.height_eq_natCard_of_isMaximal_isRestricted_subring {σ : Type*} [Finite σ]
    (M : Ideal (Tate σ)) [M.IsMaximal] : M.height = Nat.card σ := by
  refine le_antisymm ?_ ?_
  · have := Ideal.height_le_ringKrullDim_of_ne_top (Ideal.IsPrime.ne_top' (I := M))
    rw [ringKrullDim_isRestricted_subring] at this
    exact_mod_cast this
  revert M
  induction σ using Finite.induction_empty_option with
  | of_equiv e H =>
    intro M _
    let e' : Tate _ ≃+* Tate _ := (IsRestricted.renameAlgEquiv (R := K) e fun _ ↦ 1).toRingEquiv
    have := H (M.comap e')
    rwa [RingEquiv.height_comap, Nat.card_congr e] at this
  | h_empty => simp
  | h_option IH => exact natCard_add_one_le_height_option IH

end TauCeti.MvPowerSeries
