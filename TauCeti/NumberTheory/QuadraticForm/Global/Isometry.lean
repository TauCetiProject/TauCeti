/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.Predicates
import TauCeti.NumberTheory.QuadraticForm.Global.Isotropy

/-!
# The Hasse–Minkowski theorem for representation and isometry of forms

Let `Q` be a regular quadratic form and `R` a quadratic form on a finite-dimensional vector space,
both over a number field `K`. This file proves that `Q` admits an injective isometry into `R` if
and only if it does so at every finite and every real place of `K`
(`QuadraticForm.LocallyRepresents`), and that `Q` and `R` are isometric if and only if they are
isometric at every finite and every real place (`QuadraticForm.LocallyEquivalent`). For
representation only `Q` needs to be regular: a zero orthogonal summand of `R` does not help to
represent a regular form, globally or locally, so in the representation theorem `R` may be replaced
by its regular restriction to a complement of its radical.

For regular `R`, the representation theorem is proved by induction on the rank of `Q`. A regular
form of positive rank has a nonzero value `c`; the line `⟨c⟩` is then represented by `Q` and, by the
Hasse–Minkowski theorem for scalars, by `R`. Splitting it off gives `Q ≅ ⟨c⟩ ⊥ Q'` and
`R ≅ ⟨c⟩ ⊥ R'` with `Q'` and `R'` regular, and Witt cancellation for representation, applied at
every finite and every real place, shows that `Q'` is locally represented by `R'`. The isometry
theorem follows from the representation theorem: local isometry forces `Q` and `R` to have the same
dimension, so the resulting injective isometry is bijective.

## Main results

* `QuadraticForm.locallyRepresents_of_locallyRepresents_prod`: a regular finite-dimensional summand
  cancels from a local representation of orthogonal sums.
* `QuadraticForm.LocallyRepresents.isRepresentedBy`,
  `QuadraticForm.isRepresentedBy_iff_locallyRepresents`: the Hasse–Minkowski theorem for
  representation of regular forms.
* `QuadraticForm.LocallyEquivalent.equivalent`, `QuadraticForm.equivalent_iff_locallyEquivalent`:
  the Hasse–Minkowski theorem for isometry of regular forms.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 66:3 and 66:4.
* J.-P. Serre, *A Course in Arithmetic*, Springer (1973), Chapter IV, §3.3, Theorem 9.
-/

public section

open IsDedekindDomain NumberField NumberField.InfinitePlace QuadraticMap TauCeti

universe u v w v₀

namespace QuadraticForm

variable {K : Type u} [Field K] [NumberField K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

omit [FiniteDimensional K W] in
/-- **Local Witt cancellation for representation.** A regular finite-dimensional summand cancels
from a local representation of orthogonal sums over a number field: if `Q₀ ⊥ Q` is represented by
`Q₀ ⊥ R` at every finite and every real place, then so is `Q` by `R`. -/
theorem locallyRepresents_of_locallyRepresents_prod {V₀ : Type v₀} [AddCommGroup V₀] [Module K V₀]
    [FiniteDimensional K V₀] {Q₀ : _root_.QuadraticForm K V₀} {Q : _root_.QuadraticForm K V}
    {R : _root_.QuadraticForm K W} (hQ₀ : Q₀.Nondegenerate)
    (h : LocallyRepresents (Q₀.prod Q) (Q₀.prod R)) : Q.LocallyRepresents R := by
  rw [locallyRepresents_iff] at h ⊢
  refine ⟨fun v ↦ ?_, fun w ↦ ?_⟩
  · let : Invertible (2 : v.adicCompletion K) :=
      (Invertible.map (algebraMap K (v.adicCompletion K)) 2).copy 2 (map_ofNat _ _).symm
    exact isRepresentedBy_of_isRepresentedBy_prod (Nondegenerate.atFinitePlace hQ₀ v)
      ((Equivalent.isRepresentedBy_congr ⟨atFinitePlaceProd Q₀ Q v⟩
        ⟨atFinitePlaceProd Q₀ R v⟩).mp (h.1 v))
  · let : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
    exact isRepresentedBy_of_isRepresentedBy_prod (Nondegenerate.atRealPlace hQ₀ w)
      ((Equivalent.isRepresentedBy_congr ⟨atRealPlaceProd Q₀ Q w⟩
        ⟨atRealPlaceProd Q₀ R w⟩).mp (h.2 w))

/-- The Hasse–Minkowski theorem for representation of a regular form by a regular form, by
induction on the rank of the represented form. -/
private theorem isRepresentedBy_of_locallyRepresents_of_nondegenerate [FiniteDimensional K V]
    {Q : _root_.QuadraticForm K V} {R : _root_.QuadraticForm K W} (hQ : Q.Nondegenerate)
    (hR : R.Nondegenerate) (h : Q.LocallyRepresents R) : Q.IsRepresentedBy R := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  induction hn : Module.finrank K V generalizing V W with
  | zero =>
    have : Subsingleton V := Module.finrank_zero_iff.mp hn
    exact (isRepresentedBy_iff Q R).mpr
      ⟨0, Function.injective_of_subsingleton _, fun x ↦ by simp [Subsingleton.elim x 0]⟩
  | succ n ih =>
    -- A regular form on a nonzero space has a nonzero value `c = Q x`.
    have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hn
    obtain ⟨x, hx⟩ : ∃ x, Q x ≠ 0 := hQ.exists_isUnit.imp fun _ ↦ IsUnit.ne_zero
    set L : _root_.QuadraticForm K K := Q x • QuadraticMap.sq
    have hL : L.Nondegenerate := QuadraticMap.nondegenerate_smul_sq hx
    -- The line `⟨c⟩` is represented by `Q`, and, by Hasse–Minkowski for scalars, by `R`.
    have hLQ : L.IsRepresentedBy Q := (isRepresentedBy_smul_sq_iff Q hx).mpr
      ((represents_iff Q _).mpr ⟨x, rfl⟩)
    have hLR : L.IsRepresentedBy R := (isRepresentedBy_smul_sq_iff R hx).mpr
      ((represents_iff_locallyRepresentsScalar R _).mpr
        (h.locallyRepresentsScalar (LocallyRepresentsScalar.of_represents
          ((represents_iff Q _).mpr ⟨x, rfl⟩))))
    -- Split the line off both forms and cancel it at every finite and every real place.
    obtain ⟨P, hP, hQP⟩ := hLQ.exists_equivalent_prod hL hQ
    obtain ⟨S, hS, hRS⟩ := hLR.exists_equivalent_prod hL hR
    have hloc := locallyRepresents_of_locallyRepresents_prod hL
      ((QuadraticMap.Equivalent.locallyRepresents_congr hQP hRS).mp h)
    have hPn : Module.finrank K P = n := by
      obtain ⟨e⟩ := hQP
      have := e.toLinearEquiv.finrank_eq
      rw [Module.finrank_prod, Module.finrank_self] at this
      omega
    exact (hQP.isRepresentedBy_congr hRS).mpr
      ((IsRepresentedBy.refl L).prod (ih hP hS hloc hPn))

/-- **The Hasse–Minkowski theorem for representation of forms** (O'Meara 66:3). A regular form `Q`
over a number field `K` that is represented by a form `R` on a finite-dimensional space at every
finite and every real place is represented by `R` over `K`. -/
theorem LocallyRepresents.isRepresentedBy {Q : _root_.QuadraticForm K V}
    {R : _root_.QuadraticForm K W} (hQ : Q.Nondegenerate) (h : Q.LocallyRepresents R) :
    Q.IsRepresentedBy R := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  have : FiniteDimensional K V := h.finiteDimensional
  -- Split `R` as `R' ⊥ 0`, where `R'` is its regular restriction to a complement of the radical;
  -- the zero summand does not help to represent the regular form `Q`, globally or locally.
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl R.radical
  have hloc : Q.LocallyRepresents (R.restrict C) :=
    ((QuadraticMap.Equivalent.locallyRepresents_congr (.refl Q)
      ⟨(IsometryEquiv.restrictProdRadicalOfIsCompl R C hC).symm⟩).mp h).of_prod_zero hQ
  exact (isRepresentedBy_of_locallyRepresents_of_nondegenerate hQ
    (nondegenerate_restrict_of_isCompl_radical R hC) hloc).trans (restrict_isRepresentedBy R C)

/-- **The Hasse–Minkowski theorem for representation of forms** (O'Meara 66:3). A regular form over
a number field `K` is represented over `K` by a form on a finite-dimensional space if and only if it
is represented by it at every finite and every real place. -/
theorem isRepresentedBy_iff_locallyRepresents {Q : _root_.QuadraticForm K V}
    (R : _root_.QuadraticForm K W) (hQ : Q.Nondegenerate) :
    Q.IsRepresentedBy R ↔ Q.LocallyRepresents R :=
  ⟨LocallyRepresents.of_isRepresentedBy, fun h ↦ h.isRepresentedBy hQ⟩

/-- **The Hasse–Minkowski theorem for isometry** (O'Meara 66:4). A regular form over a number field
`K` that is isometric to a form `R` on a finite-dimensional space at every finite and every real
place is isometric to `R` over `K`. -/
theorem LocallyEquivalent.equivalent {Q : _root_.QuadraticForm K V}
    {R : _root_.QuadraticForm K W} (hQ : Q.Nondegenerate) (h : Q.LocallyEquivalent R) :
    Q.Equivalent R := by
  have : FiniteDimensional K V := h.locallyRepresents.finiteDimensional
  obtain ⟨f, hf, hfQ⟩ := (isRepresentedBy_iff Q R).mp (h.locallyRepresents.isRepresentedBy hQ)
  have hbij : Function.Bijective f :=
    ⟨hf, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h.finrank_eq).mp hf⟩
  exact ⟨{ toLinearEquiv := LinearEquiv.ofBijective f hbij
           map_app' x := by
             simpa only [LinearEquiv.coe_toLinearMap, LinearMap.toFun_eq_coe,
               LinearEquiv.ofBijective_apply] using hfQ x }⟩

/-- **The Hasse–Minkowski theorem for isometry** (O'Meara 66:4). A regular form over a number field
`K` is isometric over `K` to a form on a finite-dimensional space if and only if the two forms are
isometric at every finite and every real place. -/
theorem equivalent_iff_locallyEquivalent {Q : _root_.QuadraticForm K V}
    (R : _root_.QuadraticForm K W) (hQ : Q.Nondegenerate) :
    Q.Equivalent R ↔ Q.LocallyEquivalent R :=
  ⟨LocallyEquivalent.of_equivalent, fun h ↦ h.equivalent hQ⟩

end QuadraticForm
