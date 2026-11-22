/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.Predicates
import TauCeti.NumberTheory.QuadraticForm.Global.HigherRank
import TauCeti.NumberTheory.QuadraticForm.Global.LowRank
import TauCeti.NumberTheory.QuadraticForm.Global.Quaternary
import TauCeti.NumberTheory.QuadraticForm.Global.Ternary.Basic

/-!
# The Hasse–Minkowski theorem for isotropy

Let `Q` be a quadratic form on a finite-dimensional vector space over a number field `K`. This file
proves the Hasse–Minkowski theorem: `Q` is isotropic over `K` if and only if it is isotropic at
every finite and every real place of `K` (`QuadraticForm.IsLocallyIsotropic`). As a consequence, a
regular form represents a scalar over `K` if and only if it represents it at every finite and
every real place.

An anisotropic form over a number field is regular, so it is isometric to a diagonal form
`TauCeti.presentedForm p` with unit weights, and it suffices to treat these diagonal forms, by
strong induction on their rank. In rank at most two the theorem is
`QuadraticForm.not_anisotropic_iff_isLocallyIsotropic_of_finrank_le_two`, which rests on the global
square theorem; in rank three it is `QuadraticForm.not_anisotropic_of_isLocallyIsotropic_ternary`,
which rests on the quadratic Hasse norm theorem; in rank four it is
`QuadraticForm.not_anisotropic_of_isLocallyIsotropic_quaternary`, by quaternary descent. In rank
`n ≥ 5`, `QuadraticForm.not_anisotropic_of_isLocallyIsotropic_of_five_le_finrank` reduces the
theorem to diagonal forms of rank `n - 1`.

A nonzero scalar `a` is represented by a regular form `Q` exactly when `⟨-a⟩ ⊥ Q` is isotropic, and
local representation of `a` makes `⟨-a⟩ ⊥ Q` locally isotropic, so the theorem for isotropy gives
the theorem for representation of scalars.

## Main results

* `QuadraticForm.not_anisotropic_of_isLocallyIsotropic`: a locally isotropic quadratic form over a
  number field is isotropic.
* `QuadraticForm.not_anisotropic_iff_isLocallyIsotropic`: the Hasse–Minkowski theorem for isotropy.
* `QuadraticForm.anisotropic_iff_not_isLocallyIsotropic`: a quadratic form over a number field is
  anisotropic if and only if it is anisotropic at some finite or real place.
* `QuadraticForm.represents_iff_locallyRepresentsScalar`: a regular quadratic form over a number
  field represents a scalar if and only if it represents it at every finite and every real place.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 66:1 and 66:3.
* J. S. Milne, *Class Field Theory*, v4.03, Chapter VIII, Theorem 3.5(b), p. 235, and its proof,
  p. 237.
* J.-P. Serre, *A Course in Arithmetic*, Springer (1973), Chapter IV, §3.2, Theorem 8.
-/

public section

open QuadraticMap TauCeti

universe u v

namespace QuadraticForm

variable {K : Type u} [Field K] [NumberField K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **The Hasse–Minkowski theorem for isotropy** (O'Meara 66:1). A quadratic form on a
finite-dimensional space over a number field `K` that is isotropic at every finite and every real
place is isotropic over `K`. -/
theorem not_anisotropic_of_isLocallyIsotropic {Q : _root_.QuadraticForm K V}
    (hloc : Q.IsLocallyIsotropic) : ¬Q.Anisotropic := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  -- First the diagonal forms with unit weights, by strong induction on the rank.
  have key : ∀ (n : ℕ) (w : Fin n → Kˣ),
      (presentedForm ⟨n, w⟩).IsLocallyIsotropic → ¬(presentedForm ⟨n, w⟩).Anisotropic := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro w hw
      have hn : Module.finrank K (Fin n → K) = n := Module.finrank_fin_fun K
      rcases (by omega : n ≤ 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n) with h | rfl | rfl | h
      · exact (not_anisotropic_iff_isLocallyIsotropic_of_finrank_le_two _ (hn.trans_le h)).mpr hw
      · exact not_anisotropic_of_isLocallyIsotropic_ternary hn hw
      · exact not_anisotropic_of_isLocallyIsotropic_quaternary hn hw
      · exact not_anisotropic_of_isLocallyIsotropic_of_five_le_finrank
          (nondegenerate_presentedForm _) (h.trans_eq hn.symm) hw fun p hp ↦
            ih p.1 (by rw [hn] at hp; omega) p.2
  -- An anisotropic form is regular, hence isometric to one of these diagonal forms.
  intro hA
  obtain ⟨p, hp⟩ := exists_presentedForm_equivalent Q hA.nondegenerate
  exact key p.1 p.2 ((QuadraticMap.Equivalent.isLocallyIsotropic_iff hp).mp hloc)
    (hp.anisotropic_iff.mp hA)

/-- **The Hasse–Minkowski theorem for isotropy** (O'Meara 66:1). A quadratic form on a
finite-dimensional space over a number field `K` is isotropic over `K` if and only if it is
isotropic at every finite and every real place. -/
theorem not_anisotropic_iff_isLocallyIsotropic (Q : _root_.QuadraticForm K V) :
    ¬Q.Anisotropic ↔ Q.IsLocallyIsotropic :=
  ⟨isLocallyIsotropic_of_not_anisotropic Q, not_anisotropic_of_isLocallyIsotropic⟩

/-- A quadratic form on a finite-dimensional space over a number field is anisotropic if and only if
it is anisotropic at some finite or real place. -/
theorem anisotropic_iff_not_isLocallyIsotropic (Q : _root_.QuadraticForm K V) :
    Q.Anisotropic ↔ ¬Q.IsLocallyIsotropic :=
  (not_iff_comm.mp (not_anisotropic_iff_isLocallyIsotropic Q)).symm

/-- **The Hasse–Minkowski theorem for representation of scalars** (O'Meara 66:3 for the line
`⟨a⟩`). A regular quadratic form on a finite-dimensional space over a number field `K` represents a
scalar `a ∈ K` over `K` if and only if it represents `a` at every finite and every real place. -/
theorem represents_iff_locallyRepresentsScalar {Q : _root_.QuadraticForm K V}
    (hQ : Q.Nondegenerate) (a : K) :
    Represents Q a ↔ Q.LocallyRepresentsScalar a := by
  refine ⟨LocallyRepresentsScalar.of_represents, fun h ↦ ?_⟩
  rcases eq_or_ne a 0 with rfl | ha
  · exact represents_zero Q
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  -- Local representation of `a` makes `⟨-a⟩ ⊥ Q` locally isotropic, hence isotropic.
  have hiso := not_anisotropic_of_isLocallyIsotropic h.isLocallyIsotropic_smul_sq_prod
  rw [Equivalent.anisotropic_iff ⟨IsometryEquiv.prodComm _ Q⟩] at hiso
  exact mem_unitValueSet.mp
    ((mem_unitValueSet_iff_not_anisotropic_prod Q hQ (Units.mk0 a ha)).mpr hiso)

end QuadraticForm
