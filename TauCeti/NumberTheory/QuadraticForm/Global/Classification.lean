/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Classification
public import TauCeti.NumberTheory.QuadraticForm.Global.FormInvariants
public import TauCeti.NumberTheory.QuadraticForm.Global.LocalRealization
public import TauCeti.NumberTheory.QuadraticForm.Global.Predicates

/-!
# Local classification of quadratic forms over a number field

Over a nonarchimedean local field, regular quadratic forms are classified by their rank, plain
discriminant and local Hasse invariant
(`QuadraticForm.equivalent_iff_finrank_eq_and_discr_eq_and_localHasse_eq`). This file restates
that classification at a finite place `v` of a number field `K` in terms of the invariants of a
global regular form `Q`: the rank of the localization `Q_v` is the rank of `Q`, its discriminant
is the image in `K_vˣ/(K_vˣ)²` of the global discriminant `d(Q)`, and its local Hasse invariant is
the finite Hasse sign `s_v(Q)`. So `Q_v` is isometric to a regular form `U` over `K_v` exactly when
these three invariants match those of `U`, and two localizations `Q_v` and `R_v` are isometric
exactly when `Q` and `R` have the same rank, the same discriminant at `v` and the same Hasse sign
at `v`.

Combined with Sylvester's law at the real places, this characterizes local equivalence (at every
finite and real place) by the rank, the discriminants at the finite places, the finite Hasse signs
and the real positive indices. The criterion uses the discriminant at each finite place rather
than the global discriminant: that two forms with the same discriminant at every place have the
same global discriminant is the global square theorem. In particular, forms with the same system
of local invariants `QuadraticForm.globalInvariants` are locally equivalent, and a global form
whose system is `I` is isometric at every finite and real place to each family of local forms
realizing `I`.

In global notation, the two exceptions of the local realization theorem
`TauCeti.RegularFormClass.exists_of_realization` are the small-rank conditions of
`TauCeti.NumberField.QuadraticForm.GlobalFormInvariants.IsAdmissible`.

## Main results

* `atFinitePlace_equivalent_iff_finrank_eq_and_discr_eq_and_finiteHasse_eq`: the localization of
  a global form at a finite place is isometric to a regular local form exactly when their ranks,
  discriminants and Hasse invariants agree.
* `equivalent_atFinitePlace_iff_finrank_eq_and_discr_eq_and_finiteHasse_eq`: two localizations at
  a finite place are isometric exactly when the ranks, the discriminants at that place and the
  finite Hasse signs agree.
* `locallyEquivalent_iff_finrank_eq_and_discr_eq_and_finiteHasse_eq_and_realPositiveIndex_eq`:
  two regular forms are locally equivalent exactly when their ranks, their discriminants at every
  finite place, their finite Hasse signs and their real positive indices agree.
* `QuadraticForm.LocallyEquivalent.of_globalInvariants_eq`: forms with the same system of local
  invariants are locally equivalent.
* `GlobalFormInvariants.IsLocalRealization.equivalent_atFinitePlace`,
  `GlobalFormInvariants.IsLocalRealization.equivalent_atRealPlace`: a form whose system is `I` is
  isometric at every finite and real place to any family realizing `I`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 63:20 for the local
  classification and 66:5 for the local invariants of a global form.
* J.-P. Serre, *A Course in Arithmetic*, Springer (1973), Chapter IV, §2.3, Theorem 7, and §3.1.
-/

public section

open IsDedekindDomain NumberField NumberField.InfinitePlace TauCeti
open TauCeti.NumberField.QuadraticForm (GlobalFormInvariants)

universe u v w

namespace QuadraticForm

variable {K : Type u} [Field K] [NumberField K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- The class of the localization of a form at a finite place is the scalar extension of the class
of the form. -/
private theorem formClass_atFinitePlace (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate)
    (v : HeightOneSpectrum (𝓞 K)) :
    formClass (Q.atFinitePlace v) (Nondegenerate.atFinitePlace hQ v) =
      RegularFormClass.baseChange (v.adicCompletion K) (formClass Q hQ) := by
  rw [← formClass_baseChange Q hQ]
  congr 1
  simp only [atFinitePlace_def]

/-- **Local classification at a finite place, in global notation.** The localization of a regular
form `Q` at a finite place `v` is isometric to a regular form `U` over `K_v` exactly when the rank
of `Q` is the dimension of `U`, the image of the global discriminant of `Q` in `K_vˣ/(K_vˣ)²` is
the discriminant of `U`, and the finite Hasse sign `s_v(Q)` is the local Hasse invariant of `U`. -/
theorem atFinitePlace_equivalent_iff_finrank_eq_and_discr_eq_and_finiteHasse_eq
    (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate) (v : HeightOneSpectrum (𝓞 K))
    {X : Type*} [AddCommGroup X] [Module (v.adicCompletion K) X]
    [FiniteDimensional (v.adicCompletion K) X] {U : _root_.QuadraticForm (v.adicCompletion K) X}
    (hU : U.Nondegenerate) :
    (Q.atFinitePlace v).Equivalent U ↔
      Module.finrank K V = Module.finrank (v.adicCompletion K) X ∧
      (algebraMap K (v.adicCompletion K)).squareClassMap
          (RegularFormClass.discr (formClass Q hQ)) = RegularFormClass.discr (formClass U hU) ∧
      Q.finiteHasse hQ v = RegularFormClass.localHasse (formClass U hU) := by
  rw [equivalent_iff_finrank_eq_and_discr_eq_and_localHasse_eq _
    (Nondegenerate.atFinitePlace hQ v) hU, finiteHasse_def, formClass_atFinitePlace,
    RegularFormClass.discr_baseChange, Module.finrank_baseChange]

/-- **Local classification at a finite place.** The localizations of two regular forms `Q` and
`R` at a finite place `v` are isometric exactly when `Q` and `R` have the same rank, the images of
their global discriminants in `K_vˣ/(K_vˣ)²` agree, and their finite Hasse signs at `v` agree. -/
theorem equivalent_atFinitePlace_iff_finrank_eq_and_discr_eq_and_finiteHasse_eq
    (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate) (R : _root_.QuadraticForm K W)
    (hR : R.Nondegenerate) (v : HeightOneSpectrum (𝓞 K)) :
    (Q.atFinitePlace v).Equivalent (R.atFinitePlace v) ↔
      Module.finrank K V = Module.finrank K W ∧
      (algebraMap K (v.adicCompletion K)).squareClassMap
          (RegularFormClass.discr (formClass Q hQ)) =
        (algebraMap K (v.adicCompletion K)).squareClassMap
          (RegularFormClass.discr (formClass R hR)) ∧
      Q.finiteHasse hQ v = R.finiteHasse hR v := by
  rw [atFinitePlace_equivalent_iff_finrank_eq_and_discr_eq_and_finiteHasse_eq Q hQ v
      (Nondegenerate.atFinitePlace hR v),
    formClass_atFinitePlace, RegularFormClass.discr_baseChange, Module.finrank_baseChange,
    finiteHasse_eq_localHasse_baseChange R hR v]

/-- **Local equivalence by invariants.** Two regular forms over a number field are isometric at
every finite and every real place exactly when they have the same rank, the images of their global
discriminants agree at every finite place, and they have the same Hasse sign at every finite place
and the same positive index at every real place. -/
theorem locallyEquivalent_iff_finrank_eq_and_discr_eq_and_finiteHasse_eq_and_realPositiveIndex_eq
    {Q : _root_.QuadraticForm K V} {R : _root_.QuadraticForm K W} (hQ : Q.Nondegenerate)
    (hR : R.Nondegenerate) :
    Q.LocallyEquivalent R ↔
      Module.finrank K V = Module.finrank K W ∧
      (∀ v : HeightOneSpectrum (𝓞 K), (algebraMap K (v.adicCompletion K)).squareClassMap
          (RegularFormClass.discr (formClass Q hQ)) =
        (algebraMap K (v.adicCompletion K)).squareClassMap
          (RegularFormClass.discr (formClass R hR))) ∧
      Q.finiteHasse hQ = R.finiteHasse hR ∧ Q.realPositiveIndex = R.realPositiveIndex := by
  refine ⟨fun h => ?_, fun ⟨hrank, hd, hs, hp⟩ => (locallyEquivalent_iff Q R).mpr
    ⟨fun v => ?_, fun w => ?_⟩⟩
  · obtain ⟨hfin, hreal⟩ := (locallyEquivalent_iff Q R).mp h
    have hv := fun v =>
      (equivalent_atFinitePlace_iff_finrank_eq_and_discr_eq_and_finiteHasse_eq Q hQ R hR v).mp
        (hfin v)
    exact ⟨h.finrank_eq, fun v => (hv v).2.1, funext fun v => (hv v).2.2,
      funext fun w => (equivalent_atRealPlace_iff_realPositiveIndex_eq_of_finrank_eq hQ hR
        h.finrank_eq w).mp (hreal w)⟩
  · exact (equivalent_atFinitePlace_iff_finrank_eq_and_discr_eq_and_finiteHasse_eq Q hQ R hR
      v).mpr ⟨hrank, hd v, congrFun hs v⟩
  · exact (equivalent_atRealPlace_iff_realPositiveIndex_eq_of_finrank_eq hQ hR hrank w).mpr
      (congrFun hp w)

/-- Regular forms with the same system of local invariants are isometric at every finite and every
real place. -/
theorem LocallyEquivalent.of_globalInvariants_eq {Q : _root_.QuadraticForm K V}
    {R : _root_.QuadraticForm K W} {hQ : Q.Nondegenerate} {hR : R.Nondegenerate}
    (h : Q.globalInvariants hQ = R.globalInvariants hR) : Q.LocallyEquivalent R := by
  have hd := congrArg GlobalFormInvariants.discr h
  rw [globalInvariants_discr, globalInvariants_discr] at hd
  refine
    (locallyEquivalent_iff_finrank_eq_and_discr_eq_and_finiteHasse_eq_and_realPositiveIndex_eq
      hQ hR).mpr ⟨?_, fun v => by rw [hd], ?_, ?_⟩
  · simpa using congrArg GlobalFormInvariants.rank h
  · simpa using congrArg GlobalFormInvariants.finiteHasse h
  · simpa using congrArg GlobalFormInvariants.realPositiveIndex h

end QuadraticForm

namespace TauCeti.NumberField.QuadraticForm.GlobalFormInvariants.IsLocalRealization

variable {K : Type u} [Field K] [NumberField K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {I : GlobalFormInvariants K}
  {U : ∀ v : HeightOneSpectrum (𝓞 K),
    _root_.QuadraticForm (v.adicCompletion K) (Fin I.rank → v.adicCompletion K)}
  {R : {w : InfinitePlace K // w.IsReal} → _root_.QuadraticForm ℝ (Fin I.rank → ℝ)}
  {Q : _root_.QuadraticForm K V} {hQ : Q.Nondegenerate}

/-- A regular form whose system of local invariants is `I` is isometric at every finite place `v`
to the form at `v` of any family realizing `I`. -/
theorem equivalent_atFinitePlace (hL : I.IsLocalRealization U R)
    (hQI : Q.globalInvariants hQ = I) (v : HeightOneSpectrum (𝓞 K)) :
    (Q.atFinitePlace v).Equivalent (U v) := by
  subst hQI
  refine (Q.atFinitePlace_equivalent_iff_finrank_eq_and_discr_eq_and_finiteHasse_eq hQ v
    (hL.nondegenerate_finite v)).mpr ⟨by simp, ?_, ?_⟩
  · rw [hL.discr_finite, GlobalFormInvariants.discrAtFinitePlace_def,
      QuadraticForm.globalInvariants_discr]
  · rw [hL.localHasse_finite, QuadraticForm.globalInvariants_finiteHasse]

/-- A regular form whose system of local invariants is `I` is isometric at every real place `w`
to the form at `w` of any family realizing `I`. -/
theorem equivalent_atRealPlace (hL : I.IsLocalRealization U R)
    (hQI : Q.globalInvariants hQ = I) (w : {w : InfinitePlace K // w.IsReal}) :
    (Q.atRealPlace w).Equivalent (R w) := by
  subst hQI
  rw [QuadraticForm.equivalent_iff_sigPos_eq_and_sigNeg_eq
    (QuadraticForm.Nondegenerate.atRealPlace hQ w) (hL.nondegenerate_real w), hL.sigPos_real,
    hL.sigNeg_real, QuadraticForm.globalInvariants_realPositiveIndex,
    QuadraticForm.globalInvariants_realNegativeIndex, QuadraticForm.realPositiveIndex_eq_sigPos,
    QuadraticForm.realNegativeIndex_eq_sigNeg]
  exact ⟨rfl, rfl⟩

end TauCeti.NumberField.QuadraticForm.GlobalFormInvariants.IsLocalRealization
