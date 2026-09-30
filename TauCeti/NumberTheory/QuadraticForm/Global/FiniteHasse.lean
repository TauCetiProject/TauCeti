/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Hasse
public import TauCeti.NumberTheory.QuadraticForm.Global.Discriminant
public import TauCeti.NumberTheory.QuadraticForm.Global.Operations
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# The Hasse sign of a quadratic form at a finite place

For a regular quadratic form `Q` over a number field `K` and a finite place `v` of `K`, the
finite Hasse sign `Q.finiteHasse hQ v ∈ {±1}` is the local Hasse invariant
`TauCeti.RegularFormClass.localHasse` of the localization `Q.atFinitePlace v` over the completion
`K_v`. If `Q ≅ ⟨a₁, …, aₙ⟩` over `K`, it is the product `∏_{i<j} (aᵢ, aⱼ)_v` of the Hilbert
symbols of the localized coefficients, and it does not depend on the chosen diagonalization.

The discriminant square class of `Q` at `v` is the image of the global discriminant of `Q` in
`K_vˣ/(K_vˣ)²`, which is the discriminant of the localized form by
`QuadraticForm.discr_atFinitePlace`. It is the only local datum besides the rank that enters the
behaviour of the finite Hasse sign under the operations on forms:

* orthogonal sum: `s_v(Q ⊥ R) = s_v(Q) · s_v(R) · (d_v(Q), d_v(R))_v`;
* scaling by `a ∈ Kˣ`: `s_v(a Q) = s_v(Q) · (a, -1)_v^{n(n-1)/2} · (a, d_v(Q))_v^{n-1}`;
* negation, the case `a = -1`;
* forms that are isometric at `v`, in particular globally isometric forms, have the same finite
  Hasse sign at `v`.

Together with the rank and the discriminant, the Hasse sign is one of the three invariants that
classify regular quadratic forms over a nonarchimedean local field (O'Meara, §63).

## Main definitions

* `QuadraticForm.finiteHasse`: the Hasse sign of a regular form at a finite place.

## Main results

* `QuadraticForm.finiteHasse_eq_localHasse_baseChange`: the finite Hasse sign is the local Hasse
  invariant of the scalar extension of the global isometry class.
* `QuadraticForm.finiteHasse_eq_prod_hilbertSymbol`: its value `∏_{i<j} (aᵢ, aⱼ)_v` on any
  diagonalization `⟨a₁, …, aₙ⟩` over `K`.
* `QuadraticForm.finiteHasse_eq_of_equivalent_atFinitePlace`,
  `QuadraticMap.Equivalent.finiteHasse_eq`: forms isometric at `v`, in particular isometric forms,
  have the same finite Hasse sign.
* `QuadraticForm.finiteHasse_prod`, `QuadraticForm.finiteHasse_smul`,
  `QuadraticForm.finiteHasse_neg`: the orthogonal-sum, scaling and negation formulas.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter V, §3.
* J.-P. Serre, *A Course in Arithmetic*, Chapter IV, §2.1 and §3.1.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §63.
-/

public section
noncomputable section

open Finset IsDedekindDomain NumberField TauCeti

universe u v w

namespace QuadraticForm

variable {K : Type u} [Field K] [NumberField K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- **The Hasse sign of a regular quadratic form at a finite place** `v` of a number field: the
local Hasse invariant `∏_{i<j} (aᵢ, aⱼ)_v ∈ {±1}` of the localization of `Q` at `v`, for any
diagonalization `⟨a₁, …, aₙ⟩` of that localization over the completion `K_v`. -/
def finiteHasse (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate)
    (v : HeightOneSpectrum (𝓞 K)) : ℤˣ :=
  letI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  RegularFormClass.localHasse (formClass (atFinitePlace Q v) (Nondegenerate.atFinitePlace hQ v))

/-- The finite Hasse sign is the local Hasse invariant of the class of the localized form. -/
theorem finiteHasse_def (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate)
    (v : HeightOneSpectrum (𝓞 K)) :
    letI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    Q.finiteHasse hQ v = RegularFormClass.localHasse
      (formClass (atFinitePlace Q v) (Nondegenerate.atFinitePlace hQ v)) :=
  (rfl)

/-- The finite Hasse sign is the local Hasse invariant of the scalar extension to `K_v` of the
isometry class of `Q` over `K`. -/
theorem finiteHasse_eq_localHasse_baseChange (Q : _root_.QuadraticForm K V)
    (hQ : Q.Nondegenerate) (v : HeightOneSpectrum (𝓞 K)) :
    letI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    Q.finiteHasse hQ v = RegularFormClass.localHasse
      (RegularFormClass.baseChange (v.adicCompletion K) (formClass Q hQ)) := by
  let _ : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  rw [finiteHasse_def, ← formClass_baseChange Q hQ]
  congr 1
  simp only [atFinitePlace_def]

private theorem baseChange_presentation (v : HeightOneSpectrum (𝓞 K)) {n : ℕ} (a : Fin n → Kˣ) :
    RegularFormPresentation.baseChange (v.adicCompletion K) ⟨n, a⟩ =
      ⟨n, fun i => v.unitAtFinitePlace (a i)⟩ :=
  RegularFormPresentation.ext (RegularFormPresentation.fst_baseChange _ _) fun i =>
    Units.ext (by simp)

/-- **Independence of the diagonalization.** If `Q ≅ ⟨a₁, …, aₙ⟩` over `K`, the finite Hasse
sign of `Q` at `v` is `∏_{i<j} (aᵢ, aⱼ)_v`, the product of the Hilbert symbols over `K_v` of the
images of the coefficients. -/
theorem finiteHasse_eq_prod_hilbertSymbol (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate)
    {n : ℕ} {a : Fin n → Kˣ}
    (h : Q.Equivalent (QuadraticMap.weightedSumSquares K fun i => (a i : K)))
    (v : HeightOneSpectrum (𝓞 K)) :
    Q.finiteHasse hQ v =
      ∏ i, ∏ j ∈ Ioi i, hilbertSymbol (v.unitAtFinitePlace (a i)) (v.unitAtFinitePlace (a j)) := by
  let _ : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  rw [finiteHasse_eq_localHasse_baseChange,
    formClass_mk Q hQ ⟨n, a⟩ (by rwa [presentedForm_eq_weightedSumSquares_coe]),
    RegularFormClass.baseChange_mk, baseChange_presentation, RegularFormClass.localHasse_mk]

/-- **Isometry invariance.** Regular forms whose localizations at `v` are isometric have the same
finite Hasse sign at `v`. -/
theorem finiteHasse_eq_of_equivalent_atFinitePlace {Q : _root_.QuadraticForm K V}
    {R : _root_.QuadraticForm K W} (hQ : Q.Nondegenerate) (hR : R.Nondegenerate)
    {v : HeightOneSpectrum (𝓞 K)} (h : (Q.atFinitePlace v).Equivalent (R.atFinitePlace v)) :
    Q.finiteHasse hQ v = R.finiteHasse hR v := by
  rw [finiteHasse_def, finiteHasse_def, (formClass_eq_iff _ _ _ _).mpr h]

/-- Isometric regular forms have the same finite Hasse sign at every finite place. -/
theorem _root_.QuadraticMap.Equivalent.finiteHasse_eq {Q : _root_.QuadraticForm K V}
    {R : _root_.QuadraticForm K W} (h : Q.Equivalent R) (hQ : Q.Nondegenerate)
    (hR : R.Nondegenerate) (v : HeightOneSpectrum (𝓞 K)) :
    Q.finiteHasse hQ v = R.finiteHasse hR v :=
  finiteHasse_eq_of_equivalent_atFinitePlace hQ hR (h.atFinitePlace v)

/-- The finite Hasse sign of a form of rank at most one is trivial. -/
theorem finiteHasse_eq_one_of_finrank_le_one (Q : _root_.QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V ≤ 1) (v : HeightOneSpectrum (𝓞 K)) :
    Q.finiteHasse hQ v = 1 := by
  rw [finiteHasse_eq_localHasse_baseChange]
  exact RegularFormClass.localHasse_eq_one_of_rank_le_one
    (by rwa [RegularFormClass.rank_baseChange, rank_formClass])

/-- **The orthogonal-sum formula** `s_v(Q ⊥ R) = s_v(Q) · s_v(R) · (d_v(Q), d_v(R))_v`, where
`d_v` is the image in `K_vˣ/(K_vˣ)²` of the global discriminant. -/
theorem finiteHasse_prod (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate)
    (R : _root_.QuadraticForm K W) (hR : R.Nondegenerate) (v : HeightOneSpectrum (𝓞 K)) :
    finiteHasse (Q.prod R) (hQ.prod hR) v = Q.finiteHasse hQ v * R.finiteHasse hR v *
      hilbertSymbolOnSquareClasses
        ((algebraMap K (v.adicCompletion K)).squareClassMap
          (RegularFormClass.discr (formClass Q hQ)))
        ((algebraMap K (v.adicCompletion K)).squareClassMap
          (RegularFormClass.discr (formClass R hR))) := by
  rw [finiteHasse_eq_localHasse_baseChange, finiteHasse_eq_localHasse_baseChange,
    finiteHasse_eq_localHasse_baseChange, formClass_prod, RegularFormClass.baseChange_add,
    RegularFormClass.localHasse_add, RegularFormClass.discr_baseChange,
    RegularFormClass.discr_baseChange]

/-- **The scaling formula** `s_v(a Q) = s_v(Q) · (a, -1)_v^{n(n-1)/2} · (a, d_v(Q))_v^{n-1}` for
`a ∈ Kˣ` and a form `Q` of rank `n`, where `d_v(Q)` is the image in `K_vˣ/(K_vˣ)²` of the global
discriminant. -/
theorem finiteHasse_smul (a : Kˣ) (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate)
    (haQ : ((a : K) • Q).Nondegenerate) (v : HeightOneSpectrum (𝓞 K)) :
    ((a : K) • Q).finiteHasse haQ v = Q.finiteHasse hQ v *
      hilbertSymbol (v.unitAtFinitePlace a) (-1) ^ (Module.finrank K V).choose 2 *
      hilbertSymbolOnSquareClasses (squareClass (v.unitAtFinitePlace a))
        ((algebraMap K (v.adicCompletion K)).squareClassMap
          (RegularFormClass.discr (formClass Q hQ))) ^ (Module.finrank K V - 1) := by
  rw [finiteHasse_eq_localHasse_baseChange, finiteHasse_eq_localHasse_baseChange,
    formClass_smul a Q hQ haQ, RegularFormClass.baseChange_mul, RegularFormClass.baseChange_mk,
    baseChange_presentation, RegularFormClass.localHasse_mk_rankOne_mul,
    RegularFormClass.rank_baseChange, rank_formClass, RegularFormClass.discr_baseChange]

/-- **The negation formula** `s_v(-Q) = s_v(Q) · (-1, -1)_v^{n(n-1)/2} · (-1, d_v(Q))_v^{n-1}`
for a form `Q` of rank `n`, where `d_v(Q)` is the image in `K_vˣ/(K_vˣ)²` of the global
discriminant. -/
theorem finiteHasse_neg (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate)
    (v : HeightOneSpectrum (𝓞 K)) :
    (-Q).finiteHasse ((QuadraticMap.nondegenerate_neg Q).mpr hQ) v = Q.finiteHasse hQ v *
      hilbertSymbol (-1 : (v.adicCompletion K)ˣ) (-1) ^ (Module.finrank K V).choose 2 *
      hilbertSymbolOnSquareClasses (squareClass (-1 : (v.adicCompletion K)ˣ))
        ((algebraMap K (v.adicCompletion K)).squareClassMap
          (RegularFormClass.discr (formClass Q hQ))) ^ (Module.finrank K V - 1) := by
  have hneg : -Q = ((-1 : Kˣ) : K) • Q := by ext x; simp
  have hu : v.unitAtFinitePlace (-1 : Kˣ) = -1 := Units.ext (by simp)
  have h := finiteHasse_smul (-1) Q hQ (hneg ▸ (QuadraticMap.nondegenerate_neg Q).mpr hQ) v
  rw [hu] at h
  rw [← h]
  congr 1

end QuadraticForm
