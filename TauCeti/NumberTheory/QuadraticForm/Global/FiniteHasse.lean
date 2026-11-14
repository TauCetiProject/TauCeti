/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Hasse
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Completion
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
  diagonalization `⟨a₁, …, aₙ⟩` over `K`, and `QuadraticForm.finiteHasse_weightedSumSquares_binary`:
  the single symbol `(a, b)_v` for a binary form `⟨a, b⟩`.
* `QuadraticForm.finiteHasse_eq_of_equivalent_atFinitePlace`,
  `QuadraticMap.Equivalent.finiteHasse_eq`: forms isometric at `v`, in particular isometric forms,
  have the same finite Hasse sign.
* `QuadraticForm.finiteHasse_eq_one_of_finrank_le_one`,
  `QuadraticForm.finiteHasse_eq_one_of_finrank_eq_two`: the finite Hasse sign is trivial in rank at
  most one, and in rank two wherever the discriminant is the class of `-1`.
* `QuadraticForm.finiteHasse_prod`, `QuadraticForm.finiteHasse_smul`,
  `QuadraticForm.finiteHasse_neg`: the orthogonal-sum, scaling and negation formulas.
* `TauCeti.RegularFormClass.mapRingEquiv_adicCompletionCongr_baseChange`,
  `TauCeti.RegularFormClass.discr_mapRingEquiv_adicCompletionCongr_eq_of_eq`,
  `TauCeti.RegularFormClass.localHasse_baseChange_adicCompletion_of_ringEquiv`: transport of
  localized regular-form classes, discriminants, and local Hasse invariants along
  `adicCompletionCongr`.
* `QuadraticForm.finiteHasse_of_semilinearEquiv`,
  `QuadraticForm.finiteHasse_equivOfRingEquiv_of_semilinearEquiv`,
  `QuadraticForm.finiteHasse_baseChange_of_surjective`: invariance of the finite Hasse sign under
  semilinear equivalences over field isomorphisms and under scalar extension along surjective
  homomorphisms of number fields.

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

/-- The finite Hasse sign of a binary diagonal form `⟨a, b⟩` at `v` is the single Hilbert symbol
`(a, b)_v` of the images of its coefficients. -/
@[simp]
theorem finiteHasse_weightedSumSquares_binary (a b : Kˣ)
    (h : (QuadraticMap.weightedSumSquares K ![(a : K), (b : K)]).Nondegenerate)
    (v : HeightOneSpectrum (𝓞 K)) :
    finiteHasse (QuadraticMap.weightedSumSquares K ![(a : K), (b : K)]) h v =
      hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace b) := by
  have hw : (fun i => ((![a, b] i : Kˣ) : K)) = ![(a : K), (b : K)] := by
    ext i
    fin_cases i <;> rfl
  have h0 : Ioi (0 : Fin 2) = {1} := by decide
  have h1 : Ioi (1 : Fin 2) = ∅ := by decide
  rw [finiteHasse_eq_prod_hilbertSymbol _ h (a := ![a, b]) (by rw [hw]; exact .refl _),
    Fin.prod_univ_two, h0, h1]
  simp

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
@[simp]
theorem finiteHasse_eq_one_of_finrank_le_one (Q : _root_.QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V ≤ 1) (v : HeightOneSpectrum (𝓞 K)) :
    Q.finiteHasse hQ v = 1 := by
  rw [finiteHasse_eq_localHasse_baseChange]
  exact RegularFormClass.localHasse_eq_one_of_rank_le_one
    (by rwa [RegularFormClass.rank_baseChange, rank_formClass])

/-- The finite Hasse sign of a binary form is trivial at every finite place `v` at which the image
of its global discriminant in `K_vˣ/(K_vˣ)²` is the class of `-1`: there the localization is a
hyperbolic plane. -/
theorem finiteHasse_eq_one_of_finrank_eq_two (Q : _root_.QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 2) {v : HeightOneSpectrum (𝓞 K)}
    (hd : letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
      (algebraMap K (v.adicCompletion K)).squareClassMap (RegularFormClass.discr (formClass Q hQ)) =
        squareClass (-1)) :
    Q.finiteHasse hQ v = 1 := by
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  rw [finiteHasse_eq_localHasse_baseChange]
  exact RegularFormClass.localHasse_eq_one_of_rank_eq_two_of_discr_eq_neg_one
    (by rwa [RegularFormClass.rank_baseChange, rank_formClass])
    (by rwa [RegularFormClass.discr_baseChange])

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
    (v : HeightOneSpectrum (𝓞 K)) :
    ((a : K) • Q).finiteHasse ((QuadraticMap.nondegenerate_smul_iff a.isUnit Q).mpr hQ) v =
      Q.finiteHasse hQ v *
      hilbertSymbol (v.unitAtFinitePlace a) (-1) ^ (Module.finrank K V).choose 2 *
      hilbertSymbolOnSquareClasses (squareClass (v.unitAtFinitePlace a))
        ((algebraMap K (v.adicCompletion K)).squareClassMap
          (RegularFormClass.discr (formClass Q hQ))) ^ (Module.finrank K V - 1) := by
  rw [finiteHasse_eq_localHasse_baseChange, finiteHasse_eq_localHasse_baseChange,
    formClass_smul a Q hQ, RegularFormClass.baseChange_mul, RegularFormClass.baseChange_mk,
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
  have h := finiteHasse_smul (-1) Q hQ v
  rw [hu] at h
  rw [← h]
  congr 1

end QuadraticForm

namespace TauCeti.RegularFormClass

open IsDedekindDomain.HeightOneSpectrum

section DedekindDomain

variable {R R' K K' : Type*} [CommRing R] [IsDedekindDomain R] [CommRing R'] [IsDedekindDomain R']
  [Field K] [Field K'] [Algebra R K] [IsFractionRing R K] [Algebra R' K'] [IsFractionRing R' K']

/-- Transporting the `K_v`-scalar extension of a regular-form class along `adicCompletionCongr`
agrees with extending scalars of the `e`-transported class to `K'_w`. -/
@[simp]
theorem mapRingEquiv_adicCompletionCongr_baseChange
    {v : HeightOneSpectrum R} {w : HeightOneSpectrum R'}
    [Invertible (2 : K)] [Invertible (2 : K')]
    [Invertible (2 : v.adicCompletion K)] [Invertible (2 : w.adicCompletion K')]
    {e : K ≃+* K'} (he : ∀ x, w.valuation K' (e x) = v.valuation K x)
    (x : RegularFormClass K) :
    mapRingEquiv (adicCompletionCongr v w e he) (baseChange (v.adicCompletion K) x) =
      baseChange (w.adicCompletion K') (mapRingEquiv e x) :=
  mapRingEquiv_baseChange e (adicCompletionCongr v w e he) (adicCompletionCongr_algebraMap he) x

/-- If a regular-form class over `K_v` has discriminant equal to the localization of a square class
`d` of `K`, transporting it along `adicCompletionCongr` gives a class over `K'_w` whose
discriminant is the localization of `e(d)`. -/
theorem discr_mapRingEquiv_adicCompletionCongr_eq_of_eq
    {v : HeightOneSpectrum R} {w : HeightOneSpectrum R'}
    [Invertible (2 : v.adicCompletion K)] [Invertible (2 : w.adicCompletion K')]
    {e : K ≃+* K'} (he : ∀ x, w.valuation K' (e x) = v.valuation K x)
    {x : RegularFormClass (v.adicCompletion K)} {d : SquareClassGroup K}
    (hd : discr x = (algebraMap K (v.adicCompletion K)).squareClassMap d) :
    discr (mapRingEquiv (adicCompletionCongr v w e he) x) =
      (algebraMap K' (w.adicCompletion K')).squareClassMap ((e : K →+* K').squareClassMap d) := by
  have hcomp : (adicCompletionCongr v w e he :
        v.adicCompletion K →+* w.adicCompletion K').comp (algebraMap K (v.adicCompletion K)) =
      (algebraMap K' (w.adicCompletion K')).comp (e : K →+* K') :=
    RingHom.ext fun a ↦ adicCompletionCongr_algebraMap he a
  rw [discr_mapRingEquiv, hd, ← LinearMap.comp_apply, ← RingHom.squareClassMap_comp, hcomp,
    RingHom.squareClassMap_comp, LinearMap.comp_apply]

/-- Along a valuation-preserving isomorphism `e : K ≃+* K'` of fraction fields of Dedekind domains
with finite residue fields at `v` and `w`, the local Hasse invariant at `w` of a transported
regular-form class equals the local Hasse invariant at `v` of the original class. -/
theorem localHasse_baseChange_adicCompletion_of_valuation_eq
    {v : HeightOneSpectrum R} {w : HeightOneSpectrum R'}
    [Finite (R ⧸ v.asIdeal)] [Finite (R' ⧸ w.asIdeal)]
    [Invertible (2 : K)] [Invertible (2 : K')]
    [Invertible (2 : v.adicCompletion K)] [Invertible (2 : w.adicCompletion K')]
    {e : K ≃+* K'} (he : ∀ x, w.valuation K' (e x) = v.valuation K x)
    (x : RegularFormClass K) :
    localHasse (baseChange (w.adicCompletion K') (mapRingEquiv e x)) =
      localHasse (baseChange (v.adicCompletion K) x) := by
  rw [← mapRingEquiv_adicCompletionCongr_baseChange he, localHasse_mapRingEquiv]

end DedekindDomain

section NumberField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]

-- Not `@[simp]`: once the finite residue-field instances are in scope, `localHasse_mapRingEquiv`
-- already simplifies the left-hand side.
/-- Transporting a regular-form class between number-field completions along `adicCompletionCongr`
preserves its local Hasse invariant, supplying the residue-field finiteness instances from the
number-field assumptions. -/
theorem localHasse_mapRingEquiv_adicCompletionCongr
    {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
    {e : K ≃+* L} (he : ∀ x, w.valuation L (e x) = v.valuation K x)
    (x : RegularFormClass (v.adicCompletion K)) :
    letI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    letI : Finite (𝓞 L ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
    localHasse (mapRingEquiv (adicCompletionCongr v w e he) x) = localHasse x := by
  let _ : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  let _ : Finite (𝓞 L ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  exact localHasse_mapRingEquiv (adicCompletionCongr v w e he) x

/-- For a ring isomorphism `e : K ≃+* L` of number fields carrying a finite place `v` to `w`, the
local Hasse invariant at `w` of a transported global regular-form class equals the local Hasse
invariant at `v` of the original class. -/
theorem localHasse_baseChange_adicCompletion_of_ringEquiv (e : K ≃+* L)
    {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
    (hvw : w.asIdeal = Ideal.map (RingOfIntegers.mapRingEquiv e) v.asIdeal)
    (x : RegularFormClass K) :
    letI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    letI : Finite (𝓞 L ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
    localHasse (baseChange (w.adicCompletion L) (mapRingEquiv e x)) =
      localHasse (baseChange (v.adicCompletion K) x) := by
  let _ : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  let _ : Finite (𝓞 L ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  have he (a : K) : w.valuation L (e a) = v.valuation K a := by
    simpa using valuation_ringEquivOfRingEquiv (K := K) (K' := L)
      (RingOfIntegers.mapRingEquiv e) hvw a
  exact localHasse_baseChange_adicCompletion_of_valuation_eq he x

end NumberField

end TauCeti.RegularFormClass

namespace QuadraticForm

open IsDedekindDomain.HeightOneSpectrum

section SemilinearEquiv

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
variable {σ : K →+* L} {σ' : L →+* K} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {W : Type*} [AddCommGroup W] [Module L W] [FiniteDimensional L W]

/-- Regular quadratic forms over number fields intertwined by a semilinear equivalence
`f : V ≃ₛₗ[σ] W` (`Q' (f u) = σ (Q u)`) have the same finite Hasse sign at finite places `v` and
`w` whose valuations are intertwined by `σ`. -/
theorem finiteHasse_of_semilinearEquiv_of_valuation_eq
    {Q : _root_.QuadraticForm K V} {Q' : _root_.QuadraticForm L W}
    (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate)
    (f : V ≃ₛₗ[σ] W) (hf : ∀ u, Q' (f u) = σ (Q u))
    {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
    (he : ∀ a, w.valuation L (σ a) = v.valuation K a) :
    Q'.finiteHasse hQ' w = Q.finiteHasse hQ v := by
  let _ : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  let _ : Finite (𝓞 L ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  rw [finiteHasse_eq_localHasse_baseChange, finiteHasse_eq_localHasse_baseChange,
    formClass_eq_mapRingEquiv_of_semilinearEquiv hQ hQ' f hf]
  exact RegularFormClass.localHasse_baseChange_adicCompletion_of_valuation_eq
    (e := RingHomInvPair.toRingEquiv σ σ') he (formClass Q hQ)

/-- Regular quadratic forms over number fields intertwined by a semilinear equivalence
`f : V ≃ₛₗ[σ] W` carrying a finite place `v` to `w` have the same finite Hasse sign at `w` and
`v`. -/
theorem finiteHasse_of_semilinearEquiv
    {Q : _root_.QuadraticForm K V} {Q' : _root_.QuadraticForm L W}
    (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate)
    (f : V ≃ₛₗ[σ] W) (hf : ∀ u, Q' (f u) = σ (Q u))
    {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
    (hvw : w.asIdeal =
      Ideal.map (RingOfIntegers.mapRingEquiv (RingHomInvPair.toRingEquiv σ σ')) v.asIdeal) :
    Q'.finiteHasse hQ' w = Q.finiteHasse hQ v := by
  apply finiteHasse_of_semilinearEquiv_of_valuation_eq hQ hQ' f hf
  intro a
  simpa using valuation_ringEquivOfRingEquiv (K := K) (K' := L)
    (RingOfIntegers.mapRingEquiv (RingHomInvPair.toRingEquiv σ σ')) hvw a

/-- Specialization of `finiteHasse_of_semilinearEquiv` when the place of `L` is the image of `v`
under `HeightOneSpectrum.equivOfRingEquiv` along `RingHomInvPair.toRingEquiv σ σ'`. -/
theorem finiteHasse_equivOfRingEquiv_of_semilinearEquiv
    {Q : _root_.QuadraticForm K V} {Q' : _root_.QuadraticForm L W}
    (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate)
    (f : V ≃ₛₗ[σ] W) (hf : ∀ u, Q' (f u) = σ (Q u))
    (v : HeightOneSpectrum (𝓞 K)) :
    Q'.finiteHasse hQ'
        (HeightOneSpectrum.equivOfRingEquiv
          (RingOfIntegers.mapRingEquiv (RingHomInvPair.toRingEquiv σ σ')) v) =
      Q.finiteHasse hQ v :=
  finiteHasse_of_semilinearEquiv hQ hQ' f hf
    (asIdeal_equivOfRingEquiv (RingOfIntegers.mapRingEquiv (RingHomInvPair.toRingEquiv σ σ')) v)

end SemilinearEquiv

section BaseChange

open scoped AdicCompletionExtension

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- If the canonical completion map `completionAlgHom v w` is surjective at a finite place `w` of
`L` above `v` of `K`, extending scalars of a regular form `Q` from `K` to `L` preserves its finite
Hasse sign. -/
theorem finiteHasse_baseChange_of_completionAlgHom_surjective
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal]
    (h : Function.Surjective (completionAlgHom v w))
    (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate) :
    (Q.baseChange L).finiteHasse (Nondegenerate.baseChange hQ) w = Q.finiteHasse hQ v := by
  let _ : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  let _ : Finite (𝓞 L ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  have hsurj : Function.Surjective (algebraMap (v.adicCompletion K) (w.adicCompletion L)) := by
    rw [algebraMap_eq_completionAlgHom]
    exact h
  rw [finiteHasse_eq_localHasse_baseChange, finiteHasse_eq_localHasse_baseChange,
    formClass_baseChange Q hQ, RegularFormClass.baseChange_baseChange L (w.adicCompletion L),
    ← RegularFormClass.baseChange_baseChange (v.adicCompletion K) (w.adicCompletion L),
    RegularFormClass.localHasse_baseChange_of_surjective hsurj]

/-- Extending scalars of a regular form along a surjective homomorphism of number fields (for
example, from `Shrink.{0} K` to `K`) preserves the finite Hasse sign at any pair of lying-over
finite places. -/
theorem finiteHasse_baseChange_of_surjective
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal]
    (h : Function.Surjective (algebraMap K L))
    (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate) :
    (Q.baseChange L).finiteHasse (Nondegenerate.baseChange hQ) w = Q.finiteHasse hQ v :=
  finiteHasse_baseChange_of_completionAlgHom_surjective v w
    (completionAlgHom_bijective_of_surjective v w h).surjective Q hQ

end BaseChange

end QuadraticForm
