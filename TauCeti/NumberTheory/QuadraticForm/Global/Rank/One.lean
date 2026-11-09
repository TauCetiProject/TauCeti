/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.Classification
public import TauCeti.NumberTheory.QuadraticForm.Global.ComplexPlaces
public import TauCeti.NumberTheory.QuadraticForm.Global.Discriminant
import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.LowRank

/-!
# Prescribed local behavior in rank one

A regular line is classified over any field of characteristic different from two by its plain
discriminant. Consequently, if regular lines at all finite and real places of a number field have
discriminants obtained from one global square class, the global line representing that class has
exactly the prescribed local isometry classes. Any regular complex line is automatically
isometric to its complex scalar extension. This is the rank-one case of existence with
prescribed local behavior; it needs no Hilbert-sign correction.

Every admissible rank-one invariant system is therefore realized by a regular global line.
The finite Hasse signs must all be one, and the real positive indices are determined by the
localized discriminant. Conversely, the invariants of a regular line are admissible: its Hasse
product is one because there are no pairs of diagonal coefficients. These statements need
neither Hilbert reciprocity nor a local-global principle for isotropy or representation.

The proof uses the low-rank classification of regular form classes and the compatibility of
discriminants with scalar extension.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 72:1.
-/

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace QuadraticMap TauCeti

namespace TauCeti.NumberField.QuadraticForm

variable {K : Type*} [Field K] [NumberField K]

/-- **Existence with prescribed local behavior for regular lines.** If every prescribed finite
and real local line has the image of one global discriminant class `d`, then a global line of
discriminant `d` localizes to those lines and to any prescribed regular complex line. -/
theorem exists_rankOne_form_equivalent_at_places (d : SquareClassGroup K)
    (U : ∀ v : HeightOneSpectrum (𝓞 K),
      _root_.QuadraticForm (v.adicCompletion K) (Fin 1 → v.adicCompletion K))
    (R : ∀ _w : {w : InfinitePlace K // w.IsReal},
      _root_.QuadraticForm ℝ (Fin 1 → ℝ))
    (C : ∀ _w : InfinitePlace K, _root_.QuadraticForm ℂ (Fin 1 → ℂ))
    (hU : ∀ v, (U v).Nondegenerate) (hR : ∀ w, (R w).Nondegenerate)
    (hC : ∀ w, (C w).Nondegenerate)
    (hUd : ∀ (v : HeightOneSpectrum (𝓞 K)),
      letI : Invertible (2 : v.adicCompletion K) :=
        (Invertible.map (algebraMap K (v.adicCompletion K)) 2).copy 2 (map_ofNat _ _).symm;
      RegularFormClass.discr (formClass (U v) (hU v)) =
        (algebraMap K (v.adicCompletion K)).squareClassMap d)
    (hRd : ∀ (w : {w : InfinitePlace K // w.IsReal}),
      RegularFormClass.discr (formClass (R w) (hR w)) =
      (embedding_of_isReal w.2).squareClassMap d) :
    ∃ Q : _root_.QuadraticForm K (Fin 1 → K), ∃ hQ : Q.Nondegenerate,
      (letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero;
        RegularFormClass.discr (formClass Q hQ) = d) ∧
      (∀ v, (Q.atFinitePlace v).Equivalent (U v)) ∧
      (∀ w, (Q.atRealPlace w).Equivalent (R w)) ∧
      ∀ w, (Q.atComplexEmbedding w).Equivalent (C w) := by
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let a : Kˣ := Additive.toMul (Quotient.out d)
  let p : RegularFormPresentation K := ⟨1, fun _ => a⟩
  let Q : _root_.QuadraticForm K (Fin 1 → K) := presentedForm p
  let hQ : Q.Nondegenerate := nondegenerate_presentedForm p
  have hd : RegularFormClass.discr (formClass Q hQ) = d := by
    have hp : formClass Q hQ = Quotient.mk (regularFormSetoid K) p :=
      formClass_presentedForm p
    rw [hp, RegularFormClass.discr_mk]
    simp [p, a]
  refine ⟨Q, hQ, hd, ?_, ?_, ?_⟩
  · intro v
    let _ : Invertible (2 : v.adicCompletion K) :=
      (Invertible.map (algebraMap K (v.adicCompletion K)) 2).copy 2 (map_ofNat _ _).symm
    have hQv := _root_.QuadraticForm.Nondegenerate.atFinitePlace hQ v
    apply (_root_.QuadraticForm.equivalent_iff_discr_eq_and_hasseInvariant_eq
      (Q.atFinitePlace v) hQv (hU v) (by simp) (by simp)).mpr
    constructor
    · rw [_root_.QuadraticForm.discr_atFinitePlace Q hQ v, hd, ← hUd v]
    · rw [RegularFormClass.hasseInvariant_eq_one_of_rank_le_one (by simp),
        RegularFormClass.hasseInvariant_eq_one_of_rank_le_one (by simp)]
  · intro w
    have hQw := _root_.QuadraticForm.Nondegenerate.atRealPlace hQ w
    apply (_root_.QuadraticForm.equivalent_iff_discr_eq_and_hasseInvariant_eq
      (Q.atRealPlace w) hQw (hR w) (by simp) (by simp)).mpr
    constructor
    · rw [_root_.QuadraticForm.discr_atRealPlace Q hQ w, hd, ← hRd w]
    · rw [RegularFormClass.hasseInvariant_eq_one_of_rank_le_one (by simp),
        RegularFormClass.hasseInvariant_eq_one_of_rank_le_one (by simp)]
  · intro w
    let _ : Invertible (2 : ℂ) := invertibleOfNonzero two_ne_zero
    exact (_root_.QuadraticForm.equivalent_iff_finrank_eq_of_isSepClosed
      (Q.atComplexEmbedding w) (C w)
      (_root_.QuadraticForm.Nondegenerate.atComplexEmbedding hQ w) (hC w)).mpr (by simp)

namespace GlobalFormInvariants

/-- Every admissible rank-one system is realized by a regular global line. -/
theorem IsAdmissible.exists_globalForm_of_rank_eq_one {I : GlobalFormInvariants K}
    (hI : I.IsAdmissible) (hn : I.rank = 1) :
    ∃ (Q : _root_.QuadraticForm K (Fin 1 → K)) (hQ : Q.Nondegenerate),
      Q.globalInvariants hQ = I := by
  -- Reduce the coordinate spaces of the local realizations to `Fin 1`.
  rcases I with ⟨n, d, s, p⟩
  dsimp only at hn
  subst n
  obtain ⟨U, R, hL⟩ := hI.exists_isLocalRealization
  let C : InfinitePlace K → _root_.QuadraticForm ℂ (Fin 1 → ℂ) :=
    fun _ => presentedForm ⟨1, fun _ => 1⟩
  obtain ⟨Q, hQ, hd, -, hR, -⟩ := exists_rankOne_form_equivalent_at_places d U R C
    hL.nondegenerate_finite hL.nondegenerate_real
    (fun _ => nondegenerate_presentedForm ⟨1, fun _ => (1 : ℂˣ)⟩)
    (fun v => by
      -- The localization API uses a mapped inverse of two, whereas local invariants use
      -- the canonical characteristic-zero instance; `Invertible` is a subsingleton.
      rw [Subsingleton.elim
        ((Invertible.map (algebraMap K (v.adicCompletion K)) 2).copy 2 (map_ofNat _ _).symm)
        (invertibleTwo : Invertible (2 : v.adicCompletion K))]
      simpa only [discrAtFinitePlace_def] using hL.discr_finite v)
    (fun w => by simpa only [discrAtRealPlace_def] using hL.discr_real hI w)
  refine ⟨Q, hQ, GlobalFormInvariants.ext (by simp) ?_ (funext fun v => ?_)
    (funext fun w => ?_)⟩
  · rw [_root_.QuadraticForm.globalInvariants_discr]
    exact hd
  · rw [_root_.QuadraticForm.globalInvariants_finiteHasse,
      _root_.QuadraticForm.finiteHasse_eq_one_of_finrank_le_one Q hQ (by simp)]
    exact (hI.finiteHasse_eq_one_of_rank_eq_one rfl v).symm
  · rw [_root_.QuadraticForm.globalInvariants_realPositiveIndex,
      _root_.QuadraticForm.realPositiveIndex_eq_sigPos, (hR w).sigPos_eq]
    exact hL.sigPos_real w

/-- In rank one, admissibility is equivalent to realization by a regular global line. -/
theorem isAdmissible_iff_exists_globalForm_of_rank_eq_one (I : GlobalFormInvariants K)
    (hn : I.rank = 1) :
    I.IsAdmissible ↔ ∃ (Q : _root_.QuadraticForm K (Fin 1 → K)) (hQ : Q.Nondegenerate),
      Q.globalInvariants hQ = I := by
  refine ⟨fun hI => hI.exists_globalForm_of_rank_eq_one hn, ?_⟩
  rintro ⟨Q, hQ, rfl⟩
  apply (Q.isAdmissible_globalInvariants_iff hQ).mpr
  refine ⟨by simp, ?_⟩
  -- Every real negative index is at most one, so every real Hasse sign is one.
  have hreal (w) : (Q.globalInvariants hQ).realHasse w = 1 := by
    have hsum : Q.realPositiveIndex w + Q.realNegativeIndex w = 1 := by
      simpa using _root_.QuadraticForm.realPositiveIndex_add_realNegativeIndex_eq_finrank hQ w
    have hbound : Q.realNegativeIndex w ≤ 1 := by omega
    rw [realHasse_def, Q.globalInvariants_realNegativeIndex hQ]
    interval_cases Q.realNegativeIndex w <;> norm_num
  rw [hasseProduct_def]
  simp only [_root_.QuadraticForm.globalInvariants_finiteHasse,
    _root_.QuadraticForm.finiteHasse_eq_one_of_finrank_le_one Q hQ (by simp),
    hreal, finprod_one, Finset.prod_const_one, mul_one]

/-- A rank-one admissible system has a global realization isometric at every finite and real
place to any chosen local realization of that system. -/
theorem IsAdmissible.exists_globalForm_equivalent_at_places_of_rank_eq_one
    {I : GlobalFormInvariants K} (hI : I.IsAdmissible) (hn : I.rank = 1)
    {U : ∀ v : HeightOneSpectrum (𝓞 K),
      _root_.QuadraticForm (v.adicCompletion K) (Fin I.rank → v.adicCompletion K)}
    {R : {w : InfinitePlace K // w.IsReal} → _root_.QuadraticForm ℝ (Fin I.rank → ℝ)}
    (hL : I.IsLocalRealization U R) :
    ∃ (Q : _root_.QuadraticForm K (Fin 1 → K)) (hQ : Q.Nondegenerate),
      Q.globalInvariants hQ = I ∧
      (∀ v, (Q.atFinitePlace v).Equivalent (U v)) ∧
      ∀ w, (Q.atRealPlace w).Equivalent (R w) := by
  obtain ⟨Q, hQ, hQI⟩ := hI.exists_globalForm_of_rank_eq_one hn
  exact ⟨Q, hQ, hQI, hL.equivalent_atFinitePlace hQI, hL.equivalent_atRealPlace hQI⟩

end GlobalFormInvariants

end TauCeti.NumberField.QuadraticForm
