/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsRealClosed.Real
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Signature
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Witt
public import TauCeti.NumberTheory.QuadraticForm.Global.Classification

/-!
# Witt classes of the localizations of a quadratic form

Let `Q` and `R` be regular quadratic forms over a number field `K`. This file gives invariant
criteria for the localizations `Q_v` and `R_v` to have the same Witt class, place by place, in
terms of invariants of the global forms.

* At a finite place `v`, the Witt class of a regular form over the nonarchimedean local field
  `K_v` is determined by its rank modulo two, its signed discriminant `d±` and its Clifford
  invariant `c` (`TauCeti.wittClass_eq_iff_rank_modEq_and_signedDiscr_eq_and_cliffordInvariant_eq`).
  The rank of `Q_v` is the rank of `Q`, and both `d±` and `c` commute with scalar extension. So
  `Q_v` and `R_v` have the same Witt class exactly when the ranks of `Q` and `R` have the same
  parity and the images in `K_v` of the global invariants `d±(Q), d±(R) ∈ Kˣ/(Kˣ)²` and
  `c(Q), c(R) ∈ Br(K)` agree.
* At a real place `w`, the signature `W(ℝ) → ℤ` is an isomorphism, so `Q_w` and `R_w` have the
  same Witt class exactly when the integer signatures `p_w - q_w` agree.

Unlike the isometry criterion at a finite place
(`QuadraticForm.equivalent_atFinitePlace_iff_finrank_eq_and_discr_eq_and_finiteHasse_eq`), the
ranks need not be equal: the invariants used here do not change when a hyperbolic plane is
added. The criteria use the images of the global signed discriminants at every finite place; that
two forms whose signed discriminants agree at every finite place have the same global signed
discriminant is the global square theorem.

Complex places are omitted: over `ℂ` the Witt class of a regular form is determined by its rank
modulo two, which the finite places already detect.

## Main results

* `QuadraticForm.wittClass_formClass_atFinitePlace_eq_iff`: the localizations at a finite place
  have the same Witt class exactly when the ranks have the same parity and the signed
  discriminants and Clifford invariants agree in `K_v`.
* `QuadraticForm.wittClass_formClass_atRealPlace_eq_iff`: the localizations at a real place have
  the same Witt class exactly when their signatures agree.
* `QuadraticForm.locally_wittClass_formClass_eq_iff`: the localizations have the same Witt class
  at every finite and every real place exactly when the ranks have the same parity, the signed
  discriminants and Clifford invariants agree at every finite place, and the signatures agree at
  every real place.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Graduate Studies in Mathematics 67,
  American Mathematical Society (2005), Chapter II, §3, for the signature, and Chapter V, §3, for
  the signed discriminant and the Clifford invariant.
* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 63:20 for the local
  classification and §66 for the local invariants of a global form.
-/

public section

open IsDedekindDomain NumberField TauCeti

universe u v w

namespace QuadraticForm

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- **Witt classes at a real place.** The localizations of two regular forms at a real place `w`
have the same Witt class exactly when their signatures `p_w - q_w` agree. -/
theorem wittClass_formClass_atRealPlace_eq_iff (Q : _root_.QuadraticForm K V)
    (hQ : Q.Nondegenerate) (R : _root_.QuadraticForm K W) (hR : R.Nondegenerate)
    (w : {w : InfinitePlace K // w.IsReal}) :
    wittClass (formClass (Q.atRealPlace w) (Nondegenerate.atRealPlace hQ w)) =
        wittClass (formClass (R.atRealPlace w) (Nondegenerate.atRealPlace hR w)) ↔
      (Q.realPositiveIndex w : ℤ) - Q.realNegativeIndex w =
        (R.realPositiveIndex w : ℤ) - R.realNegativeIndex w := by
  rw [wittClass_eq_iff_signature_eq, signature_formClass, signature_formClass,
    realPositiveIndex_eq_sigPos, realPositiveIndex_eq_sigPos, realNegativeIndex_eq_sigNeg,
    realNegativeIndex_eq_sigNeg]

variable [NumberField K]

/-- **Witt classes at a finite place.** The localizations of two regular forms `Q` and `R` at a
finite place `v` have the same Witt class exactly when the ranks of `Q` and `R` have the same
parity, the images in `K_vˣ/(K_vˣ)²` of their signed discriminants agree, and the images in the
Brauer group of `K_v` of their Clifford invariants agree. -/
theorem wittClass_formClass_atFinitePlace_eq_iff (Q : _root_.QuadraticForm K V)
    (hQ : Q.Nondegenerate) (R : _root_.QuadraticForm K W) (hR : R.Nondegenerate)
    (v : HeightOneSpectrum (𝓞 K)) :
    wittClass (formClass (Q.atFinitePlace v) (Nondegenerate.atFinitePlace hQ v)) =
        wittClass (formClass (R.atFinitePlace v) (Nondegenerate.atFinitePlace hR v)) ↔
      Module.finrank K V ≡ Module.finrank K W [MOD 2] ∧
      (algebraMap K (v.adicCompletion K)).squareClassMap
          (RegularFormClass.signedDiscr (formClass Q hQ)) =
        (algebraMap K (v.adicCompletion K)).squareClassMap
          (RegularFormClass.signedDiscr (formClass R hR)) ∧
      BrauerGroup.baseChange K (v.adicCompletion K)
          (RegularFormClass.cliffordInvariant (formClass Q hQ)) =
        BrauerGroup.baseChange K (v.adicCompletion K)
          (RegularFormClass.cliffordInvariant (formClass R hR)) := by
  rw [wittClass_eq_iff_rank_modEq_and_signedDiscr_eq_and_cliffordInvariant_eq,
    formClass_atFinitePlace Q hQ, formClass_atFinitePlace R hR]
  simp

/-- **Witt classes at every place.** The localizations of two regular forms over a number field
have the same Witt class at every finite and every real place exactly when their ranks have the
same parity, the images of their signed discriminants and of their Clifford invariants agree at
every finite place, and their signatures agree at every real place. -/
theorem locally_wittClass_formClass_eq_iff {Q : _root_.QuadraticForm K V}
    {R : _root_.QuadraticForm K W} (hQ : Q.Nondegenerate) (hR : R.Nondegenerate) :
    ((∀ v : HeightOneSpectrum (𝓞 K),
        wittClass (formClass (Q.atFinitePlace v) (Nondegenerate.atFinitePlace hQ v)) =
          wittClass (formClass (R.atFinitePlace v) (Nondegenerate.atFinitePlace hR v))) ∧
      ∀ w : {w : InfinitePlace K // w.IsReal},
        wittClass (formClass (Q.atRealPlace w) (Nondegenerate.atRealPlace hQ w)) =
          wittClass (formClass (R.atRealPlace w) (Nondegenerate.atRealPlace hR w))) ↔
      Module.finrank K V ≡ Module.finrank K W [MOD 2] ∧
      (∀ v : HeightOneSpectrum (𝓞 K), (algebraMap K (v.adicCompletion K)).squareClassMap
          (RegularFormClass.signedDiscr (formClass Q hQ)) =
        (algebraMap K (v.adicCompletion K)).squareClassMap
          (RegularFormClass.signedDiscr (formClass R hR))) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), BrauerGroup.baseChange K (v.adicCompletion K)
          (RegularFormClass.cliffordInvariant (formClass Q hQ)) =
        BrauerGroup.baseChange K (v.adicCompletion K)
          (RegularFormClass.cliffordInvariant (formClass R hR))) ∧
      ∀ w : {w : InfinitePlace K // w.IsReal},
        (Q.realPositiveIndex w : ℤ) - Q.realNegativeIndex w =
          (R.realPositiveIndex w : ℤ) - R.realNegativeIndex w := by
  simp only [wittClass_formClass_atFinitePlace_eq_iff Q hQ R hR,
    wittClass_formClass_atRealPlace_eq_iff Q hQ R hR, forall_and]
  -- A number field has a finite place, so the parity condition at every finite place is the
  -- parity condition itself.
  exact ⟨fun ⟨⟨hn, hd, hc⟩, hs⟩ => ⟨hn (Classical.arbitrary _), hd, hc, hs⟩,
    fun ⟨hn, hd, hc, hs⟩ => ⟨⟨fun _ => hn, hd, hc⟩, hs⟩⟩

end QuadraticForm
