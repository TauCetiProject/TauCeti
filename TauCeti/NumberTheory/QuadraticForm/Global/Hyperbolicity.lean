/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsRealClosed.Real
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Signature
public import TauCeti.NumberTheory.QuadraticForm.Global.Classification
import TauCeti.NumberTheory.QuadraticForm.Global.WittLocalization

/-!
# Hyperbolicity of quadratic forms over a number field

A regular quadratic form is hyperbolic when its isometry class is a sum `m • ℍ` of hyperbolic
planes. This file characterizes hyperbolicity of the localizations of a regular form `Q` over a
number field `K` by the invariants of `Q`.

* At a finite place `v`, the localization `Q_v` is `m • ℍ` exactly when `Q` has rank `2m`, the image
  of its discriminant in `K_vˣ/(K_vˣ)²` is `m · [-1]`, and its finite Hasse sign at `v` is
  `(-1, -1)_v^{m(m-1)/2}`, the Hasse sign of `m` hyperbolic planes. This is the local
  classification by rank, discriminant and Hasse invariant.
* At a real place `w`, the localization `Q_w` is `m • ℍ` exactly when `Q` has rank `2m` and
  positive index `m` at `w`. This is Sylvester's law of inertia.

Together, `Q` is hyperbolic at every finite and every real place exactly when it has rank `2m`,
the discriminant `m · [-1]` at every finite place, the Hasse sign `(-1, -1)_v^{m(m-1)/2}` at every
finite place `v`, and the positive index `m` at every real place.

A form that is hyperbolic over `K` is hyperbolic at every place. Conversely, a form that is
hyperbolic at every finite and every real place is hyperbolic over `K`: its Witt class vanishes at
every place, hence over `K` by the injectivity of the global-to-local map of Witt rings
(`TauCeti.WittRing.globalToLocal_injective`), and a regular form with trivial Witt class is a sum
of hyperbolic planes. So the conditions above also characterize hyperbolicity over `K`.

## Main results

* `QuadraticForm.formClass_atFinitePlace_eq_nsmul_hyperbolicClass_iff`: hyperbolicity at a finite
  place by rank, discriminant and finite Hasse sign.
* `QuadraticForm.formClass_atRealPlace_eq_nsmul_hyperbolicClass_iff`: hyperbolicity at a real
  place by rank and positive index.
* `QuadraticForm.locally_formClass_eq_nsmul_hyperbolicClass_iff`: hyperbolicity at every finite
  and every real place by the local invariants.
* `QuadraticForm.formClass_eq_nsmul_hyperbolicClass_iff_locally`: a regular form is hyperbolic
  over `K` exactly when it is hyperbolic at every finite and every real place.
* `QuadraticForm.formClass_atFinitePlace_eq_nsmul_hyperbolicClass`,
  `QuadraticForm.formClass_atRealPlace_eq_nsmul_hyperbolicClass`: a form hyperbolic over `K` is
  hyperbolic at every finite and every real place.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 63:20 and 66:4.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, AMS (2005), Chapter VI, §3.
* J. S. Milne, *Class Field Theory*, v4.03, Chapter VIII, Theorem 6.3, p. 252.
-/

public section

open IsDedekindDomain NumberField NumberField.InfinitePlace TauCeti

universe u v

namespace QuadraticForm

section RealPlace

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **Hyperbolicity at a real place.** The localization of a regular form `Q` at a real place `w`
is the sum of `m` hyperbolic planes exactly when `Q` has rank `2m` and positive index `m` at `w`. -/
theorem formClass_atRealPlace_eq_nsmul_hyperbolicClass_iff {Q : _root_.QuadraticForm K V}
    (hQ : Q.Nondegenerate) (w : {w : InfinitePlace K // w.IsReal}) (m : ℕ) :
    formClass (Q.atRealPlace w) (Nondegenerate.atRealPlace hQ w) = m • hyperbolicClass ℝ ↔
      Module.finrank K V = 2 * m ∧ Q.realPositiveIndex w = m := by
  have hpq := realPositiveIndex_add_realNegativeIndex_eq_finrank hQ w
  simp only [RegularFormClass.eq_iff_rank_eq_and_signature_eq, rank_formClass,
    finrank_atRealPlace, signature_formClass, RegularFormClass.signature_nsmul,
    RegularFormClass.signature_hyperbolicClass, smul_zero, RegularFormClass.rank_nsmul,
    rank_hyperbolicClass, realPositiveIndex_eq_sigPos, realNegativeIndex_eq_sigNeg] at hpq ⊢
  omega

/-- A regular form that is the sum of `m` hyperbolic planes over `K` is the sum of `m` hyperbolic
planes at every real place. -/
theorem formClass_atRealPlace_eq_nsmul_hyperbolicClass [Invertible (2 : K)]
    {Q : _root_.QuadraticForm K V} {hQ : Q.Nondegenerate} {m : ℕ}
    (h : formClass Q hQ = m • hyperbolicClass K) (w : {w : InfinitePlace K // w.IsReal}) :
    formClass (Q.atRealPlace w) (Nondegenerate.atRealPlace hQ w) = m • hyperbolicClass ℝ := by
  let : Algebra K ℝ := (embedding_of_isReal w.property).toAlgebra
  have hb := formClass_atRealPlace Q hQ w
  rwa [h, RegularFormClass.baseChange_nsmul, RegularFormClass.baseChange_hyperbolicClass] at hb

end RealPlace

variable {K : Type u} [Field K] [NumberField K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **Hyperbolicity at a finite place.** The localization of a regular form `Q` at a finite place
`v` is the sum of `m` hyperbolic planes exactly when `Q` has rank `2m`, the image of its
discriminant in `K_vˣ/(K_vˣ)²` is `m · [-1]`, and its finite Hasse sign at `v` is
`(-1, -1)_v^{m(m-1)/2}`. -/
theorem formClass_atFinitePlace_eq_nsmul_hyperbolicClass_iff (Q : _root_.QuadraticForm K V)
    (hQ : Q.Nondegenerate) (v : HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    formClass (Q.atFinitePlace v) (Nondegenerate.atFinitePlace hQ v) =
        m • hyperbolicClass (v.adicCompletion K) ↔
      Module.finrank K V = 2 * m ∧
      (algebraMap K (v.adicCompletion K)).squareClassMap
          (RegularFormClass.discr (formClass Q hQ)) =
        m • squareClass (-1 : (v.adicCompletion K)ˣ) ∧
      Q.finiteHasse hQ v = hilbertSymbol (-1 : (v.adicCompletion K)ˣ) (-1) ^ m.choose 2 := by
  have hd : RegularFormClass.discr (formClass (Q.atFinitePlace v)
      (Nondegenerate.atFinitePlace hQ v)) = (algebraMap K (v.adicCompletion K)).squareClassMap
        (RegularFormClass.discr (formClass Q hQ)) := by
    rw [formClass_atFinitePlace, RegularFormClass.discr_baseChange]
  rw [RegularFormClass.eq_nsmul_hyperbolicClass_iff, rank_formClass, Module.finrank_baseChange,
    hd, ← finiteHasse_def]

/-- **Local hyperbolicity by invariants.** A regular form `Q` is the sum of `m` hyperbolic planes
at every finite and every real place exactly when it has rank `2m`, the image of its discriminant
at every finite place is `m · [-1]`, its finite Hasse sign at every finite place `v` is
`(-1, -1)_v^{m(m-1)/2}`, and its positive index at every real place is `m`. -/
theorem locally_formClass_eq_nsmul_hyperbolicClass_iff (Q : _root_.QuadraticForm K V)
    (hQ : Q.Nondegenerate) (m : ℕ) :
    ((∀ v : HeightOneSpectrum (𝓞 K), formClass (Q.atFinitePlace v)
        (Nondegenerate.atFinitePlace hQ v) = m • hyperbolicClass (v.adicCompletion K)) ∧
      ∀ w : {w : InfinitePlace K // w.IsReal},
        formClass (Q.atRealPlace w) (Nondegenerate.atRealPlace hQ w) = m • hyperbolicClass ℝ) ↔
      Module.finrank K V = 2 * m ∧
      (∀ v : HeightOneSpectrum (𝓞 K), (algebraMap K (v.adicCompletion K)).squareClassMap
          (RegularFormClass.discr (formClass Q hQ)) =
        m • squareClass (-1 : (v.adicCompletion K)ˣ)) ∧
      (∀ v : HeightOneSpectrum (𝓞 K),
        Q.finiteHasse hQ v = hilbertSymbol (-1 : (v.adicCompletion K)ˣ) (-1) ^ m.choose 2) ∧
      ∀ w : {w : InfinitePlace K // w.IsReal}, Q.realPositiveIndex w = m := by
  refine ⟨fun ⟨hv, hw⟩ => ?_, fun ⟨hr, hd, hs, hp⟩ =>
    ⟨fun v => (Q.formClass_atFinitePlace_eq_nsmul_hyperbolicClass_iff hQ v m).mpr ⟨hr, hd v, hs v⟩,
      fun w => (formClass_atRealPlace_eq_nsmul_hyperbolicClass_iff hQ w m).mpr ⟨hr, hp w⟩⟩⟩
  have hv' v := (Q.formClass_atFinitePlace_eq_nsmul_hyperbolicClass_iff hQ v m).mp (hv v)
  obtain ⟨v⟩ := (inferInstance : Nonempty (HeightOneSpectrum (𝓞 K)))
  exact ⟨(hv' v).1, fun v => (hv' v).2.1, fun v => (hv' v).2.2,
    fun w => ((formClass_atRealPlace_eq_nsmul_hyperbolicClass_iff hQ w m).mp (hw w)).2⟩

/-- A regular form that is the sum of `m` hyperbolic planes over `K` is the sum of `m` hyperbolic
planes at every finite place. -/
theorem formClass_atFinitePlace_eq_nsmul_hyperbolicClass {Q : _root_.QuadraticForm K V}
    {hQ : Q.Nondegenerate} {m : ℕ} (h : formClass Q hQ = m • hyperbolicClass K)
    (v : HeightOneSpectrum (𝓞 K)) :
    formClass (Q.atFinitePlace v) (Nondegenerate.atFinitePlace hQ v) =
      m • hyperbolicClass (v.adicCompletion K) := by
  have hb := formClass_atFinitePlace Q hQ v
  rwa [h, RegularFormClass.baseChange_nsmul, RegularFormClass.baseChange_hyperbolicClass] at hb

/-- **Global hyperbolicity** (the Hasse–Minkowski theorem for hyperbolic forms). A regular form
over a number field is the sum of `m` hyperbolic planes exactly when it is the sum of `m`
hyperbolic planes at every finite and every real place. -/
theorem formClass_eq_nsmul_hyperbolicClass_iff_locally (Q : _root_.QuadraticForm K V)
    (hQ : Q.Nondegenerate) (m : ℕ) :
    formClass Q hQ = m • hyperbolicClass K ↔
      (∀ v : HeightOneSpectrum (𝓞 K), formClass (Q.atFinitePlace v)
          (Nondegenerate.atFinitePlace hQ v) = m • hyperbolicClass (v.adicCompletion K)) ∧
        ∀ w : {w : InfinitePlace K // w.IsReal},
          formClass (Q.atRealPlace w) (Nondegenerate.atRealPlace hQ w) = m • hyperbolicClass ℝ := by
  refine ⟨fun h => ⟨formClass_atFinitePlace_eq_nsmul_hyperbolicClass h,
    formClass_atRealPlace_eq_nsmul_hyperbolicClass h⟩, fun hloc => ?_⟩
  have hr := ((locally_formClass_eq_nsmul_hyperbolicClass_iff Q hQ m).mp hloc).1
  -- The Witt class of `Q` vanishes at every finite and every real place, hence over `K`.
  have hW : wittClass (formClass Q hQ) = 0 := by
    refine WittRing.globalToLocal_injective ?_
    rw [map_zero, WittRing.globalToLocal_wittClass_formClass]
    refine Prod.ext (funext fun v => ?_) (funext fun w => ?_) <;>
      simp only [hloc.1, hloc.2, map_nsmul, wittClass_hyperbolicClass, smul_zero,
        Prod.fst_zero, Prod.snd_zero, Pi.zero_apply]
  -- So `Q` is a sum of hyperbolic planes, and comparing ranks gives their number.
  obtain ⟨k, hk⟩ : ∃ k : ℕ, formClass Q hQ = k • hyperbolicClass K :=
    ⟨_, by simpa [wittClass_eq_zero_iff.mp hW] using
      RegularFormClass.wittDecomposition (formClass Q hQ)⟩
  have hrk := congrArg RegularFormClass.rank hk
  rw [rank_formClass, rank_nsmul_hyperbolicClass, hr] at hrk
  rw [hk, show k = m by omega]

end QuadraticForm
