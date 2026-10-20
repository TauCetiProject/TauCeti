/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsRealClosed.Real
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Signature
public import TauCeti.NumberTheory.QuadraticForm.Global.Classification

/-!
# Local hyperbolicity of quadratic forms over a number field

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
finite place `v`, and the positive index `m` at every real place. A form that is hyperbolic over
`K` is hyperbolic at every place, so these are also necessary conditions for hyperbolicity over
`K`. The converse, that a form hyperbolic at every finite and real place is hyperbolic over `K`,
is the Hasse–Minkowski theorem for isometry applied to `Q` and `m • ℍ`; this file does not use it.

## Main results

* `QuadraticForm.formClass_atFinitePlace_eq_nsmul_hyperbolicClass_iff`: hyperbolicity at a finite
  place by rank, discriminant and finite Hasse sign.
* `QuadraticForm.formClass_atRealPlace_eq_nsmul_hyperbolicClass_iff`: hyperbolicity at a real
  place by rank and positive index.
* `QuadraticForm.locally_formClass_eq_nsmul_hyperbolicClass_iff`: hyperbolicity at every finite
  and every real place by the local invariants.
* `QuadraticForm.formClass_atFinitePlace_eq_nsmul_hyperbolicClass`,
  `QuadraticForm.formClass_atRealPlace_eq_nsmul_hyperbolicClass`: a form hyperbolic over `K` is
  hyperbolic at every finite and every real place.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 63:20 and 66:4.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, AMS (2005), Chapter VI, §3.
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
  rw [RegularFormClass.eq_iff_rank_eq_and_signature_eq, rank_formClass, finrank_atRealPlace,
    signature_formClass, RegularFormClass.signature_nsmul,
    RegularFormClass.signature_hyperbolicClass, smul_zero, ← realPositiveIndex_eq_sigPos,
    ← realNegativeIndex_eq_sigNeg, RegularFormClass.rank_nsmul, rank_hyperbolicClass]
  omega

/-- A regular form that is the sum of `m` hyperbolic planes over `K` is the sum of `m` hyperbolic
planes at every real place. -/
theorem formClass_atRealPlace_eq_nsmul_hyperbolicClass [Invertible (2 : K)]
    {Q : _root_.QuadraticForm K V} {hQ : Q.Nondegenerate} {m : ℕ}
    (h : formClass Q hQ = m • hyperbolicClass K) (w : {w : InfinitePlace K // w.IsReal}) :
    formClass (Q.atRealPlace w) (Nondegenerate.atRealPlace hQ w) = m • hyperbolicClass ℝ := by
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  have hb := formClass_baseChange (L := ℝ) Q hQ
  rw [h, RegularFormClass.baseChange_nsmul, RegularFormClass.baseChange_hyperbolicClass] at hb
  -- `hb` is about the base change along the real embedding, which is the localization by
  -- `atRealPlace_def`. The localization, `hb` and the goal may carry different `Invertible 2`
  -- instances, equal because `Invertible 2` is a subsingleton.
  convert hb using 2
  · convert atRealPlace_def Q w
    exact Subsingleton.elim _ _
  · exact congrArg _ (Subsingleton.elim _ _)

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
  rw [RegularFormClass.eq_nsmul_hyperbolicClass_iff, rank_formClass, Module.finrank_baseChange,
    formClass_atFinitePlace, RegularFormClass.discr_baseChange, ← formClass_atFinitePlace,
    ← finiteHasse_def]

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
  rw [h, RegularFormClass.baseChange_nsmul, RegularFormClass.baseChange_hyperbolicClass] at hb
  -- `baseChange_hyperbolicClass` states its result with the `Invertible 2` instance transported
  -- from `K`, while the goal uses the canonical instance of `K_v`; the two are equal because
  -- `Invertible 2` is a subsingleton.
  exact hb.trans (by congr 2; exact Subsingleton.elim _ _)

end QuadraticForm
