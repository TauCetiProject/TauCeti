/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Witt.BaseChange
public import TauCeti.NumberTheory.QuadraticForm.Global.LocalWittClass
import TauCeti.LinearAlgebra.QuadraticForm.Witt.SepClosed

/-!
# The global-to-local map of Witt rings of a number field

Let `K` be a number field. Scalar extension along the canonical map `K → K_v` at each finite place
`v`, and along the real embedding at each real place `w`, induces ring homomorphisms
`W(K) → W(K_v)` and `W(K) → W(ℝ)` of Witt rings. Together they form the global-to-local map

```text
W(K) → ∏_v W(K_v) × ∏_w W(ℝ).
```

On the Witt class of a regular form `Q` its components are the Witt classes of the localizations
`Q_v` and `Q_w`.

The kernel of this map is described by invariants of the global Witt class. Over a
nonarchimedean local field a Witt class vanishes exactly when its dimension is even and its
signed discriminant and Clifford invariant are trivial, and the signature `W(ℝ) → ℤ` is an
isomorphism. All three local invariants are the images of the global ones. So `x ∈ W(K)` maps to
zero exactly when `x` has even dimension, its signed discriminant `d±(x) ∈ Kˣ/(Kˣ)²` becomes a
square in every `K_v`, its Clifford invariant `c(x) ∈ Br(K)` splits over every `K_v`, and its
signature vanishes at every real place.

Complex places are omitted: the Witt ring of `ℂ` is `ZMod 2`, detected by the dimension modulo
two, which the finite places already see. Scalar extension along the complex embedding of an
infinite place is defined as well, and two classes with the same image under the global-to-local
map have the same image at every complex embedding, so adding complex coordinates would not change
the kernel.

That the global-to-local map is injective is the Hasse–Minkowski theorem for Witt classes; this
file does not prove it.

## Main definitions

* `TauCeti.WittRing.atRealPlace`: scalar extension of Witt classes along a real embedding.
* `TauCeti.WittRing.atComplexEmbedding`: scalar extension of Witt classes along the complex
  embedding of an infinite place.
* `TauCeti.WittRing.globalToLocal`: the global-to-local map of Witt rings.

## Main results

* `TauCeti.WittRing.globalToLocal_wittClass_formClass`: on the Witt class of a regular form, the
  global-to-local map gives the Witt classes of its localizations.
* `TauCeti.WittRing.globalToLocal_eq_zero_iff`: the kernel of the global-to-local map, described
  by the dimension modulo two, the signed discriminant, the Clifford invariant and the real
  signatures.
* `TauCeti.WittRing.signature_atRealPlace_wittClass_formClass`: the signature of the real
  coordinate of the Witt class of a regular form is the difference of its two inertia indices.
* `TauCeti.WittRing.atComplexEmbedding_eq_of_globalToLocal_eq`: classes with the same image under
  the global-to-local map agree at every complex embedding.
* `QuadraticForm.globalToLocal_wittClass_formClass_eq_iff`: two regular forms have the same image
  under the global-to-local map exactly when their ranks have the same parity, their signed
  discriminants and Clifford invariants agree at every finite place and their signatures agree at
  every real place.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Graduate Studies in Mathematics 67,
  American Mathematical Society (2005), Chapter II, §§1–3, for scalar extension of Witt classes
  and the real and complex Witt rings, Chapter VI, §3, for the map `W(K) → ∏_v W(K_v)`, and
  Chapter V, §3, for the signed discriminant and the Clifford invariant.
* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 63:20 for the local
  classification.
-/

public section

open IsDedekindDomain NumberField

universe u v w

namespace TauCeti

namespace WittRing

variable {K : Type u} [Field K]

section InfinitePlace

variable [Invertible (2 : K)]

/-- **Localization of Witt classes at a real place**: scalar extension `W(K) → W(ℝ)` along the
real embedding of the real place `w`. -/
noncomputable def atRealPlace (w : {w : InfinitePlace K // w.IsReal}) :
    WittRing K →+* WittRing ℝ :=
  letI : Algebra K ℝ := (InfinitePlace.embedding_of_isReal w.2).toAlgebra
  baseChange

/-- Localization of Witt classes at a real place is scalar extension along the real embedding of
the place. -/
theorem atRealPlace_def (w : {w : InfinitePlace K // w.IsReal}) :
    letI : Algebra K ℝ := (InfinitePlace.embedding_of_isReal w.2).toAlgebra
    atRealPlace w = baseChange :=
  (rfl)

/-- The localization at a real place of the Witt class of a regular form is the Witt class of the
form's localization at that place. -/
@[simp]
theorem atRealPlace_wittClass_formClass {V : Type v} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (w : {w : InfinitePlace K // w.IsReal}) :
    atRealPlace w (wittClass (formClass Q hQ)) =
      wittClass (formClass (Q.atRealPlace w) (QuadraticForm.Nondegenerate.atRealPlace hQ w)) := by
  let : Algebra K ℝ := (InfinitePlace.embedding_of_isReal w.2).toAlgebra
  rw [QuadraticForm.formClass_atRealPlace Q hQ w, ← baseChange_wittClass, atRealPlace_def]

/-- The signature of the localization at a real place of the Witt class of a regular form is the
difference of the positive and negative indices of the form at that place. -/
theorem signature_atRealPlace_wittClass_formClass {V : Type v} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (w : {w : InfinitePlace K // w.IsReal}) :
    signature (atRealPlace w (wittClass (formClass Q hQ))) =
      (Q.realPositiveIndex w : ℤ) - Q.realNegativeIndex w := by
  rw [atRealPlace_wittClass_formClass, signature_wittClass, signature_formClass,
    QuadraticForm.realPositiveIndex_eq_sigPos, QuadraticForm.realNegativeIndex_eq_sigNeg]

/-- **Localization of Witt classes at a complex embedding**: scalar extension `W(K) → W(ℂ)` along
the complex embedding of the infinite place `w`. -/
noncomputable def atComplexEmbedding (w : InfinitePlace K) : WittRing K →+* WittRing ℂ :=
  letI : Algebra K ℂ := w.embedding.toAlgebra
  baseChange

/-- Localization of Witt classes at a complex embedding is scalar extension along the complex
embedding of the place. -/
theorem atComplexEmbedding_def (w : InfinitePlace K) :
    letI : Algebra K ℂ := w.embedding.toAlgebra
    atComplexEmbedding w = baseChange :=
  (rfl)

/-- The localization at a complex embedding of the Witt class of a regular form is the Witt class
of the form's scalar extension along that embedding. -/
@[simp]
theorem atComplexEmbedding_wittClass_formClass {V : Type v} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (w : InfinitePlace K) :
    atComplexEmbedding w (wittClass (formClass Q hQ)) =
      wittClass (formClass (Q.atComplexEmbedding w)
        (QuadraticForm.Nondegenerate.atComplexEmbedding hQ w)) := by
  let : Algebra K ℂ := w.embedding.toAlgebra
  rw [QuadraticForm.formClass_atComplexEmbedding Q hQ w, ← baseChange_wittClass,
    atComplexEmbedding_def]

/-- A Witt class vanishes at a complex embedding exactly when it has even dimension. -/
@[simp]
theorem atComplexEmbedding_eq_zero_iff (x : WittRing K) (w : InfinitePlace K) :
    atComplexEmbedding w x = 0 ↔ dimMod2 x = 0 := by
  let : Algebra K ℂ := w.embedding.toAlgebra
  simpa only [atComplexEmbedding_def] using baseChange_eq_zero_iff_dimMod2_eq_zero (L := ℂ) x

end InfinitePlace

variable [NumberField K]

variable (K) in
/-- **The global-to-local map of Witt rings** `W(K) → ∏_v W(K_v) × ∏_w W(ℝ)` of a number field
`K`, with one component for each finite place `v` and one for each real place `w`, each given by
scalar extension. -/
noncomputable def globalToLocal :
    WittRing K →+* (∀ v : HeightOneSpectrum (𝓞 K), WittRing (v.adicCompletion K)) ×
      ({w : InfinitePlace K // w.IsReal} → WittRing ℝ) :=
  (RingHom.pi fun _ => baseChange).prod (RingHom.pi atRealPlace)

/-- The finite-place components of the global-to-local map are scalar extensions to the
completions. -/
@[simp]
theorem globalToLocal_apply_fst (x : WittRing K) (v : HeightOneSpectrum (𝓞 K)) :
    (globalToLocal K x).1 v = baseChange x :=
  (rfl)

/-- The real-place components of the global-to-local map are the localizations at the real
places. -/
@[simp]
theorem globalToLocal_apply_snd (x : WittRing K) (w : {w : InfinitePlace K // w.IsReal}) :
    (globalToLocal K x).2 w = atRealPlace w x :=
  (rfl)

/-- On the Witt class of a regular form `Q`, the global-to-local map gives the Witt classes of the
localizations `Q_v` at the finite places and `Q_w` at the real places. -/
theorem globalToLocal_wittClass_formClass {V : Type v} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    globalToLocal K (wittClass (formClass Q hQ)) =
      (fun v => wittClass
          (formClass (Q.atFinitePlace v) (QuadraticForm.Nondegenerate.atFinitePlace hQ v)),
        fun w => wittClass
          (formClass (Q.atRealPlace w) (QuadraticForm.Nondegenerate.atRealPlace hQ w))) := by
  ext v <;> dsimp only
  · rw [globalToLocal_apply_fst, baseChange_wittClass, QuadraticForm.formClass_atFinitePlace]
  · rw [globalToLocal_apply_snd, atRealPlace_wittClass_formClass]

/-- **The kernel of the global-to-local map.** A Witt class of a number field `K` vanishes at
every finite and every real place exactly when it has even dimension, its signed discriminant
becomes a square in every completion `K_v`, its Clifford invariant splits over every `K_v`, and
its signature vanishes at every real place. -/
theorem globalToLocal_eq_zero_iff (x : WittRing K) :
    globalToLocal K x = 0 ↔ dimMod2 x = 0 ∧
      (∀ v : HeightOneSpectrum (𝓞 K),
        (algebraMap K (v.adicCompletion K)).squareClassMap (signedDiscr x) = 0) ∧
      (∀ v : HeightOneSpectrum (𝓞 K),
        BrauerGroup.baseChange K (v.adicCompletion K) (cliffordInvariant x) = 1) ∧
      ∀ w : {w : InfinitePlace K // w.IsReal}, signature (atRealPlace w x) = 0 := by
  simp only [Prod.ext_iff, funext_iff, globalToLocal_apply_fst, globalToLocal_apply_snd,
    Prod.fst_zero, Prod.snd_zero, Pi.zero_apply,
    eq_zero_iff_dimMod2_eq_zero_and_signedDiscr_eq_zero_and_cliffordInvariant_eq_one,
    dimMod2_baseChange, signedDiscr_baseChange, cliffordInvariant_baseChange, forall_and,
    ← equivInt_apply, EmbeddingLike.map_eq_zero_iff]
  -- A number field has a finite place, so even dimension at every finite place is even dimension.
  exact ⟨fun ⟨⟨hn, hd, hc⟩, hs⟩ => ⟨hn (Classical.arbitrary _), hd, hc, hs⟩,
    fun ⟨hn, hd, hc, hs⟩ => ⟨⟨fun _ => hn, hd, hc⟩, hs⟩⟩

/-- Two Witt classes with the same image under the global-to-local map have the same image at
every complex embedding. -/
theorem atComplexEmbedding_eq_of_globalToLocal_eq {x y : WittRing K}
    (h : globalToLocal K x = globalToLocal K y) (w : InfinitePlace K) :
    atComplexEmbedding w x = atComplexEmbedding w y := by
  let : Algebra K ℂ := w.embedding.toAlgebra
  have hv := congrArg (fun z => z.1 (Classical.arbitrary (HeightOneSpectrum (𝓞 K)))) h
  simp only [globalToLocal_apply_fst] at hv
  simpa only [atComplexEmbedding_def] using
    baseChange_eq_of_baseChange_eq_of_isSepClosed (M := ℂ) hv

end WittRing

end TauCeti

namespace QuadraticForm

open TauCeti

variable {K : Type u} [Field K] [NumberField K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- **Equal images under the global-to-local map.** Two regular forms over a number field have
Witt classes with the same image in `∏_v W(K_v) × ∏_w W(ℝ)` exactly when their ranks have the same
parity, the images of their signed discriminants and of their Clifford invariants agree at every
finite place, and their signatures agree at every real place. -/
theorem globalToLocal_wittClass_formClass_eq_iff {Q : _root_.QuadraticForm K V}
    {R : _root_.QuadraticForm K W} (hQ : Q.Nondegenerate) (hR : R.Nondegenerate) :
    WittRing.globalToLocal K (wittClass (formClass Q hQ)) =
        WittRing.globalToLocal K (wittClass (formClass R hR)) ↔
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
  rw [WittRing.globalToLocal_wittClass_formClass, WittRing.globalToLocal_wittClass_formClass,
    Prod.ext_iff, funext_iff, funext_iff]
  exact locally_wittClass_formClass_eq_iff hQ hR

end QuadraticForm
