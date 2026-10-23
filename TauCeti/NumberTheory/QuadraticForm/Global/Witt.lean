/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Witt.BaseChange
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Signature
public import TauCeti.NumberTheory.QuadraticForm.Global.Signature
import TauCeti.LinearAlgebra.QuadraticForm.Witt.SepClosed
import TauCeti.NumberTheory.NumberField.FinitePlace

/-!
# Localization of global Witt classes

Scalar extension gives a ring homomorphism from the Witt ring of a number field to the product
of its Witt rings at all finite and real places. Its coordinates on the class of a regular form
are the Witt classes of the actual localizations of that form. The real coordinates recover the
integer signatures.

Complex coordinates impose no additional condition on the kernel. A class vanishing at one
finite place has even dimension modulo two. Its scalar extension to `ℂ` therefore vanishes,
since dimension modulo two classifies complex Witt classes. This also applies to differences of
classes, so equality at finite and real places already entails equality at complex places.

The maps use `WittRing.baseChange`, and the complex calculation uses
`WittRing.eq_zero_of_dimMod2_eq_zero_of_isSepClosed`. No local-global injectivity theorem is
needed for these constructions.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter II, §§1–3, for scalar
  extension of Witt classes and the real and complex Witt rings.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §66, for localization over number fields.
-/

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace

namespace TauCeti.NumberField.QuadraticForm

variable (K : Type*) [Field K] [NumberField K]

/-- Finite completions have characteristic zero through the canonical algebra map. -/
local instance (v : HeightOneSpectrum (𝓞 K)) : CharZero (v.adicCompletion K) :=
  charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective

/-- Scalar extension of Witt classes to a finite completion. -/
def wittAtFinitePlace (v : HeightOneSpectrum (𝓞 K)) :
    WittRing K →+* WittRing (v.adicCompletion K) :=
  WittRing.baseChange

/-- Scalar extension of Witt classes along a real place. -/
def wittAtRealPlace (w : {w : InfinitePlace K // w.IsReal}) : WittRing K →+* WittRing ℝ :=
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  WittRing.baseChange

/-- Scalar extension of Witt classes along the complex embedding representing a place. -/
def wittAtComplexEmbedding (w : InfinitePlace K) : WittRing K →+* WittRing ℂ :=
  let : Algebra K ℂ := w.embedding.toAlgebra
  WittRing.baseChange

/-- Finite Witt localization is the canonical scalar-extension homomorphism. -/
theorem wittAtFinitePlace_def (v : HeightOneSpectrum (𝓞 K)) :
    wittAtFinitePlace K v = WittRing.baseChange (K := K) (L := v.adicCompletion K) :=
  (rfl)

/-- Real Witt localization uses the algebra structure of the chosen real embedding. -/
theorem wittAtRealPlace_def (w : {w : InfinitePlace K // w.IsReal}) :
    letI : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
    wittAtRealPlace K w = WittRing.baseChange (K := K) (L := ℝ) :=
  (rfl)

/-- Complex Witt localization uses the algebra structure of the chosen complex embedding. -/
theorem wittAtComplexEmbedding_def (w : InfinitePlace K) :
    letI : Algebra K ℂ := w.embedding.toAlgebra
    wittAtComplexEmbedding K w = WittRing.baseChange (K := K) (L := ℂ) :=
  (rfl)

/-- The global-to-local Witt homomorphism, with all finite and real coordinates. -/
def globalToLocalWitt : WittRing K →+*
    (∀ v : HeightOneSpectrum (𝓞 K), WittRing (v.adicCompletion K)) ×
      ({w : InfinitePlace K // w.IsReal} → WittRing ℝ) :=
  (RingHom.pi (wittAtFinitePlace K)).prod (RingHom.pi (wittAtRealPlace K))

variable {K}

/-- The finite coordinate of the global-to-local map is scalar extension to that completion. -/
@[simp]
theorem globalToLocalWitt_finite (x : WittRing K) (v : HeightOneSpectrum (𝓞 K)) :
    (globalToLocalWitt K x).1 v = wittAtFinitePlace K v x :=
  (rfl)

/-- The real coordinate of the global-to-local map is scalar extension along that real place. -/
@[simp]
theorem globalToLocalWitt_real (x : WittRing K) (w : {w : InfinitePlace K // w.IsReal}) :
    (globalToLocalWitt K x).2 w = wittAtRealPlace K w x :=
  (rfl)

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Finite localization of a Witt class agrees with localization of its regular form. -/
@[simp]
theorem wittAtFinitePlace_wittClass_formClass (Q : _root_.QuadraticForm K V)
    (hQ : Q.Nondegenerate) (v : HeightOneSpectrum (𝓞 K)) :
    wittAtFinitePlace K v (wittClass (formClass Q hQ)) =
      wittClass (formClass (Q.atFinitePlace v)
        (_root_.QuadraticForm.Nondegenerate.atFinitePlace hQ v)) := by
  rw [wittAtFinitePlace_def, WittRing.baseChange_wittClass,
    ← _root_.QuadraticForm.formClass_baseChange Q hQ]
  congr 1
  simp only [_root_.QuadraticForm.atFinitePlace_def]

/-- Real localization of a Witt class agrees with localization of its regular form. -/
@[simp]
theorem wittAtRealPlace_wittClass_formClass (Q : _root_.QuadraticForm K V)
    (hQ : Q.Nondegenerate) (w : {w : InfinitePlace K // w.IsReal}) :
    wittAtRealPlace K w (wittClass (formClass Q hQ)) =
      wittClass (formClass (Q.atRealPlace w)
        (_root_.QuadraticForm.Nondegenerate.atRealPlace hQ w)) := by
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  rw [wittAtRealPlace_def, WittRing.baseChange_wittClass,
    ← _root_.QuadraticForm.formClass_baseChange Q hQ]
  congr 1
  simp only [_root_.QuadraticForm.atRealPlace_def]

/-- Complex localization of a Witt class agrees with scalar extension of its regular form. -/
@[simp]
theorem wittAtComplexEmbedding_wittClass_formClass (Q : _root_.QuadraticForm K V)
    (hQ : Q.Nondegenerate) (w : InfinitePlace K) :
    wittAtComplexEmbedding K w (wittClass (formClass Q hQ)) =
      wittClass (formClass (Q.atComplexEmbedding w)
        (_root_.QuadraticForm.Nondegenerate.atComplexEmbedding hQ w)) := by
  let : Algebra K ℂ := w.embedding.toAlgebra
  rw [wittAtComplexEmbedding_def, WittRing.baseChange_wittClass,
    ← _root_.QuadraticForm.formClass_baseChange Q hQ]
  congr 1
  simp only [_root_.QuadraticForm.atComplexEmbedding_def]

/-- The signature of a real Witt coordinate is the difference of the two local inertia indices. -/
theorem signature_wittAtRealPlace_wittClass_formClass (Q : _root_.QuadraticForm K V)
    (hQ : Q.Nondegenerate) (w : {w : InfinitePlace K // w.IsReal}) :
    WittRing.signature (wittAtRealPlace K w (wittClass (formClass Q hQ))) =
      (Q.realPositiveIndex w : ℤ) - Q.realNegativeIndex w := by
  rw [wittAtRealPlace_wittClass_formClass, WittRing.signature_wittClass, signature_formClass,
    _root_.QuadraticForm.realPositiveIndex_eq_sigPos,
    _root_.QuadraticForm.realNegativeIndex_eq_sigNeg]

/-- A class lies in the kernel exactly when its finite and real scalar extensions all vanish. -/
@[simp]
theorem globalToLocalWitt_eq_zero_iff (x : WittRing K) :
    globalToLocalWitt K x = 0 ↔
      (∀ v, wittAtFinitePlace K v x = 0) ∧ ∀ w, wittAtRealPlace K w x = 0 := by
  simp only [Prod.ext_iff, funext_iff, globalToLocalWitt_finite, globalToLocalWitt_real,
    Prod.fst_zero, Prod.snd_zero, Pi.zero_apply]

/-- Complex localization vanishes exactly when the global Witt class has even dimension. -/
@[simp]
theorem wittAtComplexEmbedding_eq_zero_iff (x : WittRing K) (w : InfinitePlace K) :
    wittAtComplexEmbedding K w x = 0 ↔ WittRing.dimMod2 x = 0 := by
  let : Algebra K ℂ := w.embedding.toAlgebra
  constructor
  · intro h
    simpa only [wittAtComplexEmbedding_def, WittRing.dimMod2_baseChange, map_zero] using
      congrArg WittRing.dimMod2 h
  · intro h
    apply WittRing.eq_zero_of_dimMod2_eq_zero_of_isSepClosed
    simpa only [wittAtComplexEmbedding_def, WittRing.dimMod2_baseChange] using h

/-- Vanishing at the finite coordinates forces even dimension, including for virtual classes. -/
theorem dimMod2_eq_zero_of_globalToLocalWitt_eq_zero {x : WittRing K}
    (h : globalToLocalWitt K x = 0) : WittRing.dimMod2 x = 0 := by
  obtain ⟨v⟩ := (inferInstance : Nonempty (HeightOneSpectrum (𝓞 K)))
  have hv := (globalToLocalWitt_eq_zero_iff x).mp h |>.1 v
  simpa only [wittAtFinitePlace_def, WittRing.dimMod2_baseChange, map_zero] using
    congrArg WittRing.dimMod2 hv

/-- Equal finite and real Witt coordinates entail equal coordinates at every complex embedding. -/
theorem wittAtComplexEmbedding_eq_of_globalToLocalWitt_eq {x y : WittRing K}
    (h : globalToLocalWitt K x = globalToLocalWitt K y) (w : InfinitePlace K) :
    wittAtComplexEmbedding K w x = wittAtComplexEmbedding K w y := by
  have hsub : globalToLocalWitt K (x - y) = 0 := by simp [h]
  have hdim := dimMod2_eq_zero_of_globalToLocalWitt_eq_zero hsub
  have hc := (wittAtComplexEmbedding_eq_zero_iff (x - y) w).mpr hdim
  simpa only [map_sub, sub_eq_zero] using hc

end TauCeti.NumberField.QuadraticForm
