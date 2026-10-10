/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import TauCeti.Analysis.InnerProductSpace.Complexification.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique

/-!
# Real descent for bounded functional calculus

This module exposes the canonical conjugation action on operators over a real
Hilbert-space complexification.  A conjugation-fixed complex operator descends
to a bounded real operator, and real continuous functional calculus preserves
the fixed-point subalgebra.  These are the reusable seams needed for real
infinite-dimensional polar factorization.

## Main definitions and results

* `TauCeti.RealComplexification.canonicalConjugation`: the canonical conjugation of a real
  complexification, an antilinear isometric involution;
* `TauCeti.RealComplexification.conjugateOperator`: the induced involution on bounded complex
  operators, together with its ring, norm and adjoint laws;
* `TauCeti.RealComplexification.conjugateOperator_cfc_eq`: continuous functional calculus
  commutes with the conjugation, so the fixed-point subalgebra is preserved;
  `conjugateOperator_cfc` is the same statement with the continuity side condition removed;
* `TauCeti.RealComplexification.fixed_operator_maps_real_to_real`: a conjugation-fixed operator
  descends to the real subspace;
* `TauCeti.RealComplexification.complexify_adjoint` and `complexify_gram`: complexification
  intertwines adjoints and Gram operators.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `DavisKahan/SpectralTheory/Complexification/FunctionalCalculus.lean`.
* Extraction class: **moved**, not restated.  Its only non-Mathlib import is
  `Complexification/Basic.lean`, which is already in `ForTauCeti`, so it depended on nothing
  in the paper library.
* The enclosing namespace was `TauCeti.DavisKahan.Experimental.ExactSinTheta.`
  `RealComplexificationFunctionalCalculus`: two paper names, a staging word, and a repetition
  of the parent.  It is now simply `TauCeti.RealComplexification`, the namespace of the
  `complexify` it is about — which is where `complexify_adjoint` and `complexify_gram` belonged
  all along.  The `scoped instance` moved with it, so consumers now write
  `open scoped TauCeti.RealComplexification`.
* Original authors / copyright: Jon Crall, OpenAI GPT-5.6 Thinking; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none**.
-/

public section

open scoped InnerProductSpace ComplexConjugate Topology

namespace TauCeti
namespace RealComplexification

open Module (finrank)
open Filter

noncomputable section

universe v vF w

variable {E : Type v} {F : Type vF}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Scalar restriction of the complex operator algebra to the reals.

**`scoped`, deliberately, and not `local` or global.**  Global is the ℝ-algebra diamond that
Mathlib declines to install for `Algebra.complexToReal`, so that door stays shut.  `local` was
what this was until 2026-07-30, and it forced three other modules to reinstall a *second*
declaration of the same instance; lemmas stated against one copy then had to be proved defeq
against the other, which is what timed out `isDefEq` when `Threshold.lean` first tried to import
this module's lemmas.  A scope gives every consumer the *same* declaration, so there is nothing
to prove.  Open it with `open scoped RealComplexification`. -/
noncomputable scoped instance complexOperatorRealAlgebra :
    Algebra ℝ (RealComplexification E →L[ℂ] RealComplexification E) :=
  Algebra.complexToReal

/-- Real continuous functional calculus on the complexified operator algebra.  `scoped` for the
same reason as `complexOperatorRealAlgebra` above. -/
noncomputable scoped instance realContinuousFunctionalCalculus :
    ContinuousFunctionalCalculus ℝ
      (RealComplexification E →L[ℂ] RealComplexification E) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

omit [CompleteSpace E] in
/-- The real scalar action inherited from the complex-operator algebra agrees with the
ambient real action on operators.  This is the compatibility needed to run *real*
continuous functional calculus inside the complex operator algebra. -/
theorem restrictedReal_smul_operator_eq
    (r : ℝ) (A : RealComplexification E →L[ℂ] RealComplexification E) :
    @SMul.smul ℝ (RealComplexification E →L[ℂ] RealComplexification E)
        complexOperatorRealAlgebra.toSMul r A = r • A := by
  apply ContinuousLinearMap.ext
  intro z
  change (r : ℂ) • A z = r • A z
  apply RealComplexification.ext
  · rw [RealComplexification.re_complex_smul,
      RealComplexification.re_real_smul]
    simp
  · rw [RealComplexification.im_complex_smul,
      RealComplexification.im_real_smul]
    simp

/-! ## Canonical conjugation on the complexification -/

/-- Canonical conjugation, bundled as an antiunitary involution. -/
@[expose]
noncomputable def canonicalConjugation :
    RealComplexification E ≃ₗᵢ⋆[ℂ] RealComplexification E where
  toFun := conjugation
  invFun := conjugation
  left_inv := conjugation_involutive
  right_inv := conjugation_involutive
  map_add' z w := by
    apply RealComplexification.ext <;> simp
  map_smul' := conjugation_complex_smul
  norm_map' := conjugation.norm_map

omit [CompleteSpace E] in
/-- The canonical conjugation acts pointwise as `conjugation`. -/
@[simp]
theorem canonicalConjugation_apply (z : RealComplexification E) :
    (canonicalConjugation (E := E)) z = conjugation z := rfl

omit [CompleteSpace E] in
/-- The canonical conjugation is its own inverse: conjugation is an involution. -/
@[simp]
theorem canonicalConjugation_symm_apply (z : RealComplexification E) :
    (canonicalConjugation (E := E)).symm z = conjugation z := by
  apply (canonicalConjugation (E := E)).injective
  simp [canonicalConjugation]

omit [CompleteSpace E] in
/-- Conjugation reverses the two slots of the complex inner product. -/
theorem inner_conjugation (z w : RealComplexification E) :
    ⟪conjugation z, conjugation w⟫_ℂ = ⟪w, z⟫_ℂ := by
  apply Complex.ext
  · simp [inner_apply, real_inner_comm]
  · simp [inner_apply, real_inner_comm]
    ring

omit [CompleteSpace E] in
/-- Conjugating the left slot exchanges the roles of the two arguments. -/
theorem inner_conjugation_left (z w : RealComplexification E) :
    ⟪conjugation z, w⟫_ℂ = ⟪conjugation w, z⟫_ℂ := by
  calc
    ⟪conjugation z, w⟫_ℂ =
        ⟪conjugation z, conjugation (conjugation w)⟫_ℂ := by simp
    _ = ⟪conjugation w, z⟫_ℂ := inner_conjugation z (conjugation w)

omit [CompleteSpace E] in
/-- Conjugating the right slot exchanges the roles of the two arguments. -/
theorem inner_conjugation_right (z w : RealComplexification E) :
    ⟪z, conjugation w⟫_ℂ = ⟪w, conjugation z⟫_ℂ := by
  calc
    ⟪z, conjugation w⟫_ℂ =
        ⟪conjugation (conjugation z), conjugation w⟫_ℂ := by simp
    _ = ⟪w, conjugation z⟫_ℂ := inner_conjugation (conjugation z) w

/-- Conjugation of a complexified bounded operator by canonical conjugation. -/
noncomputable def conjugateOperator
    (A : RealComplexification E →L[ℂ] RealComplexification E) :
    RealComplexification E →L[ℂ] RealComplexification E :=
  (canonicalConjugation (E := E)).toLinearIsometry.toContinuousLinearMap.comp
    (A.comp (canonicalConjugation (E := E)).symm.toLinearIsometry.toContinuousLinearMap)

omit [CompleteSpace E] in
/-- Pointwise formula for the conjugated operator: conjugate the input, apply `A`,
conjugate the output. -/
@[simp]
theorem conjugateOperator_apply
    (A : RealComplexification E →L[ℂ] RealComplexification E)
    (z : RealComplexification E) :
    conjugateOperator A z = conjugation (A (conjugation z)) := by
  simp [conjugateOperator]

omit [CompleteSpace E] in
/-- Conjugation fixes the zero operator. -/
@[simp]
theorem conjugateOperator_zero :
    conjugateOperator (0 : RealComplexification E →L[ℂ] RealComplexification E) = 0 := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext <;> simp [conjugateOperator_apply]

omit [CompleteSpace E] in
/-- Conjugation of operators is additive. -/
@[simp]
theorem conjugateOperator_add (A B : RealComplexification E →L[ℂ] RealComplexification E) :
    conjugateOperator (A + B) = conjugateOperator A + conjugateOperator B := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext <;> simp [conjugateOperator_apply]

omit [CompleteSpace E] in
/-- Conjugation commutes with negation. -/
@[simp]
theorem conjugateOperator_neg (A : RealComplexification E →L[ℂ] RealComplexification E) :
    conjugateOperator (-A) = -conjugateOperator A := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext <;> simp [conjugateOperator_apply]

omit [CompleteSpace E] in
/-- Conjugation commutes with subtraction. -/
@[simp]
theorem conjugateOperator_sub (A B : RealComplexification E →L[ℂ] RealComplexification E) :
    conjugateOperator (A - B) = conjugateOperator A - conjugateOperator B := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext <;> simp [conjugateOperator_apply]

omit [CompleteSpace E] in
/-- Conjugation fixes the identity operator. -/
@[simp]
theorem conjugateOperator_one :
    conjugateOperator (1 : RealComplexification E →L[ℂ] RealComplexification E) = 1 := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext <;> simp [conjugateOperator_apply]

omit [CompleteSpace E] in
/-- Conjugation is multiplicative, and preserves the order of composition — it is an
algebra map, not an anti-map. -/
@[simp]
theorem conjugateOperator_mul (A B : RealComplexification E →L[ℂ] RealComplexification E) :
    conjugateOperator (A * B) = conjugateOperator A * conjugateOperator B := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext <;>
    simp [conjugateOperator_apply, mul_apply_eq_comp]

omit [CompleteSpace E] in
/-- Conjugation is linear over `ℝ`.  Contrast `conjugateOperator_complex_smul`, where a
complex scalar picks up a conjugate. -/
@[simp]
theorem conjugateOperator_real_smul (r : ℝ)
    (A : RealComplexification E →L[ℂ] RealComplexification E) :
    conjugateOperator (r • A) = r • conjugateOperator A := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext <;> simp [conjugateOperator_apply]

omit [CompleteSpace E] in
/-- Conjugation of operators is **conjugate**-linear over `ℂ`. -/
theorem conjugateOperator_complex_smul (c : ℂ)
    (A : RealComplexification E →L[ℂ] RealComplexification E) :
    conjugateOperator (c • A) = (starRingEnd ℂ) c • conjugateOperator A := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [conjugateOperator_apply, smul_apply, conjugation_complex_smul]

omit [CompleteSpace E] in
/-- Conjugating twice returns the original operator. -/
@[simp]
theorem conjugateOperator_involutive (A : RealComplexification E →L[ℂ] RealComplexification E) :
    conjugateOperator (conjugateOperator A) = A := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext <;> simp [conjugateOperator_apply]

/-- Canonical conjugation commutes with taking adjoints. -/
theorem conjugateOperator_adjoint (A : RealComplexification E →L[ℂ] RealComplexification E) :
    conjugateOperator A.adjoint = (conjugateOperator A).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff
    (conjugateOperator A.adjoint) (conjugateOperator A)).2
  intro x y
  calc
    ⟪conjugateOperator A.adjoint x, y⟫_ℂ =
        ⟪conjugation y, A.adjoint (conjugation x)⟫_ℂ := by
          rw [conjugateOperator_apply, inner_conjugation_left]
    _ = ⟪A (conjugation y), conjugation x⟫_ℂ :=
      ContinuousLinearMap.adjoint_inner_right A (conjugation y) (conjugation x)
    _ = ⟪x, conjugation (A (conjugation y))⟫_ℂ := by
      rw [inner_conjugation_right]
    _ = ⟪x, conjugateOperator A y⟫_ℂ := by rw [conjugateOperator_apply]

omit [CompleteSpace E] in
/-- Conjugation does not increase the operator norm.  With `conjugateOperator_involutive`
this one-sided bound upgrades to the equality `norm_conjugateOperator`. -/
theorem norm_conjugateOperator_le (A : RealComplexification E →L[ℂ] RealComplexification E) :
    ‖conjugateOperator A‖ ≤ ‖A‖ := by
  refine (conjugateOperator A).opNorm_le_bound (norm_nonneg A) ?_
  intro z
  calc
    ‖conjugateOperator A z‖ = ‖A (conjugation z)‖ := by simp
    _ ≤ ‖A‖ * ‖conjugation z‖ := A.le_opNorm _
    _ = ‖A‖ * ‖z‖ := by rw [conjugation.norm_map]

omit [CompleteSpace E] in
/-- Conjugation preserves the operator norm. -/
theorem norm_conjugateOperator (A : RealComplexification E →L[ℂ] RealComplexification E) :
    ‖conjugateOperator A‖ = ‖A‖ := by
  apply le_antisymm (norm_conjugateOperator_le A)
  calc
    ‖A‖ = ‖conjugateOperator (conjugateOperator A)‖ := by simp
    _ ≤ ‖conjugateOperator A‖ := norm_conjugateOperator_le _

omit [CompleteSpace E] in
/-- Conjugation is an isometry of the operator algebra.  It is only *conjugate*-linear
over `ℂ`, so this is a metric statement rather than a linear-isometry one. -/
theorem isometry_conjugateOperator :
    Isometry (conjugateOperator :
      (RealComplexification E →L[ℂ] RealComplexification E) →
        (RealComplexification E →L[ℂ] RealComplexification E)) := by
  apply Isometry.of_dist_eq
  intro A B
  rw [dist_eq_norm, dist_eq_norm, ← conjugateOperator_sub,
    norm_conjugateOperator]

/-- Canonical conjugation is a continuous real star-algebra automorphism of
bounded operators on the complexification. -/
noncomputable def conjugateOperatorHom :
    (RealComplexification E →L[ℂ] RealComplexification E) →⋆ₐ[ℝ]
      (RealComplexification E →L[ℂ] RealComplexification E) where
  toFun := conjugateOperator
  map_one' := conjugateOperator_one
  map_zero' := conjugateOperator_zero
  map_mul' := conjugateOperator_mul
  map_add' := conjugateOperator_add
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one]
    change conjugateOperator
        (@SMul.smul ℝ (RealComplexification E →L[ℂ] RealComplexification E)
          complexOperatorRealAlgebra.toSMul r 1) =
      @SMul.smul ℝ (RealComplexification E →L[ℂ] RealComplexification E)
        complexOperatorRealAlgebra.toSMul r 1
    rw [restrictedReal_smul_operator_eq,
      conjugateOperator_real_smul, conjugateOperator_one]
  map_star' A := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using
      conjugateOperator_adjoint A

/-- The conjugation star-algebra map is continuous, being an isometry. -/
theorem continuous_conjugateOperatorHom :
    Continuous (conjugateOperatorHom :
      (RealComplexification E →L[ℂ] RealComplexification E) →
        (RealComplexification E →L[ℂ] RealComplexification E)) :=
  isometry_conjugateOperator.continuous

omit [CompleteSpace E] in
/-- Every complexified real operator is fixed by canonical conjugation. -/
theorem conjugateOperator_complexify (A : E →L[ℝ] E) :
    conjugateOperator (complexify A) = complexify A := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext <;> simp [conjugateOperator_apply]

/-- **The bundled functional calculus of a conjugation-fixed self-adjoint operator lands in
the fixed-point subalgebra.**  Stated for `cfcHom`, the `⋆`-algebra homomorphism itself, rather
than for a single symbol: this is what a *descent* of the calculus needs, and the symbol-level
statements `conjugateOperator_cfc_eq` and `conjugateOperator_cfc` below are corollaries.

The proof is the uniqueness of the calculus: `conjugateOperatorHom.comp (cfcHom hC)` is another
continuous real `⋆`-algebra homomorphism sending the restricted identity to `C`. -/
theorem conjugateOperator_cfcHom
    (C : RealComplexification E →L[ℂ] RealComplexification E) (hC : IsSelfAdjoint C)
    (hfix : conjugateOperator C = C) (g : C(spectrum ℝ C, ℝ)) :
    conjugateOperator (cfcHom hC g) = cfcHom hC g := by
  let φ : C(spectrum ℝ C, ℝ) →⋆ₐ[ℝ] (RealComplexification E →L[ℂ] RealComplexification E) :=
    conjugateOperatorHom.comp (cfcHom hC)
  have hφcont : Continuous φ :=
    continuous_conjugateOperatorHom.comp (cfcHom_continuous hC)
  have hφid : φ ((ContinuousMap.id ℝ).restrict (spectrum ℝ C)) = C := by
    change conjugateOperator
      (cfcHom hC ((ContinuousMap.id ℝ).restrict (spectrum ℝ C))) = C
    rw [cfcHom_id hC]
    exact hfix
  have heq : cfcHom hC = φ :=
    cfcHom_eq_of_continuous_of_map_id hC φ hφcont hφid
  have happ := DFunLike.congr_fun heq g
  change cfcHom hC g = conjugateOperator (cfcHom hC g) at happ
  exact happ.symm

/-- Continuous real functional calculus of a conjugation-fixed self-adjoint
operator remains conjugation-fixed. -/
theorem conjugateOperator_cfc_eq
    (C : RealComplexification E →L[ℂ] RealComplexification E) (hC : IsSelfAdjoint C)
    (hfix : conjugateOperator C = C) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ C)) :
    conjugateOperator (cfc f C) = cfc f C := by
  rw [cfc_apply f C hC hf]
  exact conjugateOperator_cfcHom C hC hfix _

/-! ## Descent of conjugation-fixed operators -/

omit [CompleteSpace E] in
/-- A conjugation-fixed operator maps the real copy into itself: the imaginary coordinate
of `A (ofReal x)` vanishes. -/
theorem fixed_operator_maps_real_to_real
    {A : RealComplexification E →L[ℂ] RealComplexification E}
    (hfix : conjugateOperator A = A) (x : E) :
    im (A (ofReal x)) = 0 := by
  have hpoint :=
    congrArg (fun B : RealComplexification E →L[ℂ] RealComplexification E => B (ofReal x)) hfix
  have hcoord := congrArg im hpoint
  have hneg : -im (A (ofReal x)) = im (A (ofReal x)) := by
    simpa only [conjugateOperator_apply, conjugation_ofReal, im_conj] using hcoord
  have htwo : (2 : ℝ) • im (A (ofReal x)) = 0 := by
    calc
      (2 : ℝ) • im (A (ofReal x)) =
          im (A (ofReal x)) + im (A (ofReal x)) := two_smul ℝ _
      _ = -im (A (ofReal x)) + im (A (ofReal x)) :=
        congrArg (fun y => y + im (A (ofReal x))) hneg.symm
      _ = 0 := neg_add_cancel _
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

omit [CompleteSpace E] in
/-- On the real copy, a conjugation-fixed operator is determined by its real restriction. -/
theorem fixed_operator_on_ofReal
    {A : RealComplexification E →L[ℂ] RealComplexification E}
    (hfix : conjugateOperator A = A) (x : E) :
    A (ofReal x) = ofReal (realPartOperator A x) := by
  apply RealComplexification.ext
  · simp
  · simp [fixed_operator_maps_real_to_real hfix x]

omit [CompleteSpace E] in
/-- A conjugation-fixed complex operator is exactly the complexification of its
restriction to the real copy. -/
theorem complexify_realPartOperator
    {A : RealComplexification E →L[ℂ] RealComplexification E} (hfix : conjugateOperator A = A) :
    complexify (realPartOperator A) = A := by
  apply ContinuousLinearMap.ext
  intro z
  have hz : z = ofReal (re z) + Complex.I • ofReal (im z) := by
    apply RealComplexification.ext <;> simp
  calc
    complexify (realPartOperator A) z =
        ofReal (realPartOperator A (re z)) +
          Complex.I • ofReal (realPartOperator A (im z)) := by
      apply RealComplexification.ext <;> simp
    _ = A (ofReal (re z)) + Complex.I • A (ofReal (im z)) := by
      rw [fixed_operator_on_ofReal hfix, fixed_operator_on_ofReal hfix]
    _ = A z := by
      rw [← map_smul, ← map_add, ← hz]

/-! ## Complexification and the Gram operator -/

/-- Complexification commutes with the Hilbert-space adjoint. -/
theorem complexify_adjoint (T : E →L[ℝ] F) :
    complexify T.adjoint = (complexify T).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff
    (complexify T.adjoint) (complexify T)).2
  intro z w
  simp only [inner_apply, re_complexify, im_complexify]
  rw [ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left]

/-- Complexification commutes with forming the Gram operator `Tᵃ ∘ T`. -/
theorem complexify_gram (T : E →L[ℝ] F) :
    complexify (T.adjoint ∘L T) =
      (complexify T).adjoint ∘L complexify T := by
  rw [complexify_comp, complexify_adjoint]

/-! ## Complexification as a real `⋆`-algebra homomorphism

`Complexification/Basic.lean` supplies the additive and composition laws; `complexify_comp` and
`complexify_id` are the ring laws once `ContinuousLinearMap.mul_def` is unfolded.  Adding
`complexify_adjoint` bundles `complexify` into a unital `⋆`-algebra map over `ℝ`, which is the
form the real spectral theory needs.

**The `⋆`-algebra structure maps are not re-exported as separate lemmas here.**  Three
`DavisKahan` modules already declare `complexify_mul`, `complexify_one` and `complexify_star` in
three different namespaces, and several of their consumers use the bare names under an `open` of
this namespace; a fourth copy here would make those uses ambiguous.  Use
`map_mul complexifyStarAlgHom`, `map_one`, `map_star` instead, and see the note in
`RealContinuousFunctionalCalculus.lean` on consolidating the three. -/

omit [CompleteSpace E] in
/-- Complexification intertwines the real algebra map of `E →L[ℝ] E` with the *complex* algebra
map of the complexified operator algebra, along `ℝ → ℂ`.

Stated against `algebraMap ℂ` rather than `algebraMap ℝ` because the complexified operator
algebra carries **two** real algebra structures: `ContinuousLinearMap.algebra`, which is global
and sends `r` to the ambient `r • 1`, and the scoped `complexOperatorRealAlgebra`, which sends
`r` to `(r : ℂ) • 1`.  They are propositionally but not definitionally equal.  The complex
algebra map is unambiguous, so it is the one to phrase transport against. -/
theorem complexify_algebraMapComplex (r : ℝ) :
    complexify (algebraMap ℝ (E →L[ℝ] E) r) =
      algebraMap ℂ (RealComplexification E →L[ℂ] RealComplexification E) (r : ℂ) := by
  have hone : complexify (1 : E →L[ℝ] E) = 1 := complexify_id
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    complexify_real_smul, hone]

omit [CompleteSpace E] in
/-- The scoped real algebra structure on the complexified operator algebra factors the complex
one through `ℝ → ℂ`; this holds by definition of `Algebra.complexToReal`.  It is what makes
`spectrum ℝ` on that algebra the real trace of `spectrum ℂ`. -/
theorem algebraMap_complexOperator (r : ℝ) :
    algebraMap ℝ (RealComplexification E →L[ℂ] RealComplexification E) r =
      algebraMap ℂ (RealComplexification E →L[ℂ] RealComplexification E) (r : ℂ) := rfl

omit [CompleteSpace E] in
/-- Complexification intertwines the two *real* algebra maps, for the scoped real structure on
the target. -/
theorem complexify_algebraMapReal (r : ℝ) :
    complexify (algebraMap ℝ (E →L[ℝ] E) r) =
      algebraMap ℝ (RealComplexification E →L[ℂ] RealComplexification E) r := by
  rw [algebraMap_complexOperator, complexify_algebraMapComplex]

/-- **Complexification bundled as a unital real `⋆`-algebra homomorphism.**  Its target carries
the scoped real algebra structure `complexOperatorRealAlgebra`, so a consumer needs
`open scoped TauCeti.RealComplexification`. -/
@[expose]
noncomputable def complexifyStarAlgHom :
    (E →L[ℝ] E) →⋆ₐ[ℝ] (RealComplexification E →L[ℂ] RealComplexification E) where
  toFun := complexify
  map_one' := complexify_id
  map_mul' A B := by
    simpa only [ContinuousLinearMap.mul_def] using complexify_comp A B
  map_zero' := complexify_zero
  map_add' := complexify_add
  commutes' := complexify_algebraMapReal
  map_star' A := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using complexify_adjoint A

/-- `complexifyStarAlgHom` acts by `complexify`. -/
@[simp]
theorem complexifyStarAlgHom_apply (A : E →L[ℝ] E) :
    complexifyStarAlgHom A = complexify A := rfl

/-! ## The fixed-point subalgebra is closed under the whole spectral calculus

`conjugateOperator_cfc_eq` above needs the symbol to be continuous on the
spectrum.  The result below removes that side condition.  Modulus transport is
kept downstream in `ForTauCeti.Analysis.InnerProductSpace.ModulusTransport`, so
this functional-calculus foundation does not depend on the modulus built from it. -/

/-- The continuous functional calculus of a conjugation-fixed self-adjoint
operator is conjugation-fixed, with **no continuity hypothesis** on the symbol:
off the continuous symbols the calculus is zero, which is fixed as well. -/
theorem conjugateOperator_cfc
    (C : RealComplexification E →L[ℂ] RealComplexification E) (hC : IsSelfAdjoint C)
    (hfix : conjugateOperator C = C) (f : ℝ → ℝ) :
    conjugateOperator (cfc f C) = cfc f C := by
  by_cases hf : ContinuousOn f (spectrum ℝ C)
  · exact conjugateOperator_cfc_eq C hC hfix f hf
  · rw [cfc_apply_of_not_continuousOn C hf, conjugateOperator_zero]

/-- Canonical conjugation preserves positivity of an operator.  It is an
`ℝ`-linear `⋆`-algebra automorphism, so it preserves both halves of the
definition; the quadratic form is transported by conjugating the argument. -/
theorem conjugateOperator_nonneg
    {A : RealComplexification E →L[ℂ] RealComplexification E} (hA : 0 ≤ A) :
    0 ≤ conjugateOperator A := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive] at hA ⊢
  refine ⟨?_, fun z => ?_⟩
  · rw [← ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric,
      ContinuousLinearMap.isSelfAdjoint_iff', ← conjugateOperator_adjoint]
    have : ContinuousLinearMap.adjoint A = A := by
      rw [← ContinuousLinearMap.isSelfAdjoint_iff']
      exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 hA.1
    rw [this]
  · have hval : ⟪conjugateOperator A z, z⟫_ℂ =
        (starRingEnd ℂ) ⟪A (conjugation z), conjugation z⟫_ℂ := by
      rw [conjugateOperator_apply, inner_conjugation_left, ← inner_conj_symm]
    have h := hA.2 (conjugation z)
    simp only [ContinuousLinearMap.reApplyInnerSelf_apply] at h ⊢
    rw [hval, RCLike.re_eq_complex_re, Complex.conj_re, ← RCLike.re_eq_complex_re]
    exact h


end

end RealComplexification
end TauCeti
