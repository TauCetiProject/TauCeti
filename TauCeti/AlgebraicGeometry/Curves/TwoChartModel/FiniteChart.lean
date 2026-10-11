/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Basic
public import TauCeti.FieldTheory.FunctionField.AffineModel.IntegralClosure
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
-- Proof-only: finiteness of normalization of a polynomial chart.
import TauCeti.RingTheory.IntegralClosure.MvPolynomial

/-!
# Finite polynomial charts of the two-chart model

For a transcendental function `x` on an algebraic function field `F/k`, the finite chart
`𝒪_x` is the normalization of `k[x]` in `F`. Evaluation at `x` gives the concrete map
`k[X] → 𝒪_x`; it is finite without a separability assumption. The same construction at
`x⁻¹` gives the chart at infinity. These are the affine maps that glue to the finite
map from the two-chart model to the projective line.

## Main results

* `twoChartModel.polynomialChartMap`: evaluation `k[X] → 𝒪_x`.
* `twoChartModel.polynomialChartMap_injective`: the map identifies `k[X]` with `k[x]`.
* `twoChartModel.polynomialChartMap_finite`: the chart map is finite.
* `twoChartModel.isFinite_specMap_polynomialChartMap`: the induced morphism of affine schemes
  is finite.

The finiteness input is `TauCeti.IsIntegralClosure.finite_adjoin_of_transcendental`,
transported across `Polynomial.algEquivOfTranscendental`.

The two affine normalizations are the charts of the projective model in Stichtenoth,
*Algebraic Function Fields and Codes*, second edition, Section III.2 and Appendix B.
-/

public section

open _root_.AlgebraicGeometry
open scoped _root_.IntermediateField
open _root_.IntermediateField.algebraAdjoinAdjoin

namespace TauCeti.AlgebraicGeometry.twoChartModel

universe u

variable {k F : Type u} [Field k] [Field F] [Algebra k F]

/-- Evaluation at `x`, regarded as a map from the polynomial chart of the projective line
to the corresponding normalization chart of the function field. -/
noncomputable def polynomialChartMap (x : F) : Polynomial k →ₐ[k]
    holomorphyRing {P : Place k F | x ∈ P.integers} :=
  Polynomial.aeval (R := k) (A := holomorphyRing {P : Place k F | x ∈ P.integers})
    ⟨x, mem_holomorphyRing_iff.mpr fun _ hP ↦ hP⟩

@[simp]
theorem polynomialChartMap_X (x : F) :
    polynomialChartMap (k := k) x Polynomial.X =
      (⟨x, mem_holomorphyRing_iff.mpr fun _ hP ↦ hP⟩ :
        holomorphyRing {P : Place k F | x ∈ P.integers}) := by
  simp [polynomialChartMap]

@[simp]
theorem polynomialChartMap_C (x : F) (c : k) :
    polynomialChartMap (k := k) x (Polynomial.C c) = algebraMap k _ c := by
  simp [polynomialChartMap]

@[simp]
theorem coe_polynomialChartMap (x : F) (p : Polynomial k) :
    ((polynomialChartMap (k := k) x p :
      holomorphyRing {P : Place k F | x ∈ P.integers}) : F) = Polynomial.aeval x p := by
  simp [polynomialChartMap]

/-- Evaluation into the normalization chart is injective when `x` is transcendental. -/
theorem polynomialChartMap_injective {x : F} (hx : Transcendental k x) :
    Function.Injective (polynomialChartMap (k := k) x) := by
  intro p q hpq
  apply (transcendental_iff_injective.mp hx)
  simpa [polynomialChartMap] using congrArg
    (fun a : holomorphyRing {P : Place k F | x ∈ P.integers} ↦ (a : F)) hpq

/-- The normalization chart is a finite module over the polynomial chart, including for
inseparable extensions of `k(X)`. -/
theorem polynomialChartMap_finite (hF : IsFunctionField k F) {x : F}
    (hx : Transcendental k x) : (polynomialChartMap (k := k) x).toRingHom.Finite := by
  let A := holomorphyRing {P : Place k F | x ∈ P.integers}
  let y : A := ⟨x, mem_holomorphyRing_iff.mpr fun _ hP ↦ hP⟩
  have hBA : Algebra.adjoin k {x} ≤ A :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr y.property)
  let ι : Algebra.adjoin k {x} →ₐ[k] A := Subalgebra.inclusion hBA
  have hfin : ι.toRingHom.Finite := by
    let C := integralClosure (Algebra.adjoin k {x}) F
    have : FiniteDimensional k⟮x⟯ F := hF.finiteDimensional_adjoin hx
    have hfinC : (algebraMap (Algebra.adjoin k {x}) C).Finite := by
      -- For this algebraMap, `RingHom.Finite` unfolds to `Module.Finite` for the
      -- algebra-induced module structure on `C`, which is the structure used by the theorem.
      change Module.Finite (Algebra.adjoin k {x}) C
      exact IsIntegralClosure.finite_adjoin_of_transcendental k hx F C
    let e : C ≃+* A := (Subalgebra.equivOfEq _ _
      (restrictScalars_integralClosure_adjoin_eq_holomorphyRing hF x)).toRingEquiv
    have he : ι.toRingHom = e.toRingHom.comp (algebraMap _ C) := by
      ext a
      rfl
    rw [he]
    exact e.finite.comp hfinC
  have heval : (polynomialChartMap (k := k) x).toRingHom =
      ι.toRingHom.comp (Polynomial.algEquivOfTranscendental k x hx).toRingHom := by
    ext
    · simp [polynomialChartMap, ι]
    · simp [polynomialChartMap, ι]
  rw [heval]
  exact hfin.comp (Polynomial.algEquivOfTranscendental k x hx).toRingEquiv.finite

/-- The morphism from the normalization chart to the affine chart of `ℙ¹_k` is finite. -/
theorem isFinite_specMap_polynomialChartMap (hF : IsFunctionField k F) {x : F}
    (hx : Transcendental k x) :
    IsFinite (Spec.map (CommRingCat.ofHom (polynomialChartMap (k := k) x).toRingHom)) :=
  (IsFinite.SpecMap_iff _).mpr (polynomialChartMap_finite hF hx)

end TauCeti.AlgebraicGeometry.twoChartModel
