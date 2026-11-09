/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Law.Basic
public import TauCeti.Analysis.CStarAlgebra.GNS.Basic
public import TauCeti.Analysis.InnerProductSpace.BorelCalculus.DiagonalMeasure
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart

/-!
# Scalar laws and GNS spectral measures

The law of a selfadjoint element with respect to a positive functional agrees with its scalar
spectral measure in any vector-state realization. The diagonal measure is carried by the
complex spectrum of the represented operator; pushing it forward by the real part gives the
law on the real line. In particular, the canonical GNS representation and its cyclic vector
recover the C⋆-algebraic law, without a faithfulness assumption on the functional.

The comparison uses `ContinuousLinearMap.diagMeasure`, the scalar spectral measure characterized
by integration of the continuous functional calculus, and `PositiveLinearMap.eq_law_iff`, the
corresponding characterization of the scalar law. The GNS representation can have a smaller
spectrum than the original element; equality of the measures does not assert equality of spectra.

## References

* G. J. Murphy, *C⋆-Algebras and Operator Theory*, §3.3.
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, §VII.2.
-/

public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace ComplexOrder

namespace PositiveLinearMap

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A vector-state realization identifies the law of a selfadjoint element with the pushforward
of its scalar spectral measure along the real part. Neither the representation nor the
functional is required to be faithful, and the vector need not have norm one. -/
theorem law_eq_map_diagMeasure (φ : A →ₚ[ℂ] ℂ) (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hφ : ∀ x, ⟪ξ, π x ξ⟫_ℂ = φ x) {a : A} (ha : IsSelfAdjoint a) :
    let _ : IsStarNormal (π a) := (ha.map π).isStarNormal
    φ.law a = ((π a).diagMeasure ξ).map (fun z : spectrum ℂ (π a) => (z : ℂ).re) := by
  have hπa : IsSelfAdjoint (π a) := ha.map π
  let _ : IsStarNormal (π a) := hπa.isStarNormal
  refine (eq_law_iff.2 fun f hf => ?_).symm
  rw [integral_map (by fun_prop) (by fun_prop), ← integral_complex_ofReal]
  rw [(π a).integral_diagMeasure_eq_inner_cfc ξ (fun z => (f z.re : ℂ)),
    cfc_comp_re f (π a) hf.continuousOn, hπa.coe_realPart,
    ← π.map_cfc f a hf.continuousOn (ha := ha) (hφa := hπa), hφ]

/-- The C⋆-algebraic law is the scalar spectral measure of the GNS operator at the canonical
cyclic vector, viewed as a measure on the real line. This holds even for nonfaithful states. -/
theorem law_eq_map_gns_diagMeasure (φ : A →ₚ[ℂ] ℂ) {a : A} (ha : IsSelfAdjoint a) :
    let _ : IsStarNormal (φ.gnsStarAlgHom a) := (ha.map φ.gnsStarAlgHom).isStarNormal
    φ.law a = ((φ.gnsStarAlgHom a).diagMeasure φ.gnsVector).map
      (fun z : spectrum ℂ (φ.gnsStarAlgHom a) => (z : ℂ).re) :=
  φ.law_eq_map_diagMeasure φ.gnsStarAlgHom φ.gnsVector
    (fun x => by simp) ha

end PositiveLinearMap
