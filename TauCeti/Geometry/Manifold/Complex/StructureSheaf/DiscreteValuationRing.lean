/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Domain
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.LocalRing
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Order
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Holomorphic stalks are discrete valuation rings

The stalk of the holomorphic structure sheaf of a complex curve is a discrete valuation
ring. Every centered local coordinate is a uniformizer. Thus Mathlib's discrete valuation
and fractional-ideal theory applies to holomorphic germs, providing the local algebra for
divisor sheaves and their point twists.

The coordinate may be any chart in the maximal differentiable atlas; no compactness,
connectedness or Hausdorff hypothesis is needed.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, §§1, 6 and 16.
-/

public noncomputable section

open IsManifold
open scoped ContDiff Manifold
open TauCeti TauCeti.holomorphicStructureSheaf

namespace OpenPartialHomeomorph

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  (e : OpenPartialHomeomorph X ℂ) (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X) (x : X)

/-- A centered holomorphic coordinate is irreducible in the local ring of germs. -/
theorem irreducible_holomorphicCoordinateGerm (hx : x ∈ e.source) :
    Irreducible (holomorphicCoordinateGerm e he x hx) := by
  apply IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal
    _ (holomorphicCoordinateGerm_ne_zero e he x hx)
  rw [maximalIdeal_stalk, ker_eval_eq_span_holomorphicCoordinateGerm e he x hx]

end OpenPartialHomeomorph

namespace TauCeti.holomorphicStructureSheaf

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

/-- The stalk of the holomorphic structure sheaf on a complex curve is a discrete valuation
ring, with any centered local coordinate as uniformizer. -/
instance instIsDiscreteValuationRingStalk (x : X) :
    IsDiscreteValuationRing ((holomorphicStructureSheaf 𝓘(ℂ) X).presheaf.stalk x) := by
  -- The construction uses `OpenPartialHomeomorph.ker_eval_eq_span_holomorphicCoordinateGerm`
  -- and `TauCeti.holomorphicStructureSheaf.existsUnique_mem_pow_ker_eval_notMem_succ`, then
  -- Mathlib's `IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization`.
  let e := chartAt ℂ x
  let he := chart_mem_maximalAtlas x (I := 𝓘(ℂ)) (n := 1)
  let c := e.holomorphicCoordinateGerm he x (mem_chart_source ℂ x)
  have hc : Irreducible c := e.irreducible_holomorphicCoordinateGerm he x (mem_chart_source ℂ x)
  apply IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
  refine ⟨c, hc, fun {f} hf => ?_⟩
  obtain ⟨n, ⟨hn, hnext⟩, -⟩ := existsUnique_mem_pow_ker_eval_notMem_succ x hf
  rw [e.ker_eval_eq_span_holomorphicCoordinateGerm he x (mem_chart_source ℂ x),
    Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hn
  obtain ⟨q, hq⟩ := hn
  have hqunit : IsUnit q := by
    rw [isUnit_stalk_iff]
    intro hzero
    have hdiv : c ∣ q :=
      (e.holomorphicCoordinateGerm_dvd_iff_eval_eq_zero he x (mem_chart_source ℂ x) q).mpr hzero
    apply hnext
    rw [e.ker_eval_eq_span_holomorphicCoordinateGerm he x (mem_chart_source ℂ x),
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    obtain ⟨r, hr⟩ := hdiv
    exact ⟨r, by rw [hq, pow_succ, mul_assoc, ← hr]⟩
  obtain ⟨u, rfl⟩ := hqunit
  exact ⟨n, u, hq.symm⟩

end TauCeti.holomorphicStructureSheaf
