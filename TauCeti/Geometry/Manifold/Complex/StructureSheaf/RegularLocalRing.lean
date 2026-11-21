/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Cotangent
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Regular
public import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay
import TauCeti.RingTheory.Regular.RegularSequence

/-!
# Coordinate parameters of regular holomorphic local rings

Centered coordinates in any holomorphic chart form a regular sequence in the holomorphic local
ring (`OpenPartialHomeomorph.isRegular_ofFn_holomorphicLinearCoordinateGerm`). Thus successive
coordinate equations are non-zero-divisors on the successive quotients. This is the local algebra
underlying smooth holomorphic zero sets.

Moreover, any holomorphic germ vanishing at the base point with nonzero derivative in a chart
generates a prime ideal, and is prime and irreducible in the holomorphic stalk
(`OpenPartialHomeomorph.isPrime_span_of_holomorphicStalkFDeriv_ne_zero`,
`OpenPartialHomeomorph.prime_of_holomorphicStalkFDeriv_ne_zero`,
`OpenPartialHomeomorph.irreducible_of_holomorphicStalkFDeriv_ne_zero`). In particular, this
applies to centered linear coordinate germs along nonzero functionals.

## References

* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter II.
* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter II.
-/

public noncomputable section

open IsLocalRing
open scoped ContDiff Manifold

namespace OpenPartialHomeomorph

open TauCeti TauCeti.holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]

/-- Centered coordinates of a holomorphic chart, in any ordered basis, form a regular sequence
in the holomorphic local ring. In particular each coordinate is a non-zero-divisor after
quotienting by the preceding coordinates. -/
theorem isRegular_ofFn_holomorphicLinearCoordinateGerm (e : OpenPartialHomeomorph X E)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) ω X) (x : X) (hx : x ∈ e.source)
    {n : ℕ} (b : Module.Basis (Fin n) ℂ E) :
    RingTheory.Sequence.IsRegular ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x)
      (List.ofFn fun i ↦ e.holomorphicLinearCoordinateGerm he x
        (LinearMap.toContinuousLinearMap (b.coord i)) hx) := by
  have := e.isRegularLocalRing_holomorphicStalk he hx
  have hspan :
      (maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x)).spanFinrank = n := by
    rw [e.spanFinrank_maximalIdeal_holomorphicStalk he hx, Module.finrank_eq_card_basis b,
      Fintype.card_fin]
  apply TauCeti.IsRegularLocalRing.isRegular_of_ofList_eq_maximalIdeal
  · rw [Ideal.ofList_ofFn, maximalIdeal_stalk]
    exact (e.ker_eval_eq_span_holomorphicLinearCoordinateGerm he b hx).symm
  · simp only [List.length_ofFn, hspan, le_refl]

/-- A holomorphic germ vanishing at `x` with nonzero derivative in a chart generates a prime ideal
in the holomorphic stalk. -/
theorem isPrime_span_of_holomorphicStalkFDeriv_ne_zero (e : OpenPartialHomeomorph X E)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) ω X) (x : X) (hx : x ∈ e.source)
    {s : (holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x}
    (hs : s ∈ maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x))
    (hds : e.holomorphicStalkFDeriv x hx s ≠ 0) :
    (Ideal.span {s}).IsPrime := by
  have := e.isRegularLocalRing_holomorphicStalk he hx
  refine TauCeti.IsRegularLocalRing.span_singleton_isPrime_of_notMem_sq hs fun hsq ↦ hds ?_
  exact (e.holomorphicStalkFDeriv_eq_zero_iff x hx he ⟨s, hs⟩).2 hsq

/-- A holomorphic germ vanishing at `x` with nonzero derivative in a chart is prime in the
holomorphic stalk. -/
theorem prime_of_holomorphicStalkFDeriv_ne_zero (e : OpenPartialHomeomorph X E)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) ω X) (x : X) (hx : x ∈ e.source)
    {s : (holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x}
    (hs : s ∈ maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x))
    (hds : e.holomorphicStalkFDeriv x hx s ≠ 0) :
    Prime s := by
  have := e.isRegularLocalRing_holomorphicStalk he hx
  refine (Ideal.span_singleton_prime fun h0 ↦ hds ?_).1
    (e.isPrime_span_of_holomorphicStalkFDeriv_ne_zero he x hx hs hds)
  simp [h0]

/-- A holomorphic germ vanishing at `x` with nonzero derivative in a chart is irreducible in the
holomorphic stalk. -/
theorem irreducible_of_holomorphicStalkFDeriv_ne_zero (e : OpenPartialHomeomorph X E)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) ω X) (x : X) (hx : x ∈ e.source)
    {s : (holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x}
    (hs : s ∈ maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x))
    (hds : e.holomorphicStalkFDeriv x hx s ≠ 0) :
    Irreducible s := by
  have := e.isRegularLocalRing_holomorphicStalk he hx
  exact (e.prime_of_holomorphicStalkFDeriv_ne_zero he x hx hs hds).irreducible

/-- For any nonzero continuous linear functional `ℓ` on `E`, the centered linear coordinate germ
along `ℓ` generates a prime ideal in the holomorphic stalk. -/
theorem isPrime_span_holomorphicLinearCoordinateGerm (e : OpenPartialHomeomorph X E)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) ω X) (x : X) (hx : x ∈ e.source)
    {ℓ : StrongDual ℂ E} (hℓ : ℓ ≠ 0) :
    (Ideal.span {e.holomorphicLinearCoordinateGerm he x ℓ hx}).IsPrime :=
  e.isPrime_span_of_holomorphicStalkFDeriv_ne_zero he x hx (by simp) (by simpa)

/-- For any nonzero continuous linear functional `ℓ` on `E`, the centered linear coordinate germ
along `ℓ` is prime in the holomorphic stalk. -/
theorem prime_holomorphicLinearCoordinateGerm (e : OpenPartialHomeomorph X E)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) ω X) (x : X) (hx : x ∈ e.source)
    {ℓ : StrongDual ℂ E} (hℓ : ℓ ≠ 0) :
    Prime (e.holomorphicLinearCoordinateGerm he x ℓ hx) :=
  e.prime_of_holomorphicStalkFDeriv_ne_zero he x hx (by simp) (by simpa)

/-- For any nonzero continuous linear functional `ℓ` on `E`, the centered linear coordinate germ
along `ℓ` is irreducible in the holomorphic stalk. -/
theorem irreducible_holomorphicLinearCoordinateGerm (e : OpenPartialHomeomorph X E)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) ω X) (x : X) (hx : x ∈ e.source)
    {ℓ : StrongDual ℂ E} (hℓ : ℓ ≠ 0) :
    Irreducible (e.holomorphicLinearCoordinateGerm he x ℓ hx) :=
  e.irreducible_of_holomorphicStalkFDeriv_ne_zero he x hx (by simp) (by simpa)

end OpenPartialHomeomorph
