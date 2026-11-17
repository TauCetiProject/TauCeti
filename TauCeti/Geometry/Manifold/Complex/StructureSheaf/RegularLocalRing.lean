/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Cotangent
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Dimension
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Noetherian
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Regular
public import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay
import Mathlib.Algebra.Module.SpanRankOperations
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.RingTheory.Regular.RegularSequence

/-!
# Coordinate parameters of regular holomorphic local rings

The local ring of holomorphic germs on a finite-dimensional complex manifold without boundary
is regular, of Krull dimension equal to the complex dimension of the model
(`TauCeti.holomorphicStructureSheaf.stalkIsRegularLocalRing`,
`TauCeti.holomorphicStructureSheaf.ringKrullDim_stalk`). Its maximal ideal needs exactly that many
generators (`TauCeti.holomorphicStructureSheaf.spanFinrank_maximalIdeal_stalk`), by the
cotangent-space calculation.

Centered coordinates in any holomorphic chart form a regular sequence, not merely a generating
family of the maximal ideal. Thus successive coordinate equations are non-zero-divisors on the
successive quotients. This is the local algebra underlying smooth holomorphic zero sets.
The generator count also applies to the native complex-smooth sheaf stalks through their
canonical comparison with holomorphic germs.

The regularity and dimension formulas also hold chart-locally at any point in the domain of a
holomorphic chart with respect to a boundaryless model, without assuming a global manifold
structure on `X`. The centered coordinate germ along any nonzero continuous linear functional on
the model generates a prime ideal and is prime and irreducible.

## Main declarations

* `TauCeti.holomorphicStructureSheaf.spanFinrank_maximalIdeal_stalk`,
  `TauCeti.holomorphicStructureSheaf.finrank_cotangentSpace_stalk` (and their `smoothStalk`
  counterparts): the maximal-ideal generator count and the cotangent dimension equal
  `Module.finrank ℂ E`.
* `OpenPartialHomeomorph.isRegularLocalRing_holomorphicStalk`,
  `OpenPartialHomeomorph.spanFinrank_maximalIdeal_holomorphicStalk`,
  `OpenPartialHomeomorph.ringKrullDim_holomorphicStalk`: the chart-local versions.
* `OpenPartialHomeomorph.isRegular_ofFn_holomorphicLinearCoordinateGerm`: centered basis
  coordinate germs form a regular sequence.
* `OpenPartialHomeomorph.isPrime_span_holomorphicLinearCoordinateGerm`,
  `OpenPartialHomeomorph.prime_holomorphicLinearCoordinateGerm`,
  `OpenPartialHomeomorph.irreducible_holomorphicLinearCoordinateGerm`: any nonzero centered linear
  coordinate germ is prime and irreducible.

## References

* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter II.
* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter II.
* H. Grauert and R. Remmert, *Coherent Analytic Sheaves*, Chapter 2.
-/

public noncomputable section

open IsLocalRing
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

/-- The minimal number of generators of the maximal ideal of a holomorphic stalk equals the
complex dimension of the manifold model. -/
theorem spanFinrank_maximalIdeal_stalk (x : X) :
    (maximalIdeal ((holomorphicStructureSheaf I X).presheaf.stalk x)).spanFinrank =
      Module.finrank ℂ E := by
  let : IsManifold I ω X := IsManifold.of_ne_zero ω one_ne_zero inferInstance
  rw [← Ideal.spanFinrank_map_eq_of_ringEquiv
    (stalkEquivModelSpace (I := I) (V := Fin (Module.finrank ℂ E) → ℂ) x
      (ContinuousLinearEquiv.ofFinrankEq (by simp))),
    map_ringEquiv_maximalIdeal, spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  let V := Fin (Module.finrank ℂ E) → ℂ
  exact ((OpenPartialHomeomorph.refl V).finrank_cotangentSpace_holomorphicStalk
    _ (Set.mem_univ _)
    (StructureGroupoid.id_mem_maximalAtlas (contDiffGroupoid ω 𝓘(ℂ, V)))).trans (by simp [V])

/-- The kernel of evaluation on a holomorphic stalk needs as many generators as the complex
model dimension. This is the generator count in the simp normal form of the maximal ideal. -/
@[simp]
theorem spanFinrank_ker_eval (x : X) :
    (RingHom.ker (eval I X x)).spanFinrank = Module.finrank ℂ E := by
  rw [← maximalIdeal_stalk, spanFinrank_maximalIdeal_stalk]

/-- The maximal ideal of the native complex-smooth stalk needs as many generators as the
complex model dimension. -/
@[simp]
theorem spanFinrank_maximalIdeal_smoothStalk (x : X) :
    (maximalIdeal ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x)).spanFinrank =
      Module.finrank ℂ E := by
  rw [← map_ringEquiv_maximalIdeal (smoothStalkIso I X x).commRingCatIsoToRingEquiv,
    Ideal.spanFinrank_map_eq_of_ringEquiv, spanFinrank_maximalIdeal_stalk]

/-- The dimension of the algebraic cotangent space of a holomorphic stalk over its residue field
equals the complex dimension of the model space. -/
theorem finrank_cotangentSpace_stalk (x : X) :
    Module.finrank (ResidueField ((holomorphicStructureSheaf I X).presheaf.stalk x))
      (CotangentSpace ((holomorphicStructureSheaf I X).presheaf.stalk x)) =
        Module.finrank ℂ E := by
  rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, spanFinrank_maximalIdeal_stalk]

/-- The dimension of the algebraic cotangent space of a complex-smooth structure-sheaf stalk over
its residue field equals the complex dimension of the model space. -/
theorem finrank_cotangentSpace_smoothStalk (x : X) :
    Module.finrank (ResidueField ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x))
      (CotangentSpace ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x)) =
        Module.finrank ℂ E := by
  rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, spanFinrank_maximalIdeal_smoothStalk]

end TauCeti.holomorphicStructureSheaf

namespace OpenPartialHomeomorph

open TauCeti TauCeti.holomorphicStructureSheaf

section Boundaryless

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X]
  (e : OpenPartialHomeomorph X H) (he : e ∈ IsManifold.maximalAtlas I ω X) {x : X}
  (hx : x ∈ e.source)

include he hx in
/-- At any point in the domain of a holomorphic chart with respect to a boundaryless model on a
finite-dimensional complex normed space `E`, the holomorphic stalk is a regular local ring,
without assuming a global manifold structure on `X`. -/
theorem isRegularLocalRing_holomorphicStalk :
    IsRegularLocalRing ((holomorphicStructureSheaf I X).presheaf.stalk x) :=
  .of_ringEquiv (e.holomorphicStalkEquivModelSpace he x hx
    (ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm)).symm

include he hx in
/-- At any point in the domain of a holomorphic chart with respect to a boundaryless model on `E`,
the minimal number of generators of the maximal ideal of the holomorphic stalk equals
`finrank ℂ E`. -/
theorem spanFinrank_maximalIdeal_holomorphicStalk :
    (maximalIdeal ((holomorphicStructureSheaf I X).presheaf.stalk x)).spanFinrank =
      Module.finrank ℂ E := by
  rw [← Ideal.spanFinrank_map_eq_of_ringEquiv (e.holomorphicStalkEquivModelSpace he x hx
      (ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm)),
    map_ringEquiv_maximalIdeal, spanFinrank_maximalIdeal_stalk, Module.finrank_fin_fun]

include he hx in
/-- At any point in the domain of a holomorphic chart with respect to a boundaryless model on `E`,
the Krull dimension of the holomorphic stalk equals `finrank ℂ E`. -/
theorem ringKrullDim_holomorphicStalk :
    ringKrullDim ((holomorphicStructureSheaf I X).presheaf.stalk x) = Module.finrank ℂ E := by
  have := e.isRegularLocalRing_holomorphicStalk he hx
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal,
    e.spanFinrank_maximalIdeal_holomorphicStalk he hx]

end Boundaryless

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
  let σ := e.holomorphicStalkEquivModelSpace he x hx b.equivFun.toContinuousLinearEquiv
  let := IsRegularLocalRing.of_ringEquiv σ.symm
  have hspan :
      (maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x)).spanFinrank = n := by
    rw [← Ideal.spanFinrank_map_eq_of_ringEquiv σ, map_ringEquiv_maximalIdeal,
      spanFinrank_maximalIdeal_stalk]
    simp
  apply TauCeti.IsRegularLocalRing.isRegular_of_ofList_eq_maximalIdeal
  · rw [Ideal.ofList_ofFn, maximalIdeal_stalk]
    exact (e.ker_eval_eq_span_holomorphicLinearCoordinateGerm he b hx).symm
  · simp only [List.length_ofFn, hspan, le_refl]

section Prime

variable (e : OpenPartialHomeomorph X E) (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) ω X) {x : X}
  (hx : x ∈ e.source)

/-- For any nonzero continuous linear functional `ℓ` on `E`, the centered linear coordinate germ
along `ℓ` generates a prime ideal in the holomorphic stalk. -/
theorem isPrime_span_holomorphicLinearCoordinateGerm {ℓ : StrongDual ℂ E} (hℓ : ℓ ≠ 0) :
    (Ideal.span {e.holomorphicLinearCoordinateGerm he x ℓ hx}).IsPrime := by
  have := e.isRegularLocalRing_holomorphicStalk he hx
  have hm : e.holomorphicLinearCoordinateGerm he x ℓ hx ∈
      maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x) := by simp
  refine TauCeti.IsRegularLocalRing.span_singleton_isPrime_of_notMem_sq hm fun hsq ↦ hℓ ?_
  simpa using (e.holomorphicStalkFDeriv_eq_zero_iff x hx he ⟨_, hm⟩).2 hsq

/-- For any nonzero continuous linear functional `ℓ` on `E`, the centered linear coordinate germ
along `ℓ` is prime in the holomorphic stalk. -/
theorem prime_holomorphicLinearCoordinateGerm {ℓ : StrongDual ℂ E} (hℓ : ℓ ≠ 0) :
    Prime (e.holomorphicLinearCoordinateGerm he x ℓ hx) := by
  have := e.isRegularLocalRing_holomorphicStalk he hx
  refine (Ideal.span_singleton_prime fun h0 ↦ hℓ ?_).1
    (e.isPrime_span_holomorphicLinearCoordinateGerm he hx hℓ)
  simpa [h0] using (e.holomorphicStalkFDeriv_holomorphicLinearCoordinateGerm x hx he ℓ).symm

/-- For any nonzero continuous linear functional `ℓ` on `E`, the centered linear coordinate germ
along `ℓ` is irreducible in the holomorphic stalk. -/
theorem irreducible_holomorphicLinearCoordinateGerm {ℓ : StrongDual ℂ E} (hℓ : ℓ ≠ 0) :
    Irreducible (e.holomorphicLinearCoordinateGerm he x ℓ hx) := by
  have := e.isRegularLocalRing_holomorphicStalk he hx
  exact (e.prime_holomorphicLinearCoordinateGerm he hx hℓ).irreducible

end Prime

end OpenPartialHomeomorph
