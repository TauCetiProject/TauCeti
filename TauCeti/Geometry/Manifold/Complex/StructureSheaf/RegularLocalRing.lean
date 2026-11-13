/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Cotangent
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Noetherian

import Mathlib.Algebra.Module.SpanRankOperations
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Dimension
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.StalkPullback
import TauCeti.RingTheory.Regular.RegularSequence
import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay

/-!
# Holomorphic stalks are regular local rings

At any point `x` of a finite-dimensional complex manifold `X` without boundary modelled on `E`, the
stalk `𝒪_{X, x}` of holomorphic germs is a regular local ring whose Krull dimension, maximal-ideal
minimal generator count, and residue-field cotangent dimension all equal `finrank ℂ E`.

On a complex normed model space `V`, differentiating germs at `x` identifies the algebraic
cotangent space `𝔪 / 𝔪²` with `StrongDual ℂ V` over the residue field, while coordinate hyperplane
restrictions bound the Krull dimension from below by `finrank ℂ V`. Since `𝒪_{V, x}` is Noetherian,
the minimal number of generators of `𝔪` equals the cotangent dimension `finrank ℂ V`, matching the
Krull dimension lower bound. Local analytic chart pullbacks transport regularity and dimension to
every holomorphic chart and every boundaryless complex manifold, and the holomorphic/complex-smooth
stalk comparison transfers them to Mathlib's complex-smooth structure sheaf.

In any holomorphic chart at `x` and for any `Fin n`-indexed basis of `E`, the centered linear
coordinate germs generate the maximal ideal in `finrank ℂ E` elements and therefore form a regular
sequence (a regular system of parameters) on `𝒪_{X, x}`.

## Main declarations

* `TauCeti.holomorphicStructureSheaf.stalkIsRegularLocalRing`,
  `TauCeti.holomorphicStructureSheaf.smoothStalkIsRegularLocalRing`: stalks of the holomorphic and
  complex-smooth structure sheaves are regular local rings.
* `TauCeti.holomorphicStructureSheaf.ringKrullDim_stalk`,
  `TauCeti.holomorphicStructureSheaf.spanFinrank_maximalIdeal_stalk`,
  `TauCeti.holomorphicStructureSheaf.finrank_cotangentSpace_stalk` (and their `smoothStalk`
  counterparts): the Krull dimension, maximal-ideal generator count, and cotangent dimension equal
  `Module.finrank ℂ E`.
* `OpenPartialHomeomorph.isRegularLocalRing_holomorphicStalk`,
  `OpenPartialHomeomorph.isRegular_ofFn_holomorphicLinearCoordinateGerm`,
  `OpenPartialHomeomorph.prime_holomorphicLinearCoordinateGerm`,
  `OpenPartialHomeomorph.irreducible_holomorphicLinearCoordinateGerm`: in the domain of any
  holomorphic chart, the stalk is a regular local ring, centered basis coordinate germs form a
  regular sequence, and any nonzero centered linear coordinate germ is prime and irreducible.

## References

* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter II, §2.
* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter II.
* H. Grauert and R. Remmert, *Coherent Analytic Sheaves*, Chapter 2.
-/

public noncomputable section

open Filter IsLocalRing IsManifold Module Topology
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

section ModelSpace

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

private theorem spanFinrank_maximalIdeal_stalk_modelSpace (x : V) :
    (maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk x)).spanFinrank =
      finrank ℂ V := by
  rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  exact (chartAt V x).finrank_cotangentSpace_holomorphicStalk x (mem_chart_source V x)
    (chart_mem_maximalAtlas x)

private theorem isRegularLocalRing_stalk_modelSpace (x : V) :
    IsRegularLocalRing ((holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk x) := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [spanFinrank_maximalIdeal_stalk_modelSpace x]
  exact finrank_le_ringKrullDim_stalk_modelSpace x

end ModelSpace

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

private theorem exists_stalk_ringEquiv_modelSpace (x : X) :
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : NormedSpace ℂ V) (_ : FiniteDimensional ℂ V)
      (v : V), finrank ℂ V = finrank ℂ E ∧
        Nonempty (((holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk v) ≃+*
          (holomorphicStructureSheaf I X).presheaf.stalk x) := by
  let : IsManifold I ω X := IsManifold.of_ne_zero ω one_ne_zero inferInstance
  let L : E ≃L[ℂ] Fin (finrank ℂ E) → ℂ := ContinuousLinearEquiv.ofFinrankEq (by simp)
  exact ⟨Fin (finrank ℂ E) → ℂ, inferInstance, inferInstance, inferInstance,
    (L ∘ extChartAt I x) x, by simp,
    ⟨RingEquiv.ofBijective _ (stalkPullback_comp_extChartAt_bijective x L)⟩⟩

/-- The stalk of holomorphic functions at any point of a finite-dimensional complex manifold
without boundary is a regular local ring. -/
instance stalkIsRegularLocalRing (x : X) :
    IsRegularLocalRing ((holomorphicStructureSheaf I X).presheaf.stalk x) := by
  obtain ⟨V, _, _, _, v, -, ⟨φ⟩⟩ := exists_stalk_ringEquiv_modelSpace (I := I) x
  have := isRegularLocalRing_stalk_modelSpace v
  exact IsRegularLocalRing.of_ringEquiv φ

/-- The minimal number of generators of the maximal ideal of a holomorphic stalk equals the complex
dimension of the model space. -/
theorem spanFinrank_maximalIdeal_stalk (x : X) :
    (maximalIdeal ((holomorphicStructureSheaf I X).presheaf.stalk x)).spanFinrank =
      finrank ℂ E := by
  obtain ⟨V, _, _, _, v, hV, ⟨φ⟩⟩ := exists_stalk_ringEquiv_modelSpace (I := I) x
  rw [← map_ringEquiv_maximalIdeal φ, Ideal.spanFinrank_map_eq_of_ringEquiv,
    spanFinrank_maximalIdeal_stalk_modelSpace, hV]

/-- The Krull dimension of the holomorphic stalk at any point of a finite-dimensional complex
manifold without boundary equals the complex dimension of its model space. -/
theorem ringKrullDim_stalk (x : X) :
    ringKrullDim ((holomorphicStructureSheaf I X).presheaf.stalk x) = finrank ℂ E := by
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal, spanFinrank_maximalIdeal_stalk]

/-- The dimension of the algebraic cotangent space of a holomorphic stalk over its residue field
equals the complex dimension of the model space. -/
theorem finrank_cotangentSpace_stalk (x : X) :
    finrank (ResidueField ((holomorphicStructureSheaf I X).presheaf.stalk x))
      (CotangentSpace ((holomorphicStructureSheaf I X).presheaf.stalk x)) = finrank ℂ E := by
  rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, spanFinrank_maximalIdeal_stalk]

/-- A stalk of Mathlib's complex-smooth structure sheaf on a finite-dimensional complex manifold
without boundary is a regular local ring, via its comparison with holomorphic germs. -/
instance smoothStalkIsRegularLocalRing (x : X) :
    IsRegularLocalRing ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x) :=
  IsRegularLocalRing.of_ringEquiv (smoothStalkIso I X x).commRingCatIsoToRingEquiv

/-- The minimal number of generators of the maximal ideal of a complex-smooth structure-sheaf stalk
equals the complex dimension of the model space. -/
theorem spanFinrank_maximalIdeal_smoothStalk (x : X) :
    (maximalIdeal ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x)).spanFinrank =
      finrank ℂ E := by
  let e := (smoothStalkIso I X x).commRingCatIsoToRingEquiv
  rw [← map_ringEquiv_maximalIdeal e, Ideal.spanFinrank_map_eq_of_ringEquiv,
    spanFinrank_maximalIdeal_stalk]

/-- The Krull dimension of a complex-smooth structure-sheaf stalk on a finite-dimensional complex
manifold without boundary equals the complex dimension of its model space. -/
theorem ringKrullDim_smoothStalk (x : X) :
    ringKrullDim ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x) = finrank ℂ E := by
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal, spanFinrank_maximalIdeal_smoothStalk]

/-- The dimension of the algebraic cotangent space of a complex-smooth structure-sheaf stalk over
its residue field equals the complex dimension of the model space. -/
theorem finrank_cotangentSpace_smoothStalk (x : X) :
    finrank (ResidueField ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x))
      (CotangentSpace ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x)) = finrank ℂ E := by
  rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, spanFinrank_maximalIdeal_smoothStalk]

end Manifold

end TauCeti.holomorphicStructureSheaf

namespace OpenPartialHomeomorph

open TauCeti TauCeti.holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  (e : OpenPartialHomeomorph X E) (he : e ∈ maximalAtlas 𝓘(ℂ, E) ω X) {x : X} (hx : x ∈ e.source)

include he hx in
/-- At any point in the domain of a holomorphic chart into a finite-dimensional complex normed
space `E`, the holomorphic stalk is a regular local ring, without assuming a global manifold
structure on `X`. -/
theorem isRegularLocalRing_holomorphicStalk :
    IsRegularLocalRing ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x) := by
  let L : E ≃L[ℂ] Fin (finrank ℂ E) → ℂ := ContinuousLinearEquiv.ofFinrankEq (by simp)
  have := isRegularLocalRing_stalk_modelSpace (L (e x))
  exact IsRegularLocalRing.of_ringEquiv
    (RingEquiv.ofBijective _ (e.holomorphicStalkPullback_comp_bijective he hx L))

include he hx in
/-- At any point in the domain of a holomorphic chart into `E`, the minimal number of generators of
the maximal ideal of the holomorphic stalk equals `finrank ℂ E`. -/
theorem spanFinrank_maximalIdeal_holomorphicStalk :
    (maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x)).spanFinrank =
      finrank ℂ E := by
  have := e.isRegularLocalRing_holomorphicStalk he hx
  rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  exact e.finrank_cotangentSpace_holomorphicStalk x hx he

include he hx in
/-- At any point in the domain of a holomorphic chart into `E`, the Krull dimension of the
holomorphic stalk equals `finrank ℂ E`. -/
theorem ringKrullDim_holomorphicStalk :
    ringKrullDim ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x) = finrank ℂ E := by
  have := e.isRegularLocalRing_holomorphicStalk he hx
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal,
    e.spanFinrank_maximalIdeal_holomorphicStalk he hx]

/-- **Holomorphic coordinates form a regular sequence.** At any point in the domain of a
holomorphic chart into `E` and for any `Fin n`-indexed basis `b` of `E`, the centered linear
coordinate germs along `b` form a regular sequence (a regular system of parameters) on the
holomorphic stalk. -/
theorem isRegular_ofFn_holomorphicLinearCoordinateGerm {n : ℕ} (b : Module.Basis (Fin n) ℂ E) :
    RingTheory.Sequence.IsRegular ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x)
      (List.ofFn fun i ↦
        e.holomorphicLinearCoordinateGerm he x
          (LinearMap.toContinuousLinearMap (b.coord i)) hx) := by
  have := e.isRegularLocalRing_holomorphicStalk he hx
  apply TauCeti.IsRegularLocalRing.isRegular_of_ofList_eq_maximalIdeal
  · rw [Ideal.ofList_ofFn, maximalIdeal_stalk,
      e.ker_eval_eq_span_holomorphicLinearCoordinateGerm he b hx]
  · rw [List.length_ofFn, e.spanFinrank_maximalIdeal_holomorphicStalk he hx,
      finrank_eq_card_basis b, Fintype.card_fin]

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

end OpenPartialHomeomorph
