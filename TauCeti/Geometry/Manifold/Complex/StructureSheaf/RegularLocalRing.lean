/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Cotangent
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Dimension
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Noetherian
public import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay
import Mathlib.Algebra.Module.SpanRankOperations
import TauCeti.RingTheory.Regular.RegularSequence

/-!
# Regular holomorphic local rings and coordinate parameters

The local ring of holomorphic germs on a finite-dimensional complex manifold without boundary
is regular, of Krull dimension equal to the complex dimension of the model. Its maximal ideal
needs exactly that many generators. These statements combine the cotangent-space calculation,
Noetherianity and the dimension lower bound for holomorphic stalks.

Centered coordinates in any holomorphic chart form a regular sequence, not merely a generating
family of the maximal ideal. Thus successive coordinate equations are non-zero-divisors on the
successive quotients. This is the local algebra underlying smooth holomorphic zero sets.
The dimension and regularity statements also apply to the native complex-smooth sheaf stalks
through their canonical comparison with holomorphic germs.

## References

* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter II.
* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter II.
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
-- Normalize the generator count before expanding the maximal ideal as the kernel of evaluation.
@[simp↓]
theorem spanFinrank_maximalIdeal_stalk (x : X) :
    (maximalIdeal ((holomorphicStructureSheaf I X).presheaf.stalk x)).spanFinrank =
      Module.finrank ℂ E := by
  let : IsManifold I ω X := IsManifold.of_ne_zero ω one_ne_zero inferInstance
  -- Use a finite coordinate space in Type so this also covers models in higher universes.
  let V := Fin (Module.finrank ℂ E) → ℂ
  let e : E ≃L[ℂ] V := ContinuousLinearEquiv.ofFinrankEq (by simp [V])
  let σ := RingEquiv.ofBijective _ (stalkPullback_comp_extChartAt_bijective (I := I) x e)
  rw [← Ideal.spanFinrank_map_eq_of_ringEquiv σ.symm,
    map_ringEquiv_maximalIdeal, spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  simpa only [Function.comp_apply, V, Module.finrank_pi, Module.finrank_self, mul_one,
    Fintype.card_fin] using
    (OpenPartialHomeomorph.refl V).finrank_cotangentSpace_holomorphicStalk
      (e (extChartAt I x x)) (Set.mem_univ _)
      (StructureGroupoid.id_mem_maximalAtlas (contDiffGroupoid ω 𝓘(ℂ, V)))

/-- The holomorphic local ring at a point of a complex manifold has Krull dimension equal to
its complex dimension, including dimension zero. -/
@[simp]
theorem ringKrullDim_stalk (x : X) :
    ringKrullDim ((holomorphicStructureSheaf I X).presheaf.stalk x) =
      (Module.finrank ℂ E : WithBot ℕ∞) := by
  refine le_antisymm ?_ ?_
  · simpa only [spanFinrank_maximalIdeal_stalk] using
      ringKrullDim_le_spanFinrank_maximalIdeal
        ((holomorphicStructureSheaf I X).presheaf.stalk x)
  · let : IsManifold I ω X := IsManifold.of_ne_zero ω one_ne_zero inferInstance
    let V := Fin (Module.finrank ℂ E) → ℂ
    let e : E ≃L[ℂ] V := ContinuousLinearEquiv.ofFinrankEq (by simp [V])
    let σ := RingEquiv.ofBijective _ (stalkPullback_comp_extChartAt_bijective (I := I) x e)
    rw [← σ.ringKrullDim]
    simpa [V] using finrank_le_ringKrullDim_stalk_modelSpace (e (extChartAt I x x))

/-- Holomorphic stalks on finite-dimensional complex manifolds without boundary are regular
local rings. No global separation or countability hypothesis is required. -/
instance stalkIsRegularLocalRing (x : X) :
    IsRegularLocalRing ((holomorphicStructureSheaf I X).presheaf.stalk x) := by
  apply (isRegularLocalRing_iff _).2
  rw [spanFinrank_maximalIdeal_stalk, ringKrullDim_stalk]

/-- The Krull dimension of the native complex-smooth stalk is the complex dimension of the
model, under its canonical identification with holomorphic germs. -/
@[simp]
theorem ringKrullDim_smoothStalk (x : X) :
    ringKrullDim ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x) =
      (Module.finrank ℂ E : WithBot ℕ∞) := by
  rw [← (smoothStalkIso I X x).commRingCatIsoToRingEquiv.ringKrullDim, ringKrullDim_stalk]

/-- Native complex-smooth stalks are regular local rings via the holomorphic comparison. -/
instance smoothStalkIsRegularLocalRing (x : X) :
    IsRegularLocalRing ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x) :=
  IsRegularLocalRing.of_ringEquiv (smoothStalkIso I X x).commRingCatIsoToRingEquiv

end TauCeti.holomorphicStructureSheaf

namespace OpenPartialHomeomorph

open TauCeti TauCeti.holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) 1 X]

/-- Centered coordinates of a holomorphic chart, in any ordered basis, form a regular sequence
in the holomorphic local ring. In particular each coordinate is a non-zero-divisor after
quotienting by the preceding coordinates. -/
theorem isRegular_holomorphicLinearCoordinateGerm (e : OpenPartialHomeomorph X E)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) ω X) (x : X) (hx : x ∈ e.source)
    {n : ℕ} (b : Module.Basis (Fin n) ℂ E) :
    RingTheory.Sequence.IsRegular ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x)
      (List.ofFn fun i ↦ e.holomorphicLinearCoordinateGerm he x
        (LinearMap.toContinuousLinearMap (b.coord i)) hx) := by
  apply TauCeti.IsRegularLocalRing.isRegular_of_ofList_eq_maximalIdeal
  · rw [Ideal.ofList_ofFn, maximalIdeal_stalk]
    exact (e.ker_eval_eq_span_holomorphicLinearCoordinateGerm he b hx).symm
  · simp only [List.length_ofFn, spanFinrank_maximalIdeal_stalk]
    simpa only [Fintype.card_fin] using (Module.finrank_eq_card_basis b).symm.le

end OpenPartialHomeomorph
