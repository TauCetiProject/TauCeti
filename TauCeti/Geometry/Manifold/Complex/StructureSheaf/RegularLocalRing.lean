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
import TauCeti.Geometry.Manifold.Complex.Analytic
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
  · exact finrank_le_ringKrullDim_stalk x

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
theorem isRegular_ofFn_holomorphicLinearCoordinateGerm (e : OpenPartialHomeomorph X E)
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
