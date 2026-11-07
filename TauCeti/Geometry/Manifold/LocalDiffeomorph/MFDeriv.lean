/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Differentials of a partial diffeomorphism

The differentials of a partial diffeomorphism and of its inverse are mutually inverse at
corresponding points, as for a global diffeomorphism
(`Diffeomorph.mfderiv_symm_apply_mfderiv_apply`), and on the open source of a partial
diffeomorphism the differential within the source is the differential.

## Main results

* `PartialDiffeomorph.mfderivWithin_source`: the differential within the source is the differential.
* `PartialDiffeomorph.mfderiv_symm_apply_mfderiv_apply`: the differential of the inverse undoes the
  differential.
* `PartialDiffeomorph.mfderiv_apply_mfderiv_symm_apply`: the differential undoes the differential of
  the inverse.
-/

public section

open Filter
open scoped Manifold Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : WithTop ℕ∞}

namespace PartialDiffeomorph

/-- On the open source of a partial diffeomorphism the differential within the source is the
differential. -/
theorem mfderivWithin_source (Φ : PartialDiffeomorph I J M N n)
    {x : M} (hx : x ∈ Φ.source) : mfderivWithin I J Φ Φ.source x = mfderiv I J Φ x :=
  mfderivWithin_of_isOpen Φ.open_source hx

/-- The differential of the inverse of a partial diffeomorphism undoes its differential. -/
theorem mfderiv_symm_apply_mfderiv_apply (Φ : PartialDiffeomorph I J M N n) (hn : n ≠ 0) {x : M}
    (hx : x ∈ Φ.source) (v : TangentSpace I x) :
    mfderiv J I Φ.symm (Φ x) (mfderiv I J Φ x v) = v := by
  have hcomp := mfderiv_comp x (Φ.symm.mdifferentiableAt hn (Φ.map_source hx))
    (Φ.mdifferentiableAt hn hx)
  have heq : (Φ.symm ∘ Φ : M → M) =ᶠ[𝓝 x] id :=
    eventually_of_mem (Φ.open_source.mem_nhds hx) fun z hz ↦ Φ.left_inv hz
  rw [heq.mfderiv_eq, mfderiv_id] at hcomp
  exact (DFunLike.congr_fun hcomp v).symm

/-- The differential of a partial diffeomorphism undoes the differential of its inverse. -/
theorem mfderiv_apply_mfderiv_symm_apply (Φ : PartialDiffeomorph I J M N n) (hn : n ≠ 0) {y : N}
    (hy : y ∈ Φ.target) (v : TangentSpace J y) :
    mfderiv I J Φ (Φ.symm y) (mfderiv J I Φ.symm y v) = v :=
  Φ.symm.mfderiv_symm_apply_mfderiv_apply hn hy v

end PartialDiffeomorph
