/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import TauCeti.Analysis.CStarAlgebra.Module.Action
public import TauCeti.Analysis.CStarAlgebra.Module.Synonym

import TauCeti.Analysis.CStarAlgebra.Module.Self
import TauCeti.LinearAlgebra.Prod

/-!
# Automatic continuity on finitely generated free right Hilbert C⋆-modules

* Every linear map out of `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` into any topological right `A`-module
  (`[ContinuousAdd E] [ContinuousSMul Aᵐᵒᵖ E]`) over a uniform ring `[Ring A] [UniformSpace A]`
  with finite `ι` is continuous (`LinearMap.continuous_of_finite_pi_cstarModule`).
* Between Banach spaces, any linear right inverse `g` of a continuous linear map `f`
  (`f ∘ₗ g = .id`) for which `g ∘ₗ f` is continuous is itself continuous
  (`LinearMap.continuous_rightInverse_of_comp_eq_id`).
* Specializing to `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` over a C⋆-algebra `A` yields automatic continuity of any
  right `A`-linear right inverse from a complete right Hilbert `A`-module
  (`LinearMap.continuous_rightInverse_of_comp_eq_id_of_finite_pi_cstarModule`).

## Main declarations

* `LinearMap.continuous_of_finite_pi_cstarModule`: continuity of right `A`-linear maps out of
  `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` for finite `ι` over `[Ring A] [UniformSpace A]`.
* `LinearMap.continuous_rightInverse_of_comp_eq_id`: closed-graph continuity of a linear right
  inverse `g` (`f ∘ₗ g = .id`) between Banach spaces when `f` and `g ∘ₗ f` are continuous.
* `LinearMap.continuous_rightInverse_of_comp_eq_id_of_finite_pi_cstarModule`: continuity of a right
  `A`-linear right inverse `E →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` for complete `E`.
-/

public section

open MulOpposite
open scoped WithCStarModule

namespace LinearMap

/-- Every right `A`-linear map out of a finitely generated free module `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)`
(with finite `ι`) over a uniform ring into a topological right `A`-module is continuous. -/
theorem continuous_of_finite_pi_cstarModule {A E ι : Type*} [Ring A] [UniformSpace A]
    [AddCommMonoid E] [Module Aᵐᵒᵖ E] [TopologicalSpace E] [ContinuousAdd E]
    [ContinuousSMul Aᵐᵒᵖ E] [Finite ι] (f : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →ₗ[Aᵐᵒᵖ] E) : Continuous f := by
  let e := TauCeti.WithCStarModule.piOpLinearEquiv A ι
  have he : Continuous e := continuous_pi fun i ↦
    (MulOpposite.continuous_op.comp ((continuous_apply i).comp
      (WithCStarModule.equivL Aᵐᵒᵖ (A := Aᵐᵒᵖ) (E := ι → A)).continuous)).congr
      fun w ↦ (TauCeti.WithCStarModule.piOpLinearEquiv_apply w i).symm
  exact ((f.comp e.symm.toLinearMap).continuous_on_pi.comp he).congr fun w ↦ by simp

/-- Between Banach spaces, if `f ∘ₗ g = LinearMap.id`, `f` is continuous, and `g ∘ₗ f` is
continuous, then the right inverse `g` is continuous by the closed graph theorem. -/
theorem continuous_rightInverse_of_comp_eq_id {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (g : E →ₗ[𝕜] F) (f : F →ₗ[𝕜] E) (hfg : f ∘ₗ g = LinearMap.id)
    (hf : Continuous f) (hgf : Continuous (g ∘ₗ f)) : Continuous g := by
  refine g.continuous_of_isClosed_graph ?_
  rw [g.coe_graph_eq_of_comp_eq_id f hfg]
  exact (isClosed_eq (hf.comp continuous_snd) continuous_fst).inter
    (isClosed_eq (hgf.comp continuous_snd) continuous_snd)

/-- If `f : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →ₗ[Aᵐᵒᵖ] E` and `g : E →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` satisfy
`f ∘ₗ g = .id` on a complete right Hilbert `A`-module `E`, then `g` is continuous. -/
theorem continuous_rightInverse_of_comp_eq_id_of_finite_pi_cstarModule {A E ι : Type*}
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [SeminormedAddCommGroup E] [NormedSpace ℂ E] [Module Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]
    [CompleteSpace E] [Finite ι] (f : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →ₗ[Aᵐᵒᵖ] E)
    (g : E →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) (hfg : f ∘ₗ g = LinearMap.id) : Continuous g := by
  let : Fintype ι := Fintype.ofFinite ι
  have : IsScalarTower ℂ Aᵐᵒᵖ E := CStarModule.isScalarTower Aᵐᵒᵖ E
  have : IsScalarTower ℂ Aᵐᵒᵖ C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) := CStarModule.isScalarTower _ _
  let : NormedAddCommGroup E := TauCeti.CStarModule.normedAddCommGroupOfCStarModule Aᵐᵒᵖ E
  let : IsBoundedSMul Aᵐᵒᵖ E := IsBoundedSMul.of_norm_smul_le CStarModule.norm_smul_le
  let : IsBoundedSMul Aᵐᵒᵖ C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) :=
    IsBoundedSMul.of_norm_smul_le CStarModule.norm_smul_le
  exact (g.restrictScalars ℂ).continuous_rightInverse_of_comp_eq_id (f.restrictScalars ℂ)
    (LinearMap.ext fun z ↦ LinearMap.congr_fun hfg z) f.continuous_of_finite_pi_cstarModule
    (g ∘ₗ f).continuous_of_finite_pi_cstarModule

end LinearMap
