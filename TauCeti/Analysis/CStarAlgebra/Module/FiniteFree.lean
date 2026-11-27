/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.Action
public import TauCeti.Analysis.CStarAlgebra.Module.Self

import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Automatic continuity on finitely generated free right Hilbert C⋆-modules

Over a unital C⋆-algebra `A`, `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` is a finitely generated free right Hilbert
`A`-module when `ι` is finite, identified with `ι → Aᵐᵒᵖ` via
`TauCeti.WithCStarModule.piOpLinearEquiv`. Every right `A`-linear map out of `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)`
into a right Hilbert `A`-module is continuous (`LinearMap.continuous_of_finite_pi_cstarModule`), and
by the closed graph theorem any right `A`-linear right inverse into `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` from a
complete right Hilbert `A`-module is also continuous
(`LinearMap.continuous_rightInverse_of_comp_eq_id_of_finite_pi_cstarModule`).

## Main declarations

* `LinearMap.continuous_of_finite_pi_cstarModule`: continuity of right `A`-linear maps out of
  `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` for finite `ι`.
* `LinearMap.continuous_rightInverse_of_comp_eq_id_of_finite_pi_cstarModule`: continuity of a right
  `A`-linear right inverse `E →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` for complete `E`.
-/

public section

open MulOpposite
open scoped WithCStarModule

namespace LinearMap

/-- For a split linear surjection `f ∘ₗ g = LinearMap.id`, the graph of `g` consists of pairs
`(x, y)` such that `f y = x` and `g (f y) = y`. -/
private theorem coe_graph_eq_of_comp_eq_id {R M N : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N] (f : N →ₗ[R] M) (g : M →ₗ[R] N)
    (hfg : f ∘ₗ g = LinearMap.id) :
    (g.graph : Set (M × N)) = {p : M × N | f p.2 = p.1 ∧ (g ∘ₗ f) p.2 = p.2} := by
  ext ⟨x, y⟩
  have hfg_apply (z : M) : f (g z) = z := LinearMap.congr_fun hfg z
  simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, Set.mem_ofPred_eq, LinearMap.comp_apply]
  exact ⟨fun h ↦ ⟨by rw [h, hfg_apply], by rw [h, hfg_apply]⟩, fun ⟨h1, h2⟩ ↦ by rw [← h1, h2]⟩

variable {A E : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [Module Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]

/-- Every right `A`-linear map out of a finitely generated free right Hilbert `A`-module
`C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` into a right Hilbert `A`-module is continuous. -/
theorem continuous_of_finite_pi_cstarModule {ι : Type*} [Finite ι]
    (f : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →ₗ[Aᵐᵒᵖ] E) : Continuous f := by
  let : IsBoundedSMul Aᵐᵒᵖ E := IsBoundedSMul.of_norm_smul_le CStarModule.norm_smul_le
  let e := TauCeti.WithCStarModule.piOpLinearEquiv A ι
  have he : Continuous e := continuous_pi fun i ↦
    (MulOpposite.continuous_op.comp ((continuous_apply i).comp
      (WithCStarModule.equivL ℂ (A := Aᵐᵒᵖ) (E := ι → A)).continuous)).congr
      fun w ↦ (WithCStarModule.piOpLinearEquiv_apply w i).symm
  exact ((f.comp e.symm.toLinearMap).continuous_on_pi.comp he).congr fun w ↦ by simp

/-- If `f : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →ₗ[Aᵐᵒᵖ] E` and `g : E →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` satisfy
`f ∘ₗ g = .id` on a complete right Hilbert `A`-module `E`, then `g` is continuous. -/
theorem continuous_rightInverse_of_comp_eq_id_of_finite_pi_cstarModule {ι : Type*} [Finite ι]
    [CompleteSpace E] (f : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →ₗ[Aᵐᵒᵖ] E)
    (g : E →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) (hfg : f ∘ₗ g = LinearMap.id) : Continuous g := by
  let : Fintype ι := Fintype.ofFinite ι
  have : IsScalarTower ℂ Aᵐᵒᵖ E := CStarModule.isScalarTower Aᵐᵒᵖ E
  have : IsScalarTower ℂ Aᵐᵒᵖ C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) := CStarModule.isScalarTower _ _
  let : NormedAddCommGroup E := NormedAddCommGroup.ofSeparation fun x ↦
    (CStarModule.norm_zero_iff Aᵐᵒᵖ x).mp
  refine (g.restrictScalars ℂ).continuous_of_isClosed_graph ?_
  rw [coe_graph_eq_of_comp_eq_id (f.restrictScalars ℂ) (g.restrictScalars ℂ)
    (LinearMap.ext fun z ↦ LinearMap.congr_fun hfg z)]
  exact (isClosed_eq (f.continuous_of_finite_pi_cstarModule.comp continuous_snd)
    continuous_fst).inter (isClosed_eq
      ((g ∘ₗ f).continuous_of_finite_pi_cstarModule.comp continuous_snd) continuous_snd)

end LinearMap
