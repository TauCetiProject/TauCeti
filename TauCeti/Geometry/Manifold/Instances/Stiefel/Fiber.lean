/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Stiefel

/-!
# Orthonormal triples over a point of the sphere

An orthonormal triple `(p, u, v)` of a real inner product space `E` is a point `p` of the unit
sphere together with an orthonormal two-frame `(u, v)` of the orthogonal complement `p^⊥`, the
tangent space of the sphere at `p`. So the Stiefel manifold `V₃(E)` of orthonormal triples
(`TauCeti.stiefel E 3`) is the space of orthonormal tangent two-frames of the unit sphere, and its
fibre over `p` under the projection to the first vector is the Stiefel manifold `V₂(p^⊥)` of
orthonormal two-frames of `p^⊥`. This file provides the inclusion of that fibre.

## Main declarations

* `TauCeti.stiefelFrameIncl`: the inclusion `V₂(p^⊥) → V₃(E)`, `(u, v) ↦ (p, u, v)`.
* `TauCeti.range_stiefelFrameIncl`: its range is the fibre over `p` of the projection to the
  first vector.
* `TauCeti.stiefelFrameIncl_injective`: it is injective.
-/

public section

open Metric
open scoped RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (p : sphere (0 : E) 1)

/-- The inclusion `V₂(p^⊥) → V₃(E)`, `(u, v) ↦ (p, u, v)`, of the frames of the tangent space at
`p` as the fibre over `p` of the projection to the first vector. -/
def stiefelFrameIncl : C(stiefel (ℝ ∙ (p : E))ᗮ 2, stiefel E 3) where
  toFun x := ⟨![(p : E), ((x : Fin 2 → (ℝ ∙ (p : E))ᗮ) 0 : E),
      ((x : Fin 2 → (ℝ ∙ (p : E))ᗮ) 1 : E)], by
    obtain ⟨hu, hv, huv⟩ := mem_stiefel_two_iff.1 x.2
    set u := (x : Fin 2 → (ℝ ∙ (p : E))ᗮ) 0
    set v := (x : Fin 2 → (ℝ ∙ (p : E))ᗮ) 1
    have hu₁ : ‖(u : E)‖ = 1 := hu
    have hv₁ : ‖(v : E)‖ = 1 := hv
    have huv₁ : ⟪(u : E), (v : E)⟫ = 0 := (Submodule.coe_inner _ u v).symm.trans huv
    have hpu : ⟪(p : E), (u : E)⟫ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.1 u.2
    have hpv : ⟪(p : E), (v : E)⟫ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.1 v.2
    have hp : ‖(p : E)‖ = 1 := norm_eq_of_mem_sphere p
    refine mem_stiefel_iff.2 ⟨fun i => ?_, fun i j hij => ?_⟩
    · fin_cases i <;> simp [hp, hu₁, hv₁]
    · fin_cases i <;> fin_cases j <;>
        simp_all [real_inner_comm]⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_pi fun i => ?_) _
    fin_cases i
    · exact continuous_const
    · exact continuous_subtype_val.comp ((continuous_apply 0).comp continuous_subtype_val)
    · exact continuous_subtype_val.comp ((continuous_apply 1).comp continuous_subtype_val)

@[simp]
theorem coe_stiefelFrameIncl (x : stiefel (ℝ ∙ (p : E))ᗮ 2) :
    ((stiefelFrameIncl p x : stiefel E 3) : Fin 3 → E) =
      ![(p : E), ((x : Fin 2 → (ℝ ∙ (p : E))ᗮ) 0 : E), ((x : Fin 2 → (ℝ ∙ (p : E))ᗮ) 1 : E)] :=
  (rfl)

@[simp]
theorem stiefelProj_zero_stiefelFrameIncl (x : stiefel (ℝ ∙ (p : E))ᗮ 2) :
    stiefelProj E 3 0 (stiefelFrameIncl p x) = p :=
  Subtype.ext (by simp)

/-- The inclusion `V₂(p^⊥) → V₃(E)` is injective. -/
theorem stiefelFrameIncl_injective : Function.Injective (stiefelFrameIncl p) := by
  intro x y h
  have h' := congrArg Subtype.val h
  simp only [coe_stiefelFrameIncl] at h'
  refine Subtype.ext (funext fun i => Subtype.ext ?_)
  fin_cases i
  · exact congrFun h' 1
  · exact congrFun h' 2

/-- The frames of `p^⊥` are exactly the fibre over `p` of the projection `V₃(E) → Sⁿ` to the first
vector. -/
theorem range_stiefelFrameIncl : Set.range (stiefelFrameIncl p) = stiefelProj E 3 0 ⁻¹' {p} := by
  refine Set.Subset.antisymm (Set.range_subset_iff.2 fun x => by simp) fun y hy => ?_
  have hy0 : (y : Fin 3 → E) 0 = p := (coe_stiefelProj 0 y).symm.trans (congrArg Subtype.val hy)
  have hon := mem_stiefel_iff.1 y.2
  have hmem (i : Fin 3) (hi : i ≠ 0) : (y : Fin 3 → E) i ∈ (ℝ ∙ (p : E))ᗮ :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.2 (hy0 ▸ hon.2 hi.symm)
  refine ⟨⟨![⟨_, hmem 1 (by decide)⟩, ⟨_, hmem 2 (by decide)⟩], mem_stiefel_two_iff.2
    ⟨by simpa using hon.1 1, by simpa using hon.1 2,
      by simpa using hon.2 (by decide : (1 : Fin 3) ≠ 2)⟩⟩, ?_⟩
  refine Subtype.ext (funext fun i => ?_)
  fin_cases i
  · exact hy0.symm
  · rfl
  · rfl

end TauCeti
