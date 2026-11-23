/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Friedrichs

/-!
# The Friedrichs extension is minimal in form order

Let `S ≤ T` be partial linear operators on a Hilbert space `E`, both symmetric with the same lower
bound `γ`. The form completion `LinearPMap.FriedrichsSpace` of `S` embeds isometrically into that
of `T` (`LinearPMap.friedrichsSpaceMap`): on the domain of `S`, the form inner products
`⟪S x, y⟫ + (1 - γ) ⟪x, y⟫` and `⟪T x, y⟫ + (1 - γ) ⟪x, y⟫` agree. The embedding is compatible with
the inclusions into `E` and carries the closed form of `S` to that of `T`.

When `T` is self-adjoint it is its own Friedrichs extension
(`LinearPMap.eq_friedrichsExtension_self`), so its closed form `q_T` is `LinearPMap.friedrichsForm`
of `T`. The embedding then says that `T ≤ S_F` in form order, for the Friedrichs extension `S_F`
of `S`: the form domain of `S_F` lies in that of `T`
(`LinearPMap.range_friedrichsInclusion_le`), and `q_T = q_(S_F)` on it
(`LinearPMap.friedrichsForm_friedrichsSpaceMap`). This is the form-order half of the extremal
property of the Friedrichs extension (Krein's theorem).

## Main declarations

* `LinearPMap.friedrichsSpaceMap`: the isometric embedding of form completions for `S ≤ T`.
* `LinearPMap.friedrichsInclusion_friedrichsSpaceMap`: it commutes with the inclusions into `E`.
* `LinearPMap.friedrichsForm_friedrichsSpaceMap`: it carries the closed form of `S` to that of
  `T`.
* `LinearPMap.range_friedrichsInclusion_le`: the form domain of `S` lies in that of `T`.
* `LinearPMap.eq_friedrichsExtension_self`: a densely defined self-adjoint operator with lower
  bound `γ` is its own Friedrichs extension.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace LinearPMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {S T : E →ₗ.[𝕜] E} {γ : ℝ} (hS : S.IsSymmetricBoundedBelow γ) (hT : T.IsSymmetricBoundedBelow γ)

namespace FriedrichsPre

/-- For `S ≤ T`, the inclusion of the domain of `S` into that of `T`, as a linear isometry of the
form pre-Hilbert spaces. -/
def mapOfLE (hST : S ≤ T) : FriedrichsPre S γ hS →ₗᵢ[𝕜] FriedrichsPre T γ hT where
  toFun x := ofDomain (Submodule.inclusion hST.1 x.toDomain)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' x := by
    rw [norm_eq_sqrt_re_inner (𝕜 := 𝕜), norm_eq_sqrt_re_inner (𝕜 := 𝕜), inner_def, inner_def,
      hST.2 (x := x.toDomain) (y := Submodule.inclusion hST.1 x.toDomain) rfl]
    rfl

@[simp]
theorem toDomain_mapOfLE (hST : S ≤ T) (x : FriedrichsPre S γ hS) :
    ((mapOfLE hS hT hST x).toDomain : E) = x.toDomain :=
  (rfl)

end FriedrichsPre

/-- For `S ≤ T` with the same lower bound, the **isometric embedding of form completions**
`FriedrichsSpace S → FriedrichsSpace T`, extending the inclusion of the domain of `S` into that of
`T`. -/
def friedrichsSpaceMap (hST : S ≤ T) : FriedrichsSpace S γ hS →ₗᵢ[𝕜] FriedrichsSpace T γ hT where
  toLinearMap := (FriedrichsPre.mapOfLE hS hT hST).toContinuousLinearMap.completion.toLinearMap
  norm_map' u := by
    induction u using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) continuous_norm
    | ih x =>
      simp [ContinuousLinearMap.completion_apply_coe, UniformSpace.Completion.norm_coe]

/-- On the domain of `S`, the embedding of form completions is the inclusion of domains. -/
@[simp]
theorem friedrichsSpaceMap_toFriedrichsSpace (hST : S ≤ T) (x : S.domain) :
    friedrichsSpaceMap hS hT hST (toFriedrichsSpace hS x) =
      toFriedrichsSpace hT (Submodule.inclusion hST.1 x) := by
  simp only [friedrichsSpaceMap, toFriedrichsSpace_apply]
  exact ContinuousLinearMap.completion_apply_coe _ _

variable [CompleteSpace E]

/-- The embedding of form completions commutes with the inclusions into `E`. -/
@[simp]
theorem friedrichsInclusion_friedrichsSpaceMap (hST : S ≤ T) (u : FriedrichsSpace S γ hS) :
    friedrichsInclusion hT (friedrichsSpaceMap hS hT hST u) = friedrichsInclusion hS u := by
  refine (denseRange_toFriedrichsSpace hS).induction_on u
    (isClosed_eq (by fun_prop) (by fun_prop)) fun x ↦ ?_
  simp

/-- **The form domain of `S` lies in the form domain of `T`** for `S ≤ T` with the same lower
bound. -/
theorem range_friedrichsInclusion_le (hST : S ≤ T) :
    Set.range (friedrichsInclusion hS) ⊆ Set.range (friedrichsInclusion hT) := by
  rintro _ ⟨u, rfl⟩
  exact ⟨_, friedrichsInclusion_friedrichsSpaceMap hS hT hST u⟩

/-- **The closed forms agree on the smaller form domain**: for `S ≤ T` with the same lower bound,
the closed form of `T` restricted to the form completion of `S` is the closed form of `S`. -/
theorem friedrichsForm_friedrichsSpaceMap (hST : S ≤ T) (u v : FriedrichsSpace S γ hS) :
    friedrichsForm hT (friedrichsSpaceMap hS hT hST u) (friedrichsSpaceMap hS hT hST v) =
      friedrichsForm hS u v := by
  rw [friedrichsForm_apply, friedrichsForm_apply, LinearIsometry.inner_map_map,
    friedrichsInclusion_friedrichsSpaceMap, friedrichsInclusion_friedrichsSpaceMap]

/-- **A self-adjoint operator is its own Friedrichs extension.** A densely defined self-adjoint
operator `T` with lower bound `γ` equals the Friedrichs extension of `T` itself, so its closed form
is `LinearPMap.friedrichsForm` of `T`. -/
theorem eq_friedrichsExtension_self (hdense : Dense (T.domain : Set E)) (hT' : IsSelfAdjoint T) :
    T = friedrichsExtension hT hdense :=
  eq_friedrichsExtension_of_isSelfAdjoint hT hdense hT' le_rfl fun x ↦
    ⟨toFriedrichsSpace hT x, friedrichsInclusion_toFriedrichsSpace hT x⟩

end LinearPMap
