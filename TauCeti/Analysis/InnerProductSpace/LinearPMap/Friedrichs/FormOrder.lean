/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Friedrichs.Basic
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Embedding of Friedrichs form completions for `S ≤ T`

Let `S ≤ T` be partial linear operators on a Hilbert space `E`, both symmetric with the same lower
bound `γ`. The form completion `LinearPMap.FriedrichsSpace` of `S` embeds isometrically into that
of `T` (`LinearPMap.friedrichsSpaceMap`): on the domain of `S`, the form inner products
`⟪S x, y⟫ + (1 - γ) ⟪x, y⟫` and `⟪T x, y⟫ + (1 - γ) ⟪x, y⟫` agree
(`LinearPMap.FriedrichsPre.inner_ofDomain_inclusion`). The embedding is compatible with the
inclusions into `E` and carries the closed form of `S` to that of `T`.

Informal consequence, not formalized here: no declaration in this file mentions
`LinearPMap.friedrichsExtension` or self-adjointness. Suppose in addition that `T` is densely
defined and self-adjoint with the same lower bound `γ` as `S`. Then `T` is its own Friedrichs
extension (`LinearPMap.eq_friedrichsExtension_of_isSelfAdjoint` applied to `T ≤ T`), so its
closed form `q_T` is `LinearPMap.friedrichsForm` of `T`. Through this identification the
results here say that `T ≤ S_F` in form order for the Friedrichs extension `S_F` of `S`: the form
domain of `S_F` lies in that of `T` (`LinearPMap.range_friedrichsInclusion_subset`), and
`q_T = q_(S_F)` on it (`LinearPMap.friedrichsForm_friedrichsSpaceMap`). This is the form-order
step towards the extremal property of the Friedrichs extension (Krein's theorem), which is
usually stated for all semibounded self-adjoint extensions, without the same-`γ` restriction.

## Main declarations

* `LinearPMap.friedrichsSpaceMap`: the isometric embedding of form completions for `S ≤ T`.
* `LinearPMap.friedrichsInclusion_friedrichsSpaceMap`: it commutes with the inclusions into `E`.
* `LinearPMap.friedrichsForm_friedrichsSpaceMap`: it carries the closed form of `S` to that of
  `T`.
* `LinearPMap.range_friedrichsInclusion_subset`: the form domain of `S` lies in that of `T`.

## References

* M. G. Krein, *The theory of self-adjoint extensions of semi-bounded Hermitian transformations
  and its applications. I*, Mat. Sb. 20(62) (1947), 431-495.
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Springer GTM 265 (2012),
  Chapter 10, §10.3 (form order) and §10.4 (the Friedrichs extension).
* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1995), Chapter VI, §2.3.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace LinearPMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {S T : E →ₗ.[𝕜] E} {γ : ℝ} (hS : S.IsSymmetricBoundedBelow γ) (hT : T.IsSymmetricBoundedBelow γ)

namespace FriedrichsPre

/-- For `S ≤ T`, the form inner products of `S` and `T` agree on the domain of `S`. -/
theorem inner_ofDomain_inclusion (hST : S ≤ T) (x y : FriedrichsPre S γ hS) :
    ⟪(ofDomain (Submodule.inclusion hST.1 x.toDomain) : FriedrichsPre T γ hT),
      ofDomain (Submodule.inclusion hST.1 y.toDomain)⟫_𝕜 = ⟪x, y⟫_𝕜 := by
  rw [inner_def, inner_def, toDomain_ofDomain, toDomain_ofDomain,
    ← hST.2 (x := x.toDomain) (y := Submodule.inclusion hST.1 x.toDomain) rfl,
    Submodule.coe_inclusion, Submodule.coe_inclusion]

/-- For `S ≤ T`, the inclusion of the domain of `S` into that of `T`, as a linear isometry of the
form pre-Hilbert spaces. -/
def mapOfLE (hST : S ≤ T) : FriedrichsPre S γ hS →ₗᵢ[𝕜] FriedrichsPre T γ hT :=
  LinearMap.isometryOfInner
    { toFun x := ofDomain (Submodule.inclusion hST.1 x.toDomain)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    (inner_ofDomain_inclusion hS hT hST)

/-- `FriedrichsPre.mapOfLE` keeps the underlying vector. -/
@[simp]
theorem toDomain_mapOfLE (hST : S ≤ T) (x : FriedrichsPre S γ hS) :
    ((mapOfLE hS hT hST x).toDomain : E) = x.toDomain :=
  (rfl)

end FriedrichsPre

/-- For `S ≤ T` with the same lower bound, the **isometric embedding of form completions**
`FriedrichsSpace S → FriedrichsSpace T`, extending the inclusion of the domain of `S` into that of
`T`. -/
def friedrichsSpaceMap (hST : S ≤ T) : FriedrichsSpace S γ hS →ₗᵢ[𝕜] FriedrichsSpace T γ hT :=
  (UniformSpace.Completion.toComplₗᵢ.comp (FriedrichsPre.mapOfLE hS hT hST)).fromCompletion

/-- On `FriedrichsPre S`, the embedding of form completions is `FriedrichsPre.mapOfLE`. -/
@[simp]
theorem friedrichsSpaceMap_coe (hST : S ≤ T) (y : FriedrichsPre S γ hS) :
    friedrichsSpaceMap hS hT hST y = (FriedrichsPre.mapOfLE hS hT hST y : FriedrichsSpace T γ hT) :=
  LinearIsometry.fromCompletion_apply_coe _ _

/-- On the domain of `S`, the embedding of form completions is the inclusion of domains. -/
@[simp]
theorem friedrichsSpaceMap_toFriedrichsSpace (hST : S ≤ T) (x : S.domain) :
    friedrichsSpaceMap hS hT hST (toFriedrichsSpace hS x) =
      toFriedrichsSpace hT (Submodule.inclusion hST.1 x) := by
  rw [toFriedrichsSpace_apply, toFriedrichsSpace_apply, friedrichsSpaceMap_coe]
  exact congrArg _ <| FriedrichsPre.ext <| Subtype.ext <| by simp

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
theorem range_friedrichsInclusion_subset (hST : S ≤ T) :
    Set.range (friedrichsInclusion hS) ⊆ Set.range (friedrichsInclusion hT) := by
  rintro _ ⟨u, rfl⟩
  exact ⟨_, friedrichsInclusion_friedrichsSpaceMap hS hT hST u⟩

/-- **The closed forms agree on the smaller form domain**: for `S ≤ T` with the same lower bound,
the closed form of `T` restricted to the form completion of `S` is the closed form of `S`. -/
@[simp]
theorem friedrichsForm_friedrichsSpaceMap (hST : S ≤ T) (u v : FriedrichsSpace S γ hS) :
    friedrichsForm hT (friedrichsSpaceMap hS hT hST u) (friedrichsSpaceMap hS hT hST v) =
      friedrichsForm hS u v := by
  rw [friedrichsForm_apply, friedrichsForm_apply, LinearIsometry.inner_map_map,
    friedrichsInclusion_friedrichsSpaceMap, friedrichsInclusion_friedrichsSpaceMap]

end LinearPMap
