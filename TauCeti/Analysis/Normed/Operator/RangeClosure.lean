/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Extend
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# The closure of the range of a linear map, and extensions of operators to it

Let `R : D →ₗ[𝕜] H` be a linear map from a vector space `D` without topology to a normed space
`H`. The closure of its range (`LinearMap.rangeClosure`) is a closed subspace of `H`, hence a
Banach space when `H` is, in which the elements `R u` (`LinearMap.toRangeClosure`) are dense. This
is how a space of smooth objects `D`, measured by the norm `‖R u‖`, is completed inside a known
Banach space: Sobolev spaces of functions and of sections on a compact manifold are of this form,
with `R` the chart readings.

A linear map `P : D →ₗ[𝕜] D'` satisfying an a priori estimate `‖R' (P u)‖ ≤ C ‖R u‖` extends by
continuity to a continuous linear map between the closures (`LinearMap.rangeClosureExtension`).
The extension is unique, and extensions add and compose. Two linear maps `R`, `R'` out of `D`
controlling each other give isomorphic closures (`LinearMap.rangeClosureCongr`).

## Main definitions

* `LinearMap.rangeClosure`: the closure of the range of `R`.
* `LinearMap.toRangeClosure`: `R` with codomain restricted to the closure of its range.
* `LinearMap.rangeClosureMap`: the restriction to the closures of a continuous linear map `T`
  with `T ∘ R = R'`.
* `LinearMap.rangeClosureExtension`: the continuous extension of `P : D →ₗ[𝕜] D'` from the
  closure of the range of `R` to that of `R'`.
* `LinearMap.rangeClosureCongr`: the isomorphism between the closures of two linear maps that
  control each other.

## Main results

* `LinearMap.denseRange_toRangeClosure`: the elements `R u` are dense in the closure.
* `LinearMap.norm_rangeClosureMap_le`, `LinearMap.rangeClosureMap_injective`: the restriction of a
  map `T` to the closures has operator norm at most `‖T‖`, and it is injective when `T` is.
* `LinearMap.denseRange_rangeClosureMap`: the restriction of a map between the closures has dense
  range.
* `LinearMap.rangeClosure_ext`: a continuous linear map out of the closure is determined by its
  values on the elements `R u`.
* `LinearMap.rangeClosureExtension_toRangeClosure`, `LinearMap.rangeClosureExtension_eq`: the
  extension of a map satisfying an a priori estimate agrees with it, and is the only continuous
  map that does; `LinearMap.rangeClosureExtension_comp`: extensions compose.
-/

public section

noncomputable section

namespace LinearMap

variable {𝕜 D H : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup D] [Module 𝕜 D]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H] (R : D →ₗ[𝕜] H)

/-- The **closure of the range** of a linear map `R : D →ₗ[𝕜] H` into a normed space: a closed
subspace of `H`, hence a Banach space when `H` is. -/
abbrev rangeClosure : Submodule 𝕜 H :=
  (range R).topologicalClosure

instance [CompleteSpace H] : CompleteSpace R.rangeClosure :=
  inferInstanceAs (CompleteSpace (range R).topologicalClosure)

theorem isClosed_rangeClosure : IsClosed (R.rangeClosure : Set H) :=
  Submodule.isClosed_topologicalClosure _

/-- The elements of the closure of the range of `R` are the limits of values of `R`. -/
theorem mem_rangeClosure_iff {x : H} : x ∈ R.rangeClosure ↔ x ∈ closure (Set.range R) := by
  rw [← SetLike.mem_coe, rangeClosure, Submodule.topologicalClosure_coe, coe_range]

/-- The closure of the range of `R` is the smallest closed subspace containing every `R u`. -/
theorem rangeClosure_le_of_isClosed {S : Submodule 𝕜 H} (hS : IsClosed (S : Set H))
    (h : ∀ u, R u ∈ S) : R.rangeClosure ≤ S :=
  Submodule.topologicalClosure_minimal _ (range_le_iff_comap.2 (eq_top_iff.2 fun u _ ↦ h u)) hS

theorem apply_mem_rangeClosure (u : D) : R u ∈ R.rangeClosure :=
  Submodule.le_topologicalClosure _ (mem_range_self _ u)

/-- The linear map `R` with codomain restricted to the closure of its range. -/
def toRangeClosure : D →ₗ[𝕜] R.rangeClosure :=
  R.codRestrict _ R.apply_mem_rangeClosure

@[simp]
theorem coe_toRangeClosure (u : D) : (R.toRangeClosure u : H) = R u :=
  (rfl)

theorem norm_toRangeClosure (u : D) : ‖R.toRangeClosure u‖ = ‖R u‖ :=
  (rfl)

/-- **The values of `R` are dense** in the closure of its range. -/
theorem denseRange_toRangeClosure : DenseRange R.toRangeClosure := by
  rw [DenseRange, Subtype.dense_iff, ← Set.range_comp]
  exact (Submodule.topologicalClosure_coe _).le

/-- A continuous linear map out of the closure of the range of `R` is determined by its values on
the elements `R u`. -/
theorem rangeClosure_ext {F : Type*} [TopologicalSpace F] [AddCommMonoid F] [Module 𝕜 F]
    [T2Space F] {f g : R.rangeClosure →L[𝕜] F}
    (h : ∀ u, f (R.toRangeClosure u) = g (R.toRangeClosure u)) : f = g :=
  ContinuousLinearMap.ext fun x ↦ R.denseRange_toRangeClosure.induction
    (fun _ ⟨u, hu⟩ ↦ hu ▸ h u) (isClosed_eq f.continuous g.continuous) x

/-! ### Maps between the closures -/

variable {H' : Type*} [NormedAddCommGroup H'] [NormedSpace 𝕜 H'] {R}

/-- A continuous linear map `T : H →L[𝕜] H'` with `T (R u) = R' u` for every `u` maps the closure
of the range of `R` into that of `R'`. -/
theorem map_mem_rangeClosure {R' : D →ₗ[𝕜] H'} {T : H →L[𝕜] H'} (hT : ∀ u, T (R u) = R' u)
    {x : H} (hx : x ∈ R.rangeClosure) : T x ∈ R'.rangeClosure := by
  refine Submodule.topologicalClosure_mono ?_
    (Submodule.topologicalClosure_map _ _ (Submodule.mem_map_of_mem hx))
  rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
  exact ⟨u, (hT u).symm⟩

variable (R) (R' : D →ₗ[𝕜] H')

/-- The restriction of a continuous linear map `T : H →L[𝕜] H'` with `T (R u) = R' u` for every
`u` to a map from the closure of the range of `R` to that of `R'`. -/
def rangeClosureMap (T : H →L[𝕜] H') (hT : ∀ u, T (R u) = R' u) :
    R.rangeClosure →L[𝕜] R'.rangeClosure :=
  T.restrict fun _ hx ↦ map_mem_rangeClosure hT hx

variable {R R'}

@[simp]
theorem coe_rangeClosureMap_apply {T : H →L[𝕜] H'} (hT : ∀ u, T (R u) = R' u)
    (x : R.rangeClosure) : (R.rangeClosureMap R' T hT x : H') = T x :=
  (rfl)

@[simp]
theorem rangeClosureMap_toRangeClosure {T : H →L[𝕜] H'} (hT : ∀ u, T (R u) = R' u) (u : D) :
    R.rangeClosureMap R' T hT (R.toRangeClosure u) = R'.toRangeClosure u :=
  Subtype.ext (hT u)

/-- The restriction of `T` to the closures has the norms of `T`. -/
theorem norm_rangeClosureMap_apply {T : H →L[𝕜] H'} (hT : ∀ u, T (R u) = R' u)
    (x : R.rangeClosure) : ‖R.rangeClosureMap R' T hT x‖ = ‖T x‖ :=
  (rfl)

/-- The restriction of `T` to the closures has operator norm at most that of `T`. -/
theorem norm_rangeClosureMap_le {T : H →L[𝕜] H'} (hT : ∀ u, T (R u) = R' u) :
    ‖R.rangeClosureMap R' T hT‖ ≤ ‖T‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) fun x ↦ by
    rw [norm_rangeClosureMap_apply, ← Submodule.norm_coe x]
    exact T.le_opNorm x

/-- The restriction to the closures of an injective continuous linear map is injective. -/
theorem rangeClosureMap_injective {T : H →L[𝕜] H'} (hT : ∀ u, T (R u) = R' u)
    (hT' : Function.Injective T) : Function.Injective (R.rangeClosureMap R' T hT) :=
  fun _ _ h ↦ Subtype.ext (hT' (congrArg Subtype.val h))

/-- The restriction to the closures of a continuous linear map `T` with `T (R u) = R' u` has dense
range: its range contains every `R' u`. -/
theorem denseRange_rangeClosureMap {T : H →L[𝕜] H'} (hT : ∀ u, T (R u) = R' u) :
    DenseRange (R.rangeClosureMap R' T hT) :=
  .of_comp (g := R.toRangeClosure) <| by
    convert R'.denseRange_toRangeClosure using 1
    ext1 u
    exact rangeClosureMap_toRangeClosure hT u

/-! ### Extending operators by continuity -/

variable {D' D'' H'' : Type*} [AddCommGroup D'] [Module 𝕜 D'] [AddCommGroup D''] [Module 𝕜 D'']
  [NormedAddCommGroup H''] [NormedSpace 𝕜 H''] [CompleteSpace H']

variable (R) in
/-- The **extension of an operator** `P : D →ₗ[𝕜] D'` to a continuous linear map from the closure
of the range of `R : D →ₗ[𝕜] H` to that of `R' : D' →ₗ[𝕜] H'`, by continuity from the dense
values of `R` (`LinearMap.extendOfNorm`). It extends `P` exactly when `P` satisfies an a priori
estimate `‖R' (P u)‖ ≤ C ‖R u‖` (`LinearMap.rangeClosureExtension_toRangeClosure`), and it is then
the unique continuous extension (`LinearMap.rangeClosureExtension_eq`). -/
def rangeClosureExtension (R' : D' →ₗ[𝕜] H') (P : D →ₗ[𝕜] D') :
    R.rangeClosure →L[𝕜] R'.rangeClosure :=
  (R'.toRangeClosure ∘ₗ P).extendOfNorm R.toRangeClosure

variable {R' : D' →ₗ[𝕜] H'} {P : D →ₗ[𝕜] D'}

/-- An operator satisfying an a priori estimate `‖R' (P u)‖ ≤ C ‖R u‖` is extended by
`LinearMap.rangeClosureExtension`. -/
theorem rangeClosureExtension_toRangeClosure (hP : ∃ C, ∀ u, ‖R' (P u)‖ ≤ C * ‖R u‖) (u : D) :
    R.rangeClosureExtension R' P (R.toRangeClosure u) = R'.toRangeClosure (P u) :=
  extendOfNorm_eq R.denseRange_toRangeClosure
    (by simpa only [comp_apply, norm_toRangeClosure] using hP) u

/-- The a priori estimate `‖R' (P u)‖ ≤ C ‖R u‖` persists for the extension of `P`. -/
theorem norm_rangeClosureExtension_apply_le {C : ℝ} (hP : ∀ u, ‖R' (P u)‖ ≤ C * ‖R u‖)
    (x : R.rangeClosure) : ‖R.rangeClosureExtension R' P x‖ ≤ C * ‖x‖ :=
  norm_extendOfNorm_apply_le R.denseRange_toRangeClosure C
    (by simpa only [comp_apply, norm_toRangeClosure] using hP) x

/-- **Uniqueness of the extension.** A continuous linear map between the closures that agrees with
`P` is the extension of `P`. No estimate is assumed: the continuity of `L` provides it. -/
theorem rangeClosureExtension_eq (L : R.rangeClosure →L[𝕜] R'.rangeClosure)
    (hL : ∀ u, L (R.toRangeClosure u) = R'.toRangeClosure (P u)) :
    R.rangeClosureExtension R' P = L :=
  extendOfNorm_unique R.denseRange_toRangeClosure ‖L‖
    (fun u ↦ by simpa only [comp_apply, ← hL] using L.le_opNorm _) L (LinearMap.ext hL)

/-- The extension of the identity is the restriction of any continuous linear map `T` with
`T (R u) = R' u`. -/
theorem rangeClosureExtension_id {R' : D →ₗ[𝕜] H'} {T : H →L[𝕜] H'}
    (hT : ∀ u, T (R u) = R' u) :
    R.rangeClosureExtension R' LinearMap.id = R.rangeClosureMap R' T hT :=
  rangeClosureExtension_eq _ fun u ↦ rangeClosureMap_toRangeClosure hT u

/-- The extension of a sum of operators satisfying a priori estimates is the sum of their
extensions. -/
theorem rangeClosureExtension_add {Q : D →ₗ[𝕜] D'} (hP : ∃ C, ∀ u, ‖R' (P u)‖ ≤ C * ‖R u‖)
    (hQ : ∃ C, ∀ u, ‖R' (Q u)‖ ≤ C * ‖R u‖) :
    R.rangeClosureExtension R' (P + Q) =
      R.rangeClosureExtension R' P + R.rangeClosureExtension R' Q :=
  rangeClosureExtension_eq _ fun u ↦ by
    simp [rangeClosureExtension_toRangeClosure hP, rangeClosureExtension_toRangeClosure hQ]

/-- The extension of a difference of operators satisfying a priori estimates is the difference of
their extensions. -/
theorem rangeClosureExtension_sub {Q : D →ₗ[𝕜] D'} (hP : ∃ C, ∀ u, ‖R' (P u)‖ ≤ C * ‖R u‖)
    (hQ : ∃ C, ∀ u, ‖R' (Q u)‖ ≤ C * ‖R u‖) :
    R.rangeClosureExtension R' (P - Q) =
      R.rangeClosureExtension R' P - R.rangeClosureExtension R' Q :=
  rangeClosureExtension_eq _ fun u ↦ by
    simp [rangeClosureExtension_toRangeClosure hP, rangeClosureExtension_toRangeClosure hQ]

/-- The extension of a scalar multiple of an operator satisfying an a priori estimate is the
scalar multiple of its extension. -/
theorem rangeClosureExtension_smul (a : 𝕜) (hP : ∃ C, ∀ u, ‖R' (P u)‖ ≤ C * ‖R u‖) :
    R.rangeClosureExtension R' (a • P) = a • R.rangeClosureExtension R' P :=
  rangeClosureExtension_eq _ fun u ↦ by simp [rangeClosureExtension_toRangeClosure hP]

variable [CompleteSpace H] in
/-- The extension of the identity from the closure of the range of `R` to itself is the
identity. -/
@[simp]
theorem rangeClosureExtension_id_self : R.rangeClosureExtension R LinearMap.id = 1 :=
  rangeClosureExtension_eq _ fun _ ↦ rfl

variable [CompleteSpace H'']

/-- Following the extension of `P` by the restriction of a continuous linear map `T` with
`T (R' v) = R'' v` gives the extension of `P` into the closure of the range of `R''`. -/
theorem rangeClosureMap_comp_rangeClosureExtension {R'' : D' →ₗ[𝕜] H''} {T : H' →L[𝕜] H''}
    (hT : ∀ v, T (R' v) = R'' v) (hP : ∃ C, ∀ u, ‖R' (P u)‖ ≤ C * ‖R u‖) :
    R'.rangeClosureMap R'' T hT ∘L R.rangeClosureExtension R' P =
      R.rangeClosureExtension R'' P :=
  (rangeClosureExtension_eq _ fun u ↦ by
    rw [ContinuousLinearMap.comp_apply, rangeClosureExtension_toRangeClosure hP,
      rangeClosureMap_toRangeClosure]).symm

/-- Precomposing the extension of `P` with the restriction of a continuous linear map `T` with
`T (R₀ u) = R u` gives the extension of `P` from the closure of the range of `R₀`. -/
theorem rangeClosureExtension_comp_rangeClosureMap {H₀ : Type*} [NormedAddCommGroup H₀]
    [NormedSpace 𝕜 H₀] {R₀ : D →ₗ[𝕜] H₀} {T : H₀ →L[𝕜] H} (hT : ∀ u, T (R₀ u) = R u)
    (hP : ∃ C, ∀ u, ‖R' (P u)‖ ≤ C * ‖R u‖) :
    R.rangeClosureExtension R' P ∘L R₀.rangeClosureMap R T hT = R₀.rangeClosureExtension R' P :=
  (rangeClosureExtension_eq _ fun u ↦ by
    rw [ContinuousLinearMap.comp_apply, rangeClosureMap_toRangeClosure,
      rangeClosureExtension_toRangeClosure hP]).symm

/-- **The extension of a composition** is the composition of the extensions, when both operators
satisfy a priori estimates. -/
theorem rangeClosureExtension_comp {R'' : D'' →ₗ[𝕜] H''} {Q : D' →ₗ[𝕜] D''}
    (hQ : ∃ C, ∀ u, ‖R'' (Q u)‖ ≤ C * ‖R' u‖) (hP : ∃ C, ∀ u, ‖R' (P u)‖ ≤ C * ‖R u‖) :
    R'.rangeClosureExtension R'' Q ∘L R.rangeClosureExtension R' P =
      R.rangeClosureExtension R'' (Q ∘ₗ P) :=
  (rangeClosureExtension_eq _ fun u ↦ by
    rw [ContinuousLinearMap.comp_apply, rangeClosureExtension_toRangeClosure hP,
      rangeClosureExtension_toRangeClosure hQ, comp_apply]).symm

/-! ### Linear maps controlling each other -/

variable [CompleteSpace H]

variable (R) in
/-- **Linear maps controlling each other have isomorphic range closures.** If `R` and `R'` out of
the same space `D` satisfy `‖R' u‖ ≤ C ‖R u‖` and `‖R u‖ ≤ C' ‖R' u‖`, the closures of their
ranges are isomorphic Banach spaces, through the isomorphism sending `R u` to `R' u`
(`LinearMap.rangeClosureCongr_toRangeClosure`). -/
def rangeClosureCongr (R' : D →ₗ[𝕜] H') (h : ∃ C, ∀ u, ‖R' u‖ ≤ C * ‖R u‖)
    (h' : ∃ C, ∀ u, ‖R u‖ ≤ C * ‖R' u‖) : R.rangeClosure ≃L[𝕜] R'.rangeClosure :=
  (LinearEquiv.refl 𝕜 D).extend R.toRangeClosure R'.toRangeClosure R.denseRange_toRangeClosure
    (by simpa using h) R'.denseRange_toRangeClosure (by simpa using h')

@[simp]
theorem rangeClosureCongr_toRangeClosure {R' : D →ₗ[𝕜] H'} (h : ∃ C, ∀ u, ‖R' u‖ ≤ C * ‖R u‖)
    (h' : ∃ C, ∀ u, ‖R u‖ ≤ C * ‖R' u‖) (u : D) :
    R.rangeClosureCongr R' h h' (R.toRangeClosure u) = R'.toRangeClosure u := by
  rw [rangeClosureCongr, LinearEquiv.extend_eq, LinearEquiv.refl_apply]

@[simp]
theorem rangeClosureCongr_symm_toRangeClosure {R' : D →ₗ[𝕜] H'}
    (h : ∃ C, ∀ u, ‖R' u‖ ≤ C * ‖R u‖) (h' : ∃ C, ∀ u, ‖R u‖ ≤ C * ‖R' u‖) (u : D) :
    (R.rangeClosureCongr R' h h').symm (R'.toRangeClosure u) = R.toRangeClosure u := by
  rw [rangeClosureCongr, LinearEquiv.extend_symm_eq, LinearEquiv.refl_symm,
    LinearEquiv.refl_apply]

end LinearMap
