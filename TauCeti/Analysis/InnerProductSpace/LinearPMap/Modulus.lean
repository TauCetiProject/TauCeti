/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Sqrt
public import TauCeti.Analysis.InnerProductSpace.Modulus
import TauCeti.Analysis.Normed.Operator.LinearPMap.GraphCore
import TauCeti.LinearAlgebra.LinearPMap.Basic

/-!
# The modulus of a closed unbounded operator

For a closed densely defined partial linear map `T : E →ₗ.[𝕜] F` between Hilbert spaces over
`RCLike 𝕜`, von Neumann's theorem (`LinearPMap.isSelfAdjoint_adjointComp`) states that the maximal
composition `T†T = T.adjointComp` is self-adjoint, with nonnegative quadratic form
`0 ≤ re ⟪T†T x, x⟫ = ‖T x‖²`. Its unique nonnegative self-adjoint square root (`LinearPMap.sqrt`)
is the **modulus** `|T| = (T†T)^(1/2) = T.modulus : E →ₗ.[𝕜] E` of `T`.

On the subspace `D(T†T)` — which is simultaneously a graph core for `T`
(`LinearPMap.IsClosed.hasCore_adjointComp_domain`) and a graph core for `|T|`
(`LinearPMap.IsClosed.hasCore_adjointComp_domain_modulus`) — the identity `|T|† |T| = T†T` yields
pointwise norm equality `‖|T| x‖ = ‖T x‖`. Passing to graph closures along both cores shows that
`|T|` and `T` have the **exact same domain** `D(|T|) = D(T)` and satisfy `‖|T| x‖ = ‖T x‖` for
every `x ∈ D(T)`. Consequently `ker |T| = ker T`, `(range |T|)ᗮ = ker T`, and the closure of
`range |T|` is `(ker T)ᗮ`.

## Main definitions and results

* `LinearPMap.modulus`: the modulus `|T| = T.adjointComp.sqrt` of a partial linear map.
* `LinearPMap.IsClosed.isSelfAdjoint_modulus`, `LinearPMap.IsClosed.re_inner_modulus_nonneg`,
  `LinearPMap.IsClosed.modulus_adjointComp`: `|T|` is self-adjoint, nonnegative, and satisfies
  `|T|† |T| = T†T` on maximal domain.
* `LinearPMap.IsClosed.eq_modulus_iff`: characterization of `|T|` as the unique nonnegative
  self-adjoint partial linear map `M` with `M.adjointComp = T.adjointComp`.
* `LinearPMap.IsClosed.modulus_domain` and `LinearPMap.IsClosed.norm_modulus_apply`:
  `T.modulus.domain = T.domain` and `‖T.modulus ⟨x, hxM⟩‖ = ‖T ⟨x, hx⟩‖`.
* `LinearPMap.IsClosed.ker_modulus`, `LinearPMap.IsClosed.orthogonal_range_modulus`,
  `LinearPMap.IsClosed.topologicalClosure_range_modulus`: kernel and range-closure identities.
* `IsSelfAdjoint.modulus_eq_of_re_inner_nonneg`: a nonnegative self-adjoint operator equals its
  own modulus.
* `ContinuousLinearMap.toPMap_top_modulus`: compatibility with `ContinuousLinearMap.modulus` for
  bounded operators viewed on `⊤`.

## References

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, revised ed.,
  Academic Press (1980), Theorem VIII.32.
* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1995), §VI.2.7.
* J. Weidmann, *Linear Operators in Hilbert Spaces*, Graduate Texts in Mathematics 68, Springer
  (1980), §7.1.
-/

public section

namespace LinearPMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- The **modulus** `|T| = (T†T)^(1/2)` of a partial linear map `T : E →ₗ.[𝕜] F`: the positive
square root (`LinearPMap.sqrt`) of the maximal composition `T†T = T.adjointComp`. -/
noncomputable def modulus (T : E →ₗ.[𝕜] F) : E →ₗ.[𝕜] E :=
  T.adjointComp.sqrt

/-- Unfolding lemma: `T.modulus` is `T.adjointComp.sqrt`. -/
theorem modulus_eq_sqrt_adjointComp (T : E →ₗ.[𝕜] F) : T.modulus = T.adjointComp.sqrt :=
  (rfl)

/-- The modulus of the zero partial linear map (on `⊤`) is zero. -/
@[simp]
theorem modulus_zero : (0 : E →ₗ.[𝕜] F).modulus = 0 := by
  have hd : Dense (((0 : E →ₗ.[𝕜] F).domain : Set E)) := by simp [dense_univ]
  have hadj : (0 : E →ₗ.[𝕜] F)† = 0 := by
    have hdom : (0 : E →ₗ.[𝕜] F)†.domain = ⊤ := eq_top_iff.mpr fun y _ ↦
      mem_adjoint_domain_of_exists y ⟨0, fun _ ↦ by simp⟩
    exact LinearPMap.ext hdom fun y hy _ ↦ adjoint_apply_eq hd ⟨y, hy⟩ fun _ ↦ by simp
  have hcomp : (0 : E →ₗ.[𝕜] F).adjointComp = 0 := by
    have hdom : (0 : E →ₗ.[𝕜] F).adjointComp.domain = ⊤ := eq_top_iff.mpr fun _ _ ↦
      mem_adjointComp_domain.mpr ⟨Submodule.mem_top, by rw [hadj]; exact Submodule.mem_top⟩
    refine LinearPMap.ext hdom fun _ _ _ ↦ ?_
    rw [adjointComp_apply]
    exact LinearPMap.congr_fun hadj _ Submodule.mem_top
  rw [modulus_eq_sqrt_adjointComp, hcomp, sqrt_zero]

section Closed

variable [CompleteSpace F]

/-- The modulus of a closed densely defined partial linear map is self-adjoint. -/
theorem IsClosed.isSelfAdjoint_modulus {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) : IsSelfAdjoint T.modulus :=
  (isSelfAdjoint_adjointComp T hT hd).isSelfAdjoint_sqrt (re_inner_adjointComp_nonneg T)

/-- The modulus of a closed densely defined partial linear map is closed. -/
theorem IsClosed.isClosed_modulus {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) : T.modulus.IsClosed :=
  (hT.isSelfAdjoint_modulus hd).isClosed

/-- The modulus of a closed densely defined partial linear map is densely defined. -/
theorem IsClosed.dense_modulus_domain {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) : Dense (T.modulus.domain : Set E) :=
  (hT.isSelfAdjoint_modulus hd).dense_domain

/-- The quadratic form of `T.modulus` is nonnegative on `T.modulus.domain`. -/
theorem IsClosed.re_inner_modulus_nonneg {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) (x : T.modulus.domain) :
    0 ≤ RCLike.re ⟪T.modulus x, (x : E)⟫ :=
  (isSelfAdjoint_adjointComp T hT hd).re_inner_sqrt_nonneg (re_inner_adjointComp_nonneg T) x

/-- Squaring `T.modulus` via `adjointComp` recovers `T.adjointComp`: `|T|† |T| = T†T`. -/
theorem IsClosed.modulus_adjointComp {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) : T.modulus.adjointComp = T.adjointComp :=
  (isSelfAdjoint_adjointComp T hT hd).sqrt_adjointComp (re_inner_adjointComp_nonneg T)

/-- The domain of `T†T` is contained in the domain of `|T|`. -/
theorem IsClosed.adjointComp_domain_le_modulus_domain {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) : T.adjointComp.domain ≤ T.modulus.domain :=
  (isSelfAdjoint_adjointComp T hT hd).domain_le_sqrt_domain (re_inner_adjointComp_nonneg T)

/-- The domain of `T†T` is a graph core for `|T|`. -/
theorem IsClosed.hasCore_adjointComp_domain_modulus {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) : T.modulus.HasCore T.adjointComp.domain :=
  (isSelfAdjoint_adjointComp T hT hd).hasCore_sqrt_domain (re_inner_adjointComp_nonneg T)

/-- **Uniqueness of the modulus.** Any nonnegative self-adjoint partial linear map `M` with
`M.adjointComp = T.adjointComp` equals `T.modulus`. -/
theorem IsClosed.eq_modulus {T : E →ₗ.[𝕜] F} {M : E →ₗ.[𝕜] E} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) (hM : IsSelfAdjoint M)
    (hMpos : ∀ x : M.domain, 0 ≤ RCLike.re ⟪M x, (x : E)⟫)
    (hMsq : M.adjointComp = T.adjointComp) : M = T.modulus :=
  (isSelfAdjoint_adjointComp T hT hd).eq_sqrt (re_inner_adjointComp_nonneg T) hM hMpos hMsq

/-- Characterization of `T.modulus` as the unique nonnegative self-adjoint partial linear map whose
`adjointComp` is `T.adjointComp`. -/
theorem IsClosed.eq_modulus_iff {T : E →ₗ.[𝕜] F} {M : E →ₗ.[𝕜] E} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) :
    M = T.modulus ↔ IsSelfAdjoint M ∧
      (∀ x : M.domain, 0 ≤ RCLike.re ⟪M x, (x : E)⟫) ∧ M.adjointComp = T.adjointComp :=
  (isSelfAdjoint_adjointComp T hT hd).eq_sqrt_iff (re_inner_adjointComp_nonneg T)

private theorem norm_modulus_apply_of_mem_adjointComp_domain {T : E →ₗ.[𝕜] F}
    (hT : T.IsClosed) (hd : Dense (T.domain : Set E)) (u : E) (hu : u ∈ T.adjointComp.domain) :
    ‖T.modulus ⟨u, hT.adjointComp_domain_le_modulus_domain hd hu⟩‖ =
      ‖T ⟨u, adjointComp_domain_le T hu⟩‖ := by
  have hxM : u ∈ T.modulus.adjointComp.domain := (hT.modulus_adjointComp hd).symm ▸ hu
  have hsq : ‖T.modulus ⟨u, hT.adjointComp_domain_le_modulus_domain hd hu⟩‖ ^ 2 =
      ‖T ⟨u, adjointComp_domain_le T hu⟩‖ ^ 2 := by
    have h₁ := inner_adjointComp (hT.dense_modulus_domain hd) ⟨u, hxM⟩
      (hT.adjointComp_domain_le_modulus_domain hd hu)
    have h₂ := inner_adjointComp hd ⟨u, hu⟩ (adjointComp_domain_le T hu)
    have heq : T.modulus.adjointComp ⟨u, hxM⟩ = T.adjointComp ⟨u, hu⟩ :=
      LinearPMap.congr_fun (hT.modulus_adjointComp hd) hxM hu
    have hre := congrArg RCLike.re (h₁.symm.trans (heq ▸ h₂))
    simpa only [inner_self_eq_norm_sq (𝕜 := 𝕜)] using hre
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- For a closed densely defined operator `T`, the domain of its modulus `|T|` equals `D(T)`. -/
@[simp]
theorem IsClosed.modulus_domain {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) : T.modulus.domain = T.domain :=
  le_antisymm
    ((hT.hasCore_adjointComp_domain_modulus hd).domain_le_of_norm_eq hT (adjointComp_domain_le T)
      fun u hu ↦ (norm_modulus_apply_of_mem_adjointComp_domain hT hd u hu).symm)
    (hT.hasCore_adjointComp_domain.domain_le_of_norm_eq (hT.isClosed_modulus hd)
      (hT.adjointComp_domain_le_modulus_domain hd)
      (norm_modulus_apply_of_mem_adjointComp_domain hT hd))

/-- For a closed densely defined operator `T`, `‖|T| x‖ = ‖T x‖` on their common domain
`D(|T|) = D(T)`. -/
theorem IsClosed.norm_modulus_apply {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) {x : E} (hxM : x ∈ T.modulus.domain) (hx : x ∈ T.domain) :
    ‖T.modulus ⟨x, hxM⟩‖ = ‖T ⟨x, hx⟩‖ :=
  hT.hasCore_adjointComp_domain.norm_apply_eq_of_norm_eq (hT.isClosed_modulus hd)
    (hT.adjointComp_domain_le_modulus_domain hd)
    (norm_modulus_apply_of_mem_adjointComp_domain hT hd) ⟨x, hx⟩ hxM

/-- The modulus and the operator have the same kernel when `T` is closed and densely defined. -/
@[simp]
theorem IsClosed.ker_modulus {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) : T.modulus.ker = T.ker := by
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨u, rfl, hu⟩ := mem_ker_iff.mp hx
    have hxT : (u : E) ∈ T.domain := hT.modulus_domain hd ▸ u.property
    refine mem_ker_iff.mpr ⟨⟨u, hxT⟩, rfl, norm_eq_zero.mp ?_⟩
    rw [← hT.norm_modulus_apply hd u.property hxT, hu, norm_zero]
  · obtain ⟨u, rfl, hu⟩ := mem_ker_iff.mp hx
    have hxM : (u : E) ∈ T.modulus.domain := (hT.modulus_domain hd).symm ▸ u.property
    refine mem_ker_iff.mpr ⟨⟨u, hxM⟩, rfl, norm_eq_zero.mp ?_⟩
    rw [hT.norm_modulus_apply hd hxM u.property, hu, norm_zero]

/-- For a closed densely defined operator `T`, the orthogonal complement of the range of `|T|` is
`ker T`. -/
theorem IsClosed.orthogonal_range_modulus {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) : (LinearMap.range T.modulus.toFun)ᗮ = T.ker := by
  rw [(hT.isSelfAdjoint_modulus hd).orthogonal_range_eq_ker, hT.ker_modulus hd]

/-- For a closed densely defined operator `T`, the closure of the range of `|T|` is `(ker T)ᗮ`. -/
theorem IsClosed.topologicalClosure_range_modulus {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) :
    (LinearMap.range T.modulus.toFun).topologicalClosure = T.kerᗮ := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure, hT.orthogonal_range_modulus hd]

/-- A nonnegative self-adjoint partial linear map equals its own modulus. -/
theorem _root_.IsSelfAdjoint.modulus_eq_of_re_inner_nonneg {A : E →ₗ.[𝕜] E}
    (hA : IsSelfAdjoint A) (hpos : ∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫) :
    A.modulus = A :=
  (hA.isClosed.eq_modulus hA.dense_domain hA hpos rfl).symm

/-- For a closed densely defined operator `T`, the modulus of `|T|` is `|T|`. -/
@[simp]
theorem IsClosed.modulus_modulus {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) : T.modulus.modulus = T.modulus :=
  (hT.isSelfAdjoint_modulus hd).modulus_eq_of_re_inner_nonneg (hT.re_inner_modulus_nonneg hd)

end Closed

end LinearPMap

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

attribute [local instance] ContinuousLinearMap.realAlgebra ContinuousLinearMap.realIsScalarTower in
/-- Viewing a bounded operator `B` as a partial linear map on `⊤`, its unbounded modulus coincides
with `ContinuousLinearMap.modulus B` on `⊤`. -/
@[simp]
theorem toPMap_top_modulus (B : E →L[𝕜] F) :
    ((B : E →ₗ[𝕜] F).toPMap ⊤).modulus =
      ((B.modulus : E →L[𝕜] E) : E →ₗ[𝕜] E).toPMap ⊤ := by
  rw [LinearPMap.modulus_eq_sqrt_adjointComp, B.toPMap_top_adjointComp,
    (isPositive_adjoint_comp_self B).toPMap_top_sqrt, ← B.modulus_eq_sqrt]

end ContinuousLinearMap

end

