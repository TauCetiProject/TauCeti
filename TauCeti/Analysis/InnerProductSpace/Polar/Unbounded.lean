/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Modulus
public import TauCeti.Analysis.InnerProductSpace.Polar.Bounded
public import TauCeti.LinearAlgebra.LinearPMap.Basic
import TauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions
import TauCeti.Analysis.InnerProductSpace.LinearPMap.PartialIsometry
import TauCeti.Analysis.InnerProductSpace.LinearPMap.SubmoduleAdjoint
import TauCeti.Topology.Algebra.Module.LinearPMap.Basic

/-!
# The polar decomposition of a closed unbounded operator

Every closed densely defined partial linear map `T : E →ₗ.[𝕜] F` between Hilbert spaces over
`RCLike 𝕜` has modulus `|T| = (T†T)^(1/2) = T.modulus` sharing its exact domain `D(|T|) = D(T)` and
pointwise norms `‖|T| x‖ = ‖T x‖` (`LinearPMap.IsClosed.modulus_domain`,
`LinearPMap.IsClosed.norm_modulus_apply`). Equipping `D(T) ⊓ D(|T|)` with the discrete topology and
passing `x ↦ T x` and `x ↦ |T| x` to `ContinuousLinearMap.factorThru` produces a canonical bounded
operator `T.polarFactor : E →L[𝕜] F` extending `|T| x ↦ T x` by continuity to the closure of
`range |T|` and by zero on its orthogonal complement.

For a closed densely defined operator `T`:

* **Right polar decomposition:** `(T.polarFactor : E →ₗ[𝕜] F).compPMap T.modulus = T`
  (`LinearPMap.IsClosed.polarFactor_compPMap_modulus`), where `v = T.polarFactor` is a partial
  isometry (`LinearPMap.IsClosed.isPartialIsometry_polarFactor`) with initial space `(ker T)ᗮ`
  (`v† ∘L v = T.kerᗮ.starProjection`) and final space `closure (range T)`
  (`v ∘L v† = (LinearMap.range T.toFun).topologicalClosure.starProjection`).
* **Uniqueness:** `v = T.polarFactor` is the unique bounded operator `V : E →L[𝕜] F` satisfying
  `(V : E →ₗ[𝕜] F).compPMap T.modulus = T` and vanishing on `ker T`
  (`LinearPMap.IsClosed.eq_polarFactor_iff`); jointly, both factors `(v, M)` in
  `T = (v : E →ₗ[𝕜] F).compPMap M` are uniquely determined as `(T.polarFactor, T.modulus)` when
  `M` is nonnegative self-adjoint and `v` is a partial isometry with `v.ker = M.ker`
  (`LinearPMap.eq_modulus_and_eq_polarFactor`).
* **Adjoint and left polar decomposition:** `(T†).modulus = (v : E →ₗ[𝕜] F).compPMap T†`
  (`LinearPMap.IsClosed.modulus_adjoint_eq_polarFactor_compPMap_adjoint`),
  `(T†).polarFactor = v†` (`LinearPMap.IsClosed.polarFactor_adjoint`), and `T = |T†| ∘ v` on
  maximal domain (`LinearPMap.IsClosed.modulus_adjoint_comp_polarFactor`).
* **Bounded compatibility:** for `B : E →L[𝕜] F`, `((B : E →ₗ[𝕜] F).toPMap ⊤).polarFactor` agrees
  with `ContinuousLinearMap.polarFactor B` (`ContinuousLinearMap.toPMap_top_polarFactor`).

## Main definitions and results

* `LinearPMap.polarFactor`: the bounded factor `E →L[𝕜] F` of a partial linear map; a partial
  isometry when `T` is closed and densely defined.
* `LinearPMap.IsClosed.polarFactor_compPMap_modulus`: right polar decomposition `v |T| = T`.
* `LinearPMap.IsClosed.isPartialIsometry_polarFactor`, `LinearPMap.IsClosed.ker_polarFactor`,
  `LinearPMap.IsClosed.range_polarFactor`,
  `LinearPMap.IsClosed.adjoint_polarFactor_comp_polarFactor`,
  `LinearPMap.IsClosed.polarFactor_comp_adjoint_polarFactor`: initial and final projections of `v`.
* `LinearPMap.IsClosed.eq_polarFactor`, `LinearPMap.IsClosed.eq_polarFactor_iff`, and
  `LinearPMap.eq_modulus_and_eq_polarFactor`: uniqueness of the polar factor and joint uniqueness
  of `(v, |T|)`.
* `LinearPMap.IsClosed.adjoint_eq_modulus_comp_adjoint_polarFactor`: `T† = |T| ∘ v†` on maximal
  domain.
* `LinearPMap.IsClosed.modulus_adjoint_eq_polarFactor_compPMap_adjoint`: `|T†| = v ∘ T†`.
* `LinearPMap.IsClosed.polarFactor_adjoint`: `(T†).polarFactor = v†`.
* `LinearPMap.IsClosed.modulus_adjoint_comp_polarFactor`: left polar decomposition `|T†| ∘ v = T`
  on maximal domain.
* `ContinuousLinearMap.toPMap_top_polarFactor`: compatibility with
  `ContinuousLinearMap.polarFactor`.

## References

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, revised ed.,
  Academic Press (1980), Theorem VIII.32.
* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1995), §VI.2.7, Theorem 2.26.
* R. V. Kadison, J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras, Vol. I*,
  Academic Press (1983), Theorem 2.7.8.
-/

public section

noncomputable section

namespace LinearPMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- Discrete-topology copy of `T.domain ⊓ T.modulus.domain`, used internally to feed `x ↦ T x` and
`x ↦ |T| x` to `ContinuousLinearMap.factorThru` without creating a `TopologicalSpace` diamond on
the submodule subtype. -/
private def PolarDom (T : E →ₗ.[𝕜] F) : Type _ :=
  ↥(T.domain ⊓ T.modulus.domain)

private instance (T : E →ₗ.[𝕜] F) : AddCommGroup (PolarDom T) :=
  inferInstanceAs (AddCommGroup ↥(T.domain ⊓ T.modulus.domain))

private instance (T : E →ₗ.[𝕜] F) : Module 𝕜 (PolarDom T) :=
  inferInstanceAs (Module 𝕜 ↥(T.domain ⊓ T.modulus.domain))

private instance (T : E →ₗ.[𝕜] F) : TopologicalSpace (PolarDom T) := ⊥

private instance (T : E →ₗ.[𝕜] F) : DiscreteTopology (PolarDom T) := ⟨rfl⟩

private def PolarDom.mk {T : E →ₗ.[𝕜] F} {x : E} (hx : x ∈ T.domain) (hxM : x ∈ T.modulus.domain) :
    PolarDom T :=
  (⟨x, ⟨hx, hxM⟩⟩ : ↥(T.domain ⊓ T.modulus.domain))

private def PolarDom.val {T : E →ₗ.[𝕜] F} (d : PolarDom T) : E :=
  Subtype.val (d : ↥(T.domain ⊓ T.modulus.domain))

private theorem PolarDom.val_mem_domain {T : E →ₗ.[𝕜] F} (d : PolarDom T) :
    d.val ∈ T.domain :=
  (d : ↥(T.domain ⊓ T.modulus.domain)).property.1

private theorem PolarDom.val_mem_modulus_domain {T : E →ₗ.[𝕜] F} (d : PolarDom T) :
    d.val ∈ T.modulus.domain :=
  (d : ↥(T.domain ⊓ T.modulus.domain)).property.2

private theorem PolarDom.val_mk {T : E →ₗ.[𝕜] F} {x : E} (hx : x ∈ T.domain)
    (hxM : x ∈ T.modulus.domain) : (PolarDom.mk hx hxM).val = x :=
  -- `PolarDom` is a type-synonym wrapper around `↥(T.domain ⊓ T.modulus.domain)`.
  rfl

private def polarTargetCLM (T : E →ₗ.[𝕜] F) : PolarDom T →L[𝕜] F :=
  ⟨T.toFun.comp (Submodule.inclusion inf_le_left), continuous_of_discreteTopology⟩

private def polarModulusCLM (T : E →ₗ.[𝕜] F) : PolarDom T →L[𝕜] E :=
  ⟨T.modulus.toFun.comp (Submodule.inclusion inf_le_right), continuous_of_discreteTopology⟩

private theorem polarTargetCLM_apply {T : E →ₗ.[𝕜] F} (d : PolarDom T) :
    polarTargetCLM T d = T ⟨d.val, d.val_mem_domain⟩ :=
  -- Unfolds `polarTargetCLM` across the `PolarDom` type synonym.
  rfl

private theorem polarModulusCLM_apply {T : E →ₗ.[𝕜] F} (d : PolarDom T) :
    polarModulusCLM T d = T.modulus ⟨d.val, d.val_mem_modulus_domain⟩ :=
  -- Unfolds `polarModulusCLM` across the `PolarDom` type synonym.
  rfl

private theorem polarTargetCLM_mk {T : E →ₗ.[𝕜] F} {x : E} (hx : x ∈ T.domain)
    (hxM : x ∈ T.modulus.domain) : polarTargetCLM T (PolarDom.mk hx hxM) = T ⟨x, hx⟩ := by
  rw [polarTargetCLM_apply]
  exact congrArg T (Subtype.ext (PolarDom.val_mk hx hxM))

private theorem polarModulusCLM_mk {T : E →ₗ.[𝕜] F} {x : E} (hx : x ∈ T.domain)
    (hxM : x ∈ T.modulus.domain) :
    polarModulusCLM T (PolarDom.mk hx hxM) = T.modulus ⟨x, hxM⟩ := by
  rw [polarModulusCLM_apply]
  exact congrArg T.modulus (Subtype.ext (PolarDom.val_mk hx hxM))

variable [CompleteSpace F]

/-- The **polar factor** of a partial linear map `T : E →ₗ.[𝕜] F`: a bounded operator `E →L[𝕜] F`
constructed by factoring `T` through `T.modulus` on `T.domain ⊓ T.modulus.domain`. When `T` is
closed and densely defined, it extends `|T| x ↦ T x` by continuity to the closure of `range |T|`
and by zero on its orthogonal complement, giving the unique partial isometry `v` satisfying
`(v : E →ₗ[𝕜] F).compPMap T.modulus = T` and vanishing on `ker T`. Outside closed densely defined
operators its behavior is unspecified. -/
def polarFactor (T : E →ₗ.[𝕜] F) : E →L[𝕜] F :=
  (polarTargetCLM T).factorThru (polarModulusCLM T)

private theorem norm_polarTargetCLM_eq {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) (d : PolarDom T) :
    ‖polarTargetCLM T d‖ = ‖polarModulusCLM T d‖ := by
  rw [polarTargetCLM_apply, polarModulusCLM_apply]
  exact (hT.norm_modulus_apply hd d.val_mem_modulus_domain d.val_mem_domain).symm

private theorem range_polarModulusCLM {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) :
    (polarModulusCLM T).range = LinearMap.range T.modulus.toFun := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨d, rfl⟩
    exact ⟨⟨d.val, d.val_mem_modulus_domain⟩, (polarModulusCLM_apply d).symm⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨PolarDom.mk (hT.modulus_domain hd ▸ x.property) x.property,
      polarModulusCLM_mk _ x.property⟩

private theorem range_polarTargetCLM {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) :
    (polarTargetCLM T).range = LinearMap.range T.toFun := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨d, rfl⟩
    exact ⟨⟨d.val, d.val_mem_domain⟩, (polarTargetCLM_apply d).symm⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨PolarDom.mk x.property ((hT.modulus_domain hd).symm ▸ x.property),
      polarTargetCLM_mk x.property _⟩

/-! ### Right polar decomposition, projections, and uniqueness -/

/-- The polar factor maps `|T| x` to `T x` for every `x` in their common domain `D(|T|) = D(T)`. -/
theorem IsClosed.polarFactor_modulus_apply {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) {x : E} (hxM : x ∈ T.modulus.domain) (hx : x ∈ T.domain) :
    T.polarFactor (T.modulus ⟨x, hxM⟩) = T ⟨x, hx⟩ := by
  have h := (polarTargetCLM T).factorThru_apply_apply (A := polarModulusCLM T)
    ⟨1, fun z ↦ by rw [one_mul, norm_polarTargetCLM_eq hT hd z]⟩ (PolarDom.mk hx hxM)
  rwa [polarModulusCLM_mk, polarTargetCLM_mk] at h

/-- **Right polar decomposition** of a closed densely defined operator: `v ∘ |T| = T`, with exact
domain equality `D(v ∘ |T|) = D(|T|) = D(T)`. -/
theorem IsClosed.polarFactor_compPMap_modulus {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) :
    (T.polarFactor : E →ₗ[𝕜] F).compPMap T.modulus = T := by
  refine LinearPMap.ext ((LinearMap.compPMap_domain _ _).trans (hT.modulus_domain hd))
    fun _ _ hx ↦ ?_
  rw [LinearMap.compPMap_apply, ContinuousLinearMap.coe_coe]
  exact hT.polarFactor_modulus_apply hd _ hx

/-- The polar factor vanishes on `ker T`. -/
theorem IsClosed.polarFactor_apply_of_mem_ker {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) {x : E} (hx : x ∈ T.ker) : T.polarFactor x = 0 :=
  ContinuousLinearMap.factorThru_apply_of_mem_orthogonal
    (by rwa [range_polarModulusCLM hT hd, hT.orthogonal_range_modulus hd])

/-- The polar factor has the same kernel as `T`. -/
@[simp]
theorem IsClosed.ker_polarFactor {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) : T.polarFactor.ker = T.ker := by
  rw [polarFactor, ContinuousLinearMap.ker_factorThru (norm_polarTargetCLM_eq hT hd),
    range_polarModulusCLM hT hd, hT.orthogonal_range_modulus hd]

/-- The initial space `(ker v)ᗮ` of the polar factor is `(ker T)ᗮ`. -/
theorem IsClosed.orthogonal_ker_polarFactor {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) : T.polarFactor.kerᗮ = T.kerᗮ :=
  congrArg Submodule.orthogonal (hT.ker_polarFactor hd)

/-- The polar factor preserves norms on its initial space `(ker T)ᗮ`. -/
theorem IsClosed.norm_polarFactor_apply {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) {x : E} (hx : x ∈ T.kerᗮ) :
    ‖T.polarFactor x‖ = ‖x‖ :=
  ContinuousLinearMap.norm_factorThru_apply (norm_polarTargetCLM_eq hT hd)
    (by rwa [range_polarModulusCLM hT hd, hT.topologicalClosure_range_modulus hd])

/-- The polar factor of a closed densely defined operator is a partial isometry. -/
theorem IsClosed.isPartialIsometry_polarFactor {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) : T.polarFactor.IsPartialIsometry :=
  ContinuousLinearMap.isPartialIsometry_factorThru (norm_polarTargetCLM_eq hT hd)

/-- The initial projection `v† v` of the polar factor is the orthogonal projection onto
`(ker T)ᗮ`. -/
theorem IsClosed.adjoint_polarFactor_comp_polarFactor {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) :
    T.polarFactor.adjoint ∘L T.polarFactor = T.kerᗮ.starProjection := by
  simpa only [hT.ker_polarFactor hd] using
    (hT.isPartialIsometry_polarFactor hd).adjoint_comp_self_eq_starProjection

/-- The range of the polar factor is the closure of the range of `T`. -/
theorem IsClosed.range_polarFactor {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) :
    T.polarFactor.range = (LinearMap.range T.toFun).topologicalClosure := by
  rw [polarFactor, ContinuousLinearMap.range_factorThru (norm_polarTargetCLM_eq hT hd),
    range_polarTargetCLM hT hd]

/-- The final projection `v v†` of the polar factor is the orthogonal projection onto the closure
of the range of `T`. -/
theorem IsClosed.polarFactor_comp_adjoint_polarFactor {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) :
    T.polarFactor ∘L T.polarFactor.adjoint =
      (LinearMap.range T.toFun).topologicalClosure.starProjection := by
  rw [polarFactor, ContinuousLinearMap.factorThru_comp_adjoint_factorThru
    (norm_polarTargetCLM_eq hT hd), range_polarTargetCLM hT hd]

/-- **Uniqueness of the polar factor.** Any bounded operator `V : E →L[𝕜] F` satisfying
`(V : E →ₗ[𝕜] F).compPMap T.modulus = T` and vanishing on `ker T` equals `T.polarFactor`. Notice
`V` is not assumed a priori to be a partial isometry. -/
theorem IsClosed.eq_polarFactor {T : E →ₗ.[𝕜] F} {V : E →L[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) (hV : (V : E →ₗ[𝕜] F).compPMap T.modulus = T)
    (hV₀ : ∀ x ∈ T.ker, V x = 0) : V = T.polarFactor := by
  refine ContinuousLinearMap.eq_factorThru ?_ fun y hy ↦ ?_
  · ext d
    rw [ContinuousLinearMap.comp_apply, polarModulusCLM_apply, polarTargetCLM_apply]
    exact LinearPMap.congr_fun hV d.val_mem_modulus_domain d.val_mem_domain
  · rw [range_polarModulusCLM hT hd, hT.orthogonal_range_modulus hd] at hy
    exact hV₀ y hy

/-- Characterization of `T.polarFactor` as the unique bounded operator factoring `T` through
`T.modulus` and vanishing on `ker T`. -/
theorem IsClosed.eq_polarFactor_iff {T : E →ₗ.[𝕜] F} {V : E →L[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) :
    V = T.polarFactor ↔
      (V : E →ₗ[𝕜] F).compPMap T.modulus = T ∧ ∀ x ∈ T.ker, V x = 0 := by
  refine ⟨?_, fun ⟨hV, hV₀⟩ ↦ hT.eq_polarFactor hd hV hV₀⟩
  rintro rfl
  exact ⟨hT.polarFactor_compPMap_modulus hd, fun _ hx ↦ hT.polarFactor_apply_of_mem_ker hd hx⟩

/-- **Joint uniqueness of the polar decomposition.** If `M : E →ₗ.[𝕜] E` is nonnegative and
self-adjoint, `V : E →L[𝕜] F` is a partial isometry with `V.ker = M.ker`, and
`(V : E →ₗ[𝕜] F).compPMap M = T`, then `M = T.modulus` and `V = T.polarFactor`.

Neither closedness nor density of `T.domain` is assumed: both follow from `T = V ∘ M`. -/
theorem eq_modulus_and_eq_polarFactor {T : E →ₗ.[𝕜] F} {M : E →ₗ.[𝕜] E} {V : E →L[𝕜] F}
    (hM : IsSelfAdjoint M) (hMpos : ∀ x : M.domain, 0 ≤ RCLike.re ⟪M x, (x : E)⟫)
    (hVpi : V.IsPartialIsometry) (hVker : V.ker = M.ker)
    (hVM : (V : E →ₗ[𝕜] F).compPMap M = T) :
    M = T.modulus ∧ V = T.polarFactor := by
  have hrange : LinearMap.range M.toFun ≤ V.kerᗮ :=
    hVker ▸ hM.isFormalAdjoint.range_le_orthogonal_ker
  have hT : T.IsClosed := hVM ▸ hVpi.isClosed_compPMap hrange hM.isClosed
  have hd : Dense (T.domain : Set E) := hVM ▸ hM.dense_domain
  have hM' : M = T.modulus :=
    hT.eq_modulus hd hM hMpos (hVM ▸ (hVpi.compPMap_adjointComp hrange).symm)
  refine ⟨hM', hT.eq_polarFactor hd (hM' ▸ hVM) fun x hx ↦ ?_⟩
  rw [← hT.ker_modulus hd, ← hM', ← hVker, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx
  exact hx

/-! ### Adjoint and left polar decomposition -/

/-- The adjoint of the polar factor sends `T x` back to `|T| x` on `D(T) = D(|T|)`. -/
theorem IsClosed.adjoint_polarFactor_apply_apply {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) {x : E} (hx : x ∈ T.domain) (hxM : x ∈ T.modulus.domain) :
    T.polarFactor.adjoint (T ⟨x, hx⟩) = T.modulus ⟨x, hxM⟩ := by
  have h := congr($(ContinuousLinearMap.adjoint_factorThru_comp (norm_polarTargetCLM_eq hT hd))
    (PolarDom.mk hx hxM))
  rwa [ContinuousLinearMap.comp_apply, polarTargetCLM_mk, polarModulusCLM_mk] at h

/-- Composing `v†` on the left with `T` recovers `|T|`: `(v† : F →ₗ[𝕜] E).compPMap T = |T|`. -/
theorem IsClosed.adjoint_polarFactor_compPMap {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) :
    (T.polarFactor.adjoint : F →ₗ[𝕜] E).compPMap T = T.modulus := by
  refine LinearPMap.ext ((LinearMap.compPMap_domain _ _).trans (hT.modulus_domain hd).symm)
    fun _ _ hxM ↦ ?_
  rw [LinearMap.compPMap_apply, ContinuousLinearMap.coe_coe]
  exact hT.adjoint_polarFactor_apply_apply hd _ hxM

/-- **Adjoint of the right polar decomposition:** `T† = |T| ∘ v†` on its maximal domain
`{y : F | v† y ∈ D(|T|)}`. -/
theorem IsClosed.adjoint_eq_modulus_comp_adjoint_polarFactor {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) :
    T† = T.modulus.compLinearMap (T.polarFactor.adjoint : F →ₗ[𝕜] E) := by
  conv_lhs => rw [← hT.polarFactor_compPMap_modulus hd]
  rw [T.polarFactor.compPMap_adjoint T.modulus,
    isSelfAdjoint_def.mp (hT.isSelfAdjoint_modulus hd)]

/-- For a closed densely defined operator `T`, a vector `y : F` belongs to `D(T†)` if and only if
`v† y ∈ D(T)`. -/
theorem IsClosed.mem_adjoint_domain_iff_adjoint_polarFactor_mem {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) {y : F} :
    y ∈ T†.domain ↔ T.polarFactor.adjoint y ∈ T.domain := by
  conv_lhs => rw [hT.adjoint_eq_modulus_comp_adjoint_polarFactor hd]
  rw [mem_compLinearMap_domain, ContinuousLinearMap.coe_coe, hT.modulus_domain hd]

/-- Evaluating `T† y` as `|T| (v† y)` for `y ∈ D(T†)`. -/
theorem IsClosed.adjoint_apply_eq_modulus_apply {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) (y : T†.domain) :
    T† y = T.modulus ⟨T.polarFactor.adjoint y,
      (hT.modulus_domain hd).symm ▸
        (hT.mem_adjoint_domain_iff_adjoint_polarFactor_mem hd).mp y.property⟩ := by
  have hv : (T.polarFactor.adjoint : F →ₗ[𝕜] E) (y : F) ∈ T.modulus.domain :=
    (hT.modulus_domain hd).symm ▸
      (hT.mem_adjoint_domain_iff_adjoint_polarFactor_mem hd).mp y.property
  have hcomp := (mem_compLinearMap_domain T.modulus
    (T.polarFactor.adjoint : F →ₗ[𝕜] E)).mpr hv
  rw [LinearPMap.congr_fun (hT.adjoint_eq_modulus_comp_adjoint_polarFactor hd) y.property hcomp,
    compLinearMap_apply]
  simp only [ContinuousLinearMap.coe_coe]

private theorem isSelfAdjoint_polarFactor_compPMap_adjoint {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) :
    IsSelfAdjoint ((T.polarFactor : E →ₗ[𝕜] F).compPMap T†) := by
  rw [isSelfAdjoint_def, T.polarFactor.compPMap_adjoint T†, adjoint_adjoint hT hd]
  have hdom : (T.compLinearMap (T.polarFactor.adjoint : F →ₗ[𝕜] E)).domain =
      ((T.polarFactor : E →ₗ[𝕜] F).compPMap T†).domain := by
    ext y
    rw [mem_compLinearMap_domain, LinearMap.compPMap_domain, ContinuousLinearMap.coe_coe]
    exact (hT.mem_adjoint_domain_iff_adjoint_polarFactor_mem hd).symm
  refine LinearPMap.ext hdom fun y hy₁ hy₂ ↦ ?_
  have hyT : y ∈ T†.domain := by simpa using hy₂
  have hv₁ : T.polarFactor.adjoint y ∈ T.domain :=
    (hT.mem_adjoint_domain_iff_adjoint_polarFactor_mem hd).mp hyT
  have hrhs : ((T.polarFactor : E →ₗ[𝕜] F).compPMap T†) ⟨y, hy₂⟩ = T.polarFactor (T† ⟨y, hyT⟩) :=
    LinearMap.compPMap_apply _ (T†) ⟨y, hy₂⟩
  rw [compLinearMap_apply, hrhs, hT.adjoint_apply_eq_modulus_apply hd ⟨y, hyT⟩]
  exact (hT.polarFactor_modulus_apply hd _ hv₁).symm

/-- For a closed partial linear map `T`, the range of `T†` lies in the initial space `(ker v)ᗮ` of
its polar factor `v`. No density assumption on `T.domain` is needed: when `T.domain` is not dense,
`T†` takes the value `0`. -/
theorem IsClosed.range_adjoint_le_orthogonal_ker_polarFactor {T : E →ₗ.[𝕜] F} (hT : T.IsClosed) :
    LinearMap.range (T†).toFun ≤ T.polarFactor.kerᗮ := by
  rintro _ ⟨y, rfl⟩
  by_cases hd : Dense (T.domain : Set E)
  · rw [hT.ker_polarFactor hd]
    exact adjoint_apply_mem_orthogonal_ker T y
  · rw [toFun_eq_coe, adjoint_apply_of_not_dense hd]
    exact zero_mem _

/-- For a closed densely defined operator `T`, the modulus of `T†` is `v ∘ T†` on `D(T†)`. -/
theorem IsClosed.modulus_adjoint_eq_polarFactor_compPMap_adjoint {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) :
    (T†).modulus = (T.polarFactor : E →ₗ[𝕜] F).compPMap T† := by
  let Q := (T.polarFactor : E →ₗ[𝕜] F).compPMap T†
  have hQ : IsSelfAdjoint Q := isSelfAdjoint_polarFactor_compPMap_adjoint hT hd
  have hQpos : ∀ y : Q.domain, 0 ≤ RCLike.re ⟪Q y, (y : F)⟫ := fun y ↦ by
    have hy : (y : F) ∈ T†.domain := by simpa [Q] using y.property
    have hv : T.polarFactor.adjoint (y : F) ∈ T.modulus.domain :=
      (hT.modulus_domain hd).symm ▸ (hT.mem_adjoint_domain_iff_adjoint_polarFactor_mem hd).mp hy
    have hQy : Q y = T.polarFactor (T† ⟨y, hy⟩) := LinearMap.compPMap_apply _ (T†) y
    rw [hQy, ← T.polarFactor.adjoint_inner_right, hT.adjoint_apply_eq_modulus_apply hd ⟨y, hy⟩]
    exact hT.re_inner_modulus_nonneg hd ⟨T.polarFactor.adjoint (y : F), hv⟩
  exact ((adjoint_isClosed hd).eq_modulus (dense_adjoint_domain hT.isClosable) hQ hQpos
    ((hT.isPartialIsometry_polarFactor hd).compPMap_adjointComp
      hT.range_adjoint_le_orthogonal_ker_polarFactor)).symm

/-- For a closed densely defined operator `T`, the polar factor of `T†` is `v†`. -/
@[simp]
theorem IsClosed.polarFactor_adjoint {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) :
    (T†).polarFactor = T.polarFactor.adjoint := by
  refine ((adjoint_isClosed hd).eq_polarFactor (dense_adjoint_domain hT.isClosable) ?_
    fun y hy ↦ ?_).symm
  · rw [hT.modulus_adjoint_eq_polarFactor_compPMap_adjoint hd]
    exact (hT.isPartialIsometry_polarFactor hd).adjoint_compPMap_compPMap
      hT.range_adjoint_le_orthogonal_ker_polarFactor
  · rw [← orthogonal_range_eq_ker_adjoint hd,
      ← Submodule.orthogonal_closure (LinearMap.range T.toFun), ← hT.range_polarFactor hd,
      T.polarFactor.orthogonal_range, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hy
    exact hy

/-- **Left polar decomposition** of a closed densely defined operator: `|T†| ∘ v = T` on its
maximal domain `{x : E | v x ∈ D(|T†|)}`. -/
theorem IsClosed.modulus_adjoint_comp_polarFactor {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) :
    (T†).modulus.compLinearMap (T.polarFactor : E →ₗ[𝕜] F) = T := by
  have h := (adjoint_isClosed hd).adjoint_eq_modulus_comp_adjoint_polarFactor
    (dense_adjoint_domain hT.isClosable)
  rw [adjoint_adjoint hT hd, hT.polarFactor_adjoint hd,
    ContinuousLinearMap.adjoint_adjoint] at h
  exact h.symm

end LinearPMap

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Viewing a bounded operator `B` as a partial linear map on `⊤`, its unbounded polar factor
coincides with `ContinuousLinearMap.polarFactor B`. -/
@[simp]
theorem toPMap_top_polarFactor (B : E →L[𝕜] F) :
    ((B : E →ₗ[𝕜] F).toPMap ⊤).polarFactor = B.polarFactor := by
  have hd : Dense (((⊤ : Submodule 𝕜 E) : Set E)) := by
    rw [Submodule.top_coe]; exact dense_univ
  refine (B.isClosed_toPMap_top.eq_polarFactor hd ?_ fun x hx ↦ ?_).symm
  · rw [B.toPMap_top_modulus]
    refine LinearPMap.ext (LinearMap.compPMap_domain _ _) fun x hx₁ hx₂ ↦ ?_
    calc ((B.polarFactor : E →ₗ[𝕜] F).compPMap ((B.modulus : E →ₗ[𝕜] E).toPMap ⊤)) ⟨x, hx₁⟩
        = B.polarFactor (((B.modulus : E →ₗ[𝕜] E).toPMap ⊤) ⟨x, Submodule.mem_top⟩) :=
          LinearMap.compPMap_apply _ _ ⟨x, hx₁⟩
      _ = B.polarFactor (B.modulus x) :=
          congrArg B.polarFactor
            (LinearMap.toPMap_apply (B.modulus : E →ₗ[𝕜] E) ⊤ ⟨x, Submodule.mem_top⟩)
      _ = B x := B.polarFactor_modulus_apply x
      _ = ((B : E →ₗ[𝕜] F).toPMap ⊤) ⟨x, hx₂⟩ :=
          (LinearMap.toPMap_apply (B : E →ₗ[𝕜] F) ⊤ ⟨x, Submodule.mem_top⟩).symm
  · rw [LinearMap.toPMap_ker, top_inf_eq] at hx
    exact B.polarFactor_apply_of_mem_ker hx

end ContinuousLinearMap

namespace LinearPMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The polar factor of the zero partial linear map (on `⊤`) is zero. -/
@[simp]
theorem polarFactor_zero : (0 : E →ₗ.[𝕜] F).polarFactor = 0 := by
  have h0 : ((0 : E →L[𝕜] F) : E →ₗ[𝕜] F).toPMap ⊤ = (0 : E →ₗ.[𝕜] F) := by
    refine LinearPMap.ext (LinearMap.toPMap_domain _ _) fun _ _ _ ↦ ?_
    simp
  rw [← h0, ContinuousLinearMap.toPMap_top_polarFactor, ContinuousLinearMap.polarFactor_zero]

end LinearPMap

end

end
