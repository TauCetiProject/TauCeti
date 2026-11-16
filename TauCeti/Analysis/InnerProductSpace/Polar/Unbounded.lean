/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Modulus
public import TauCeti.Analysis.InnerProductSpace.Polar.Bounded
import TauCeti.Analysis.InnerProductSpace.LinearPMap.SubmoduleAdjoint
import TauCeti.LinearAlgebra.LinearPMap.Basic

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
  (`LinearPMap.IsClosed.eq_polarFactor_iff`); jointly with `LinearPMap.IsClosed.eq_modulus_iff`,
  both factors `(v, |T|)` of `T = v |T|` are uniquely determined when `|T|` is nonnegative
  self-adjoint and `ker v = ker T`.
* **Adjoint and left polar decomposition:** `(T†).modulus = (v : E →ₗ[𝕜] F).compPMap T† = (T T†)^½`
  (`LinearPMap.IsClosed.modulus_adjoint_eq_polarFactor_compPMap_adjoint`,
  `LinearPMap.IsClosed.modulus_adjoint_eq_sqrt_compAdjoint`), `(T†).polarFactor = v†`
  (`LinearPMap.IsClosed.polarFactor_adjoint`), and `T = |T†| ∘ v` on maximal domain
  (`LinearPMap.IsClosed.modulus_adjoint_comp_polarFactor`).
* **Bounded compatibility:** for `B : E →L[𝕜] F`, `((B : E →ₗ[𝕜] F).toPMap ⊤).polarFactor` agrees
  with `ContinuousLinearMap.polarFactor B` (`ContinuousLinearMap.toPMap_top_polarFactor`).

## Main definitions and results

* `LinearPMap.polarFactor`: the polar partial isometry `E →L[𝕜] F` of a partial linear map.
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
* `LinearPMap.IsClosed.modulus_adjoint_eq_polarFactor_compPMap_adjoint` and
  `LinearPMap.IsClosed.modulus_adjoint_eq_sqrt_compAdjoint`: `|T†| = v ∘ T† = (T T†)^(1/2)`.
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
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

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

private def polarTargetCLM (T : E →ₗ.[𝕜] F) : PolarDom T →L[𝕜] F :=
  ⟨T.toFun.comp (Submodule.inclusion inf_le_left), continuous_of_discreteTopology⟩

private def polarModulusCLM (T : E →ₗ.[𝕜] F) : PolarDom T →L[𝕜] E :=
  ⟨T.modulus.toFun.comp (Submodule.inclusion inf_le_right), continuous_of_discreteTopology⟩

/-- The **polar factor** of a partial linear map `T : E →ₗ.[𝕜] F`: the bounded operator
`E →L[𝕜] F` extending `|T| x ↦ T x` by continuity to the closure of `range |T|` and by zero on its
orthogonal complement. When `T` is closed and densely defined, it is the unique partial isometry
`v` satisfying `(v : E →ₗ[𝕜] F).compPMap T.modulus = T` and vanishing on `ker T`. -/
def polarFactor (T : E →ₗ.[𝕜] F) : E →L[𝕜] F :=
  (polarTargetCLM T).factorThru (polarModulusCLM T)

private theorem norm_polarTargetCLM_eq {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) (d : PolarDom T) :
    ‖polarTargetCLM T d‖ = ‖polarModulusCLM T d‖ := by
  let u : ↥(T.domain ⊓ T.modulus.domain) := d
  exact (hT.norm_modulus_apply hd u.2.2 u.2.1).symm

private theorem range_polarModulusCLM {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) :
    (polarModulusCLM T).range = LinearMap.range T.modulus.toFun := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨d, rfl⟩
    let u : ↥(T.domain ⊓ T.modulus.domain) := d
    exact ⟨⟨u, u.2.2⟩, rfl⟩
  · rintro _ ⟨x, rfl⟩
    let d : PolarDom T := (⟨x, ⟨hT.modulus_domain hd ▸ x.2, x.2⟩⟩ : ↥(T.domain ⊓ T.modulus.domain))
    exact ⟨d, rfl⟩

private theorem range_polarTargetCLM {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) :
    (polarTargetCLM T).range = LinearMap.range T.toFun := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨d, rfl⟩
    let u : ↥(T.domain ⊓ T.modulus.domain) := d
    exact ⟨⟨u, u.2.1⟩, rfl⟩
  · rintro _ ⟨x, rfl⟩
    let d : PolarDom T :=
      (⟨x, ⟨x.2, (hT.modulus_domain hd).symm ▸ x.2⟩⟩ : ↥(T.domain ⊓ T.modulus.domain))
    exact ⟨d, rfl⟩

/-! ### Right polar decomposition, projections, and uniqueness -/

/-- The polar factor maps `|T| x` to `T x` for every `x` in their common domain `D(|T|) = D(T)`. -/
theorem IsClosed.polarFactor_modulus_apply {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) {x : E} (hxM : x ∈ T.modulus.domain) (hx : x ∈ T.domain) :
    T.polarFactor (T.modulus ⟨x, hxM⟩) = T ⟨x, hx⟩ := by
  let d : PolarDom T := (⟨x, ⟨hx, hxM⟩⟩ : ↥(T.domain ⊓ T.modulus.domain))
  exact (polarTargetCLM T).factorThru_apply_apply
    ⟨1, fun z ↦ by rw [one_mul, norm_polarTargetCLM_eq hT hd z]⟩ d

/-- **Right polar decomposition** of a closed densely defined operator: `v ∘ |T| = T`, with exact
domain equality `D(v ∘ |T|) = D(|T|) = D(T)`. -/
theorem IsClosed.polarFactor_compPMap_modulus {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) :
    (T.polarFactor : E →ₗ[𝕜] F).compPMap T.modulus = T :=
  LinearPMap.ext (hT.modulus_domain hd) fun _ hxM hx ↦ hT.polarFactor_modulus_apply hd hxM hx

/-- The polar factor vanishes on `ker T`. -/
theorem IsClosed.polarFactor_apply_of_mem_ker {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) {x : E} (hx : x ∈ T.ker) : T.polarFactor x = 0 :=
  ContinuousLinearMap.factorThru_apply_of_mem_orthogonal
    (by rwa [range_polarModulusCLM hT hd, hT.orthogonal_range_modulus hd])

/-- The polar factor has the same kernel as `T`. -/
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
    let u : ↥(T.domain ⊓ T.modulus.domain) := d
    exact LinearPMap.congr_fun hV u.2.2 u.2.1
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

private theorem adjoint_apply_apply_of_ker_eq {M : E →ₗ.[𝕜] E} {V : E →L[𝕜] F}
    (hM : IsSelfAdjoint M) (hVpi : V.IsPartialIsometry) (hVker : V.ker = M.ker) (x : M.domain) :
    V.adjoint (V (M x)) = M x := by
  have hx : M x ∈ V.kerᗮ := hVker ▸ hM.isFormalAdjoint.apply_mem_orthogonal_ker x
  have hsp := congr($(hVpi.adjoint_comp_self_eq_starProjection) (M x))
  rwa [ContinuousLinearMap.comp_apply, Submodule.starProjection_eq_self_iff.mpr hx] at hsp

private theorem compPMap_adjointComp_eq {M : E →ₗ.[𝕜] E} {V : E →L[𝕜] F}
    (hM : IsSelfAdjoint M) (hVpi : V.IsPartialIsometry) (hVker : V.ker = M.ker) :
    ((V : E →ₗ[𝕜] F).compPMap M).adjointComp = M.adjointComp := by
  have hadj : ((V : E →ₗ[𝕜] F).compPMap M)† =
      M.comp ((V.adjoint : F →ₗ[𝕜] E).toPMap (M.domain.comap (V.adjoint : F →ₗ[𝕜] E)))
        fun y ↦ y.2 := by
    rw [V.compPMap_adjoint M]
    exact congrArg (fun N : E →ₗ.[𝕜] E ↦
      N.comp ((V.adjoint : F →ₗ[𝕜] E).toPMap (N.domain.comap (V.adjoint : F →ₗ[𝕜] E)))
        fun y ↦ y.2) (isSelfAdjoint_def.mp hM)
  have hproj := adjoint_apply_apply_of_ker_eq hM hVpi hVker
  have hM'eq : M† = M := isSelfAdjoint_def.mp hM
  have hMdom : M†.domain = M.domain := congrArg domain hM'eq
  have hdom : ((V : E →ₗ[𝕜] F).compPMap M).adjointComp.domain = M.adjointComp.domain := by
    ext x
    rw [mem_adjointComp_domain, mem_adjointComp_domain, hM'eq]
    refine ⟨fun ⟨hx, hVMx⟩ ↦ ⟨hx, ?_⟩, fun ⟨hx, hMx⟩ ↦ ⟨hx, ?_⟩⟩
    · rw [hadj] at hVMx
      -- Unfold `.comp` domain membership on `hVMx`.
      change V.adjoint (V (M ⟨x, hx⟩)) ∈ M.domain at hVMx
      rwa [hproj ⟨x, hx⟩] at hVMx
    · rw [hadj]
      -- Unfold `.comp` domain membership to `V.adjoint (V (M ⟨x, hx⟩)) ∈ M.domain`.
      change V.adjoint (V (M ⟨x, hx⟩)) ∈ M.domain
      rwa [hproj ⟨x, hx⟩]
  refine LinearPMap.ext hdom fun x hx₁ hx₂ ↦ ?_
  have hxM : x ∈ M.domain := adjointComp_domain_le M hx₂
  have hMx : M ⟨x, hxM⟩ ∈ M.domain :=
    (SetLike.ext_iff.mp hMdom _).mp (mem_adjointComp_domain.mp hx₂).choose_spec
  have hVMx : V.adjoint (V (M ⟨x, hxM⟩)) ∈ M.domain := (hproj ⟨x, hxM⟩).symm ▸ hMx
  rw [adjointComp_apply _ ⟨x, hx₁⟩, adjointComp_apply M ⟨x, hx₂⟩]
  have rhs_eq : M† ⟨M ⟨x, adjointComp_domain_le M hx₂⟩,
      (mem_adjointComp_domain.mp hx₂).choose_spec⟩ = M ⟨M ⟨x, hxM⟩, hMx⟩ :=
    LinearPMap.congr_fun hM'eq (mem_adjointComp_domain.mp hx₂).choose_spec hMx
  have hVMx_comp : ((V : E →ₗ[𝕜] F).compPMap M) ⟨x, adjointComp_domain_le _ hx₁⟩ ∈
      (M.comp ((V.adjoint : F →ₗ[𝕜] E).toPMap (M.domain.comap (V.adjoint : F →ₗ[𝕜] E)))
        fun y ↦ y.2).domain := hVMx
  have lhs_eq : (((V : E →ₗ[𝕜] F).compPMap M)†)
      ⟨((V : E →ₗ[𝕜] F).compPMap M) ⟨x, adjointComp_domain_le _ hx₁⟩,
        (mem_adjointComp_domain.mp hx₁).choose_spec⟩ =
      M ⟨V.adjoint (V (M ⟨x, hxM⟩)), hVMx⟩ :=
    LinearPMap.congr_fun hadj (mem_adjointComp_domain.mp hx₁).choose_spec hVMx_comp
  rw [lhs_eq, rhs_eq]
  exact congrArg M (Subtype.ext (hproj ⟨x, hxM⟩))

private theorem isClosed_compPMap_of_isPartialIsometry {M : E →ₗ.[𝕜] E} {V : E →L[𝕜] F}
    (hM : IsSelfAdjoint M) (hVpi : V.IsPartialIsometry) (hVker : V.ker = M.ker) :
    ((V : E →ₗ[𝕜] F).compPMap M).IsClosed := by
  have hproj := adjoint_apply_apply_of_ker_eq hM hVpi hVker
  have hgraph : (((V : E →ₗ[𝕜] F).compPMap M).graph : Set (E × F)) =
      {p | (p.1, V.adjoint p.2) ∈ (M.graph : Set (E × E)) ∧ V (V.adjoint p.2) = p.2} := by
    ext ⟨x, y⟩
    rw [SetLike.mem_coe, mem_graph_iff]
    refine ⟨?_, fun ⟨hp₁, hp₂⟩ ↦ ?_⟩
    · rintro ⟨u, rfl, rfl⟩
      refine ⟨M.mem_graph_iff.mpr ⟨u, rfl, ?_⟩, ?_⟩
      · rw [LinearMap.compPMap_apply, ContinuousLinearMap.coe_coe, hproj u]
      · rw [LinearMap.compPMap_apply, ContinuousLinearMap.coe_coe, hproj u]
    · obtain ⟨u, hu₁, hu₂⟩ := M.mem_graph_iff.mp hp₁
      let u' : ((V : E →ₗ[𝕜] F).compPMap M).domain := ⟨u, u.2⟩
      refine ⟨u', hu₁, ?_⟩
      rw [LinearMap.compPMap_apply, ContinuousLinearMap.coe_coe]
      exact (congrArg V hu₂).trans hp₂
  rw [IsClosed, hgraph]
  exact (hM.isClosed.preimage
    (continuous_fst.prodMk (V.adjoint.continuous.comp continuous_snd))).inter
    (isClosed_eq (V.continuous.comp (V.adjoint.continuous.comp continuous_snd)) continuous_snd)

/-- **Joint uniqueness of the polar decomposition.** If `M : E →ₗ.[𝕜] E` is nonnegative and
self-adjoint, `V : E →L[𝕜] F` is a partial isometry with `V.ker = M.ker`, and
`(V : E →ₗ[𝕜] F).compPMap M = T`, then `M = T.modulus` and `V = T.polarFactor`.

Neither closedness nor density of `T.domain` is assumed: both follow from `T = V ∘ M`. -/
theorem eq_modulus_and_eq_polarFactor {T : E →ₗ.[𝕜] F} {M : E →ₗ.[𝕜] E} {V : E →L[𝕜] F}
    (hM : IsSelfAdjoint M) (hMpos : ∀ x : M.domain, 0 ≤ RCLike.re ⟪M x, (x : E)⟫)
    (hVpi : V.IsPartialIsometry) (hVker : V.ker = M.ker)
    (hVM : (V : E →ₗ[𝕜] F).compPMap M = T) :
    M = T.modulus ∧ V = T.polarFactor := by
  have hT : T.IsClosed := hVM ▸ isClosed_compPMap_of_isPartialIsometry hM hVpi hVker
  have hd : Dense (T.domain : Set E) := hVM ▸ hM.dense_domain
  have hM' : M = T.modulus :=
    hT.eq_modulus hd hM hMpos (hVM ▸ (compPMap_adjointComp_eq hM hVpi hVker).symm)
  refine ⟨hM', hT.eq_polarFactor hd (hM' ▸ hVM) fun x hx ↦ ?_⟩
  rw [← hT.ker_modulus hd, ← hM', ← hVker, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx
  exact hx

/-! ### Adjoint and left polar decomposition -/

/-- The adjoint of the polar factor sends `T x` back to `|T| x` on `D(T) = D(|T|)`. -/
theorem IsClosed.adjoint_polarFactor_apply_apply {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) {x : E} (hx : x ∈ T.domain) (hxM : x ∈ T.modulus.domain) :
    T.polarFactor.adjoint (T ⟨x, hx⟩) = T.modulus ⟨x, hxM⟩ := by
  let d : PolarDom T := (⟨x, ⟨hx, hxM⟩⟩ : ↥(T.domain ⊓ T.modulus.domain))
  exact congr($(ContinuousLinearMap.adjoint_factorThru_comp (norm_polarTargetCLM_eq hT hd)) d)

/-- Composing `v†` on the left with `T` recovers `|T|`: `(v† : F →ₗ[𝕜] E).compPMap T = |T|`. -/
theorem IsClosed.adjoint_polarFactor_compPMap {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) :
    (T.polarFactor.adjoint : F →ₗ[𝕜] E).compPMap T = T.modulus :=
  LinearPMap.ext (hT.modulus_domain hd).symm fun _ hx hxM ↦
    hT.adjoint_polarFactor_apply_apply hd hx hxM

/-- **Adjoint of the right polar decomposition:** `T† = |T| ∘ v†` on its maximal domain
`{y : F | v† y ∈ D(|T|)}`. -/
theorem IsClosed.adjoint_eq_modulus_comp_adjoint_polarFactor {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) :
    T† = T.modulus.comp
      ((T.polarFactor.adjoint : F →ₗ[𝕜] E).toPMap
        (T.modulus.domain.comap (T.polarFactor.adjoint : F →ₗ[𝕜] E))) fun y ↦ y.2 := by
  conv_lhs => rw [← hT.polarFactor_compPMap_modulus hd]
  rw [T.polarFactor.compPMap_adjoint T.modulus]
  exact congrArg (fun N : E →ₗ.[𝕜] E ↦
    N.comp ((T.polarFactor.adjoint : F →ₗ[𝕜] E).toPMap
      (N.domain.comap (T.polarFactor.adjoint : F →ₗ[𝕜] E))) fun y ↦ y.2)
    (isSelfAdjoint_def.mp (hT.isSelfAdjoint_modulus hd))

/-- For a closed densely defined operator `T`, a vector `y : F` belongs to `D(T†)` if and only if
`v† y ∈ D(T)`. -/
theorem IsClosed.mem_adjoint_domain_iff_adjoint_polarFactor_mem {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) {y : F} :
    y ∈ T†.domain ↔ T.polarFactor.adjoint y ∈ T.domain := by
  have hdom := congrArg domain (hT.adjoint_eq_modulus_comp_adjoint_polarFactor hd)
  -- Unfold `.comp` domain membership on the RHS to `T.polarFactor.adjoint y ∈ T.modulus.domain`.
  have hmem : y ∈ T†.domain ↔ T.polarFactor.adjoint y ∈ T.modulus.domain :=
    Iff.of_eq congr(y ∈ $hdom)
  rwa [hT.modulus_domain hd] at hmem

/-- Evaluating `T† y` as `|T| (v† y)` for `y ∈ D(T†)`. -/
theorem IsClosed.adjoint_apply_eq_modulus_apply {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) (y : T†.domain) :
    T† y = T.modulus ⟨T.polarFactor.adjoint y,
      (hT.modulus_domain hd).symm ▸
        (hT.mem_adjoint_domain_iff_adjoint_polarFactor_mem hd).mp y.2⟩ := by
  have hv : T.polarFactor.adjoint (y : F) ∈ T.modulus.domain :=
    (hT.modulus_domain hd).symm ▸ (hT.mem_adjoint_domain_iff_adjoint_polarFactor_mem hd).mp y.2
  have hcomp : (y : F) ∈ (T.modulus.comp
      ((T.polarFactor.adjoint : F →ₗ[𝕜] E).toPMap
        (T.modulus.domain.comap (T.polarFactor.adjoint : F →ₗ[𝕜] E))) fun z ↦ z.2).domain := hv
  exact LinearPMap.congr_fun (hT.adjoint_eq_modulus_comp_adjoint_polarFactor hd) y.2 hcomp

private theorem adjoint_polarFactor_polarFactor_adjoint_apply {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) (y : T†.domain) :
    T.polarFactor.adjoint (T.polarFactor (T† y)) = T† y := by
  have h := congr($(hT.adjoint_polarFactor_comp_polarFactor hd) (T† y))
  rwa [ContinuousLinearMap.comp_apply,
    Submodule.starProjection_eq_self_iff.mpr (adjoint_apply_mem_orthogonal_ker T y)] at h

private theorem isSelfAdjoint_polarFactor_compPMap_adjoint {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) :
    IsSelfAdjoint ((T.polarFactor : E →ₗ[𝕜] F).compPMap T†) := by
  rw [isSelfAdjoint_def, T.polarFactor.compPMap_adjoint T†]
  have hadj : T††.comp ((T.polarFactor.adjoint : F →ₗ[𝕜] E).toPMap
        (T††.domain.comap (T.polarFactor.adjoint : F →ₗ[𝕜] E))) (fun y ↦ y.2) =
      T.comp ((T.polarFactor.adjoint : F →ₗ[𝕜] E).toPMap
        (T.domain.comap (T.polarFactor.adjoint : F →ₗ[𝕜] E))) fun y ↦ y.2 :=
    congrArg (fun N : E →ₗ.[𝕜] F ↦
      N.comp ((T.polarFactor.adjoint : F →ₗ[𝕜] E).toPMap
        (N.domain.comap (T.polarFactor.adjoint : F →ₗ[𝕜] E))) fun y ↦ y.2)
      (hT.adjoint_adjoint hd)
  rw [hadj]
  have hdom : (T.comp ((T.polarFactor.adjoint : F →ₗ[𝕜] E).toPMap
        (T.domain.comap (T.polarFactor.adjoint : F →ₗ[𝕜] E))) fun y ↦ y.2).domain =
      ((T.polarFactor : E →ₗ[𝕜] F).compPMap T†).domain := by
    ext y
    exact (hT.mem_adjoint_domain_iff_adjoint_polarFactor_mem hd).symm
  refine LinearPMap.ext hdom fun y hy₁ hy₂ ↦ ?_
  have hv₁ : T.polarFactor.adjoint y ∈ T.domain :=
    (hT.mem_adjoint_domain_iff_adjoint_polarFactor_mem hd).mp hy₂
  -- Unfold `.comp` and `compPMap` evaluations using `hv₁ : T.polarFactor.adjoint y ∈ T.domain`.
  change T ⟨T.polarFactor.adjoint y, hv₁⟩ = T.polarFactor (T† ⟨y, hy₂⟩)
  rw [hT.adjoint_apply_eq_modulus_apply hd ⟨y, hy₂⟩]
  exact (hT.polarFactor_modulus_apply hd _ hv₁).symm

private theorem polarFactor_compPMap_adjoint_adjointComp {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) :
    ((T.polarFactor : E →ₗ[𝕜] F).compPMap T†).adjointComp = T.compAdjoint := by
  let Q := (T.polarFactor : E →ₗ[𝕜] F).compPMap T†
  have hQeq : Q† = Q := isSelfAdjoint_def.mp (isSelfAdjoint_polarFactor_compPMap_adjoint hT hd)
  have hQdom : Q†.domain = Q.domain := congrArg domain hQeq
  have hdom : Q.adjointComp.domain = T.compAdjoint.domain := by
    ext y
    rw [mem_adjointComp_domain, mem_compAdjoint_domain, hQeq]
    refine ⟨fun ⟨hy, hQy⟩ ↦ ⟨hy, ?_⟩, fun ⟨hy, hTy⟩ ↦ ⟨hy, ?_⟩⟩
    · have hmem : T.polarFactor (T† ⟨y, hy⟩) ∈ T†.domain := hQy
      rw [hT.mem_adjoint_domain_iff_adjoint_polarFactor_mem hd,
        adjoint_polarFactor_polarFactor_adjoint_apply hT hd ⟨y, hy⟩] at hmem
      exact hmem
    · have hmem : T.polarFactor (T† ⟨y, hy⟩) ∈ T†.domain :=
        (hT.mem_adjoint_domain_iff_adjoint_polarFactor_mem hd).mpr
          (by rwa [adjoint_polarFactor_polarFactor_adjoint_apply hT hd ⟨y, hy⟩])
      exact hmem
  refine LinearPMap.ext hdom fun y hy₁ hy₂ ↦ ?_
  have hyQ : y ∈ Q.domain := adjointComp_domain_le Q hy₁
  have hyT : y ∈ T†.domain := hyQ
  have hQy : Q ⟨y, hyQ⟩ ∈ Q.domain :=
    (SetLike.ext_iff.mp hQdom _).mp (mem_adjointComp_domain.mp hy₁).choose_spec
  rw [adjointComp_apply Q ⟨y, hy₁⟩, compAdjoint_apply]
  have hval : Q† ⟨Q ⟨y, adjointComp_domain_le Q hy₁⟩,
      (mem_adjointComp_domain.mp hy₁).choose_spec⟩ = Q ⟨Q ⟨y, hyQ⟩, hQy⟩ :=
    LinearPMap.congr_fun hQeq (mem_adjointComp_domain.mp hy₁).choose_spec hQy
  rw [hval]
  have hQy' : T.polarFactor (T† ⟨y, hyT⟩) ∈ T†.domain := hQy
  -- Evaluate `Q` twice using `v† (v (T† y)) = T† y` and `v (|T| (T† y)) = T (T† y)`.
  change T.polarFactor (T† ⟨T.polarFactor (T† ⟨y, hyT⟩), hQy'⟩) = T ⟨T† ⟨y, _⟩, _⟩
  have hTy_dom : T.polarFactor.adjoint (T.polarFactor (T† ⟨y, hyT⟩)) ∈ T.domain := by
    rw [adjoint_polarFactor_polarFactor_adjoint_apply hT hd ⟨y, hyT⟩]
    exact (mem_compAdjoint_domain.mp hy₂).choose_spec
  rw [hT.adjoint_apply_eq_modulus_apply hd ⟨_, hQy'⟩,
    hT.polarFactor_modulus_apply hd _ hTy_dom]
  exact congrArg T (Subtype.ext (adjoint_polarFactor_polarFactor_adjoint_apply hT hd ⟨y, hyT⟩))

/-- For a closed densely defined operator `T`, the modulus of `T†` is `v ∘ T†` on `D(T†)`. -/
theorem IsClosed.modulus_adjoint_eq_polarFactor_compPMap_adjoint {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) :
    (T†).modulus = (T.polarFactor : E →ₗ[𝕜] F).compPMap T† := by
  let Q := (T.polarFactor : E →ₗ[𝕜] F).compPMap T†
  have hQ : IsSelfAdjoint Q := isSelfAdjoint_polarFactor_compPMap_adjoint hT hd
  have hQpos : ∀ y : Q.domain, 0 ≤ RCLike.re ⟪Q y, (y : F)⟫ := fun y ↦ by
    have hy : (y : F) ∈ T†.domain := y.2
    have hv : T.polarFactor.adjoint (y : F) ∈ T.modulus.domain :=
      (hT.modulus_domain hd).symm ▸ (hT.mem_adjoint_domain_iff_adjoint_polarFactor_mem hd).mp hy
    -- Unfold `Q y` to `T.polarFactor (T† ⟨y, hy⟩)`.
    change 0 ≤ RCLike.re ⟪T.polarFactor (T† ⟨y, hy⟩), (y : F)⟫
    rw [← T.polarFactor.adjoint_inner_right, hT.adjoint_apply_eq_modulus_apply hd ⟨y, hy⟩]
    exact hT.re_inner_modulus_nonneg hd ⟨T.polarFactor.adjoint (y : F), hv⟩
  refine ((adjoint_isClosed hd).eq_modulus (dense_adjoint_domain hT.isClosable) hQ hQpos ?_).symm
  rw [← hT.compAdjoint_eq_adjoint_adjointComp]
  exact polarFactor_compPMap_adjoint_adjointComp hT hd

/-- For a closed operator `T`, the modulus of `T†` is the positive square root of `T T†`:
`|T†| = (T T†)^(1/2)`. -/
theorem IsClosed.modulus_adjoint_eq_sqrt_compAdjoint {T : E →ₗ.[𝕜] F} (hT : T.IsClosed) :
    (T†).modulus = T.compAdjoint.sqrt := by
  rw [modulus_eq_sqrt_adjointComp, hT.compAdjoint_eq_adjoint_adjointComp]

/-- For a closed densely defined operator `T`, the polar factor of `T†` is `v†`. -/
theorem IsClosed.polarFactor_adjoint {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) :
    (T†).polarFactor = T.polarFactor.adjoint := by
  refine ((adjoint_isClosed hd).eq_polarFactor (dense_adjoint_domain hT.isClosable) ?_
    fun y hy ↦ ?_).symm
  · rw [hT.modulus_adjoint_eq_polarFactor_compPMap_adjoint hd]
    refine LinearPMap.ext rfl fun y hy₁ hy₂ ↦ ?_
    -- Unfold `compPMap` twice to `v† (v (T† y)) = T† y`.
    change T.polarFactor.adjoint (T.polarFactor (T† ⟨y, hy₁⟩)) = T† ⟨y, hy₂⟩
    exact adjoint_polarFactor_polarFactor_adjoint_apply hT hd ⟨y, hy₁⟩
  · rw [← orthogonal_range_eq_ker_adjoint hd,
      ← Submodule.orthogonal_closure (LinearMap.range T.toFun), ← hT.range_polarFactor hd,
      T.polarFactor.orthogonal_range, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hy
    exact hy

/-- **Left polar decomposition** of a closed densely defined operator: `|T†| ∘ v = T` on its
maximal domain `{x : E | v x ∈ D(|T†|)}`. -/
theorem IsClosed.modulus_adjoint_comp_polarFactor {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) :
    (T†).modulus.comp ((T.polarFactor : E →ₗ[𝕜] F).toPMap
        ((T†).modulus.domain.comap (T.polarFactor : E →ₗ[𝕜] F))) (fun x ↦ x.2) = T := by
  have h := (adjoint_isClosed hd).adjoint_eq_modulus_comp_adjoint_polarFactor
    (dense_adjoint_domain hT.isClosable)
  have hW : (T†).polarFactor.adjoint = T.polarFactor := by
    rw [hT.polarFactor_adjoint hd, ContinuousLinearMap.adjoint_adjoint]
  have hrhs := congrArg (fun W : E →L[𝕜] F ↦
    (T†).modulus.comp ((W : E →ₗ[𝕜] F).toPMap
      ((T†).modulus.domain.comap (W : E →ₗ[𝕜] F))) fun x ↦ x.2) hW
  exact hrhs.symm.trans (h.symm.trans (hT.adjoint_adjoint hd))

end LinearPMap

namespace ContinuousLinearMap

section Topological

variable {R E F : Type*} [CommRing R]
  [AddCommGroup E] [Module R E] [TopologicalSpace E]
  [AddCommGroup F] [Module R F] [TopologicalSpace F] [T2Space F]

/-- Viewing a continuous linear map `B` into a `T₂` space as a partial linear map on `⊤` produces a
closed partial linear map. -/
theorem isClosed_toPMap_top (B : E →L[R] F) : ((B : E →ₗ[R] F).toPMap ⊤).IsClosed := by
  have h : (((B : E →ₗ[R] F).toPMap ⊤).graph : Set (E × F)) = {p | B p.1 = p.2} := by
    ext ⟨x, y⟩
    simp [LinearPMap.mem_graph_iff]
  rw [LinearPMap.IsClosed, h]
  exact isClosed_eq (B.continuous.comp continuous_fst) continuous_snd

end Topological

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
    refine LinearPMap.ext rfl fun x _ _ ↦ ?_
    exact B.polarFactor_modulus_apply x
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
  have h0 : ((0 : E →L[𝕜] F) : E →ₗ[𝕜] F).toPMap ⊤ = (0 : E →ₗ.[𝕜] F) :=
    LinearPMap.ext rfl fun _ _ _ ↦ rfl
  rw [← h0, ContinuousLinearMap.toPMap_top_polarFactor, ContinuousLinearMap.polarFactor_zero]

end LinearPMap

end

end
