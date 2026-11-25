/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
/-
Adapted from: Spectra (https://github.com/adambornemann-glitch/Spectra),
`Spectra/Operator/KatoRellich.lean` and `Spectra/Operator/Bounded.lean`,
commit `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`,
Copyright (c) 2026 Spectra Formalization Project,
released under the Apache 2.0 license.  The full attribution and the changes
made here are recorded in the `## Provenance` section of the module
documentation below.
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint
public import TauCeti.Topology.Algebra.Module.LinearPMap.Conj
public import TauCeti.LinearAlgebra.LinearPMap.Basic

/-!
# Bounded perturbations, compositions, and unitary conjugation of partial linear maps

* `LinearPMap.isSelfAdjoint_toPMap_top`: a bounded self-adjoint operator,
  viewed as a partial map on the full domain, is self-adjoint.
* `LinearPMap.isSelfAdjoint_perturb_bounded`: adding a bounded self-adjoint
  operator to a self-adjoint partial map preserves self-adjointness.
* `LinearPMap.adjoint_conj`: for any partial map `A` and a linear isometric
  equivalence `U`, the adjoint of the conjugate `U A U⁻¹` (see `LinearPMap.conj`)
  is `U A† U⁻¹`.
* `LinearPMap.isSelfAdjoint_conj_iff`: `U A U⁻¹` is self-adjoint exactly when
  `A` is.
* `ContinuousLinearMap.compPMap_adjoint`: the adjoint of `W ∘ M` for a bounded
  operator `W` and an arbitrary partial linear map `M` is `M† ∘ W†` on its maximal
  domain.

The algebraic, domain-defined perturbation API is in
`TauCeti.LinearAlgebra.LinearPMap.Perturbation`, and conjugation by linear and
continuous linear equivalences in `TauCeti.LinearAlgebra.LinearPMap.Conj` and
`TauCeti.Topology.Algebra.Module.LinearPMap.Conj`.

## Provenance

* **Original repository:** Spectra, commit `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`.
* **Original declarations:** `Spectra.Operator.perturbedOp` (with
  `perturbedOp_domain`, `perturbedOp_apply`) in `Spectra/Operator/KatoRellich.lean`;
  the self-adjointness obligation inside `Spectra.Operator.SelfAdjointOperator.ofBounded`
  in `Spectra/Operator/Bounded.lean`.
* **Original authors / copyright / licence:** Copyright (c) 2026 Spectra
  Formalization Project, Apache 2.0.  Apache 2.0 §4(b): **modified** — see below.
  §4(c): notices retained here and in the file header.
* **Adaptation:** the bounded self-adjointness result is stated using Mathlib's
  `LinearPMap` and its `VAdd` operation.
-/

public section

namespace LinearPMap

open scoped InnerProductSpace


section HilbertSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

section Bounded

variable [CompleteSpace H]

/-- A bounded self-adjoint operator is self-adjoint as a partial map on `⊤`. -/
theorem isSelfAdjoint_toPMap_top {T : H →L[𝕜] H} (hT : IsSelfAdjoint T) :
    IsSelfAdjoint ((T : H →ₗ[𝕜] H).toPMap ⊤) := by
  have hdense : Dense ((⊤ : Submodule 𝕜 H) : Set H) := by
    rw [Submodule.top_coe]; exact dense_univ
  have hTadj : ContinuousLinearMap.adjoint T = T :=
    (ContinuousLinearMap.star_eq_adjoint T).symm.trans hT
  rw [_root_.LinearPMap.isSelfAdjoint_def,
    ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense T hdense, hTadj]

/-- **Bounded Kato--Rellich.** Adding a bounded self-adjoint endomorphism to a
self-adjoint partial map preserves self-adjointness and its domain. -/
theorem isSelfAdjoint_perturb_bounded {A : H →ₗ.[𝕜] H} (hA : IsSelfAdjoint A)
    {T : H →L[𝕜] H} (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (T.toLinearMap +ᵥ A) := by
  set B := T.toLinearMap +ᵥ A
  have hB_apply (x : A.domain) : B x = T (x : H) + A x := by
    -- The argument type depends on the partial map's domain. Rewriting `hB`
    -- under the application is not well-typed; unfold the local abbreviation
    -- without rewriting the dependent argument, then use the public law.
    change (T.toLinearMap +ᵥ A) x = T (x : H) + A x
    exact LinearPMap.vadd_apply T.toLinearMap A x
  have hdense : Dense (A.domain : Set H) := hA.dense_domain
  have hsymA : A.IsFormalAdjoint A := hA.isFormalAdjoint
  have hTadj : ContinuousLinearMap.adjoint T = T :=
    (ContinuousLinearMap.star_eq_adjoint T).symm.trans hT
  have hTsym : ∀ u v : H, ⟪T u, v⟫_𝕜 = ⟪u, T v⟫_𝕜 := by
    intro u v
    rw [← ContinuousLinearMap.adjoint_inner_left, hTadj]
  -- `B` is symmetric
  have hsymB : B.IsFormalAdjoint B := by
    intro x y
    rw [hB_apply x, hB_apply y, inner_add_left, inner_add_right,
      hsymA x y, hTsym (x : H) (y : H)]
  -- `T` contributes a continuous term, so `B` and `A` have the same adjoint domain
  have hsub : ∀ y : H, y ∈ (_root_.LinearPMap.adjoint B).domain → y ∈ A.domain := by
    intro y hy
    rw [_root_.LinearPMap.mem_adjoint_domain_iff] at hy
    have hTcont : Continuous fun x : A.domain => ⟪y, T (x : H)⟫_𝕜 :=
      ((innerSL 𝕜 y).comp (T.comp (Submodule.subtypeL A.domain))).continuous
    have hAcont : Continuous ((innerₛₗ 𝕜 y).comp A.toFun) := by
      have hsplit : (fun x : A.domain => ((innerₛₗ 𝕜 y).comp A.toFun) x)
          = fun x : A.domain =>
              ((innerₛₗ 𝕜 y).comp B.toFun) x - ⟪y, T (x : H)⟫_𝕜 := by
        funext x
        simp only [LinearMap.comp_apply, LinearPMap.toFun_eq_coe,
          innerₛₗ_apply_apply]
        rw [hB_apply x, inner_add_right]
        abel
      have hcont : Continuous fun x : A.domain => ((innerₛₗ 𝕜 y).comp A.toFun) x := by
        rw [hsplit]; exact hy.sub hTcont
      exact hcont
    have hmemA : y ∈ (_root_.LinearPMap.adjoint A).domain :=
      (_root_.LinearPMap.mem_adjoint_domain_iff (T := A) y).mpr hAcont
    rwa [_root_.LinearPMap.isSelfAdjoint_def.mp hA] at hmemA
  -- symmetry gives `B ≤ B†`; the domain inclusion above makes it an equality
  have hle : B ≤ _root_.LinearPMap.adjoint B :=
    _root_.LinearPMap.IsFormalAdjoint.le_adjoint (T := B) (S := B) hdense hsymB
  have hdomeq : B.domain = (_root_.LinearPMap.adjoint B).domain :=
    le_antisymm hle.1 (fun y hy => hsub y hy)
  rw [_root_.LinearPMap.isSelfAdjoint_def]
  exact (_root_.LinearPMap.eq_of_le_of_domain_eq hle hdomeq).symm


end Bounded

section Conj

variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H']

/-! The conjugate `U A U⁻¹` by a linear isometric equivalence `U` is written
`A.conj ((U : H ≃L[𝕜] H') : H ≃ₗ[𝕜] H')`, the form in which the conjugation lemmas for continuous
linear equivalences (density, closedness, resolvents, spectra) apply. -/

/-- Conjugation by a linear isometric equivalence preserves formal adjointness. -/
theorem IsFormalAdjoint.conj {T S : H →ₗ.[𝕜] H} (h : T.IsFormalAdjoint S) (U : H ≃ₗᵢ[𝕜] H') :
    (T.conj ((U : H ≃L[𝕜] H') : H ≃ₗ[𝕜] H')).IsFormalAdjoint
      (S.conj ((U : H ≃L[𝕜] H') : H ≃ₗ[𝕜] H')) := fun x y ↦ by
  simpa [LinearIsometryEquiv.inner_map_eq_flip] using
    h ⟨_, mem_conj_domain_iff.1 x.property⟩ ⟨_, mem_conj_domain_iff.1 y.property⟩

variable [CompleteSpace H] [CompleteSpace H']

/-- A vector lies in the domain of the adjoint of `U A U⁻¹` exactly when its preimage under `U`
lies in the domain of `A†`. -/
private theorem mem_adjoint_conj_domain_iff {A : H →ₗ.[𝕜] H} (U : H ≃ₗᵢ[𝕜] H') {y : H'} :
    y ∈ (A.conj ((U : H ≃L[𝕜] H') : H ≃ₗ[𝕜] H'))†.domain ↔ U.symm y ∈ A†.domain := by
  have hφ : Continuous fun x : (A.conj ((U : H ≃L[𝕜] H') : H ≃ₗ[𝕜] H')).domain ↦
      (⟨U.symm x, by simpa using mem_conj_domain_iff.1 x.property⟩ : A.domain) :=
    (U.symm.continuous.comp continuous_subtypeVal).subtype_mk _
  have hψ : Continuous fun x : A.domain ↦
      (⟨U x, map_mem_conj_domain x⟩ : (A.conj ((U : H ≃L[𝕜] H') : H ≃ₗ[𝕜] H')).domain) :=
    (U.continuous.comp continuous_subtypeVal).subtype_mk _
  rw [mem_adjoint_domain_iff, mem_adjoint_domain_iff]
  refine ⟨fun h ↦ (h.comp hψ).congr fun x ↦ ?_, fun h ↦ (h.comp hφ).congr fun x ↦ ?_⟩
  · simp [LinearIsometryEquiv.inner_map_eq_flip]
  · simp [LinearIsometryEquiv.inner_map_eq_flip]

/-- **Adjoint of a unitary conjugate.** For a linear isometric equivalence `U`,
`(U A U⁻¹)† = U A† U⁻¹`. -/
@[simp]
theorem adjoint_conj (A : H →ₗ.[𝕜] H) (U : H ≃ₗᵢ[𝕜] H') :
    (A.conj ((U : H ≃L[𝕜] H') : H ≃ₗ[𝕜] H'))† = (A†).conj ((U : H ≃L[𝕜] H') : H ≃ₗ[𝕜] H') := by
  by_cases hA : Dense (A.domain : Set H)
  · have hA' : Dense ((A.conj ((U : H ≃L[𝕜] H') : H ≃ₗ[𝕜] H')).domain : Set H') := by
      simpa using hA
    refine le_antisymm ?_ (((adjoint_isFormalAdjoint hA).symm.conj U).le_adjoint hA')
    rw [← conj_le_conj_iff (e := ((U : H ≃L[𝕜] H') : H ≃ₗ[𝕜] H').symm), conj_conj_symm]
    have h := (adjoint_isFormalAdjoint hA').symm.conj U.symm
    rw [LinearIsometryEquiv.toContinuousLinearEquiv_symm, ContinuousLinearEquiv.toLinearEquiv_symm,
      conj_conj_symm] at h
    exact h.le_adjoint hA
  · -- Off dense domains both adjoints take the junk value `0`, on the same domain.
    have hA' : ¬Dense ((A.conj ((U : H ≃L[𝕜] H') : H ≃ₗ[𝕜] H')).domain : Set H') := by
      simpa using hA
    refine ext (Submodule.ext fun y ↦ ?_) fun y hy hy' ↦ ?_
    · simp [mem_adjoint_conj_domain_iff]
    · rw [adjoint_apply_of_not_dense hA', conj_apply, adjoint_apply_of_not_dense hA,
        _root_.map_zero]

/-- Conjugation by a linear isometric equivalence preserves self-adjointness. -/
theorem _root_.IsSelfAdjoint.conj {A : H →ₗ.[𝕜] H} (hA : IsSelfAdjoint A)
    (U : H ≃ₗᵢ[𝕜] H') : IsSelfAdjoint (A.conj ((U : H ≃L[𝕜] H') : H ≃ₗ[𝕜] H')) := by
  rw [isSelfAdjoint_def, adjoint_conj, isSelfAdjoint_def.1 hA]

/-- A unitary conjugate `U A U⁻¹` is self-adjoint exactly when `A` is. -/
@[simp]
theorem isSelfAdjoint_conj_iff {A : H →ₗ.[𝕜] H} (U : H ≃ₗᵢ[𝕜] H') :
    IsSelfAdjoint (A.conj ((U : H ≃L[𝕜] H') : H ≃ₗ[𝕜] H')) ↔ IsSelfAdjoint A :=
  ⟨fun h ↦ by simpa using h.conj U.symm, (·.conj U)⟩

end Conj

end HilbertSpace

end LinearPMap

namespace ContinuousLinearMap

open scoped InnerProductSpace LinearPMap

variable {𝕜 G E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The adjoint of a bounded operator composed on the left with an arbitrary partial linear map
`M` is `M† ∘ W†` on its maximal domain `{y | W† y ∈ M†.domain}`. No closedness or density
assumption on `M` is needed. -/
theorem compPMap_adjoint (W : E →L[𝕜] F) (M : G →ₗ.[𝕜] E) :
    ((W : E →ₗ[𝕜] F).compPMap M)† = M†.compLinearMap (W.adjoint : F →ₗ[𝕜] E) := by
  have hdom : ((W : E →ₗ[𝕜] F).compPMap M)†.domain =
      (M†.compLinearMap (W.adjoint : F →ₗ[𝕜] E)).domain := by
    ext y
    rw [LinearPMap.mem_compLinearMap_domain, coe_coe,
      LinearPMap.mem_adjoint_domain_iff, LinearPMap.mem_adjoint_domain_iff]
    have hfun : ⇑((innerₛₗ 𝕜 y).comp ((W : E →ₗ[𝕜] F).compPMap M).toFun) =
        ⇑((innerₛₗ 𝕜 (W.adjoint y)).comp M.toFun) := by
      funext x
      exact (W.adjoint_inner_left (M x) y).symm
    exact Iff.of_eq congr(Continuous $hfun)
  refine LinearPMap.ext hdom fun y hy hy' ↦ ?_
  rw [LinearPMap.compLinearMap_apply]
  by_cases hd : Dense (M.domain : Set G)
  · have hd' : Dense (((W : E →ₗ[𝕜] F).compPMap M).domain : Set G) := by
      rwa [LinearMap.compPMap_domain]
    refine LinearPMap.adjoint_apply_eq hd' ⟨y, hy⟩ fun x ↦ ?_
    let xM : M.domain := ⟨x, by simpa using x.property⟩
    have hx : ((W : E →ₗ[𝕜] F).compPMap M) x = W (M xM) := LinearMap.compPMap_apply _ M x
    rw [hx, LinearPMap.adjoint_isFormalAdjoint hd _ xM]
    exact W.adjoint_inner_left (M xM) y
  · have hd' : ¬Dense (((W : E →ₗ[𝕜] F).compPMap M).domain : Set G) := by
      rwa [LinearMap.compPMap_domain]
    rw [LinearPMap.adjoint_apply_of_not_dense hd' ⟨y, hy⟩,
      LinearPMap.adjoint_apply_of_not_dense hd]

end ContinuousLinearMap
