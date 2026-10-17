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

/-!
# Bounded perturbations and unitary conjugation of partial linear maps

* `LinearPMap.isSelfAdjoint_toPMap_top`: a bounded self-adjoint operator,
  viewed as a partial map on the full domain, is self-adjoint.
* `LinearPMap.isSelfAdjoint_perturb_bounded`: adding a bounded self-adjoint
  operator to a self-adjoint partial map preserves self-adjointness.
* `LinearPMap.unitaryConj`: transports a partial map, including its domain,
  along a linear isometric equivalence. Self-adjointness is preserved by this
  conjugation.

The algebraic, domain-defined perturbation API is in
`TauCeti.LinearAlgebra.LinearPMap.Perturbation`.

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
  set B := T.toLinearMap +ᵥ A with hB
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

section UnitaryConj

variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H']

/-- The unitary conjugate `U A U⁻¹`, with domain obtained by transporting
`A.domain` along the linear isometric equivalence `U`. -/
noncomputable def unitaryConj (U : H ≃ₗᵢ[𝕜] H') (A : H →ₗ.[𝕜] H) : H' →ₗ.[𝕜] H' where
  domain := A.domain.comap U.symm.toLinearMap
  toFun :=
    let D : Submodule 𝕜 H' := A.domain.comap U.symm.toLinearMap
    let p : D →ₗ[𝕜] A.domain :=
      (U.symm.toLinearMap.comp D.subtype).codRestrict A.domain (fun x => x.property)
    U.toLinearMap.comp (A.toFun.comp p)

/-- Membership in the conjugated domain is membership after transport by `U.symm`. -/
@[simp] theorem mem_unitaryConj_domain_iff {U : H ≃ₗᵢ[𝕜] H'} {A : H →ₗ.[𝕜] H} {x : H'} :
    x ∈ (unitaryConj U A).domain ↔ U.symm x ∈ A.domain := Iff.rfl

/-- Evaluate the unitary conjugate on its transported domain. -/
@[simp]
theorem unitaryConj_apply (U : H ≃ₗᵢ[𝕜] H') (A : H →ₗ.[𝕜] H)
    (x : (unitaryConj U A).domain) :
    unitaryConj U A x =
      U (A ⟨U.symm (x : H'),
        (mem_unitaryConj_domain_iff (U := U) (A := A)).mp x.property⟩) := by
  rfl
/-- `U` carries `A.domain` into the conjugated domain.  This is the membership
witness needed to state `unitaryConj_apply_map`, which is the form of the
conjugation law that is usable from the *original* domain. -/
theorem map_mem_unitaryConj_domain (U : H ≃ₗᵢ[𝕜] H') (A : H →ₗ.[𝕜] H) (y : A.domain) :
    U (y : H) ∈ (unitaryConj U A).domain := by
  rw [mem_unitaryConj_domain_iff, U.symm_apply_apply]
  exact y.2

/-- **The intertwining law**, in the form consumers want: conjugation composed
with `U` is `U` composed with `A`, indexed by the *original* domain rather than
the conjugated one. -/
theorem unitaryConj_apply_map (U : H ≃ₗᵢ[𝕜] H') (A : H →ₗ.[𝕜] H) (y : A.domain) :
    unitaryConj U A ⟨U (y : H), map_mem_unitaryConj_domain U A y⟩ = U (A y) := by
  rw [unitaryConj_apply]
  congr 1
  exact congrArg A (Subtype.ext (U.symm_apply_apply (y : H)))

section UnitaryConjSelfAdjoint

variable [CompleteSpace H] [CompleteSpace H']

/-- Unitary conjugation preserves self-adjointness, transporting the domain. -/
theorem isSelfAdjoint_unitaryConj {U : H ≃ₗᵢ[𝕜] H'} {A : H →ₗ.[𝕜] H}
    (hA : IsSelfAdjoint A) : IsSelfAdjoint (unitaryConj U A) := by
  set B := unitaryConj U A with hB
  have hB_apply (x : B.domain) (hx : U.symm (x : H') ∈ A.domain) :
      B x = U (A ⟨U.symm (x : H'), hx⟩) := by
    simpa only [hB] using (unitaryConj_apply U A x)
  have hdenseA : Dense (A.domain : Set H) := hA.dense_domain
  have hsymA : A.IsFormalAdjoint A := hA.isFormalAdjoint
  -- `U` is a surjective isometry, so it carries a dense set to a dense set
  have hdenseB : Dense (B.domain : Set H') := by
    have himg : (U : H ≃ₗᵢ[𝕜] H') '' (A.domain : Set H) ⊆ (B.domain : Set H') := by
      rintro _ ⟨w, hw, rfl⟩
      simpa only [hB, SetLike.mem_coe] using (map_mem_unitaryConj_domain U A ⟨w, hw⟩)
    exact Dense.mono himg ((U.toHomeomorph.isDenseEmbedding).dense_image.mpr hdenseA)
  -- symmetry of `B`
  have hsymB : B.IsFormalAdjoint B := by
    intro x y
    have hx : U.symm (x : H') ∈ A.domain := by
      apply (mem_unitaryConj_domain_iff (U := U) (A := A)).mp
      simpa only [hB] using x.property
    have hy : U.symm (y : H') ∈ A.domain := by
      apply (mem_unitaryConj_domain_iff (U := U) (A := A)).mp
      simpa only [hB] using y.property
    calc ⟪B x, (y : H')⟫_𝕜
        = ⟪U (A ⟨U.symm (x : H'), hx⟩), U (U.symm (y : H'))⟫_𝕜 := by
          rw [U.apply_symm_apply, hB_apply x hx]
      _ = ⟪A ⟨U.symm (x : H'), hx⟩, U.symm (y : H')⟫_𝕜 := U.inner_map_map _ _
      _ = ⟪U.symm (x : H'), A ⟨U.symm (y : H'), hy⟩⟫_𝕜 :=
          hsymA ⟨U.symm (x : H'), hx⟩ ⟨U.symm (y : H'), hy⟩
      _ = ⟪U (U.symm (x : H')), U (A ⟨U.symm (y : H'), hy⟩)⟫_𝕜 :=
          (U.inner_map_map _ _).symm
      _ = ⟪(x : H'), B y⟫_𝕜 := by
          rw [U.apply_symm_apply, hB_apply y hy]
  -- the adjoint domain of `B` sits inside `B`'s domain
  have hsub : ∀ y : H', y ∈ (_root_.LinearPMap.adjoint B).domain → y ∈ B.domain := by
    intro y hy
    have hform := _root_.LinearPMap.adjoint_isFormalAdjoint (T := B) hdenseB ⟨y, hy⟩
    rw [hB, mem_unitaryConj_domain_iff]
    have hwit : ∀ u : A.domain,
        ⟪U.symm ((_root_.LinearPMap.adjoint B) ⟨y, hy⟩), (u : H)⟫_𝕜 = ⟪U.symm y, A u⟫_𝕜 := by
      intro u
      have h := hform ⟨U (u : H), map_mem_unitaryConj_domain U A u⟩
      rw [unitaryConj_apply_map] at h
      calc ⟪U.symm ((_root_.LinearPMap.adjoint B) ⟨y, hy⟩), (u : H)⟫_𝕜
          = ⟪(_root_.LinearPMap.adjoint B) ⟨y, hy⟩, U (u : H)⟫_𝕜 := by
            rw [← U.inner_map_map (U.symm _) (u : H), U.apply_symm_apply]
        _ = ⟪y, U (A u)⟫_𝕜 := h
        _ = ⟪U.symm y, A u⟫_𝕜 := by
            rw [← U.inner_map_map (U.symm y) (A u), U.apply_symm_apply]
    have hmem : U.symm y ∈ (_root_.LinearPMap.adjoint A).domain :=
      _root_.LinearPMap.mem_adjoint_domain_of_exists _
        ⟨U.symm ((_root_.LinearPMap.adjoint B) ⟨y, hy⟩), hwit⟩
    rwa [_root_.LinearPMap.isSelfAdjoint_def.mp hA] at hmem
  have hle : B ≤ _root_.LinearPMap.adjoint B :=
    _root_.LinearPMap.IsFormalAdjoint.le_adjoint (T := B) (S := B) hdenseB hsymB
  have hdomeq : B.domain = (_root_.LinearPMap.adjoint B).domain :=
    le_antisymm hle.1 hsub
  rw [_root_.LinearPMap.isSelfAdjoint_def]
  exact (_root_.LinearPMap.eq_of_le_of_domain_eq hle hdomeq).symm

end UnitaryConjSelfAdjoint

end UnitaryConj

end HilbertSpace

end LinearPMap
