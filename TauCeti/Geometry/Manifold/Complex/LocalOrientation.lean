/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Linear
public import TauCeti.Geometry.Manifold.Complex.FundamentalClass

/-!
# The canonical local orientations of a Riemann surface in centred holomorphic charts

Let `M` be a Riemann surface with its canonical homological orientation
(`TauCeti.complexHomologicalOrientation`), and let `e` be a holomorphic chart at `x`. The centred
chart `y ↦ e y - e x`, on the source of `e`, maps `x` to the origin and no other point there, so it
acts on local homology at `x`. This file proves that it carries the canonical local orientation of
`M` at `x`, read in the source of `e` through excision, to the local orientation of `ℂ` at the
origin selected by its standard orientation `Complex.orientation`
(`TauCeti.localHomologyMap_sub_complexHomologicalOrientation`).

This is the normalization asked of an oriented chart by the computation of the local index of a
section at a transverse zero as the sign of a Jacobian determinant
(`TauCeti.VectorBundleOrientation.sectionIndex_eq_sign_det_of_hasFDerivAt`), so that computation
applies to sections of complex line bundles over Riemann surfaces read in holomorphic charts.

The proof reads the canonical local orientation in the centred chart, which is holomorphic with the
same derivative as `e`, and restricts that chart to its source. It then compares the identity-chart
generator of `ℂ` with the local orientation selected by `Complex.orientation`. That comparison holds
in every real inner product space: a linear isometry to the Euclidean model commutes with the
connecting morphisms and with radial projection, and carries the sphere generator selected by an
orientation to the one selected by its image, while `Orientation.localOrientation` is defined
through the Euclidean model.
-/

public section

noncomputable section

open Module Set Topology

namespace TauCeti

/-! ### The identity-chart generator of an inner product space -/

-- These private lemmas are a temporary copy of the identity-chart comparison of the open Tau Ceti
-- pull request https://github.com/TauCetiProject/TauCeti/pull/37381, which adds them publicly to
-- `TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Linear` as
-- `LinearIsometryEquiv.localHomologyMap_localOrientationOfOrientedChart_refl` and
-- `Orientation.localOrientation_eq_localOrientationOfOrientedChart_refl`. Once that lands, this
-- section is to be deleted and its uses replaced by those lemmas.
section IdentityChart

open CategoryTheory

universe w

variable {E G : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] {n : ℕ}

/-- Radial projection onto the unit sphere commutes with a linear isometry. -/
private theorem snd_complZeroPairIso_comp_complSingletonHomotopyEquivSphere (f : E ≃ₗᵢ[ℝ] G) :
    TopPair.Hom.snd f.toContinuousLinearEquiv.complZeroPairIso.hom ≫
        TopCat.ofHom (complSingletonHomotopyEquivSphere (0 : G)).toFun =
      TopCat.ofHom (complSingletonHomotopyEquivSphere (0 : E)).toFun ≫
        TopCat.ofHom ⟨f.toLinearIsometry.unitSphereMap,
          f.toLinearIsometry.continuous_unitSphereMap⟩ := by
  ext z
  rw [ContinuousLinearEquiv.complZeroPairIso_hom]
  -- The subspace of `TopPair.ofSubset` is the subtype `{0}ᶜ` only after unfolding the pair, so
  -- each of the following three `erw` steps matches a lemma about the subtype against a term
  -- stated for the subspace of the pair: the composites, the second component of the pair map,
  -- and radial projection on `E`.
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  refine (coe_complSingletonHomotopyEquivSphere_apply (0 : G) _).trans ?_
  erw [TopPair.ofSubsetMap_snd_apply]
  simp only [TopCat.hom_ofHom, ContinuousMap.coe_mk, LinearIsometry.coe_unitSphereMap_apply]
  erw [coe_complSingletonHomotopyEquivSphere_apply]
  simp

/-- A linear isometry `f : E ≃ₗᵢ[ℝ] G` carries the local orientation of `E` at the origin selected
by `ω` in the identity chart to the local orientation of `G` at the origin selected by `ω.map f` in
the identity chart. -/
private theorem map_localOrientationOfOrientedChart_refl_linearIsometryEquiv (f : E ≃ₗᵢ[ℝ] G)
    (ω : Orientation ℝ E (Fin (n + 1))) (hE : finrank ℝ E = n + 1)
    (hG : finrank ℝ G = n + 1) (hE₀ : (0 : E) ∈ (OpenPartialHomeomorph.refl E).source)
    (hG₀ : (0 : G) ∈ (OpenPartialHomeomorph.refl G).source) :
    ((OpenPartialHomeomorph.refl E).localOrientationOfOrientedChart hE₀ ω hE).map
        f.toContinuousLinearEquiv.complZeroPairIso =
      (OpenPartialHomeomorph.refl G).localOrientationOfOrientedChart hG₀
        (ω.map _ f.toLinearEquiv) hG := by
  set R := ModuleCat.of ℤ (ULift.{w} ℤ)
  let eE := singularHomologyComplSingletonIsoOfOrientation R (OpenPartialHomeomorph.refl E) hE₀ ω hE
  let eG := singularHomologyComplSingletonIsoOfOrientation R (OpenPartialHomeomorph.refl G) hG₀
    (ω.map _ f.toLinearEquiv) hG
  -- `f` commutes with the connecting morphisms, radial projection and the sphere generators.
  have he : TopPair.singularHomologyMap f.toContinuousLinearEquiv.complZeroPairIso.hom R (n + 1) ≫
      eG.hom = eE.hom := by
    simp only [eE, eG, singularHomologyComplSingletonIsoOfOrientation_refl_hom]
    rw [← TopPair.reducedSingularHomologyδ_naturality_assoc]
    congr 1
    -- The composite is only type-correct after unfolding the subspace of the pair.
    rw [← Category.assoc]
    erw [← Functor.map_comp, snd_complZeroPairIso_comp_complSingletonHomotopyEquivSphere]
    erw [Functor.map_comp, Category.assoc]
    congr 1
    exact reducedSingularHomologySphereIsoOfOrientation_hom_naturality R ω _ f rfl hE
  apply Subtype.ext
  rw [LocalOrientation.coe_map, OpenPartialHomeomorph.coe_localOrientationOfOrientedChart,
    OpenPartialHomeomorph.coe_localOrientationOfOrientedChart]
  apply (ConcreteCategory.bijective_of_isIso eG.hom).1
  rw [← ConcreteCategory.comp_apply, he]
  exact (eE.inv_hom_id_apply 1).trans (eG.inv_hom_id_apply 1).symm

/-- In a real inner product space `E` of dimension `n + 1`, the local orientation of `E` at the
origin selected by `ω` is the one selected by `ω` in the identity chart of `E`. -/
private theorem localOrientation_eq_refl_localOrientationOfOrientedChart
    (ω : Orientation ℝ E (Fin (n + 1))) (hE : finrank ℝ E = n + 1)
    (hE₀ : (0 : E) ∈ (OpenPartialHomeomorph.refl E).source) :
    ω.localOrientation hE =
      (OpenPartialHomeomorph.refl E).localOrientationOfOrientedChart hE₀ ω hE := by
  have : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_eq_succ hE
  -- The coordinates of an orthonormal basis indexed like the Euclidean model.
  have hcard : finrank ℝ E = Fintype.card (ULift.{w} (Fin (n + 1))) := by simp [hE]
  let b := (stdOrthonormalBasis ℝ E).reindex
    (Fintype.equivOfCardEq ((finrank_eq_card_basis (stdOrthonormalBasis ℝ E).toBasis).symm.trans
      hcard))
  let f : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (ULift.{w} (Fin (n + 1))) := b.repr
  have hM : finrank ℝ (EuclideanSpace ℝ (ULift.{w} (Fin (n + 1)))) = n + 1 :=
    finrank_euclideanSpace_ulift_fin (n + 1)
  have hM₀ : (0 : EuclideanSpace ℝ (ULift.{w} (Fin (n + 1)))) ∈
      (OpenPartialHomeomorph.refl _).source := by
    rw [OpenPartialHomeomorph.refl_source]
    exact mem_univ _
  have h₁ := Orientation.localOrientation_map f.toContinuousLinearEquiv ω hE hM
  rw [Orientation.localOrientation_euclideanSpace _ hM] at h₁
  have h₂ := map_localOrientationOfOrientedChart_refl_linearIsometryEquiv f ω hE hM hE₀ hM₀
  -- Both sides are carried by `f` to the same local orientation of the model.
  have h₃ := congrArg (fun z ↦ z.map f.toContinuousLinearEquiv.complZeroPairIso.symm)
    (h₂.trans h₁)
  simp only [← LocalOrientation.map_trans, Iso.self_symm_id] at h₃
  rw [LocalOrientation.map_refl, LocalOrientation.map_refl] at h₃
  exact h₃.symm

end IdentityChart

/-! ### Centred holomorphic charts -/

open scoped _root_.Manifold ContDiff

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) 1 M]

/-- The canonical local orientation of a Riemann surface at `x` is the one selected by
`Complex.orientation` in the centred chart `e - e x`, for a holomorphic chart `e` at `x`: the
transition from `e` is a translation. -/
private theorem complexHomologicalOrientation_eq_centred {k : ℕ∞ω} [NeZero k]
    {e : OpenPartialHomeomorph M ℂ} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) k M) {x : M}
    (hx : x ∈ e.source)
    (hx₀ : x ∈ (e.trans (Homeomorph.subRight (e x)).toOpenPartialHomeomorph).source) :
    (complexHomologicalOrientation M x).val =
      ((e.trans (Homeomorph.subRight (e x)).toOpenPartialHomeomorph).localOrientationOfOrientedChart
        hx₀ Complex.orientation (n := 1) Complex.finrank_real_complex).val := by
  have hd : HasFDerivAt ((e.trans (Homeomorph.subRight (e x)).toOpenPartialHomeomorph) ∘ e.symm)
      (ContinuousLinearMap.id ℝ ℂ) (e x) := by
    refine ((hasFDerivAt_id (e x)).sub_const (e x)).congr_of_eventuallyEq ?_
    filter_upwards [e.eventually_right_inverse' hx] with y hy
    simp [hy]
  have hdet : (ContinuousLinearMap.id ℝ ℂ).det = 1 := LinearMap.det_id
  rw [complexHomologicalOrientation_apply_of_mem_maximalAtlas he hx,
    OpenPartialHomeomorph.coe_localOrientationOfOrientedChart_eq_sign_det_smul _ _ e _ hx hx₀ hd
      (hdet ▸ one_ne_zero), hdet, sign_one, SignType.coe_one, one_smul]

/-- **The canonical local orientations in a centred holomorphic chart.** For a `C^k` holomorphic
chart `e` of a Riemann surface `M` at `x`, with `k ≠ 0`, the centred chart `y ↦ e y - e x` on the
source of `e` carries the canonical local orientation of `M` at `x`, read in the source of `e`
through excision, to the local orientation of `ℂ` at the origin selected by
`Complex.orientation`. -/
theorem localHomologyMap_sub_complexHomologicalOrientation {k : ℕ∞ω} [NeZero k]
    {e : OpenPartialHomeomorph M ℂ} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) k M) {x : M}
    (hx : x ∈ e.source)
    (h : (⟨fun y : e.source ↦ e y - e x, e.continuousOn.domRestrict.sub continuous_const⟩ :
      C(e.source, ℂ)) ⁻¹' {0} ⊆ {⟨x, hx⟩}) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun y : e.source ↦ e y - e x, e.continuousOn.domRestrict.sub continuous_const⟩ :
          C(e.source, ℂ)) (S := {⟨x, hx⟩}) (T := {0}) h 2
        ((e.open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨x, hx⟩ 2).symm
          (complexHomologicalOrientation M x)).val =
      (Complex.orientation.localOrientation Complex.finrank_real_complex).val := by
  set Z := ModuleCat.of ℤ (ULift.{0} ℤ)
  -- The centred chart `e₀ = e - e x`, a chart of `M` with the same source as `e`.
  set e₀ : OpenPartialHomeomorph M ℂ := e.trans (Homeomorph.subRight (e x)).toOpenPartialHomeomorph
  have hx₀ : x ∈ e₀.source := by simpa [e₀] using hx
  have hoM := complexHomologicalOrientation_eq_centred he hx hx₀
  -- The restriction of `e₀` to the source of `e`, a chart of the subtype.
  let s : TopologicalSpace.Opens M := ⟨e.source, e.open_source⟩
  let φ : OpenPartialHomeomorph s ℂ := e₀.subtypeRestr (s := s) ⟨⟨x, hx⟩⟩
  have hxφ : (⟨x, hx⟩ : s) ∈ φ.source := by
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact hx₀
  let ι : C(e.source, M) := ⟨Subtype.val, continuous_subtype_val⟩
  have hι : ι ⁻¹' {x} ⊆ {⟨x, hx⟩} := fun y hy ↦ Subtype.ext hy
  -- The inclusion carries the local orientation selected in `φ` to that selected in `e₀`.
  have h₁ := OpenPartialHomeomorph.localHomologyMap_localOrientationOfOrientedChart
    Complex.orientation Complex.finrank_real_complex ι φ e₀ hxφ hx₀
    (Filter.Eventually.of_forall fun _ ↦ rfl) hι
  -- So the local orientation selected in `φ` is the canonical one, read in the source of `e`.
  have h₂ : ((e.open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨x, hx⟩ 2).symm
      (complexHomologicalOrientation M x)) =
      φ.localOrientationOfOrientedChart hxφ Complex.orientation Complex.finrank_real_complex := by
    rw [Equiv.symm_apply_eq]
    apply Subtype.ext
    rw [IsOpenEmbedding.coe_localOrientationEquiv, localHomologyIsoOfIsOpenEmbedding_hom, hoM]
    exact h₁.symm
  -- The centred chart carries the local orientation selected in `φ` to the identity-chart
  -- generator of `ℂ` at the origin, which is the local orientation selected by the orientation.
  -- The value `τ x = 0` enters the morphism type and the preimage condition, so it is generalized
  -- and substituted instead of rewritten.
  set τ : C(e.source, ℂ) :=
    ⟨fun y : e.source ↦ e y - e x, e.continuousOn.domRestrict.sub continuous_const⟩
  have h₃ : ∀ {c : ℂ}, τ ⟨x, hx⟩ = c → ∀ (h' : τ ⁻¹' {c} ⊆ {⟨x, hx⟩}),
      localHomologyMap Z τ (S := {⟨x, hx⟩}) (T := {c}) h' 2
          (φ.localOrientationOfOrientedChart hxφ Complex.orientation
            Complex.finrank_real_complex).val =
        ((OpenPartialHomeomorph.refl ℂ).localOrientationOfOrientedChart (by simp)
          Complex.orientation Complex.finrank_real_complex).val := by
    rintro _ rfl h'
    exact OpenPartialHomeomorph.localHomologyMap_localOrientationOfOrientedChart
      Complex.orientation Complex.finrank_real_complex τ φ (OpenPartialHomeomorph.refl ℂ) hxφ
      (by simp) (Filter.Eventually.of_forall fun _ ↦ rfl) h'
  rw [h₂, h₃ (sub_self (e x)) h,
    localOrientation_eq_refl_localOrientationOfOrientedChart _ _ (by simp)]

end TauCeti
