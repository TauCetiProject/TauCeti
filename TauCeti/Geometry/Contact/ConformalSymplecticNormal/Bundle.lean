/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.ConformalSymplecticNormal
public import TauCeti.Geometry.Contact.Levi
public import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.SmulRight
public import TauCeti.Geometry.Manifold.VectorBundle.ConstantRank
public import TauCeti.Geometry.Manifold.VectorBundle.Hom.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Quotient
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Subbundle
public import TauCeti.Geometry.Manifold.VectorBundle.Trivial

/-!
# The conformal symplectic normal bundle of an isotropic immersion

Let `D` be a smooth contact structure on a Hausdorff manifold `M`, and let `f : N → M` be a smooth
isotropic immersion: `f` is horizontal for `D` (`TauCeti.IsHorizontalMap`) and its differentials
are injective. At each `y : N` the conformal symplectic normal space
`(T_y N)^⊥ ⧸ T_y N` (`TauCeti.ConformalSymplecticNormal`) is the quotient of the Levi orthogonal
`(T_y N)^⊥ ⊆ D_(f y)` of the tangent image by the tangent image, with the nondegenerate form
induced by the Levi form, valued in the contact line. This file shows that these spaces form a
smooth vector bundle over a nonempty `N`, of rank `dim M - 2 dim N - 1`: the conformal symplectic
normal bundle of `f`, the normal data of the isotropic neighbourhood theorem.

* **Local frames.** The Levi orthogonal `TauCeti.leviOrthogonal J D f y ⊆ T_(f y) M` of the
  tangent image is described by a local defining form (`TauCeti.mem_leviOrthogonal_iff_of_ker_eq`)
  and has dimension `dim M - dim N - 1` (`TauCeti.IsHorizontalMap.finrank_leviOrthogonal_add`).
  Near each point of `N`, with a local contact form `α` defining `D` and a local frame `eᵢ` of
  `TN`, the Levi orthogonals are the kernels of the smooth bundle map
  `f^* TM → ℝ^(1 + dim N)`, `v ↦ (α (v), (dα (df eᵢ, v))ᵢ)`, which is fibrewise onto by the
  dimension count. So they form a smooth subbundle of `f^* TM`
  (`TauCeti.hasLocalContMDiffSubbundleFrames_leviOrthogonal`), and, read in `D`, of the pullback
  `f^* D` of the contact structure (`TauCeti.hasLocalContMDiffSubbundleFrames_orthogonalBilin`).
* **The bundle.** The tangent images form a smooth subbundle of the bundle of Levi orthogonals
  (`TauCeti.hasLocalContMDiffSubbundleFrames_comap_range`), and the quotient is the conformal
  symplectic normal bundle (`TauCeti.conformalSymplecticNormalPrebundle`,
  `TauCeti.conformalSymplecticNormalPrebundle_eq`), a smooth vector bundle
  (`TauCeti.contMDiffVectorBundle_conformalSymplecticNormalPrebundle`).

The bundle is defined from `D` alone: no contact form or coorientation is chosen, so it applies to
contact structures that are not the kernel of any global one-form. Local defining forms enter only
the proof that local frames exist.

## Main definitions

* `TauCeti.leviOrthogonalPullback`: the Levi orthogonals of the tangent images of a map, as
  subspaces of the fibres of the pullback of the contact structure.
* `TauCeti.conformalSymplecticNormalPrebundle`: the conformal symplectic normal bundle of a smooth
  isotropic immersion, as a vector prebundle with fibres `TauCeti.ConformalSymplecticNormal`.

## Main results

* `TauCeti.hasLocalContMDiffSubbundleFrames_leviOrthogonal`,
  `TauCeti.hasLocalContMDiffSubbundleFrames_orthogonalBilin`: the Levi orthogonals of a smooth
  isotropic immersion have smooth local frames.
* `TauCeti.contMDiffVectorBundle_leviOrthogonalPullback`: the Levi orthogonals form a smooth
  vector bundle.
* `TauCeti.hasLocalContMDiffSubbundleFrames_comap_range`: the tangent images have smooth local
  frames inside the bundle of Levi orthogonals.
* `TauCeti.IsHorizontalMap.card_add_card_eq_finrank`: the rank count `dim N + (dim M - 2 dim N - 1)
  = dim M - dim N - 1` for the quotient.
* `TauCeti.conformalSymplecticNormalPrebundle_eq`: the conformal symplectic normal bundle is the
  quotient prebundle of the bundle of Levi orthogonals by the tangent images.
* `TauCeti.contMDiffVectorBundle_conformalSymplecticNormalPrebundle`: the conformal symplectic
  normal bundle is a smooth vector bundle of rank `dim M - 2 dim N - 1`.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Section 2.5 (the conformal symplectic normal bundle).
* S. Courte and S. Guillermou, *Introduction to symplectic and contact geometry*, course notes,
  Université Grenoble Alpes (2018), Proposition 3.5, p. 35 (the conformal symplectic normal bundle
  with values in the contact line).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 10
  (local frame criteria for subbundles and quotient bundles).
-/

public section

noncomputable section

open Set Filter Function Module Bundle
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  {D : Π x : M, Submodule ℝ (TangentSpace I x)} {f : N → M} {y : N}

omit [CompleteSpace E] [IsManifold I 2 M] in
/-- `C^(∞ + 1)` charts on the target manifold, needed by the smooth vector bundle structure of a
smooth distribution (`TauCeti.IsContMDiffDistribution.contMDiffVectorBundle`) at smoothness `∞`. -/
local instance instIsManifoldConformalSymplecticNormalTarget [IsManifold I ∞ M] :
    IsManifold I ((∞ : WithTop ℕ∞) + 1) M :=
  IsManifold.of_le (n := ∞) (by simp)

/-- `C^(∞ + 1)` charts on the source manifold, as for the target. -/
local instance instIsManifoldConformalSymplecticNormalSource [IsManifold J ∞ N] :
    IsManifold J ((∞ : WithTop ℕ∞) + 1) N :=
  IsManifold.of_le (n := ∞) (by simp)

/-! ### Local frames of the Levi orthogonal -/

section Frames

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I ∞ M] [IsManifold J ∞ N]
  [T2Space M] {K : Type*} [FunLike K N M] [ContinuousMapClass K N M]

variable (f) in
/-- The bundle map `f^* TM → ℝ^(k + 1)`, `v ↦ (α (v), (dα (Y i, v))ᵢ)`, of a one-form `α` and
sections `Y i` of `f^* TM`. Where `α` defines a contact structure `D` and the `Y i` form a basis of
the tangent image of `f`, its kernel is the Levi orthogonal. -/
private def leviOrthogonalMap {k : ℕ} (α : SmoothForm I M ℝ 1)
    (Y : Fin k → Π y, TangentSpace I (f y)) (y : N) :
    ((f : N → M) *ᵖ (TangentSpace I)) y →L[ℝ] Bundle.Trivial N (Fin (k + 1) → ℝ) y :=
  ContinuousLinearMap.pi (Fin.cons (SmoothForm.degreeOneEquiv α (f y)) fun i ↦
    ((mextDerivₗ I 1 α).val (f y)).toContinuousMultilinearMap.toContinuousLinearMap ![Y i y, 0] 1)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I ∞ M]
  [IsManifold J ∞ N] [T2Space M] [TopologicalSpace N] [ContinuousMapClass K N M] in
private theorem leviOrthogonalMap_apply {k : ℕ} {f : K} (α : SmoothForm I M ℝ 1)
    (Y : Fin k → Π y, TangentSpace I (f y)) (y : N) (v : ((f : N → M) *ᵖ (TangentSpace I)) y) :
    leviOrthogonalMap f α Y y v =
      Fin.cons (α.val (f y) ![v]) fun i ↦ (mextDerivₗ I 1 α).val (f y) ![Y i y, v] := by
  funext j
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · exact SmoothForm.degreeOneEquiv_apply_apply_vec α (f y) v
  · exact (ContinuousMultilinearMap.toContinuousLinearMap_apply _ _ _ _).trans (congrArg _ <|
      funext <| Fin.forall_fin_two.2 ⟨update_of_ne (by decide) _ _, update_self _ _ _⟩)

omit [CompleteSpace E] [FiniteDimensional ℝ E'] [IsManifold I ∞ M] [IsManifold J ∞ N] [T2Space M] in
/-- The bundle map `TauCeti.leviOrthogonalMap` is smooth at every point where the sections `Y i`
are smooth as maps into `TM`: its components are a one-form and a two-form evaluated along smooth
maps into `TM`. -/
private theorem contMDiffAt_leviOrthogonalMap {k : ℕ} {f : K} (hf : ContMDiff J I ∞ f)
    (α : SmoothForm I M ℝ 1) {Y : Fin k → Π y, TangentSpace I (f y)} {y : N}
    (hY : ∀ i, ContMDiffAt J I.tangent ∞
      (fun y ↦ TotalSpace.mk' E (E := TangentSpace I) (f y) (Y i y)) y) :
    letI := Bundle.Pullback.contMDiffVectorBundle (n := ∞) (F := E) (E := TangentSpace I)
      (IB := I) (IB' := J) hf
    ContMDiffAt J (J.prod 𝓘(ℝ, E →L[ℝ] (Fin (k + 1) → ℝ))) ∞
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] (Fin (k + 1) → ℝ))
        (E := fun y ↦ ((f : N → M) *ᵖ (TangentSpace I)) y →L[ℝ]
          Bundle.Trivial N (Fin (k + 1) → ℝ) y) y (leviOrthogonalMap f α Y y)) y := by
  refine (contMDiffAt_hom_bundle_iff _ y).2 fun v ↦ ?_
  -- The induced map of total spaces, `(y, v) ↦ (y, α (v), (dα (Y i, v))ᵢ)`.
  have hb : ContMDiffAt (J.prod 𝓘(ℝ, E)) I ∞
      (fun p : TotalSpace E ((f : N → M) *ᵖ (TangentSpace I)) ↦ f p.proj) ⟨y, v⟩ :=
    hf.contMDiffAt.comp (⟨y, v⟩ : TotalSpace E ((f : N → M) *ᵖ (TangentSpace I)))
      (contMDiffAt_proj (F := E) ((f : N → M) *ᵖ (TangentSpace I)))
  have hsnd : ContMDiffAt (J.prod 𝓘(ℝ, E)) I.tangent ∞
      (fun p : TotalSpace E ((f : N → M) *ᵖ (TangentSpace I)) ↦
        TotalSpace.mk' E (E := TangentSpace I) (f p.proj) p.snd) ⟨y, v⟩ :=
    Bundle.Pullback.contMDiff_lift f hf _
  refine (Bundle.Trivial.contMDiffAt_mk_iff (I := J) (F := Fin (k + 1) → ℝ)
    (b := fun p : TotalSpace E ((f : N → M) *ᵖ (TangentSpace I)) ↦ p.proj)
    (f := fun p ↦ leviOrthogonalMap f α Y p.proj p.snd)).2
    ⟨contMDiffAt_proj (IB := J) (F := E) ((f : N → M) *ᵖ (TangentSpace I)), ?_⟩
  refine (contMDiffAt_pi_module_iff.2 fun j ↦ ?_).congr_of_eventuallyEq
    (Eventually.of_forall fun p ↦ leviOrthogonalMap_apply α Y p.proj p.snd)
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · simp only [Fin.cons_zero]
    have hα : ContMDiffAt (J.prod 𝓘(ℝ, E)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
        (fun p : TotalSpace E ((f : N → M) *ᵖ (TangentSpace I)) ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) (f p.proj)
          (SmoothForm.degreeOneEquiv α (f p.proj))) ⟨y, v⟩ :=
      ((SmoothForm.degreeOneEquiv α).contMDiff (f y)).comp
        (⟨y, v⟩ : TotalSpace E ((f : N → M) *ᵖ (TangentSpace I))) hb
    exact (hα.clm_bundle_apply_scalar hsnd).congr_of_eventuallyEq (Eventually.of_forall
      fun p ↦ (SmoothForm.degreeOneEquiv_apply_apply_vec α (f p.proj) p.snd).symm)
  · simp only [Fin.cons_succ]
    have hYp : ContMDiffAt (J.prod 𝓘(ℝ, E)) I.tangent ∞
        (fun p : TotalSpace E ((f : N → M) *ᵖ (TangentSpace I)) ↦
          TotalSpace.mk' E (E := TangentSpace I) (f p.proj) (Y i p.proj)) ⟨y, v⟩ :=
      (hY i).comp (⟨y, v⟩ : TotalSpace E ((f : N → M) *ᵖ (TangentSpace I)))
        (contMDiffAt_proj (F := E) ((f : N → M) *ᵖ (TangentSpace I)))
    exact (Bundle.Trivial.contMDiffAt_mk_iff.1
      ((mextDerivₗ I 1 α).contMDiffAt_eval₂ hYp hsnd)).2.congr_of_eventuallyEq
        (Eventually.of_forall fun p ↦
          (SmoothBundleForm.eval₂_apply (mextDerivₗ I 1 α) (f p.proj) (Y i p.proj) p.snd).symm)

/-- **Local frames of the Levi orthogonal.** Near every point of `N`, the Levi orthogonals of the
tangent images of a smooth isotropic immersion `f` are the kernels of the smooth fibrewise
surjective bundle map `TauCeti.leviOrthogonalMap` built from a local contact form `α` defining
`D` and the pushforward of a local frame of `TN`. Hence they have smooth local frames. -/
private theorem exists_isSubbundleFrameOn_leviOrthogonal (hD : IsContactDistribution I ∞ D)
    {f : K} (hf : ContMDiff J I ∞ f) (hfD : IsHorizontalMap J D f)
    (hinj : ∀ y, Injective (mfderiv J I f y)) (y₀ : N) :
    ∃ U : Set N, IsOpen U ∧ y₀ ∈ U ∧
      ∃ X : Fin (finrank ℝ E - finrank ℝ (Fin (finrank ℝ E' + 1) → ℝ)) →
          (Π y, ((f : N → M) *ᵖ (TangentSpace I)) y),
        IsSubbundleFrameOn (E := (f : N → M) *ᵖ (TangentSpace I)) E (leviOrthogonal J D f) X U ∧
          ∀ i, ContMDiffOn J (J.prod 𝓘(ℝ, E)) ∞
            (fun y ↦ TotalSpace.mk' E (E := (f : N → M) *ᵖ (TangentSpace I)) y (X i y)) U := by
  obtain ⟨W, hW, hy₀W, α, hα⟩ := hD.exists_smoothForm_ker_eq_isContactFormAt (f y₀)
  let eN := trivializationAt E' (TangentSpace J) y₀
  let b := Module.finBasis ℝ E'
  -- The pushforward of the local frame of `TN` given by the trivialization `eN`.
  let Y (i : Fin (finrank ℝ E')) (y : N) : TangentSpace I (f y) :=
    mfderiv J I f y (eN.localFrame b i y)
  have hY (i : Fin (finrank ℝ E')) : ContMDiffOn J I.tangent ∞
      (fun y ↦ TotalSpace.mk' E (E := TangentSpace I) (f y) (Y i y)) eN.baseSet := fun y hy ↦
    ((ContMDiff.contMDiff_tangentMap hf (m := ∞) le_rfl).contMDiffAt.comp y
      ((eN.contMDiffOn_localFrame_baseSet (I := J) (n := ∞) b i).contMDiffAt
        (eN.open_baseSet.mem_nhds hy))).contMDiffWithinAt
  let A := leviOrthogonalMap f α Y
  let S := eN.baseSet ∩ (f : N → M) ⁻¹' W
  have hS : IsOpen S := eN.open_baseSet.inter (hW.preimage (map_continuous f))
  -- On `S`, the kernel of `A` is the Levi orthogonal.
  have hker (y : N) (hy : y ∈ S) : (A y).ker = leviOrthogonal J D f y := by
    ext v
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, leviOrthogonalMap_apply]
    refine Iff.trans ?_ (mem_leviOrthogonal_iff_of_basis (v := v)
      (hD.isContMDiffDistribution.of_le (by simp)) hfD
      (eventually_of_mem (hW.mem_nhds hy.2) fun z hz ↦ (hα z hz).1) (eN.basisAt b hy.1)).symm
    simp only [funext_iff, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Pi.zero_apply, Y,
      eN.localFrame_apply_of_mem_baseSet b hy.1, mextDerivₗ_apply]
  -- On `S`, the bundle map is onto, by counting dimensions.
  have hsurj (y : N) (hy : y ∈ S) : Surjective (A y) := by
    have : FiniteDimensional ℝ (((f : N → M) *ᵖ (TangentSpace I)) y) :=
      inferInstanceAs (FiniteDimensional ℝ E)
    have hr := LinearMap.finrank_range_add_finrank_ker (A y).toLinearMap
    have h1 : finrank ℝ (LinearMap.ker (A y).toLinearMap) + (finrank ℝ E' + 1) = finrank ℝ E := by
      rw [show LinearMap.ker (A y).toLinearMap = leviOrthogonal J D f y from hker y hy]
      exact hfD.finrank_leviOrthogonal_add hD (by simp) (hf.contMDiffAt.of_le (by simp)) (hinj y)
    have hF : finrank ℝ (Bundle.Trivial N (Fin (finrank ℝ E' + 1) → ℝ) y) = finrank ℝ E' + 1 :=
      Module.finrank_fin_fun ℝ
    -- The fibres of `f^* TM` are the model space `E` by definition.
    have hE : finrank ℝ (((f : N → M) *ᵖ (TangentSpace I)) y) = finrank ℝ E := rfl
    refine LinearMap.range_eq_top.1 (Submodule.eq_top_of_finrank_eq ?_)
    omega
  have := Bundle.Pullback.contMDiffVectorBundle (n := ∞) (F := E) (E := TangentSpace I)
    (IB := I) (IB' := J) hf
  obtain ⟨U, hUS, hU, hy₀U, X, hX, hXs⟩ := exists_isSubbundleFrameOn_ker_of_surjective hS
    (fun y hy ↦ (contMDiffAt_leviOrthogonalMap hf α fun i ↦
      (hY i).contMDiffAt (eN.open_baseSet.mem_nhds hy.1)).contMDiffWithinAt) hsurj
    ⟨FiberBundle.mem_baseSet_trivializationAt' y₀, hy₀W⟩
  exact ⟨U, hU, hy₀U, X, ⟨hX.continuousOn, hX.linearIndependent,
    fun hy ↦ (hX.span_eq hy).trans (hker _ (hUS hy))⟩, hXs⟩

/-- **The Levi orthogonal has smooth local frames.** For a smooth isotropic immersion `f` into a
smooth contact manifold, the Levi orthogonals of the tangent images form a smooth subbundle of
`f^* TM` of rank `dim M - dim N - 1`. -/
theorem hasLocalContMDiffSubbundleFrames_leviOrthogonal (hD : IsContactDistribution I ∞ D)
    {f : K} (hf : ContMDiff J I ∞ f) (hfD : IsHorizontalMap J D f)
    (hinj : ∀ y, Injective (mfderiv J I f y)) :
    HasLocalContMDiffSubbundleFrames (E := (f : N → M) *ᵖ (TangentSpace I)) J ∞ E
      (Fin (finrank ℝ E - (finrank ℝ E' + 1))) (leviOrthogonal J D f) := by
  refine hasLocalContMDiffSubbundleFrames_iff.2 fun y₀ ↦ ?_
  obtain ⟨U, hU, hy₀, X, hX, hXs⟩ := exists_isSubbundleFrameOn_leviOrthogonal hD hf hfD hinj y₀
  have hr : finrank ℝ E - (finrank ℝ E' + 1) =
      finrank ℝ E - finrank ℝ (Fin (finrank ℝ E' + 1) → ℝ) := by
    rw [Module.finrank_fin_fun]
  refine ⟨U, hU, hy₀, fun i ↦ X (Fin.cast hr i), ⟨fun i ↦ hX.continuousOn _,
    fun hy ↦ (hX.linearIndependent hy).comp _ (Fin.cast_injective hr), fun hy ↦ ?_⟩,
    fun i ↦ hXs _⟩
  rw [← hX.span_eq hy, ← (finCongr hr).surjective.range_comp]
  simp only [Function.comp_def, finCongr_apply]

/-- **The Levi orthogonal inside the contact structure has smooth local frames.** For a smooth
isotropic immersion `f` into a smooth contact manifold `(M, D)`, the Levi orthogonals
`(T_y N)^⊥ ⊆ D_(f y)` of the tangent images form a smooth subbundle, of rank
`dim M - dim N - 1`, of the pullback `f^* D` of the contact structure, regarded as a vector bundle
(`TauCeti.IsContMDiffDistribution.fiberBundle`). Its quotients by the tangent images are the
conformal symplectic normal spaces. -/
theorem hasLocalContMDiffSubbundleFrames_orthogonalBilin (hD : IsContactDistribution I ∞ D)
    {f : K} (hf : ContMDiff J I ∞ f) (hfD : IsHorizontalMap J D f)
    (hinj : ∀ y, Injective (mfderiv J I f y)) :
    letI := hD.isContMDiffDistribution.fiberBundle
    HasLocalContMDiffSubbundleFrames (E := (f : N → M) *ᵖ fun x ↦ D x) J ∞
      (Fin (finrank ℝ E - 1) → ℝ) (Fin (finrank ℝ E - (finrank ℝ E' + 1))) fun y ↦
        ((LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype).orthogonalBilin
          (distributionLeviForm D (f y)) := by
  let := hD.isContMDiffDistribution.fiberBundle
  classical
  refine hasLocalContMDiffSubbundleFrames_iff.2 fun y₀ ↦ ?_
  obtain ⟨U, hU, hy₀, X, hX, hXs⟩ :=
    hasLocalContMDiffSubbundleFrames_iff.1 (hasLocalContMDiffSubbundleFrames_leviOrthogonal hD hf
      hfD hinj) y₀
  have hXD {y : N} (hy : y ∈ U) (i) : X i y ∈ D (f y) :=
    leviOrthogonal_le ((hX.span_eq hy).le (Submodule.subset_span ⟨i, rfl⟩))
  -- The frame, read in `D`; it is set to zero off `U`.
  let X' (i) (y : N) : D (f y) := if h : X i y ∈ D (f y) then ⟨X i y, h⟩ else 0
  have hX' {y : N} (hy : y ∈ U) (i) : (X' i y : TangentSpace I (f y)) = X i y := by
    simp only [X', hXD hy i, ↓reduceDIte]
    -- Both sides are `X i y`, read in the fibres `(f^* TM) y` and `T_(f y) M`, which agree by
    -- definition of the pullback.
    rfl
  have hsmooth (i) : ContMDiffOn J (J.prod 𝓘(ℝ, Fin (finrank ℝ E - 1) → ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (Fin (finrank ℝ E - 1) → ℝ)
        (E := (f : N → M) *ᵖ fun x ↦ D x) y (X' i y)) U := fun y hy ↦
    (hD.isContMDiffDistribution.contMDiffAt_pullback_mk hf.contMDiffAt
      ((hXs i).contMDiffAt (hU.mem_nhds hy))
      (eventually_of_mem (hU.mem_nhds hy) fun _ hz ↦ hX' hz i)).contMDiffWithinAt
  refine ⟨U, hU, hy₀, X', ⟨fun i ↦ (hsmooth i).continuousOn, fun {y} hy ↦ ?_, fun {y} hy ↦ ?_⟩,
    hsmooth⟩
  · refine LinearIndependent.of_comp (D (f y)).subtype ?_
    -- The fibres of `f^* D` are the subspaces `D (f y)`; restated there so that `simp` applies.
    change LinearIndependent ℝ fun i ↦ ((X' i y : D (f y)) : TangentSpace I (f y))
    simp only [hX' hy]
    exact hX.linearIndependent hy
  · refine Submodule.map_injective_of_injective (D (f y)).injective_subtype ?_
    -- The fibres of `f^* D` are the subspaces `D (f y)`; restated there so that `rw` applies.
    change Submodule.map (D (f y)).subtype
      (Submodule.span ℝ (Set.range fun i ↦ (X' i y : D (f y)))) =
        Submodule.map (D (f y)).subtype
          (((LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype).orthogonalBilin
            (distributionLeviForm D (f y)))
    rw [map_subtype_orthogonalBilin_eq_leviOrthogonal, Submodule.map_span, ← Set.range_comp]
    -- The composite with the inclusion of `D` is the coercion to `TM`.
    change Submodule.span ℝ (Set.range fun i ↦ (X' i y : TangentSpace I (f y))) =
      leviOrthogonal J D f y
    simp only [hX' hy]
    exact hX.span_eq hy

end Frames

/-! ### The conformal symplectic normal bundle -/

section Bundle

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I ∞ M] [IsManifold J ∞ N]
  [T2Space M] {K : Type*} [FunLike K N M] [ContinuousMapClass K N M]

variable (J D) in
/-- The Levi orthogonals of the tangent images of `f` in `D`, as subspaces of the fibres of the
pullback `f^* D`. -/
abbrev leviOrthogonalPullback (f : N → M) (y : N) :
    Submodule ℝ ((f *ᵖ fun x ↦ D x) y) :=
  ((LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype).orthogonalBilin
    (distributionLeviForm D (f y))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I ∞ M] [IsManifold J ∞ N]
  [T2Space M] in
/-- A basis `t` of the tangent image of a horizontal map `f` at `y`, read in the Levi orthogonal
of the tangent image inside `D`, is a basis of the tangent image there. -/
private theorem linearIndependent_and_span_eq_comap_range (hfD : IsHorizontalMap J D f) {y : N}
    (hiso : (LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype ≤
      leviOrthogonalPullback J D f y)
    {ι : Type*} {t : ι → TangentSpace I (f y)} (ht : LinearIndependent ℝ t)
    (hspan : Submodule.span ℝ (Set.range t) = LinearMap.range (mfderiv J I f y).toLinearMap)
    {z : ι → leviOrthogonalPullback J D f y}
    (hz : ∀ i, (D (f y)).subtype (z i).val = t i) :
    LinearIndependent ℝ z ∧ Submodule.span ℝ (Set.range z) =
      ((LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype).comap
        (leviOrthogonalPullback J D f y).subtype := by
  -- Both sides are compared through the injective inclusion into `T_(f y) M`.
  let L : leviOrthogonalPullback J D f y →ₗ[ℝ] TangentSpace I (f y) :=
    (D (f y)).subtype ∘ₗ (leviOrthogonalPullback J D f y).subtype
  have hL : Injective L := (D (f y)).injective_subtype.comp Subtype.val_injective
  have hLz : L ∘ z = t := funext hz
  refine ⟨LinearIndependent.of_comp L (hLz ▸ ht), Submodule.map_injective_of_injective hL ?_⟩
  rw [Submodule.map_span, ← Set.range_comp, hLz, hspan]
  ext v
  simp only [Submodule.mem_map]
  constructor
  · intro hv
    exact ⟨⟨⟨v, hfD.range_mfderiv_le y hv⟩, hiso hv⟩, hv, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact hu

open Classical in
/-- The tangent images of a smooth isotropic immersion have smooth local frames inside the bundle
of their Levi orthogonals (`TauCeti.hasLocalContMDiffSubbundleFrames_orthogonalBilin`). The
conformal symplectic normal bundle is the quotient bundle of this subbundle
(`TauCeti.conformalSymplecticNormalPrebundle_eq`). -/
theorem hasLocalContMDiffSubbundleFrames_comap_range (hD : IsContactDistribution I ∞ D)
    {f : K} (hf : ContMDiff J I ∞ f) (hfD : IsHorizontalMap J D f)
    (hinj : ∀ y, Injective (mfderiv J I f y)) :
    letI := hD.isContMDiffDistribution.fiberBundle
    letI := hD.isContMDiffDistribution.vectorBundle
    letI := subbundleTopology (Fin (finrank ℝ E - 1) → ℝ) (E := (f : N → M) *ᵖ fun x ↦ D x)
      (F' := Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ) (leviOrthogonalPullback J D f)
    letI := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj).fiberBundle
    HasLocalContMDiffSubbundleFrames J ∞ (Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ)
      (Fin (finrank ℝ E')) (E := fun y ↦ leviOrthogonalPullback J D f y)
      fun y ↦ ((LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype).comap
        (leviOrthogonalPullback J D f y).subtype := by
  let := hD.isContMDiffDistribution.fiberBundle
  let := hD.isContMDiffDistribution.vectorBundle
  have := hD.isContMDiffDistribution.contMDiffVectorBundle
  have := Bundle.Pullback.contMDiffVectorBundle (n := ∞) (F := Fin (finrank ℝ E - 1) → ℝ)
    (E := fun x ↦ D x) (IB := I) (IB' := J) hf
  have hW := hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj
  let := subbundleTopology (Fin (finrank ℝ E - 1) → ℝ) (E := (f : N → M) *ᵖ fun x ↦ D x)
    (F' := Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ) (leviOrthogonalPullback J D f)
  let := hW.fiberBundle
  have hiso (y : N) : (LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype ≤
      leviOrthogonalPullback J D f y :=
    hfD.le_orthogonalBilin hD (by simp) (hf.contMDiffAt.of_le (by simp))
  refine hasLocalContMDiffSubbundleFrames_iff.2 fun y₀ ↦ ?_
  obtain ⟨U, hU, hy₀, T, hT, hTs⟩ := hasLocalContMDiffSubbundleFrames_iff.1
    (ContMDiff.hasLocalContMDiffSubbundleFrames_range_mfderiv (m := ∞) hf le_rfl hinj) y₀
  have hTr {y : N} (hy : y ∈ U) (i) :
      T i y ∈ LinearMap.range (mfderiv J I f y).toLinearMap :=
    (hT.span_eq hy).le (Submodule.subset_span ⟨i, rfl⟩)
  -- The frame of the tangent images, read in the Levi orthogonals; it is set to zero off `U`.
  let Z (i) (y : N) : leviOrthogonalPullback J D f y :=
    if h : T i y ∈ LinearMap.range (mfderiv J I f y).toLinearMap then
      ⟨⟨T i y, hfD.range_mfderiv_le y h⟩, hiso y h⟩ else 0
  -- The values of `Z` in `D`.
  let zD (i) (y : N) : D (f y) := (Z i y).val
  have hZ {y : N} (hy : y ∈ U) (i) : (zD i y : TangentSpace I (f y)) = T i y := by
    simp only [zD, Z, hTr hy i, ↓reduceDIte]
    -- Both sides are `T i y`, read in the fibres `(f^* TM) y` and `T_(f y) M`, which agree by
    -- definition of the pullback.
    rfl
  have hsmooth (i) : ContMDiffOn J (J.prod 𝓘(ℝ, Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ)
        (E := fun y ↦ leviOrthogonalPullback J D f y) y (Z i y)) U := by
    refine hW.contMDiffOn_totalSpace_mk (b := id) (w := fun y ↦ zD i y) le_rfl
      (fun y hy ↦ ?_) fun y ↦ (Z i y).property
    exact (hD.isContMDiffDistribution.contMDiffAt_pullback_mk hf.contMDiffAt
      ((hTs i).contMDiffAt (hU.mem_nhds hy))
      (eventually_of_mem (hU.mem_nhds hy) fun _ hz ↦ hZ hz i)).contMDiffWithinAt
  have hbasis {y : N} (hy : y ∈ U) := linearIndependent_and_span_eq_comap_range hfD (hiso y)
    (hT.linearIndependent hy) (hT.span_eq hy) (z := (Z · y)) (hZ hy)
  exact ⟨U, hU, hy₀, Z, ⟨fun i ↦ (hsmooth i).continuousOn, fun hy ↦ (hbasis hy).1,
    fun hy ↦ (hbasis hy).2⟩, hsmooth⟩

omit [FiniteDimensional ℝ E'] [T2Space M] [ContinuousMapClass K N M] in
/-- The ranks of the subbundles in the construction of the conformal symplectic normal bundle: the
tangent image of rank `dim N` inside the Levi orthogonal of rank `dim M - dim N - 1`, with
quotient of rank `dim M - 2 dim N - 1`. -/
theorem IsHorizontalMap.card_add_card_eq_finrank [Nonempty N] (hD : IsContactDistribution I ∞ D)
    {f : K} (hf : ContMDiff J I ∞ f) (hfD : IsHorizontalMap J D f)
    (hinj : ∀ y, Injective (mfderiv J I f y)) :
    Fintype.card (Fin (finrank ℝ E')) + Fintype.card (Fin (finrank ℝ E - 2 * finrank ℝ E' - 1)) =
      finrank ℝ (Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ) := by
  let y : N := Classical.arbitrary N
  have h := hfD.finrank_conformalSymplecticNormal_add hD (by simp)
    (hf.contMDiffAt.of_le (by simp)) (hinj y)
  rw [Fintype.card_fin, Fintype.card_fin, Module.finrank_fin_fun]
  omega

/-- **The bundle of Levi orthogonals is a smooth vector bundle.** For a smooth isotropic immersion
`f` into a smooth contact manifold `(M, D)`, the Levi orthogonals of the tangent images, a smooth
subbundle of `f^* D` (`TauCeti.hasLocalContMDiffSubbundleFrames_orthogonalBilin`), form a smooth
vector bundle. The conformal symplectic normal bundle is its quotient by the tangent images. -/
theorem contMDiffVectorBundle_leviOrthogonalPullback (hD : IsContactDistribution I ∞ D)
    {f : K} (hf : ContMDiff J I ∞ f) (hfD : IsHorizontalMap J D f)
    (hinj : ∀ y, Injective (mfderiv J I f y)) :
    letI := hD.isContMDiffDistribution.fiberBundle
    letI := hD.isContMDiffDistribution.vectorBundle
    letI := subbundleTopology (Fin (finrank ℝ E - 1) → ℝ) (E := (f : N → M) *ᵖ fun x ↦ D x)
      (F' := Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ) (leviOrthogonalPullback J D f)
    letI := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj).fiberBundle
    letI := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj).vectorBundle
    ContMDiffVectorBundle ∞ (Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ)
      (fun y ↦ leviOrthogonalPullback J D f y) J := by
  let := hD.isContMDiffDistribution.fiberBundle
  let := hD.isContMDiffDistribution.vectorBundle
  have := hD.isContMDiffDistribution.contMDiffVectorBundle
  have := Bundle.Pullback.contMDiffVectorBundle (n := ∞) (F := Fin (finrank ℝ E - 1) → ℝ)
    (E := fun x ↦ D x) (IB := I) (IB' := J) hf
  exact (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj).contMDiffVectorBundle

/-- **The conformal symplectic normal bundle.** Let `f : N → M` be a smooth isotropic immersion of
a nonempty manifold into a smooth contact manifold `(M, D)`. Its conformal symplectic normal spaces
`(T_y N)^⊥ ⧸ T_y N` (`TauCeti.ConformalSymplecticNormal`) form a vector prebundle over `N`, of rank
`dim M - 2 dim N - 1`: the quotient of the bundle of Levi orthogonals of the tangent images, a
smooth subbundle of `f^* D` (`TauCeti.hasLocalContMDiffSubbundleFrames_orthogonalBilin`), by the
tangent images. Its pretrivializations are those of smooth local frames of the quotient, and it is
a smooth vector bundle
(`TauCeti.contMDiffVectorBundle_conformalSymplecticNormalPrebundle`). -/
def conformalSymplecticNormalPrebundle [Nonempty N] (hD : IsContactDistribution I ∞ D)
    {f : K} (hf : ContMDiff J I ∞ f) (hfD : IsHorizontalMap J D f)
    (hinj : ∀ y, Injective (mfderiv J I f y)) :
    VectorPrebundle ℝ (Fin (finrank ℝ E - 2 * finrank ℝ E' - 1) → ℝ)
      (fun y ↦ ConformalSymplecticNormal J D f y) :=
  letI := hD.isContMDiffDistribution.fiberBundle
  letI := hD.isContMDiffDistribution.vectorBundle
  letI := subbundleTopology (Fin (finrank ℝ E - 1) → ℝ) (E := (f : N → M) *ᵖ fun x ↦ D x)
    (F' := Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ) (leviOrthogonalPullback J D f)
  letI := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj).fiberBundle
  letI := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj).vectorBundle
  have := contMDiffVectorBundle_leviOrthogonalPullback hD hf hfD hinj
  (hasLocalContMDiffSubbundleFrames_comap_range hD hf hfD hinj).quotientPrebundle
    (hfD.card_add_card_eq_finrank hD hf hinj)

open Classical in
/-- **The conformal symplectic normal bundle is a quotient bundle.** The prebundle
`TauCeti.conformalSymplecticNormalPrebundle` is the quotient prebundle of the bundle of Levi
orthogonals by the smooth subbundle of tangent images
(`TauCeti.hasLocalContMDiffSubbundleFrames_comap_range`). So the smoothness criteria for the
quotient map and for local lifts of sections
(`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiff_totalSpace_mkQ`,
`TauCeti.HasLocalContMDiffSubbundleFrames.exists_contMDiffOn_mk_eq`) apply to it. -/
theorem conformalSymplecticNormalPrebundle_eq [Nonempty N] (hD : IsContactDistribution I ∞ D)
    {f : K} (hf : ContMDiff J I ∞ f) (hfD : IsHorizontalMap J D f)
    (hinj : ∀ y, Injective (mfderiv J I f y)) :
    letI := hD.isContMDiffDistribution.fiberBundle
    letI := hD.isContMDiffDistribution.vectorBundle
    letI := subbundleTopology (Fin (finrank ℝ E - 1) → ℝ) (E := (f : N → M) *ᵖ fun x ↦ D x)
      (F' := Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ) (leviOrthogonalPullback J D f)
    letI := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj).fiberBundle
    letI := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj).vectorBundle
    haveI := contMDiffVectorBundle_leviOrthogonalPullback hD hf hfD hinj
    conformalSymplecticNormalPrebundle hD hf hfD hinj =
      (hasLocalContMDiffSubbundleFrames_comap_range hD hf hfD hinj).quotientPrebundle
        (hfD.card_add_card_eq_finrank hD hf hinj) := by
  unfold conformalSymplecticNormalPrebundle
  rfl

/-- **The conformal symplectic normal bundle is a smooth vector bundle.** For a smooth isotropic
immersion `f : N → M` of a nonempty manifold into a smooth contact manifold `(M, D)`, the
conformal symplectic normal spaces `(T_y N)^⊥ ⧸ T_y N`, with the topology and atlas of
`TauCeti.conformalSymplecticNormalPrebundle`, form a smooth vector bundle of rank
`dim M - 2 dim N - 1` over `N`. -/
theorem contMDiffVectorBundle_conformalSymplecticNormalPrebundle [Nonempty N]
    (hD : IsContactDistribution I ∞ D) {f : K} (hf : ContMDiff J I ∞ f)
    (hfD : IsHorizontalMap J D f) (hinj : ∀ y, Injective (mfderiv J I f y)) :
    letI := (conformalSymplecticNormalPrebundle hD hf hfD hinj).totalSpaceTopology
    letI := (conformalSymplecticNormalPrebundle hD hf hfD hinj).toFiberBundle
    letI := (conformalSymplecticNormalPrebundle hD hf hfD hinj).toVectorBundle
    ContMDiffVectorBundle ∞ (Fin (finrank ℝ E - 2 * finrank ℝ E' - 1) → ℝ)
      (fun y ↦ ConformalSymplecticNormal J D f y) J := by
  let := hD.isContMDiffDistribution.fiberBundle
  let := hD.isContMDiffDistribution.vectorBundle
  let := subbundleTopology (Fin (finrank ℝ E - 1) → ℝ) (E := (f : N → M) *ᵖ fun x ↦ D x)
    (F' := Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ) (leviOrthogonalPullback J D f)
  let := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj).fiberBundle
  let := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj).vectorBundle
  have := contMDiffVectorBundle_leviOrthogonalPullback hD hf hfD hinj
  rw [conformalSymplecticNormalPrebundle_eq hD hf hfD hinj]
  exact (hasLocalContMDiffSubbundleFrames_comap_range hD hf hfD hinj
    ).contMDiffVectorBundle_quotientPrebundle (hfD.card_add_card_eq_finrank hD hf hinj)

end Bundle

end TauCeti
