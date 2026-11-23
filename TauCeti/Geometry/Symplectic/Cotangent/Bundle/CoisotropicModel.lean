/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Annihilator
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville
public import TauCeti.Geometry.Symplectic.Lagrangian.CoisotropicModel
public import TauCeti.Geometry.Symplectic.Manifold.Flat
public import TauCeti.Geometry.Symplectic.Manifold.Opens
import TauCeti.Topology.VectorBundle.Hom

/-!
# The coisotropic embedding model of a presymplectic form

Let `σ` be a two-form on a finite-dimensional manifold `Q` and let `D` be a distribution on `Q`
complementary to the kernel of `σ` at every point, `T_q Q = D_q ⊕ ker σ_q`. The annihilators
`D⁰_q ⊆ T*_q Q` of a smooth distribution of rank `k` form a smooth vector subbundle of rank
`r = dim Q - k` of the cotangent bundle (`TauCeti.IsContMDiffDistribution.annihilatorFiberBundle`),
and restriction to `ker σ_q` identifies each fibre `D⁰_q` with the dual `(ker σ_q)*`. So `D⁰` is a
realization of the dual of the kernel bundle of `σ` inside `T*Q`. On its total space, Gotay's
**coisotropic model form** is

`Ω = π^* σ + ι^* ω`

(`TauCeti.CotangentBundle.coisotropicModelForm`), where `π : D⁰ → Q` is the projection,
`ι : D⁰ → T*Q` the inclusion and `ω = -dλ` the canonical symplectic form of `T*Q`. This file
proves that, when `D` is complementary to `ker σ`, `Ω` is nondegenerate near the zero section, and
symplectic there when `σ` is closed, that the zero section pulls `Ω` back to `σ`, and that the
tangent spaces of the zero section are coisotropic for it: this is the model of Gotay's
coisotropic embedding theorem.

* Along the zero section, in the splitting `T_(0_q) D⁰ ≅ T_q Q × D⁰_q` of
  `TauCeti.Bundle.zeroSectionTangentEquiv`, the inclusion `ι` has differential `(v, a) ↦ (v, a)`
  in the preferred chart of `T*Q` at the zero covector
  (`TauCeti.CotangentBundle.mfderiv_annihilatorInclusion_zeroSection`), so
  `Ω((v, a), (v', a')) = σ(v, v') + a'(v) - a(v')`
  (`TauCeti.CotangentBundle.eval₂_coisotropicModelForm_zeroSection`).
* A covector `a ∈ D⁰_q` satisfies `a(v) = a(P v)` for the projection `P` onto `ker σ_q` along
  `D_q`. Restricting `a` to `ker σ_q` therefore carries `Ω` at the zero covector over `q` to the
  linear coisotropic model `LinearMap.BilinForm.IsAlt.coisotropicModel` of `σ_q` on
  `T_q Q × (ker σ_q)*` (`TauCeti.CotangentBundle.exists_linearEquiv_coisotropicModel`). Hence
  `Ω` is nondegenerate along the zero section
  (`TauCeti.CotangentBundle.nondegenerate_bilinFormAt_coisotropicModelForm_zeroSection`), and the
  zero section is coisotropic: the `Ω`-orthogonal of its tangent space is the image of
  `ker σ_q`
  (`TauCeti.CotangentBundle.forall_eval₂_coisotropicModelForm_mfderiv_zeroSection_eq_zero_iff`).
* The zero section pulls `Ω` back to `σ`
  (`TauCeti.CotangentBundle.mpullback_zeroSection_coisotropicModelForm`), and `Ω` is closed
  exactly when `σ` is (`TauCeti.CotangentBundle.isClosed_coisotropicModelForm_iff`).
* Nondegeneracy is an open condition, so `Ω` is nondegenerate on an open neighbourhood of the
  zero section
  (`TauCeti.CotangentBundle.exists_opens_isNondegenerate_mpullback_coisotropicModelForm`).
  For a closed `σ` and the canonical bundle structure on the annihilators of a smooth
  distribution, `Ω` is a symplectic form there
  (`TauCeti.CotangentBundle.exists_opens_isSymplectic_mpullback_coisotropicModelForm`).

Apart from the last statement, the results hold for any smooth vector bundle structure on the
annihilators, with model fibre `F`, for which the inclusion into `T*Q` is smooth. This keeps the
local bundle instances of `TauCeti.IsContMDiffDistribution.annihilatorFiberBundle` out of the
statements; the last statement instantiates them.

## References

* M. J. Gotay, *On coisotropic imbeddings of presymplectic manifolds*, Proceedings of the
  American Mathematical Society 84 (1982), 111–114.
* V. Guillemin and S. Sternberg, *Symplectic Techniques in Physics*, Cambridge University Press,
  1984, Section 39 (the coisotropic embedding theorem).
-/

public section

noncomputable section

open Bundle Manifold Module Set
open scoped Manifold ContDiff

namespace TauCeti.CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  {D : Π x : Q, Submodule ℝ (TangentSpace I x)} (σ : SmoothTwoForm I Q)

section Model

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiberBundle F fun x ↦ annihilatorSpace I D x] [VectorBundle ℝ F fun x ↦ annihilatorSpace I D x]
  [ContMDiffVectorBundle ∞ F (fun x ↦ annihilatorSpace I D x) I]

local notation "N" => TotalSpace F fun x ↦ annihilatorSpace I D x

local notation "ι" => annihilatorInclusion I D F

/-- **Gotay's coisotropic model form** `Ω = π^* σ + ι^* ω` on the total space of the annihilator
bundle `D⁰ ⊆ T*Q` of a distribution `D`, where `π : D⁰ → Q` is the projection, `ι : D⁰ → T*Q` the
inclusion, assumed smooth, and `ω` the canonical symplectic form of `T*Q`. When `D` is
complementary to the kernel of `σ`, the fibres of `D⁰` are the duals of the kernels of `σ`, and `Ω`
is nondegenerate near the zero section. It is closed when `σ` is, and the zero section pulls it
back to `σ`. -/
def coisotropicModelForm
    (hι : ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ (annihilatorInclusion I D F)) :
    SmoothTwoForm (I.prod 𝓘(ℝ, F)) N :=
  SmoothForm.mpullback (π F fun x ↦ annihilatorSpace I D x) (Bundle.contMDiff_proj _) σ +
    SmoothForm.mpullback ι hι (symplecticForm I Q)

variable (hι : ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ (annihilatorInclusion I D F))

/-- The coisotropic model form evaluates as `σ` on the projections to `Q` plus the canonical form
of `T*Q` on the images in `T*Q`. -/
theorem eval₂_coisotropicModelForm (z : N) (u u' : TangentSpace (I.prod 𝓘(ℝ, F)) z) :
    SmoothBundleForm.eval₂ (coisotropicModelForm σ hι) z u u' =
      SmoothBundleForm.eval₂ σ z.proj (mfderiv (I.prod 𝓘(ℝ, F)) I (π F _) z u)
          (mfderiv (I.prod 𝓘(ℝ, F)) I (π F _) z u') +
        SmoothBundleForm.eval₂ (symplecticForm I Q) (ι z)
          (mfderiv (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ι z u)
          (mfderiv (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ι z u') := by
  rw [coisotropicModelForm, SmoothBundleForm.eval₂_add, SmoothForm.eval₂_mpullback,
    SmoothForm.eval₂_mpullback]

/-- **The coisotropic model form along the zero section.** In the splitting
`T_(0_q) D⁰ ≅ T_q Q × D⁰_q`, the model form pairs `(v, a)` with `(v', a')` to
`σ(v, v') + a'(v) - a(v')`. -/
theorem eval₂_coisotropicModelForm_zeroSection (q : Q)
    (u u' : TangentSpace (I.prod 𝓘(ℝ, F)) (zeroSection F (fun x ↦ annihilatorSpace I D x) q)) :
    SmoothBundleForm.eval₂ (coisotropicModelForm σ hι)
        (zeroSection F (fun x ↦ annihilatorSpace I D x) q) u u' =
      SmoothBundleForm.eval₂ σ q (TauCeti.Bundle.zeroSectionTangentEquiv (I := I) q u).1
          (TauCeti.Bundle.zeroSectionTangentEquiv (I := I) q u').1 +
        ((TauCeti.Bundle.zeroSectionTangentEquiv (I := I) q u').2 : TangentSpace I q →L[ℝ] ℝ)
          (TauCeti.Bundle.zeroSectionTangentEquiv (I := I) q u).1 -
        ((TauCeti.Bundle.zeroSectionTangentEquiv (I := I) q u).2 : TangentSpace I q →L[ℝ] ℝ)
          (TauCeti.Bundle.zeroSectionTangentEquiv (I := I) q u').1 := by
  have hπ (w : TangentSpace (I.prod 𝓘(ℝ, F)) (zeroSection F (fun x ↦ annihilatorSpace I D x) q)) :
      mfderiv (I.prod 𝓘(ℝ, F)) I (π F fun x ↦ annihilatorSpace I D x)
        (zeroSection F (fun x ↦ annihilatorSpace I D x) q) w =
      (TauCeti.Bundle.zeroSectionTangentEquiv (I := I) q w).1 := by
    rw [Bundle.mfderiv_proj, TauCeti.Bundle.zeroSectionTangentEquiv_apply]
    -- `TangentSpace` is only definitionally the model `E × F`, so `ContinuousLinearMap.coe_fst'`
    -- does not rewrite here; the first projection is closed by unfolding instead.
    rfl
  rw [eval₂_coisotropicModelForm, eval₂_symplecticForm, hπ, hπ, add_sub_assoc]
  refine congrArg _ ((strongDualCotangentSymplecticForm_apply (V := E) _ _).trans ?_)
  have hι0 := hι.mdifferentiableAt (x := zeroSection F (fun x ↦ annihilatorSpace I D x) q)
    (by simp)
  rw [mfderiv_annihilatorInclusion_zeroSection q hι0,
    mfderiv_annihilatorInclusion_zeroSection q hι0]
  -- Both sides are the same pairings once the pair projections reduce; the cotangent tangent
  -- space is only definitionally `E × (E →L[ℝ] ℝ)`, so this needs unfolding rather than `simp`.
  rfl

/-- **The zero section pulls the coisotropic model form back to `σ`.** -/
@[simp]
theorem mpullback_zeroSection_coisotropicModelForm :
    SmoothForm.mpullback (zeroSection F fun x ↦ annihilatorSpace I D x)
      (contMDiff_zeroSection ℝ _) (coisotropicModelForm σ hι) = σ := by
  refine SmoothBundleForm.ext_eval₂ fun q v w ↦ ?_
  rw [SmoothForm.eval₂_mpullback, eval₂_coisotropicModelForm_zeroSection,
    TauCeti.Bundle.zeroSectionTangentEquiv_mfderiv_zeroSection,
    TauCeti.Bundle.zeroSectionTangentEquiv_mfderiv_zeroSection]
  simp

/-- **The coisotropic model form is closed exactly when `σ` is.** -/
theorem isClosed_coisotropicModelForm_iff : (coisotropicModelForm σ hι).IsClosed ↔ σ.IsClosed := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← mpullback_zeroSection_coisotropicModelForm σ hι]
    exact h.mpullback _ _
  · exact (h.mpullback _ _).add (isSymplectic_symplecticForm.isClosed.mpullback _ _)

variable [FiniteDimensional ℝ E]

/-- **The coisotropic model form at the zero section is the linear coisotropic model.** If `D q`
is complementary to the kernel `K` of `σ_q`, the tangent space of the annihilator bundle at the
zero covector over `q` is linearly isomorphic to `T_q Q × K*`, carrying the model form to the
linear coisotropic model `LinearMap.BilinForm.IsAlt.coisotropicModel` of `σ_q` for the projection
onto `K` along `D q`, and the differential of the zero section to the inclusion `v ↦ (v, 0)`. -/
theorem exists_linearEquiv_coisotropicModel (q : Q)
    (hq : IsCompl (D q) (LinearMap.ker (σ.bilinFormAt q))) :
    ∃ e : TangentSpace (I.prod 𝓘(ℝ, F)) (zeroSection F (fun x ↦ annihilatorSpace I D x) q) ≃ₗ[ℝ]
        TangentSpace I q × Module.Dual ℝ (LinearMap.ker (σ.bilinFormAt q)),
      (∀ u u', SmoothBundleForm.eval₂ (coisotropicModelForm σ hι)
          (zeroSection F (fun x ↦ annihilatorSpace I D x) q) u u' =
        (SmoothForm.isAlt_bilinFormAt σ q).coisotropicModel
          ((LinearMap.ker (σ.bilinFormAt q)).projectionOnto (D q) hq.symm)
          (Submodule.projectionOnto_apply_left hq.symm) (e u) (e u')) ∧
      ∀ v, e (mfderiv I (I.prod 𝓘(ℝ, F)) (zeroSection F fun x ↦ annihilatorSpace I D x) q v) =
        (v, 0) := by
  set K := LinearMap.ker (σ.bilinFormAt q)
  set P := K.projectionOnto (D q) hq.symm
  -- A covector annihilating `D q` is determined by its restriction to `K`: it equals its
  -- composition with the projection onto `K` along `D q`.
  have hP (a : annihilatorSpace I D q) (v : TangentSpace I q) :
      (a : TangentSpace I q →L[ℝ] ℝ) (P v) = (a : TangentSpace I q →L[ℝ] ℝ) v := by
    have h0 : (a : TangentSpace I q →L[ℝ] ℝ) ((D q).projection K hq v) = 0 :=
      mem_annihilatorSpace_iff.mp a.property _ (Submodule.projection_apply_mem hq v)
    conv_rhs => rw [← Submodule.projection_add_projection_eq_self hq v]
    rw [map_add, h0, zero_add, Submodule.projection_apply]
  -- Restriction to `K` identifies the annihilator of `D q` with `K*`.
  let ρ : annihilatorSpace I D q →ₗ[ℝ] Module.Dual ℝ K :=
    K.subtype.dualMap ∘ₗ ContinuousLinearMap.coeLM ℝ ∘ₗ (annihilatorSpace I D q).subtype
  have hρ (a : annihilatorSpace I D q) (k : K) :
      ρ a k = (a : TangentSpace I q →L[ℝ] ℝ) k := rfl
  have hρbij : Function.Bijective ρ := by
    refine ⟨(injective_iff_map_eq_zero ρ).mpr fun a ha ↦ Subtype.ext <| ContinuousLinearMap.ext
      fun v ↦ ?_, fun f ↦ ⟨⟨LinearMap.toContinuousLinearMap (f ∘ₗ P),
        mem_annihilatorSpace_iff.mpr fun v hv ↦ ?_⟩, LinearMap.ext fun k ↦ ?_⟩⟩
    · rw [← hP, ← hρ, ha, LinearMap.zero_apply, ZeroMemClass.coe_zero, zero_apply]
    · simp [P, (Submodule.projectionOnto_apply_eq_zero_iff hq.symm).mpr hv]
    · simp [hρ, P]
  let e := (Bundle.zeroSectionTangentEquiv (I := I) (F := F) (V := fun x ↦ annihilatorSpace I D x)
    q).toLinearEquiv.trans ((LinearEquiv.refl ℝ (TangentSpace I q)).prodCongr
      (LinearEquiv.ofBijective ρ hρbij))
  refine ⟨e, fun u u' ↦ ?_, fun v ↦ ?_⟩
  · rw [eval₂_coisotropicModelForm_zeroSection, LinearMap.BilinForm.IsAlt.coisotropicModel_apply]
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
      LinearEquiv.ofBijective_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
      SmoothForm.bilinFormAt_apply]
    rw [hρ, hρ, hP, hP]
  · simp [e]

/-- **The coisotropic model form is nondegenerate along the zero section** wherever `D q` is
complementary to the kernel of `σ_q`. -/
theorem nondegenerate_bilinFormAt_coisotropicModelForm_zeroSection (q : Q)
    (hq : IsCompl (D q) (LinearMap.ker (σ.bilinFormAt q))) :
    ((coisotropicModelForm σ hι).bilinFormAt
      (zeroSection F (fun x ↦ annihilatorSpace I D x) q)).Nondegenerate := by
  obtain ⟨e, he, -⟩ := exists_linearEquiv_coisotropicModel σ hι q hq
  refine ((SmoothForm.isAlt_bilinFormAt _ _).isRefl.nondegenerate_iff_separatingLeft).mpr
    fun u hu ↦ e.injective ?_
  rw [map_zero]
  refine ((SmoothForm.isAlt_bilinFormAt σ q).coisotropicModel _
    (Submodule.projectionOnto_apply_left hq.symm)).nondegenerate.1 _ fun y ↦ ?_
  have h := hu (e.symm y)
  rwa [SmoothForm.bilinFormAt_apply, he, e.apply_symm_apply] at h

/-- **The zero section is coisotropic for the model form.** If `D q` is complementary to the kernel
of `σ_q`, a tangent vector at the zero covector over `q` is orthogonal for the model form to the
tangent space of the zero section exactly when it is tangent to the zero section in a direction of
the kernel of `σ_q`. -/
theorem forall_eval₂_coisotropicModelForm_mfderiv_zeroSection_eq_zero_iff (q : Q)
    (hq : IsCompl (D q) (LinearMap.ker (σ.bilinFormAt q)))
    (w : TangentSpace (I.prod 𝓘(ℝ, F)) (zeroSection F (fun x ↦ annihilatorSpace I D x) q)) :
    (∀ v, SmoothBundleForm.eval₂ (coisotropicModelForm σ hι)
        (zeroSection F (fun x ↦ annihilatorSpace I D x) q)
        (mfderiv I (I.prod 𝓘(ℝ, F)) (zeroSection F fun x ↦ annihilatorSpace I D x) q v) w = 0) ↔
      w ∈ (LinearMap.ker (σ.bilinFormAt q)).map
        (mfderiv I (I.prod 𝓘(ℝ, F)) (zeroSection F fun x ↦ annihilatorSpace I D x) q :
          TangentSpace I q →ₗ[ℝ] _) := by
  obtain ⟨e, he, hζ⟩ := exists_linearEquiv_coisotropicModel σ hι q hq
  set Ω₀ := (SmoothForm.isAlt_bilinFormAt σ q).coisotropicModel
    ((LinearMap.ker (σ.bilinFormAt q)).projectionOnto (D q) hq.symm)
    (Submodule.projectionOnto_apply_left hq.symm)
  have key : (∀ v, SmoothBundleForm.eval₂ (coisotropicModelForm σ hι)
      (zeroSection F (fun x ↦ annihilatorSpace I D x) q)
      (mfderiv I (I.prod 𝓘(ℝ, F)) (zeroSection F fun x ↦ annihilatorSpace I D x) q v) w = 0) ↔
      e w ∈ Ω₀.orthogonal (LinearMap.range (LinearMap.inl ℝ _ _)) := by
    simp only [SymplecticForm.mem_orthogonal_iff, LinearMap.mem_range, LinearMap.inl_apply,
      forall_exists_index, forall_apply_eq_imp_iff, he, hζ, Ω₀]
  rw [key, LinearMap.BilinForm.IsAlt.orthogonal_range_inl_coisotropicModel]
  constructor
  · rintro ⟨k, hk, hkw⟩
    refine ⟨k, hk, e.injective ?_⟩
    rw [ContinuousLinearMap.coe_coe, hζ, ← hkw, LinearMap.inl_apply]
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, by rw [ContinuousLinearMap.coe_coe, hζ, LinearMap.inl_apply]⟩

/-- **The coisotropic model form is nondegenerate near the zero section.** If `D` is complementary
to the kernel of `σ` at every point, then the model form is nondegenerate on an open neighbourhood
`U` of the zero section, so it restricts to a nondegenerate form on `U`. -/
theorem exists_opens_isNondegenerate_mpullback_coisotropicModelForm [FiniteDimensional ℝ F]
    (hσC : ∀ q, IsCompl (D q) (LinearMap.ker (σ.bilinFormAt q))) :
    ∃ U : TopologicalSpace.Opens N,
      (∀ q, zeroSection F (fun x ↦ annihilatorSpace I D x) q ∈ U) ∧
      SmoothTwoForm.IsNondegenerate (SmoothForm.mpullback (Subtype.val : U → N)
        contMDiff_subtypeVal (coisotropicModelForm σ hι)) := by
  -- The model form is nondegenerate where its flat map is invertible, an open condition.
  -- The bundles and the base map are given explicitly, as unification cannot read them off the
  -- section.
  have hU : IsOpen {z | ((coisotropicModelForm σ hι).flat z).IsInvertible} :=
    Continuous.isOpen_setOf_clm_bundle_isInvertible (𝕜 := ℝ) (F₁ := E × F)
      (F₂ := E × F →L[ℝ] ℝ) (E₁ := TangentSpace (I.prod 𝓘(ℝ, F)))
      (E₂ := fun z : N ↦ TangentSpace (I.prod 𝓘(ℝ, F)) z →L[ℝ] ℝ) (b := fun z ↦ z)
      (ϕ := (coisotropicModelForm σ hι).flat) (coisotropicModelForm σ hι).contMDiff_flat.continuous
  refine ⟨⟨_, hU⟩, fun q ↦ ?_, SmoothTwoForm.isNondegenerate_iff_separatingLeft.mpr
    fun z v hv ↦ ?_⟩
  · exact SmoothTwoForm.isInvertible_flat_iff.mpr
      (nondegenerate_bilinFormAt_coisotropicModelForm_zeroSection σ hι q (hσC q))
  · exact ((SmoothTwoForm.nondegenerate_bilinFormAt_mpullback_subtype_val_iff
      (σ := coisotropicModelForm σ hι) z).mpr
        (SmoothTwoForm.isInvertible_flat_iff.mp z.property)).1 v
      fun w ↦ (SmoothForm.bilinFormAt_apply _ z v w).trans (hv w)

end Model

/-- **The coisotropic embedding model.** Let `σ` be a closed two-form on `Q` and `D` a smooth
distribution of rank `k` complementary to the kernel of `σ` at every point, so that the kernels
have constant rank `r`. On an open neighbourhood `U` of the zero section of the annihilator bundle
`D⁰ ≅ (ker σ)*`, of rank `r`, the coisotropic model form restricts to a symplectic form. -/
theorem exists_opens_isSymplectic_mpullback_coisotropicModelForm [FiniteDimensional ℝ E] {k r : ℕ}
    (hσ : σ.IsClosed)
    (hC : IsContMDiffDistribution I ∞ k D) (hk : k + r = finrank ℝ E)
    (hσC : ∀ q, IsCompl (D q) (LinearMap.ker (σ.bilinFormAt q))) :
    -- `∞ + 1` is definitionally `∞` in `WithTop ℕ∞`, so the smooth structure is reused as is.
    haveI : IsManifold I (∞ + 1) Q := ‹IsManifold I ∞ Q›
    letI := hC.annihilatorFiberBundle hk
    letI := hC.annihilatorVectorBundle hk
    letI := hC.annihilatorContMDiffVectorBundle hk
    ∃ U : TopologicalSpace.Opens (TotalSpace (Fin r → ℝ) fun x ↦ annihilatorSpace I D x),
      (∀ q, zeroSection (Fin r → ℝ) (fun x ↦ annihilatorSpace I D x) q ∈ U) ∧
      SmoothTwoForm.IsSymplectic (SmoothForm.mpullback (Subtype.val : U → _) contMDiff_subtypeVal
        (coisotropicModelForm σ (hC.contMDiff_annihilatorInclusion hk))) := by
  -- As in the statement, `∞ + 1` is definitionally `∞`.
  have : IsManifold I (∞ + 1) Q := ‹IsManifold I ∞ Q›
  let := hC.annihilatorFiberBundle hk
  let := hC.annihilatorVectorBundle hk
  let := hC.annihilatorContMDiffVectorBundle hk
  obtain ⟨U, hζU, hU⟩ := exists_opens_isNondegenerate_mpullback_coisotropicModelForm σ
    (hC.contMDiff_annihilatorInclusion hk) hσC
  exact ⟨U, hζU, ((isClosed_coisotropicModelForm_iff σ _).mpr hσ).mpullback _ _, hU⟩

end TauCeti.CotangentBundle
