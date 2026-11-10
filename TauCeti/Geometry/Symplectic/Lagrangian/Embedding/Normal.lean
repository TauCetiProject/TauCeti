/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Quotient
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback
public import TauCeti.Geometry.Symplectic.Lagrangian.Manifold
public import TauCeti.Geometry.Symplectic.Manifold.Flat
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The normal bundle of a Lagrangian embedding is its cotangent bundle

Let `f : Q → M` be a smooth embedding into a manifold with a nondegenerate two-form `σ`, whose
tangent images `df_x(T_x Q)` are Lagrangian. At each point `x` the normal space
`T_(f x) M ⧸ df_x(T_x Q)` is identified with the cotangent space `T_x^* Q` by

`[v] ↦ σ_(f x)(df_x ·, v)`

(`TauCeti.SmoothEmbedding.normalSpaceEquivOfIsLagrangianMap`). The covector
`σ_(f x)(df_x ·, v)` (`TauCeti.SmoothEmbedding.pairingCovector`) vanishes exactly when `v` is
`σ`-orthogonal to the tangent image, that is, when `v` lies in the tangent image, which is
Lagrangian. So it descends to an injective map on the normal space, which is bijective because
both spaces have the dimension of `Q`.

These fibrewise isomorphisms are smooth. For a `C^n` embedding the intrinsic normal bundle is a
`C^m` vector bundle when `m + 1 ≤ n`, and for `m + 1 ≤ ∞` the induced map of total spaces into the
cotangent bundle `T^* Q` is `C^m`
(`TauCeti.SmoothEmbedding.contMDiff_normalSpaceEquivOfIsLagrangianMap`).
Since a smooth family of fibrewise linear equivalences has a smooth inverse, the normal bundle of a
Lagrangian embedding is `C^m`-diffeomorphic to `T^* Q` over the identity of `Q`
(`TauCeti.SmoothEmbedding.normalBundleDiffeomorphOfIsLagrangianMap`).

Combined with a tubular neighbourhood, this identifies a neighbourhood of a Lagrangian submanifold
with a neighbourhood of the zero section of its cotangent bundle. It is the linear input of
Weinstein's Lagrangian neighbourhood theorem.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 8.
* A. Weinstein, *Symplectic manifolds and their Lagrangian submanifolds*, Advances in
  Mathematics 6 (1971), 329–346.
-/

public section

noncomputable section

open Bundle Module
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {E F P H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  {n : ℕ∞ω} {σ : SmoothTwoForm J N} {hσ : σ.IsNondegenerate}
  (f : SmoothEmbedding I J n M N)

/-- The covector `σ_(f x)(df_x ·, v)` at `x` obtained by pairing an ambient tangent vector `v` at
`f x` with the tangent vectors of the embedded manifold, as a continuous linear function of `v`.
It is `(-σ)(v, ·)` pulled back along `df_x`. -/
def pairingCovector (σ : SmoothTwoForm J N) (x : M) :
    TangentSpace J (f x) →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  -- Tangent spaces are their model spaces, whose norms make composition continuous.
  (ContinuousLinearMap.compL ℝ E F ℝ).flip (mfderiv I J f x) ∘L (-σ).flat (f x)

/-- The pairing covector of `v` is the contraction `(-σ)(v, ·)` pulled back along `df_x`. -/
theorem pairingCovector_apply (x : M) (v : TangentSpace J (f x)) :
    f.pairingCovector σ x v = (-σ).flat (f x) v ∘L mfderiv I J f x :=
  ContinuousLinearMap.ext fun _ ↦ rfl

/-- The pairing covector of `v` evaluates on `u` as `σ_(f x)(df_x u, v)`. -/
@[simp]
theorem pairingCovector_apply_apply (x : M) (v : TangentSpace J (f x)) (u : TangentSpace I x) :
    f.pairingCovector σ x v u = SmoothBundleForm.eval₂ σ (f x) (mfderiv I J f x u) v := by
  rw [pairingCovector_apply, ContinuousLinearMap.comp_apply, SmoothTwoForm.flat_apply,
    SmoothBundleForm.eval₂_neg, SmoothBundleForm.eval₂_swap, neg_neg]

variable {f} in
/-- For an isotropic embedding, the covector `σ(df ·, v)` vanishes for `v` tangent to the image. -/
theorem pairingCovector_eq_zero_of_mem_tangentRange (hf : hσ.IsIsotropicMap I f) (hn : n ≠ 0)
    (x : M) {v : TangentSpace J (f x)} (hv : v ∈ f.tangentRange x hn) :
    f.pairingCovector σ x v = 0 := by
  obtain ⟨w, rfl⟩ := hv
  ext u
  simpa using SmoothTwoForm.IsNondegenerate.isIsotropicMap_iff.1 hf x u w

variable {f} in
/-- For a Lagrangian embedding, the covector `σ(df ·, v)` vanishes exactly for `v` tangent to the
image. -/
theorem pairingCovector_eq_zero_iff_mem_tangentRange (hf : hσ.IsLagrangianMap I f) (hn : n ≠ 0)
    (x : M) (v : TangentSpace J (f x)) :
    f.pairingCovector σ x v = 0 ↔ v ∈ f.tangentRange x hn := by
  refine ⟨fun h ↦ ?_, pairingCovector_eq_zero_of_mem_tangentRange hf.isIsotropicMap hn x⟩
  refine SymplecticForm.isCoisotropic_iff.1
    (SmoothTwoForm.IsNondegenerate.isCoisotropicMap_iff.1 hf.isCoisotropicMap x) v ?_
  rintro _ ⟨u, rfl⟩
  simpa using congr($h u)

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- **The normal space of a Lagrangian embedding is its cotangent space.** For an embedding `f`
with Lagrangian tangent images for a nondegenerate two-form `σ`, the normal class `[v]` of an
ambient tangent vector `v` at `f x` corresponds to the covector `σ_(f x)(df_x ·, v)` at `x`. -/
def normalSpaceEquivOfIsLagrangianMap (hf : hσ.IsLagrangianMap I f) (hn : n ≠ 0) (x : M) :
    f.NormalSpace x hn ≃L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  let φ := f.normalLiftL x hn (f.pairingCovector σ x)
    fun _ ↦ pairingCovector_eq_zero_of_mem_tangentRange hf.isIsotropicMap hn x
  have hφ : ∀ v, φ (f.normalClass x hn v) = f.pairingCovector σ x v := fun v ↦ by
    rw [← normalClassL_apply, ← ContinuousLinearMap.comp_apply, normalLiftL_comp_normalClassL]
  have hinj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun w hw ↦ ?_
    obtain ⟨v, rfl⟩ := f.normalClass_surjective x hn w
    rw [hφ, pairingCovector_eq_zero_iff_mem_tangentRange hf hn] at hw
    exact (f.normalClass_eq_zero_iff x hn v).2 hw
  -- The normal space and the cotangent space both have the dimension of `T_x Q`.
  have hdim : finrank ℝ (f.NormalSpace x hn) = finrank ℝ (TangentSpace I x →L[ℝ] ℝ) := by
    have h2 := hf.two_mul_finrank (f.isImmersion.mfderiv_injective hn x)
    rw [f.finrank_normalSpace x hn, ← LinearMap.toContinuousLinearMap.finrank_eq,
      Subspace.dual_finrank_eq, finrank_tangentSpace, finrank_tangentSpace]
    omega
  (φ.toLinearMap.linearEquivOfInjective hinj hdim).toContinuousLinearEquiv

variable {f} in
/-- The normal class `[v]` of an ambient tangent vector at `f x` corresponds to the covector
`σ_(f x)(df_x ·, v)`. -/
@[simp]
theorem normalSpaceEquivOfIsLagrangianMap_normalClass (hf : hσ.IsLagrangianMap I f) (hn : n ≠ 0)
    (x : M) (v : TangentSpace J (f x)) :
    f.normalSpaceEquivOfIsLagrangianMap hf hn x (f.normalClass x hn v) =
      f.pairingCovector σ x v := by
  rw [normalSpaceEquivOfIsLagrangianMap, LinearEquiv.coe_toContinuousLinearEquiv',
    LinearMap.linearEquivOfInjective_apply, ContinuousLinearMap.coe_coe, ← normalClassL_apply,
    ← ContinuousLinearMap.comp_apply, normalLiftL_comp_normalClassL]

variable {f} in
/-- The codimension of a Lagrangian embedding of a nonempty manifold is the dimension of its
cotangent model fibre, so `E →L[ℝ] ℝ` is a model fibre for its normal bundle. -/
theorem finrank_continuousLinearMap_eq_sub_of_isLagrangianMap [Nonempty M]
    (hf : hσ.IsLagrangianMap I f) (hn : n ≠ 0) :
    finrank ℝ (E →L[ℝ] ℝ) = finrank ℝ F - finrank ℝ E := by
  have h2 := hf.two_mul_finrank (f.isImmersion.mfderiv_injective hn (Classical.arbitrary M))
  rw [← LinearMap.toContinuousLinearMap.finrank_eq, Subspace.dual_finrank_eq]
  omega

variable {f} {m : ℕ∞ω} [IsManifold I (m + 1) M]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- **The identification of the normal bundle of a Lagrangian embedding with its cotangent
bundle is smooth.** For a `C^n` embedding with Lagrangian tangent images and `m + 1 ≤ n`, the map
of total spaces from the intrinsic normal bundle, with model fibre `P` of the codimension, to the
cotangent bundle `T^* Q` induced by `normalSpaceEquivOfIsLagrangianMap` is `C^m`. The bound
`m + 1 ≤ ∞` reflects that the form `σ` is smooth. -/
theorem contMDiff_normalSpaceEquivOfIsLagrangianMap (hf : hσ.IsLagrangianMap I f) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hm' : m + 1 ≤ ∞) (hdim : finrank ℝ P = finrank ℝ F - finrank ℝ E) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    ContMDiff (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) m
      (fun p : TotalSpace P (fun x ↦ f.NormalSpace x hn) ↦
        (TotalSpace.mk' (E →L[ℝ] ℝ) p.proj
          (f.normalSpaceEquivOfIsLagrangianMap hf hn p.proj p.2) : CotangentBundle I M)) := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  have : IsManifold J (m + 1) N := .of_le hm'
  let := f.normalSpaceFiberBundle hn hdim
  rw [f.contMDiff_normalBundle_iff hn hm hdim]
  have hfm : ContMDiff I J (m + 1) f := f.contMDiff.of_le hm
  -- The ambient covector `(-σ)(v, ·) = σ(·, v)` at `f x`, as a function of `⟨x, v⟩`.
  have hlift : ContMDiff (I.prod 𝓘(ℝ, F)) (J.prod 𝓘(ℝ, F)) m
      (fun p : TotalSpace F ((f : M → N) *ᵖ (TangentSpace J)) ↦
        TotalSpace.mk' F (E := TangentSpace J) (f p.proj) p.2) :=
    ((Bundle.Pullback.contMDiff_iff f (hfm.of_le le_self_add)).mp contMDiff_id).2
  have hflat : ContMDiff (I.prod 𝓘(ℝ, F)) (J.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) m
      (fun p : TotalSpace F ((f : M → N) *ᵖ (TangentSpace J)) ↦
        TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
          (E := fun y : N ↦ TangentSpace J y →L[ℝ] TangentSpace J y →L[ℝ] ℝ)
          (f p.proj) ((-σ).flat (f p.proj))) :=
    ((-σ).contMDiff_flat.of_le (le_self_add.trans hm')).comp
      ((hfm.of_le le_self_add).comp
        (Bundle.contMDiff_proj (F := F) ((f : M → N) *ᵖ (TangentSpace J))))
  have hΨ := ContMDiff.clm_bundle_apply (F₁ := F) (F₂ := F →L[ℝ] ℝ) (E₁ := TangentSpace J)
    (E₂ := fun y : N ↦ TangentSpace J y →L[ℝ] ℝ) hflat hlift
  refine (CotangentBundle.contMDiff_mk_comp_mfderiv (f := f) (g := TotalSpace.proj) (fun _ ↦ rfl)
    hΨ (Bundle.contMDiff_proj (F := F) ((f : M → N) *ᵖ (TangentSpace J)))
    f.contMDiff hm).congr fun ⟨x, v⟩ ↦ ?_
  rw [Function.comp_apply, normalQuotientMap_apply]
  exact congrArg (TotalSpace.mk' (E →L[ℝ] ℝ) x)
    ((normalSpaceEquivOfIsLagrangianMap_normalClass hf hn x v).trans
      (f.pairingCovector_apply x v))

/-- **The normal bundle of a Lagrangian embedding is diffeomorphic to its cotangent bundle.** For
a `C^n` embedding with Lagrangian tangent images and `m + 1 ≤ n`, the intrinsic normal bundle,
with model fibre `P` of the codimension, is `C^m`-diffeomorphic to `T^* Q` over the identity, by
`[v] ↦ σ(df ·, v)` on each fibre. -/
def normalBundleDiffeomorphOfIsLagrangianMap (hf : hσ.IsLagrangianMap I f) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hm' : m + 1 ≤ ∞) (hdim : finrank ℝ P = finrank ℝ F - finrank ℝ E) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^m⟮I.prod 𝓘(ℝ, P), I.prod 𝓘(ℝ, E →L[ℝ] ℝ)⟯
      CotangentBundle I M :=
  haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  letI := f.normalSpaceFiberBundle hn hdim
  letI := f.normalSpaceVectorBundle hn hdim
  TauCeti.bundleDiffeomorph (f.normalSpaceEquivOfIsLagrangianMap hf hn)
    (contMDiff_normalSpaceEquivOfIsLagrangianMap hf hn hm hm' hdim)

/-- The diffeomorphism sends a normal vector at `x` to its covector at `x`. -/
@[simp]
theorem normalBundleDiffeomorphOfIsLagrangianMap_apply (hf : hσ.IsLagrangianMap I f) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hm' : m + 1 ≤ ∞) (hdim : finrank ℝ P = finrank ℝ F - finrank ℝ E)
    (p : TotalSpace P (fun x ↦ f.NormalSpace x hn)) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    normalBundleDiffeomorphOfIsLagrangianMap hf hn hm hm' hdim p =
      ⟨p.proj, f.normalSpaceEquivOfIsLagrangianMap hf hn p.proj p.2⟩ := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  exact TauCeti.bundleDiffeomorph_apply _ _ p

/-- The inverse diffeomorphism sends a covector at `x` to the corresponding normal vector at `x`. -/
@[simp]
theorem normalBundleDiffeomorphOfIsLagrangianMap_symm_apply (hf : hσ.IsLagrangianMap I f)
    (hn : n ≠ 0) (hm : m + 1 ≤ n) (hm' : m + 1 ≤ ∞) (hdim : finrank ℝ P = finrank ℝ F - finrank ℝ E)
    (p : CotangentBundle I M) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    (normalBundleDiffeomorphOfIsLagrangianMap hf hn hm hm' hdim).symm p =
      ⟨p.proj, (f.normalSpaceEquivOfIsLagrangianMap hf hn p.proj).symm p.2⟩ := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  exact TauCeti.bundleDiffeomorph_symm_apply _ _ p

end TauCeti.SmoothEmbedding
