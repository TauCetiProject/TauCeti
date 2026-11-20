/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Prod
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Geometry.Manifold.Riemannian.Sphere.Gradient
import TauCeti.Geometry.Manifold.VectorBundle.Trivial

/-!
# Smooth structure of the sphere tangent bundle and radial-normal splitting

For an `(n + 1)`-dimensional real inner product space `E`, `TauCeti.sphereTangentEquiv x`
identifies the native tangent space `TangentSpace (𝓡 n) x` at `x : sphere (0 : E) 1` isometrically
with the orthogonal complement `(ℝ ∙ (x : E))ᗮ`. Building on
`TauCeti.contMDiff_coe_sphereTangentEquiv` (in `Sphere/Basic.lean`) and
`TauCeti.contMDiff_sphereTangentEquiv_symm` (in `Sphere/Gradient.lean`), this file promotes that
pointwise identification to `C^k` manifold and vector-bundle equivalences at every regularity
`k : ℕ∞ω`:

* `TauCeti.sphereTangentProj` and `TauCeti.contMDiff_sphereTangentProj`: projecting an ambient
  vector tangentially back to `TangentSpace (𝓡 n) x` via `(ℝ ∙ (x : E))ᗮ.orthogonalProjectionOnto`
  is `C^k` for all `k : ℕ∞ω`.
* `TauCeti.contMDiff_sphereTangentEquiv_symm_along_iff`: lifting an ambient map `w : M → E`
  satisfying `w y ∈ (ℝ ∙ (base y : E))ᗮ` along `(sphereTangentEquiv (base y)).symm` produces a
  `C^k` map into `TangentBundle (𝓡 n) (sphere (0 : E) 1)` if and only if `base` and `w` are `C^k`.
* `TauCeti.hasLocalContMDiffSubbundleFrames_orthogonalSpanSphere` and
  `TauCeti.sphereTangentSubbundleDiffeomorph`: the orthogonal complements `(ℝ ∙ (x : E))ᗮ` form a
  `C^k` subbundle of the trivial bundle `sphere (0 : E) 1 × E`, and `sphereTangentEquiv` gives a
  `C^k` bundle diffeomorphism onto its total space.
* `TauCeti.sphereTangentProdRealDiffeomorph` and `TauCeti.sphereTangentProdTrivialDiffeomorph`:
  adjoining the radial normal line `ℝ ∙ (x : E)` splits the ambient trivial bundle as
  `TSⁿ ⊕ ε¹ ≅ εⁿ⁺¹`, with explicit inverse `u ↦ (sphereTangentProj x u, ⟪x, u⟫)`.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press (1974), §3 and §11.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 10.
* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
-/

public section

noncomputable section

open Bundle Metric Module Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)]

/-! ### Smooth tangential projection and tangent lifts -/

/-- Tangential projection of an ambient vector `u : E` into the native tangent space
`TangentSpace (𝓡 n) x` at `x : sphere (0 : E) 1`. -/
def sphereTangentProj (x : sphere (0 : E) 1) (u : E) : TangentSpace (𝓡 n) x :=
  (sphereTangentEquiv x).symm ((ℝ ∙ (x : E))ᗮ.orthogonalProjectionOnto u)

@[simp]
theorem sphereTangentEquiv_sphereTangentProj (x : sphere (0 : E) 1) (u : E) :
    sphereTangentEquiv (n := n) x (sphereTangentProj (n := n) x u) =
      (ℝ ∙ (x : E))ᗮ.orthogonalProjectionOnto u :=
  LinearIsometryEquiv.apply_symm_apply _ _

theorem coe_sphereTangentEquiv_sphereTangentProj (x : sphere (0 : E) 1) (u : E) :
    (sphereTangentEquiv (n := n) x (sphereTangentProj (n := n) x u) : E) =
      u - inner ℝ (x : E) u • (x : E) := by
  rw [sphereTangentEquiv_sphereTangentProj, Submodule.coe_orthogonalProjectionOnto_apply,
    Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_unit_singleton ℝ (norm_eq_of_mem_sphere x)]

@[simp]
theorem mfderiv_subtypeVal_sphereTangentProj (x : sphere (0 : E) 1) (u : E) :
    mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x (sphereTangentProj (n := n) x u) =
      u - inner ℝ (x : E) u • (x : E) := by
  rw [← coe_sphereTangentEquiv_apply, coe_sphereTangentEquiv_sphereTangentProj]

@[simp]
theorem sphereTangentProj_of_mem_orthogonal {x : sphere (0 : E) 1} {u : E}
    (hu : u ∈ (ℝ ∙ (x : E))ᗮ) :
    sphereTangentProj (n := n) x u = (sphereTangentEquiv (n := n) x).symm ⟨u, hu⟩ := by
  rw [sphereTangentProj, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨u, hu⟩]

theorem sphereTangentProj_coe_sphereTangentEquiv (x : sphere (0 : E) 1)
    (v : TangentSpace (𝓡 n) x) :
    sphereTangentProj x (sphereTangentEquiv x v) = v := by
  rw [sphereTangentProj_of_mem_orthogonal (sphereTangentEquiv x v).property, Subtype.coe_eta,
    LinearIsometryEquiv.symm_apply_apply]

@[simp]
theorem sphereTangentProj_mfderiv_subtypeVal (x : sphere (0 : E) 1)
    (v : TangentSpace (𝓡 n) x) :
    sphereTangentProj x (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x v) = v := by
  rw [← coe_sphereTangentEquiv_apply, sphereTangentProj_coe_sphereTangentEquiv]

@[simp]
theorem sphereTangentProj_coe_self (x : sphere (0 : E) 1) :
    sphereTangentProj (n := n) x (x : E) = 0 := by
  rw [sphereTangentProj,
    Submodule.orthogonalProjectionOnto_orthogonal_apply_eq_zero
      (Submodule.mem_span_singleton_self (x : E)),
    map_zero]

/-- Projecting an ambient vector `(x, u) : sphere (0 : E) 1 × E` tangentially into
`TangentBundle (𝓡 n) (sphere (0 : E) 1)` is `C^k` at every regularity `k : ℕ∞ω`. -/
theorem contMDiff_sphereTangentProj {k : ℕ∞ω} :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ, E)) (𝓡 n).tangent k
      (fun p : sphere (0 : E) 1 × E ↦
        (⟨p.1, sphereTangentProj p.1 p.2⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) := by
  have hu : ContMDiff ((𝓡 n).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) k
      (fun p : sphere (0 : E) 1 × E ↦ ((ℝ ∙ (p.1 : E))ᗮ.orthogonalProjectionOnto p.2 : E)) := by
    have hsub : ContMDiff ((𝓡 n).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) k
        (fun p : sphere (0 : E) 1 × E ↦ p.2 - inner ℝ (p.1 : E) p.2 • (p.1 : E)) :=
      contMDiff_snd.sub
        ((contDiff_inner.contMDiff.comp
          ((contMDiff_coe_sphere.comp contMDiff_fst).prodMk_space contMDiff_snd)).smul
          (contMDiff_coe_sphere.comp contMDiff_fst))
    exact hsub.congr fun p ↦ by
      rw [Submodule.coe_orthogonalProjectionOnto_apply, Submodule.starProjection_orthogonal_val,
        Submodule.starProjection_unit_singleton ℝ (norm_eq_of_mem_sphere p.1)]
  exact contMDiff_sphereTangentEquiv_symm contMDiff_fst hu fun p ↦
    ((ℝ ∙ (p.1 : E))ᗮ.orthogonalProjectionOnto p.2).property

/-- **Smoothness of sphere tangent lifts.** A map
`y ↦ ⟨base y, (sphereTangentEquiv (base y)).symm ⟨w y, hw y⟩⟩` into
`TangentBundle (𝓡 n) (sphere (0 : E) 1)` is `C^k` if and only if both `base` and the ambient
vector map `w` are `C^k`. -/
theorem contMDiff_sphereTangentEquiv_symm_along_iff
    {EM H M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [TopologicalSpace H] {J : ModelWithCorners ℝ EM H}
    [TopologicalSpace M] [ChartedSpace H M] {k : ℕ∞ω}
    {base : M → sphere (0 : E) 1} {w : M → E} (hw : ∀ y, w y ∈ (ℝ ∙ (base y : E))ᗮ) :
    ContMDiff J (𝓡 n).tangent k
        (fun y ↦ (⟨base y, (sphereTangentEquiv (base y)).symm ⟨w y, hw y⟩⟩ :
          TangentBundle (𝓡 n) (sphere (0 : E) 1))) ↔
      ContMDiff J (𝓡 n) k base ∧ ContMDiff J 𝓘(ℝ, E) k w := by
  refine ⟨fun h ↦ ⟨(Bundle.contMDiff_proj _).comp h, ?_⟩, fun ⟨hb, hwm⟩ ↦
    contMDiff_sphereTangentEquiv_symm hb hwm hw⟩
  refine (contMDiff_coe_sphereTangentEquiv.comp h).congr fun y ↦ ?_
  simp only [Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]

/-! ### The smooth subbundle `(ℝ ∙ x)ᗮ` and bundle equivalence with `TSⁿ` -/

/-- The tangent hyperplanes `(ℝ ∙ (x : E))ᗮ` admit `C^k` local subbundle frames of rank `n` inside
the ambient trivial bundle `Bundle.Trivial (sphere (0 : E) 1) E` at every regularity `k : ℕ∞ω`. -/
theorem hasLocalContMDiffSubbundleFrames_orthogonalSpanSphere {k : ℕ∞ω} :
    HasLocalContMDiffSubbundleFrames (𝓡 n) k E (Fin n)
      (fun x : sphere (0 : E) 1 ↦
        ((ℝ ∙ (x : E))ᗮ : Submodule ℝ (Bundle.Trivial (sphere (0 : E) 1) E x))) := by
  refine hasLocalContMDiffSubbundleFrames_iff.mpr fun x₀ ↦ ?_
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x₀
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let X : Fin n → ∀ x : sphere (0 : E) 1, Bundle.Trivial (sphere (0 : E) 1) E x :=
    fun i x ↦ (sphereTangentEquiv x (e.symm x (b i)) : E)
  have hX (i : Fin n) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) k
        (fun x ↦ TotalSpace.mk' E (E := Bundle.Trivial (sphere (0 : E) 1) E) x (X i x))
        e.baseSet := by
    have hsec : ContMDiffOn (𝓡 n) (𝓡 n).tangent k
        (fun x ↦ (⟨x, e.symm x (b i)⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) e.baseSet := by
      intro x hx
      refine ((e.contMDiffAt_section_iff hx).mpr ?_).contMDiffWithinAt
      refine (contMDiffAt_const (c := b i)).congr_of_eventuallyEq ?_
      filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
      simp [e.apply_mk_symm hy]
    intro x hx
    exact (Bundle.Trivial.contMDiffAt_mk_iff.mpr ⟨contMDiffAt_id,
      contMDiff_coe_sphereTangentEquiv.contMDiffAt.comp x
        ((hsec x hx).contMDiffAt (e.open_baseSet.mem_nhds hx))⟩).contMDiffWithinAt
  have hbasis (x : sphere (0 : E) 1) (hx : x ∈ e.baseSet) :
      (fun i ↦ X i x) =
        fun i ↦ (((b.toBasis.map (e.linearEquivAt ℝ x hx).symm).map
          (sphereTangentEquiv x).toLinearEquiv) i : E) := by
    ext i
    dsimp only [X, Basis.map_apply, LinearIsometryEquiv.coe_toLinearEquiv]
    rw [e.linearEquivAt_symm_apply x hx, OrthonormalBasis.coe_toBasis]
  refine ⟨e.baseSet, e.open_baseSet, FiberBundle.mem_baseSet_trivializationAt' x₀, X, ?_, hX⟩
  refine
    { continuousOn := fun i ↦ (hX i).continuousOn
      linearIndependent := fun {x} hx ↦ ?_
      span_eq := fun {x} hx ↦ ?_ }
  · rw [hbasis x hx]
    exact (((b.toBasis.map (e.linearEquivAt ℝ x hx).symm).map
      (sphereTangentEquiv x).toLinearEquiv).linearIndependent).map' (ℝ ∙ (x : E))ᗮ.subtype
      (Submodule.ker_subtype _)
  · rw [hbasis x hx]
    set B := (b.toBasis.map (e.linearEquivAt ℝ x hx).symm).map
      (sphereTangentEquiv x).toLinearEquiv
    calc
      Submodule.span ℝ (range fun i ↦ (B i : E))
        = (Submodule.span ℝ (range B)).map (ℝ ∙ (x : E))ᗮ.subtype := by
            rw [Submodule.map_span, ← range_comp]
            rfl
      _ = (⊤ : Submodule ℝ (ℝ ∙ (x : E))ᗮ).map (ℝ ∙ (x : E))ᗮ.subtype := by rw [B.span_eq]
      _ = (ℝ ∙ (x : E))ᗮ := Submodule.map_subtype_top _

omit [Fact (finrank ℝ E = n + 1)] in
/-- The total space of the orthogonal-complement hyperplanes `(ℝ ∙ (x : E))ᗮ` over the unit sphere
carries the subspace topology from `sphere (0 : E) 1 × E`. -/
instance instTopologicalSpaceTotalSpaceOrthogonalSpanSphere (F : Type*) :
    TopologicalSpace (TotalSpace F fun x : sphere (0 : E) 1 ↦ (ℝ ∙ (x : E))ᗮ) :=
  subbundleTopology E (F' := F)
    (fun x : sphere (0 : E) 1 ↦
      ((ℝ ∙ (x : E))ᗮ : Submodule ℝ (Bundle.Trivial (sphere (0 : E) 1) E x)))

/-- The orthogonal-complement hyperplanes `(ℝ ∙ (x : E))ᗮ` form a rank-`n` fibre bundle over
`sphere (0 : E) 1` via their analytic subbundle frames. -/
instance instFiberBundleOrthogonalSpanSphere :
    FiberBundle (Fin n → ℝ) (fun x : sphere (0 : E) 1 ↦ (ℝ ∙ (x : E))ᗮ) :=
  (hasLocalContMDiffSubbundleFrames_orthogonalSpanSphere (E := E) (n := n) (k := ω)).fiberBundle

/-- The orthogonal-complement hyperplanes `(ℝ ∙ (x : E))ᗮ` form a real vector bundle over
`sphere (0 : E) 1`. -/
instance instVectorBundleOrthogonalSpanSphere :
    VectorBundle ℝ (Fin n → ℝ) (fun x : sphere (0 : E) 1 ↦ (ℝ ∙ (x : E))ᗮ) :=
  (hasLocalContMDiffSubbundleFrames_orthogonalSpanSphere (E := E) (n := n) (k := ω)).vectorBundle

/-- The orthogonal-complement subbundle `(ℝ ∙ (x : E))ᗮ` over `sphere (0 : E) 1` is an analytic
(`C^ω`, hence `C^k` for every `k : ℕ∞ω`) vector bundle. -/
instance instContMDiffVectorBundleOrthogonalSpanSphere :
    ContMDiffVectorBundle ω (Fin n → ℝ) (fun x : sphere (0 : E) 1 ↦ (ℝ ∙ (x : E))ᗮ) (𝓡 n) :=
  (hasLocalContMDiffSubbundleFrames_orthogonalSpanSphere
    (E := E) (n := n) (k := ω)).contMDiffVectorBundle

/-- **Smooth isomorphism between `TSⁿ` and the orthogonal-complement subbundle `x^⊥`.**
Differentiating the ambient inclusion identifies `TangentBundle (𝓡 n) (sphere (0 : E) 1)` with the
total space of the subbundle `x ↦ (ℝ ∙ (x : E))ᗮ` by a `C^k` bundle diffeomorphism at every
regularity `k : ℕ∞ω`, with inverse `(sphereTangentEquiv x).symm`. -/
def sphereTangentSubbundleDiffeomorph {k : ℕ∞ω} :
    TangentBundle (𝓡 n) (sphere (0 : E) 1) ≃ₘ^k⟮(𝓡 n).tangent, (𝓡 n).prod 𝓘(ℝ, Fin n → ℝ)⟯
      TotalSpace (Fin n → ℝ) (fun x : sphere (0 : E) 1 ↦ (ℝ ∙ (x : E))ᗮ) := by
  let hsub := hasLocalContMDiffSubbundleFrames_orthogonalSpanSphere (E := E) (n := n) (k := ω)
  have hincl : ContMDiff ((𝓡 n).prod 𝓘(ℝ, Fin n → ℝ)) ((𝓡 n).prod 𝓘(ℝ, E)) k
      (fun q : TotalSpace (Fin n → ℝ) (fun x : sphere (0 : E) 1 ↦ (ℝ ∙ (x : E))ᗮ) ↦
        (⟨q.proj, (q.snd : E)⟩ : TotalSpace E (Bundle.Trivial (sphere (0 : E) 1) E))) :=
    hsub.contMDiff_totalSpace_inclusion.of_le le_top
  have hinv : ContMDiff ((𝓡 n).prod 𝓘(ℝ, Fin n → ℝ)) (𝓡 n).tangent k
      (fun q : TotalSpace (Fin n → ℝ) (fun x : sphere (0 : E) 1 ↦ (ℝ ∙ (x : E))ᗮ) ↦
        TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) q.proj
          ((sphereTangentEquiv (n := n) q.proj).symm.toContinuousLinearEquiv q.snd)) :=
    (contMDiff_sphereTangentEquiv_symm_along_iff fun q ↦ q.snd.property).mpr
      (Bundle.Trivial.contMDiff_mk_iff.mp hincl)
  exact (bundleDiffeomorph
    (fun x ↦ (sphereTangentEquiv (n := n) x).symm.toContinuousLinearEquiv) hinv).symm

@[simp]
theorem sphereTangentSubbundleDiffeomorph_apply {k : ℕ∞ω}
    (p : TangentBundle (𝓡 n) (sphere (0 : E) 1)) :
    sphereTangentSubbundleDiffeomorph (k := k) p = ⟨p.proj, sphereTangentEquiv p.proj p.snd⟩ := by
  simp [sphereTangentSubbundleDiffeomorph]

@[simp]
theorem sphereTangentSubbundleDiffeomorph_symm_apply {k : ℕ∞ω}
    (q : TotalSpace (Fin n → ℝ) (fun x : sphere (0 : E) 1 ↦ (ℝ ∙ (x : E))ᗮ)) :
    (sphereTangentSubbundleDiffeomorph (k := k)).symm q =
      ⟨q.proj, (sphereTangentEquiv q.proj).symm q.snd⟩ := by
  rw [sphereTangentSubbundleDiffeomorph]
  exact bundleDiffeomorph_apply _ _ q

/-! ### Radial-normal splitting `TSⁿ ⊕ ε¹ ≅ εⁿ⁺¹` -/

/-- **Radial-normal splitting of the sphere tangent bundle.** Adjoining the radial normal coordinate
`t` sends `(⟨x, v⟩, t) : TangentBundle (𝓡 n) (sphere (0 : E) 1) × ℝ` to
`(x, sphereTangentEquiv x v + t • x) : sphere (0 : E) 1 × E`, a `C^k` diffeomorphism with inverse
`(x, u) ↦ (⟨x, sphereTangentProj x u⟩, ⟪x, u⟫)`. -/
def sphereTangentProdRealDiffeomorph {k : ℕ∞ω} :
    (TangentBundle (𝓡 n) (sphere (0 : E) 1) × ℝ) ≃ₘ^k⟮(𝓡 n).tangent.prod 𝓘(ℝ, ℝ),
      (𝓡 n).prod 𝓘(ℝ, E)⟯ (sphere (0 : E) 1 × E) where
  toFun p := (p.1.proj, (sphereTangentEquiv p.1.proj p.1.snd : E) + p.2 • (p.1.proj : E))
  invFun q := (⟨q.1, sphereTangentProj q.1 q.2⟩, inner ℝ (q.1 : E) q.2)
  left_inv := by
    rintro ⟨⟨x, v⟩, t⟩
    have hx : inner ℝ (x : E) (x : E) = 1 :=
      inner_self_eq_one_of_norm_eq_one (norm_eq_of_mem_sphere x)
    have horth : inner ℝ (x : E) (sphereTangentEquiv x v : E) = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp (sphereTangentEquiv x v).property
    have hinner : inner ℝ (x : E) ((sphereTangentEquiv x v : E) + t • (x : E)) = t := by
      rw [inner_add_right, real_inner_smul_right, horth, hx, zero_add, mul_one]
    refine Prod.ext (TotalSpace.ext rfl ?_) hinner
    simp only [heq_eq_eq]
    apply (sphereTangentEquiv x).injective
    apply Subtype.ext
    rw [coe_sphereTangentEquiv_sphereTangentProj, hinner, add_sub_cancel_right]
  right_inv := by
    rintro ⟨x, u⟩
    refine Prod.ext rfl ?_
    dsimp only
    rw [coe_sphereTangentEquiv_sphereTangentProj, sub_add_cancel]
  contMDiff_toFun := by
    have hbase : ContMDiff ((𝓡 n).tangent.prod 𝓘(ℝ, ℝ)) (𝓡 n) k
        (fun p : TangentBundle (𝓡 n) (sphere (0 : E) 1) × ℝ ↦ p.1.proj) :=
      (Bundle.contMDiff_proj _).comp contMDiff_fst
    have htan : ContMDiff ((𝓡 n).tangent.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) k
        (fun p : TangentBundle (𝓡 n) (sphere (0 : E) 1) × ℝ ↦
          (sphereTangentEquiv p.1.proj p.1.snd : E)) :=
      contMDiff_coe_sphereTangentEquiv.comp contMDiff_fst
    have hrad : ContMDiff ((𝓡 n).tangent.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) k
        (fun p : TangentBundle (𝓡 n) (sphere (0 : E) 1) × ℝ ↦ p.2 • (p.1.proj : E)) :=
      contMDiff_snd.smul (contMDiff_coe_sphere.comp hbase)
    exact hbase.prodMk (htan.add hrad)
  contMDiff_invFun :=
    contMDiff_sphereTangentProj.prodMk
      (contDiff_inner.contMDiff.comp
        ((contMDiff_coe_sphere.comp contMDiff_fst).prodMk_space contMDiff_snd))

@[simp]
theorem sphereTangentProdRealDiffeomorph_apply {k : ℕ∞ω}
    (p : TangentBundle (𝓡 n) (sphere (0 : E) 1) × ℝ) :
    sphereTangentProdRealDiffeomorph (k := k) p =
      (p.1.proj, (sphereTangentEquiv p.1.proj p.1.snd : E) + p.2 • (p.1.proj : E)) :=
  (rfl)

@[simp]
theorem sphereTangentProdRealDiffeomorph_symm_apply {k : ℕ∞ω} (q : sphere (0 : E) 1 × E) :
    (sphereTangentProdRealDiffeomorph (n := n) (k := k)).symm q =
      (⟨q.1, sphereTangentProj (n := n) q.1 q.2⟩, inner ℝ (q.1 : E) q.2) :=
  (rfl)

/-- **Whitney-sum form of the radial-normal splitting (`TSⁿ ⊕ ε¹ ≅ εⁿ⁺¹`).** The direct sum of the
sphere tangent bundle with the trivial real line bundle is `C^k`-diffeomorphic over
`sphere (0 : E) 1` to the trivial rank-`(n + 1)` bundle with fibre `E`. -/
def sphereTangentProdTrivialDiffeomorph {k : ℕ∞ω} :
    TotalSpace (EuclideanSpace ℝ (Fin n) × ℝ)
      ((fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) ×ᵇ
        Bundle.Trivial (sphere (0 : E) 1) ℝ) ≃ₘ^k⟮(𝓡 n).prod
          𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ), (𝓡 n).prod 𝓘(ℝ, E)⟯
      TotalSpace E (Bundle.Trivial (sphere (0 : E) 1) E) where
  toFun p := ⟨p.proj, (sphereTangentEquiv p.proj p.snd.1 : E) + (p.snd.2 : ℝ) • (p.proj : E)⟩
  invFun q := ⟨q.proj, (sphereTangentProj q.proj q.snd, inner ℝ (q.proj : E) q.snd)⟩
  left_inv p := by
    have h := (sphereTangentProdRealDiffeomorph (E := E) (n := n) (k := k)).left_inv
      (⟨p.proj, p.snd.1⟩, p.snd.2)
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    exact TotalSpace.ext rfl (heq_of_eq (Prod.ext (TotalSpace.mk_inj.mp h1) h2))
  right_inv q := by
    have h := (sphereTangentProdRealDiffeomorph (E := E) (n := n) (k := k)).right_inv
      (q.proj, q.snd)
    exact TotalSpace.ext rfl (heq_of_eq (Prod.mk.inj h).2)
  contMDiff_toFun := by
    have hp1 : ContMDiff ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)) (𝓡 n).tangent k
        (fun p : TotalSpace (EuclideanSpace ℝ (Fin n) × ℝ)
          ((fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) ×ᵇ
            Bundle.Trivial (sphere (0 : E) 1) ℝ) ↦
          (⟨p.proj, p.snd.1⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) :=
      Bundle.Prod.contMDiff_fst
    have hp2 : ContMDiff ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)) 𝓘(ℝ, ℝ) k
        (fun p : TotalSpace (EuclideanSpace ℝ (Fin n) × ℝ)
          ((fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) ×ᵇ
            Bundle.Trivial (sphere (0 : E) 1) ℝ) ↦ (p.snd.2 : ℝ)) :=
      (Bundle.Trivial.contMDiff_mk_iff.mp Bundle.Prod.contMDiff_snd).2
    refine Bundle.Trivial.contMDiff_mk_iff.mpr ⟨Bundle.contMDiff_proj _, ?_⟩
    exact (contMDiff_coe_sphereTangentEquiv.comp hp1).add
      (hp2.smul (contMDiff_coe_sphere.comp (Bundle.contMDiff_proj _)))
  contMDiff_invFun := by
    intro q
    obtain ⟨hq1, hq2⟩ := Bundle.Trivial.contMDiffAt_mk_iff.mp
      (contMDiffAt_id (I := (𝓡 n).prod 𝓘(ℝ, E)) (x := q))
    refine Bundle.contMDiffAt_totalSpace_prod_iff.mpr ⟨?_, ?_⟩
    · exact contMDiff_sphereTangentProj.contMDiffAt.comp q (hq1.prodMk hq2)
    · exact Bundle.Trivial.contMDiffAt_mk_iff.mpr ⟨hq1,
        contDiff_inner.contMDiff.contMDiffAt.comp q
          ((contMDiff_coe_sphere.contMDiffAt.comp q hq1).prodMk_space hq2)⟩

@[simp]
theorem sphereTangentProdTrivialDiffeomorph_apply {k : ℕ∞ω}
    (p : TotalSpace (EuclideanSpace ℝ (Fin n) × ℝ)
      ((fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) ×ᵇ
        Bundle.Trivial (sphere (0 : E) 1) ℝ)) :
    sphereTangentProdTrivialDiffeomorph (k := k) p =
      ⟨p.proj, (sphereTangentEquiv p.proj p.snd.1 : E) + (p.snd.2 : ℝ) • (p.proj : E)⟩ :=
  (rfl)

@[simp]
theorem sphereTangentProdTrivialDiffeomorph_symm_apply {k : ℕ∞ω}
    (q : TotalSpace E (Bundle.Trivial (sphere (0 : E) 1) E)) :
    (sphereTangentProdTrivialDiffeomorph (n := n) (k := k)).symm q =
      ⟨q.proj, (sphereTangentProj (n := n) q.proj q.snd, inner ℝ (q.proj : E) q.snd)⟩ :=
  (rfl)

end TauCeti
