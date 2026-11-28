/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Prod
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
import TauCeti.Geometry.Manifold.ContMDiff.InnerProductSpace
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.Riemannian.Sphere.Gradient
import TauCeti.Geometry.Manifold.VectorBundle.Hom.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.OrthogonalComplement

/-!
# Smooth structure of the sphere tangent bundle and radial-normal splitting

For an `(n + 1)`-dimensional real inner product space `E`, `TauCeti.sphereTangentEquiv x`
identifies the native tangent space `TangentSpace (𝓡 n) x` at `x : sphere (0 : E) 1` isometrically
with the orthogonal complement `(ℝ ∙ (x : E))ᗮ`, and
`TauCeti.sphereTangentProj x : E →L[ℝ] TangentSpace (𝓡 n) x` (in `Sphere/Basic.lean`) is the
tangential projection: it restricts to `(TauCeti.sphereTangentEquiv x).symm` on `(ℝ ∙ (x : E))ᗮ` and
kills `x`. Building on `TauCeti.contMDiff_coe_sphereTangentEquiv` (in `Sphere/Basic.lean`),
`TauCeti.contMDiff_sphereTangentEquiv_symm` (in `Sphere/Gradient.lean`), and
`TauCeti.hasLocalContMDiffSubbundleFrames_orthogonalSpan` (in
`VectorBundle/Riemannian/OrthogonalComplement.lean`), this file promotes those pointwise
identifications to `C^k` manifold and vector-bundle equivalences at every regularity `k : ℕ∞ω`:

* `TauCeti.contMDiff_sphereTangentProj`: for any `C^k` base map `f : M → sphere (0 : E) 1` and
  `C^k` ambient map `u : M → E`, the tangential projection
  `z ↦ ⟨f z, sphereTangentProj (f z) (u z)⟩` into `TangentBundle (𝓡 n) (sphere (0 : E) 1)` is
  `C^k` for all `k : ℕ∞ω`.
* `TauCeti.hasLocalContMDiffSubbundleFrames_orthogonalSpanSphere` and
  `TauCeti.sphereTangentSubbundleDiffeomorph`: the orthogonal complements `(ℝ ∙ (x : E))ᗮ` form a
  `C^k` subbundle of `Bundle.Trivial (sphere (0 : E) 1) E`, and `sphereTangentEquiv` gives a `C^k`
  bundle diffeomorphism onto its total space.
* `TauCeti.sphereTangentProdRealEquiv`, `TauCeti.sphereTangentProdTrivialDiffeomorph`, and
  `TauCeti.sphereTangentProdRealDiffeomorph`: adjoining the radial normal line `ℝ ∙ (x : E)`
  splits the ambient trivial bundle as `TSⁿ ⊕ ε¹ ≅ εⁿ⁺¹`, with explicit inverse
  `u ↦ (sphereTangentProj x u, ⟪x, u⟫)`.

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

/-! ### Smooth tangential projection -/

/-- For any `C^k` base map `f : M → sphere (0 : E) 1` and `C^k` ambient map `u : M → E`, the
tangential projection `z ↦ ⟨f z, sphereTangentProj (f z) (u z)⟩` into
`TangentBundle (𝓡 n) (sphere (0 : E) 1)` is `C^k` at every regularity `k : ℕ∞ω`. -/
theorem contMDiff_sphereTangentProj {E' H' M : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} [TopologicalSpace M] [ChartedSpace H' M]
    {k : ℕ∞ω} {f : M → sphere (0 : E) 1} {u : M → E}
    (hf : ContMDiff J (𝓡 n) k f) (hu : ContMDiff J 𝓘(ℝ, E) k u) :
    ContMDiff J (𝓡 n).tangent k
      (fun z ↦ (⟨f z, sphereTangentProj (f z) (u z)⟩ :
        TangentBundle (𝓡 n) (sphere (0 : E) 1))) := by
  have hu' : ContMDiff J 𝓘(ℝ, E) k
      (fun z ↦ ((ℝ ∙ (f z : E))ᗮ.orthogonalProjectionOnto (u z) : E)) :=
    (contMDiff_starProjection_orthogonal_span_singleton
      (contMDiff_coe_sphere.comp hf) hu
      fun z ↦ ne_zero_of_mem_unit_sphere (f z)).congr fun z ↦
        (Submodule.coe_orthogonalProjectionOnto_apply _ _).symm
  have h := contMDiff_sphereTangentEquiv_symm hf hu' fun z ↦
    ((ℝ ∙ (f z : E))ᗮ.orthogonalProjectionOnto (u z)).property
  exact h.congr fun z ↦ congrArg (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (f z))
    (by simp only [sphereTangentProj_apply, Subtype.coe_eta])

/-! ### The smooth subbundle `(ℝ ∙ x)ᗮ` and bundle equivalence with `TSⁿ` -/

/-- The tangent hyperplanes `(ℝ ∙ (x : E))ᗮ` admit `C^k` local subbundle frames of rank `n` inside
the ambient trivial bundle `Bundle.Trivial (sphere (0 : E) 1) E` at every regularity `k : ℕ∞ω`. -/
theorem hasLocalContMDiffSubbundleFrames_orthogonalSpanSphere {k : ℕ∞ω} :
    HasLocalContMDiffSubbundleFrames (𝓡 n) k E (Fin n)
      (fun x : sphere (0 : E) 1 ↦
        ((ℝ ∙ (x : E))ᗮ : Submodule ℝ (Bundle.Trivial (sphere (0 : E) 1) E x))) :=
  hasLocalContMDiffSubbundleFrames_orthogonalSpan contMDiff_coe_sphere ne_zero_of_mem_unit_sphere

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

private theorem contMDiff_sphereTangentSubbundle_symm {k : ℕ∞ω} :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ, Fin n → ℝ)) (𝓡 n).tangent k
      (fun q : TotalSpace (Fin n → ℝ) (fun x : sphere (0 : E) 1 ↦ (ℝ ∙ (x : E))ᗮ) ↦
        TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) q.proj
          ((sphereTangentEquiv (n := n) q.proj).symm.toContinuousLinearEquiv q.snd)) := by
  have hincl := Bundle.Trivial.contMDiff_mk_iff.mp
    ((hasLocalContMDiffSubbundleFrames_orthogonalSpanSphere (E := E) (n := n)
      (k := ω)).contMDiff_totalSpace_inclusion.of_le (le_top : k ≤ ω))
  have h := contMDiff_sphereTangentEquiv_symm hincl.1 hincl.2 fun q ↦ q.snd.property
  exact h.congr fun q ↦ congrArg (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) q.proj)
    (by simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv, Subtype.coe_eta])

/-- **Smooth isomorphism between `TSⁿ` and the orthogonal-complement subbundle `x^⊥`.**
Differentiating the ambient inclusion identifies `TangentBundle (𝓡 n) (sphere (0 : E) 1)` with the
total space of the subbundle `x ↦ (ℝ ∙ (x : E))ᗮ` by a `C^k` bundle diffeomorphism at every
regularity `k : ℕ∞ω`, with inverse `(sphereTangentEquiv x).symm`. -/
def sphereTangentSubbundleDiffeomorph {k : ℕ∞ω} :
    TangentBundle (𝓡 n) (sphere (0 : E) 1) ≃ₘ^k⟮(𝓡 n).tangent, (𝓡 n).prod 𝓘(ℝ, Fin n → ℝ)⟯
      TotalSpace (Fin n → ℝ) (fun x : sphere (0 : E) 1 ↦ (ℝ ∙ (x : E))ᗮ) :=
  (bundleDiffeomorph
    (fun x ↦ (sphereTangentEquiv (n := n) x).symm.toContinuousLinearEquiv)
    (contMDiff_sphereTangentSubbundle_symm (E := E) (n := n) (k := k))).symm

/-- Forward formula for `TauCeti.sphereTangentSubbundleDiffeomorph`. -/
@[simp]
theorem sphereTangentSubbundleDiffeomorph_apply {k : ℕ∞ω}
    (p : TangentBundle (𝓡 n) (sphere (0 : E) 1)) :
    sphereTangentSubbundleDiffeomorph (k := k) p = ⟨p.proj, sphereTangentEquiv p.proj p.snd⟩ := by
  rw [sphereTangentSubbundleDiffeomorph, bundleDiffeomorph_symm_apply]
  simp

/-- Inverse formula for `TauCeti.sphereTangentSubbundleDiffeomorph`. -/
@[simp]
theorem sphereTangentSubbundleDiffeomorph_symm_apply {k : ℕ∞ω}
    (q : TotalSpace (Fin n → ℝ) (fun x : sphere (0 : E) 1 ↦ (ℝ ∙ (x : E))ᗮ)) :
    (sphereTangentSubbundleDiffeomorph (k := k)).symm q =
      ⟨q.proj, (sphereTangentEquiv q.proj).symm q.snd⟩ := by
  rw [sphereTangentSubbundleDiffeomorph, Diffeomorph.symm_symm, bundleDiffeomorph_apply]
  simp

/-! ### Radial-normal splitting `TSⁿ ⊕ ε¹ ≅ εⁿ⁺¹` -/

/-- **Fibrewise radial-normal linear equivalence.** At `x : sphere (0 : E) 1`, adjoining the
radial line `ℝ ∙ (x : E)` to `TangentSpace (𝓡 n) x` via `TauCeti.sphereTangentEquiv` and
`LinearIsometryEquiv.toSpanUnitSingleton` gives a continuous linear equivalence
`(TangentSpace (𝓡 n) x × ℝ) ≃L[ℝ] E`, mapping `p ↦ sphereTangentEquiv x p.1 + p.2 • x`. -/
def sphereTangentProdRealEquiv (x : sphere (0 : E) 1) :
    (TangentSpace (𝓡 n) x × ℝ) ≃L[ℝ] E :=
  (((sphereTangentEquiv x).toLinearEquiv.prodCongr
      (LinearIsometryEquiv.toSpanUnitSingleton (x : E)
        (norm_eq_of_mem_sphere x)).toLinearEquiv).trans
    (Submodule.prodEquivOfIsCompl (ℝ ∙ (x : E))ᗮ (ℝ ∙ (x : E))
      (Submodule.isCompl_orthogonal (ℝ ∙ (x : E))).symm)).toContinuousLinearEquiv

/-- Forward formula for `TauCeti.sphereTangentProdRealEquiv`. -/
@[simp]
theorem sphereTangentProdRealEquiv_apply (x : sphere (0 : E) 1)
    (p : TangentSpace (𝓡 n) x × ℝ) :
    sphereTangentProdRealEquiv x p = (sphereTangentEquiv x p.1 : E) + p.2 • (x : E) := by
  simp [sphereTangentProdRealEquiv, Submodule.coe_prodEquivOfIsCompl',
    LinearIsometryEquiv.toSpanUnitSingleton_apply]

/-- Inverse formula for `TauCeti.sphereTangentProdRealEquiv`, recovering the tangential
projection and radial inner product. -/
@[simp]
theorem sphereTangentProdRealEquiv_symm_apply (x : sphere (0 : E) 1) (u : E) :
    (sphereTangentProdRealEquiv (n := n) x).symm u =
      (sphereTangentProj (n := n) x u, inner ℝ (x : E) u) := by
  apply (sphereTangentProdRealEquiv (n := n) x).injective
  simp

/-- **Whitney-sum form of the radial-normal splitting (`TSⁿ ⊕ ε¹ ≅ εⁿ⁺¹`).** The direct sum of the
sphere tangent bundle with the trivial real line bundle is `C^k`-diffeomorphic over
`sphere (0 : E) 1` to the trivial rank-`(n + 1)` bundle with fibre `E`. -/
def sphereTangentProdTrivialDiffeomorph {k : ℕ∞ω} :
    TotalSpace (EuclideanSpace ℝ (Fin n) × ℝ)
      ((fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) ×ᵇ
        Bundle.Trivial (sphere (0 : E) 1) ℝ) ≃ₘ^k⟮(𝓡 n).prod
          𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ), (𝓡 n).prod 𝓘(ℝ, E)⟯
      TotalSpace E (Bundle.Trivial (sphere (0 : E) 1) E) :=
  bundleDiffeomorph (fun x ↦ sphereTangentProdRealEquiv (E := E) (n := n) x) <| by
    have h : ContMDiff
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)) 𝓘(ℝ, E) k
        (fun p : TotalSpace (EuclideanSpace ℝ (Fin n) × ℝ)
            ((fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) ×ᵇ
              Bundle.Trivial (sphere (0 : E) 1) ℝ) ↦
          (sphereTangentEquiv p.proj p.snd.1 : E) + (p.snd.2 : ℝ) • (p.proj : E)) :=
      (contMDiff_coe_sphereTangentEquiv.comp Bundle.Prod.contMDiff_fst).add
        ((Bundle.Trivial.contMDiff_mk_iff.mp Bundle.Prod.contMDiff_snd).2.smul
          (contMDiff_coe_sphere.comp (Bundle.contMDiff_proj _)))
    exact (Bundle.Trivial.contMDiff_mk_iff.mpr ⟨Bundle.contMDiff_proj _, h⟩).congr fun p ↦
      congrArg (TotalSpace.mk' E p.proj) (sphereTangentProdRealEquiv_apply p.proj p.snd)

/-- Forward formula for `TauCeti.sphereTangentProdTrivialDiffeomorph`. -/
@[simp]
theorem sphereTangentProdTrivialDiffeomorph_apply {k : ℕ∞ω}
    (p : TotalSpace (EuclideanSpace ℝ (Fin n) × ℝ)
      ((fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) ×ᵇ
        Bundle.Trivial (sphere (0 : E) 1) ℝ)) :
    sphereTangentProdTrivialDiffeomorph (k := k) p =
      ⟨p.proj, (sphereTangentEquiv p.proj p.snd.1 : E) + (p.snd.2 : ℝ) • (p.proj : E)⟩ := by
  simp [sphereTangentProdTrivialDiffeomorph]

/-- Inverse formula for `TauCeti.sphereTangentProdTrivialDiffeomorph`. -/
@[simp]
theorem sphereTangentProdTrivialDiffeomorph_symm_apply {k : ℕ∞ω}
    (q : TotalSpace E (Bundle.Trivial (sphere (0 : E) 1) E)) :
    (sphereTangentProdTrivialDiffeomorph (n := n) (k := k)).symm q =
      ⟨q.proj, (sphereTangentProj (n := n) q.proj q.snd, inner ℝ (q.proj : E) q.snd)⟩ := by
  simp [sphereTangentProdTrivialDiffeomorph]

/-- **Radial-normal splitting of the sphere tangent bundle.** Adjoining the radial normal coordinate
`t` sends `(⟨x, v⟩, t) : TangentBundle (𝓡 n) (sphere (0 : E) 1) × ℝ` to
`(x, sphereTangentEquiv x v + t • x) : sphere (0 : E) 1 × E`, a `C^k` diffeomorphism with inverse
`(x, u) ↦ (⟨x, sphereTangentProj x u⟩, ⟪x, u⟫)`. -/
def sphereTangentProdRealDiffeomorph {k : ℕ∞ω} :
    (TangentBundle (𝓡 n) (sphere (0 : E) 1) × ℝ) ≃ₘ^k⟮(𝓡 n).tangent.prod 𝓘(ℝ, ℝ),
      (𝓡 n).prod 𝓘(ℝ, E)⟯ (sphere (0 : E) 1 × E) :=
  ((Bundle.Prod.diffeomorphProdTrivial (𝓡 n) ℝ
      (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) k).symm.trans
    (sphereTangentProdTrivialDiffeomorph (E := E) (n := n) (k := k))).trans
    (Bundle.Trivial.diffeomorphProd (𝓡 n) (sphere (0 : E) 1) E k)

/-- Forward formula for `TauCeti.sphereTangentProdRealDiffeomorph`. -/
@[simp]
theorem sphereTangentProdRealDiffeomorph_apply {k : ℕ∞ω}
    (p : TangentBundle (𝓡 n) (sphere (0 : E) 1) × ℝ) :
    sphereTangentProdRealDiffeomorph (k := k) p =
      (p.1.proj, (sphereTangentEquiv p.1.proj p.1.snd : E) + p.2 • (p.1.proj : E)) := by
  simp [sphereTangentProdRealDiffeomorph]

/-- Inverse formula for `TauCeti.sphereTangentProdRealDiffeomorph`. -/
@[simp]
theorem sphereTangentProdRealDiffeomorph_symm_apply {k : ℕ∞ω} (q : sphere (0 : E) 1 × E) :
    (sphereTangentProdRealDiffeomorph (n := n) (k := k)).symm q =
      (⟨q.1, sphereTangentProj (n := n) q.1 q.2⟩, inner ℝ (q.1 : E) q.2) := by
  apply (sphereTangentProdRealDiffeomorph (n := n) (k := k)).injective
  simp

end TauCeti
