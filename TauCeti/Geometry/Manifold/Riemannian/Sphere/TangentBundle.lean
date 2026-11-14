/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Prod
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Geometry.Manifold.Riemannian.Sphere.Gradient
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame.Orthonormal
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Translate
import TauCeti.Geometry.Manifold.VectorBundle.Trivial

/-!
# Smooth structure of the sphere tangent bundle, radial-normal splitting, and orthonormal frames

For an `(n + 1)`-dimensional real inner product space `E`, `TauCeti.sphereTangentEquiv x`
identifies the native tangent space `TangentSpace (𝓡 n) x` at `x : sphere (0 : E) 1` isometrically
with the orthogonal complement `(ℝ ∙ (x : E))ᗮ`. This file promotes that pointwise identification
to `C^k` manifold and vector-bundle equivalences at every regularity `k : ℕ∞ω`:

* `TauCeti.contMDiff_coe_sphereTangentEquiv` and `TauCeti.contMDiff_sphereTangentProj`: reading a
  tangent vector in `E` and projecting an ambient vector tangentially back to `TangentSpace (𝓡 n) x`
  are `C^k` maps for all `k : ℕ∞ω` (the latter expanded along an orthonormal basis of height
  gradients).
* `TauCeti.contMDiff_sphereTangentEquiv_symm_iff`: lifting an ambient map `w : M → E` satisfying
  `w y ∈ (ℝ ∙ (base y : E))ᗮ` along `(sphereTangentEquiv (base y)).symm` produces a `C^k` map into
  `TangentBundle (𝓡 n) (sphere (0 : E) 1)` if and only if `base` and `w` are `C^k`.
* `TauCeti.hasLocalContMDiffSubbundleFrames_orthogonalSpanSphere` and
  `TauCeti.sphereTangentSubbundleDiffeomorph`: the orthogonal complements `(ℝ ∙ (x : E))ᗮ` form a
  `C^k` subbundle of the trivial bundle `sphere (0 : E) 1 × E`, and `sphereTangentEquiv` gives a
  `C^k` bundle diffeomorphism onto its total space.
* `TauCeti.sphereTangentProdRealDiffeomorph` and `TauCeti.sphereTangentProdTrivialDiffeomorph`:
  adjoining the radial normal line `ℝ ∙ (x : E)` splits the ambient trivial bundle as
  `TSⁿ ⊕ ε¹ ≅ εⁿ⁺¹`, with explicit inverse `u ↦ (sphereTangentProj x u, ⟪x, u⟫)`.
* `TauCeti.sphereTangentDiffeomorphOfOrthonormal`: any global `C^k` orthonormal tangent frame `v`
  on `sphere (0 : E) 1` induces a `C^k` trivialization diffeomorphism
  `TangentBundle (𝓡 n) (sphere (0 : E) 1) ≃ₘ^k sphere (0 : E) 1 × EuclideanSpace ℝ (Fin n)` by
  inner-product coordinates `p ↦ (p.proj, i ↦ ⟪v i p.proj, p.2⟫)` and inverse
  `(x, c) ↦ ⟨x, ∑ i, c i • v i x⟩`.

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

/-! ### Smooth ambient evaluation and tangential projection -/

/-- Orthogonal projection of an ambient vector `u : E` onto the tangent hyperplane `(ℝ ∙ (x : E))ᗮ`
at a point `x` of the unit sphere. -/
def orthogonalProjSphere (x : sphere (0 : E) 1) (u : E) : (ℝ ∙ (x : E))ᗮ :=
  ⟨u - inner ℝ (x : E) u • (x : E), by
    have hx : inner ℝ (x : E) (x : E) = 1 := by
      rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere x, one_pow]
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right,
      real_inner_smul_right, hx, mul_one, sub_self]⟩

@[simp]
theorem coe_orthogonalProjSphere (x : sphere (0 : E) 1) (u : E) :
    (orthogonalProjSphere x u : E) = u - inner ℝ (x : E) u • (x : E) :=
  (rfl)

@[simp]
theorem orthogonalProjSphere_of_mem {x : sphere (0 : E) 1} {u : E}
    (hu : u ∈ (ℝ ∙ (x : E))ᗮ) :
    orthogonalProjSphere x u = ⟨u, hu⟩ := by
  ext
  rw [coe_orthogonalProjSphere, Submodule.mem_orthogonal_singleton_iff_inner_right.mp hu,
    zero_smul, sub_zero]

variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]

/-- Reading a sphere tangent vector in the ambient space `E` through `TauCeti.sphereTangentEquiv`
is `C^k` at every regularity `k : ℕ∞ω`. -/
theorem contMDiff_coe_sphereTangentEquiv {k : ℕ∞ω} :
    ContMDiff (𝓡 n).tangent 𝓘(ℝ, E) k
      (fun p : TangentBundle (𝓡 n) (sphere (0 : E) 1) ↦
        (sphereTangentEquiv p.proj p.2 : E)) := by
  have hω : ContMDiff (𝓡 n).tangent 𝓘(ℝ, E) ω
      (fun p : TangentBundle (𝓡 n) (sphere (0 : E) 1) ↦
        (tangentMap (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) p).2) :=
    (contMDiff_snd_tangentBundle_modelSpace E 𝓘(ℝ, E)).comp
      ((contMDiff_coe_sphere (m := ω)).contMDiff_tangentMap (m := ω) (by simp))
  refine (hω.of_le le_top).congr fun p ↦ ?_
  rw [coe_sphereTangentEquiv_apply]
  rfl

/-- Tangential projection of an ambient vector `u : E` into the native tangent space
`TangentSpace (𝓡 n) x` at `x : sphere (0 : E) 1`. -/
def sphereTangentProj (x : sphere (0 : E) 1) (u : E) : TangentSpace (𝓡 n) x :=
  (sphereTangentEquiv x).symm (orthogonalProjSphere x u)

@[simp]
theorem sphereTangentEquiv_sphereTangentProj (x : sphere (0 : E) 1) (u : E) :
    sphereTangentEquiv (n := n) x (sphereTangentProj (n := n) x u) = orthogonalProjSphere x u :=
  LinearIsometryEquiv.apply_symm_apply _ _

theorem coe_sphereTangentEquiv_sphereTangentProj (x : sphere (0 : E) 1) (u : E) :
    (sphereTangentEquiv (n := n) x (sphereTangentProj (n := n) x u) : E) =
      u - inner ℝ (x : E) u • (x : E) := by
  rw [sphereTangentEquiv_sphereTangentProj, coe_orthogonalProjSphere]

@[simp]
theorem mfderiv_subtypeVal_sphereTangentProj (x : sphere (0 : E) 1) (u : E) :
    mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x (sphereTangentProj (n := n) x u) =
      u - inner ℝ (x : E) u • (x : E) := by
  rw [← coe_sphereTangentEquiv_apply, coe_sphereTangentEquiv_sphereTangentProj]

@[simp]
theorem sphereTangentProj_of_mem_orthogonal {x : sphere (0 : E) 1} {u : E}
    (hu : u ∈ (ℝ ∙ (x : E))ᗮ) :
    sphereTangentProj (n := n) x u = (sphereTangentEquiv (n := n) x).symm ⟨u, hu⟩ := by
  rw [sphereTangentProj, orthogonalProjSphere_of_mem hu]

theorem sphereTangentProj_coe_sphereTangentEquiv (x : sphere (0 : E) 1)
    (v : TangentSpace (𝓡 n) x) :
    sphereTangentProj x (sphereTangentEquiv x v) = v := by
  rw [sphereTangentProj_of_mem_orthogonal (sphereTangentEquiv x v).2, Subtype.coe_eta,
    LinearIsometryEquiv.symm_apply_apply]

@[simp]
theorem sphereTangentProj_mfderiv_subtypeVal (x : sphere (0 : E) 1)
    (v : TangentSpace (𝓡 n) x) :
    sphereTangentProj x (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x v) = v := by
  rw [← coe_sphereTangentEquiv_apply, sphereTangentProj_coe_sphereTangentEquiv]

@[simp]
theorem sphereTangentProj_coe_self (x : sphere (0 : E) 1) :
    sphereTangentProj (n := n) x (x : E) = 0 := by
  apply (sphereTangentEquiv (n := n) x).injective
  apply Subtype.ext
  have hx : inner ℝ (x : E) (x : E) = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere x, one_pow]
  rw [coe_sphereTangentEquiv_sphereTangentProj, map_zero, Submodule.coe_zero, hx, one_smul,
    sub_self]

/-- `TauCeti.sphereTangentProj` expands in any `(n + 1)`-element orthonormal basis `b` of `E` as
`∑ j, ⟪b j, u⟫ • grad (q ↦ ⟪b j, q⟫) x`. -/
private theorem sphereTangentProj_eq_sum_mgradient
    (b : OrthonormalBasis (Fin (n + 1)) ℝ E) (x : sphere (0 : E) 1) (u : E) :
    sphereTangentProj x u =
      ∑ j, inner ℝ (b j) u •
        Manifold.mgradient (𝓡 n) (fun q : sphere (0 : E) 1 ↦ inner ℝ (b j) (q : E)) x := by
  apply (sphereTangentEquiv x).injective
  apply Subtype.ext
  rw [coe_sphereTangentEquiv_sphereTangentProj, map_sum, Submodule.coe_sum]
  have hterm (j : Fin (n + 1)) :
      ((sphereTangentEquiv x (inner ℝ (b j) u •
          Manifold.mgradient (𝓡 n) (fun q : sphere (0 : E) 1 ↦ inner ℝ (b j) (q : E)) x) :
          (ℝ ∙ (x : E))ᗮ) : E) =
        inner ℝ (b j) u • b j - (inner ℝ (b j) u * inner ℝ (b j) (x : E)) • (x : E) := by
    rw [map_smul, Submodule.coe_smul, ← mvfderiv_subtypeVal_sphere_eq_sphereTangentEquiv,
      mvfderiv_coe_mgradient_inner_coe_sphere, smul_sub, smul_smul]
  simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.sum_smul, b.sum_repr' u]
  congr 2
  calc
    inner ℝ (x : E) u
      = ∑ j, inner ℝ (x : E) (b j) * inner ℝ (b j) u := by
          simpa only [RCLike.conj_to_real] using (b.sum_inner_mul_inner (x : E) u).symm
    _ = ∑ j, inner ℝ (b j) u * inner ℝ (b j) (x : E) := by
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [real_inner_comm (x : E) (b j), mul_comm]

/-- Projecting an ambient vector `(x, u) : sphere (0 : E) 1 × E` tangentially into
`TangentBundle (𝓡 n) (sphere (0 : E) 1)` is `C^k` at every regularity `k : ℕ∞ω`. -/
theorem contMDiff_sphereTangentProj {k : ℕ∞ω} :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ, E)) (𝓡 n).tangent k
      (fun p : sphere (0 : E) 1 × E ↦
        (⟨p.1, sphereTangentProj p.1 p.2⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  let b : OrthonormalBasis (Fin (n + 1)) ℝ E :=
    (stdOrthonormalBasis ℝ E).reindex (finCongr Fact.out)
  let g (j : Fin (n + 1)) (x : sphere (0 : E) 1) : TangentSpace (𝓡 n) x :=
    Manifold.mgradient (𝓡 n) (fun q : sphere (0 : E) 1 ↦ inner ℝ (b j) (q : E)) x
  have hg (j : Fin (n + 1)) :
      ContMDiff (𝓡 n) (𝓡 n).tangent k
        (fun x ↦ (⟨x, g j x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) := by
    have hh : ContMDiff (𝓡 n) 𝓘(ℝ) (ω + 1)
        (fun q : sphere (0 : E) 1 ↦ inner ℝ (b j) (q : E)) :=
      (innerSL ℝ (b j)).contDiff.contMDiff.comp contMDiff_coe_sphere
    exact (Manifold.contMDiff_mgradient (n := ω) hh).of_le le_top
  have hsum : ContMDiff ((𝓡 n).prod 𝓘(ℝ, E)) (𝓡 n).tangent k
      (fun p : sphere (0 : E) 1 × E ↦
        (⟨p.1, ∑ j, inner ℝ (b j) p.2 • g j p.1⟩ :
          TangentBundle (𝓡 n) (sphere (0 : E) 1))) :=
    ContMDiff.sum_sectionAlong Finset.univ
      (fun j (p : sphere (0 : E) 1 × E) ↦ inner ℝ (b j) p.2 • g j p.1) contMDiff_fst
      fun j _ ↦ ((innerSL ℝ (b j)).contDiff.contMDiff.comp contMDiff_snd).smul_totalSpace
        ((hg j).comp contMDiff_fst)
  exact hsum.congr fun p ↦
    congrArg (TotalSpace.mk p.1) (sphereTangentProj_eq_sum_mgradient b p.1 p.2)

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
  refine ⟨fun h ↦ ⟨(Bundle.contMDiff_proj _).comp h, ?_⟩, fun ⟨hb, hwm⟩ ↦ ?_⟩
  · refine (contMDiff_coe_sphereTangentEquiv.comp h).congr fun y ↦ ?_
    simp only [Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]
  · refine (contMDiff_sphereTangentProj.comp (hb.prodMk hwm)).congr fun y ↦ ?_
    simp only [Function.comp_apply, sphereTangentProj_of_mem_orthogonal (hw y)]

/-- A section `x ↦ (sphereTangentEquiv x).symm ⟨w x, hw x⟩` of the sphere tangent bundle is `C^k`
if and only if its ambient coordinate map `w : sphere (0 : E) 1 → E` is `C^k`. -/
theorem contMDiff_sphereTangentEquiv_symm_iff {k : ℕ∞ω}
    {w : sphere (0 : E) 1 → E} (hw : ∀ x : sphere (0 : E) 1, w x ∈ (ℝ ∙ (x : E))ᗮ) :
    ContMDiff (𝓡 n) (𝓡 n).tangent k
        (fun x ↦ (⟨x, (sphereTangentEquiv x).symm ⟨w x, hw x⟩⟩ :
          TangentBundle (𝓡 n) (sphere (0 : E) 1))) ↔
      ContMDiff (𝓡 n) 𝓘(ℝ, E) k w :=
  (contMDiff_sphereTangentEquiv_symm_along_iff hw).trans (and_iff_right contMDiff_id)

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
        (⟨q.proj, (q.2 : E)⟩ : TotalSpace E (Bundle.Trivial (sphere (0 : E) 1) E))) :=
    hsub.contMDiff_totalSpace_inclusion.of_le le_top
  have hinv : ContMDiff ((𝓡 n).prod 𝓘(ℝ, Fin n → ℝ)) (𝓡 n).tangent k
      (fun q : TotalSpace (Fin n → ℝ) (fun x : sphere (0 : E) 1 ↦ (ℝ ∙ (x : E))ᗮ) ↦
        TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) q.proj
          ((sphereTangentEquiv (n := n) q.proj).symm.toContinuousLinearEquiv q.2)) :=
    (contMDiff_sphereTangentEquiv_symm_along_iff fun q ↦ q.2.2).mpr
      (Bundle.Trivial.contMDiff_mk_iff.mp hincl)
  exact (bundleDiffeomorph
    (fun x ↦ (sphereTangentEquiv (n := n) x).symm.toContinuousLinearEquiv) hinv).symm

@[simp]
theorem sphereTangentSubbundleDiffeomorph_apply {k : ℕ∞ω}
    (p : TangentBundle (𝓡 n) (sphere (0 : E) 1)) :
    sphereTangentSubbundleDiffeomorph (k := k) p = ⟨p.proj, sphereTangentEquiv p.proj p.2⟩ := by
  simp [sphereTangentSubbundleDiffeomorph]

@[simp]
theorem sphereTangentSubbundleDiffeomorph_symm_apply {k : ℕ∞ω}
    (q : TotalSpace (Fin n → ℝ) (fun x : sphere (0 : E) 1 ↦ (ℝ ∙ (x : E))ᗮ)) :
    (sphereTangentSubbundleDiffeomorph (k := k)).symm q =
      ⟨q.proj, (sphereTangentEquiv q.proj).symm q.2⟩ := by
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
  toFun p := (p.1.proj, (sphereTangentEquiv p.1.proj p.1.2 : E) + p.2 • (p.1.proj : E))
  invFun q := (⟨q.1, sphereTangentProj q.1 q.2⟩, inner ℝ (q.1 : E) q.2)
  left_inv := by
    rintro ⟨⟨x, v⟩, t⟩
    have hx : inner ℝ (x : E) (x : E) = 1 := by
      rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere x, one_pow]
    have horth : inner ℝ (x : E) (sphereTangentEquiv x v : E) = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp (sphereTangentEquiv x v).2
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
          (sphereTangentEquiv p.1.proj p.1.2 : E)) :=
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
      (p.1.proj, (sphereTangentEquiv p.1.proj p.1.2 : E) + p.2 • (p.1.proj : E)) :=
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
  toFun p := ⟨p.proj, (sphereTangentEquiv p.proj p.2.1 : E) + (p.2.2 : ℝ) • (p.proj : E)⟩
  invFun q := ⟨q.proj, (sphereTangentProj q.proj q.2, inner ℝ (q.proj : E) q.2)⟩
  left_inv p := by
    have h := (sphereTangentProdRealDiffeomorph (E := E) (n := n) (k := k)).left_inv
      (⟨p.proj, p.2.1⟩, p.2.2)
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    exact TotalSpace.ext rfl (heq_of_eq (Prod.ext (TotalSpace.mk_inj.mp h1) h2))
  right_inv q := by
    have h := (sphereTangentProdRealDiffeomorph (E := E) (n := n) (k := k)).right_inv
      (q.proj, q.2)
    exact TotalSpace.ext rfl (heq_of_eq (Prod.mk.inj h).2)
  contMDiff_toFun := by
    have hp1 : ContMDiff ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)) (𝓡 n).tangent k
        (fun p : TotalSpace (EuclideanSpace ℝ (Fin n) × ℝ)
          ((fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) ×ᵇ
            Bundle.Trivial (sphere (0 : E) 1) ℝ) ↦
          (⟨p.proj, p.2.1⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) :=
      Bundle.Prod.contMDiff_fst
    have hp2 : ContMDiff ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)) 𝓘(ℝ, ℝ) k
        (fun p : TotalSpace (EuclideanSpace ℝ (Fin n) × ℝ)
          ((fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) ×ᵇ
            Bundle.Trivial (sphere (0 : E) 1) ℝ) ↦ (p.2.2 : ℝ)) :=
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
      ⟨p.proj, (sphereTangentEquiv p.proj p.2.1 : E) + (p.2.2 : ℝ) • (p.proj : E)⟩ :=
  (rfl)

@[simp]
theorem sphereTangentProdTrivialDiffeomorph_symm_apply {k : ℕ∞ω}
    (q : TotalSpace E (Bundle.Trivial (sphere (0 : E) 1) E)) :
    (sphereTangentProdTrivialDiffeomorph (n := n) (k := k)).symm q =
      ⟨q.proj, (sphereTangentProj (n := n) q.proj q.2, inner ℝ (q.proj : E) q.2)⟩ :=
  (rfl)

end TauCeti

/-! ### Global tangent trivialization from a smooth orthonormal frame -/

namespace Orthonormal

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- Pointwise orthonormal basis of `TangentSpace (𝓡 n) x` associated to an `n`-element orthonormal
family in `TangentSpace (𝓡 n) x`. -/
def sphereTangentOrthonormalBasis {x : sphere (0 : E) 1}
    {v : Fin n → TangentSpace (𝓡 n) x} (hv : Orthonormal ℝ v) :
    OrthonormalBasis (Fin n) ℝ (TangentSpace (𝓡 n) x) := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    (sphereTangentEquiv x).symm.toLinearEquiv.finiteDimensional
  have hfin : finrank ℝ (Submodule.span ℝ (Set.range v)) = finrank ℝ (TangentSpace (𝓡 n) x) := by
    rw [finrank_span_eq_card hv.linearIndependent, Fintype.card_fin,
      (sphereTangentEquiv x).toLinearEquiv.finrank_eq,
      Submodule.finrank_orthogonal_span_singleton (n := n) (ne_zero_of_mem_unit_sphere x)]
  exact OrthonormalBasis.mk hv (Submodule.eq_top_of_finrank_eq hfin).ge

@[simp]
theorem sphereTangentOrthonormalBasis_apply {x : sphere (0 : E) 1}
    {v : Fin n → TangentSpace (𝓡 n) x} (hv : Orthonormal ℝ v) (i : Fin n) :
    hv.sphereTangentOrthonormalBasis i = v i := by
  simp [sphereTangentOrthonormalBasis]

end Orthonormal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- A global `C^k` family of `n` pointwise orthonormal vector fields on `sphere (0 : E) 1` forms a
`C^k` global frame (`IsLocalFrameOn` on `Set.univ`). -/
theorem isLocalFrameOn_univ_sphere_of_orthonormal {k : ℕ∞ω}
    {v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x}
    (horth : ∀ x, Orthonormal ℝ fun i ↦ v i x)
    (hv : ∀ i, ContMDiff (𝓡 n) (𝓡 n).tangent k
      (fun x ↦ (⟨x, v i x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1)))) :
    IsLocalFrameOn (𝓡 n) (EuclideanSpace ℝ (Fin n)) k v univ := by
  refine ⟨fun {x} _ ↦ (horth x).linearIndependent, fun {x} _ ↦ ?_, fun i ↦ (hv i).contMDiffOn⟩
  have hcoe : ⇑(horth x).sphereTangentOrthonormalBasis = fun i ↦ v i x :=
    funext (horth x).sphereTangentOrthonormalBasis_apply
  rw [← (horth x).sphereTangentOrthonormalBasis.toBasis.span_eq, OrthonormalBasis.coe_toBasis,
    hcoe]

/-- The frame coefficient functionals of a global orthonormal frame on `sphere (0 : E) 1` are its
round-metric inner products. -/
@[simp]
theorem coeff_isLocalFrameOn_univ_sphere_of_orthonormal {k : ℕ∞ω}
    {v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x}
    (horth : ∀ x, Orthonormal ℝ fun i ↦ v i x)
    (hv : ∀ i, ContMDiff (𝓡 n) (𝓡 n).tangent k
      (fun x ↦ (⟨x, v i x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))))
    (i : Fin n) (x : sphere (0 : E) 1) (w : TangentSpace (𝓡 n) x) :
    (isLocalFrameOn_univ_sphere_of_orthonormal horth hv).coeff i x w = inner ℝ (v i x) w :=
  (isLocalFrameOn_univ_sphere_of_orthonormal horth hv).coeff_eq_inner (mem_univ x) (horth x) i w

/-- **Global tangent-bundle trivialization by inner-product coordinates.** Any `n` pointwise
orthonormal `C^k` tangent vector fields `v` on `sphere (0 : E) 1` trivialize
`TangentBundle (𝓡 n) (sphere (0 : E) 1)` by a global `C^k` diffeomorphism sending `⟨x, w⟩` to
`(x, i ↦ ⟪v i x, w⟫)` and `(x, c)` back to `⟨x, ∑ i, c i • v i x⟩`. -/
def sphereTangentDiffeomorphOfOrthonormal {k : ℕ∞ω}
    {v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x}
    (horth : ∀ x, Orthonormal ℝ fun i ↦ v i x)
    (hv : ∀ i, ContMDiff (𝓡 n) (𝓡 n).tangent k
      (fun x ↦ (⟨x, v i x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1)))) :
    TangentBundle (𝓡 n) (sphere (0 : E) 1) ≃ₘ^k⟮(𝓡 n).tangent,
      (𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯
      (sphere (0 : E) 1 × EuclideanSpace ℝ (Fin n)) where
  toFun p := (p.proj, WithLp.toLp 2 fun i ↦ inner ℝ (v i p.proj) p.2)
  invFun q := ⟨q.1, ∑ i, q.2.ofLp i • v i q.1⟩
  left_inv p := by
    refine TotalSpace.ext rfl (heq_of_eq ?_)
    have hb := (horth p.proj).sphereTangentOrthonormalBasis.sum_repr' p.2
    simpa only [WithLp.ofLp_toLp, Orthonormal.sphereTangentOrthonormalBasis_apply] using hb
  right_inv := by
    rintro ⟨x, c⟩
    refine Prod.ext rfl (PiLp.ext fun i ↦ ?_)
    simpa only [WithLp.ofLp_toLp] using (horth x).inner_right_fintype c.ofLp i
  contMDiff_toFun := by
    let : IsContMDiffRiemannianBundle (𝓡 n) k (EuclideanSpace ℝ (Fin n))
        (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
      IsContMDiffRiemannianBundle.of_le le_top
    have hcoord : ContMDiff (𝓡 n).tangent 𝓘(ℝ, Fin n → ℝ) k
        (fun p : TangentBundle (𝓡 n) (sphere (0 : E) 1) ↦
          fun i : Fin n ↦ inner ℝ (v i p.proj) p.2) :=
      contMDiff_pi_module_iff.mpr fun i ↦
        ((hv i).comp (Bundle.contMDiff_proj _)).inner_bundle contMDiff_id
    have htoLp : ContDiff ℝ k (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) :=
      (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toContinuousLinearEquiv.contDiff
    exact (Bundle.contMDiff_proj _).prodMk (htoLp.contMDiff.comp hcoord)
  contMDiff_invFun :=
    ContMDiff.sum_sectionAlong Finset.univ
      (fun i (q : sphere (0 : E) 1 × EuclideanSpace ℝ (Fin n)) ↦ q.2.ofLp i • v i q.1)
      contMDiff_fst fun i _ ↦
        ((PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin n ↦ ℝ) i).contDiff.contMDiff.comp
          contMDiff_snd).smul_totalSpace ((hv i).comp contMDiff_fst)

@[simp]
theorem sphereTangentDiffeomorphOfOrthonormal_apply_fst {k : ℕ∞ω}
    {v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x}
    (horth : ∀ x, Orthonormal ℝ fun i ↦ v i x)
    (hv : ∀ i, ContMDiff (𝓡 n) (𝓡 n).tangent k
      (fun x ↦ (⟨x, v i x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))))
    (p : TangentBundle (𝓡 n) (sphere (0 : E) 1)) :
    (sphereTangentDiffeomorphOfOrthonormal horth hv p).1 = p.proj :=
  (rfl)

@[simp]
theorem sphereTangentDiffeomorphOfOrthonormal_apply_snd {k : ℕ∞ω}
    {v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x}
    (horth : ∀ x, Orthonormal ℝ fun i ↦ v i x)
    (hv : ∀ i, ContMDiff (𝓡 n) (𝓡 n).tangent k
      (fun x ↦ (⟨x, v i x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))))
    (p : TangentBundle (𝓡 n) (sphere (0 : E) 1)) (i : Fin n) :
    ((sphereTangentDiffeomorphOfOrthonormal horth hv p).2).ofLp i = inner ℝ (v i p.proj) p.2 :=
  (rfl)

@[simp]
theorem sphereTangentDiffeomorphOfOrthonormal_symm_apply {k : ℕ∞ω}
    {v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x}
    (horth : ∀ x, Orthonormal ℝ fun i ↦ v i x)
    (hv : ∀ i, ContMDiff (𝓡 n) (𝓡 n).tangent k
      (fun x ↦ (⟨x, v i x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))))
    (q : sphere (0 : E) 1 × EuclideanSpace ℝ (Fin n)) :
    (sphereTangentDiffeomorphOfOrthonormal horth hv).symm q =
      ⟨q.1, ∑ i, q.2.ofLp i • v i q.1⟩ :=
  (rfl)

/-- The inner-product coordinate trivialization preserves fibre norms. -/
@[simp]
theorem norm_sphereTangentDiffeomorphOfOrthonormal_snd {k : ℕ∞ω}
    {v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x}
    (horth : ∀ x, Orthonormal ℝ fun i ↦ v i x)
    (hv : ∀ i, ContMDiff (𝓡 n) (𝓡 n).tangent k
      (fun x ↦ (⟨x, v i x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))))
    (p : TangentBundle (𝓡 n) (sphere (0 : E) 1)) :
    ‖(sphereTangentDiffeomorphOfOrthonormal horth hv p).2‖ = ‖p.2‖ := by
  have hrepr : (sphereTangentDiffeomorphOfOrthonormal horth hv p).2 =
      (horth p.proj).sphereTangentOrthonormalBasis.repr p.2 :=
    PiLp.ext fun i ↦ by
      rw [sphereTangentDiffeomorphOfOrthonormal_apply_snd, OrthonormalBasis.repr_apply_apply,
        Orthonormal.sphereTangentOrthonormalBasis_apply]
  rw [hrepr, LinearIsometryEquiv.norm_map]

end TauCeti
