/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Submersion
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.Manifold.Submersion.Basic
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph

/-!
# Recognizing diffeomorphisms and maximal atlases through submersions

A bijection commuting with two surjective `C^n` submersions out of a common boundaryless manifold
is a `C^m` diffeomorphism for every `m ≤ n` (`Equiv.diffeomorphOfSubmersions`). Unlike the dual
criterion for immersions (`Homeomorph.diffeomorphOfImmersions`), no continuity assumption on the
bijection or its inverse is needed: smoothness in both directions descends along local sections of
the two submersions (`Manifold.IsSubmersion.contMDiff_comp_iff`).

For a surjective `C^n` submersion `f : M → N`, the codomain charts of the submersion normal form
cover `N` and lie in its `C^n` maximal atlas, so `N` is automatically a `C^n` manifold
(`Manifold.IsSubmersion.isManifold`). When `M` has no boundary, an open partial homeomorphism `φ`
from `N` to its model space belongs to the `C^n` maximal atlas of `N` if and only if `φ ∘ f` is a
`C^n` submersion at every point of `f ⁻¹' φ.source` (`Manifold.IsSubmersion.mem_maximalAtlas_iff`).
Since that condition does not refer to the atlas on `N`, a surjective map from a boundaryless
manifold can be a `C^n` submersion for at most one `C^n` maximal atlas on the target
(`Manifold.IsSubmersion.maximalAtlas_eq`).

## Main declarations

* `Equiv.diffeomorphOfSubmersions`: a bijection commuting with two surjective `C^n` submersions out
  of a boundaryless manifold is a `C^m` diffeomorphism for `m ≤ n`.
* `ChartedSpace.exists_diffeomorph_apply_eq_self_of_isSubmersion`: two atlases on the same
  topological space for which a common surjection from a boundaryless manifold is a `C^n`
  submersion are diffeomorphic by the identity.
* `Manifold.IsSubmersion.isManifold`: the target of a surjective `C^n` submersion is a `C^n`
  manifold.
* `Manifold.IsSubmersion.mem_maximalAtlas_iff`: charts in the maximal atlas of a submersion target
  are detected by precomposing with the submersion.
* `Manifold.IsSubmersion.maximalAtlas_eq`: two charted-space structures on the same topological
  space with a common model making a surjection from a boundaryless manifold a `C^n` submersion
  have the same `C^n` maximal atlas.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Theorem 4.31
  (uniqueness of quotient manifold structures).
-/

public section

open Function Set Topology
open scoped ContDiff Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F V H G W : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [TopologicalSpace W]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G} {K : ModelWithCorners 𝕜 V W}
  {M N P : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [cN : ChartedSpace G N] [TopologicalSpace P] [cP : ChartedSpace W P]
  {m n : ℕ∞ω} {f : M → N} {g : M → P}

namespace Equiv

/-- **Uniqueness of quotient manifold structures up to diffeomorphism.** A bijection `e : N ≃ P`
satisfying `e ∘ f = g` for two `C^n` submersions `f : M → N` and `g : M → P` out of a boundaryless
manifold, with `f` surjective, is a `C^m` diffeomorphism for every `m ≤ n`. Neither continuity of
`e` nor surjectivity of `g` needs to be assumed separately, as `g = e ∘ f` is surjective and
smoothness descends along local sections of `f` and `g`. -/
noncomputable def diffeomorphOfSubmersions [I.Boundaryless] (e : N ≃ P)
    (hf : Manifold.IsSubmersion I J n f) (hsurj : Surjective f) (hm : m ≤ n)
    (hg : Manifold.IsSubmersion I K n g) (h : e ∘ f = g) : N ≃ₘ^m⟮J, K⟯ P where
  toEquiv := e
  contMDiff_toFun := (hf.contMDiff_comp_iff hsurj hm).1 (h.symm ▸ hg.contMDiff.of_le hm)
  contMDiff_invFun := by
    have hsurj' : Surjective g := h ▸ e.surjective.comp hsurj
    have h' : e.symm ∘ g = f := funext fun x ↦ e.symm_apply_eq.2 (congrFun h x).symm
    exact (hg.contMDiff_comp_iff hsurj' hm).1 (h'.symm ▸ hf.contMDiff.of_le hm)

/-- Upgrading a bijection through submersions preserves the underlying equivalence. -/
@[simp]
theorem diffeomorphOfSubmersions_toEquiv [I.Boundaryless] (e : N ≃ P)
    (hf : Manifold.IsSubmersion I J n f) (hsurj : Surjective f) (hm : m ≤ n)
    (hg : Manifold.IsSubmersion I K n g) (h : e ∘ f = g) :
    (e.diffeomorphOfSubmersions hf hsurj hm hg h).toEquiv = e :=
  (rfl)

/-- `Equiv.diffeomorphOfSubmersions` evaluates as the original bijection. -/
@[simp]
theorem diffeomorphOfSubmersions_apply [I.Boundaryless] (e : N ≃ P)
    (hf : Manifold.IsSubmersion I J n f) (hsurj : Surjective f) (hm : m ≤ n)
    (hg : Manifold.IsSubmersion I K n g) (h : e ∘ f = g) (y : N) :
    e.diffeomorphOfSubmersions hf hsurj hm hg h y = e y :=
  (rfl)

/-- The inverse of `Equiv.diffeomorphOfSubmersions` evaluates as the inverse bijection. -/
@[simp]
theorem diffeomorphOfSubmersions_symm_apply [I.Boundaryless] (e : N ≃ P)
    (hf : Manifold.IsSubmersion I J n f) (hsurj : Surjective f) (hm : m ≤ n)
    (hg : Manifold.IsSubmersion I K n g) (h : e ∘ f = g) (z : P) :
    (e.diffeomorphOfSubmersions hf hsurj hm hg h).symm z = e.symm z :=
  (rfl)

/-- The underlying function of `Equiv.diffeomorphOfSubmersions` is `e`. -/
theorem coe_diffeomorphOfSubmersions [I.Boundaryless] (e : N ≃ P)
    (hf : Manifold.IsSubmersion I J n f) (hsurj : Surjective f) (hm : m ≤ n)
    (hg : Manifold.IsSubmersion I K n g) (h : e ∘ f = g) :
    ⇑(e.diffeomorphOfSubmersions hf hsurj hm hg h) = e :=
  (rfl)

/-- The underlying function of the inverse of `Equiv.diffeomorphOfSubmersions` is `e.symm`. -/
theorem coe_diffeomorphOfSubmersions_symm [I.Boundaryless] (e : N ≃ P)
    (hf : Manifold.IsSubmersion I J n f) (hsurj : Surjective f) (hm : m ≤ n)
    (hg : Manifold.IsSubmersion I K n g) (h : e ∘ f = g) :
    ⇑(e.diffeomorphOfSubmersions hf hsurj hm hg h).symm = e.symm :=
  (rfl)

end Equiv

namespace ChartedSpace

omit cN in
/-- Two atlases on the same topological space, possibly modeled on different spaces, are `C^m`
diffeomorphic by the identity for `m ≤ n` whenever the same surjection out of a boundaryless
manifold is a `C^n` submersion for both atlases. -/
theorem exists_diffeomorph_apply_eq_self_of_isSubmersion [I.Boundaryless]
    (a : ChartedSpace G N) (b : ChartedSpace W N)
    (ha : letI := a; Manifold.IsSubmersion I J n f)
    (hb : letI := b; Manifold.IsSubmersion I K n f) (hsurj : Surjective f) (hm : m ≤ n) :
    letI := a
    letI := b
    ∃ e : N ≃ₘ^m⟮J, K⟯ N, ∀ y, e y = y :=
  ⟨Equiv.diffeomorphOfSubmersions (cN := a) (cP := b) (Equiv.refl N) ha hsurj hm hb rfl,
    fun _ ↦ rfl⟩

end ChartedSpace

namespace Manifold.IsSubmersion

/-- **Smoothness of a submersion target.** The target of a surjective `C^n` submersion is a `C^n`
manifold: the codomain charts supplied by the submersion normal form belong to the `C^n` maximal
atlas and cover the target, so every pair of atlas charts is locally compatible through them. -/
theorem isManifold (hf : IsSubmersion I J n f) (hsurj : Surjective f) : IsManifold J n N where
  compatible {e e'} he he' := by
    refine (contDiffGroupoid n J).locality fun u hu ↦ ?_
    obtain ⟨x, hx⟩ := hsurj (e.symm u)
    have hsub := (hf.isSubmersionAt x).isSubmersionAtOfComplement_complement
    let ψ := hsub.codChart
    have hψ : ψ ∈ (contDiffGroupoid n J).maximalAtlas N := hsub.codChart_mem_maximalAtlas
    let s := e.target ∩ e.symm ⁻¹' ψ.source
    have hs : IsOpen s := e.symm.continuousOn_toFun.isOpen_inter_preimage
      e.open_target ψ.open_source
    have hus : u ∈ s := ⟨hu.1, mem_preimage.2 (hx ▸ hsub.mem_codChart_source)⟩
    refine ⟨s, hs, hus, ?_⟩
    have hA : e.symm ≫ₕ ψ ∈ contDiffGroupoid n J := (_root_.mem_maximalAtlas_iff.1 hψ e he).2
    have hB : ψ.symm ≫ₕ e' ∈ contDiffGroupoid n J := (_root_.mem_maximalAtlas_iff.1 hψ e' he').1
    have hC := (contDiffGroupoid n J).trans hA hB
    have hD : (e.symm ≫ₕ ψ) ≫ₕ ψ.symm ≫ₕ e' ≈ (e.symm ≫ₕ e').restr s := calc
      (e.symm ≫ₕ ψ) ≫ₕ ψ.symm ≫ₕ e' = e.symm ≫ₕ (ψ ≫ₕ ψ.symm) ≫ₕ e' := by
        simp only [OpenPartialHomeomorph.trans_assoc]
      _ ≈ e.symm ≫ₕ OpenPartialHomeomorph.ofSet ψ.source ψ.open_source ≫ₕ e' :=
        OpenPartialHomeomorph.EqOnSource.trans' (Setoid.refl _)
          (.trans' ψ.self_trans_symm (Setoid.refl _))
      _ ≈ (e.symm ≫ₕ OpenPartialHomeomorph.ofSet ψ.source ψ.open_source) ≫ₕ e' := by
        rw [OpenPartialHomeomorph.trans_assoc]
      _ ≈ e.symm.restr s ≫ₕ e' := by
        rw [OpenPartialHomeomorph.trans_of_set']
        exact Setoid.refl _
      _ ≈ (e.symm ≫ₕ e').restr s := by rw [OpenPartialHomeomorph.restr_trans]
    exact (contDiffGroupoid n J).mem_of_eqOnSource hC (Setoid.symm hD)

/-- **Maximal atlas charts via a surjective submersion.** For a surjective `C^n` submersion
`f : M → N` out of a boundaryless manifold, an open partial homeomorphism
`φ : OpenPartialHomeomorph N G` belongs to the `C^n` maximal atlas of `N` if and only if `φ ∘ f` is
a `C^n` submersion at every point of `f ⁻¹' φ.source`. -/
theorem mem_maximalAtlas_iff [I.Boundaryless]
    (hf : IsSubmersion I J n f) (hsurj : Surjective f) (φ : OpenPartialHomeomorph N G) :
    φ ∈ IsManifold.maximalAtlas J n N ↔ ∀ x, f x ∈ φ.source → IsSubmersionAt I J n (φ ∘ f) x := by
  have := hf.isManifold hsurj
  refine ⟨fun hφ x hfx ↦
    (φ.isLocalDiffeomorphAt_of_mem_maximalAtlas hφ hfx).comp_isSubmersionAt (hf.isSubmersionAt x),
    fun h ↦ ?_⟩
  rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn]
  refine ⟨fun y hy ↦ ?_, fun w hw ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := hsurj y
    exact (((hf.isSubmersionAt x).contMDiffAt_comp_iff le_rfl).1
      (h x hy).contMDiffAt).contMDiffWithinAt
  · obtain ⟨x, hx⟩ := hsurj (φ.symm w)
    have hfx : f x ∈ φ.source := hx ▸ φ.map_target hw
    have hφfx : (φ ∘ f) x = w := by simp [hx, φ.right_inv hw]
    obtain ⟨U, hU, hwU, s, hsx, hs, hφfs⟩ := (h x hfx).exists_contMDiffOn_section
    have hwU' : w ∈ U := hφfx ▸ hwU
    have hfs : ContMDiffAt J J n (f ∘ s) w :=
      hf.contMDiff.contMDiffAt.comp w (hs.contMDiffAt (hU.mem_nhds hwU'))
    have hsw : f (s w) ∈ φ.source := by rwa [← hφfx, hsx]
    refine (hfs.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [hU.mem_nhds hwU',
      hfs.continuousAt.preimage_mem_nhds (φ.open_source.mem_nhds hsw)] with u huU hfu
    exact (congrArg φ.symm (hφfs u huU)).symm.trans (φ.left_inv hfu)

omit cN in
/-- **Uniqueness of the maximal atlas of a submersion quotient.** Two charted-space structures on
the same topological space `N` with a common model `J` for which a surjective map `f : M → N` from
a boundaryless manifold is a `C^n` submersion have the same `C^n` maximal atlas. -/
theorem maximalAtlas_eq [I.Boundaryless] {a b : ChartedSpace G N}
    (hfa : letI := a; IsSubmersion I J n f) (hfb : letI := b; IsSubmersion I J n f)
    (hsurj : Surjective f) :
    (letI := a; IsManifold.maximalAtlas J n N) = (letI := b; IsManifold.maximalAtlas J n N) := by
  have key (c : ChartedSpace G N) (hfc : letI := c; IsSubmersion I J n f)
      (φ : OpenPartialHomeomorph N G) :
      (letI := c; φ ∈ IsManifold.maximalAtlas J n N) ↔
        ∀ x, f x ∈ φ.source → IsSubmersionAt I J n (φ ∘ f) x := by
    let := c
    exact hfc.mem_maximalAtlas_iff hsurj φ
  ext φ
  rw [key a hfa, key b hfb]

end Manifold.IsSubmersion
