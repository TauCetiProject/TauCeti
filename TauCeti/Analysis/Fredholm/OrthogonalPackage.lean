/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Adjoint
public import TauCeti.Analysis.InnerProductSpace.Projection.Basic

/-!
# Orthogonal Fredholm packages and quasi-inverse error projections

A `ContinuousLinearMap.FredholmPackage` for an operator `T : E →L[𝕜] F` splits the domain as
`E = X₁ ⊕ X₀` and the codomain as `F = R₁ ⊕ C₀`, with `X₀ = ker T` and `R₁ = range T`
complemented by a closed finite-codimensional subspace `X₁` and a finite-dimensional subspace `C₀`,
and identifies `T` on `X₁` with an isomorphism `equiv : X₁ ≃L[𝕜] R₁`.

This file first records the general structure of the package quasi-inverse
`pkg.quasiInverse : F →L[𝕜] E`:
* `pkg.symm` packages `pkg.quasiInverse` itself as a Fredholm operator with swapped decompositions,
  kernel `C₀`, range `X₁`, and opposite index `-T.index`. In particular `pkg.quasiInverse` has
  finite rank only when the ambient domain `E` is finite-dimensional.
* `pkg.quasiInverse ∘L T` and `T ∘L pkg.quasiInverse` are the projections onto `X₁` along `X₀` and
  onto `R₁` along `C₀`, so their differences from the identity are the finite-rank projections onto
  `X₀` and `C₀`.

When `E` and `F` are Hilbert spaces over `ℝ` or `ℂ`, the orthogonal complements `X₁ = (ker T)ᗮ` and
`C₀ = ker T† = (range T)ᗮ` assemble via `ContinuousLinearMap.IsFredholm.fredholmPackage` into a
canonical orthogonal package `ContinuousLinearMap.IsFredholm.orthogonalFredholmPackage`. Its
essential equivalence is `ContinuousLinearMap.orthogonalKerEquivRange`, its two corner errors are
the orthogonal projections onto `ker T` and `ker T†`, and its kernel, range, and codomain
projection are compared with those of arbitrary Fredholm packages for `T`.

## Main declarations

* `ContinuousLinearMap.FredholmPackage.symm`: the dual `FredholmPackage` for `pkg.quasiInverse`.
* `ContinuousLinearMap.FredholmPackage.id_sub_quasiInverse_comp_self`,
  `ContinuousLinearMap.FredholmPackage.id_sub_self_comp_quasiInverse`: the two finite-rank corner
  error projections of a Fredholm package.
* `ContinuousLinearMap.isTopCompl_range_ker_adjoint_of_isClosed_range`: on Hilbert spaces, a
  closed-range operator splits the target topologically as `range T ⊕ ker T†`.
* `ContinuousLinearMap.IsFredholm.orthogonalFredholmPackage`: the canonical `FredholmPackage`
  built from `(ker T)ᗮ` and `ker T†`.
* `ContinuousLinearMap.IsFredholm.id_sub_orthogonalFredholmPackage_quasiInverse_comp_self`,
  `ContinuousLinearMap.IsFredholm.id_sub_self_comp_orthogonalFredholmPackage_quasiInverse`: the
  quasi-inverse of the orthogonal package inverts `T` up to `starProjection` onto `ker T` and
  `ker T†`.

## References

* [N. Bourbaki, *Théories Spectrales*, Chapitre III, § 3, n° 2][bourbaki2023]
* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix A.1.
-/

public section

noncomputable section

open Module Submodule Topology
open scoped InnerProduct

namespace ContinuousLinearMap

/-! ### General Fredholm packages and their quasi-inverse error projections -/

/-- Given a `FredholmDecomposition` `dec` of `E`, `dec.proj₀` is the continuous linear projection
onto the finite-dimensional part `dec.X₀` along the essential part `dec.X₁`. -/
abbrev _root_.FredholmDecomposition.proj₀ {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousSub E]
    (dec : FredholmDecomposition 𝕜 E) : E →L[𝕜] dec.X₀ :=
  dec.X₀.projectionOntoL dec.X₁ dec.isTopCompl.symm

namespace FredholmPackage

section TVS

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  {T : E →L[𝕜] F} (pkg : T.FredholmPackage)

-- The body is exposed so that `pkg.symm.decDom` and `pkg.symm.decCodom` reduce in downstream types.
/-- Swapping the domain and codomain decompositions of a `FredholmPackage` for `T` gives a
`FredholmPackage` for `pkg.quasiInverse`. -/
@[expose]
def symm : pkg.quasiInverse.FredholmPackage where
  decDom := pkg.decCodom
  decCodom := pkg.decDom
  equiv := pkg.equiv.symm
  eq_equiv := rfl

@[simp]
theorem symm_decDom : pkg.symm.decDom = pkg.decCodom :=
  rfl

@[simp]
theorem symm_decCodom : pkg.symm.decCodom = pkg.decDom :=
  rfl

@[simp]
theorem symm_equiv : pkg.symm.equiv = pkg.equiv.symm :=
  rfl

/-- Taking the quasi-inverse of the dual package recovers the original operator. -/
@[simp]
theorem symm_quasiInverse : pkg.symm.quasiInverse = T :=
  pkg.eq_equiv.symm

/-- The kernel of `pkg.quasiInverse` is the finite-dimensional codomain complement `decCodom.X₀`. -/
@[simp]
theorem ker_quasiInverse : pkg.quasiInverse.ker = pkg.decCodom.X₀ :=
  pkg.symm.ker_eq

/-- The range of `pkg.quasiInverse` is the essential domain summand `decDom.X₁`. -/
@[simp]
theorem range_quasiInverse : pkg.quasiInverse.range = pkg.decDom.X₁ :=
  pkg.symm.range_eq

/-- Left composition of `T` with `pkg.quasiInverse` is the projection onto `decDom.X₁` along
`decDom.X₀`. -/
theorem quasiInverse_comp_self :
    pkg.quasiInverse ∘L T = pkg.decDom.X₁.projectionL pkg.decDom.X₀ pkg.decDom.isTopCompl := by
  ext x
  have hx : T x = (pkg.decCodom.X₁.subtypeL ∘L pkg.equiv ∘L pkg.decDom.proj) x :=
    DFunLike.congr_fun pkg.eq_equiv x
  rw [comp_apply, hx, FredholmPackage.quasiInverse]
  simp only [comp_apply, ContinuousLinearEquiv.coe_coe, Submodule.subtypeL_apply]
  rw [Submodule.projectionOntoL_apply_left pkg.decCodom.isTopCompl,
    ContinuousLinearEquiv.symm_apply_apply, Submodule.coe_projectionOntoL_apply]

/-- Right composition of `T` with `pkg.quasiInverse` is the projection onto `decCodom.X₁` along
`decCodom.X₀`. -/
theorem self_comp_quasiInverse :
    T ∘L pkg.quasiInverse = pkg.decCodom.X₁.projectionL pkg.decCodom.X₀ pkg.decCodom.isTopCompl :=
  (congrArg (· ∘L pkg.quasiInverse) pkg.symm_quasiInverse.symm).trans
    pkg.symm.quasiInverse_comp_self

/-- The left quasi-inverse defect `id - pkg.quasiInverse ∘L T` is the finite-rank projection onto
the kernel `decDom.X₀` along `decDom.X₁`. -/
theorem id_sub_quasiInverse_comp_self [IsTopologicalAddGroup E] :
    ContinuousLinearMap.id 𝕜 E - pkg.quasiInverse ∘L T =
      pkg.decDom.X₀.projectionL pkg.decDom.X₁ pkg.decDom.isTopCompl.symm := by
  rw [pkg.quasiInverse_comp_self,
    ← Submodule.projectionL_eq_id_sub_projectionL pkg.decDom.isTopCompl]

/-- The right quasi-inverse defect `id - T ∘L pkg.quasiInverse` is the finite-rank projection onto
the codomain complement `decCodom.X₀` along `decCodom.X₁`. -/
theorem id_sub_self_comp_quasiInverse [IsTopologicalAddGroup F] :
    ContinuousLinearMap.id 𝕜 F - T ∘L pkg.quasiInverse =
      pkg.decCodom.X₀.projectionL pkg.decCodom.X₁ pkg.decCodom.isTopCompl.symm := by
  rw [pkg.self_comp_quasiInverse,
    ← Submodule.projectionL_eq_id_sub_projectionL pkg.decCodom.isTopCompl]

/-- The left error `id - pkg.quasiInverse ∘L T` has finite range `decDom.X₀`. -/
theorem hasFiniteRange_id_sub_quasiInverse_comp_self [IsTopologicalAddGroup E] :
    LinearMap.HasFiniteRange
      (ContinuousLinearMap.id 𝕜 E - pkg.quasiInverse ∘L T).toLinearMap := by
  have := pkg.decDom.finite_X₀
  have h := congrArg ContinuousLinearMap.toLinearMap pkg.id_sub_quasiInverse_comp_self
  rw [LinearMap.HasFiniteRange, h]
  change (pkg.decDom.X₀.projectionL pkg.decDom.X₁ pkg.decDom.isTopCompl.symm).range.FG
  rw [Submodule.range_projectionL]
  exact .of_finite

/-- The right error `id - T ∘L pkg.quasiInverse` has finite range `decCodom.X₀`. -/
theorem hasFiniteRange_id_sub_self_comp_quasiInverse [IsTopologicalAddGroup F] :
    LinearMap.HasFiniteRange
      (ContinuousLinearMap.id 𝕜 F - T ∘L pkg.quasiInverse).toLinearMap := by
  simpa only [symm_quasiInverse] using pkg.symm.hasFiniteRange_id_sub_quasiInverse_comp_self

/-- The quasi-inverse of a Fredholm package has finite range if and only if the entire domain `E`
is finite-dimensional; on an infinite-dimensional domain it is never a finite-rank map. -/
theorem hasFiniteRange_quasiInverse_iff :
    LinearMap.HasFiniteRange (pkg.quasiInverse : F →ₗ[𝕜] E) ↔ FiniteDimensional 𝕜 E := by
  have := pkg.decDom.finite_X₀
  rw [LinearMap.HasFiniteRange]
  change pkg.quasiInverse.range.FG ↔ FiniteDimensional 𝕜 E
  rw [pkg.range_quasiInverse, Submodule.fg_iff_finiteDimensional]
  refine ⟨fun hX₁ => ?_, fun _ => inferInstance⟩
  exact (Submodule.prodEquivOfIsCompl pkg.decDom.X₁ pkg.decDom.X₀
    pkg.decDom.isTopCompl.isCompl).finiteDimensional

/-- The index of an operator admitting a `FredholmPackage` is `dim decDom.X₀ - dim decCodom.X₀`. -/
theorem index_eq :
    T.index = (finrank 𝕜 pkg.decDom.X₀ : ℤ) - finrank 𝕜 pkg.decCodom.X₀ := by
  rw [index_eq_finrank_sub, pkg.ker_eq, pkg.range_eq,
    (pkg.decCodom.X₁.quotientEquivOfIsCompl pkg.decCodom.X₀
      pkg.decCodom.isTopCompl.isCompl).finrank_eq]

/-- The quasi-inverse of a `FredholmPackage` has index opposite to that of `T`. -/
@[simp]
theorem index_quasiInverse : pkg.quasiInverse.index = -T.index := by
  rw [pkg.symm.index_eq, pkg.index_eq, symm_decDom, symm_decCodom]
  omega

/-- Over a complete scalar field, the quasi-inverse attached to a `FredholmPackage` is itself a
Fredholm operator. -/
theorem isFredholm_quasiInverse [CompleteSpace 𝕜]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
    [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [T2Space F] :
    IsFredholm pkg.quasiInverse :=
  pkg.symm.isFredholm

end TVS

end FredholmPackage

/-! ### Orthogonal Fredholm packages on Hilbert spaces -/

section Hilbert

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Two topological-complement projections onto the same subspace `p` along equal complements `q`
and `q'` coincide as continuous linear maps `G →L[𝕜] p`. -/
private theorem projectionOntoL_eq_of_eq {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {p q q' : Submodule 𝕜 G} (h : IsTopCompl p q) (h' : IsTopCompl p q') (hq : q = q') :
    p.projectionOntoL q h = p.projectionOntoL q' h' := by
  apply ContinuousLinearMap.coe_inj.mp
  refine LinearMap.ext_on_codisjoint h.isCompl.codisjoint (fun x hx => ?_) (fun x hx => ?_)
  · exact (Submodule.projectionOntoL_apply_left h ⟨x, hx⟩).trans
      (Submodule.projectionOntoL_apply_left h' ⟨x, hx⟩).symm
  · have hx' : x ∈ q' := hq ▸ hx
    exact (Submodule.projectionOntoL_apply_right h ⟨x, hx⟩).trans
      (Submodule.projectionOntoL_apply_right h' ⟨x, hx'⟩).symm

/-- For a closed-range operator `T` between Hilbert spaces, `range T` and `ker T†` are topological
complements. -/
theorem isTopCompl_range_ker_adjoint_of_isClosed_range (T : E →L[𝕜] F)
    (hT : IsClosed (T.range : Set F)) :
    IsTopCompl T.range (T†).ker := by
  let : CompleteSpace T.range := hT.completeSpace_coe
  simpa only [T.orthogonal_range] using T.range.isTopCompl_orthogonal

-- The body is exposed so that `decDom` and `decCodom` reduce to `(ker T)ᗮ ⊕ ker T` and
-- `range T ⊕ ker T†` in the types of downstream projections and Schur complements.
/-- The canonical **orthogonal Fredholm package** of a Fredholm operator `T` between Hilbert
spaces: it decomposes the domain as `(ker T)ᗮ ⊕ ker T` and the codomain as `range T ⊕ ker T†` via
`ContinuousLinearMap.IsFredholm.fredholmPackage`. -/
@[expose]
def IsFredholm.orthogonalFredholmPackage {T : E →L[𝕜] F} (hT : T.IsFredholm) :
    T.FredholmPackage :=
  hT.fredholmPackage T.ker.isTopCompl_orthogonal
    (T.isTopCompl_range_ker_adjoint_of_isClosed_range hT.isClosed_range)

namespace IsFredholm

variable {T : E →L[𝕜] F} (hT : T.IsFredholm)

@[simp]
theorem orthogonalFredholmPackage_decDom_X₀ :
    hT.orthogonalFredholmPackage.decDom.X₀ = T.ker :=
  rfl

@[simp]
theorem orthogonalFredholmPackage_decDom_X₁ :
    hT.orthogonalFredholmPackage.decDom.X₁ = T.kerᗮ :=
  rfl

@[simp]
theorem orthogonalFredholmPackage_decCodom_X₁ :
    hT.orthogonalFredholmPackage.decCodom.X₁ = T.range :=
  rfl

@[simp]
theorem orthogonalFredholmPackage_decCodom_X₀ :
    hT.orthogonalFredholmPackage.decCodom.X₀ = (T†).ker :=
  rfl

/-- The domain projection of `hT.orthogonalFredholmPackage` is the orthogonal projection onto
`(ker T)ᗮ`. -/
@[simp]
theorem orthogonalFredholmPackage_decDom_proj :
    hT.orthogonalFredholmPackage.decDom.proj = T.kerᗮ.orthogonalProjectionOnto :=
  projectionOntoL_eq_of_eq _ _ (Submodule.orthogonal_orthogonal T.ker).symm

/-- The inessential domain projection of `hT.orthogonalFredholmPackage` is the orthogonal
projection onto `ker T`. -/
@[simp]
theorem orthogonalFredholmPackage_decDom_proj₀ :
    hT.orthogonalFredholmPackage.decDom.proj₀ = T.ker.orthogonalProjectionOnto :=
  projectionOntoL_eq_of_eq _ _ rfl

/-- The inessential codomain projection of `hT.orthogonalFredholmPackage` is the orthogonal
projection onto `ker T†`. -/
@[simp]
theorem orthogonalFredholmPackage_decCodom_proj₀ :
    hT.orthogonalFredholmPackage.decCodom.proj₀ = (T†).ker.orthogonalProjectionOnto :=
  projectionOntoL_eq_of_eq _ _
    (T.range_eq_orthogonal_ker_adjoint_of_isClosed_range hT.isClosed_range)

/-- When `T.range` carries its `HasOrthogonalProjection` instance, the codomain projection of
`hT.orthogonalFredholmPackage` is literally `T.range.orthogonalProjectionOnto`. -/
theorem orthogonalFredholmPackage_decCodom_proj [T.range.HasOrthogonalProjection] :
    hT.orthogonalFredholmPackage.decCodom.proj = T.range.orthogonalProjectionOnto :=
  projectionOntoL_eq_of_eq _ _ T.orthogonal_range.symm

/-- Viewed in `F`, the codomain projection of `hT.orthogonalFredholmPackage` is
`T.range.starProjection`. -/
theorem subtypeL_comp_orthogonalFredholmPackage_decCodom_proj_eq_starProjection
    [T.range.HasOrthogonalProjection] :
    hT.orthogonalFredholmPackage.decCodom.X₁.subtypeL ∘L
        hT.orthogonalFredholmPackage.decCodom.proj = T.range.starProjection := by
  ext y
  exact congr_arg Subtype.val (DFunLike.congr_fun hT.orthogonalFredholmPackage_decCodom_proj y)

/-- Viewed in the ambient target `F`, the codomain projection of `hT.orthogonalFredholmPackage` is
`id - (ker T†).starProjection`. Unlike `orthogonalFredholmPackage_decCodom_proj`, this requires no
`HasOrthogonalProjection` instance on `T.range`. -/
theorem subtypeL_comp_orthogonalFredholmPackage_decCodom_proj :
    hT.orthogonalFredholmPackage.decCodom.X₁.subtypeL ∘L
        hT.orthogonalFredholmPackage.decCodom.proj =
      ContinuousLinearMap.id 𝕜 F - (T†).ker.starProjection := by
  let : CompleteSpace T.range := hT.isClosed_range.completeSpace_coe
  rw [hT.subtypeL_comp_orthogonalFredholmPackage_decCodom_proj_eq_starProjection]
  ext y
  simp only [sub_apply, id_apply, ← T.orthogonal_range, Submodule.starProjection_orthogonal_val,
    sub_sub_cancel]

/-- The essential isomorphism of `hT.orthogonalFredholmPackage` is
`T.orthogonalKerEquivRange hT.isClosed_range`. -/
@[simp]
theorem orthogonalFredholmPackage_equiv :
    hT.orthogonalFredholmPackage.equiv = T.orthogonalKerEquivRange hT.isClosed_range := by
  ext x
  exact (congr_arg Subtype.val
    (DFunLike.congr_fun hT.orthogonalFredholmPackage.equiv_eq_restrict x)).trans
    (T.orthogonalKerEquivRange_apply hT.isClosed_range x).symm

/-- Left composition of `T` with the orthogonal quasi-inverse is orthogonal projection onto
`(ker T)ᗮ`. -/
@[simp]
theorem orthogonalFredholmPackage_quasiInverse_comp_self :
    hT.orthogonalFredholmPackage.quasiInverse ∘L T = T.kerᗮ.starProjection := by
  ext x
  rw [hT.orthogonalFredholmPackage.quasiInverse_comp_self, ← Submodule.coe_projectionOntoL_apply]
  exact congr_arg Subtype.val (DFunLike.congr_fun hT.orthogonalFredholmPackage_decDom_proj x)

/-- Right composition of `T` with the orthogonal quasi-inverse is `id - (ker T†).starProjection`. -/
theorem self_comp_orthogonalFredholmPackage_quasiInverse :
    T ∘L hT.orthogonalFredholmPackage.quasiInverse =
      ContinuousLinearMap.id 𝕜 F - (T†).ker.starProjection := by
  rw [hT.orthogonalFredholmPackage.self_comp_quasiInverse]
  exact hT.subtypeL_comp_orthogonalFredholmPackage_decCodom_proj

/-- When `T.range` carries `HasOrthogonalProjection`, right composition of `T` with the orthogonal
quasi-inverse is `T.range.starProjection`. -/
theorem self_comp_orthogonalFredholmPackage_quasiInverse_eq_starProjection
    [T.range.HasOrthogonalProjection] :
    T ∘L hT.orthogonalFredholmPackage.quasiInverse = T.range.starProjection := by
  rw [hT.orthogonalFredholmPackage.self_comp_quasiInverse]
  exact hT.subtypeL_comp_orthogonalFredholmPackage_decCodom_proj_eq_starProjection

/-- The left error of the orthogonal quasi-inverse is the finite-rank orthogonal projection onto
`ker T`. -/
theorem id_sub_orthogonalFredholmPackage_quasiInverse_comp_self :
    ContinuousLinearMap.id 𝕜 E - hT.orthogonalFredholmPackage.quasiInverse ∘L T =
      T.ker.starProjection := by
  ext x
  rw [sub_apply, id_apply, hT.orthogonalFredholmPackage_quasiInverse_comp_self,
    Submodule.starProjection_orthogonal_val, sub_sub_cancel]

/-- The right error of the orthogonal quasi-inverse is the finite-rank orthogonal projection onto
`ker T†`. -/
@[simp]
theorem id_sub_self_comp_orthogonalFredholmPackage_quasiInverse :
    ContinuousLinearMap.id 𝕜 F - T ∘L hT.orthogonalFredholmPackage.quasiInverse =
      (T†).ker.starProjection := by
  rw [hT.self_comp_orthogonalFredholmPackage_quasiInverse, sub_sub_cancel]

/-! ### Comparison with general Fredholm packages -/

/-- Any `FredholmPackage` for `T` whose codomain complement is `(range T)ᗮ` has the same ambient
codomain projection in `F →L[𝕜] F` as `hT.orthogonalFredholmPackage`, namely
`id - (ker T†).starProjection`. -/
theorem subtypeL_comp_decCodom_proj_eq_orthogonalFredholmPackage_of_eq_orthogonal
    (pkg : T.FredholmPackage) (hcod : pkg.decCodom.X₀ = T.rangeᗮ) :
    pkg.decCodom.X₁.subtypeL ∘L pkg.decCodom.proj =
      hT.orthogonalFredholmPackage.decCodom.X₁.subtypeL ∘L
        hT.orthogonalFredholmPackage.decCodom.proj := by
  apply ContinuousLinearMap.coe_inj.mp
  refine LinearMap.ext_on_codisjoint pkg.decCodom.isTopCompl.isCompl.codisjoint
    (fun y hy => ?_) (fun y hy => ?_)
  · have hyR : y ∈ T.range := pkg.range_eq ▸ hy
    change (pkg.decCodom.proj y : F) = (hT.orthogonalFredholmPackage.decCodom.proj y : F)
    exact (congrArg Subtype.val (Submodule.projectionOntoL_apply_left
      pkg.decCodom.isTopCompl ⟨y, hy⟩)).trans
      (congrArg Subtype.val (Submodule.projectionOntoL_apply_left
        hT.orthogonalFredholmPackage.decCodom.isTopCompl ⟨y, hyR⟩)).symm
  · have hyK : y ∈ (T†).ker := T.orthogonal_range ▸ hcod ▸ hy
    have h₁ : pkg.decCodom.proj y = 0 :=
      Submodule.projectionOntoL_apply_right pkg.decCodom.isTopCompl ⟨y, hy⟩
    have h₂ : hT.orthogonalFredholmPackage.decCodom.proj y = 0 :=
      Submodule.projectionOntoL_apply_right
        hT.orthogonalFredholmPackage.decCodom.isTopCompl ⟨y, hyK⟩
    change (pkg.decCodom.proj y : F) = (hT.orthogonalFredholmPackage.decCodom.proj y : F)
    rw [h₁, h₂]
    rfl

end IsFredholm

end Hilbert

end ContinuousLinearMap

end
