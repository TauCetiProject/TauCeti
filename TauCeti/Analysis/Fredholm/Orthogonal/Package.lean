/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Basic
public import TauCeti.Analysis.Fredholm.Adjoint
import TauCeti.Topology.Algebra.Module.Complement

/-!
# Orthogonal Fredholm packages on Hilbert spaces

When `E` and `F` are Hilbert spaces over `ℝ` or `ℂ` and `T : E →L[𝕜] F` is Fredholm, the orthogonal
complements `X₁ = (ker T)ᗮ` and `C₀ = ker T† = (range T)ᗮ` assemble via
`ContinuousLinearMap.IsFredholm.fredholmPackage` into a canonical orthogonal package
`ContinuousLinearMap.IsFredholm.orthogonalFredholmPackage` splitting the domain as
`(ker T)ᗮ ⊕ ker T` and the codomain as `range T ⊕ ker T†`.

Its component projections are the orthogonal projections onto `(ker T)ᗮ`, `ker T`, `range T`, and
`ker T†`, its essential equivalence is `ContinuousLinearMap.orthogonalKerEquivRange`, and its two
finite-rank quasi-inverse error projections `id - quasiInverse ∘L T` and `id - T ∘L quasiInverse`
are `T.ker.starProjection` and `(T†).ker.starProjection`. For an arbitrary `FredholmPackage` `pkg`
of `T`, identifying `pkg.decCodom.X₀` with `ker T†` through the cokernel `F ⧸ T.range` via
`ContinuousLinearMap.FredholmPackage.decCodomX₀EquivKerAdjoint` carries the package defect
projection `pkg.decCodom.proj₀` to the orthogonal defect projection
`(T†).ker.orthogonalProjectionOnto`.

General topological-vector-space package duality (`ContinuousLinearMap.FredholmPackage.symm`),
cokernel equivalence (`ContinuousLinearMap.FredholmPackage.cokerEquiv`), quasi-inverse error
projections, and ambient projection congruence live in `TauCeti.Analysis.Fredholm.Basic`.

## Main declarations

* `ContinuousLinearMap.IsFredholm.orthogonalFredholmPackage`: the canonical `FredholmPackage`
  built from `(ker T)ᗮ` and `ker T†`.
* `ContinuousLinearMap.IsFredholm.orthogonalFredholmPackage_decDom_proj`,
  `ContinuousLinearMap.IsFredholm.orthogonalFredholmPackage_decDom_proj₀`,
  `ContinuousLinearMap.IsFredholm.orthogonalFredholmPackage_decCodom_proj`,
  `ContinuousLinearMap.IsFredholm.orthogonalFredholmPackage_decCodom_proj₀`: the four orthogonal
  summand projections of `hT.orthogonalFredholmPackage`.
* `ContinuousLinearMap.IsFredholm.id_sub_orthogonalFredholmPackage_quasiInverse_comp_self`,
  `ContinuousLinearMap.IsFredholm.id_sub_self_comp_orthogonalFredholmPackage_quasiInverse`: the
  quasi-inverse of the orthogonal package inverts `T` up to `starProjection` onto `ker T` and
  `ker T†`.
* `ContinuousLinearMap.FredholmPackage.decCodomX₀EquivKerAdjoint`,
  `ContinuousLinearMap.FredholmPackage.decCodomX₀EquivKerAdjoint_comp_decCodom_proj₀`,
  `FredholmPackage.decCodomX₀EquivKerAdjoint_symm_comp_orthogonalProjectionOnto`:
  cokernel-mediated identification `pkg.decCodom.X₀ ≃L[𝕜] ker T†` for any `FredholmPackage` `pkg`
  of `T`, carrying `pkg.decCodom.proj₀` to `(T†).ker.orthogonalProjectionOnto`.

## References

* [N. Bourbaki, *Théories Spectrales*, Chapitre III, § 3, n° 2][bourbaki2023]
* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix A.1.
-/

public section

noncomputable section

open Module Submodule Topology
open scoped InnerProduct

namespace ContinuousLinearMap

section Hilbert

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

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
    hT.orthogonalFredholmPackage.decDom.proj = T.kerᗮ.orthogonalProjectionOnto := by
  rw [Submodule.orthogonalProjectionOnto]
  exact Submodule.projectionOntoL_congr (Submodule.orthogonal_orthogonal T.ker).symm

/-- The inessential domain projection of `hT.orthogonalFredholmPackage` is the orthogonal
projection onto `ker T`. -/
@[simp]
theorem orthogonalFredholmPackage_decDom_proj₀ :
    hT.orthogonalFredholmPackage.decDom.proj₀ = T.ker.orthogonalProjectionOnto := by
  rw [Submodule.orthogonalProjectionOnto]
  exact Submodule.projectionOntoL_congr rfl

/-- The inessential codomain projection of `hT.orthogonalFredholmPackage` is the orthogonal
projection onto `ker T†`. -/
@[simp]
theorem orthogonalFredholmPackage_decCodom_proj₀ :
    hT.orthogonalFredholmPackage.decCodom.proj₀ = (T†).ker.orthogonalProjectionOnto := by
  rw [Submodule.orthogonalProjectionOnto]
  exact Submodule.projectionOntoL_congr
    (T.range_eq_orthogonal_ker_adjoint_of_isClosed_range hT.isClosed_range)

/-- When `T.range` carries its `HasOrthogonalProjection` instance, the codomain projection of
`hT.orthogonalFredholmPackage` is `T.range.orthogonalProjectionOnto`. -/
@[simp]
theorem orthogonalFredholmPackage_decCodom_proj [T.range.HasOrthogonalProjection] :
    hT.orthogonalFredholmPackage.decCodom.proj = T.range.orthogonalProjectionOnto := by
  rw [Submodule.orthogonalProjectionOnto]
  exact Submodule.projectionOntoL_congr T.orthogonal_range.symm

/-- Viewed in `F`, the ambient codomain projection of `hT.orthogonalFredholmPackage` is
`T.range.starProjection`. -/
theorem projectionL_orthogonalFredholmPackage_decCodom_eq_starProjection
    [T.range.HasOrthogonalProjection] :
    hT.orthogonalFredholmPackage.decCodom.X₁.projectionL
        hT.orthogonalFredholmPackage.decCodom.X₀
        hT.orthogonalFredholmPackage.decCodom.isTopCompl =
      T.range.starProjection := by
  rw [Submodule.starProjection, Submodule.orthogonalProjectionOnto, ← Submodule.projectionL]
  exact Submodule.projectionL_congr rfl T.orthogonal_range.symm

/-- Viewed in the ambient target `F`, the codomain projection of `hT.orthogonalFredholmPackage` is
`id - (ker T†).starProjection`. Unlike
`projectionL_orthogonalFredholmPackage_decCodom_eq_starProjection`, this requires no
`HasOrthogonalProjection` instance on `T.range`. -/
theorem projectionL_orthogonalFredholmPackage_decCodom :
    hT.orthogonalFredholmPackage.decCodom.X₁.projectionL
        hT.orthogonalFredholmPackage.decCodom.X₀
        hT.orthogonalFredholmPackage.decCodom.isTopCompl =
      ContinuousLinearMap.id 𝕜 F - (T†).ker.starProjection := by
  let : CompleteSpace T.range := hT.isClosed_range.completeSpace_coe
  rw [hT.projectionL_orthogonalFredholmPackage_decCodom_eq_starProjection]
  ext y
  simp only [sub_apply, id_apply, ← T.orthogonal_range, Submodule.starProjection_orthogonal_val,
    sub_sub_cancel]

/-- The essential isomorphism of `hT.orthogonalFredholmPackage` is
`T.orthogonalKerEquivRange hT.isClosed_range`. -/
@[simp]
theorem orthogonalFredholmPackage_equiv :
    hT.orthogonalFredholmPackage.equiv = T.orthogonalKerEquivRange hT.isClosed_range := by
  ext x
  have hx : (hT.orthogonalFredholmPackage.equiv x : F) = T x :=
    (congr_arg Subtype.val
      (DFunLike.congr_fun hT.orthogonalFredholmPackage.equiv_eq_restrict x)).trans
      (T.coe_restrict_apply _ x)
  exact hx.trans (T.orthogonalKerEquivRange_apply hT.isClosed_range x).symm

/-- Left composition of `T` with the orthogonal quasi-inverse is orthogonal projection onto
`(ker T)ᗮ`. -/
@[simp]
theorem orthogonalFredholmPackage_quasiInverse_comp_self :
    hT.orthogonalFredholmPackage.quasiInverse ∘L T = T.kerᗮ.starProjection := by
  rw [hT.orthogonalFredholmPackage.quasiInverse_comp_self, Submodule.starProjection,
    Submodule.orthogonalProjectionOnto, ← Submodule.projectionL]
  exact Submodule.projectionL_congr rfl T.ker.orthogonal_orthogonal.symm

/-- Right composition of `T` with the orthogonal quasi-inverse is `id - (ker T†).starProjection`. -/
theorem self_comp_orthogonalFredholmPackage_quasiInverse :
    T ∘L hT.orthogonalFredholmPackage.quasiInverse =
      ContinuousLinearMap.id 𝕜 F - (T†).ker.starProjection := by
  rw [hT.orthogonalFredholmPackage.self_comp_quasiInverse]
  exact hT.projectionL_orthogonalFredholmPackage_decCodom

/-- When `T.range` carries `HasOrthogonalProjection`, right composition of `T` with the orthogonal
quasi-inverse is `T.range.starProjection`. -/
theorem self_comp_orthogonalFredholmPackage_quasiInverse_eq_starProjection
    [T.range.HasOrthogonalProjection] :
    T ∘L hT.orthogonalFredholmPackage.quasiInverse = T.range.starProjection := by
  rw [hT.orthogonalFredholmPackage.self_comp_quasiInverse]
  exact hT.projectionL_orthogonalFredholmPackage_decCodom_eq_starProjection

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

/-- For the canonical orthogonal package, `cokerEquiv` agrees with
`T.cokerEquivKerAdjoint hT.isClosed_range`. -/
@[simp]
theorem orthogonalFredholmPackage_cokerEquiv :
    hT.orthogonalFredholmPackage.cokerEquiv = T.cokerEquivKerAdjoint hT.isClosed_range :=
  ContinuousLinearEquiv.symm_bijective.injective <|
    ContinuousLinearEquiv.ext <| funext fun (y₀ : (T†).ker) ↦
      (hT.orthogonalFredholmPackage.cokerEquiv_symm_apply y₀).trans
        (T.cokerEquivKerAdjoint_symm_apply hT.isClosed_range y₀).symm

end IsFredholm

/-! ### Comparison of arbitrary Fredholm packages with the orthogonal defect projection -/

namespace FredholmPackage

variable {T : E →L[𝕜] F} (pkg : T.FredholmPackage)

/-- For any `FredholmPackage` `pkg` of `T` between Hilbert spaces, `pkg.decCodomX₀EquivKerAdjoint`
identifies the codomain complement `pkg.decCodom.X₀` with `ker T†` through the cokernel
`F ⧸ T.range` by composing `pkg.cokerEquiv.symm` with `T.cokerEquivKerAdjoint`. -/
def decCodomX₀EquivKerAdjoint : pkg.decCodom.X₀ ≃L[𝕜] (T†).ker :=
  pkg.cokerEquiv.symm.trans (T.cokerEquivKerAdjoint pkg.isFredholm.isClosed_range)

/-- Identifying `pkg.decCodom.X₀` with `ker T†` through `F ⧸ T.range` carries the codomain defect
projection `pkg.decCodom.proj₀` of any `FredholmPackage` `pkg` to the orthogonal defect projection
`(T†).ker.orthogonalProjectionOnto`. -/
@[simp]
theorem decCodomX₀EquivKerAdjoint_comp_decCodom_proj₀ :
    (pkg.decCodomX₀EquivKerAdjoint : pkg.decCodom.X₀ →L[𝕜] (T†).ker) ∘L pkg.decCodom.proj₀ =
      (T†).ker.orthogonalProjectionOnto := by
  rw [decCodomX₀EquivKerAdjoint, ← ContinuousLinearEquiv.comp_coe, comp_assoc,
    pkg.cokerEquiv_symm_comp_decCodom_proj₀]
  ext y
  simp [T.orthogonal_range]

/-- Inverse form of `decCodomX₀EquivKerAdjoint_comp_decCodom_proj₀`: composing
`pkg.decCodomX₀EquivKerAdjoint.symm` with `(T†).ker.orthogonalProjectionOnto` recovers
`pkg.decCodom.proj₀`. -/
@[simp]
theorem decCodomX₀EquivKerAdjoint_symm_comp_orthogonalProjectionOnto :
    (pkg.decCodomX₀EquivKerAdjoint.symm : (T†).ker →L[𝕜] pkg.decCodom.X₀) ∘L
      (T†).ker.orthogonalProjectionOnto = pkg.decCodom.proj₀ := by
  rw [← pkg.decCodomX₀EquivKerAdjoint_comp_decCodom_proj₀, ← comp_assoc]
  ext y
  simp

@[simp]
theorem decCodomX₀EquivKerAdjoint_apply (y₀ : pkg.decCodom.X₀) :
    pkg.decCodomX₀EquivKerAdjoint y₀ = (T†).ker.orthogonalProjectionOnto (y₀ : F) := by
  rw [← pkg.decCodomX₀EquivKerAdjoint_comp_decCodom_proj₀, comp_apply,
    ContinuousLinearEquiv.coe_coe,
    Submodule.projectionOntoL_apply_left pkg.decCodom.isTopCompl.symm]

@[simp]
theorem decCodomX₀EquivKerAdjoint_symm_apply (y₀ : (T†).ker) :
    pkg.decCodomX₀EquivKerAdjoint.symm y₀ = pkg.decCodom.proj₀ (y₀ : F) := by
  rw [← pkg.decCodomX₀EquivKerAdjoint_symm_comp_orthogonalProjectionOnto, comp_apply,
    ContinuousLinearEquiv.coe_coe, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

end FredholmPackage

end Hilbert

end ContinuousLinearMap

end
