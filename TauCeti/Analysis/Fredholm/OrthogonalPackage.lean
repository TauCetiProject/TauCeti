/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Adjoint
public import TauCeti.Analysis.InnerProductSpace.MoorePenrose
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Analysis.InnerProductSpace.Projection.Completeness

/-!
# Orthogonal Fredholm packages and the Moore–Penrose quasi-inverse

Every Fredholm operator between topological vector spaces admits a `FredholmPackage`, splitting its
domain and codomain into topological complements on which the operator has block form
$\begin{pmatrix} \Phi & 0 \\ 0 & 0 \end{pmatrix}$, and any such package determines a continuous
quasi-inverse whose range, kernel, Fredholmness, and negated index are computed in general by
`ContinuousLinearMap.FredholmPackage.range_quasiInverse`,
`ContinuousLinearMap.FredholmPackage.ker_quasiInverse`,
`ContinuousLinearMap.FredholmPackage.isFredholm_quasiInverse`, and
`ContinuousLinearMap.FredholmPackage.index_quasiInverse`. On general Banach spaces these splittings
require a noncanonical choice of topological complements to the kernel and range.

Between Hilbert spaces, a closed-range operator `T : E →L[𝕜] F` already comes with canonical
orthogonal splittings `E = (ker T)ᗮ ⊕ ker T` and `F = range T ⊕ ker T†`, and the projections onto
the summands along these orthogonal complements agree with the Hilbert-space orthogonal projections.
Specializing `IsFredholm.fredholmPackage` to these splittings produces a canonical
`IsFredholm.orthogonalFredholmPackage` whose essential isomorphism is
`ContinuousLinearMap.orthogonalKerEquivRange`.

Its associated continuous quasi-inverse `hT.orthogonalFredholmPackage.quasiInverse` vanishes on
`ker T†` and inverts `T` onto `(ker T)ᗮ`. Consequently its two compositions with `T` are the
orthogonal projections `(ker T)ᗮ.starProjection` and `(range T).starProjection`, so it satisfies all
four Penrose equations (`IsFredholm.isMoorePenroseInverse_orthogonalFredholmPackage_quasiInverse`).
Uniqueness of the Moore–Penrose inverse then shows without choosing bases that taking Hilbert
adjoints commutes with forming the canonical orthogonal quasi-inverse.

## Main declarations

* `ContinuousLinearMap.IsFredholm.hasOrthogonalProjection_range`: the range of any Fredholm
  operator into a Hilbert space admits an orthogonal projection.
* `ContinuousLinearMap.IsFredholm.orthogonalFredholmPackage`: the canonical `FredholmPackage`
  built from the orthogonal splittings `E = (ker T)ᗮ ⊕ ker T` and `F = range T ⊕ ker T†`.
* `ContinuousLinearMap.IsFredholm.orthogonalFredholmPackage_decDom_proj` and
  `ContinuousLinearMap.IsFredholm.orthogonalFredholmPackage_decCodom_proj`: the essential domain
  and codomain projections of the orthogonal Fredholm package agree with the Hilbert-space
  orthogonal projections.
* `ContinuousLinearMap.IsFredholm.orthogonalFredholmPackage_quasiInverse_comp_self`,
  `ContinuousLinearMap.IsFredholm.orthogonalFredholmPackage_quasiInverse_apply_self`,
  `ContinuousLinearMap.IsFredholm.self_comp_orthogonalFredholmPackage_quasiInverse`, and
  `ContinuousLinearMap.IsFredholm.apply_orthogonalFredholmPackage_quasiInverse`: the two products
  of `T` with its orthogonal quasi-inverse are `(ker T)ᗮ.starProjection` and
  `(range T).starProjection`.
* `ContinuousLinearMap.IsFredholm.isMoorePenroseInverse_orthogonalFredholmPackage_quasiInverse`:
  the orthogonal quasi-inverse satisfies the four Penrose equations.
* `ContinuousLinearMap.IsFredholm.adjoint_orthogonalFredholmPackage_quasiInverse`: taking the
  Hilbert adjoint commutes with forming the orthogonal quasi-inverse.

## References

* N. Bourbaki, *Théories Spectrales*, Chapitre III, §3, n° 2.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix A.1.
-/

public section

open Module Submodule
open scoped InnerProduct

namespace ContinuousLinearMap

section HasOrthogonalProjection

variable {𝕜 G F : Type*} [RCLike 𝕜]
  [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The range of a Fredholm operator into a Hilbert space admits an orthogonal projection. -/
theorem IsFredholm.hasOrthogonalProjection_range {S : G →L[𝕜] F} (hS : S.IsFredholm) :
    S.range.HasOrthogonalProjection :=
  Submodule.hasOrthogonalProjection_iff_isClosed.mpr hS.isClosed_range

end HasOrthogonalProjection

section OrthogonalPackage

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  {T : E →L[𝕜] F}

-- `FredholmPackage` has fields `decDom.proj`, `decCodom.proj`, and `equiv` whose types mention
-- `decDom.X₁` and `decCodom.X₁`; exposing this constructor lets those summands reduce in types.
/-- The canonical `FredholmPackage` of a Fredholm operator `T : E →L[𝕜] F` between Hilbert spaces,
associated to the orthogonal decompositions `E = (ker T)ᗮ ⊕ ker T` and `F = range T ⊕ ker T†`. -/
@[expose]
noncomputable def IsFredholm.orthogonalFredholmPackage (hT : T.IsFredholm) :
    T.FredholmPackage :=
  hT.fredholmPackage T.ker.isTopCompl_orthogonal (T.isTopCompl_range_ker_adjoint hT.isClosed_range)

/-- The inessential domain summand of the orthogonal Fredholm package is `ker T`. -/
@[simp]
theorem IsFredholm.orthogonalFredholmPackage_decDom_X₀ (hT : T.IsFredholm) :
    hT.orthogonalFredholmPackage.decDom.X₀ = T.ker :=
  (rfl)

/-- The essential domain summand of the orthogonal Fredholm package is `(ker T)ᗮ`. -/
@[simp]
theorem IsFredholm.orthogonalFredholmPackage_decDom_X₁ (hT : T.IsFredholm) :
    hT.orthogonalFredholmPackage.decDom.X₁ = (T.ker)ᗮ :=
  (rfl)

/-- The essential codomain summand of the orthogonal Fredholm package is `range T`. -/
@[simp]
theorem IsFredholm.orthogonalFredholmPackage_decCodom_X₁ (hT : T.IsFredholm) :
    hT.orthogonalFredholmPackage.decCodom.X₁ = T.range :=
  (rfl)

/-- The inessential codomain summand of the orthogonal Fredholm package is `ker T†`. -/
@[simp]
theorem IsFredholm.orthogonalFredholmPackage_decCodom_X₀ (hT : T.IsFredholm) :
    hT.orthogonalFredholmPackage.decCodom.X₀ = (T†).ker :=
  (rfl)

/-- The domain projection of the orthogonal Fredholm package is the orthogonal projection onto
`(ker T)ᗮ`. -/
@[simp]
theorem IsFredholm.orthogonalFredholmPackage_decDom_proj (hT : T.IsFredholm) :
    hT.orthogonalFredholmPackage.decDom.proj = (T.ker)ᗮ.orthogonalProjectionOnto :=
  T.ker.projectionOntoL_orthogonal_eq_orthogonalProjectionOnto

/-- The codomain projection of the orthogonal Fredholm package is the orthogonal projection onto
`range T`. -/
@[simp]
theorem IsFredholm.orthogonalFredholmPackage_decCodom_proj (hT : T.IsFredholm)
    [T.range.HasOrthogonalProjection] :
    hT.orthogonalFredholmPackage.decCodom.proj = T.range.orthogonalProjectionOnto :=
  T.projectionOntoL_range_ker_adjoint_eq_orthogonalProjectionOnto hT.isClosed_range

/-- Read in the ambient codomain `F`, the codomain projection of the orthogonal Fredholm package is
`id - (ker T†).starProjection`. -/
theorem IsFredholm.subtypeL_comp_orthogonalFredholmPackage_decCodom_proj (hT : T.IsFredholm) :
    T.range.subtypeL ∘L hT.orthogonalFredholmPackage.decCodom.proj =
      .id 𝕜 F - ((T†).ker).starProjection := by
  have : T.range.HasOrthogonalProjection := hT.hasOrthogonalProjection_range
  rw [hT.orthogonalFredholmPackage_decCodom_proj, ← Submodule.starProjection,
    T.starProjection_ker_adjoint, Submodule.starProjection_orthogonal, sub_sub_cancel]

/-- The essential isomorphism of the orthogonal Fredholm package is
`ContinuousLinearMap.orthogonalKerEquivRange`. -/
@[simp]
theorem IsFredholm.orthogonalFredholmPackage_equiv (hT : T.IsFredholm) :
    hT.orthogonalFredholmPackage.equiv = T.orthogonalKerEquivRange hT.isClosed_range := by
  ext x
  exact congrArg Subtype.val
      (DFunLike.congr_fun hT.orthogonalFredholmPackage.equiv_eq_restrict x) |>.trans
    (T.orthogonalKerEquivRange_apply hT.isClosed_range x).symm

/-! ### The orthogonal quasi-inverse and Penrose equations -/

/-- Explicit formula for the canonical quasi-inverse of the orthogonal Fredholm package as
orthogonal projection onto `range T`, followed by the inverse of `T` onto `(ker T)ᗮ`, followed by
inclusion into `E`. -/
theorem IsFredholm.orthogonalFredholmPackage_quasiInverse_eq (hT : T.IsFredholm)
    [T.range.HasOrthogonalProjection] :
    hT.orthogonalFredholmPackage.quasiInverse =
      (T.ker)ᗮ.subtypeL ∘L
        ((T.orthogonalKerEquivRange hT.isClosed_range).symm : T.range →L[𝕜] (T.ker)ᗮ) ∘L
          T.range.orthogonalProjectionOnto := by
  rw [FredholmPackage.quasiInverse, hT.orthogonalFredholmPackage_equiv,
    hT.orthogonalFredholmPackage_decCodom_proj]
  rfl

/-- The canonical quasi-inverse from the orthogonal Fredholm package vanishes on `ker T†`. -/
@[simp]
theorem IsFredholm.orthogonalFredholmPackage_quasiInverse_apply_of_mem_ker_adjoint
    (hT : T.IsFredholm) {y : F} (hy : y ∈ (T†).ker) :
    hT.orthogonalFredholmPackage.quasiInverse y = 0 :=
  LinearMap.mem_ker.mp (hT.orthogonalFredholmPackage.ker_quasiInverse ▸ hy)

/-- Restricting the orthogonal quasi-inverse to `ker T†` gives the zero operator. -/
@[simp]
theorem IsFredholm.orthogonalFredholmPackage_quasiInverse_comp_subtypeL_ker_adjoint
    (hT : T.IsFredholm) :
    hT.orthogonalFredholmPackage.quasiInverse ∘L (T†).ker.subtypeL = 0 := by
  ext y
  simp only [comp_apply, subtypeL_apply, zero_apply]
  exact LinearMap.mem_ker.mp (hT.orthogonalFredholmPackage.ker_quasiInverse ▸ y.property)

/-- Every value of the orthogonal quasi-inverse lies in `(ker T)ᗮ`. -/
@[simp]
theorem IsFredholm.orthogonalFredholmPackage_quasiInverse_apply_mem_orthogonal_ker
    (hT : T.IsFredholm) (y : F) :
    hT.orthogonalFredholmPackage.quasiInverse y ∈ (T.ker)ᗮ := by
  rw [← hT.orthogonalFredholmPackage_decDom_X₁, ← hT.orthogonalFredholmPackage.range_quasiInverse]
  exact LinearMap.mem_range_self _ y

/-- Precomposing the orthogonal quasi-inverse with `T` gives the orthogonal projection onto
`(ker T)ᗮ`. -/
@[simp]
theorem IsFredholm.orthogonalFredholmPackage_quasiInverse_comp_self (hT : T.IsFredholm) :
    hT.orthogonalFredholmPackage.quasiInverse ∘L T = (T.ker)ᗮ.starProjection := by
  have : T.range.HasOrthogonalProjection := hT.hasOrthogonalProjection_range
  ext x
  have hmem : T x ∈ T.range := LinearMap.mem_range_self _ x
  have hproj : T.range.orthogonalProjectionOnto (T x) = ⟨T x, hmem⟩ :=
    T.range.orthogonalProjectionOnto_mem_subspace_eq_self ⟨T x, hmem⟩
  have hsub : T ((T.ker)ᗮ.orthogonalProjectionOnto x : E) = T x :=
    congr($T.comp_starProjection_orthogonal_ker x)
  have heq : (T.orthogonalKerEquivRange hT.isClosed_range).symm ⟨T x, hmem⟩ =
      (T.ker)ᗮ.orthogonalProjectionOnto x := by
    apply (T.orthogonalKerEquivRange hT.isClosed_range).injective
    apply Subtype.ext
    rw [(T.orthogonalKerEquivRange hT.isClosed_range).apply_symm_apply,
      T.orthogonalKerEquivRange_apply, hsub]
  rw [hT.orthogonalFredholmPackage_quasiInverse_eq]
  simp [hproj, heq]

/-- Pointwise form of `orthogonalFredholmPackage_quasiInverse_comp_self`. -/
@[simp]
theorem IsFredholm.orthogonalFredholmPackage_quasiInverse_apply_self (hT : T.IsFredholm) (x : E) :
    hT.orthogonalFredholmPackage.quasiInverse (T x) = (T.ker)ᗮ.starProjection x := by
  rw [← comp_apply, hT.orthogonalFredholmPackage_quasiInverse_comp_self]

/-- The defect `id - Q ∘L T` of the orthogonal quasi-inverse on the domain is the orthogonal
projection onto `ker T`. -/
theorem IsFredholm.id_sub_orthogonalFredholmPackage_quasiInverse_comp_self (hT : T.IsFredholm) :
    .id 𝕜 E - hT.orthogonalFredholmPackage.quasiInverse ∘L T = T.ker.starProjection := by
  rw [hT.orthogonalFredholmPackage_quasiInverse_comp_self, Submodule.starProjection_orthogonal,
    sub_sub_cancel]

/-- Postcomposing the orthogonal quasi-inverse with `T` gives the orthogonal projection onto
`range T`. -/
@[simp]
theorem IsFredholm.self_comp_orthogonalFredholmPackage_quasiInverse (hT : T.IsFredholm)
    [T.range.HasOrthogonalProjection] :
    T ∘L hT.orthogonalFredholmPackage.quasiInverse = T.range.starProjection := by
  rw [hT.orthogonalFredholmPackage_quasiInverse_eq]
  ext y
  simp

/-- Pointwise form of `self_comp_orthogonalFredholmPackage_quasiInverse`. -/
@[simp]
theorem IsFredholm.apply_orthogonalFredholmPackage_quasiInverse (hT : T.IsFredholm)
    [T.range.HasOrthogonalProjection] (y : F) :
    T (hT.orthogonalFredholmPackage.quasiInverse y) = T.range.starProjection y := by
  rw [← comp_apply, hT.self_comp_orthogonalFredholmPackage_quasiInverse]

/-- The defect `id - T ∘L Q` of the orthogonal quasi-inverse on the codomain is the orthogonal
projection onto `ker T†`. -/
theorem IsFredholm.id_sub_self_comp_orthogonalFredholmPackage_quasiInverse (hT : T.IsFredholm) :
    .id 𝕜 F - T ∘L hT.orthogonalFredholmPackage.quasiInverse = ((T†).ker).starProjection := by
  have : T.range.HasOrthogonalProjection := hT.hasOrthogonalProjection_range
  rw [hT.self_comp_orthogonalFredholmPackage_quasiInverse, T.starProjection_ker_adjoint,
    Submodule.starProjection_orthogonal]

/-- **Moore–Penrose characterization of the orthogonal quasi-inverse.** For a Fredholm operator `T`
between Hilbert spaces, `hT.orthogonalFredholmPackage.quasiInverse` satisfies all four Penrose
equations for `T`. -/
theorem IsFredholm.isMoorePenroseInverse_orthogonalFredholmPackage_quasiInverse
    (hT : T.IsFredholm) :
    LinearMap.IsMoorePenroseInverse (T : E →ₗ[𝕜] F)
      (hT.orthogonalFredholmPackage.quasiInverse : F →ₗ[𝕜] E) := by
  have : T.range.HasOrthogonalProjection := hT.hasOrthogonalProjection_range
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← ContinuousLinearMap.toLinearMap_comp, ← ContinuousLinearMap.toLinearMap_comp,
      hT.orthogonalFredholmPackage_quasiInverse_comp_self, T.comp_starProjection_orthogonal_ker]
  · refine LinearMap.ext fun y ↦ ?_
    exact congr($hT.orthogonalFredholmPackage_quasiInverse_comp_self
        (hT.orthogonalFredholmPackage.quasiInverse y)).trans
      (Submodule.starProjection_eq_self_iff.mpr
        (hT.orthogonalFredholmPackage_quasiInverse_apply_mem_orthogonal_ker y))
  · rw [← ContinuousLinearMap.toLinearMap_comp,
      hT.self_comp_orthogonalFredholmPackage_quasiInverse]
    exact T.range.starProjection_isSymmetric
  · rw [← ContinuousLinearMap.toLinearMap_comp,
      hT.orthogonalFredholmPackage_quasiInverse_comp_self]
    exact (T.ker)ᗮ.starProjection_isSymmetric

/-- Taking the Hilbert adjoint commutes with forming the canonical orthogonal quasi-inverse of a
Fredholm operator. -/
@[simp]
theorem IsFredholm.adjoint_orthogonalFredholmPackage_quasiInverse (hT : T.IsFredholm) :
    (hT.orthogonalFredholmPackage.quasiInverse)† =
      hT.adjoint.orthogonalFredholmPackage.quasiInverse :=
  ContinuousLinearMap.coe_inj.mp <|
    (isMoorePenroseInverse_adjoint
      hT.isMoorePenroseInverse_orthogonalFredholmPackage_quasiInverse).unique
        hT.adjoint.isMoorePenroseInverse_orthogonalFredholmPackage_quasiInverse

end OrthogonalPackage

end ContinuousLinearMap

end
