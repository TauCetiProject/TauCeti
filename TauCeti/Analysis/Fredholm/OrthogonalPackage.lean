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
quasi-inverse. On general Banach spaces these splittings require a noncanonical choice of
topological complements to the kernel and range.

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
adjoints commutes with forming the canonical orthogonal quasi-inverse, and the quasi-inverse is
itself Fredholm of opposite index.

## Main declarations

* `ContinuousLinearMap.projectionOntoL_orthogonal_ker_eq_orthogonalProjectionOnto`,
  `ContinuousLinearMap.projectionOntoL_range_ker_adjoint_eq_orthogonalProjectionOnto`,
  `ContinuousLinearMap.projectionOntoL_ker_adjoint_range_eq_orthogonalProjectionOnto`: the
  topological projections associated to `E = (ker T)ᗮ ⊕ ker T` and `F = range T ⊕ ker T†` agree
  with the Hilbert-space orthogonal projections.
* `ContinuousLinearMap.IsFredholm.orthogonalFredholmPackage`: the canonical `FredholmPackage`
  built from the orthogonal splittings `E = (ker T)ᗮ ⊕ ker T` and `F = range T ⊕ ker T†`.
* `ContinuousLinearMap.IsFredholm.orthogonalFredholmPackage_quasiInverse_comp_self` and
  `ContinuousLinearMap.IsFredholm.self_comp_orthogonalFredholmPackage_quasiInverse`: the two
  products of `T` with its orthogonal quasi-inverse are `(ker T)ᗮ.starProjection` and
  `(range T).starProjection`.
* `ContinuousLinearMap.IsFredholm.isMoorePenroseInverse_orthogonalFredholmPackage_quasiInverse`:
  the orthogonal quasi-inverse satisfies the four Penrose equations.
* `ContinuousLinearMap.IsFredholm.adjoint_orthogonalFredholmPackage_quasiInverse`: taking the
  Hilbert adjoint commutes with forming the orthogonal quasi-inverse.
* `ContinuousLinearMap.IsFredholm.index_orthogonalFredholmPackage_quasiInverse`: the orthogonal
  quasi-inverse is Fredholm of index `-T.index`.

## References

* N. Bourbaki, *Théories Spectrales*, Chapitre III, §3, n° 2.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix A.1.
-/

public section

open Module Submodule
open scoped InnerProduct

namespace ContinuousLinearMap

section OrthogonalProjections

variable {𝕜 : Type*} [RCLike 𝕜]

/-- When two topological complements in an inner product space are mutually orthogonal, the
continuous projection onto the first along the second is the orthogonal projection. -/
private theorem projectionOntoL_eq_orthogonalProjectionOnto_of_isOrtho
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    {U V : Submodule 𝕜 H} [U.HasOrthogonalProjection]
    (hUV : U.IsTopCompl V) (h_ortho : U ⟂ V) :
    U.projectionOntoL V hUV = U.orthogonalProjectionOnto := by
  refine ContinuousLinearMap.coe_inj.mp <| LinearMap.ext_on_codisjoint hUV.isCompl.codisjoint ?_ ?_
  · intro u hu
    exact (U.projectionOntoL_apply_left hUV ⟨u, hu⟩).trans
      (U.orthogonalProjectionOnto_mem_subspace_eq_self ⟨u, hu⟩).symm
  · intro v hv
    exact (U.projectionOntoL_apply_eq_zero_of_mem_right hUV hv).trans
      (Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal (h_ortho.symm hv)).symm

section Domain

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [TopologicalSpace F] [AddCommMonoid F] [Module 𝕜 F]

/-- The topological projection onto `(ker T)ᗮ` along `ker T` agrees with the Hilbert-space
orthogonal projection onto `(ker T)ᗮ`. -/
theorem projectionOntoL_orthogonal_ker_eq_orthogonalProjectionOnto
    (T : E →L[𝕜] F) [T.ker.HasOrthogonalProjection] :
    (T.ker)ᗮ.projectionOntoL T.ker T.ker.isTopCompl_orthogonal.symm =
      (T.ker)ᗮ.orthogonalProjectionOnto :=
  projectionOntoL_eq_orthogonalProjectionOnto_of_isOrtho
    T.ker.isTopCompl_orthogonal.symm T.ker.isOrtho_orthogonal_left

end Domain

section Codomain

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- For a closed-range operator between Hilbert spaces, the topological projection onto `range T`
along `ker T†` agrees with the orthogonal projection onto `range T`. -/
theorem projectionOntoL_range_ker_adjoint_eq_orthogonalProjectionOnto {T : E →L[𝕜] F}
    (hT : IsClosed (T.range : Set F)) [T.range.HasOrthogonalProjection] :
    T.range.projectionOntoL (T†).ker (T.isTopCompl_range_ker_adjoint hT) =
      T.range.orthogonalProjectionOnto := by
  refine projectionOntoL_eq_orthogonalProjectionOnto_of_isOrtho
    (T.isTopCompl_range_ker_adjoint hT) ?_
  rw [← T.orthogonal_range]
  exact T.range.isOrtho_orthogonal_right

/-- For a closed-range operator between Hilbert spaces, the topological projection onto `ker T†`
along `range T` agrees with the orthogonal projection onto `ker T†`. -/
theorem projectionOntoL_ker_adjoint_range_eq_orthogonalProjectionOnto {T : E →L[𝕜] F}
    (hT : IsClosed (T.range : Set F)) :
    ((T†).ker).projectionOntoL T.range (T.isTopCompl_range_ker_adjoint hT).symm =
      ((T†).ker).orthogonalProjectionOnto := by
  refine projectionOntoL_eq_orthogonalProjectionOnto_of_isOrtho
    (T.isTopCompl_range_ker_adjoint hT).symm ?_
  rw [← T.orthogonal_range]
  exact T.range.isOrtho_orthogonal_left

end Codomain

end OrthogonalProjections

section OrthogonalPackage

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  {T : E →L[𝕜] F}

/-- The range of a Fredholm operator into a Hilbert space admits an orthogonal projection. -/
theorem IsFredholm.hasOrthogonalProjection_range {G : Type*} [NormedAddCommGroup G]
    [NormedSpace 𝕜 G] {S : G →L[𝕜] F} (hS : S.IsFredholm) :
    S.range.HasOrthogonalProjection :=
  Submodule.hasOrthogonalProjection_iff_isClosed.mpr hS.isClosed_range

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

/-- Every Fredholm package for `T` shares the inessential domain summand `ker T` with the canonical
orthogonal package. -/
theorem FredholmPackage.decDom_X₀_eq_orthogonalFredholmPackage (pkg : T.FredholmPackage)
    (hT : T.IsFredholm) :
    pkg.decDom.X₀ = hT.orthogonalFredholmPackage.decDom.X₀ :=
  pkg.ker_eq.symm

/-- Every Fredholm package for `T` shares the essential codomain summand `range T` with the
canonical orthogonal package. -/
theorem FredholmPackage.decCodom_X₁_eq_orthogonalFredholmPackage (pkg : T.FredholmPackage)
    (hT : T.IsFredholm) :
    pkg.decCodom.X₁ = hT.orthogonalFredholmPackage.decCodom.X₁ :=
  pkg.range_eq.symm

/-- The domain projection of the orthogonal Fredholm package is the orthogonal projection onto
`(ker T)ᗮ`. -/
@[simp]
theorem IsFredholm.orthogonalFredholmPackage_decDom_proj (hT : T.IsFredholm) :
    hT.orthogonalFredholmPackage.decDom.proj = (T.ker)ᗮ.orthogonalProjectionOnto :=
  T.projectionOntoL_orthogonal_ker_eq_orthogonalProjectionOnto

/-- The codomain projection of the orthogonal Fredholm package is the orthogonal projection onto
`range T`. -/
@[simp]
theorem IsFredholm.orthogonalFredholmPackage_decCodom_proj (hT : T.IsFredholm)
    [T.range.HasOrthogonalProjection] :
    hT.orthogonalFredholmPackage.decCodom.proj = T.range.orthogonalProjectionOnto :=
  T.projectionOntoL_range_ker_adjoint_eq_orthogonalProjectionOnto hT.isClosed_range

/-- For any bounded operator `T : E →L[𝕜] F` between Hilbert spaces, the orthogonal projection onto
`ker T†` equals the orthogonal projection onto `(range T)ᗮ`. -/
theorem starProjection_ker_adjoint (T : E →L[𝕜] F) :
    ((T†).ker).starProjection = T.rangeᗮ.starProjection := by
  ext y
  exact Submodule.eq_starProjection_of_mem_orthogonal
    (T.orthogonal_range ▸ T.rangeᗮ.starProjection_apply_mem y)
    (T.orthogonal_range ▸ T.rangeᗮ.sub_starProjection_mem_orthogonal y)

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
  ext y
  have heq : ∀ z : T.range,
      hT.orthogonalFredholmPackage.equiv.symm z =
        (T.orthogonalKerEquivRange hT.isClosed_range).symm z :=
    fun z ↦ congrArg (·.symm z) hT.orthogonalFredholmPackage_equiv
  have hproj : hT.orthogonalFredholmPackage.decCodom.proj y = T.range.orthogonalProjectionOnto y :=
    congr($hT.orthogonalFredholmPackage_decCodom_proj y)
  exact congrArg Subtype.val ((heq _).trans (congrArg _ hproj))

/-- The canonical quasi-inverse from the orthogonal Fredholm package vanishes on `ker T†`. -/
@[simp]
theorem IsFredholm.orthogonalFredholmPackage_quasiInverse_apply_of_mem_ker_adjoint
    (hT : T.IsFredholm) {y : F} (hy : y ∈ (T†).ker) :
    hT.orthogonalFredholmPackage.quasiInverse y = 0 := by
  have : T.range.HasOrthogonalProjection := hT.hasOrthogonalProjection_range
  have hy' : y ∈ T.rangeᗮ := T.orthogonal_range.symm ▸ hy
  rw [hT.orthogonalFredholmPackage_quasiInverse_eq]
  simp [Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hy']

/-- Restricting the orthogonal quasi-inverse to `ker T†` gives the zero operator. -/
@[simp]
theorem IsFredholm.orthogonalFredholmPackage_quasiInverse_comp_subtypeL_ker_adjoint
    (hT : T.IsFredholm) :
    hT.orthogonalFredholmPackage.quasiInverse ∘L (T†).ker.subtypeL = 0 := by
  ext y
  exact hT.orthogonalFredholmPackage_quasiInverse_apply_of_mem_ker_adjoint y.2

/-- Every value of the orthogonal quasi-inverse lies in `(ker T)ᗮ`. -/
@[simp]
theorem IsFredholm.orthogonalFredholmPackage_quasiInverse_apply_mem_orthogonal_ker
    (hT : T.IsFredholm) (y : F) :
    hT.orthogonalFredholmPackage.quasiInverse y ∈ (T.ker)ᗮ :=
  Subtype.coe_prop _

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

/-- The defect `id - T ∘L Q` of the orthogonal quasi-inverse on the codomain is the orthogonal
projection onto `ker T†`. -/
theorem IsFredholm.id_sub_self_comp_orthogonalFredholmPackage_quasiInverse (hT : T.IsFredholm) :
    .id 𝕜 F - T ∘L hT.orthogonalFredholmPackage.quasiInverse = ((T†).ker).starProjection := by
  have : T.range.HasOrthogonalProjection := hT.hasOrthogonalProjection_range
  rw [hT.self_comp_orthogonalFredholmPackage_quasiInverse, T.starProjection_ker_adjoint,
    Submodule.starProjection_orthogonal]

/-- The range of the orthogonal quasi-inverse is `(ker T)ᗮ`. -/
@[simp]
theorem IsFredholm.range_orthogonalFredholmPackage_quasiInverse (hT : T.IsFredholm) :
    hT.orthogonalFredholmPackage.quasiInverse.range = (T.ker)ᗮ := by
  refine le_antisymm ?_ fun x hx ↦ ?_
  · rintro _ ⟨y, rfl⟩
    exact hT.orthogonalFredholmPackage_quasiInverse_apply_mem_orthogonal_ker y
  · refine ⟨T x, ?_⟩
    exact congr($hT.orthogonalFredholmPackage_quasiInverse_comp_self x).trans
      (Submodule.starProjection_eq_self_iff.mpr hx)

/-- The kernel of the orthogonal quasi-inverse is `ker T†`. -/
@[simp]
theorem IsFredholm.ker_orthogonalFredholmPackage_quasiInverse (hT : T.IsFredholm) :
    hT.orthogonalFredholmPackage.quasiInverse.ker = (T†).ker := by
  refine le_antisymm (fun y hy ↦ ?_) fun y hy ↦
    hT.orthogonalFredholmPackage_quasiInverse_apply_of_mem_ker_adjoint hy
  have hy' : hT.orthogonalFredholmPackage.quasiInverse y = 0 := LinearMap.mem_ker.mp hy
  have hy0 : T (hT.orthogonalFredholmPackage.quasiInverse y) = 0 := by rw [hy', map_zero]
  have hproj := congr($hT.id_sub_self_comp_orthogonalFredholmPackage_quasiInverse y)
  simp only [sub_apply, id_apply, comp_apply, hy0, sub_zero] at hproj
  exact hproj ▸ Submodule.starProjection_apply_mem ((T†).ker) y

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

/-- For bounded operators between Hilbert spaces, the Moore–Penrose relation is preserved by taking
Hilbert adjoints. -/
theorem isMoorePenroseInverse_adjoint {A : E →L[𝕜] F} {B : F →L[𝕜] E}
    (h : LinearMap.IsMoorePenroseInverse (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E)) :
    LinearMap.IsMoorePenroseInverse (A† : F →ₗ[𝕜] E) (B† : E →ₗ[𝕜] F) where
  comp_comp_self := by
    have h1 : A ∘L B ∘L A = A := ContinuousLinearMap.coe_inj.mp h.comp_comp_self
    rw [← ContinuousLinearMap.toLinearMap_comp, ← ContinuousLinearMap.toLinearMap_comp]
    exact congrArg ContinuousLinearMap.toLinearMap <|
      calc A† ∘L B† ∘L A† = (A ∘L B ∘L A)† := by simp [ContinuousLinearMap.comp_assoc]
        _ = A† := congrArg ContinuousLinearMap.adjoint h1
  comp_comp_self' := by
    have h2 : B ∘L A ∘L B = B := ContinuousLinearMap.coe_inj.mp h.comp_comp_self'
    rw [← ContinuousLinearMap.toLinearMap_comp, ← ContinuousLinearMap.toLinearMap_comp]
    exact congrArg ContinuousLinearMap.toLinearMap <|
      calc B† ∘L A† ∘L B† = (B ∘L A ∘L B)† := by simp [ContinuousLinearMap.comp_assoc]
        _ = B† := congrArg ContinuousLinearMap.adjoint h2
  isSymmetric_comp := by
    have hBA : IsSelfAdjoint (B ∘L A) :=
      (B ∘L A).isSelfAdjoint_iff_isSymmetric.mpr h.isSymmetric_comp'
    have h3 : A† ∘L B† = B ∘L A := (ContinuousLinearMap.adjoint_comp B A).symm.trans hBA.adjoint_eq
    rw [← ContinuousLinearMap.toLinearMap_comp, h3]
    exact h.isSymmetric_comp'
  isSymmetric_comp' := by
    have hAB : IsSelfAdjoint (A ∘L B) :=
      (A ∘L B).isSelfAdjoint_iff_isSymmetric.mpr h.isSymmetric_comp
    have h4 : B† ∘L A† = A ∘L B := (ContinuousLinearMap.adjoint_comp A B).symm.trans hAB.adjoint_eq
    rw [← ContinuousLinearMap.toLinearMap_comp, h4]
    exact h.isSymmetric_comp

/-- For bounded operators between Hilbert spaces, `B†` is a Moore–Penrose inverse of `A†` if and
only if `B` is a Moore–Penrose inverse of `A`. -/
@[simp]
theorem isMoorePenroseInverse_adjoint_iff {A : E →L[𝕜] F} {B : F →L[𝕜] E} :
    LinearMap.IsMoorePenroseInverse (A† : F →ₗ[𝕜] E) (B† : E →ₗ[𝕜] F) ↔
      LinearMap.IsMoorePenroseInverse (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E) :=
  ⟨fun h ↦ by simpa using isMoorePenroseInverse_adjoint h, isMoorePenroseInverse_adjoint⟩

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

/-- The canonical orthogonal quasi-inverse of a Fredholm operator is itself Fredholm. -/
theorem IsFredholm.isFredholm_orthogonalFredholmPackage_quasiInverse (hT : T.IsFredholm) :
    hT.orthogonalFredholmPackage.quasiInverse.IsFredholm :=
  IsFredholm.of_isQuasiInverse hT.orthogonalFredholmPackage.isQuasiInverse.symm

/-- The canonical orthogonal quasi-inverse of a Fredholm operator has opposite Fredholm index. -/
@[simp]
theorem IsFredholm.index_orthogonalFredholmPackage_quasiInverse (hT : T.IsFredholm) :
    hT.orthogonalFredholmPackage.quasiInverse.index = -T.index := by
  rw [ContinuousLinearMap.index_eq_finrank_sub, ContinuousLinearMap.index_eq_finrank_sub,
    hT.ker_orthogonalFredholmPackage_quasiInverse,
    hT.range_orthogonalFredholmPackage_quasiInverse,
    ← LinearEquiv.finrank_eq (T.cokerEquivKerAdjoint hT.isClosed_range).toLinearEquiv,
    LinearEquiv.finrank_eq
      ((T.ker)ᗮ.quotientEquivOfIsCompl T.ker T.ker.isCompl_orthogonal.symm)]
  omega

end OrthogonalPackage

end ContinuousLinearMap

end
