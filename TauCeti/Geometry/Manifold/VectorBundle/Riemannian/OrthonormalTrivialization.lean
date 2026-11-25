/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.OrthonormalTrivialization
public import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization
public import TauCeti.Geometry.Manifold.VectorBundle.GramSchmidt
public import Mathlib.Geometry.Manifold.Diffeomorph
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Coordinates
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Regularity

/-!
# Smooth orthonormal trivializations of Riemannian vector bundles

Given a `C^n` Riemannian vector bundle `E → B` (whose model fibre `F` need only be a real normed
space) and a pointwise orthonormal basis `d b` of each fibre `E b` whose basis vectors are `C^n`
sections, reading coordinates in `d` defines a `C^n` diffeomorphism
`TauCeti.orthonormalBasisTotalSpaceEuclideanDiffeomorph` between `TotalSpace F E` and
`B × EuclideanSpace ℝ ι` that is a linear isometry on every fibre. Unlike general frame
trivializations (`IsLocalFrameOn.trivialization`), no operator inversion is needed: the forward map
takes Riemannian inner products `⟪d b i, v⟫_ℝ`, and the inverse reconstructs vectors by finite
linear combinations `∑ i, y i • d b i`. Both directions work without change in rank zero (`ι`
empty).

When the model fibre `F` is a real inner product space carrying a fixed orthonormal basis `c`,
composing with `c.repr.symm` gives a `C^n` diffeomorphism `OrthonormalBasis.totalSpaceDiffeomorph`
onto `B × F` agreeing everywhere with the global topological chart
`OrthonormalBasis.bundleTrivialization`. Locally over an open set `U`,
`OrthonormalBasis.bundleTrivialization` agrees on `U` with the frame trivialization of the
underlying `C^n` local frame, and therefore belongs to the maximal atlas of `C^n` fiberwise linear
trivializations (`OrthonormalBasis.bundleTrivialization_mem_maximalAtlas`). In particular, the
Gram–Schmidt orthogonalization `Bundle.Trivialization.orthonormal` of any compatible linear local
trivialization in the `C^n` maximal atlas lies in the `C^n` maximal atlas
(`Bundle.Trivialization.orthonormal_mem_maximalAtlas`).

## Main definitions

* `TauCeti.orthonormalBasisTotalSpaceEuclideanDiffeomorph`: `C^n` diffeomorphism
  `TotalSpace F E ≃ₘ^n B × EuclideanSpace ℝ ι` induced by a `C^n` global orthonormal basis `d`.
* `TauCeti.orthonormalFrameDiffeomorph`: `C^n` diffeomorphism
  `TotalSpace F E ≃ₘ^n B × EuclideanSpace ℝ ι` built directly from a `C^n` orthonormal frame.
* `OrthonormalBasis.totalSpaceDiffeomorph`: `C^n` diffeomorphism `TotalSpace F E ≃ₘ^n B × F`
  sending `d b` to a model orthonormal basis `c`.

## Main results

* `OrthonormalBasis.bundleTrivialization_mem_maximalAtlas`,
  `OrthonormalBasis.bundleTrivialization_univ_mem_maximalAtlas`: the local or global chart of a
  `C^n` orthonormal basis lies in
  `(contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F E)`.
* `Bundle.Trivialization.orthonormal_mem_maximalAtlas`: Gram–Schmidt orthogonalization of any linear
  trivialization in `(contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F E)` also lies in
  that maximal atlas.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §2.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 10.
-/

public section

noncomputable section

open Bundle Set TauCeti
open scoped Manifold ContDiff Topology InnerProductSpace

namespace TauCeti

section RCLikeLocal

variable {𝕜 : Type*} [RCLike 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace 𝕜 (E b)]
  [FiberBundle F E] {n : ℕ∞ω} {ι : Type*} [Fintype ι]

open scoped Classical in
/-- A family of orthonormal bases over `U` whose zero-extended sections are `C^n` on `U` forms a
`C^n` local frame on `U`. -/
theorem isLocalFrameOn_of_orthonormalBasis {U : Set B}
    (d : ∀ b : U, OrthonormalBasis ι 𝕜 (E b))
    (hd : ∀ i, ContMDiffOn IB (IB.prod 𝓘(𝕜, F)) n
      (fun b ↦ TotalSpace.mk' F b (if hb : b ∈ U then d ⟨b, hb⟩ i else 0)) U) :
    IsLocalFrameOn IB F n
      (fun i b ↦ if hb : b ∈ U then d ⟨b, hb⟩ i else 0) U := by
  have hfun : ∀ {b : B} (hb : b ∈ U),
      (fun i ↦ (if hb' : b ∈ U then d ⟨b, hb'⟩ i else 0 : E b)) =
        fun i ↦ (d ⟨b, hb⟩).toBasis i := fun {b} hb ↦ by
    funext i
    simp only [hb, ↓reduceDIte, OrthonormalBasis.coe_toBasis]
  exact
    { linearIndependent := fun {b} hb ↦ by
        rw [hfun hb]
        exact (d ⟨b, hb⟩).toBasis.linearIndependent
      generating := fun {b} hb ↦ by
        rw [hfun hb]
        exact (d ⟨b, hb⟩).toBasis.span_eq.ge
      contMDiffOn := hd }

open scoped Classical in
/-- Restricting `C^n` zero-extended orthonormal-basis sections to `U` gives the continuous subtype
sections consumed by `OrthonormalBasis.bundleTrivialization`. -/
theorem continuous_of_contMDiffOn_orthonormalBasis {U : Set B}
    (d : ∀ b : U, OrthonormalBasis ι 𝕜 (E b))
    (hd : ∀ i, ContMDiffOn IB (IB.prod 𝓘(𝕜, F)) n
      (fun b ↦ TotalSpace.mk' F b (if hb : b ∈ U then d ⟨b, hb⟩ i else 0)) U) (i : ι) :
    Continuous fun b : U ↦ TotalSpace.mk' F (b : B) (d b i) :=
  ((hd i).continuousOn.comp_continuous continuous_subtypeVal fun b ↦ b.property).congr fun b ↦
    congrArg (TotalSpace.mk' F (b : B)) (by simp [b.property])

end RCLikeLocal

end TauCeti

section RealBundle

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  {n : ℕ∞ω} {ι : Type*} [Fintype ι]

namespace TauCeti

/-- Reading coordinates in a `C^n` global orthonormal basis defines a `C^n` map from
`TotalSpace F E` to `EuclideanSpace ℝ ι`. -/
theorem contMDiff_orthonormalBasis_repr_totalSpace [IsContMDiffRiemannianBundle IB n F E]
    (d : ∀ b : B, OrthonormalBasis ι ℝ (E b))
    (hd : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (d b i))) :
    ContMDiff (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, EuclideanSpace ℝ ι) n
      (fun p : TotalSpace F E ↦ (d p.proj).repr p.snd) := by
  have hpi : ContMDiff (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, ι → ℝ) n
      (fun p : TotalSpace F E ↦ fun i ↦ ⟪d p.proj i, p.snd⟫_ℝ) :=
    contMDiff_pi_module_iff.mpr fun i ↦
      ((hd i).comp (Bundle.contMDiff_proj E)).inner_bundle contMDiff_id
  refine ((EuclideanSpace.equiv ι ℝ).symm.contDiff.comp_contMDiff hpi).congr fun p ↦ ?_
  ext i
  exact (d p.proj).repr_apply_apply p.snd i

/-- Reconstructing fibre vectors from `EuclideanSpace ℝ ι` coordinates in a `C^n` global
orthonormal basis defines a `C^n` map into `TotalSpace F E`. -/
theorem contMDiff_orthonormalBasis_repr_symm_totalSpace
    (d : ∀ b : B, OrthonormalBasis ι ℝ (E b))
    (hd : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (d b i))) :
    ContMDiff (IB.prod 𝓘(ℝ, EuclideanSpace ℝ ι)) (IB.prod 𝓘(ℝ, F)) n
      (fun p : B × EuclideanSpace ℝ ι ↦ TotalSpace.mk' F p.1 ((d p.1).repr.symm p.2)) := by
  have hsum : ContMDiff (IB.prod 𝓘(ℝ, EuclideanSpace ℝ ι)) (IB.prod 𝓘(ℝ, F)) n
      (fun p : B × EuclideanSpace ℝ ι ↦ TotalSpace.mk' F p.1 (∑ i, p.2 i • d p.1 i)) :=
    ContMDiff.sum_sectionAlong Finset.univ (fun i (p : B × EuclideanSpace ℝ ι) ↦ p.2 i • d p.1 i)
      contMDiff_fst fun i _ ↦
        ((EuclideanSpace.proj i).contDiff.comp_contMDiff contMDiff_snd).smul_totalSpace
          ((hd i).comp contMDiff_fst)
  exact hsum.congr fun p ↦ congrArg (TotalSpace.mk' F p.1) ((d p.1).sum_repr_symm p.2).symm

section EuclideanDiffeomorph

variable [IsContMDiffRiemannianBundle IB n F E]

/-- A `C^n` global orthonormal basis `d` of a `C^n` Riemannian vector bundle induces a `C^n`
diffeomorphism between `TotalSpace F E` and `B × EuclideanSpace ℝ ι` acting as `(d b).repr` on
each fibre. -/
def orthonormalBasisTotalSpaceEuclideanDiffeomorph
    (d : ∀ b : B, OrthonormalBasis ι ℝ (E b))
    (hd : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (d b i))) :
    TotalSpace F E ≃ₘ^n⟮IB.prod 𝓘(ℝ, F), IB.prod 𝓘(ℝ, EuclideanSpace ℝ ι)⟯
      B × EuclideanSpace ℝ ι where
  toFun p := (p.proj, (d p.proj).repr p.snd)
  invFun p := ⟨p.1, (d p.1).repr.symm p.2⟩
  left_inv p := by cases p; simp
  right_inv p := by cases p; simp
  contMDiff_toFun := (Bundle.contMDiff_proj E).prodMk
    (contMDiff_orthonormalBasis_repr_totalSpace d hd)
  contMDiff_invFun := contMDiff_orthonormalBasis_repr_symm_totalSpace d hd

@[simp]
theorem orthonormalBasisTotalSpaceEuclideanDiffeomorph_apply
    (d : ∀ b : B, OrthonormalBasis ι ℝ (E b))
    (hd : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (d b i)))
    (b : B) (v : E b) :
    orthonormalBasisTotalSpaceEuclideanDiffeomorph d hd ⟨b, v⟩ = (b, (d b).repr v) :=
  (rfl)

@[simp]
theorem orthonormalBasisTotalSpaceEuclideanDiffeomorph_fst
    (d : ∀ b : B, OrthonormalBasis ι ℝ (E b))
    (hd : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (d b i)))
    (p : TotalSpace F E) :
    (orthonormalBasisTotalSpaceEuclideanDiffeomorph d hd p).1 = p.proj :=
  (rfl)

/-- Each coordinate of `TauCeti.orthonormalBasisTotalSpaceEuclideanDiffeomorph` is the Riemannian
inner product with the corresponding frame vector. -/
theorem orthonormalBasisTotalSpaceEuclideanDiffeomorph_snd_apply
    (d : ∀ b : B, OrthonormalBasis ι ℝ (E b))
    (hd : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (d b i)))
    (b : B) (v : E b) (i : ι) :
    (orthonormalBasisTotalSpaceEuclideanDiffeomorph d hd ⟨b, v⟩).2 i = ⟪d b i, v⟫_ℝ :=
  (d b).repr_apply_apply v i

@[simp]
theorem orthonormalBasisTotalSpaceEuclideanDiffeomorph_symm_apply
    (d : ∀ b : B, OrthonormalBasis ι ℝ (E b))
    (hd : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (d b i)))
    (b : B) (y : EuclideanSpace ℝ ι) :
    (orthonormalBasisTotalSpaceEuclideanDiffeomorph d hd).symm (b, y) = ⟨b, (d b).repr.symm y⟩ :=
  (rfl)

/-- The inverse of `TauCeti.orthonormalBasisTotalSpaceEuclideanDiffeomorph` expands coordinates as
a finite linear combination in `d b`. -/
theorem orthonormalBasisTotalSpaceEuclideanDiffeomorph_symm_eq_sum
    (d : ∀ b : B, OrthonormalBasis ι ℝ (E b))
    (hd : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (d b i)))
    (b : B) (y : EuclideanSpace ℝ ι) :
    (orthonormalBasisTotalSpaceEuclideanDiffeomorph d hd).symm (b, y) = ⟨b, ∑ i, y i • d b i⟩ :=
  congrArg (TotalSpace.mk' F b) ((d b).sum_repr_symm y).symm

@[simp]
theorem norm_orthonormalBasisTotalSpaceEuclideanDiffeomorph_snd
    (d : ∀ b : B, OrthonormalBasis ι ℝ (E b))
    (hd : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (d b i)))
    (p : TotalSpace F E) :
    ‖(orthonormalBasisTotalSpaceEuclideanDiffeomorph d hd p).2‖ = ‖p.snd‖ :=
  (d p.proj).repr.norm_map p.snd

/-- `TauCeti.orthonormalBasisTotalSpaceEuclideanDiffeomorph` preserves the inner product on each
fibre. -/
theorem inner_orthonormalBasisTotalSpaceEuclideanDiffeomorph_snd
    (d : ∀ b : B, OrthonormalBasis ι ℝ (E b))
    (hd : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (d b i)))
    (b : B) (v w : E b) :
    ⟪(orthonormalBasisTotalSpaceEuclideanDiffeomorph d hd ⟨b, v⟩).2,
      (orthonormalBasisTotalSpaceEuclideanDiffeomorph d hd ⟨b, w⟩).2⟫_ℝ = ⟪v, w⟫_ℝ :=
  (d b).repr.inner_map_map v w

end EuclideanDiffeomorph

section OrthonormalFrame

variable [FiniteDimensional ℝ F] [IsContMDiffRiemannianBundle IB n F E]

/-- A `C^n` global orthonormal frame of a `C^n` Riemannian vector bundle with cardinality
`finrank ℝ F` induces a `C^n` diffeomorphism `TotalSpace F E ≃ₘ^n B × EuclideanSpace ℝ ι`. -/
def orthonormalFrameDiffeomorph
    {v : ι → ∀ b : B, E b}
    (hv : ∀ b, Orthonormal ℝ (fun i ↦ v i b))
    (hrank : Fintype.card ι = Module.finrank ℝ F)
    (hsmooth : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (v i b))) :
    TotalSpace F E ≃ₘ^n⟮IB.prod 𝓘(ℝ, F), IB.prod 𝓘(ℝ, EuclideanSpace ℝ ι)⟯
      B × EuclideanSpace ℝ ι :=
  orthonormalBasisTotalSpaceEuclideanDiffeomorph
    (orthonormalBasisOfOrthonormalSections hv hrank) fun i ↦ by
      simpa only [orthonormalBasisOfOrthonormalSections_apply] using hsmooth i

/-- `TauCeti.orthonormalFrameDiffeomorph` unfolds to
`TauCeti.orthonormalBasisTotalSpaceEuclideanDiffeomorph` applied to
`TauCeti.orthonormalBasisOfOrthonormalSections`. -/
theorem orthonormalFrameDiffeomorph_def
    {v : ι → ∀ b : B, E b}
    (hv : ∀ b, Orthonormal ℝ (fun i ↦ v i b))
    (hrank : Fintype.card ι = Module.finrank ℝ F)
    (hsmooth : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (v i b))) :
    orthonormalFrameDiffeomorph hv hrank hsmooth =
      orthonormalBasisTotalSpaceEuclideanDiffeomorph
        (orthonormalBasisOfOrthonormalSections hv hrank) (fun i ↦ by
          simpa only [orthonormalBasisOfOrthonormalSections_apply] using hsmooth i) :=
  (rfl)

@[simp]
theorem orthonormalFrameDiffeomorph_fst
    {v : ι → ∀ b : B, E b}
    (hv : ∀ b, Orthonormal ℝ (fun i ↦ v i b))
    (hrank : Fintype.card ι = Module.finrank ℝ F)
    (hsmooth : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (v i b)))
    (p : TotalSpace F E) :
    (orthonormalFrameDiffeomorph hv hrank hsmooth p).1 = p.proj :=
  orthonormalBasisTotalSpaceEuclideanDiffeomorph_fst _ _ p

@[simp]
theorem orthonormalFrameDiffeomorph_snd_apply
    {v : ι → ∀ b : B, E b}
    (hv : ∀ b, Orthonormal ℝ (fun i ↦ v i b))
    (hrank : Fintype.card ι = Module.finrank ℝ F)
    (hsmooth : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (v i b)))
    (b : B) (w : E b) (i : ι) :
    (orthonormalFrameDiffeomorph hv hrank hsmooth ⟨b, w⟩).2 i = ⟪v i b, w⟫_ℝ := by
  rw [orthonormalFrameDiffeomorph_def, orthonormalBasisTotalSpaceEuclideanDiffeomorph_snd_apply,
    orthonormalBasisOfOrthonormalSections_apply]

/-- The inverse of `TauCeti.orthonormalFrameDiffeomorph` expands coordinates as a finite linear
combination in the frame sections. -/
@[simp]
theorem orthonormalFrameDiffeomorph_symm_eq_sum
    {v : ι → ∀ b : B, E b}
    (hv : ∀ b, Orthonormal ℝ (fun i ↦ v i b))
    (hrank : Fintype.card ι = Module.finrank ℝ F)
    (hsmooth : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (v i b)))
    (b : B) (y : EuclideanSpace ℝ ι) :
    (orthonormalFrameDiffeomorph hv hrank hsmooth).symm (b, y) = ⟨b, ∑ i, y i • v i b⟩ := by
  rw [orthonormalFrameDiffeomorph_def, orthonormalBasisTotalSpaceEuclideanDiffeomorph_symm_eq_sum]
  simp only [orthonormalBasisOfOrthonormalSections_apply]

@[simp]
theorem norm_orthonormalFrameDiffeomorph_snd
    {v : ι → ∀ b : B, E b}
    (hv : ∀ b, Orthonormal ℝ (fun i ↦ v i b))
    (hrank : Fintype.card ι = Module.finrank ℝ F)
    (hsmooth : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (v i b)))
    (p : TotalSpace F E) :
    ‖(orthonormalFrameDiffeomorph hv hrank hsmooth p).2‖ = ‖p.snd‖ :=
  norm_orthonormalBasisTotalSpaceEuclideanDiffeomorph_snd _ _ p

/-- `TauCeti.orthonormalFrameDiffeomorph` preserves the inner product on each fibre. -/
theorem inner_orthonormalFrameDiffeomorph_snd
    {v : ι → ∀ b : B, E b}
    (hv : ∀ b, Orthonormal ℝ (fun i ↦ v i b))
    (hrank : Fintype.card ι = Module.finrank ℝ F)
    (hsmooth : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (v i b)))
    (b : B) (w₁ w₂ : E b) :
    ⟪(orthonormalFrameDiffeomorph hv hrank hsmooth ⟨b, w₁⟩).2,
      (orthonormalFrameDiffeomorph hv hrank hsmooth ⟨b, w₂⟩).2⟫_ℝ = ⟪w₁, w₂⟫_ℝ :=
  inner_orthonormalBasisTotalSpaceEuclideanDiffeomorph_snd _ _ b w₁ w₂

end OrthonormalFrame

end TauCeti

namespace Bundle.Trivialization

variable [LinearOrder ι] [LocallyFiniteOrderBot ι]
  [IsContMDiffRiemannianBundle IB n F E] [ContMDiffVectorBundle n F E IB]

open scoped Classical in
/-- The Gram–Schmidt orthonormal basis vectors of any linear trivialization in the `C^n` maximal
atlas are `C^n` on its base set (extended by `0` outside it). -/
theorem contMDiffOn_orthonormalBasis_of_mem_maximalAtlas
    (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    (he : e.toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F E))
    (c : Module.Basis ι ℝ F) (i : ι) :
    ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F y
        (if hy : y ∈ e.baseSet then e.orthonormalBasis c ⟨y, hy⟩ i else 0))
      e.baseSet := by
  have hfr := e.isLocalFrameOn_symm_of_mem_maximalAtlas he c
  have heq {y : B} (hy : y ∈ e.baseSet) :
      (if hy : y ∈ e.baseSet then e.orthonormalBasis c ⟨y, hy⟩ i else 0 : E y) =
        InnerProductSpace.gramSchmidtNormed ℝ (fun j ↦ e.symm y (c j)) i := by
    simp only [hy, ↓reduceDIte, e.orthonormalBasis_apply c ⟨y, hy⟩ i]
    congr 1
    funext j
    exact e.symmL_apply hy (c j)
  intro x hx
  refine ((ContMDiffAt.gramSchmidtNormed_bundle i (fun j _ ↦ hfr.contMDiffAt e.open_baseSet hx j)
    ((hfr.linearIndependent hx).linearIndepOn _)).contMDiffWithinAt).congr (fun y hy ↦ ?_) ?_
  · exact congrArg (TotalSpace.mk' F y) (heq hy)
  · exact congrArg (TotalSpace.mk' F x) (heq hx)

end Bundle.Trivialization

end RealBundle

section RealInnerModel

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  {n : ℕ∞ω} {ι : Type*} [Fintype ι]

namespace OrthonormalBasis

section Global

variable [IsContMDiffRiemannianBundle IB n F E]

/-- Given a model orthonormal basis `c : OrthonormalBasis ι ℝ F` and a `C^n` global orthonormal
basis `d` of `E`, the induced `C^n` diffeomorphism `TotalSpace F E ≃ₘ^n B × F` is a linear
isometry on every fibre. -/
def totalSpaceDiffeomorph (c : OrthonormalBasis ι ℝ F)
    (d : ∀ b : B, OrthonormalBasis ι ℝ (E b))
    (hd : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (d b i))) :
    TotalSpace F E ≃ₘ^n⟮IB.prod 𝓘(ℝ, F), IB.prod 𝓘(ℝ, F)⟯ B × F where
  toFun p := (p.proj, c.repr.symm ((d p.proj).repr p.snd))
  invFun p := ⟨p.1, (d p.1).repr.symm (c.repr p.2)⟩
  left_inv p := by cases p; simp
  right_inv p := by cases p; simp
  contMDiff_toFun := (Bundle.contMDiff_proj E).prodMk
    (c.repr.symm.toContinuousLinearEquiv.contDiff.comp_contMDiff
      (contMDiff_orthonormalBasis_repr_totalSpace d hd))
  contMDiff_invFun := (contMDiff_orthonormalBasis_repr_symm_totalSpace d hd).comp
    (contMDiff_fst.prodMk (c.repr.toContinuousLinearEquiv.contDiff.comp_contMDiff contMDiff_snd))

@[simp]
theorem totalSpaceDiffeomorph_apply (c : OrthonormalBasis ι ℝ F)
    (d : ∀ b : B, OrthonormalBasis ι ℝ (E b))
    (hd : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (d b i)))
    (b : B) (v : E b) :
    c.totalSpaceDiffeomorph d hd ⟨b, v⟩ = (b, c.repr.symm ((d b).repr v)) :=
  (rfl)

@[simp]
theorem totalSpaceDiffeomorph_fst (c : OrthonormalBasis ι ℝ F)
    (d : ∀ b : B, OrthonormalBasis ι ℝ (E b))
    (hd : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (d b i)))
    (p : TotalSpace F E) :
    (c.totalSpaceDiffeomorph d hd p).1 = p.proj :=
  (rfl)

@[simp]
theorem totalSpaceDiffeomorph_symm_apply (c : OrthonormalBasis ι ℝ F)
    (d : ∀ b : B, OrthonormalBasis ι ℝ (E b))
    (hd : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (d b i)))
    (b : B) (w : F) :
    (c.totalSpaceDiffeomorph d hd).symm (b, w) = ⟨b, (d b).repr.symm (c.repr w)⟩ :=
  (rfl)

@[simp]
theorem norm_totalSpaceDiffeomorph_snd (c : OrthonormalBasis ι ℝ F)
    (d : ∀ b : B, OrthonormalBasis ι ℝ (E b))
    (hd : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (d b i)))
    (p : TotalSpace F E) :
    ‖(c.totalSpaceDiffeomorph d hd p).2‖ = ‖p.snd‖ := by
  cases p
  exact (c.repr.symm.norm_map _).trans ((d _).repr.norm_map _)

/-- `OrthonormalBasis.totalSpaceDiffeomorph` preserves the inner product on each fibre. -/
theorem inner_totalSpaceDiffeomorph_snd (c : OrthonormalBasis ι ℝ F)
    (d : ∀ b : B, OrthonormalBasis ι ℝ (E b))
    (hd : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (d b i)))
    (b : B) (v w : E b) :
    ⟪(c.totalSpaceDiffeomorph d hd ⟨b, v⟩).2,
      (c.totalSpaceDiffeomorph d hd ⟨b, w⟩).2⟫_ℝ = ⟪v, w⟫_ℝ :=
  (c.repr.symm.inner_map_map _ _).trans ((d b).repr.inner_map_map v w)

/-- Over `U = univ`, the topological trivialization `OrthonormalBasis.bundleTrivialization` agrees
everywhere with `OrthonormalBasis.totalSpaceDiffeomorph`. -/
theorem bundleTrivialization_univ_apply [IsContinuousRiemannianBundle F E]
    (c : OrthonormalBasis ι ℝ F)
    (d : ∀ b : B, OrthonormalBasis ι ℝ (E b))
    (hd : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (d b i)))
    (p : TotalSpace F E) :
    c.bundleTrivialization isOpen_univ (fun b ↦ d b.val)
        (fun i ↦ (hd i).continuous.comp continuous_subtypeVal) p =
      c.totalSpaceDiffeomorph d hd p := by
  cases p
  simp

end Global

section MaximalAtlas

variable [IsContinuousRiemannianBundle F E] [ContMDiffVectorBundle n F E IB]

open scoped Classical in
/-- The local trivialization associated to a `C^n` orthonormal basis on an open set `U` belongs to
the maximal atlas of `C^n` fiberwise linear trivializations. -/
theorem bundleTrivialization_mem_maximalAtlas
    (c : OrthonormalBasis ι ℝ F) {U : Set B} (hU : IsOpen U)
    (d : ∀ b : U, OrthonormalBasis ι ℝ (E b))
    (hd : ∀ i, ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n
      (fun b ↦ TotalSpace.mk' F b (if hb : b ∈ U then d ⟨b, hb⟩ i else 0)) U) :
    (c.bundleTrivialization hU d
        (continuous_of_contMDiffOn_orthonormalBasis d hd)).toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F E) := by
  set hs := isLocalFrameOn_of_orthonormalBasis d hd
  have hbasis : ∀ {b : B} (hb : b ∈ U), hs.toBasisAt hb = (d ⟨b, hb⟩).toBasis := fun {b} hb ↦ by
    refine Module.Basis.eq_of_apply_eq fun i ↦ ?_
    rw [IsLocalFrameOn.toBasisAt_coe, OrthonormalBasis.coe_toBasis]
    simp [hb]
  refine Trivialization.mem_maximalAtlas_of_eq_on_baseSet
    (e₂ := hs.trivialization hU c.toBasis)
    ((c.bundleTrivialization_baseSet hU d _).trans (hs.baseSet_trivialization hU c.toBasis).symm)
    (fun {b} hb v ↦ ?_) (hs.trivialization_mem_maximalAtlas hU c.toBasis)
  have hbU : b ∈ U := by simpa only [bundleTrivialization_baseSet] using hb
  rw [bundleTrivialization_apply c hU d _ hbU v, hs.trivialization_apply hU c.toBasis hbU v,
    hbasis hbU, toBasis_equiv_refl]
  simp

/-- Over `U = univ`, the global trivialization associated to a `C^n` orthonormal basis belongs to
the maximal atlas of `C^n` fiberwise linear trivializations. -/
theorem bundleTrivialization_univ_mem_maximalAtlas
    (c : OrthonormalBasis ι ℝ F)
    (d : ∀ b : B, OrthonormalBasis ι ℝ (E b))
    (hd : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (d b i))) :
    (c.bundleTrivialization isOpen_univ (fun b ↦ d b.val)
        (fun i ↦ (hd i).continuous.comp continuous_subtypeVal)).toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F E) := by
  classical
  exact c.bundleTrivialization_mem_maximalAtlas isOpen_univ (fun b ↦ d b.val) fun i ↦
    (hd i).contMDiffOn.congr fun b hb ↦ by simp [hb]

end MaximalAtlas

end OrthonormalBasis

namespace Bundle.Trivialization

variable [LinearOrder ι] [LocallyFiniteOrderBot ι]
  [IsContMDiffRiemannianBundle IB n F E] [IsContinuousRiemannianBundle F E]
  [ContMDiffVectorBundle n F E IB]

/-- Gram–Schmidt orthogonalization of any linear trivialization in the `C^n` maximal atlas of a
`C^n` Riemannian vector bundle also belongs to the `C^n` maximal atlas. -/
theorem orthonormal_mem_maximalAtlas
    (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    (he : e.toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F E))
    (c : OrthonormalBasis ι ℝ F) :
    (e.orthonormal c).toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F E) := by
  classical
  have hd := e.contMDiffOn_orthonormalBasis_of_mem_maximalAtlas he c.toBasis
  rw [e.orthonormal_eq_bundleTrivialization c
    (continuous_of_contMDiffOn_orthonormalBasis (e.orthonormalBasis c.toBasis) hd)]
  exact c.bundleTrivialization_mem_maximalAtlas e.open_baseSet (e.orthonormalBasis c.toBasis) hd

end Bundle.Trivialization

end RealInnerModel

end
