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
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Translate

/-!
# Smooth orthonormal trivializations of Riemannian vector bundles

Given a `C^n` Riemannian vector bundle `E → B` and a pointwise orthonormal basis `d b` of each
fibre `E b` whose basis vectors are `C^n` sections, reading coordinates in `d` defines a `C^n`
diffeomorphism `OrthonormalBasis.totalSpaceEuclideanDiffeomorph` between `TotalSpace F E` and
`B × EuclideanSpace ℝ ι` that is a linear isometry on every fibre. Unlike general frame
trivializations (`IsLocalFrameOn.trivialization`), no operator inversion is needed: the forward
map takes Riemannian inner products `⟪d b i, v⟫_ℝ`, and the inverse reconstructs vectors by finite
linear combinations `∑ i, y i • d b i`. Both directions work without change in rank zero (`ι`
empty).

When the model fibre `F` carries a fixed orthonormal basis `c`, composing with `c.repr.symm` gives
a `C^n` diffeomorphism `OrthonormalBasis.totalSpaceDiffeomorph` onto `B × F` agreeing everywhere
with the global topological chart `OrthonormalBasis.bundleTrivialization`. Locally over an open set
`U`, `OrthonormalBasis.bundleTrivialization` agrees on `U` with the frame trivialization of the
underlying `C^n` local frame, and therefore belongs to the maximal atlas of `C^n` fiberwise linear
trivializations (`OrthonormalBasis.bundleTrivialization_mem_maximalAtlas`). In particular, the
Gram–Schmidt orthogonalization `Bundle.Trivialization.orthonormal` of any compatible local
trivialization lies in the `C^n` maximal atlas
(`Bundle.Trivialization.orthonormal_mem_maximalAtlas`).

## Main definitions

* `OrthonormalBasis.totalSpaceEuclideanDiffeomorph`: `C^n` diffeomorphism
  `TotalSpace F E ≃ₘ^n B × EuclideanSpace ℝ ι` induced by a `C^n` global orthonormal basis `d`.
* `OrthonormalBasis.totalSpaceDiffeomorph`: `C^n` diffeomorphism `TotalSpace F E ≃ₘ^n B × F`
  sending `d b` to a model orthonormal basis `c`.
* `TauCeti.orthonormalBasisOfOrthonormalSections`: pointwise `OrthonormalBasis` built from a
  pointwise orthonormal family of sections matching `finrank ℝ F` (including rank zero).
* `TauCeti.orthonormalFrameDiffeomorph`: `C^n` diffeomorphism
  `TotalSpace F E ≃ₘ^n B × EuclideanSpace ℝ ι` built directly from a `C^n` orthonormal frame.

## Main results

* `Bundle.Trivialization.mem_maximalAtlas_of_eq_on_baseSet`: a linear trivialization agreeing on
  its base set with a member of the `C^n` maximal atlas also belongs to the `C^n` maximal atlas.
* `OrthonormalBasis.bundleTrivialization_mem_maximalAtlas`: the local chart of a `C^n` orthonormal
  basis lies in `(contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F E)`.
* `Bundle.Trivialization.orthonormal_mem_maximalAtlas`: Gram–Schmidt orthogonalization of an atlas
  chart lies in `(contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F E)`.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §5.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 10.
-/

public section

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology InnerProductSpace

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  {n : ℕ∞ω} {ι : Type*} [Fintype ι]

namespace Bundle.Trivialization

/-- If two linear bundle trivializations have the same base set and agree on every fibre over that
base set, and the second belongs to the `C^n` maximal atlas, then so does the first. -/
theorem mem_maximalAtlas_of_eq_on_baseSet {e₁ e₂ : Trivialization F (π F E)}
    [e₁.IsLinear ℝ] [e₂.IsLinear ℝ]
    (hbase : e₁.baseSet = e₂.baseSet)
    (happly : ∀ {b : B}, b ∈ e₁.baseSet → ∀ v : E b, e₁ ⟨b, v⟩ = e₂ ⟨b, v⟩)
    (he₂ : e₂.toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F E)) :
    e₁.toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F E) := by
  have hsymm : ∀ {b : B}, b ∈ e₁.baseSet → ∀ w : F, e₁.symm b w = e₂.symm b w :=
    fun {b} hb₁ w ↦ by
      have hb₂ : b ∈ e₂.baseSet := hbase ▸ hb₁
      calc
        e₁.symm b w = e₂.symm b (e₂ ⟨b, e₁.symm b w⟩).2 :=
          (e₂.symm_apply_apply_mk hb₂ (e₁.symm b w)).symm
        _ = e₂.symm b (e₁ ⟨b, e₁.symm b w⟩).2 := by rw [← happly hb₁]
        _ = e₂.symm b w := by rw [e₁.apply_mk_symm hb₁]
  refine (mem_maximalAtlas_contMDiffFiberwiseLinear_iff IB n e₁).2 fun e' _ ↦ ?_
  obtain ⟨hc₁, hc₂⟩ := (mem_maximalAtlas_contMDiffFiberwiseLinear_iff IB n e₂).1 he₂ e'
  rw [← hbase] at hc₁ hc₂
  refine ⟨hc₁.congr fun b hb ↦ ?_, hc₂.congr fun b hb ↦ ?_⟩
  · ext w
    have hb₂ : b ∈ e₂.baseSet ∩ e'.baseSet := ⟨hbase ▸ hb.1, hb.2⟩
    simp only [ContinuousLinearEquiv.coe_coe, coordChangeL_apply e₁ e' hb,
      coordChangeL_apply e₂ e' hb₂, hsymm hb.1 w]
  · ext w
    have hb' : b ∈ e'.baseSet ∩ e₁.baseSet := ⟨hb.2, hb.1⟩
    have hb₂' : b ∈ e'.baseSet ∩ e₂.baseSet := ⟨hb.2, hbase ▸ hb.1⟩
    simp only [ContinuousLinearEquiv.coe_coe, coordChangeL_apply e' e₁ hb',
      coordChangeL_apply e' e₂ hb₂', happly hb.1]

end Bundle.Trivialization

namespace OrthonormalBasis

section Global

variable [IsContMDiffRiemannianBundle IB n F E]

/-- Reading coordinates in a `C^n` global orthonormal basis defines a `C^n` map from
`TotalSpace F E` to `EuclideanSpace ℝ ι`. -/
theorem contMDiff_repr_totalSpace
    (d : ∀ b : B, OrthonormalBasis ι ℝ (E b))
    (hd : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (d b i))) :
    ContMDiff (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, EuclideanSpace ℝ ι) n
      (fun p : TotalSpace F E ↦ (d p.proj).repr p.2) := by
  have hpi : ContMDiff (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, ι → ℝ) n
      (fun p : TotalSpace F E ↦ fun i ↦ ⟪d p.proj i, p.2⟫_ℝ) :=
    contMDiff_pi_module_iff.mpr fun i ↦
      ((hd i).comp (Bundle.contMDiff_proj E)).inner_bundle contMDiff_id
  refine ((EuclideanSpace.equiv ι ℝ).symm.contDiff.comp_contMDiff hpi).congr fun p ↦ ?_
  ext i
  exact (d p.proj).repr_apply_apply p.2 i

omit [IsContMDiffRiemannianBundle IB n F E] in
/-- Reconstructing fibre vectors from `EuclideanSpace ℝ ι` coordinates in a `C^n` global
orthonormal basis defines a `C^n` map into `TotalSpace F E`. -/
theorem contMDiff_repr_symm_totalSpace
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

/-- A `C^n` global orthonormal basis `d` of a `C^n` Riemannian vector bundle induces a `C^n`
diffeomorphism between `TotalSpace F E` and `B × EuclideanSpace ℝ ι` acting as `(d b).repr` on
each fibre. -/
def totalSpaceEuclideanDiffeomorph
    (d : ∀ b : B, OrthonormalBasis ι ℝ (E b))
    (hd : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (d b i))) :
    TotalSpace F E ≃ₘ^n⟮IB.prod 𝓘(ℝ, F), IB.prod 𝓘(ℝ, EuclideanSpace ℝ ι)⟯
      B × EuclideanSpace ℝ ι where
  toFun p := (p.proj, (d p.proj).repr p.2)
  invFun p := ⟨p.1, (d p.1).repr.symm p.2⟩
  left_inv p := by cases p; simp
  right_inv p := by cases p; simp
  contMDiff_toFun := (Bundle.contMDiff_proj E).prodMk (contMDiff_repr_totalSpace d hd)
  contMDiff_invFun := contMDiff_repr_symm_totalSpace d hd

@[simp]
theorem totalSpaceEuclideanDiffeomorph_apply
    (d : ∀ b : B, OrthonormalBasis ι ℝ (E b))
    (hd : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (d b i)))
    (b : B) (v : E b) :
    totalSpaceEuclideanDiffeomorph d hd ⟨b, v⟩ = (b, (d b).repr v) :=
  (rfl)

@[simp]
theorem totalSpaceEuclideanDiffeomorph_fst
    (d : ∀ b : B, OrthonormalBasis ι ℝ (E b))
    (hd : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (d b i)))
    (p : TotalSpace F E) :
    (totalSpaceEuclideanDiffeomorph d hd p).1 = p.proj :=
  (rfl)

/-- Each coordinate of `OrthonormalBasis.totalSpaceEuclideanDiffeomorph` is the Riemannian inner
product with the corresponding frame vector. -/
theorem totalSpaceEuclideanDiffeomorph_snd_apply
    (d : ∀ b : B, OrthonormalBasis ι ℝ (E b))
    (hd : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (d b i)))
    (b : B) (v : E b) (i : ι) :
    (totalSpaceEuclideanDiffeomorph d hd ⟨b, v⟩).2 i = ⟪d b i, v⟫_ℝ :=
  (d b).repr_apply_apply v i

@[simp]
theorem totalSpaceEuclideanDiffeomorph_symm_apply
    (d : ∀ b : B, OrthonormalBasis ι ℝ (E b))
    (hd : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (d b i)))
    (b : B) (y : EuclideanSpace ℝ ι) :
    (totalSpaceEuclideanDiffeomorph d hd).symm (b, y) = ⟨b, (d b).repr.symm y⟩ :=
  (rfl)

/-- The inverse of `OrthonormalBasis.totalSpaceEuclideanDiffeomorph` expands coordinates as a finite
linear combination in `d b`. -/
theorem totalSpaceEuclideanDiffeomorph_symm_eq_sum
    (d : ∀ b : B, OrthonormalBasis ι ℝ (E b))
    (hd : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (d b i)))
    (b : B) (y : EuclideanSpace ℝ ι) :
    (totalSpaceEuclideanDiffeomorph d hd).symm (b, y) = ⟨b, ∑ i, y i • d b i⟩ :=
  congrArg (TotalSpace.mk' F b) ((d b).sum_repr_symm y).symm

@[simp]
theorem norm_totalSpaceEuclideanDiffeomorph_snd
    (d : ∀ b : B, OrthonormalBasis ι ℝ (E b))
    (hd : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (d b i)))
    (p : TotalSpace F E) :
    ‖(totalSpaceEuclideanDiffeomorph d hd p).2‖ = ‖p.2‖ :=
  (d p.proj).repr.norm_map p.2

/-- `OrthonormalBasis.totalSpaceEuclideanDiffeomorph` preserves the inner product on each fibre. -/
theorem inner_totalSpaceEuclideanDiffeomorph_snd
    (d : ∀ b : B, OrthonormalBasis ι ℝ (E b))
    (hd : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (d b i)))
    (b : B) (v w : E b) :
    ⟪(totalSpaceEuclideanDiffeomorph d hd ⟨b, v⟩).2,
      (totalSpaceEuclideanDiffeomorph d hd ⟨b, w⟩).2⟫_ℝ = ⟪v, w⟫_ℝ :=
  (d b).repr.inner_map_map v w

/-- Given a model orthonormal basis `c : OrthonormalBasis ι ℝ F` and a `C^n` global orthonormal
basis `d` of `E`, the induced `C^n` diffeomorphism `TotalSpace F E ≃ₘ^n B × F` is a linear
isometry on every fibre. -/
def totalSpaceDiffeomorph (c : OrthonormalBasis ι ℝ F)
    (d : ∀ b : B, OrthonormalBasis ι ℝ (E b))
    (hd : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (d b i))) :
    TotalSpace F E ≃ₘ^n⟮IB.prod 𝓘(ℝ, F), IB.prod 𝓘(ℝ, F)⟯ B × F where
  toFun p := (p.proj, c.repr.symm ((d p.proj).repr p.2))
  invFun p := ⟨p.1, (d p.1).repr.symm (c.repr p.2)⟩
  left_inv p := by cases p; simp
  right_inv p := by cases p; simp
  contMDiff_toFun := (Bundle.contMDiff_proj E).prodMk
    (c.repr.symm.toContinuousLinearEquiv.contDiff.comp_contMDiff
      (contMDiff_repr_totalSpace d hd))
  contMDiff_invFun := (contMDiff_repr_symm_totalSpace d hd).comp
    (contMDiff_fst.prodMk (c.repr.toContinuousLinearEquiv.contDiff.comp_contMDiff contMDiff_snd))

@[simp]
theorem totalSpaceDiffeomorph_apply (c : OrthonormalBasis ι ℝ F)
    (d : ∀ b : B, OrthonormalBasis ι ℝ (E b))
    (hd : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (d b i)))
    (b : B) (v : E b) :
    c.totalSpaceDiffeomorph d hd ⟨b, v⟩ = (b, c.repr.symm ((d b).repr v)) :=
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
    ‖(c.totalSpaceDiffeomorph d hd p).2‖ = ‖p.2‖ := by
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
    c.bundleTrivialization isOpen_univ (fun b ↦ d b.1)
        (fun i ↦ (hd i).continuous.comp continuous_subtype_val) p =
      c.totalSpaceDiffeomorph d hd p := by
  cases p
  simp

end Global

section Local

open scoped Classical in
omit [VectorBundle ℝ F E] in
/-- A family of orthonormal bases over `U` whose zero-extended sections are `C^n` on `U` forms a
`C^n` local frame on `U`. -/
theorem isLocalFrameOn_of_orthonormalBasis {U : Set B}
    (d : ∀ b : U, OrthonormalBasis ι ℝ (E b))
    (hd : ∀ i, ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n
      (fun b ↦ TotalSpace.mk' F b (if hb : b ∈ U then d ⟨b, hb⟩ i else 0)) U) :
    IsLocalFrameOn IB F n
      (fun i b ↦ if hb : b ∈ U then d ⟨b, hb⟩ i else 0) U where
  linearIndependent {b} hb := by
    have hfun : (fun i ↦ (if hb' : b ∈ U then d ⟨b, hb'⟩ i else 0 : E b)) =
        fun i ↦ (d ⟨b, hb⟩).toBasis i :=
      funext fun i ↦ dite_eq_left_of_eq_true (eq_true hb)
    rw [hfun]
    exact (d ⟨b, hb⟩).toBasis.linearIndependent
  generating {b} hb := by
    have hfun : (fun i ↦ (if hb' : b ∈ U then d ⟨b, hb'⟩ i else 0 : E b)) =
        fun i ↦ (d ⟨b, hb⟩).toBasis i :=
      funext fun i ↦ dite_eq_left_of_eq_true (eq_true hb)
    rw [hfun]
    exact (d ⟨b, hb⟩).toBasis.span_eq.ge
  contMDiffOn := hd

open scoped Classical in
omit [VectorBundle ℝ F E] in
/-- Restricting `C^n` zero-extended orthonormal-basis sections to `U` gives the continuous subtype
sections consumed by `OrthonormalBasis.bundleTrivialization`. -/
theorem continuous_of_contMDiffOn_orthonormalBasis {U : Set B}
    (d : ∀ b : U, OrthonormalBasis ι ℝ (E b))
    (hd : ∀ i, ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n
      (fun b ↦ TotalSpace.mk' F b (if hb : b ∈ U then d ⟨b, hb⟩ i else 0)) U) (i : ι) :
    Continuous fun b : U ↦ TotalSpace.mk' F (b : B) (d b i) :=
  ((hd i).continuousOn.comp_continuous continuous_subtype_val fun b ↦ b.2).congr fun b ↦
    congrArg (TotalSpace.mk' F (b : B)) (dite_eq_left_of_eq_true (eq_true b.2))

/-- For two orthonormal bases indexed by the same finite type, the algebraic `Basis.equiv` along
`Equiv.refl ι` coincides with `d₀.repr.trans c.repr.symm`. -/
theorem toBasis_equiv_refl {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
    [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
    (d₀ : OrthonormalBasis ι ℝ V₁) (c : OrthonormalBasis ι ℝ V₂) :
    d₀.toBasis.equiv c.toBasis (Equiv.refl ι) = (d₀.repr.trans c.repr.symm).toLinearEquiv := by
  classical
  refine LinearEquiv.toLinearMap_injective (d₀.toBasis.ext fun i ↦ ?_)
  rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
  simp

open scoped Classical in
/-- The local trivialization associated to a `C^n` orthonormal basis on an open set `U` belongs to
the maximal atlas of `C^n` fiberwise linear trivializations. -/
theorem bundleTrivialization_mem_maximalAtlas [IsContinuousRiemannianBundle F E]
    [ContMDiffVectorBundle n F E IB]
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
    exact dite_eq_left_of_eq_true (eq_true hb)
  refine Trivialization.mem_maximalAtlas_of_eq_on_baseSet
    (e₂ := hs.trivialization hU c.toBasis)
    ((c.bundleTrivialization_baseSet hU d _).trans (hs.baseSet_trivialization hU c.toBasis).symm)
    (fun {b} hb v ↦ ?_) (hs.trivialization_mem_maximalAtlas hU c.toBasis)
  have hbU : b ∈ U := by simpa only [bundleTrivialization_baseSet] using hb
  rw [bundleTrivialization_apply c hU d _ hbU v, hs.trivialization_apply hU c.toBasis hbU v,
    hbasis hbU, toBasis_equiv_refl]
  rfl

end Local

end OrthonormalBasis

namespace Bundle.Trivialization

/-- Gram–Schmidt orthogonalization of an atlas chart of a `C^n` Riemannian vector bundle belongs to
the maximal atlas of `C^n` fiberwise linear trivializations. -/
theorem orthonormal_mem_maximalAtlas [LinearOrder ι] [LocallyFiniteOrderBot ι]
    [IsContinuousRiemannianBundle F E] [IsContMDiffRiemannianBundle IB n F E]
    [ContMDiffVectorBundle n F E IB]
    (e : Trivialization F (π F E)) [MemTrivializationAtlas e] (c : OrthonormalBasis ι ℝ F) :
    (e.orthonormal c).toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F E) := by
  have hd := e.contMDiffOn_orthonormalBasis (I := IB) (n := n) c.toBasis
  refine mem_maximalAtlas_of_eq_on_baseSet
    (e₂ := c.bundleTrivialization e.open_baseSet (e.orthonormalBasis c.toBasis)
      (OrthonormalBasis.continuous_of_contMDiffOn_orthonormalBasis
        (e.orthonormalBasis c.toBasis) hd))
    ((e.orthonormal_baseSet c).trans (c.bundleTrivialization_baseSet _ _ _).symm)
    (fun {b} hb v ↦ ?_)
    (c.bundleTrivialization_mem_maximalAtlas e.open_baseSet (e.orthonormalBasis c.toBasis) hd)
  have hb' : b ∈ e.baseSet := by simpa only [orthonormal_baseSet] using hb
  rw [e.orthonormal_apply c hb' v, OrthonormalBasis.bundleTrivialization_apply c _ _ _ hb' v]

end Bundle.Trivialization

namespace TauCeti

variable [FiniteDimensional ℝ F]

/-- A pointwise orthonormal family of sections indexed by `ι` with `Fintype.card ι = finrank ℝ F`
defines a pointwise `OrthonormalBasis` of every fibre (including rank zero). -/
def orthonormalBasisOfOrthonormalSections {v : ι → ∀ b : B, E b}
    (hv : ∀ b, Orthonormal ℝ (fun i ↦ v i b))
    (hrank : Fintype.card ι = Module.finrank ℝ F) (b : B) :
    OrthonormalBasis ι ℝ (E b) := by
  have hlin := (trivializationAt F E b).linearEquivAt ℝ b (mem_baseSet_trivializationAt F E b)
  haveI : FiniteDimensional ℝ (E b) := hlin.symm.finiteDimensional
  have hfin : Fintype.card ι = Module.finrank ℝ (E b) := hrank.trans hlin.finrank_eq.symm
  exact (basisOfLinearIndependentOfCardEqFinrank' (fun i ↦ v i b) (hv b).linearIndependent
    hfin).toOrthonormalBasis
    (by simpa only [coe_basisOfLinearIndependentOfCardEqFinrank'] using hv b)

@[simp]
theorem orthonormalBasisOfOrthonormalSections_apply {v : ι → ∀ b : B, E b}
    (hv : ∀ b, Orthonormal ℝ (fun i ↦ v i b))
    (hrank : Fintype.card ι = Module.finrank ℝ F) (b : B) (i : ι) :
    orthonormalBasisOfOrthonormalSections hv hrank b i = v i b := by
  simp [orthonormalBasisOfOrthonormalSections]

/-- A `C^n` global orthonormal frame of a `C^n` Riemannian vector bundle with cardinality
`finrank ℝ F` induces a `C^n` diffeomorphism `TotalSpace F E ≃ₘ^n B × EuclideanSpace ℝ ι`. -/
def orthonormalFrameDiffeomorph [IsContMDiffRiemannianBundle IB n F E]
    {v : ι → ∀ b : B, E b}
    (hv : ∀ b, Orthonormal ℝ (fun i ↦ v i b))
    (hrank : Fintype.card ι = Module.finrank ℝ F)
    (hsmooth : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (v i b))) :
    TotalSpace F E ≃ₘ^n⟮IB.prod 𝓘(ℝ, F), IB.prod 𝓘(ℝ, EuclideanSpace ℝ ι)⟯
      B × EuclideanSpace ℝ ι :=
  OrthonormalBasis.totalSpaceEuclideanDiffeomorph
    (orthonormalBasisOfOrthonormalSections hv hrank) fun i ↦ by
      simpa only [orthonormalBasisOfOrthonormalSections_apply] using hsmooth i

@[simp]
theorem orthonormalFrameDiffeomorph_snd_apply [IsContMDiffRiemannianBundle IB n F E]
    {v : ι → ∀ b : B, E b}
    (hv : ∀ b, Orthonormal ℝ (fun i ↦ v i b))
    (hrank : Fintype.card ι = Module.finrank ℝ F)
    (hsmooth : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (v i b)))
    (b : B) (w : E b) (i : ι) :
    (orthonormalFrameDiffeomorph hv hrank hsmooth ⟨b, w⟩).2 i = ⟪v i b, w⟫_ℝ := by
  rw [orthonormalFrameDiffeomorph, OrthonormalBasis.totalSpaceEuclideanDiffeomorph_snd_apply,
    orthonormalBasisOfOrthonormalSections_apply]

/-- The inverse of `TauCeti.orthonormalFrameDiffeomorph` expands coordinates as a finite linear
combination in the frame sections. -/
theorem orthonormalFrameDiffeomorph_symm_eq_sum [IsContMDiffRiemannianBundle IB n F E]
    {v : ι → ∀ b : B, E b}
    (hv : ∀ b, Orthonormal ℝ (fun i ↦ v i b))
    (hrank : Fintype.card ι = Module.finrank ℝ F)
    (hsmooth : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F b (v i b)))
    (b : B) (y : EuclideanSpace ℝ ι) :
    (orthonormalFrameDiffeomorph hv hrank hsmooth).symm (b, y) = ⟨b, ∑ i, y i • v i b⟩ := by
  rw [orthonormalFrameDiffeomorph, OrthonormalBasis.totalSpaceEuclideanDiffeomorph_symm_eq_sum]
  simp only [orthonormalBasisOfOrthonormalSections_apply]

end TauCeti

end
