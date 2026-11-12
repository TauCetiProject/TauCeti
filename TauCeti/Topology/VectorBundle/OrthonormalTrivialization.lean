/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.GramSchmidt

/-!
# Orthonormal trivializations of Riemannian vector bundles

`OrthonormalBasis.bundleTrivialization` turns a continuous local orthonormal basis into
a native bundle trivialization with isometric fibre maps. Coordinates are inner products
with the local basis; the inverse is the corresponding finite linear combination.
`Bundle.Trivialization.orthonormal` applies this construction to the Gram–Schmidt basis
of an existing linear chart. Thus every continuous finite-rank real Riemannian bundle
has local isometric charts, including rank zero. These charts give the orthogonal
coordinate changes used to trivialize the orthonormal frame bundle.

The construction uses Mathlib's `OrthonormalBasis.repr` and the continuous local
Gram–Schmidt bases in `TauCeti.Topology.VectorBundle.GramSchmidt`.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, §5.
-/

public section

noncomputable section

open Bundle Set
open scoped Topology InnerProductSpace

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]
  {ι : Type*} [Fintype ι]

namespace OrthonormalBasis

variable (c : OrthonormalBasis ι ℝ F) {U : Set B} (hU : IsOpen U)
  (d : ∀ b : U, OrthonormalBasis ι ℝ (E b))
  (hd : ∀ i, Continuous fun b : U ↦ TotalSpace.mk' F (b : B) (d b i))

include hd in
private theorem continuous_local_repr :
    Continuous fun p : {p : TotalSpace F E // p.proj ∈ U} ↦
      (d ⟨p.val.proj, p.property⟩).repr p.val.2 := by
  apply continuous_induced_rng.2
  apply continuous_pi
  intro i
  simp only [Function.comp_def, OrthonormalBasis.repr_apply_apply]
  have hbase : Continuous (fun p : {p : TotalSpace F E // p.proj ∈ U} ↦
      (⟨p.val.proj, p.property⟩ : U)) :=
    ((FiberBundle.continuous_proj F E).comp continuous_subtype_val).subtype_mk _
  exact ((hd i).comp hbase).inner_bundle continuous_subtype_val

include hd in
omit [IsContinuousRiemannianBundle F E] in
private theorem continuous_local_repr_symm :
    Continuous fun p : U × F ↦ TotalSpace.mk' F (p.1 : B)
      ((d p.1).repr.symm (c.repr p.2)) := by
  classical
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(continuous_subtype_val.comp continuous_fst).continuousAt, ?_⟩
  let e := trivializationAt F E (p.1 : B)
  have hmem : ∀ᶠ q : U × F in 𝓝 p, (q.1 : B) ∈ e.baseSet :=
    (continuous_subtype_val.comp continuous_fst).continuousAt
      (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F E (p.1 : B)))
  have hc (i : ι) : ContinuousAt
      (fun q : U × F ↦ TotalSpace.mk' F (q.1 : B) (d q.1 i)) p :=
    ((hd i).comp continuous_fst).continuousAt
  have he (i : ι) := ((FiberBundle.continuousAt_totalSpace F _).1 (hc i)).2
  have hcoef (i : ι) : Continuous (fun q : U × F ↦ c.repr q.2 i) := by
    fun_prop
  have hsum : ContinuousAt
      (fun q : U × F ↦ ∑ i, c.repr q.2 i • (e ⟨(q.1 : B), d q.1 i⟩).2) p :=
    tendsto_finsetSum Finset.univ fun i _ ↦
      (hcoef i).continuousAt.smul (he i)
  apply hsum.congr_of_eventuallyEq (hmem.mono fun q hq ↦ ?_)
  dsimp only at e ⊢
  simp only [← e.continuousLinearMapAt_apply_of_mem (R := ℝ) hq,
    ← map_smul, ← map_sum, OrthonormalBasis.sum_repr_symm]
  exact (Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hq _).symm

open scoped Classical in
/-- A continuous local orthonormal basis defines a bundle chart whose fibre map sends that
basis to the fixed orthonormal model basis `c`. -/
def bundleTrivialization : Trivialization F (π F E) where
  toFun p := (p.proj, if h : p.proj ∈ U then c.repr.symm ((d ⟨p.proj, h⟩).repr p.2) else 0)
  invFun p := ⟨p.1, if h : p.1 ∈ U then (d ⟨p.1, h⟩).repr.symm (c.repr p.2) else 0⟩
  source := (π F E) ⁻¹' U
  target := U ×ˢ univ
  map_source' p hp := ⟨hp, mem_univ _⟩
  map_target' p hp := hp.1
  left_inv' p hp := by
    have hb : p.proj ∈ U := hp
    simp [hb]
  right_inv' p hp := by simp [hp.1]
  open_source := hU.preimage (FiberBundle.continuous_proj F E)
  open_target := hU.prod isOpen_univ
  continuousOn_toFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact ((FiberBundle.continuous_proj F E).comp continuous_subtype_val).prodMk
      ((c.repr.symm.continuous.comp (continuous_local_repr d hd)).congr
        fun p ↦ by simp [p.property])
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h : Continuous (fun p : U ×ˢ (univ : Set F) ↦
        ((⟨p.val.1, p.property.1⟩ : U), p.val.2)) :=
      ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
        (continuous_snd.comp continuous_subtype_val)
    exact ((continuous_local_repr_symm c d hd).comp h).congr fun p ↦ by
      simp [p.property.1]
  baseSet := U
  open_baseSet := hU
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

@[simp]
theorem bundleTrivialization_baseSet :
    (bundleTrivialization c hU d hd).baseSet = U := (rfl)

/-- On its domain, the chart reads the coordinates in the supplied orthonormal basis. -/
@[simp]
theorem bundleTrivialization_apply {b : B} (hb : b ∈ U) (v : E b) :
    bundleTrivialization c hU d hd ⟨b, v⟩ =
      (b, c.repr.symm ((d ⟨b, hb⟩).repr v)) := by
  simp [bundleTrivialization, Trivialization.toFun', hb]

instance bundleTrivialization_isLinear :
    (bundleTrivialization c hU d hd).IsLinear ℝ where
  linear b hb := by
    constructor
    · intro v w
      simp [bundleTrivialization_apply c hU d hd hb]
    · intro a v
      simp [bundleTrivialization_apply c hU d hd hb]

/-- The fibre equivalence of the chart is the isometry between the two orthonormal bases. -/
@[simp]
theorem bundleTrivialization_linearEquivAt {b : B} (hb : b ∈ U) :
    (bundleTrivialization c hU d hd).linearEquivAt ℝ b
      (by simpa only [bundleTrivialization_baseSet] using hb) =
      ((d ⟨b, hb⟩).repr.trans c.repr.symm).toLinearEquiv := by
  ext v
  exact congrArg Prod.snd (bundleTrivialization_apply c hU d hd hb v)

/-- The inverse chart reconstructs a vector from its model coordinates. -/
@[simp]
theorem bundleTrivialization_symm {b : B} (hb : b ∈ U) (v : F) :
    (bundleTrivialization c hU d hd).symm b v =
      (d ⟨b, hb⟩).repr.symm (c.repr v) := by
  let t := bundleTrivialization c hU d hd
  have ht : b ∈ t.baseSet := by
    simpa only [t, bundleTrivialization_baseSet] using hb
  rw [← Trivialization.symmL_apply (R := ℝ) t ht v]
  apply (t.continuousLinearEquivAt ℝ b ht).injective
  rw [Trivialization.coe_continuousLinearEquivAt_eq, t.continuousLinearMapAt_symmL ht]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) t ht]
  simp [t, bundleTrivialization_apply c hU d hd hb]

end OrthonormalBasis

namespace Bundle.Trivialization

variable [LinearOrder ι] [LocallyFiniteOrderBot ι] (e : Trivialization F (π F E)) [e.IsLinear ℝ]
  (c : OrthonormalBasis ι ℝ F)

/-- Orthogonalize a linear bundle chart by Gram–Schmidt, keeping its original base set. -/
def orthonormal : Trivialization F (π F E) :=
  OrthonormalBasis.bundleTrivialization c e.open_baseSet
    (e.orthonormalBasis c.toBasis) (e.continuous_orthonormalBasis c.toBasis)

@[simp]
theorem orthonormal_baseSet : (e.orthonormal c).baseSet = e.baseSet := by
  simp [orthonormal]

instance orthonormal_isLinear : (e.orthonormal c).IsLinear ℝ :=
  OrthonormalBasis.bundleTrivialization_isLinear c e.open_baseSet
    (e.orthonormalBasis c.toBasis) (e.continuous_orthonormalBasis c.toBasis)

/-- The orthogonalized chart reads coordinates in its Gram–Schmidt basis. -/
@[simp]
theorem orthonormal_apply {b : B} (hb : b ∈ e.baseSet) (v : E b) :
    e.orthonormal c ⟨b, v⟩ =
      (b, c.repr.symm ((e.orthonormalBasis c.toBasis ⟨b, hb⟩).repr v)) := by
  simp [orthonormal, hb]

/-- The inverse orthogonalized chart reconstructs a vector in its Gram–Schmidt basis. -/
@[simp]
theorem orthonormal_symm {b : B} (hb : b ∈ e.baseSet) (v : F) :
    (e.orthonormal c).symm b v =
      (e.orthonormalBasis c.toBasis ⟨b, hb⟩).repr.symm (c.repr v) := by
  simp [orthonormal, hb]

end Bundle.Trivialization

namespace OrthonormalBasis

variable [LinearOrder ι] [LocallyFiniteOrderBot ι]

/-- A continuous real Riemannian vector bundle with a finite orthonormal model basis has
a linear, norm-preserving trivialization around every base point. No separation or
paracompactness assumption on the base is needed. -/
theorem exists_orthonormal_trivialization (c : OrthonormalBasis ι ℝ F) (x : B) :
    ∃ e : Trivialization F (π F E), e.IsLinear ℝ ∧ x ∈ e.baseSet ∧
      ∀ (b : B), b ∈ e.baseSet → ∀ v : E b, ‖(e ⟨b, v⟩).2‖ = ‖v‖ := by
  let e := trivializationAt F E x
  refine ⟨e.orthonormal c, inferInstance, ?_, ?_⟩
  · simpa only [Trivialization.orthonormal_baseSet] using mem_baseSet_trivializationAt F E x
  · intro b hb v
    have hb' : b ∈ e.baseSet := by
      simpa only [Trivialization.orthonormal_baseSet] using hb
    simp [hb']

end OrthonormalBasis
