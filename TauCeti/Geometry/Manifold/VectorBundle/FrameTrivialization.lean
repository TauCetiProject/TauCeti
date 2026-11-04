/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
public import TauCeti.Geometry.Manifold.VectorBundle.MaximalAtlas

/-!
# Trivializations from local frames, and trivial line bundles

Let `V → B` be a `C^n` vector bundle whose model fibre `F` has a finite basis `b`. A `C^n` local
frame `s` of `V` on an open set `U` (in the sense of Mathlib's `IsLocalFrameOn`) determines a
linear trivialization over `U`: a vector `v ∈ V x` is sent to the vector of `F` having the same
coordinates in `b` as `v` has in the frame `s · x`. This file constructs that trivialization and
shows that it belongs to the maximal atlas of trivializations compatible with the `C^n` structure
of `V`. Conversely, for a member `e` of that maximal atlas, the sections `x ↦ e.symm x (b i)` form a
`C^n` local frame on its base set. So `V` admits a compatible trivialization over `U` exactly when
it admits a `C^n` local frame on `U`.

Read in a trivialization `e'` of the bundle's atlas, the frame becomes a family of invertible
operators of `F`, the coordinate change from the frame trivialization to `e'`. Its entries are the
coordinates of the frame sections in `e'`, hence `C^n`, and its inverse is `C^n` because operator
inversion is smooth. This gives both the continuity needed to define the trivialization and its
`C^n` compatibility with the atlas. The same construction for continuous local frames of a family
of subspaces of a topological vector bundle, with the subspace topology, is
`TauCeti.IsSubbundleFrameOn.trivialization`. Mathlib's `Bundle.Trivialization.localFrame`
gives the converse direction for trivializations of the bundle's own atlas.

For a bundle of rank one a single section that vanishes nowhere on `U` is a local frame on `U`.
Hence a line bundle admits a compatible trivialization over `U` exactly when it has a `C^n`
section without zeros on `U`; with `U = univ`, it is trivial exactly when it has a nowhere-zero
`C^n` section. Over the model `𝓘(ℂ, EB)` with `n = ∞`, the maximal atlas consists of the
holomorphic trivializations of a holomorphic vector bundle, and this is the criterion that a
holomorphic line bundle is holomorphically trivial exactly when it has a nowhere-vanishing
holomorphic section.

## Main definitions

* `IsLocalFrameOn.trivialization`: the trivialization over `U` defined by a local frame on an
  open set `U` and a basis of the model fibre.

## Main results

* `IsLocalFrameOn.trivialization_mem_maximalAtlas`: the trivialization of a `C^n` local frame lies
  in the maximal atlas of `C^n` trivializations.
* `Bundle.Trivialization.isLocalFrameOn_symm_of_mem_maximalAtlas`: a member of the maximal atlas
  carries the basis of the model fibre to a `C^n` local frame on its base set.
* `ContMDiffVectorBundle.exists_trivialization_baseSet_eq_iff_exists_isLocalFrameOn`: a compatible
  trivialization over an open set exists exactly when a `C^n` local frame on it does.
* `IsLocalFrameOn.of_finrank_eq_one`: in a bundle of rank one, a section without zeros is a frame.
* `ContMDiffVectorBundle.exists_trivialization_baseSet_eq_univ_iff_exists_ne_zero`: a line bundle
  has a global compatible trivialization exactly when it has a nowhere-zero `C^n` section.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2
  (holomorphic vector bundles, local frames and trivializations).
* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 10 (local frames and the local trivializations
  associated with them).
-/

public section

noncomputable section

open Bundle Set Module Filter
open scoped Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  {n : ℕ∞ω} {ι : Type*} {U : Set B}

namespace IsLocalFrameOn

variable {s : ι → Π x, V x}

/-! ### Coordinates in a frame -/

section Coordinates

variable (hs : IsLocalFrameOn IB F n s U) (b : Basis ι 𝕜 F)

open scoped Classical in
/-- Over `U`, the linear map sending a vector of `V x` to the vector of `F` with the same
coordinates in `b`; zero off `U`. -/
private def coords (x : B) : V x →ₗ[𝕜] F :=
  if hx : x ∈ U then ((hs.toBasisAt hx).equiv b (Equiv.refl ι)).toLinearMap else 0

open scoped Classical in
/-- Over `U`, the linear map sending a vector of `F` to the vector of `V x` with the same
coordinates in the frame; zero off `U`. -/
private def vec (x : B) : F →ₗ[𝕜] V x :=
  if hx : x ∈ U then ((hs.toBasisAt hx).equiv b (Equiv.refl ι)).symm.toLinearMap else 0

variable {x : B}

private theorem coords_of_mem (hx : x ∈ U) (v : V x) :
    hs.coords b x v = (hs.toBasisAt hx).equiv b (Equiv.refl ι) v := by
  simp [coords, hx]

private theorem vec_of_mem (hx : x ∈ U) (w : F) :
    hs.vec b x w = ((hs.toBasisAt hx).equiv b (Equiv.refl ι)).symm w := by
  simp [vec, hx]

private theorem vec_coords (hx : x ∈ U) (v : V x) : hs.vec b x (hs.coords b x v) = v := by
  rw [vec_of_mem hs b hx, coords_of_mem hs b hx, LinearEquiv.symm_apply_apply]

private theorem coords_vec (hx : x ∈ U) (w : F) : hs.coords b x (hs.vec b x w) = w := by
  rw [vec_of_mem hs b hx, coords_of_mem hs b hx, LinearEquiv.apply_symm_apply]

variable [Fintype ι] in
/-- Over `U`, the vector with coordinates `b.repr w` in the frame is the corresponding linear
combination of the frame sections. -/
private theorem vec_apply (hx : x ∈ U) (w : F) : hs.vec b x w = ∑ i, b.repr w i • s i x := by
  rw [vec_of_mem hs b hx, Basis.equiv_symm]
  conv_lhs => rw [← b.sum_repr w]
  simp only [map_sum, map_smul, Basis.equiv_apply, Equiv.refl_symm, Equiv.refl_apply,
    toBasisAt_coe]

end Coordinates

/-! ### The frame read in a trivialization -/

variable [CompleteSpace 𝕜]

section Operator

variable [Fintype ι] (s) (b : Basis ι 𝕜 F)

/-- The frame `s` at `x`, read in a trivialization `e'`, as the operator of `F` sending `w` to the
coordinates in `e'` of the combination of the frame with coefficients `b.repr w`. -/
private def frameOperator (e' : Trivialization F (π F V)) (x : B) : F →L[𝕜] F :=
  ∑ i, ContinuousLinearMap.smulRightL 𝕜 F F
    ((ContinuousLinearMap.proj i).comp (b.equivFunL : F →L[𝕜] ι → 𝕜)) (e' ⟨x, s i x⟩).2

variable {s} (e' : Trivialization F (π F V)) [e'.IsLinear 𝕜] {x : B}

private theorem frameOperator_apply (hx' : x ∈ e'.baseSet) (w : F) :
    frameOperator s b e' x w = (e' ⟨x, ∑ i, b.repr w i • s i x⟩).2 := by
  rw [← e'.continuousLinearMapAt_apply_of_mem (R := 𝕜) hx', map_sum]
  simp_rw [map_smul, e'.continuousLinearMapAt_apply_of_mem (R := 𝕜) hx']
  simp [frameOperator]

variable (hs : IsLocalFrameOn IB F n s U)

include hs in
private theorem frameOperator_vec (hx : x ∈ U) (hx' : x ∈ e'.baseSet) (w : F) :
    frameOperator s b e' x w = (e' ⟨x, hs.vec b x w⟩).2 := by
  rw [frameOperator_apply b e' hx', vec_apply hs b hx]

/-- Over `U ∩ e'.baseSet`, the frame read in `e'` is invertible: it is the composite of the
isomorphism of `F` onto `V x` given by the frame with the isomorphism `e'` of `V x` onto `F`. -/
private def frameEquiv (hx : x ∈ U) (hx' : x ∈ e'.baseSet) : F ≃L[𝕜] F :=
  have : FiniteDimensional 𝕜 F := .of_basis b
  (((hs.toBasisAt hx).equiv b (Equiv.refl ι)).symm.trans
    (e'.linearEquivAt 𝕜 x hx')).toContinuousLinearEquiv

private theorem coe_frameEquiv (hx : x ∈ U) (hx' : x ∈ e'.baseSet) :
    (frameEquiv b e' hs hx hx' : F →L[𝕜] F) = frameOperator s b e' x := by
  ext w
  rw [frameOperator_vec b e' hs hx hx', vec_of_mem hs b hx]
  simp [frameEquiv, Trivialization.linearEquivAt_apply]

include hs in
private theorem isInvertible_frameOperator (hx : x ∈ U) (hx' : x ∈ e'.baseSet) :
    (frameOperator s b e' x).IsInvertible :=
  ⟨_, coe_frameEquiv b e' hs hx hx'⟩

private theorem frameOperator_coords (hx : x ∈ U) (hx' : x ∈ e'.baseSet) (v : V x) :
    frameOperator s b e' x (hs.coords b x v) = (e' ⟨x, v⟩).2 := by
  rw [frameOperator_vec b e' hs hx hx', vec_coords hs b hx]

/-- Over `U ∩ e'.baseSet`, the coordinates of a vector in the frame are obtained from its
coordinates in `e'` by inverting the frame read in `e'`. -/
private theorem coords_eq_inverse (hx : x ∈ U) (hx' : x ∈ e'.baseSet) (v : V x) :
    hs.coords b x v = (frameOperator s b e' x).inverse (e' ⟨x, v⟩).2 := by
  rw [← frameOperator_coords b e' hs hx hx', ← coe_frameEquiv b e' hs hx hx',
    ContinuousLinearMap.inverse_equiv]
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]

omit [e'.IsLinear 𝕜] in
include hs in
private theorem continuousOn_frameOperator :
    ContinuousOn (frameOperator s b e') (U ∩ e'.baseSet) := by
  refine continuousOn_finsetSum _ fun i _ ↦ ?_
  refine (ContinuousLinearMap.smulRightL 𝕜 F F _).continuous.comp_continuousOn ?_
  exact continuous_snd.comp_continuousOn (e'.continuousOn.comp
    ((hs.contMDiffOn i).continuousOn.mono inter_subset_left) fun y hy ↦ e'.mem_source.2 hy.2)

include hs in
private theorem continuousAt_inverse_frameOperator (hU : IsOpen U) (hx : x ∈ U)
    (hx' : x ∈ e'.baseSet) :
    ContinuousAt (fun y ↦ (frameOperator s b e' y).inverse) x := by
  have : FiniteDimensional 𝕜 F := .of_basis b
  have : CompleteSpace F := FiniteDimensional.complete 𝕜 F
  exact ((isInvertible_frameOperator b e' hs hx hx').contDiffAt_map_inverse
    (n := 0)).continuousAt.comp ((continuousOn_frameOperator b e' hs).continuousAt
    ((hU.inter e'.open_baseSet).mem_nhds ⟨hx, hx'⟩))

end Operator

/-! ### The trivialization -/

section Trivialization

variable [VectorBundle 𝕜 F V] [Finite ι] (hs : IsLocalFrameOn IB F n s U) (hU : IsOpen U)
  (b : Basis ι 𝕜 F)

include hU in
private theorem continuousAt_coords {p : TotalSpace F V} (hp : p.proj ∈ U) :
    ContinuousAt (fun q : TotalSpace F V ↦ hs.coords b q.proj q.2) p := by
  let := Fintype.ofFinite ι
  set e' := trivializationAt F V p.proj
  have hp' : p.proj ∈ e'.baseSet := FiberBundle.mem_baseSet_trivializationAt' p.proj
  have hproj := (FiberBundle.continuous_proj F V).continuousAt (x := p)
  refine (((continuousAt_inverse_frameOperator b e' hs hU hp hp').comp hproj).clm_apply
    (e'.continuousAt (e'.mem_source.2 hp')).snd).congr ?_
  filter_upwards [hproj.preimage_mem_nhds ((hU.inter e'.open_baseSet).mem_nhds ⟨hp, hp'⟩)]
    with q hq
  exact (coords_eq_inverse b e' hs hq.1 hq.2 q.2).symm

include hU in
private theorem continuousAt_vec {q : B × F} (hq : q.1 ∈ U) :
    ContinuousAt (fun q : B × F ↦ TotalSpace.mk' F q.1 (hs.vec b q.1 q.2)) q := by
  let := Fintype.ofFinite ι
  rw [FiberBundle.continuousAt_totalSpace]
  set e' := trivializationAt F V q.1
  have hq' : q.1 ∈ e'.baseSet := FiberBundle.mem_baseSet_trivializationAt' q.1
  refine ⟨continuousAt_fst, ((((continuousOn_frameOperator b e' hs).continuousAt
    ((hU.inter e'.open_baseSet).mem_nhds ⟨hq, hq'⟩)).comp continuousAt_fst).clm_apply
      continuousAt_snd).congr ?_⟩
  filter_upwards [continuousAt_fst.preimage_mem_nhds
    ((hU.inter e'.open_baseSet).mem_nhds ⟨hq, hq'⟩)] with r hr
  exact frameOperator_vec b e' hs hr.1 hr.2 r.2

/-- The trivialization of `V` over an open set `U` defined by a local frame `s` on `U` and a basis
`b` of the model fibre: over `U`, a vector of `V x` is sent to the vector of `F` with the same
coordinates in `b` as it has in the frame `s · x`. -/
def trivialization : Trivialization F (π F V) where
  toFun p := (p.proj, hs.coords b p.proj p.2)
  invFun q := TotalSpace.mk' F q.1 (hs.vec b q.1 q.2)
  source := π F V ⁻¹' U
  target := U ×ˢ univ
  map_source' _ hp := ⟨hp, mem_univ _⟩
  map_target' _ hq := hq.1
  left_inv' p hp := by
    dsimp only
    rw [vec_coords hs b hp]
  right_inv' q hq := by
    dsimp only
    rw [coords_vec hs b hq.1]
  open_source := hU.preimage (FiberBundle.continuous_proj F V)
  open_target := hU.prod isOpen_univ
  continuousOn_toFun := continuousOn_of_forall_continuousAt fun _ hp ↦
    (FiberBundle.continuous_proj F V).continuousAt.prodMk (continuousAt_coords hs hU b hp)
  continuousOn_invFun := continuousOn_of_forall_continuousAt fun _ hq ↦
    continuousAt_vec hs hU b hq.1
  baseSet := U
  open_baseSet := hU
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

@[simp]
theorem baseSet_trivialization : (hs.trivialization hU b).baseSet = U :=
  (rfl)

private theorem trivialization_apply_eq (p : TotalSpace F V) :
    hs.trivialization hU b p = (p.proj, hs.coords b p.proj p.2) :=
  (rfl)

private theorem trivialization_symm_apply_eq (q : B × F) :
    (hs.trivialization hU b).toOpenPartialHomeomorph.symm q =
      TotalSpace.mk' F q.1 (hs.vec b q.1 q.2) :=
  (rfl)

/-- Over `U`, the frame trivialization sends a vector to the vector of `F` with the same
coordinates in `b` as it has in the frame. -/
theorem trivialization_apply {x : B} (hx : x ∈ U) (v : V x) :
    hs.trivialization hU b ⟨x, v⟩ = (x, (hs.toBasisAt hx).equiv b (Equiv.refl ι) v) := by
  rw [trivialization_apply_eq, coords_of_mem hs b hx]

/-- Over `U`, the frame trivialization sends the frame vector `s i x` to the basis vector `b i`. -/
@[simp]
theorem trivialization_apply_frame {x : B} (hx : x ∈ U) (i : ι) :
    hs.trivialization hU b ⟨x, s i x⟩ = (x, b i) := by
  rw [trivialization_apply hs hU b hx, ← toBasisAt_coe hs hx, Basis.equiv_apply,
    Equiv.refl_apply]

variable [Fintype ι] in
/-- Over `U`, the inverse of the frame trivialization sends `w` to the combination of the frame
with coefficients `b.repr w`. -/
@[simp]
theorem trivialization_symm_apply {x : B} (hx : x ∈ U) (w : F) :
    (hs.trivialization hU b).symm x w = ∑ i, b.repr w i • s i x := by
  rw [Trivialization.symm_apply _ hx]
  exact vec_apply hs b hx w

/-- The frame trivialization is fibrewise linear. -/
instance isLinear_trivialization : (hs.trivialization hU b).IsLinear 𝕜 where
  linear x _ := (hs.coords b x).isLinear

variable [Fintype ι] in
/-- The coordinate change from the frame trivialization to a linear trivialization `e'` is the
frame read in `e'`. -/
private theorem coordChangeL_trivialization (e' : Trivialization F (π F V)) [e'.IsLinear 𝕜]
    {x : B} (hx : x ∈ U ∩ e'.baseSet) :
    ((hs.trivialization hU b).coordChangeL 𝕜 e' x : F →L[𝕜] F) = frameOperator s b e' x := by
  ext w
  rw [ContinuousLinearEquiv.coe_coe, Trivialization.coordChangeL_apply' _ _ hx,
    trivialization_symm_apply_eq, frameOperator_vec b e' hs hx.1 hx.2]

/-- **Local frames give compatible trivializations.** The trivialization defined by a `C^n` local
frame lies in the maximal atlas of trivializations compatible with the `C^n` structure of the
bundle. -/
theorem trivialization_mem_maximalAtlas [ContMDiffVectorBundle n F V IB] :
    (hs.trivialization hU b).toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F V) := by
  let := Fintype.ofFinite ι
  have : FiniteDimensional 𝕜 F := .of_basis b
  have : CompleteSpace F := FiniteDimensional.complete 𝕜 F
  refine (Trivialization.mem_maximalAtlas_contMDiffFiberwiseLinear_iff IB n _).2 fun e' _ ↦ ?_
  -- Read in `e'`, the frame is a `C^n` family of operators, its coordinates in `e'` being `C^n`.
  have hframe : ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (frameOperator s b e') (U ∩ e'.baseSet) := by
    refine contMDiffOn_finsetSum fun i _ ↦ ?_
    refine (ContinuousLinearMap.smulRightL 𝕜 F F _).contMDiff.comp_contMDiffOn ?_
    exact (Trivialization.contMDiffOn_section_iff_of_mem_maximalAtlas
      (Trivialization.mem_maximalAtlas_of_memTrivializationAtlas IB n e')
      inter_subset_right).1 ((hs.contMDiffOn i).mono inter_subset_left)
  -- The reverse coordinate change is the inverse of the frame read in `e'`.
  have hsymm : ∀ x ∈ U ∩ e'.baseSet, (e'.coordChangeL 𝕜 (hs.trivialization hU b) x : F →L[𝕜] F) =
      (frameOperator s b e' x).inverse := fun x hx ↦ by
    rw [← (hs.trivialization hU b).symm_coordChangeL e' ⟨hx.2, hx.1⟩,
      ← ContinuousLinearMap.inverse_equiv, coordChangeL_trivialization hs hU b e' hx]
  refine ⟨hframe.congr fun x hx ↦ coordChangeL_trivialization hs hU b e' hx, fun x hx ↦ ?_⟩
  -- Operator inversion is smooth at the invertible operator `frameOperator s b e' x`.
  have hinv := (isInvertible_frameOperator b e' hs hx.1 hx.2).contDiffAt_map_inverse (n := n)
  exact (hinv.contMDiffAt.comp_contMDiffWithinAt x (hframe x hx)).congr hsymm (hsymm x hx)

end Trivialization

end IsLocalFrameOn

/-! ### Frames from compatible trivializations -/

namespace Bundle.Trivialization

variable [VectorBundle 𝕜 F V] [ContMDiffVectorBundle n F V IB]

/-- **Compatible trivializations give local frames.** A member `e` of the maximal atlas of `C^n`
trivializations carries a basis `b` of the model fibre to the `C^n` local frame
`x ↦ e.symm x (b i)` on its base set. -/
theorem isLocalFrameOn_symm_of_mem_maximalAtlas (e : Trivialization F (π F V)) [e.IsLinear 𝕜]
    (he : e.toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F V))
    (b : Basis ι 𝕜 F) :
    IsLocalFrameOn IB F n (fun i x ↦ e.symm x (b i)) e.baseSet := by
  have hb : ∀ {x} (hx : x ∈ e.baseSet),
      (fun i ↦ e.symm x (b i)) = b.map (e.linearEquivAt 𝕜 x hx).symm := fun hx ↦ by
    ext i
    simp [Trivialization.linearEquivAt_symm_apply]
  refine ⟨fun hx ↦ hb hx ▸ Basis.linearIndependent _, fun hx ↦ hb hx ▸ (Basis.span_eq _).ge,
    fun i ↦ ?_⟩
  refine (contMDiffOn_section_iff_of_mem_maximalAtlas he subset_rfl).2
    (contMDiffOn_const (c := b i) |>.congr fun x hx ↦ ?_)
  rw [e.apply_mk_symm hx]

end Bundle.Trivialization

namespace ContMDiffVectorBundle

variable [CompleteSpace 𝕜] [VectorBundle 𝕜 F V] [ContMDiffVectorBundle n F V IB]

/-- A `C^n` vector bundle whose model fibre has a finite basis indexed by `ι` admits a
trivialization over an open set `U` in the maximal atlas of `C^n` trivializations exactly when it
admits a `C^n` local frame on `U` indexed by `ι`. -/
theorem exists_trivialization_baseSet_eq_iff_exists_isLocalFrameOn [Finite ι] (hU : IsOpen U)
    (b : Basis ι 𝕜 F) :
    (∃ (e : Trivialization F (π F V)) (_ : e.IsLinear 𝕜),
        e.toOpenPartialHomeomorph ∈
          (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F V) ∧ e.baseSet = U) ↔
      ∃ s : ι → Π x, V x, IsLocalFrameOn IB F n s U := by
  constructor
  · rintro ⟨e, _, he, rfl⟩
    exact ⟨_, e.isLocalFrameOn_symm_of_mem_maximalAtlas he b⟩
  · rintro ⟨s, hs⟩
    exact ⟨hs.trivialization hU b, inferInstance, hs.trivialization_mem_maximalAtlas hU b, rfl⟩

end ContMDiffVectorBundle

/-! ### Line bundles -/

variable [VectorBundle 𝕜 F V]

/-- In a vector bundle of rank one, a `C^n` section without zeros on `U` is a `C^n` local frame
on `U`, indexed by any type with a single element. -/
theorem IsLocalFrameOn.of_finrank_eq_one [Unique ι] (hF : finrank 𝕜 F = 1) {σ : Π x, V x}
    (hσ : ContMDiffOn IB (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (σ x)) U)
    (hσ₀ : ∀ x ∈ U, σ x ≠ 0) :
    IsLocalFrameOn IB F n (fun _ : ι ↦ σ) U := by
  have hV : ∀ x, finrank 𝕜 (V x) = 1 := fun x ↦
    ((trivializationAt F V x).linearEquivAt 𝕜 x
      (FiberBundle.mem_baseSet_trivializationAt' x)).finrank_eq.trans hF
  have hb : ∀ {x} (hx : x ∈ U),
      (fun _ : ι ↦ σ x) = FiniteDimensional.basisSingleton ι (hV x) (σ x) (hσ₀ x hx) := fun hx ↦ by
    ext
    rw [FiniteDimensional.basisSingleton_apply]
  exact ⟨fun hx ↦ hb hx ▸ Basis.linearIndependent _, fun hx ↦ hb hx ▸ (Basis.span_eq _).ge,
    fun _ ↦ hσ⟩

namespace ContMDiffVectorBundle

variable [CompleteSpace 𝕜] [ContMDiffVectorBundle n F V IB]

/-- A `C^n` line bundle admits a trivialization over an open set `U` in the maximal atlas of `C^n`
trivializations exactly when it has a `C^n` section without zeros on `U`. -/
theorem exists_trivialization_baseSet_eq_iff_exists_ne_zero (hF : finrank 𝕜 F = 1)
    (hU : IsOpen U) :
    (∃ (e : Trivialization F (π F V)) (_ : e.IsLinear 𝕜),
        e.toOpenPartialHomeomorph ∈
          (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F V) ∧ e.baseSet = U) ↔
      ∃ σ : Π x, V x, ContMDiffOn IB (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (σ x)) U ∧
        ∀ x ∈ U, σ x ≠ 0 := by
  rw [exists_trivialization_baseSet_eq_iff_exists_isLocalFrameOn hU (basisUnique Unit hF)]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s (), hs.contMDiffOn (), fun x hx ↦ (hs.linearIndependent hx).ne_zero ()⟩
  · rintro ⟨σ, hσ, hσ₀⟩
    exact ⟨_, .of_finrank_eq_one hF hσ hσ₀⟩

/-- **The trivial line bundle criterion.** A `C^n` line bundle has a trivialization over the whole
base in the maximal atlas of `C^n` trivializations, that is, it is trivial as a `C^n` vector
bundle, exactly when it has a `C^n` section that vanishes nowhere. For a holomorphic line bundle,
over `𝓘(ℂ, EB)` with `n = ∞`, this says that it is holomorphically trivial exactly when it has a
nowhere-vanishing holomorphic section. -/
theorem exists_trivialization_baseSet_eq_univ_iff_exists_ne_zero (hF : finrank 𝕜 F = 1) :
    (∃ (e : Trivialization F (π F V)) (_ : e.IsLinear 𝕜),
        e.toOpenPartialHomeomorph ∈
          (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F V) ∧ e.baseSet = univ) ↔
      ∃ σ : Π x, V x, ContMDiff IB (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (σ x)) ∧
        ∀ x, σ x ≠ 0 := by
  simpa [contMDiffOn_univ] using exists_trivialization_baseSet_eq_iff_exists_ne_zero hF isOpen_univ

end ContMDiffVectorBundle
