/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Topology.Algebra.Star.Unitary
public import TauCeti.Topology.VectorBundle.GramSchmidt

/-!
# The orthonormal frame bundle of a Riemannian vector bundle

Let `E → B` be a continuous Riemannian vector bundle with model fibre `F`, and let `V` be a real
inner product space. An orthonormal frame of the fibre `E b` modelled on `V` is a linear isometric
equivalence `V ≃ₗᵢ[ℝ] E b`; when `V` is `EuclideanSpace ℝ (Fin n)` this is an ordered orthonormal
basis of `E b`. The orthonormal frame bundle `TauCeti.OrthonormalFrameBundle F E V` is the set of
pairs of a base point and an orthonormal frame of the fibre over it. It carries the topology of
pointwise convergence of frames in the total space of `E`: a map into it is continuous exactly
when, for every `v : V`, the image of `v` under the frame is a continuous map into the total space
(`TauCeti.OrthonormalFrameBundle.continuous_iff`).

The orthogonal group of `V`, as the unitary group `unitary (V →L[ℝ] V)` of the operator algebra
with its operator-norm topology, acts on the right by precomposition. When `V` is
finite-dimensional the action is continuous, and on each fibre it is free
(`TauCeti.OrthonormalFrameBundle.smul_eq_self_iff`) and transitive
(`TauCeti.OrthonormalFrameBundle.exists_smul_eq_iff`).

A linear trivialization `e` of `E`, a model basis `c` of `F` and an orthonormal basis `b` of `V`
with a common finite index type give a local orthonormal frame over `e.baseSet`
(`Bundle.Trivialization.orthonormalFrame`): Gram–Schmidt applied to the inverse images of `c`,
matched with `b`. It is a continuous local section of the frame bundle
(`Bundle.Trivialization.continuous_orthonormalFrame`). Dividing by it trivializes the frame bundle
over `e.baseSet` with fibre the orthogonal group (`Bundle.Trivialization.orthonormalFrameBundle`),
and this trivialization is equivariant for the right action
(`Bundle.Trivialization.orthonormalFrameBundle_smul`). So when `V` has the dimension of `F`, the
orthonormal frame bundle is locally trivial with structure group the orthogonal group, by
trivializations equivariant for the action
(`TauCeti.OrthonormalFrameBundle.exists_trivialization`).

## Main definitions

* `TauCeti.OrthonormalFrameBundle F E V`: the orthonormal frames of the fibres of `E` modelled
  on `V`, with the right action of `unitary (V →L[ℝ] V)`.
* `Bundle.Trivialization.orthonormalFrame`: the Gram–Schmidt orthonormal frame over the base set
  of a linear trivialization.
* `Bundle.Trivialization.orthonormalFrameBundle`: the induced trivialization of the frame bundle.

## Main results

* `TauCeti.OrthonormalFrameBundle.continuous_totalSpaceMk_frame_apply`: applying frames to vectors
  is jointly continuous.
* `TauCeti.OrthonormalFrameBundle.smul_eq_self_iff`,
  `TauCeti.OrthonormalFrameBundle.exists_smul_eq_iff`: the action is free and transitive on fibres.
* `TauCeti.OrthonormalFrameBundle.exists_trivialization`: the frame bundle is locally trivial,
  equivariantly for the action.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §2 (Euclidean vector bundles and orthonormal frames by Gram–Schmidt).
* D. Husemoller, *Fibre Bundles*, third edition, Graduate Texts in Mathematics 20, Springer
  (1994), Chapter 4, §1 (principal bundles) and Chapter 5, §§4–5 (the principal bundle of
  orthonormal frames).
-/

public section

noncomputable section

open Bundle Set InnerProductSpace MulOpposite
open scoped Topology

variable {B : Type*} {F : Type*} {E : B → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace TauCeti

/-- The orthonormal frame bundle of the Riemannian vector bundle `E` with model fibre `F`,
modelled on the inner product space `V`: the pairs of a point of the base and a linear isometric
equivalence from `V` to the fibre over it. The model fibre `F` enters only through the topology,
which is read in the total space of `E`. -/
structure OrthonormalFrameBundle (F : Type*) (E : B → Type*) [∀ x, NormedAddCommGroup (E x)]
    [∀ x, InnerProductSpace ℝ (E x)] (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] where
  /-- The base point. -/
  proj : B
  /-- The orthonormal frame of the fibre over the base point. -/
  frame : V ≃ₗᵢ[ℝ] E proj

namespace OrthonormalFrameBundle

/-- Two frames over the same base point are equal exactly when they are equal as linear isometric
equivalences. -/
theorem mk_eq_mk_iff {b : B} {φ ψ : V ≃ₗᵢ[ℝ] E b} :
    (⟨b, φ⟩ : OrthonormalFrameBundle F E V) = ⟨b, ψ⟩ ↔ φ = ψ := by
  constructor
  · exact fun h ↦ eq_of_heq (OrthonormalFrameBundle.mk.inj h).2
  · rintro rfl
    rfl

section Action

variable [CompleteSpace V]

/-- The right action of the orthogonal group `unitary (V →L[ℝ] V)` on orthonormal frames by
precomposition: `op g` carries the frame `φ` to `φ ∘ g`. -/
instance : MulAction (unitary (V →L[ℝ] V))ᵐᵒᵖ (OrthonormalFrameBundle F E V) where
  smul g p := ⟨p.proj, (Unitary.linearIsometryEquiv g.unop).trans p.frame⟩
  -- By the definition of `smul`, both sides of each action law are frames over `p.proj`, so
  -- `mk_eq_mk_iff` reduces the law to an identity of linear isometric equivalences. In
  -- `mul_smul`, the frame of `h • p` is by definition the composite that `trans_assoc` expects.
  one_smul p := mk_eq_mk_iff.2 <| by
    rw [unop_one, map_one, LinearIsometryEquiv.one_def, LinearIsometryEquiv.refl_trans]
  mul_smul g h p := mk_eq_mk_iff.2 <| by
    rw [unop_mul, map_mul, LinearIsometryEquiv.mul_def]
    exact LinearIsometryEquiv.trans_assoc _ _ _

/-- The action preserves the base point. -/
@[simp]
theorem proj_smul (g : (unitary (V →L[ℝ] V))ᵐᵒᵖ) (p : OrthonormalFrameBundle F E V) :
    (g • p).proj = p.proj :=
  rfl

/-- The action precomposes the frame with the orthogonal transformation. -/
@[simp]
theorem frame_smul_apply (g : (unitary (V →L[ℝ] V))ᵐᵒᵖ) (p : OrthonormalFrameBundle F E V)
    (v : V) : (g • p).frame v = p.frame ((g.unop : V →L[ℝ] V) v) :=
  rfl

/-- The action is free: only the identity fixes a frame. -/
@[simp]
theorem smul_eq_self_iff {g : unitary (V →L[ℝ] V)} {p : OrthonormalFrameBundle F E V} :
    op g • p = p ↔ g = 1 := by
  refine ⟨fun h ↦ ?_, by rintro rfl; exact one_smul _ p⟩
  obtain ⟨b, φ⟩ := p
  have hφ : (Unitary.linearIsometryEquiv g).trans φ = φ := mk_eq_mk_iff.1 h
  refine Unitary.linearIsometryEquiv.injective ?_
  rw [map_one, LinearIsometryEquiv.one_def]
  ext v
  simpa using congrArg (fun ψ : V ≃ₗᵢ[ℝ] E b ↦ φ.symm (ψ v)) hφ

/-- The action is transitive on fibres: two frames differ by an orthogonal transformation exactly
when they lie over the same base point. -/
theorem exists_smul_eq_iff {p q : OrthonormalFrameBundle F E V} :
    (∃ g : unitary (V →L[ℝ] V), op g • p = q) ↔ p.proj = q.proj := by
  refine ⟨fun ⟨g, h⟩ ↦ h ▸ rfl, fun h ↦ ?_⟩
  obtain ⟨b, φ⟩ := p
  obtain ⟨b', ψ⟩ := q
  obtain rfl : b = b' := h
  refine ⟨Unitary.linearIsometryEquiv.symm (ψ.trans φ.symm), mk_eq_mk_iff.2 ?_⟩
  ext v
  simp

end Action

variable [TopologicalSpace (TotalSpace F E)]

/-- The topology of pointwise convergence of frames: the coarsest topology for which applying
the frames to each vector of `V` is continuous into the total space of `E`. -/
instance : TopologicalSpace (OrthonormalFrameBundle F E V) :=
  .induced (fun p v ↦ (⟨p.proj, p.frame v⟩ : TotalSpace F E)) Pi.topologicalSpace

/-- A map into the orthonormal frame bundle is continuous exactly when its frames, applied to each
vector of `V`, give continuous maps into the total space of `E`. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → OrthonormalFrameBundle F E V} :
    Continuous f ↔ ∀ v, Continuous fun x ↦ (⟨(f x).proj, (f x).frame v⟩ : TotalSpace F E) :=
  continuous_induced_rng.trans continuous_pi_iff

/-- Applying the frames to a fixed vector of `V` is continuous into the total space of `E`. -/
theorem continuous_totalSpaceMk_frame (v : V) :
    Continuous fun p : OrthonormalFrameBundle F E V ↦ (⟨p.proj, p.frame v⟩ : TotalSpace F E) :=
  continuous_iff.1 continuous_id v

variable [NormedAddCommGroup F] [TopologicalSpace B] [FiberBundle F E]

/-- The projection of the orthonormal frame bundle to the base is continuous. -/
theorem continuous_proj : Continuous (proj : OrthonormalFrameBundle F E V → B) :=
  (FiberBundle.continuous_proj F E).comp (continuous_totalSpaceMk_frame 0)

variable [NormedSpace ℝ F] [VectorBundle ℝ F E]

/-- The frame at `p`, read as a linear map `V →L[ℝ] F` in the linear trivialization `e`. -/
private def coord (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    (p : OrthonormalFrameBundle F E V) : V →L[ℝ] F :=
  (e.continuousLinearMapAt ℝ p.proj).comp (p.frame.toContinuousLinearEquiv : V →L[ℝ] E p.proj)

omit [VectorBundle ℝ F E] in
private theorem coord_apply {e : Trivialization F (π F E)} [e.IsLinear ℝ]
    {p : OrthonormalFrameBundle F E V} (hp : p.proj ∈ e.baseSet) (v : V) :
    coord e p v = (e ⟨p.proj, p.frame v⟩).2 := by
  simp only [coord, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  exact e.continuousLinearMapAt_apply_of_mem (R := ℝ) hp _

omit [VectorBundle ℝ F E] in
private theorem continuousOn_coord [FiniteDimensional ℝ V] (e : Trivialization F (π F E))
    [e.IsLinear ℝ] :
    ContinuousOn (coord e) (proj ⁻¹' e.baseSet : Set (OrthonormalFrameBundle F E V)) := by
  refine continuousOn_clm_apply.2 fun v ↦ ?_
  have h : ContinuousOn (fun p : OrthonormalFrameBundle F E V ↦ (e ⟨p.proj, p.frame v⟩).2)
      (proj ⁻¹' e.baseSet) :=
    continuous_snd.comp_continuousOn (e.continuousOn.comp
      (continuous_totalSpaceMk_frame v).continuousOn fun p hp ↦ e.mem_source.2 hp)
  exact h.congr fun p hp ↦ coord_apply hp v

/-- Applying frames to vectors is jointly continuous. -/
theorem continuous_totalSpaceMk_frame_apply [FiniteDimensional ℝ V] :
    Continuous fun q : OrthonormalFrameBundle F E V × V ↦
      (⟨q.1.proj, q.1.frame q.2⟩ : TotalSpace F E) := by
  refine continuous_iff_continuousAt.2 fun q₀ ↦ ?_
  let e := trivializationAt F E q₀.1.proj
  have hU : proj ⁻¹' e.baseSet ∈ 𝓝 q₀.1 :=
    (e.open_baseSet.preimage continuous_proj).mem_nhds (mem_baseSet_trivializationAt F E _)
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(continuous_proj.comp continuous_fst).continuousAt, ?_⟩
  -- Near `q₀`, the coordinates in `e` are the application of the continuous family `coord e`.
  have hc : ContinuousAt (fun q : OrthonormalFrameBundle F E V × V ↦ coord e q.1 q.2) q₀ :=
    (((continuousOn_coord e).continuousAt hU).comp continuous_fst.continuousAt).clm_apply
      continuous_snd.continuousAt
  refine hc.congr ?_
  filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds hU] with q hq
  exact coord_apply hq q.2

/-- The right action of the orthogonal group on orthonormal frames is continuous. -/
instance [FiniteDimensional ℝ V] :
    ContinuousSMul (unitary (V →L[ℝ] V))ᵐᵒᵖ (OrthonormalFrameBundle F E V) where
  continuous_smul := continuous_iff.2 fun _ ↦ continuous_totalSpaceMk_frame_apply.comp
    (continuous_snd.prodMk (((continuous_subtype_val.comp continuous_unop).comp
      continuous_fst).clm_apply continuous_const))

end OrthonormalFrameBundle

end TauCeti

open TauCeti OrthonormalFrameBundle

namespace Bundle.Trivialization

variable [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace (TotalSpace F E)]
  [TopologicalSpace B] [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]
  (e : Trivialization F (π F E)) [e.IsLinear ℝ]
  {ι : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι]
  (c : Module.Basis ι ℝ F) (b : OrthonormalBasis ι ℝ V)

/-- The local orthonormal frame over the base set of a linear trivialization `e`: the
Gram–Schmidt orthonormal basis `e.orthonormalBasis c` of each fibre, matched with the orthonormal
basis `b` of `V`. -/
def orthonormalFrame (y : e.baseSet) : V ≃ₗᵢ[ℝ] E y :=
  b.equiv (e.orthonormalBasis c y) (Equiv.refl ι)

omit [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E] in
/-- The local orthonormal frame sends `v` to the combination of the Gram–Schmidt basis vectors
with the coordinates of `v` in `b`. -/
theorem orthonormalFrame_apply (y : e.baseSet) (v : V) :
    e.orthonormalFrame c b y v = ∑ i, ⟪b i, v⟫_ℝ • e.orthonormalBasis c y i := by
  simp [orthonormalFrame, OrthonormalBasis.equiv_apply, OrthonormalBasis.repr_apply_apply]

omit [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E] in
/-- The inverse of the local orthonormal frame reads a vector of the fibre through its coordinates
in the Gram–Schmidt basis. -/
theorem orthonormalFrame_symm_apply (y : e.baseSet) (x : E y) :
    (e.orthonormalFrame c b y).symm x = ∑ i, ⟪e.orthonormalBasis c y i, x⟫_ℝ • b i := by
  simp [orthonormalFrame, OrthonormalBasis.equiv_apply, OrthonormalBasis.repr_apply_apply]

omit [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E] in
/-- The local orthonormal frame sends the basis `b` to the Gram–Schmidt basis. -/
@[simp]
theorem orthonormalFrame_apply_basis (y : e.baseSet) (i : ι) :
    e.orthonormalFrame c b y (b i) = e.orthonormalBasis c y i := by
  simp [orthonormalFrame]

/-- The local orthonormal frame is a continuous local section of the orthonormal frame bundle. -/
theorem continuous_orthonormalFrame :
    Continuous fun y : e.baseSet ↦
      (⟨y, e.orthonormalFrame c b y⟩ : OrthonormalFrameBundle F E V) := by
  refine OrthonormalFrameBundle.continuous_iff.2 fun v ↦ ?_
  have hT (i : ι) : Continuous fun y : e.baseSet ↦ (e ⟨y, e.orthonormalBasis c y i⟩).2 :=
    continuous_snd.comp (e.continuousOn.comp_continuous (e.continuous_orthonormalBasis c i)
      fun y ↦ e.mem_source.2 y.2)
  have hc : Continuous fun y : e.baseSet ↦
      ∑ i, ⟪b i, v⟫_ℝ • (e ⟨y, e.orthonormalBasis c y i⟩).2 :=
    continuous_finsetSum Finset.univ fun i _ ↦ (hT i).const_smul _
  refine (e.continuousOn_symm.comp_continuous (continuous_subtype_val.prodMk hc)
    fun y ↦ ⟨y.2, mem_univ _⟩).congr fun y ↦ ?_
  -- In the coordinates of `e`, the frame applied to `v` is the matching combination of the
  -- coordinates of the Gram–Schmidt basis vectors.
  have hsum : ∑ i, ⟪b i, v⟫_ℝ • (e ⟨y, e.orthonormalBasis c y i⟩).2 =
      (e ⟨y, e.orthonormalFrame c b y v⟩).2 := by
    simp only [← e.continuousLinearMapAt_apply_of_mem (R := ℝ) y.2, orthonormalFrame_apply,
      map_sum, map_smul]
  simp [hsum, e.symm_apply_apply_mk y.2]

open scoped Classical in
/-- The chosen frame over each point: the local frame over the base set of `e`, and the local
frame of the preferred trivialization elsewhere. Only its values over `e.baseSet` matter. -/
private def frameAt (y : B) : V ≃ₗᵢ[ℝ] E y :=
  if h : y ∈ e.baseSet then e.orthonormalFrame c b ⟨y, h⟩
  else (trivializationAt F E y).orthonormalFrame c b ⟨y, mem_baseSet_trivializationAt F E y⟩

omit [IsContinuousRiemannianBundle F E] in
private theorem frameAt_of_mem {y : B} (h : y ∈ e.baseSet) :
    frameAt e c b y = e.orthonormalFrame c b ⟨y, h⟩ := by
  simp [frameAt, h]

variable [FiniteDimensional ℝ V]

/-- The trivialization of the orthonormal frame bundle over the base set of a linear
trivialization `e`, with fibre the orthogonal group of `V`: a frame `φ` over `y` goes to
`(y, σ_y⁻¹ ∘ φ)`, where `σ = e.orthonormalFrame c b` is the local orthonormal frame. -/
def orthonormalFrameBundle :
    Trivialization (unitary (V →L[ℝ] V)) (proj : OrthonormalFrameBundle F E V → B) where
  toFun p := (p.proj, Unitary.linearIsometryEquiv.symm (p.frame.trans (frameAt e c b p.proj).symm))
  invFun q := op q.2 • (⟨q.1, frameAt e c b q.1⟩ : OrthonormalFrameBundle F E V)
  source := proj ⁻¹' e.baseSet
  target := e.baseSet ×ˢ univ
  map_source' _ hp := ⟨hp, mem_univ _⟩
  map_target' _ hq := hq.1
  left_inv' p _ := by
    obtain ⟨y, φ⟩ := p
    refine mk_eq_mk_iff.2 ?_
    ext v
    simp
  right_inv' q _ := by
    refine Prod.ext rfl (Unitary.linearIsometryEquiv.injective ?_)
    ext v
    simp [← Unitary.coe_linearIsometryEquiv_apply]
  open_source := e.open_baseSet.preimage continuous_proj
  open_target := e.open_baseSet.prod isOpen_univ
  continuousOn_toFun := by
    refine continuous_proj.continuousOn.prodMk ?_
    refine Topology.IsInducing.subtypeVal.continuousOn_iff.2
      (continuousOn_clm_apply.2 fun v ↦ ?_)
    rw [continuousOn_iff_continuous_domRestrict]
    have hσ (i : ι) : Continuous fun p : (proj ⁻¹' e.baseSet : Set (OrthonormalFrameBundle F E V)) ↦
        (⟨p.1.proj, e.orthonormalBasis c ⟨p.1.proj, p.2⟩ i⟩ : TotalSpace F E) :=
      (e.continuous_orthonormalBasis c i).comp
        ((continuous_proj.comp continuous_subtype_val).subtype_mk _)
    have hφ : Continuous fun p : (proj ⁻¹' e.baseSet : Set (OrthonormalFrameBundle F E V)) ↦
        (⟨p.1.proj, p.1.frame v⟩ : TotalSpace F E) :=
      (continuous_totalSpaceMk_frame v).comp continuous_subtype_val
    -- Over the base set, the quotient by the local frame applied to `v` has the coordinates
    -- `⟪σ i, φ v⟫` in the orthonormal basis `b`.
    refine (continuous_finsetSum Finset.univ fun i _ ↦
      ((hσ i).inner_bundle hφ).smul (continuous_const (y := b i))).congr fun p ↦ ?_
    simp [frameAt_of_mem e c b p.2, orthonormalFrame_symm_apply]
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hσ : Continuous fun q : (e.baseSet ×ˢ univ : Set (B × unitary (V →L[ℝ] V))) ↦
        (⟨q.1.1, frameAt e c b q.1.1⟩ : OrthonormalFrameBundle F E V) :=
      ((e.continuous_orthonormalFrame c b).comp
        ((continuous_fst.comp continuous_subtype_val).subtype_mk fun q ↦ q.2.1)).congr fun q ↦
          mk_eq_mk_iff.2 (frameAt_of_mem e c b q.2.1).symm
    exact (continuous_op.comp (continuous_snd.comp continuous_subtype_val)).smul hσ
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

/-- The induced trivialization of the frame bundle has the base set of `e`. -/
@[simp]
theorem baseSet_orthonormalFrameBundle :
    (e.orthonormalFrameBundle c b :
      Trivialization _ (proj : OrthonormalFrameBundle F E V → B)).baseSet = e.baseSet :=
  (rfl)

private theorem orthonormalFrameBundle_symm_apply' (q : B × unitary (V →L[ℝ] V)) :
    (e.orthonormalFrameBundle c b).toOpenPartialHomeomorph.symm q =
      op q.2 • (⟨q.1, frameAt e c b q.1⟩ : OrthonormalFrameBundle F E V) :=
  rfl

private theorem orthonormalFrameBundle_apply (p : OrthonormalFrameBundle F E V) :
    e.orthonormalFrameBundle c b p =
      (p.proj, Unitary.linearIsometryEquiv.symm (p.frame.trans (frameAt e c b p.proj).symm)) :=
  rfl

/-- The trivialization reads a frame over the base set of `e` as its quotient by the local
orthonormal frame. -/
theorem orthonormalFrameBundle_apply_mk (y : e.baseSet) (φ : V ≃ₗᵢ[ℝ] E y) :
    e.orthonormalFrameBundle c b (⟨y, φ⟩ : OrthonormalFrameBundle F E V) =
      ((y : B), Unitary.linearIsometryEquiv.symm (φ.trans (e.orthonormalFrame c b y).symm)) := by
  rw [orthonormalFrameBundle_apply, frameAt_of_mem e c b y.2]

/-- The inverse of the trivialization carries `(y, g)` to the local orthonormal frame at `y`
acted on by `g`. -/
theorem orthonormalFrameBundle_symm_apply (y : e.baseSet) (g : unitary (V →L[ℝ] V)) :
    (e.orthonormalFrameBundle c b).toOpenPartialHomeomorph.symm ((y : B), g) =
      op g • (⟨y, e.orthonormalFrame c b y⟩ : OrthonormalFrameBundle F E V) := by
  rw [orthonormalFrameBundle_symm_apply', frameAt_of_mem e c b y.2]

/-- The local orthonormal frame corresponds to the identity of the orthogonal group. -/
@[simp]
theorem orthonormalFrameBundle_apply_orthonormalFrame (y : e.baseSet) :
    e.orthonormalFrameBundle c b (⟨y, e.orthonormalFrame c b y⟩ : OrthonormalFrameBundle F E V) =
      ((y : B), 1) := by
  rw [orthonormalFrameBundle_apply_mk, LinearIsometryEquiv.self_trans_symm,
    ← LinearIsometryEquiv.one_def, map_one]

/-- The trivialization is equivariant: it intertwines the right action on frames with right
multiplication in the orthogonal group. -/
theorem orthonormalFrameBundle_smul (g : unitary (V →L[ℝ] V)) (p : OrthonormalFrameBundle F E V) :
    e.orthonormalFrameBundle c b (op g • p) =
      ((e.orthonormalFrameBundle c b p).1, (e.orthonormalFrameBundle c b p).2 * g) := by
  refine Prod.ext rfl (Unitary.linearIsometryEquiv.injective ?_)
  ext v
  simp [orthonormalFrameBundle_apply, ← Unitary.coe_linearIsometryEquiv_apply]

end Bundle.Trivialization

namespace TauCeti.OrthonormalFrameBundle

variable [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace (TotalSpace F E)]
  [TopologicalSpace B] [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]

/-- When `V` has the dimension of the model fibre, the orthonormal frame bundle is locally trivial
with fibre the orthogonal group of `V`, by trivializations equivariant for the right action. -/
theorem exists_trivialization [FiniteDimensional ℝ F] [FiniteDimensional ℝ V]
    (h : Module.finrank ℝ V = Module.finrank ℝ F) (x : B) :
    ∃ t : Trivialization (unitary (V →L[ℝ] V)) (proj : OrthonormalFrameBundle F E V → B),
      x ∈ t.baseSet ∧ ∀ (g : unitary (V →L[ℝ] V)) (p : OrthonormalFrameBundle F E V),
        t (op g • p) = ((t p).1, (t p).2 * g) :=
  ⟨(trivializationAt F E x).orthonormalFrameBundle (Module.finBasisOfFinrankEq ℝ F h.symm)
      (stdOrthonormalBasis ℝ V),
    mem_baseSet_trivializationAt F E x, Trivialization.orthonormalFrameBundle_smul _ _ _⟩

end TauCeti.OrthonormalFrameBundle
