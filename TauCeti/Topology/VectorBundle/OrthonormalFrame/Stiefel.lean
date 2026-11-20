/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HurewiczFibration.LocallyTrivial
public import TauCeti.Topology.Homotopy.SerreFibration.Basic
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Basic
public import TauCeti.Topology.VectorBundle.SphereBundle.Stiefel
import TauCeti.Topology.Homotopy.SerreFibration.FiberBundle

/-!
# The Stiefel bundle of a Euclidean vector bundle is locally trivial

Let `E → B` be a real vector bundle with model fibre `F` whose fibres are inner product spaces with
continuous norm (`TauCeti.ContinuousFiberNorm`), and let `V` be a finite-dimensional real inner
product space. The Stiefel bundle `V_k(E)` (`TauCeti.StiefelBundle F E k`) of orthonormal
`k`-frames in the fibres of `E` is trivialized by local orthonormal frames of `E`: over the base
set of a linear trivialization `e`, the Gram–Schmidt orthonormal frame `σ_y : V ≃ E_y`
(`Bundle.Trivialization.orthonormalFrame`) identifies the frames of `E_y` with the frames of `V`,
vector by vector. This gives a chart of `V_k(E) → B` with fibre the Stiefel manifold `V_k(V)`
(`Bundle.Trivialization.stiefelBundle`), sending a frame `(x₁, …, x_k)` of `E_y` to
`(y, (σ_y⁻¹ x₁, …, σ_y⁻¹ x_k))`. Its vectors are read in the same frames as the vectors of the
orthonormal frame bundle.

So when `V` has the dimension of `F`, the Stiefel bundle is locally trivial with fibre `V_k(V)`
(`TauCeti.StiefelBundle.exists_trivialization`). Consequently:

* its projection to the base is proper, since `V_k(V)` is compact
  (`TauCeti.StiefelBundle.isProperMap_proj`), and the Stiefel bundle over a compact base is
  compact (`TauCeti.StiefelBundle.instCompactSpace`);
* its projection is a Serre fibration (`TauCeti.TopCat.mem_serreFibrations_stiefelBundleProj`),
  and a Hurewicz fibration over a normal paracompact base
  (`TauCeti.StiefelBundle.isHurewiczFibration_proj`).

For `k = 3` and `F` of dimension `n + 1`, `V₃(E)` is the parameter space of the family of
two-spheres `TauCeti.stiefelBundleSphereFamily` of the sphere bundle `S(E)`, which lies over
`S(E)` by the first vector of a frame. The chart reads every vector of a frame in the local
orthonormal frame (`Bundle.Trivialization.coe_stiefelBundle_apply_snd`), so it carries the
projections to the vectors of a frame to the projections `TauCeti.stiefelProj` of `V_k(V)`.

## References

* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §7.7 (Stiefel
  manifolds) and §§12.1–12.2 (bundles with an orthogonal structure group).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §2 (orthonormal frames by Gram–Schmidt) and Chapter 5.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 6.23.
-/

public section

noncomputable section

open Bundle Set InnerProductSpace TauCeti

universe u w

variable {B : Type w} {F : Type*} {E : B → Type w} [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace (TotalSpace F E)]
  [TopologicalSpace B] [FiberBundle F E] [VectorBundle ℝ F E] [ContinuousFiberNorm F E]

namespace Bundle.Trivialization

variable (e : Trivialization F (π F E)) [e.IsLinear ℝ]
  {ι : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι]
  (c : Module.Basis ι ℝ F) (b : OrthonormalBasis ι ℝ V) (k : ℕ)

/-- The trivialization of the Stiefel bundle `V_k(E)` over the base set of a linear trivialization
`e`, with fibre the Stiefel manifold `V_k(V)`: a frame `(x₁, …, x_k)` of `E_y` goes to
`(y, (σ_y⁻¹ x₁, …, σ_y⁻¹ x_k))`, where `σ = e.orthonormalFrame c b` is the local Gram–Schmidt
orthonormal frame. -/
def stiefelBundle :
    Trivialization (stiefel V k) (StiefelBundle.proj : StiefelBundle F E k → B) where
  toFun p := (p.proj, ⟨(orthonormalFrameAt e c b p.proj).symm ∘ p.frame.val,
    mem_stiefel_iff.2 ((mem_stiefel_iff.1 p.frame.property).comp_linearIsometryEquiv _)⟩)
  invFun q := ⟨q.1, ⟨orthonormalFrameAt e c b q.1 ∘ q.2.val,
    mem_stiefel_iff.2 ((mem_stiefel_iff.1 q.2.property).comp_linearIsometryEquiv _)⟩⟩
  source := StiefelBundle.proj ⁻¹' e.baseSet
  target := e.baseSet ×ˢ univ
  map_source' _ hp := ⟨hp, mem_univ _⟩
  map_target' _ hq := hq.1
  left_inv' p _ := by
    obtain ⟨y, x⟩ := p
    exact StiefelBundle.mk_eq_mk_iff.2 (Subtype.ext (funext fun i ↦ by simp))
  right_inv' q _ := Prod.ext rfl (Subtype.ext (funext fun i ↦ by simp))
  open_source := e.open_baseSet.preimage StiefelBundle.continuous_proj
  open_target := e.open_baseSet.prod isOpen_univ
  continuousOn_toFun := by
    refine StiefelBundle.continuous_proj.continuousOn.prodMk ?_
    refine Topology.IsInducing.subtypeVal.continuousOn_iff.2 (continuousOn_pi.2 fun i ↦ ?_)
    exact (continuousOn_orthonormalFrameAt_symm e c b).comp
      (StiefelBundle.continuous_totalSpaceMk_frame i).continuousOn fun _ hp ↦ hp
  continuousOn_invFun := by
    have : FiniteDimensional ℝ V := .of_basis b.toBasis
    rw [continuousOn_iff_continuous_domRestrict]
    refine StiefelBundle.continuous_iff.2 ⟨continuous_fst.comp continuous_subtypeVal, fun i ↦ ?_⟩
    -- The `i`th vector is the local orthonormal frame applied to the `i`th vector of the model
    -- frame, and applying frames to vectors is jointly continuous.
    have hσ : Continuous fun q : (e.baseSet ×ˢ univ : Set (B × stiefel V k)) ↦
        (⟨q.val.1, orthonormalFrameAt e c b q.val.1⟩ : OrthonormalFrameBundle ℝ F E V) :=
      ((e.continuous_orthonormalFrame c b).comp
        ((continuous_fst.comp continuous_subtypeVal).subtype_mk fun q ↦ q.property.1)).congr fun q ↦
          OrthonormalFrameBundle.mk_eq_mk_iff.2 (orthonormalFrameAt_of_mem e c b q.property.1).symm
    have hv : Continuous fun q : (e.baseSet ×ˢ univ : Set (B × stiefel V k)) ↦ q.val.2.val i :=
      (continuous_apply i).comp
        (continuous_subtypeVal.comp (continuous_snd.comp continuous_subtypeVal))
    exact OrthonormalFrameBundle.continuous_totalSpaceMk_frame_apply.comp (hσ.prodMk hv)
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

/-- The trivialization of the Stiefel bundle has the base set of `e`. -/
@[simp]
theorem baseSet_stiefelBundle :
    (e.stiefelBundle c b k :
      Trivialization _ (StiefelBundle.proj : StiefelBundle F E k → B)).baseSet = e.baseSet :=
  (rfl)

private theorem stiefelBundle_apply (p : StiefelBundle F E k) :
    e.stiefelBundle c b k p = (p.proj, ⟨(orthonormalFrameAt e c b p.proj).symm ∘ p.frame.val,
      mem_stiefel_iff.2 ((mem_stiefel_iff.1 p.frame.property).comp_linearIsometryEquiv _)⟩) :=
  rfl

private theorem stiefelBundle_symm_apply' (q : B × stiefel V k) :
    (e.stiefelBundle c b k).toOpenPartialHomeomorph.symm q =
      (⟨q.1, ⟨orthonormalFrameAt e c b q.1 ∘ q.2.val,
        mem_stiefel_iff.2 ((mem_stiefel_iff.1 q.2.property).comp_linearIsometryEquiv _)⟩⟩ :
          StiefelBundle F E k) :=
  rfl

/-- The trivialization reads each vector of a frame over the base set of `e` in the local
orthonormal frame. -/
@[simp]
theorem coe_stiefelBundle_apply_snd (y : e.baseSet) (x : stiefel (E y) k) (i : Fin k) :
    ((e.stiefelBundle c b k (⟨y, x⟩ : StiefelBundle F E k)).2 : Fin k → V) i =
      (e.orthonormalFrame c b y).symm (x.val i) := by
  simp [stiefelBundle_apply]

/-- The inverse of the trivialization applies the local orthonormal frame at `y` to each vector of
a frame of `V`. -/
theorem stiefelBundle_symm_apply (y : e.baseSet) (x : stiefel V k) :
    (e.stiefelBundle c b k).toOpenPartialHomeomorph.symm ((y : B), x) =
      (⟨y, ⟨e.orthonormalFrame c b y ∘ x.val,
        mem_stiefel_iff.2 ((mem_stiefel_iff.1 x.property).comp_linearIsometryEquiv _)⟩⟩ :
          StiefelBundle F E k) := by
  rw [stiefelBundle_symm_apply', StiefelBundle.mk_eq_mk_iff]
  exact Subtype.ext (by simp)

end Bundle.Trivialization

namespace TauCeti

namespace StiefelBundle

variable [FiniteDimensional ℝ F] [FiniteDimensional ℝ V]

variable (V) in
/-- **The Stiefel bundle of a Euclidean vector bundle is locally trivial.** If `V` has the
dimension of the model fibre `F`, every point of the base lies in the base set of a chart of
`V_k(E) → B` with fibre the Stiefel manifold `V_k(V)`, given by a local orthonormal frame of `E`.
No separation or paracompactness assumption on the base is needed. -/
theorem exists_trivialization (h : Module.finrank ℝ V = Module.finrank ℝ F) (k : ℕ) (x : B) :
    ∃ t : Trivialization (stiefel V k) (proj : StiefelBundle F E k → B), x ∈ t.baseSet :=
  ⟨(trivializationAt F E x).stiefelBundle (Module.finBasisOfFinrankEq ℝ F h.symm)
      (stdOrthonormalBasis ℝ V) k,
    mem_baseSet_trivializationAt F E x⟩

variable (F E) in
/-- The projection of the Stiefel bundle to the base is proper: its fibres are the compact
Stiefel manifolds of the fibres. -/
theorem isProperMap_proj (k : ℕ) : IsProperMap (proj : StiefelBundle F E k → B) :=
  isProperMap_of_forall_exists_trivialization
    (exists_trivialization (EuclideanSpace ℝ (Fin (Module.finrank ℝ F)))
      finrank_euclideanSpace_fin k)

/-- The Stiefel bundle of a Euclidean vector bundle over a compact base is compact. -/
instance instCompactSpace [CompactSpace B] (k : ℕ) : CompactSpace (StiefelBundle F E k) :=
  ⟨by simpa using (isProperMap_proj F E k).isCompact_preimage isCompact_univ⟩

variable (F E) in
/-- **The Stiefel bundle of a Euclidean vector bundle over a normal paracompact base is a Hurewicz
fibration.** This includes every paracompact Hausdorff base. -/
theorem isHurewiczFibration_proj [NormalSpace B] [ParacompactSpace B] (k : ℕ) :
    IsHurewiczFibration.{u} (proj : StiefelBundle F E k → B) :=
  isHurewiczFibration_of_exists_trivialization
    (exists_trivialization (EuclideanSpace ℝ (Fin (Module.finrank ℝ F)))
      finrank_euclideanSpace_fin k)

end StiefelBundle

variable [FiniteDimensional ℝ F]

variable (F E) in
/-- **The Stiefel bundle of a Euclidean vector bundle is a Serre fibration.** -/
theorem TopCat.mem_serreFibrations_stiefelBundleProj (k : ℕ) :
    TopCat.serreFibrations (_root_.TopCat.ofHom ⟨_, StiefelBundle.continuous_proj⟩ :
      _root_.TopCat.of (StiefelBundle F E k) ⟶ _root_.TopCat.of B) :=
  TopCat.mem_serreFibrations_of_exists_trivialization
    (StiefelBundle.exists_trivialization (EuclideanSpace ℝ (Fin (Module.finrank ℝ F)))
      finrank_euclideanSpace_fin k)

end TauCeti
