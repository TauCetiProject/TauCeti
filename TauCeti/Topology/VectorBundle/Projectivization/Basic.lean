/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Projectivization.Action
public import TauCeti.Topology.FiberBundle.Associated.Section
public import TauCeti.Topology.FiberBundle.Proper
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Principal
public import TauCeti.Topology.VectorBundle.Riemannian.Hermitian

/-!
# The projectivization of a Hermitian vector bundle

Let `E → B` be a vector bundle over `𝕜 = ℝ` or `ℂ` with finite-dimensional model fibre `F` and
fibre inner products with continuous norm, and let `V` be an inner product space of the dimension
of `F`. The *projectivization* `TauCeti.ProjectiveBundle 𝕜 F E V` of `E` is the bundle associated
with the orthonormal frame bundle `TauCeti.OrthonormalFrameBundle.Fiber 𝕜 F E V` and the action of
the unitary group `unitary (V →L[𝕜] V)` on the projective space `ℙ 𝕜 V` by moving lines. Its points
over `b` are the classes `[φ, ℓ]` of an orthonormal frame `φ : V ≃ₗᵢ[𝕜] E b` and a line `ℓ` of
`V`, and `[φ, ℓ]` is identified with the line `φ ℓ` of `E b`
(`TauCeti.projectiveBundleFiberEquiv`), independently of the frame
(`TauCeti.projectiveBundleFiberEquiv_mk`). So the fibre over `b` is the projective space
`ℙ 𝕜 (E b)`. As an associated bundle it is a fibre bundle with model fibre `ℙ 𝕜 V`. For `𝕜 = ℂ`
this is the complex projective bundle `P(E)` of lines of a Hermitian bundle, a `ℂℙⁿ⁻¹`-bundle;
for `𝕜 = ℝ` it is the real projective bundle of a Riemannian bundle.

Each point `y` of `P(E)` carries its *tautological line*
`TauCeti.ProjectiveBundle.tautologicalLine y`, the line of `E` over the base point of `y` that `y`
represents. The pairs of a point `y` and a vector of its tautological line form the subset
`TauCeti.ProjectiveBundle.tautologicalLineSet` of `P(E) × E`, closed when the base is Hausdorff
(`TauCeti.ProjectiveBundle.isClosed_tautologicalLineSet`). In a chart of `P(E)` the tautological
line is read off the coordinate in `ℙ 𝕜 V` through the Gram–Schmidt frame of the chart
(`TauCeti.ProjectiveBundle.projectiveBundleFiberEquiv_eq_trivializationAt`).

The fibre `ℙ 𝕜 V` is compact, so the projection of `P(E)` is proper and `P(E)` is compact over a
compact base. In rank one each fibre is a single point and the projection is a homeomorphism
(`TauCeti.ProjectiveBundle.projHomeomorphOfFinrankEqOne`). The projectivization of the trivial
bundle `B × V` is the product `B × ℙ 𝕜 V` (`TauCeti.ProjectiveBundle.trivialHomeomorph`).

## Main definitions

* `TauCeti.ProjectiveBundle 𝕜 F E V`: the projectivization `P(E)`, with model fibre `ℙ 𝕜 V`.
* `TauCeti.projectiveBundleFiberEquiv b`: the fibre of `P(E)` over `b` is `ℙ 𝕜 (E b)`.
* `TauCeti.ProjectiveBundle.tautologicalLine y`: the line of `E` represented by `y`.
* `TauCeti.ProjectiveBundle.tautologicalLineSet 𝕜 F E V`: the tautological line as a subset of
  `P(E) × E`.
* `TauCeti.ProjectiveBundle.trivialHomeomorph`: `P(B × V) ≃ₜ B × ℙ 𝕜 V`.

## Main results

* `TauCeti.projectiveBundleFiberEquiv_mk`: `[φ, ℓ]` is the line `φ ℓ`.
* `TauCeti.ProjectiveBundle.finrank_tautologicalLine`: the tautological lines are lines.
* `TauCeti.ProjectiveBundle.isClosed_tautologicalLineSet`: the tautological line is closed in
  `P(E) × E` over a Hausdorff base.
* `TauCeti.ProjectiveBundle.isProperMap_proj`,
  `TauCeti.ProjectiveBundle.instCompactSpaceTotalSpace`: `P(E)` is proper over `B`, and compact
  over a compact base.
* `TauCeti.ProjectiveBundle.projHomeomorphOfFinrankEqOne`: in rank one `P(E)` is the base.

## References

* R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*, Graduate Texts in Mathematics 82,
  Springer (1982), §20 (the projectivization of a complex vector bundle and its tautological
  sub-bundle).
* D. Husemoller, *Fibre Bundles*, third edition, Graduate Texts in Mathematics 20, Springer
  (1994), Chapter 17, §2 (the projective bundle associated with a vector bundle).
-/

public section

noncomputable section

open Bundle Set MulOpposite Topology Module
open scoped LinearAlgebra.Projectivization

/-! ### Projective spaces -/

namespace Projectivization

section DivisionRing

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- **The incidence relation of projective space is closed**: the pairs of a point of `ℙ K V` and
a vector on its line form a closed subset of `ℙ K V × V`. -/
theorem isClosed_setOf_mem_submodule [TopologicalSpace V] [T1Space V] [T2Space (ℙ K V)] :
    IsClosed {p : ℙ K V × V | p.2 ∈ p.1.submodule} := by
  -- The complement is the image, under the open embedding `ℙ K V × (V ∖ 0) → ℙ K V × V`, of the
  -- open set of pairs `(x, v)` with `x ≠ [v]`.
  have hι : IsOpenEmbedding (Prod.map id Subtype.val : ℙ K V × {v : V // v ≠ 0} → ℙ K V × V) :=
    IsOpenEmbedding.id.prodMap (isOpen_ne.isOpenEmbedding_subtypeVal)
  have hc : {p : ℙ K V × V | p.2 ∈ p.1.submodule}ᶜ =
      Prod.map id Subtype.val '' {q : ℙ K V × {v : V // v ≠ 0} | q.1 ≠ mk' K q.2} := by
    ext ⟨x, v⟩
    simp only [mem_compl_iff, mem_ofPred_eq, mem_submodule_iff, not_forall, mem_image,
      Prod.exists, Prod.map, id_eq, Prod.mk.injEq, Subtype.exists, mk'_eq_mk]
    constructor
    · rintro ⟨hv, hx⟩
      exact ⟨x, v, hv, Ne.symm hx, rfl, rfl⟩
    · rintro ⟨x, v, hv, hx, rfl, rfl⟩
      exact ⟨hv, Ne.symm hx⟩
  rw [← isOpen_compl_iff, hc]
  exact hι.isOpenMap _ (isOpen_ne_fun continuous_fst (continuous_mk'.comp continuous_snd))

end DivisionRing

end Projectivization

namespace TauCeti

/-! ### The action of the unitary group -/

section Action

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]

/-- The unitary group of `V`, with its operator-norm topology, acts jointly continuously on `V`. -/
instance instContinuousSMulUnitaryContinuousLinearMap :
    ContinuousSMul (unitary (V →L[𝕜] V)) V :=
  ⟨isBoundedBilinearMap_apply.continuous.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)⟩

/-- Moving a line `ℓ` by the unitary transformation `ψ⁻¹ ∘ φ` and then by the frame `ψ` is moving
it by the frame `φ`. -/
private theorem mapLinearEquiv_unitary_smul {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace 𝕜 W] (φ ψ : V ≃ₗᵢ[𝕜] W) (ℓ : ℙ 𝕜 V) :
    Projectivization.mapLinearEquiv ψ.toLinearEquiv
        (Unitary.linearIsometryEquiv.symm (φ.trans ψ.symm) • ℓ) =
      Projectivization.mapLinearEquiv φ.toLinearEquiv ℓ := by
  induction ℓ using Projectivization.ind with | h v hv =>
  rw [Projectivization.smul_mk, Projectivization.mapLinearEquiv_mk,
    Projectivization.mapLinearEquiv_mk]
  congr 1
  change ψ ((Unitary.linearIsometryEquiv.symm (φ.trans ψ.symm) : V →L[𝕜] V) v) = φ v
  simp

end Action

/-! ### The projective bundle -/

variable {𝕜 : Type*} [RCLike 𝕜] {B : Type*} [TopologicalSpace B] {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {E : B → Type*} [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace 𝕜 (E x)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [VectorBundle 𝕜 F E] [ContinuousFiberNorm F E] [FiniteDimensional 𝕜 F]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  [FiniteDimensional 𝕜 V] [hV : Fact (finrank 𝕜 V = finrank 𝕜 F)]

variable (𝕜 F E V) in
/-- The **projectivization** `P(E)` of a vector bundle `E` with fibre inner products: the bundle
associated with the orthonormal frame bundle of `E` modelled on `V` and the action of the unitary
group of `V` on the lines of `V`. Its fibre over `b` is identified with the projective space
`ℙ 𝕜 (E b)` of lines of `E b` (`TauCeti.projectiveBundleFiberEquiv`). For `𝕜 = ℂ` this is the
complex projective bundle of a Hermitian vector bundle. -/
abbrev ProjectiveBundle : B → Type _ :=
  AssociatedBundle (unitary (V →L[𝕜] V)) (OrthonormalFrameBundle.Fiber 𝕜 F E V) (ℙ 𝕜 V)

/-- The fibre of the projectivization `P(E)` over `b` is the projective space of lines of `E b`:
the class `[φ, ℓ]` of a frame and a line of `V` is the line `φ ℓ`
(`TauCeti.projectiveBundleFiberEquiv_mk`). -/
def projectiveBundleFiberEquiv (b : B) : ProjectiveBundle 𝕜 F E V b ≃ ℙ 𝕜 (E b) :=
  -- Read the class in a fixed frame `p` over `b`; by `projectiveBundleFiberEquiv_mk` the result
  -- does not depend on `p`.
  let p : OrthonormalFrameBundle.Fiber 𝕜 F E V b :=
    (FiberBundle.homeomorphAt (unitary (V →L[𝕜] V)) (OrthonormalFrameBundle.Fiber 𝕜 F E V) b).symm 1
  (Equiv.ofBijective _ (AssociatedBundle.mk_bijective (G := unitary (V →L[𝕜] V)) (F := ℙ 𝕜 V)
    p)).symm.trans (Projectivization.mapLinearEquiv p.frame.toLinearEquiv)

/-- **The fibre of `P(E)` is `ℙ(E_b)`.** The class `[φ, ℓ]` of a frame `φ` of `E b` and a line `ℓ`
of `V` is the line `φ ℓ` of `E b`. -/
@[simp]
theorem projectiveBundleFiberEquiv_mk {b : B} (φ : OrthonormalFrameBundle.Fiber 𝕜 F E V b)
    (ℓ : ℙ 𝕜 V) :
    projectiveBundleFiberEquiv b (AssociatedBundle.mk (unitary (V →L[𝕜] V)) φ ℓ) =
      Projectivization.mapLinearEquiv φ.frame.toLinearEquiv ℓ := by
  set p : OrthonormalFrameBundle.Fiber 𝕜 F E V b :=
    (FiberBundle.homeomorphAt (unitary (V →L[𝕜] V)) (OrthonormalFrameBundle.Fiber 𝕜 F E V) b).symm 1
  have h : AssociatedBundle.mk (unitary (V →L[𝕜] V)) φ ℓ =
      AssociatedBundle.mk (unitary (V →L[𝕜] V)) p
        (PrincipalBundle.division (unitary (V →L[𝕜] V)) p φ • ℓ) :=
    (AssociatedBundle.mk_eq_mk_iff.2 rfl).symm
  rw [projectiveBundleFiberEquiv, Equiv.trans_apply, h, Equiv.ofBijective_symm_apply_apply,
    OrthonormalFrameBundle.division_eq]
  exact mapLinearEquiv_unitary_smul _ _ _

/-- The class of a frame `φ` and the line `φ⁻¹ L` is the line `L`. -/
theorem projectiveBundleFiberEquiv_symm_apply {b : B}
    (φ : OrthonormalFrameBundle.Fiber 𝕜 F E V b) (L : ℙ 𝕜 (E b)) :
    (projectiveBundleFiberEquiv b).symm L = AssociatedBundle.mk (unitary (V →L[𝕜] V)) φ
      (Projectivization.mapLinearEquiv φ.frame.toLinearEquiv.symm L) := by
  rw [Equiv.symm_apply_eq, projectiveBundleFiberEquiv_mk, ← Projectivization.mapLinearEquiv_symm,
    Equiv.apply_symm_apply]

namespace ProjectiveBundle

variable (F) in
/-- The Gram–Schmidt frame at `y` of the preferred trivialization of `E` at `b`: the frame in which
the preferred trivialization of `P(E)` at `b` reads lines (see
`TauCeti.ProjectiveBundle.projectiveBundleFiberEquiv_eq_trivializationAt`). -/
abbrev chartFrame (b y : B) : V ≃ₗᵢ[𝕜] E y :=
  (trivializationAt F E b).orthonormalFrameAt (Module.finBasisOfFinrankEq 𝕜 F hV.out.symm)
    (stdOrthonormalBasis 𝕜 V) y

/-- **The charts of `P(E)`.** Over the base set of the preferred trivialization of `E` at `b`, the
line of `E` represented by a point of `P(E)` is the image, under the Gram–Schmidt frame
`TauCeti.ProjectiveBundle.chartFrame b`, of its coordinate in the preferred chart of `P(E)` at
`b`. -/
theorem projectiveBundleFiberEquiv_eq_trivializationAt {b : B}
    (y : TotalSpace (ℙ 𝕜 V) (ProjectiveBundle 𝕜 F E V))
    (hy : y.proj ∈ (trivializationAt F E b).baseSet) :
    projectiveBundleFiberEquiv y.proj y.2 =
      Projectivization.mapLinearEquiv (chartFrame F (E := E) (V := V) b y.proj).toLinearEquiv
        (trivializationAt (ℙ 𝕜 V) (ProjectiveBundle 𝕜 F E V) b y).2 := by
  obtain ⟨y, w⟩ := y
  obtain ⟨φ, ℓ, rfl⟩ := AssociatedBundle.exists_mk w
  have hy' : y ∈ (trivializationAt (unitary (V →L[𝕜] V))
      (OrthonormalFrameBundle.Fiber 𝕜 F E V) b).baseSet := by
    rwa [OrthonormalFrameBundle.baseSet_trivializationAt_fiber]
  have h := (trivializationAt F E b).orthonormalFrameBundle_apply_mk
    (Module.finBasisOfFinrankEq 𝕜 F hV.out.symm) (stdOrthonormalBasis 𝕜 V) ⟨y, hy⟩ φ.frame
  rw [AssociatedBundle.trivializationAt_mk_snd hy', projectiveBundleFiberEquiv_mk,
    OrthonormalFrameBundle.trivializationAt_fiber,
    OrthonormalFrameBundle.trivializationAtFiber_apply,
    OrthonormalFrameBundle.totalSpaceEquiv_apply]
  simp only at h ⊢
  rw [h, chartFrame, Trivialization.orthonormalFrameAt_of_mem _ _ _ hy]
  exact (mapLinearEquiv_unitary_smul _ _ _).symm

/-! ### The tautological line -/

/-- The **tautological line** of a point `y` of `P(E)`: the line of `E` over the base point of
`y` that `y` represents. -/
def tautologicalLine (y : TotalSpace (ℙ 𝕜 V) (ProjectiveBundle 𝕜 F E V)) :
    Submodule 𝕜 (E y.proj) :=
  (projectiveBundleFiberEquiv y.proj y.2).submodule

/-- The tautological line of `y` is the line `projectiveBundleFiberEquiv y.proj y.2`. -/
theorem tautologicalLine_def (y : TotalSpace (ℙ 𝕜 V) (ProjectiveBundle 𝕜 F E V)) :
    tautologicalLine y = (projectiveBundleFiberEquiv y.proj y.2).submodule :=
  (rfl)

/-- The tautological line of `[φ, ℓ]` is the image of `ℓ` under the frame `φ`. -/
@[simp]
theorem tautologicalLine_mk {b : B} (φ : OrthonormalFrameBundle.Fiber 𝕜 F E V b) (ℓ : ℙ 𝕜 V) :
    tautologicalLine (⟨b, AssociatedBundle.mk _ φ ℓ⟩ :
        TotalSpace (ℙ 𝕜 V) (ProjectiveBundle 𝕜 F E V)) =
      ℓ.submodule.map (φ.frame.toLinearEquiv : V →ₗ[𝕜] E b) := by
  rw [tautologicalLine_def, projectiveBundleFiberEquiv_mk,
    Projectivization.submodule_mapLinearEquiv]

/-- The tautological lines are lines. -/
@[simp]
theorem finrank_tautologicalLine (y : TotalSpace (ℙ 𝕜 V) (ProjectiveBundle 𝕜 F E V)) :
    finrank 𝕜 (tautologicalLine y) = 1 :=
  Projectivization.finrank_submodule _

variable (𝕜 F E V) in
/-- The **tautological line** of `P(E)` as a subset of `P(E) × E`: the pairs of a point `y` of
`P(E)` and a vector of `E` on the tautological line of `y`. -/
def tautologicalLineSet : Set (TotalSpace (ℙ 𝕜 V) (ProjectiveBundle 𝕜 F E V) × TotalSpace F E) :=
  {z | ∃ w ∈ tautologicalLine z.1, z.2 = ⟨z.1.proj, w⟩}

/-- The fibre of the tautological line over a point `y` of `P(E)` is the tautological line of
`y`. -/
@[simp]
theorem mk_mem_tautologicalLineSet_iff {y : TotalSpace (ℙ 𝕜 V) (ProjectiveBundle 𝕜 F E V)}
    {w : E y.proj} : (y, ⟨y.proj, w⟩) ∈ tautologicalLineSet 𝕜 F E V ↔ w ∈ tautologicalLine y :=
  ⟨fun ⟨_, hw', h⟩ ↦ TotalSpace.mk_inj.1 h ▸ hw', fun hw ↦ ⟨w, hw, rfl⟩⟩

/-- A point of the tautological line lies over a point of `E` with the same base point. -/
theorem proj_eq_of_mem_tautologicalLineSet {z} (hz : z ∈ tautologicalLineSet 𝕜 F E V) :
    z.2.proj = z.1.proj := by
  obtain ⟨w, -, h⟩ := hz
  rw [h]

/-- **The tautological line is closed.** Over a Hausdorff base, the pairs of a point of `P(E)`
and a vector on its tautological line form a closed subset of `P(E) × E`. -/
theorem isClosed_tautologicalLineSet [T2Space B] : IsClosed (tautologicalLineSet 𝕜 F E V) := by
  have hπP := FiberBundle.continuous_proj (ℙ 𝕜 V) (ProjectiveBundle 𝕜 F E V)
  have hπE := FiberBundle.continuous_proj F E
  refine isOpen_compl_iff.1 (isOpen_iff_mem_nhds.2 fun z hz ↦ ?_)
  obtain ⟨⟨b, y⟩, ⟨b', v⟩⟩ := z
  by_cases hbb : b' = b
  swap
  · -- Pairs over different base points do not meet the tautological line.
    filter_upwards [(isOpen_ne_fun (hπE.comp continuous_snd) (hπP.comp continuous_fst)).mem_nhds
      hbb] with z hz hzS
    exact hz (proj_eq_of_mem_tautologicalLineSet hzS)
  subst hbb
  -- Near `(y, v)`, read the point of `P(E)` in its chart at `b` and the vector of `E` in the
  -- Gram–Schmidt frame of that chart: the tautological line becomes the incidence relation.
  set e := trivializationAt F E b'
  set eP := trivializationAt (ℙ 𝕜 V) (ProjectiveBundle 𝕜 F E V) b'
  set f : TotalSpace (ℙ 𝕜 V) (ProjectiveBundle 𝕜 F E V) × TotalSpace F E → ℙ 𝕜 V × V :=
    fun z ↦ ((eP z.1).2, (chartFrame F (𝕜 := 𝕜) (E := E) (V := V) b' z.2.proj).symm z.2.2)
  have hb : b' ∈ e.baseSet := mem_baseSet_trivializationAt F E b'
  have hbP : b' ∈ eP.baseSet := by
    rw [AssociatedBundle.baseSet_trivializationAt,
      OrthonormalFrameBundle.baseSet_trivializationAt_fiber]
    exact hb
  have hf : ContinuousAt f (⟨b', y⟩, ⟨b', v⟩) := by
    refine ContinuousAt.prodMk ?_ ?_
    · exact continuous_snd.continuousAt.comp
        ((eP.continuousAt (eP.mem_source.2 hbP)).comp continuous_fst.continuousAt)
    · exact ((e.continuousOn_orthonormalFrameAt_symm _ _).continuousAt
        ((e.open_baseSet.preimage hπE).mem_nhds hb)).comp continuous_snd.continuousAt
  have hiff : ∀ {y'} (w : E y'.proj), y'.proj ∈ e.baseSet →
      ((y', ⟨y'.proj, w⟩) ∈ tautologicalLineSet 𝕜 F E V ↔
        f (y', ⟨y'.proj, w⟩) ∈ {p : ℙ 𝕜 V × V | p.2 ∈ p.1.submodule}) := by
    intro y' w hy'
    rw [mk_mem_tautologicalLineSet_iff, tautologicalLine_def,
      projectiveBundleFiberEquiv_eq_trivializationAt y' hy',
      Projectivization.submodule_mapLinearEquiv, Submodule.mem_map_equiv]
    rfl
  have hz' : f (⟨b', y⟩, ⟨b', v⟩) ∉ {p : ℙ 𝕜 V × V | p.2 ∈ p.1.submodule} :=
    fun h ↦ hz ((hiff (y' := ⟨b', y⟩) v hb).2 h)
  filter_upwards [hf.preimage_mem_nhds
      (Projectivization.isClosed_setOf_mem_submodule.isOpen_compl.mem_nhds hz'),
    (hπP.comp continuous_fst).continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hb)]
    with z hzf hze hzS
  obtain ⟨w, hw', hw⟩ := hzS
  have hz2 : z = (z.1, ⟨z.1.proj, w⟩) := Prod.ext rfl hw
  rw [hz2] at hzf
  exact hzf ((hiff w hze).1 (mk_mem_tautologicalLineSet_iff.2 hw'))

/-! ### Compactness and rank one -/

/-- The projection of `P(E)` is proper: its fibres are the compact projective spaces `ℙ 𝕜 V`. -/
theorem isProperMap_proj :
    IsProperMap (TotalSpace.proj : TotalSpace (ℙ 𝕜 V) (ProjectiveBundle 𝕜 F E V) → B) :=
  FiberBundle.isProperMap_proj (ℙ 𝕜 V) (ProjectiveBundle 𝕜 F E V)

/-- The projectivization of a vector bundle over a compact base is compact. -/
instance instCompactSpaceTotalSpace [CompactSpace B] :
    CompactSpace (TotalSpace (ℙ 𝕜 V) (ProjectiveBundle 𝕜 F E V)) :=
  ⟨by simpa using
    (isProperMap_proj (𝕜 := 𝕜) (F := F) (E := E) (V := V)).isCompact_preimage isCompact_univ⟩

/-- In rank one, the projection of `P(E)` is bijective: each fibre is a single point. -/
private theorem bijective_proj_of_finrank_eq_one (h : finrank 𝕜 F = 1) :
    Function.Bijective (TotalSpace.proj : TotalSpace (ℙ 𝕜 V) (ProjectiveBundle 𝕜 F E V) → B) := by
  have hV1 : finrank 𝕜 V = 1 := hV.out.trans h
  have : Subsingleton (ℙ 𝕜 V) := Projectivization.subsingleton_of_rank_le_one <| by
    rw [← Module.finrank_eq_rank, hV1, Nat.cast_one]
  have : Nontrivial V := Module.finrank_pos_iff.1 (by rw [hV1]; exact one_pos)
  refine ⟨fun y y' hy ↦ ?_, FiberBundle.surjective_proj (ℙ 𝕜 V) (ProjectiveBundle 𝕜 F E V)⟩
  obtain ⟨b, ℓ⟩ := y
  obtain ⟨b', ℓ'⟩ := y'
  obtain rfl : b = b' := hy
  exact congrArg (TotalSpace.mk b) (Subsingleton.elim (α := ℙ 𝕜 V) ℓ ℓ')

/-- **The projectivization of a line bundle is its base.** When `E` has rank one, each fibre of
`P(E)` is a single point, and the projection is a homeomorphism onto the base. -/
def projHomeomorphOfFinrankEqOne (h : finrank 𝕜 F = 1) :
    TotalSpace (ℙ 𝕜 V) (ProjectiveBundle 𝕜 F E V) ≃ₜ B :=
  (Equiv.ofBijective _ (bijective_proj_of_finrank_eq_one h)).toHomeomorphOfContinuousOpen
    (FiberBundle.continuous_proj _ _) (FiberBundle.isOpenMap_proj _ _)

/-- In rank one, the identification of `P(E)` with the base is the projection. -/
@[simp]
theorem projHomeomorphOfFinrankEqOne_apply (h : finrank 𝕜 F = 1)
    (y : TotalSpace (ℙ 𝕜 V) (ProjectiveBundle 𝕜 F E V)) :
    projHomeomorphOfFinrankEqOne h y = y.proj :=
  (rfl)

end ProjectiveBundle

/-! ### The trivial bundle -/

namespace ProjectiveBundle

variable (B) in
/-- The identity frame of the trivial bundle `B × V` at each point. -/
def trivialFrame (b : B) : OrthonormalFrameBundle.Fiber 𝕜 V (Trivial B V) V b :=
  .ofFrame (LinearIsometryEquiv.refl 𝕜 V)

omit hV [FiniteDimensional 𝕜 V] in
/-- The identity frames form a continuous global section of the frame bundle of `B × V`. -/
theorem continuous_trivialFrame :
    Continuous fun b ↦
      TotalSpace.mk' (unitary (V →L[𝕜] V)) b (trivialFrame (𝕜 := 𝕜) (V := V) B b) :=
  continuous_induced_rng.2 <|
    OrthonormalFrameBundle.continuous_iff.2 fun v ↦ by
      have h : Continuous fun x : B ↦ (Trivial.homeomorphProd B V).symm (x, v) :=
        (Trivial.homeomorphProd B V).symm.continuous.comp (continuous_id.prodMk continuous_const)
      refine h.congr fun x ↦ ?_
      rw [Function.comp_apply, OrthonormalFrameBundle.totalSpaceEquiv_apply]
      rfl

variable (𝕜 B V) in
/-- **The projectivization of a trivial bundle is a product**: `P(B × V)` is homeomorphic to
`B × ℙ 𝕜 V`, by the global identity frame. Its second component is the line represented by a point
(`TauCeti.ProjectiveBundle.snd_trivialHomeomorph`). -/
def trivialHomeomorph :
    TotalSpace (ℙ 𝕜 V) (ProjectiveBundle 𝕜 V (Trivial B V) V) ≃ₜ B × ℙ 𝕜 V :=
  (AssociatedBundle.prodHomeomorphOfSection _ continuous_trivialFrame).symm

/-- The identification `P(B × V) ≃ₜ B × ℙ 𝕜 V` preserves the base point. -/
@[simp]
theorem fst_trivialHomeomorph (y : TotalSpace (ℙ 𝕜 V) (ProjectiveBundle 𝕜 V (Trivial B V) V)) :
    (trivialHomeomorph 𝕜 B V y).1 = y.proj :=
  AssociatedBundle.fst_prodHomeomorphOfSection_symm _ _ y

/-- The identification `P(B × V) ≃ₜ B × ℙ 𝕜 V` sends a point to the line of `V` it represents. -/
@[simp]
theorem snd_trivialHomeomorph (y : TotalSpace (ℙ 𝕜 V) (ProjectiveBundle 𝕜 V (Trivial B V) V)) :
    ((trivialHomeomorph 𝕜 B V y).2 : ℙ 𝕜 V) = projectiveBundleFiberEquiv y.proj y.2 := by
  obtain ⟨b, w⟩ := y
  obtain ⟨ℓ, rfl⟩ := (AssociatedBundle.mk_bijective (F := ℙ 𝕜 V) (trivialFrame (𝕜 := 𝕜) B b)).2 w
  rw [trivialHomeomorph, AssociatedBundle.prodHomeomorphOfSection_symm_mk,
    projectiveBundleFiberEquiv_mk, trivialFrame, OrthonormalFrameBundle.Fiber.frame_ofFrame,
    LinearIsometryEquiv.toLinearEquiv_refl, Projectivization.mapLinearEquiv_refl, Equiv.refl_apply]

/-- The inverse of `P(B × V) ≃ₜ B × ℙ 𝕜 V` sends `(b, ℓ)` to the class of the identity frame and
`ℓ`. -/
@[simp]
theorem trivialHomeomorph_symm_apply (x : B × ℙ 𝕜 V) :
    (trivialHomeomorph 𝕜 B V).symm x = ⟨x.1, AssociatedBundle.mk _ (trivialFrame B x.1) x.2⟩ := by
  rw [trivialHomeomorph, Homeomorph.symm_symm, AssociatedBundle.prodHomeomorphOfSection_apply]

end ProjectiveBundle

end TauCeti
