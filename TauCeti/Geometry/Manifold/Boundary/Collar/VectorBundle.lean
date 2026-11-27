/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Smooth
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.TotallyReal.Trivialization
public import TauCeti.Topology.VectorBundle.RealForm
public import TauCeti.Topology.Algebra.Module.ComplexSmulI
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Smooth vector-bundle comparison along a given collar

A given smooth collar of a manifold with compact boundary identifies the original boundary
fibres of any finite-rank smooth complex bundle with its fibres at a uniform positive depth.
The comparison and its inverse are jointly real-smooth. It is the identity on the zero slice.
Transporting every boundary frame by the same comparison makes overlap coefficients independent
of depth. This is a conditional ingredient for smooth doubling of bundle pairs; it constructs
neither the collar nor a doubled bundle, and asserts no choice independence.

## Main results

* `TauCeti.SmoothCollar.exists_bundleComparison`: a common complex-linear comparison with
  smooth native pullback maps in both directions and exact identity on the zero slice.
* `TauCeti.SmoothCollar.BundleComparison.isSubbundleFrameOn_transport`: transport of given
  smooth real boundary frames to the smaller collar cylinder over their domain.
* `TauCeti.SmoothCollar.BundleComparison.hasLocalContMDiffSubbundleFrames_transport`: the
  corresponding native local-frame criterion for the transported subbundle.
* `TauCeti.SmoothCollar.BundleComparison.exists_adaptedTrivialization`: a smooth complex-linear
  trivialization with exactly the original boundary-frame coordinates.
* `TauCeti.SmoothCollar.BundleComparison.repr_map_equiv_apply_eq_ofReal_re`: coordinates
  equal to the original real boundary coefficients at every depth.

Only the boundary is assumed compact and Hausdorff. Boundary dimension zero, rank zero and
empty or disconnected boundary are included.
-/

public section

open Bundle FiberBundle Set Function Module
open scoped Manifold ContDiff Topology
noncomputable section

namespace TauCeti.SmoothCollar




open TauCeti.EuclideanHalfSpace

private theorem exists_uniformDepth {N : Type*} [TopologicalSpace N] [CompactSpace N]
    {U : Set (N × normalIioOpens 1)} (hU : IsOpen U)
    (hzero : ∀ y, (y, normalIioOpensZero zero_lt_one) ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ y (t : normalIioOpens 1),
      t.val.val 0 < ε → (y, t) ∈ U := by
  have htube : U ∈ (𝓝ˢ (univ : Set N)) ×ˢ 𝓝 (normalIioOpensZero zero_lt_one) :=
    isCompact_univ.mem_nhdsSet_prod_of_forall fun y _ ↦ by
      rw [← nhds_prod_eq]
      exact hU.mem_nhds (hzero y)
  obtain ⟨W, hW, V, hV, hWV⟩ := Filter.mem_prod_iff.mp htube
  obtain ⟨O, hOV, hOo, h0O⟩ := mem_nhds_iff.mp hV
  have hOimage : IsOpen (Subtype.val '' O : Set (EuclideanHalfSpace 1)) :=
    (normalIioOpens 1).isOpen.isOpenMap_subtypeVal _ hOo
  have h0image : (0 : EuclideanHalfSpace 1) ∈ Subtype.val '' O :=
    ⟨normalIioOpensZero zero_lt_one, h0O, coe_normalIioOpensZero zero_lt_one⟩
  obtain ⟨δ, hδ, hδO⟩ := exists_normalIio_subset hOimage h0image
  refine ⟨min δ (1 / 2), lt_min hδ (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  intro y t ht
  have htδ : t.val ∈ normalIio δ :=
    (mem_normalIio).mpr (lt_of_lt_of_le ht (min_le_left _ _))
  obtain ⟨t', ht'O, htt⟩ := hδO htδ
  have hteq : t' = t := Subtype.ext htt
  exact hWV ⟨subset_of_mem_nhdsSet hW (mem_univ y), hOV (hteq ▸ ht'O)⟩



section ComparisonData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  (c : SmoothCollar n ∞ M) (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (V : M → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)] [FiberBundle F V]
  (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)

/-- A smooth comparison along a positive initial segment of a given collar. Its fibre maps
compare the original native fibres, and its diffeomorphism uses exactly their native pullbacks.
The zero law is stated on the original total space, so it expresses the identity across the
collar's actual point equality without identifying different fibre types by definition.
This packages comparison data and does not define a new bundle carrier. -/
structure BundleComparison where
  /-- The complex-linear comparison of the original boundary and collar fibres. -/
  equiv : ∀ p : ↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens ε,
    V (p.1 : M) ≃L[ℂ] V (c (p.1, Set.inclusion (fun _ ht ↦
      mem_normalIioOpens.mpr (lt_trans (mem_normalIioOpens.mp ht) hε1)) p.2))
  /-- Its native real-smooth total-space diffeomorphism. -/
  diffeomorph :
    let b₀ : C(↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens ε, M) :=
      ⟨fun p ↦ (p.1 : M), continuous_subtypeVal.comp continuous_fst⟩
    let b₁ : C(↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens ε, M) :=
      ⟨fun p ↦ c (p.1, Set.inclusion (fun _ ht ↦
      mem_normalIioOpens.mpr (lt_trans (mem_normalIioOpens.mp ht) hε1)) p.2),
        c.continuous.comp (continuous_fst.prodMk
          ((continuous_inclusion (show normalIioOpens ε ≤ normalIioOpens 1 from
            fun _ ht ↦ mem_normalIioOpens.mpr
              (lt_trans (mem_normalIioOpens.mp ht) hε1))).comp continuous_snd))⟩
    TotalSpace F ((b₀ : _ → M) *ᵖ V) ≃ₘ^∞⟮
      ((𝓡 n).prod (𝓡∂ 1)).prod 𝓘(ℝ, F),
      ((𝓡 n).prod (𝓡∂ 1)).prod 𝓘(ℝ, F)⟯ TotalSpace F ((b₁ : _ → M) *ᵖ V)
  /-- The forward diffeomorphism evaluates the stated fibre equivalence. -/
  apply_eq : ∀ p v, diffeomorph ⟨p, v⟩ = ⟨p, equiv p v⟩
  /-- The inverse diffeomorphism evaluates the inverse fibre equivalence. -/
  symm_apply_eq : ∀ p v, diffeomorph.symm ⟨p, v⟩ = ⟨p, (equiv p).symm v⟩
  /-- At depth zero the original total-space vector is unchanged. -/
  zero_eq : ∀ (y : ↥((𝓡∂ (n + 1)).boundary M)) (v : V (y : M)),
    (TotalSpace.mk' F (c (y, Set.inclusion (fun _ ht ↦
      mem_normalIioOpens.mpr (lt_trans (mem_normalIioOpens.mp ht) hε1)) (normalIioOpensZero hε0)))
      (equiv (y, normalIioOpensZero hε0) v)) = TotalSpace.mk' F (y : M) v

-- The evaluation fields are used explicitly: simplifying ContinuousMap coercions in their
-- implicit types changes the native pullback bundle instances, so they are not simp lemmas.
attribute [simp] BundleComparison.zero_eq

end ComparisonData

section Collar

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space ↥((𝓡∂ (n + 1)).boundary M)]
  [CompactSpace ↥((𝓡∂ (n + 1)).boundary M)]

local instance boundarySmooth : IsManifold (𝓡 n) ∞ ↥((𝓡∂ (n + 1)).boundary M) :=
  isManifold_boundary M

local instance depthSigmaCompact (ε : ℝ) : SigmaCompactSpace (normalIioOpens ε) := by
  let : LocallyCompactSpace (EuclideanHalfSpace 1) := (𝓡∂ 1).locallyCompactSpace
  let : SecondCountableTopology (EuclideanHalfSpace 1) := (𝓡∂ 1).secondCountableTopology
  let : LocallyCompactSpace (normalIioOpens ε) :=
    ChartedSpace.locallyCompactSpace (EuclideanHalfSpace 1) (normalIioOpens ε)
  infer_instance



omit [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space ↥((𝓡∂ (n + 1)).boundary M)]
  [CompactSpace ↥((𝓡∂ (n + 1)).boundary M)] in
private def sourceBase (c : SmoothCollar n ∞ M) (ε : ℝ) :
    C^∞⟮(𝓡 n).prod (𝓡∂ 1), ↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens ε;
      𝓡∂ (n + 1), M⟯ :=
  ⟨fun p ↦ (p.1 : M), c.contMDiff_subtypeVal_boundary.comp contMDiff_fst⟩

omit [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space ↥((𝓡∂ (n + 1)).boundary M)]
  [CompactSpace ↥((𝓡∂ (n + 1)).boundary M)] in
private def targetBase (c : SmoothCollar n ∞ M) {ε : ℝ} (hε : ε < 1) :
    C^∞⟮(𝓡 n).prod (𝓡∂ 1), ↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens ε;
      𝓡∂ (n + 1), M⟯ := by
  have hsub : normalIioOpens ε ≤ normalIioOpens 1 := fun _ ht ↦
    mem_normalIioOpens.mpr (lt_trans (mem_normalIioOpens.mp ht) hε)
  exact ⟨c ∘ (fun p ↦ (p.1, Set.inclusion hsub p.2)),
    c.contMDiff.comp (contMDiff_fst.prodMk
      ((contMDiff_inclusion hsub).comp contMDiff_snd))⟩


variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F]
  (V : M → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance originalRealBundle : VectorBundle ℝ F V := VectorBundle.restrictScalars ℝ ℂ F V
local instance finiteRealModel : FiniteDimensional ℝ F := Module.Finite.trans ℂ F
local instance completeRealModel : CompleteSpace F := FiniteDimensional.completeSpace ℝ F
variable [ContMDiffVectorBundle ∞ F V (𝓡∂ (n + 1))]

section FibreContinuity

variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]

private theorem exists_admissibleMap (c : SmoothCollar n ∞ M) :
    let b₀ := sourceBase c 1
    let b₁ : C^∞⟮(𝓡 n).prod (𝓡∂ 1),
      ↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens 1; 𝓡∂ (n + 1), M⟯ := ⟨c, c.contMDiff⟩
    ∃ A : ∀ p, ((b₀ : _ → M) *ᵖ V) p →L[ℝ] ((b₁ : _ → M) *ᵖ V) p,
      ContMDiff ((𝓡 n).prod (𝓡∂ 1)) (((𝓡 n).prod (𝓡∂ 1)).prod 𝓘(ℝ, F →L[ℝ] F)) ∞
        (fun p ↦ TotalSpace.mk' (F →L[ℝ] F) p (A p)) ∧
      (∀ p v, A p (Complex.I • v) = Complex.I • A p v) ∧
      ∀ p, p.2 = normalIioOpensZero one_pos → ∀ h : b₀ p = b₁ p,
        ∀ v, A p v = cast (congrArg V h) v := by
  let b₀ := sourceBase c 1
  let b₁ : C^∞⟮(𝓡 n).prod (𝓡∂ 1),
      ↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens 1; 𝓡∂ (n + 1), M⟯ := ⟨c, c.contMDiff⟩
  let D := {p : ↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens 1 |
    p.2 = normalIioOpensZero one_pos}
  have hD : IsClosed D := isClosed_eq continuous_snd continuous_const
  have hbase (p) (hp : p ∈ D) : b₀ p = b₁ p := by
    -- Unfold the two private base maps to read coincidence in the original manifold.
    change (p.1 : M) = c p
    rcases p with ⟨y, t⟩
    -- `D` is the zero-slice predicate; this exposes its normal coordinate after destructuring `p`.
    change t = normalIioOpensZero one_pos at hp
    subst t
    exact (c.apply_zero y).symm
  exact Pullback.exists_contMDiff_hom_map_I_eq_cast b₀ b₁ D hD hbase

private theorem exists_invertibleMap (c : SmoothCollar n ∞ M) :
    let b₀ := sourceBase c 1
    let b₁ : C^∞⟮(𝓡 n).prod (𝓡∂ 1),
      ↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens 1; 𝓡∂ (n + 1), M⟯ := ⟨c, c.contMDiff⟩
    ∃ A : ∀ p, ((b₀ : _ → M) *ᵖ V) p →L[ℝ] ((b₁ : _ → M) *ᵖ V) p,
      ContMDiff ((𝓡 n).prod (𝓡∂ 1)) (((𝓡 n).prod (𝓡∂ 1)).prod 𝓘(ℝ, F →L[ℝ] F)) ∞
        (fun p ↦ TotalSpace.mk' (F →L[ℝ] F) p (A p)) ∧
      (∀ p v, A p (Complex.I • v) = Complex.I • A p v) ∧
      (∀ p, p.2 = normalIioOpensZero one_pos → ∀ h : b₀ p = b₁ p,
        ∀ v, A p v = cast (congrArg V h) v) ∧
      ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ y (t : normalIioOpens 1),
        t.val.val 0 < ε → (A (y, t)).IsInvertible := by
  let P := ↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens 1
  let IP := (𝓡 n).prod (𝓡∂ 1)
  let b₀ := sourceBase c 1
  let b₁ : C^∞⟮IP, P; 𝓡∂ (n + 1), M⟯ := ⟨c, c.contMDiff⟩
  obtain ⟨A, hA, hI, hZ⟩ := exists_admissibleMap F V c
  -- Keep the two native pullback families explicit when using the returned Hom section.
  -- Name the native pullback families explicitly: the private bundled base maps and the
  -- inline continuous maps have the same evaluations but different inferred bundle presentations.
  change ContMDiff IP (IP.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
    (fun p : P ↦ TotalSpace.mk' (F →L[ℝ] F)
      (E := fun p ↦ ((b₀ : P → M) *ᵖ V) p →L[ℝ] ((b₁ : P → M) *ᵖ V) p) p (A p)) at hA
  have hAc : Continuous (fun p : P ↦ TotalSpace.mk' (F →L[ℝ] F)
      (E := fun p ↦ ((b₀ : P → M) *ᵖ V) p →L[ℝ] ((b₁ : P → M) *ᵖ V) p) p (A p)) :=
    hA.continuous
  have hU : IsOpen {p : P | (A p).IsInvertible} :=
    Continuous.isOpen_setOf_clm_bundle_isInvertible
      (F₁ := F) (F₂ := F) (E₁ := (b₀ : P → M) *ᵖ V) (E₂ := (b₁ : P → M) *ᵖ V)
      (b := id) (ϕ := A) hAc
  have hUZ (y : ↥((𝓡∂ (n + 1)).boundary M)) :
      (y, normalIioOpensZero one_pos) ∈ {p : P | (A p).IsInvertible} := by
    exact ContinuousLinearMap.isInvertible_of_eq_cast (c.apply_zero y).symm
      (A (y, normalIioOpensZero one_pos))
      (fun v ↦ hZ (y, normalIioOpensZero one_pos) rfl (c.apply_zero y).symm v)
  exact ⟨A, hA, hI, hZ, exists_uniformDepth hU hUZ⟩

private def comparisonOfEquiv (c : SmoothCollar n ∞ M) (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1)
    (e : ∀ p, ((sourceBase c ε : _ → M) *ᵖ V) p ≃L[ℝ]
      ((targetBase c h1 : _ → M) *ᵖ V) p)
    (hComm : ∀ p v, e p (Complex.I • v) = Complex.I • e p v)
    (hE : ContMDiff (((𝓡 n).prod (𝓡∂ 1)).prod 𝓘(ℝ, F))
      (((𝓡 n).prod (𝓡∂ 1)).prod 𝓘(ℝ, F)) ∞
      (fun v : TotalSpace F ((sourceBase c ε : _ → M) *ᵖ V) ↦
        TotalSpace.mk' F (E := (targetBase c h1 : _ → M) *ᵖ V) v.proj (e v.proj v.snd)))
    (hzero : ∀ (y : ↥((𝓡∂ (n + 1)).boundary M)) (v : V (y : M)),
      TotalSpace.mk' F (E := V) (targetBase c h1 (y, normalIioOpensZero h0))
        (e (y, normalIioOpensZero h0) v) = TotalSpace.mk' F (E := V) (y : M) v) :
    BundleComparison c F V ε h0 h1 := by
  let T p := (e p).complexOfMapISmul (hComm p)
  refine {
    equiv := T
    diffeomorph := TauCeti.bundleDiffeomorph e hE
    apply_eq := ?_
    symm_apply_eq := ?_
    zero_eq := ?_ }
  · intro p v
    -- Expand the comparison field to the native bundle diffeomorphism so its public
    -- evaluation law applies to these explicitly typed pullback total spaces.
    change (TauCeti.bundleDiffeomorph e hE) ⟨p, v⟩ =
      TotalSpace.mk' F (E := (targetBase c h1 : _ → M) *ᵖ V) p (T p v)
    rw [TauCeti.bundleDiffeomorph_apply]
    exact (congrArg (TotalSpace.mk' F p)
      ((e p).complexOfMapISmul_apply (hComm p) v)).symm
  · intro p v
    -- Expand the comparison field to the native bundle diffeomorphism so its public
    -- evaluation law applies to these explicitly typed pullback total spaces.
    change (TauCeti.bundleDiffeomorph e hE).symm ⟨p, v⟩ =
      TotalSpace.mk' F (E := (sourceBase c ε : _ → M) *ᵖ V) p ((T p).symm v)
    rw [TauCeti.bundleDiffeomorph_symm_apply]
    exact (congrArg (TotalSpace.mk' F p)
      ((e p).complexOfMapISmul_symm_apply (hComm p) v)).symm
  · intro y v
    -- Expose the original total-space constructor; complex promotion preserves evaluation
    -- and `complexOfMapISmul_apply` below supplies that equality explicitly.
    change TotalSpace.mk' F (E := V) (targetBase c h1 (y, normalIioOpensZero h0))
      ((e (y, normalIioOpensZero h0)).complexOfMapISmul _ v) = _
    exact (congrArg (TotalSpace.mk' F (E := V)
      (targetBase c h1 (y, normalIioOpensZero h0)))
      ((e (y, normalIioOpensZero h0)).complexOfMapISmul_apply
        (hComm (y, normalIioOpensZero h0)) v)).trans (hzero y v)

omit [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space ↥((𝓡∂ (n + 1)).boundary M)]
  [CompactSpace ↥((𝓡∂ (n + 1)).boundary M)] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [TopologicalSpace (TotalSpace F V)] [FiberBundle F V]
  [VectorBundle ℂ F V] [ContMDiffVectorBundle ∞ F V (𝓡∂ (n + 1))]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, Module ℂ (V x)] in
private theorem restrictedMap_zero (c : SmoothCollar n ∞ M)
    (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1)
    (A : ∀ p : ↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens 1,
      ((sourceBase c 1 : _ → M) *ᵖ V) p →L[ℝ] V (c p))
    (hZ : ∀ p, p.2 = normalIioOpensZero one_pos → ∀ h : sourceBase c 1 p = c p,
      ∀ v, A p v = cast (congrArg V h) v)
    (e : ∀ p, ((sourceBase c ε : _ → M) *ᵖ V) p ≃L[ℝ]
      ((targetBase c h1 : _ → M) *ᵖ V) p)
    (he : ∀ p v, e p v = A (p.1, Set.inclusion (fun _ ht ↦
      mem_normalIioOpens.mpr (lt_trans (mem_normalIioOpens.mp ht) h1)) p.2) v) :
    ∀ (y : ↥((𝓡∂ (n + 1)).boundary M)) (v : V (y : M)),
      TotalSpace.mk' F (E := V) (targetBase c h1 (y, normalIioOpensZero h0))
        (e (y, normalIioOpensZero h0) v) = TotalSpace.mk' F (E := V) (y : M) v := by
  intro y v
  have hsub : normalIioOpens ε ≤ normalIioOpens 1 := fun _ ht ↦
    mem_normalIioOpens.mpr (lt_trans (mem_normalIioOpens.mp ht) h1)
  let q := (y, normalIioOpensZero h0)
  let p := (y, Set.inclusion hsub (normalIioOpensZero h0))
  have hz : p.2 = normalIioOpensZero one_pos := by
    apply Subtype.ext
    exact (Set.coe_inclusion hsub _).trans
      ((coe_normalIioOpensZero h0).trans (coe_normalIioOpensZero one_pos).symm)
  have hb : sourceBase c 1 p = c p := by
    -- The private base-map equality is now read in the original manifold after destructuring.
    change (y : M) = c (y, p.2)
    rw [hz]
    exact (c.apply_zero y).symm
  have hv : e q v = cast (congrArg V hb) v := (he q v).trans (hZ p hz hb v)
  exact (congrArg (TotalSpace.mk' F (E := V) (c p)) hv).trans (TotalSpace.mk_cast hb v)


end FibreContinuity


/-- A given smooth collar of a compact boundary admits a smooth complex-linear comparison
between the original boundary fibres and the fibres at a uniform positive collar depth.
Both total-space directions use the native pullbacks, and the comparison is exactly the
identity at depth zero. No global trivialization, connection or metric is required. -/
theorem exists_bundleComparison (c : SmoothCollar n ∞ M) :
    ∃ ε : ℝ, ∃ hε0 : 0 < ε, ∃ hε1 : ε < 1,
      Nonempty (BundleComparison c F V ε hε0 hε1) := by
  have : ∀ x, IsTopologicalAddGroup (V x) := VectorBundle.isTopologicalAddGroup ℝ F V
  have : ∀ x, ContinuousSMul ℝ (V x) := VectorBundle.continuousSMul ℝ F V
  let P := ↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens 1
  let IP := (𝓡 n).prod (𝓡∂ 1)
  let b₀ := sourceBase c 1
  let b₁ : C^∞⟮IP, P; 𝓡∂ (n + 1), M⟯ := ⟨c, c.contMDiff⟩
  obtain ⟨A, hA, hI, hZ, ε, hε0, hε1, hεU⟩ := exists_invertibleMap F V c
  -- Name the native pullback families explicitly: the private bundled base maps and the
  -- inline continuous maps have the same evaluations but different inferred bundle presentations.
  change ContMDiff IP (IP.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
    (fun p : P ↦ TotalSpace.mk' (F →L[ℝ] F)
      (E := fun p ↦ ((b₀ : P → M) *ᵖ V) p →L[ℝ] ((b₁ : P → M) *ᵖ V) p) p (A p)) at hA
  let Q := ↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens ε
  have hsub : normalIioOpens ε ≤ normalIioOpens 1 := fun _ ht ↦
    mem_normalIioOpens.mpr (lt_trans (mem_normalIioOpens.mp ht) hε1)
  let j : C^∞⟮IP, Q; IP, P⟯ := ⟨fun q ↦ (q.1, Set.inclusion hsub q.2),
    contMDiff_fst.prodMk ((contMDiff_inclusion hsub).comp contMDiff_snd)⟩
  have hInv (q : Q) : (A (j q)).IsInvertible := by
    apply hεU q.1 (j q).2
    -- Membership in the open invertibility cylinder uses the original normal coordinate;
    -- `Set.inclusion` retains that coordinate when restricting the collar depth.
    change (Set.inclusion hsub q.2).val.val 0 < ε
    rw [Set.coe_inclusion hsub q.2]
    exact mem_normalIioOpens.mp q.2.property
  let f₀ := b₀.comp j
  let f₁ := b₁.comp j
  let e (q : Q) : ((f₀ : Q → M) *ᵖ V) q ≃L[ℝ] ((f₁ : Q → M) *ᵖ V) q :=
    Classical.choose (hInv q)
  have he (q : Q) : (e q).toContinuousLinearMap = A (j q) := Classical.choose_spec (hInv q)
  have hev (q : Q) (v : ((f₀ : Q → M) *ᵖ V) q) : e q v = A (j q) v :=
    congrArg (fun f ↦ f v) (he q)
  have hComm (q : Q) (v : ((f₀ : Q → M) *ᵖ V) q) :
      e q (Complex.I • v) = Complex.I • e q v :=
    (hev q (Complex.I • v)).trans
      ((hI (j q) v).trans (congrArg (Complex.I • ·) (hev q v).symm))
  have hE : ContMDiff (IP.prod 𝓘(ℝ, F)) (IP.prod 𝓘(ℝ, F)) ∞
      (fun v : TotalSpace F ((f₀ : Q → M) *ᵖ V) ↦
        TotalSpace.mk' F (E := (f₁ : Q → M) *ᵖ V) v.proj (e v.proj v.snd)) :=
    (Pullback.contMDiff_fiberwise_comp_of_hom b₀ b₁ A hA j).congr fun v ↦
      congrArg (TotalSpace.mk' F (E := (f₁ : Q → M) *ᵖ V) v.proj) (hev v.proj v.snd)
  exact ⟨ε, hε0, hε1, ⟨comparisonOfEquiv F V c ε hε0 hε1 e hComm hE
    (restrictedMap_zero F V c ε hε0 hε1 A hZ e hev)⟩⟩

section Frames

variable {F V} {c : SmoothCollar n ∞ M} {ε : ℝ} {hε0 : 0 < ε} {hε1 : ε < 1}
  (B : BundleComparison c F V ε hε0 hε1)

/-- The image of a real boundary subspace under the common complex-linear collar comparison. -/
def BundleComparison.transportSubspace
    (L : ∀ y : ↥((𝓡∂ (n + 1)).boundary M), Submodule ℝ (V (y : M)))
    (p : ↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens ε) :
    Submodule ℝ (V (c (p.1, Set.inclusion (fun _ ht ↦
      mem_normalIioOpens.mpr (lt_trans (mem_normalIioOpens.mp ht) hε1)) p.2))) :=
  (L p.1).map ((B.equiv p).toLinearEquiv.restrictScalars ℝ).toLinearMap

omit [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space ↥((𝓡∂ (n + 1)).boundary M)]
  [CompactSpace ↥((𝓡∂ (n + 1)).boundary M)] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F] [VectorBundle ℂ F V]
  [ContMDiffVectorBundle ∞ F V (𝓡∂ (n + 1))] in
/-- The defining image formula for the transported real subspace. -/
theorem BundleComparison.transportSubspace_def
    (L : ∀ y : ↥((𝓡∂ (n + 1)).boundary M), Submodule ℝ (V (y : M)))
    (p : ↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens ε) :
    B.transportSubspace L p =
      (L p.1).map ((B.equiv p).toLinearEquiv.restrictScalars ℝ).toLinearMap := by rfl

omit [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space ↥((𝓡∂ (n + 1)).boundary M)]
  [CompactSpace ↥((𝓡∂ (n + 1)).boundary M)] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F] [VectorBundle ℂ F V]
  [ContMDiffVectorBundle ∞ F V (𝓡∂ (n + 1))] in
/-- Membership in the transported subspace is membership of the inverse image. -/
theorem BundleComparison.mem_transportSubspace_iff
    (L : ∀ y : ↥((𝓡∂ (n + 1)).boundary M), Submodule ℝ (V (y : M)))
    (p : ↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens ε)
    (w : V (c (p.1, Set.inclusion (fun _ ht ↦
      mem_normalIioOpens.mpr (lt_trans (mem_normalIioOpens.mp ht) hε1)) p.2))) :
    w ∈ B.transportSubspace L p ↔ (B.equiv p).symm w ∈ L p.1 := by
  rw [B.transportSubspace_def]
  exact Submodule.mem_map_equiv (e := (B.equiv p).toLinearEquiv.restrictScalars ℝ) (L p.1)

omit [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space ↥((𝓡∂ (n + 1)).boundary M)]
  [CompactSpace ↥((𝓡∂ (n + 1)).boundary M)] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F] [VectorBundle ℂ F V]
  [ContMDiffVectorBundle ∞ F V (𝓡∂ (n + 1))] in
/-- A transported vector lies in the transported subspace exactly when the original does. -/
@[simp]
theorem BundleComparison.equiv_apply_mem_transportSubspace_iff
    (L : ∀ y : ↥((𝓡∂ (n + 1)).boundary M), Submodule ℝ (V (y : M)))
    (p : ↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens ε) (v : V (p.1 : M)) :
    B.equiv p v ∈ B.transportSubspace L p ↔ v ∈ L p.1 := by
  rw [B.mem_transportSubspace_iff, (B.equiv p).symm_apply_apply]

omit [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space ↥((𝓡∂ (n + 1)).boundary M)]
  [CompactSpace ↥((𝓡∂ (n + 1)).boundary M)] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F] [VectorBundle ℂ F V]
  [ContMDiffVectorBundle ∞ F V (𝓡∂ (n + 1))] in
/-- On the zero slice the transported real subspace has exactly the original vectors in the
original total space. This states the identity without identifying different fibre types. -/
theorem BundleComparison.transportSubspace_zero_range
    (L : ∀ y : ↥((𝓡∂ (n + 1)).boundary M), Submodule ℝ (V (y : M)))
    (y : ↥((𝓡∂ (n + 1)).boundary M)) :
    range (fun v : B.transportSubspace L (y, normalIioOpensZero hε0) ↦
      TotalSpace.mk' F (E := V)
        (c (y, Set.inclusion (fun _ ht ↦
          mem_normalIioOpens.mpr (lt_trans (mem_normalIioOpens.mp ht) hε1))
          (normalIioOpensZero hε0))) (v : _)) =
      range (fun v : L y ↦ TotalSpace.mk' F (E := V) (y : M) (v : V (y : M))) := by
  ext z
  constructor
  · rintro ⟨⟨w, hw⟩, rfl⟩
    rw [B.transportSubspace_def] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    exact ⟨⟨v, hv⟩, (B.zero_eq y v).symm⟩
  · rintro ⟨v, rfl⟩
    refine ⟨⟨B.equiv (y, normalIioOpensZero hε0) v, ?_⟩, B.zero_eq y v⟩
    exact (B.equiv_apply_mem_transportSubspace_iff L (y, normalIioOpensZero hε0)
      (v : V (y : M))).2 v.property

omit [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space ↥((𝓡∂ (n + 1)).boundary M)]
  [CompactSpace ↥((𝓡∂ (n + 1)).boundary M)] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F] [VectorBundle ℂ F V]
  [ContMDiffVectorBundle ∞ F V (𝓡∂ (n + 1))] in
/-- The transported subspace is maximal totally real exactly when the original one is. -/
theorem BundleComparison.isMaximalTotallyReal_transportSubspace_iff
    (L : ∀ y : ↥((𝓡∂ (n + 1)).boundary M), Submodule ℝ (V (y : M)))
    (p : ↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens ε) :
    IsMaximalTotallyReal ((LinearMap.lsmul ℂ _ Complex.I).restrictScalars ℝ)
      (B.transportSubspace L p) ↔
    IsMaximalTotallyReal ((LinearMap.lsmul ℂ _ Complex.I).restrictScalars ℝ) (L p.1) := by
  apply LinearEquiv.isMaximalTotallyReal_map_iff
    ((B.equiv p).toLinearEquiv.restrictScalars ℝ)
  exact LinearMap.ext fun v ↦ ((B.equiv p).map_smul Complex.I v).symm

omit [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space ↥((𝓡∂ (n + 1)).boundary M)]
  [CompactSpace ↥((𝓡∂ (n + 1)).boundary M)] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [VectorBundle ℂ F V] [ContMDiffVectorBundle ∞ F V (𝓡∂ (n + 1))]
  [∀ x, Module ℝ (V x)] in
/-- A smooth section along the original boundary remains smooth after the common collar
comparison. Smoothness refers to the native total spaces, without a topology on a section space. -/
theorem BundleComparison.contMDiffOn_transport {U : Set ↥((𝓡∂ (n + 1)).boundary M)}
    (σ : ∀ y : ↥((𝓡∂ (n + 1)).boundary M), V (y : M))
    (hσ : ContMDiffOn (𝓡 n) ((𝓡∂ (n + 1)).prod 𝓘(ℝ, F)) ∞
      (fun y : ↥((𝓡∂ (n + 1)).boundary M) ↦
        TotalSpace.mk' F (E := V) (y : M) (σ y)) U) :
    ContMDiffOn ((𝓡 n).prod (𝓡∂ 1)) (((𝓡 n).prod (𝓡∂ 1)).prod 𝓘(ℝ, F)) ∞
      (fun p ↦ TotalSpace.mk' F (E := ((⟨fun p ↦ c (p.1, Set.inclusion (fun _ ht ↦
        mem_normalIioOpens.mpr (lt_trans (mem_normalIioOpens.mp ht) hε1)) p.2),
        c.continuous.comp (continuous_fst.prodMk ((continuous_inclusion (fun _ ht ↦
          mem_normalIioOpens.mpr (lt_trans (mem_normalIioOpens.mp ht) hε1))).comp
          continuous_snd))⟩ : C(↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens ε, M)) *ᵖ V))
        p (B.equiv p (σ p.1))) (Prod.fst ⁻¹' U) := by
  have hs : ContMDiffOn ((𝓡 n).prod (𝓡∂ 1))
      (((𝓡 n).prod (𝓡∂ 1)).prod 𝓘(ℝ, F)) ∞
      (fun p ↦ TotalSpace.mk' F (E := ((⟨fun p ↦ (p.1 : M),
        continuous_subtypeVal.comp continuous_fst⟩ :
        C(↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens ε, M)) *ᵖ V))
        p (σ p.1)) (Prod.fst ⁻¹' U) := by
    intro p hp
    apply (Pullback.contMDiffWithinAt_iff (sourceBase c ε)
      (sourceBase c ε).contMDiff.contMDiffAt).2
    exact ⟨contMDiffWithinAt_id, (hσ p.1 hp).comp p contMDiffWithinAt_fst (fun _ h ↦ h)⟩
  exact (B.diffeomorph.contMDiff.comp_contMDiffOn hs).congr
    (fun p _ ↦ (B.apply_eq p (σ p.1)).symm)

variable {ι : Type*} {U : Set ↥((𝓡∂ (n + 1)).boundary M)}
  {L : ∀ y : ↥((𝓡∂ (n + 1)).boundary M), Submodule ℝ (V (y : M))}
  {σ : ι → ∀ y : ↥((𝓡∂ (n + 1)).boundary M), V (y : M)}

omit [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space ↥((𝓡∂ (n + 1)).boundary M)]
  [CompactSpace ↥((𝓡∂ (n + 1)).boundary M)] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F] [VectorBundle ℂ F V]
  [ContMDiffVectorBundle ∞ F V (𝓡∂ (n + 1))] in
/-- Transport extends every given smooth real boundary frame on `U` to a smooth real frame
on the collar cylinder `Prod.fst ⁻¹' U` over `U`, at every depth below `ε`. -/
theorem BundleComparison.isSubbundleFrameOn_transport
    (hX : IsSubbundleFrameOn F (E := (ContinuousMap.subtypeVal
      ((𝓡∂ (n + 1)).boundary M) : _ → M) *ᵖ V) L σ U)
    (hσ : ∀ i, ContMDiffOn (𝓡 n) ((𝓡∂ (n + 1)).prod 𝓘(ℝ, F)) ∞
      (fun y : ↥((𝓡∂ (n + 1)).boundary M) ↦
        TotalSpace.mk' F (E := V) (y : M) (σ i y)) U) :
    let b₁ : C(↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens ε, M) :=
      ⟨fun p ↦ c (p.1, Set.inclusion (fun _ ht ↦
        mem_normalIioOpens.mpr (lt_trans (mem_normalIioOpens.mp ht) hε1)) p.2),
        c.continuous.comp (continuous_fst.prodMk ((continuous_inclusion (fun _ ht ↦
          mem_normalIioOpens.mpr (lt_trans (mem_normalIioOpens.mp ht) hε1))).comp continuous_snd))⟩
    IsSubbundleFrameOn F (E := (b₁ : _ → M) *ᵖ V) (B.transportSubspace L)
      (fun i p ↦ B.equiv p (σ i p.1)) (Prod.fst ⁻¹' U) ∧
    ∀ i, ContMDiffOn ((𝓡 n).prod (𝓡∂ 1))
      (((𝓡 n).prod (𝓡∂ 1)).prod 𝓘(ℝ, F)) ∞
      (fun p ↦ TotalSpace.mk' F (E := (b₁ : _ → M) *ᵖ V) p
        (B.equiv p (σ i p.1))) (Prod.fst ⁻¹' U) := by
  have hs i := B.contMDiffOn_transport (σ i) (hσ i)
  refine ⟨⟨fun i ↦ (hs i).continuousOn, fun {p} hp ↦ ?_, fun {p} hp ↦ ?_⟩, hs⟩
  · exact (hX.linearIndependent hp).map'
      ((B.equiv p).toLinearEquiv.restrictScalars ℝ).toLinearMap
      (LinearMap.ker_eq_bot.mpr (B.equiv p).injective)
  · let e := (B.equiv p).toLinearEquiv.restrictScalars ℝ
    have hmap := Submodule.map_span e.toLinearMap (range (σ · p.1))
    have hr : e '' range (σ · p.1) = range (fun i ↦ B.equiv p (σ i p.1)) :=
      (range_comp e (σ · p.1)).symm
    exact ((congrArg (Submodule.span ℝ) hr).symm.trans hmap.symm).trans
      (congrArg (Submodule.map e.toLinearMap) (hX.span_eq hp))


omit [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space ↥((𝓡∂ (n + 1)).boundary M)]
  [CompactSpace ↥((𝓡∂ (n + 1)).boundary M)] [FiniteDimensional ℂ F] in
/-- The transported boundary frame defines a native smooth complex-linear trivialization on
the full collar cylinder over its domain `U`. Its coordinates are exactly the original
boundary-frame coordinates,
so the same comparison normalizes all frames simultaneously. -/
theorem BundleComparison.exists_adaptedTrivialization [Finite ι]
    (hX : IsSubbundleFrameOn F (E := (ContinuousMap.subtypeVal
      ((𝓡∂ (n + 1)).boundary M) : _ → M) *ᵖ V) L σ U)
    (hσ : ∀ i, ContMDiffOn (𝓡 n) ((𝓡∂ (n + 1)).prod 𝓘(ℝ, F)) ∞
      (fun y : ↥((𝓡∂ (n + 1)).boundary M) ↦
        TotalSpace.mk' F (E := V) (y : M) (σ i y)) U)
    (hU : IsOpen U)
    (hL : ∀ y ∈ U, IsMaximalTotallyReal
      ((LinearMap.lsmul ℂ (V (y : M)) Complex.I).restrictScalars ℝ) (L y))
    (b : Basis ι ℂ F) :
    let b₁ : C(↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens ε, M) :=
      ⟨fun p ↦ c (p.1, Set.inclusion (fun _ ht ↦
        mem_normalIioOpens.mpr (lt_trans (mem_normalIioOpens.mp ht) hε1)) p.2),
        c.continuous.comp (continuous_fst.prodMk ((continuous_inclusion (fun _ ht ↦
          mem_normalIioOpens.mpr (lt_trans (mem_normalIioOpens.mp ht) hε1))).comp continuous_snd))⟩
    ∃ (e : Trivialization F (π F ((b₁ : _ → M) *ᵖ V))) (_ : e.IsLinear ℂ),
      e.toOpenPartialHomeomorph ∈
        (contMDiffFiberwiseLinear _ F ((𝓡 n).prod (𝓡∂ 1)) ∞).maximalAtlas
          (TotalSpace F ((b₁ : _ → M) *ᵖ V)) ∧
      e.baseSet = Prod.fst ⁻¹' U ∧
      ∀ (p : ↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens ε)
      (hp : p.1 ∈ U) (v : V (p.1 : M)),
        e ⟨p, B.equiv p v⟩ =
          (p, (hX.complexBasis (x := p.1) hp (hL p.1 hp)).equiv b (Equiv.refl ι) v) := by
  let b₁ : C(↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens ε, M) :=
    ⟨fun p ↦ c (p.1, Set.inclusion (fun _ ht ↦
      mem_normalIioOpens.mpr (lt_trans (mem_normalIioOpens.mp ht) hε1)) p.2),
      c.continuous.comp (continuous_fst.prodMk ((continuous_inclusion (fun _ ht ↦
        mem_normalIioOpens.mpr (lt_trans (mem_normalIioOpens.mp ht) hε1))).comp continuous_snd))⟩
  have hb₁ : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) ∞ b₁ :=
    (targetBase c hε1).contMDiff
  let : ContMDiffVectorBundle ∞ F ((b₁ : _ → M) *ᵖ V) ((𝓡 n).prod (𝓡∂ 1)) :=
    ContMDiffVectorBundle.pullback F V _ (⟨b₁, hb₁⟩ : C^∞⟮(𝓡 n).prod (𝓡∂ 1),
      ↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens ε; 𝓡∂ (n + 1), M⟯)
  obtain ⟨hτ, hτs⟩ := B.isSubbundleFrameOn_transport hX hσ
  have hτL p (hp : p ∈ Prod.fst ⁻¹' U) :=
    (B.isMaximalTotallyReal_transportSubspace_iff L p).2 (hL p.1 hp)
  let fr := hτ.isLocalFrameOn_complexDoubledFrame hτL hτs
  have hW : IsOpen (Prod.fst ⁻¹' U : Set
      (↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens ε)) := hU.preimage continuous_fst
  let e := fr.trivialization hW (Complex.basisOneI.smulTower b)
  let : e.IsLinear ℂ :=
    IsLocalFrameOn.isLinear_complex_trivialization_complexDoubledFrame fr hW b
  refine ⟨e, inferInstance, fr.trivialization_mem_maximalAtlas hW _,
    fr.baseSet_trivialization hW _, ?_⟩
  intro p hp v
  have hpe : p ∈ e.baseSet := by
    rw [show e.baseSet = Prod.fst ⁻¹' U from fr.baseSet_trivialization hW _]
    exact hp
  let β := hX.complexBasis (x := p.1) hp (hL p.1 hp)
  have he : (e.linearEquivAt ℂ p hpe).toLinearMap ∘ₗ (B.equiv p).toLinearEquiv.toLinearMap =
      (β.equiv b (Equiv.refl ι)).toLinearMap := by
    apply β.ext
    intro i
    simp only [LinearEquiv.coe_coe]
    rw [Basis.equiv_apply, Equiv.refl_apply]
    have hβ : β i = σ i p.1 := congrFun (hX.coe_complexBasis (x := p.1) hp (hL p.1 hp)) i
    rw [hβ]
    exact congrArg Prod.snd (fr.trivialization_complexDoubledFrame_apply_frame hW b hp i)
  apply Prod.ext
  · exact e.coe_fst (e.mem_source.mpr hpe)
  · exact LinearMap.congr_fun he v


omit [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space ↥((𝓡∂ (n + 1)).boundary M)]
  [CompactSpace ↥((𝓡∂ (n + 1)).boundary M)] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F] [VectorBundle ℂ F V]
  [ContMDiffVectorBundle ∞ F V (𝓡∂ (n + 1))] in
/-- Every vector in the real boundary subspace has the same real coordinates after transport.
In particular, this gives the overlap coefficients of any second boundary frame. The right
side contains no depth parameter; its inclusion into `ℂ` fixes both reality and exact depth
independence, including empty frames. -/
theorem BundleComparison.repr_map_equiv_apply_eq_ofReal_re
    (hX : IsSubbundleFrameOn F (E := (ContinuousMap.subtypeVal
      ((𝓡∂ (n + 1)).boundary M) : _ → M) *ᵖ V) L σ U)
    {y : ↥((𝓡∂ (n + 1)).boundary M)} (hyU : y ∈ U)
    (hL : IsMaximalTotallyReal
      ((LinearMap.lsmul ℂ (V (y : M)) Complex.I).restrictScalars ℝ) (L y))
    (t : normalIioOpens ε) (i : ι) (v : V (y : M)) (hv : v ∈ L y) :
    (((hX.complexBasis (x := y) hyU hL).map (B.equiv (y, t)).toLinearEquiv).repr
      (B.equiv (y, t) v)) i =
        (((hX.complexBasis (x := y) hyU hL).repr v i).re : ℂ) := by
  let β : Basis ι ℂ (V (y : M)) := hX.complexBasis hyU hL
  have h := hX.complexBasis_repr_coe hyU hL ⟨v, hv⟩ i
  have hz : (β.repr v i).im = 0 :=
    (congrArg Complex.im h).trans (Complex.ofReal_im _)
  have hc : β.repr v i = ((β.repr v i).re : ℂ) :=
    Complex.ext (by simp) (by simpa using hz)
  -- Read the native boundary pullback basis in its original fibre and expose the linear
  -- equivalence evaluation: `Basis.map_repr` cannot infer these pullback-family reductions.
  change ((β.map (B.equiv (y, t)).toLinearEquiv).repr
    ((B.equiv (y, t)).toLinearEquiv v)) i = ((β.repr v i).re : ℂ)
  rw [Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  exact hc



omit [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space ↥((𝓡∂ (n + 1)).boundary M)]
  [CompactSpace ↥((𝓡∂ (n + 1)).boundary M)] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F] [VectorBundle ℂ F V]
  [ContMDiffVectorBundle ∞ F V (𝓡∂ (n + 1))] in
/-- Smooth local frames of the given native boundary subbundle extend by the common comparison
at every collar point. This supplies the native smooth-subbundle criterion for the transported
family, without choosing a global frame. -/
theorem BundleComparison.hasLocalContMDiffSubbundleFrames_transport
    (hLs : HasLocalContMDiffSubbundleFrames (𝓡 n) ∞ F ι
      (E := (ContinuousMap.subtypeVal ((𝓡∂ (n + 1)).boundary M) : _ → M) *ᵖ V) L) :
    let b₁ : C(↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens ε, M) :=
      ⟨fun p ↦ c (p.1, Set.inclusion (fun _ ht ↦
        mem_normalIioOpens.mpr (lt_trans (mem_normalIioOpens.mp ht) hε1)) p.2),
        c.continuous.comp (continuous_fst.prodMk ((continuous_inclusion (fun _ ht ↦
          mem_normalIioOpens.mpr (lt_trans (mem_normalIioOpens.mp ht) hε1))).comp continuous_snd))⟩
    HasLocalContMDiffSubbundleFrames ((𝓡 n).prod (𝓡∂ 1)) ∞ F ι
      (E := (b₁ : _ → M) *ᵖ V) (B.transportSubspace L) := by
  apply hasLocalContMDiffSubbundleFrames_iff.mpr
  intro p
  obtain ⟨U, hU, hp, σ, hX, hσ⟩ := hasLocalContMDiffSubbundleFrames_iff.mp hLs p.1
  have hσ' i : ContMDiffOn (𝓡 n) ((𝓡∂ (n + 1)).prod 𝓘(ℝ, F)) ∞
      (fun y : ↥((𝓡∂ (n + 1)).boundary M) ↦
        TotalSpace.mk' F (E := V) (y : M) (σ i y)) U :=
    (Pullback.contMDiff_lift (F := F) (E := V)
      (ContinuousMap.subtypeVal ((𝓡∂ (n + 1)).boundary M))
      c.contMDiff_subtypeVal_boundary).comp_contMDiffOn (hσ i)
  obtain ⟨hτ, hτs⟩ := B.isSubbundleFrameOn_transport hX hσ'
  exact ⟨Prod.fst ⁻¹' U, hU.preimage continuous_fst, hp,
    (fun i q ↦ B.equiv q (σ i q.1)), hτ, hτs⟩


end Frames

end Collar

end TauCeti.SmoothCollar
