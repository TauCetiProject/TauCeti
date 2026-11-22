/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.VectorBundle
public import TauCeti.Geometry.Manifold.VectorBundle.Trivial

/-!
# Constructed collar comparisons

These clients obtain the comparison from the existence theorem, then evaluate its original
fibres. The trivial line checks nonzero transport, multiplication by `i`, inverse evaluation and
the zero identity. Literal rank zero, empty boundary and zero-dimensional boundary are included.
-/

public section

open Bundle TauCeti TauCeti.SmoothCollar TauCeti.EuclideanHalfSpace Set Module
open scoped Manifold ContDiff
namespace TauCeti.SmoothCollar.Examples

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ∞ M]
  [T2Space ↥((𝓡∂ (n + 1)).boundary M)]
  [CompactSpace ↥((𝓡∂ (n + 1)).boundary M)]

/-- The constructed line comparison sends `1` to a nonzero vector and respects `i`, while
its actual fibrewise inverse recovers every original boundary vector. -/
theorem exists_lineComparison (c : SmoothCollar n ∞ M) :
    ∃ (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
      (B : BundleComparison c ℂ (Trivial M ℂ) ε hε0 hε1),
      ∀ p, B.equiv p 1 ≠ 0 ∧
        B.equiv p (Complex.I • 1) = Complex.I • B.equiv p 1 ∧
        (B.equiv p).symm (B.equiv p 1) = 1 := by
  obtain ⟨ε, h0, h1, ⟨B⟩⟩ := exists_bundleComparison ℂ (Trivial M ℂ) c
  refine ⟨ε, h0, h1, B, fun p ↦ ⟨?_, (B.equiv p).map_smul _ _, ?_⟩⟩
  · intro h
    exact one_ne_zero ((B.equiv p).injective (h.trans (B.equiv p).map_zero.symm))
  · exact (B.equiv p).symm_apply_apply _

/-- The produced comparison is exactly the original total-space identity on the zero slice. -/
example (c : SmoothCollar n ∞ M) :
    ∃ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1)
      (B : BundleComparison c ℂ (Trivial M ℂ) ε h0 h1),
      ∀ (y : ↥((𝓡∂ (n + 1)).boundary M)),
        (TotalSpace.mk' ℂ (E := Trivial M ℂ)
          (c (y, Set.inclusion (fun _ ht ↦ mem_normalIioOpens.mpr
            (lt_trans (mem_normalIioOpens.mp ht) h1)) (normalIioOpensZero h0)))
          (B.equiv (y, normalIioOpensZero h0) (1 : ℂ))) =
            TotalSpace.mk' ℂ (E := Trivial M ℂ) (y : M) (1 : ℂ) := by
  obtain ⟨ε, h0, h1, ⟨B⟩⟩ := exists_bundleComparison ℂ (Trivial M ℂ) c
  exact ⟨ε, h0, h1, B, fun y ↦ B.zero_eq y (1 : ℂ)⟩

/-- No nonzero fibre vector or positive fibre rank is required. -/
example (c : SmoothCollar n ∞ M) :
    ∃ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1)
      (B : BundleComparison c (Fin 0 → ℂ) (Trivial M (Fin 0 → ℂ)) ε h0 h1),
      ∀ p, B.equiv p 0 = 0 ∧ (B.equiv p).symm 0 = 0 := by
  obtain ⟨ε, h0, h1, ⟨B⟩⟩ := exists_bundleComparison (Fin 0 → ℂ) (Trivial M (Fin 0 → ℂ)) c
  exact ⟨ε, h0, h1, B, fun p ↦ ⟨(B.equiv p).map_zero, (B.equiv p).symm.map_zero⟩⟩

/-- Empty boundary uses the actual empty collar, with no selected boundary point. -/
example [IsEmpty ↥((𝓡∂ (n + 1)).boundary M)] :
    ∃ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1),
      Nonempty (BundleComparison (SmoothCollar.ofIsEmpty n ∞ M)
        ℂ (Trivial M ℂ) ε h0 h1) :=
  exists_bundleComparison ℂ (Trivial M ℂ) _

local instance boundarySmooth : IsManifold (𝓡 n) ∞ ↥((𝓡∂ (n + 1)).boundary M) :=
  isManifold_boundary M

omit [T2Space ↥((𝓡∂ (n + 1)).boundary M)]
  [CompactSpace ↥((𝓡∂ (n + 1)).boundary M)] in
private theorem lineSection_smooth (g : ↥((𝓡∂ (n + 1)).boundary M) → ℝ)
    (hg : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ g) :
    ContMDiff (𝓡 n) ((𝓡∂ (n + 1)).prod 𝓘(ℝ, ℂ)) ∞
      (fun y : ↥((𝓡∂ (n + 1)).boundary M) ↦
        TotalSpace.mk' ℂ (E := Trivial M ℂ) (y : M) (g y • (1 : ℂ))) := by
  exact Bundle.Trivial.contMDiff_mk_iff.2
    ⟨(isImmersion_subtypeVal_boundary (k := ∞) M).contMDiff, hg.smul contMDiff_const⟩

omit [T2Space ↥((𝓡∂ (n + 1)).boundary M)]
  [CompactSpace ↥((𝓡∂ (n + 1)).boundary M)] in
private theorem lineFrame (g : ↥((𝓡∂ (n + 1)).boundary M) → ℝ)
    (hg : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ g) (hgn : ∀ y, g y ≠ 0) :
    IsSubbundleFrameOn ℂ (E := (ContinuousMap.subtypeVal
      ((𝓡∂ (n + 1)).boundary M) : _ → M) *ᵖ (Trivial M ℂ))
      (fun _ ↦ Submodule.span ℝ {(1 : ℂ)})
      (fun (_ : Unit) y ↦ g y • (1 : ℂ)) univ := by
  have hs : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, ℂ)) ∞
      (fun y ↦ TotalSpace.mk' ℂ (E := (ContinuousMap.subtypeVal
        ((𝓡∂ (n + 1)).boundary M) : _ → M) *ᵖ (Trivial M ℂ)) y (g y • (1 : ℂ))) :=
    (Pullback.contMDiff_iff (ContinuousMap.subtypeVal ((𝓡∂ (n + 1)).boundary M))
      (isImmersion_subtypeVal_boundary (k := ∞) M).contMDiff).2
        ⟨contMDiff_id, lineSection_smooth g hg⟩
  refine ⟨fun _ ↦ hs.continuous.continuousOn, fun {y} _ ↦ ?_, fun {y} _ ↦ ?_⟩
  -- The native boundary pullback of the trivial line has the original complex fibre.
  -- Expose that fibre and its displayed frame before applying the scalar independence law.
  · change LinearIndependent ℝ (fun _ : Unit ↦ g y • (1 : ℂ))
    rw [linearIndependent_unique_iff]
    exact smul_ne_zero (hgn y) one_ne_zero
  -- Likewise, the native frame span is read in the original fibre before the scalar-span law.
  · change Submodule.span ℝ (range (fun _ : Unit ↦ g y • (1 : ℂ))) = _
    rw [range_unique]
    exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (hgn y)) 1

/-- A real change of boundary frame has exactly its original coefficient in an actual smooth
complex-linear collar trivialization, at every depth. The coefficient may vary with the boundary
point; its nonzero frame remains nonzero throughout the collar. -/
theorem exists_real_frame_coordinates (c : SmoothCollar n ∞ M)
    (g : ↥((𝓡∂ (n + 1)).boundary M) → ℝ)
    (hg : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ g) (hgn : ∀ y, g y ≠ 0) :
    ∃ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1)
      (B : BundleComparison c ℂ (Trivial M ℂ) ε h0 h1),
    let b₁ : C(↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens ε, M) :=
      ⟨fun p ↦ c (p.1, Set.inclusion (fun _ ht ↦
        mem_normalIioOpens.mpr (lt_trans (mem_normalIioOpens.mp ht) h1)) p.2),
        c.continuous.comp (continuous_fst.prodMk ((continuous_inclusion (fun _ ht ↦
          mem_normalIioOpens.mpr (lt_trans (mem_normalIioOpens.mp ht) h1))).comp continuous_snd))⟩
    ∃ (e : Trivialization ℂ (π ℂ ((b₁ : _ → M) *ᵖ (Trivial M ℂ)))) (_ : e.IsLinear ℂ),
      e.toOpenPartialHomeomorph ∈
        (contMDiffFiberwiseLinear _ ℂ ((𝓡 n).prod (𝓡∂ 1)) ∞).maximalAtlas
          (TotalSpace ℂ ((b₁ : _ → M) *ᵖ (Trivial M ℂ))) ∧
      e.baseSet = univ ∧
      ∀ (y : ↥((𝓡∂ (n + 1)).boundary M)) (t : normalIioOpens ε),
        e ⟨(y, t), B.equiv (y, t) (g y • (1 : ℂ))⟩ = ((y, t), (g y : ℂ)) ∧
          B.equiv (y, t) (g y • (1 : ℂ)) ≠ 0 := by
  obtain ⟨ε, h0, h1, ⟨B⟩⟩ := exists_bundleComparison ℂ (Trivial M ℂ) c
  let hX := lineFrame (fun _ : ↥((𝓡∂ (n + 1)).boundary M) ↦ 1)
    contMDiff_const (fun _ ↦ one_ne_zero)
  let hY := lineFrame g hg hgn
  have hL y (_ : y ∈ (univ : Set ↥((𝓡∂ (n + 1)).boundary M))) :=
    isMaximalTotallyReal_span_one
  have hσ := lineSection_smooth (fun _ : ↥((𝓡∂ (n + 1)).boundary M) ↦ 1) contMDiff_const
  obtain ⟨e, he, hAtlas, hBase, hCoord⟩ := B.exists_adaptedTrivialization hX
    (fun _ ↦ hσ.contMDiffOn) isOpen_univ hL (Basis.singleton Unit ℂ)
  have hτ := (B.isSubbundleFrameOn_transport hY
    (fun _ ↦ (lineSection_smooth g hg).contMDiffOn)).1
  refine ⟨ε, h0, h1, B, e, he, hAtlas, by simpa only [preimage_univ] using hBase,
    fun y t ↦ ⟨?_, ?_⟩⟩
  · let β : Basis Unit ℂ ℂ := hX.complexBasis (x := y) (mem_univ y) (hL y (mem_univ y))
    have hβ : β () = (1 : ℂ) := by
      have h := congrFun (hX.coe_complexBasis (x := y) (mem_univ y)
        (hL y (mem_univ y))) ()
      -- `coe_complexBasis` returns the original boundary frame, whose coefficient here is one.
      exact h.trans (one_smul ℝ (1 : ℂ))
    have hv : g y • (1 : ℂ) = (g y : ℂ) • β () := by rw [hβ]; simp
    have hc : β.equiv (Basis.singleton Unit ℂ) (Equiv.refl Unit) (g y • (1 : ℂ)) =
        (g y : ℂ) := by
      rw [hv, map_smul, Basis.equiv_apply, Equiv.refl_apply]
      simp
    exact (hCoord (y, t) (mem_univ y) (g y • (1 : ℂ))).trans
      (congrArg (fun z ↦ ((y, t), z)) hc)
  · exact (hτ.linearIndependent (mem_univ (y, t))).ne_zero ()


/-- A nonconstant real boundary-frame coefficient stays nonconstant, while it is unchanged
at every depth in the actual native smooth trivialization. -/
example (c : SmoothCollar n ∞ M) (g : ↥((𝓡∂ (n + 1)).boundary M) → ℝ)
    (hg : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ g) (hgn : ∀ y, g y ≠ 0)
    (y₀ y₁ : ↥((𝓡∂ (n + 1)).boundary M)) (hdiff : g y₀ ≠ g y₁) :
    ∃ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1)
      (B : BundleComparison c ℂ (Trivial M ℂ) ε h0 h1),
    let b₁ : C(↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens ε, M) :=
      ⟨fun p ↦ c (p.1, Set.inclusion (fun _ ht ↦
        mem_normalIioOpens.mpr (lt_trans (mem_normalIioOpens.mp ht) h1)) p.2),
        c.continuous.comp (continuous_fst.prodMk ((continuous_inclusion (fun _ ht ↦
          mem_normalIioOpens.mpr (lt_trans (mem_normalIioOpens.mp ht) h1))).comp continuous_snd))⟩
    ∃ (e : Trivialization ℂ (π ℂ ((b₁ : _ → M) *ᵖ (Trivial M ℂ)))) (_ : e.IsLinear ℂ),
      e.toOpenPartialHomeomorph ∈
        (contMDiffFiberwiseLinear _ ℂ ((𝓡 n).prod (𝓡∂ 1)) ∞).maximalAtlas
          (TotalSpace ℂ ((b₁ : _ → M) *ᵖ (Trivial M ℂ))) ∧
      ∀ s t : normalIioOpens ε,
        (e ⟨(y₀, s), B.equiv (y₀, s) (g y₀ • (1 : ℂ))⟩).2 ≠
          (e ⟨(y₁, t), B.equiv (y₁, t) (g y₁ • (1 : ℂ))⟩).2 := by
  obtain ⟨ε, h0, h1, B, e, he, hAtlas, _, hCoord⟩ := exists_real_frame_coordinates c g hg hgn
  refine ⟨ε, h0, h1, B, e, he, hAtlas, fun s t ↦ ?_⟩
  rw [congrArg Prod.snd (hCoord y₀ s).1, congrArg Prod.snd (hCoord y₁ t).1]
  exact fun h ↦ hdiff (Complex.ofReal_injective h)


/-- Literal rank zero also constructs the native smooth complex trivialization from the empty
real frame, instead of only checking a fibrewise zero equation. -/
example (c : SmoothCollar n ∞ M) :
    ∃ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1)
      (B : BundleComparison c (Fin 0 → ℂ) (Trivial M (Fin 0 → ℂ)) ε h0 h1),
    let b₁ : C(↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens ε, M) :=
      ⟨fun p ↦ c (p.1, Set.inclusion (fun _ ht ↦
        mem_normalIioOpens.mpr (lt_trans (mem_normalIioOpens.mp ht) h1)) p.2),
        c.continuous.comp (continuous_fst.prodMk ((continuous_inclusion (fun _ ht ↦
          mem_normalIioOpens.mpr (lt_trans (mem_normalIioOpens.mp ht) h1))).comp continuous_snd))⟩
    ∃ (e : Trivialization (Fin 0 → ℂ) (π (Fin 0 → ℂ)
        ((b₁ : _ → M) *ᵖ (Trivial M (Fin 0 → ℂ))))) (_ : e.IsLinear ℂ),
      e.toOpenPartialHomeomorph ∈
        (contMDiffFiberwiseLinear _ (Fin 0 → ℂ) ((𝓡 n).prod (𝓡∂ 1)) ∞).maximalAtlas
          (TotalSpace (Fin 0 → ℂ) ((b₁ : _ → M) *ᵖ (Trivial M (Fin 0 → ℂ)))) ∧
      ∀ p, e ⟨p, (0 : Fin 0 → ℂ)⟩ = (p, 0) := by
  obtain ⟨ε, h0, h1, ⟨B⟩⟩ :=
    exists_bundleComparison (Fin 0 → ℂ) (Trivial M (Fin 0 → ℂ)) c
  let σ : Fin 0 → ∀ y : ↥((𝓡∂ (n + 1)).boundary M), Trivial M (Fin 0 → ℂ) (y : M) :=
    fun i ↦ Fin.elim0 i
  have hX : IsSubbundleFrameOn (Fin 0 → ℂ) (E := (ContinuousMap.subtypeVal
      ((𝓡∂ (n + 1)).boundary M) : _ → M) *ᵖ (Trivial M (Fin 0 → ℂ)))
      (fun y ↦ (⊥ : Submodule ℝ (Trivial M (Fin 0 → ℂ) (y : M)))) σ univ := by
    refine ⟨fun i ↦ Fin.elim0 i, fun _ ↦ linearIndependent_empty_type, fun {y} _ ↦ ?_⟩
    -- The rank-zero boundary pullback is the original `Fin 0 → ℂ` fibre; the frame range is empty.
    exact (congrArg (Submodule.span ℝ) (range_eq_empty _)).trans Submodule.span_empty
  have hL (y : ↥((𝓡∂ (n + 1)).boundary M)) (_ : y ∈ (univ : Set _)) :
      IsMaximalTotallyReal ((LinearMap.lsmul ℂ (Trivial M (Fin 0 → ℂ) (y : M))
        Complex.I).restrictScalars ℝ) ⊥ := by
    rw [isMaximalTotallyReal_iff]
    exact ⟨disjoint_bot_left, codisjoint_iff.mpr (Subsingleton.elim _ _)⟩
  obtain ⟨e, he, hAtlas, _, hCoord⟩ := B.exists_adaptedTrivialization hX
    (fun i ↦ Fin.elim0 i) isOpen_univ hL (Pi.basisFun ℂ (Fin 0))
  refine ⟨ε, h0, h1, B, e, he, hAtlas, fun p ↦ ?_⟩
  apply Prod.ext
  · simpa only [map_zero] using
      congrArg Prod.fst (hCoord p (mem_univ p.1) (0 : Fin 0 → ℂ))
  · exact Subsingleton.elim _ _


section ArbitraryBundle

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F]
  (V : M → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance realBundle : VectorBundle ℝ F V := VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle ∞ F V (𝓡∂ (n + 1))]

/-- An arbitrary native bundle, without a global frame, has the same constructed inverse,
base projection and maximal totally real boundary-subspace transport. -/
example (c : SmoothCollar n ∞ M)
    (L : ∀ y : ↥((𝓡∂ (n + 1)).boundary M), Submodule ℝ (V (y : M)))
    (hL : ∀ y : ↥((𝓡∂ (n + 1)).boundary M), IsMaximalTotallyReal
      ((LinearMap.lsmul ℂ (V (y : M)) Complex.I).restrictScalars ℝ) (L y)) :
    ∃ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1)
      (B : BundleComparison c F V ε h0 h1),
      ∀ (p : ↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens ε) (v : V (p.1 : M)),
        (B.equiv p).symm (B.equiv p v) = v ∧
        (B.diffeomorph ⟨p, v⟩).proj = p ∧
        IsMaximalTotallyReal ((LinearMap.lsmul ℂ _ Complex.I).restrictScalars ℝ)
          (B.transportSubspace L p) := by
  obtain ⟨ε, h0, h1, ⟨B⟩⟩ := exists_bundleComparison F V c
  exact ⟨ε, h0, h1, B, fun p v ↦ ⟨(B.equiv p).symm_apply_apply v,
    congrArg TotalSpace.proj (B.apply_eq p v),
    (B.isMaximalTotallyReal_transportSubspace_iff L p).2 (hL p.1)⟩⟩

/-- Two actual boundary frames retain real, depth-independent coordinates under the constructed
comparison; transported frame vectors also satisfy the public subspace membership API. -/
example (c : SmoothCollar n ∞ M) {ι κ : Type*}
    {L : ∀ y : ↥((𝓡∂ (n + 1)).boundary M), Submodule ℝ (V (y : M))}
    {σ : ι → ∀ y : ↥((𝓡∂ (n + 1)).boundary M), V (y : M)}
    {τ : κ → ∀ y : ↥((𝓡∂ (n + 1)).boundary M), V (y : M)}
    (hX : IsSubbundleFrameOn F (E := (ContinuousMap.subtypeVal
      ((𝓡∂ (n + 1)).boundary M) : _ → M) *ᵖ V) L σ univ)
    (hY : IsSubbundleFrameOn F (E := (ContinuousMap.subtypeVal
      ((𝓡∂ (n + 1)).boundary M) : _ → M) *ᵖ V) L τ univ)
    (hL : ∀ y : ↥((𝓡∂ (n + 1)).boundary M), IsMaximalTotallyReal
      ((LinearMap.lsmul ℂ (V (y : M)) Complex.I).restrictScalars ℝ) (L y)) :
    ∃ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1)
      (B : BundleComparison c F V ε h0 h1),
      ∀ (y : ↥((𝓡∂ (n + 1)).boundary M)) (t : normalIioOpens ε) (i : ι) (j : κ),
        let β := hX.complexBasis (x := y) (mem_univ y) (hL y)
        ((β.map (B.equiv (y, t)).toLinearEquiv).repr (B.equiv (y, t) (τ j y))) i =
          ((β.repr (τ j y) i).re : ℂ) ∧
        B.equiv (y, t) (τ j y) ∈ B.transportSubspace L (y, t) := by
  obtain ⟨ε, h0, h1, ⟨B⟩⟩ := exists_bundleComparison F V c
  refine ⟨ε, h0, h1, B, fun y t i j ↦ ?_⟩
  exact ⟨B.repr_map_equiv_apply_eq_ofReal_re hX (mem_univ y) (hL y) t i
    (τ j y) (hY.apply_mem j (mem_univ y)),
    (B.equiv_apply_mem_transportSubspace_iff L (y, t) (τ j y)).2
      (hY.apply_mem j (mem_univ y))⟩

end ArbitraryBundle

end

noncomputable section

/-- Literal zero-dimensional boundary, without a positive-dimension condition on it. -/
example {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M]
    [IsManifold (𝓡∂ 1) ∞ M] [T2Space ↥((𝓡∂ 1).boundary M)]
    [CompactSpace ↥((𝓡∂ 1).boundary M)] (c : SmoothCollar 0 ∞ M) :
    ∃ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1)
      (B : BundleComparison c ℂ (Trivial M ℂ) ε h0 h1), ∀ p, B.equiv p 1 ≠ 0 := by
  obtain ⟨ε, h0, h1, B, hB⟩ := exists_lineComparison c
  exact ⟨ε, h0, h1, B, fun p ↦ (hB p).1⟩

/-- The native charted-space constructor on the literal empty carrier. -/
local instance emptyCharted (n : ℕ) : ChartedSpace (EuclideanHalfSpace (n + 1)) Empty :=
  ChartedSpace.empty _ _

/-- The actual empty manifold and its native empty collar require no chosen base point. -/
example (n : ℕ) :
    ∃ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1),
      Nonempty (BundleComparison (SmoothCollar.ofIsEmpty n ∞ Empty)
        ℂ (Trivial Empty ℂ) ε h0 h1) :=
  exists_bundleComparison ℂ (Trivial Empty ℂ) _

end

end TauCeti.SmoothCollar.Examples
