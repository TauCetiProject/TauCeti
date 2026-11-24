/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
import Mathlib.Topology.VectorBundle.FiniteDimensional
import TauCeti.Analysis.Complex.Schwarz
import Mathlib.Topology.ContinuousMap.Compact
import TauCeti.Geometry.Manifold.CoordinateBall

/-!
# Finite determination of holomorphic sections

On a compact Hausdorff complex curve, finitely many fibre evaluations determine every
holomorphic section of a finite-rank vector bundle. Consequently its native section module
is finite-dimensional. The proof uses nested coordinate discs, bounds for the actual bundle
transitions on compact overlaps, and the vector-valued Schwarz lemma at a finite set of
sample points. It chooses no topology on the section module.

The complex chart model is the ordinary boundaryless model. Neither connectedness nor
nonemptiness of the base nor positive rank of the bundle is required.

## References

* O. Forster, *Lectures on Riemann Surfaces*, §§14–16.
-/

public noncomputable section

open Bundle Function Metric Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ContMDiffSection

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {V : X → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
  [VectorBundle ℂ F V] {n : ℕ∞ω} [IsManifold 𝓘(ℂ) n X]
  [ContMDiffVectorBundle n F V 𝓘(ℂ)]

private def chartReading (e : OpenPartialHomeomorph X ℂ) (T : Trivialization F (π F V))
    [MemTrivializationAtlas T] (s : Cₛ^n⟮𝓘(ℂ); F, V⟯) (z : ℂ) : F :=
  T.linearMapAt ℂ (e.symm z) (s (e.symm z))

private theorem differentiableOn_chartReading (hn : n ≠ 0)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (T : Trivialization F (π F V)) [MemTrivializationAtlas T]
    (s : Cₛ^n⟮𝓘(ℂ); F, V⟯) :
    DifferentiableOn ℂ (chartReading e T s) (e.target ∩ e.symm ⁻¹' T.baseSet) := by
  have hs := T.contMDiffOn_section_baseSet_iff.mp s.contMDiff.contMDiffOn
  have he' := contMDiffOn_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ)) (n := n) he)
  have hc := hs.comp (he'.mono inter_subset_left) (fun _ hz ↦ hz.2)
  refine (hc.contDiffOn.differentiableOn hn).congr ?_
  intro z hz
  exact congrFun (T.coe_linearMapAt_of_mem hz.2) _

private def closedBallReading (hn : n ≠ 0)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (T : Trivialization F (π F V)) [MemTrivializationAtlas T]
    (c : ℂ) (r : ℝ) (h : closedBall c r ⊆ e.target ∩ e.symm ⁻¹' T.baseSet)
    (s : Cₛ^n⟮𝓘(ℂ); F, V⟯) : C(closedBall c r, F) where
  toFun z := chartReading e T s z
  continuous_toFun := ((differentiableOn_chartReading hn e he T s).continuousOn.mono h)
    |>.comp_continuous continuous_subtypeVal (fun z ↦ z.property)

private structure NestedDiscs (ι : Type u) where
  e : ι → OpenPartialHomeomorph X ℂ
  c : ι → ℂ
  r : ι → ℝ
  k : ι → X
  chart_mem : ∀ i, e i ∈ atlas ℂ X
  radius_pos : ∀ i, 0 < r i
  valid : ∀ i, closedBall (c i) (2 * r i) ⊆
    (e i).target ∩ (e i).symm ⁻¹' (trivializationAt F V (k i)).baseSet
  cover : ∀ x, ∃ i, x ∈ (e i).symm '' closedBall (c i) (r i)

omit [NormedSpace ℂ F] [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
  [VectorBundle ℂ F V] in
private theorem exists_nestedDiscs [CompactSpace X] :
    ∃ (ι : Type u) (_ : Finite ι), Nonempty (NestedDiscs (F := F) (V := V) ι) := by
  classical
  let U (x : X) : Opens X := ⟨(trivializationAt F V x).baseSet,
    (trivializationAt F V x).open_baseSet⟩
  have hU : IsOpenCover U := .mk <| eq_top_iff.2 fun x _ ↦
    Opens.mem_iSup.mpr ⟨x, mem_baseSet_trivializationAt F V x⟩
  obtain ⟨ι, hι, e, c, r, he, hr, htarget, hsub, hcover⟩ :=
    TauCeti.exists_finite_preimageBall_cover (H := ℂ) 2 hU
  let : Finite ι := hι
  choose k hk using hsub
  refine ⟨ι, inferInstance, ⟨⟨e, c, r, k, he, hr, ?_, ?_⟩⟩⟩
  · exact fun i z hz ↦ ⟨htarget i hz, hk i ⟨z, hz, rfl⟩⟩
  · intro x
    have hx : x ∈ ⨆ i, (e i).preimageBall (c i) (r i) := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    obtain ⟨hx, hz⟩ := OpenPartialHomeomorph.mem_preimageBall.mp hi
    exact ⟨i, e i x, ball_subset_closedBall hz, (e i).left_inv hx⟩

namespace NestedDiscs

variable {ι : Type u}

private abbrev T (A : NestedDiscs (F := F) (V := V) ι) (i : ι) :
    Trivialization F (π F V) := trivializationAt F V (A.k i)
private def K (A : NestedDiscs (F := F) (V := V) ι) (i : ι) : Set X :=
  (A.e i).symm '' closedBall (A.c i) (A.r i)
private def L (A : NestedDiscs (F := F) (V := V) ι) (i : ι) : Set X :=
  (A.e i).symm '' closedBall (A.c i) (2 * A.r i)

omit [NormedSpace ℂ F] [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
  [VectorBundle ℂ F V] in
private theorem inner (A : NestedDiscs (F := F) (V := V) ι) (i : ι) : closedBall (A.c i) (A.r i) ⊆
    (A.e i).target ∩ (A.e i).symm ⁻¹' (A.T i).baseSet :=
  (closedBall_subset_closedBall (by linarith [A.radius_pos i])).trans (A.valid i)

omit [NormedSpace ℂ F] [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
  [VectorBundle ℂ F V] in
private theorem compact_K (A : NestedDiscs (F := F) (V := V) ι) (i : ι) : IsCompact (A.K i) :=
  (isCompact_closedBall _ _).image_of_continuousOn
    ((A.e i).continuousOn_symm.mono fun _ hz ↦ (A.inner i hz).1)

omit [NormedSpace ℂ F] [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
  [VectorBundle ℂ F V] in
private theorem compact_L (A : NestedDiscs (F := F) (V := V) ι) (i : ι) : IsCompact (A.L i) :=
  (isCompact_closedBall _ _).image_of_continuousOn
    ((A.e i).continuousOn_symm.mono fun _ hz ↦ (A.valid i hz).1)

omit [NormedSpace ℂ F] [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
  [VectorBundle ℂ F V] in
private theorem K_subset (A : NestedDiscs (F := F) (V := V) ι) (i : ι) :
    A.K i ⊆ (A.T i).baseSet := by
  rintro _ ⟨z, hz, rfl⟩
  exact (A.inner i hz).2

omit [NormedSpace ℂ F] [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
  [VectorBundle ℂ F V] in
private theorem L_subset (A : NestedDiscs (F := F) (V := V) ι) (i : ι) :
    A.L i ⊆ (A.T i).baseSet := by
  rintro _ ⟨z, hz, rfl⟩
  exact (A.valid i hz).2

private def readingMap (A : NestedDiscs (F := F) (V := V) ι)
    (hn : n ≠ 0) :
    Cₛ^n⟮𝓘(ℂ); F, V⟯ →ₗ[ℂ] ((i : ι) → C(closedBall (A.c i) (A.r i), F)) where
  toFun s i := closedBallReading hn (A.e i) (A.chart_mem i) (A.T i)
    (A.c i) (A.r i) (A.inner i) s
  map_add' s t := by funext i; ext z; exact (A.T i).linearMapAt ℂ _ |>.map_add _ _
  map_smul' a s := by funext i; ext z; exact (A.T i).linearMapAt ℂ _ |>.map_smul _ _

variable [Fintype ι]

private theorem inner_norm_le (A : NestedDiscs (F := F) (V := V) ι)
    (hn : n ≠ 0) (s : Cₛ^n⟮𝓘(ℂ); F, V⟯) (i : ι)
    {x : X} (hx : x ∈ A.K i) :
    ‖(A.T i).linearMapAt ℂ x (s x)‖ ≤ ‖A.readingMap hn s‖ := by
  obtain ⟨z, hz, rfl⟩ := hx
  exact ((A.readingMap hn s i).norm_coe_le_norm ⟨z, hz⟩).trans
    (norm_le_pi_norm (A.readingMap hn s) i)

omit [Fintype ι] in
private theorem exists_transition_bound [Finite ι] (A : NestedDiscs (F := F) (V := V) ι)
    [T2Space X] : ∃ C : ℝ, 1 ≤ C ∧ ∀ i j x, x ∈ A.L i ∩ A.K j →
    ‖((A.T j).coordChangeL ℂ (A.T i) x : F →L[ℂ] F)‖ ≤ C := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hB (i j : ι) : ∃ B : ℝ, ∀ x ∈ A.L i ∩ A.K j,
      ‖((A.T j).coordChangeL ℂ (A.T i) x : F →L[ℂ] F)‖ ≤ B :=
    ((A.compact_L i).inter (A.compact_K j)).exists_bound_of_continuousOn
      ((continuousOn_coordChange ℂ (A.T j) (A.T i)).mono fun x hx ↦
        ⟨A.K_subset j hx.2, A.L_subset i hx.1⟩)
  choose B hB using hB
  let C : ℝ := 1 + ∑ i, ∑ j, |B i j|
  have hC : 1 ≤ C := by
    have : 0 ≤ ∑ i, ∑ j, |B i j| := by positivity
    dsimp [C]
    linarith
  refine ⟨C, hC, fun i j x hx ↦ (hB i j x hx).trans ?_⟩
  calc
    B i j ≤ |B i j| := le_abs_self _
    _ ≤ ∑ j, |B i j| :=
      Finset.single_le_sum (f := fun b : ι ↦ |B i b|)
        (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i, ∑ j, |B i j| :=
      Finset.single_le_sum (f := fun a : ι ↦ ∑ b : ι, |B a b|)
        (fun _ _ ↦ by positivity) (Finset.mem_univ i)
    _ ≤ C := by dsimp [C]; linarith

private theorem exists_outer_bound (A : NestedDiscs (F := F) (V := V) ι)
    [T2Space X] (hn : n ≠ 0) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (s : Cₛ^n⟮𝓘(ℂ); F, V⟯) i z, z ∈ closedBall (A.c i) (2 * A.r i) →
      ‖chartReading (A.e i) (A.T i) s z‖ ≤ C * ‖A.readingMap hn s‖ := by
  obtain ⟨C, hC, hB⟩ := A.exists_transition_bound
  refine ⟨C, hC, ?_⟩
  intro s i z hz
  let x := (A.e i).symm z
  have hxL : x ∈ A.L i := ⟨z, hz, rfl⟩
  obtain ⟨j, hxK⟩ := A.cover x
  have htrans : (A.T i).linearMapAt ℂ x (s x) =
      (A.T j).coordChangeL ℂ (A.T i) x ((A.T j).linearMapAt ℂ x (s x)) := by
    rw [(A.T j).coordChangeL_apply (A.T i) ⟨A.K_subset j hxK, A.L_subset i hxL⟩,
      (A.T j).coe_linearMapAt_of_mem (A.K_subset j hxK),
      (A.T j).symm_apply_apply_mk (A.K_subset j hxK),
      (A.T i).coe_linearMapAt_of_mem (A.L_subset i hxL)]
  -- The coordinate reading evaluates the original fibre at the inverse base chart.
  unfold chartReading
  rw [htrans]
  exact ((A.T j).coordChangeL ℂ (A.T i) x : F →L[ℂ] F).le_opNorm _ |>.trans
    (mul_le_mul (hB i j x ⟨hxL, hxK⟩) (A.inner_norm_le hn s j hxK)
      (norm_nonneg _) (by linarith))

omit [Fintype ι] in
private theorem readingMap_injective [Finite ι] (A : NestedDiscs (F := F) (V := V) ι)
    (hn : n ≠ 0) : Injective (A.readingMap hn) := by
  let : Fintype ι := Fintype.ofFinite ι
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro s hs
  ext x
  simp only [ContMDiffSection.coe_zero, Pi.zero_apply]
  obtain ⟨i, hx⟩ := A.cover x
  have heq : (A.T i).linearMapAt ℂ x (s x) = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    simpa only [hs, norm_zero] using A.inner_norm_le hn s i hx
  have hxT := A.K_subset i hx
  apply ((A.T i).linearEquivAt ℂ x hxT).injective
  rw [map_zero]
  exact (congrArg (fun L : V x →ₗ[ℂ] F ↦ L (s x))
    ((A.T i).linearMapAt_def_of_mem (R := ℂ) hxT)).symm.trans heq

omit [Fintype ι] in
private theorem exists_finset_eval_injective [Finite ι] (A : NestedDiscs (F := F) (V := V) ι)
    [T2Space X] (hn : n ≠ 0) :
    ∃ P : Finset X, Injective (LinearMap.pi fun x : P ↦ evalLinearMap 𝓘(ℂ) F n V x) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨C, hC, hbound⟩ := A.exists_outer_bound hn
  have hε (i : ι) : 0 < A.r i / (4 * C) := div_pos (A.radius_pos i) (by linarith)
  choose P hP hPfinite hnet using fun i ↦
    finite_cover_balls_of_compact (isCompact_closedBall (A.c i) (A.r i)) (hε i)
  let Q : Finset X := Finset.univ.biUnion fun i ↦ (hPfinite i).toFinset.image (A.e i).symm
  refine ⟨Q, LinearMap.ker_eq_bot.mp ?_⟩
  apply LinearMap.ker_eq_bot'.mpr
  intro s hs
  have hzero (i : ι) (w : ℂ) (hw : w ∈ P i) : chartReading (A.e i) (A.T i) s w = 0 := by
    have hxQ : (A.e i).symm w ∈ Q := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
      Finset.mem_image.mpr ⟨w, (hPfinite i).mem_toFinset.mpr hw, rfl⟩⟩
    have hz : s ((A.e i).symm w) = 0 := by
      simpa only [LinearMap.pi_apply, evalLinearMap_apply, Pi.zero_apply] using congrFun hs ⟨_, hxQ⟩
    exact (congrArg ((A.T i).linearMapAt ℂ _) hz).trans (map_zero _)
  have hsmall : ‖A.readingMap hn s‖ ≤ ‖A.readingMap hn s‖ / 2 := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro z
    exact TauCeti.norm_le_half_of_eq_zero_on_net
      ((differentiableOn_chartReading hn (A.e i) (A.chart_mem i) (A.T i) s).mono
        (ball_subset_closedBall.trans (A.valid i)))
      (fun z hz ↦ hbound s i z (ball_subset_closedBall hz)) (hP i) (hnet i) (hzero i) z.property
  have hRs : A.readingMap hn s = 0 :=
    norm_eq_zero.mp (by linarith [norm_nonneg (A.readingMap hn s)])
  exact A.readingMap_injective hn (hRs.trans (map_zero _).symm)

end NestedDiscs

/-- Finitely many values in the original fibres determine a holomorphic section on a compact
Hausdorff complex curve. The section regularity may be any nonzero complex differentiability
order; neither connectedness nor nonemptiness nor finite rank is needed for this assertion. -/
theorem exists_finset_eval_injective_of_compactSpace [CompactSpace X] [T2Space X] (hn : n ≠ 0) :
    ∃ P : Finset X, Injective (LinearMap.pi fun x : P ↦ evalLinearMap 𝓘(ℂ) F n V x) := by
  obtain ⟨ι, hι, ⟨A⟩⟩ := exists_nestedDiscs (F := F) (V := V)
  let : Finite ι := hι
  exact A.exists_finset_eval_injective hn

/-- The native holomorphic section module of a finite-rank bundle on a compact Hausdorff
complex curve is finite-dimensional, at every nonzero complex differentiability order. -/
theorem finiteDimensional_of_compactSpace [CompactSpace X] [T2Space X] [FiniteDimensional ℂ F]
    (hn : n ≠ 0) : FiniteDimensional ℂ Cₛ^n⟮𝓘(ℂ); F, V⟯ := by
  let (x : X) : FiniteDimensional ℂ (V x) := VectorBundle.finiteDimensional ℂ F V x
  obtain ⟨P, hP⟩ := exists_finset_eval_injective_of_compactSpace (F := F) (V := V) hn
  exact FiniteDimensional.of_injective _ hP

/-- Analytic sections of a finite-rank holomorphic bundle on a compact Hausdorff complex curve
form a finite-dimensional complex vector space. -/
instance instFiniteDimensionalHolomorphic [CompactSpace X] [T2Space X]
    [FiniteDimensional ℂ F] [IsManifold 𝓘(ℂ) ω X]
    [ContMDiffVectorBundle ω F V 𝓘(ℂ)] : FiniteDimensional ℂ Cₛ^ω⟮𝓘(ℂ); F, V⟯ :=
  finiteDimensional_of_compactSpace (by simp)

/-- Complex smooth sections of a finite-rank holomorphic bundle on a compact complex curve
form a finite-dimensional complex vector space. -/
instance instFiniteDimensionalSmooth [CompactSpace X] [T2Space X]
    [FiniteDimensional ℂ F] [IsManifold 𝓘(ℂ) ∞ X]
    [ContMDiffVectorBundle ∞ F V 𝓘(ℂ)] : FiniteDimensional ℂ Cₛ^∞⟮𝓘(ℂ); F, V⟯ :=
  finiteDimensional_of_compactSpace (by simp)

end ContMDiffSection
