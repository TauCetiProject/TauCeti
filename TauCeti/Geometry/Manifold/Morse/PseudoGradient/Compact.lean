/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Existence
import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Pseudo-gradients near compact sets

A smooth function whose critical points on a compact set are nondegenerate has a smooth
pseudo-gradient on a neighbourhood of that set. The field strictly decreases the function at
every regular point of the neighbourhood and is literally the linear Morse-chart field on a
smaller chart around every critical point of the compact set.

This local form does not require the ambient manifold to be compact, and imposes no condition on
critical points away from the chosen compact set. It supplies pseudo-gradients on compact level
bands for the local deformation and handle-attachment constructions of Morse theory.

## Main declarations

* `IsCompact.exists_contMDiff_pseudoGradientOn_nhds`: existence near a compact set whose critical
  points are nondegenerate.
* `TauCeti.IsMorse.exists_contMDiff_pseudoGradientOn_nhds`: the specialization to a Morse
  function and an arbitrary compact set.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Proposition 2.2.3 and its proof.
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
  [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]

open TauCeti in
/-- **Existence of a pseudo-gradient near a compact set.** Let `K` be a compact subset of a
regular Hausdorff sigma-compact manifold and let `f` be smooth. If every critical point of `f` in
`K` is nondegenerate,
then on an open neighbourhood `U` of `K` there is a smooth vector field along which `f` strictly
decreases at every regular point. Around each critical point in `K`, the field agrees on the
whole source of a smaller Morse chart with that chart's linear pseudo-gradient field.

The field is defined globally, but no condition is imposed away from `U`. In particular the
ambient manifold need not be compact and `f` may have arbitrary critical points away from `K`. -/
theorem IsCompact.exists_contMDiff_pseudoGradientOn_nhds [T2Space M] [SigmaCompactSpace M]
    {K : Set M}
    (hK : IsCompact K) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)
    (hnd : ∀ x ∈ K, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 →
      IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x) :
    ∃ U ∈ 𝓝ˢ K, IsOpen U ∧
      ∃ X : (x : M) → TangentSpace 𝓘(ℝ, E) x,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
            (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
          (∀ x ∈ U, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x ≠ 0 →
            mvfderiv 𝓘(ℝ, E) f x (X x) < 0) ∧
          ∀ x ∈ K, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 →
            ∃ φ : MorseChart E f x, φ.toChart.source ⊆ U ∧
              ∀ y ∈ φ.toChart.source, X y = φ.field y := by
  classical
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  let C := criticalPoints 𝓘(ℝ, E) f ∩ K
  have hC : C.Finite := by
    refine (hK.inter_left (isClosed_criticalPoints (hf.of_le (by simp)))).finite ?_
    rw [isDiscrete_iff_nhdsNE]
    rintro x ⟨hx, hxK⟩
    rw [inf_principal_eq_bot]
    filter_upwards [(hnd x hxK
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 hx)).eventually_notMem_criticalPoints]
      with y hy using fun h ↦ hy h.1
  let φ : ∀ x ∈ C, MorseChart E f x := fun x hx ↦
    ((hnd x hx.2 (mem_criticalPoints_iff_mfderiv_eq_zero.1 hx.1)).nonempty_morseChart
      (Eventually.of_forall fun _ ↦ hf.contMDiffAt)).some
  obtain ⟨W, hW, hWdisj⟩ := hC.t2_separation
  have hA : ∀ x (hx : x ∈ C), ∃ A, A ∈ 𝓝 x ∧ IsClosed A ∧
      A ⊆ (φ x hx).toChart.source ∩ W x := fun x hx ↦
    exists_mem_nhds_isClosed_subset
      (Filter.inter_mem ((φ x hx).toChart.open_source.mem_nhds (φ x hx).mem_source)
        ((hW x).2.mem_nhds (hW x).1))
  choose A hAn hAc hAsub using hA
  let A' : M → Set M := fun x ↦ if hx : x ∈ C then A x hx else ∅
  have hA' : ∀ x (hx : x ∈ C), A' x = A x hx := fun x hx ↦ by simp [A', hx]
  let G := ⋃ x ∈ C, interior (A' x)
  have hGo : IsOpen G := isOpen_biUnion fun _ _ ↦ isOpen_interior
  have hcritical_mem_G {x : M} (hxK : x ∈ K)
      (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) : x ∈ G := by
    have hxC : x ∈ C := ⟨mem_criticalPoints_iff_mfderiv_eq_zero.2 hx, hxK⟩
    refine mem_iUnion₂.2 ⟨x, hxC, ?_⟩
    rw [hA' x hxC]
    exact mem_interior_iff_mem_nhds.2 (hAn x hxC)
  let R := K \ G
  have hRc : IsCompact R := hK.diff hGo
  have hRreg : ∀ x ∈ R, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x ≠ 0 := by
    intro x hx hzero
    exact hx.2 (hcritical_mem_G hx.1 hzero)
  have hB : ∀ x ∈ R, ∃ B, B ∈ 𝓝 x ∧ IsClosed B ∧
      B ⊆ (criticalPoints 𝓘(ℝ, E) f)ᶜ := fun x hx ↦
    exists_mem_nhds_isClosed_subset
      ((isClosed_criticalPoints (hf.of_le (by simp))).isOpen_compl.mem_nhds
        (fun hcrit ↦ hRreg x hx (mem_criticalPoints_iff_mfderiv_eq_zero.1 hcrit)))
  choose B hBn hBc hBsub using hB
  let B' : M → Set M := fun x ↦ if hx : x ∈ R then B x hx else ∅
  have hB' : ∀ x (hx : x ∈ R), B' x = B x hx := fun x hx ↦ by simp [B', hx]
  obtain ⟨q, hqR, hq⟩ := hRc.elim_nhds_subcover B' fun x hx ↦ by
    rw [hB' x hx]
    exact hBn x hx
  let D := ⋃ x ∈ q, B' x
  have hDc : IsClosed D := isClosed_biUnion_finset fun x hx ↦ by
    rw [hB' x (hqR x hx)]
    exact hBc x (hqR x hx)
  have hRD : R ⊆ D := hq
  have hDreg : D ⊆ (criticalPoints 𝓘(ℝ, E) f)ᶜ := by
    rintro y hy
    obtain ⟨x, hxq, hyB⟩ := mem_iUnion₂.1 hy
    rw [hB' x (hqR x hxq)] at hyB
    exact hBsub x (hqR x hxq) hyB
  have hAclosed : IsClosed (⋃ x ∈ C, A' x) :=
    hC.isClosed_biUnion fun x hx ↦ by rw [hA' x hx]; exact hAc x hx
  let ℓ : (y : M) → TangentSpace 𝓘(ℝ, E) y →L[ℝ] ℝ :=
    fun y ↦ mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y
  let t : (y : M) → Set (TangentSpace 𝓘(ℝ, E) y) := fun y ↦
    {v | y ∈ D → ℓ y v < 0} ∩
      ⋂ x, ⋂ (hx : x ∈ C), ⋂ (_ : y ∈ A x hx), {(φ x hx).field y}
  have ht : ∀ y, Convex ℝ (t y) := by
    intro y
    refine Convex.inter ?_ (convex_iInter fun x ↦ convex_iInter fun hx ↦
      convex_iInter fun _ ↦ convex_singleton _)
    by_cases hy : y ∈ D
    · simp only [hy, true_implies]
      change Convex ℝ {v | (ℓ y).toLinearMap v < 0}
      exact convex_halfSpace_lt (ℓ y).isLinear 0
    · simp [hy, convex_univ]
  have hloc : ∀ y₀ : M, ∃ V ∈ 𝓝 y₀, ∃ s : (y : M) → TangentSpace 𝓘(ℝ, E) y,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
        (fun y ↦ (⟨y, s y⟩ : TangentBundle 𝓘(ℝ, E) M)) V ∧ ∀ y ∈ V, s y ∈ t y := by
    intro y₀
    by_cases h : ∃ x, ∃ hx : x ∈ C, y₀ ∈ A x hx
    · obtain ⟨x, hx, hy₀⟩ := h
      have hVo : IsOpen ((φ x hx).toChart.source ∩ W x) :=
        (φ x hx).toChart.open_source.inter (hW x).2
      refine ⟨_, hVo.mem_nhds (hAsub x hx hy₀), (φ x hx).field,
        (φ x hx).contMDiffOn_field.mono inter_subset_left, fun y hy ↦ ⟨fun hyD ↦ ?_, ?_⟩⟩
      · have hycrit : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y ≠ 0 := by
          simpa only [mem_compl_iff, mem_criticalPoints_iff_mfderiv_eq_zero] using hDreg hyD
        exact (φ x hx).mvfderiv_field_apply_lt_zero hy.1 fun hyx ↦
          hycrit (hyx ▸ mem_criticalPoints_iff_mfderiv_eq_zero.1 hx.1)
      · simp only [mem_iInter, mem_singleton_iff]
        intro x' hx' hy'
        have hxx' : x = x' := by
          by_contra hne
          exact Set.disjoint_left.1 (hWdisj hx hx' hne) hy.2 ((hAsub x' hx' hy').2)
        subst hxx'
        rfl
    · simp only [not_exists] at h
      by_cases hy₀D : y₀ ∈ D
      · have hcrit : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y₀ ≠ 0 := by
          simpa only [mem_compl_iff, mem_criticalPoints_iff_mfderiv_eq_zero] using hDreg hy₀D
        obtain ⟨v, V, hV, hVc, hVneg⟩ :=
          exists_mem_nhds_mvfderiv_chartConstField_lt_zero hf hcrit
        refine ⟨_, Filter.inter_mem (hAclosed.isOpen_compl.mem_nhds ?_) hV,
          chartConstField E y₀ v,
          (contMDiffOn_chartConstField y₀ v).mono fun y hy ↦ hVc hy.2,
          fun y hy ↦ ⟨fun _ ↦ hVneg y hy.2, ?_⟩⟩
        · simp only [mem_compl_iff, mem_iUnion, not_exists]
          intro x hx hmem
          rw [hA' x hx] at hmem
          exact h x hx hmem
        · simp only [mem_iInter, mem_singleton_iff]
          intro x hx hyA
          exfalso
          refine hy.1 (mem_iUnion₂.2 ⟨x, hx, ?_⟩)
          rwa [hA' x hx]
      · refine ⟨Dᶜ ∩ (⋃ x ∈ C, A' x)ᶜ,
          Filter.inter_mem (hDc.isOpen_compl.mem_nhds hy₀D)
            (hAclosed.isOpen_compl.mem_nhds ?_), fun _ ↦ 0,
          (Bundle.contMDiff_zeroSection ℝ
            (TangentSpace 𝓘(ℝ, E) : M → Type _)).contMDiffOn,
          fun y hy ↦ ?_⟩
        · simp only [mem_compl_iff, mem_iUnion, not_exists]
          intro x hx hmem
          rw [hA' x hx] at hmem
          exact h x hx hmem
        · refine ⟨fun hyD ↦ (hy.1 hyD).elim, ?_⟩
          simp only [mem_iInter, mem_singleton_iff]
          intro x hx hyA
          exfalso
          exact hy.2 (mem_iUnion₂.2 ⟨x, hx, by rwa [hA' x hx]⟩)
  obtain ⟨s, hs⟩ := exists_contMDiffSection_forall_mem_convex_of_local 𝓘(ℝ, E)
    (n := (⊤ : ℕ∞)) (TangentSpace 𝓘(ℝ, E)) t ht hloc
  have hdesc : Continuous (fun y ↦ mvfderiv 𝓘(ℝ, E) f y (s y)) :=
    ((hf.contMDiff_mvfderiv_apply (m := (⊤ : ℕ∞)) (by simp)).comp s.contMDiff).continuous
  let V := (fun y ↦ mvfderiv 𝓘(ℝ, E) f y (s y)) ⁻¹' Iio 0
  let U := V ∪ G
  have hVo : IsOpen V := isOpen_Iio.preimage hdesc
  have hUo : IsOpen U := hVo.union hGo
  have hKU : K ⊆ U := by
    intro x hxK
    by_cases hxG : x ∈ G
    · exact Or.inr hxG
    · apply Or.inl
      have hxR : x ∈ R := ⟨hxK, hxG⟩
      exact (hs x).1 (hRD hxR)
  refine ⟨U, mem_nhdsSet_iff_forall.2 fun x hx ↦ hUo.mem_nhds (hKU hx), hUo, s,
    s.contMDiff, ?_, ?_⟩
  · intro y hy hyreg
    rcases hy with hyV | hyG
    · exact hyV
    · obtain ⟨x, hxC, hyA⟩ := mem_iUnion₂.1 hyG
      have hyA' : y ∈ interior (A x hxC) := by rwa [← hA' x hxC]
      have hysource : y ∈ (φ x hxC).toChart.source :=
        (hAsub x hxC (interior_subset hyA')).1
      have hsy : s y = (φ x hxC).field y := by
        have := (hs y).2
        simp only [mem_iInter, mem_singleton_iff] at this
        exact this x hxC (interior_subset hyA')
      rw [hsy]
      exact (φ x hxC).mvfderiv_field_apply_lt_zero hysource fun hyx ↦
        hyreg (hyx ▸ mem_criticalPoints_iff_mfderiv_eq_zero.1 hxC.1)
  · intro x hxK hx
    have hxC : x ∈ C := ⟨mem_criticalPoints_iff_mfderiv_eq_zero.2 hx, hxK⟩
    let ψ := (φ x hxC).restr isOpen_interior (mem_interior_iff_mem_nhds.2 (hAn x hxC))
    refine ⟨ψ, fun y hy ↦ ?_, fun y hy ↦ ?_⟩
    · rw [MorseChart.restr_source] at hy
      apply Or.inr
      refine mem_iUnion₂.2 ⟨x, hxC, ?_⟩
      rw [hA' x hxC]
      exact hy.2
    rw [MorseChart.restr_source] at hy
    have hyA : y ∈ A x hxC := interior_subset hy.2
    have hsy : s y = (φ x hxC).field y := by
      have := (hs y).2
      simp only [mem_iInter, mem_singleton_iff] at this
      exact this x hxC hyA
    simpa only [ψ, MorseChart.restr_field] using hsy

namespace TauCeti

/-- A Morse function has a smooth pseudo-gradient on a neighbourhood of every compact set. The
field retains the exact linear normal form on smaller Morse charts around the critical points in
that set. -/
theorem IsMorse.exists_contMDiff_pseudoGradientOn_nhds [T2Space M] [SigmaCompactSpace M]
    {K : Set M}
    (hf : IsMorse 𝓘(ℝ, E) f) (hK : IsCompact K) :
    ∃ U ∈ 𝓝ˢ K, IsOpen U ∧
      ∃ X : (x : M) → TangentSpace 𝓘(ℝ, E) x,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
            (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
          (∀ x ∈ U, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x ≠ 0 →
            mvfderiv 𝓘(ℝ, E) f x (X x) < 0) ∧
          ∀ x ∈ K, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 →
            ∃ φ : MorseChart E f x, φ.toChart.source ⊆ U ∧
              ∀ y ∈ φ.toChart.source, X y = φ.field y :=
  IsCompact.exists_contMDiff_pseudoGradientOn_nhds hK hf.contMDiff fun _ _ hx ↦
    hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero hx

end TauCeti
