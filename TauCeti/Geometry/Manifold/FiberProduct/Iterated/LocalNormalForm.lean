/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.FiberProduct.Iterated.Manifold

/-!
# Local projection normal form of iterated fibre products

Around any point `y` of the `(k + 1)`-fold fibre product `IteratedFiberProduct π (k + 1)` of a
`C^n` submersion `π : Y → M` (`1 ≤ n`), all `k + 1` coordinates `y.1 i` lie over the same base
point `x = baseProj π y ∈ M`. Given any chart `ψ` of the maximal `C^n` atlas of `M` around `x`,
this file retargets the submersion normal form of `π` at each `y.1 i` onto the common codomain
chart `ψ` and assembles the resulting simultaneous charts `φ i` of `Y` into a `C^n`
`PartialDiffeomorph` `Φ` from `Y^[k+1]` around `y` into
`EM × (Fin (k + 1) → Fin (dim Y - dim M) → ℝ)`.

In these local coordinates:
* `baseProj π` reads as the projection `(u, v) ↦ u` onto `EM`,
* each factor projection `proj π i` reads through `φ i` and the splitting `L i` as
  `(u, v) ↦ (u, v i)`, and
* on the product chart domain `∏ i, (φ i).source`, the matching condition
  `∀ i j, π (w i) = π (w j)` is equivalent to equality of the `EM`-coordinates
  `(L i ((φ i).extend IY (w i))).1`.

No Hausdorff, countability, or surjectivity assumptions are needed.

## Main results

* `TauCeti.exists_localNormalForm_iteratedFiberProduct`: local projection normal form of
  `IteratedFiberProduct π (k + 1)` over any base chart `ψ`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer (2013),
  Theorem 4.12 (submersion normal form) and Theorem 6.30 (transverse preimages).
-/

public section

open Function Set Module Filter Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {EY HY Y EM HM M : Type*}
  [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
  [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IY : ModelWithCorners ℝ EY HY} {IM : ModelWithCorners ℝ EM HM}
  [TopologicalSpace Y] [ChartedSpace HY Y]
  [TopologicalSpace M] [ChartedSpace HM M]
  {n : ℕ∞ω} [IsManifold IY n Y]
  [IY.Boundaryless] [IM.Boundaryless]

/-- Retarget a submersion normal form at `y₀` onto any prescribed chart `ψ` of the maximal atlas
around `π y₀`, keeping the same complement and linear equivalence. -/
private theorem exists_domChart_of_codChart {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {π : Y → M} {y₀ : Y} (h : Manifold.IsSubmersionAtOfComplement F IY IM n π y₀)
    {ψ : OpenPartialHomeomorph M HM} (hψ : ψ ∈ IsManifold.maximalAtlas IM n M)
    (hy₀ : π y₀ ∈ ψ.source) :
    ∃ φ : OpenPartialHomeomorph Y HY,
      φ ∈ IsManifold.maximalAtlas IY n Y ∧
      y₀ ∈ φ.source ∧
      φ.source ⊆ π ⁻¹' ψ.source ∧
      ∀ z ∈ φ.source, ψ.extend IM (π z) = (h.equiv (φ.extend IY z)).1 := by
  let φ₀ := h.domChart
  let ψ₀ := h.codChart
  let L := h.equiv
  have hIY : ∀ u : EY, IY (IY.symm u) = u := fun u ↦ IY.right_inv (by simp [IY.range_eq_univ])
  have hIY_symm : ContMDiff 𝓘(ℝ, EY) IY n IY.symm :=
    contMDiffOn_univ.1 (IY.range_eq_univ ▸ IY.contMDiffOn_symm)
  have hIM_symm : ContMDiff 𝓘(ℝ, EM) IM n IM.symm :=
    contMDiffOn_univ.1 (IM.range_eq_univ ▸ IM.contMDiffOn_symm)
  -- Transition from `ψ₀` to `ψ` in model coordinates of `M`.
  let τ₀ : OpenPartialHomeomorph HM HM := ψ₀.symm.trans ψ
  let τ : OpenPartialHomeomorph EM EM :=
    (IM.toHomeomorph.symm.transOpenPartialHomeomorph τ₀).transHomeomorph IM.toHomeomorph
  have hτ_to : ContMDiffOn 𝓘(ℝ, EM) 𝓘(ℝ, EM) n τ τ.source := by
    have h1 := (contMDiffOn_of_mem_maximalAtlas hψ).comp
      ((contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).comp
        (hIM_symm.contMDiffOn (s := τ.source)) (fun u hu ↦ hu.1))
      (fun u hu ↦ hu.2)
    exact IM.contMDiff.comp_contMDiffOn h1
  have hτ_inv : ContMDiffOn 𝓘(ℝ, EM) 𝓘(ℝ, EM) n τ.symm τ.target := by
    have h1 := (contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).comp
      ((contMDiffOn_symm_of_mem_maximalAtlas hψ).comp
        (hIM_symm.contMDiffOn (s := τ.target)) (fun u hu ↦ hu.1))
      (fun u hu ↦ hu.2)
    exact IM.contMDiff.comp_contMDiffOn h1
  -- Apply `τ` on the base factor and the identity on the fibre complement `F`.
  let g : OpenPartialHomeomorph EY EY :=
    (L.toHomeomorph.transOpenPartialHomeomorph
      (τ.prod (OpenPartialHomeomorph.refl F))).transHomeomorph L.symm.toHomeomorph
  have hg_to : ContMDiffOn 𝓘(ℝ, EY) 𝓘(ℝ, EY) n g g.source := by
    have hprod : ContMDiffOn 𝓘(ℝ, EM × F) 𝓘(ℝ, EM × F) n
        (τ.prod (OpenPartialHomeomorph.refl F)) (τ.prod (OpenPartialHomeomorph.refl F)).source :=
      (hτ_to.comp ((ContinuousLinearMap.fst ℝ EM F).contMDiff.contMDiffOn
          (s := (τ.prod (OpenPartialHomeomorph.refl F)).source))
        (fun p hp ↦ hp.1)).prodMk_space
        (ContinuousLinearMap.snd ℝ EM F).contMDiff.contMDiffOn
    exact L.symm.contDiff.contMDiff.comp_contMDiffOn
      (hprod.comp L.contDiff.contMDiff.contMDiffOn fun u hu ↦ hu)
  have hg_inv : ContMDiffOn 𝓘(ℝ, EY) 𝓘(ℝ, EY) n g.symm g.target := by
    have hprod : ContMDiffOn 𝓘(ℝ, EM × F) 𝓘(ℝ, EM × F) n
        (τ.prod (OpenPartialHomeomorph.refl F)).symm
        (τ.prod (OpenPartialHomeomorph.refl F)).target :=
      (hτ_inv.comp ((ContinuousLinearMap.fst ℝ EM F).contMDiff.contMDiffOn
          (s := (τ.prod (OpenPartialHomeomorph.refl F)).target))
        (fun p hp ↦ hp.1)).prodMk_space
        (ContinuousLinearMap.snd ℝ EM F).contMDiff.contMDiffOn
    exact L.symm.contDiff.contMDiff.comp_contMDiffOn
      (hprod.comp L.contDiff.contMDiff.contMDiffOn fun u hu ↦ hu)
  -- Precompose `φ₀` with `g` in model coordinates of `Y`.
  let φ : OpenPartialHomeomorph Y HY :=
    ((φ₀.transHomeomorph IY.toHomeomorph).trans g).transHomeomorph IY.toHomeomorph.symm
  have hφ_atlas : φ ∈ IsManifold.maximalAtlas IY n Y := by
    refine φ.mem_maximalAtlas_of_contMDiffOn ?_ ?_
    · have h1 := IY.contMDiff.comp_contMDiffOn
        (contMDiffOn_of_mem_maximalAtlas h.domChart_mem_maximalAtlas)
      exact hIY_symm.comp_contMDiffOn
        (hg_to.comp (h1.mono fun z hz ↦ hz.1) fun z hz ↦ hz.2)
    · have h1 := (contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).comp
        (hIY_symm.contMDiffOn (s := IY '' φ₀.target)) (fun u hu ↦ by
          rcases hu with ⟨w, hw, rfl⟩
          simpa [IY.left_inv] using hw)
      have h2 := hg_inv.comp (IY.contMDiff.contMDiffOn (s := φ.target))
        (fun z hz ↦ by simpa [φ, hIY] using hz.1)
      exact h1.comp h2 (fun z hz ↦
        ⟨IY.symm (g.symm (IY z)), by simpa [φ, hIY] using hz.2, hIY _⟩)
  have hy₀_φ : y₀ ∈ φ.source := by
    refine ⟨h.mem_domChart_source, ?_⟩
    have heq := h.codChart_extend_apply h.mem_domChart_source
    -- Unfold membership in `g.source` to the base component in `τ.source`.
    change (L (φ₀.extend IY y₀)).1 ∈ τ.source ∧ _
    refine ⟨?_, trivial⟩
    rw [← h.projection_apply, ← heq]
    -- Unfold membership in `τ.source` through `IM.symm` and `ψ₀.symm.trans ψ`.
    change IM.symm (IM (ψ₀ (π y₀))) ∈ ψ₀.target ∧ ψ₀.symm (IM.symm (IM (ψ₀ (π y₀)))) ∈ ψ.source
    rw [IM.left_inv]
    exact ⟨ψ₀.map_source h.mem_codChart_source, by rwa [ψ₀.left_inv h.mem_codChart_source]⟩
  have hsub : φ.source ⊆ π ⁻¹' ψ.source := by
    intro z hz
    have hz₀ : z ∈ φ₀.source := hz.1
    have hgz : (L (φ₀.extend IY z)).1 ∈ τ.source := hz.2.1
    have heq := h.codChart_extend_apply hz₀
    rw [← h.projection_apply, ← heq] at hgz
    have hmem : ψ₀.symm (IM.symm (IM (ψ₀ (π z)))) ∈ ψ.source := hgz.2
    rw [IM.left_inv, ψ₀.left_inv (h.source_subset_preimage_source hz₀)] at hmem
    exact hmem
  refine ⟨φ, hφ_atlas, hy₀_φ, hsub, fun z hz ↦ ?_⟩
  have hz₀ : z ∈ φ₀.source := hz.1
  have heq := h.codChart_extend_apply hz₀
  have hφz : φ.extend IY z = g (φ₀.extend IY z) := by
    simp [φ, OpenPartialHomeomorph.extend, hIY]
  rw [hφz]
  have hLg : (L (g (φ₀.extend IY z))).1 = τ (L (φ₀.extend IY z)).1 := by
    simp [g]
  rw [hLg, ← h.projection_apply, ← heq]
  simp [τ, τ₀, ψ₀, OpenPartialHomeomorph.extend, IM.left_inv,
    h.codChart.left_inv (h.source_subset_preimage_source hz₀)]

variable [IsManifold IM n M] [FiniteDimensional ℝ EY] [FiniteDimensional ℝ EM]

/-- **Local projection normal form of `IteratedFiberProduct π (k + 1)`.** Around any point
`y ∈ Y^[k+1]` and any chart `ψ` of `M` around `baseProj π y`, there exist simultaneous maximal
charts `φ i` of `Y` around `y.1 i`, linear splittings
`L i : EY ≃L[ℝ] EM × (Fin (dim Y - dim M) → ℝ)`, and a `C^n` partial diffeomorphism `Φ` on
`Y^[k+1]` around `y` with values in `EM × (Fin (k + 1) → Fin (dim Y - dim M) → ℝ)` such that:
* `baseProj π` reads as the projection onto `EM`,
* each factor projection `proj π i` (in chart `φ i` and splitting `L i`) reads as
  `(u, v) ↦ (u, v i)`, and
* on the product chart domain `∏ i, (φ i).source`, the matching condition
  `∀ i j, π (w i) = π (w j)` is equivalent to equality of the `EM`-coordinates
  `(L i ((φ i).extend IY (w i))).1`. -/
theorem exists_localNormalForm_iteratedFiberProduct {π : Y → M} (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) (k : ℕ)
    (y : IteratedFiberProduct π (k + 1))
    {ψ : OpenPartialHomeomorph M HM} (hψ : ψ ∈ IsManifold.maximalAtlas IM n M)
    (hy : IteratedFiberProduct.baseProj π y ∈ ψ.source) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    ∃ (φ : Fin (k + 1) → OpenPartialHomeomorph Y HY)
      (L : Fin (k + 1) → EY ≃L[ℝ] EM × (Fin (finrank ℝ EY - finrank ℝ EM) → ℝ))
      (Φ : PartialDiffeomorph
        𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
        𝓘(ℝ, EM × (Fin (k + 1) → Fin (finrank ℝ EY - finrank ℝ EM) → ℝ))
        (IteratedFiberProduct π (k + 1))
        (EM × (Fin (k + 1) → Fin (finrank ℝ EY - finrank ℝ EM) → ℝ)) n),
      (∀ i, φ i ∈ IsManifold.maximalAtlas IY n Y) ∧
      (∀ i, y.1 i ∈ (φ i).source) ∧
      (∀ i, (φ i).source ⊆ π ⁻¹' ψ.source) ∧
      y ∈ Φ.source ∧
      Φ.source = {z : IteratedFiberProduct π (k + 1) | ∀ i, z.1 i ∈ (φ i).source} ∧
      (∀ z ∈ Φ.source, ψ.extend IM (IteratedFiberProduct.baseProj π z) = (Φ z).1) ∧
      (∀ z ∈ Φ.source, ∀ i : Fin (k + 1),
        L i ((φ i).extend IY (z.1 i)) = ((Φ z).1, (Φ z).2 i)) ∧
      (∀ w : Fin (k + 1) → Y, (∀ i, w i ∈ (φ i).source) →
        ((∀ i j : Fin (k + 1), π (w i) = π (w j)) ↔
          ∀ i j : Fin (k + 1),
            (L i ((φ i).extend IY (w i))).1 = (L j ((φ j).extend IY (w j))).1)) := by
  classical
  let := iteratedFiberProductChartedSpace hn hπ k
  have := isManifold_iteratedFiberProduct hn hπ k
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  let F := Fin (finrank ℝ EY - finrank ℝ EM) → ℝ
  let Kk := 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
  have hsubm : ∀ i : Fin (k + 1), Manifold.IsSubmersionAtOfComplement F IY IM n π (y.1 i) :=
    fun i ↦ hπ.contMDiff.contMDiffOn.isSubmersionAtOfComplement_of_surjective_mfderiv
      isOpen_univ (mem_univ (y.1 i)) hn (hπ.surjective_mfderiv hn0 (y.1 i))
  have hchart : ∀ i : Fin (k + 1),
      ∃ φi : OpenPartialHomeomorph Y HY,
        φi ∈ IsManifold.maximalAtlas IY n Y ∧
        y.1 i ∈ φi.source ∧
        φi.source ⊆ π ⁻¹' ψ.source ∧
        ∀ z ∈ φi.source, ψ.extend IM (π z) = ((hsubm i).equiv (φi.extend IY z)).1 :=
    fun i ↦ exists_domChart_of_codChart (hsubm i) hψ
      (by rwa [← IteratedFiberProduct.baseProj_eq π y i])
  let φ : Fin (k + 1) → OpenPartialHomeomorph Y HY := fun i ↦ (hchart i).choose
  let L : Fin (k + 1) → EY ≃L[ℝ] EM × F := fun i ↦ (hsubm i).equiv
  have hφ_atlas : ∀ i, φ i ∈ IsManifold.maximalAtlas IY n Y := fun i ↦ (hchart i).choose_spec.1
  have hy_φ : ∀ i, y.1 i ∈ (φ i).source := fun i ↦ (hchart i).choose_spec.2.1
  have hφ_sub : ∀ i, (φ i).source ⊆ π ⁻¹' ψ.source := fun i ↦ (hchart i).choose_spec.2.2.1
  have hφ_eq : ∀ (i : Fin (k + 1)) {z : Y}, z ∈ (φ i).source →
      ψ.extend IM (π z) = (L i ((φ i).extend IY z)).1 :=
    fun i _ hz ↦ (hchart i).choose_spec.2.2.2 _ hz
  let U : Set (IteratedFiberProduct π (k + 1)) := {z | ∀ i, z.1 i ∈ (φ i).source}
  let V : Set (EM × (Fin (k + 1) → F)) :=
    {p | ∀ i, (L i).symm (p.1, p.2 i) ∈ ((φ i).extend IY).target}
  have hU_open : IsOpen U := by
    have : U = ⋂ i : Fin (k + 1), IteratedFiberProduct.proj π i ⁻¹' (φ i).source := by
      ext z
      simp [U]
    rw [this]
    exact isOpen_iInter_of_finite fun i ↦
      (φ i).open_source.preimage (IteratedFiberProduct.continuous_proj π i)
  have hV_open : IsOpen V := by
    have htarget : ∀ i, IsOpen ((φ i).extend IY).target := fun i ↦ by
      rw [OpenPartialHomeomorph.extend_target, IY.range_eq_univ, inter_univ]
      exact (φ i).open_target.preimage IY.continuous_symm
    have : V = ⋂ i : Fin (k + 1),
        (fun p : EM × (Fin (k + 1) → F) ↦ (L i).symm (p.1, p.2 i)) ⁻¹'
          ((φ i).extend IY).target := by
      ext p
      simp [V]
    rw [this]
    exact isOpen_iInter_of_finite fun i ↦
      (htarget i).preimage ((L i).symm.continuous.comp
        (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd)))
  let toFun : IteratedFiberProduct π (k + 1) → EM × (Fin (k + 1) → F) :=
    fun z ↦ (ψ.extend IM (IteratedFiberProduct.baseProj π z),
      fun i ↦ (L i ((φ i).extend IY (z.1 i))).2)
  have hinv_mem : ∀ {p : EM × (Fin (k + 1) → F)}, p ∈ V → ∀ (i : Fin (k + 1)),
      ((φ i).extend IY).symm ((L i).symm (p.1, p.2 i)) ∈ (φ i).source := fun hp i ↦ by
    have := ((φ i).extend IY).map_target (hp i)
    rwa [OpenPartialHomeomorph.extend_source] at this
  have hinv_match : ∀ {p : EM × (Fin (k + 1) → F)}, p ∈ V → ∀ (i j : Fin (k + 1)),
      π (((φ i).extend IY).symm ((L i).symm (p.1, p.2 i))) =
        π (((φ j).extend IY).symm ((L j).symm (p.1, p.2 j))) := by
    intro p hp i j
    have hi := hinv_mem hp i
    have hj := hinv_mem hp j
    refine (ψ.extend IM).injOn (by rw [OpenPartialHomeomorph.extend_source]; exact hφ_sub i hi)
      (by rw [OpenPartialHomeomorph.extend_source]; exact hφ_sub j hj) ?_
    rw [hφ_eq i hi, hφ_eq j hj, ((φ i).extend IY).right_inv (hp i),
      ((φ j).extend IY).right_inv (hp j), (L i).apply_symm_apply, (L j).apply_symm_apply]
  let invFun : EM × (Fin (k + 1) → F) → IteratedFiberProduct π (k + 1) := fun p ↦
    if hp : p ∈ V then
      ⟨fun i ↦ ((φ i).extend IY).symm ((L i).symm (p.1, p.2 i)), hinv_match hp⟩
    else y
  have htoFun_pair : ∀ {z : IteratedFiberProduct π (k + 1)}, z ∈ U → ∀ i : Fin (k + 1),
      ((toFun z).1, (toFun z).2 i) = L i ((φ i).extend IY (z.1 i)) := by
    intro z hz i
    refine Prod.ext ?_ rfl
    rw [← hφ_eq i (hz i), ← IteratedFiberProduct.baseProj_eq π z i]
  have hmap_source : ∀ z ∈ U, toFun z ∈ V := by
    intro z hz i
    rw [htoFun_pair hz i, (L i).symm_apply_apply]
    exact ((φ i).extend IY).map_source (by rw [OpenPartialHomeomorph.extend_source]; exact hz i)
  have hmap_target : ∀ p ∈ V, invFun p ∈ U := fun p hp i ↦ by
    simp only [invFun, hp, ↓reduceDIte]
    exact hinv_mem hp i
  have hleft_inv : ∀ z ∈ U, invFun (toFun z) = z := by
    intro z hz
    simp only [invFun, hmap_source z hz, ↓reduceDIte]
    apply IteratedFiberProduct.ext
    intro i
    dsimp only
    rw [htoFun_pair hz i, (L i).symm_apply_apply]
    exact ((φ i).extend IY).left_inv (by rw [OpenPartialHomeomorph.extend_source]; exact hz i)
  have hright_inv : ∀ p ∈ V, toFun (invFun p) = p := by
    intro p hp
    simp only [toFun, invFun, hp, ↓reduceDIte, IteratedFiberProduct.baseProj_eq_zero]
    refine Prod.ext ?_ (funext fun i ↦ ?_)
    · rw [hφ_eq 0 (hinv_mem hp 0), ((φ 0).extend IY).right_inv (hp 0), (L 0).apply_symm_apply]
    · dsimp only
      rw [((φ i).extend IY).right_inv (hp i), (L i).apply_symm_apply]
  have hto_smooth : ContMDiffOn Kk 𝓘(ℝ, EM × (Fin (k + 1) → F)) n toFun U := by
    have h1 : ContMDiffOn Kk 𝓘(ℝ, EM) n
        (fun z ↦ ψ.extend IM (IteratedFiberProduct.baseProj π z)) U :=
      (ψ.contMDiffOn_extend hψ).comp
        (contMDiff_baseProj_iteratedFiberProduct hn hπ k).contMDiffOn
        (fun z hz ↦ hφ_sub 0 (hz 0))
    have h2 : ContMDiffOn Kk 𝓘(ℝ, Fin (k + 1) → F) n
        (fun z i ↦ (L i ((φ i).extend IY (z.1 i))).2) U := by
      refine contMDiffOn_pi_module_iff.2 fun i ↦ ?_
      exact (ContinuousLinearMap.snd ℝ EM F).contMDiff.comp_contMDiffOn <|
        (L i).contDiff.contMDiff.comp_contMDiffOn <|
          ((φ i).contMDiffOn_extend (hφ_atlas i)).comp
            (contMDiff_proj_iteratedFiberProduct hn hπ k i).contMDiffOn
            (fun z hz ↦ hz i)
    exact h1.prodMk_space h2
  have hinv_smooth : ContMDiffOn 𝓘(ℝ, EM × (Fin (k + 1) → F)) Kk n invFun V := by
    have hinv_pi : ContMDiffOn 𝓘(ℝ, EM × (Fin (k + 1) → F))
        (ModelWithCorners.pi (fun _ : Fin (k + 1) ↦ IY)) n (Subtype.val ∘ invFun) V := by
      refine contMDiffOn_pi_iff.2 fun i ↦ ?_
      have harg : ContMDiff 𝓘(ℝ, EM × (Fin (k + 1) → F)) 𝓘(ℝ, EY) n
          (fun p : EM × (Fin (k + 1) → F) ↦ (L i).symm (p.1, p.2 i)) :=
        (L i).symm.contDiff.contMDiff.comp <|
          (ContinuousLinearMap.fst ℝ EM (Fin (k + 1) → F)).contMDiff.prodMk_space
            ((ContinuousLinearMap.proj (R := ℝ) i).contMDiff.comp
              (ContinuousLinearMap.snd ℝ EM (Fin (k + 1) → F)).contMDiff)
      have hcoord : ContMDiffOn 𝓘(ℝ, EM × (Fin (k + 1) → F)) IY n
          (fun p ↦ ((φ i).extend IY).symm ((L i).symm (p.1, p.2 i))) V :=
        (contMDiffOn_extend_symm (hφ_atlas i)).comp harg.contMDiffOn fun p hp ↦ by
          have hpi := hp i
          rw [OpenPartialHomeomorph.extend_target] at hpi
          exact ⟨IY.symm ((L i).symm (p.1, p.2 i)), hpi.1, IY.right_inv hpi.2⟩
      refine hcoord.congr fun p hp ↦ ?_
      simp [invFun, hp]
    have hinv_cont : ContinuousOn invFun V :=
      IsEmbedding.subtypeVal.continuousOn_iff.2 hinv_pi.continuousOn
    intro p hp
    have hpi_at := hinv_pi.contMDiffAt (hV_open.mem_nhds hp)
    have hcont_at := hinv_cont.continuousAt (hV_open.mem_nhds hp)
    exact ((ContMDiffAt.iff_comp_isImmersionAt
      ((isSmoothEmbedding_coe_iteratedFiberProduct hn hπ k).isImmersion.isImmersionAt
        (invFun p))).2 ⟨hcont_at, hpi_at⟩).contMDiffWithinAt
  let Φ : PartialDiffeomorph Kk 𝓘(ℝ, EM × (Fin (k + 1) → F))
      (IteratedFiberProduct π (k + 1)) (EM × (Fin (k + 1) → F)) n :=
    { toFun := toFun
      invFun := invFun
      source := U
      target := V
      map_source' := hmap_source
      map_target' := hmap_target
      left_inv' := hleft_inv
      right_inv' := hright_inv
      open_source := hU_open
      open_target := hV_open
      contMDiffOn_toFun := hto_smooth
      contMDiffOn_invFun := hinv_smooth }
  refine ⟨φ, L, Φ, hφ_atlas, hy_φ, hφ_sub, hy_φ, rfl,
    fun z _ ↦ rfl, fun z hz i ↦ (htoFun_pair hz i).symm, fun w hw ↦ ?_⟩
  constructor
  · intro h i j
    rw [← hφ_eq i (hw i), ← hφ_eq j (hw j), h i j]
  · intro h i j
    refine (ψ.extend IM).injOn (by rw [OpenPartialHomeomorph.extend_source]; exact hφ_sub i (hw i))
      (by rw [OpenPartialHomeomorph.extend_source]; exact hφ_sub j (hw j)) ?_
    rw [hφ_eq i (hw i), hφ_eq j (hw j)]
    exact h i j

end TauCeti
