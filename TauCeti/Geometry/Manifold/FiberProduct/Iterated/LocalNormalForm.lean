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
    fun i ↦ (hsubm i).exists_domChart_of_codChart hψ
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
  have hU_open : IsOpen U :=
    (show U = ⋂ i : Fin (k + 1), IteratedFiberProduct.proj π i ⁻¹' (φ i).source by ext; simp [U]) ▸
      isOpen_iInter_of_finite fun i ↦
        (φ i).open_source.preimage (IteratedFiberProduct.continuous_proj π i)
  have hV_open : IsOpen V :=
    (show V = ⋂ i : Fin (k + 1),
        (fun p : EM × (Fin (k + 1) → F) ↦ (L i).symm (p.1, p.2 i)) ⁻¹'
          ((φ i).extend IY).target by ext; simp [V]) ▸
      isOpen_iInter_of_finite fun i ↦ by
        have ht : IsOpen ((φ i).extend IY).target := by
          rw [OpenPartialHomeomorph.extend_target, IY.range_eq_univ, inter_univ]
          exact (φ i).open_target.preimage IY.continuous_symm
        exact ht.preimage ((L i).symm.continuous.comp
          (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd)))
  let toFun : IteratedFiberProduct π (k + 1) → EM × (Fin (k + 1) → F) :=
    fun z ↦ (ψ.extend IM (IteratedFiberProduct.baseProj π z),
      fun i ↦ (L i ((φ i).extend IY (z.1 i))).2)
  have hinv_mem : ∀ {p : EM × (Fin (k + 1) → F)}, p ∈ V → ∀ (i : Fin (k + 1)),
      ((φ i).extend IY).symm ((L i).symm (p.1, p.2 i)) ∈ (φ i).source := fun hp i ↦ by
    simpa only [OpenPartialHomeomorph.extend_source] using ((φ i).extend IY).map_target (hp i)
  have hinv_match : ∀ {p : EM × (Fin (k + 1) → F)}, p ∈ V → ∀ (i j : Fin (k + 1)),
      π (((φ i).extend IY).symm ((L i).symm (p.1, p.2 i))) =
        π (((φ j).extend IY).symm ((L j).symm (p.1, p.2 j))) := fun hp i j ↦
    (ψ.extend IM).injOn
      (by rw [OpenPartialHomeomorph.extend_source]; exact hφ_sub i (hinv_mem hp i))
      (by rw [OpenPartialHomeomorph.extend_source]; exact hφ_sub j (hinv_mem hp j)) <| by
      rw [hφ_eq i (hinv_mem hp i), hφ_eq j (hinv_mem hp j), ((φ i).extend IY).right_inv (hp i),
        ((φ j).extend IY).right_inv (hp j), (L i).apply_symm_apply, (L j).apply_symm_apply]
  let invFun : EM × (Fin (k + 1) → F) → IteratedFiberProduct π (k + 1) := fun p ↦
    if hp : p ∈ V then
      ⟨fun i ↦ ((φ i).extend IY).symm ((L i).symm (p.1, p.2 i)), hinv_match hp⟩
    else y
  have htoFun_pair : ∀ {z : IteratedFiberProduct π (k + 1)}, z ∈ U → ∀ i : Fin (k + 1),
      ((toFun z).1, (toFun z).2 i) = L i ((φ i).extend IY (z.1 i)) := fun {z} hz i ↦
    Prod.ext (by rw [← hφ_eq i (hz i), ← IteratedFiberProduct.baseProj_eq π z i]) rfl
  have hmap_source : ∀ z ∈ U, toFun z ∈ V := fun z hz i ↦ by
    rw [htoFun_pair hz i, (L i).symm_apply_apply]
    exact ((φ i).extend IY).map_source (by rw [OpenPartialHomeomorph.extend_source]; exact hz i)
  have hleft_inv : ∀ z ∈ U, invFun (toFun z) = z := fun z hz ↦ by
    simp only [invFun, hmap_source z hz, ↓reduceDIte]
    refine IteratedFiberProduct.ext π fun i ↦ ?_
    dsimp only
    rw [htoFun_pair hz i, (L i).symm_apply_apply]
    exact ((φ i).extend IY).left_inv (by rw [OpenPartialHomeomorph.extend_source]; exact hz i)
  have hright_inv : ∀ p ∈ V, toFun (invFun p) = p := fun p hp ↦ by
    simp only [toFun, invFun, hp, ↓reduceDIte, IteratedFiberProduct.baseProj_eq_zero]
    refine Prod.ext ?_ (funext fun i ↦ ?_)
    · rw [hφ_eq 0 (hinv_mem hp 0), ((φ 0).extend IY).right_inv (hp 0), (L 0).apply_symm_apply]
    · dsimp only; rw [((φ i).extend IY).right_inv (hp i), (L i).apply_symm_apply]
  have hto_smooth : ContMDiffOn Kk 𝓘(ℝ, EM × (Fin (k + 1) → F)) n toFun U :=
    ((ψ.contMDiffOn_extend hψ).comp (contMDiff_baseProj_iteratedFiberProduct hn hπ k).contMDiffOn
      fun z hz ↦ by
        simpa only [mem_preimage, IteratedFiberProduct.baseProj_eq_zero] using
          hφ_sub 0 (hz 0)).prodMk_space <|
      contMDiffOn_pi_module_iff.2 fun i ↦
        (ContinuousLinearMap.snd ℝ EM F).contMDiff.comp_contMDiffOn <|
          (L i).contDiff.contMDiff.comp_contMDiffOn <|
            ((φ i).contMDiffOn_extend (hφ_atlas i)).comp
              (by
                have h := (contMDiff_proj_iteratedFiberProduct hn hπ k i).contMDiffOn (s := U)
                rw [IteratedFiberProduct.proj_eq_comp] at h; exact h)
              fun z hz ↦ hz i
  have hinv_smooth : ContMDiffOn 𝓘(ℝ, EM × (Fin (k + 1) → F)) Kk n invFun V := by
    have hinv_pi : ContMDiffOn 𝓘(ℝ, EM × (Fin (k + 1) → F))
        (ModelWithCorners.pi (fun _ : Fin (k + 1) ↦ IY)) n (Subtype.val ∘ invFun) V :=
      contMDiffOn_pi_iff.2 fun i ↦ by
        have harg : ContMDiff 𝓘(ℝ, EM × (Fin (k + 1) → F)) 𝓘(ℝ, EY) n
            (fun p : EM × (Fin (k + 1) → F) ↦ (L i).symm (p.1, p.2 i)) :=
          (L i).symm.contDiff.contMDiff.comp <|
            (ContinuousLinearMap.fst ℝ EM (Fin (k + 1) → F)).contMDiff.prodMk_space
              ((ContinuousLinearMap.proj (R := ℝ) i).contMDiff.comp
                (ContinuousLinearMap.snd ℝ EM (Fin (k + 1) → F)).contMDiff)
        exact ((contMDiffOn_extend_symm (hφ_atlas i)).comp harg.contMDiffOn fun p hp ↦ by
          have hpi := hp i; rw [OpenPartialHomeomorph.extend_target] at hpi
          exact ⟨IY.symm ((L i).symm (p.1, p.2 i)), hpi.1, IY.right_inv hpi.2⟩).congr
          fun p hp ↦ by simp [invFun, hp]
    intro p hp
    exact ((ContMDiffAt.iff_comp_isImmersionAt
      ((isSmoothEmbedding_coe_iteratedFiberProduct hn hπ k).isImmersion.isImmersionAt
        (invFun p))).2
      ⟨(IsEmbedding.subtypeVal.continuousOn_iff.2 hinv_pi.continuousOn).continuousAt
          (hV_open.mem_nhds hp),
        hinv_pi.contMDiffAt (hV_open.mem_nhds hp)⟩).contMDiffWithinAt
  refine ⟨φ, L,
    { toFun := toFun, invFun := invFun, source := U, target := V, map_source' := hmap_source,
      map_target' := fun p hp i ↦ by simp only [invFun, hp, ↓reduceDIte]; exact hinv_mem hp i,
      left_inv' := hleft_inv, right_inv' := hright_inv, open_source := hU_open,
      open_target := hV_open, contMDiffOn_toFun := hto_smooth, contMDiffOn_invFun := hinv_smooth },
    hφ_atlas, hy_φ, hφ_sub, hy_φ, rfl, fun z _ ↦ rfl, fun z hz i ↦ (htoFun_pair hz i).symm,
    fun w hw ↦ ⟨fun h i j ↦ by rw [← hφ_eq i (hw i), ← hφ_eq j (hw j), h i j], fun h i j ↦
      (ψ.extend IM).injOn (by rw [OpenPartialHomeomorph.extend_source]; exact hφ_sub i (hw i))
        (by rw [OpenPartialHomeomorph.extend_source]; exact hφ_sub j (hw j))
        (by rw [hφ_eq i (hw i), hφ_eq j (hw j)]; exact h i j)⟩⟩

end TauCeti
