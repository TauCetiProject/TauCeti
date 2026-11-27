/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Iterated.Submersion
public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Local projection normal form of iterated fibre products

Around any point `y` of the `(k + 1)`-fold fibre product `IteratedFiberProduct π (k + 1)` of a
`C^n` submersion `π : Y → M` (`1 ≤ n`), all `k + 1` coordinates `y.1 i` lie over the same base
point `x = IteratedFiberProduct.baseProj y ∈ M`. Given any chart `ψ` of the maximal `C^n` atlas of
`M` around `x`, this file retargets the submersion normal form of `π` at each `y.1 i` onto the
common codomain chart `ψ` (using `Manifold.IsSubmersionAtOfComplement.exists_domChart_of_codChart`)
and assembles the resulting simultaneous charts `φ i` of `Y` into a `C^n` `PartialDiffeomorph` `Φ`
from `Y^[k+1]` around `y` into `EM × (Fin (k + 1) → Fin (dim Y - dim M) → ℝ)`.

In these local coordinates:
* `IteratedFiberProduct.baseProj` reads as the projection `(u, v) ↦ u` onto `EM`,
* each factor projection `IteratedFiberProduct.eval i` reads through `φ i` and the splitting `L i`
  as `(u, v) ↦ (u, v i)`, and
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

section LocalNormalForm

variable {EY HY Y EM HM M : Type*}
  [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
  [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IY : ModelWithCorners ℝ EY HY} {IM : ModelWithCorners ℝ EM HM}
  [TopologicalSpace Y] [ChartedSpace HY Y]
  [TopologicalSpace M] [ChartedSpace HM M]
  {n : ℕ∞ω} [IsManifold IY n Y] [IsManifold IM n M]
  [IY.Boundaryless] [IM.Boundaryless]
  [FiniteDimensional ℝ EY] [FiniteDimensional ℝ EM]

omit [ChartedSpace HY Y] [TopologicalSpace M] in
private theorem isOpen_localNormalFormSource {π : Y → M} (k : ℕ)
    (φ : Fin (k + 1) → OpenPartialHomeomorph Y HY) :
    IsOpen {z : IteratedFiberProduct π (k + 1) | ∀ i, z.val i ∈ (φ i).source} := by
  have hEq : {z : IteratedFiberProduct π (k + 1) | ∀ i, z.val i ∈ (φ i).source} =
      ⋂ i : Fin (k + 1), IteratedFiberProduct.eval i ⁻¹' (φ i).source := by
    ext; simp [IteratedFiberProduct.eval_apply]
  rw [hEq]
  exact isOpen_iInter_of_finite fun i ↦
    (φ i).open_source.preimage (IteratedFiberProduct.continuous_eval i)

omit [ChartedSpace HY Y] [FiniteDimensional ℝ EY] [FiniteDimensional ℝ EM] in
private theorem isOpen_localNormalFormTarget (k : ℕ)
    (φ : Fin (k + 1) → OpenPartialHomeomorph Y HY)
    (L : Fin (k + 1) → EY ≃L[ℝ] EM × (Fin (finrank ℝ EY - finrank ℝ EM) → ℝ)) :
    IsOpen {p : EM × (Fin (k + 1) → Fin (finrank ℝ EY - finrank ℝ EM) → ℝ) |
      ∀ i, (L i).symm (p.1, p.2 i) ∈ ((φ i).extend IY).target} := by
  let F := Fin (finrank ℝ EY - finrank ℝ EM) → ℝ
  have hEq : {p : EM × (Fin (k + 1) → F) |
        ∀ i, (L i).symm (p.1, p.2 i) ∈ ((φ i).extend IY).target} =
      ⋂ i : Fin (k + 1),
        (fun p : EM × (Fin (k + 1) → F) ↦ (L i).symm (p.1, p.2 i)) ⁻¹'
          ((φ i).extend IY).target := by
    ext; simp
  rw [hEq]
  refine isOpen_iInter_of_finite fun i ↦
    (φ i).isOpen_extend_target.preimage ((L i).symm.continuous.comp
      (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd)))

private theorem contMDiffOn_localNormalForm_toFun {π : Y → M} (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) (k : ℕ)
    (φ : Fin (k + 1) → OpenPartialHomeomorph Y HY)
    (hφ_atlas : ∀ i, φ i ∈ IsManifold.maximalAtlas IY n Y)
    (L : Fin (k + 1) → EY ≃L[ℝ] EM × (Fin (finrank ℝ EY - finrank ℝ EM) → ℝ))
    {ψ : OpenPartialHomeomorph M HM} (hψ : ψ ∈ IsManifold.maximalAtlas IM n M)
    (hφ_sub : ∀ i, (φ i).source ⊆ π ⁻¹' ψ.source) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    ContMDiffOn
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
      𝓘(ℝ, EM × (Fin (k + 1) → Fin (finrank ℝ EY - finrank ℝ EM) → ℝ)) n
      (fun z : IteratedFiberProduct π (k + 1) ↦
        (ψ.extend IM (IteratedFiberProduct.baseProj z),
          fun i ↦ (L i ((φ i).extend IY (z.val i))).2))
      {z : IteratedFiberProduct π (k + 1) | ∀ i, z.val i ∈ (φ i).source} := by
  let := iteratedFiberProductChartedSpace hn hπ k
  let F := Fin (finrank ℝ EY - finrank ℝ EM) → ℝ
  have hbase : ContMDiffOn
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
      𝓘(ℝ, EM) n (fun z ↦ ψ.extend IM (IteratedFiberProduct.baseProj z))
      {z : IteratedFiberProduct π (k + 1) | ∀ i, z.val i ∈ (φ i).source} :=
    (ψ.contMDiffOn_extend hψ).comp (contMDiff_baseProj hn hπ le_rfl).contMDiffOn
      fun z hz ↦ by
        simpa only [mem_preimage, IteratedFiberProduct.baseProj_eq_apply z 0] using hφ_sub 0 (hz 0)
  have hfib : ContMDiffOn
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin (k + 1) → F) n
      (fun z i ↦ (L i ((φ i).extend IY (z.val i))).2)
      {z : IteratedFiberProduct π (k + 1) | ∀ i, z.val i ∈ (φ i).source} :=
    contMDiffOn_pi_module_iff.2 fun i ↦
      (ContinuousLinearMap.snd ℝ EM F).contMDiff.comp_contMDiffOn <|
        (L i).contDiff.contMDiff.comp_contMDiffOn <|
          ((φ i).contMDiffOn_extend (hφ_atlas i)).comp
            ((contMDiff_eval hn hπ le_rfl i).congr
              fun z ↦ (IteratedFiberProduct.eval_apply i z).symm).contMDiffOn
            fun z hz ↦ hz i
  exact hbase.prodMk_space hfib

private theorem contMDiffOn_localNormalForm_invFun {π : Y → M} (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) (k : ℕ)
    (φ : Fin (k + 1) → OpenPartialHomeomorph Y HY)
    (hφ_atlas : ∀ i, φ i ∈ IsManifold.maximalAtlas IY n Y)
    (L : Fin (k + 1) → EY ≃L[ℝ] EM × (Fin (finrank ℝ EY - finrank ℝ EM) → ℝ))
    (invFun : EM × (Fin (k + 1) → Fin (finrank ℝ EY - finrank ℝ EM) → ℝ) →
      IteratedFiberProduct π (k + 1))
    (hinv_eq : ∀ p ∈ {p : EM × (Fin (k + 1) → Fin (finrank ℝ EY - finrank ℝ EM) → ℝ) |
        ∀ i, (L i).symm (p.1, p.2 i) ∈ ((φ i).extend IY).target},
      ∀ i, (invFun p).val i = ((φ i).extend IY).symm ((L i).symm (p.1, p.2 i))) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    ContMDiffOn
      𝓘(ℝ, EM × (Fin (k + 1) → Fin (finrank ℝ EY - finrank ℝ EM) → ℝ))
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) n invFun
      {p | ∀ i, (L i).symm (p.1, p.2 i) ∈ ((φ i).extend IY).target} := by
  let := iteratedFiberProductChartedSpace hn hπ k
  let F := Fin (finrank ℝ EY - finrank ℝ EM) → ℝ
  have hinv_pi : ContMDiffOn 𝓘(ℝ, EM × (Fin (k + 1) → F))
      (ModelWithCorners.pi (fun _ : Fin (k + 1) ↦ IY)) n (Subtype.val ∘ invFun)
      {p | ∀ i, (L i).symm (p.1, p.2 i) ∈ ((φ i).extend IY).target} :=
    contMDiffOn_pi_iff.2 fun i ↦ by
      have harg : ContMDiff 𝓘(ℝ, EM × (Fin (k + 1) → F)) 𝓘(ℝ, EY) n
          (fun p : EM × (Fin (k + 1) → F) ↦ (L i).symm (p.1, p.2 i)) :=
        (L i).symm.contDiff.contMDiff.comp <|
          (ContinuousLinearMap.fst ℝ EM (Fin (k + 1) → F)).contMDiff.prodMk_space
            ((ContinuousLinearMap.proj (R := ℝ) i).contMDiff.comp
              (ContinuousLinearMap.snd ℝ EM (Fin (k + 1) → F)).contMDiff)
      exact ((contMDiffOn_extend_symm (hφ_atlas i)).comp harg.contMDiffOn fun p hp ↦ by
        have hpi := hp i
        rw [OpenPartialHomeomorph.extend_target] at hpi
        exact ⟨IY.symm ((L i).symm (p.1, p.2 i)), hpi.1, IY.right_inv hpi.2⟩).congr
        fun p hp ↦ hinv_eq p hp i
  exact (isSmoothEmbedding_coe_iteratedFiberProduct hn hπ k).contMDiffOn_iff_comp.2 hinv_pi

omit [ChartedSpace HY Y] [ChartedSpace HM M]
  [IsManifold IY n Y] [IsManifold IM n M] [IY.Boundaryless] [IM.Boundaryless]
  [FiniteDimensional ℝ EY] [FiniteDimensional ℝ EM] in
private theorem localNormalForm_pair_eq {π : Y → M} {k : ℕ}
    {ψ : OpenPartialHomeomorph M HM}
    {φ : Fin (k + 1) → OpenPartialHomeomorph Y HY}
    {L : Fin (k + 1) → EY ≃L[ℝ] EM × (Fin (finrank ℝ EY - finrank ℝ EM) → ℝ)}
    (hφ_eq : ∀ (i : Fin (k + 1)) {z : Y}, z ∈ (φ i).source →
      ψ.extend IM (π z) = (L i ((φ i).extend IY z)).1)
    {z : IteratedFiberProduct π (k + 1)} (hz : ∀ i, z.val i ∈ (φ i).source)
    (i : Fin (k + 1)) :
    L i ((φ i).extend IY (z.val i)) =
      (ψ.extend IM (IteratedFiberProduct.baseProj z), (L i ((φ i).extend IY (z.val i))).2) :=
  Prod.ext (by rw [← hφ_eq i (hz i), ← IteratedFiberProduct.baseProj_eq_apply z i]) rfl

open Classical in
/-- Assemble the simultaneous submersion charts `φ i` and linear splittings `L i` over a base
chart `ψ` into a `C^n` `PartialDiffeomorph` around `y ∈ Y^[k + 1]`. -/
private noncomputable def localNormalFormPartialDiffeomorph {π : Y → M} (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) (k : ℕ) (y : IteratedFiberProduct π (k + 1))
    {ψ : OpenPartialHomeomorph M HM} (hψ : ψ ∈ IsManifold.maximalAtlas IM n M)
    (φ : Fin (k + 1) → OpenPartialHomeomorph Y HY)
    (hφ_atlas : ∀ i, φ i ∈ IsManifold.maximalAtlas IY n Y)
    (hφ_sub : ∀ i, (φ i).source ⊆ π ⁻¹' ψ.source)
    (L : Fin (k + 1) → EY ≃L[ℝ] EM × (Fin (finrank ℝ EY - finrank ℝ EM) → ℝ))
    (hφ_eq : ∀ (i : Fin (k + 1)) {z : Y}, z ∈ (φ i).source →
      ψ.extend IM (π z) = (L i ((φ i).extend IY z)).1) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    PartialDiffeomorph
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
      𝓘(ℝ, EM × (Fin (k + 1) → Fin (finrank ℝ EY - finrank ℝ EM) → ℝ))
      (IteratedFiberProduct π (k + 1))
      (EM × (Fin (k + 1) → Fin (finrank ℝ EY - finrank ℝ EM) → ℝ)) n :=
  letI := iteratedFiberProductChartedSpace hn hπ k
  let F := Fin (finrank ℝ EY - finrank ℝ EM) → ℝ
  let U : Set (IteratedFiberProduct π (k + 1)) := {z | ∀ i, z.val i ∈ (φ i).source}
  let V : Set (EM × (Fin (k + 1) → F)) :=
    {p | ∀ i, (L i).symm (p.1, p.2 i) ∈ ((φ i).extend IY).target}
  let toFun : IteratedFiberProduct π (k + 1) → EM × (Fin (k + 1) → F) := fun z ↦
    (ψ.extend IM (IteratedFiberProduct.baseProj z), fun i ↦ (L i ((φ i).extend IY (z.val i))).2)
  let hinv_mem : ∀ {p : EM × (Fin (k + 1) → F)}, p ∈ V → ∀ (i : Fin (k + 1)),
      ((φ i).extend IY).symm ((L i).symm (p.1, p.2 i)) ∈ (φ i).source := fun hp i ↦ by
    simpa only [OpenPartialHomeomorph.extend_source] using ((φ i).extend IY).map_target (hp i)
  let hinv_match : ∀ {p : EM × (Fin (k + 1) → F)}, p ∈ V → ∀ (i j : Fin (k + 1)),
      π (((φ i).extend IY).symm ((L i).symm (p.1, p.2 i))) =
        π (((φ j).extend IY).symm ((L j).symm (p.1, p.2 j))) := fun hp ↦
    (forall_apply_eq_iff_fst_extend_eq (L := fun i ↦ (L i)) hφ_sub hφ_eq (hinv_mem hp)).2
      fun i j ↦ by
        rw [((φ i).extend IY).right_inv (hp i), ((φ j).extend IY).right_inv (hp j),
          (L i).apply_symm_apply, (L j).apply_symm_apply]
  let invFun : EM × (Fin (k + 1) → F) → IteratedFiberProduct π (k + 1) := fun p ↦
    if hp : p ∈ V then
      ⟨fun i ↦ ((φ i).extend IY).symm ((L i).symm (p.1, p.2 i)), hinv_match hp⟩
    else y
  let htoFun_pair : ∀ {z : IteratedFiberProduct π (k + 1)}, z ∈ U → ∀ i : Fin (k + 1),
      ((toFun z).1, (toFun z).2 i) = L i ((φ i).extend IY (z.val i)) := fun hz i ↦
    (localNormalForm_pair_eq hφ_eq hz i).symm
  let hmap_source : ∀ z ∈ U, toFun z ∈ V := fun z hz i ↦ by
    rw [htoFun_pair hz i, (L i).symm_apply_apply]
    exact ((φ i).extend IY).map_source (by rw [OpenPartialHomeomorph.extend_source]; exact hz i)
  { toFun := toFun
    invFun := invFun
    source := U
    target := V
    map_source' := hmap_source
    map_target' := fun p hp i ↦ by simp only [invFun, hp, ↓reduceDIte]; exact hinv_mem hp i
    left_inv' := fun z hz ↦ IteratedFiberProduct.ext fun i ↦ by
      simp only [invFun, hmap_source z hz, ↓reduceDIte, IteratedFiberProduct.eval_apply]
      rw [htoFun_pair hz i, (L i).symm_apply_apply]
      exact ((φ i).extend IY).left_inv (by rw [OpenPartialHomeomorph.extend_source]; exact hz i)
    right_inv' := fun p hp ↦ by
      simp only [toFun, invFun, hp, ↓reduceDIte, IteratedFiberProduct.baseProj_eq_apply _ 0]
      refine Prod.ext ?_ (funext fun i ↦ ?_)
      · rw [hφ_eq 0 (hinv_mem hp 0), ((φ 0).extend IY).right_inv (hp 0), (L 0).apply_symm_apply]
      · dsimp only; rw [((φ i).extend IY).right_inv (hp i), (L i).apply_symm_apply]
    open_source := isOpen_localNormalFormSource k φ
    open_target := isOpen_localNormalFormTarget k φ L
    contMDiffOn_toFun :=
      contMDiffOn_localNormalForm_toFun hn hπ k φ hφ_atlas L hψ hφ_sub
    contMDiffOn_invFun :=
      contMDiffOn_localNormalForm_invFun hn hπ k φ hφ_atlas L invFun fun p hp i ↦ by
        have hpV : p ∈ V := hp
        simp only [invFun, hpV, ↓reduceDIte] }

-- Unfolds the term definition of `localNormalFormPartialDiffeomorph` to its `source` field.
private theorem localNormalFormPartialDiffeomorph_source {π : Y → M} (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) (k : ℕ) (y : IteratedFiberProduct π (k + 1))
    {ψ : OpenPartialHomeomorph M HM} (hψ : ψ ∈ IsManifold.maximalAtlas IM n M)
    (φ : Fin (k + 1) → OpenPartialHomeomorph Y HY)
    (hφ_atlas : ∀ i, φ i ∈ IsManifold.maximalAtlas IY n Y)
    (hφ_sub : ∀ i, (φ i).source ⊆ π ⁻¹' ψ.source)
    (L : Fin (k + 1) → EY ≃L[ℝ] EM × (Fin (finrank ℝ EY - finrank ℝ EM) → ℝ))
    (hφ_eq : ∀ (i : Fin (k + 1)) {z : Y}, z ∈ (φ i).source →
      ψ.extend IM (π z) = (L i ((φ i).extend IY z)).1) :
    (localNormalFormPartialDiffeomorph hn hπ k y hψ φ hφ_atlas hφ_sub L hφ_eq).source =
      {z : IteratedFiberProduct π (k + 1) | ∀ i, z.val i ∈ (φ i).source} := rfl

-- Unfolds the term definition of `localNormalFormPartialDiffeomorph` to its first coordinate.
private theorem localNormalFormPartialDiffeomorph_apply_fst {π : Y → M} (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) (k : ℕ) (y : IteratedFiberProduct π (k + 1))
    {ψ : OpenPartialHomeomorph M HM} (hψ : ψ ∈ IsManifold.maximalAtlas IM n M)
    (φ : Fin (k + 1) → OpenPartialHomeomorph Y HY)
    (hφ_atlas : ∀ i, φ i ∈ IsManifold.maximalAtlas IY n Y)
    (hφ_sub : ∀ i, (φ i).source ⊆ π ⁻¹' ψ.source)
    (L : Fin (k + 1) → EY ≃L[ℝ] EM × (Fin (finrank ℝ EY - finrank ℝ EM) → ℝ))
    (hφ_eq : ∀ (i : Fin (k + 1)) {z : Y}, z ∈ (φ i).source →
      ψ.extend IM (π z) = (L i ((φ i).extend IY z)).1)
    (z : IteratedFiberProduct π (k + 1)) :
    (localNormalFormPartialDiffeomorph hn hπ k y hψ φ hφ_atlas hφ_sub L hφ_eq z).1 =
      ψ.extend IM (IteratedFiberProduct.baseProj z) := rfl

-- Unfolds the term definition of `localNormalFormPartialDiffeomorph` to its fibre coordinate.
private theorem localNormalFormPartialDiffeomorph_apply_snd {π : Y → M} (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) (k : ℕ) (y : IteratedFiberProduct π (k + 1))
    {ψ : OpenPartialHomeomorph M HM} (hψ : ψ ∈ IsManifold.maximalAtlas IM n M)
    (φ : Fin (k + 1) → OpenPartialHomeomorph Y HY)
    (hφ_atlas : ∀ i, φ i ∈ IsManifold.maximalAtlas IY n Y)
    (hφ_sub : ∀ i, (φ i).source ⊆ π ⁻¹' ψ.source)
    (L : Fin (k + 1) → EY ≃L[ℝ] EM × (Fin (finrank ℝ EY - finrank ℝ EM) → ℝ))
    (hφ_eq : ∀ (i : Fin (k + 1)) {z : Y}, z ∈ (φ i).source →
      ψ.extend IM (π z) = (L i ((φ i).extend IY z)).1)
    (z : IteratedFiberProduct π (k + 1)) (i : Fin (k + 1)) :
    (localNormalFormPartialDiffeomorph hn hπ k y hψ φ hφ_atlas hφ_sub L hφ_eq z).2 i =
      (L i ((φ i).extend IY (z.val i))).2 := rfl

/-- **Local projection normal form of `IteratedFiberProduct π (k + 1)`.** Around any point
`y ∈ Y^[k+1]` and any chart `ψ` of `M` around `IteratedFiberProduct.baseProj y`, there exist
simultaneous maximal charts `φ i` of `Y` around `y.val i`, linear splittings
`L i : EY ≃L[ℝ] EM × (Fin (dim Y - dim M) → ℝ)`, and a `C^n` partial diffeomorphism `Φ` on
`Y^[k+1]` around `y` with values in `EM × (Fin (k + 1) → Fin (dim Y - dim M) → ℝ)` such that:
* `IteratedFiberProduct.baseProj` reads as the projection onto `EM`,
* each factor projection `IteratedFiberProduct.eval i` (in chart `φ i` and splitting `L i`) reads
  as `(u, v) ↦ (u, v i)`, and
* on the product chart domain `∏ i, (φ i).source`, the matching condition
  `∀ i j, π (w i) = π (w j)` is equivalent to equality of the `EM`-coordinates
  `(L i ((φ i).extend IY (w i))).1`. -/
theorem exists_localNormalForm_iteratedFiberProduct {π : Y → M} (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) (k : ℕ)
    (y : IteratedFiberProduct π (k + 1))
    {ψ : OpenPartialHomeomorph M HM} (hψ : ψ ∈ IsManifold.maximalAtlas IM n M)
    (hy : IteratedFiberProduct.baseProj y ∈ ψ.source) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    ∃ (φ : Fin (k + 1) → OpenPartialHomeomorph Y HY)
      (L : Fin (k + 1) → EY ≃L[ℝ] EM × (Fin (finrank ℝ EY - finrank ℝ EM) → ℝ))
      (Φ : PartialDiffeomorph
        𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
        𝓘(ℝ, EM × (Fin (k + 1) → Fin (finrank ℝ EY - finrank ℝ EM) → ℝ))
        (IteratedFiberProduct π (k + 1))
        (EM × (Fin (k + 1) → Fin (finrank ℝ EY - finrank ℝ EM) → ℝ)) n),
      (∀ i, φ i ∈ IsManifold.maximalAtlas IY n Y) ∧
      (∀ i, y.val i ∈ (φ i).source) ∧
      (∀ i, (φ i).source ⊆ π ⁻¹' ψ.source) ∧
      y ∈ Φ.source ∧
      Φ.source = {z : IteratedFiberProduct π (k + 1) | ∀ i, z.val i ∈ (φ i).source} ∧
      (∀ z ∈ Φ.source, ψ.extend IM (IteratedFiberProduct.baseProj z) = (Φ z).1) ∧
      (∀ z ∈ Φ.source, ∀ i : Fin (k + 1),
        L i ((φ i).extend IY (z.val i)) = ((Φ z).1, (Φ z).2 i)) ∧
      (∀ w : Fin (k + 1) → Y, (∀ i, w i ∈ (φ i).source) →
        ((∀ i j : Fin (k + 1), π (w i) = π (w j)) ↔
          ∀ i j : Fin (k + 1),
            (L i ((φ i).extend IY (w i))).1 = (L j ((φ j).extend IY (w j))).1)) := by
  classical
  let := iteratedFiberProductChartedSpace hn hπ k
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  let F := Fin (finrank ℝ EY - finrank ℝ EM) → ℝ
  have hsubm : ∀ i : Fin (k + 1), Manifold.IsSubmersionAtOfComplement F IY IM n π (y.val i) :=
    fun i ↦ hπ.contMDiff.contMDiffOn.isSubmersionAtOfComplement_of_surjective_mfderiv
      isOpen_univ (mem_univ (y.val i)) hn (hπ.surjective_mfderiv hn0 (y.val i))
  have hchart : ∀ i : Fin (k + 1),
      ∃ φi : OpenPartialHomeomorph Y HY,
        φi ∈ IsManifold.maximalAtlas IY n Y ∧
        y.val i ∈ φi.source ∧
        φi.source ⊆ π ⁻¹' ψ.source ∧
        ∀ z ∈ φi.source, ψ.extend IM (π z) = ((hsubm i).equiv (φi.extend IY z)).1 :=
    fun i ↦ (hsubm i).exists_domChart_of_codChart hψ
      (by rwa [← IteratedFiberProduct.baseProj_eq_apply y i])
  let φ : Fin (k + 1) → OpenPartialHomeomorph Y HY := fun i ↦ (hchart i).choose
  let L : Fin (k + 1) → EY ≃L[ℝ] EM × F := fun i ↦ (hsubm i).equiv
  have hφ_atlas : ∀ i, φ i ∈ IsManifold.maximalAtlas IY n Y := fun i ↦ (hchart i).choose_spec.1
  have hy_φ : ∀ i, y.val i ∈ (φ i).source := fun i ↦ (hchart i).choose_spec.2.1
  have hφ_sub : ∀ i, (φ i).source ⊆ π ⁻¹' ψ.source := fun i ↦ (hchart i).choose_spec.2.2.1
  have hφ_eq : ∀ (i : Fin (k + 1)) {z : Y}, z ∈ (φ i).source →
      ψ.extend IM (π z) = (L i ((φ i).extend IY z)).1 :=
    fun i _ hz ↦ (hchart i).choose_spec.2.2.2 _ hz
  let Φ := localNormalFormPartialDiffeomorph hn hπ k y hψ φ hφ_atlas hφ_sub L hφ_eq
  have hΦ_src : Φ.source = {z : IteratedFiberProduct π (k + 1) | ∀ i, z.val i ∈ (φ i).source} :=
    localNormalFormPartialDiffeomorph_source hn hπ k y hψ φ hφ_atlas hφ_sub L hφ_eq
  have hΦ_fst : ∀ z, (Φ z).1 = ψ.extend IM (IteratedFiberProduct.baseProj z) :=
    localNormalFormPartialDiffeomorph_apply_fst hn hπ k y hψ φ hφ_atlas hφ_sub L hφ_eq
  have hΦ_snd : ∀ z i, (Φ z).2 i = (L i ((φ i).extend IY (z.val i))).2 :=
    localNormalFormPartialDiffeomorph_apply_snd hn hπ k y hψ φ hφ_atlas hφ_sub L hφ_eq
  refine ⟨φ, L, Φ, hφ_atlas, hy_φ, hφ_sub, ?_, hΦ_src, fun z _ ↦ (hΦ_fst z).symm, ?_, ?_⟩
  · rw [hΦ_src]
    exact hy_φ
  · intro z hz i
    rw [hΦ_src] at hz
    rw [hΦ_fst z, hΦ_snd z i]
    exact localNormalForm_pair_eq hφ_eq hz i
  · exact fun w hw ↦ forall_apply_eq_iff_fst_extend_eq (L := fun i ↦ (L i)) hφ_sub hφ_eq hw

end LocalNormalForm

end TauCeti
