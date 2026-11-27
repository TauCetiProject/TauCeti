/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Identity
public import TauCeti.Geometry.Manifold.FiberProduct.Iterated.Basic
public import TauCeti.Geometry.Manifold.FiberProduct.Submersion
public import TauCeti.Geometry.Manifold.IsManifold.Pi
import TauCeti.Geometry.Manifold.Diffeomorph.Pi
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.Immersion.Diffeomorph
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Pi
import TauCeti.Geometry.Manifold.PullbackGroupoid
import TauCeti.Geometry.Manifold.SmoothEmbedding.LeftInverse

/-!
# Iterated fibre products of submersions

For a `C^n` submersion `π : Y → M` (`1 ≤ n`) between finite-dimensional boundaryless real
manifolds, the `k`-fold fibre product `Y^[k]` (`k = m + 1 ≥ 1`) is the subtype
`TauCeti.IteratedFiberProduct π k = {y : Fin k → Y // ∀ i j, π (y i) = π (y j)}` equipped with
its subspace topology in `Fin k → Y`.

`TauCeti.iteratedFiberProductChartedSpace` constructs a `C^n` manifold structure on
`IteratedFiberProduct π (m + 1)` of dimension `(m + 1) * dim Y - m * dim M` by iterating the
binary transverse fibre-product atlas `TauCeti.transverseFiberProductChartedSpace`: the base case
`k = 1` pulls back the identity base change `{p : M × Y // id p.1 = π p.2}`, and the step from
`k` to `k + 1` forms the transverse fibre product of `IteratedFiberProduct.baseProj` with `π`.
Because `π` is a submersion, transversality holds unconditionally at every step, even when `Y` or
`M` is empty, and no separation or countability assumption is required for the manifold,
embedding, normal-form, or submersion assertions.

With this atlas:
* the subtype inclusion into `Fin (m + 1) → Y` is a `C^n` smooth embedding whose tangent image
  consists of tuples of tangent vectors with equal images under `mfderiv IY IM π`
  (`TauCeti.isSmoothEmbedding_coe_iteratedFiberProduct`,
  `TauCeti.mem_range_mfderiv_coe_iteratedFiberProduct_iff`);
* when `M` is Hausdorff, the multidiagonal `{z : Fin k → M | ∀ i j, z i = z j}` is closed and
  `IteratedFiberProduct π k` is a closed embedded submanifold of `Fin k → Y`, as the preimage of
  that multidiagonal under `Pi.map fun _ ↦ π`
  (`TauCeti.isClosedEmbedding_coe_iteratedFiberProduct`);
* around every point of `IteratedFiberProduct π (m + 1)` there is a product of maximal-atlas
  submersion charts of `Y` over the preferred target chart of `M` in which the submanifold is cut
  out by equality of the base-projection coordinates
  (`TauCeti.exists_submersionCharts_iteratedFiberProduct`);
* the smooth structure is independent of the order of iteration: splitting `k₁ + k₂` factors
  (`k₁ = m₁ + 1`, `k₂ = m₂ + 1`) gives a canonical `C^n` diffeomorphism with the transverse fibre
  product of `Y^[k₁]` and `Y^[k₂]` over `M`
  (`TauCeti.iteratedFiberProductSplitDiffeomorph`), covering both left and right iteration;
* the common projection `IteratedFiberProduct.baseProj` to `M` is a `C^n` submersion (surjective
  if and only if `π` is surjective), and every factor projection `IteratedFiberProduct.eval i` to
  `Y` is a surjective `C^n` submersion (`TauCeti.isSubmersion_baseProj`,
  `TauCeti.isSubmersion_eval`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 4.12 (rank theorem for submersions), Theorem 4.26 (local sections of submersions),
  and Theorem 6.30 (transverse preimages).
-/

public section

open Function Set Module Topology
open scoped Manifold ContDiff

namespace TauCeti

section Manifold

variable {EY HY Y EM HM M : Type*}
  [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
  [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IY : ModelWithCorners ℝ EY HY} {IM : ModelWithCorners ℝ EM HM}
  [TopologicalSpace Y] [ChartedSpace HY Y]
  [TopologicalSpace M] [ChartedSpace HM M]
  {n : ℕ∞ω}

private def iteratedOneHomeomorph {π : Y → M} (hπ : Continuous π) :
    IteratedFiberProduct π 1 ≃ₜ {p : M × Y // id p.1 = π p.2} where
  toFun y := ⟨(π (y.val 0), y.val 0), rfl⟩
  invFun p := ⟨fun _ ↦ p.val.2, fun _ _ ↦ rfl⟩
  left_inv y := Subtype.ext (funext fun i ↦ by rw [Fin.eq_zero i])
  right_inv p := Subtype.ext (Prod.ext p.property.symm rfl)
  continuous_toFun :=
    ((hπ.comp (IteratedFiberProduct.continuous_eval 0)).prodMk
      (IteratedFiberProduct.continuous_eval 0)).subtype_mk _
  continuous_invFun :=
    (continuous_pi fun _ ↦ continuous_subtypeVal.snd).subtype_mk _

private def iteratedStepHomeomorph {π : Y → M} (m : ℕ) :
    IteratedFiberProduct π (m + 2) ≃ₜ
      {p : IteratedFiberProduct π (m + 1) × Y // IteratedFiberProduct.baseProj p.1 = π p.2} where
  toFun y := ⟨(⟨Fin.init y.val, fun i j ↦ y.property i.castSucc j.castSucc⟩, y.val (Fin.last
      (m + 1))),
    y.property 0 (Fin.last (m + 1))⟩
  invFun p := ⟨Fin.snoc (α := fun _ ↦ Y) p.val.1.val p.val.2, by
    have hbase : ∀ i : Fin (m + 2),
        π (Fin.snoc (α := fun _ ↦ Y) p.val.1.val p.val.2 i) = IteratedFiberProduct.baseProj p.val.1
            :=
      fun i ↦ i.lastCases
        (by simp only [Fin.snoc_last]; exact p.property.symm)
        (fun k ↦ by simp only [Fin.snoc_castSucc]; exact (p.val.1.property 0 k).symm)
    exact fun i j ↦ (hbase i).trans (hbase j).symm⟩
  left_inv y := Subtype.ext (Fin.snoc_init_self y.val)
  right_inv p := by ext <;> simp
  continuous_toFun :=
    (((continuous_pi fun k : Fin (m + 1) ↦
      IteratedFiberProduct.continuous_eval k.castSucc).subtype_mk _).prodMk
      (IteratedFiberProduct.continuous_eval (Fin.last (m + 1)))).subtype_mk _
  continuous_invFun := by
    refine (continuous_pi fun i ↦ ?_).subtype_mk _
    induction i using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last]
      exact continuous_subtypeVal.snd
    | cast k =>
      simp only [Fin.snoc_castSucc]
      exact (IteratedFiberProduct.continuous_eval k).comp continuous_subtypeVal.fst

omit [ChartedSpace HY Y] [ChartedSpace HM M] in
/-- On a product chart domain `∏ i, (φ i).source` over a codomain chart `ψ` where `ψ.extend IM ∘ π`
reads as `(L i ∘ (φ i).extend IY ·).1`, a tuple `w : ι → Y` satisfies the equal-fibre
matching condition `∀ i j, π (w i) = π (w j)` if and only if all base-projection coordinates
`(L i ((φ i).extend IY (w i))).1` agree. -/
theorem forall_apply_eq_iff_fst_extend_eq {π : Y → M} {ι F : Type*}
    {ψ : OpenPartialHomeomorph M HM}
    {φ : ι → OpenPartialHomeomorph Y HY}
    {L : ι → EY → EM × F}
    (hφ_sub : ∀ i, (φ i).source ⊆ π ⁻¹' ψ.source)
    (hφ_eq : ∀ (i : ι) {w : Y}, w ∈ (φ i).source →
      ψ.extend IM (π w) = (L i ((φ i).extend IY w)).1)
    {w : ι → Y} (hw : ∀ i, w i ∈ (φ i).source) :
    (∀ i j : ι, π (w i) = π (w j)) ↔
      ∀ i j : ι, (L i ((φ i).extend IY (w i))).1 = (L j ((φ j).extend IY (w j))).1 :=
  ⟨fun h i j ↦ by rw [← hφ_eq i (hw i), ← hφ_eq j (hw j), h i j], fun h i j ↦
    (ψ.extend IM).injOn
      (by rw [OpenPartialHomeomorph.extend_source]; exact hφ_sub i (hw i))
      (by rw [OpenPartialHomeomorph.extend_source]; exact hφ_sub j (hw j))
      (by rw [hφ_eq i (hw i), hφ_eq j (hw j)]; exact h i j)⟩

variable [IsManifold IY n Y] [IsManifold IM n M]
  [IY.Boundaryless]
  [FiniteDimensional ℝ EY] [FiniteDimensional ℝ EM]

/-- **Local projection normal form for `IteratedFiberProduct`.** Around every point
`y : IteratedFiberProduct π (m + 1)`, there exist maximal-atlas charts `φ i` of `Y` around `y.1 i`
(whose product `OpenPartialHomeomorph.pi φ` belongs to the maximal atlas of `Fin (m + 1) → Y`) and
linear splittings `L i : EY ≃L[ℝ] EM × (Fin (dim Y - dim M) → ℝ)` over `extChartAt IM (baseProj y)`
such that, on `(OpenPartialHomeomorph.pi φ).source`, a tuple `z : Fin (m + 1) → Y` belongs to
`IteratedFiberProduct π (m + 1)` if and only if all its base-projection coordinates
`(L i ((φ i).extend IY (z i))).1` agree. The base `M` is not required to be boundaryless. -/
theorem exists_submersionCharts_iteratedFiberProduct {π : Y → M} (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) {m : ℕ}
    (y : IteratedFiberProduct π (m + 1)) :
    ∃ (φ : ∀ _ : Fin (m + 1), OpenPartialHomeomorph Y HY)
      (L : ∀ _ : Fin (m + 1), EY ≃L[ℝ] EM × (Fin (finrank ℝ EY - finrank ℝ EM) → ℝ)),
      y.val ∈ (OpenPartialHomeomorph.pi φ).source ∧
      OpenPartialHomeomorph.pi φ ∈
        IsManifold.maximalAtlas (ModelWithCorners.pi fun _ : Fin (m + 1) ↦ IY) n
          (Fin (m + 1) → Y) ∧
      (∀ i (w : Y), w ∈ (φ i).source →
        extChartAt IM (IteratedFiberProduct.baseProj y) (π w) =
          (L i ((φ i).extend IY w)).1) ∧
      ∀ z ∈ (OpenPartialHomeomorph.pi φ).source,
        (z ∈ range (Subtype.val : IteratedFiberProduct π (m + 1) → (Fin (m + 1) → Y)) ↔
          ∀ i j : Fin (m + 1),
            (L i ((φ i).extend IY (z i))).1 = (L j ((φ j).extend IY (z j))).1) := by
  choose φ L hyφ hφmax hφsub hφeq using fun i : Fin (m + 1) ↦ by
    simpa only [← IteratedFiberProduct.baseProj_eq_apply y i] using
      hπ.exists_domChart_mem_maximalAtlas_chartAt hn (y.val i)
  refine ⟨φ, L, fun i _ ↦ hyφ i, TauCeti.pi_mem_maximalAtlas hφmax, hφeq, fun z hz ↦ ?_⟩
  rw [mem_range_coe_iteratedFiberProduct_iff]
  exact forall_apply_eq_iff_fst_extend_eq
    (ψ := chartAt HM (IteratedFiberProduct.baseProj y)) (L := fun i ↦ (L i))
    hφsub (fun i _ hw ↦ hφeq i _ hw) (fun i ↦ hz i trivial)

variable [IM.Boundaryless]

/-- **Manifold structure and smooth embedding of iterated submersion fibre products.** For a `C^n`
submersion `π : Y → M` (`1 ≤ n`) between finite-dimensional boundaryless real manifolds, the
`(m + 1)`-fold fibre product `IteratedFiberProduct π (m + 1)` carries a `C^n` manifold structure
of dimension `(m + 1) * dim Y - m * dim M` with its subspace topology, smoothly embedded into
`Fin (m + 1) → Y`, whose tangent image consists of tuples of tangent vectors with equal images
under `mfderiv IY IM π`. -/
theorem exists_isManifold_iteratedFiberProduct_isSmoothEmbedding {π : Y → M}
    (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π) (m : ℕ) :
    ∃ cs : ChartedSpace (Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ)
        (IteratedFiberProduct π (m + 1)),
      letI := cs
      IsManifold 𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) n
        (IteratedFiberProduct π (m + 1)) ∧
      Manifold.IsSmoothEmbedding
        𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ)
        (ModelWithCorners.pi fun _ : Fin (m + 1) ↦ IY) n
        (Subtype.val : IteratedFiberProduct π (m + 1) → (Fin (m + 1) → Y)) ∧
      ∀ (y : IteratedFiberProduct π (m + 1))
        (v : TangentSpace (ModelWithCorners.pi fun _ : Fin (m + 1) ↦ IY) y.val),
        v ∈ (mfderiv
          𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ)
          (ModelWithCorners.pi fun _ : Fin (m + 1) ↦ IY)
          (Subtype.val : IteratedFiberProduct π (m + 1) → (Fin (m + 1) → Y)) y).range ↔
        ∀ i j : Fin (m + 1),
          mfderiv IY IM π (y.val i) (v i) =
            tangentSpaceCast IM (π (y.val j)) (π (y.val i)) (mfderiv IY IM π (y.val j) (v j)) := by
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have : IsManifold IY 1 Y := .of_le hn
  induction m with
  | zero =>
    let d₀ := finrank ℝ EM + finrank ℝ EY - finrank ℝ EM
    have hd₀ : d₀ = (0 + 1) * finrank ℝ EY - 0 * finrank ℝ EM := by omega
    rw [← hd₀]
    let := transverseFiberProductChartedSpace hn (contMDiff_id (I := IM)) hπ.contMDiff
      (fun p _ ↦ transverse_id_left π p)
    have := isManifold_transverseFiberProduct hn (contMDiff_id (I := IM)) hπ.contMDiff
      (fun p _ ↦ transverse_id_left π p)
    let e₀ := iteratedOneHomeomorph hπ.contMDiff.continuous
    let := e₀.pullbackChartedSpace (H := Fin d₀ → ℝ)
    have := e₀.pullback_isManifold 𝓘(ℝ, Fin d₀ → ℝ) n
    let Φ : IteratedFiberProduct π 1 ≃ₘ^n⟮𝓘(ℝ, Fin d₀ → ℝ),
        ModelWithCorners.pi (fun _ : Fin 1 ↦ IY)⟯ (Fin 1 → Y) :=
      ((e₀.pullbackDiffeomorph 𝓘(ℝ, Fin d₀ → ℝ) n).trans
        (transverseFiberProductIdLeftDiffeomorph hn hπ.contMDiff)).trans
        (Diffeomorph.piUnique (fun _ : Fin 1 ↦ IY) (fun _ : Fin 1 ↦ Y) n).symm
    have hΦcoe : (Φ : IteratedFiberProduct π 1 → (Fin 1 → Y)) = Subtype.val := by
      funext y i
      rw [Fin.eq_zero i]
      simp only [Φ, Diffeomorph.coe_trans, Function.comp_apply, Diffeomorph.piUnique_symm_apply,
        uniqueElim_const, Homeomorph.coe_pullbackDiffeomorph]
      exact transverseFiberProductIdLeftDiffeomorph_apply hn hπ.contMDiff (e₀ y)
    have himm : Manifold.IsImmersion 𝓘(ℝ, Fin d₀ → ℝ)
        (ModelWithCorners.pi fun _ : Fin 1 ↦ IY) n
        (Subtype.val : IteratedFiberProduct π 1 → (Fin 1 → Y)) := by
      rw [← hΦcoe, ← comp_id (f := (Φ : IteratedFiberProduct π 1 → (Fin 1 → Y)))]
      exact Φ.isImmersion_comp hn Manifold.IsImmersion.id
    refine ⟨inferInstance, inferInstance, ⟨himm, IsEmbedding.subtypeVal⟩, fun y v ↦ ?_⟩
    rw [← hΦcoe]
    exact ⟨fun _ i j ↦ by rw [Fin.eq_zero i, Fin.eq_zero j]; rfl,
      fun _ ↦ (Φ.isInvertible_mfderiv hn0).surjective v⟩
  | succ m ih =>
    obtain ⟨cs_m, hman_m, hemb_m, hrange_m⟩ := ih
    let := cs_m
    let d_m := (m + 1) * finrank ℝ EY - m * finrank ℝ EM
    let K_m := 𝓘(ℝ, Fin d_m → ℝ)
    let PI_m := ModelWithCorners.pi fun _ : Fin (m + 1) ↦ IY
    let PI_succ := ModelWithCorners.pi fun _ : Fin (m + 2) ↦ IY
    have hf : ContMDiff K_m IM n
        (IteratedFiberProduct.baseProj : IteratedFiberProduct π (m + 1) → M) :=
      hπ.contMDiff.comp ((contMDiff_apply (i := (0 : Fin (m + 1)))).comp hemb_m.contMDiff)
    have htrans := fun (p : IteratedFiberProduct π (m + 1) × Y)
      (_ : IteratedFiberProduct.baseProj p.1 = π p.2) ↦
        transverse_of_isSubmersion_right (IX := K_m) (f := IteratedFiberProduct.baseProj) hn hπ p
    let Q := {p : IteratedFiberProduct π (m + 1) × Y //
      IteratedFiberProduct.baseProj p.1 = π p.2}
    let d' := finrank ℝ (Fin d_m → ℝ) + finrank ℝ EY - finrank ℝ EM
    have hd' : d' = (m + 2) * finrank ℝ EY - (m + 1) * finrank ℝ EM := by
      dsimp only [d', d_m]
      rw [Module.finrank_fin_fun, Nat.succ_mul (m + 1) (finrank ℝ EY),
        Nat.succ_mul m (finrank ℝ EM)]
      rcases le_or_gt (m * finrank ℝ EM) ((m + 1) * finrank ℝ EY) with h | h
      · rw [← Nat.sub_add_comm h, Nat.sub_sub]
      · have : finrank ℝ EY < finrank ℝ EM := lt_of_not_ge fun hba ↦ by
          have := Nat.mul_le_mul_left m hba
          rw [Nat.succ_mul m (finrank ℝ EY)] at h
          omega
        omega
    rw [← hd']
    let := transverseFiberProductChartedSpace hn hf hπ.contMDiff htrans
    have := isManifold_transverseFiberProduct hn hf hπ.contMDiff htrans
    have hemb_Q := isSmoothEmbedding_coe_transverseFiberProduct hn hf hπ.contMDiff htrans
    have hrange_Q := mem_range_mfderiv_coe_transverseFiberProduct_iff hn hf hπ.contMDiff htrans
    let e_step := iteratedStepHomeomorph (π := π) m
    let := e_step.pullbackChartedSpace (H := Fin d' → ℝ)
    have := e_step.pullback_isManifold 𝓘(ℝ, Fin d' → ℝ) n
    let ψ := e_step.pullbackDiffeomorph 𝓘(ℝ, Fin d' → ℝ) n
    have hψ_coe : (ψ : IteratedFiberProduct π (m + 2) → Q) = e_step :=
      Homeomorph.coe_pullbackDiffeomorph 𝓘(ℝ, Fin d' → ℝ) n e_step
    have he_step_cont : ContMDiff 𝓘(ℝ, Fin d' → ℝ) 𝓘(ℝ, Fin d' → ℝ) n e_step :=
      hψ_coe ▸ ψ.contMDiff
    have he_step_inv : ∀ y : IteratedFiberProduct π (m + 2),
        (mfderiv 𝓘(ℝ, Fin d' → ℝ) 𝓘(ℝ, Fin d' → ℝ) e_step y).IsInvertible :=
      fun y ↦ hψ_coe ▸ ψ.isInvertible_mfderiv hn0
    let snocD := Diffeomorph.piSnoc (fun _ : Fin (m + 2) ↦ IY) (fun _ : Fin (m + 2) ↦ Y) n
    have hfactor : (Subtype.val : IteratedFiberProduct π (m + 2) → (Fin (m + 2) → Y)) =
        snocD ∘ Prod.map Subtype.val id ∘ (Subtype.val : Q → _) ∘ e_step := by
      funext y
      simp only [Function.comp_apply, snocD, Diffeomorph.piSnoc_apply]
      exact (Fin.snoc_init_self y.val).symm
    have hcont_coe : ContMDiff 𝓘(ℝ, Fin d' → ℝ) PI_succ n
        (Subtype.val : IteratedFiberProduct π (m + 2) → (Fin (m + 2) → Y)) := by
      rw [hfactor]
      exact snocD.contMDiff.comp ((hemb_m.contMDiff.prodMap contMDiff_id).comp
        (hemb_Q.contMDiff.comp he_step_cont))
    -- Compute the differential of `Subtype.val` along the four-step factorization.
    have hmf_coe : ∀ (y : IteratedFiberProduct π (m + 2))
        (ξ : TangentSpace 𝓘(ℝ, Fin d' → ℝ) y),
        mfderiv 𝓘(ℝ, Fin d' → ℝ) PI_succ Subtype.val y ξ =
          Fin.snoc (α := fun _ ↦ EY)
            (mfderiv K_m PI_m Subtype.val (e_step y).val.1
              (mfderiv 𝓘(ℝ, Fin d' → ℝ) (K_m.prod IY) Subtype.val (e_step y)
                (mfderiv 𝓘(ℝ, Fin d' → ℝ) 𝓘(ℝ, Fin d' → ℝ) e_step y ξ)).1)
            (mfderiv 𝓘(ℝ, Fin d' → ℝ) (K_m.prod IY) Subtype.val (e_step y)
              (mfderiv 𝓘(ℝ, Fin d' → ℝ) 𝓘(ℝ, Fin d' → ℝ) e_step y ξ)).2 := by
      intro y ξ
      have : IsManifold K_m 1 (IteratedFiberProduct π (m + 1)) := .of_le hn
      let q : Q := e_step y
      have hed := (he_step_cont y).mdifferentiableAt hn0
      have hQd := (hemb_Q.contMDiff q).mdifferentiableAt hn0
      have hmd := ((hemb_m.contMDiff.prodMap (contMDiff_id (I := IY))) q.val).mdifferentiableAt hn0
      have hsnocd := (snocD.contMDiff (q.val.1.val, q.val.2)).mdifferentiableAt hn0
      have hprod : mfderiv (K_m.prod IY) (PI_m.prod IY) (Prod.map Subtype.val id) q.val =
          (mfderiv K_m PI_m Subtype.val q.val.1).prodMap
            (ContinuousLinearMap.id ℝ (TangentSpace IY q.val.2)) := by
        rw [mfderiv_prodMap (p := q.val) ((hemb_m.contMDiff q.val.1).mdifferentiableAt hn0)
          (mdifferentiableAt_id (I := IY)), mfderiv_id]
      rw [hfactor, mfderiv_comp_apply y hsnocd (hmd.comp y (hQd.comp y hed)),
        mfderiv_comp_apply y hmd (hQd.comp y hed), mfderiv_comp_apply y hQd hed]
      exact (congrArg (mfderiv (PI_m.prod IY) PI_succ snocD (q.val.1.val, q.val.2))
        (DFunLike.congr_fun hprod _)).trans
        (Diffeomorph.mfderiv_piSnoc_apply (fun _ : Fin (m + 2) ↦ IY)
          (fun _ : Fin (m + 2) ↦ Y) n (q.val.1.val, q.val.2) _ _)
    have himm : Manifold.IsImmersion 𝓘(ℝ, Fin d' → ℝ) PI_succ n
        (Subtype.val : IteratedFiberProduct π (m + 2) → (Fin (m + 2) → Y)) := by
      refine hcont_coe.isImmersion_of_injective_mfderiv hn fun y ξ₁ ξ₂ hξ ↦ ?_
      have hsnoc := (hmf_coe y ξ₁).symm.trans (hξ.trans (hmf_coe y ξ₂))
      have hinit := (Fin.init_snoc (α := fun _ ↦ EY) _ _).symm.trans
        ((congrArg Fin.init hsnoc).trans (Fin.init_snoc (α := fun _ ↦ EY) _ _))
      have hlast := (Fin.snoc_last (α := fun _ ↦ EY) _ _).symm.trans
        ((congrFun hsnoc (Fin.last (m + 1))).trans (Fin.snoc_last (α := fun _ ↦ EY) _ _))
      have hpair := Prod.ext
        ((hemb_m.isImmersion.isImmersionAt (e_step y).val.1).mfderiv_injective hn0 hinit) hlast
      exact (he_step_inv y).injective
        ((hemb_Q.isImmersion.isImmersionAt (e_step y)).mfderiv_injective hn0 hpair)
    refine ⟨inferInstance, inferInstance, ⟨himm, IsEmbedding.subtypeVal⟩, fun y v ↦ ?_⟩
    -- Identify the differential of `baseProj` at `p₁ = (e_step y).1.1` through the `0`-th factor.
    let p₁ : IteratedFiberProduct π (m + 1) := (e_step y).val.1
    have hmf_base : ∀ ζ : TangentSpace K_m p₁,
        mfderiv K_m IM IteratedFiberProduct.baseProj p₁ ζ =
          mfderiv IY IM π (y.val 0)
            ((mfderiv K_m PI_m Subtype.val p₁ ζ : Fin (m + 1) → EY) 0) := fun ζ ↦ by
      have he0 := (TauCeti.hasMFDerivAt_apply (I := fun _ : Fin (m + 1) ↦ IY)
        (0 : Fin (m + 1)) p₁.val).mdifferentiableAt
      have hπd := (hπ.contMDiff (p₁.val 0)).mdifferentiableAt hn0
      have hc1 := mfderiv_comp p₁ (hπd.comp p₁.val he0) ((hemb_m.contMDiff p₁).mdifferentiableAt
          hn0)
      have hc2 := mfderiv_comp p₁.val hπd he0
      rw [TauCeti.mfderiv_apply] at hc2
      exact DFunLike.congr_fun
        (hc1.trans (congrArg (·.comp (mfderiv K_m PI_m Subtype.val p₁)) hc2)) ζ
    constructor
    · rintro ⟨ξ, hξ⟩
      let η := mfderiv 𝓘(ℝ, Fin d' → ℝ) 𝓘(ℝ, Fin d' → ℝ) e_step y ξ
      let pair := mfderiv 𝓘(ℝ, Fin d' → ℝ) (K_m.prod IY) Subtype.val (e_step y) η
      let u : Fin (m + 1) → EY := mfderiv K_m PI_m Subtype.val p₁ pair.1
      have hv_eq : v = Fin.snoc (α := fun _ ↦ EY) u pair.2 := hξ.symm.trans (hmf_coe y ξ)
      have hQmem := (hmf_base pair.1).symm.trans ((hrange_Q (e_step y) pair).1 ⟨η, rfl⟩)
      have humem := (hrange_m p₁ u).1 ⟨pair.1, rfl⟩
      -- Every coordinate agrees with coordinate `0` after transporting to `π (y.1 0)`.
      have h0 : ∀ i : Fin (m + 2),
          tangentSpaceCast IM (π (y.val i)) (π (y.val 0)) (mfderiv IY IM π (y.val i) (v i)) =
            mfderiv IY IM π (y.val 0) (u 0) := fun i ↦ by
        rw [hv_eq]
        induction i using Fin.lastCases with
        | last => simp only [Fin.snoc_last]; exact hQmem.symm
        | cast k => simp only [Fin.snoc_castSucc]; exact (humem 0 k).symm
      exact fun i j ↦ (eq_tangentSpaceCast_iff_tangentSpaceCast_eq (y.property i 0)
          (y.property j 0)).2
        ((h0 i).trans (h0 j).symm)
    · intro hv
      obtain ⟨ζ, hζ⟩ := (hrange_m p₁ (Fin.init v)).2 fun i j ↦ hv i.castSucc j.castSucc
      rw [ContinuousLinearMap.coe_coe] at hζ
      have hQcond := (hmf_base ζ).trans
        ((congrArg (mfderiv IY IM π (y.val 0)) (congrFun hζ 0)).trans (hv 0 (Fin.last (m + 1))))
      obtain ⟨η, hη⟩ := (hrange_Q (e_step y) (ζ, v (Fin.last (m + 1)))).2 hQcond
      rw [ContinuousLinearMap.coe_coe] at hη
      obtain ⟨ξ, hξ⟩ := (he_step_inv y).surjective η
      refine ⟨ξ, (hmf_coe y ξ).trans ?_⟩
      rw [hξ, hη, hζ]
      exact Fin.snoc_init_self v

section ChosenAtlas

variable {π : Y → M} (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π)

/-- The canonical `C^n` atlas on `IteratedFiberProduct π (m + 1)`, constructed by iterating
`TauCeti.transverseFiberProductChartedSpace` along `IteratedFiberProduct.baseProj` and `π`. It uses
the subspace topology inherited from `Fin (m + 1) → Y` and is a named definition rather than a
global instance. -/
@[instance_reducible]
noncomputable def iteratedFiberProductChartedSpace (m : ℕ) :
    ChartedSpace (Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ)
      (IteratedFiberProduct π (m + 1)) :=
  (exists_isManifold_iteratedFiberProduct_isSmoothEmbedding hn hπ m).choose

/-- With its chosen atlas, `IteratedFiberProduct π (m + 1)` is a `C^n` manifold of dimension
`(m + 1) * dim Y - m * dim M`. -/
theorem isManifold_iteratedFiberProduct (m : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ m
    IsManifold 𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) n
      (IteratedFiberProduct π (m + 1)) :=
  (exists_isManifold_iteratedFiberProduct_isSmoothEmbedding hn hπ m).choose_spec.1

/-- With its chosen atlas, the inclusion of `IteratedFiberProduct π (m + 1)` into `Fin (m + 1) → Y`
is a `C^n` smooth embedding. -/
theorem isSmoothEmbedding_coe_iteratedFiberProduct (m : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ m
    Manifold.IsSmoothEmbedding
      𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ)
      (ModelWithCorners.pi fun _ : Fin (m + 1) ↦ IY) n
      (Subtype.val : IteratedFiberProduct π (m + 1) → (Fin (m + 1) → Y)) :=
  (exists_isManifold_iteratedFiberProduct_isSmoothEmbedding hn hπ m).choose_spec.2.1

/-- A tangent tuple in `Fin (m + 1) → Y` lies in the tangent image of
`IteratedFiberProduct π (m + 1)` if and only if all its coordinates have equal images under
`mfderiv IY IM π`. -/
theorem mem_range_mfderiv_coe_iteratedFiberProduct_iff (m : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ m
    ∀ (y : IteratedFiberProduct π (m + 1))
      (v : TangentSpace (ModelWithCorners.pi fun _ : Fin (m + 1) ↦ IY) y.val),
      v ∈ (mfderiv
        𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ)
        (ModelWithCorners.pi fun _ : Fin (m + 1) ↦ IY)
        (Subtype.val : IteratedFiberProduct π (m + 1) → (Fin (m + 1) → Y)) y).range ↔
      ∀ i j : Fin (m + 1),
        mfderiv IY IM π (y.val i) (v i) =
          tangentSpaceCast IM (π (y.val j)) (π (y.val i)) (mfderiv IY IM π (y.val j) (v j)) :=
  (exists_isManifold_iteratedFiberProduct_isSmoothEmbedding hn hπ m).choose_spec.2.2

/-- **Pointwise smooth universal property of `IteratedFiberProduct`.** For `m' ≤ n`, a map into
`IteratedFiberProduct π (m + 1)` is `C^{m'}` at `x` if and only if each coordinate map into `Y` is
`C^{m'}` at `x`. No separate continuity assumption is required. -/
theorem contMDiffAt_iteratedFiberProduct_iff {EX HX X : Type*}
    [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
    {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X]
    {m : ℕ} {m' : ℕ∞ω} (hm' : m' ≤ n) {f : X → IteratedFiberProduct π (m + 1)} {x : X} :
    letI := iteratedFiberProductChartedSpace hn hπ m
    ContMDiffAt IX 𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) m' f x ↔
      ∀ i : Fin (m + 1), ContMDiffAt IX IY m' (fun x ↦ IteratedFiberProduct.eval i (f x)) x := by
  let := iteratedFiberProductChartedSpace hn hπ m
  rw [((isSmoothEmbedding_coe_iteratedFiberProduct hn hπ m).of_le hm').contMDiffAt_iff_comp,
    contMDiffAt_pi_iff]
  rfl

/-- **Smooth universal property of `IteratedFiberProduct`.** For `m' ≤ n`, a map into
`IteratedFiberProduct π (m + 1)` is `C^{m'}` if and only if each coordinate map into `Y` is
`C^{m'}`. No separate continuity assumption is required. -/
theorem contMDiff_iteratedFiberProduct_iff {EX HX X : Type*}
    [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
    {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X]
    {m : ℕ} {m' : ℕ∞ω} (hm' : m' ≤ n) {f : X → IteratedFiberProduct π (m + 1)} :
    letI := iteratedFiberProductChartedSpace hn hπ m
    ContMDiff IX 𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) m' f ↔
      ∀ i : Fin (m + 1), ContMDiff IX IY m' (fun x ↦ IteratedFiberProduct.eval i (f x)) := by
  let := iteratedFiberProductChartedSpace hn hπ m
  exact (forall_congr' fun _ ↦ contMDiffAt_iteratedFiberProduct_iff hn hπ hm').trans forall_comm

/-- Every factor projection `eval i : Y^[m + 1] → Y` is `C^{m'}` for `m' ≤ n`. -/
theorem contMDiff_eval {m : ℕ} {m' : ℕ∞ω} (hm' : m' ≤ n) (i : Fin (m + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ m
    ContMDiff 𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) IY m'
      (IteratedFiberProduct.eval i : IteratedFiberProduct π (m + 1) → Y) := by
  let := iteratedFiberProductChartedSpace hn hπ m
  exact (contMDiff_apply (i := i)).comp
    ((isSmoothEmbedding_coe_iteratedFiberProduct hn hπ m).contMDiff.of_le hm')

/-- The diagonal map `const (m + 1) : Y → Y^[m + 1]` is `C^{m'}` for `m' ≤ n`. -/
theorem contMDiff_const {m : ℕ} {m' : ℕ∞ω} (hm' : m' ≤ n) :
    letI := iteratedFiberProductChartedSpace hn hπ m
    ContMDiff IY 𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) m'
      (IteratedFiberProduct.const (π := π) (m + 1)) := by
  let := iteratedFiberProductChartedSpace hn hπ m
  exact (contMDiff_iteratedFiberProduct_iff hn hπ hm').2 fun _ ↦ contMDiff_id

/-- **The diagonal inclusion is a smooth embedding.** On `IteratedFiberProduct π (m + 1)`,
`const (m + 1) : Y → Y^[m + 1]` is a `C^n` smooth embedding, split by `eval 0`. -/
theorem isSmoothEmbedding_const (m : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ m
    Manifold.IsSmoothEmbedding IY
      𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) n
      (IteratedFiberProduct.const (π := π) (m + 1)) := by
  let := iteratedFiberProductChartedSpace hn hπ m
  have := isManifold_iteratedFiberProduct hn hπ m
  exact (contMDiff_const hn hπ le_rfl).isSmoothEmbedding_of_leftInverse hn
    (contMDiff_eval hn hπ hn 0) (fun z ↦ IteratedFiberProduct.eval_const 0 z)

/-- The base projection `baseProj : Y^[m + 1] → M` is `C^{m'}` for `m' ≤ n`. -/
theorem contMDiff_baseProj {m : ℕ} {m' : ℕ∞ω} (hm' : m' ≤ n) :
    letI := iteratedFiberProductChartedSpace hn hπ m
    ContMDiff 𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) IM m'
      (IteratedFiberProduct.baseProj : IteratedFiberProduct π (m + 1) → M) := by
  let := iteratedFiberProductChartedSpace hn hπ m
  exact (hπ.contMDiff.of_le hm').comp (contMDiff_eval hn hπ hm' 0)

/-- The differential of `eval i` at `y` is the `i`-th coordinate of the differential of
`Subtype.val`. -/
theorem mfderiv_eval_apply {m : ℕ} (y : IteratedFiberProduct π (m + 1)) (i : Fin (m + 1))
    (ξ : letI := iteratedFiberProductChartedSpace hn hπ m
      TangentSpace 𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) y) :
    letI := iteratedFiberProductChartedSpace hn hπ m
    mfderiv 𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) IY
      (IteratedFiberProduct.eval i) y ξ =
      mfderiv 𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ)
        (ModelWithCorners.pi fun _ : Fin (m + 1) ↦ IY) Subtype.val y ξ i := by
  let := iteratedFiberProductChartedSpace hn hπ m
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have hcomp := mfderiv_comp y (TauCeti.hasMFDerivAt_apply i y.val).mdifferentiableAt
    (((isSmoothEmbedding_coe_iteratedFiberProduct hn hπ m).contMDiff y).mdifferentiableAt hn0)
  rw [TauCeti.mfderiv_apply] at hcomp
  exact DFunLike.congr_fun hcomp ξ

/-- Every family of tangent vectors `(v i)` along `y : IteratedFiberProduct π (m + 1)` with equal
images under `mfderiv IY IM π` arises from a tangent vector `ξ` of `IteratedFiberProduct π (m + 1)`
under the differentials of `eval i`. -/
theorem exists_mfderiv_eval_eq_of_iteratedFiberProduct {m : ℕ}
    (y : IteratedFiberProduct π (m + 1)) (v : ∀ i : Fin (m + 1), TangentSpace IY (y.val i))
    (hv : ∀ i j : Fin (m + 1),
      mfderiv IY IM π (y.val i) (v i) =
        tangentSpaceCast IM (π (y.val j)) (π (y.val i)) (mfderiv IY IM π (y.val j) (v j))) :
    letI := iteratedFiberProductChartedSpace hn hπ m
    ∃ ξ, ∀ i : Fin (m + 1),
      mfderiv 𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) IY
        (IteratedFiberProduct.eval i) y ξ = v i := by
  let := iteratedFiberProductChartedSpace hn hπ m
  obtain ⟨ξ, hξ⟩ := (mem_range_mfderiv_coe_iteratedFiberProduct_iff hn hπ m y v).2 hv
  exact ⟨ξ, fun i ↦ (mfderiv_eval_apply hn hπ y i ξ).trans (congrFun hξ i)⟩

/-- A tangent vector of `IteratedFiberProduct π (m + 1)` is zero when the differentials of all
factor projections `eval i` vanish on it. -/
theorem eq_zero_of_mfderiv_eval_iteratedFiberProduct {m : ℕ}
    (y : IteratedFiberProduct π (m + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ m
    ∀ ξ : TangentSpace 𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) y,
      (∀ i : Fin (m + 1),
        mfderiv 𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) IY
          (IteratedFiberProduct.eval i) y ξ = 0) →
      ξ = 0 := by
  let := iteratedFiberProductChartedSpace hn hπ m
  intro ξ hξ
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have hi := isSmoothEmbedding_coe_iteratedFiberProduct hn hπ m
  refine (injective_iff_map_eq_zero _).1 ((hi.isImmersion.isImmersionAt y).mfderiv_injective hn0)
    ξ (funext fun i ↦ ?_)
  exact (mfderiv_eval_apply hn hπ y i ξ).symm.trans (hξ i)

/-- **The composite base projection is a submersion.** On `IteratedFiberProduct π (m + 1)`,
`IteratedFiberProduct.baseProj : Y^[m + 1] → M` is a `C^n` submersion. -/
theorem isSubmersion_baseProj (m : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ m
    Manifold.IsSubmersion
      𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) IM n
      (IteratedFiberProduct.baseProj : IteratedFiberProduct π (m + 1) → M) := by
  let := iteratedFiberProductChartedSpace hn hπ m
  have := isManifold_iteratedFiberProduct hn hπ m
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  refine ((contMDiff_baseProj hn hπ le_rfl).isSubmersionOfComplement_of_surjective_mfderiv hn
    fun y w ↦ ?_).isSubmersion
  choose v hv using fun i : Fin (m + 1) ↦
    ((tangentSpaceCast IM (π (y.val i)) (IteratedFiberProduct.baseProj y)).surjective.comp
      (hπ.surjective_mfderiv hn0 (y.val i))) w
  have hcompat : ∀ i j : Fin (m + 1),
      mfderiv IY IM π (y.val i) (v i) =
        tangentSpaceCast IM (π (y.val j)) (π (y.val i)) (mfderiv IY IM π (y.val j) (v j)) :=
    fun i j ↦ (eq_tangentSpaceCast_iff_tangentSpaceCast_eq (y.property i 0) (y.property j 0)).2
      ((hv i).trans (hv j).symm)
  obtain ⟨ξ, hξ⟩ := exists_mfderiv_eval_eq_of_iteratedFiberProduct hn hπ y v hcompat
  refine ⟨ξ, ?_⟩
  have hc := mfderiv_comp_apply y ((hπ.contMDiff (y.val 0)).mdifferentiableAt hn0)
    (((contMDiff_eval hn hπ le_rfl 0) y).mdifferentiableAt hn0) ξ
  exact hc.trans (by rw [hξ 0]; exact hv 0)

/-- **Every factor projection is a surjective submersion.** On `IteratedFiberProduct π (m + 1)`,
each coordinate projection `eval i : Y^[m + 1] → Y` is a `C^n` submersion. -/
theorem isSubmersion_eval {m : ℕ} (i : Fin (m + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ m
    Manifold.IsSubmersion
      𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) IY n
      (IteratedFiberProduct.eval i : IteratedFiberProduct π (m + 1) → Y) := by
  let := iteratedFiberProductChartedSpace hn hπ m
  have := isManifold_iteratedFiberProduct hn hπ m
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  refine ((contMDiff_eval hn hπ le_rfl i).isSubmersionOfComplement_of_surjective_mfderiv hn
    fun y u ↦ ?_).isSubmersion
  let w₀ : TangentSpace IM (π (y.val i)) := mfderiv IY IM π (y.val i) u
  have hsurj : ∀ j : Fin (m + 1),
      ∃ v_j : TangentSpace IY (y.val j),
        (j = i → tangentSpaceCast IY (y.val j) (y.val i) v_j = u) ∧
          tangentSpaceCast IM (π (y.val j)) (π (y.val i)) (mfderiv IY IM π (y.val j) v_j) = w₀ := by
    intro j
    by_cases hji : j = i
    · subst hji; exact ⟨u, fun _ ↦ rfl, rfl⟩
    · obtain ⟨v_j, hv_j⟩ := ((tangentSpaceCast IM (π (y.val j)) (π (y.val i))).surjective.comp
        (hπ.surjective_mfderiv hn0 (y.val j))) w₀
      exact ⟨v_j, fun h ↦ (hji h).elim, hv_j⟩
  choose v hv_eq hv_map using hsurj
  have hcompat : ∀ j₁ j₂ : Fin (m + 1),
      mfderiv IY IM π (y.val j₁) (v j₁) =
        tangentSpaceCast IM (π (y.val j₂)) (π (y.val j₁)) (mfderiv IY IM π (y.val j₂) (v j₂)) :=
    fun j₁ j₂ ↦ (eq_tangentSpaceCast_iff_tangentSpaceCast_eq (y.property j₁ i) (y.property j₂ i)).2
      ((hv_map j₁).trans (hv_map j₂).symm)
  obtain ⟨ξ, hξ⟩ := exists_mfderiv_eval_eq_of_iteratedFiberProduct hn hπ y v hcompat
  exact ⟨ξ, (hξ i).trans (hv_eq i rfl)⟩

/-! ### Canonical diffeomorphisms for `k = 1`, `k = 2`, and arbitrary splittings -/

/-- The one-fold fibre product `IteratedFiberProduct π 1` is `C^n` diffeomorphic to `Y` via
evaluation at `0`, with inverse `const 1`. -/
noncomputable def iteratedFiberProductOneDiffeomorph :
    letI := iteratedFiberProductChartedSpace hn hπ 0
    IteratedFiberProduct π 1 ≃ₘ^n⟮
      𝓘(ℝ, Fin ((0 + 1) * finrank ℝ EY - 0 * finrank ℝ EM) → ℝ), IY⟯ Y := by
  letI := iteratedFiberProductChartedSpace hn hπ 0
  exact
    { toFun := IteratedFiberProduct.eval 0
      invFun := IteratedFiberProduct.const 1
      left_inv := fun y ↦ Subtype.ext (funext fun i ↦ by rw [Fin.eq_zero i]; rfl)
      right_inv := fun _ ↦ rfl
      contMDiff_toFun := contMDiff_eval hn hπ le_rfl 0
      contMDiff_invFun := contMDiff_const hn hπ le_rfl }

/-- `iteratedFiberProductOneDiffeomorph` evaluates at coordinate `0`. -/
@[simp]
theorem iteratedFiberProductOneDiffeomorph_apply (y : IteratedFiberProduct π 1) :
    letI := iteratedFiberProductChartedSpace hn hπ 0
    iteratedFiberProductOneDiffeomorph hn hπ y = IteratedFiberProduct.eval 0 y := (rfl)

/-- The inverse of `iteratedFiberProductOneDiffeomorph` is the diagonal `const 1`. -/
@[simp]
theorem iteratedFiberProductOneDiffeomorph_symm_apply (z : Y) :
    letI := iteratedFiberProductChartedSpace hn hπ 0
    (iteratedFiberProductOneDiffeomorph hn hπ).symm z = IteratedFiberProduct.const 1 z := (rfl)

/-- The two-fold fibre product `IteratedFiberProduct π 2` is `C^n` diffeomorphic to the binary
transverse fibre product `{p : Y × Y // π p.1 = π p.2}` via `y ↦ (y₀, y₁)`. -/
noncomputable def iteratedFiberProductTwoDiffeomorph :
    letI := iteratedFiberProductChartedSpace hn hπ 1
    letI := transverseFiberProductChartedSpace hn hπ.contMDiff hπ.contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_right hn hπ p)
    IteratedFiberProduct π 2 ≃ₘ^n⟮
      𝓘(ℝ, Fin ((1 + 1) * finrank ℝ EY - 1 * finrank ℝ EM) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ EY + finrank ℝ EY - finrank ℝ EM) → ℝ)⟯
      {p : Y × Y // π p.1 = π p.2} := by
  letI := iteratedFiberProductChartedSpace hn hπ 1
  letI := transverseFiberProductChartedSpace hn hπ.contMDiff hπ.contMDiff
    (fun p _ ↦ transverse_of_isSubmersion_right hn hπ p)
  have hemb := isSmoothEmbedding_coe_transverseFiberProduct hn hπ.contMDiff hπ.contMDiff
    (fun p _ ↦ transverse_of_isSubmersion_right hn hπ p)
  refine
    { toFun := fun y ↦ ⟨(IteratedFiberProduct.eval 0 y, IteratedFiberProduct.eval 1 y),
        y.property 0 1⟩
      invFun := fun p ↦ ⟨![p.val.1, p.val.2], fun i j ↦ by
        fin_cases i <;> fin_cases j <;> simp [p.property]⟩
      left_inv := fun y ↦ Subtype.ext (funext fun i ↦ by fin_cases i <;> rfl)
      right_inv := fun _ ↦ rfl
      contMDiff_toFun := hemb.contMDiff_iff_comp.2
        ((contMDiff_eval hn hπ le_rfl 0).prodMk (contMDiff_eval hn hπ le_rfl 1))
      contMDiff_invFun := (contMDiff_iteratedFiberProduct_iff hn hπ le_rfl).2 fun i ↦ by
        fin_cases i
        exacts [hemb.contMDiff.fst, hemb.contMDiff.snd] }

/-- `iteratedFiberProductTwoDiffeomorph` sends `y` to the pair `(eval 0 y, eval 1 y)`. -/
@[simp]
theorem coe_iteratedFiberProductTwoDiffeomorph_apply (y : IteratedFiberProduct π 2) :
    letI := iteratedFiberProductChartedSpace hn hπ 1
    letI := transverseFiberProductChartedSpace hn hπ.contMDiff hπ.contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_right hn hπ p)
    (iteratedFiberProductTwoDiffeomorph hn hπ y : Y × Y) =
      (IteratedFiberProduct.eval 0 y, IteratedFiberProduct.eval 1 y) := (rfl)

/-- The inverse of `iteratedFiberProductTwoDiffeomorph` sends `p` to the two-tuple
`![p.1.1, p.1.2]`. -/
@[simp]
theorem coe_iteratedFiberProductTwoDiffeomorph_symm_apply
    (p : {p : Y × Y // π p.1 = π p.2}) :
    letI := iteratedFiberProductChartedSpace hn hπ 1
    letI := transverseFiberProductChartedSpace hn hπ.contMDiff hπ.contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_right hn hπ p)
    ((iteratedFiberProductTwoDiffeomorph hn hπ).symm p : Fin 2 → Y) = ![p.val.1, p.val.2] := (rfl)

/-- Canonical `C^n` diffeomorphism `Y^[m + 2] ≃ₘ^n Y^[m + 1] ×_M Y` identifying the
`(m + 2)`-fold iterated fibre product with one binary transverse fibre-product step over `M`. -/
noncomputable def iteratedFiberProductStepDiffeomorph (m : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ (m + 1)
    letI := iteratedFiberProductChartedSpace hn hπ m
    haveI := isManifold_iteratedFiberProduct hn hπ m
    letI := transverseFiberProductChartedSpace hn
      (contMDiff_baseProj hn hπ (m := m) le_rfl) hπ.contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_right hn hπ p)
    IteratedFiberProduct π (m + 2) ≃ₘ^n⟮
      𝓘(ℝ, Fin ((m + 2) * finrank ℝ EY - (m + 1) * finrank ℝ EM) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ (Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) +
        finrank ℝ EY - finrank ℝ EM) → ℝ)⟯
      {p : IteratedFiberProduct π (m + 1) × Y // IteratedFiberProduct.baseProj p.1 = π p.2} := by
  letI := iteratedFiberProductChartedSpace hn hπ (m + 1)
  letI := iteratedFiberProductChartedSpace hn hπ m
  haveI := isManifold_iteratedFiberProduct hn hπ m
  letI := transverseFiberProductChartedSpace hn
    (contMDiff_baseProj hn hπ (m := m) le_rfl) hπ.contMDiff
    (fun p _ ↦ transverse_of_isSubmersion_right hn hπ p)
  have hemb := isSmoothEmbedding_coe_transverseFiberProduct hn
    (contMDiff_baseProj hn hπ (m := m) le_rfl) hπ.contMDiff
    (fun p _ ↦ transverse_of_isSubmersion_right hn hπ p)
  let e := iteratedStepHomeomorph (π := π) m
  exact
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      contMDiff_toFun := hemb.contMDiff_iff_comp.2 <|
        ((contMDiff_iteratedFiberProduct_iff hn hπ le_rfl).2 fun j ↦
          contMDiff_eval hn hπ le_rfl j.castSucc).prodMk
          (contMDiff_eval hn hπ le_rfl (Fin.last (m + 1)))
      contMDiff_invFun := (contMDiff_iteratedFiberProduct_iff hn hπ le_rfl).2 fun i ↦ by
        induction i using Fin.lastCases with
        | last =>
          exact hemb.contMDiff.snd.congr fun x ↦
            Fin.snoc_last (α := fun _ ↦ Y) x.val.2 x.val.1.val
        | cast j =>
          exact ((contMDiff_eval hn hπ le_rfl j).comp hemb.contMDiff.fst).congr fun x ↦
            Fin.snoc_castSucc (α := fun _ ↦ Y) x.val.2 x.val.1.val j }

/-- The underlying tuple of the first factor of `iteratedFiberProductStepDiffeomorph` is
`Fin.init y.val`. -/
@[simp]
theorem coe_fst_iteratedFiberProductStepDiffeomorph (m : ℕ)
    (y : IteratedFiberProduct π (m + 2)) :
    letI := iteratedFiberProductChartedSpace hn hπ (m + 1)
    letI := iteratedFiberProductChartedSpace hn hπ m
    haveI := isManifold_iteratedFiberProduct hn hπ m
    letI := transverseFiberProductChartedSpace hn
      (contMDiff_baseProj hn hπ (m := m) le_rfl) hπ.contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_right hn hπ p)
    ((iteratedFiberProductStepDiffeomorph hn hπ m y).val.1 : Fin (m + 1) → Y) =
      Fin.init y.val := (rfl)

/-- The first factor of `iteratedFiberProductStepDiffeomorph` evaluates at `j.castSucc`. -/
theorem eval_fst_iteratedFiberProductStepDiffeomorph (m : ℕ)
    (y : IteratedFiberProduct π (m + 2)) (j : Fin (m + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ (m + 1)
    letI := iteratedFiberProductChartedSpace hn hπ m
    haveI := isManifold_iteratedFiberProduct hn hπ m
    letI := transverseFiberProductChartedSpace hn
      (contMDiff_baseProj hn hπ (m := m) le_rfl) hπ.contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_right hn hπ p)
    IteratedFiberProduct.eval j (iteratedFiberProductStepDiffeomorph hn hπ m y).val.1 =
      IteratedFiberProduct.eval j.castSucc y := (rfl)

/-- The second factor of `iteratedFiberProductStepDiffeomorph` is the last coordinate. -/
@[simp]
theorem snd_iteratedFiberProductStepDiffeomorph (m : ℕ)
    (y : IteratedFiberProduct π (m + 2)) :
    letI := iteratedFiberProductChartedSpace hn hπ (m + 1)
    letI := iteratedFiberProductChartedSpace hn hπ m
    haveI := isManifold_iteratedFiberProduct hn hπ m
    letI := transverseFiberProductChartedSpace hn
      (contMDiff_baseProj hn hπ (m := m) le_rfl) hπ.contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_right hn hπ p)
    (iteratedFiberProductStepDiffeomorph hn hπ m y).val.2 =
      IteratedFiberProduct.eval (Fin.last (m + 1)) y := (rfl)

/-- The underlying tuple of `(iteratedFiberProductStepDiffeomorph hn hπ m).symm p` appends `p.1.2`
to `p.1.1` via `Fin.snoc`. -/
@[simp]
theorem coe_iteratedFiberProductStepDiffeomorph_symm (m : ℕ)
    (p : {p : IteratedFiberProduct π (m + 1) × Y // IteratedFiberProduct.baseProj p.1 = π p.2}) :
    letI := iteratedFiberProductChartedSpace hn hπ (m + 1)
    letI := iteratedFiberProductChartedSpace hn hπ m
    haveI := isManifold_iteratedFiberProduct hn hπ m
    letI := transverseFiberProductChartedSpace hn
      (contMDiff_baseProj hn hπ (m := m) le_rfl) hπ.contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_right hn hπ p)
    ((iteratedFiberProductStepDiffeomorph hn hπ m).symm p : Fin (m + 2) → Y) =
      Fin.snoc p.val.1.val p.val.2 := (rfl)

/-- The inverse of `iteratedFiberProductStepDiffeomorph` evaluates via `Fin.snoc`. -/
theorem eval_iteratedFiberProductStepDiffeomorph_symm (m : ℕ)
    (p : {p : IteratedFiberProduct π (m + 1) × Y // IteratedFiberProduct.baseProj p.1 = π p.2})
    (i : Fin (m + 2)) :
    letI := iteratedFiberProductChartedSpace hn hπ (m + 1)
    letI := iteratedFiberProductChartedSpace hn hπ m
    haveI := isManifold_iteratedFiberProduct hn hπ m
    letI := transverseFiberProductChartedSpace hn
      (contMDiff_baseProj hn hπ (m := m) le_rfl) hπ.contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_right hn hπ p)
    IteratedFiberProduct.eval i ((iteratedFiberProductStepDiffeomorph hn hπ m).symm p) =
      Fin.snoc (α := fun _ ↦ Y) p.val.1.val p.val.2 i := (rfl)

/-- **Independence of the order of iteration.** Splitting an `(m₁ + m₂ + 2)`-tuple into its first
`m₁ + 1` and last `m₂ + 1` coordinates defines a `C^n` diffeomorphism from
`IteratedFiberProduct π (m₁ + m₂ + 2)` onto the binary transverse fibre product of
`IteratedFiberProduct π (m₁ + 1)` and `IteratedFiberProduct π (m₂ + 1)` over `M`. In particular,
left iteration (`m₁ = 0`), right iteration (`m₂ = 0`), and arbitrary parenthesizations produce
canonically diffeomorphic manifolds. -/
noncomputable def iteratedFiberProductSplitDiffeomorph (m₁ m₂ : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ m₁
    letI := iteratedFiberProductChartedSpace hn hπ m₂
    letI := iteratedFiberProductChartedSpace hn hπ (m₁ + m₂ + 1)
    haveI := isManifold_iteratedFiberProduct hn hπ m₁
    haveI := isManifold_iteratedFiberProduct hn hπ m₂
    letI := transverseFiberProductChartedSpace hn
      (contMDiff_baseProj hn hπ (m := m₁) le_rfl) (contMDiff_baseProj hn hπ (m := m₂) le_rfl)
      (fun p _ ↦ transverse_of_isSubmersion_right hn (isSubmersion_baseProj hn hπ m₂) p)
    IteratedFiberProduct π (m₁ + m₂ + 2) ≃ₘ^n⟮
      𝓘(ℝ, Fin ((m₁ + m₂ + 2) * finrank ℝ EY - (m₁ + m₂ + 1) * finrank ℝ EM) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ (Fin ((m₁ + 1) * finrank ℝ EY - m₁ * finrank ℝ EM) → ℝ) +
        finrank ℝ (Fin ((m₂ + 1) * finrank ℝ EY - m₂ * finrank ℝ EM) → ℝ) -
        finrank ℝ EM) → ℝ)⟯
      {p : IteratedFiberProduct π (m₁ + 1) × IteratedFiberProduct π (m₂ + 1) //
        IteratedFiberProduct.baseProj p.1 = IteratedFiberProduct.baseProj p.2} := by
  letI := iteratedFiberProductChartedSpace hn hπ m₁
  letI := iteratedFiberProductChartedSpace hn hπ m₂
  letI := iteratedFiberProductChartedSpace hn hπ (m₁ + m₂ + 1)
  haveI := isManifold_iteratedFiberProduct hn hπ m₁
  haveI := isManifold_iteratedFiberProduct hn hπ m₂
  letI := transverseFiberProductChartedSpace hn
    (contMDiff_baseProj hn hπ (m := m₁) le_rfl) (contMDiff_baseProj hn hπ (m := m₂) le_rfl)
    (fun p _ ↦ transverse_of_isSubmersion_right hn (isSubmersion_baseProj hn hπ m₂) p)
  have hemb := isSmoothEmbedding_coe_transverseFiberProduct hn
    (contMDiff_baseProj hn hπ (m := m₁) le_rfl) (contMDiff_baseProj hn hπ (m := m₂) le_rfl)
    (fun p _ ↦ transverse_of_isSubmersion_right hn (isSubmersion_baseProj hn hπ m₂) p)
  let castEquiv : Fin ((m₁ + 1) + (m₂ + 1)) ≃ Fin (m₁ + m₂ + 2) := finCongr (by omega)
  refine
    { toFun := fun y ↦
        ⟨(⟨fun i ↦ y.val (castEquiv (Fin.castAdd (m₂ + 1) i)), fun _ _ ↦ y.property _ _⟩,
          ⟨fun j ↦ y.val (castEquiv (Fin.natAdd (m₁ + 1) j)), fun _ _ ↦ y.property _ _⟩),
              y.property _ _⟩
      invFun := fun p ↦
        ⟨fun k ↦ Fin.append p.val.1.val p.val.2.val (castEquiv.symm k), by
          have hbase : ∀ r : Fin ((m₁ + 1) + (m₂ + 1)),
              π (Fin.append p.val.1.val p.val.2.val r) = IteratedFiberProduct.baseProj p.val.1
                  := fun r ↦ by
            induction r using Fin.addCases with
            | left i =>
              rw [Fin.append_left]
              exact (IteratedFiberProduct.baseProj_eq_apply p.val.1 i).symm
            | right j =>
              rw [Fin.append_right]
              exact (IteratedFiberProduct.baseProj_eq_apply p.val.2 j).symm.trans p.property.symm
          exact fun _ _ ↦ (hbase _).trans (hbase _).symm⟩
      left_inv := fun y ↦ Subtype.ext (funext fun k ↦ by
        obtain ⟨r, rfl⟩ := castEquiv.surjective k
        dsimp only
        rw [Equiv.symm_apply_apply]
        induction r using Fin.addCases with
        | left i => rw [Fin.append_left]
        | right j => rw [Fin.append_right])
      right_inv := fun p ↦ Subtype.ext <| Prod.ext
        (Subtype.ext (funext fun _ ↦ by simp only [Equiv.symm_apply_apply, Fin.append_left]))
        (Subtype.ext (funext fun _ ↦ by simp only [Equiv.symm_apply_apply, Fin.append_right]))
      contMDiff_toFun := hemb.contMDiff_iff_comp.2 <|
        ((contMDiff_iteratedFiberProduct_iff hn hπ le_rfl).2 fun i ↦
          contMDiff_eval hn hπ le_rfl (castEquiv (Fin.castAdd (m₂ + 1) i))).prodMk
        ((contMDiff_iteratedFiberProduct_iff hn hπ le_rfl).2 fun j ↦
          contMDiff_eval hn hπ le_rfl (castEquiv (Fin.natAdd (m₁ + 1) j)))
      contMDiff_invFun := (contMDiff_iteratedFiberProduct_iff hn hπ le_rfl).2 fun k ↦ by
        obtain ⟨r, rfl⟩ := castEquiv.surjective k
        simp only [IteratedFiberProduct.eval_apply, Equiv.coe_fn_symm_mk, Equiv.symm_apply_apply]
        induction r using Fin.addCases with
        | left i =>
          simp only [Fin.append_left]
          exact (contMDiff_eval hn hπ le_rfl i).comp hemb.contMDiff.fst
        | right j =>
          simp only [Fin.append_right]
          exact (contMDiff_eval hn hπ le_rfl j).comp hemb.contMDiff.snd }

/-- The underlying tuple of the first factor of `iteratedFiberProductSplitDiffeomorph` reads the
left block of indices. -/
@[simp]
theorem coe_fst_iteratedFiberProductSplitDiffeomorph (m₁ m₂ : ℕ)
    (y : IteratedFiberProduct π (m₁ + m₂ + 2)) :
    letI := iteratedFiberProductChartedSpace hn hπ m₁
    letI := iteratedFiberProductChartedSpace hn hπ m₂
    letI := iteratedFiberProductChartedSpace hn hπ (m₁ + m₂ + 1)
    haveI := isManifold_iteratedFiberProduct hn hπ m₁
    haveI := isManifold_iteratedFiberProduct hn hπ m₂
    letI := transverseFiberProductChartedSpace hn
      (contMDiff_baseProj hn hπ (m := m₁) le_rfl) (contMDiff_baseProj hn hπ (m := m₂) le_rfl)
      (fun p _ ↦ transverse_of_isSubmersion_right hn (isSubmersion_baseProj hn hπ m₂) p)
    ((iteratedFiberProductSplitDiffeomorph hn hπ m₁ m₂ y).val.1 : Fin (m₁ + 1) → Y) =
      fun i ↦ y.val (finCongr (by omega) (Fin.castAdd (m₂ + 1) i)) := (rfl)

/-- The first factor of `iteratedFiberProductSplitDiffeomorph` evaluates at the left block of
indices. -/
theorem eval_fst_iteratedFiberProductSplitDiffeomorph (m₁ m₂ : ℕ)
    (y : IteratedFiberProduct π (m₁ + m₂ + 2)) (i : Fin (m₁ + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ m₁
    letI := iteratedFiberProductChartedSpace hn hπ m₂
    letI := iteratedFiberProductChartedSpace hn hπ (m₁ + m₂ + 1)
    haveI := isManifold_iteratedFiberProduct hn hπ m₁
    haveI := isManifold_iteratedFiberProduct hn hπ m₂
    letI := transverseFiberProductChartedSpace hn
      (contMDiff_baseProj hn hπ (m := m₁) le_rfl) (contMDiff_baseProj hn hπ (m := m₂) le_rfl)
      (fun p _ ↦ transverse_of_isSubmersion_right hn (isSubmersion_baseProj hn hπ m₂) p)
    IteratedFiberProduct.eval i (iteratedFiberProductSplitDiffeomorph hn hπ m₁ m₂ y).val.1 =
      IteratedFiberProduct.eval (finCongr (by omega) (Fin.castAdd (m₂ + 1) i)) y := (rfl)

/-- The underlying tuple of the second factor of `iteratedFiberProductSplitDiffeomorph` reads the
right block of indices. -/
@[simp]
theorem coe_snd_iteratedFiberProductSplitDiffeomorph (m₁ m₂ : ℕ)
    (y : IteratedFiberProduct π (m₁ + m₂ + 2)) :
    letI := iteratedFiberProductChartedSpace hn hπ m₁
    letI := iteratedFiberProductChartedSpace hn hπ m₂
    letI := iteratedFiberProductChartedSpace hn hπ (m₁ + m₂ + 1)
    haveI := isManifold_iteratedFiberProduct hn hπ m₁
    haveI := isManifold_iteratedFiberProduct hn hπ m₂
    letI := transverseFiberProductChartedSpace hn
      (contMDiff_baseProj hn hπ (m := m₁) le_rfl) (contMDiff_baseProj hn hπ (m := m₂) le_rfl)
      (fun p _ ↦ transverse_of_isSubmersion_right hn (isSubmersion_baseProj hn hπ m₂) p)
    ((iteratedFiberProductSplitDiffeomorph hn hπ m₁ m₂ y).val.2 : Fin (m₂ + 1) → Y) =
      fun j ↦ y.val (finCongr (by omega) (Fin.natAdd (m₁ + 1) j)) := (rfl)

/-- The second factor of `iteratedFiberProductSplitDiffeomorph` evaluates at the right block of
indices. -/
theorem eval_snd_iteratedFiberProductSplitDiffeomorph (m₁ m₂ : ℕ)
    (y : IteratedFiberProduct π (m₁ + m₂ + 2)) (j : Fin (m₂ + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ m₁
    letI := iteratedFiberProductChartedSpace hn hπ m₂
    letI := iteratedFiberProductChartedSpace hn hπ (m₁ + m₂ + 1)
    haveI := isManifold_iteratedFiberProduct hn hπ m₁
    haveI := isManifold_iteratedFiberProduct hn hπ m₂
    letI := transverseFiberProductChartedSpace hn
      (contMDiff_baseProj hn hπ (m := m₁) le_rfl) (contMDiff_baseProj hn hπ (m := m₂) le_rfl)
      (fun p _ ↦ transverse_of_isSubmersion_right hn (isSubmersion_baseProj hn hπ m₂) p)
    IteratedFiberProduct.eval j (iteratedFiberProductSplitDiffeomorph hn hπ m₁ m₂ y).val.2 =
      IteratedFiberProduct.eval (finCongr (by omega) (Fin.natAdd (m₁ + 1) j)) y := (rfl)

/-- The underlying tuple of `(iteratedFiberProductSplitDiffeomorph hn hπ m₁ m₂).symm p`
concatenates the two tuples via `Fin.append`. -/
@[simp]
theorem coe_iteratedFiberProductSplitDiffeomorph_symm (m₁ m₂ : ℕ)
    (p : {p : IteratedFiberProduct π (m₁ + 1) × IteratedFiberProduct π (m₂ + 1) //
      IteratedFiberProduct.baseProj p.1 = IteratedFiberProduct.baseProj p.2}) :
    letI := iteratedFiberProductChartedSpace hn hπ m₁
    letI := iteratedFiberProductChartedSpace hn hπ m₂
    letI := iteratedFiberProductChartedSpace hn hπ (m₁ + m₂ + 1)
    haveI := isManifold_iteratedFiberProduct hn hπ m₁
    haveI := isManifold_iteratedFiberProduct hn hπ m₂
    letI := transverseFiberProductChartedSpace hn
      (contMDiff_baseProj hn hπ (m := m₁) le_rfl) (contMDiff_baseProj hn hπ (m := m₂) le_rfl)
      (fun p _ ↦ transverse_of_isSubmersion_right hn (isSubmersion_baseProj hn hπ m₂) p)
    ((iteratedFiberProductSplitDiffeomorph hn hπ m₁ m₂).symm p : Fin (m₁ + m₂ + 2) → Y) =
      fun k ↦ Fin.append p.val.1.val p.val.2.val ((finCongr (by omega)).symm k) := (rfl)

/-- The inverse of `iteratedFiberProductSplitDiffeomorph` concatenates the two tuples via
`Fin.append`. -/
theorem eval_iteratedFiberProductSplitDiffeomorph_symm (m₁ m₂ : ℕ)
    (p : {p : IteratedFiberProduct π (m₁ + 1) × IteratedFiberProduct π (m₂ + 1) //
      IteratedFiberProduct.baseProj p.1 = IteratedFiberProduct.baseProj p.2})
    (k : Fin (m₁ + m₂ + 2)) :
    letI := iteratedFiberProductChartedSpace hn hπ m₁
    letI := iteratedFiberProductChartedSpace hn hπ m₂
    letI := iteratedFiberProductChartedSpace hn hπ (m₁ + m₂ + 1)
    haveI := isManifold_iteratedFiberProduct hn hπ m₁
    haveI := isManifold_iteratedFiberProduct hn hπ m₂
    letI := transverseFiberProductChartedSpace hn
      (contMDiff_baseProj hn hπ (m := m₁) le_rfl) (contMDiff_baseProj hn hπ (m := m₂) le_rfl)
      (fun p _ ↦ transverse_of_isSubmersion_right hn (isSubmersion_baseProj hn hπ m₂) p)
    IteratedFiberProduct.eval k ((iteratedFiberProductSplitDiffeomorph hn hπ m₁ m₂).symm p) =
      Fin.append p.val.1.val p.val.2.val ((finCongr (by omega)).symm k) := (rfl)

end ChosenAtlas

/-- For the identity submersion `id : M → M`, every iterated fibre product
`IteratedFiberProduct id (m + 1)` is `C^n` diffeomorphic to `M` of dimension
`(m + 1) * dim M - m * dim M = dim M`. -/
noncomputable def iteratedFiberProductIdDiffeomorph (hn : 1 ≤ n) (m : ℕ) :
    letI := iteratedFiberProductChartedSpace hn
      (Manifold.IsSubmersion.id (I := IM) (n := n) (M := M)) m
    IteratedFiberProduct (id : M → M) (m + 1) ≃ₘ^n⟮
      𝓘(ℝ, Fin ((m + 1) * finrank ℝ EM - m * finrank ℝ EM) → ℝ), IM⟯ M := by
  let h_id := Manifold.IsSubmersion.id (I := IM) (n := n) (M := M)
  letI := iteratedFiberProductChartedSpace hn h_id m
  exact
    { toFun := IteratedFiberProduct.baseProj
      invFun := IteratedFiberProduct.const (m + 1)
      left_inv := fun y ↦ Subtype.ext (funext fun i ↦ (y.property 0 i))
      right_inv := fun _ ↦ rfl
      contMDiff_toFun := contMDiff_baseProj hn h_id le_rfl
      contMDiff_invFun := contMDiff_const hn h_id le_rfl }

/-- `iteratedFiberProductIdDiffeomorph` acts by `IteratedFiberProduct.baseProj`. -/
@[simp]
theorem iteratedFiberProductIdDiffeomorph_apply (hn : 1 ≤ n) (m : ℕ)
    (y : IteratedFiberProduct (id : M → M) (m + 1)) :
    letI := iteratedFiberProductChartedSpace hn
      (Manifold.IsSubmersion.id (I := IM) (n := n) (M := M)) m
    iteratedFiberProductIdDiffeomorph (IM := IM) hn m y = IteratedFiberProduct.baseProj y := (rfl)

/-- The inverse of `iteratedFiberProductIdDiffeomorph` is the constant diagonal `const (m + 1)`. -/
@[simp]
theorem iteratedFiberProductIdDiffeomorph_symm_apply (hn : 1 ≤ n) (m : ℕ) (x : M) :
    letI := iteratedFiberProductChartedSpace hn
      (Manifold.IsSubmersion.id (I := IM) (n := n) (M := M)) m
    (iteratedFiberProductIdDiffeomorph (IM := IM) hn m).symm x =
      IteratedFiberProduct.const (m + 1) x := (rfl)

end Manifold

end TauCeti
