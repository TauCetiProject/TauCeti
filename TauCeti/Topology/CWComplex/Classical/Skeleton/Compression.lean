/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Subcomplex
public import TauCeti.Analysis.Convex.RadialPush
public import TauCeti.Analysis.Normed.Module.Ball.Retraction
public import TauCeti.Topology.CWComplex.Classical.CompactSupport
public import TauCeti.Topology.CWComplex.Classical.OpenCells
public import TauCeti.Topology.CWComplex.Classical.Quotient
public import TauCeti.Topology.CWComplex.Classical.Skeleton.Basic
public import TauCeti.Topology.Homotopy.AvoidPoint
public import TauCeti.Topology.Homotopy.HomotopicRel

/-!
# Compressing maps of low-dimensional compacta into skeleta

Let `C` be a relative CW complex in a Hausdorff space `X`, and write `Xᵏ = skeletonLT C (k + 1)`
for its `k`-skeleton. Let `K` be a compact subset of a finite-dimensional real normed space `E`.
This file proves that maps `K → X` can be pushed off the cells of dimension greater than
`dim E`:

* If `dim E < k` and `f : K → X` lands in `Xᵏ`, then for every `k`-cell `j`, `f` is homotopic,
  relative to the points not sent into the open cell `j`, to a map sending those points into the
  frontier of `j` (`TauCeti.exists_homotopicRel_cellFrontier`). This is Hatcher's Lemma 4.10.
* Doing this for the finitely many `k`-cells that the compact image of `f` meets compresses `f`
  into `Xᵏ⁻¹`, relative to the points already sent there
  (`TauCeti.exists_homotopicRel_skeletonLT`).
* Since the image of `f` lies in some finite skeleton, every map `f : K → X` into the complex is
  homotopic, relative to the points sent into `Xⁿ` with `n = dim E`, to a map into `Xⁿ`
  (`TauCeti.exists_homotopicRel_skeletonLT_finrank`). Applied to a closed `i`-ball with `i ≤ n`,
  placed in an `n`-dimensional space, it homotopes every map of pairs `(Dⁱ, Sⁱ⁻¹) → (X, Xⁿ)`
  relative to `Sⁱ⁻¹` into `Xⁿ`; this is the compression property behind Hatcher's
  Corollary 4.12, that the pair `(X, Xⁿ)` is `n`-connected.

These are the steps of the cellular approximation theorem that concern a single cell of the
domain; the theorem itself follows from them by induction over the cells of the domain using the
homotopy extension property.

To push a map off a `k`-cell, read the open cell, which is open in `Xᵏ`, as a chart through the
inverse of its characteristic map. `ContinuousMap.exists_homotopyRel_notMem_range` homotopes the
map off one point `p` of the open cell, and, the image being compact, off a small ball around
`p`. The radial deformation of the closed unit ball away from `p` onto the unit sphere
(`Convex.exists_homotopyRel_frontier`), read through the characteristic map, is a homotopy of
`Xᵏ` that is supported in the open cell and ends by pushing the rest of the cell onto its
frontier.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Lemma 4.10, Theorem 4.8 and Corollary 4.12.
-/

public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex unitInterval Module

universe u

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D] {k : ℕ}

/-- The inverse of the characteristic map of a `k`-cell, as a chart of the `k`-skeleton whose
source is the open cell and whose target is the open unit ball. Outside the closed unit ball the
inverse chart is extended by the radial retraction. -/
private def openCellChart (j : cell C k) :
    OpenPartialHomeomorph (skeletonLT C ((k + 1 : ℕ) : ℕ∞) : Set X) (Fin k → ℝ) where
  toFun x := (map k j).symm x
  invFun y := ⟨map k j (radialRetraction 1 y), map_mem_skeletonLT_succ j <| by
    rw [norm_radialRetraction zero_le_one]
    exact min_le_right _ _⟩
  source := Subtype.val ⁻¹' openCell k j
  target := ball 0 1
  map_source' x hx := map_symm_mem_ball k hx
  map_target' y hy := by
    rw [mem_preimage, Subtype.coe_mk, radialRetraction_of_norm_le (mem_ball_zero_iff.1 hy).le]
    exact ⟨y, hy, rfl⟩
  left_inv' x hx := Subtype.ext <| by
    rw [Subtype.coe_mk,
      radialRetraction_of_norm_le (mem_ball_zero_iff.1 (map_symm_mem_ball k hx)).le]
    exact map_map_symm k hx
  right_inv' y hy := by
    rw [Subtype.coe_mk, radialRetraction_of_norm_le (mem_ball_zero_iff.1 hy).le]
    exact (map k j).left_inv (by rwa [source_eq])
  open_source := isOpen_preimage_val_openCell k Subset.rfl j
  open_target := isOpen_ball
  continuousOn_toFun := (continuousOn_symm k j).comp continuous_subtype_val.continuousOn
    fun x hx ↦ by rwa [target_map_eq_openCell]
  continuousOn_invFun := Continuous.continuousOn <| Continuous.subtype_mk
    ((continuousOn k j).comp_continuous (lipschitzWith_radialRetraction zero_le_one).continuous
      fun y ↦ radialRetraction_mem_closedBall zero_le_one y) _

private lemma openCellChart_apply (j : cell C k) (x : (skeletonLT C ((k + 1 : ℕ) : ℕ∞) : Set X)) :
    openCellChart j x = (map k j).symm x :=
  rfl

/-- The image of the target of `openCellChart j` under its inverse is the open cell `j`. -/
private lemma openCellChart_symm_image_target (j : cell C k) :
    (openCellChart j).symm '' ball 0 1 = Subtype.val ⁻¹' openCell k j :=
  (openCellChart j).symm_image_target_eq_source

/-- The deformation of the `k`-skeleton obtained from a deformation `Ψ` of the closed unit ball
by reading it through the characteristic map of the `k`-cell `j`, at time `t`: a point of the open
cell `j` moves by `Ψ`, and every other point is fixed. -/
private def cellPushVal (j : cell C k) (Ψ : C(I × (Fin k → ℝ), Fin k → ℝ)) (q : I × X) : X :=
  open Classical in
  if q.2 ∈ openCell k j then map k j (Ψ (q.1, (map k j).symm q.2)) else q.2

omit [T2Space X] in
private lemma cellPushVal_of_notMem {j : cell C k} {Ψ : C(I × (Fin k → ℝ), Fin k → ℝ)} {t : I}
    {x : X} (hx : x ∉ openCell k j) : cellPushVal j Ψ (t, x) = x := by
  simp [cellPushVal, hx]

omit [T2Space X] in
private lemma cellPushVal_of_mem {j : cell C k} {Ψ : C(I × (Fin k → ℝ), Fin k → ℝ)} {t : I}
    {x : X} (hx : x ∈ openCell k j) :
    cellPushVal j Ψ (t, x) = map k j (Ψ (t, (map k j).symm x)) := by
  simp [cellPushVal, hx]

/-- Through the characteristic map of `j`, the deformation of the skeleton is `Ψ`, provided `Ψ`
fixes the unit sphere. -/
private lemma cellPushVal_map {j : cell C k} {Ψ : C(I × (Fin k → ℝ), Fin k → ℝ)}
    (hΨ : ∀ t y, ‖y‖ = 1 → Ψ (t, y) = y) (t : I) {y : Fin k → ℝ} (hy : ‖y‖ ≤ 1) :
    cellPushVal j Ψ (t, map k j y) = map k j (Ψ (t, y)) := by
  rcases hy.lt_or_eq with hy | hy
  · have hmem : y ∈ (map k j).source := by rwa [source_eq, mem_ball_zero_iff]
    rw [cellPushVal_of_mem ⟨y, mem_ball_zero_iff.2 hy, rfl⟩, (map k j).left_inv hmem]
  · -- A point of the boundary sphere lands in the frontier of the cell, outside the open cell.
    rw [hΨ t y hy, cellPushVal_of_notMem fun h ↦
      (disjoint_skeletonLT_openCell le_rfl).notMem_of_mem_right h
        (cellFrontier_subset_skeletonLT k j ⟨y, mem_sphere_zero_iff_norm.2 hy, rfl⟩)]

private lemma continuous_cellPushVal (j : cell C k) {Ψ : C(I × (Fin k → ℝ), Fin k → ℝ)}
    (hΨ : ∀ t y, ‖y‖ = 1 → Ψ (t, y) = y) (hΨb : ∀ t y, ‖y‖ ≤ 1 → ‖Ψ (t, y)‖ ≤ 1) :
    Continuous fun q : I × (skeletonLT C ((k + 1 : ℕ) : ℕ∞) : Set X) ↦
      cellPushVal j Ψ (q.1, q.2) := by
  rw [continuous_prod_complex_iff]
  refine ⟨fun m ⟨i, hi⟩ ↦ ?_, ?_⟩
  · have hm : m ≤ k := Nat.lt_succ_iff.1 (by
      simpa only [RelCWComplex.skeletonLT_I, mem_ofPred_eq, Nat.cast_lt] using hi)
    by_cases hij : (⟨m, i⟩ : Σ n, cell C n) = ⟨k, j⟩
    · -- On the cell `j` the deformation is `Ψ`, read through the characteristic map.
      obtain ⟨rfl, hij⟩ := Sigma.mk.inj_iff.1 hij
      obtain rfl := eq_of_heq hij
      refine ((continuousOn m i).comp_continuous (Ψ.continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
        fun q ↦ mem_closedBall_zero_iff.2 (hΨb _ _ (mem_closedBall_zero_iff.1 q.2.2))).congr
        fun q ↦ ?_
      exact (cellPushVal_map hΨ q.1 (mem_closedBall_zero_iff.1 q.2.2)).symm
    · -- Every other cell of the skeleton misses the open cell `j`, and is fixed.
      refine ((continuousOn m i).comp_continuous (continuous_subtype_val.comp continuous_snd)
        fun q ↦ q.2.2).congr fun q ↦ (cellPushVal_of_notMem ?_).symm
      exact (disjoint_closedCell_openCell_of_ne k hm hij).notMem_of_mem_left ⟨q.2, q.2.2, rfl⟩
  · -- The base lies in the `(k-1)`-skeleton, which misses the open cell `j`.
    refine (continuous_subtype_val.comp continuous_snd).congr fun q ↦
      (cellPushVal_of_notMem ?_).symm
    exact (disjoint_skeletonLT_openCell le_rfl).notMem_of_mem_left
      ((skeletonLT C k).base_subset q.2.2)

private lemma cellPushVal_mem {j : cell C k} {Ψ : C(I × (Fin k → ℝ), Fin k → ℝ)}
    (hΨb : ∀ t y, ‖y‖ ≤ 1 → ‖Ψ (t, y)‖ ≤ 1) (t : I) {x : X}
    (hx : x ∈ (skeletonLT C ((k + 1 : ℕ) : ℕ∞) : Set X)) :
    cellPushVal j Ψ (t, x) ∈ (skeletonLT C ((k + 1 : ℕ) : ℕ∞) : Set X) := by
  by_cases hxj : x ∈ openCell k j
  · rw [cellPushVal_of_mem hxj]
    exact map_mem_skeletonLT_succ j (hΨb _ _ (mem_ball_zero_iff.1 (map_symm_mem_ball k hxj)).le)
  · rwa [cellPushVal_of_notMem hxj]

/-- **A deformation of the closed unit ball fixing the unit sphere, read through the
characteristic map of a `k`-cell `j`, deforms maps into the `k`-skeleton relative to the points
not sent into the open cell `j`.** A point `z` sent into the open cell, at `map k j y`, ends at
`map k j (g y)`. -/
private lemma exists_homotopicRel_openCell (j : cell C k) {g : C(Fin k → ℝ, Fin k → ℝ)}
    (Ψ : (ContinuousMap.id _).HomotopyRel g (frontier (closedBall 0 1)))
    (hΨb : ∀ t y, ‖y‖ ≤ 1 → ‖Ψ (t, y)‖ ≤ 1) {Z : Type*} [TopologicalSpace Z]
    (f : C(Z, (skeletonLT C ((k + 1 : ℕ) : ℕ∞) : Set X))) {S : Set Z}
    (hS : ∀ z ∈ S, (f z : X) ∉ openCell k j) :
    ∃ f' : C(Z, (skeletonLT C ((k + 1 : ℕ) : ℕ∞) : Set X)), f.HomotopicRel f' S ∧
      (∀ z, (f z : X) ∈ openCell k j → (f' z : X) = map k j (g ((map k j).symm (f z)))) ∧
      ∀ z, (f z : X) ∉ openCell k j → f' z = f z := by
  have hΨ (t : I) (y : Fin k → ℝ) (hy : ‖y‖ = 1) : Ψ (t, y) = y :=
    Ψ.eq_fst t (frontier_closedBall (0 : Fin k → ℝ) one_ne_zero ▸ mem_sphere_zero_iff_norm.2 hy)
  let Q : C(I × Z, (skeletonLT C ((k + 1 : ℕ) : ℕ∞) : Set X)) :=
    ⟨fun q ↦ ⟨cellPushVal j Ψ.toContinuousMap (q.1, f q.2), cellPushVal_mem hΨb q.1 (f q.2).2⟩,
      ((continuous_cellPushVal j hΨ hΨb).comp
        (continuous_fst.prodMk (f.continuous.comp continuous_snd))).subtype_mk _⟩
  have hQ (q : I × Z) : (Q q : X) = cellPushVal j Ψ.toContinuousMap (q.1, f q.2) := rfl
  have h0 (z : Z) : Q (0, z) = f z := by
    refine Subtype.ext ?_
    by_cases hz : (f z : X) ∈ openCell k j
    · -- At time `0` the deformation `Ψ` is the identity.
      rw [hQ, cellPushVal_of_mem hz, ContinuousMap.HomotopyWith.coe_toContinuousMap,
        Ψ.apply_zero, ContinuousMap.id_apply, map_map_symm k hz]
    · exact cellPushVal_of_notMem hz
  refine ⟨Q.curry 1, ⟨⟨⟨Q, h0, fun _ ↦ rfl⟩, fun t z hz ↦ Subtype.ext ?_⟩⟩, fun z hz ↦ ?_,
    fun z hz ↦ Subtype.ext ?_⟩
  · exact cellPushVal_of_notMem (hS z hz)
  · rw [ContinuousMap.curry_apply, hQ, cellPushVal_of_mem hz,
      ContinuousMap.HomotopyWith.coe_toContinuousMap, Ψ.apply_one]
  · exact cellPushVal_of_notMem hz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Pushing a map off a cell of higher dimension** (Hatcher, Lemma 4.10). Let `K` be a compact
subset of a real normed space of dimension less than `k`, and let `f : K → X` land in the
`k`-skeleton `skeletonLT C (k + 1)`. For every `k`-cell `j`, `f` is homotopic, relative to the
points that `f` does not send into the open cell `j`, to a map sending the points that `f` sends
into the open cell `j` into its frontier. -/
theorem exists_homotopicRel_cellFrontier {K : Set E} (hK : IsCompact K) (hk : finrank ℝ E < k)
    (j : cell C k) (f : C(K, X)) (hf : ∀ x, f x ∈ (skeletonLT C ((k + 1 : ℕ) : ℕ∞) : Set X)) :
    ∃ g : C(K, X), f.HomotopicRel g (f ⁻¹' openCell k j)ᶜ ∧
      ∀ x, f x ∈ openCell k j → g x ∈ cellFrontier k j := by
  let f' : C(K, (skeletonLT C ((k + 1 : ℕ) : ℕ∞) : Set X)) :=
    ⟨fun x ↦ ⟨f x, hf x⟩, f.continuous.subtype_mk hf⟩
  let φ := openCellChart (C := C) j
  -- First homotope `f` off a point `φ.symm p` of the open cell, keeping the open cell in itself.
  obtain ⟨g₁, ⟨H₁⟩, hg₁, p, hp, hpg₁⟩ := f'.exists_homotopyRel_notMem_range hK.isClosed
    (by rwa [Module.finrank_fin_fun]) φ one_pos Subset.rfl
  rw [openCellChart_symm_image_target] at H₁
  -- The image of `g₁` is compact, so `g₁` misses `φ.symm (ball p ε)` for some `ε > 0`.
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hU : IsOpen (φ.target ∩ φ.symm ⁻¹' (range g₁)ᶜ) :=
    φ.continuousOn_symm.isOpen_inter_preimage φ.open_target
      (isCompact_range g₁.continuous).isClosed.isOpen_compl
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU p ⟨hp, hpg₁⟩
  -- Then push the closed unit ball radially away from `p` onto the sphere.
  obtain ⟨ψ, Ψ, hΨs, hΨε⟩ := (convex_closedBall (0 : Fin k → ℝ) 1).exists_homotopyRel_frontier
    isClosed_closedBall isBounded_closedBall (by rwa [interior_closedBall _ one_ne_zero]) hε
  rw [frontier_closedBall _ one_ne_zero] at hΨε
  obtain ⟨g₂, hg₂, hg₂j, -⟩ := exists_homotopicRel_openCell j Ψ
    (fun t y hy ↦ mem_closedBall_zero_iff.1 (hΨs t y (mem_closedBall_zero_iff.2 hy))) g₁
    (S := (f ⁻¹' openCell k j)ᶜ) fun x hx ↦ (H₁.fst_eq_snd hx) ▸ hx
  let val : C((skeletonLT C ((k + 1 : ℕ) : ℕ∞) : Set X), X) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  have h := (ContinuousMap.HomotopicRel.trans ⟨H₁⟩ hg₂).comp_continuousMap val
  rw [show val.comp f' = f from ContinuousMap.ext fun _ ↦ rfl] at h
  refine ⟨val.comp g₂, h, fun x hx ↦ ?_⟩
  -- A point sent into the open cell is sent by `g₁` into the open cell, but outside
  -- `φ.symm (ball p ε)`, so the radial push sends it to the frontier.
  have hx₁ : (g₁ x : X) ∈ openCell k j := hg₁ x hx
  have hy := map_symm_mem_ball k hx₁
  have hyε : ε ≤ dist ((map k j).symm (g₁ x)) p := by
    by_contra! h
    refine (hεU (mem_ball.2 h)).2 ⟨x, ?_⟩
    rw [← openCellChart_apply]
    exact (φ.left_inv hx₁).symm
  rw [ContinuousMap.comp_apply, ContinuousMap.coe_mk, hg₂j x hx₁]
  exact ⟨_, hΨε _ (ball_subset_closedBall hy) hyε, rfl⟩

/-- **Compressing a map of a low-dimensional compactum into the next lower skeleton.** Let `K` be
a compact subset of a real normed space of dimension less than `k`. Every map `f : K → X` landing
in the `k`-skeleton `skeletonLT C (k + 1)` is homotopic, relative to the points that `f` sends
into the `(k-1)`-skeleton `skeletonLT C k`, to a map into `skeletonLT C k`. -/
theorem exists_homotopicRel_skeletonLT {K : Set E} (hK : IsCompact K) (hk : finrank ℝ E < k)
    (f : C(K, X)) (hf : ∀ x, f x ∈ (skeletonLT C ((k + 1 : ℕ) : ℕ∞) : Set X)) :
    ∃ g : C(K, X), f.HomotopicRel g (f ⁻¹' (skeletonLT C (k : ℕ∞) : Set X)) ∧
      ∀ x, g x ∈ (skeletonLT C (k : ℕ∞) : Set X) := by
  classical
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  -- The compact image of `f` meets only finitely many open `k`-cells.
  have hA : {j : cell C k | (range f ∩ openCell k j).Nonempty}.Finite :=
    (finite_setOf_nonempty_inter_openCell_of_isCompact (C := C)
      (isCompact_range f.continuous)).preimage (f := Sigma.mk k) sigma_mk_injective.injOn
  -- Push `f` off these cells one at a time, never entering an open `k`-cell that `f` misses.
  have key (T : Finset (cell C k)) : ∃ g : C(K, X),
      f.HomotopicRel g (f ⁻¹' (skeletonLT C (k : ℕ∞) : Set X)) ∧
      (∀ x, g x ∈ (skeletonLT C ((k + 1 : ℕ) : ℕ∞) : Set X)) ∧
      (∀ x, ∀ j ∈ T, g x ∉ openCell k j) ∧
      ∀ x (j : cell C k), g x ∈ openCell k j → f x ∈ openCell k j := by
    induction T using Finset.induction_on with
    | empty => exact ⟨f, .refl f, hf, by simp, fun _ _ h ↦ h⟩
    | insert j T _ ih =>
      obtain ⟨g, hfg, hg, hgT, hgf⟩ := ih
      obtain ⟨g₂, hgg₂, hg₂⟩ := exists_homotopicRel_cellFrontier hK hk j g hg
      have heq (x) (hx : g x ∉ openCell k j) : g₂ x = g x := (hgg₂.fst_eq_snd hx).symm
      have hskel (x) (hx : g x ∈ openCell k j) : g₂ x ∈ (skeletonLT C (k : ℕ∞) : Set X) :=
        cellFrontier_subset_skeletonLT k j (hg₂ x hx)
      have hnot (x) (hx : g x ∈ openCell k j) (i : cell C k) : g₂ x ∉ openCell k i :=
        (disjoint_skeletonLT_openCell le_rfl).notMem_of_mem_left (hskel x hx)
      refine ⟨g₂, hfg.trans (hgg₂.mono fun x hx hgx ↦ ?_), fun x ↦ ?_, fun x i hi ↦ ?_,
        fun x i hi ↦ ?_⟩
      · -- A point sent into `skeletonLT C k` is fixed by the first homotopy, so `g` sends it
        -- outside the open cell `j`.
        rw [mem_preimage, hfg.fst_eq_snd hx] at hx
        exact (disjoint_skeletonLT_openCell le_rfl).notMem_of_mem_left hx hgx
      · by_cases hx : g x ∈ openCell k j
        · exact skeletonLT_mono (by exact_mod_cast k.le_succ) (hskel x hx)
        · exact heq x hx ▸ hg x
      · by_cases hx : g x ∈ openCell k j
        · exact hnot x hx i
        · rw [heq x hx]
          rcases Finset.mem_insert.1 hi with rfl | hi
          exacts [hx, hgT x i hi]
      · by_cases hx : g x ∈ openCell k j
        · exact absurd hi (hnot x hx i)
        · exact hgf x i (heq x hx ▸ hi)
  -- After all of them, the map lies in no open `k`-cell.
  obtain ⟨g, hfg, hg, hgA, hgf⟩ := key hA.toFinset
  refine ⟨g, hfg, fun x ↦ mem_skeletonLT_of_forall_notMem_openCell k (hg x) fun j hj ↦ ?_⟩
  exact hgA x j (hA.mem_toFinset.2 ⟨f x, ⟨x, rfl⟩, hgf x j hj⟩) hj

/-- **Compressing a map of a compactum into the skeleton of its dimension**, the compression
step of Hatcher's Corollary 4.12. Let `K` be a compact subset of a real normed space of
dimension `n`. Every map `f : K → X` into the complex is homotopic, relative to the points that
`f` sends into the `n`-skeleton `skeletonLT C (n + 1)`, to a map into `skeletonLT C (n + 1)`. -/
theorem exists_homotopicRel_skeletonLT_finrank {K : Set E} (hK : IsCompact K) (f : C(K, X))
    (hf : ∀ x, f x ∈ C) :
    ∃ g : C(K, X), f.HomotopicRel g (f ⁻¹' (skeletonLT C ((finrank ℝ E + 1 : ℕ) : ℕ∞) : Set X)) ∧
      ∀ x, g x ∈ (skeletonLT C ((finrank ℝ E + 1 : ℕ) : ℕ∞) : Set X) := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  set n := finrank ℝ E
  -- The compact image of `f` lies in a finite skeleton; compress it one dimension at a time.
  obtain ⟨m, hm⟩ := exists_subset_skeletonLT_of_isCompact (C := C) (isCompact_range f.continuous)
    (range_subset_iff.2 hf)
  induction m generalizing f with
  | zero =>
    exact ⟨f, .refl f, fun x ↦ skeletonLT_mono (by exact_mod_cast Nat.zero_le _) (hm ⟨x, rfl⟩)⟩
  | succ m ih =>
    by_cases hmn : m + 1 ≤ n + 1
    · exact ⟨f, .refl f, fun x ↦ skeletonLT_mono (by exact_mod_cast hmn) (hm ⟨x, rfl⟩)⟩
    obtain ⟨g₁, hfg₁, hg₁⟩ := exists_homotopicRel_skeletonLT hK (by omega) f
      fun x ↦ hm ⟨x, rfl⟩
    obtain ⟨g, hg₁g, hg⟩ := ih g₁ (fun x ↦ (skeletonLT C m).subset_complex (hg₁ x))
      (range_subset_iff.2 hg₁)
    have hsub : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) ⊆ (skeletonLT C (m : ℕ∞) : Set X) :=
      skeletonLT_mono (by exact_mod_cast (by omega : n + 1 ≤ m))
    -- Points sent into `skeletonLT C (n + 1)` are fixed by the first compression.
    refine ⟨g, (hfg₁.mono fun x hx ↦ hsub hx).trans (hg₁g.mono fun x hx ↦ ?_), hg⟩
    rw [mem_preimage, ← hfg₁.fst_eq_snd (hsub hx)]
    exact hx

end TauCeti
