/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.RadialPush
public import TauCeti.Topology.CWComplex.Classical.CompactSupport
public import TauCeti.Topology.CWComplex.Classical.Skeleton.CellDeformation
public import TauCeti.Topology.Homotopy.AvoidPoint
public import TauCeti.Topology.Homotopy.Homotopic.Rel

/-!
# Compressing maps of low-dimensional compacta into skeleta

Let `C` be a relative CW complex in a Hausdorff space `X`, and write `Xᵏ = skeletonLT C (k + 1)`
for its `k`-skeleton. Let `K` be a compact subset of a finite-dimensional real normed space `E`.
This file proves that maps `K → C` into the complex can be pushed off the cells of dimension
greater than `dim E`, by homotopies of maps into the complex:

* If `dim E < k` and `f : K → C` lands in `Xᵏ`, then for every `k`-cell `j`, `f` is homotopic,
  relative to the points not sent into the open cell `j`, to a map sending the points that `f`
  sends into the open cell `j` into its frontier (`TauCeti.exists_homotopicRel_cellFrontier`).
  This is Hatcher's Lemma 4.10 together with the radial push from the proof of Theorem 4.8.
* Doing this for the finitely many `k`-cells that the compact image of `f` meets compresses `f`
  into `Xᵏ⁻¹`, relative to the points already sent there
  (`TauCeti.exists_homotopicRel_skeletonLT`).
* Since the image of `f` lies in some finite skeleton, every map `f : K → C` into the complex is
  homotopic, relative to the points sent into `Xⁿ` with `dim E ≤ n`, to a map into `Xⁿ`
  (`TauCeti.exists_homotopicRel_skeletonLT_finrank`). Applied to a closed `i`-ball with `i ≤ n`,
  it homotopes every map of pairs `(Dⁱ, Sⁱ⁻¹) → (C, Xⁿ)` relative to `Sⁱ⁻¹` into `Xⁿ`; this is
  the compression property behind Hatcher's Corollary 4.12, that the pair `(C, Xⁿ)` is
  `n`-connected.

These are the steps of the cellular approximation theorem that concern a single cell of the
domain; the theorem itself (`TauCeti.exists_isCellular_homotopicRel`) follows from them by
induction over the skeleta of the domain using the homotopy extension property.

To push a map off a `k`-cell, read the open cell, which is open in `Xᵏ`, as a chart through the
inverse of its characteristic map (`TauCeti.openCellChart`).
`ContinuousMap.exists_homotopyRel_notMem_range` homotopes the map off one point `p` of the open
cell, and, the image being compact, off a small ball around `p`. The radial deformation of the
closed unit ball away from `p` onto the unit sphere (`Convex.exists_homotopyRel_frontier`), read
through the characteristic map (`TauCeti.cellDeformation`), is a homotopy of `Xᵏ` that is
supported in the open cell and ends by pushing the rest of the cell onto its
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Pushing a map off a cell of higher dimension** (Hatcher, Lemma 4.10 together with the
radial push from the proof of Theorem 4.8). Let `K` be a compact subset of a real normed space
of dimension less than `k`, and let `f : K → C` land in the `k`-skeleton `skeletonLT C (k + 1)`.
For every `k`-cell `j`, `f` is homotopic as a map into `C`, relative to the points that `f` does
not send into the open cell `j`, to a map sending the points that `f` sends into the open cell `j`
into its frontier. -/
theorem exists_homotopicRel_cellFrontier {K : Set E} (hK : IsCompact K) (hk : finrank ℝ E < k)
    (j : cell C k) (f : C(K, C))
    (hf : ∀ x, (f x : X) ∈ (skeletonLT C ((k + 1 : ℕ) : ℕ∞) : Set X)) :
    ∃ g : C(K, C), f.HomotopicRel g {x | (f x : X) ∈ openCell k j}ᶜ ∧
      ∀ x, (f x : X) ∈ openCell k j → (g x : X) ∈ cellFrontier k j := by
  let f' : C(K, (skeletonLT C ((k + 1 : ℕ) : ℕ∞) : Set X)) :=
    ⟨fun x ↦ ⟨f x, hf x⟩, (continuous_subtype_val.comp f.continuous).subtype_mk hf⟩
  let φ := openCellChart k j
  have hφs : φ.source = Subtype.val ⁻¹' openCell k j := openCellChart_source k j
  have hφt : φ.target = ball 0 1 := openCellChart_target k j
  -- First homotope `f` off a point `φ.symm p` of the open cell, keeping the open cell in itself.
  obtain ⟨g₁, ⟨H₁⟩, hg₁, p, hp, hpg₁⟩ := f'.exists_homotopyRel_notMem_range hK.isClosed
    (by rwa [Module.finrank_fin_fun]) φ one_pos hφt.ge
  rw [openCellChart_symm_image_ball] at H₁
  rw [hφs] at hg₁
  -- The image of `g₁` is compact, so `g₁` misses `φ.symm (ball p ε)` for some `ε > 0`.
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hU : IsOpen (φ.target ∩ φ.symm ⁻¹' (range g₁)ᶜ) :=
    φ.continuousOn_symm.isOpen_inter_preimage φ.open_target
      (isCompact_range g₁.continuous).isClosed.isOpen_compl
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU p ⟨hφt ▸ hp, hpg₁⟩
  -- Then push the closed unit ball radially away from `p` onto the sphere.
  obtain ⟨ψ, Ψ, hΨs, hΨε⟩ := (convex_closedBall (0 : Fin k → ℝ) 1).exists_homotopyRel_frontier
    isClosed_closedBall isBounded_closedBall (by rwa [interior_closedBall _ one_ne_zero]) hε
  rw [frontier_closedBall _ one_ne_zero] at hΨε
  obtain ⟨g₂, hg₂, hg₂j, -⟩ := exists_homotopicRel_openCell j Ψ
    (fun t y hy ↦ mem_closedBall_zero_iff.1 (hΨs t y (mem_closedBall_zero_iff.2 hy))) g₁
    (S := {x | (f x : X) ∈ openCell k j}ᶜ) fun x hx ↦ (H₁.fst_eq_snd hx) ▸ hx
  let incl : C((skeletonLT C ((k + 1 : ℕ) : ℕ∞) : Set X), C) :=
    ⟨fun y ↦ ⟨y, (skeletonLT C _).subset_complex y.2⟩, by fun_prop⟩
  have h := (ContinuousMap.HomotopicRel.trans ⟨H₁⟩ hg₂).comp_continuousMap incl
  -- Composing `f'` with the inclusion of the skeleton into the complex recovers `f`.
  have hvf : incl.comp f' = f := ContinuousMap.ext fun _ ↦ rfl
  rw [hvf] at h
  refine ⟨incl.comp g₂, h, fun x hx ↦ ?_⟩
  -- A point sent into the open cell is sent by `g₁` into the open cell, but outside
  -- `φ.symm (ball p ε)`, so the radial push sends it to the frontier.
  have hx₁ : (g₁ x : X) ∈ openCell k j := hg₁ x hx
  have hy := map_symm_mem_ball k hx₁
  have hyε : ε ≤ dist ((map k j).symm (g₁ x)) p := by
    by_contra! h
    refine (hεU (mem_ball.2 h)).2 ⟨x, ?_⟩
    rw [← openCellChart_apply]
    exact (φ.left_inv (hφs ▸ hx₁)).symm
  rw [ContinuousMap.comp_apply, ContinuousMap.coe_mk, hg₂j x hx₁]
  exact ⟨_, hΨε _ (ball_subset_closedBall hy) hyε, rfl⟩

/-- **Compressing a map of a low-dimensional compactum into the next lower skeleton.** Let `K` be
a compact subset of a real normed space of dimension less than `k`. Every map `f : K → C` landing
in the `k`-skeleton `skeletonLT C (k + 1)` is homotopic as a map into `C`, relative to the points
that `f` sends into the `(k-1)`-skeleton `skeletonLT C k`, to a map into `skeletonLT C k`. -/
theorem exists_homotopicRel_skeletonLT {K : Set E} (hK : IsCompact K) (hk : finrank ℝ E < k)
    (f : C(K, C)) (hf : ∀ x, (f x : X) ∈ (skeletonLT C ((k + 1 : ℕ) : ℕ∞) : Set X)) :
    ∃ g : C(K, C), f.HomotopicRel g {x | (f x : X) ∈ (skeletonLT C (k : ℕ∞) : Set X)} ∧
      ∀ x, (g x : X) ∈ (skeletonLT C (k : ℕ∞) : Set X) := by
  classical
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  -- The compact image of `f` meets only finitely many open `k`-cells.
  have hA : {j : cell C k | (range (fun x ↦ (f x : X)) ∩ openCell k j).Nonempty}.Finite :=
    (finite_setOf_nonempty_inter_openCell_of_isCompact (C := C)
      (isCompact_range (continuous_subtype_val.comp f.continuous))).preimage (f := Sigma.mk k)
      sigma_mk_injective.injOn
  -- Push `f` off these cells one at a time, never entering an open `k`-cell that `f` misses.
  have key (T : Finset (cell C k)) : ∃ g : C(K, C),
      f.HomotopicRel g {x | (f x : X) ∈ (skeletonLT C (k : ℕ∞) : Set X)} ∧
      (∀ x, (g x : X) ∈ (skeletonLT C ((k + 1 : ℕ) : ℕ∞) : Set X)) ∧
      (∀ x, ∀ j ∈ T, (g x : X) ∉ openCell k j) ∧
      ∀ x (j : cell C k), (g x : X) ∈ openCell k j → (f x : X) ∈ openCell k j := by
    induction T using Finset.induction_on with
    | empty => exact ⟨f, .refl f, hf, by simp, fun _ _ h ↦ h⟩
    | insert j T _ ih =>
      obtain ⟨g, hfg, hg, hgT, hgf⟩ := ih
      obtain ⟨g₂, hgg₂, hg₂⟩ := exists_homotopicRel_cellFrontier hK hk j g hg
      have heq (x) (hx : (g x : X) ∉ openCell k j) : g₂ x = g x := (hgg₂.fst_eq_snd hx).symm
      have hskel (x) (hx : (g x : X) ∈ openCell k j) :
          (g₂ x : X) ∈ (skeletonLT C (k : ℕ∞) : Set X) :=
        cellFrontier_subset_skeletonLT k j (hg₂ x hx)
      have hnot (x) (hx : (g x : X) ∈ openCell k j) (i : cell C k) : (g₂ x : X) ∉ openCell k i :=
        (disjoint_skeletonLT_openCell le_rfl).notMem_of_mem_left (hskel x hx)
      refine ⟨g₂, hfg.trans (hgg₂.mono fun x hx hgx ↦ ?_), fun x ↦ ?_, fun x i hi ↦ ?_,
        fun x i hi ↦ ?_⟩
      · -- A point sent into `skeletonLT C k` is fixed by the first homotopy, so `g` sends it
        -- outside the open cell `j`.
        rw [mem_ofPred_eq, hfg.fst_eq_snd hx] at hx
        exact (disjoint_skeletonLT_openCell le_rfl).notMem_of_mem_left hx hgx
      · by_cases hx : (g x : X) ∈ openCell k j
        · exact skeletonLT_mono (by exact_mod_cast k.le_succ) (hskel x hx)
        · exact heq x hx ▸ hg x
      · by_cases hx : (g x : X) ∈ openCell k j
        · exact hnot x hx i
        · rw [heq x hx]
          rcases Finset.mem_insert.1 hi with rfl | hi
          exacts [hx, hgT x i hi]
      · by_cases hx : (g x : X) ∈ openCell k j
        · exact absurd hi (hnot x hx i)
        · exact hgf x i (heq x hx ▸ hi)
  -- After all of them, the map lies in no open `k`-cell.
  obtain ⟨g, hfg, hg, hgA, hgf⟩ := key hA.toFinset
  refine ⟨g, hfg, fun x ↦ mem_skeletonLT_of_forall_notMem_openCell k (hg x) fun j hj ↦ ?_⟩
  exact hgA x j (hA.mem_toFinset.2 ⟨f x, ⟨x, rfl⟩, hgf x j hj⟩) hj

/-- **Compressing a map of a compactum into a skeleton of at least its dimension**, the
compression step of Hatcher's Corollary 4.12. Let `K` be a compact subset of a real normed space
of dimension at most `n`. Every map `f : K → C` into the complex is homotopic as a map into `C`,
relative to the points that `f` sends into the `n`-skeleton `skeletonLT C (n + 1)`, to a map into
`skeletonLT C (n + 1)`. -/
theorem exists_homotopicRel_skeletonLT_finrank {K : Set E} (hK : IsCompact K) {n : ℕ}
    (hn : finrank ℝ E ≤ n) (f : C(K, C)) :
    ∃ g : C(K, C),
      f.HomotopicRel g {x | (f x : X) ∈ (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)} ∧
      ∀ x, (g x : X) ∈ (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  -- The compact image of `f` lies in a finite skeleton; compress it one dimension at a time.
  obtain ⟨m, hm⟩ := exists_subset_skeletonLT_of_isCompact (C := C)
    (isCompact_range (continuous_subtype_val.comp f.continuous))
    (range_subset_iff.2 fun x ↦ (f x).2)
  induction m generalizing f with
  | zero =>
    exact ⟨f, .refl f, fun x ↦ skeletonLT_mono (by exact_mod_cast Nat.zero_le _) (hm ⟨x, rfl⟩)⟩
  | succ m ih =>
    by_cases hmn : m + 1 ≤ n + 1
    · exact ⟨f, .refl f, fun x ↦ skeletonLT_mono (by exact_mod_cast hmn) (hm ⟨x, rfl⟩)⟩
    obtain ⟨g₁, hfg₁, hg₁⟩ := exists_homotopicRel_skeletonLT hK (by omega) f
      fun x ↦ hm ⟨x, rfl⟩
    obtain ⟨g, hg₁g, hg⟩ := ih g₁ (range_subset_iff.2 hg₁)
    have hsub : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) ⊆ (skeletonLT C (m : ℕ∞) : Set X) :=
      skeletonLT_mono (by exact_mod_cast (by omega : n + 1 ≤ m))
    -- Points sent into `skeletonLT C (n + 1)` are fixed by the first compression.
    refine ⟨g, (hfg₁.mono fun x hx ↦ hsub hx).trans (hg₁g.mono fun x hx ↦ ?_), hg⟩
    rw [mem_ofPred_eq, ← hfg₁.fst_eq_snd (hsub hx)]
    exact hx

end TauCeti
