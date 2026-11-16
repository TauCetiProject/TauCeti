/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Subcomplex
public import TauCeti.Topology.CWComplex.Classical.Subcomplex
public import TauCeti.Topology.CWComplex.Classical.Skeleton.Induction
public import TauCeti.Topology.Homotopy.Extension.Ball

import TauCeti.Topology.CWComplex.Classical.Skeleton.CellDeformation
import TauCeti.Topology.Homotopy.Extension.NDRPair

/-!
# Relative CW inclusions are closed cofibrations

The base `D` of a relative CW complex `C` has the homotopy extension property inside `C`, and so
do every skeleton and every subcomplex of `C`.  As `X` is Hausdorff, these subsets are closed
(`TauCeti.HasHomotopyExtensionProperty.isClosed`), so their inclusions are closed cofibrations.
This is what makes skeletal induction and homotopy-invariance arguments for CW pairs work: maps
and homotopies can be modified on the base or on a skeleton and extended over the whole complex.

## Main results

* `TauCeti.hasHomotopyExtensionProperty_skeletonLT_succ`: `skeletonLT C n` has the homotopy
  extension property inside `skeletonLT C (n + 1)`.
* `TauCeti.hasHomotopyExtensionProperty_skeletonLT`: every skeleton has the homotopy extension
  property inside the complex.
* `TauCeti.hasHomotopyExtensionProperty_base`: **the base of a relative CW complex has the
  homotopy extension property inside the complex.**
* `Topology.RelCWComplex.Subcomplex.hasHomotopyExtensionProperty`: a subcomplex has the homotopy
  extension property inside the complex, since the complex is a CW complex relative to it.
* `TauCeti.hasHomotopyExtensionProperty_range_of_coe_map_eq`: the range of a map between CW
  complexes carrying every cell onto a cell, characteristic maps included, has the homotopy
  extension property, being a subcomplex.
* `TauCeti.hasHomotopyExtensionProperty_singleton_of_notMem_base`,
  `TauCeti.hasHomotopyExtensionProperty_singleton`,
  `TauCeti.hasHomotopyExtensionProperty_singleton_univ`: **every point of a Hausdorff CW complex
  has the homotopy extension property** (every CW complex is well-pointed at any base point).

## Related results

`TauCeti.hasHomotopyExtensionProperty_sphere_closedBall` gives the homotopy extension property
for the boundary of a closed cell.  The homotopies are extended over the closed cells and glued
over the skeleta by `TauCeti.exists_continuousMap_prod_skeletonLT_succ` and
`TauCeti.exists_continuousMap_prod_complex_of_skeletonLT`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, Proposition 0.16: a CW pair has the homotopy extension property.
-/

public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex unitInterval

universe u

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]

/-- **`skeletonLT C n` has the homotopy extension property inside `skeletonLT C (n + 1)`.** -/
theorem hasHomotopyExtensionProperty_skeletonLT_succ (n : ℕ) :
    HasHomotopyExtensionProperty (Subtype.val ⁻¹' (skeletonLT C n : Set X) :
      Set (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)) := by
  rw [hasHomotopyExtensionProperty_iff]
  intro Y _ f G hG
  -- Extend `G` over every closed `n`-cell, by the homotopy extension property of the boundary
  -- sphere inside the closed ball.
  have hext : ∀ j : cell C n, ∃ K : C(I × closedBall (0 : Fin n → ℝ) 1, Y),
      (∀ y, K (0, y) = f ⟨map n j y, map_mem_skeletonLT_succ j (mem_closedBall_zero_iff.1 y.2)⟩) ∧
      ∀ t (y : closedBall (0 : Fin n → ℝ) 1) (hy : (y : Fin n → ℝ) ∈ sphere 0 1),
        K (t, y) = G (t, ⟨⟨map n j y, map_mem_skeletonLT_succ j (mem_closedBall_zero_iff.1 y.2)⟩,
          cellFrontier_subset_skeletonLT n j ⟨y, hy, rfl⟩⟩) := by
    intro j
    obtain ⟨K, hK0, hKs⟩ :=
      (hasHomotopyExtensionProperty_sphere_closedBall (E := Fin n → ℝ)).exists_extension_of_isClosed
        (isClosed_sphere.preimage continuous_subtype_val)
        (f.comp ⟨fun y ↦ ⟨map n j y, map_mem_skeletonLT_succ j (mem_closedBall_zero_iff.1 y.2)⟩,
          (continuous_map_closedBall j).subtype_mk _⟩)
        (G.comp ⟨fun p ↦ (p.1, ⟨⟨map n j p.2,
          map_mem_skeletonLT_succ j (mem_closedBall_zero_iff.1 p.2.1.2)⟩,
          cellFrontier_subset_skeletonLT n j ⟨p.2, p.2.2, rfl⟩⟩),
          continuous_fst.prodMk ((((continuous_map_closedBall j).comp
            (continuous_subtype_val.comp continuous_snd)).subtype_mk _).subtype_mk _)⟩)
        fun a ↦ hG _
    exact ⟨K, hK0, fun t y hy ↦ hKs t ⟨y, hy⟩⟩
  choose K hK0 hKs using hext
  -- Glue `G` and the extensions `K j` over the closed `n`-cells.
  obtain ⟨F, hFG, hFK⟩ := exists_continuousMap_prod_skeletonLT_succ
    (G.comp ⟨fun p : I × (skeletonLT C n : Set X) ↦
      (p.1, ⟨⟨(p.2 : X), skeletonLT_mono (by exact_mod_cast n.le_succ) p.2.2⟩, p.2.2⟩),
      by fun_prop⟩) K hKs
  refine ⟨F, fun x ↦ ?_, fun t a ↦ hFG t a.1 a.2⟩
  obtain hx | ⟨j, y, hy, hxy⟩ := mem_skeletonLT_or_exists_map x.2
  · rw [hFG 0 x hx]
    exact hG ⟨x, hx⟩
  · obtain rfl : x = ⟨map n j y, map_mem_skeletonLT_succ j hy.le⟩ := Subtype.ext hxy.symm
    exact (hFK j 0 ⟨y, mem_closedBall_zero_iff.2 hy.le⟩).trans (hK0 j _)

section Glue

variable {Y : Type u} [TopologicalSpace Y] {k : ℕ} {f : C(C, Y)}
  {H : C(I × (Subtype.val ⁻¹' (skeletonLT C k : Set X) : Set C), Y)}

variable (k f H) in
/-- The solutions of the homotopy extension problem `(f, H)` on the successive skeleta
`skeletonLT C (k + j)`, each obtained from the previous one by
`TauCeti.hasHomotopyExtensionProperty_skeletonLT_succ`. -/
private def extensionSeq (hH : ∀ a, H (0, a) = f a) : (j : ℕ) →
    {G : C(I × (skeletonLT C ((k + j : ℕ) : ℕ∞) : Set X), Y) //
      ∀ x, G (0, x) = f ⟨x, (skeletonLT C _).subset_complex x.2⟩}
  | 0 => ⟨H.comp ⟨fun p ↦ (p.1, ⟨⟨p.2, (skeletonLT C _).subset_complex p.2.2⟩, p.2.2⟩),
      by fun_prop⟩, fun x ↦ hH _⟩
  | j + 1 =>
    have h := (hasHomotopyExtensionProperty_skeletonLT_succ (C := C) (k + j)).exists_extension
      (f.comp ⟨fun x ↦ ⟨x, (skeletonLT C _).subset_complex x.2⟩, by fun_prop⟩)
      ((extensionSeq hH j).1.comp ⟨fun p ↦ (p.1, ⟨p.2, p.2.2⟩), by fun_prop⟩)
      fun a ↦ (extensionSeq hH j).2 _
    ⟨h.choose, h.choose_spec.1⟩

private lemma extensionSeq_succ_apply {hH : ∀ a, H (0, a) = f a} (j : ℕ) (t : I)
    (x : X) (hx : x ∈ (skeletonLT C ((k + j : ℕ) : ℕ∞) : Set X)) :
    (extensionSeq k f H hH (j + 1)).1
        (t, ⟨x, skeletonLT_mono (by exact_mod_cast (k + j).le_succ) hx⟩) =
      (extensionSeq k f H hH j).1 (t, ⟨x, hx⟩) := by
  rw [extensionSeq]
  exact ((hasHomotopyExtensionProperty_skeletonLT_succ (C := C) (k + j)).exists_extension _ _
    fun a ↦ (extensionSeq k f H hH j).2 _).choose_spec.2 t ⟨_, hx⟩

end Glue

/-- **Every skeleton of a relative CW complex has the homotopy extension property inside the
complex.** -/
theorem hasHomotopyExtensionProperty_skeletonLT (k : ℕ) :
    HasHomotopyExtensionProperty (Subtype.val ⁻¹' (skeletonLT C k : Set X) : Set C) := by
  rw [hasHomotopyExtensionProperty_iff]
  intro Y _ f H hH
  -- Solve the problem on the successive skeleta and glue the solutions.
  obtain ⟨G, hG⟩ := exists_continuousMap_prod_complex_of_skeletonLT
    (fun j ↦ (extensionSeq k f H hH j).1) (extensionSeq_succ_apply (hH := hH))
  refine ⟨G, fun x ↦ ?_, fun t a ↦ hG 0 t a.1 a.2⟩
  obtain ⟨j, hj⟩ := exists_mem_skeletonLT_add k x.2
  exact (hG j 0 x hj).trans ((extensionSeq k f H hH j).2 _)

/-- **Relative CW inclusions are cofibrations: the base of a relative CW complex has the homotopy
extension property inside the complex.**  The base is also closed
(`TauCeti.HasHomotopyExtensionProperty.isClosed`), so the inclusion is a closed cofibration. -/
theorem hasHomotopyExtensionProperty_base :
    HasHomotopyExtensionProperty (Subtype.val ⁻¹' D : Set C) := by
  simpa only [Nat.cast_zero, skeletonLT_zero_eq_base] using
    hasHomotopyExtensionProperty_skeletonLT (C := C) 0

/-- **CW pairs are cofibrations: a subcomplex has the homotopy extension property inside the
complex.** The complex is a CW complex relative to the subcomplex
(`Topology.RelCWComplex.Subcomplex.relCWComplex`), whose base has the homotopy extension property.
-/
theorem _root_.Topology.RelCWComplex.Subcomplex.hasHomotopyExtensionProperty
    (E : Subcomplex C) : HasHomotopyExtensionProperty (Subtype.val ⁻¹' (E : Set X) : Set C) :=
  @hasHomotopyExtensionProperty_base X _ _ C E E.relCWComplex

/-- **The range of a map carrying cells onto cells has the homotopy extension property.** Let `W`
and `Y` carry CW structures on `univ`, and let `g : W → Y` carry every `n`-cell `i` of `W` onto an
`n`-cell `ι n i` of `Y`, in the sense that `map n (ι n i) = g ∘ map n i`. Then the range of `g`
is the subcomplex of `Y` made of these cells, so it has the homotopy extension property. -/
theorem hasHomotopyExtensionProperty_range_of_coe_map_eq {W Y : Type*} [TopologicalSpace W]
    [CWComplex (univ : Set W)] [TopologicalSpace Y] [T2Space Y] [CWComplex (univ : Set Y)]
    {g : W → Y} (ι : ∀ n, cell (univ : Set W) n → cell (univ : Set Y) n)
    (hι : ∀ n i, ⇑(map n (ι n i)) = g ∘ map n i) :
    HasHomotopyExtensionProperty (range g) := by
  have himage (n : ℕ) (i : cell (univ : Set W) n) (s : Set (Fin n → ℝ)) :
      map n (ι n i) '' s = g '' (map n i '' s) := by
    rw [hι, image_comp]
  -- The range of `g` is the subcomplex of `Y` whose cells are those in the range of `ι`.
  let E : Subcomplex (univ : Set Y) :=
    CWComplex.Subcomplex.mk' _ (range g) (fun n ↦ range (ι n))
    (fun n j ↦ by
      obtain ⟨_, i, rfl⟩ := j
      rw [closedCell, himage]
      exact image_subset_range _ _)
    (by
      refine Subset.antisymm (iUnion₂_subset fun n j ↦ ?_) ?_
      · obtain ⟨_, i, rfl⟩ := j
        rw [openCell, himage]
        exact image_subset_range _ _
      · rintro _ ⟨w, rfl⟩
        obtain ⟨n, i, hw⟩ := mem_iUnion₂.1 <|
          (CWComplex.iUnion_openCell_eq_complex (C := (univ : Set W))).symm ▸ mem_univ w
        refine mem_iUnion₂.2 ⟨n, ⟨ι n i, i, rfl⟩, ?_⟩
        rw [openCell, himage]
        exact mem_image_of_mem g hw)
  have h := E.hasHomotopyExtensionProperty.image (Homeomorph.Set.univ Y)
  rwa [Homeomorph.Set.univ_apply, image_preimage_eq_range_inter, Subtype.range_coe, univ_inter]
    at h

section Singleton

/-- A deformation of `Fin n → ℝ` fixing the unit sphere and keeping the closed unit ball inside
itself that contracts the ball of radius `(1 - ‖y₀‖) / 2` around `y₀ ∈ ball 0 1` onto `y₀`. -/
private def ballPointDeformation {n : ℕ} (y₀ : Fin n → ℝ) :
    C(I × (Fin n → ℝ), Fin n → ℝ) where
  toFun q := q.2 -
    ((q.1 : ℝ) * (projIcc 0 1 zero_le_one (2 - ‖q.2 - y₀‖ / ((1 - ‖y₀‖) / 2)) : ℝ)) • (q.2 - y₀)
  continuous_toFun := by fun_prop

private lemma ballPointDeformation_properties {n : ℕ} {y₀ : Fin n → ℝ} (hy₀ : ‖y₀‖ < 1) :
    let r₀ := (1 - ‖y₀‖) / 2
    (∀ y, ballPointDeformation y₀ (0, y) = y) ∧
    (∀ t, ballPointDeformation y₀ (t, y₀) = y₀) ∧
    (∀ t y, ‖y‖ = 1 → ballPointDeformation y₀ (t, y) = y) ∧
    (∀ t y, ‖y‖ ≤ 1 → ‖ballPointDeformation y₀ (t, y)‖ ≤ 1) ∧
    (∀ y, ‖y - y₀‖ < r₀ → ballPointDeformation y₀ (1, y) = y₀) := by
  set r₀ : ℝ := (1 - ‖y₀‖) / 2 with hr₀_def
  have hr₀ : 0 < r₀ := by linarith [hr₀_def]
  refine ⟨fun y ↦ by simp [ballPointDeformation], fun t ↦ by simp [ballPointDeformation],
    fun t y hy ↦ ?_, fun t y hy ↦ ?_, fun y hy ↦ ?_⟩
  · -- On the unit sphere `‖y - y₀‖ ≥ 1 - ‖y₀‖ = 2 r₀`, so the cutoff vanishes.
    have hdist : 2 * r₀ ≤ ‖y - y₀‖ := by
      have := norm_sub_norm_le y y₀
      linarith [hy, hr₀_def]
    have hle : 2 - ‖y - y₀‖ / r₀ ≤ 0 := by
      have : 2 ≤ ‖y - y₀‖ / r₀ := (le_div_iff₀ hr₀).2 hdist
      linarith
    simp [ballPointDeformation, ← hr₀_def, projIcc_of_le_left zero_le_one hle]
  · -- Each point moves along the segment toward `y₀ ∈ closedBall 0 1`.
    let s : I := t * projIcc 0 1 zero_le_one (2 - ‖y - y₀‖ / r₀)
    have hconv : ballPointDeformation y₀ (t, y) = (1 - (s : ℝ)) • y + (s : ℝ) • y₀ := by
      simp only [ballPointDeformation, ContinuousMap.coe_mk, s, Icc.coe_mul, ← hr₀_def]
      module
    rw [hconv, ← mem_closedBall_zero_iff]
    exact (convex_closedBall (0 : Fin n → ℝ) 1) (mem_closedBall_zero_iff.2 hy)
      (mem_closedBall_zero_iff.2 hy₀.le) (by linarith [s.2.2]) s.2.1 (by linarith)
  · -- Inside radius `r₀`, the cutoff is `1` and time `1` sends `y` to `y₀`.
    have hge : 1 ≤ 2 - ‖y - y₀‖ / r₀ := by
      have : ‖y - y₀‖ / r₀ < 1 := (div_lt_one hr₀).2 hy
      linarith
    simp [ballPointDeformation, ← hr₀_def, projIcc_of_right_le zero_le_one hge]

/-- A continuous control function on `skeletonLT C (n + 1)` vanishing only at `x ∈ openCell n j`
and strictly below `1` only within radius `(1 - ‖y₀‖) / 2` of `y₀ = (map n j).symm x` in cell `j`.
-/
private lemma exists_singletonControl_skeletonLT {n : ℕ} (j : cell C n) {x : X}
    (hx : x ∈ openCell n j) :
    ∃ u : C((skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X), I),
      (∀ z, u z = 0 ↔ (z : X) = x) ∧
      ∀ z, u z < 1 → ∃ y, ‖y‖ < 1 ∧ map n j y = z ∧
        ‖y - (map n j).symm x‖ < (1 - ‖(map n j).symm x‖) / 2 := by
  classical
  let y₀ : Fin n → ℝ := (map n j).symm x
  have hy₀ : ‖y₀‖ < 1 := mem_ball_zero_iff.1 (map_symm_mem_ball n hx)
  set r₀ : ℝ := (1 - ‖y₀‖) / 2 with hr₀_def
  have hr₀ : 0 < r₀ := by linarith [hr₀_def]
  let K : cell C n → C(Unit × closedBall (0 : Fin n → ℝ) 1, I) := fun i ↦
    if i = j then ⟨fun p ↦ projIcc 0 1 zero_le_one (‖(p.2 : Fin n → ℝ) - y₀‖ / r₀), by fun_prop⟩
    else ContinuousMap.const _ 1
  obtain ⟨u, hu_skel, hu_cell⟩ := exists_continuousMap_prod_skeletonLT_succ
    (ContinuousMap.const (Unit × (skeletonLT C n : Set X)) (1 : I)) K fun i _ y hy ↦ by
      dsimp only [K]
      split_ifs with hij
      · have hdist : r₀ ≤ ‖(y : Fin n → ℝ) - y₀‖ := by
          have := norm_sub_norm_le (y : Fin n → ℝ) y₀
          linarith [mem_sphere_zero_iff_norm.1 hy, hr₀_def]
        simp [projIcc_of_right_le zero_le_one ((one_le_div hr₀).2 hdist)]
      · rfl
  refine ⟨u.comp ⟨fun z ↦ ((), z), by fun_prop⟩, fun z ↦ ?_, fun z hz ↦ ?_⟩
  · simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk]
    obtain hz' | ⟨i, y, hy, hzy⟩ := mem_skeletonLT_or_exists_map z.2
    · rw [hu_skel () z hz']
      exact ⟨fun h ↦ absurd h one_ne_zero,
        fun h ↦ absurd (h ▸ hz') (disjoint_skeletonLT_openCell le_rfl |>.notMem_of_mem_right hx)⟩
    · have hsub : z = ⟨map n i y, map_mem_skeletonLT_succ i hy.le⟩ := Subtype.ext hzy.symm
      rw [hsub, hu_cell i () ⟨y, mem_closedBall_zero_iff.2 hy.le⟩]
      by_cases hij : i = j
      · subst hij
        simp only [K, ↓reduceIte, ContinuousMap.coe_mk]
        refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
        · have h0 : (projIcc 0 1 zero_le_one (‖y - y₀‖ / r₀) : ℝ) = 0 := congrArg Subtype.val h
          rw [coe_projIcc] at h0
          rcases min_le_iff.1 (max_le_iff.1 h0.le).2 with h1 | hdiv
          · norm_num at h1
          · have h0' := (div_le_iff₀ hr₀).1 hdiv
            have hy_eq : y = y₀ := sub_eq_zero.1 (norm_le_zero_iff.1 (by linarith))
            rw [hy_eq]
            exact map_map_symm n hx
        · have hy_eq : y = y₀ := by
            simpa only [y₀] using
              ((map n i).left_inv ((source_eq n i).symm ▸ mem_ball_zero_iff.2 hy)).symm.trans
                (congrArg (map n i).symm h)
          simp [hy_eq]
      · simp only [K, hij, ↓reduceIte, ContinuousMap.const_apply]
        refine ⟨fun h ↦ absurd h one_ne_zero, fun h ↦ False.elim ?_⟩
        exact (disjoint_openCell_of_ne (by simpa using hij)).notMem_of_mem_left
          ⟨y, mem_ball_zero_iff.2 hy, rfl⟩ (h ▸ hx)
  · simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk] at hz
    obtain hz' | ⟨i, y, hy, hzy⟩ := mem_skeletonLT_or_exists_map z.2
    · rw [hu_skel () z hz'] at hz
      exact (lt_irrefl _ hz).elim
    · have hsub : z = ⟨map n i y, map_mem_skeletonLT_succ i hy.le⟩ := Subtype.ext hzy.symm
      rw [hsub, hu_cell i () ⟨y, mem_closedBall_zero_iff.2 hy.le⟩] at hz
      by_cases hij : i = j
      · subst hij
        simp only [K, ↓reduceIte, ContinuousMap.coe_mk] at hz
        refine ⟨y, hy, hzy, ?_⟩
        by_contra! hge
        rw [projIcc_of_right_le zero_le_one ((one_le_div hr₀).2 hge)] at hz
        exact lt_irrefl _ hz
      · simp [K, hij] at hz

/-- A point `x` in an open `n`-cell of `(C, D)` has the homotopy extension property inside the
`n`-skeleton `skeletonLT C (n + 1)`, via explicit NDR data supported in that open cell. -/
private lemma hasHomotopyExtensionProperty_singleton_skeletonLT {n : ℕ} (j : cell C n) {x : X}
    (hx : x ∈ openCell n j) :
    HasHomotopyExtensionProperty ({⟨x, openCell_subset_skeletonLT n j hx⟩} :
      Set (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)) := by
  let y₀ : Fin n → ℝ := (map n j).symm x
  obtain ⟨hΨ0, hΨy₀, hΨs, hΨb, hΨ1⟩ :=
    ballPointDeformation_properties (mem_ball_zero_iff.1 (map_symm_mem_ball n hx))
  obtain ⟨u, hu0, hu1⟩ := exists_singletonControl_skeletonLT j hx
  exact NDRPair.hasHomotopyExtensionProperty
    { control := u
      control_eq_zero_iff := fun z ↦ (hu0 z).trans (by simp [Subtype.ext_iff])
      deformation := ⟨fun q ↦ ⟨cellDeformation {j} (ballPointDeformation y₀) (q.1, q.2),
          cellDeformation_mem hΨb q.1 q.2.2⟩,
        (continuous_cellDeformation {j} hΨs hΨb).subtype_mk _⟩
      deformation_zero := fun z ↦ Subtype.ext <| by
        simp only [ContinuousMap.coe_mk]
        by_cases hz : (z : X) ∈ openCell n j
        · rw [cellDeformation_of_mem (mem_singleton j) hz, hΨ0, map_map_symm n hz]
        · exact cellDeformation_of_notMem fun i hi ↦ by rwa [mem_singleton_iff.1 hi]
      deformation_of_mem := fun t z hz ↦ Subtype.ext <| by
        rw [mem_singleton_iff.1 hz]
        simp only [ContinuousMap.coe_mk]
        rw [cellDeformation_of_mem (mem_singleton j) hx, hΨy₀, map_map_symm n hx]
      deformation_one_mem := fun {z} hz ↦ by
        obtain ⟨y, hy, hzy, hlt⟩ := hu1 z hz
        rw [mem_singleton_iff, Subtype.ext_iff]
        simp only [ContinuousMap.coe_mk]
        rw [← hzy, cellDeformation_of_mem (mem_singleton j) ⟨y, mem_ball_zero_iff.2 hy, rfl⟩,
          (map n j).left_inv ((source_eq n j).symm ▸ mem_ball_zero_iff.2 hy), hΨ1 y hlt,
          map_map_symm n hx] }

/-- **Every point of a Hausdorff relative CW complex outside the base has the homotopy extension
property.** -/
theorem hasHomotopyExtensionProperty_singleton_of_notMem_base {x₀ : C} (hx₀ : (x₀ : X) ∉ D) :
    HasHomotopyExtensionProperty ({x₀} : Set C) := by
  -- `x₀` lies in a unique open `n`-cell `j`; `{x₀}` has NDR data in `skeletonLT C (n + 1)`, which
  -- in turn has the homotopy extension property in `C`.
  have hxC : (x₀ : X) ∈ D ∪ ⋃ n, ⋃ j : cell C n, openCell n j := by
    rw [union_iUnion_openCell_eq_complex]
    exact x₀.2
  obtain ⟨n, j, hxj⟩ := mem_iUnion₂.1 (hxC.resolve_left hx₀)
  let hsub := (skeletonLT C ((n + 1 : ℕ) : ℕ∞)).subset_complex
  have hrange : range (inclusion hsub) =
      (Subtype.val ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) : Set C) := by
    ext z
    exact ⟨fun ⟨w, hw⟩ ↦ hw ▸ w.2, fun hz ↦ ⟨⟨z, hz⟩, rfl⟩⟩
  have himg := (hasHomotopyExtensionProperty_singleton_skeletonLT j hxj).image_of_isEmbedding
    (Topology.IsEmbedding.inclusion hsub) (hrange ▸ hasHomotopyExtensionProperty_skeletonLT (n + 1))
  rwa [image_singleton] at himg

/-- **Every point of a Hausdorff CW complex has the homotopy extension property** (every Hausdorff
CW complex is well-pointed at every base point). -/
theorem hasHomotopyExtensionProperty_singleton {C : Set X} [CWComplex C] (x₀ : C) :
    HasHomotopyExtensionProperty ({x₀} : Set C) :=
  hasHomotopyExtensionProperty_singleton_of_notMem_base (notMem_empty _)

/-- **Every point of a Hausdorff space carrying a CW structure on `univ` has the homotopy extension
property.** -/
theorem hasHomotopyExtensionProperty_singleton_univ [CWComplex (univ : Set X)] (x₀ : X) :
    HasHomotopyExtensionProperty ({x₀} : Set X) := by
  have h := (hasHomotopyExtensionProperty_singleton (⟨x₀, mem_univ x₀⟩ : (univ : Set X))).image
    (Homeomorph.Set.univ X)
  rwa [image_singleton, Homeomorph.Set.univ_apply] at h

end Singleton

end TauCeti
