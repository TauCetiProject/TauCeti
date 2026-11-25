/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import TauCeti.AlgebraicTopology.Homotopy.Relative.Disk
public import TauCeti.AlgebraicTopology.Homotopy.Relative.Exact
public import TauCeti.Topology.CWComplex.Classical.Subcomplex
public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace
public import TauCeti.Topology.Homotopy.HomotopyGroup.Product
public import TauCeti.Topology.Homotopy.Homotopic.Rel

import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange
import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
import TauCeti.Topology.CWComplex.Classical.Skeleton.Compression
import TauCeti.Topology.CWComplex.Classical.Zero
import TauCeti.Topology.Homotopy.Extension.Basepoint
import TauCeti.Topology.Homotopy.Extension.CWComplex
import TauCeti.Topology.Homotopy.HomotopyGroup.BasepointChange
import TauCeti.Topology.Homotopy.HomotopyGroup.Homotopy
import TauCeti.Topology.Homotopy.HomotopyGroup.PathComponent
import TauCeti.Topology.Homotopy.Path
import TauCeti.Topology.PathComponent

/-!
# Maps from a CW complex into a space without higher homotopy

Let `Y` be a space whose homotopy groups `πₙ(Y, y)` vanish for `n ≥ 2` at every point `y`, such as
a `K(H, 1)`. A map from a CW complex into `Y` is determined up to homotopy by what it does on the
`1`-skeleton up to homotopy: two maps `f g : C → Y` out of a relative CW complex `(C, D)` that, on
every path in `C` between points of the `0`-skeleton, agree up to homotopy relative to the
endpoints, are homotopic relative to the `0`-skeleton
(`TauCeti.homotopicRel_skeletonLT_one_of_forall_homotopicRel`).

For any path-connected Hausdorff CW complex `(C, x₀)` — with arbitrary `0`-skeleton and arbitrary
base point `x₀` — and any target `(Y, y₀)` with `πₙ(Y, y₀) = 0` for `n ≥ 2` (only at `y₀`, without
requiring `Y` to be path connected), pointed maps `f, g : (C, x₀) → (Y, y₀)` are homotopic relative
to `{x₀}` if and only if they induce the same homomorphism `π₁(C, x₀) →* π₁(Y, y₀)`
(`TauCeti.homotopicRel_of_mapOfEq_eq`, `TauCeti.homotopicRel_singleton_iff_mapOfEq_eq`). Likewise,
unbased maps `f, g : X → Y` out of a path-connected Hausdorff CW complex are freely homotopic if
and only if their induced homomorphisms on `π₁` are intertwined by basepoint change along some path
from `f x₀` to `g x₀` (`TauCeti.homotopic_iff_exists_path_fundamentalGroupMulEquivOfPath`). This is
the uniqueness half of Hatcher's Proposition 1B.9 in full generality.

The proof reads a homotopy from `f` to `g` relative to a set `A` as a deformation, relative to
`A`, of the map `(f, g) : C → Y × Y` into the diagonal. Since the diagonal `Δ ⊆ Y × Y` is a
retract of `Y × Y` and `πₙ(Y × Y)` vanishes for `n ≥ 2`, the exact sequence of the pair shows that
the relative homotopy sets `πₙ(Y × Y, Δ)` vanish for `n ≥ 2`
(`TauCeti.subsingleton_relHomotopyGroup_diagonal`). So the compression lemma deforms `(f, g)` into
`Δ` relative to `D` as soon as `(C, D)` has no cells of dimension `0` or `1` and `f = g` on `D`
(`TauCeti.homotopicRel_base_of_isEmpty_cell`). When the base point is a `0`-cell `v₀`, deforming `f`
on the discrete `0`-skeleton along conjugate paths and extending via the homotopy extension property
reduces to `TauCeti.homotopicRel_skeletonLT_one_of_forall_homotopicRel`; for an arbitrary base point
`x₀`, transporting to a `0`-cell `v₀` along a path `δ` yields a homotopy whose trace loop at `x₀` is
nullhomotopic by naturality of `FundamentalGroupoidFunctor.homotopicMapsNatIso`, and
`TauCeti.HasHomotopyExtensionProperty.homotopicRel_singleton_of_homotopic_refl` makes the homotopy
stationary at `x₀`. Corestricting to `pathComponent y₀` eliminates higher-homotopy assumptions
outside the base point's path component.

## Main results

* `TauCeti.subsingleton_relHomotopyGroup_diagonal`: the relative homotopy sets of the diagonal in
  `Y × Y` vanish from degree `2` on.
* `TauCeti.homotopicRel_base_of_isEmpty_cell`: maps agreeing on the base of a relative CW complex
  without cells of dimension `0` and `1` are homotopic relative to the base.
* `TauCeti.homotopicRel_skeletonLT_one_of_forall_homotopicRel`: maps agreeing up to homotopy on
  paths between points of the `0`-skeleton are homotopic relative to the `0`-skeleton.
* `TauCeti.homotopicRel_singleton_of_mapOfEq_eq`: pointed uniqueness for a relative CW complex
  `(C, D)` whose relative `0`-skeleton is `{x₀}`.
* `TauCeti.homotopicRel_of_mapOfEq_eq`, `TauCeti.homotopicRel_singleton_iff_mapOfEq_eq`,
  `TauCeti.homotopicRel_of_mapOfEq_eq_of_cwComplex`,
  `TauCeti.homotopicRel_singleton_iff_mapOfEq_eq_of_cwComplex`: **pointed maps from any
  path-connected Hausdorff CW complex into a space with `πₙ(Y, y₀) = 0` (`n ≥ 2`) are determined, up
  to homotopy relative to `{x₀}`, by the homomorphism they induce on `π₁`.**
* `TauCeti.homotopic_iff_exists_path_fundamentalGroupMulEquivOfPath`,
  `TauCeti.homotopic_iff_exists_path_fundamentalGroupMulEquivOfPath_of_cwComplex`: **unbased maps
  out of a path-connected Hausdorff CW complex into a space with `πₙ(Y, g x₀) = 0` (`n ≥ 2`) are
  freely homotopic if and only if their induced maps on `π₁` agree up to basepoint change along a
  path.**

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 1.B, Proposition 1B.9, and Section 4.1, Lemma 4.6 (the compression lemma).
-/

public section

noncomputable section

universe u v

open Metric Set Topology Topology.RelCWComplex
open scoped unitInterval Topology.Homotopy

namespace TauCeti

variable {Y : Type v} [TopologicalSpace Y]

/-- If the homotopy groups of `Y` vanish from degree `2` on, at every point, then so do the
relative homotopy sets `π_{n+2}(Y × Y, Δ, b)` of the diagonal `Δ ⊆ Y × Y`, at every point `b` of
the diagonal. -/
theorem subsingleton_relHomotopyGroup_diagonal
    (hY : ∀ (y : Y) (n : ℕ), Subsingleton (π_ (n + 2) Y y)) (n : ℕ) (b : diagonal Y) :
    Subsingleton (RelHomotopyGroup (Fin (n + 1))
      ⟨TopPair.ofSubset (X := TopCat.of (Y × Y)) (diagonal Y), b⟩) := by
  -- The diagonal is a retract of `Y × Y`, so its inclusion is injective on homotopy groups.
  let r : C(Y × Y, diagonal Y) := ⟨fun p ↦ ⟨(p.1, p.1), rfl⟩, by fun_prop⟩
  have hr : r (b : Y × Y) = b := Subtype.ext (Prod.ext rfl b.property)
  have hrι : r.comp (ContinuousMap.subtypeVal (diagonal Y)) = ContinuousMap.id _ := by
    ext ⟨p, hp⟩
    · simp [r]
    · simpa [r] using hp
  -- `π_{n+2}(Y × Y, b)` is the product of two homotopy groups of `Y`.
  have hY' (y : Y) : Subsingleton (HomotopyGroup (Option (Fin (n + 1))) Y y) :=
    (HomotopyGroup.congrEquiv (finSuccEquiv (n + 1))).subsingleton_congr.1 (hY y n)
  have hYY : Subsingleton (HomotopyGroup (Option (Fin (n + 1))) (Y × Y) (b : Y × Y)) :=
    (HomotopyGroup.prodEquiv (b : Y × Y).1 (b : Y × Y).2).subsingleton_congr.2 inferInstance
  -- The absolute group of the pair is `π_{n+2}(Y × Y, b)` up to unfolding `TopPair.ofSubset`, so
  -- `hYY` is passed explicitly rather than found by instance search.
  exact RelHomotopyGroup.subsingleton_of_injective_of_surjective
    (Function.LeftInverse.injective (g := HomotopyGroup.map r hr)
      (HomotopyGroup.map_map_of_comp_eq_id r _ rfl hr hrι))
    (@Function.surjective_to_subsingleton _ _ _ hYY _)

variable {X : Type u} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]

/-- Let `(C, D)` be a relative CW complex without cells of dimension `0` and `1`, and let `Y` be a
space whose homotopy groups vanish from degree `2` on, at every point. Then two maps `C → Y` that
agree on `D` are homotopic relative to `D`. -/
theorem homotopicRel_base_of_isEmpty_cell (h₀ : IsEmpty (cell C 0)) (h₁ : IsEmpty (cell C 1))
    (hY : ∀ (y : Y) (n : ℕ), Subsingleton (π_ (n + 2) Y y)) {f g : C(C, Y)}
    (hfg : ∀ x : C, (x : X) ∈ D → f x = g x) :
    f.HomotopicRel g {x : C | (x : X) ∈ D} := by
  -- Deform `(f, g)` into the diagonal relative to `D`, and project to either factor.
  obtain ⟨G, hG, hGΔ⟩ := exists_homotopicRel_range_subset_of_relHomotopyGroup
    (Y := TopCat.of (Y × Y)) (B := diagonal Y) (fun h ↦ (h₀.false h.some).elim)
    (fun n hn b ↦ by
      rcases n with _ | n
      · exact (h₁.false hn.some).elim
      · exact subsingleton_relHomotopyGroup_diagonal hY n b)
    (f.prodMk g) fun x hx ↦ hfg x hx
  have hG' : ContinuousMap.fst.comp G = ContinuousMap.snd.comp G := by
    ext x
    exact hGΔ ⟨x, rfl⟩
  have h₁ := hG.comp_continuousMap ContinuousMap.fst
  have h₂ := hG.comp_continuousMap ContinuousMap.snd
  have hf : ContinuousMap.fst.comp (f.prodMk g) = f := by ext; simp
  have hg : ContinuousMap.snd.comp (f.prodMk g) = g := by ext; simp
  rw [hf, hG'] at h₁
  rw [hg] at h₂
  exact h₁.trans h₂.symm

/-- Let `(C, D)` be a relative CW complex, and let `Y` be a space whose homotopy groups vanish from
degree `2` on, at every point. Let `f g : C → Y` be such that, for every path `γ` in `C` between
points of the `0`-skeleton `skeletonLT C 1`, the paths `f ∘ γ` and `g ∘ γ` are homotopic
relative to their endpoints. Then `f` and `g` are homotopic relative to the `0`-skeleton. -/
theorem homotopicRel_skeletonLT_one_of_forall_homotopicRel
    (hY : ∀ (y : Y) (n : ℕ), Subsingleton (π_ (n + 2) Y y)) {f g : C(C, Y)}
    (hfg : ∀ γ : C(I, C), (γ 0 : X) ∈ skeletonLT C 1 → (γ 1 : X) ∈ skeletonLT C 1 →
      (f.comp γ).HomotopicRel (g.comp γ) {0, 1}) :
    f.HomotopicRel g {x : C | (x : X) ∈ skeletonLT C 1} := by
  -- The interval as the closed unit ball of `Fin 1 → ℝ`, by `t ↦ 2 * t - 1`.
  let e : I ≃ₜ closedBall (0 : Fin 1 → ℝ) 1 :=
    (Homeomorph.funUnique (Fin 1) I).symm.trans (cubeHomeomorphClosedBall (Fin 1))
  have he (t : I) : (e t : Fin 1 → ℝ) ∈ sphere 0 1 ↔ t = 0 ∨ t = 1 := by
    rw [mem_sphere_zero_iff_norm, Homeomorph.trans_apply, norm_cubeHomeomorphClosedBall_eq_one_iff]
    simp [Cube.boundary]
  -- Through the characteristic map, each `1`-cell is a path between points of the `0`-skeleton.
  have hcell (j : cell C 1) : (f.comp (cellMap j)).HomotopicRel (g.comp (cellMap j))
      {y | (y : Fin 1 → ℝ) ∈ sphere 0 1} := by
    have hγ (t : I) (ht : t = 0 ∨ t = 1) : ((cellMap j (e t) : C) : X) ∈ skeletonLT C 1 :=
      cellFrontier_subset_skeletonLT 1 j
        ⟨e t, (he t).2 ht, (coe_cellMap_apply j _).symm⟩
    have h := (hfg ((cellMap j).comp e) (hγ 0 (Or.inl rfl)) (hγ 1 (Or.inr rfl))).precomp
      (e.symm : C(closedBall (0 : Fin 1 → ℝ) 1, I))
    have hΦ : ((cellMap j).comp (e : C(I, closedBall (0 : Fin 1 → ℝ) 1))).comp
        (e.symm : C(closedBall (0 : Fin 1 → ℝ) 1, I)) = cellMap j := by
      ext y
      simp
    simp only [ContinuousMap.comp_assoc, hΦ] at h
    refine h.mono fun y hy ↦ (he _).1 ?_
    simpa using hy
  -- Homotope `f`, relative to the `0`-skeleton, to agree with `g` on every `1`-cell.
  obtain ⟨f₁, hff₁, hf₁⟩ := exists_homotopicRel_cellMap 1 f (fun j ↦ g.comp (cellMap j)) hcell
  -- `f₁` agrees with `g` on the `1`-skeleton, and `C` has no cells of dimension `0` or `1`
  -- relative to its `1`-skeleton.
  let E := skeletonLT C 2
  have hf₁g : ∀ x : C, (x : X) ∈ E → f₁ x = g x := by
    have h : MapsTo (f₁.prodMk g) {x : C | (x : X) ∈ skeletonLT C ((1 + 1 : ℕ) : ℕ∞)}
        (diagonal Y) := by
      refine mapsTo_skeletonLT_succ_iff.2 ⟨fun x hx ↦ ?_, fun j y ↦ hf₁ j y⟩
      simp only [mem_diagonal_iff, ContinuousMap.prod_eval]
      rw [← hff₁.fst_eq_snd hx]
      exact (hfg (.const I x) hx hx).fst_eq_snd (Or.inl rfl)
    exact fun x hx ↦ h hx
  have hE (n : ℕ) (hn : n < 2) : IsEmpty (@cell X _ C E E.relCWComplex n) := by
    refine ⟨fun i ↦ (E.relCWComplexCellEquiv n i).property ?_⟩
    simp only [E, skeletonLT_I, mem_ofPred_eq]
    exact_mod_cast hn
  -- The structure relative to `E` is not an instance: `C` already carries one relative to `D`.
  have h := @homotopicRel_base_of_isEmpty_cell Y _ X _ _ C E E.relCWComplex (hE 0 two_pos)
    (hE 1 one_lt_two) hY f₁ g hf₁g
  exact hff₁.trans (h.mono fun x hx ↦ skeletonLT_mono (by norm_num) hx)

/-- **Maps out of a relative CW complex with a singleton relative `0`-skeleton are determined by
their effect on `π₁`.** Let `(C, D)` be a relative CW complex whose relative `0`-skeleton
`skeletonLT C 1` is a single point `x₀` (for an absolute CW complex with an arbitrary `0`-skeleton,
see `TauCeti.homotopicRel_of_mapOfEq_eq`), and let `Y` be a space whose homotopy groups vanish from
degree `2` on, at every point. Two maps `C → Y` sending `x₀` to `y₀` and inducing the same
homomorphism `π₁(C, x₀) → π₁(Y, y₀)` are homotopic relative to `x₀`. -/
theorem homotopicRel_singleton_of_mapOfEq_eq
    (hY : ∀ (y : Y) (n : ℕ), Subsingleton (π_ (n + 2) Y y)) {x₀ : C}
    (hx₀ : {x : C | (x : X) ∈ skeletonLT C 1} = {x₀}) {f g : C(C, Y)} {y₀ : Y}
    (hf : f x₀ = y₀) (hg : g x₀ = y₀)
    (hfg : FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg) :
    f.HomotopicRel g {x₀} := by
  rw [← hx₀]
  refine homotopicRel_skeletonLT_one_of_forall_homotopicRel hY fun γ h₀ h₁ ↦ ?_
  -- A path between points of the `0`-skeleton is a loop at `x₀`.
  have h₀' : γ 0 = x₀ := by
    rw [← mem_singleton_iff, ← hx₀]
    exact h₀
  have h₁' : γ 1 = x₀ := by
    rw [← mem_singleton_iff, ← hx₀]
    exact h₁
  let p : Path x₀ x₀ := ⟨γ, h₀', h₁'⟩
  have h := congrArg CategoryTheory.End.asHom <|
    DFunLike.congr_fun hfg (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))
  simp only [FundamentalGroup.mapOfEq_apply] at h
  -- A homotopy of paths is a homotopy relative to `{0, 1}` of the underlying maps `f ∘ γ` and
  -- `g ∘ γ`; the casts along `hf` and `hg` only change the endpoint proofs.
  obtain ⟨H⟩ := Path.Homotopic.Quotient.exact h
  exact ⟨H⟩

section ArbitraryCWComplex

/-- Deform `f` relative to a `0`-cell `v₀` on the discrete `0`-skeleton `A` along the paths
`(f ∘ α_a)⁻¹ · (g ∘ α_a)` so that the resulting map `f₁` agrees with `g` on `A` and carries each
chosen path `α_a` into the homotopy class of `g ∘ α_a`. -/
private lemma exists_homotopicRel_eq_on_skeletonLT_one {C : Set X} [CWComplex C]
    {v₀ : C} (hv₀ : (v₀ : X) ∈ skeletonLT C 1) {f g : C(C, Y)} (hg : g v₀ = f v₀)
    (α : (a : (Subtype.val ⁻¹' (skeletonLT C ((1 : ℕ) : ℕ∞) : Set X) : Set C)) → Path v₀ a)
    (hα₀ : α ⟨v₀, hv₀⟩ = Path.refl v₀) :
    ∃ (f₁ : C(C, Y)) (hf₁v : f₁ v₀ = f v₀)
      (hf₁ : ∀ a : (Subtype.val ⁻¹' (skeletonLT C ((1 : ℕ) : ℕ∞) : Set X) : Set C), f₁ a = g a),
      f.HomotopicRel f₁ {v₀} ∧
      ∀ a : (Subtype.val ⁻¹' (skeletonLT C ((1 : ℕ) : ℕ∞) : Set X) : Set C),
        Path.Homotopic.Quotient.mk ((α a).map f₁.continuous) =
          Path.Homotopic.Quotient.cast (Path.Homotopic.Quotient.mk ((α a).map g.continuous))
            (hf₁v.trans hg.symm) (hf₁ a) := by
  classical
  -- Step 1: Identify `A` with the discrete `0`-skeleton and extend the vertexwise path family `β`
  -- to a homotopy `G` on `C` fixing `v₀`.
  let A : Set C := Subtype.val ⁻¹' (skeletonLT C ((1 : ℕ) : ℕ∞) : Set X)
  have := zeroSkeletonDiscreteTopology C
  let eA : A ≃ₜ ↑(skeletonLT C ((1 : ℕ) : ℕ∞)) :=
    { toFun := fun a ↦ ⟨(a : C), a.property⟩
      invFun := fun b ↦
        ⟨⟨(b : X), (skeletonLT C ((1 : ℕ) : ℕ∞)).subset_complex b.property⟩, b.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have : DiscreteTopology A := eA.symm.discreteTopology
  let β (a : A) : Path (f a) (g a) :=
    if h : (a : C) = v₀ then
      (Path.refl (f v₀)).cast (congrArg f h) ((congrArg g h).trans hg)
    else ((α a).map f.continuous).symm.trans (((α a).map g.continuous).cast hg.symm rfl)
  let H₀ : C(I × A, Y) :=
    (ContinuousMap.uncurry ⟨fun a : A ↦ (β a).toContinuousMap, continuous_of_discreteTopology⟩).comp
      ContinuousMap.prodSwap
  obtain ⟨G, hG₀, hG₁⟩ :=
    (hasHomotopyExtensionProperty_skeletonLT (C := C) 1).exists_extension_of_isClosed
      (hasHomotopyExtensionProperty_skeletonLT (C := C) 1).isClosed f H₀ fun a ↦ by simp [H₀]
  let f₁ : C(C, Y) := ⟨fun x ↦ G (1, x), by fun_prop⟩
  have hf₁ (a : A) : f₁ a = g a := (hG₁ 1 a).trans (by simp [H₀])
  have hGv₀ (t : I) : G (t, v₀) = f v₀ := (hG₁ t ⟨v₀, hv₀⟩).trans (by simp [H₀, β])
  let Grel : f.HomotopyRel f₁ {v₀} :=
    { toContinuousMap := G, map_zero_left := hG₀, map_one_left := fun _ ↦ rfl
      prop' := fun t x hx ↦ by rw [mem_singleton_iff.1 hx]; exact hGv₀ t }
  refine ⟨f₁, hGv₀ 1, hf₁, ⟨Grel⟩, fun a ↦ ?_⟩
  -- Step 2: For `a ≠ v₀`, trace naturality along `α a` cancels `f ∘ α a` against `β a`.
  by_cases ha : (a : C) = v₀
  · obtain rfl : a = ⟨v₀, hv₀⟩ := Subtype.ext ha
    rw [Subsingleton.elim (hf₁ ⟨v₀, hv₀⟩) ((hGv₀ 1).trans hg.symm), hα₀]
    simp
  · have heval_v₀ : Grel.toHomotopy.evalAt v₀ = (Path.refl (f v₀)).cast rfl (hGv₀ 1) :=
      Path.ext (funext hGv₀)
    have heval_a : Grel.toHomotopy.evalAt a = (β a).cast rfl (hf₁ a) :=
      Path.ext <| funext fun t ↦ (hG₁ t a).trans (by simp [H₀])
    have h := Path.Homotopic.Quotient.evalAt_trans_map_of_mk_evalAt_eq Grel.toHomotopy (α a) hg
      (hf₁ a) (by simp [heval_a, β, ha])
    simp only [heval_v₀, Path.Homotopic.Quotient.mk_cast, Path.Homotopic.Quotient.mk_refl,
      Path.Homotopic.Quotient.cast_refl_trans] at h
    simpa using congrArg (fun q ↦ q.cast (hGv₀ 1) rfl) h

/-- Pointed uniqueness at a `0`-cell `v₀ ∈ skeletonLT C 1`, when higher homotopy groups of `Y`
vanish everywhere. -/
private lemma homotopicRel_of_mem_skeletonLT_one {C : Set X} [CWComplex C] [PathConnectedSpace C]
    (hY : ∀ (y : Y) (n : ℕ), Subsingleton (π_ (n + 2) Y y)) {v₀ : C}
    (hv₀ : (v₀ : X) ∈ skeletonLT C 1) {f g : C(C, Y)} {y₀ : Y}
    (hf : f v₀ = y₀) (hg : g v₀ = y₀)
    (hfg : FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg) :
    f.HomotopicRel g {v₀} := by
  classical
  subst hf
  -- Deform `f` relative to `{v₀}` so it agrees with `g` on the `0`-skeleton and along chosen paths
  -- `α a` from `v₀` to each `0`-cell `a`.
  let A : Set C := Subtype.val ⁻¹' (skeletonLT C ((1 : ℕ) : ℕ∞) : Set X)
  let α (a : A) : Path v₀ a :=
    if h : (a : C) = v₀ then (Path.refl v₀).cast rfl h else PathConnectedSpace.somePath v₀ a
  obtain ⟨f₁, hf₁v, hf₁, hff₁, hα⟩ :=
    exists_homotopicRel_eq_on_skeletonLT_one hv₀ hg α (by simp [α])
  have hf₁g_map : FundamentalGroup.mapOfEq f₁ hf₁v = FundamentalGroup.mapOfEq g hg :=
    (FundamentalGroup.mapOfEq_eq_of_homotopicRel rfl hf₁v (mem_singleton v₀) hff₁).symm.trans hfg
  -- Every path `p` between `0`-cells closes up via `α` to a loop `ℓ` at `v₀`, on which `f₁` and `g`
  -- agree up to homotopy; cancelling the `α`-legs yields agreement on `p`.
  have hskel : f₁.HomotopicRel g {x : C | (x : X) ∈ skeletonLT C 1} := by
    refine homotopicRel_skeletonLT_one_of_forall_homotopicRel hY fun γ h₀ h₁ ↦ ?_
    let a₀ : A := ⟨γ 0, h₀⟩
    let a₁ : A := ⟨γ 1, h₁⟩
    let p : Path (a₀ : C) (a₁ : C) := ⟨γ, rfl, rfl⟩
    let ℓ : Path v₀ v₀ := (α a₀).trans (p.trans (α a₁).symm)
    have hℓ := congrArg
      (fun q : Path.Homotopic.Quotient (f v₀) (f v₀) ↦ Path.Homotopic.Quotient.cast q hf₁v hf₁v) <|
      congrArg CategoryTheory.End.asHom <|
      DFunLike.congr_fun hf₁g_map (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ℓ))
    rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply,
      ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_map] at hℓ
    simp only [Path.Homotopic.Quotient.cast_cast, Path.Homotopic.Quotient.cast_rfl_rfl, ℓ,
      Path.map_trans, ← Path.map_symm, Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_symm] at hℓ
    rw [Path.Homotopic.Quotient.cast_trans _ _ (hf₁v.trans hg.symm) (hf₁ a₀) (hf₁v.trans hg.symm),
      Path.Homotopic.Quotient.cast_trans _ _ (hf₁ a₀) (hf₁ a₁) (hf₁v.trans hg.symm),
      ← Path.Homotopic.Quotient.symm_cast, ← hα a₀, ← hα a₁] at hℓ
    have hedge := Path.Homotopic.Quotient.trans_right_cancel
      (Path.Homotopic.Quotient.trans_left_cancel hℓ)
    rw [← Path.Homotopic.Quotient.mk_cast] at hedge
    obtain ⟨H⟩ := Path.Homotopic.Quotient.exact hedge
    exact ⟨H⟩
  exact hff₁.trans (hskel.mono fun x hx ↦ by rw [mem_singleton_iff.1 hx]; exact hv₀)

/-- Pointed uniqueness at an arbitrary base point `x₀ : C`, when higher homotopy groups of `Y`
vanish everywhere. -/
private lemma homotopicRel_of_forall_subsingleton {C : Set X} [CWComplex C] [PathConnectedSpace C]
    (hY : ∀ (y : Y) (n : ℕ), Subsingleton (π_ (n + 2) Y y)) {x₀ : C} {f g : C(C, Y)} {y₀ : Y}
    (hf : f x₀ = y₀) (hg : g x₀ = y₀)
    (hfg : FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg) :
    f.HomotopicRel g {x₀} := by
  subst hf
  -- Step 1: Move `f` at a `0`-cell `v₀` along `γ_v = (f ∘ δ)⁻¹ · (g ∘ δ)` so `f₁ v₀ = g v₀` and
  -- `(f₁)_* = g_*` at `v₀`, then apply `0`-cell uniqueness relative to `{v₀}`.
  obtain ⟨w₀, hw₀⟩ := nonempty_skeletonLT_one (C := C) ⟨x₀, x₀.property⟩
  let v₀ : C := ⟨w₀, (skeletonLT C ((1 : ℕ) : ℕ∞)).subset_complex hw₀⟩
  let δ : Path x₀ v₀ := PathConnectedSpace.somePath x₀ v₀
  let γ_v : Path (f v₀) (g v₀) :=
    (δ.map f.continuous).symm.trans ((δ.map g.continuous).cast hg.symm rfl)
  obtain ⟨f₁, hf₁v, H₁, hH₁, -⟩ :=
    (hasHomotopyExtensionProperty_singleton
      (notMem_empty _)).exists_mapOfEq_eq_fundamentalGroupMulEquivOfPath_map
      isClosed_singleton f γ_v
  have heval₁ : H₁.evalAt v₀ = γ_v.cast rfl hf₁v := Path.ext (funext hH₁)
  have hf₁g_v₀ := H₁.mapOfEq_eq_of_evalAt_basepointChange δ rfl hg hf₁v rfl heval₁ hfg
  obtain ⟨H₂⟩ := homotopicRel_of_mem_skeletonLT_one hY hw₀ hf₁v rfl hf₁g_v₀
  -- Step 2: The combined homotopy `H = H₁.trans H₂` has trace `γ_v` at `v₀`, so trace naturality
  -- along `δ` makes `H.evalAt x₀` null-homotopic; straighten `H` at `{x₀}`.
  let H : f.Homotopy g := H₁.trans H₂.toHomotopy
  refine (hasHomotopyExtensionProperty_singleton
    (notMem_empty _)).homotopicRel_singleton_of_homotopic_refl isClosed_singleton H rfl hg ?_
  apply Path.Homotopic.Quotient.exact
  have hH₂ : H₂.toHomotopy.evalAt v₀ = (Path.refl (g v₀)).cast hf₁v rfl :=
    Path.ext <| funext fun t ↦ (H₂.prop t v₀ (mem_singleton v₀)).trans hf₁v
  have h := Path.Homotopic.Quotient.evalAt_trans_map_of_mk_evalAt_eq H δ hg rfl (by
    rw [ContinuousMap.Homotopy.evalAt_trans, Path.Homotopic.Quotient.mk_trans, heval₁, hH₂,
      Path.Homotopic.Quotient.mk_cast, Path.Homotopic.Quotient.mk_cast,
      Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.trans_cast_refl,
      Path.Homotopic.Quotient.cast_cast, Path.Homotopic.Quotient.cast_rfl_rfl]
    simp [γ_v])
  rw [← Path.Homotopic.Quotient.cast_refl_trans hg] at h
  simpa using congrArg (fun q ↦ q.cast rfl hg.symm)
    (Path.Homotopic.Quotient.trans_right_cancel h)

/-- **Pointed maps out of a path-connected Hausdorff CW complex are determined by `π₁` (Hatcher,
Proposition 1B.9, uniqueness).** Let `C` be a path-connected CW complex in a Hausdorff space `X`
with arbitrary base point `x₀`, and let `(Y, y₀)` be a based space (in any universe) with
`πₙ(Y, y₀) = 0` for all `n ≥ 2` (without assuming `Y` is path connected). Two pointed maps
`f, g : (C, x₀) → (Y, y₀)` inducing the same homomorphism `π₁(C, x₀) →* π₁(Y, y₀)` are homotopic
relative to `{x₀}`. -/
theorem homotopicRel_of_mapOfEq_eq {C : Set X} [CWComplex C] [PathConnectedSpace C]
    {x₀ : C} {y₀ : Y} (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀))
    {f g : C(C, Y)} (hf : f x₀ = y₀) (hg : g x₀ = y₀)
    (hfg : FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg) :
    f.HomotopicRel g {x₀} := by
  -- Both `f` and `g` land in `pathComponent y₀`, where all higher homotopy groups vanish.
  let S : Set Y := pathComponent y₀
  let y₀' : S := ⟨y₀, mem_pathComponent_self y₀⟩
  let f' : C(C, S) := ⟨fun x ↦ ⟨f x, mem_pathComponent_iff.2 <|
    hf ▸ (PathConnectedSpace.joined x₀ x).map f.continuous⟩, by fun_prop⟩
  let g' : C(C, S) := ⟨fun x ↦ ⟨g x, mem_pathComponent_iff.2 <|
    hg ▸ (PathConnectedSpace.joined x₀ x).map g.continuous⟩, by fun_prop⟩
  have hf' : f' x₀ = y₀' := Subtype.ext hf
  have hg' : g' x₀ = y₀' := Subtype.ext hg
  have hS : ∀ (z : S) (n : ℕ), Subsingleton (π_ (n + 2) S z) := fun z n ↦ by
    have hz : Subsingleton (π_ (n + 2) Y z) :=
      (homotopyGroupEquivOfPath (N := Fin (n + 2)) z.property.somePath).subsingleton_congr.1
        (hY n)
    have hbij := HomotopyGroup.bijective_map_subtypeVal_of_pathComponent_subset
      (N := Fin (n + 2)) (S := S) (x := z) (fun _ hw ↦ z.property.trans hw) rfl
    exact hbij.1.subsingleton
  have hinj : Function.Injective
      (FundamentalGroup.mapOfEq (ContinuousMap.subtypeVal S)
        (rfl : ContinuousMap.subtypeVal S y₀' = y₀)) :=
    ((HomotopyGroup.bijective_map_iff_bijective_mapOfEq (ContinuousMap.subtypeVal S) rfl).1
      (HomotopyGroup.bijective_map_subtypeVal_of_pathComponent_subset
        (N := Fin 1) (S := S) (x := y₀') subset_rfl rfl)).1
  have hfg' : FundamentalGroup.mapOfEq f' hf' = FundamentalGroup.mapOfEq g' hg' :=
    MonoidHom.ext fun a ↦ hinj <| by
      rw [FundamentalGroup.mapOfEq_mapOfEq_eq_mapOfEq rfl hf'
        (rfl : ContinuousMap.subtypeVal S y₀' = y₀) hf a,
        FundamentalGroup.mapOfEq_mapOfEq_eq_mapOfEq rfl hg'
          (rfl : ContinuousMap.subtypeVal S y₀' = y₀) hg a]
      exact DFunLike.congr_fun hfg a
  exact (homotopicRel_of_forall_subsingleton hS hf' hg' hfg').comp_continuousMap
    (ContinuousMap.subtypeVal S)

/-- **Pointed homotopy classification out of a path-connected Hausdorff CW complex.** Pointed maps
`(C, x₀) → (Y, y₀)` into a space with `πₙ(Y, y₀) = 0` (`n ≥ 2`) are homotopic relative to `{x₀}`
if and only if they induce the same homomorphism on fundamental groups. -/
theorem homotopicRel_singleton_iff_mapOfEq_eq {C : Set X} [CWComplex C] [PathConnectedSpace C]
    {x₀ : C} {y₀ : Y} (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀))
    {f g : C(C, Y)} (hf : f x₀ = y₀) (hg : g x₀ = y₀) :
    f.HomotopicRel g {x₀} ↔ FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg :=
  ⟨FundamentalGroup.mapOfEq_eq_of_homotopicRel hf hg (mem_singleton x₀),
    homotopicRel_of_mapOfEq_eq hY hf hg⟩

/-- **Pointed maps out of a path-connected Hausdorff CW complex on `univ` are determined by `π₁`
(Hatcher, Proposition 1B.9, uniqueness).** Two maps `f, g : X → Y` sending an arbitrary base point
`x₀` to `y₀` into a space with `πₙ(Y, y₀) = 0` (`n ≥ 2`) that induce the same homomorphism
`π₁(X, x₀) →* π₁(Y, y₀)` are homotopic relative to `{x₀}`. -/
theorem homotopicRel_of_mapOfEq_eq_of_cwComplex [CWComplex (univ : Set X)] [PathConnectedSpace X]
    {x₀ : X} {y₀ : Y} (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀))
    {f g : C(X, Y)} (hf : f x₀ = y₀) (hg : g x₀ = y₀)
    (hfg : FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg) :
    f.HomotopicRel g {x₀} := by
  let e := Homeomorph.Set.univ X
  refine (ContinuousMap.HomotopicRel.comp_homeomorph_iff e).1 ?_
  have hpre : (e : C((univ : Set X), X)) ⁻¹' {x₀} = {⟨x₀, mem_univ x₀⟩} := by
    ext; simp [e, Subtype.ext_iff]
  rw [hpre]
  refine homotopicRel_of_mapOfEq_eq (x₀ := ⟨x₀, mem_univ x₀⟩) hY hf hg (MonoidHom.ext fun p ↦ ?_)
  rw [← FundamentalGroup.mapOfEq_comp f (e : C((univ : Set X), X)) rfl hf,
    ← FundamentalGroup.mapOfEq_comp g (e : C((univ : Set X), X)) rfl hg]
  exact DFunLike.congr_fun hfg _

/-- **Pointed homotopy classification for a path-connected Hausdorff CW structure on `univ`.** -/
theorem homotopicRel_singleton_iff_mapOfEq_eq_of_cwComplex [CWComplex (univ : Set X)]
    [PathConnectedSpace X] {x₀ : X} {y₀ : Y} (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀))
    {f g : C(X, Y)} (hf : f x₀ = y₀) (hg : g x₀ = y₀) :
    f.HomotopicRel g {x₀} ↔ FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg :=
  ⟨FundamentalGroup.mapOfEq_eq_of_homotopicRel hf hg (mem_singleton x₀),
    homotopicRel_of_mapOfEq_eq_of_cwComplex hY hf hg⟩

/-- **Free homotopy classification out of a path-connected Hausdorff CW complex (Hatcher,
Proposition 1B.9, unbased uniqueness).** Let `C` be a path-connected CW complex in a Hausdorff
space `X` with base point `x₀`, and let `f, g : C → Y` be continuous maps into a space with
`πₙ(Y, g x₀) = 0` for all `n ≥ 2`. Then `f` and `g` are freely homotopic if and only if there is a
path `γ` from `f x₀` to `g x₀` such that changing base point along `γ` intertwines `f_*` and `g_*`
on `π₁(C, x₀)`. -/
theorem homotopic_iff_exists_path_fundamentalGroupMulEquivOfPath {C : Set X} [CWComplex C]
    [PathConnectedSpace C] (x₀ : C) {f g : C(C, Y)}
    (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y (g x₀))) :
    f.Homotopic g ↔
      ∃ γ : Path (f x₀) (g x₀),
        ∀ a, FundamentalGroup.fundamentalGroupMulEquivOfPath γ (FundamentalGroup.map f x₀ a) =
          FundamentalGroup.map g x₀ a := by
  refine ⟨fun ⟨H⟩ ↦ ⟨H.evalAt x₀, H.fundamentalGroupMulEquivOfPath_evalAt_map x₀⟩, ?_⟩
  rintro ⟨γ, hγ⟩
  -- Deform `f` along `γ` at `x₀` to obtain `f₁` with `f₁ x₀ = g x₀` and `(f₁)_* = g_*`.
  obtain ⟨f₁, hf₁, F, -, hf₁π⟩ :=
    (hasHomotopyExtensionProperty_singleton
      (notMem_empty _)).exists_mapOfEq_eq_fundamentalGroupMulEquivOfPath_map
      isClosed_singleton f γ
  have hmap : FundamentalGroup.mapOfEq f₁ hf₁ = FundamentalGroup.mapOfEq g rfl :=
    MonoidHom.ext fun a ↦
      (hf₁π a).trans ((hγ a).trans (DFunLike.congr_fun (FundamentalGroup.mapOfEq_rfl g) a).symm)
  exact ContinuousMap.Homotopic.trans ⟨F⟩
    (homotopicRel_of_mapOfEq_eq hY hf₁ rfl hmap).homotopic

/-- **Free homotopy classification out of a path-connected Hausdorff CW complex on `univ` (Hatcher,
Proposition 1B.9, unbased uniqueness).** -/
theorem homotopic_iff_exists_path_fundamentalGroupMulEquivOfPath_of_cwComplex
    [CWComplex (univ : Set X)] [PathConnectedSpace X] (x₀ : X) {f g : C(X, Y)}
    (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y (g x₀))) :
    f.Homotopic g ↔
      ∃ γ : Path (f x₀) (g x₀),
        ∀ a, FundamentalGroup.fundamentalGroupMulEquivOfPath γ (FundamentalGroup.map f x₀ a) =
          FundamentalGroup.map g x₀ a := by
  refine ⟨fun ⟨H⟩ ↦ ⟨H.evalAt x₀, H.fundamentalGroupMulEquivOfPath_evalAt_map x₀⟩, ?_⟩
  rintro ⟨γ, hγ⟩
  let e := Homeomorph.Set.univ X
  let u₀ : (univ : Set X) := ⟨x₀, mem_univ x₀⟩
  refine (ContinuousMap.Homotopic.comp_homeomorph_iff e).1
    ((homotopic_iff_exists_path_fundamentalGroupMulEquivOfPath
      (f := f.comp (e : C((univ : Set X), X))) (g := g.comp (e : C((univ : Set X), X)))
      u₀ hY).2 ⟨γ, fun a ↦ ?_⟩)
  have hcomp (k : C(X, Y)) :
      FundamentalGroup.map (k.comp (e : C((univ : Set X), X))) u₀ a =
        FundamentalGroup.map k x₀ (FundamentalGroup.map (e : C((univ : Set X), X)) u₀ a) := by
    simp only [← FundamentalGroup.mapOfEq_rfl]
    exact (FundamentalGroup.mapOfEq_comp k (e : C((univ : Set X), X)) rfl rfl a).symm
  rw [hcomp f, hcomp g]
  exact hγ _

end ArbitraryCWComplex

end TauCeti
