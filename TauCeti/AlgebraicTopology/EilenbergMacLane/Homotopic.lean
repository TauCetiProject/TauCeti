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

/-!
# Maps from a CW complex into a space without higher homotopy

Let `Y` be a space whose homotopy groups `πₙ(Y, y)` vanish for `n ≥ 2` at every point `y`, such as
a `K(H, 1)`. A map from a CW complex into `Y` is determined up to homotopy by what it does on the
`1`-skeleton up to homotopy: two maps `f g : C → Y` out of a relative CW complex `(C, D)` that, on
every path in `C` between points of the `0`-skeleton, agree up to homotopy relative to the
endpoints, are homotopic relative to the `0`-skeleton
(`TauCeti.homotopicRel_skeletonLT_one_of_forall_homotopicRel`). For a complex whose only `0`-cell
is its base point, this says that pointed maps inducing the same homomorphism of fundamental groups
are homotopic relative to the base point (`TauCeti.homotopicRel_singleton_of_mapOfEq_eq`). This is
the uniqueness half of Hatcher's Proposition 1B.9 for complexes with a single `0`-cell, the case
to which Hatcher reduces by collapsing a maximal tree; for the cellular classifying space, the
existence half is `TauCeti.exists_mapOfEq_cellularClassifyingSpace`.

The proof reads a homotopy from `f` to `g` relative to a set `A` as a deformation, relative to
`A`, of the map `(f, g) : C → Y × Y` into the diagonal. Since the diagonal `Δ ⊆ Y × Y` is a
retract of `Y × Y` and `πₙ(Y × Y)` vanishes for `n ≥ 2`, the exact sequence of the pair shows that
the relative homotopy sets `πₙ(Y × Y, Δ)` vanish for `n ≥ 2`
(`TauCeti.subsingleton_relHomotopyGroup_diagonal`). So the compression lemma deforms `(f, g)` into
`Δ` relative to `D` as soon as `(C, D)` has no cells of dimension `0` or `1` and `f = g` on `D`
(`TauCeti.homotopicRel_base_of_isEmpty_cell`). In general the hypothesis on paths first lets one
homotope `f`, relative to the `0`-skeleton, to agree with `g` on every `1`-cell, and the
compression lemma then applies to `C` relative to its `1`-skeleton
(`Topology.RelCWComplex.Subcomplex.relCWComplex`), which has no cells of dimension below `2`.

Only the vanishing of the higher homotopy groups of `Y` is used: neither space needs to be path
connected, and `Y` need not have the homotopy type of a CW complex.

## Main results

* `TauCeti.subsingleton_relHomotopyGroup_diagonal`: the relative homotopy sets of the diagonal in
  `Y × Y` vanish from degree `2` on.
* `TauCeti.homotopicRel_base_of_isEmpty_cell`: maps agreeing on the base of a relative CW complex
  without cells of dimension `0` and `1` are homotopic relative to the base.
* `TauCeti.homotopicRel_skeletonLT_one_of_forall_homotopicRel`: maps agreeing up to homotopy on
  paths between points of the `0`-skeleton are homotopic relative to the `0`-skeleton.
* `TauCeti.homotopicRel_singleton_of_mapOfEq_eq`: **pointed maps from a CW complex with a single
  `0`-cell into a space without higher homotopy are determined, up to homotopy relative to the
  base point, by the homomorphism they induce on fundamental groups.**

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
  have hr : r (b : Y × Y) = b := Subtype.ext (Prod.ext rfl b.2)
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
    refine ⟨fun i ↦ (E.relCWComplexCellEquiv n i).2 ?_⟩
    simp only [E, skeletonLT_I, mem_ofPred_eq]
    exact_mod_cast hn
  -- The structure relative to `E` is not an instance: `C` already carries one relative to `D`.
  have h := @homotopicRel_base_of_isEmpty_cell Y _ X _ _ C E E.relCWComplex (hE 0 two_pos)
    (hE 1 one_lt_two) hY f₁ g hf₁g
  exact hff₁.trans (h.mono fun x hx ↦ skeletonLT_mono (by norm_num) hx)

/-- **Maps into a space without higher homotopy are determined by their effect on `π₁`.** Let `C`
be a relative CW complex whose `0`-skeleton is a single point `x₀`, such as a CW complex with a
single `0`-cell, and let `Y` be a space whose homotopy groups vanish from degree `2` on, at every
point, such as a `K(H, 1)`. Two maps `C → Y` sending `x₀` to `y₀` and inducing the same
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

end TauCeti
