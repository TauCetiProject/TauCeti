/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.Skeleton.Induction
public import TauCeti.Topology.Homotopy.Extension.Ball

/-!
# Extending maps over a relative CW complex

Let `C` be a relative CW complex with base `D`, and let `Y` be a space such that every map from
the sphere `Sⁿ⁻¹` to `Y` is null-homotopic, for each `n` for which `C` has `n`-cells.  Then every
map `D → Y` extends to a map `C → Y`, and more generally every map out of the skeleton
`skeletonLT C k` extends over `C` when the condition holds for the cells of dimension at least
`k`.

The extension is built skeleton by skeleton.  An `n`-cell is attached along the restriction of its
characteristic map to the sphere, so a map on `skeletonLT C n` composed with that restriction is
a map `Sⁿ⁻¹ → Y`.  It is null-homotopic by hypothesis, so it extends over the closed ball
(`ContinuousMap.nullhomotopic_iff_exists_extension_closedBall`), and these extensions glue to a
map on `skeletonLT C (n + 1)` (`TauCeti.exists_continuousMap_prod_skeletonLT_succ`).  The maps on
the successive skeleta glue to a map on `C`
(`TauCeti.exists_continuousMap_prod_complex_of_skeletonLT`).

The spheres are those of the characteristic maps, the unit spheres of `Fin n → ℝ` with the sup
norm.  For `n = 0` the sphere is empty and the closed ball is a point, so the hypothesis for
`0`-cells says that `Y` is nonempty.  For path-connected `Y` the condition in dimension `n` is
Hatcher's hypothesis `πₙ₋₁(Y) = 0`, stated through free null-homotopies of maps from the sphere.

## Main results

* `TauCeti.exists_extension_skeletonLT_of_nullhomotopic`: maps out of `skeletonLT C k` extend over
  `C` when maps to `Y` from the boundary spheres of the cells of dimension at least `k` are
  null-homotopic.
* `TauCeti.exists_extension_of_nullhomotopic`: the **extension lemma**, maps out of the base `D`
  extend over `C`.
* `TauCeti.exists_extension_of_contractibleSpace`: maps out of the base into a contractible space
  extend over `C`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Lemma 4.7 (the extension lemma).
* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter II, Section 3.
-/

public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]
  {Y : Type*} [TopologicalSpace Y]

section Seq

variable {k : ℕ}

/-- A map on `skeletonLT C n` extends over the closed `n`-cells when its compositions with the
attaching maps of the `n`-cells are null-homotopic. -/
private lemma exists_extension_skeletonLT_succ {n : ℕ}
    (h : Nonempty (cell C n) → ∀ g : C(sphere (0 : Fin n → ℝ) 1, Y), g.Nullhomotopic)
    (f : C(Unit × (skeletonLT C n : Set X), Y)) :
    ∃ F : C(Unit × (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X), Y),
      ∀ z (x : X) (hx : x ∈ (skeletonLT C n : Set X)),
        F (z, ⟨x, skeletonLT_mono (by exact_mod_cast n.le_succ) hx⟩) = f (z, ⟨x, hx⟩) := by
  have hext (j : cell C n) : ∃ K : C(Unit × closedBall (0 : Fin n → ℝ) 1, Y),
      ∀ z (y : closedBall (0 : Fin n → ℝ) 1) (hy : (y : Fin n → ℝ) ∈ sphere 0 1),
        K (z, y) = f (z, ⟨map n j y, cellFrontier_subset_skeletonLT n j ⟨y, hy, rfl⟩⟩) := by
    -- The attaching map of `j` followed by `f` is null-homotopic, so it extends over the ball.
    let g : C(sphere (0 : Fin n → ℝ) 1, Y) :=
      ⟨fun y ↦ f ((), ⟨map n j y, cellFrontier_subset_skeletonLT n j ⟨y, y.2, rfl⟩⟩),
        f.continuous.comp (continuous_const.prodMk
          (((continuousOn n j).comp_continuous continuous_subtype_val
            fun y ↦ sphere_subset_closedBall y.2).subtype_mk _))⟩
    obtain ⟨G, hG⟩ := (g.nullhomotopic_iff_exists_extension_closedBall).1 (h ⟨j⟩ g)
    exact ⟨G.comp ⟨Prod.snd, continuous_snd⟩, fun () y hy ↦ hG ⟨y, hy⟩⟩
  choose K hK using hext
  obtain ⟨F, hF, -⟩ := exists_continuousMap_prod_skeletonLT_succ f K hK
  exact ⟨F, hF⟩

variable (k) in
/-- The extensions of a map on `Unit × skeletonLT C k` over the successive skeleta
`skeletonLT C (k + j)`, each obtained from the previous one by extending over the closed cells. -/
private def extensionSeq
    (h : ∀ n, k ≤ n → Nonempty (cell C n) → ∀ g : C(sphere (0 : Fin n → ℝ) 1, Y),
      g.Nullhomotopic)
    (f : C(Unit × (skeletonLT C k : Set X), Y)) :
    (j : ℕ) → C(Unit × (skeletonLT C ((k + j : ℕ) : ℕ∞) : Set X), Y)
  | 0 => f
  | j + 1 =>
    (exists_extension_skeletonLT_succ (h (k + j) (Nat.le_add_right k j))
      (extensionSeq h f j)).choose

private lemma extensionSeq_succ_apply
    {h : ∀ n, k ≤ n → Nonempty (cell C n) → ∀ g : C(sphere (0 : Fin n → ℝ) 1, Y),
      g.Nullhomotopic}
    {f : C(Unit × (skeletonLT C k : Set X), Y)} (j : ℕ) (z : Unit) (x : X)
    (hx : x ∈ (skeletonLT C ((k + j : ℕ) : ℕ∞) : Set X)) :
    extensionSeq k h f (j + 1)
        (z, ⟨x, skeletonLT_mono (by exact_mod_cast (k + j).le_succ) hx⟩) =
      extensionSeq k h f j (z, ⟨x, hx⟩) :=
  (exists_extension_skeletonLT_succ (h (k + j) (Nat.le_add_right k j))
    (extensionSeq k h f j)).choose_spec z x hx

end Seq

/-- **Maps out of a skeleton extend over a relative CW complex** when, for every `n ≥ k` such that
`C` has `n`-cells, every map from the unit sphere of `Fin n → ℝ` to `Y` is null-homotopic. -/
theorem exists_extension_skeletonLT_of_nullhomotopic (k : ℕ)
    (h : ∀ n, k ≤ n → Nonempty (cell C n) → ∀ g : C(sphere (0 : Fin n → ℝ) 1, Y),
      g.Nullhomotopic)
    (f : C((skeletonLT C k : Set X), Y)) :
    ∃ F : C(C, Y), ∀ x : (skeletonLT C k : Set X),
      F ⟨x, (skeletonLT C k).subset_complex x.2⟩ = f x := by
  obtain ⟨G, hG⟩ := exists_continuousMap_prod_complex_of_skeletonLT
    (extensionSeq k h (f.comp ⟨Prod.snd, continuous_snd⟩)) extensionSeq_succ_apply
  exact ⟨G.comp ⟨fun x ↦ ((), x), by fun_prop⟩, fun x ↦ hG 0 () x x.2⟩

/-- **The extension lemma.**  Every map out of the base of a relative CW complex extends over the
complex when, for every `n` such that `C` has `n`-cells, every map from the unit sphere of
`Fin n → ℝ` to `Y` is null-homotopic. -/
theorem exists_extension_of_nullhomotopic
    (h : ∀ n, Nonempty (cell C n) → ∀ g : C(sphere (0 : Fin n → ℝ) 1, Y), g.Nullhomotopic)
    (f : C(D, Y)) :
    ∃ F : C(C, Y), ∀ x : D, F ⟨x, base_subset_complex x.2⟩ = f x := by
  have h0 : (skeletonLT C (0 : ℕ) : Set X) = D := skeletonLT_zero_eq_base
  obtain ⟨F, hF⟩ := exists_extension_skeletonLT_of_nullhomotopic 0 (fun n _ ↦ h n)
    (f.comp ⟨Set.inclusion h0.le, continuous_inclusion h0.le⟩)
  exact ⟨F, fun x ↦ hF ⟨x, h0.ge x.2⟩⟩

/-- Every map out of the base of a relative CW complex into a contractible space extends over the
complex. -/
theorem exists_extension_of_contractibleSpace [ContractibleSpace Y] (f : C(D, Y)) :
    ∃ F : C(C, Y), ∀ x : D, F ⟨x, base_subset_complex x.2⟩ = f x :=
  exists_extension_of_nullhomotopic (fun _ _ g ↦ (id_nullhomotopic Y).comp_left g) f

end TauCeti
