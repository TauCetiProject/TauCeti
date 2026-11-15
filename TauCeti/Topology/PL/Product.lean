/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PL.Map

/-!
# Products of piecewise-linear maps

Pairing two piecewise-affine maps refines their finite polyhedral covers by intersections.
Localizing this construction gives pairing and products of PL maps, and characterizes PL
maps into a product by their components. The product theorem supplies PL coordinate changes
for product manifolds, including products of models with boundary and corners.

Reference: C. Rourke and B. Sanderson, *Introduction to Piecewise-Linear Topology*,
Chapters 1–2. The affine pieces use Mathlib's `ContinuousAffineMap.prod`.
-/

public section

open Set Filter Topology

namespace TauCeti

variable {E F G D : Type*}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
  [AddCommGroup D] [Module ℝ D] [TopologicalSpace D]

/-- Pairing two piecewise-affine maps on the same set is piecewise affine. -/
theorem IsPiecewiseAffineOn.prodMk {f : E → F} {g : E → G} {s : Set E}
    (hf : IsPiecewiseAffineOn f s) (hg : IsPiecewiseAffineOn g s) :
    IsPiecewiseAffineOn (fun x => (f x, g x)) s := by
  obtain ⟨n, C, A, hC, hcovC, hA⟩ := isPiecewiseAffineOn_iff.mp hf
  obtain ⟨m, D, B, hD, hcovD, hB⟩ := isPiecewiseAffineOn_iff.mp hg
  refine isPiecewiseAffineOn_of_finite (ι := Fin n × Fin m)
    (C := fun p => C p.1 ∩ D p.2) (A := fun p => (A p.1).prod (B p.2))
    (fun p => (hC p.1).inter (hD p.2)) ?_ ?_
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcovC hx)
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcovD hx)
    exact mem_iUnion.mpr ⟨(i, j), hi, hj⟩
  · rintro ⟨i, j⟩ x ⟨hx, hi, hj⟩
    exact Prod.ext (hA i ⟨hx, hi⟩) (hB j ⟨hx, hj⟩)

/-- A map into a product is piecewise affine exactly when both components are. -/
@[simp]
theorem isPiecewiseAffineOn_prod_iff {f : E → F × G} {s : Set E} :
    IsPiecewiseAffineOn f s ↔
      IsPiecewiseAffineOn (fun x => (f x).1) s ∧
        IsPiecewiseAffineOn (fun x => (f x).2) s := by
  constructor
  · intro hf
    exact ⟨(isPiecewiseAffineOn_continuousAffineMap
      (ContinuousLinearMap.fst ℝ F G).toContinuousAffineMap univ).comp hf
        (mapsTo_univ _ _),
      (isPiecewiseAffineOn_continuousAffineMap
      (ContinuousLinearMap.snd ℝ F G).toContinuousAffineMap univ).comp hf
        (mapsTo_univ _ _)⟩
  · rintro ⟨hf, hg⟩
    exact hf.prodMk hg

/-- Products of piecewise-affine maps are piecewise affine on product sets. -/
theorem IsPiecewiseAffineOn.prodMap {f : E → F} {g : G → D} {s : Set E} {t : Set G}
    (hf : IsPiecewiseAffineOn f s) (hg : IsPiecewiseAffineOn g t) :
    IsPiecewiseAffineOn (Prod.map f g) (s ×ˢ t) := by
  have hfst := hf.comp (isPiecewiseAffineOn_continuousAffineMap
    (ContinuousLinearMap.fst ℝ E G).toContinuousAffineMap (s ×ˢ t))
    (fun _ hx => hx.1)
  have hsnd := hg.comp (isPiecewiseAffineOn_continuousAffineMap
    (ContinuousLinearMap.snd ℝ E G).toContinuousAffineMap (s ×ˢ t))
    (fun _ hx => hx.2)
  exact hfst.prodMk hsnd

/-- Pairing two PL maps on the same set is PL. -/
theorem IsPLOn.prodMk {f : E → F} {g : E → G} {s : Set E}
    (hf : IsPLOn f s) (hg : IsPLOn g s) : IsPLOn (fun x => (f x, g x)) s := by
  rw [isPLOn_iff] at hf hg ⊢
  intro x hx
  obtain ⟨U, hU, hfU⟩ := hf x hx
  obtain ⟨V, hV, hgV⟩ := hg x hx
  exact ⟨U ∩ V, inter_mem hU hV,
    (hfU.mono inter_subset_left).prodMk (hgV.mono inter_subset_right)⟩

/-- A map into a product is PL exactly when both components are. -/
@[simp]
theorem isPLOn_prod_iff {f : E → F × G} {s : Set E} :
    IsPLOn f s ↔ IsPLOn (fun x => (f x).1) s ∧ IsPLOn (fun x => (f x).2) s := by
  constructor
  · intro hf
    exact ⟨(isPLOn_continuousAffineMap
      (ContinuousLinearMap.fst ℝ F G).toContinuousAffineMap univ).comp hf
        (mapsTo_univ _ _),
      (isPLOn_continuousAffineMap
      (ContinuousLinearMap.snd ℝ F G).toContinuousAffineMap univ).comp hf
        (mapsTo_univ _ _)⟩
  · rintro ⟨hf, hg⟩
    exact hf.prodMk hg

/-- Products of PL maps are PL on product sets. No finiteness or openness assumption on
the domains is needed. -/
theorem IsPLOn.prodMap {f : E → F} {g : G → D} {s : Set E} {t : Set G}
    (hf : IsPLOn f s) (hg : IsPLOn g t) : IsPLOn (Prod.map f g) (s ×ˢ t) := by
  rw [isPLOn_iff] at hf hg ⊢
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  obtain ⟨U, hU, hfU⟩ := hf x hx
  obtain ⟨V, hV, hgV⟩ := hg y hy
  exact ⟨U ×ˢ V, nhdsWithin_prod hU hV, hfU.prodMap hgV⟩

end TauCeti
