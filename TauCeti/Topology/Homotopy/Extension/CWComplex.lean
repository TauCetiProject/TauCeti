/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Subcomplex
public import TauCeti.Topology.CWComplex.Classical.Skeleton.Induction
public import TauCeti.Topology.Homotopy.Extension.Ball

/-!
# Relative CW inclusions are closed cofibrations

The base `D` of a relative CW complex `C` has the homotopy extension property inside `C`, and so
does every skeleton of `C`.  As `X` is Hausdorff, these subsets are closed
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
    have hmap : Continuous fun y : closedBall (0 : Fin n → ℝ) 1 ↦ map n j y :=
      (continuousOn n j).comp_continuous continuous_subtype_val fun y ↦ y.2
    obtain ⟨K, hK0, hKs⟩ :=
      (hasHomotopyExtensionProperty_sphere_closedBall (E := Fin n → ℝ)).exists_extension_of_isClosed
        (isClosed_sphere.preimage continuous_subtype_val)
        (f.comp ⟨fun y ↦ ⟨map n j y, map_mem_skeletonLT_succ j (mem_closedBall_zero_iff.1 y.2)⟩,
          hmap.subtype_mk _⟩)
        (G.comp ⟨fun p ↦ (p.1, ⟨⟨map n j p.2,
          map_mem_skeletonLT_succ j (mem_closedBall_zero_iff.1 p.2.1.2)⟩,
          cellFrontier_subset_skeletonLT n j ⟨p.2, p.2.2, rfl⟩⟩),
          continuous_fst.prodMk (((hmap.comp
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

end TauCeti
