/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Basic
public import TauCeti.RepresentationTheory.ClassicalGroups.DominantWeight
import TauCeti.Algebra.BigOperators.Fin
import Mathlib.Order.Fin.Basic

/-!
# Cyclic boundaries of hives

Boundary differences are read clockwise along `A → B → C → A`. On each side of a
hive they are antitone, so an integer hive determines three native dominant weights.
The sum of all entries of the three boundary weights is zero. Before imposing hive
inequalities, the boundary restriction is a linear map on the entire space of labellings.

The conventions follow Knutson–Tao, *The honeycomb model of GLₙ(ℂ) tensor
products I*, Appendix 2.
-/

public section

namespace TauCeti.Hive

open Finset

variable {n : ℕ} {R : Type*}

section Group

variable [AddCommGroup R]

/-- Clockwise forward differences along the three sides of a labelling. -/
def boundary (h : Vertex n → R) (s : Fin 3) (i : Fin n) : R :=
  h (Vertex.edge n s i.succ) - h (Vertex.edge n s i.castSucc)

/-- Each boundary entry is the corresponding clockwise forward difference. -/
@[simp] theorem boundary_apply (h : Vertex n → R) (s : Fin 3) (i : Fin n) :
    boundary h s i = h (Vertex.edge n s i.succ) - h (Vertex.edge n s i.castSucc) := (rfl)

@[simp] theorem boundary_zero : boundary (0 : Vertex n → R) = 0 := by
  funext s i
  simp [boundary]

@[simp] theorem boundary_add (h k : Vertex n → R) : boundary (h + k) = boundary h + boundary k := by
  funext s i
  simp only [boundary, Pi.add_apply]
  abel

/-- Boundary differences do not depend on the additive gauge. -/
@[simp] theorem boundary_add_const (h : Vertex n → R) (c : R) :
    boundary (fun p => h p + c) = boundary h := by
  funext s i
  simp [boundary]

/-- The sum along one side is the difference of its endpoint values. -/
theorem sum_boundary (h : Vertex n → R) (s : Fin 3) :
    ∑ i, boundary h s i = h (Vertex.edge n s (Fin.last n)) - h (Vertex.edge n s 0) := by
  simpa only [boundary] using
    Fin.sum_univ_succ_sub_castSucc (fun i => h (Vertex.edge n s i))

/-- The cyclic trace of a boundary is zero, without a normalization assumption. -/
theorem sum_boundary_eq_zero (h : Vertex n → R) : ∑ s, ∑ i, boundary h s i = 0 := by
  simp only [sum_boundary, Fin.sum_univ_three, Vertex.edge_zero, Vertex.edge_one,
    Vertex.edge_two, Vertex.edgeAB_last, Vertex.edgeAB_zero, Vertex.rotate_rotate_rotate]
  abel

/-- Boundary restriction on the full space of labellings is linear. -/
def boundaryLinearMap (K : Type*) [Semiring K] [Module K R] :
    (Vertex n → R) →ₗ[K] (Fin 3 → Fin n → R) where
  toFun := boundary
  map_add' := boundary_add
  map_smul' c h := by
    funext s i
    simp [boundary, smul_sub]

@[simp] theorem boundaryLinearMap_apply (K : Type*) [Semiring K] [Module K R]
    (h : Vertex n → R) : boundaryLinearMap K h = boundary h := (rfl)

end Group

section OrderedGroup

variable [AddCommGroup R] [Preorder R] [IsOrderedAddMonoid R]

private theorem edgeAB_midpoint_inequality {k : ℕ} {h : Vertex (k + 2) → R}
    (hh : IsHive h) (i : Fin (k + 1)) :
    h (Vertex.edgeAB (k + 2) ⟨i, by omega⟩) +
        h (Vertex.edgeAB (k + 2) ⟨i + 2, by omega⟩) ≤
      h (Vertex.edgeAB (k + 2) ⟨i + 1, by omega⟩) +
        h (Vertex.edgeAB (k + 2) ⟨i + 1, by omega⟩) := by
  let p : Vertex k := ⟨k - i, i, 0, by omega⟩
  let u : Vertex 2 := ⟨1, 0, 1, rfl⟩
  let v : Vertex 2 := ⟨0, 1, 1, rfl⟩
  let e : Vertex 2 := ⟨1, 1, 0, rfl⟩
  have h1 := ((isHive_iff h).mp hh) (isRhombus_at_cornerA.add p)
  have h2 := ((isHive_iff h).mp hh) (isRhombus_at_cornerA.rotate.add p)
  have he : p.add e = Vertex.edgeAB (k + 2) ⟨i + 1, by omega⟩ := by
    ext <;> simp [p, e]; omega
  have hA : p.add (Vertex.cornerA 2) = Vertex.edgeAB (k + 2) ⟨i, by omega⟩ := by
    ext <;> simp [p]; omega
  have hB : p.add (Vertex.cornerA 2).rotate =
      Vertex.edgeAB (k + 2) ⟨i + 2, by omega⟩ := by
    ext <;> simp [p]
  have hr1 : (⟨1, 1, 0, rfl⟩ : Vertex 2).rotate = v := by ext <;> simp [v]
  have hr2 : (⟨1, 0, 1, rfl⟩ : Vertex 2).rotate = e := by ext <;> simp [e]
  have hr3 : (⟨0, 1, 1, rfl⟩ : Vertex 2).rotate = u := by ext <;> simp [u]
  rw [hr1, hr2, hr3] at h2
  have hs : (h (p.add (Vertex.cornerA 2)) + h (p.add (Vertex.cornerA 2).rotate)) +
      (h (p.add u) + h (p.add v)) ≤ (h (p.add e) + h (p.add e)) +
      (h (p.add u) + h (p.add v)) := by
    convert add_le_add h1 h2 using 1 <;> dsimp only [u, v, e] <;> abel
  simpa only [he, hA, hB] using (add_le_add_iff_right _).mp hs

/- The boundary dominance proof adds the two unit rhombi sharing the inward triangle
at an edge point. -/
/-- The clockwise differences on each side of a hive labelling are antitone.
This holds for arbitrary ordered abelian group values and without normalization. -/
theorem IsHive.boundary_antitone {h : Vertex n → R} (hh : IsHive h) (s : Fin 3) :
    Antitone (boundary h s) := by
  have base : ∀ {h : Vertex n → R}, IsHive h → Antitone (boundary h 0) := by
    intro h hh
    cases n with
    | zero => exact fun i => Fin.elim0 i
    | succ n =>
      apply Fin.antitone_iff_succ_le.mpr
      intro i
      cases n with
      | zero => exact Fin.elim0 i
      | succ k =>
        have hi := edgeAB_midpoint_inequality hh i
        simp only [boundary, Vertex.edge_zero, sub_le_sub_iff]
        rw [add_comm]
        convert hi using 1 <;> congr 3
  -- Normalize the nonzero Fin literals from fin_cases so the edge evaluation lemmas match.
  fin_cases s
  · exact base hh
  · change Antitone (boundary h 1)
    intro i j hij
    simpa only [boundary, Vertex.edge_one, Vertex.edge_zero] using base hh.rotate hij
  · change Antitone (boundary h 2)
    intro i j hij
    simpa only [boundary, Vertex.edge_two, Vertex.edge_zero] using base hh.rotate.rotate hij

/-- Each side of a normalized hive has antitone boundary differences. -/
theorem boundary_antitone (h : Hive n R) (s : Fin 3) :
    Antitone (boundary (h : Vertex n → R) s) := h.isHive.boundary_antitone s

/-- The boundary is unchanged when an unnormalized hive is normalized. -/
@[simp] theorem boundary_normalize (h : Vertex n → R) (hh : IsHive h) :
    boundary (normalize h hh : Vertex n → R) = boundary h := by
  funext s i
  simp [boundary]

end OrderedGroup

/-- The three cyclic dominant weights of an integer hive. -/
def boundaryWeight (h : IntegerHive n) (s : Fin 3) : DominantWeight n :=
  ⟨boundary (h : Vertex n → ℤ) s, h.boundary_antitone s⟩

@[simp] theorem boundaryWeight_apply (h : IntegerHive n) (s : Fin 3) (i : Fin n) :
    (h.boundaryWeight s).val i = boundary (h : Vertex n → ℤ) s i := (rfl)

end TauCeti.Hive
