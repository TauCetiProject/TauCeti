/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Reduction

/-!
# The reduced loop group of a Serre graph

Reduced closed paths at a vertex form a group: multiplication concatenates and reduces,
and inversion reverses the darts. Backtrack homotopy gives the equality criterion for
this group. For the rose, the two orientations of a petal give distinct elements.

## References

* J.-P. Serre, *Trees*, Chapter I, §§2.2–2.3.
-/

public section

namespace TauCeti.SerreGraph

variable (Γ : SerreGraph)

/-- Reduced closed paths at `v`; equality is literal equality of their normal forms. -/
structure ReducedLoop (v : Γ.V) where
  /-- The normal form of the loop. -/
  path : Γ.Path v v
  /-- The stored path has no immediate backtrack. -/
  isReduced : Path.IsReduced Γ path

namespace ReducedLoop

variable {Γ : SerreGraph} {v : Γ.V}

/-- Two reduced loops are equal when their underlying paths are equal. -/
@[ext] theorem ext {p q : ReducedLoop Γ v} (h : p.path = q.path) : p = q := by
  cases p
  cases q
  cases h
  rfl

/-- The reduced loop represented by a closed path, obtained by reducing it. -/
noncomputable def ofPath (p : Γ.Path v v) : ReducedLoop Γ v :=
  ⟨Path.reduce Γ p, Path.isReduced_reduce Γ p⟩

@[simp] theorem path_ofPath (p : Γ.Path v v) : (ofPath p).path = Path.reduce Γ p := by
  simp only [ofPath]

/-- A reduced loop is unchanged by normalisation. -/
@[simp] theorem ofPath_path (p : ReducedLoop Γ v) : ofPath p.path = p := by
  apply ext
  exact Path.reduce_eq_self_of_isReduced Γ p.path p.isReduced

noncomputable instance : One (ReducedLoop Γ v) := ⟨ofPath Quiver.Path.nil⟩

noncomputable instance : Mul (ReducedLoop Γ v) := ⟨fun p q => ofPath (p.path.comp q.path)⟩

instance : Inv (ReducedLoop Γ v) :=
  ⟨fun p => ⟨p.path.reverse, (Path.isReduced_reverse Γ _).2 p.isReduced⟩⟩

@[simp] theorem path_one : (1 : ReducedLoop Γ v).path = Quiver.Path.nil := by
  exact Path.reduce_nil Γ v

@[simp] theorem path_mul (p q : ReducedLoop Γ v) :
    (p * q).path = Path.reduce Γ (p.path.comp q.path) := path_ofPath _

@[simp] theorem path_inv (p : ReducedLoop Γ v) :
    (p⁻¹).path = p.path.reverse := rfl

noncomputable instance : Group (ReducedLoop Γ v) where
  toOne := inferInstance
  toMul := inferInstance
  toInv := inferInstance
  one_mul p := by
    apply ext
    rw [path_mul, path_one, Quiver.Path.nil_comp]
    exact Path.reduce_eq_self_of_isReduced Γ p.path p.isReduced
  mul_one p := by
    apply ext
    rw [path_mul, path_one, Quiver.Path.comp_nil]
    exact Path.reduce_eq_self_of_isReduced Γ p.path p.isReduced
  mul_assoc p q r := by
    apply ext
    rw [path_mul, path_mul, path_mul, path_mul]
    rw [Path.reduce_comp_reduce_left, Path.reduce_comp_reduce_right,
      Quiver.Path.comp_assoc]
  inv_mul_cancel p := by
    apply ext
    rw [path_mul, path_inv, path_one]
    have h := Path.homotopic_comp_reverse Γ p.path.reverse
    simpa only [Quiver.Path.reverse_reverse, Path.reduce_nil] using h.reduce_eq Γ

@[simp] theorem ofPath_nil :
    ofPath (Quiver.Path.nil : Γ.Path v v) = 1 := by
  apply ext
  rw [path_ofPath, Path.reduce_nil, path_one]

/-- The group product agrees with concatenation of arbitrary closed paths. -/
@[simp] theorem ofPath_comp (p q : Γ.Path v v) :
    ofPath (p.comp q) = ofPath p * ofPath q := by
  apply ext
  rw [path_ofPath, path_mul, path_ofPath, path_ofPath]
  rw [Path.reduce_comp_reduce_left, Path.reduce_comp_reduce_right]

/-- Two closed paths represent the same loop precisely when they are backtrack homotopic. -/
theorem ofPath_eq_ofPath_iff (p q : Γ.Path v v) :
    ofPath p = ofPath q ↔ Path.Homotopic Γ p q := by
  constructor
  · intro h
    apply (Path.homotopic_iff_reduce_eq Γ).2
    exact congrArg ReducedLoop.path h
  · intro h
    apply ext
    exact (Path.homotopic_iff_reduce_eq Γ).1 h

/-- A closed path represents the identity exactly when it is backtrack homotopic
to the empty path. -/
theorem ofPath_eq_one_iff (p : Γ.Path v v) :
    ofPath p = 1 ↔ Path.Homotopic Γ p Quiver.Path.nil := by
  rw [← ofPath_nil]
  exact ofPath_eq_ofPath_iff p Quiver.Path.nil

/-- Reversing a closed path gives the inverse reduced loop. -/
@[simp] theorem ofPath_reverse (p : Γ.Path v v) : ofPath p.reverse = (ofPath p)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← ofPath_comp]
  exact (ofPath_eq_one_iff _).2 (Path.homotopic_comp_reverse Γ p)

end ReducedLoop

/-- The two orientations of a rose petal give distinct elements of its reduced loop group. -/
theorem rose_petal_ne_reverse {α : Type*} (a : α) :
    (ReducedLoop.ofPath ((rose α).dart (a, true)).toPath :
      ReducedLoop (rose α) PUnit.unit) ≠
    ReducedLoop.ofPath ((rose α).dart (a, false)).toPath := by
  intro h
  exact Path.rose_not_homotopic_reverse a
    ((ReducedLoop.ofPath_eq_ofPath_iff _ _).mp h)

end TauCeti.SerreGraph
