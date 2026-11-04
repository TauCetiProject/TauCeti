/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Reduction

/-!
# The reduced path group of a Serre graph

At a vertex of a Serre graph, reduced closed paths form a group. Multiplication concatenates
paths and removes adjacent inverse darts; inversion reverses a path. The normal form identifies
this group with backtrack-homotopy classes of closed paths. This is the path model to be compared
with a spanning-tree presentation of the fundamental group of a graph.

## References

* J.-P. Serre, *Trees*, Chapter I, §§2.2–3.1.
* A. Hatcher, *Algebraic Topology*, §1.A, Proposition 1A.2.
-/

public section

namespace TauCeti.SerreGraph

universe u w

variable (Γ : SerreGraph.{u, w}) (v : Γ.V)

/-- Reduced closed paths at `v`, with concatenation followed by free reduction. -/
structure PathGroup where
  /-- The underlying closed path. -/
  toPath : Γ.Path v v
  /-- The path has no adjacent inverse darts. -/
  isReduced : Path.IsReduced Γ toPath

namespace PathGroup

variable {Γ : SerreGraph.{u, w}} {v : Γ.V}

noncomputable section

@[ext] theorem ext {p q : PathGroup Γ v} (h : p.toPath = q.toPath) : p = q :=
  by cases p; cases q; cases h; rfl

/-- The underlying reduced path determines a path group element. -/
theorem toPath_injective : Function.Injective (toPath : PathGroup Γ v → Γ.Path v v) :=
  fun _ _ => ext

/-- The class of a closed path, represented by its reduced form. -/
def ofPath (p : Γ.Path v v) : PathGroup Γ v :=
  ⟨Path.reduce Γ p, Path.isReduced_reduce Γ p⟩

-- The exported theorem cannot unfold the hidden body of `ofPath`; prove this privately first.
private theorem toPath_ofPath_raw (p : Γ.Path v v) :
    (ofPath p).toPath = Path.reduce Γ p := rfl

@[simp] theorem toPath_ofPath (p : Γ.Path v v) :
    (ofPath p).toPath = Path.reduce Γ p := toPath_ofPath_raw p

@[simp] theorem ofPath_toPath (p : PathGroup Γ v) : ofPath p.toPath = p := by
  apply ext
  exact Path.reduce_eq_self_of_isReduced Γ p.toPath p.isReduced

/-- Every reduced-path group element is represented by a closed path. -/
theorem ofPath_surjective : Function.Surjective (ofPath : Γ.Path v v → PathGroup Γ v) :=
  fun p => ⟨p.toPath, ofPath_toPath p⟩

/-- Prove a property of path group elements by checking classes of closed paths. -/
@[elab_as_elim] theorem induction_on {P : PathGroup Γ v → Prop} (g : PathGroup Γ v)
    (h : ∀ p : Γ.Path v v, P (ofPath p)) : P g := by
  obtain ⟨p, rfl⟩ := ofPath_surjective g
  exact h p

/-- Two closed paths represent the same group element exactly when they are backtrack
homotopic. -/
theorem ofPath_eq_iff_homotopic (p q : Γ.Path v v) :
    ofPath p = ofPath q ↔ Path.Homotopic Γ p q := by
  rw [Path.homotopic_iff_reduce_eq]
  exact ⟨fun h => congrArg toPath h, fun h => ext h⟩

/-- Multiplication in the reduced path group. -/
private def mul (p q : PathGroup Γ v) : PathGroup Γ v := ofPath (p.toPath.comp q.toPath)

/-- The empty path. -/
private def one : PathGroup Γ v := ofPath Quiver.Path.nil

/-- Reverse a reduced closed path. -/
private def inv (p : PathGroup Γ v) : PathGroup Γ v := ofPath p.toPath.reverse

private theorem toPath_mul_raw (p q : PathGroup Γ v) :
    (mul p q).toPath = Path.reduce Γ (p.toPath.comp q.toPath) := rfl

private theorem toPath_one_raw : (one : PathGroup Γ v).toPath = Quiver.Path.nil := by
  simp [one]

private theorem toPath_inv_raw (p : PathGroup Γ v) :
    (inv p).toPath = p.toPath.reverse := by
  rw [inv, toPath_ofPath, Path.reduce_reverse]
  simp only [Path.reduce_eq_self_of_isReduced Γ p.toPath p.isReduced]

-- The exported instance cannot refer to private operation definitions. Its fields repeat their
-- bodies, while the private names make the laws available before the instance is constructed.
instance : Group (PathGroup Γ v) where
  mul p q := ofPath (p.toPath.comp q.toPath)
  one := ofPath Quiver.Path.nil
  inv p := ofPath p.toPath.reverse
  mul_assoc a b c := by
    -- The group laws are checked on the raw operations before the instance is available.
    change mul (mul a b) c = mul a (mul b c)
    apply ext
    simp only [toPath_mul_raw, Path.reduce_comp_reduce_left,
      Path.reduce_comp_reduce_right, Quiver.Path.comp_assoc]
  one_mul a := by
    change mul one a = a
    apply ext
    simp only [toPath_mul_raw, toPath_one_raw, Quiver.Path.nil_comp]
    exact Path.reduce_eq_self_of_isReduced Γ a.toPath a.isReduced
  mul_one a := by
    change mul a one = a
    apply ext
    simp only [toPath_mul_raw, toPath_one_raw, Quiver.Path.comp_nil]
    exact Path.reduce_eq_self_of_isReduced Γ a.toPath a.isReduced
  inv_mul_cancel a := by
    change mul (inv a) a = one
    apply ext
    simp only [toPath_mul_raw, toPath_inv_raw, toPath_one_raw, Path.reduce_reverse_comp]

@[simp] theorem toPath_mul (p q : PathGroup Γ v) :
    (p * q).toPath = Path.reduce Γ (p.toPath.comp q.toPath) :=
  toPath_mul_raw p q

@[simp] theorem toPath_one : (1 : PathGroup Γ v).toPath = Quiver.Path.nil :=
  toPath_one_raw

@[simp] theorem toPath_inv (p : PathGroup Γ v) :
    (p⁻¹).toPath = p.toPath.reverse :=
  toPath_inv_raw p

@[simp] theorem ofPath_nil : ofPath (Quiver.Path.nil : Γ.Path v v) = 1 := by
  apply ext
  simp

/-- Concatenation of closed paths becomes multiplication in the reduced path group. -/
@[simp] theorem ofPath_comp (p q : Γ.Path v v) :
    ofPath (p.comp q) = ofPath p * ofPath q := by
  -- Expand the group operation to its path construction.
  change ofPath (p.comp q) = mul (ofPath p) (ofPath q)
  apply ext
  simp only [toPath_ofPath, toPath_mul_raw, Path.reduce_comp_reduce_left,
    Path.reduce_comp_reduce_right]

/-- Reversing a closed path becomes inversion in the reduced path group. -/
@[simp] theorem ofPath_reverse (p : Γ.Path v v) :
    ofPath p.reverse = (ofPath p)⁻¹ := by
  -- Expand inversion to reversal of a representative.
  change ofPath p.reverse = inv (ofPath p)
  apply ext
  simp only [toPath_ofPath, toPath_inv_raw, Path.reduce_reverse]

end
end PathGroup

end TauCeti.SerreGraph
