/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import TauCeti.Combinatorics.Graph.Serre.Tree

/-!
# The reduced path group of a Serre graph

At a vertex of a Serre graph, reduced closed paths form a group. Multiplication concatenates
paths and removes adjacent inverse darts; inversion reverses a path. The normal form identifies
this group with backtrack-homotopy classes of closed paths. This is the path model to be compared
with a spanning-tree presentation of the fundamental group of a graph. The reduced path groups of
an acyclic graph are trivial. A petal loop of a rose and its reverse are distinct elements.

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

/-- A petal loop of a rose and its reverse are distinct elements of the reduced path group. -/
theorem ofPath_reverse_rosePetal_ne {α : Type*} (a : α) :
    ofPath (rosePetal a).reverse ≠ ofPath (rosePetal a) := fun h => by
  -- The vertex type of `rose α` unfolds only at default transparency, so the homotopy is restated
  -- between paths at the ends of the dart before rewriting.
  have h' : Path.Homotopic (rose α) ((rose α).dart (a, true)).toPath
      ((rose α).dart (a, true)).toPath.reverse :=
    rosePetal_eq_toPath a ▸ ((ofPath_eq_iff_homotopic _ _).mp h).symm
  have hrev : Quiver.reverse ((rose α).dart (a, true)) = (rose α).dart (a, false) :=
    Subtype.ext ((reverse_val _ _).trans ((congrArg _ (dart_val _ _)).trans (dart_val _ _).symm))
  rw [Quiver.Path.reverse_toPath, hrev] at h'
  exact Path.rose_not_homotopic_reverse a h'

/-- Reversal-compatible dart weights extend to a homomorphism on reduced closed paths. -/
def lift {G : Type*} [Group G] (wt : Γ.E → G)
    (hwt : ∀ e, wt (Γ.rev e) = (wt e)⁻¹) : PathGroup Γ v →* G where
  toFun p := p.toPath.weight (fun {a b : Γ.V} (e : a ⟶ b) => wt e.val)
  map_one' := by simp
  map_mul' p q := by
    rw [toPath_mul, ← (Path.homotopic_reduce Γ _).weight_eq Γ wt hwt]
    exact Quiver.Path.weight_comp _ _ _

theorem lift_apply {G : Type*} [Group G] (wt : Γ.E → G)
    (hwt : ∀ e, wt (Γ.rev e) = (wt e)⁻¹) (p : PathGroup Γ v) :
    lift wt hwt p = p.toPath.weight (fun {a b : Γ.V} (e : a ⟶ b) => wt e.val) := (rfl)

/-- The weight of a closed path can be computed before reducing it. -/
@[simp] theorem lift_ofPath {G : Type*} [Group G] (wt : Γ.E → G)
    (hwt : ∀ e, wt (Γ.rev e) = (wt e)⁻¹) (p : Γ.Path v v) :
    lift wt hwt (ofPath p) = p.weight (fun {a b : Γ.V} (e : a ⟶ b) => wt e.val) := by
  rw [lift_apply, toPath_ofPath]
  exact ((Path.homotopic_reduce Γ p).weight_eq Γ wt hwt).symm

/-- **Changing the connecting path conjugates a based loop.** For a closed path `p` at `a` and two
paths `γ` and `η` from `v` to `a`, the loop `η p η⁻¹` at `v` is the conjugate of the loop
`γ p γ⁻¹` by the class of `η γ⁻¹`. -/
theorem ofPath_comp_comp_reverse {a : Γ.V} (p : Γ.Path a a) (γ η : Γ.Path v a) :
    ofPath ((η.comp p).comp η.reverse) =
      ofPath (η.comp γ.reverse) * ofPath ((γ.comp p).comp γ.reverse) *
        (ofPath (η.comp γ.reverse))⁻¹ := by
  rw [← ofPath_reverse, ← ofPath_comp, ← ofPath_comp, ofPath_eq_iff_homotopic]
  -- Cancelling `γ⁻¹ γ` twice reduces `η γ⁻¹ · γ p γ⁻¹ · γ η⁻¹` to `η p η⁻¹`.
  have hc {c : Γ.V} (r : Γ.Path a c) : Path.Homotopic Γ (γ.reverse.comp (γ.comp r)) r := by
    simpa only [Quiver.Path.comp_assoc, Quiver.Path.nil_comp] using
      (Path.Homotopic.reverse_comp Γ γ).comp_right Γ r
  simp only [Quiver.Path.reverse_comp, Quiver.Path.reverse_reverse, Quiver.Path.comp_assoc]
  exact ((((((hc η.reverse).comp_left Γ p).comp_left Γ γ).comp_left Γ γ.reverse).comp_left Γ
    η).trans ((hc _).comp_left Γ η)).symm

/-- The normal closure of a family of closed paths `p i`, each based at `v` along a path to its
start, does not depend on the choice of these connecting paths. -/
theorem normalClosure_range_ofPath_comp_comp_reverse {ι : Sort*} {a : ι → Γ.V}
    (p : ∀ i, Γ.Path (a i) (a i)) (γ η : ∀ i, Γ.Path v (a i)) :
    Subgroup.normalClosure (Set.range fun i => ofPath (((γ i).comp (p i)).comp (γ i).reverse)) =
      Subgroup.normalClosure
        (Set.range fun i => ofPath (((η i).comp (p i)).comp (η i).reverse)) := by
  -- Each loop of one family is a conjugate of the corresponding loop of the other family.
  have key (γ η : ∀ i, Γ.Path v (a i)) :
      Subgroup.normalClosure (Set.range fun i => ofPath (((γ i).comp (p i)).comp (γ i).reverse)) ≤
        Subgroup.normalClosure
          (Set.range fun i => ofPath (((η i).comp (p i)).comp (η i).reverse)) := by
    refine Subgroup.normalClosure_le_normal (Set.range_subset_iff.2 fun i => ?_)
    rw [ofPath_comp_comp_reverse _ (η i) (γ i)]
    exact (Subgroup.normalClosure_normal).conj_mem _
      (Subgroup.subset_normalClosure (Set.mem_range_self i)) _
  exact le_antisymm (key γ η) (key η γ)

end
end PathGroup

variable {Γ} in
/-- The reduced path groups of an acyclic graph are trivial: the only reduced closed path is
the empty one. -/
theorem IsAcyclic.subsingleton_pathGroup (h : Γ.IsAcyclic) (v : Γ.V) :
    Subsingleton (PathGroup Γ v) :=
  ⟨fun p q => PathGroup.ext <| h.eq_of_isReduced p.isReduced q.isReduced⟩

end TauCeti.SerreGraph
