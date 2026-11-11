/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Aut
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Units.Equiv

/-!
# The line

The line is the Serre graph with the integers as vertices and one geometric edge between `n` and
`n + 1`. It is the Cayley graph of the infinite cyclic group, that is of the free group of rank
one, and it is a tree: a reduced path never turns back, so it moves monotonically and cannot
close up.

The coordinate `SerreGraph.lineVertexEquiv` identifies the vertices with the integers, and the
integers act on the line by translation, `SerreGraph.lineShift`, with `k • n = k + n`.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.2 and §6.4.
-/

public section

namespace TauCeti
namespace SerreGraph

/-- The line: the vertices are the integers, the dart `(n, true)` runs from `n` to `n + 1`, and
its reverse `(n, false)` runs back. -/
@[expose] def line : SerreGraph.{0, 0} where
  V := ℤ
  E := ℤ × Bool
  src e := if e.2 then e.1 else e.1 + 1
  rev e := (e.1, !e.2)
  rev_rev e := by simp
  rev_ne e := by simp [Prod.ext_iff]

theorem line_src (e : ℤ × Bool) : line.src e = if e.2 then e.1 else e.1 + 1 := (rfl)

@[simp] theorem line_rev (e : ℤ × Bool) : line.rev e = (e.1, !e.2) := (rfl)

theorem line_tgt (e : ℤ × Bool) : line.tgt e = if e.2 then e.1 + 1 else e.1 := by
  obtain ⟨n, d⟩ := e
  cases d <;> rfl

/-- The vertices of the line are the integers. -/
def lineVertexEquiv : line.V ≃ ℤ :=
  Equiv.refl ℤ

@[simp] theorem lineVertexEquiv_src (e : ℤ × Bool) :
    lineVertexEquiv (line.src e) = if e.2 then e.1 else e.1 + 1 := (rfl)

/-- A dart of the line moves one step up or down according to its orientation. -/
@[simp] theorem lineVertexEquiv_tgt (e : ℤ × Bool) :
    lineVertexEquiv (line.tgt e) = lineVertexEquiv (line.src e) + if e.2 then 1 else -1 := by
  obtain ⟨n, d⟩ := e
  rw [lineVertexEquiv_src]
  -- The target of `(n, d)` is the integer `n + 1` or `n`, by the definition of the line.
  cases d
  · exact (add_neg_cancel_right n 1).symm
  · rfl

/-- A dart continuing a dart of the line without turning back has the same orientation. -/
theorem line_snd_eq_of_ne_rev {e f : ℤ × Bool} (h : line.src e = line.tgt f)
    (hne : e ≠ line.rev f) : e.2 = f.2 := by
  obtain ⟨m, d⟩ := e
  obtain ⟨n, d'⟩ := f
  -- Compare the endpoints as integers.
  have h' : (if d then m else m + 1 : ℤ) = if d' then n + 1 else n :=
    (line_src (m, d)).symm.trans (h.trans (line_tgt (n, d')))
  have hne' : ¬(m = n ∧ d = !d') := fun ⟨h₁, h₂⟩ => hne (by rw [line_rev, h₁, h₂])
  cases d <;> cases d' <;> simp at h' hne' ⊢ <;> omega

/-- A reduced path in the line moves monotonically, in the direction of each of its darts. -/
theorem lineVertexEquiv_eq_add_of_isReduced {a b : line.V} (p : line.Path a b)
    (hp : Path.IsReduced line p) : ∀ x ∈ Path.darts line p,
      lineVertexEquiv b = lineVertexEquiv a + (if Prod.snd x then 1 else -1) * p.length := by
  induction p with
  | nil => simp
  | @cons b c p e ih =>
    have hc := lineVertexEquiv_tgt e.1
    rw [e.2.1, e.2.2] at hc
    cases p with
    | nil =>
      intro x hx
      rw [Path.darts_cons, Path.darts_nil, List.nil_append, List.mem_singleton] at hx
      subst hx
      rw [Quiver.Path.length_cons, Quiver.Path.length_nil]
      simpa using hc
    | cons q f =>
      obtain ⟨hpf, hne⟩ := (Path.isReduced_cons_cons line q f e).mp hp
      have ih := ih hpf
      have hfe : Prod.snd e.1 = Prod.snd f.1 :=
        line_snd_eq_of_ne_rev (e.2.1.trans f.2.2.symm) hne
      have hf := ih f.1 (by rw [Path.darts_cons]; exact List.mem_append_right _ (by simp))
      intro x hx
      rw [Path.darts_cons, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · have hx' := ih x hx
        simp only [Quiver.Path.length_cons] at hf hx' ⊢
        grind
      · simp only [Quiver.Path.length_cons] at hf ⊢
        grind

/-- The line is acyclic. -/
theorem line_isAcyclic : line.IsAcyclic := by
  refine (isAcyclic_iff line).mpr fun a p hp => ?_
  cases p with
  | nil => rfl
  | cons q e =>
    have h := lineVertexEquiv_eq_add_of_isReduced _ hp e.1
      (by rw [Path.darts_cons]; exact List.mem_append_right _ (by simp))
    rw [Quiver.Path.length_cons] at h
    cases Prod.snd e.1 <;> simp at h <;> omega

/-- Every vertex of the line is joined to every vertex above it. -/
private theorem line_nonempty_path_add (k : ℕ) :
    ∀ a b : line.V, lineVertexEquiv b = lineVertexEquiv a + k → Nonempty (line.Path a b) := by
  induction k with
  | zero =>
    intro a b h
    obtain rfl : b = a := lineVertexEquiv.injective (by simpa using h)
    exact ⟨.nil⟩
  | succ k ih =>
    intro a b h
    -- The last dart is `(n, true)`, from `n = a + k` to `n + 1 = b`.
    let n : ℤ := lineVertexEquiv a + k
    obtain ⟨p⟩ := ih a (line.src (n, true)) (by simp [lineVertexEquiv_src, n])
    refine ⟨p.cons ⟨(n, true), rfl, lineVertexEquiv.injective ?_⟩⟩
    rw [lineVertexEquiv_tgt, lineVertexEquiv_src, h]
    simp [n]
    omega

theorem line_connected : line.Connected := by
  refine (connected_iff line).mpr ⟨⟨lineVertexEquiv.symm 0⟩,
    (preconnected_iff line).mpr fun a b => ?_⟩
  have key (a b : line.V) (hab : lineVertexEquiv a ≤ lineVertexEquiv b) :
      Nonempty (line.Path a b) :=
    line_nonempty_path_add (lineVertexEquiv b - lineVertexEquiv a).toNat a b (by omega)
  rcases le_total (lineVertexEquiv a) (lineVertexEquiv b) with hab | hab
  · exact key a b hab
  · obtain ⟨p⟩ := key b a hab
    exact ⟨p.reverse⟩

/-- The line is a tree. -/
theorem line_isTree : line.IsTree :=
  (isTree_iff line).mpr ⟨line_connected, line_isAcyclic⟩

/-- The translation action of the integers on the line, `k • n = k + n`. -/
def lineShift : Multiplicative ℤ →* line.Aut where
  toFun k :=
    { equivV := (Equiv.addLeft k.toAdd : ℤ ≃ ℤ)
      equivE := ((Equiv.addLeft k.toAdd).prodCongr (Equiv.refl Bool) : ℤ × Bool ≃ ℤ × Bool)
      -- The vertices and darts of `line` are only definitionally `ℤ` and `ℤ × Bool`, so the
      -- lemmas about `Equiv.addLeft` and `Equiv.prodCongr` cannot rewrite these goals. Each
      -- `show` below evaluates the two equivalences on their arguments, `k • n = k.toAdd + n`.
      map_src := fun ⟨n, d⟩ => show lineVertexEquiv (line.src (k.toAdd + n, d)) =
          k.toAdd + lineVertexEquiv (line.src (n, d)) by
        simp only [lineVertexEquiv_src]
        split_ifs <;> omega
      map_rev _ := rfl }
  -- Here the `show`s also evaluate the identity automorphism as `Equiv.refl` and a product of
  -- automorphisms as the composite of their equivalences.
  map_one' := Aut.ext
    (fun (v : ℤ) => show (1 : Multiplicative ℤ).toAdd + v = v by rw [toAdd_one, zero_add])
    (fun (e : ℤ × Bool) => Prod.ext
      (show (1 : Multiplicative ℤ).toAdd + e.1 = e.1 by rw [toAdd_one, zero_add]) rfl)
  map_mul' x y := Aut.ext
    (fun (v : ℤ) => show (x * y).toAdd + v = x.toAdd + (y.toAdd + v) by
      rw [toAdd_mul, add_assoc])
    (fun (e : ℤ × Bool) => Prod.ext
      (show (x * y).toAdd + e.1 = x.toAdd + (y.toAdd + e.1) by rw [toAdd_mul, add_assoc]) rfl)

/-- Translation adds to the coordinate of a vertex. -/
@[simp] theorem lineVertexEquiv_lineShift_smul (k : Multiplicative ℤ) (v : line.V) :
    lineVertexEquiv (lineShift k • v) = k.toAdd + lineVertexEquiv v := (rfl)

/-- Translation moves a dart without changing its orientation. -/
@[simp] theorem lineShift_smul_dart (k : Multiplicative ℤ) (e : line.E) :
    lineShift k • e = Prod.mk (k.toAdd + Prod.fst e) (Prod.snd e) := (rfl)

end SerreGraph
end TauCeti
