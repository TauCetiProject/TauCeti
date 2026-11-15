/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.Path
public import Mathlib.GroupTheory.Complement

/-!
# The normal form theorem for paths in a graph of groups

Let `𝔸` be a graph of groups over a Serre graph `Γ`. An alternating `𝔸`-path from `a` to `b` is a
sequence `g₀, e₁, g₁, …, e_k, g_k` in which `e₁ ⋯ e_k` is an edge path from `a` to `b` and each
`g_i` lies in the vertex group at the end of `e_i`. It is reduced when it contains no backtracking
`e, ω_e(c), rev e`; such a subsequence can be replaced by `α_e(c)` without changing the homotopy
class. Fix, for every dart `e : a ⟶ b`, a left transversal of `α_e(A_e)` in `A_a`. A normal word
is a reduced alternating path in which every vertex group element `g_i` with `i < k` lies in the
transversal of the dart `e_{i+1}` that follows it.

Appending a letter to a normal word and normalizing again defines, for each letter `l` from `x` to
`y`, a map from the normal words ending at `x` to those ending at `y`. These maps satisfy the
defining relations of homotopy of `𝔸`-paths, so appending the letters of a path one at a time
gives a homotopy invariant `normalForm`. Since every normal word is its own normal form, every
`𝔸`-path is homotopic to exactly one normal word. Consequently the elements of `π₁(𝔸, a)`
correspond to the normal words of closed paths at `a`. The vertex group `A_a` embeds in
`π₁(𝔸, a)`, and so does `A_b` for every vertex `b` joined to `a` by an `𝔸`-path.

The construction follows the normal forms of Mathlib for amalgamated products and HNN extensions,
`Monoid.PushoutI.NormalWord` and `HNNExtension.NormalWord`: choose transversals, let the
generators act on normal words, and check the defining relations. Here `𝔸`-paths are built by
appending letters on the right, so letters act on the right and the transversals are left
transversals.

## Main definitions

* `TauCeti.GraphOfGroups.Transversal`: a choice of left transversals of the edge group images.
* `TauCeti.GraphOfGroups.AlternatingPath`: alternating `𝔸`-paths `g₀, e₁, g₁, …, e_k, g_k`.
* `TauCeti.GraphOfGroups.AlternatingPath.IsReduced`: alternating paths without backtracking.
* `TauCeti.GraphOfGroups.NormalWord`: normal words for a transversal.
* `TauCeti.GraphOfGroups.NormalWord.appendPath`: appending an `𝔸`-path to a normal word.
* `TauCeti.GraphOfGroups.normalForm`: the normal form of an `𝔸`-path.

## Main results

* `TauCeti.GraphOfGroups.normalForm_eq_normalForm_iff`: two `𝔸`-paths are homotopic exactly
  when they have the same normal form.
* `TauCeti.GraphOfGroups.NormalWord.toPath_homotopic_toPath_iff`: distinct normal words are not
  homotopic.
* `TauCeti.GraphOfGroups.π₁.normalWordEquiv`: `π₁(𝔸, a)` is in bijection with the normal words of
  closed paths at `a`.
* `TauCeti.GraphOfGroups.Path.ofVertex_homotopic_nil_iff`: a nontrivial vertex group element is
  not homotopic to the empty path.
* `TauCeti.GraphOfGroups.π₁.vertexHom_injective`: the vertex group `A_b` embeds in `π₁(𝔸, a)`
  through `g ↦ p g p⁻¹`, for every `𝔸`-path `p` from `a` to `b`.

## References

* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Definitions 2.2–2.3 and Proposition 2.4.
* J.-P. Serre, *Trees*, Chapter I, §5.2, Theorem 11.
-/

public section

universe u v w x

namespace TauCeti

namespace GraphOfGroups

variable {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ)

/-- A transversal for the graph of groups `𝔸`: for every dart `e : a ⟶ b` of `Γ`, a left
transversal of the subgroup `α_e(A_e)` of `A_a`, that is, a set containing exactly one element of
each left coset `g α_e(A_e)`. -/
abbrev Transversal : Type (max u v w) :=
  ∀ ⦃a b : Γ.V⦄ (e : a ⟶ b), (𝔸.αArrow e).range.LeftTransversal

namespace Transversal

variable {𝔸} (d : 𝔸.Transversal) {a b : Γ.V} (e : a ⟶ b)

/-- The representative in the transversal `d e` of the left coset `g α_e(A_e)`. -/
noncomputable def rep (g : 𝔸.vertexGroup a) : 𝔸.vertexGroup a :=
  ((d e).2.equiv g).1

/-- The element `c` of the edge group with `g = rep g * α_e(c)`. -/
noncomputable def edgePart (g : 𝔸.vertexGroup a) : 𝔸.edgeGroup (Γ.toGeomEdge e.1) :=
  (MonoidHom.ofInjective (𝔸.αArrow_injective e)).symm
    ⟨((d e).2.equiv g).2.1, ((d e).2.equiv g).2.2⟩

@[simp] theorem rep_mem (g : 𝔸.vertexGroup a) : d.rep e g ∈ (d e).1 :=
  ((d e).2.equiv g).1.2

/-- Every `g ∈ A_a` is its representative times an element `α_e(c)` of `α_e(A_e)`. -/
@[simp] theorem rep_mul_αArrow_edgePart (g : 𝔸.vertexGroup a) :
    d.rep e g * 𝔸.αArrow e (d.edgePart e g) = g := by
  simpa [rep, edgePart] using (d e).2.equiv_fst_mul_equiv_snd g

/-- An element of the transversal is its own representative. -/
theorem rep_of_mem {g : 𝔸.vertexGroup a} (hg : g ∈ (d e).1) : d.rep e g = g :=
  congrArg Subtype.val ((d e).2.equiv_fst_eq_self_of_mem_of_one_mem (one_mem _) hg)

/-- An element of the transversal has trivial edge group part. -/
theorem edgePart_of_mem {g : 𝔸.vertexGroup a} (hg : g ∈ (d e).1) : d.edgePart e g = 1 := by
  simp only [edgePart, (d e).2.equiv_snd_eq_one_of_mem_of_one_mem (one_mem _) hg]
  exact map_one _

@[simp] theorem rep_rep (g : 𝔸.vertexGroup a) : d.rep e (d.rep e g) = d.rep e g :=
  d.rep_of_mem e (d.rep_mem e g)

@[simp] theorem edgePart_rep (g : 𝔸.vertexGroup a) : d.edgePart e (d.rep e g) = 1 :=
  d.edgePart_of_mem e (d.rep_mem e g)

@[simp] theorem rep_mul_αArrow (g : 𝔸.vertexGroup a) (c : 𝔸.edgeGroup (Γ.toGeomEdge e.1)) :
    d.rep e (g * 𝔸.αArrow e c) = d.rep e g := by
  rw [rep, (d e).2.equiv_mul_right_of_mem (MonoidHom.mem_range.2 ⟨c, rfl⟩), rep]

@[simp] theorem edgePart_mul_αArrow (g : 𝔸.vertexGroup a) (c : 𝔸.edgeGroup (Γ.toGeomEdge e.1)) :
    d.edgePart e (g * 𝔸.αArrow e c) = d.edgePart e g * c :=
  𝔸.αArrow_injective e <| mul_left_cancel (a := d.rep e (g * 𝔸.αArrow e c)) <| by
    rw [rep_mul_αArrow_edgePart, rep_mul_αArrow, map_mul, ← mul_assoc, rep_mul_αArrow_edgePart]

/-- The representative of `g` lies in `α_e(A_e)` exactly when `g` does. -/
theorem rep_mem_range_iff (g : 𝔸.vertexGroup a) :
    d.rep e g ∈ (𝔸.αArrow e).range ↔ g ∈ (𝔸.αArrow e).range := by
  rw [← (𝔸.αArrow e).range.mul_mem_cancel_right ⟨d.edgePart e g, rfl⟩, rep_mul_αArrow_edgePart]

end Transversal

/-! ### Alternating paths -/

/-- The alternating `𝔸`-paths `g₀, e₁, g₁, …, e_k, g_k` from `a` to `b`: `e₁ ⋯ e_k` is an edge
path from `a` to `b` in `Γ`, `g₀ ∈ A_a` and `g_i` lies in the vertex group of the target of
`e_i`. The path `single g` is `g₀ = g` of length zero, and `cons p e g` is `p` followed by the dart
`e` and the element `g`. -/
inductive AlternatingPath (a : Γ.V) : Γ.V → Type (max u v w)
  /-- The alternating path `g` of length zero. -/
  | single (g : 𝔸.vertexGroup a) : AlternatingPath a a
  /-- The alternating path `p` followed by the dart `e` and the vertex group element `g`. -/
  | cons {b c : Γ.V} (p : AlternatingPath a b) (e : b ⟶ c) (g : 𝔸.vertexGroup c) :
      AlternatingPath a c

namespace AlternatingPath

variable {𝔸} {a : Γ.V}

/-- The last vertex group element `g_k` of an alternating path. -/
def last : ∀ {b : Γ.V}, 𝔸.AlternatingPath a b → 𝔸.vertexGroup b
  | _, single g => g
  | _, cons _ _ g => g

/-- Replace the last vertex group element `g_k` of an alternating path. -/
def setLast : ∀ {b : Γ.V}, 𝔸.AlternatingPath a b → 𝔸.vertexGroup b → 𝔸.AlternatingPath a b
  | _, single _, h => single h
  | _, cons p e _, h => cons p e h

@[simp] theorem last_single (g : 𝔸.vertexGroup a) : (single g : 𝔸.AlternatingPath a a).last = g :=
  (rfl)

@[simp] theorem last_cons {b c : Γ.V} (p : 𝔸.AlternatingPath a b) (e : b ⟶ c)
    (g : 𝔸.vertexGroup c) : (cons p e g).last = g :=
  (rfl)

@[simp] theorem setLast_single (g h : 𝔸.vertexGroup a) :
    (single g : 𝔸.AlternatingPath a a).setLast h = single h :=
  (rfl)

@[simp] theorem setLast_cons {b c : Γ.V} (p : 𝔸.AlternatingPath a b) (e : b ⟶ c)
    (g h : 𝔸.vertexGroup c) : (cons p e g).setLast h = cons p e h :=
  (rfl)

@[simp] theorem last_setLast {b : Γ.V} (p : 𝔸.AlternatingPath a b) (g : 𝔸.vertexGroup b) :
    (p.setLast g).last = g := by
  cases p <;> rfl

@[simp] theorem setLast_last {b : Γ.V} (p : 𝔸.AlternatingPath a b) : p.setLast p.last = p := by
  cases p <;> rfl

@[simp] theorem setLast_setLast {b : Γ.V} (p : 𝔸.AlternatingPath a b) (g h : 𝔸.vertexGroup b) :
    (p.setLast g).setLast h = p.setLast h := by
  cases p <;> rfl

/-- The `𝔸`-path `g₀ e₁ g₁ ⋯ e_k g_k` spelled by an alternating path. -/
def toPath : ∀ {b : Γ.V}, 𝔸.AlternatingPath a b → 𝔸.Path ⟨a⟩ ⟨b⟩
  | _, single g => Path.ofVertex g
  | _, cons p e g => (p.toPath.cons (Letter.dart e)).cons (Letter.vertex g)

@[simp] theorem toPath_single (g : 𝔸.vertexGroup a) :
    (single g : 𝔸.AlternatingPath a a).toPath = Path.ofVertex g :=
  (rfl)

@[simp] theorem toPath_cons {b c : Γ.V} (p : 𝔸.AlternatingPath a b) (e : b ⟶ c)
    (g : 𝔸.vertexGroup c) :
    (cons p e g).toPath = (p.toPath.cons (Letter.dart e)).cons (Letter.vertex g) :=
  (rfl)

/-- Multiplying the last element of an alternating path by `g` amounts, up to homotopy, to
appending the vertex group letter `g`. -/
theorem toPath_setLast_mul_homotopic {b : Γ.V} (p : 𝔸.AlternatingPath a b)
    (g : 𝔸.vertexGroup b) :
    Path.Homotopic (p.setLast (p.last * g)).toPath (p.toPath.cons (Letter.vertex g)) := by
  cases p with
  | single h => simpa [Path.ofVertex_eq_nil_cons] using (Path.Homotopic.mul _ h g).symm
  | cons p e h => exact (Path.Homotopic.mul _ h g).symm

/-- `p.Cancels e` says that `p` ends with the dart `rev e` followed by an element of `α_e(A_e)`,
so that appending `e` creates the backtracking `rev e, α_e(c), e`. -/
def Cancels : ∀ {b c : Γ.V}, 𝔸.AlternatingPath a b → (b ⟶ c) → Prop
  | _, _, single _, _ => False
  | _, _, cons _ e' g, e => e'.1 = Γ.rev e.1 ∧ g ∈ (𝔸.αArrow e).range

@[simp] theorem not_cancels_single {c : Γ.V} (g : 𝔸.vertexGroup a) (e : a ⟶ c) :
    ¬ (single g : 𝔸.AlternatingPath a a).Cancels e :=
  id

@[simp] theorem cancels_cons_iff {b c d : Γ.V} (p : 𝔸.AlternatingPath a b) (e' : b ⟶ c)
    (g : 𝔸.vertexGroup c) (e : c ⟶ d) :
    (cons p e' g).Cancels e ↔ e'.1 = Γ.rev e.1 ∧ g ∈ (𝔸.αArrow e).range :=
  Iff.rfl

/-- In terms of the first dart: `p, e', g` followed by `e` backtracks when `e` reverses `e'` and
`g ∈ ω_{e'}(A_{e'})`. -/
theorem cancels_cons_iff_ωArrow {b c d : Γ.V} (p : 𝔸.AlternatingPath a b) (e' : b ⟶ c)
    (g : 𝔸.vertexGroup c) (e : c ⟶ d) :
    (cons p e' g).Cancels e ↔ e.1 = Γ.rev e'.1 ∧ g ∈ (𝔸.ωArrow e').range := by
  have hrev : Function.Involutive Γ.rev := Γ.rev_rev
  rw [cancels_cons_iff, ← (eq_comm.trans hrev.eq_iff : e'.1 = Γ.rev e.1 ↔ _)]
  exact and_congr_right fun h ↦ by rw [𝔸.range_ωArrow_eq_range_αArrow e' e h]

/-- `p` backtracks with `e` exactly when it ends with `rev e, α_e(c)`. -/
theorem cancels_iff {b c : Γ.V} {p : 𝔸.AlternatingPath a b} {e : b ⟶ c} :
    p.Cancels e ↔ ∃ (q : 𝔸.AlternatingPath a c) (c₀ : 𝔸.edgeGroup (Γ.toGeomEdge e.1)),
      p = cons q (Quiver.reverse e) (𝔸.αArrow e c₀) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · cases p with
    | single => exact h.elim
    | cons q e' g =>
      obtain ⟨h₁, c₀, rfl⟩ := h
      obtain rfl := Γ.src_eq_tgt_of_val_eq_rev h₁
      obtain rfl := Γ.eq_reverse_of_val_eq_rev h₁
      exact ⟨q, c₀, rfl⟩
  · rintro ⟨q, c₀, rfl⟩
    exact ⟨Γ.reverse_val e, c₀, rfl⟩

/-- Changing the last element of `p` within its left coset of `α_e(A_e)` does not change whether
`p` backtracks with `e`. -/
theorem cancels_setLast {b c : Γ.V} {p : 𝔸.AlternatingPath a b} {e : b ⟶ c} {g : 𝔸.vertexGroup b}
    (hg : g ∈ (𝔸.αArrow e).range ↔ p.last ∈ (𝔸.αArrow e).range) :
    (p.setLast g).Cancels e ↔ p.Cancels e := by
  cases p with
  | single => exact Iff.rfl
  | cons p e' h => exact and_congr_right fun _ ↦ hg

/-- An alternating path is reduced when it contains no backtracking `e, ω_e(c), rev e`. -/
def IsReduced : ∀ {b : Γ.V}, 𝔸.AlternatingPath a b → Prop
  | _, single _ => True
  | _, cons p e _ => p.IsReduced ∧ ¬ p.Cancels e

@[simp] theorem isReduced_single (g : 𝔸.vertexGroup a) :
    (single g : 𝔸.AlternatingPath a a).IsReduced :=
  True.intro

@[simp] theorem isReduced_cons_iff {b c : Γ.V} (p : 𝔸.AlternatingPath a b) (e : b ⟶ c)
    (g : 𝔸.vertexGroup c) : (cons p e g).IsReduced ↔ p.IsReduced ∧ ¬ p.Cancels e :=
  Iff.rfl

@[simp] theorem isReduced_setLast {b : Γ.V} (p : 𝔸.AlternatingPath a b) (g : 𝔸.vertexGroup b) :
    (p.setLast g).IsReduced ↔ p.IsReduced := by
  cases p <;> rfl

variable (d : 𝔸.Transversal)

/-- An alternating path is normalized for the transversal `d` when every vertex group element
except the last lies in the transversal of the dart that follows it. -/
def IsNormalized : ∀ {b : Γ.V}, 𝔸.AlternatingPath a b → Prop
  | _, single _ => True
  | _, cons p e _ => p.IsNormalized ∧ p.last ∈ (d e).1

@[simp] theorem isNormalized_single (g : 𝔸.vertexGroup a) :
    (single g : 𝔸.AlternatingPath a a).IsNormalized d :=
  True.intro

@[simp] theorem isNormalized_cons_iff {b c : Γ.V} (p : 𝔸.AlternatingPath a b) (e : b ⟶ c)
    (g : 𝔸.vertexGroup c) : (cons p e g).IsNormalized d ↔ p.IsNormalized d ∧ p.last ∈ (d e).1 :=
  Iff.rfl

@[simp] theorem isNormalized_setLast {b : Γ.V} (p : 𝔸.AlternatingPath a b) (g : 𝔸.vertexGroup b) :
    (p.setLast g).IsNormalized d ↔ p.IsNormalized d := by
  cases p <;> rfl

/-- Deleting the backtracking `rev e, α_e(c), e` created by appending the dart `e` to `p`: the
last dart and element of `p` are removed and `ω_e(c)` is multiplied onto the new last element. -/
noncomputable def cancelDart :
    ∀ {b c : Γ.V} (p : 𝔸.AlternatingPath a b) (e : b ⟶ c), p.Cancels e → 𝔸.AlternatingPath a c
  | _, _, single _, _, h => h.elim
  | _, c, cons q _ g, e, h =>
    let q' : 𝔸.AlternatingPath a c := Γ.src_eq_tgt_of_val_eq_rev h.1 ▸ q
    q'.setLast
      (q'.last * 𝔸.ωArrow e ((MonoidHom.ofInjective (𝔸.αArrow_injective e)).symm ⟨g, h.2⟩))

/-- Deleting the backtracking `rev e, α_e(c), e` from `q, rev e, α_e(c)` gives `q` with
`ω_e(c)` multiplied onto its last element. -/
theorem cancelDart_cons_reverse {b c : Γ.V} (q : 𝔸.AlternatingPath a c) (e : b ⟶ c)
    (c₀ : 𝔸.edgeGroup (Γ.toGeomEdge e.1))
    (h : (cons q (Quiver.reverse e) (𝔸.αArrow e c₀)).Cancels e) :
    (cons q (Quiver.reverse e) (𝔸.αArrow e c₀)).cancelDart e h =
      q.setLast (q.last * 𝔸.ωArrow e c₀) := by
  simp only [cancelDart]
  congr 3
  exact 𝔸.αArrow_injective e (by simp)

open scoped Classical in
/-- Appending the dart `e` to `p` and normalizing at the new end for the transversal `d`. If `p`
ends with `rev e, α_e(c)`, the backtracking `rev e, α_e(c), e` is deleted: the last dart and
element of `p` are removed and `ω_e(c)` is multiplied onto the new last element. Otherwise the last
element `g` of `p` is written `g = s α_e(c)` with `s` in the transversal `d e`, `p` becomes
`…, s, e, ω_e(c)`, and no other entry of `p` changes. When `p` is reduced and normalized, so is
the result. -/
noncomputable def appendDart {b c : Γ.V} (p : 𝔸.AlternatingPath a b) (e : b ⟶ c) :
    𝔸.AlternatingPath a c :=
  if h : p.Cancels e then p.cancelDart e h
  else cons (p.setLast (d.rep e p.last)) e (𝔸.ωArrow e (d.edgePart e p.last))

theorem appendDart_of_cancels {b c : Γ.V} {p : 𝔸.AlternatingPath a b} {e : b ⟶ c}
    (h : p.Cancels e) : p.appendDart d e = p.cancelDart e h :=
  dite_eq_left h

theorem appendDart_of_not_cancels {b c : Γ.V} {p : 𝔸.AlternatingPath a b} {e : b ⟶ c}
    (h : ¬ p.Cancels e) :
    p.appendDart d e = cons (p.setLast (d.rep e p.last)) e (𝔸.ωArrow e (d.edgePart e p.last)) :=
  dite_eq_right h

/-- Appending a dart to an alternating path of length zero never creates a backtracking. -/
@[simp] theorem appendDart_single {c : Γ.V} (g : 𝔸.vertexGroup a) (e : a ⟶ c) :
    (single g).appendDart d e = cons (single (d.rep e g)) e (𝔸.ωArrow e (d.edgePart e g)) :=
  appendDart_of_not_cancels d (not_cancels_single g e)

/-- Appending `e` after `rev e, α_e(c)` deletes the backtracking. -/
theorem appendDart_cons_of_eq {b c : Γ.V} (q : 𝔸.AlternatingPath a c) {e' : c ⟶ b} {e : b ⟶ c}
    (he : e' = Quiver.reverse e) {g : 𝔸.vertexGroup b} {c₀ : 𝔸.edgeGroup (Γ.toGeomEdge e.1)}
    (hg : g = 𝔸.αArrow e c₀) :
    (cons q e' g).appendDart d e = q.setLast (q.last * 𝔸.ωArrow e c₀) := by
  subst he hg
  rw [appendDart_of_cancels d
    ((cancels_cons_iff ..).2 ⟨Γ.reverse_val e, c₀, rfl⟩),
    cancelDart_cons_reverse]

/-- Appending a dart to a reduced path and normalizing gives a reduced path. -/
theorem IsReduced.appendDart {b c : Γ.V} {p : 𝔸.AlternatingPath a b} (hp : p.IsReduced)
    (e : b ⟶ c) : (p.appendDart d e).IsReduced := by
  by_cases h : p.Cancels e
  · obtain ⟨q, c₀, rfl⟩ := cancels_iff.1 h
    rw [appendDart_cons_of_eq d q rfl rfl, isReduced_setLast]
    exact hp.1
  · rw [appendDart_of_not_cancels d h, isReduced_cons_iff, isReduced_setLast,
      cancels_setLast (d.rep_mem_range_iff e _)]
    exact ⟨hp, h⟩

/-- Appending a dart to a normalized path and normalizing gives a normalized path. -/
theorem IsNormalized.appendDart {b c : Γ.V} {p : 𝔸.AlternatingPath a b} (hp : p.IsNormalized d)
    (e : b ⟶ c) : (p.appendDart d e).IsNormalized d := by
  by_cases h : p.Cancels e
  · obtain ⟨q, c₀, rfl⟩ := cancels_iff.1 h
    rw [appendDart_cons_of_eq d q rfl rfl, isNormalized_setLast]
    exact hp.1
  · rw [appendDart_of_not_cancels d h, isNormalized_cons_iff, isNormalized_setLast, last_setLast]
    exact ⟨hp, d.rep_mem e _⟩

/-- Appending a dart and then its reverse to a reduced normalized path gives the path back. -/
theorem appendDart_appendDart_reverse {b c : Γ.V} {p : 𝔸.AlternatingPath a b} (hr : p.IsReduced)
    (hn : p.IsNormalized d) (e : b ⟶ c) :
    (p.appendDart d e).appendDart d (Quiver.reverse e) = p := by
  by_cases h : p.Cancels e
  · obtain ⟨q, c₀, rfl⟩ := cancels_iff.1 h
    obtain ⟨c', hα, hω⟩ := 𝔸.exists_αArrow_reverse_eq_and_ωArrow_reverse_eq e c₀
    have hq : ¬ (q.setLast (q.last * 𝔸.ωArrow e c₀)).Cancels (Quiver.reverse e) := by
      refine (cancels_setLast ?_).not.2 hr.2
      rw [← hα]
      exact (𝔸.αArrow (Quiver.reverse e)).range.mul_mem_cancel_right ⟨_, rfl⟩
    rw [appendDart_cons_of_eq d q rfl rfl, appendDart_of_not_cancels d hq]
    simp [← hα, d.rep_of_mem _ hn.2, d.edgePart_of_mem _ hn.2, hω]
  · obtain ⟨c', hα, hω⟩ := 𝔸.exists_αArrow_reverse_eq_and_ωArrow_reverse_eq e (d.edgePart e p.last)
    simp [appendDart_of_not_cancels d h,
      appendDart_cons_of_eq d _ (Quiver.reverse_reverse e).symm hα.symm, hω]

/-- Moving an edge group element across an appended dart: appending `e` and then `ω_e(c)` is
appending `α_e(c)` and then `e`. -/
theorem setLast_appendDart_ωArrow {b c : Γ.V} (p : 𝔸.AlternatingPath a b) (e : b ⟶ c)
    (c₀ : 𝔸.edgeGroup (Γ.toGeomEdge e.1)) :
    (p.appendDart d e).setLast ((p.appendDart d e).last * 𝔸.ωArrow e c₀) =
      (p.setLast (p.last * 𝔸.αArrow e c₀)).appendDart d e := by
  by_cases h : p.Cancels e
  · obtain ⟨q, c₁, rfl⟩ := cancels_iff.1 h
    rw [appendDart_cons_of_eq d q rfl rfl, last_cons, setLast_cons,
      appendDart_cons_of_eq d q rfl (map_mul _ _ _).symm]
    simp [mul_assoc]
  · have h' : ¬ (p.setLast (p.last * 𝔸.αArrow e c₀)).Cancels e := by
      rwa [cancels_setLast ((𝔸.αArrow e).range.mul_mem_cancel_right ⟨_, rfl⟩)]
    rw [appendDart_of_not_cancels d h, appendDart_of_not_cancels d h']
    simp

/-- Appending a dart and normalizing does not change the homotopy class. -/
theorem toPath_appendDart_homotopic {b c : Γ.V} (p : 𝔸.AlternatingPath a b) (e : b ⟶ c) :
    Path.Homotopic (p.appendDart d e).toPath (p.toPath.cons (Letter.dart e)) := by
  by_cases h : p.Cancels e
  · obtain ⟨q, c₀, rfl⟩ := cancels_iff.1 h
    obtain ⟨c', hα, hω⟩ := 𝔸.exists_αArrow_reverse_eq_and_ωArrow_reverse_eq e c₀
    have h₁ := Path.Homotopic.dart_reverse
      (q.toPath.cons (Letter.vertex (𝔸.αArrow (Quiver.reverse e) c'))) (Quiver.reverse e)
    rw [Quiver.reverse_reverse] at h₁
    rw [appendDart_cons_of_eq d q rfl rfl, toPath_cons, ← hω, ← hα]
    exact (q.toPath_setLast_mul_homotopic _).trans <| h₁.symm.trans <|
      ((Path.Homotopic.dart_ωArrow _ (Quiver.reverse e) c').cons _).symm
  · rw [appendDart_of_not_cancels d h, toPath_cons]
    refine (Path.Homotopic.dart_ωArrow _ e _).trans (Path.Homotopic.cons ?_ _)
    simpa using ((p.setLast (d.rep e p.last)).toPath_setLast_mul_homotopic
      (𝔸.αArrow e (d.edgePart e p.last))).symm

end AlternatingPath

variable {𝔸} in
/-- A normal word for the transversal `d`: a reduced alternating path from `a` to `b` in which
every vertex group element except the last lies in the transversal of the dart that follows it.
Each `𝔸`-path from `a` to `b` is homotopic to exactly one normal word
(`TauCeti.GraphOfGroups.normalForm_eq_normalForm_iff`). -/
@[ext] structure NormalWord (d : 𝔸.Transversal) (a b : Γ.V) where
  /-- The underlying alternating path. -/
  toAlternatingPath : 𝔸.AlternatingPath a b
  /-- A normal word contains no backtracking. -/
  isReduced : toAlternatingPath.IsReduced
  /-- The vertex group elements before the darts lie in the transversal. -/
  isNormalized : toAlternatingPath.IsNormalized d

namespace NormalWord

variable {𝔸} {d : 𝔸.Transversal} {a : Γ.V}

variable (d) in
/-- The normal word `g` of length zero, for an element `g` of the vertex group `A_a`. -/
def single (g : 𝔸.vertexGroup a) : NormalWord d a a :=
  ⟨.single g, True.intro, True.intro⟩

variable (d a) in
/-- The normal word `1` of length zero. -/
def empty : NormalWord d a a :=
  single d 1

/-- The `𝔸`-path spelled by a normal word. -/
def toPath {b : Γ.V} (w : NormalWord d a b) : 𝔸.Path ⟨a⟩ ⟨b⟩ :=
  w.toAlternatingPath.toPath

theorem toPath_def {b : Γ.V} (w : NormalWord d a b) : w.toPath = w.toAlternatingPath.toPath :=
  (rfl)

/-- Multiplying the last vertex group element of a normal word on the right. -/
def mulLast {b : Γ.V} (w : NormalWord d a b) (g : 𝔸.vertexGroup b) : NormalWord d a b :=
  ⟨w.1.setLast (w.1.last * g), by simpa using w.2, by simpa using w.3⟩

/-- Appending a dart to a normal word and normalizing. -/
noncomputable def appendDart {b c : Γ.V} (w : NormalWord d a b) (e : b ⟶ c) : NormalWord d a c :=
  ⟨w.1.appendDart d e, w.2.appendDart d e, w.3.appendDart d e⟩

@[simp] theorem toAlternatingPath_single (g : 𝔸.vertexGroup a) :
    (single d g).toAlternatingPath = .single g :=
  (rfl)

@[simp] theorem toAlternatingPath_empty : (empty d a).toAlternatingPath = .single 1 :=
  (rfl)

@[simp] theorem single_one : single d (1 : 𝔸.vertexGroup a) = empty d a :=
  (rfl)

@[simp] theorem toPath_single (g : 𝔸.vertexGroup a) : (single d g).toPath = Path.ofVertex g :=
  (rfl)

@[simp] theorem toPath_empty : (empty d a).toPath = Path.ofVertex 1 :=
  (rfl)

@[simp] theorem single_inj {g h : 𝔸.vertexGroup a} : single d g = single d h ↔ g = h := by
  simp [NormalWord.ext_iff]

@[simp] theorem single_eq_empty_iff {g : 𝔸.vertexGroup a} : single d g = empty d a ↔ g = 1 := by
  rw [← single_one, single_inj]

@[simp] theorem empty_eq_single_iff {g : 𝔸.vertexGroup a} : empty d a = single d g ↔ g = 1 := by
  rw [eq_comm, single_eq_empty_iff]

@[simp] theorem toAlternatingPath_mulLast {b : Γ.V} (w : NormalWord d a b) (g : 𝔸.vertexGroup b) :
    (w.mulLast g).toAlternatingPath = w.1.setLast (w.1.last * g) :=
  (rfl)

@[simp] theorem toAlternatingPath_appendDart {b c : Γ.V} (w : NormalWord d a b) (e : b ⟶ c) :
    (w.appendDart e).toAlternatingPath = w.1.appendDart d e :=
  (rfl)

@[simp] theorem mulLast_mulLast {b : Γ.V} (w : NormalWord d a b) (g h : 𝔸.vertexGroup b) :
    (w.mulLast g).mulLast h = w.mulLast (g * h) := by
  ext1
  simp [mul_assoc]

@[simp] theorem mulLast_one {b : Γ.V} (w : NormalWord d a b) : w.mulLast 1 = w := by
  ext1
  simp

@[simp] theorem mulLast_single (g h : 𝔸.vertexGroup a) :
    (single d g).mulLast h = single d (g * h) :=
  (rfl)

@[simp] theorem mulLast_empty (g : 𝔸.vertexGroup a) : (empty d a).mulLast g = single d g := by
  rw [← single_one, mulLast_single, one_mul]

/-- Appending a dart and then its reverse to a normal word gives the word back. -/
@[simp] theorem appendDart_appendDart_reverse {b c : Γ.V} (w : NormalWord d a b) (e : b ⟶ c) :
    (w.appendDart e).appendDart (Quiver.reverse e) = w := by
  ext1
  exact AlternatingPath.appendDart_appendDart_reverse d w.2 w.3 e

/-- Appending the reverse of a dart and then the dart to a normal word gives the word back. -/
@[simp] theorem appendDart_reverse_appendDart {b c : Γ.V} (w : NormalWord d a c) (e : b ⟶ c) :
    (w.appendDart (Quiver.reverse e)).appendDart e = w := by
  have h := w.appendDart_appendDart_reverse (Quiver.reverse e)
  rwa [Quiver.reverse_reverse] at h

/-- Appending `e` and then `ω_e(c)` to a normal word is appending `α_e(c)` and then `e`. -/
theorem mulLast_appendDart_ωArrow {b c : Γ.V} (w : NormalWord d a b) (e : b ⟶ c)
    (c₀ : 𝔸.edgeGroup (Γ.toGeomEdge e.1)) :
    (w.appendDart e).mulLast (𝔸.ωArrow e c₀) = (w.mulLast (𝔸.αArrow e c₀)).appendDart e := by
  ext1
  exact AlternatingPath.setLast_appendDart_ωArrow d w.1 e c₀

/-- Appending a letter to a normal word and normalizing. -/
noncomputable def appendLetter :
    ∀ {x y : 𝔸.LetterVertex}, NormalWord d a x.as → 𝔸.Letter x y → NormalWord d a y.as
  | _, _, w, .vertex g => w.mulLast g
  | _, _, w, .dart e => w.appendDart e

/-- Appending an `𝔸`-path to a normal word letter by letter, normalizing after each letter. -/
noncomputable def appendPath {x : 𝔸.LetterVertex} (w : NormalWord d a x.as) :
    ∀ {y : 𝔸.LetterVertex}, 𝔸.Path x y → NormalWord d a y.as
  | _, .nil => w
  | _, .cons p l => (w.appendPath p).appendLetter l

@[simp] theorem appendLetter_vertex {b : Γ.V} (w : NormalWord d a b) (g : 𝔸.vertexGroup b) :
    w.appendLetter (Letter.vertex g) = w.mulLast g :=
  (rfl)

@[simp] theorem appendLetter_dart {b c : Γ.V} (w : NormalWord d a b) (e : b ⟶ c) :
    w.appendLetter (Letter.dart (𝔸 := 𝔸) e) = w.appendDart e :=
  (rfl)

@[simp] theorem appendPath_nil {x : 𝔸.LetterVertex} (w : NormalWord d a x.as) :
    w.appendPath (Quiver.Path.nil : 𝔸.Path x x) = w :=
  (rfl)

@[simp] theorem appendPath_cons {x y z : 𝔸.LetterVertex} (w : NormalWord d a x.as)
    (p : 𝔸.Path x y) (l : 𝔸.Letter y z) :
    w.appendPath (p.cons l) = (w.appendPath p).appendLetter l :=
  (rfl)

@[simp] theorem appendPath_comp {x y z : 𝔸.LetterVertex} (w : NormalWord d a x.as)
    (p : 𝔸.Path x y) (q : 𝔸.Path y z) :
    w.appendPath (p.comp q) = (w.appendPath p).appendPath q := by
  induction q with
  | nil => simp
  | cons q l ih => simp [ih]

@[simp] theorem appendPath_ofVertex {b : Γ.V} (w : NormalWord d a b) (g : 𝔸.vertexGroup b) :
    w.appendPath (Path.ofVertex g) = w.mulLast g := by
  simp [Path.ofVertex_eq_nil_cons]

@[simp] theorem appendPath_ofDart {b c : Γ.V} (w : NormalWord d a b) (e : b ⟶ c) :
    w.appendPath (Path.ofDart e) = w.appendDart e := by
  simp [Path.ofDart_eq_nil_cons]

/-- Homotopic paths act in the same way on normal words. -/
theorem appendPath_eq_of_homotopic {x y : 𝔸.LetterVertex} (w : NormalWord d a x.as)
    {p q : 𝔸.Path x y} (h : p.Homotopic q) : w.appendPath p = w.appendPath q := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | cons _ l ih => simp only [appendPath_cons, ih]
  | mul p g h => simp
  | one p => simp
  | dart_reverse p e => simp
  | dart_ω e c p =>
    simpa [Γ.dart_def] using mulLast_appendDart_ωArrow (w.appendPath p) ⟨e, rfl, rfl⟩ c

/-- Appending a letter and normalizing does not change the homotopy class. -/
theorem toPath_appendLetter_homotopic {x y : 𝔸.LetterVertex} (w : NormalWord d a x.as)
    (l : 𝔸.Letter x y) : Path.Homotopic (w.appendLetter l).toPath (w.toPath.cons l) := by
  cases l with
  | vertex g => exact w.1.toPath_setLast_mul_homotopic g
  | dart e => exact w.1.toPath_appendDart_homotopic d e

/-- Appending a path and normalizing does not change the homotopy class. -/
theorem toPath_appendPath_homotopic {x y : 𝔸.LetterVertex} (w : NormalWord d a x.as)
    (p : 𝔸.Path x y) : Path.Homotopic (w.appendPath p).toPath (w.toPath.comp p) := by
  induction p with
  | nil => exact .refl _
  | cons p l ih => exact (toPath_appendLetter_homotopic _ l).trans (ih.cons l)

/-- The empty normal word spells a path homotopic to the empty path. -/
theorem toPath_empty_homotopic : Path.Homotopic (empty d a).toPath Quiver.Path.nil :=
  Path.Homotopic.ofVertex_one

end NormalWord

section normalForm

variable {𝔸} (d : 𝔸.Transversal) {a b : Γ.V}

/-- The normal form of an `𝔸`-path from `a` to `b` for the transversal `d`: the normal word
obtained from the empty word by appending the letters of the path one at a time. -/
noncomputable def normalForm (p : 𝔸.Path ⟨a⟩ ⟨b⟩) : NormalWord d a b :=
  (NormalWord.empty d a).appendPath p

theorem normalForm_def (p : 𝔸.Path ⟨a⟩ ⟨b⟩) :
    normalForm d p = (NormalWord.empty d a).appendPath p :=
  (rfl)

@[simp] theorem normalForm_nil :
    normalForm d (Quiver.Path.nil : 𝔸.Path ⟨a⟩ ⟨a⟩) = NormalWord.empty d a :=
  (rfl)

@[simp] theorem normalForm_cons {c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨c⟩) (l : 𝔸.Letter ⟨c⟩ ⟨b⟩) :
    normalForm d (p.cons l) = (normalForm d p).appendLetter l :=
  (rfl)

@[simp] theorem normalForm_comp {c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨c⟩) (q : 𝔸.Path ⟨c⟩ ⟨b⟩) :
    normalForm d (p.comp q) = (normalForm d p).appendPath q :=
  NormalWord.appendPath_comp _ p q

@[simp] theorem normalForm_ofVertex (g : 𝔸.vertexGroup a) :
    normalForm d (Path.ofVertex g) = NormalWord.single d g := by
  simp [normalForm_def]

@[simp] theorem normalForm_ofDart (e : a ⟶ b) :
    normalForm d (Path.ofDart e) = (NormalWord.empty d a).appendDart e :=
  NormalWord.appendPath_ofDart _ e

/-- A path is homotopic to its normal form. -/
theorem toPath_normalForm_homotopic (p : 𝔸.Path ⟨a⟩ ⟨b⟩) :
    Path.Homotopic (normalForm d p).toPath p :=
  (NormalWord.toPath_appendPath_homotopic _ p).trans <| by
    simpa using (NormalWord.toPath_empty_homotopic (d := d)).comp (.refl p)

/-- Homotopic paths have the same normal form. -/
theorem normalForm_eq_of_homotopic {p q : 𝔸.Path ⟨a⟩ ⟨b⟩} (h : p.Homotopic q) :
    normalForm d p = normalForm d q :=
  NormalWord.appendPath_eq_of_homotopic _ h

/-- **Normal form theorem**: two `𝔸`-paths are homotopic exactly when they have the same normal
form. -/
theorem normalForm_eq_normalForm_iff {p q : 𝔸.Path ⟨a⟩ ⟨b⟩} :
    normalForm d p = normalForm d q ↔ p.Homotopic q :=
  ⟨fun h ↦ (toPath_normalForm_homotopic d p).symm.trans
    (h ▸ toPath_normalForm_homotopic d q), normalForm_eq_of_homotopic d⟩

private theorem normalForm_toPath_aux :
    ∀ {b : Γ.V} (p : 𝔸.AlternatingPath a b) (hr : p.IsReduced) (hn : p.IsNormalized d),
      normalForm d p.toPath = ⟨p, hr, hn⟩
  | _, .single g, _, _ => by
    ext1
    simp
  | _, .cons p e g, hr, hn => by
    ext1
    simp [normalForm_toPath_aux p hr.1 hn.1, AlternatingPath.appendDart_of_not_cancels d hr.2,
      d.rep_of_mem e hn.2, d.edgePart_of_mem e hn.2]

/-- A normal word is its own normal form. -/
@[simp] theorem normalForm_toPath (w : NormalWord d a b) : normalForm d w.toPath = w :=
  normalForm_toPath_aux d w.1 w.2 w.3

/-- Two normal words are homotopic only when they are equal. -/
@[simp] theorem NormalWord.toPath_homotopic_toPath_iff {w w' : NormalWord d a b} :
    w.toPath.Homotopic w'.toPath ↔ w = w' := by
  rw [← normalForm_eq_normalForm_iff d, normalForm_toPath, normalForm_toPath]

end normalForm

namespace π₁

variable {𝔸} (d : 𝔸.Transversal) (a : Γ.V)

/-- The elements of `π₁(𝔸, a)` correspond to the normal words of closed paths at `a`: an element
is sent to the normal form of any closed path representing it. -/
noncomputable def normalWordEquiv : π₁ 𝔸 a ≃ NormalWord d a a where
  toFun := lift (normalForm d) fun _ _ ↦ normalForm_eq_of_homotopic d
  invFun w := mk w.toPath
  left_inv g := induction_on g fun p ↦ by
    rw [lift_mk]
    exact mk_eq_mk_iff.2 (toPath_normalForm_homotopic d p)
  right_inv w := by
    rw [lift_mk]
    exact normalForm_toPath d w

@[simp] theorem normalWordEquiv_mk (p : 𝔸.Path ⟨a⟩ ⟨a⟩) :
    normalWordEquiv d a (mk p) = normalForm d p :=
  lift_mk _ _ p

@[simp] theorem normalWordEquiv_one : normalWordEquiv d a 1 = NormalWord.empty d a := by
  rw [← mk_nil, normalWordEquiv_mk, normalForm_nil]

@[simp] theorem normalWordEquiv_symm_apply (w : NormalWord d a a) :
    (normalWordEquiv d a).symm w = mk w.toPath :=
  (rfl)

@[simp] theorem mk_toPath_normalForm (p : 𝔸.Path ⟨a⟩ ⟨a⟩) : mk (normalForm d p).toPath = mk p :=
  mk_eq_mk_iff.2 (toPath_normalForm_homotopic d p)

end π₁

/-! ### Injectivity of the vertex groups -/

namespace Path

variable {𝔸} {a : Γ.V}

/-- Two vertex group elements, read as `𝔸`-paths consisting of a single vertex group letter, are
homotopic only when they are equal. -/
@[simp] theorem ofVertex_homotopic_ofVertex_iff {g h : 𝔸.vertexGroup a} :
    (ofVertex g).Homotopic (ofVertex h) ↔ g = h := by
  rw [← normalForm_eq_normalForm_iff default, normalForm_ofVertex, normalForm_ofVertex,
    NormalWord.single_inj]

/-- A nontrivial vertex group element, read as an `𝔸`-path consisting of a single vertex group
letter, is not homotopic to the empty path. -/
@[simp] theorem ofVertex_homotopic_nil_iff {g : 𝔸.vertexGroup a} :
    (ofVertex g).Homotopic Quiver.Path.nil ↔ g = 1 := by
  rw [← ofVertex_homotopic_ofVertex_iff]
  exact ⟨(·.trans Homotopic.ofVertex_one.symm), (·.trans Homotopic.ofVertex_one)⟩

/-- The empty path is not homotopic to a nontrivial vertex group element. -/
@[simp] theorem nil_homotopic_ofVertex_iff {g : 𝔸.vertexGroup a} :
    Homotopic Quiver.Path.nil (ofVertex g) ↔ g = 1 := by
  rw [← ofVertex_homotopic_nil_iff]
  exact ⟨.symm, .symm⟩

end Path

namespace π₁

variable {𝔸} {a b : Γ.V}

/-- The vertex group `A_b` embeds in `π₁(𝔸, a)` through `g ↦ p g p⁻¹`, for every `𝔸`-path `p`
from `a` to `b`. -/
theorem vertexHom_injective (p : 𝔸.Path ⟨a⟩ ⟨b⟩) : Function.Injective (vertexHom p) := by
  intro g h hgh
  rw [vertexHom_apply, vertexHom_apply, mk_eq_mk_iff] at hgh
  -- Conjugating back by `p` recovers the vertex group letters.
  have key (k : 𝔸.vertexGroup b) : Path.Homotopic
      ((p.reverse.comp ((p.comp (Path.ofVertex k)).comp p.reverse)).comp p) (Path.ofVertex k) := by
    simpa only [Quiver.Path.comp_assoc, Quiver.Path.nil_comp, Quiver.Path.comp_nil] using
      (Path.Homotopic.reverse_comp p).comp
        ((Path.Homotopic.refl (Path.ofVertex k)).comp (Path.Homotopic.reverse_comp p))
  exact Path.ofVertex_homotopic_ofVertex_iff.1 <|
    (key g).symm.trans <| (((hgh.comp_left p.reverse).comp_right p)).trans (key h)

@[simp] theorem vertexHom_inj (p : 𝔸.Path ⟨a⟩ ⟨b⟩) {g h : 𝔸.vertexGroup b} :
    vertexHom p g = vertexHom p h ↔ g = h :=
  (vertexHom_injective p).eq_iff

@[simp] theorem vertexHom_eq_one_iff (p : 𝔸.Path ⟨a⟩ ⟨b⟩) {g : 𝔸.vertexGroup b} :
    vertexHom p g = 1 ↔ g = 1 :=
  map_eq_one_iff _ (vertexHom_injective p)

@[simp] theorem mk_ofVertex_inj {g h : 𝔸.vertexGroup a} :
    mk (Path.ofVertex g) = mk (Path.ofVertex h) ↔ g = h :=
  mk_eq_mk_iff.trans Path.ofVertex_homotopic_ofVertex_iff

@[simp] theorem mk_ofVertex_eq_one_iff {g : 𝔸.vertexGroup a} :
    mk (Path.ofVertex g) = 1 ↔ g = 1 := by
  rw [← mk_nil, mk_eq_mk_iff, Path.ofVertex_homotopic_nil_iff]

end π₁

end GraphOfGroups

end TauCeti
