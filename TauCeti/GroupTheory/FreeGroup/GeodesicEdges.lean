/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.Reduce
public import TauCeti.LinearAlgebra.Matrix.PosSemidef

/-!
# Geodesic edges in the Cayley tree of a free group

The Cayley graph of `FreeGroup α` with respect to the free generators is a tree. We record an
edge as a pair `(y, a) : FreeGroup α × α`, standing for the edge joining `y` and `y * of a`; left
multiplication by `g` acts on edges by `(y, a) ↦ (g * y, a)`. The finite set
`FreeGroup.geodesicEdges g` consists of the edges of the geodesic from `1` to `g`; reading the
reduced word of `g` letter by letter traverses them in order.

The assignment `g ↦ geodesicEdges g` is Haagerup's cocycle with values in the finite sets of
edges under symmetric difference:

`geodesicEdges (g * h) = geodesicEdges g ∆ g • geodesicEdges h`.

Consequently `geodesicEdges (g⁻¹ * h)` is the translate by `g⁻¹` of
`geodesicEdges g ∆ geodesicEdges h`, so the word metric of the free group is a symmetric-difference
metric, and any multiplicative weight on letters is a product over a symmetric difference. With
the Schur product theorem this gives Haagerup's positive-definite functions on free groups: for
real weights `ρ a ∈ [-1, 1]`, the function sending `g` to the product of `ρ` over the letters of
the reduced word of `g` is positive definite, and in particular so is `g ↦ r ^ ‖g‖` for
`|r| ≤ 1`, where `‖g‖` is the word length `FreeGroup.norm g`.

## Main declarations

* `FreeGroup.geodesicEdges`: the edges of the geodesic from `1` to `g` in the Cayley tree.
* `FreeGroup.geodesicEdges_mul_of`: multiplying by a generator toggles one edge.
* `FreeGroup.geodesicEdges_mul`: the cocycle identity.
* `FreeGroup.geodesicEdges_inv_mul`: the edges of the geodesic from `g` to `h`, moved to `1`.
* `FreeGroup.prod_geodesicEdges` and `FreeGroup.card_geodesicEdges`: products over geodesic
  edges are products over the letters of the reduced word, and `#(geodesicEdges g) = norm g`.
* `FreeGroup.card_symmDiff_geodesicEdges`: `#(geodesicEdges g ∆ geodesicEdges h) = norm (g⁻¹ * h)`.
* `FreeGroup.posSemidef_prod_map_toWord_inv_mul` and `FreeGroup.posSemidef_pow_norm_inv_mul`:
  Haagerup's positive-definite functions on free groups.

## References

* U. Haagerup, *An example of a non nuclear C*-algebra, which has the metric approximation
  property*, Invent. Math. 50 (1979), 279–293.
* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, Examples 16.1.2.
-/

public section

open Finset
open scoped ComplexOrder

namespace FreeGroup

variable {α : Type*}

/-- The edge of the Cayley tree traversed by reading the letter `x` at the vertex `y`: it joins
`y` and `y * mk [x]`. -/
private def letterEdge (y : FreeGroup α) (x : α × Bool) : FreeGroup α × α :=
  (if x.2 then y else y * mk [x], x.1)

/-- The edges, in order, of the path in the Cayley tree that starts at `y` and reads the word
`w` letter by letter. -/
private def edgesFrom : FreeGroup α → List (α × Bool) → List (FreeGroup α × α)
  | _, [] => []
  | y, x :: w => letterEdge y x :: edgesFrom (y * mk [x]) w

private theorem edgesFrom_append (y : FreeGroup α) (u v : List (α × Bool)) :
    edgesFrom y (u ++ v) = edgesFrom y u ++ edgesFrom (y * mk u) v := by
  induction u generalizing y with
  | nil => simp [edgesFrom, ← one_eq_mk]
  | cons x u ih => simp [edgesFrom, ih, mul_assoc, mul_mk]

/-- The endpoints of `letterEdge y x` are `y` and `y * mk [x]`, in one order or the other. -/
private theorem letterEdge_endpoints (y : FreeGroup α) (x : α × Bool) :
    ((letterEdge y x).1 = y ∧ (letterEdge y x).1 * of (letterEdge y x).2 = y * mk [x]) ∨
      ((letterEdge y x).1 = y * mk [x] ∧ (letterEdge y x).1 * of (letterEdge y x).2 = y) := by
  obtain ⟨a, _ | _⟩ := x
  · have : mk [(a, false)] = (of a)⁻¹ := by simp [of, inv_mk, invRev]
    simp [letterEdge, this]
  · simp [letterEdge, of]

/-- Both endpoints of an edge on the path from `y` reading `w` lie within distance `w.length`
of `y`. -/
private theorem norm_of_mem_edgesFrom {y : FreeGroup α} {w : List (α × Bool)}
    {e : FreeGroup α × α} (he : e ∈ edgesFrom y w) [DecidableEq α] :
    norm (y⁻¹ * e.1) ≤ w.length ∧ norm (y⁻¹ * (e.1 * of e.2)) ≤ w.length := by
  induction w generalizing y with
  | nil => simp [edgesFrom] at he
  | cons x w ih =>
    have hx : norm (mk [x]) ≤ 1 := norm_mk_le
    rcases List.mem_cons.1 he with rfl | he
    · rcases letterEdge_endpoints y x with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₂, h₁] <;>
        simp only [inv_mul_cancel, inv_mul_cancel_left, norm_one, List.length_cons] <;>
        omega
    · obtain ⟨ih₁, ih₂⟩ := ih he
      have key (z : FreeGroup α) : y⁻¹ * z = mk [x] * ((y * mk [x])⁻¹ * z) := by group
      rw [key, key (e.1 * of e.2)]
      exact ⟨(norm_mul_le _ _).trans (by simp only [List.length_cons]; omega),
        (norm_mul_le _ _).trans (by simp only [List.length_cons]; omega)⟩

variable [DecidableEq α]

/-- The edges of the geodesic from `1` to `g` in the Cayley tree of the free group. The pair
`(y, a)` stands for the edge joining `y` and `y * of a`; reading the reduced word of `g` letter by
letter traverses these edges in order. -/
def geodesicEdges (g : FreeGroup α) : Finset (FreeGroup α × α) :=
  (edgesFrom 1 g.toWord).toFinset

/-- Appending a letter to a reduced word adds one new edge to the geodesic. -/
private theorem geodesicEdges_mul_mk_singleton {g : FreeGroup α} {x : α × Bool}
    (h : (g * mk [x]).toWord = g.toWord ++ [x]) :
    geodesicEdges (g * mk [x]) = insert (letterEdge g x) (geodesicEdges g) ∧
      letterEdge g x ∉ geodesicEdges g := by
  refine ⟨?_, fun hmem => ?_⟩
  · ext e
    simp [geodesicEdges, h, edgesFrom_append, edgesFrom, mk_toWord, or_comm]
  · obtain ⟨h₁, h₂⟩ := norm_of_mem_edgesFrom (List.mem_toFinset.1 hmem)
    have hn : norm (g * mk [x]) = norm g + 1 := by simp [norm, h]
    simp only [inv_one, one_mul] at h₁ h₂
    rcases letterEdge_endpoints g x with ⟨-, h⟩ | ⟨h, -⟩
    · rw [h] at h₂
      exact absurd h₂ (by simp only [norm] at hn ⊢; omega)
    · rw [h] at h₁
      exact absurd h₁ (by simp only [norm] at hn ⊢; omega)

@[simp]
theorem geodesicEdges_one : geodesicEdges (1 : FreeGroup α) = ∅ := by
  simp [geodesicEdges, edgesFrom]

@[simp]
theorem geodesicEdges_of (a : α) : geodesicEdges (of a) = {((1 : FreeGroup α), a)} := by
  simp [geodesicEdges, edgesFrom, letterEdge]

/-- Multiplying by a generator on the right toggles the edge joining `g` and `g * of a`. -/
theorem geodesicEdges_mul_of (g : FreeGroup α) (a : α) :
    geodesicEdges (g * of a) = symmDiff (geodesicEdges g) {(g, a)} := by
  by_cases hlast : g.toWord.getLast? = some (a, false)
  · -- The reduced word of `g` ends with `(of a)⁻¹`, which multiplication by `of a` cancels.
    set h := g * of a
    have hinv : mk [(a, false)] = (of a)⁻¹ := by simp [of, inv_mk, invRev]
    have hg : h * mk [(a, false)] = g := by simp [h, hinv]
    have hw : (h * mk [(a, false)]).toWord = h.toWord ++ [(a, false)] := by
      rw [hg, show h.toWord = g.toWord.dropLast by simp [h, of, toWord_mul_mk_eq, hlast]]
      exact (List.dropLast_append_getLast? _ hlast).symm
    obtain ⟨hins, hnot⟩ := geodesicEdges_mul_mk_singleton hw
    have he : letterEdge h (a, false) = (g, a) := by simp [letterEdge, hg]
    rw [hg, he] at hins
    rw [he] at hnot
    ext e
    by_cases e = (g, a) <;> simp_all [Finset.mem_symmDiff]
  · have hw : (g * mk [(a, true)]).toWord = g.toWord ++ [(a, true)] := by
      simp [toWord_mul_mk_eq, hlast]
    obtain ⟨hins, hnot⟩ := geodesicEdges_mul_mk_singleton hw
    have he : letterEdge g (a, true) = (g, a) := by simp [letterEdge]
    rw [he] at hins hnot
    rw [of, hins]
    ext e
    by_cases e = (g, a) <;> simp_all [Finset.mem_symmDiff]

/-- Multiplying by an inverse generator on the right toggles the edge joining `g * (of a)⁻¹`
and `g`. -/
theorem geodesicEdges_mul_inv_of (g : FreeGroup α) (a : α) :
    geodesicEdges (g * (of a)⁻¹) = symmDiff (geodesicEdges g) {(g * (of a)⁻¹, a)} := by
  have h := geodesicEdges_mul_of (g * (of a)⁻¹) a
  rw [inv_mul_cancel_right] at h
  rw [h, symmDiff_symmDiff_cancel_right]

@[simp]
theorem geodesicEdges_inv_of (a : α) :
    geodesicEdges (of a)⁻¹ = {((of a)⁻¹, a)} := by
  rw [← one_mul (of a)⁻¹, geodesicEdges_mul_inv_of, geodesicEdges_one, ← bot_eq_empty,
    bot_symmDiff]

/-- **Haagerup's cocycle identity.** The geodesic to `g * h` is the symmetric difference of the
geodesic to `g` and the translate by `g` of the geodesic to `h`. -/
theorem geodesicEdges_mul (g h : FreeGroup α) :
    geodesicEdges (g * h) =
      symmDiff (geodesicEdges g) ((geodesicEdges h).image (Prod.map (g * ·) id)) := by
  induction h using FreeGroup.induction_on generalizing g with
  | one => simp only [mul_one, geodesicEdges_one, image_empty]; exact (symmDiff_bot _).symm
  | of a => simp [geodesicEdges_mul_of]
  | inv_of a _ => simp [geodesicEdges_mul_inv_of, geodesicEdges_inv_of]
  | mul x y hx hy =>
    have hinj (k : FreeGroup α) : Function.Injective (Prod.map (k * ·) (id : α → α)) :=
      (mul_right_injective k).prodMap Function.injective_id
    rw [← mul_assoc, hy, hx, hy, image_symmDiff _ _ (hinj g), image_image, symmDiff_assoc]
    congr 3
    ext <;> simp [mul_assoc]

theorem geodesicEdges_inv (g : FreeGroup α) :
    geodesicEdges g⁻¹ = (geodesicEdges g).image (Prod.map (g⁻¹ * ·) id) := by
  have h := geodesicEdges_mul g⁻¹ g
  rw [inv_mul_cancel, geodesicEdges_one, ← bot_eq_empty, eq_comm, symmDiff_eq_bot] at h
  exact h

/-- The geodesic from `g` to `h`, translated to start at `1`, is the geodesic to `g⁻¹ * h`: its
edges are those lying on exactly one of the geodesics from `1` to `g` and to `h`. -/
theorem geodesicEdges_inv_mul (g h : FreeGroup α) :
    geodesicEdges (g⁻¹ * h) =
      (symmDiff (geodesicEdges g) (geodesicEdges h)).image (Prod.map (g⁻¹ * ·) id) := by
  rw [geodesicEdges_mul, geodesicEdges_inv,
    image_symmDiff _ _ ((mul_right_injective g⁻¹).prodMap Function.injective_id)]

/-- A product over the geodesic edges of `g`, weighted by the generator labelling each edge, is
the corresponding product over the letters of the reduced word of `g`. -/
theorem prod_geodesicEdges {M : Type*} [CommMonoid M] (f : α → M) (g : FreeGroup α) :
    ∏ e ∈ geodesicEdges g, f e.2 = (g.toWord.map fun x => f x.1).prod := by
  induction g using induction_on_reduced with
  | one => simp
  | mul_mk_singleton g x hw ih =>
    obtain ⟨hins, hnot⟩ := geodesicEdges_mul_mk_singleton hw
    rw [hins, prod_insert hnot, ih, hw, List.map_append, List.prod_append]
    simp [letterEdge, mul_comm]

/-- The geodesic from `1` to `g` has `norm g` edges. -/
@[simp]
theorem card_geodesicEdges (g : FreeGroup α) : #(geodesicEdges g) = norm g := by
  induction g using induction_on_reduced with
  | one => simp
  | mul_mk_singleton g x hw ih =>
    obtain ⟨hins, hnot⟩ := geodesicEdges_mul_mk_singleton hw
    rw [hins, card_insert_of_notMem hnot, ih]
    simp [norm, hw]

/-- The word metric of the free group is the symmetric-difference metric on geodesic edge sets. -/
theorem card_symmDiff_geodesicEdges (g h : FreeGroup α) :
    #(symmDiff (geodesicEdges g) (geodesicEdges h)) = norm (g⁻¹ * h) := by
  rw [← card_geodesicEdges, geodesicEdges_inv_mul,
    card_image_of_injective _ ((mul_right_injective g⁻¹).prodMap Function.injective_id)]

/-- **Haagerup's positive-definite functions on free groups.** For real weights `ρ a ∈ [-1, 1]`
on the generators, the function sending `g` to the product of `ρ` over the letters of the reduced
word of `g` is positive definite: the kernel `(g, h) ↦ φ (g⁻¹ * h)` is positive semidefinite. -/
theorem posSemidef_prod_map_toWord_inv_mul {𝕜 : Type*} [RCLike 𝕜] (ρ : α → ℝ)
    (hρ : ∀ a, |ρ a| ≤ 1) :
    Matrix.PosSemidef (fun g h : FreeGroup α =>
      ((((g⁻¹ * h).toWord.map fun x => ρ x.1).prod : ℝ) : 𝕜)) := by
  have key (g h : FreeGroup α) : ((g⁻¹ * h).toWord.map fun x => ρ x.1).prod =
      ∏ e ∈ symmDiff (geodesicEdges g) (geodesicEdges h), ρ e.2 := by
    rw [← prod_geodesicEdges, geodesicEdges_inv_mul,
      prod_image fun _ _ _ _ h => (mul_right_injective g⁻¹).prodMap Function.injective_id h]
    rfl
  simp_rw [key]
  exact TauCeti.posSemidef_prod_symmDiff geodesicEdges fun e => hρ e.2

/-- **Haagerup's lemma.** For `|r| ≤ 1`, the function `g ↦ r ^ norm g` on a free group is positive
definite: the kernel `(g, h) ↦ r ^ norm (g⁻¹ * h)` is positive semidefinite. -/
theorem posSemidef_pow_norm_inv_mul {𝕜 : Type*} [RCLike 𝕜] {r : ℝ} (hr : |r| ≤ 1) :
    Matrix.PosSemidef (fun g h : FreeGroup α => ((r ^ norm (g⁻¹ * h) : ℝ) : 𝕜)) := by
  simpa [norm] using posSemidef_prod_map_toWord_inv_mul (𝕜 := 𝕜) (fun _ : α => r) fun _ => hr

end FreeGroup
