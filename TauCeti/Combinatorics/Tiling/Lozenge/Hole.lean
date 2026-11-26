/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Cochain
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Holes obstruct simple connectivity

If `Q` is a nonempty finite set of faces outside a region `R` such that every face sharing an
edge with a face of `Q` lies in `Q ∪ R`, then `R` is not simply connected. The witness is the
cochain dual to a path of faces from a face `q₀ ∈ Q` to infinity, the ray of faces to the right of
`q₀`: it sums to zero round every face other than `q₀` and to `±1` round `q₀`. If it had a
primitive on `R`, subtracting the coboundary of that primitive would give a cochain vanishing on the
edges of `R` with the same sums round faces; the signed sum of these over the faces of `Q`
telescopes to a sum over the boundary edges of `Q`, all of which are edges of `R`, so it vanishes,
while it is `±1`.

## Main definitions

* `TauCeti.faceSum c f`: the sum `c(f, e₁) + c(f, e₂) − c(f, e₃)` of a cochain round a face, so
  that `c` is closed on `R` when it vanishes on every face of `R`.
* `TauCeti.faceSign f`: `1` on white faces and `−1` on black ones, the orientation making
  `faceSign f * faceSum c f` the counterclockwise circulation of `c` round `f`.
* `TauCeti.rayCochain q`: the cochain dual to the ray of faces to the right of the face `q`.

## Main statements

* `TauCeti.sum_faceSign_mul_faceSum_eq_zero`: the signed sum of the face sums of a cochain over a
  finite set `Q` of faces vanishes when the cochain vanishes on the edges with exactly one face in
  `Q`.
* `TauCeti.faceSum_rayCochain_of_ne`, `TauCeti.faceSign_mul_faceSum_rayCochain_self`: the ray
  cochain of `q` sums to zero round every face other than `q`, and its circulation round `q` is
  `1`.
* `TauCeti.not_isSimplyConnectedRegion_of_hole`: a region with a hole is not simply connected.

## References

* R. Kenyon, *Lectures on dimers*, IAS/Park City Math. Ser. 16 (2009).
-/

public section

namespace TauCeti

/-- The sum `c(f, e₁) + c(f, e₂) − c(f, e₃)` of a cochain round a face `f`. A cochain is closed on
a region when this vanishes on every face of the region. -/
def faceSum (c : TriEdge → ℤ) (f : TriFace) : ℤ :=
  c (f.edge 0) + c (f.edge 1) - c (f.edge 2)

/-- The orientation sign of a face: `1` for white faces and `−1` for black ones. Round a white face
`faceSum` runs counterclockwise and round a black face clockwise. -/
def faceSign (f : TriFace) : ℤ :=
  if f.isWhite then 1 else -1

variable {R : Set TriFace} {c : TriEdge → ℤ} {f : TriFace}

theorem faceSum_def (c : TriEdge → ℤ) (f : TriFace) :
    faceSum c f = c (f.edge 0) + c (f.edge 1) - c (f.edge 2) := (rfl)

theorem faceSign_def (f : TriFace) : faceSign f = if f.isWhite then 1 else -1 := (rfl)

theorem isClosedCochainOn_iff_faceSum : IsClosedCochainOn R c ↔ ∀ f ∈ R, faceSum c f = 0 := by
  simp only [isClosedCochainOn_def, faceSum_def, sub_eq_zero]

/-- The coboundary of a function sums to zero round every face. -/
theorem faceSum_coboundary (g : ℤ × ℤ → ℤ) (f : TriFace) :
    faceSum (fun e => g e.target - g e.v) f = 0 :=
  isClosedCochainOn_iff_faceSum.1 (isClosedCochainOn_coboundary Set.univ g) f (Set.mem_univ f)

/-! ### The other face across an edge -/

/-- The face across the edge of direction `k` of `f`. -/
def TriFace.across (f : TriFace) (k : Fin 3) : TriFace :=
  if f.isWhite then (f.edge k).blackFace else (f.edge k).whiteFace

theorem TriFace.across_def (f : TriFace) (k : Fin 3) :
    f.across k = if f.isWhite then (f.edge k).blackFace else (f.edge k).whiteFace := (rfl)

@[simp] theorem TriFace.isWhite_across (f : TriFace) (k : Fin 3) :
    (f.across k).isWhite = !f.isWhite := by
  rw [TriFace.across_def]
  cases f.isWhite <;> simp

theorem TriFace.edge_mem_edges_across (f : TriFace) (k : Fin 3) :
    f.edge k ∈ (f.across k).edges := by
  rw [TriFace.across_def]
  split_ifs
  · exact (f.edge k).mem_blackFace_edges
  · exact (f.edge k).mem_whiteFace_edges

@[simp] theorem TriFace.edge_across (f : TriFace) (k : Fin 3) : (f.across k).edge k = f.edge k := by
  have := TriFace.mem_edges_iff_edge_eq.1 (f.edge_mem_edges_across k)
  rwa [TriFace.edge_k] at this

theorem TriFace.across_ne (f : TriFace) (k : Fin 3) : f.across k ≠ f := fun h => by
  have := congrArg TriFace.isWhite h
  cases hf : f.isWhite <;> simp [hf] at this

@[simp] theorem TriFace.across_across (f : TriFace) (k : Fin 3) : (f.across k).across k = f := by
  rw [TriFace.across_def (f.across k), TriFace.edge_across, TriFace.isWhite_across]
  cases hf : f.isWhite
  · exact (TriEdge.eq_blackFace_of_mem_edges (f.edge_mem_edges k) hf).symm
  · exact (TriEdge.eq_whiteFace_of_mem_edges (f.edge_mem_edges k) hf).symm

/-! ### Discrete Stokes -/

/-- **Discrete Stokes formula.** If a cochain `d` vanishes on every edge of a face of a finite set
`Q` whose face across it is not in `Q`, then the signed sum of the face sums of `d` over `Q`
vanishes: each edge with both faces in `Q` is counted once in each direction. -/
theorem sum_faceSign_mul_faceSum_eq_zero (Q : Finset TriFace) (d : TriEdge → ℤ)
    (hd : ∀ q ∈ Q, ∀ k, q.across k ∉ Q → d (q.edge k) = 0) :
    ∑ q ∈ Q, faceSign q * faceSum d q = 0 := by
  classical
  let s : Fin 3 → ℤ := ![1, 1, -1]
  have hsum : ∀ q, faceSign q * faceSum d q = ∑ k : Fin 3, faceSign q * s k * d (q.edge k) := by
    intro q
    simp only [faceSum_def, Fin.sum_univ_three, s, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  simp_rw [hsum]
  rw [← Finset.sum_product']
  refine Finset.sum_involution
    (fun a _ => if a.1.across a.2 ∈ Q then (a.1.across a.2, a.2) else a) ?_ ?_ ?_ ?_
  · rintro ⟨q, k⟩ ha
    have hq : q ∈ Q := (Finset.mem_product.1 ha).1
    dsimp only
    split_ifs with h
    · have : faceSign (q.across k) = -faceSign q := by
        simp only [faceSign_def, TriFace.isWhite_across]
        cases q.isWhite <;> simp
      rw [this, TriFace.edge_across]
      ring
    · rw [hd q hq k h]
      ring
  · rintro ⟨q, k⟩ ha hne
    have hq : q ∈ Q := (Finset.mem_product.1 ha).1
    dsimp only
    split_ifs with h
    · exact fun h' => TriFace.across_ne q k (congrArg Prod.fst h')
    · exact absurd (by rw [hd q hq k h]; ring) hne
  · rintro ⟨q, k⟩ ha
    dsimp only
    split_ifs with h
    · exact Finset.mem_product.2 ⟨h, Finset.mem_univ _⟩
    · exact ha
  · rintro ⟨q, k⟩ ha
    have hq : q ∈ Q := (Finset.mem_product.1 ha).1
    dsimp only
    split_ifs with h h'
    · simp
    · exact absurd (by rw [TriFace.across_across]; exact hq) h'
    · simp

/-! ### The ray cochain -/

/-- The cochain dual to the ray of faces to the right of the face `q = W(v)` or `B(v)`: `1` on the
edges `((i, v₂), 2)` and `((i, v₂), 3)` with `i > v₁`, which the faces `B(v + e₁), W(v + e₁),
B(v + 2e₁), …` cross, and, for a black face `q = B(v)`, also `1` on its edge `(v, 3)`, across which
the ray leaves `B(v)`. -/
def rayCochain (q : TriFace) (e : TriEdge) : ℤ :=
  (if e.k ≠ 0 ∧ e.v.2 = q.v.2 ∧ q.v.1 < e.v.1 then 1 else 0) +
    if q.isWhite = false ∧ e = ⟨q.v, 2⟩ then 1 else 0

theorem rayCochain_def (q : TriFace) (e : TriEdge) :
    rayCochain q e = (if e.k ≠ 0 ∧ e.v.2 = q.v.2 ∧ q.v.1 < e.v.1 then 1 else 0) +
      if q.isWhite = false ∧ e = ⟨q.v, 2⟩ then 1 else 0 := (rfl)

/-- The ray cochain of `q` sums to zero round every face other than `q`. -/
theorem faceSum_rayCochain_of_ne {q : TriFace} (hf : f ≠ q) : faceSum (rayCochain q) f = 0 := by
  obtain ⟨⟨a, b⟩, cq⟩ := q
  obtain ⟨⟨x, y⟩, cf⟩ := f
  have hxy : cf = cq → ¬(x = a ∧ y = b) := fun h1 h2 => hf (by rw [h1, h2.1, h2.2])
  clear hf
  cases cf <;> cases cq <;>
    simp only [Bool.true_eq_false, Bool.false_eq_true, false_implies, true_implies] at hxy <;>
    simp only [faceSum_def, Fin.isValue, TriFace.edge_mk_false, TriFace.edge_mk_true, ↓reduceIte,
      Prod.mk_add_mk, add_zero, rayCochain_def, ne_eq, not_true_eq_false, false_and,
      TriEdge.mk.injEq, Prod.mk.injEq, Fin.reduceEq, and_false, one_ne_zero, not_false_eq_true,
      true_and, zero_add, and_true, sub_add_cancel_left, neg_eq_zero, ite_eq_right_iff, imp_false,
      not_and, Bool.true_eq_false, and_self, sub_self, zero_ne_one] <;>
    (try split_ifs) <;> omega

/-- The circulation of the ray cochain of `q` round `q` is `1`. -/
theorem faceSign_mul_faceSum_rayCochain_self (q : TriFace) :
    faceSign q * faceSum (rayCochain q) q = 1 := by
  obtain ⟨⟨a, b⟩, cq⟩ := q
  cases cq <;>
    simp [faceSign_def, faceSum_def, rayCochain_def, TriFace.edge_mk_true, TriFace.edge_mk_false]

/-! ### Holes -/

/-- **Holes obstruct simple connectivity.** If `Q` is a nonempty finite set of faces outside `R`
such that every face sharing an edge with a face of `Q` lies in `Q ∪ R`, then `R` is not simply
connected. -/
theorem not_isSimplyConnectedRegion_of_hole {Q : Finset TriFace} (hQ : Q.Nonempty)
    (hQR : ∀ q ∈ Q, q ∉ R)
    (hnbr : ∀ q ∈ Q, ∀ g : TriFace, ∀ e ∈ q.edges, e ∈ g.edges → g ∈ Q ∨ g ∈ R) :
    ¬ IsSimplyConnectedRegion R := by
  intro hR
  obtain ⟨q₀, hq₀⟩ := hQ
  have hclosed : IsClosedCochainOn R (rayCochain q₀) :=
    isClosedCochainOn_iff_faceSum.2 fun f hf =>
      faceSum_rayCochain_of_ne fun h => hQR q₀ hq₀ (h ▸ hf)
  obtain ⟨g, hg⟩ := isExactCochainOn_def.1 (hR.isExactCochainOn_of_isClosedCochainOn _ hclosed)
  rw [isCochainPrimitiveOn_def] at hg
  set d : TriEdge → ℤ := fun e => rayCochain q₀ e - (g e.target - g e.v) with hd_def
  have hface : ∀ f, faceSum d f = faceSum (rayCochain q₀) f := fun f => by
    have := faceSum_coboundary g f
    simp only [faceSum_def, hd_def] at this ⊢
    linarith
  have hzero := sum_faceSign_mul_faceSum_eq_zero Q d fun q hq k hk => by
    have hR' : q.across k ∈ R :=
      (hnbr q hq _ _ (q.edge_mem_edges k) (q.edge_mem_edges_across k)).resolve_left hk
    simp only [hd_def]
    rw [hg _ (mem_regionEdges.2 ⟨_, hR', q.edge_mem_edges_across k⟩), sub_self]
  simp_rw [hface] at hzero
  rw [Finset.sum_eq_single_of_mem q₀ hq₀ fun f _ hf => by
    rw [faceSum_rayCochain_of_ne hf, mul_zero], faceSign_mul_faceSum_rayCochain_self] at hzero
  exact one_ne_zero hzero

end TauCeti
