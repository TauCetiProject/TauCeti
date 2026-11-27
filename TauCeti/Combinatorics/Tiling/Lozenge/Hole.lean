/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Cochain
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin

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

variable {R : Set TriFace} {f : TriFace}

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
    · rw [faceSign_across, TriFace.edge_across]
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
  cases cf <;> cases cq <;> simp [faceSum_def, rayCochain_def, TriFace.ext_iff] at hf ⊢ <;> grind

/-- The circulation of the ray cochain of `q` round `q` is `1`. -/
theorem faceSign_mul_faceSum_rayCochain_self (q : TriFace) :
    faceSign q * faceSum (rayCochain q) q = 1 := by
  obtain ⟨⟨a, b⟩, cq⟩ := q
  cases cq <;> simp [faceSum_def, rayCochain_def]

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
  set d : TriEdge → ℤ := rayCochain q₀ - fun e => g e.target - g e.v with hd_def
  have hface : ∀ f, faceSum d f = faceSum (rayCochain q₀) f := fun f => by
    rw [hd_def, faceSum_sub, faceSum_coboundary, sub_zero]
  have hzero := sum_faceSign_mul_faceSum_eq_zero Q d fun q hq k hk => by
    have hR' : q.across k ∈ R :=
      (hnbr q hq _ _ (q.edge_mem_edges k) (q.edge_mem_edges_across k)).resolve_left hk
    rw [hd_def, Pi.sub_apply, hg _ (mem_regionEdges.2 ⟨_, hR', q.edge_mem_edges_across k⟩),
      sub_self]
  simp_rw [hface] at hzero
  rw [Finset.sum_eq_single_of_mem q₀ hq₀ fun f _ hf => by
    rw [faceSum_rayCochain_of_ne hf, mul_zero], faceSign_mul_faceSum_rayCochain_self] at hzero
  exact one_ne_zero hzero

end TauCeti
