/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.RelativeGrading

/-!
# Moving the basepoint of a Heegaard diagram across `α`-curves

Let `(Σ, α, β, z)` be a pointed Heegaard diagram of a closed `3`-manifold `Y`. Ozsváth and Szabó
show that moving the basepoint changes the spin^c structure of every generator by the same class:
for a basepoint arc from `z₁` to `z₂` which avoids the `β`-curves and crosses the `α`-curve `αᵢ`
algebraically once and every other `α`-curve algebraically zero times,
`s_{z₂}(x) - s_{z₁}(x) = αᵢ*`, the Poincaré dual of a cycle dual to `αᵢ`
(arXiv:math/0101206, Lemma 2.19). Since `c₁(s + a) = c₁(s) + 2 a` and the first Chern class
evaluates on the class `H(P)` of a periodic domain as the combinatorial Maslov index
`⟨c₁(s_z(x)), H(P)⟩ = μ_x(P) = e(P) + 2 n_x(P)` (arXiv:math/0105202, Proposition 7.5), this
predicts that the Maslov indices of periodic domains change by twice the pairing with `αᵢ*`, which
on `H(P)` is, up to the orientation convention, the coefficient of `αᵢ` in `∂P`.

This file proves the combinatorial form of this change for the incidence data
`TauCeti.HeegaardRegionSystem`.

A path of regions crossing only `α`-arcs (`TauCeti.HeegaardRegionSystem.IsAlphaPath`) is a list
of crossings: the entry `(p, true)` crosses the `α`-arc starting at `p` from its right to its
left, and `(p, false)` crosses it back. Along such a path the multiplicity of a domain `D` changes
by its `α`-boundary at each crossing
(`TauCeti.HeegaardRegionSystem.IsAlphaPath.sub_eq_sum_map`). When the `α`-boundary of `D` is a sum
`∑ aᵢ αᵢ` of whole `α`-curves, as for a periodic domain, the total change depends only on the
algebraic crossing numbers `kᵢ` of the path with the `α`-curves
(`TauCeti.HeegaardRegionSystem.alphaCrossingNumber`): it is `∑ kᵢ aᵢ`
(`TauCeti.HeegaardRegionSystem.IsAlphaPath.sub_eq_sum_alphaCrossingNumber_mul`). This records the
traced cycle of a general basepoint path, not only its endpoints.

Moving the single basepoint from the region `z₁` to the region `z₂` identifies the periodic
domains of the two pointed diagrams by `P ↦ P - n_{z₂}(P) Σ`, where `Σ = 1` is the whole surface
(`TauCeti.HeegaardRegionSystem.basepointChangeEquiv`); the two periodic domains have the same
boundary, hence represent the same class in `H₂(Y; ℤ)`. Since the whole surface has Maslov index
two, the Maslov index drops by `2 n_{z₂}(P)`
(`TauCeti.HeegaardRegionSystem.maslovIndex_basepointChangeEquiv`), and for a path from `z₁` to
`z₂` this is `2 ∑ kᵢ aᵢ(P)`
(`TauCeti.HeegaardRegionSystem.IsAlphaPath.maslovIndex_basepointChangeEquiv`). For a path crossing
`αᵢ` algebraically once and the other `α`-curves algebraically zero times the drop is `2 aᵢ(P)`
(`TauCeti.HeegaardRegionSystem.IsAlphaPath.maslovIndex_basepointChangeEquiv_of_eq_single`),
the same for every generator: the combinatorial form of `s_{z₂}(x) - s_{z₁}(x) = αᵢ*`. Reversing
the path negates every crossing number (`TauCeti.HeegaardRegionSystem.alphaCrossingNumber_reverse`
and `TauCeti.HeegaardRegionSystem.alphaCrossingNumber_map_not`), and the constant path has
crossing numbers zero, so the increments are `-αᵢ*` and `0`. On a
geometric diagram, identifying the pairing with `c₁` requires the two theorems recalled above,
which are not formalized here.

## Main definitions

* `TauCeti.HeegaardRegionSystem.IsAlphaPath`: a path of regions crossing only `α`-arcs.
* `TauCeti.HeegaardRegionSystem.alphaCrossingNumber`: its algebraic crossing number with an
  `α`-curve.
* `TauCeti.HeegaardRegionSystem.basepointChangeEquiv`: the identification of the periodic domains
  of the diagrams pointed at `z₁` and at `z₂`.

## Main results

* `TauCeti.HeegaardRegionSystem.IsAlphaPath.sub_eq_sum_alphaCrossingNumber_mul`: along a path
  from `r` to `r'`, a domain with `α`-boundary `∑ aᵢ αᵢ` changes by `∑ kᵢ aᵢ`.
* `TauCeti.HeegaardRegionSystem.IsAlphaPath.append` and
  `TauCeti.HeegaardRegionSystem.IsAlphaPath.reverse`: paths concatenate and reverse.
* `TauCeti.HeegaardRegionSystem.alphaCrossingNumber_append`,
  `TauCeti.HeegaardRegionSystem.alphaCrossingNumber_reverse` and
  `TauCeti.HeegaardRegionSystem.alphaCrossingNumber_map_not`: crossing numbers add under
  concatenation, are unchanged by reversing the list and negate when every crossing is flipped.
* `TauCeti.HeegaardRegionSystem.basepointChangeEquiv_trans`: moving the basepoint in two steps is
  moving it in one.
* `TauCeti.HeegaardRegionSystem.maslovIndex_basepointChangeEquiv`: the Maslov index drops by
  `2 n_{z₂}(P)`.
* `TauCeti.HeegaardRegionSystem.mem_periodicMaslovIndices_withBasepoints_iff`: the periodic Maslov
  indices of the diagram pointed at `z₂` are the numbers `μ_x(P) - 2 n_{z₂}(P)` for the periodic
  domains `P` of the diagram pointed at `z₁`.
* `TauCeti.HeegaardRegionSystem.IsAlphaPath.maslovIndex_basepointChangeEquiv_of_eq_single`:
  across a path crossing `αᵢ` algebraically once and the other `α`-curves algebraically zero times,
  the Maslov index of every periodic domain drops by twice its `αᵢ`-coefficient.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), Lemma 2.19 (the change of spin^c
  structure under a change of basepoint).
* P. Ozsváth and Z. Szabó, *Holomorphic disks and three-manifold invariants: properties and
  applications*, Ann. of Math. **159** (2004),
  [arXiv:math/0105202](https://arxiv.org/abs/math/0105202), Proposition 7.5
  (`⟨c₁(s_z(x)), H(P)⟩ = e(P) + 2 n_x(P)`).
-/

public section

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  (H : HeegaardRegionSystem n Point Region Basepoint)

open Finset

section AlphaPath

/-- `H.IsAlphaPath r l r'`: the list of crossings `l` is a path of regions from `r` to `r'`
crossing only `α`-arcs. The entry `(p, true)` crosses the `α`-arc starting at `p` from the region
on its right to the region on its left, and `(p, false)` crosses it from left to right. A
basepoint arc avoiding the `β`-curves traces such a path. -/
inductive IsAlphaPath : Region → List (Point × Bool) → Region → Prop
  /-- The constant path. -/
  | nil (r : Region) : IsAlphaPath r [] r
  /-- Cross the `α`-arc starting at `p` from its right to its left, then follow `l`. -/
  | cons_true {p : Point} {l : List (Point × Bool)} {r : Region} :
      IsAlphaPath (H.alphaLeft p) l r → IsAlphaPath (H.alphaRight p) ((p, true) :: l) r
  /-- Cross the `α`-arc starting at `p` from its left to its right, then follow `l`. -/
  | cons_false {p : Point} {l : List (Point × Bool)} {r : Region} :
      IsAlphaPath (H.alphaRight p) l r → IsAlphaPath (H.alphaLeft p) ((p, false) :: l) r

/-- The empty list of crossings is a path from `r` to `r'` exactly when `r = r'`. -/
@[simp]
theorem isAlphaPath_nil_iff {r r' : Region} : H.IsAlphaPath r [] r' ↔ r = r' :=
  ⟨by rintro ⟨⟩; rfl, by rintro rfl; exact .nil r⟩

/-- A list of crossings starting with `(p, b)` is a path from `r` exactly when `r` is the region
on the side of the `α`-arc starting at `p` that the crossing leaves, and the rest of the list is a
path from the region on the other side. -/
@[simp]
theorem isAlphaPath_cons_iff {r r' : Region} {p : Point} {b : Bool} {l : List (Point × Bool)} :
    H.IsAlphaPath r ((p, b) :: l) r' ↔
      r = (if b then H.alphaRight p else H.alphaLeft p) ∧
        H.IsAlphaPath (if b then H.alphaLeft p else H.alphaRight p) l r' := by
  constructor
  · rintro (_ | h | h) <;> simpa
  · cases b <;> rintro ⟨rfl, h⟩
    exacts [.cons_false h, .cons_true h]

/-- The algebraic crossing number of a list of crossings with the `α`-curve `αᵢ`: each crossing of
an arc of `αᵢ` from right to left counts `+1`, and each crossing from left to right counts
`-1`. -/
def alphaCrossingNumber (l : List (Point × Bool)) (i : Fin n) : ℤ :=
  (l.map fun s => if H.alpha s.1 = i then (if s.2 then 1 else -1) else 0).sum

@[simp]
theorem alphaCrossingNumber_nil (i : Fin n) : H.alphaCrossingNumber [] i = 0 :=
  (rfl)

@[simp]
theorem alphaCrossingNumber_cons (s : Point × Bool) (l : List (Point × Bool)) (i : Fin n) :
    H.alphaCrossingNumber (s :: l) i =
      (if H.alpha s.1 = i then (if s.2 then 1 else -1) else 0) + H.alphaCrossingNumber l i := by
  simp [alphaCrossingNumber]

@[simp]
theorem alphaCrossingNumber_append (l l' : List (Point × Bool)) (i : Fin n) :
    H.alphaCrossingNumber (l ++ l') i = H.alphaCrossingNumber l i + H.alphaCrossingNumber l' i := by
  simp [alphaCrossingNumber]

/-- Traversing a list of crossings in the opposite order does not change its crossing numbers. -/
@[simp]
theorem alphaCrossingNumber_reverse (l : List (Point × Bool)) (i : Fin n) :
    H.alphaCrossingNumber l.reverse i = H.alphaCrossingNumber l i := by
  simp [alphaCrossingNumber, List.map_reverse]

/-- Making each crossing in the opposite direction negates the crossing numbers. -/
@[simp]
theorem alphaCrossingNumber_map_not (l : List (Point × Bool)) (i : Fin n) :
    H.alphaCrossingNumber (l.map fun s => (s.1, !s.2)) i = -H.alphaCrossingNumber l i := by
  induction l with
  | nil => simp
  | cons s l ih =>
    rw [List.map_cons, alphaCrossingNumber_cons, ih, alphaCrossingNumber_cons]
    rcases s with ⟨p, _ | _⟩ <;> by_cases h : H.alpha p = i <;> simp [h] <;> ring

variable {H}

namespace IsAlphaPath

variable {r r' r'' : Region} {l l' : List (Point × Bool)}

/-- Concatenating a path from `r` to `r'` with a path from `r'` to `r''` gives a path from `r` to
`r''`. -/
theorem append (h : H.IsAlphaPath r l r') (h' : H.IsAlphaPath r' l' r'') :
    H.IsAlphaPath r (l ++ l') r'' := by
  induction h with
  | nil => exact h'
  | cons_true _ ih => exact .cons_true (ih h')
  | cons_false _ ih => exact .cons_false (ih h')

/-- Traversing a path from `r` to `r'` backwards, each crossing in the opposite direction, gives a
path from `r'` to `r`. -/
theorem reverse (h : H.IsAlphaPath r l r') :
    H.IsAlphaPath r' (l.map fun s => (s.1, !s.2)).reverse r := by
  induction h with
  | nil r => exact .nil r
  | @cons_true p l r _ ih =>
    simpa using ih.append (.cons_false (.nil _) : H.IsAlphaPath (H.alphaLeft p) [(p, false)] _)
  | @cons_false p l r _ ih =>
    simpa using ih.append (.cons_true (.nil _) : H.IsAlphaPath (H.alphaRight p) [(p, true)] _)

/-- Along a path from `r` to `r'`, the multiplicity of a domain `D` changes at each crossing by
its `α`-boundary on the crossed arc, with the sign of the crossing. -/
theorem sub_eq_sum_map (h : H.IsAlphaPath r l r') (D : Region → ℤ) :
    D r' - D r = (l.map fun s => (if s.2 then 1 else -1) * H.alphaBoundary D s.1).sum := by
  induction h with
  | nil => simp
  | cons_true _ ih | cons_false _ ih =>
    rw [List.map_cons, List.sum_cons, ← ih, alphaBoundary_apply]
    simp only [Bool.false_eq_true, ↓reduceIte]
    ring

/-- Along a path from `r` to `r'`, a domain whose `α`-boundary is the sum `∑ aᵢ αᵢ` of whole
`α`-curves changes by `∑ kᵢ aᵢ`, for the crossing numbers `kᵢ` of the path with the `α`-curves.
The change only depends on the traced cycle of the path. -/
theorem sub_eq_sum_alphaCrossingNumber_mul (h : H.IsAlphaPath r l r') {D : Region → ℤ}
    {a : Fin n → ℤ} (ha : ∀ p, H.alphaBoundary D p = a (H.alpha p)) :
    D r' - D r = ∑ i, H.alphaCrossingNumber l i * a i := by
  simp_rw [h.sub_eq_sum_map D, ha]
  clear h
  induction l with
  | nil => simp
  | cons s l ih =>
    rw [List.map_cons, List.sum_cons, ih]
    simp [add_mul, sum_add_distrib, ite_mul]

end IsAlphaPath

end AlphaPath

section BasepointChange

variable {z₁ z₂ z₃ : Region}

/-- Subtracting `n_{z₂}(P)` copies of the whole surface from a periodic domain `P` for one
basepoint gives a periodic domain for the basepoint `z₂`, with the same boundary. -/
private theorem sub_smul_one_mem_periodicDomains {P : Region → ℤ}
    (hP : P ∈ (H.withBasepoints fun _ : Unit => z₁).periodicDomains) :
    P - P z₂ • 1 ∈ (H.withBasepoints fun _ : Unit => z₂).periodicDomains := by
  rw [mem_periodicDomains_withBasepoints_iff] at hP ⊢
  refine ⟨by simp, ?_, ?_⟩ <;> rw [map_sub, map_zsmul] <;> simp [hP.2.1, hP.2.2]

variable (z₁ z₂) in
/-- Moving the single basepoint from the region `z₁` to the region `z₂` identifies the periodic
domains of the two pointed diagrams: a periodic domain `P` for `z₁` corresponds to
`P - n_{z₂}(P) Σ`, where `Σ = 1` is the whole surface. The two have the same boundary, so on a
geometric diagram they represent the same class in `H₂(Y; ℤ)`. -/
def basepointChangeEquiv :
    (H.withBasepoints fun _ : Unit => z₁).periodicDomains ≃+
      (H.withBasepoints fun _ : Unit => z₂).periodicDomains where
  toFun P := ⟨P - (P : Region → ℤ) z₂ • 1, sub_smul_one_mem_periodicDomains H P.property⟩
  invFun Q := ⟨Q - (Q : Region → ℤ) z₁ • 1, sub_smul_one_mem_periodicDomains H Q.property⟩
  left_inv P := Subtype.ext <| by
    have h := (mem_periodicDomains_withBasepoints_iff.mp P.property).1
    ext r
    simp [h]
  right_inv Q := Subtype.ext <| by
    have h := (mem_periodicDomains_withBasepoints_iff.mp Q.property).1
    ext r
    simp [h]
  map_add' P Q := Subtype.ext <| by
    ext r
    simp only [AddSubgroup.coe_add, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply,
      smul_eq_mul, mul_one]
    ring

@[simp]
theorem coe_basepointChangeEquiv_apply
    (P : (H.withBasepoints fun _ : Unit => z₁).periodicDomains) :
    (H.basepointChangeEquiv z₁ z₂ P : Region → ℤ) = P - (P : Region → ℤ) z₂ • 1 :=
  (rfl)

/-- Moving the basepoint back is the inverse identification. -/
@[simp]
theorem basepointChangeEquiv_symm :
    (H.basepointChangeEquiv z₁ z₂).symm = H.basepointChangeEquiv z₂ z₁ :=
  (rfl)

/-- Not moving the basepoint is the identity. -/
@[simp]
theorem basepointChangeEquiv_self : H.basepointChangeEquiv z₁ z₁ = AddEquiv.refl _ := by
  ext P r
  simp [(mem_periodicDomains_withBasepoints_iff.mp P.property).1]

/-- Moving the basepoint from `z₁` to `z₂` and then to `z₃` is moving it from `z₁` to `z₃`. -/
@[simp]
theorem basepointChangeEquiv_trans :
    (H.basepointChangeEquiv z₁ z₂).trans (H.basepointChangeEquiv z₂ z₃) =
      H.basepointChangeEquiv z₁ z₃ := by
  ext P r
  simp only [AddEquiv.trans_apply, coe_basepointChangeEquiv_apply, Pi.sub_apply, Pi.smul_apply,
    Pi.one_apply, smul_eq_mul, mul_one]
  ring

namespace IsAlphaPath

variable {H} {l : List (Point × Bool)}

/-- Along a path from `z₁` to `z₂` crossing only `α`-arcs, a periodic domain `P` for the basepoint
`z₁` with `α`-boundary `∑ aᵢ αᵢ` has multiplicity `n_{z₂}(P) = ∑ kᵢ aᵢ` at `z₂`, for the crossing
numbers `kᵢ` of the path. -/
theorem apply_eq_sum_alphaCrossingNumber_mul (h : H.IsAlphaPath z₁ l z₂)
    (P : (H.withBasepoints fun _ : Unit => z₁).periodicDomains) {a : Fin n → ℤ}
    (ha : ∀ p, H.alphaBoundary P p = a (H.alpha p)) :
    (P : Region → ℤ) z₂ = ∑ i, H.alphaCrossingNumber l i * a i := by
  rw [← h.sub_eq_sum_alphaCrossingNumber_mul ha,
    (mem_periodicDomains_withBasepoints_iff.mp P.property).1, sub_zero]

end IsAlphaPath

variable [Fintype Point] [DecidableEq Region] [Fintype Region] {χ : Region → ℤ}

/-- When the region Euler characteristics are those of a closed surface of genus `n`, moving the
basepoint from `z₁` to `z₂` lowers the Maslov index of a periodic domain `P` by `2 n_{z₂}(P)`, at
any two generators: the whole surface has Maslov index two. -/
theorem maslovIndex_basepointChangeEquiv (hχ : ∑ r, χ r - Fintype.card Point = 2 - 2 * (n : ℤ))
    (x y : H.Generator) (P : (H.withBasepoints fun _ : Unit => z₁).periodicDomains) :
    H.maslovIndex χ x y (H.basepointChangeEquiv z₁ z₂ P) =
      H.maslovIndex χ x y P - 2 * (P : Region → ℤ) z₂ := by
  rw [coe_basepointChangeEquiv_apply, map_sub, map_zsmul, maslovIndex_one_eq_two hχ,
    zsmul_eq_mul]
  ring

/-- When the region Euler characteristics are those of a closed surface of genus `n`, the periodic
Maslov indices at `x` of the diagram pointed at `z₂` are the numbers `μ_x(P) - 2 n_{z₂}(P)` for the
periodic domains `P` of the diagram pointed at `z₁`. -/
theorem mem_periodicMaslovIndices_withBasepoints_iff
    (hχ : ∑ r, χ r - Fintype.card Point = 2 - 2 * (n : ℤ)) {x : H.Generator} {q : ℚ} :
    q ∈ (H.withBasepoints fun _ : Unit => z₂).periodicMaslovIndices χ x ↔
      ∃ P ∈ (H.withBasepoints fun _ : Unit => z₁).periodicDomains,
        H.maslovIndex χ x x P - 2 * P z₂ = q := by
  rw [mem_periodicMaslovIndices_iff]
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    obtain ⟨P, hPQ⟩ := (H.basepointChangeEquiv z₁ z₂).surjective ⟨Q, hQ⟩
    refine ⟨P, P.property, ?_⟩
    rw [← H.maslovIndex_basepointChangeEquiv hχ x x P, hPQ]
    simp
  · rintro ⟨P, hP, rfl⟩
    refine ⟨_, (H.basepointChangeEquiv z₁ z₂ ⟨P, hP⟩).property, ?_⟩
    rw [maslovIndex_withBasepoints, H.maslovIndex_basepointChangeEquiv hχ x x ⟨P, hP⟩]

namespace IsAlphaPath

variable {H} {l : List (Point × Bool)}

/-- **The change of the Maslov index under a change of basepoint.** When the region Euler
characteristics are those of a closed surface of genus `n`, moving the basepoint along a path from
`z₁` to `z₂` crossing only `α`-arcs lowers the Maslov index of a periodic domain with `α`-boundary
`∑ aᵢ αᵢ` by `2 ∑ kᵢ aᵢ`, for the crossing numbers `kᵢ` of the path, at any two generators. -/
theorem maslovIndex_basepointChangeEquiv (h : H.IsAlphaPath z₁ l z₂)
    (hχ : ∑ r, χ r - Fintype.card Point = 2 - 2 * (n : ℤ)) (x y : H.Generator)
    (P : (H.withBasepoints fun _ : Unit => z₁).periodicDomains) {a : Fin n → ℤ}
    (ha : ∀ p, H.alphaBoundary P p = a (H.alpha p)) :
    H.maslovIndex χ x y (H.basepointChangeEquiv z₁ z₂ P) =
      H.maslovIndex χ x y P - 2 * ∑ i, H.alphaCrossingNumber l i * a i := by
  rw [H.maslovIndex_basepointChangeEquiv hχ, h.apply_eq_sum_alphaCrossingNumber_mul P ha]

/-- **Moving the basepoint across `αᵢ`.** When the region Euler characteristics are those of a
closed surface of genus `n`, moving the basepoint along a path crossing only `α`-arcs, which
crosses `αᵢ` algebraically once and every other `α`-curve algebraically zero times, lowers the
Maslov index of every periodic domain by twice the coefficient `aᵢ` of `αᵢ` in its boundary, at any
two generators. This is the combinatorial form of `s_{z₂}(x) - s_{z₁}(x) = αᵢ*`: the shift is the
same for every generator. -/
theorem maslovIndex_basepointChangeEquiv_of_eq_single
    (h : H.IsAlphaPath z₁ l z₂) {i : Fin n} (hl : H.alphaCrossingNumber l = Pi.single i 1)
    (hχ : ∑ r, χ r - Fintype.card Point = 2 - 2 * (n : ℤ)) (x y : H.Generator)
    (P : (H.withBasepoints fun _ : Unit => z₁).periodicDomains) {a : Fin n → ℤ}
    (ha : ∀ p, H.alphaBoundary P p = a (H.alpha p)) :
    H.maslovIndex χ x y (H.basepointChangeEquiv z₁ z₂ P) = H.maslovIndex χ x y P - 2 * a i := by
  rw [h.maslovIndex_basepointChangeEquiv hχ x y P ha, hl]
  simp [Pi.single_apply]

end IsAlphaPath

end BasepointChange

end HeegaardRegionSystem

end TauCeti
