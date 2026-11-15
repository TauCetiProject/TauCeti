/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.WeylGroup

/-!
# Subwords of a word in the reflections of a root pairing

Let `ω = i₁ ⋯ iᵣ` be a word in the indices of the roots of a root pairing `P`, reduced or not, and
let `ε ∈ {0,1}^r` select a subword. This file defines the Weyl group elements
`w_j = s_{i₁}^{ε₁} ⋯ s_{iⱼ}^{εⱼ}` spelled by the selected letters of the first `j` positions and
the roots `β_j = w_j αᵢⱼ = (-1)^{ε_j} w_{j-1} αᵢⱼ`. These are the combinatorial data of the
torus-fixed points of a Bott–Samelson variety: the `2^r` choices `ε` index the fixed points and
`β_1, …, β_r` are the weights of the torus on the tangent space there.

## Main definitions

* `RootPairing.subwordPrefixProd ω ε j`: the Weyl group element `w_j = s_{i₁}^{ε₁} ⋯ s_{iⱼ}^{εⱼ}`.
* `RootPairing.subwordProd ω ε`: the element `w_r` of the whole word.
* `RootPairing.subwordRoot ω ε k`: the root `β = w_j αᵢⱼ` at the position `k` of the word.

## Main results

* `RootPairing.subwordRoot_eq_ite`: `β_j = (-1)^{ε_j} w_{j-1} αᵢⱼ`.
* `RootPairing.subwordProd_cons`, `RootPairing.subwordRoot_cons_zero` and
  `RootPairing.subwordRoot_cons_succ`: the recursion on the first letter of the word.

## References

* M. Demazure, *Désingularisation des variétés de Schubert généralisées*, Ann. Sci. École
  Norm. Sup. (4) 7 (1974), §2.
-/

public section

noncomputable section

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (P : RootPairing ι R M N)

/-- For a word `ω = i₁ ⋯ iᵣ` and a choice `ε ∈ {0,1}^r`, the Weyl group element
`w_j = s_{i₁}^{ε₁} ⋯ s_{iⱼ}^{εⱼ}` spelled by the letters of the first `j` positions that `ε`
selects. For `j ≥ r` it is the whole product `RootPairing.subwordProd ω ε`. -/
def subwordPrefixProd (ω : List ι) (ε : Fin ω.length → Bool) (j : ℕ) : P.weylGroup :=
  ((List.ofFn fun k ↦ if ε k then weylGroup.ofIdx P ω[k] else 1).take j).prod

/-- For a word `ω = i₁ ⋯ iᵣ` and a choice `ε ∈ {0,1}^r`, the Weyl group element
`w_r = s_{i₁}^{ε₁} ⋯ s_{iᵣ}^{εᵣ}` spelled by the subword that `ε` selects. -/
def subwordProd (ω : List ι) (ε : Fin ω.length → Bool) : P.weylGroup :=
  P.subwordPrefixProd ω ε ω.length

/-- For a word `ω = i₁ ⋯ iᵣ`, a choice `ε ∈ {0,1}^r` and a position `j`, the root
`β_j = w_j αᵢⱼ`, which is `w_{j-1} αᵢⱼ` when `ε_j = 0` and `-w_{j-1} αᵢⱼ` when `ε_j = 1`
(`RootPairing.subwordRoot_eq_ite`). At the torus-fixed point `ε` of the Bott–Samelson variety of
`ω` these are the weights of the torus on the tangent space. Positions are zero-based. -/
def subwordRoot (ω : List ι) (ε : Fin ω.length → Bool) (k : Fin ω.length) : M :=
  P.subwordPrefixProd ω ε (k + 1) • P.root ω[k]

variable {P}

@[simp]
theorem subwordPrefixProd_zero (ω : List ι) (ε : Fin ω.length → Bool) :
    P.subwordPrefixProd ω ε 0 = 1 := by
  simp [subwordPrefixProd]

/-- Past the end of the word, the prefix product is the product of the whole subword. -/
theorem subwordPrefixProd_of_length_le (ω : List ι) (ε : Fin ω.length → Bool) {j : ℕ}
    (h : ω.length ≤ j) : P.subwordPrefixProd ω ε j = P.subwordProd ω ε := by
  rw [subwordProd, subwordPrefixProd, subwordPrefixProd, List.take_of_length_le (by simpa using h),
    List.take_of_length_le (by simp)]

@[simp]
theorem subwordPrefixProd_cons_succ (i : ι) (ω : List ι) (e : Bool) (ε : Fin ω.length → Bool)
    (j : ℕ) :
    P.subwordPrefixProd (i :: ω) (Fin.cons e ε) (j + 1) =
      (if e then weylGroup.ofIdx P i else 1) * P.subwordPrefixProd ω ε j := by
  simp [subwordPrefixProd, List.ofFn_succ]

/-- Each prefix product extends the previous one by one factor. -/
theorem subwordPrefixProd_succ (ω : List ι) (ε : Fin ω.length → Bool) (k : Fin ω.length) :
    P.subwordPrefixProd ω ε (k + 1) =
      P.subwordPrefixProd ω ε k * if ε k then weylGroup.ofIdx P ω[k] else 1 := by
  rw [subwordPrefixProd, subwordPrefixProd, List.take_add_one, List.prod_append,
    List.getElem?_ofFn]
  simp

@[simp]
theorem subwordProd_nil (ε : Fin [].length → Bool) : P.subwordProd ([] : List ι) ε = 1 :=
  P.subwordPrefixProd_zero [] ε

@[simp]
theorem subwordProd_cons (i : ι) (ω : List ι) (e : Bool) (ε : Fin ω.length → Bool) :
    P.subwordProd (i :: ω) (Fin.cons e ε) =
      (if e then weylGroup.ofIdx P i else 1) * P.subwordProd ω ε :=
  subwordPrefixProd_cons_succ i ω e ε ω.length

/-- **The roots of a subword**: `β_j = (-1)^{ε_j} w_{j-1} αᵢⱼ`. -/
theorem subwordRoot_eq_ite (ω : List ι) (ε : Fin ω.length → Bool) (k : Fin ω.length) :
    P.subwordRoot ω ε k =
      if ε k then -(P.subwordPrefixProd ω ε k • P.root ω[k])
      else P.subwordPrefixProd ω ε k • P.root ω[k] := by
  rw [subwordRoot, subwordPrefixProd_succ, mul_smul]
  split_ifs <;> simp

@[simp]
theorem subwordRoot_cons_zero (i : ι) (ω : List ι) (e : Bool) (ε : Fin ω.length → Bool) :
    P.subwordRoot (i :: ω) (Fin.cons e ε) 0 = if e then -P.root i else P.root i := by
  rw [subwordRoot_eq_ite]
  simp

@[simp]
theorem subwordRoot_cons_succ (i : ι) (ω : List ι) (e : Bool) (ε : Fin ω.length → Bool)
    (k : Fin ω.length) :
    P.subwordRoot (i :: ω) (Fin.cons e ε) k.succ =
      (if e then weylGroup.ofIdx P i else 1) • P.subwordRoot ω ε k := by
  simp [subwordRoot, subwordPrefixProd_cons_succ, mul_smul]

end RootPairing
