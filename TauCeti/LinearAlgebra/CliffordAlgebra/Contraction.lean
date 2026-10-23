/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
-- Private: `CliffordAlgebra.exists_algebraMap_of_mem_range_ι_pow_zero` and
-- `CliffordAlgebra.exists_ι_of_mem_range_ι_pow_one` are used only inside a proof.
import TauCeti.LinearAlgebra.CliffordAlgebra.Grading

/-!
# Contraction against the `ℤ/2`-grading, and the change of form on right factors

Mathlib's `CliffordAlgebra.contractLeft` lowers the degree of a multivector by one, so it
exchanges the two halves of the `ℤ/2`-grading. Mathlib records neither half of that sentence:
`involute` interacts with products (`involute` is an algebra homomorphism) and with the grading,
but never with a contraction, and `evenOdd` is never related to `contractLeft` at all.

This file proves both. That a contraction carries `evenOdd Q i` into `evenOdd Q (i + 1)` is the
grading statement itself, and it is what makes an annihilation operator odd; anticommutation with
the grade involution is its operator shadow, and is what makes the grade involution usable as an
*even* operator alongside exterior multiplication and contraction — for instance because an
anisotropic vector orthogonal to a polarization acts on a spinor module by its scalar coordinate
times the grade involution. More precisely, contraction is a derivation twisted by the grade
involution, `d ⌋ (x * y) = (d ⌋ x) * y + involute x * (d ⌋ y)`, the graded Leibniz rule of an odd
operator.

The degree bookkeeping is in `ZMod 2`, where lowering and raising the degree by one are the same
map, so `evenOdd Q (i + 1)` and `evenOdd Q (i - 1)` are the same submodule; the statement below
names the first.

The parity statement is proved by induction over the grading; its base case is read off by
`CliffordAlgebra.exists_algebraMap_of_mem_range_ι_pow_zero` and
`CliffordAlgebra.exists_ι_of_mem_range_ι_pow_one`, which are general facts about the
grading and live with it.

Mathlib's `CliffordAlgebra.changeForm` is built by folding from the left, so Mathlib describes
it on left factors only (`CliffordAlgebra.changeForm_ι_mul`). The second half of this file supplies
the right-handed description `CliffordAlgebra.changeForm_mul_ι`, which rests on the graded
Leibniz rules for a contraction meeting a vector factor on the far side and on the commutation of
left with right contraction, left as a `TODO` in Mathlib. From it, `changeForm` commutes with
reversion when the bilinear form is symmetric; and since contraction anticommutes with the grade
involution, `changeForm` commutes with the grade involution for every bilinear form. In particular
`CliffordAlgebra.equivExterior` intertwines both operations with those of the exterior algebra.

## Main results

* `CliffordAlgebra.contractLeft_map`: contraction is natural under quadratic isometries.

* `CliffordAlgebra.contractLeft_mem_evenOdd`: **contraction shifts the parity**.
* `CliffordAlgebra.involute_contractLeft`: `involute (d ⌋ x) = -(d ⌋ involute x)`.
* `CliffordAlgebra.contractLeft_mul`: the graded Leibniz rule
  `d ⌋ (x * y) = (d ⌋ x) * y + involute x * (d ⌋ y)`.
* `CliffordAlgebra.contractLeft_mul_ι` and `CliffordAlgebra.contractRight_ι_mul`: the graded
  Leibniz rules for a vector factor on the far side.
* `CliffordAlgebra.contractRight_contractLeft`: `(d ⌋ x) ⌊ d' = d ⌋ (x ⌊ d')`.
* `CliffordAlgebra.contractLeft_prod_map_ι_eq_zero`: a contraction kills a product of vectors in
  its kernel.
* `CliffordAlgebra.changeForm_mul_ι`: `changeForm` on a right vector factor.
* `CliffordAlgebra.changeForm_involute` and `CliffordAlgebra.changeForm_reverse`: `changeForm`
  commutes with the grade involution, and with reversion for a symmetric form.
* `CliffordAlgebra.equivExterior_involute` and `CliffordAlgebra.equivExterior_reverse`: the same
  for the isomorphism with the exterior algebra.
* `CliffordAlgebra.equivExterior_ι_mul` and `CliffordAlgebra.equivExterior_mul_ι`: that
  isomorphism on left and right vector factors.
* `CliffordAlgebra.equivExterior_prod_map_ι_of_pairwise_isOrtho`: that isomorphism sends a product
  of pairwise orthogonal vectors to their exterior product.

## References

* [D. Grinberg, *The Clifford algebra and the Chevalley map*][grinberg_clifford_2016], for the
  contraction operators themselves.
-/

public section


universe u v w

namespace CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  {Q : QuadraticForm R M}

section Naturality

variable {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
  {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}

/-- Contraction against a linear functional commutes with the algebra map induced by a
quadratic isometry, after pulling back the functional. -/
theorem contractLeft_map (f : Q₁ →qᵢ Q₂) (d : Module.Dual R M₂)
    (x : CliffordAlgebra Q₁) :
    contractLeft d (map f x) = map f (contractLeft (d ∘ₗ f.toLinearMap) x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp only [AlgHom.commutes, contractLeft_algebraMap, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x m hx =>
    simp only [map_mul, map_apply_ι, contractLeft_ι_mul, hx, map_sub,
      map_smul, LinearMap.comp_apply, QuadraticMap.Isometry.coe_toLinearMap]

end Naturality

/-- **The grade involution anticommutes with contraction.** Contracting against a linear
functional lowers the degree by one, hence swaps the even and odd parts of the Clifford algebra,
so it anticommutes with the operator that is `+1` on the even part and `-1` on the odd part. -/
@[simp, grind =]
theorem involute_contractLeft (d : Module.Dual R M) (x : CliffordAlgebra Q) :
    involute (contractLeft d x) = -contractLeft d (involute x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy, neg_add]
  | ι_mul x a hx =>
    have hlhs : involute (contractLeft d (ι Q a * x))
        = d a • involute x - ι Q a * contractLeft d (involute x) := by
      rw [contractLeft_ι_mul, map_sub, map_smul, map_mul, involute_ι, hx, neg_mul_neg]
    have hrhs : involute (ι Q a * x) = -(ι Q a * involute x) := by
      rw [map_mul, involute_ι, neg_mul]
    rw [hlhs, hrhs, map_neg, neg_neg, contractLeft_ι_mul]

/-- **Contraction shifts the parity.** Contracting against a linear functional lowers the degree
of a multivector by one, so it carries the `i`-th half of the `ℤ/2`-grading into the other one. -/
theorem contractLeft_mem_evenOdd (d : Module.Dual R M) {i : ZMod 2} {x : CliffordAlgebra Q}
    (hx : x ∈ evenOdd Q i) : contractLeft d x ∈ evenOdd Q (i + 1) := by
  -- Two parity facts, used to keep the indices in `ZMod 2` honest.
  have hone : (1 : ZMod 2) + 1 = 0 := by decide
  have hshift : ∀ c : ZMod 2, (1 : ZMod 2) + (c + 1) = c := by decide
  induction x, hx using CliffordAlgebra.evenOdd_induction with
  | range_ι_pow v hv =>
    -- `i.val` is `0` or `1`, so `v` is a scalar or a vector.
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) i with rfl | rfl
    · obtain ⟨r, rfl⟩ := exists_algebraMap_of_mem_range_ι_pow_zero hv
      simp
    · obtain ⟨a, rfl⟩ := exists_ι_of_mem_range_ι_pow_one hv
      rw [contractLeft_ι, hone]
      exact SetLike.algebraMap_mem_graded _ _
  | add x y hx hy ihx ihy => simpa only [map_add] using add_mem ihx ihy
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    have h₂ : ι Q m₂ * x ∈ evenOdd Q (i + 1) := by
      rw [add_comm]
      exact SetLike.mul_mem_graded (ι_mem_evenOdd_one Q m₂) hx
    have h₁ : contractLeft d (ι Q m₂ * x) ∈ evenOdd Q i := by
      rw [contractLeft_ι_mul]
      refine sub_mem (Submodule.smul_mem _ _ hx) ?_
      simpa only [hshift] using SetLike.mul_mem_graded (ι_mem_evenOdd_one Q m₂) ih
    rw [mul_assoc, contractLeft_ι_mul]
    refine sub_mem (Submodule.smul_mem _ _ h₂) ?_
    rw [add_comm]
    exact SetLike.mul_mem_graded (ι_mem_evenOdd_one Q m₁) h₁

/-- **The graded Leibniz rule for contraction.** Contraction against `d` is a derivation twisted
by the grade involution: `d ⌋ (x * y) = (d ⌋ x) * y + involute x * (d ⌋ y)`.  On a homogeneous
multivector `x` of degree `n` the involution is the sign `(-1) ^ n`, which gives the familiar
odd-derivation rule. -/
theorem contractLeft_mul (d : Module.Dual R M) (x y : CliffordAlgebra Q) :
    contractLeft d (x * y) = contractLeft d x * y + involute x * contractLeft d y := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [contractLeft_algebraMap_mul, contractLeft_algebraMap, zero_mul, zero_add,
      AlgHom.commutes]
  | add x x' hx hx' => simp only [add_mul, map_add, hx, hx']; abel
  | ι_mul x a hx =>
    rw [mul_assoc, contractLeft_ι_mul, hx, contractLeft_ι_mul, map_mul, involute_ι]
    simp only [mul_add, sub_mul, smul_mul_assoc, neg_mul, mul_assoc]
    abel

/-- **The graded Leibniz rule for a right vector factor.** Contraction against `d` passes through
a right factor `ι Q m`, at the cost of the term `d m • involute x` produced by contracting that
factor itself after it has moved past `x`. -/
theorem contractLeft_mul_ι (d : Module.Dual R M) (x : CliffordAlgebra Q) (m : M) :
    contractLeft d (x * ι Q m) = contractLeft d x * ι Q m + d m • involute x := by
  rw [contractLeft_mul, contractLeft_ι, ← Algebra.commutes, ← Algebra.smul_def]

/-- **The graded Leibniz rule for right contraction and a left vector factor**, the mirror image of
`CliffordAlgebra.contractLeft_mul_ι` under reversion: `(ι Q a * x) ⌊ d` is
`ι Q a * (x ⌊ d) + d a • involute x`. -/
theorem contractRight_ι_mul (d : Module.Dual R M) (a : M) (x : CliffordAlgebra Q) :
    contractRight (ι Q a * x) d = ι Q a * contractRight x d + d a • involute x := by
  simp [contractRight_eq, contractLeft_mul_ι, reverse_involute_commute.eq]

/-- **Left and right contraction commute**: `(d ⌋ x) ⌊ d' = d ⌋ (x ⌊ d')`. This is the statement
left as a `TODO` after `CliffordAlgebra.contractRight_comm` in Mathlib. -/
theorem contractRight_contractLeft (d d' : Module.Dual R M) (x : CliffordAlgebra Q) :
    contractRight (contractLeft d x) d' = contractLeft d (contractRight x d') := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | ι_mul x a hx =>
    simp [contractLeft_ι_mul, contractRight_ι_mul, hx, involute_contractLeft]
    abel

/-- Contraction against a functional `d` kills a product of vectors that `d` annihilates. -/
theorem contractLeft_prod_map_ι_eq_zero (d : Module.Dual R M) {l : List M}
    (h : ∀ m ∈ l, d m = 0) : contractLeft d (l.map (ι Q)).prod = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, contractLeft_ι_mul, h a List.mem_cons_self, zero_smul,
      ih fun m hm ↦ h m (List.mem_cons_of_mem a hm), mul_zero, sub_zero]

section changeForm

variable {Q' : QuadraticForm R M} {B : LinearMap.BilinForm R M}
  (h : B.toQuadraticMap = Q' - Q)

/-- **`changeForm` and a right vector factor**: the right-handed counterpart of Mathlib's
`CliffordAlgebra.changeForm_ι_mul`, in which the correction term contracts from the right against
the functional `B.flip m = B · m`. No symmetry of `B` is needed. -/
theorem changeForm_mul_ι (x : CliffordAlgebra Q) (m : M) :
    changeForm h (x * ι Q m) =
      changeForm h x * ι Q' m - contractRight (changeForm h x) (B.flip m) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [Algebra.commutes, changeForm_ι_mul, changeForm_algebraMap, contractLeft_algebraMap,
      contractRight_algebraMap, sub_zero, sub_zero, Algebra.commutes]
  | add x y hx hy =>
    simp only [add_mul, map_add, hx, hy, LinearMap.add_apply]
    abel
  | ι_mul x a hx =>
    simp [mul_assoc, changeForm_ι_mul, hx, contractLeft_mul_ι, contractRight_contractLeft,
      contractRight_ι_mul, mul_sub, sub_mul]
    abel

/-- **`changeForm` commutes with the grade involution**, for every bilinear form `B`. -/
@[simp]
theorem changeForm_involute (x : CliffordAlgebra Q) :
    changeForm h (involute x) = involute (changeForm h x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x a hx =>
    simp [changeForm_ι_mul, hx, involute_contractLeft]
    abel

/-- **`changeForm` commutes with reversion** when the bilinear form `B` is symmetric. This covers
`CliffordAlgebra.equivExterior`, whose bilinear form is the symmetric
`QuadraticMap.associated (-Q)`. -/
theorem changeForm_reverse (hB : B.IsSymm) (x : CliffordAlgebra Q) :
    changeForm h (reverse x) = reverse (changeForm h x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x a hx =>
    simp [changeForm_mul_ι, hx, changeForm_ι_mul, contractRight_eq,
      ← LinearMap.isSymm_iff_eq_flip.mp hB]

end changeForm

section equivExterior

variable [Invertible (2 : R)] (Q)

/-- `CliffordAlgebra.equivExterior` on a left vector factor: the specialization of Mathlib's
`CliffordAlgebra.changeForm_ι_mul` to the bilinear form `QuadraticMap.associated (-Q)`.

Not a `simp` lemma, for the same reason as `CliffordAlgebra.equivExterior_involute`. -/
theorem equivExterior_ι_mul (m : M) (x : CliffordAlgebra Q) :
    equivExterior Q (ι Q m * x) =
      ExteriorAlgebra.ι R m * equivExterior Q x -
        contractLeft (QuadraticMap.associated (-Q) m) (equivExterior Q x) :=
  changeForm_ι_mul changeForm.associated_neg_proof m x

/-- `CliffordAlgebra.equivExterior` on a right vector factor: the specialization of
`CliffordAlgebra.changeForm_mul_ι` to the symmetric bilinear form `QuadraticMap.associated (-Q)`.

Not a `simp` lemma, for the same reason as `CliffordAlgebra.equivExterior_involute`. -/
theorem equivExterior_mul_ι (x : CliffordAlgebra Q) (m : M) :
    equivExterior Q (x * ι Q m) =
      equivExterior Q x * ExteriorAlgebra.ι R m -
        contractRight (equivExterior Q x) (QuadraticMap.associated (-Q) m) := by
  rw [← QuadraticMap.associated_flip]
  exact changeForm_mul_ι changeForm.associated_neg_proof x m

/-- `CliffordAlgebra.equivExterior` intertwines the grade involutions.

Not a `simp` lemma: `simp` unfolds `CliffordAlgebra.equivExterior` to the underlying
`CliffordAlgebra.changeForm`, where `CliffordAlgebra.changeForm_involute` applies. -/
theorem equivExterior_involute (x : CliffordAlgebra Q) :
    equivExterior Q (involute x) = involute (equivExterior Q x) :=
  changeForm_involute changeForm.associated_neg_proof x

/-- `CliffordAlgebra.equivExterior` intertwines reversion, because the bilinear form
`QuadraticMap.associated (-Q)` it changes the form by is symmetric.

Not a `simp` lemma, for the same reason as `CliffordAlgebra.equivExterior_involute`. -/
theorem equivExterior_reverse (x : CliffordAlgebra Q) :
    equivExterior Q (reverse x) = reverse (equivExterior Q x) :=
  changeForm_reverse changeForm.associated_neg_proof (QuadraticForm.associated_isSymm R (-Q)) x

/-- **`CliffordAlgebra.equivExterior` sends a product of pairwise orthogonal vectors to their
exterior product.** Each correction term of `CliffordAlgebra.equivExterior_ι_mul` contracts the
later factors against the first, and vanishes by orthogonality. No hypothesis on `Q` is needed;
in particular `Q` may be degenerate. -/
theorem equivExterior_prod_map_ι_of_pairwise_isOrtho {l : List M} (hl : l.Pairwise Q.IsOrtho) :
    equivExterior Q (l.map (ι Q)).prod = (l.map (ExteriorAlgebra.ι R)).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.pairwise_cons] at hl
    rw [List.map_cons, List.prod_cons, equivExterior_ι_mul, ih hl.2,
      contractLeft_prod_map_ι_eq_zero, sub_zero, List.map_cons, List.prod_cons]
    intro m hm
    simp [hl.1 m hm]

end equivExterior

end CliffordAlgebra
