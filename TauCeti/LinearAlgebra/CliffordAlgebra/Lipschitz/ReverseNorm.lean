/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.Norm
public import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Basic

/-!
# The reverse norm of the Lipschitz group

A Clifford algebra carries two anti-involutions that fix the scalars: the reversion `reverse`,
which fixes every vector, and Mathlib's `star = reverse ∘ involute`, which negates every vector.
Each gives a norm on the Lipschitz group. The `star` norm `lipschitzNorm` takes the value `-Q v`
on a vector `v`. This file develops the `reverse` norm `x ↦ reverse x * x`, which takes the
value `Q v` on the nose, so a spinor norm defined through it sends the reflection in `v` to the
square class of `Q v` rather than of `-Q v`.

The two norms agree on even elements and differ by the sign `(-1) ^ r` on a product of `r`
vectors. Since the square class of `-1` is in general nontrivial, they genuinely differ on odd
Lipschitz elements. Mathlib's Pin and Spin groups are cut out by the `star` norm. On the even
part the two norms agree, so the Spin group is exactly the set of even Lipschitz elements of
reverse norm one.

## Main results

* `CliffordAlgebra.reverse_prod_map_ι_mul_prod_map_ι`: the reverse norm of a product of vectors
  is the product of their quadratic norms.
* `CliffordAlgebra.star_mul_self_eq_reverse_mul_self_of_mem_even` and
  `CliffordAlgebra.star_mul_self_eq_neg_one_pow_smul_reverse_mul_self`: the two norms agree on
  even elements and differ by `(-1) ^ r` on a product of `r` vectors.
* `CliffordAlgebra.cliffordNorm`: the unit-valued reverse norm on the Lipschitz group, with its
  defining equation `CliffordAlgebra.reverse_mul_self_eq_algebraMap_cliffordNorm`.
* `CliffordAlgebra.cliffordNorm_unitι`: a vector `v` with unit `Q v` has reverse norm `Q v`.
* `CliffordAlgebra.cliffordNorm_eq_sq_mul_of_coe_eq_algebraMap_mul`: rescaling by a scalar unit
  `c` multiplies the reverse norm by `c ^ 2`.
* `CliffordAlgebra.lipschitzNorm_eq_cliffordNorm_of_mem_even` and
  `CliffordAlgebra.lipschitzNorm_eq_neg_cliffordNorm_of_mem_odd`: the comparison with the
  `star` norm on the Lipschitz group.
* `CliffordAlgebra.mem_spinGroup_iff_cliffordNorm_eq_one`: the Spin group consists of the even
  Lipschitz elements of reverse norm one.

## References

See H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2, and
T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter V §3.
-/

public section

namespace CliffordAlgebra

universe u v

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  {Q : QuadraticForm R M}

/-! ### The reverse norm on the Lipschitz group -/

variable [Invertible (2 : R)]

private theorem exists_reverse_mul_self_eq_algebraMap (x : (CliffordAlgebra Q)ˣ)
    (hx : x ∈ lipschitzGroup Q) :
    ∃ r : Rˣ, reverse (x : CliffordAlgebra Q) * x = algebraMap R (CliffordAlgebra Q) r := by
  induction hx using Subgroup.closure_induction with
  | mem x hgen =>
      obtain ⟨v, hv⟩ := hgen
      let _ := x.invertible
      let _ : Invertible (ι Q v) := by rw [hv]; infer_instance
      let _ : Invertible (Q v) := invertibleOfInvertibleι Q v
      refine ⟨unitOfInvertible (Q v), ?_⟩
      rw [← hv, reverse_ι, ι_sq_scalar, val_unitOfInvertible]
  | inv x hx ih =>
      obtain ⟨r, hr⟩ := ih
      exact ⟨r⁻¹, reverse_inv_mul_inv hr⟩
  | one =>
      exact ⟨1, by simp⟩
  | mul x y hx hy ihx ihy =>
      obtain ⟨r, hr⟩ := ihx
      obtain ⟨s, hs⟩ := ihy
      refine ⟨r * s, ?_⟩
      rw [Units.val_mul, reverse_mul_mul_self_mul hr, hs, Units.val_mul, map_mul]

private noncomputable def cliffordNormUnit (Q : QuadraticForm R M) (x : lipschitzGroup Q) : Rˣ :=
  Classical.choose (exists_reverse_mul_self_eq_algebraMap (x : (CliffordAlgebra Q)ˣ) x.2)

private theorem reverse_mul_self_eq_cliffordNormUnit (x : lipschitzGroup Q) :
    reverse ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
        ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      algebraMap R (CliffordAlgebra Q) (cliffordNormUnit Q x : R) :=
  Classical.choose_spec (exists_reverse_mul_self_eq_algebraMap (x : (CliffordAlgebra Q)ˣ) x.2)

variable (Q) in
/-- The **Clifford norm** `x ↦ reverse x * x` on the Lipschitz group, as a unit-valued
homomorphism. It takes the value `Q v` when `Q v` is a unit (`cliffordNorm_unitι`). It
agrees with the `star` norm `lipschitzNorm` on even elements and is its negative on odd ones. -/
noncomputable def cliffordNorm : lipschitzGroup Q →* Rˣ where
  toFun := cliffordNormUnit Q
  map_one' := by
    apply Units.ext
    apply algebraMap_injective Q
    rw [← reverse_mul_self_eq_cliffordNormUnit]
    simp
  map_mul' x y := by
    apply Units.ext
    apply algebraMap_injective Q
    rw [Units.val_mul, map_mul, ← reverse_mul_self_eq_cliffordNormUnit (x * y),
      ← reverse_mul_self_eq_cliffordNormUnit y]
    simp only [Subgroup.coe_mul, Units.val_mul]
    exact reverse_mul_mul_self_mul (reverse_mul_self_eq_cliffordNormUnit x)

/-- The defining equation of the Clifford norm: `reverse x * x` is the scalar `cliffordNorm Q x`. -/
@[simp]
theorem reverse_mul_self_eq_algebraMap_cliffordNorm (x : lipschitzGroup Q) :
    reverse ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
        ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      algebraMap R (CliffordAlgebra Q) (cliffordNorm Q x : R) :=
  reverse_mul_self_eq_cliffordNormUnit x

/-- The Clifford norm is also the scalar `x * reverse x`. -/
@[simp]
theorem self_mul_reverse_eq_algebraMap_cliffordNorm (x : lipschitzGroup Q) :
    ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
        reverse ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      algebraMap R (CliffordAlgebra Q) (cliffordNorm Q x : R) :=
  self_mul_reverse_of_reverse_mul_self (reverse_mul_self_eq_algebraMap_cliffordNorm x)

/-- A vector `v` with unit `Q v` has Clifford norm `Q v`, with no sign. -/
@[simp]
theorem cliffordNorm_unitι (v : M) [Invertible (Q v)] :
    cliffordNorm Q ⟨unitι Q v, unitι_mem_lipschitzGroup v⟩ = unitOfInvertible (Q v) := by
  apply Units.ext
  apply algebraMap_injective Q
  rw [← reverse_mul_self_eq_algebraMap_cliffordNorm, coe_unitι, reverse_ι, ι_sq_scalar,
    val_unitOfInvertible]

/-- Rescaling a Lipschitz element by a scalar unit `c` multiplies its Clifford norm by `c ^ 2`. -/
theorem cliffordNorm_eq_sq_mul_of_coe_eq_algebraMap_mul {x y : lipschitzGroup Q} {c : Rˣ}
    (h : ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      algebraMap R (CliffordAlgebra Q) c * ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) :
    cliffordNorm Q y = c ^ 2 * cliffordNorm Q x := by
  apply Units.ext
  apply algebraMap_injective Q
  have hc : reverse (algebraMap R (CliffordAlgebra Q) c) * algebraMap R (CliffordAlgebra Q) c =
      algebraMap R (CliffordAlgebra Q) (c * c : R) := by
    rw [reverse.commutes, map_mul]
  rw [← reverse_mul_self_eq_algebraMap_cliffordNorm, h, reverse_mul_mul_self_mul hc,
    reverse_mul_self_eq_algebraMap_cliffordNorm, ← map_mul, Units.val_mul, Units.val_pow_eq_pow_val,
    sq]

/-! ### Comparison with the `star` norm and the Spin group -/

/-- On an even Lipschitz element, the `star` norm equals the Clifford norm. -/
theorem lipschitzNorm_eq_cliffordNorm_of_mem_even (x : lipschitzGroup Q)
    (hx : ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ evenOdd Q 0) :
    lipschitzNorm Q x = cliffordNorm Q x := by
  apply Units.ext
  apply algebraMap_injective Q
  rw [← star_mul_self_eq_algebraMap_lipschitzNorm, ← reverse_mul_self_eq_algebraMap_cliffordNorm,
    star_mul_self_eq_reverse_mul_self_of_mem_even hx]

/-- On an odd Lipschitz element, the `star` norm is the negative of the Clifford norm. -/
theorem lipschitzNorm_eq_neg_cliffordNorm_of_mem_odd (x : lipschitzGroup Q)
    (hx : ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ evenOdd Q 1) :
    lipschitzNorm Q x = -cliffordNorm Q x := by
  apply Units.ext
  apply algebraMap_injective Q
  rw [← star_mul_self_eq_algebraMap_lipschitzNorm, Units.val_neg, map_neg,
    ← reverse_mul_self_eq_algebraMap_cliffordNorm,
    star_mul_self_eq_neg_reverse_mul_self_of_mem_odd hx]

/-- **Mathlib's Spin group, read through the Clifford norm.** A Lipschitz element lies in
`spinGroup Q` exactly when it is even and its Clifford norm `reverse x * x` is one. -/
@[simp]
theorem mem_spinGroup_iff_cliffordNorm_eq_one (x : lipschitzGroup Q) :
    ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ spinGroup Q ↔
      ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ evenOdd Q 0 ∧ cliffordNorm Q x = 1 := by
  rw [spinGroup.mem_iff, mem_pinGroup_iff_lipschitzNorm_eq_one, ← even_toSubmodule,
    Subalgebra.mem_toSubmodule, and_comm]
  exact and_congr_right fun hx => by rw [lipschitzNorm_eq_cliffordNorm_of_mem_even x hx]

/-- A Spin element has Clifford norm one. -/
@[simp]
theorem cliffordNorm_pinToLipschitz_spinToPin (x : spinGroup Q) :
    cliffordNorm Q (pinToLipschitz Q (spinToPin Q x)) = 1 := by
  refine ((mem_spinGroup_iff_cliffordNorm_eq_one _).1 ?_).2
  rw [coe_pinToLipschitz_apply, coe_spinToPin_apply]
  exact x.2

end CliffordAlgebra
