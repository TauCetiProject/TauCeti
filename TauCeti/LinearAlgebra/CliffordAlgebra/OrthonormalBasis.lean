/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
-- Private: the ordered-product and square formulas are used only inside proofs.
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthogonalBasis
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement

/-!
# Orthonormal bases in the Clifford algebra of minus the squared norm

Let `V` be a real inner product space and `Q` a quadratic form on `V` with `Q v = -‖v‖²`, the sign
convention under which the Clifford relation reads `c(v) c(w) + c(w) c(v) = -2 ⟪v, w⟫`. Then
orthogonality for `Q` is orthogonality for the inner product, so an orthonormal basis `e` of `V` is
an orthogonal basis for `Q` with `Q (eᵢ) = -1`. The general orthogonal-basis results of
`TauCeti.LinearAlgebra.CliffordAlgebra.OrthogonalBasis` therefore apply to `e`, and the Clifford
basis vector `e_s` indexed by a finite set `s` of indices squares to the sign
`(-1) ^ ((|s| + 1).choose 2)`.

## Main results

* `QuadraticMap.isOrtho_iff_inner_eq_zero`: orthogonality for `Q` is orthogonality for the inner
  product.
* `OrthonormalBasis.isOrthoᵢ_associated`: an orthonormal basis is orthogonal for the polar form
  of `Q`.
* `OrthonormalBasis.pairwise_isOrtho_map`: distinct orthonormal basis vectors are pairwise
  orthogonal for `Q`.
* `OrthonormalBasis.prod_map_map_eq_neg_one_pow`: `Q` takes the value `-1` on orthonormal basis
  vectors.
* `CliffordAlgebra.basis_mul_self_of_orthonormal`: `e_s * e_s = (-1) ^ ((|s| + 1).choose 2)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §1.
-/

public section

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Q : QuadraticForm ℝ V}
  (hQ : ∀ v, Q v = -‖v‖ ^ 2)
include hQ

/-- For `Q v = -‖v‖²`, orthogonality for `Q` is orthogonality for the inner product. -/
theorem QuadraticMap.isOrtho_iff_inner_eq_zero {x y : V} : Q.IsOrtho x y ↔ ⟪x, y⟫ = 0 := by
  rw [QuadraticMap.isOrtho_def, hQ, hQ, hQ, norm_add_sq_real]
  constructor <;> intro h <;> linarith

namespace OrthonormalBasis

variable {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)

/-- For `Q v = -‖v‖²`, an orthonormal basis is orthogonal for the polar form of `Q`. -/
theorem isOrthoᵢ_associated : (QuadraticMap.associated Q).IsOrthoᵢ b.toBasis :=
  fun _ _ hij ↦ QuadraticMap.associated_isOrtho.2
    ((QuadraticMap.isOrtho_iff_inner_eq_zero hQ).2 (by simpa using b.orthonormal.2 hij))

/-- For `Q v = -‖v‖²`, the members of a list of distinct orthonormal basis vectors are pairwise
orthogonal for `Q`. -/
theorem pairwise_isOrtho_map {l : List ι} (hl : l.Nodup) : (l.map b).Pairwise Q.IsOrtho :=
  List.pairwise_map.mpr <| hl.imp fun hij ↦
    (QuadraticMap.isOrtho_iff_inner_eq_zero hQ).2 (b.orthonormal.2 hij)

/-- For `Q v = -‖v‖²`, `Q` takes the value `-1` at every member of a list of orthonormal basis
vectors. -/
theorem prod_map_map_eq_neg_one_pow (l : List ι) : ((l.map b).map Q).prod = (-1) ^ l.length := by
  refine (List.prod_eq_pow_length _ (-1) fun x hx ↦ ?_).trans (by simp)
  simp only [List.map_map, List.mem_map, Function.comp_apply] at hx
  obtain ⟨i, -, rfl⟩ := hx
  simp [hQ, b.orthonormal.1 i]

end OrthonormalBasis

namespace CliffordAlgebra

/-- **The square of a Clifford basis vector of an orthonormal basis**: for `Q v = -‖v‖²`, the
ordered product `e_s` of the generators indexed by `s` satisfies
`e_s * e_s = (-1) ^ ((|s| + 1).choose 2)`. Reordering contributes `(-1) ^ (|s|.choose 2)` and
each generator squares to `-1`. -/
theorem basis_mul_self_of_orthonormal {ι : Type*} [Fintype ι] [LinearOrder ι]
    (b : OrthonormalBasis ι ℝ V) (s : Finset ι) :
    basis Q b.toBasis s * basis Q b.toBasis s = (-1) ^ (s.card + 1).choose 2 := by
  rw [basis_eq_prod_map_sort (b.isOrthoᵢ_associated hQ), OrthonormalBasis.coe_toBasis,
    prod_map_ι_sq_scalar (b.pairwise_isOrtho_map hQ (s.sort_nodup _)),
    b.prod_map_map_eq_neg_one_pow hQ, ← pow_add]
  simp [Nat.choose_succ_succ', add_comm]

end CliffordAlgebra
