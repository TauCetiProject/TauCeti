/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
-- Private: the ordered-product, square and even-relation formulas are used only inside proofs.
import TauCeti.LinearAlgebra.CliffordAlgebra.Even.Conjugation
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthogonalBasis
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Basic

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
* `OrthonormalBasis.isOrtho_apply`, `OrthonormalBasis.pairwise_isOrtho_map`: distinct orthonormal
  basis vectors are pairwise orthogonal for `Q`.
* `OrthonormalBasis.map_apply_mul_map_apply`: `Q (bᵢ) Q (bⱼ) = 1` for orthonormal basis vectors.
* `OrthonormalBasis.prod_map_map_eq_neg_one_pow`: `Q` takes the value `-1` on orthonormal basis
  vectors.
* `OrthonormalBasis.ι_apply_ι_apply_comm`, `OrthonormalBasis.ι_apply_ι_apply_self`: in every
  representation of the Clifford algebra, `c(bᵢ) c(bⱼ) = -c(bⱼ) c(bᵢ)` for `i ≠ j` and
  `c(bᵢ) c(bᵢ) = -1`.
* `OrthonormalBasis.ι_apply_eq_sum`: `c(v) = ∑ᵢ ⟪bᵢ, v⟫ c(bᵢ)` in every representation.
* `CliffordAlgebra.even_ι_bilin_add_swap_eq_neg_two_inner`: in the even subalgebra,
  `c(u) c(v) + c(v) c(u) = -2 ⟪u, v⟫`.
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

/-- For `Q v = -‖v‖²`, distinct orthonormal basis vectors are orthogonal for `Q`. -/
theorem isOrtho_apply {i j : ι} (hij : i ≠ j) : Q.IsOrtho (b i) (b j) :=
  (QuadraticMap.isOrtho_iff_inner_eq_zero hQ).2 (b.orthonormal.2 hij)

/-- For `Q v = -‖v‖²`, the members of a list of distinct orthonormal basis vectors are pairwise
orthogonal for `Q`. -/
theorem pairwise_isOrtho_map {l : List ι} (hl : l.Nodup) : (l.map b).Pairwise Q.IsOrtho :=
  List.pairwise_map.mpr <| hl.imp (b.isOrtho_apply hQ)

/-- For `Q v = -‖v‖²`, the product of the values of `Q` at two orthonormal basis vectors is one. -/
theorem map_apply_mul_map_apply (i j : ι) : Q (b i) * Q (b j) = 1 := by
  simp [hQ, b.orthonormal.1 i, b.orthonormal.1 j]

/-- For `Q v = -‖v‖²`, `Q` takes the value `-1` at every member of a list of orthonormal basis
vectors. -/
theorem prod_map_map_eq_neg_one_pow (l : List ι) : ((l.map b).map Q).prod = (-1) ^ l.length := by
  refine (List.prod_eq_pow_length _ (-1) fun x hx ↦ ?_).trans (by simp)
  simp only [List.map_map, List.mem_map, Function.comp_apply] at hx
  obtain ⟨i, -, rfl⟩ := hx
  simp [hQ, b.orthonormal.1 i]

section Representation

variable {S M : Type*} [Semiring S] [Algebra ℝ S] [AddCommGroup M] [Module S M] [Module ℝ M]
  [IsScalarTower ℝ S M] (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End S M)

/-- For `Q v = -‖v‖²`, Clifford multiplications by distinct orthonormal basis vectors anticommute
in every representation of the Clifford algebra: `c(bᵢ) c(bⱼ) y = -c(bⱼ) c(bᵢ) y`. -/
theorem ι_apply_ι_apply_comm {i j : ι} (hij : i ≠ j) (y : M) :
    ρ (CliffordAlgebra.ι Q (b i)) (ρ (CliffordAlgebra.ι Q (b j)) y) =
      -ρ (CliffordAlgebra.ι Q (b j)) (ρ (CliffordAlgebra.ι Q (b i)) y) := by
  rw [← mul_apply_eq_comp, ← map_mul,
    CliffordAlgebra.ι_mul_ι_comm_of_isOrtho (b.isOrtho_apply hQ hij), map_neg, map_mul,
    LinearMap.neg_apply, mul_apply_eq_comp]

/-- For `Q v = -‖v‖²`, Clifford multiplication by an orthonormal basis vector squares to `-1` in
every representation of the Clifford algebra: `c(bᵢ) c(bᵢ) y = -y`. -/
theorem ι_apply_ι_apply_self (i : ι) (y : M) :
    ρ (CliffordAlgebra.ι Q (b i)) (ρ (CliffordAlgebra.ι Q (b i)) y) = -y := by
  rw [← mul_apply_eq_comp, ← map_mul, CliffordAlgebra.ι_sq_scalar, AlgHom.commutes,
    Module.algebraMap_end_apply, hQ, b.orthonormal.1 i]
  simp

omit hQ in
/-- Clifford multiplication expanded in an orthonormal basis, in every representation of the
Clifford algebra: `c(v) y = ∑ᵢ ⟪bᵢ, v⟫ c(bᵢ) y`. -/
theorem ι_apply_eq_sum (v : V) (y : M) :
    ρ (CliffordAlgebra.ι Q v) y = ∑ i, ⟪b i, v⟫ • ρ (CliffordAlgebra.ι Q (b i)) y := by
  conv_lhs => rw [← b.sum_repr' v]
  simp [map_sum, map_smul, LinearMap.sum_apply]

end Representation

end OrthonormalBasis

namespace CliffordAlgebra

/-- For `Q v = -‖v‖²`, the even Clifford relation is `c(u) c(v) + c(v) c(u) = -2 ⟪u, v⟫`. -/
theorem even_ι_bilin_add_swap_eq_neg_two_inner (u v : V) :
    (even.ι Q).bilin u v + (even.ι Q).bilin v u = algebraMap ℝ (even Q) (-2 * ⟪u, v⟫) := by
  rw [even_ι_bilin_add_swap]
  congr 1
  simp only [QuadraticMap.polar, hQ, norm_add_sq_real]
  ring

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
