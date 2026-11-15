/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
-- Private: the ordered-product, square and even-relation formulas are used only inside proofs.
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Basic
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
`(-1) ^ ((|s| + 1).choose 2)`. Under any `ℝ`-algebra homomorphism out of `CliffordAlgebra Q`,
orthogonal vectors anticommute, unit vectors and orthonormal bivectors square to `-1`, and the
oriented bivector `c(e₁) c(e₂)` of an orthonormal pair is invariant under planar rotations.

## Main results

* `QuadraticMap.polar_eq_neg_two_inner`: `polar Q v w = -2 ⟪v, w⟫_ℝ`.
* `QuadraticMap.isOrtho_iff_inner_eq_zero`: orthogonality for `Q` is orthogonality for the inner
  product.
* `OrthonormalBasis.isOrthoᵢ_associated`: an orthonormal basis is orthogonal for the polar form
  of `Q`.
* `OrthonormalBasis.isOrtho_apply`, `OrthonormalBasis.pairwise_isOrtho_map`: distinct orthonormal
  basis vectors are pairwise orthogonal for `Q`.
* `OrthonormalBasis.map_apply_mul_map_apply`: `Q (bᵢ) Q (bⱼ) = 1` for orthonormal basis vectors.
* `OrthonormalBasis.prod_map_map_eq_neg_one_pow`: `Q` takes the value `-1` on orthonormal basis
  vectors.
* `CliffordAlgebra.ι_mul_ι_add_swap_eq_neg_two_inner`,
  `CliffordAlgebra.even_ι_bilin_add_swap_eq_neg_two_inner`: `c(u) c(v) + c(v) c(u) = -2 ⟪u, v⟫` in
  the Clifford algebra and its even subalgebra.
* `CliffordAlgebra.basis_mul_self_of_orthonormal`: `e_s * e_s = (-1) ^ ((|s| + 1).choose 2)`.
* `AlgHom.map_cliffordAlgebraι_mul_map_cliffordAlgebraι_add_swap_eq_neg_two_inner`,
  `AlgHom.map_cliffordAlgebraι_cos_smul_add_sin_smul_mul_neg_sin_smul_add_cos_smul`:
  polarized Clifford relation and 2-plane rotation invariance under an algebra homomorphism out of
  `CliffordAlgebra Q`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §1.
-/

public section

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Q : QuadraticForm ℝ V}
  (hQ : ∀ v, Q v = -‖v‖ ^ 2)
include hQ

/-- For `Q v = -‖v‖²` on a real inner product space, the polar bilinear form is `-2 ⟪v, w⟫_ℝ`. -/
theorem QuadraticMap.polar_eq_neg_two_inner (v w : V) :
    QuadraticMap.polar Q v w = -2 * ⟪v, w⟫ := by
  simp only [QuadraticMap.polar, hQ, norm_add_sq_real]
  ring

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

end OrthonormalBasis

namespace CliffordAlgebra

/-- For `Q v = -‖v‖²`, generators of `CliffordAlgebra Q` satisfy the polarized Clifford relation
`ι Q v * ι Q w + ι Q w * ι Q v = algebraMap ℝ _ (-2 * ⟪v, w⟫_ℝ)`. -/
theorem ι_mul_ι_add_swap_eq_neg_two_inner (v w : V) :
    ι Q v * ι Q w + ι Q w * ι Q v = algebraMap ℝ (CliffordAlgebra Q) (-2 * ⟪v, w⟫) := by
  rw [ι_mul_ι_add_swap, QuadraticMap.polar_eq_neg_two_inner hQ]

/-- For `Q v = -‖v‖²`, the even Clifford relation is `c(u) c(v) + c(v) c(u) = -2 ⟪u, v⟫`. -/
theorem even_ι_bilin_add_swap_eq_neg_two_inner (u v : V) :
    (even.ι Q).bilin u v + (even.ι Q).bilin v u = algebraMap ℝ (even Q) (-2 * ⟪u, v⟫) := by
  rw [even_ι_bilin_add_swap, QuadraticMap.polar_eq_neg_two_inner hQ]

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

omit hQ

namespace AlgHom

open CliffordAlgebra

section Semiring

variable {B : Type*} [Semiring B] [Algebra ℝ B] (ρ : CliffordAlgebra Q →ₐ[ℝ] B)

/-- **Polarized Clifford relation** for `Q v = -‖v‖²`:
`c(v) c(w) + c(w) c(v) = (-2 * ⟪v, w⟫_ℝ) • 1`. -/
theorem map_cliffordAlgebraι_mul_map_cliffordAlgebraι_add_swap_eq_neg_two_inner
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (v w : V) :
    ρ (ι Q v) * ρ (ι Q w) + ρ (ι Q w) * ρ (ι Q v) = (-2 * ⟪v, w⟫) • 1 := by
  rw [ρ.map_cliffordAlgebraι_mul_map_cliffordAlgebraι_add_swap,
    QuadraticMap.polar_eq_neg_two_inner hQ]

end Semiring

section Ring

variable {B : Type*} [Ring B] [Algebra ℝ B] (ρ : CliffordAlgebra Q →ₐ[ℝ] B)

/-- Orthogonal vectors anticommute under any algebra map out of `CliffordAlgebra Q` when
`Q v = -‖v‖²`. -/
theorem map_cliffordAlgebraι_mul_map_cliffordAlgebraι_of_inner_eq_zero
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) {v w : V} (hvw : ⟪v, w⟫ = 0) :
    ρ (ι Q v) * ρ (ι Q w) = -(ρ (ι Q w) * ρ (ι Q v)) := by
  refine eq_neg_of_add_eq_zero_left ?_
  rw [ρ.map_cliffordAlgebraι_mul_map_cliffordAlgebraι_add_swap_eq_neg_two_inner hQ, hvw, mul_zero,
    zero_smul]

/-- A unit vector acts by a square root of `-1` when `Q v = -‖v‖²`. -/
theorem map_cliffordAlgebraι_sq_of_norm_eq_one (hQ : ∀ v, Q v = -‖v‖ ^ 2) {e : V}
    (he : ‖e‖ = 1) :
    ρ (ι Q e) * ρ (ι Q e) = -1 := by
  rw [← map_mul ρ, ι_sq_scalar, hQ, he, one_pow, map_neg, map_one, map_neg, map_one]

/-- For an orthonormal pair `(e₁, e₂)` and `Q v = -‖v‖²`, the bivector `c(e₁) c(e₂)` squares to
`-1`. -/
theorem map_cliffordAlgebraι_mul_map_cliffordAlgebraι_sq_of_orthonormal
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) {e₁ e₂ : V} (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1)
    (h12 : ⟪e₁, e₂⟫ = 0) :
    (ρ (ι Q e₁) * ρ (ι Q e₂)) * (ρ (ι Q e₁) * ρ (ι Q e₂)) = -1 := by
  calc
    (ρ (ι Q e₁) * ρ (ι Q e₂)) * (ρ (ι Q e₁) * ρ (ι Q e₂))
      = ρ (ι Q e₁) * (ρ (ι Q e₂) * ρ (ι Q e₁)) * ρ (ι Q e₂) := by simp only [mul_assoc]
    _ = -(ρ (ι Q e₁) * ρ (ι Q e₁) * (ρ (ι Q e₂) * ρ (ι Q e₂))) := by
        rw [ρ.map_cliffordAlgebraι_mul_map_cliffordAlgebraι_of_inner_eq_zero hQ
          (by rw [real_inner_comm, h12])]
        simp only [mul_neg, neg_mul, mul_assoc]
    _ = -1 := by
        rw [ρ.map_cliffordAlgebraι_sq_of_norm_eq_one hQ he₁,
          ρ.map_cliffordAlgebraι_sq_of_norm_eq_one hQ he₂, neg_mul_neg, one_mul]

/-- **2-plane rotation invariance**: rotating an orthonormal pair `(e₁, e₂)` by angle `θ` preserves
the oriented Clifford product `c(e₁) c(e₂)` when `Q v = -‖v‖²`. -/
theorem map_cliffordAlgebraι_cos_smul_add_sin_smul_mul_neg_sin_smul_add_cos_smul
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) {e₁ e₂ : V} (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1)
    (h12 : ⟪e₁, e₂⟫ = 0) (θ : ℝ) :
    ρ (ι Q (Real.cos θ • e₁ + Real.sin θ • e₂)) *
        ρ (ι Q (-Real.sin θ • e₁ + Real.cos θ • e₂)) =
      ρ (ι Q e₁) * ρ (ι Q e₂) := by
  have he₁_sq := ρ.map_cliffordAlgebraι_sq_of_norm_eq_one hQ he₁
  have he₂_sq := ρ.map_cliffordAlgebraι_sq_of_norm_eq_one hQ he₂
  have h21 : ρ (ι Q e₂) * ρ (ι Q e₁) = -(ρ (ι Q e₁) * ρ (ι Q e₂)) :=
    ρ.map_cliffordAlgebraι_mul_map_cliffordAlgebraι_of_inner_eq_zero hQ
      (by rw [real_inner_comm, h12])
  simp only [neg_smul, map_add, map_neg, map_smul, add_mul, mul_add, mul_neg,
    smul_mul_assoc, mul_smul_comm, smul_neg, he₁_sq, he₂_sq, h21]
  simp only [smul_add, smul_neg, neg_add_rev, neg_neg, smul_smul]
  calc
    (Real.sin θ * Real.sin θ) • (ρ (ι Q e₁) * ρ (ι Q e₂)) + (Real.sin θ * Real.cos θ) • (1 : B) +
        ((Real.cos θ * Real.cos θ) • (ρ (ι Q e₁) * ρ (ι Q e₂)) +
          -((Real.cos θ * Real.sin θ) • (1 : B)))
      = ((Real.sin θ * Real.cos θ) • (1 : B) - (Real.cos θ * Real.sin θ) • (1 : B)) +
          (Real.cos θ ^ 2 + Real.sin θ ^ 2) • (ρ (ι Q e₁) * ρ (ι Q e₂)) := by
        rw [add_smul, sq, sq, sub_eq_add_neg]
        abel
    _ = ρ (ι Q e₁) * ρ (ι Q e₂) := by
        rw [mul_comm (Real.sin θ) (Real.cos θ), sub_self, zero_add, Real.cos_sq_add_sin_sq,
          one_smul]

end Ring

end AlgHom
