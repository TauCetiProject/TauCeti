/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
-- Private: the Clifford multiplication and ordered-product formulas are used only inside proofs.
import TauCeti.LinearAlgebra.CliffordAlgebra.Even.Conjugation
import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Basic
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
* `OrthonormalBasis.map_ι_apply_map_ι_apply`, `OrthonormalBasis.map_ι_apply_map_ι_apply_comm`: in
  a Clifford module, `c(bᵢ)² = -1`, and `c(bᵢ)` and `c(bⱼ)` anticommute for `i ≠ j`.
* `OrthonormalBasis.map_ι_eq_sum`, `OrthonormalBasis.map_ι_apply_eq_sum`: `c(v) = ∑ᵢ ⟪bᵢ, v⟫ c(bᵢ)`,
  in any real algebra receiving the Clifford algebra and applied in a Clifford module.
* `QuadraticMap.polar_eq_neg_two_inner`: the polar form of `Q` is `-2 ⟪u, v⟫`.
* `CliffordAlgebra.ι_mul_ι_add_swap_eq_neg_two_inner`, and in the even subalgebra
  `CliffordAlgebra.even_ι_bilin_add_swap_eq_neg_two_inner`: the polarized Clifford relation
  `c(u) c(v) + c(v) c(u) = -2 ⟪u, v⟫`.
* `LinearMap.apply_apply_add_swap_eq_neg_two_inner`: the same polarized relation for a
  linear map `c : W → End U` satisfying the Clifford relation `c(v)² = -⟪v, v⟫`, and
  `ContinuousLinearMap.apply_apply_add_swap_eq_neg_two_inner` for a continuous bilinear map.
* `CliffordAlgebra.sum_sum_smul_ι_mul_ι_of_symm`: for a symmetric family of scalars `mᵢⱼ`,
  `∑ᵢⱼ mᵢⱼ c(eᵢ) c(eⱼ) = -∑ᵢ mᵢᵢ`.
* `TauCeti.two_nsmul_sum_sum_apply_apply_eq`: for additive maps `γᵢ` satisfying the Clifford
  relations `γᵢ γⱼ + γⱼ γᵢ = -2 δᵢⱼ`, the contraction `∑ᵢⱼ γᵢ γⱼ B i j` of a doubly indexed family
  splits into its trace and its antisymmetrization.
* `CliffordAlgebra.basis_mul_self_of_orthonormal`: `e_s * e_s = (-1) ^ ((|s| + 1).choose 2)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §1.
-/

public section

open scoped RealInnerProductSpace

namespace TauCeti

/-- **Clifford contraction of a doubly indexed family.** Let `γᵢ` be additive maps satisfying the
Clifford relations `γᵢ γⱼ + γⱼ γᵢ = -2 δᵢⱼ`, such as Clifford multiplication by the vectors of an
orthonormal basis. Then for every family `B i j`,

`2 ∑ᵢ ∑ⱼ γᵢ γⱼ B i j = -2 ∑ᵢ B i i + ∑ᵢ ∑ⱼ γᵢ γⱼ (B i j - B j i)`.

For `B i j = ∇²σ(eᵢ, eⱼ)` the first term is twice the rough Laplacian and the second is a
curvature term. -/
theorem two_nsmul_sum_sum_apply_apply_eq {ι V G : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [FunLike G V V] [AddMonoidHomClass G V V] (γ : ι → G)
    (hγ : ∀ i j s, γ i (γ j s) + γ j (γ i s) = if i = j then -(2 • s) else 0)
    (B : ι → ι → V) :
    2 • ∑ i, ∑ j, γ i (γ j (B i j)) =
      -(2 • ∑ i, B i i) + ∑ i, ∑ j, γ i (γ j (B i j - B j i)) := by
  -- Exchanging the indices and applying the Clifford relation gives
  -- `∑ᵢ ∑ⱼ γᵢ γⱼ B j i + ∑ᵢ ∑ⱼ γᵢ γⱼ B i j = -2 ∑ᵢ B i i`.
  have hswap : ∑ i, ∑ j, γ i (γ j (B j i)) + ∑ i, ∑ j, γ i (γ j (B i j)) = -(2 • ∑ i, B i i) := by
    rw [Finset.sum_comm (f := fun i j ↦ γ i (γ j (B j i))), ← Finset.sum_add_distrib]
    simp only [← Finset.sum_add_distrib, hγ, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      Finset.sum_neg_distrib, Finset.smul_sum]
  simp only [map_sub, Finset.sum_sub_distrib, eq_sub_of_add_eq hswap]
  abel

end TauCeti

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

omit hQ in
/-- Clifford multiplication expanded in an orthonormal basis, in any real algebra receiving the
Clifford algebra: `ρ (c(v)) = ∑ᵢ ⟪bᵢ, v⟫ ρ (c(bᵢ))`. -/
theorem map_ι_eq_sum {A : Type*} [Semiring A] [Algebra ℝ A] (ρ : CliffordAlgebra Q →ₐ[ℝ] A)
    (v : V) : ρ (CliffordAlgebra.ι Q v) = ∑ i, ⟪b i, v⟫ • ρ (CliffordAlgebra.ι Q (b i)) := by
  conv_lhs => rw [← b.sum_repr' v]
  simp only [map_sum, map_smul]

omit hQ in
/-- Clifford multiplication expanded in an orthonormal basis, applied to a vector of a Clifford
module over any scalars `S` compatible with the real scalars:
`c(v) ψ = ∑ᵢ ⟪bᵢ, v⟫ c(bᵢ) ψ` (`OrthonormalBasis.map_ι_eq_sum` evaluated at `ψ`). -/
theorem map_ι_apply_eq_sum {S W : Type*} [Semiring S] [SMul ℝ S] [AddCommGroup W] [Module S W]
    [Module ℝ W] [SMulCommClass S ℝ W] [IsScalarTower ℝ S W]
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End S W) (v : V) (ψ : W) :
    ρ (CliffordAlgebra.ι Q v) ψ = ∑ i, ⟪b i, v⟫ • ρ (CliffordAlgebra.ι Q (b i)) ψ := by
  rw [b.map_ι_eq_sum ρ v, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply]

section Module

variable {K W : Type*} [Semiring K] [AddCommGroup W] [Module K W] [Algebra ℝ (Module.End K W)]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End K W)

/-- For `Q v = -‖v‖²`, Clifford multiplication by an orthonormal basis vector squares to `-1`:
`c(bᵢ) (c(bᵢ) ψ) = -ψ`. -/
theorem map_ι_apply_map_ι_apply (i : ι) (ψ : W) :
    ρ (CliffordAlgebra.ι Q (b i)) (ρ (CliffordAlgebra.ι Q (b i)) ψ) = -ψ := by
  rw [← mul_apply_eq_comp, ← map_mul, CliffordAlgebra.ι_sq_scalar, hQ, b.orthonormal.1 i]
  simp

/-- For `Q v = -‖v‖²`, Clifford multiplications by distinct orthonormal basis vectors
anticommute: `c(bᵢ) (c(bⱼ) ψ) = -c(bⱼ) (c(bᵢ) ψ)` for `i ≠ j`. -/
theorem map_ι_apply_map_ι_apply_comm {i j : ι} (hij : i ≠ j) (ψ : W) :
    ρ (CliffordAlgebra.ι Q (b i)) (ρ (CliffordAlgebra.ι Q (b j)) ψ) =
      -ρ (CliffordAlgebra.ι Q (b j)) (ρ (CliffordAlgebra.ι Q (b i)) ψ) := by
  simpa [mul_apply_eq_comp] using
    congrArg (fun x ↦ ρ x ψ) (CliffordAlgebra.ι_mul_ι_comm_of_isOrtho (b.isOrtho_apply hQ hij))

end Module

/-- Clifford multiplication by two orthonormal frame vectors preserves nonvanishing. -/
theorem map_ι_apply_map_ι_apply_ne_zero {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (i j : ι) {ψ : W} (hψ : ψ ≠ 0) :
    ρ (CliffordAlgebra.ι Q (b i)) (ρ (CliffordAlgebra.ι Q (b j)) ψ) ≠ 0 := by
  have hinj (k : ι) := CliffordAlgebra.map_ι_injective ρ (v := b k)
    (by simp [hQ, b.orthonormal.1 k])
  exact fun heq ↦ hψ <| ((hinj i).comp (hinj j)) (by simpa using heq)

end OrthonormalBasis

namespace CliffordAlgebra

/-- For `Q v = -‖v‖²`, the polar form of `Q` is `-2 ⟪u, v⟫`. -/
theorem _root_.QuadraticMap.polar_eq_neg_two_inner (u v : V) :
    QuadraticMap.polar Q u v = -2 * ⟪u, v⟫ := by
  simp only [QuadraticMap.polar, hQ, norm_add_sq_real]
  ring

/-- **The polarized Clifford relation**: for `Q v = -‖v‖²`,
`c(u) c(v) + c(v) c(u) = -2 ⟪u, v⟫`. -/
theorem ι_mul_ι_add_swap_eq_neg_two_inner (u v : V) :
    ι Q u * ι Q v + ι Q v * ι Q u = algebraMap ℝ (CliffordAlgebra Q) (-2 * ⟪u, v⟫) := by
  rw [ι_mul_ι_add_swap, QuadraticMap.polar_eq_neg_two_inner hQ]

/-- **The Clifford contraction of a symmetric matrix**: for `Q v = -‖v‖²`, an orthonormal basis
`(eᵢ)` and a symmetric family of scalars `mᵢⱼ`, the contraction `∑ᵢⱼ mᵢⱼ c(eᵢ) c(eⱼ)` is the
scalar `-∑ᵢ mᵢᵢ`: the antisymmetric parts of the products `c(eᵢ) c(eⱼ)` cancel in pairs. -/
theorem sum_sum_smul_ι_mul_ι_of_symm {I : Type*} [Fintype I] (b : OrthonormalBasis I ℝ V)
    {m : I → I → ℝ} (hm : ∀ i j, m i j = m j i) :
    ∑ i, ∑ j, m i j • (ι Q (b i) * ι Q (b j)) = algebraMap ℝ (CliffordAlgebra Q) (-∑ i, m i i) := by
  classical
  have h2 : (2 : ℝ) • ∑ i, ∑ j, m i j • (ι Q (b i) * ι Q (b j)) =
      (2 : ℝ) • algebraMap ℝ (CliffordAlgebra Q) (-∑ i, m i i) := by
    calc (2 : ℝ) • ∑ i, ∑ j, m i j • (ι Q (b i) * ι Q (b j))
        = ∑ i, ∑ j, m i j • (ι Q (b i) * ι Q (b j)) +
            ∑ i, ∑ j, m i j • (ι Q (b j) * ι Q (b i)) := by
          rw [two_smul]
          congr 1
          rw [Finset.sum_comm]
          simp_rw [hm]
      _ = ∑ i, ∑ j, m i j • algebraMap ℝ (CliffordAlgebra Q) (-2 * ⟪b i, b j⟫) := by
          simp_rw [← Finset.sum_add_distrib, ← smul_add, ι_mul_ι_add_swap_eq_neg_two_inner hQ]
      _ = (2 : ℝ) • algebraMap ℝ (CliffordAlgebra Q) (-∑ i, m i i) := by
          simp_rw [b.inner_eq_ite, Algebra.smul_def, ← map_mul, ← map_sum]
          congr 1
          simp [Finset.mul_sum, mul_comm]
  exact smul_right_injective _ two_ne_zero h2

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

omit hQ in
/-- **The polarized Clifford relation.** If a linear map `c : W → End U` from a real inner product
space satisfies the Clifford relation `c(v)² = -⟪v, v⟫`, then
`c(u) c(v) + c(v) c(u) = -2 ⟪u, v⟫`. -/
theorem LinearMap.apply_apply_add_swap_eq_neg_two_inner {W U : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [AddCommGroup U] [Module ℝ U]
    (c : W →ₗ[ℝ] Module.End ℝ U) (hc : ∀ (v : W) (s : U), c v (c v s) = -⟪v, v⟫ • s)
    (u v : W) (s : U) :
    c u (c v s) + c v (c u s) = -(2 * ⟪u, v⟫) • s := by
  have h := hc (u + v) s
  simp only [map_add, LinearMap.add_apply, hc, inner_add_left, inner_add_right,
    real_inner_comm u v] at h
  linear_combination (norm := module) h

omit hQ in
/-- **The polarized Clifford relation** for a continuous bilinear map. If
`c : W →L[ℝ] U →L[ℝ] U` satisfies the Clifford relation `c(v)² = -⟪v, v⟫`, then
`c(u) c(v) + c(v) c(u) = -2 ⟪u, v⟫`. -/
theorem ContinuousLinearMap.apply_apply_add_swap_eq_neg_two_inner {W U : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [AddCommGroup U] [Module ℝ U]
    [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousConstSMul ℝ U]
    (c : W →L[ℝ] U →L[ℝ] U) (hc : ∀ (v : W) (s : U), c v (c v s) = -⟪v, v⟫ • s)
    (u v : W) (s : U) :
    c u (c v s) + c v (c u s) = -(2 * ⟪u, v⟫) • s := by
  simpa using LinearMap.apply_apply_add_swap_eq_neg_two_inner
    ((ContinuousLinearMap.coeLM ℝ).comp c.toLinearMap) (by simpa using hc) u v s
