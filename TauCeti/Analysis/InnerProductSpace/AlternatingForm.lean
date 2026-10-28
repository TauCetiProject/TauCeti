/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Contraction
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.Specializations
public import TauCeti.LinearAlgebra.ExteriorPower.WedgePairing
public import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Alternating forms on a real inner product space

The fibres of the bundle of differential `k`-forms are the continuous alternating maps
`V [⋀^Fin k]→L[ℝ] ℝ` on a tangent space `V`. On a finite-dimensional real inner product space
they are identified with the exterior power `⋀ᵏ V`: an element `x` gives the form
`v ↦ ⟪x, v₁ ∧ ⋯ ∧ vₖ⟫`. This is `TauCeti.alternatingFormEquiv`. On a wedge of vectors it is the
wedge of the covectors `⟪uⱼ, ·⟫` in the determinant normalization,
`(u₁ ∧ ⋯ ∧ uₖ)(v₁, …, vₖ) = det ⟪uⱼ, vᵢ⟫`.

The identification carries the exterior product to the wedge product of forms,
`ContinuousAlternatingMap.wedge`, normalized by `1 / (k! l!)` as in Lee's *Introduction to Smooth
Manifolds*. It carries the contraction by `⟪u, ·⟫` to the interior product
`ContinuousAlternatingMap.curryLeft` by `u`. Transporting the inner product of `⋀ᵏ V`, given on
wedges by Gram determinants, defines the pointwise inner product of `k`-forms,
`TauCeti.alternatingFormInner`. For an orthonormal basis `(eᵢ)` it is
`⟨α, β⟩ = ∑_{i₁ < ⋯ < iₖ} α(e_{i₁}, …, e_{iₖ}) β(e_{i₁}, …, e_{iₖ})`, so the increasing wedges of
the dual coframe are orthonormal. For an arbitrary basis `b`, with dual basis `b*` for the inner
product, a form is represented by `∑ α(b_{i₁}, …, b_{iₖ}) b*_{i₁} ∧ ⋯ ∧ b*_{iₖ}`
(`TauCeti.alternatingFormEquiv_symm_eq_sum`).

## Main definitions

* `TauCeti.alternatingFormEquiv`: the linear equivalence `⋀ᵏ V ≃ₗ[ℝ] V [⋀^Fin k]→L[ℝ] ℝ`.
* `TauCeti.alternatingFormInner`: the Gram inner product of alternating `k`-forms.

## Main results

* `TauCeti.alternatingFormEquiv_wedge`: the identification carries `x ∧ y` to the wedge of forms.
* `TauCeti.alternatingFormEquiv_koszulDifferential`: it carries the contraction by `⟪u, ·⟫` to
  the interior product by `u`.
* `TauCeti.alternatingFormInner_eq_sum`: the inner product of forms in an orthonormal basis.
* `TauCeti.alternatingFormEquiv_symm_eq_sum`: the element of `⋀ᵏ V` representing a form, in
  an arbitrary basis.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 14.
* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer (1983), §6.1.
-/

public section

noncomputable section

open Module exteriorPower Set
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace TauCeti

variable (V) in
/-- The identification of the exterior power `⋀ᵏ V` of a finite-dimensional real inner product
space with the continuous alternating `k`-forms on `V`: `x` is sent to the form
`v ↦ ⟪x, v₁ ∧ ⋯ ∧ vₖ⟫`. -/
def alternatingFormEquiv (k : ℕ) : ⋀[ℝ]^k V ≃ₗ[ℝ] V [⋀^Fin k]→L[ℝ] ℝ :=
  (LinearEquiv.ofBijective (innerₗ (⋀[ℝ]^k V)) bijective_innerₗ).trans
    (alternatingMapLinearEquiv.symm.trans AlternatingMap.toContinuousAlternatingMap)

/-- The form of `x ∈ ⋀ᵏ V` evaluates on `(v₁, …, vₖ)` as `⟪x, v₁ ∧ ⋯ ∧ vₖ⟫`. -/
@[simp]
theorem alternatingFormEquiv_apply {k : ℕ} (x : ⋀[ℝ]^k V) (v : Fin k → V) :
    alternatingFormEquiv V k x v = ⟪x, ιMulti ℝ k v⟫ := by
  simp [alternatingFormEquiv]

/-- The element of `⋀ᵏ V` representing a form `α` pairs with `v₁ ∧ ⋯ ∧ vₖ` to `α v`. -/
@[simp]
theorem inner_alternatingFormEquiv_symm_ιMulti {k : ℕ} (α : V [⋀^Fin k]→L[ℝ] ℝ)
    (v : Fin k → V) : ⟪(alternatingFormEquiv V k).symm α, ιMulti ℝ k v⟫ = α v := by
  rw [← alternatingFormEquiv_apply, LinearEquiv.apply_symm_apply]

/-- The form of a wedge of vectors `u₁ ∧ ⋯ ∧ uₖ` is the wedge of the covectors `⟪uⱼ, ·⟫` in the
determinant normalization: its value on `(v₁, …, vₖ)` is `det ⟪uⱼ, vᵢ⟫`. -/
theorem alternatingFormEquiv_ιMulti_apply {k : ℕ} (u v : Fin k → V) :
    alternatingFormEquiv V k (ιMulti ℝ k u) v = (Matrix.of fun i j ↦ ⟪u j, v i⟫).det := by
  rw [alternatingFormEquiv_apply, inner_ιMulti_ιMulti]

/-- The form of a wedge of vectors is the alternatization of the product of the covectors
`⟪uⱼ, ·⟫`. -/
private theorem alternatingFormEquiv_ιMulti_toAlternatingMap {k : ℕ} (u : Fin k → V) :
    (alternatingFormEquiv V k (ιMulti ℝ k u)).toAlternatingMap =
      ((MultilinearMap.mkPiAlgebra ℝ (Fin k) ℝ).compLinearMap
        fun i ↦ innerₗ V (u i)).alternatization := by
  ext v
  simp [inner_ιMulti_ιMulti, Matrix.det_apply, MultilinearMap.alternatization_apply]

/-- The wedge-product formula on wedges of vectors: both sides are alternatizations of products
of covectors, by `ContinuousAlternatingMap.pairedWedge_toAlternatingMap_of_eq_alternatization`. -/
private theorem alternatingFormEquiv_ιMulti_append {k l : ℕ} (u : Fin k → V) (w : Fin l → V) :
    alternatingFormEquiv V (k + l) (ιMulti ℝ (k + l) (Fin.append u w)) =
      (alternatingFormEquiv V k (ιMulti ℝ k u)).wedge
        (alternatingFormEquiv V l (ιMulti ℝ l w)) := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  rw [ContinuousAlternatingMap.wedge_def,
    ContinuousAlternatingMap.pairedWedge_toAlternatingMap_of_eq_alternatization _ _
      (alternatingFormEquiv_ιMulti_toAlternatingMap u)
      (alternatingFormEquiv_ιMulti_toAlternatingMap w),
    alternatingFormEquiv_ιMulti_toAlternatingMap]
  -- The product of the covectors of `u` and of `w`, read on `Fin (k + l)`, is the product of the
  -- covectors of the concatenation.
  congr 1
  ext v
  simp [Fin.prod_univ_add]

/-- **The exterior product is the wedge product of forms**: the form of `x ∧ y` is the wedge of
the forms of `x ∈ ⋀ᵏ V` and `y ∈ ⋀ˡ V`, with the normalization of
`ContinuousAlternatingMap.wedge`. -/
theorem alternatingFormEquiv_wedge {k l : ℕ} (x : ⋀[ℝ]^k V) (y : ⋀[ℝ]^l V) :
    alternatingFormEquiv V (k + l) (exteriorPower.wedge ℝ V k l x y) =
      (alternatingFormEquiv V k x).wedge (alternatingFormEquiv V l y) := by
  -- Both sides are bilinear in `(x, y)`, so it suffices to compare them on wedges of vectors.
  let B : ⋀[ℝ]^k V →ₗ[ℝ] ⋀[ℝ]^l V →ₗ[ℝ] V [⋀^Fin (k + l)]→L[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun x y ↦ (alternatingFormEquiv V k x).wedge (alternatingFormEquiv V l y))
      (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp)
  have key :
      (exteriorPower.wedge ℝ V k l).compr₂ (alternatingFormEquiv V (k + l)).toLinearMap = B := by
    refine exteriorPower.linearMap_ext (R := ℝ) (M := V) (n := k)
      (AlternatingMap.ext fun u ↦ exteriorPower.linearMap_ext (R := ℝ) (M := V) (n := l)
        (AlternatingMap.ext fun w ↦ ?_))
    simp [B, alternatingFormEquiv_ιMulti_append]
  exact LinearMap.congr_fun₂ key x y

/-- **Contraction is the interior product**: the form of the contraction `ι_u x` of
`x ∈ ⋀ᵏ⁺¹ V` by `⟪u, ·⟫` is the interior product of the form of `x` by `u`. -/
theorem alternatingFormEquiv_koszulDifferential (u : V) {k : ℕ} (x : ⋀[ℝ]^(k + 1) V) :
    alternatingFormEquiv V k (koszulDifferential (innerₗ V u) k x) =
      (alternatingFormEquiv V (k + 1) x).curryLeft u := by
  ext v
  rw [alternatingFormEquiv_apply, ContinuousAlternatingMap.curryLeft_apply_apply,
    alternatingFormEquiv_apply, real_inner_comm, ← inner_wedgeLeft_eq_inner_koszulDifferential,
    real_inner_comm, ExteriorAlgebra.wedgeLeft_ιMulti]
  -- `Matrix.vecCons`, used by `curryLeft`, is by definition `Fin.cons`.
  rfl

variable (V) in
/-- The pointwise inner product of alternating `k`-forms, transported from the inner product of
`⋀ᵏ V` along `TauCeti.alternatingFormEquiv`. On wedges of covectors it is the Gram determinant,
and in an orthonormal basis it is computed by `TauCeti.alternatingFormInner_eq_sum`. -/
def alternatingFormInner (k : ℕ) : LinearMap.BilinForm ℝ (V [⋀^Fin k]→L[ℝ] ℝ) :=
  (innerₗ (⋀[ℝ]^k V)).compl₁₂ (alternatingFormEquiv V k).symm.toLinearMap
    (alternatingFormEquiv V k).symm.toLinearMap

/-- The inner product of two forms is the inner product of the elements of `⋀ᵏ V` representing
them. -/
theorem alternatingFormInner_apply {k : ℕ} (α β : V [⋀^Fin k]→L[ℝ] ℝ) :
    alternatingFormInner V k α β =
      ⟪(alternatingFormEquiv V k).symm α, (alternatingFormEquiv V k).symm β⟫ := by
  simp [alternatingFormInner]

/-- The identification `⋀ᵏ V ≃ₗ[ℝ] V [⋀^Fin k]→L[ℝ] ℝ` is an isometry for the inner product of
forms. -/
@[simp]
theorem alternatingFormInner_alternatingFormEquiv {k : ℕ} (x y : ⋀[ℝ]^k V) :
    alternatingFormInner V k (alternatingFormEquiv V k x) (alternatingFormEquiv V k y) =
      ⟪x, y⟫ := by
  simp [alternatingFormInner_apply]

/-- The inner product of forms is symmetric. -/
theorem alternatingFormInner_comm {k : ℕ} (α β : V [⋀^Fin k]→L[ℝ] ℝ) :
    alternatingFormInner V k α β = alternatingFormInner V k β α := by
  rw [alternatingFormInner_apply, alternatingFormInner_apply, real_inner_comm]

/-- The inner product of forms is positive semidefinite. -/
theorem alternatingFormInner_self_nonneg {k : ℕ} (α : V [⋀^Fin k]→L[ℝ] ℝ) :
    0 ≤ alternatingFormInner V k α α := by
  rw [alternatingFormInner_apply]
  exact real_inner_self_nonneg

/-- The inner product of forms is definite. -/
@[simp]
theorem alternatingFormInner_self_eq_zero {k : ℕ} {α : V [⋀^Fin k]→L[ℝ] ℝ} :
    alternatingFormInner V k α α = 0 ↔ α = 0 := by
  rw [alternatingFormInner_apply, inner_self_eq_zero, LinearEquiv.map_eq_zero_iff]

/-- **The inner product of forms in an orthonormal basis**: if `(eᵢ)` is an orthonormal basis of
`V` indexed by a linear order, then `⟨α, β⟩ = ∑ α(e_{i₁}, …, e_{iₖ}) β(e_{i₁}, …, e_{iₖ})`, the sum
running over the increasing `k`-tuples `i₁ < ⋯ < iₖ`. Equivalently, the increasing wedges of the
dual coframe are orthonormal. -/
theorem alternatingFormInner_eq_sum {ι : Type*} [Fintype ι] [LinearOrder ι]
    (b : OrthonormalBasis ι ℝ V) {k : ℕ} (α β : V [⋀^Fin k]→L[ℝ] ℝ) :
    alternatingFormInner V k α β =
      ∑ s : powersetCard ι k, α (b ∘ powersetCard.ofFinEmbEquiv.symm s) *
        β (b ∘ powersetCard.ofFinEmbEquiv.symm s) := by
  rw [alternatingFormInner_apply, ← (b.exteriorPower k).sum_inner_mul_inner]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have hs : b.exteriorPower k s = ιMulti ℝ k (b ∘ powersetCard.ofFinEmbEquiv.symm s) := by
    rw [← OrthonormalBasis.coe_toBasis, OrthonormalBasis.toBasis_exteriorPower, basis_apply,
      ιMulti_family, OrthonormalBasis.coe_toBasis]
  rw [hs, real_inner_comm ((alternatingFormEquiv V k).symm β),
    inner_alternatingFormEquiv_symm_ιMulti, inner_alternatingFormEquiv_symm_ιMulti]

variable {ι : Type*} [LinearOrder ι]

/-- The wedges of the dual basis `b*` and the coordinates of `⋀ᵏ V` in the basis induced by `b`:
`⟪b*_{i₁} ∧ ⋯ ∧ b*_{iₖ}, w₁ ∧ ⋯ ∧ wₖ⟫` is the coordinate of `w₁ ∧ ⋯ ∧ wₖ` at
`{i₁ < ⋯ < iₖ}`. -/
theorem inner_ιMulti_dualBasis [Finite ι] (b : Basis ι ℝ V) {k : ℕ} (s : powersetCard ι k)
    (w : Fin k → V) :
    ⟪ιMulti ℝ k (LinearMap.BilinForm.dualBasis (innerₗ V) nondegenerate_inner b ∘
        powersetCard.ofFinEmbEquiv.symm s), ιMulti ℝ k w⟫ =
      (b.exteriorPower k).repr (ιMulti ℝ k w) s := by
  have := Fintype.ofFinite ι
  rw [inner_ιMulti_ιMulti, basis_repr_apply, ιMultiDual_apply_ιMulti]
  congr 1
  ext i j
  simp [inner_dualBasis_left]

/-- **A form in an arbitrary basis**: the element of `⋀ᵏ V` representing a form `α` is
`∑ α(b_{i₁}, …, b_{iₖ}) b*_{i₁} ∧ ⋯ ∧ b*_{iₖ}`, the sum running over the increasing `k`-tuples
`i₁ < ⋯ < iₖ`, where `b*` is the dual basis of `b` for the inner product. -/
theorem alternatingFormEquiv_symm_eq_sum [Fintype ι] (b : Basis ι ℝ V) {k : ℕ}
    (α : V [⋀^Fin k]→L[ℝ] ℝ) :
    (alternatingFormEquiv V k).symm α = ∑ s : powersetCard ι k,
      α (b ∘ powersetCard.ofFinEmbEquiv.symm s) •
        ιMulti ℝ k (LinearMap.BilinForm.dualBasis (innerₗ V) nondegenerate_inner b ∘
          powersetCard.ofFinEmbEquiv.symm s) := by
  classical
  -- Both sides have the same inner product with each basis vector `b_{t₁} ∧ ⋯ ∧ b_{tₖ}`.
  refine InnerProductSpace.ext_inner_left_basis (b.exteriorPower k) fun t ↦ ?_
  have ht : b.exteriorPower k t = ιMulti ℝ k (b ∘ powersetCard.ofFinEmbEquiv.symm t) := by
    rw [basis_apply, ιMulti_family]
  simp only [inner_sum, real_inner_smul_right]
  simp_rw [real_inner_comm _ (b.exteriorPower k t)]
  conv_rhs => enter [2, s]; rw [ht, inner_ιMulti_dualBasis, ← ht, Basis.repr_self,
    Finsupp.single_apply]
  rw [ht, inner_alternatingFormEquiv_symm_ιMulti]
  simp

end TauCeti
