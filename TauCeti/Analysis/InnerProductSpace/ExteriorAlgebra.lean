/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ExteriorPower
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import TauCeti.LinearAlgebra.BilinearForm.Complexification
public import TauCeti.LinearAlgebra.ExteriorAlgebra.HermitianMetric
public import TauCeti.LinearAlgebra.ExteriorPower.BaseChange
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

/-!
# The exterior Gram metric on real and complexified exterior algebras

Each exterior power `⋀[ℝ]^k V` of a finite-dimensional real inner product space `V` carries
Mathlib's canonical Gram inner product, characterized on decomposable `k`-vectors by
`⟪x₁ ∧ ⋯ ∧ xₖ, y₁ ∧ ⋯ ∧ yₖ⟫ = det (⟪xᵢ, yⱼ⟫)`. Because the exterior algebra is the internal
direct sum of its homogeneous exterior powers `⨁ k : ℕ, ⋀[ℝ]^k V`, assembling these degreewise
inner products orthogonally yields a canonical symmetric positive definite bilinear form
`ExteriorAlgebra.gramBilinForm V` on the full exterior algebra `ExteriorAlgebra ℝ V`,
without choosing a basis and without registering a competing global norm instance on the exterior
algebra.

Its sesquilinear complexification `(gramBilinForm V).sesqComplexification` is the canonical
Hermitian Gram metric on `ℂ ⊗[ℝ] ExteriorAlgebra ℝ V`. Restricting it to a homogeneous degree `k`
recovers `LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V))`, distinct degrees remain
orthogonal, and for every ordered orthonormal basis `e` of `V` the base-change isomorphism
`ExteriorAlgebra.baseChangeEquiv ℝ V ℂ :
  ℂ ⊗[ℝ] ExteriorAlgebra ℝ V ≃ₐ[ℂ] ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)`
identifies `(gramBilinForm V).sesqComplexification` with the Hermitian form
`Matrix.toLinearMapₛₗ₂ (starRingEnd ℂ) (e.toBasis.baseChange ℂ).ExteriorAlgebra
  (e.toBasis.baseChange ℂ).ExteriorAlgebra 1`
making the complexified increasing wedge basis orthonormal.

## Main definitions

* `ExteriorAlgebra.gramBilinForm V`: the canonical basis-free exterior Gram bilinear form
  on `ExteriorAlgebra ℝ V`, assembling `innerₗ (⋀[ℝ]^k V)` orthogonally across all degrees `k`.

## Main results

* `ExteriorAlgebra.gramBilinForm_coe_coe`,
  `ExteriorAlgebra.gramBilinForm_eq_zero_of_mem_exteriorPower`, and
  `ExteriorAlgebra.gramBilinForm_ιMulti_ιMulti`: `gramBilinForm V` restricts to the Gram
  inner product on each `⋀[ℝ]^k V`, makes distinct degrees orthogonal, and evaluates as the
  `k × k` Gram determinant on decomposable `k`-vectors.
* `ExteriorAlgebra.gramBilinForm_toBasis_exteriorAlgebra`: for every ordered orthonormal
  basis `e` of `V`, `gramBilinForm V` agrees with the form making `e.toBasis.ExteriorAlgebra`
  orthonormal.
* `ExteriorAlgebra.isSymm_gramBilinForm` and
  `ExteriorAlgebra.posDef_toQuadraticMap_gramBilinForm`: `gramBilinForm V` is symmetric
  and positive definite.
* `ExteriorAlgebra.sesqComplexification_gramBilinForm_subtype_baseChange` and
  `ExteriorAlgebra.sesqComplexification_gramBilinForm_subtype_baseChange_eq_zero_of_ne`:
  on `ℂ ⊗[ℝ] ExteriorAlgebra ℝ V`, `(gramBilinForm V).sesqComplexification` restricts to
  `LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V))` in degree `k` and makes distinct
  degrees orthogonal.
* `ExteriorAlgebra.toLinearMapₛₗ₂_baseChange_exteriorAlgebra_baseChangeEquiv` and
  `ExteriorAlgebra.toLinearMapₛₗ₂_baseChange_exteriorAlgebra_coe_coe`: under
  `ExteriorAlgebra.baseChangeEquiv ℝ V ℂ`, the Hermitian form making the increasing wedge basis of
  `e.toBasis.baseChange ℂ` orthonormal is `(gramBilinForm V).sesqComplexification` for every
  ordered orthonormal basis `e` of `V`, and restricts in degree `k` to
  `LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V))` along
  `TauCeti.exteriorPower.equivBaseChange ℂ k`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §1 and §5.
* N. Berline, E. Getzler, and M. Vergne, *Heat Kernels and Dirac Operators* (2004), §3.1–3.2.
-/

public section

noncomputable section

open Matrix Module
open scoped ComplexOrder DirectSum RealInnerProductSpace TensorProduct

namespace ExteriorAlgebra

section Real

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The exterior Gram bilinear form** on `ExteriorAlgebra ℝ V`: the orthogonal direct sum across
all degrees `k : ℕ` of Mathlib's Gram inner product `innerₗ (⋀[ℝ]^k V)` along the homogeneous
grading `DirectSum.decomposeLinearEquiv (fun k : ℕ ↦ ⋀[ℝ]^k V)`. -/
def gramBilinForm (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : LinearMap.BilinForm ℝ (ExteriorAlgebra ℝ V) :=
  let d := DirectSum.decomposeLinearEquiv (fun k : ℕ ↦ ⋀[ℝ]^k V)
  DirectSum.toModule ℝ ℕ _
    (fun k ↦ (innerₗ (⋀[ℝ]^k V)).compl₂
      (DirectSum.component ℝ ℕ (fun i ↦ ⋀[ℝ]^i V) k ∘ₗ d.toLinearMap)) ∘ₗ
    d.toLinearMap

/-- On each homogeneous exterior power `⋀[ℝ]^k V`, `gramBilinForm V` is the Gram inner product. -/
@[simp]
theorem gramBilinForm_coe_coe {k : ℕ} (x y : ⋀[ℝ]^k V) :
    gramBilinForm V x y = ⟪x, y⟫ := by
  simp [gramBilinForm, DirectSum.component.lof_self]

/-- The restriction of `gramBilinForm V` to `⋀[ℝ]^k V` is `innerₗ (⋀[ℝ]^k V)`. -/
@[simp]
theorem gramBilinForm_restrict (k : ℕ) :
    (gramBilinForm V).restrict (⋀[ℝ]^k V) = innerₗ (⋀[ℝ]^k V) :=
  LinearMap.ext₂ fun x y ↦ gramBilinForm_coe_coe x y

/-- **Distinct exterior powers are orthogonal** for `gramBilinForm V`. -/
theorem gramBilinForm_eq_zero_of_mem_exteriorPower {p q : ℕ} (hpq : p ≠ q)
    {x y : ExteriorAlgebra ℝ V} (hx : x ∈ ⋀[ℝ]^p V) (hy : y ∈ ⋀[ℝ]^q V) :
    gramBilinForm V x y = 0 := by
  let x' : ⋀[ℝ]^p V := ⟨x, hx⟩
  let y' : ⋀[ℝ]^q V := ⟨y, hy⟩
  have hx' : x = x' := rfl
  have hy' : y = y' := rfl
  rw [hx', hy']
  simp [gramBilinForm, DirectSum.component.of, hpq.symm]

/-- **Gram-determinant formula** for `gramBilinForm V`: on decomposable `k`-vectors,
`gramBilinForm V` evaluates as `det (⟪xᵢ, yⱼ⟫)`. -/
theorem gramBilinForm_ιMulti_ιMulti (k : ℕ) (x y : Fin k → V) :
    gramBilinForm V (ExteriorAlgebra.ιMulti ℝ k x) (ExteriorAlgebra.ιMulti ℝ k y) =
      (Matrix.of fun i j ↦ ⟪x i, y j⟫).det := by
  rw [← _root_.exteriorPower.ιMulti_apply_coe, ← _root_.exteriorPower.ιMulti_apply_coe,
    gramBilinForm_coe_coe, _root_.exteriorPower.inner_ιMulti_ιMulti, ← Matrix.det_transpose]
  rfl

/-- The unit `1` has self-pairing `1` under `gramBilinForm V`. -/
@[simp]
theorem gramBilinForm_one_one : gramBilinForm V 1 1 = 1 := by
  have h := gramBilinForm_ιMulti_ιMulti (V := V) 0 ![] ![]
  simpa only [ExteriorAlgebra.ιMulti_zero_apply, Matrix.det_fin_zero] using h

/-- In degree one, `gramBilinForm V` restricts to the inner product on `V`. -/
@[simp]
theorem gramBilinForm_ι_ι (x y : V) :
    gramBilinForm V (ExteriorAlgebra.ι ℝ x) (ExteriorAlgebra.ι ℝ y) = ⟪x, y⟫ := by
  have hx : ExteriorAlgebra.ι ℝ x = ExteriorAlgebra.ιMulti ℝ 1 ![x] := by
    simp [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply]
  have hy : ExteriorAlgebra.ι ℝ y = ExteriorAlgebra.ιMulti ℝ 1 ![y] := by
    simp [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply]
  rw [hx, hy, gramBilinForm_ιMulti_ιMulti, Matrix.det_fin_one]
  rfl

/-- **Every ordered orthonormal basis of `V` induces an orthonormal wedge basis for
`gramBilinForm V`**: `gramBilinForm V` agrees with the form making `e.toBasis.ExteriorAlgebra`
orthonormal. -/
theorem gramBilinForm_toBasis_exteriorAlgebra {I : Type*} [Fintype I] [LinearOrder I]
    (e : OrthonormalBasis I ℝ V) (x y : ExteriorAlgebra ℝ V) :
    gramBilinForm V x y =
      toLinearMapₛₗ₂ (starRingEnd ℝ) e.toBasis.ExteriorAlgebra e.toBasis.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) ℝ) x y := by
  have he : toLinearMapₛₗ₂ (starRingEnd ℝ) e.toBasis e.toBasis (1 : Matrix I I ℝ) =
      { toFun := innerₗ V, map_add' := map_add _, map_smul' := fun r v ↦ by simp } := by
    refine LinearMap.ext_basis e.toBasis e.toBasis fun i j ↦ ?_
    rw [toLinearMapₛₗ₂_apply_basis, Matrix.one_apply]
    exact (orthonormal_iff_ite.mp e.orthonormal i j).symm
  let B : ExteriorAlgebra ℝ V →ₗ⋆[ℝ] ExteriorAlgebra ℝ V →ₗ[ℝ] ℝ :=
    { toFun := gramBilinForm V
      map_add' := map_add _
      map_smul' := fun r s ↦ by simp }
  have hB : B = toLinearMapₛₗ₂ (starRingEnd ℝ) e.toBasis.ExteriorAlgebra
      e.toBasis.ExteriorAlgebra (1 : Matrix (Finset I) (Finset I) ℝ) := by
    refine ExteriorAlgebra.eq_toLinearMapₛₗ₂_of_ιMulti e.toBasis B
      (fun hpq _ hs _ ht ↦ gramBilinForm_eq_zero_of_mem_exteriorPower hpq hs ht) (fun p u v ↦ ?_)
    rw [he]
    exact gramBilinForm_ιMulti_ιMulti p u v
  exact LinearMap.congr_fun₂ hB x y

/-- The increasing wedge basis of an ordered orthonormal basis of `V` is orthonormal for
`gramBilinForm V`. -/
theorem gramBilinForm_toBasis_exteriorAlgebra_apply {I : Type*} [Fintype I] [LinearOrder I]
    (e : OrthonormalBasis I ℝ V) (S T : Finset I) :
    gramBilinForm V (e.toBasis.ExteriorAlgebra S) (e.toBasis.ExteriorAlgebra T) =
      if S = T then 1 else 0 := by
  rw [gramBilinForm_toBasis_exteriorAlgebra e, toLinearMapₛₗ₂_apply_basis, Matrix.one_apply]

/-- `gramBilinForm V` is symmetric. -/
theorem isSymm_gramBilinForm : (gramBilinForm V).IsSymm :=
  ⟨fun x y ↦ by
    let e := stdOrthonormalBasis ℝ V
    rw [gramBilinForm_toBasis_exteriorAlgebra e, gramBilinForm_toBasis_exteriorAlgebra e,
      ← star_toLinearMapₛₗ₂_one_apply, star_trivial]⟩

/-- `gramBilinForm V` is positive definite. -/
theorem posDef_toQuadraticMap_gramBilinForm : (gramBilinForm V).toQuadraticMap.PosDef := by
  intro x hx
  let b := (stdOrthonormalBasis ℝ V).toBasis.ExteriorAlgebra
  have hsum : gramBilinForm V x x = ∑ S, (b.repr x S) ^ 2 := by
    rw [gramBilinForm_toBasis_exteriorAlgebra (stdOrthonormalBasis ℝ V),
      toLinearMapₛₗ₂_one_apply]
    refine Finset.sum_congr rfl fun S _ ↦ ?_
    rw [starRingEnd_apply, star_trivial, sq]
  rw [LinearMap.BilinMap.toQuadraticMap_apply, hsum]
  refine lt_of_le_of_ne (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (Ne.symm fun h0 ↦ hx ?_)
  apply b.repr.injective
  ext S
  simpa using (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ sq_nonneg _)).mp h0 S
    (Finset.mem_univ S)

end Real

section Complexification

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- `(gramBilinForm V).sesqComplexification` is Hermitian symmetric. -/
theorem isSymm_sesqComplexification_gramBilinForm :
    (gramBilinForm V).sesqComplexification.IsSymm :=
  isSymm_gramBilinForm.sesqComplexification

/-- `(gramBilinForm V).sesqComplexification` is strictly positive on nonzero complexified forms. -/
theorem sesqComplexification_gramBilinForm_self_pos
    {x : ℂ ⊗[ℝ] ExteriorAlgebra ℝ V} (hx : x ≠ 0) :
    0 < (gramBilinForm V).sesqComplexification x x :=
  LinearMap.BilinForm.sesqComplexification_self_pos isSymm_gramBilinForm
    posDef_toQuadraticMap_gramBilinForm hx

/-- **In degree `k`, `(gramBilinForm V).sesqComplexification` restricts to the sesquilinear
complexification of the Gram inner product `innerₗ (⋀[ℝ]^k V)`.** -/
@[simp]
theorem sesqComplexification_gramBilinForm_subtype_baseChange {k : ℕ}
    (x y : ℂ ⊗[ℝ] ⋀[ℝ]^k V) :
    (gramBilinForm V).sesqComplexification
        ((⋀[ℝ]^k V).subtype.baseChange ℂ x) ((⋀[ℝ]^k V).subtype.baseChange ℂ y) =
      LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V)) x y :=
  LinearMap.BilinForm.sesqComplexification_baseChange_baseChange _
    (fun u w ↦ gramBilinForm_coe_coe u w) x y

/-- **Distinct complexified exterior powers are orthogonal** for
`(gramBilinForm V).sesqComplexification`. -/
theorem sesqComplexification_gramBilinForm_subtype_baseChange_eq_zero_of_ne {p q : ℕ} (hpq : p ≠ q)
    (x : ℂ ⊗[ℝ] ⋀[ℝ]^p V) (y : ℂ ⊗[ℝ] ⋀[ℝ]^q V) :
    (gramBilinForm V).sesqComplexification
        ((⋀[ℝ]^p V).subtype.baseChange ℂ x) ((⋀[ℝ]^q V).subtype.baseChange ℂ y) = 0 := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ hx₁ hx₂ => simp only [map_add, LinearMap.add_apply, hx₁, hx₂, add_zero]
  | tmul c u =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ hy₁ hy₂ => simp only [map_add, hy₁, hy₂, add_zero]
    | tmul d w =>
      simp only [LinearMap.baseChange_tmul, Submodule.coe_subtype,
        LinearMap.BilinForm.sesqComplexification_tmul_tmul,
        gramBilinForm_eq_zero_of_mem_exteriorPower hpq u.2 w.2, Complex.ofReal_zero, mul_zero]

/-- On `⋀[ℂ]^k (ℂ ⊗[ℝ] V)`, pulling `(gramBilinForm V).sesqComplexification` back along
`ExteriorAlgebra.baseChangeEquiv ℝ V ℂ` recovers
`LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V))` along
`TauCeti.exteriorPower.equivBaseChange ℂ k`. -/
theorem sesqComplexification_gramBilinForm_baseChangeEquiv_symm_coe_coe {k : ℕ}
    (a b : ⋀[ℂ]^k (ℂ ⊗[ℝ] V)) :
    (gramBilinForm V).sesqComplexification
        ((ExteriorAlgebra.baseChangeEquiv ℝ V ℂ).symm a)
        ((ExteriorAlgebra.baseChangeEquiv ℝ V ℂ).symm b) =
      LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V))
        (TauCeti.exteriorPower.equivBaseChange ℂ k a)
        (TauCeti.exteriorPower.equivBaseChange ℂ k b) := by
  rw [← TauCeti.exteriorPower.subtype_baseChange_equivBaseChange,
    ← TauCeti.exteriorPower.subtype_baseChange_equivBaseChange,
    sesqComplexification_gramBilinForm_subtype_baseChange]

/-- Distinct homogeneous degrees of `ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)` are orthogonal under the
pullback of `(gramBilinForm V).sesqComplexification` along
`(ExteriorAlgebra.baseChangeEquiv ℝ V ℂ).symm`. -/
theorem sesqComplexification_gramBilinForm_baseChangeEquiv_symm_eq_zero_of_mem_exteriorPower
    {p q : ℕ} (hpq : p ≠ q) {a b : ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)}
    (ha : a ∈ ⋀[ℂ]^p (ℂ ⊗[ℝ] V)) (hb : b ∈ ⋀[ℂ]^q (ℂ ⊗[ℝ] V)) :
    (gramBilinForm V).sesqComplexification
        ((ExteriorAlgebra.baseChangeEquiv ℝ V ℂ).symm a)
        ((ExteriorAlgebra.baseChangeEquiv ℝ V ℂ).symm b) = 0 := by
  simpa only [TauCeti.exteriorPower.subtype_baseChange_equivBaseChange] using
    sesqComplexification_gramBilinForm_subtype_baseChange_eq_zero_of_ne hpq
      (TauCeti.exteriorPower.equivBaseChange ℂ p ⟨a, ha⟩)
      (TauCeti.exteriorPower.equivBaseChange ℂ q ⟨b, hb⟩)

/-- **Orthonormal wedge-basis identification**: for every ordered orthonormal basis `e` of `V`,
pulling the Hermitian form of `(e.toBasis.baseChange ℂ).ExteriorAlgebra` back along
`ExteriorAlgebra.baseChangeEquiv ℝ V ℂ` gives `(gramBilinForm V).sesqComplexification`. -/
theorem toLinearMapₛₗ₂_baseChange_exteriorAlgebra_baseChangeEquiv
    {I : Type*} [Fintype I] [LinearOrder I] (e : OrthonormalBasis I ℝ V)
    (x y : ℂ ⊗[ℝ] ExteriorAlgebra ℝ V) :
    toLinearMapₛₗ₂ (starRingEnd ℂ) (e.toBasis.baseChange ℂ).ExteriorAlgebra
        (e.toBasis.baseChange ℂ).ExteriorAlgebra (1 : Matrix (Finset I) (Finset I) ℂ)
        (ExteriorAlgebra.baseChangeEquiv ℝ V ℂ x)
        (ExteriorAlgebra.baseChangeEquiv ℝ V ℂ y) =
      (gramBilinForm V).sesqComplexification x y := by
  have hbasis (S : Finset I) :
      ExteriorAlgebra.baseChangeEquiv ℝ V ℂ ((1 : ℂ) ⊗ₜ[ℝ] e.toBasis.ExteriorAlgebra S) =
        (e.toBasis.baseChange ℂ).ExteriorAlgebra S := by
    apply (ExteriorAlgebra.baseChangeEquiv ℝ V ℂ).symm.injective
    rw [AlgEquiv.symm_apply_apply,
      ExteriorAlgebra.basis_apply_ofCard (e.toBasis.baseChange ℂ) (rfl : S.card = S.card),
      ExteriorAlgebra.basis_apply_ofCard e.toBasis (rfl : S.card = S.card)]
    simp only [ExteriorAlgebra.ιMulti_family, Function.comp_def, Basis.baseChange_apply,
      ExteriorAlgebra.baseChangeEquiv_symm_ιMulti_tmul, Finset.prod_const_one]
  set H := toLinearMapₛₗ₂ (starRingEnd ℂ) (e.toBasis.baseChange ℂ).ExteriorAlgebra
    (e.toBasis.baseChange ℂ).ExteriorAlgebra (1 : Matrix (Finset I) (Finset I) ℂ)
  let f := (ExteriorAlgebra.baseChangeEquiv ℝ V ℂ).toLinearMap
  have key : (H.comp f).compl₂ f = (gramBilinForm V).sesqComplexification := by
    refine LinearMap.ext_basis (e.toBasis.ExteriorAlgebra.baseChange ℂ)
      (e.toBasis.ExteriorAlgebra.baseChange ℂ) fun S T ↦ ?_
    rw [LinearMap.compl₂_apply, LinearMap.comp_apply, Basis.baseChange_apply,
      Basis.baseChange_apply]
    dsimp only [f]
    rw [AlgEquiv.toLinearMap_apply, AlgEquiv.toLinearMap_apply, hbasis, hbasis,
      toLinearMapₛₗ₂_apply_basis, Matrix.one_apply,
      LinearMap.BilinForm.sesqComplexification_tmul_tmul,
      gramBilinForm_toBasis_exteriorAlgebra_apply e S T]
    split_ifs <;> simp
  exact LinearMap.congr_fun₂ key x y

/-- On `ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)`, the Hermitian form of
`(e.toBasis.baseChange ℂ).ExteriorAlgebra` equals `(gramBilinForm V).sesqComplexification` pulled
back along `(ExteriorAlgebra.baseChangeEquiv ℝ V ℂ).symm`. -/
theorem toLinearMapₛₗ₂_baseChange_exteriorAlgebra
    {I : Type*} [Fintype I] [LinearOrder I] (e : OrthonormalBasis I ℝ V)
    (a b : ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)) :
    toLinearMapₛₗ₂ (starRingEnd ℂ) (e.toBasis.baseChange ℂ).ExteriorAlgebra
        (e.toBasis.baseChange ℂ).ExteriorAlgebra (1 : Matrix (Finset I) (Finset I) ℂ) a b =
      (gramBilinForm V).sesqComplexification
        ((ExteriorAlgebra.baseChangeEquiv ℝ V ℂ).symm a)
        ((ExteriorAlgebra.baseChangeEquiv ℝ V ℂ).symm b) := by
  simpa only [AlgEquiv.apply_symm_apply] using
    toLinearMapₛₗ₂_baseChange_exteriorAlgebra_baseChangeEquiv e
      ((ExteriorAlgebra.baseChangeEquiv ℝ V ℂ).symm a)
      ((ExteriorAlgebra.baseChangeEquiv ℝ V ℂ).symm b)

/-- **Degree-`k` comparison of the complexified wedge-basis form**: for every ordered orthonormal
basis `e` of `V`, the restriction of the Hermitian form of
`(e.toBasis.baseChange ℂ).ExteriorAlgebra` to `⋀[ℂ]^k (ℂ ⊗[ℝ] V)` is
`LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V))` along
`TauCeti.exteriorPower.equivBaseChange ℂ k`. -/
theorem toLinearMapₛₗ₂_baseChange_exteriorAlgebra_coe_coe
    {I : Type*} [Fintype I] [LinearOrder I] (e : OrthonormalBasis I ℝ V) {k : ℕ}
    (a b : ⋀[ℂ]^k (ℂ ⊗[ℝ] V)) :
    toLinearMapₛₗ₂ (starRingEnd ℂ) (e.toBasis.baseChange ℂ).ExteriorAlgebra
        (e.toBasis.baseChange ℂ).ExteriorAlgebra (1 : Matrix (Finset I) (Finset I) ℂ) a b =
      LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V))
        (TauCeti.exteriorPower.equivBaseChange ℂ k a)
        (TauCeti.exteriorPower.equivBaseChange ℂ k b) := by
  rw [toLinearMapₛₗ₂_baseChange_exteriorAlgebra e,
    sesqComplexification_gramBilinForm_baseChangeEquiv_symm_coe_coe]

/-- **Complexified Gram-determinant formula**: on decomposable `k`-vectors of `ℂ ⊗[ℝ] V`,
`(gramBilinForm V).sesqComplexification` pulled back along
`(ExteriorAlgebra.baseChangeEquiv ℝ V ℂ).symm` evaluates as the `k × k` determinant of
`LinearMap.BilinForm.sesqComplexification (innerₗ V)`. -/
theorem sesqComplexification_gramBilinForm_baseChangeEquiv_symm_ιMulti_ιMulti
    (k : ℕ) (x y : Fin k → ℂ ⊗[ℝ] V) :
    (gramBilinForm V).sesqComplexification
        ((ExteriorAlgebra.baseChangeEquiv ℝ V ℂ).symm
          (ExteriorAlgebra.ιMulti ℂ k x))
        ((ExteriorAlgebra.baseChangeEquiv ℝ V ℂ).symm
          (ExteriorAlgebra.ιMulti ℂ k y)) =
      (Matrix.of fun i j ↦
        LinearMap.BilinForm.sesqComplexification (innerₗ V) (x i) (y j)).det := by
  let e := stdOrthonormalBasis ℝ V
  have he : toLinearMapₛₗ₂ (starRingEnd ℂ) (e.toBasis.baseChange ℂ) (e.toBasis.baseChange ℂ)
      (1 : Matrix (Fin (finrank ℝ V)) (Fin (finrank ℝ V)) ℂ) =
        LinearMap.BilinForm.sesqComplexification (innerₗ V) := by
    refine LinearMap.ext_basis (e.toBasis.baseChange ℂ) (e.toBasis.baseChange ℂ) fun i j ↦ ?_
    rw [toLinearMapₛₗ₂_apply_basis, Matrix.one_apply, Basis.baseChange_apply,
      Basis.baseChange_apply]
    simp only [LinearMap.BilinForm.sesqComplexification_tmul_tmul, map_one, one_mul,
      innerₗ_apply_apply, e.coe_toBasis, orthonormal_iff_ite.mp e.orthonormal i j]
    split_ifs <;> simp
  rw [← toLinearMapₛₗ₂_baseChange_exteriorAlgebra e,
    ExteriorAlgebra.toLinearMapₛₗ₂_ιMulti_ιMulti, he]

end Complexification

end ExteriorAlgebra
