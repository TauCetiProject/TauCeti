/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis
public import TauCeti.LinearAlgebra.BilinearForm.Complexification
public import TauCeti.LinearAlgebra.CliffordAlgebra.Complexification
public import TauCeti.LinearAlgebra.ExteriorAlgebra.HermitianMetric
public import TauCeti.RepresentationTheory.Spin.Polarization.Fock.Basic
import Mathlib.Tactic.LinearCombination
import TauCeti.Geometry.Symplectic.Complex.HermitianForm
-- Private: `isSymm_polarBilin` and the polar form of `Q v = -‖v‖²` are used only inside proofs.
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis
import TauCeti.LinearAlgebra.QuadraticForm.Basic

/-!
# The Hermitian metric of the normalized Fock module

Let `Q` be a nondegenerate quadratic form on a finite-dimensional real vector space `V` and `J` an
almost complex structure preserving `Q`, with holomorphic polarization summand
`W = (J.spinPolarizationData hQJ hQ).W`. Without choosing a basis or assuming `Q` is negative
definite, `Q` induces on `W` the intrinsic Hermitian form

  `J.fockPolarForm hQJ hQ x y = -(1/2) polar Q_ℂ (conj x, y)`,

conjugate-linear in `x` and linear in `y`, where `conj x = TauCeti.tmulConj V x` lies in the
`-i`-eigenspace `W'`. In the geometric convention `Q (v) = -g (v, v)` for a symmetric real bilinear
form `g`, this form is the restriction to `W` of the sesquilinear complexification
`g.sesqComplexification`.

Applying `LinearMap.exteriorAlgebraGram` to `J.fockPolarForm hQJ hQ` yields the basis-free Hermitian
metric `J.fockGramForm hQJ hQ` on the spinor module `⋀ W`:

* **Degree orthogonality and Gram-determinant formula**: `⋀[ℂ]^p W` and `⋀[ℂ]^q W` are orthogonal
  whenever `p ≠ q`, and in every degree `p` (including `p = 0`, where the empty determinant is `1`,
  and top degree), `J.fockGramForm hQJ hQ` sends `(x₀ ∧ ⋯ ∧ x_{p-1})` and `(y₀ ∧ ⋯ ∧ y_{p-1})` to
  `det (J.fockPolarForm hQJ hQ (xᵢ, yⱼ))`.
* **Basis-free `*`-representation**: **the normalized Fock action is a `*`-representation** for
  `J.fockGramForm hQJ hQ` with respect to `CliffordAlgebra.conjStar`, its restriction to the real
  Clifford algebra is one for Clifford conjugation, and Clifford multiplication by a real vector is
  skew-Hermitian. The underlying statement is the adjointness of creation and annihilation:
  exterior multiplication by `x ∈ W` is adjoint to `-(1/2)` times the contraction
  `TauCeti.SpinPolarizationData.contract` against `conj x ∈ W'`. Since the normalized Fock action
  is `c(x) = √2 ε(x)` on `W` and `c(y) = (1/√2)` times contraction on `W'`, both halves of
  `c(v) = √2 (ε(v^(1,0)) - ι(v^(0,1)))` carry the same factor.
* **Agreement with the wedge-basis metric**: for any basis `b` of `W` orthonormal for
  `J.fockPolarForm` (meaning `polar Q_ℂ (conj bᵢ, bⱼ) = -2 δᵢⱼ`), the Hermitian form on `W` making
  `b` orthonormal equals `J.fockPolarForm hQJ hQ` and the Hermitian form on `⋀ W` making the
  increasing wedge basis of `b` orthonormal equals `J.fockGramForm hQJ hQ`, so in particular
  neither depends on the orthonormal basis.

The unnormalized native action `TauCeti.spinAction`, which is `ε(v^(1,0)) - 2 ι(v^(0,1))`, is
instead a `*`-representation for the pullback of `J.fockGramForm` along the degree scaling `T` by
`√2` (`2 ^ p` times `J.fockGramForm` on `⋀[ℂ]^p W`), and fails to be skew-Hermitian for
`J.fockGramForm` itself whenever `Q v ≠ 0`
(`TauCeti.AlmostComplexStructure.not_forall_fockGramForm_spinAction_ι_one_tmul_left`).

For a Euclidean space with `Q (v) = -‖v‖²` and an orthogonal complex structure, orthonormal bases
of `W` exist: `√2 u₁^(1,0), …, √2 u_ℓ^(1,0)` for an adapted orthonormal basis
`(u₁, J u₁, …, u_ℓ, J u_ℓ)` of `V`.

## Main definitions

* `TauCeti.AlmostComplexStructure.fockPolarForm`: the intrinsic Hermitian form
  `-(1/2) polar Q_ℂ (conj x, y)` on `W`.
* `TauCeti.AlmostComplexStructure.fockGramForm`: its exterior Gram metric on `⋀ W`.

## Main results

* `TauCeti.AlmostComplexStructure.fockPolarForm_eq_sesqComplexification`: under `Q v = -g v v`,
  `J.fockPolarForm` agrees with `g.sesqComplexification` on `W`.
* `TauCeti.AlmostComplexStructure.fockGramForm_eq_zero_of_mem_exteriorPower`,
  `TauCeti.AlmostComplexStructure.fockGramForm_ιMulti`, and
  `TauCeti.AlmostComplexStructure.fockGramForm_ιMulti_eq_det_sesqComplexification`: degree
  orthogonality and the Gram-determinant formula on `⋀ W`.
* `TauCeti.AlmostComplexStructure.fockGramForm_wedge_left`,
  `TauCeti.AlmostComplexStructure.fockGramForm_contract_left`,
  `TauCeti.AlmostComplexStructure.fockGramForm_fockAction_left`,
  `TauCeti.AlmostComplexStructure.fockGramForm_fockAction_ι_one_tmul_left`,
  `TauCeti.AlmostComplexStructure.fockGramForm_realFockAction_left`, and
  `TauCeti.AlmostComplexStructure.fockGramForm_realFockAction_ι_left`: basis-free
  creation/annihilation adjointness, `*`-representation properties, and skew-Hermitian real-vector
  action.
* `TauCeti.AlmostComplexStructure.fockGramForm_degreeScaling_of_mem_exteriorPower`,
  `TauCeti.AlmostComplexStructure.fockGramForm_degreeScaling_spinAction_left`, and
  `TauCeti.AlmostComplexStructure.not_forall_fockGramForm_spinAction_ι_one_tmul_left`: degree-`p`
  factor `2 ^ p` of the native metric, `*`-adjointness of `spinAction` after degree scaling, and
  failure without normalization when `Q v ≠ 0`.
* `TauCeti.AlmostComplexStructure.toLinearMapₛₗ₂_eq_fockPolarForm` and
  `TauCeti.AlmostComplexStructure.toLinearMapₛₗ₂_exteriorAlgebra_eq_fockGramForm`: bridge
  identifications with the coordinate forms of any orthonormal polarization basis.
* `TauCeti.AlmostComplexStructure.exists_basis_polar_tmulConj`: orthonormal bases exist for
  `Q (v) = -‖v‖²`.

## References

* L. Nicolaescu, *Lectures on the Geometry of Manifolds* (online author edition, `Lectures.pdf`),
  §2.2.4 and Proposition 12.1.19.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §5.
* W. Greub, *Multilinear Algebra*, 2nd ed., Springer (1978), Chapter 5.
-/

public section

open CliffordAlgebra LinearMap Matrix Module QuadraticMap
open TauCeti.ExteriorAlgebra
open scoped TensorProduct

namespace TauCeti.AlmostComplexStructure

section PolarAndGram

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (J : AlmostComplexStructure V)
  {Q : QuadraticForm ℝ V} [FiniteDimensional ℝ V] (hQJ : ∀ v, Q (J v) = Q v)
  (hQ : Q.Nondegenerate)

/-! ### The intrinsic Hermitian form on `W` -/

/-- **The intrinsic Hermitian form on the holomorphic polarization `W`**:
`h (x, y) = -(1/2) polar Q_ℂ (conj x, y)`, conjugate-linear in `x` and linear in `y`. -/
noncomputable def fockPolarForm :
    (J.spinPolarizationData hQJ hQ).W →ₗ⋆[ℂ] (J.spinPolarizationData hQJ hQ).W →ₗ[ℂ] ℂ :=
  (-(2 : ℂ)⁻¹) •
    (LinearMap.BilinForm.sesqComplexification Q.polarBilin).domRestrict₁₂
      (J.spinPolarizationData hQJ hQ).W (J.spinPolarizationData hQJ hQ).W

/-- `J.fockPolarForm` is `-(1/2)` times the sesquilinear complexification of `Q.polarBilin`
restricted to `W`. -/
theorem fockPolarForm_eq_neg_inv_two_mul_polarBilin_sesqComplexification
    (x y : (J.spinPolarizationData hQJ hQ).W) :
    J.fockPolarForm hQJ hQ x y =
      -(2 : ℂ)⁻¹ *
        LinearMap.BilinForm.sesqComplexification Q.polarBilin (x : ℂ ⊗[ℝ] V) (y : ℂ ⊗[ℝ] V) := by
  simp [fockPolarForm, domRestrict₁₂_apply]

/-- `J.fockPolarForm` evaluates as `-(1/2) polar Q_ℂ (conj x, y)`. -/
theorem fockPolarForm_apply (x y : (J.spinPolarizationData hQJ hQ).W) :
    J.fockPolarForm hQJ hQ x y =
      -(2 : ℂ)⁻¹ * polar (Q.baseChange ℂ) (tmulConj V x) y := by
  rw [fockPolarForm_eq_neg_inv_two_mul_polarBilin_sesqComplexification,
    LinearMap.BilinForm.sesqComplexification_apply, ← QuadraticForm.polarBilin_baseChange,
    polarBilin_apply_apply]

/-- Swapping the arguments of `J.fockPolarForm` conjugates its value. -/
theorem star_fockPolarForm_apply (x y : (J.spinPolarizationData hQJ hQ).W) :
    star (J.fockPolarForm hQJ hQ x y) = J.fockPolarForm hQJ hQ y x := by
  have hsymm : (LinearMap.BilinForm.sesqComplexification Q.polarBilin).IsSymm :=
    Q.isSymm_polarBilin.sesqComplexification
  rw [fockPolarForm_eq_neg_inv_two_mul_polarBilin_sesqComplexification,
    fockPolarForm_eq_neg_inv_two_mul_polarBilin_sesqComplexification, ← starRingEnd_apply,
    map_mul, hsymm.eq x y, map_neg, map_inv₀, map_ofNat]

/-- **The intrinsic form `J.fockPolarForm` on `W` is Hermitian.** -/
theorem isSymm_fockPolarForm : (J.fockPolarForm hQJ hQ).IsSymm := by
  rw [LinearMap.isSymm_def]
  intro x y
  rw [starRingEnd_apply, J.star_fockPolarForm_apply hQJ hQ]

/-- **Agreement with `g.sesqComplexification` in the geometric convention**: when `Q v = -g v v`
for a symmetric real bilinear form `g`, `J.fockPolarForm` is the restriction of
`g.sesqComplexification` to `W`. -/
theorem fockPolarForm_eq_sesqComplexification {g : LinearMap.BilinForm ℝ V} (hg : g.IsSymm)
    (hQg : ∀ v, Q v = -g v v) (x y : (J.spinPolarizationData hQJ hQ).W) :
    J.fockPolarForm hQJ hQ x y = g.sesqComplexification (x : ℂ ⊗[ℝ] V) (y : ℂ ⊗[ℝ] V) := by
  rw [fockPolarForm_apply,
    QuadraticForm.polar_baseChange_tmulConj_eq_two_mul_sesqComplexification hg.neg
      (fun v ↦ by simp [hQg v]),
    LinearMap.BilinForm.sesqComplexification_neg, LinearMap.neg_apply, LinearMap.neg_apply]
  ring

/-- On `(1,0)`-parts, `J.fockPolarForm` pairs `v^(1,0)` with itself to `-(1/2) Q v`. -/
theorem fockPolarForm_holomorphicPart_self (v : V) :
    J.fockPolarForm hQJ hQ
        ⟨J.holomorphicPart v, J.holomorphicPart_mem_spinPolarizationData_W hQJ hQ v⟩
        ⟨J.holomorphicPart v, J.holomorphicPart_mem_spinPolarizationData_W hQJ hQ v⟩ =
      -(2 : ℂ)⁻¹ * (Q v : ℂ) := by
  rw [fockPolarForm_eq_neg_inv_two_mul_polarBilin_sesqComplexification]
  dsimp only
  rw [J.sesqComplexification_holomorphicPart_self Q.isSymm_polarBilin (J.polar_apply_apply hQJ) v,
    polarBilin_apply_apply, polar_self]
  push_cast
  ring

/-! ### The basis-free Fock Gram metric and its Gram-determinant formula -/

/-- **The basis-free Fock Gram metric** on the spinor module `⋀ W`: the exterior Gram form of
`J.fockPolarForm hQJ hQ`. -/
noncomputable def fockGramForm :
    ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W →ₗ⋆[ℂ]
      ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W →ₗ[ℂ] ℂ :=
  (J.fockPolarForm hQJ hQ).exteriorAlgebraGram

/-- `J.fockGramForm` unfolds to `(J.fockPolarForm hQJ hQ).exteriorAlgebraGram`. -/
theorem fockGramForm_def :
    J.fockGramForm hQJ hQ = (J.fockPolarForm hQJ hQ).exteriorAlgebraGram := by
  simp [fockGramForm]

/-- **The Fock Gram metric is Hermitian.** -/
theorem isSymm_fockGramForm : (J.fockGramForm hQJ hQ).IsSymm :=
  (J.isSymm_fockPolarForm hQJ hQ).exteriorAlgebraGram

/-- Swapping the arguments of `J.fockGramForm` conjugates its value. -/
theorem star_fockGramForm_apply (s t : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W) :
    star (J.fockGramForm hQJ hQ s t) = J.fockGramForm hQJ hQ t s := by
  rw [← starRingEnd_apply, (J.isSymm_fockGramForm hQJ hQ).eq]

/-- The vacuum `1 ∈ ⋀ W` has unit Gram self-pairing. -/
theorem fockGramForm_one_one : J.fockGramForm hQJ hQ 1 1 = 1 := by
  simp [fockGramForm_def]

/-- Pairing the vacuum on the left extracts the constant term. -/
@[simp]
theorem fockGramForm_one_left (t : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W) :
    J.fockGramForm hQJ hQ 1 t = _root_.ExteriorAlgebra.algebraMapInv t := by
  simp [fockGramForm_def]

/-- Pairing the vacuum on the right conjugates the constant term. -/
@[simp]
theorem fockGramForm_one_right (s : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W) :
    J.fockGramForm hQJ hQ s 1 = star (_root_.ExteriorAlgebra.algebraMapInv s) := by
  simp [fockGramForm_def]

/-- On degree-one generators, `J.fockGramForm` recovers `J.fockPolarForm`. -/
@[simp]
theorem fockGramForm_ι_ι (x y : (J.spinPolarizationData hQJ hQ).W) :
    J.fockGramForm hQJ hQ (_root_.ExteriorAlgebra.ι ℂ x) (_root_.ExteriorAlgebra.ι ℂ y) =
      J.fockPolarForm hQJ hQ x y := by
  simp [fockGramForm_def]

/-- **Distinct exterior degrees are orthogonal** for `J.fockGramForm` on all of `⋀ W`. -/
theorem fockGramForm_eq_zero_of_mem_exteriorPower {p q : ℕ} (hpq : p ≠ q)
    {s t : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W}
    (hs : s ∈ ⋀[ℂ]^p (J.spinPolarizationData hQJ hQ).W)
    (ht : t ∈ ⋀[ℂ]^q (J.spinPolarizationData hQJ hQ).W) :
    J.fockGramForm hQJ hQ s t = 0 :=
  (J.fockPolarForm hQJ hQ).exteriorAlgebraGram_eq_zero_of_mem_exteriorPower hpq hs ht

/-- **The Gram-determinant formula for the Fock metric** in every degree `p` (including `p = 0`,
where the empty determinant is `1`, and top degree):
`J.fockGramForm (x₀ ∧ ⋯ ∧ x_{p-1}) (y₀ ∧ ⋯ ∧ y_{p-1}) = det (J.fockPolarForm (xᵢ, yⱼ))`. -/
@[simp↓]
theorem fockGramForm_ιMulti {p : ℕ} (x y : Fin p → (J.spinPolarizationData hQJ hQ).W) :
    J.fockGramForm hQJ hQ (_root_.ExteriorAlgebra.ιMulti ℂ p x)
        (_root_.ExteriorAlgebra.ιMulti ℂ p y) =
      (Matrix.of fun i j ↦ J.fockPolarForm hQJ hQ (x i) (y j)).det := by
  rw [fockGramForm_def, exteriorAlgebraGram_ιMulti]

/-- **The Gram-determinant formula in terms of `g.sesqComplexification`** under the geometric
convention `Q v = -g v v`. -/
theorem fockGramForm_ιMulti_eq_det_sesqComplexification {g : LinearMap.BilinForm ℝ V}
    (hg : g.IsSymm) (hQg : ∀ v, Q v = -g v v) {p : ℕ}
    (x y : Fin p → (J.spinPolarizationData hQJ hQ).W) :
    J.fockGramForm hQJ hQ (_root_.ExteriorAlgebra.ιMulti ℂ p x)
        (_root_.ExteriorAlgebra.ιMulti ℂ p y) =
      (Matrix.of fun i j ↦ g.sesqComplexification (x i : ℂ ⊗[ℝ] V) (y j : ℂ ⊗[ℝ] V)).det := by
  rw [fockGramForm_ιMulti]
  congr 1
  ext i j
  exact J.fockPolarForm_eq_sesqComplexification hQJ hQ hg hQg (x i) (y j)

/-! ### Basis-free `*`-representation and skew-Hermitian real-vector action -/

/-- The polarization pairing with `conj x ∈ W'` is `-2` times `J.fockPolarForm x`. -/
private theorem pairingEquiv_tmulConj_eq_fockPolarForm (x : (J.spinPolarizationData hQJ hQ).W) :
    (J.spinPolarizationData hQJ hQ).pairingEquiv
        ⟨tmulConj V x, J.tmulConj_mem_spinPolarizationData_W' hQJ hQ x.property⟩ =
      (-2 : ℂ) • J.fockPolarForm hQJ hQ x := by
  refine LinearMap.ext fun y ↦ ?_
  rw [SpinPolarizationData.pairingEquiv_apply, polar_comm, LinearMap.smul_apply,
    fockPolarForm_apply, smul_eq_mul, ← mul_assoc]
  norm_num

/-- **Creation is adjoint to annihilation** for the basis-free Fock Gram metric. -/
theorem fockGramForm_wedge_left (x : (J.spinPolarizationData hQJ hQ).W)
    (s t : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W) :
    J.fockGramForm hQJ hQ ((J.spinPolarizationData hQJ hQ).wedge x s) t =
      J.fockGramForm hQJ hQ s
        ((-(2 : ℂ)⁻¹) • (J.spinPolarizationData hQJ hQ).contract
          ⟨tmulConj V x, J.tmulConj_mem_spinPolarizationData_W' hQJ hQ x.property⟩ t) := by
  rw [fockGramForm_def, SpinPolarizationData.wedge_apply, exteriorAlgebraGram_ι_mul_left,
    SpinPolarizationData.contract_apply, J.pairingEquiv_tmulConj_eq_fockPolarForm hQJ hQ]
  simp only [map_smul, LinearMap.smul_apply, smul_smul]
  norm_num

/-- **Annihilation is adjoint to creation** for the basis-free Fock Gram metric. -/
theorem fockGramForm_contract_left (y : (J.spinPolarizationData hQJ hQ).W')
    (s t : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W) :
    J.fockGramForm hQJ hQ ((J.spinPolarizationData hQJ hQ).contract y s) t =
      J.fockGramForm hQJ hQ s
        ((-2 : ℂ) • (J.spinPolarizationData hQJ hQ).wedge
          ⟨tmulConj V y, J.tmulConj_mem_spinPolarizationData_W hQJ hQ y.property⟩ t) := by
  obtain ⟨x, rfl⟩ : ∃ x : (J.spinPolarizationData hQJ hQ).W,
      ⟨tmulConj V x, J.tmulConj_mem_spinPolarizationData_W' hQJ hQ x.property⟩ = y :=
    ⟨⟨tmulConj V y, J.tmulConj_mem_spinPolarizationData_W hQJ hQ y.property⟩,
      Subtype.ext (tmulConj_tmulConj V y)⟩
  have hx : (⟨tmulConj V (tmulConj V (x : ℂ ⊗[ℝ] V)),
      J.tmulConj_mem_spinPolarizationData_W hQJ hQ
        (J.tmulConj_mem_spinPolarizationData_W' hQJ hQ x.property)⟩ :
      (J.spinPolarizationData hQJ hQ).W) = x :=
    Subtype.ext (tmulConj_tmulConj V x)
  rw [hx, fockGramForm_def, SpinPolarizationData.contract_apply,
    J.pairingEquiv_tmulConj_eq_fockPolarForm hQJ hQ, SpinPolarizationData.wedge_apply]
  have hright := (J.fockPolarForm hQJ hQ).exteriorAlgebraGram_ι_mul_right
    (fun z ↦ (J.isSymm_fockPolarForm hQJ hQ).eq x z)
  simp only [map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hright, smul_eq_mul,
    map_neg, map_ofNat]

/-- `*`-adjointness of `J.fockAction` on holomorphic generators `x ∈ W`. -/
private theorem fockGramForm_fockAction_ι_coe_W_left (x : (J.spinPolarizationData hQJ hQ).W)
    (s t : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W) :
    J.fockGramForm hQJ hQ
        (J.fockAction hQJ hQ (CliffordAlgebra.ι (Q.baseChange ℂ) (x : ℂ ⊗[ℝ] V)) s) t =
      J.fockGramForm hQJ hQ s
        (J.fockAction hQJ hQ
          (conjStar Q (CliffordAlgebra.ι (Q.baseChange ℂ) (x : ℂ ⊗[ℝ] V))) t) := by
  have hx : tmulConj V (x : ℂ ⊗[ℝ] V) =
      ((⟨tmulConj V x, J.tmulConj_mem_spinPolarizationData_W' hQJ hQ x.property⟩ :
        (J.spinPolarizationData hQJ hQ).W') : ℂ ⊗[ℝ] V) :=
    (Subtype.coe_mk _ _).symm
  rw [conjStar_ι, map_neg, hx, fockAction_ι_coe_W', fockAction_ι_coe_W]
  simp only [LinearMap.smul_apply, LinearMap.neg_apply, LinearMap.map_smulₛₗ, map_smul, map_neg,
    J.fockGramForm_wedge_left hQJ hQ, Complex.conj_ofReal, smul_eq_mul,
    ← Complex.ofReal_inv, ← Real.sqrt_div_self, Complex.ofReal_div, Complex.ofReal_ofNat]
  ring

/-- `*`-adjointness of `J.fockAction` on antiholomorphic generators `y ∈ W'`. -/
private theorem fockGramForm_fockAction_ι_coe_W'_left (y : (J.spinPolarizationData hQJ hQ).W')
    (s t : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W) :
    J.fockGramForm hQJ hQ
        (J.fockAction hQJ hQ (CliffordAlgebra.ι (Q.baseChange ℂ) (y : ℂ ⊗[ℝ] V)) s) t =
      J.fockGramForm hQJ hQ s
        (J.fockAction hQJ hQ
          (conjStar Q (CliffordAlgebra.ι (Q.baseChange ℂ) (y : ℂ ⊗[ℝ] V))) t) := by
  have hy : tmulConj V (y : ℂ ⊗[ℝ] V) =
      ((⟨tmulConj V y, J.tmulConj_mem_spinPolarizationData_W hQJ hQ y.property⟩ :
        (J.spinPolarizationData hQJ hQ).W) : ℂ ⊗[ℝ] V) :=
    (Subtype.coe_mk _ _).symm
  rw [conjStar_ι, map_neg, hy, fockAction_ι_coe_W', fockAction_ι_coe_W]
  simp only [LinearMap.smul_apply, LinearMap.neg_apply, LinearMap.map_smulₛₗ, map_smul, map_neg,
    J.fockGramForm_contract_left hQJ hQ, ← Complex.ofReal_inv, ← Real.sqrt_div_self,
    Complex.ofReal_div, Complex.ofReal_ofNat, map_div₀, Complex.conj_ofReal, map_ofNat, smul_eq_mul]
  ring

/-- **The normalized Fock action is a `*`-representation for the basis-free Fock Gram metric**:
`J.fockGramForm (c(a) s) t = J.fockGramForm s (c(a^*) t)` without choosing a basis or assuming `Q`
is negative definite. -/
theorem fockGramForm_fockAction_left (a : CliffordAlgebra (Q.baseChange ℂ))
    (s t : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W) :
    J.fockGramForm hQJ hQ (J.fockAction hQJ hQ a s) t =
      J.fockGramForm hQJ hQ s (J.fockAction hQJ hQ (conjStar Q a) t) := by
  induction a using CliffordAlgebra.induction generalizing s t with
  | algebraMap r =>
    simp only [conjStar_algebraMap, AlgHom.commutes, Module.algebraMap_end_apply, map_smulₛₗ,
      LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
  | ι w =>
    obtain ⟨⟨⟨x, y⟩, z⟩, rfl⟩ := (J.spinPolarizationData hQJ hQ).decompositionEquiv.surjective w
    have hz : (z : ℂ ⊗[ℝ] V) = 0 := by
      have := z.property
      simpa only [spinPolarizationData_line, Submodule.mem_bot] using this
    rw [SpinPolarizationData.decompositionEquiv_apply]
    dsimp only
    rw [hz, add_zero]
    simp only [map_add, LinearMap.add_apply, J.fockGramForm_fockAction_ι_coe_W_left hQJ hQ,
      J.fockGramForm_fockAction_ι_coe_W'_left hQJ hQ]
  | add a a' ha ha' => simp only [map_add, LinearMap.add_apply, ha, ha']
  | mul a a' ha ha' =>
    simp only [conjStar_mul, map_mul, _root_.mul_apply_eq_comp]
    rw [ha, ha']

/-- **Real vectors act skew-Hermitianly for the Fock Gram metric**:
`J.fockGramForm (c(v) s) t = -J.fockGramForm s (c(v) t)`. -/
theorem fockGramForm_fockAction_ι_one_tmul_left (v : V)
    (s t : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W) :
    J.fockGramForm hQJ hQ
        (J.fockAction hQJ hQ (CliffordAlgebra.ι (Q.baseChange ℂ) ((1 : ℂ) ⊗ₜ v)) s) t =
      -J.fockGramForm hQJ hQ s
        (J.fockAction hQJ hQ (CliffordAlgebra.ι (Q.baseChange ℂ) ((1 : ℂ) ⊗ₜ v)) t) := by
  rw [J.fockGramForm_fockAction_left hQJ hQ, conjStar_ι_tmul, map_one (starRingEnd ℂ),
    map_neg, LinearMap.neg_apply, map_neg]

/-- **The real Fock action is a `*`-representation for Clifford conjugation** with respect to
`J.fockGramForm`. -/
theorem fockGramForm_realFockAction_left (a : CliffordAlgebra Q)
    (s t : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W) :
    J.fockGramForm hQJ hQ (J.realFockAction hQJ hQ a s) t =
      J.fockGramForm hQJ hQ s (J.realFockAction hQJ hQ (star a) t) := by
  rw [realFockAction_apply, realFockAction_apply, J.fockGramForm_fockAction_left hQJ hQ,
    conjStar_ofBaseChangeAux]

/-- **Every real Clifford generator `ι Q v` acts skew-Hermitianly** for `J.fockGramForm`. -/
theorem fockGramForm_realFockAction_ι_left (v : V)
    (s t : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W) :
    J.fockGramForm hQJ hQ (J.realFockAction hQJ hQ (CliffordAlgebra.ι Q v) s) t =
      -J.fockGramForm hQJ hQ s (J.realFockAction hQJ hQ (CliffordAlgebra.ι Q v) t) := by
  rw [J.fockGramForm_realFockAction_left hQJ hQ, star_ι, map_neg, LinearMap.neg_apply, map_neg]

/-- On `⋀[ℂ]^p W`, the pullback of `J.fockGramForm` along the degree scaling by `√2` rescales by
`2 ^ p`. -/
theorem fockGramForm_degreeScaling_of_mem_exteriorPower {r : ℂˣ} (hr : (r : ℂ) = Real.sqrt 2)
    {p : ℕ} {s : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W}
    (hs : s ∈ ⋀[ℂ]^p (J.spinPolarizationData hQJ hQ).W)
    (t : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W) :
    J.fockGramForm hQJ hQ (degreeScaling r s) (degreeScaling r t) =
      2 ^ p * J.fockGramForm hQJ hQ s t := by
  have h2 : (starRingEnd ℂ) (r : ℂ) * r = 2 := by
    rw [hr, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt zero_le_two,
      Complex.ofReal_ofNat]
  rw [fockGramForm_def,
    (J.fockPolarForm hQJ hQ).exteriorAlgebraGram_degreeScaling_degreeScaling_of_mem_exteriorPower
      r hs, h2]

/-- The unnormalized native action `spinAction` is a `*`-representation for the pullback of
`J.fockGramForm` along the degree scaling by `√2`. -/
theorem fockGramForm_degreeScaling_spinAction_left {r : ℂˣ} (hr : (r : ℂ) = Real.sqrt 2)
    (a : CliffordAlgebra (Q.baseChange ℂ))
    (s t : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W) :
    J.fockGramForm hQJ hQ
        (degreeScaling r (spinAction _ (J.spinPolarizationData hQJ hQ) a s)) (degreeScaling r t) =
      J.fockGramForm hQJ hQ (degreeScaling r s)
        (degreeScaling r (spinAction _ (J.spinPolarizationData hQJ hQ) (conjStar Q a) t)) := by
  have hT (b : CliffordAlgebra (Q.baseChange ℂ))
      (x : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W) :
      degreeScaling r (spinAction _ (J.spinPolarizationData hQJ hQ) b x) =
        J.fockAction hQJ hQ b (degreeScaling r x) :=
    LinearMap.congr_fun (J.degreeScaling_comp_spinAction_eq_fockAction_comp hQJ hQ hr b) x
  rw [hT, hT, J.fockGramForm_fockAction_left hQJ hQ]

/-- Whenever `Q v ≠ 0`, the unnormalized native action `spinAction (ι (1 ⊗ v))` is not
skew-Hermitian for `J.fockGramForm`. -/
theorem not_forall_fockGramForm_spinAction_ι_one_tmul_left {v : V} (hv : Q v ≠ 0) :
    ¬ ∀ s t : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W,
      J.fockGramForm hQJ hQ
          (spinAction _ (J.spinPolarizationData hQJ hQ)
            (CliffordAlgebra.ι (Q.baseChange ℂ) ((1 : ℂ) ⊗ₜ v)) s) t =
        -J.fockGramForm hQJ hQ s
          (spinAction _ (J.spinPolarizationData hQJ hQ)
            (CliffordAlgebra.ι (Q.baseChange ℂ) ((1 : ℂ) ⊗ₜ v)) t) := by
  intro hskew
  -- Evaluate the skew-Hermitian identity on `s = 1` and `t = ι w` with `w = v^(1,0)`.
  let w : (J.spinPolarizationData hQJ hQ).W :=
    ⟨J.holomorphicPart v, J.holomorphicPart_mem_spinPolarizationData_W hQJ hQ v⟩
  have h := hskew 1 (_root_.ExteriorAlgebra.ι ℂ w)
  rw [J.spinAction_ι_one_tmul_apply_one hQJ hQ v,
    J.spinAction_ι_one_tmul_apply_ι_holomorphicPart hQJ hQ v, fockGramForm_ι_ι,
    J.fockPolarForm_holomorphicPart_self hQJ hQ v, map_smul, fockGramForm_one_one,
    smul_eq_mul, mul_one] at h
  have hQv : (Q v : ℂ) = 0 := by linear_combination 2 * h
  exact hv (Complex.ofReal_eq_zero.mp hQv)

end PolarAndGram

section Metric

/-! ### Orthonormal polarization bases and the wedge-basis metric -/

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (J : AlmostComplexStructure V)
  {Q : QuadraticForm ℝ V} [FiniteDimensional ℝ V] (hQJ : ∀ v, Q (J v) = Q v)
  (hQ : Q.Nondegenerate)

section BasisW

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : Basis ι ℂ (J.spinPolarizationData hQJ hQ).W)
  (hb : ∀ i j, polar (Q.baseChange ℂ) (tmulConj V (b i : ℂ ⊗[ℝ] V)) (b j) =
    if i = j then -2 else 0)
include hb

/-- Any basis `b` of `W` with `polar Q_ℂ (conj bᵢ, bⱼ) = -2 δᵢⱼ` has `J.fockPolarForm` as its
orthonormal Hermitian form. -/
theorem toLinearMapₛₗ₂_eq_fockPolarForm :
    toLinearMapₛₗ₂ (starRingEnd ℂ) b b (1 : Matrix ι ι ℂ) = J.fockPolarForm hQJ hQ := by
  refine LinearMap.ext_basis b b fun i j ↦ ?_
  rw [toLinearMapₛₗ₂_apply_basis, Matrix.one_apply, fockPolarForm_apply, hb]
  split_ifs <;> norm_num

end BasisW

variable {ι : Type*} [Fintype ι] [LinearOrder ι]
  (b : Basis ι ℂ (J.spinPolarizationData hQJ hQ).W)
  (hb : ∀ i j, polar (Q.baseChange ℂ) (tmulConj V (b i : ℂ ⊗[ℝ] V)) (b j) =
    if i = j then -2 else 0)
include hb

/-- **For any orthonormal basis `b` of `W`, the wedge-basis Hermitian form on `⋀ W` is
`J.fockGramForm`.** -/
theorem toLinearMapₛₗ₂_exteriorAlgebra_eq_fockGramForm :
    toLinearMapₛₗ₂ (starRingEnd ℂ) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset ι) (Finset ι) ℂ) =
      J.fockGramForm hQJ hQ := by
  rw [b.toLinearMapₛₗ₂_exteriorAlgebra_eq_exteriorAlgebraGram,
    J.toLinearMapₛₗ₂_eq_fockPolarForm hQJ hQ b hb, fockGramForm_def]

end Metric

section Existence

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (J : AlmostComplexStructure V) {Q : QuadraticForm ℝ V} (hQJ : ∀ v, Q (J v) = Q v)
  (hQnd : Q.Nondegenerate)

/-- **Orthonormal bases of `W` exist** for the geometric form `Q (v) = -‖v‖²` of a Euclidean space
of dimension `2ℓ`: there is a basis `b` of `W` with `polar Q_ℂ (conj bᵢ, bⱼ) = -2 δᵢⱼ`, namely
`bₖ = √2 uₖ^(1,0)` for an orthonormal basis `(u₁, J u₁, …, u_ℓ, J u_ℓ)` of `V` adapted to `J`. -/
theorem exists_basis_polar_tmulConj (hQ : ∀ v, Q v = -‖v‖ ^ 2) (ℓ : ℕ)
    (hdim : finrank ℝ V = 2 * ℓ) :
    ∃ b : Basis (Fin ℓ) ℂ (J.spinPolarizationData hQJ hQnd).W,
      ∀ i j, polar (Q.baseChange ℂ) (tmulConj V (b i : ℂ ⊗[ℝ] V)) (b j) =
        if i = j then -2 else 0 := by
  have hJ (v : V) : ‖J v‖ = ‖v‖ := by
    have h := hQJ v
    rw [hQ, hQ, neg_inj] at h
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h
  have hpolar := QuadraticMap.polar_eq_neg_two_inner hQ
  obtain ⟨u, hu⟩ := J.exists_adapted_orthonormalBasis hJ ℓ hdim
  have hinner (a c : Fin (2 * ℓ)) : ⟪u a, u c⟫ = if a = c then 1 else 0 :=
    orthonormal_iff_ite.mp u.orthonormal a c
  let w : Fin ℓ → (J.spinPolarizationData hQJ hQnd).W := fun k ↦
    (Real.sqrt 2 : ℂ) • ⟨J.holomorphicPart (u ⟨2 * k, by omega⟩),
      J.holomorphicPart_mem_spinPolarizationData_W hQJ hQnd _⟩
  have hw (i j : Fin ℓ) : polar (Q.baseChange ℂ) (tmulConj V (w i : ℂ ⊗[ℝ] V)) (w j) =
      if i = j then -2 else 0 := by
    have hsqrt : (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt zero_le_two, Complex.ofReal_ofNat]
    simp only [w, Submodule.coe_smul, map_smulₛₗ, Complex.conj_ofReal, tmulConj_holomorphicPart,
      polar_smul_left, polar_smul_right, smul_eq_mul]
    rw [polar_comm, J.polar_holomorphicPart_antiholomorphicPart hQJ, ← hu i, hpolar, hpolar,
      hinner, hinner]
    -- The basis vectors `u (2 j)` and `u (2 i + 1)` are distinct, and `u (2 j) = u (2 i)` only
    -- for `i = j`.
    have h₁ : (⟨2 * j, by omega⟩ : Fin (2 * ℓ)) = ⟨2 * i + 1, by omega⟩ ↔ False := by
      simp only [Fin.mk.injEq, iff_false]
      omega
    have h₂ : (⟨2 * j, by omega⟩ : Fin (2 * ℓ)) = ⟨2 * i, by omega⟩ ↔ i = j := by
      simp only [Fin.ext_iff]
      omega
    simp only [h₁, h₂, ite_false]
    split_ifs
    · push_cast
      linear_combination (-1 : ℂ) * hsqrt
    · push_cast
      ring
  have hli : LinearIndependent ℂ w := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have h := congrArg (((Q.baseChange ℂ).polarBilin (tmulConj V (w i : ℂ ⊗[ℝ] V))).comp
      (J.spinPolarizationData hQJ hQnd).W.subtype) hg
    simp only [map_sum, map_smul, LinearMap.comp_apply, Submodule.subtype_apply,
      polarBilin_apply_apply, hw, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, hi,
      ite_true, map_zero] at h
    simpa using h
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' w hli ?_, fun i j ↦ ?_⟩
  · rw [Fintype.card_fin, finrank_spinPolarizationData_W, hdim]
    omega
  · simp only [basisOfLinearIndependentOfCardEqFinrank', Basis.coe_mk, hw]

end Existence

end TauCeti.AlmostComplexStructure
