/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.HermitianForm
public import TauCeti.RepresentationTheory.Spin.Polarization.Fock.Hilbert

import Mathlib.Tactic.LinearCombination
import TauCeti.Geometry.Symplectic.Finrank

/-!
# The basis-free Fock Gram metric and its Gram-determinant formula

Let `Q` be a nondegenerate quadratic form on a finite-dimensional real vector space `V` and `J` an
almost complex structure preserving `Q`, with holomorphic polarization summand
`W = (J.spinPolarizationData hQJ hQ).W`. Without choosing a basis or assuming `Q` is negative
definite, `Q` induces on `W` the intrinsic Hermitian form

  `J.fockPolarForm hQJ hQ x y = -(1/2) polar Q_ℂ (conj x, y)`,

conjugate-linear in `x` and linear in `y`, where `conj x = TauCeti.tmulConj V x` lies in the
antiholomorphic summand `W'`. In the geometric convention `Q (v) = -g (v, v)` for a symmetric
bilinear form `g`, this form is the restriction to `W` of the sesquilinear complexification
`g.sesqComplexification`.

Applying `LinearMap.exteriorAlgebraGram` to `J.fockPolarForm hQJ hQ` yields the intrinsic
Hermitian form `J.fockGramForm hQJ hQ` on the spinor module `⋀ W`. From the exterior Gram
machinery follow its global properties on `⋀ W`:

* **Degree orthogonality**: `⋀[ℂ]^p W` and `⋀[ℂ]^q W` are orthogonal whenever `p ≠ q`.
* **Gram-determinant formula**: in every degree `p` (including degree zero, where the empty
  determinant is `1`, and top degree),
  `J.fockGramForm hQJ hQ (x₀ ∧ ⋯ ∧ x_{p-1}) (y₀ ∧ ⋯ ∧ y_{p-1}) = det (h_ℂ (xᵢ, yⱼ))`.
* **Basis-free `*`-representation**: `J.fockAction` is a `*`-representation for
  `CliffordAlgebra.conjStar`, `J.realFockAction` is a `*`-representation for real Clifford
  conjugation, and every real vector `v ∈ V` acts skew-Hermitianly.
* **Agreement with the wedge-basis and Hilbert metrics**: for any basis `b` of `W` satisfying
  `polar Q_ℂ (conj bᵢ, bⱼ) = -2 δᵢⱼ`, the wedge-basis form of `b` equals `J.fockGramForm`, and in
  the Euclidean case `Q (v) = -‖v‖²` the native inner product of `fockInnerProductSpace` equals
  `J.fockGramForm`.

Finally, evaluating both actions on the vacuum `1` and `w = v^(1,0)` shows why the `√2`
normalization is required: `realFockAction (ι Q v)` sends `1 ↦ √2 • ι w` and
`ι w ↦ ((√2)⁻¹ * Q v) • 1` so its vacuum-to-degree-one matrix elements cancel, whereas the
unnormalized native action `spinAction` sends `1 ↦ ι w` and `ι w ↦ Q v • 1` and fails to be
skew-Hermitian for `J.fockGramForm` whenever `Q v ≠ 0`.

## Main definitions

* `TauCeti.AlmostComplexStructure.fockPolarForm`: the intrinsic Hermitian form
  `-(1/2) polar Q_ℂ (conj x, y)` on `W`.
* `TauCeti.AlmostComplexStructure.fockGramForm`: its exterior Gram metric on `⋀ W`.

## Main results

* `TauCeti.AlmostComplexStructure.fockPolarForm_eq_sesqComplexification`: under `Q v = -g v v`,
  `J.fockPolarForm` agrees with `g.sesqComplexification` on `W`.
* `TauCeti.AlmostComplexStructure.fockGramForm_eq_zero_of_mem_exteriorPower` and
  `TauCeti.AlmostComplexStructure.fockGramForm_ιMulti`: degree orthogonality and the
  Gram-determinant formula on `⋀ W`.
* `TauCeti.AlmostComplexStructure.fockGramForm_fockAction_left`,
  `TauCeti.AlmostComplexStructure.fockGramForm_realFockAction_left`, and
  `TauCeti.AlmostComplexStructure.fockGramForm_realFockAction_ι_left`: basis-free `*`-adjointness
  and skew-Hermitian real-vector action.
* `TauCeti.AlmostComplexStructure.toLinearMapₛₗ₂_exteriorAlgebra_eq_fockGramForm`,
  `TauCeti.AlmostComplexStructure.inner_fock_eq_fockGramForm`, and
  `TauCeti.AlmostComplexStructure.inner_fock_ιMulti`: agreement with the wedge-basis metric and
  the native Fock inner product, together with the Gram-determinant formula for `inner ℂ`.
* `TauCeti.AlmostComplexStructure.not_skewAdjoint_spinAction_ι_one_tmul`: the unnormalized native
  action of `v` is not skew-Hermitian for `J.fockGramForm` whenever `Q v ≠ 0`.

## References

* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, 2nd ed. (2007), §2.2.4 and
  Proposition 12.1.19.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §5.
* W. Greub, *Multilinear Algebra*, 2nd ed., Springer (1978), Chapter 5.
-/

public section

noncomputable section

open CliffordAlgebra LinearMap Matrix Module QuadraticMap
open TauCeti.ExteriorAlgebra
open scoped RealInnerProductSpace TensorProduct

namespace TauCeti.AlmostComplexStructure

/-- The complexified polar form pairs `v^(1,0)` and `v^(0,1)` to `Q v`. -/
private theorem polar_holomorphicPart_antiholomorphicPart_self {V : Type*} [AddCommGroup V]
    [Module ℝ V] (J : AlmostComplexStructure V) {Q : QuadraticForm ℝ V}
    (hQJ : ∀ v, Q (J v) = Q v) (v : V) :
    polar (Q.baseChange ℂ) (J.holomorphicPart v) (J.antiholomorphicPart v) = Q v := by
  have h0 : polar Q v (J v) = 0 :=
    J.bilinForm_apply_apply_self_eq_zero (g := Q.polarBilin) ⟨polar_comm Q⟩
      (J.polar_apply_apply hQJ) v
  rw [J.polar_holomorphicPart_antiholomorphicPart hQJ, h0, polar_self]
  push_cast
  ring

section PolarAndGram

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (J : AlmostComplexStructure V)
  {Q : QuadraticForm ℝ V} [FiniteDimensional ℝ V] (hQJ : ∀ v, Q (J v) = Q v)
  (hQ : Q.Nondegenerate)

/-! ### The intrinsic Hermitian form on `W` -/

/-- **The intrinsic Hermitian form on the holomorphic polarization `W`**:
`h (x, y) = -(1/2) polar Q_ℂ (conj x, y)`, conjugate-linear in `x` and linear in `y`. -/
def fockPolarForm :
    (J.spinPolarizationData hQJ hQ).W →ₗ⋆[ℂ] (J.spinPolarizationData hQJ hQ).W →ₗ[ℂ] ℂ :=
  (-(2 : ℂ)⁻¹) •
    ((((Q.baseChange ℂ).polarBilin.comp (tmulConj V)).comp
      (J.spinPolarizationData hQJ hQ).W.subtype).compl₂
        (J.spinPolarizationData hQJ hQ).W.subtype)

/-- `J.fockPolarForm` evaluates as `-(1/2) polar Q_ℂ (conj x, y)`. -/
theorem fockPolarForm_apply (x y : (J.spinPolarizationData hQJ hQ).W) :
    J.fockPolarForm hQJ hQ x y =
      -(2 : ℂ)⁻¹ * polar (Q.baseChange ℂ) (tmulConj V x) y := by
  simp [fockPolarForm]

/-- `J.fockPolarForm` is `-(1/2)` times the sesquilinear complexification of `Q.polarBilin`
restricted to `W`. -/
theorem fockPolarForm_eq_polarBilin_sesqComplexification
    (x y : (J.spinPolarizationData hQJ hQ).W) :
    J.fockPolarForm hQJ hQ x y =
      -(2 : ℂ)⁻¹ *
        LinearMap.BilinForm.sesqComplexification Q.polarBilin (x : ℂ ⊗[ℝ] V) (y : ℂ ⊗[ℝ] V) := by
  rw [fockPolarForm_apply, LinearMap.BilinForm.sesqComplexification_apply,
    ← QuadraticForm.polarBilin_baseChange, polarBilin_apply_apply]

/-- Swapping the arguments of `J.fockPolarForm` conjugates its value. -/
theorem star_fockPolarForm_apply (x y : (J.spinPolarizationData hQJ hQ).W) :
    star (J.fockPolarForm hQJ hQ x y) = J.fockPolarForm hQJ hQ y x := by
  have hsymm : (LinearMap.BilinForm.sesqComplexification Q.polarBilin).IsSymm :=
    LinearMap.BilinForm.IsSymm.sesqComplexification ⟨polar_comm Q⟩
  rw [fockPolarForm_eq_polarBilin_sesqComplexification,
    fockPolarForm_eq_polarBilin_sesqComplexification, star_mul', Complex.star_def, hsymm.eq x y,
    map_neg, map_inv₀, map_ofNat]

/-- **The intrinsic form `J.fockPolarForm` on `W` is Hermitian.** -/
theorem isSymm_fockPolarForm : (J.fockPolarForm hQJ hQ).IsSymm :=
  LinearMap.isSymm_def.mpr (J.star_fockPolarForm_apply hQJ hQ)

/-- **Agreement with `g.sesqComplexification` in the geometric convention**: when `Q v = -g v v`
for a symmetric real bilinear form `g`, `J.fockPolarForm` is the restriction of
`g.sesqComplexification` to `W`. -/
theorem fockPolarForm_eq_sesqComplexification {g : LinearMap.BilinForm ℝ V} (hg : g.IsSymm)
    (hQg : ∀ v, Q v = -g v v) (x y : (J.spinPolarizationData hQJ hQ).W) :
    J.fockPolarForm hQJ hQ x y = g.sesqComplexification (x : ℂ ⊗[ℝ] V) (y : ℂ ⊗[ℝ] V) := by
  have hpolar : Q.polarBilin = (-2 : ℝ) • g := by
    refine LinearMap.ext fun u ↦ LinearMap.ext fun v ↦ ?_
    simp only [polarBilin_apply_apply, polar, hQg, LinearMap.smul_apply, smul_eq_mul,
      map_add, LinearMap.add_apply, hg.eq v u]
    ring
  have hsesq (a b : ℂ ⊗[ℝ] V) :
      LinearMap.BilinForm.sesqComplexification Q.polarBilin a b =
        (-2 : ℂ) * g.sesqComplexification a b := by
    rw [hpolar]
    induction a using TensorProduct.inductionOn with
    | add a₁ a₂ ha₁ ha₂ => simp only [map_add, LinearMap.add_apply, ha₁, ha₂, mul_add]
    | tmul z u =>
      induction b using TensorProduct.inductionOn with
      | add b₁ b₂ hb₁ hb₂ => simp only [map_add, hb₁, hb₂, mul_add]
      | tmul w v =>
        simp only [LinearMap.BilinForm.sesqComplexification_tmul_tmul, LinearMap.smul_apply,
          smul_eq_mul]
        push_cast
        ring
  rw [fockPolarForm_eq_polarBilin_sesqComplexification, hsesq, ← mul_assoc]
  norm_num

/-- On `(1,0)`-parts, `J.fockPolarForm` pairs `v^(1,0)` with itself to `-(1/2) Q v`. -/
theorem fockPolarForm_holomorphicPart_self (v : V) :
    J.fockPolarForm hQJ hQ
        ⟨J.holomorphicPart v, J.holomorphicPart_mem_spinPolarizationData_W hQJ hQ v⟩
        ⟨J.holomorphicPart v, J.holomorphicPart_mem_spinPolarizationData_W hQJ hQ v⟩ =
      -(2 : ℂ)⁻¹ * (Q v : ℂ) := by
  rw [fockPolarForm_apply]
  dsimp only
  rw [tmulConj_holomorphicPart, polar_comm,
    J.polar_holomorphicPart_antiholomorphicPart_self hQJ v]

/-- Any basis `b` of `W` with `polar Q_ℂ (conj bᵢ, bⱼ) = -2 δᵢⱼ` has `J.fockPolarForm` as its
orthonormal Hermitian form. -/
theorem toLinearMapₛₗ₂_eq_fockPolarForm {ι : Type*} [Fintype ι] [LinearOrder ι]
    (b : Basis ι ℂ (J.spinPolarizationData hQJ hQ).W)
    (hb : ∀ i j, polar (Q.baseChange ℂ) (tmulConj V (b i : ℂ ⊗[ℝ] V)) (b j) =
      if i = j then -2 else 0) :
    toLinearMapₛₗ₂ (starRingEnd ℂ) b b (1 : Matrix ι ι ℂ) = J.fockPolarForm hQJ hQ :=
  LinearMap.ext fun x ↦ LinearMap.ext fun y ↦ by
    rw [J.toLinearMapₛₗ₂_apply_eq_polar hQJ hQ b hb, fockPolarForm_apply]

/-! ### The basis-free Fock Gram metric and its Gram-determinant formula -/

/-- **The basis-free Fock Gram metric** on the spinor module `⋀ W`: the exterior Gram form of
`J.fockPolarForm hQJ hQ`. -/
def fockGramForm :
    ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W →ₗ⋆[ℂ]
      ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W →ₗ[ℂ] ℂ :=
  (J.fockPolarForm hQJ hQ).exteriorAlgebraGram

/-- `J.fockGramForm` is definitionally `(J.fockPolarForm hQJ hQ).exteriorAlgebraGram`. -/
theorem fockGramForm_def :
    J.fockGramForm hQJ hQ = (J.fockPolarForm hQJ hQ).exteriorAlgebraGram :=
  (rfl)

/-- Swapping the arguments of `J.fockGramForm` conjugates its value. -/
theorem star_fockGramForm_apply (s t : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W) :
    star (J.fockGramForm hQJ hQ s t) = J.fockGramForm hQJ hQ t s :=
  (J.fockPolarForm hQJ hQ).star_exteriorAlgebraGram_apply (J.isSymm_fockPolarForm hQJ hQ) s t

/-- **The Fock Gram metric is Hermitian.** -/
theorem isSymm_fockGramForm : (J.fockGramForm hQJ hQ).IsSymm :=
  (J.isSymm_fockPolarForm hQJ hQ).exteriorAlgebraGram

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
@[simp]
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

/-- Explicit `2 × 2` Gram-determinant formula for `J.fockGramForm` in degree two. -/
theorem fockGramForm_ι_mul_ι (x₁ x₂ y₁ y₂ : (J.spinPolarizationData hQJ hQ).W) :
    J.fockGramForm hQJ hQ (_root_.ExteriorAlgebra.ι ℂ x₁ * _root_.ExteriorAlgebra.ι ℂ x₂)
        (_root_.ExteriorAlgebra.ι ℂ y₁ * _root_.ExteriorAlgebra.ι ℂ y₂) =
      J.fockPolarForm hQJ hQ x₁ y₁ * J.fockPolarForm hQJ hQ x₂ y₂ -
        J.fockPolarForm hQJ hQ x₁ y₂ * J.fockPolarForm hQJ hQ x₂ y₁ :=
  (J.fockPolarForm hQJ hQ).exteriorAlgebraGram_ι_mul_ι x₁ x₂ y₁ y₂

/-! ### Basis-free `*`-representation and skew-Hermitian real-vector action -/

/-- The polarization pairing with `conj x ∈ W'` is `-2` times `J.fockPolarForm x`. -/
private theorem pairingEquiv_tmulConj_eq_fockPolarForm (x : (J.spinPolarizationData hQJ hQ).W) :
    (J.spinPolarizationData hQJ hQ).pairingEquiv
        ⟨tmulConj V x, J.tmulConj_mem_spinPolarizationData_W' hQJ hQ x.2⟩ =
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
          ⟨tmulConj V x, J.tmulConj_mem_spinPolarizationData_W' hQJ hQ x.2⟩ t) := by
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
          ⟨tmulConj V y, J.tmulConj_mem_spinPolarizationData_W hQJ hQ y.2⟩ t) := by
  obtain ⟨x, rfl⟩ : ∃ x : (J.spinPolarizationData hQJ hQ).W,
      ⟨tmulConj V x, J.tmulConj_mem_spinPolarizationData_W' hQJ hQ x.2⟩ = y :=
    ⟨⟨tmulConj V y, J.tmulConj_mem_spinPolarizationData_W hQJ hQ y.2⟩,
      Subtype.ext (tmulConj_tmulConj V y)⟩
  have hx : (⟨tmulConj V (tmulConj V (x : ℂ ⊗[ℝ] V)),
      J.tmulConj_mem_spinPolarizationData_W hQJ hQ
        (J.tmulConj_mem_spinPolarizationData_W' hQJ hQ x.2)⟩ :
      (J.spinPolarizationData hQJ hQ).W) = x :=
    Subtype.ext (tmulConj_tmulConj V x)
  rw [hx, fockGramForm_def, SpinPolarizationData.contract_apply,
    J.pairingEquiv_tmulConj_eq_fockPolarForm hQJ hQ, SpinPolarizationData.wedge_apply]
  have hright := (J.fockPolarForm hQJ hQ).exteriorAlgebraGram_ι_mul_right star_involutive
    (J.star_fockPolarForm_apply hQJ hQ) x
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
      ((⟨tmulConj V x, J.tmulConj_mem_spinPolarizationData_W' hQJ hQ x.2⟩ :
        (J.spinPolarizationData hQJ hQ).W') : ℂ ⊗[ℝ] V) := (rfl)
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
      ((⟨tmulConj V y, J.tmulConj_mem_spinPolarizationData_W hQJ hQ y.2⟩ :
        (J.spinPolarizationData hQJ hQ).W) : ℂ ⊗[ℝ] V) := (rfl)
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
      have := z.2
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

/-! ### Agreement with the wedge-basis metric -/

/-- **For any orthonormal basis `b` of `W`, the wedge-basis Hermitian form on `⋀ W` is
`J.fockGramForm`.** -/
theorem toLinearMapₛₗ₂_exteriorAlgebra_eq_fockGramForm {ι : Type*} [Fintype ι] [LinearOrder ι]
    (b : Basis ι ℂ (J.spinPolarizationData hQJ hQ).W)
    (hb : ∀ i j, polar (Q.baseChange ℂ) (tmulConj V (b i : ℂ ⊗[ℝ] V)) (b j) =
      if i = j then -2 else 0) :
    toLinearMapₛₗ₂ (starRingEnd ℂ) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset ι) (Finset ι) ℂ) =
      J.fockGramForm hQJ hQ := by
  rw [ExteriorAlgebra.toLinearMapₛₗ₂_eq_exteriorAlgebraGram,
    J.toLinearMapₛₗ₂_eq_fockPolarForm hQJ hQ b hb, fockGramForm_def]

/-- **The Gram-determinant formula for the wedge-basis Fock metric** of any orthonormal polarization
basis `b`. -/
theorem toLinearMapₛₗ₂_exteriorAlgebra_ιMulti {ι : Type*} [Fintype ι] [LinearOrder ι]
    (b : Basis ι ℂ (J.spinPolarizationData hQJ hQ).W)
    (hb : ∀ i j, polar (Q.baseChange ℂ) (tmulConj V (b i : ℂ ⊗[ℝ] V)) (b j) =
      if i = j then -2 else 0)
    {p : ℕ} (x y : Fin p → (J.spinPolarizationData hQJ hQ).W) :
    toLinearMapₛₗ₂ (starRingEnd ℂ) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset ι) (Finset ι) ℂ)
        (_root_.ExteriorAlgebra.ιMulti ℂ p x) (_root_.ExteriorAlgebra.ιMulti ℂ p y) =
      (Matrix.of fun i j ↦ J.fockPolarForm hQJ hQ (x i) (y j)).det := by
  rw [J.toLinearMapₛₗ₂_exteriorAlgebra_eq_fockGramForm hQJ hQ b hb, fockGramForm_ιMulti]

/-! ### Vacuum-to-degree-one evaluations and the native-action negative control -/

/-- On the vacuum `1`, the normalized real Fock operator `c(v)` acts as `√2 • ι(v^(1,0))`. -/
theorem realFockAction_ι_apply_one (v : V) :
    J.realFockAction hQJ hQ (CliffordAlgebra.ι Q v) 1 =
      (Real.sqrt 2 : ℂ) • _root_.ExteriorAlgebra.ι ℂ
        ⟨J.holomorphicPart v, J.holomorphicPart_mem_spinPolarizationData_W hQJ hQ v⟩ := by
  rw [realFockAction_ι, fockAction_ι_one_tmul]
  simp [SpinPolarizationData.wedge_apply, SpinPolarizationData.contract_apply]

/-- Contracting `ι(v^(1,0))` by `v^(0,1)` yields `Q v • 1`. -/
private theorem contract_antiholomorphicPart_ι_holomorphicPart (v : V) :
    (J.spinPolarizationData hQJ hQ).contract
        ⟨J.antiholomorphicPart v, J.antiholomorphicPart_mem_spinPolarizationData_W' hQJ hQ v⟩
        (_root_.ExteriorAlgebra.ι ℂ
          ⟨J.holomorphicPart v, J.holomorphicPart_mem_spinPolarizationData_W hQJ hQ v⟩) =
      (Q v : ℂ) • 1 := by
  rw [SpinPolarizationData.contract_apply]
  -- View `ExteriorAlgebra.ι ℂ` as `CliffordAlgebra.ι 0` so `contractLeft_ι` evaluates it.
  change contractLeft (Q := (0 : QuadraticForm ℂ (J.spinPolarizationData hQJ hQ).W)) _
    (CliffordAlgebra.ι (0 : QuadraticForm ℂ (J.spinPolarizationData hQJ hQ).W) _) = _
  rw [contractLeft_ι, SpinPolarizationData.pairingEquiv_apply]
  dsimp only
  rw [J.polar_holomorphicPart_antiholomorphicPart_self hQJ v, Algebra.algebraMap_eq_smul_one]

/-- On `ι(v^(1,0))`, the normalized real Fock operator `c(v)` acts as `((√2)⁻¹ * Q v) • 1`. -/
theorem realFockAction_ι_apply_ι_holomorphicPart (v : V) :
    J.realFockAction hQJ hQ (CliffordAlgebra.ι Q v)
        (_root_.ExteriorAlgebra.ι ℂ
          ⟨J.holomorphicPart v, J.holomorphicPart_mem_spinPolarizationData_W hQJ hQ v⟩) =
      ((Real.sqrt 2 : ℂ)⁻¹ * (Q v : ℂ)) • 1 := by
  have hsqrt : (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt zero_le_two, Complex.ofReal_ofNat]
  have hinv : (Real.sqrt 2 : ℂ) * 2⁻¹ = (Real.sqrt 2 : ℂ)⁻¹ := by
    symm
    exact inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hsqrt, mul_inv_cancel₀ two_ne_zero])
  rw [realFockAction_ι, fockAction_ι_one_tmul, LinearMap.smul_apply, LinearMap.add_apply,
    SpinPolarizationData.wedge_apply, _root_.ExteriorAlgebra.ι_sq_zero, zero_add,
    LinearMap.smul_apply, J.contract_antiholomorphicPart_ι_holomorphicPart hQJ hQ v,
    smul_smul, smul_smul, hinv]

/-- On the vacuum `1`, the unnormalized native action `spinAction (ι (1 ⊗ v))` sends
`1 ↦ ι(v^(1,0))` without the `√2` factor. -/
theorem spinAction_ι_one_tmul_apply_one (v : V) :
    spinAction _ (J.spinPolarizationData hQJ hQ)
        (CliffordAlgebra.ι (Q.baseChange ℂ) ((1 : ℂ) ⊗ₜ v)) 1 =
      _root_.ExteriorAlgebra.ι ℂ
        ⟨J.holomorphicPart v, J.holomorphicPart_mem_spinPolarizationData_W hQJ hQ v⟩ := by
  rw [spinAction_ι_one_tmul]
  simp [SpinPolarizationData.wedge_apply, SpinPolarizationData.contract_apply]

/-- On `ι(v^(1,0))`, the unnormalized native action `spinAction (ι (1 ⊗ v))` sends
`ι(v^(1,0)) ↦ Q v • 1`. -/
theorem spinAction_ι_one_tmul_apply_ι_holomorphicPart (v : V) :
    spinAction _ (J.spinPolarizationData hQJ hQ)
        (CliffordAlgebra.ι (Q.baseChange ℂ) ((1 : ℂ) ⊗ₜ v))
        (_root_.ExteriorAlgebra.ι ℂ
          ⟨J.holomorphicPart v, J.holomorphicPart_mem_spinPolarizationData_W hQJ hQ v⟩) =
      (Q v : ℂ) • 1 := by
  rw [spinAction_ι_one_tmul, LinearMap.add_apply, SpinPolarizationData.wedge_apply,
    _root_.ExteriorAlgebra.ι_sq_zero, zero_add,
    J.contract_antiholomorphicPart_ι_holomorphicPart hQJ hQ v]

/-- **Negative control**: whenever `Q v ≠ 0`, the unnormalized native action
`spinAction (ι (1 ⊗ v))` is **not** skew-Hermitian for `J.fockGramForm`, because its
vacuum-to-degree-one matrix element is `-(1/2) Q v` whereas the negated transpose matrix element
is `-Q v`. -/
theorem not_skewAdjoint_spinAction_ι_one_tmul {v : V} (hv : Q v ≠ 0) :
    ¬ ∀ s t : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQ).W,
      J.fockGramForm hQJ hQ
          (spinAction _ (J.spinPolarizationData hQJ hQ)
            (CliffordAlgebra.ι (Q.baseChange ℂ) ((1 : ℂ) ⊗ₜ v)) s) t =
        -J.fockGramForm hQJ hQ s
          (spinAction _ (J.spinPolarizationData hQJ hQ)
            (CliffordAlgebra.ι (Q.baseChange ℂ) ((1 : ℂ) ⊗ₜ v)) t) := by
  intro hskew
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

section HilbertGram

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (J : AlmostComplexStructure V) {Q : QuadraticForm ℝ V}
  (hQJ : ∀ v, Q (J v) = Q v) (hQnd : Q.Nondegenerate)

/-- In the Euclidean convention `Q v = -‖v‖²`, `J.fockPolarForm` is the restriction to `W` of the
sesquilinear complexification of the real inner product `innerₗ V`. -/
theorem fockPolarForm_eq_sesqComplexification_innerₗ (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (x y : (J.spinPolarizationData hQJ hQnd).W) :
    J.fockPolarForm hQJ hQnd x y =
      LinearMap.BilinForm.sesqComplexification (innerₗ V) (x : ℂ ⊗[ℝ] V) (y : ℂ ⊗[ℝ] V) := by
  refine J.fockPolarForm_eq_sesqComplexification hQJ hQnd ⟨fun u v ↦ real_inner_comm v u⟩
    (fun v ↦ ?_) x y
  rw [hQ, innerₗ_apply_apply, real_inner_self_eq_norm_sq]

variable (hQ : ∀ v, Q v = -‖v‖ ^ 2)

/-- **The Fock inner product core equals the basis-free Fock Gram metric `J.fockGramForm`.** -/
theorem fockInnerProductCore_inner_eq_fockGramForm
    (s t : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQnd).W) :
    (J.fockInnerProductCore hQJ hQnd hQ).inner s t = J.fockGramForm hQJ hQnd s t := by
  obtain ⟨b, hb⟩ := J.exists_basis_polar_tmulConj hQJ hQnd hQ (finrank ℝ V / 2)
    (Nat.two_mul_div_two_of_even J.even_finrank_real).symm
  rw [J.fockInnerProductCore_inner hQJ hQnd hQ b hb,
    J.toLinearMapₛₗ₂_exteriorAlgebra_eq_fockGramForm hQJ hQnd b hb]

/-- **The native complex inner product of the Fock module is `J.fockGramForm`.** -/
theorem inner_fock_eq_fockGramForm
    (s t : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQnd).W) :
    letI := J.fockNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockInnerProductSpace hQJ hQnd hQ
    inner ℂ s t = J.fockGramForm hQJ hQnd s t :=
  J.fockInnerProductCore_inner_eq_fockGramForm hQJ hQnd hQ s t

/-- **Distinct exterior degrees are orthogonal** in the native Hermitian Fock module. -/
theorem inner_fock_eq_zero_of_mem_exteriorPower {p q : ℕ} (hpq : p ≠ q)
    {s t : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQnd).W}
    (hs : s ∈ ⋀[ℂ]^p (J.spinPolarizationData hQJ hQnd).W)
    (ht : t ∈ ⋀[ℂ]^q (J.spinPolarizationData hQJ hQnd).W) :
    letI := J.fockNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockInnerProductSpace hQJ hQnd hQ
    inner ℂ s t = 0 := by
  let := J.fockNormedAddCommGroup hQJ hQnd hQ
  let := J.fockInnerProductSpace hQJ hQnd hQ
  rw [J.inner_fock_eq_fockGramForm hQJ hQnd hQ]
  exact J.fockGramForm_eq_zero_of_mem_exteriorPower hQJ hQnd hpq hs ht

/-- **The Gram-determinant formula for the native Fock inner product** in every degree `p`:
`⟪x₀ ∧ ⋯ ∧ x_{p-1}, y₀ ∧ ⋯ ∧ y_{p-1}⟫_ℂ = det (h_ℂ (xᵢ, yⱼ))`. -/
theorem inner_fock_ιMulti {p : ℕ}
    (x y : Fin p → (J.spinPolarizationData hQJ hQnd).W) :
    letI := J.fockNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockInnerProductSpace hQJ hQnd hQ
    inner ℂ (_root_.ExteriorAlgebra.ιMulti ℂ p x) (_root_.ExteriorAlgebra.ιMulti ℂ p y) =
      (Matrix.of fun i j ↦
        LinearMap.BilinForm.sesqComplexification (innerₗ V)
          (x i : ℂ ⊗[ℝ] V) (y j : ℂ ⊗[ℝ] V)).det := by
  let := J.fockNormedAddCommGroup hQJ hQnd hQ
  let := J.fockInnerProductSpace hQJ hQnd hQ
  rw [J.inner_fock_eq_fockGramForm hQJ hQnd hQ, fockGramForm_ιMulti]
  congr 1
  ext i j
  exact J.fockPolarForm_eq_sesqComplexification_innerₗ hQJ hQnd hQ (x i) (y j)

/-- For any nonzero real vector `v ≠ 0` in a Euclidean space `(V, J)` with `Q v = -‖v‖²`, the
unnormalized native action `spinAction (ι (1 ⊗ v))` is not skew-adjoint in
`fockInnerProductSpace`. -/
theorem adjoint_spinAction_ι_one_tmul_ne_neg {v : V} (hv : v ≠ 0) :
    letI := J.fockNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockInnerProductSpace hQJ hQnd hQ
    LinearMap.adjoint
        (spinAction _ (J.spinPolarizationData hQJ hQnd)
          (CliffordAlgebra.ι (Q.baseChange ℂ) ((1 : ℂ) ⊗ₜ v))) ≠
      -spinAction _ (J.spinPolarizationData hQJ hQnd)
        (CliffordAlgebra.ι (Q.baseChange ℂ) ((1 : ℂ) ⊗ₜ v)) := by
  let := J.fockNormedAddCommGroup hQJ hQnd hQ
  let := J.fockInnerProductSpace hQJ hQnd hQ
  have hQv : Q v ≠ 0 := by
    rw [hQ, neg_ne_zero]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
  intro hadj
  refine J.not_skewAdjoint_spinAction_ι_one_tmul hQJ hQnd hQv fun s t ↦ ?_
  rw [← J.inner_fock_eq_fockGramForm hQJ hQnd hQ, ← J.inner_fock_eq_fockGramForm hQJ hQnd hQ,
    ← LinearMap.adjoint_inner_right, hadj, LinearMap.neg_apply, inner_neg_right]

end HilbertGram

end TauCeti.AlmostComplexStructure
