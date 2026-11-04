/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.Derivation
public import TauCeti.Algebra.Lie.Current.Vacuum.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Vector fields, translation and degree on the vacuum module

Let `V = U / I₀` be the vacuum module of the residue central extension `ĝ = L((t)) ⊕ R K` of an
invariant symmetric form `Φ` at the central value `a` (`TauCeti.CurrentAlgebra.VacuumModule`), where
`U = U(ĝ) / (ι K - a)` and `I₀ = U · ι(L[[t]])`.

A vector field `h d/dt` acts on `U` by the derivation `δ_h` lifting `f ⊗ x ↦ h f' ⊗ x`
(`TauCeti.CurrentAlgebra.vectorFieldEnvelopingDerivation`). When `h` is regular at the origin,
that is `h ∈ R[[t]]`, the derivative of a power series is a power series, so `δ_h` preserves `I₀`.
Hence `h d/dt` acts on `V` by an operator `D_h : u |0⟩ ↦ δ_h(u) |0⟩`
(`TauCeti.CurrentAlgebra.vacuumVectorField`). It kills the vacuum, satisfies
`D_h(u v) = δ_h(u) v + u D_h(v)`, and these two properties determine it. The operators `D_h`
satisfy the commutator relations of the Lie algebra `Der O = R[[t]] d/dt` of vector fields,
`[D_{h₁}, D_{h₂}] = D_{h₁ h₂' - h₂ h₁'}`, and `[D_h, J^x[[n]]]` is the action of the current
`h (tⁿ)' ⊗ x`.

Two vector fields give the basic structure of the vacuum vertex algebra.

* **Translation.** `T = -d/dt` (`TauCeti.CurrentAlgebra.vacuumTranslation`) kills the vacuum and
  satisfies `[T, J^x[[n]]] = -n J^x[[n - 1]]`, the coefficient form of
  `[T, J^x(z)] = ∂_z J^x(z)`. Consequently `T^k x₋₁|0⟩ = k! x₋ₖ₋₁|0⟩`. When `R` is a
  `ℚ`-algebra, so that the factorials are invertible, this says that
  `J^x(z)|0⟩ = ∑ₖ x₋ₖ₋₁|0⟩ zᵏ` is `e^{zT} x₋₁|0⟩`.
* **Degree.** `L₀ = -t d/dt` (`TauCeti.CurrentAlgebra.vacuumDegreeOperator`) kills the vacuum and
  satisfies `[L₀, J^x[[n]]] = -n J^x[[n]]` and `[L₀, T] = T`. So the mode `xₙ` maps the
  `μ`-eigenspace of `L₀` to the `(μ - n)`-eigenspace, and `T` maps it to the `(μ + 1)`-eigenspace:
  the vectors `x¹₋ₙ₁ ⋯ xᵏ₋ₙₖ|0⟩` are eigenvectors of degree `n₁ + ⋯ + nₖ`.

The results proved here hold at every central value `a`, including the critical level and
`a = 0`, over every commutative ring, and with no finiteness of `L`; only the exponential
reformulation of the translation property needs `R` to be a `ℚ`-algebra.

## Main definitions

* `TauCeti.CurrentAlgebra.vacuumVectorField`: the action of `h d/dt`, for `h ∈ R[[t]]`.
* `TauCeti.CurrentAlgebra.vacuumTranslation`: the translation operator `T = -d/dt`.
* `TauCeti.CurrentAlgebra.vacuumDegreeOperator`: the degree operator `L₀ = -t d/dt`.

## Main results

* `TauCeti.CurrentAlgebra.vacuumVectorField_smul`: `D_h(u v) = δ_h(u) v + u D_h(v)`.
* `TauCeti.CurrentAlgebra.eq_vacuumVectorField`: this and `D_h |0⟩ = 0` determine `D_h`.
* `TauCeti.CurrentAlgebra.lie_vacuumVectorField`: `[D_{h₁}, D_{h₂}] = D_{h₁ h₂' - h₂ h₁'}`.
* `TauCeti.CurrentAlgebra.lie_vacuumTranslation_ncoeff_currentField`: translation covariance of the
  current fields.
* `TauCeti.CurrentAlgebra.pow_vacuumTranslation_ncoeff_currentField_vacuum`:
  `T^k x₋₁|0⟩ = k! x₋ₖ₋₁|0⟩`.
* `TauCeti.CurrentAlgebra.lie_vacuumDegreeOperator_ncoeff_currentField` and
  `TauCeti.CurrentAlgebra.lie_vacuumDegreeOperator_vacuumTranslation`: the degree relations.

## References

* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §2.4, for the
  translation operator and the grading of the vacuum module of an affine Kac--Moody algebra.
* E. Frenkel, *Langlands Correspondence for Loop Groups*, §2.2 and §3.5, for the vacuum module
  `V_κ(𝔤)` and the action of `Der O` on it.
* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §1.3 and §4.7.
-/

public section

noncomputable section

open scoped LaurentSeries VertexOperator
open LieAlgebra TauCeti.UniversalEnvelopingAlgebra
open LieAlgebra.ofTwoCocycle (centralElement envelopingι)

attribute [local instance 1100] HahnSeries.instAlgebra

namespace TauCeti.CurrentAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
variable (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (a : R)

local notation "c" => twoCocycleOfBilinear R L Φ hΦ hΦs
local notation "UK" => CentralQuotient R (centralElement c) a
local notation "I₀" => orderLeftIdeal Φ hΦ hΦs a 0

/-! ### Vector fields regular at the origin -/

section VectorField

/-- **Vector fields regular at the origin act on the vacuum module.** For `h` of order at least `0`,
that is `h ∈ R[[t]]`, the vector field `h d/dt` acts on `V = U / I₀` by `u |0⟩ ↦ δ_h(u) |0⟩`, where
`δ_h` is the derivation of `U = U(ĝ) / (ι K - a)` acting by `h d/dt` on the currents. -/
def vacuumVectorField (h : R⸨X⸩) (hh : 0 ≤ h.orderTop) :
    Module.End R (VacuumModule Φ hΦ hΦs a) :=
  (Submodule.Quotient.restrictScalarsEquiv R I₀).toLinearMap ∘ₗ
    (Submodule.restrictScalars R I₀).mapQ (Submodule.restrictScalars R I₀)
      (vectorFieldEnvelopingDerivation Φ hΦ hΦs a h : Module.End R UK)
      (fun x hx ↦ (Submodule.restrictScalars_mem R I₀ _).2
        (vectorFieldEnvelopingDerivation_mem_orderLeftIdeal_zero Φ hΦ hΦs a hh
          ((Submodule.restrictScalars_mem R I₀ x).1 hx))) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv R I₀).symm.toLinearMap

variable {Φ hΦ hΦs a}

/-- The vector field `h d/dt` sends `u |0⟩` to `δ_h(u) |0⟩`. -/
@[simp]
theorem vacuumVectorField_smul_vacuum {h : R⸨X⸩} (hh : 0 ≤ h.orderTop) (u : UK) :
    vacuumVectorField Φ hΦ hΦs a h hh (u • vacuum Φ hΦ hΦs a) =
      (vectorFieldEnvelopingDerivation Φ hΦ hΦs a h : Module.End R UK) u • vacuum Φ hΦ hΦs a := by
  rw [← mk_eq_smul_vacuum, ← mk_eq_smul_vacuum]
  simp only [vacuumVectorField, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.mapQ_apply,
    Submodule.Quotient.restrictScalarsEquiv_mk]

/-- **Vector fields kill the vacuum.** -/
@[simp]
theorem vacuumVectorField_vacuum {h : R⸨X⸩} (hh : 0 ≤ h.orderTop) :
    vacuumVectorField Φ hΦ hΦs a h hh (vacuum Φ hΦ hΦs a) = 0 := by
  rw [← one_smul UK (vacuum Φ hΦ hΦs a), vacuumVectorField_smul_vacuum,
    derivationLieAlgebra.apply_one_eq_zero, zero_smul]

/-- **The Leibniz rule for the action of `U`**: `D_h(u v) = δ_h(u) v + u D_h(v)`. -/
theorem vacuumVectorField_smul {h : R⸨X⸩} (hh : 0 ≤ h.orderTop) (u : UK)
    (v : VacuumModule Φ hΦ hΦs a) :
    vacuumVectorField Φ hΦ hΦs a h hh (u • v) =
      (vectorFieldEnvelopingDerivation Φ hΦ hΦs a h : Module.End R UK) u • v +
        u • vacuumVectorField Φ hΦ hΦs a h hh v := by
  obtain ⟨w, rfl⟩ := exists_smul_vacuum_eq v
  rw [smul_smul, vacuumVectorField_smul_vacuum, vacuumVectorField_smul_vacuum,
    derivationLieAlgebra.leibniz, add_smul, smul_smul, smul_smul]

/-- **Uniqueness of the action of a vector field.** A map of the vacuum module which kills the
vacuum and satisfies the Leibniz rule along `δ_h` is the action of `h d/dt`. -/
theorem eq_vacuumVectorField {h : R⸨X⸩} (hh : 0 ≤ h.orderTop)
    {f : VacuumModule Φ hΦ hΦs a → VacuumModule Φ hΦ hΦs a}
    (hf : ∀ (u : UK) v,
      f (u • v) = (vectorFieldEnvelopingDerivation Φ hΦ hΦs a h : Module.End R UK) u • v + u • f v)
    (hf₀ : f (vacuum Φ hΦ hΦs a) = 0) :
    f = vacuumVectorField Φ hΦ hΦs a h hh := by
  funext v
  obtain ⟨u, rfl⟩ := exists_smul_vacuum_eq v
  rw [hf, hf₀, smul_zero, add_zero, vacuumVectorField_smul_vacuum]

/-- **Commutation with the currents**: `[D_h, u] = h u'` for every current `u`. -/
theorem lie_vacuumVectorField_envelopingAction {h : R⸨X⸩} (hh : 0 ≤ h.orderTop)
    (u : currentAlgebra R L) :
    ⁅vacuumVectorField Φ hΦ hΦs a h hh,
        envelopingAction (M := VacuumModule Φ hΦ hΦs a) Φ hΦ hΦs a u⁆ =
      envelopingAction Φ hΦ hΦs a (vectorFieldDerivation R L h u) := by
  ext v
  simp only [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, envelopingAction_apply,
    vacuumVectorField_smul, vectorFieldEnvelopingDerivation_envelopingι, add_sub_cancel_right]

/-- **The commutator relations of vector fields**: `[D_{h₁}, D_{h₂}] = D_{h₁ h₂' - h₂ h₁'}`, the
bracket of `h₁ d/dt` and `h₂ d/dt` in `Der O`. -/
theorem lie_vacuumVectorField {h₁ h₂ : R⸨X⸩} (hh₁ : 0 ≤ h₁.orderTop) (hh₂ : 0 ≤ h₂.orderTop) :
    ⁅vacuumVectorField Φ hΦ hΦs a h₁ hh₁, vacuumVectorField Φ hΦ hΦs a h₂ hh₂⁆ =
      vacuumVectorField Φ hΦ hΦs a
        (h₁ * LaurentSeries.derivative R h₂ - h₂ * LaurentSeries.derivative R h₁)
        (HahnSeries.min_orderTop_le_orderTop_sub.trans'
          (le_min (LaurentSeries.zero_le_orderTop_mul_derivative hh₁ hh₂)
            (LaurentSeries.zero_le_orderTop_mul_derivative hh₂ hh₁))) := by
  refine LinearMap.coe_injective (eq_vacuumVectorField _ (fun u v ↦ ?_) ?_)
  · -- The lift of the commutator of vector fields is the commutator of the lifts.
    have hδ := congrArg (fun D : derivationLieAlgebra R UK ↦ (D : Module.End R UK) u)
      (lie_vectorFieldEnvelopingDerivation Φ hΦ hΦs a h₁ h₂)
    simp only [LieSubalgebra.coe_bracket, Ring.lie_def, LinearMap.sub_apply,
      mul_apply_eq_comp] at hδ
    simp only [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, vacuumVectorField_smul,
      map_add, ← hδ, sub_smul, smul_sub]
    abel
  · simp [Ring.lie_def]

end VectorField

/-! ### Translation and degree -/

section TranslationDegree

local notation "J" => currentField (envelopingAction (M := VacuumModule Φ hΦ hΦs a) Φ hΦ hΦs a)
  (Iff.mpr (isSmooth_envelopingAction_iff Φ hΦ hΦs a)
    (smoothModules_quotient_orderLeftIdeal Φ hΦ hΦs a 0))

/-- The **translation operator** `T = -d/dt` on the vacuum module, the action of the vector field
`-d/dt`. It acts by `[T, xₙ] = -n xₙ₋₁` and kills the vacuum. -/
def vacuumTranslation : Module.End R (VacuumModule Φ hΦ hΦs a) :=
  vacuumVectorField Φ hΦ hΦs a (-1)
    (by rw [HahnSeries.orderTop_neg]; exact HahnSeries.zero_le_orderTop_one)

/-- The **degree operator** `L₀ = -t d/dt` on the vacuum module, the action of the vector field
`-t d/dt`. It acts by `[L₀, xₙ] = -n xₙ` and kills the vacuum. -/
def vacuumDegreeOperator : Module.End R (VacuumModule Φ hΦ hΦs a) :=
  vacuumVectorField Φ hΦ hΦs a (-HahnSeries.single 1 1)
    (by rw [HahnSeries.orderTop_neg]; exact HahnSeries.zero_le_orderTop_single zero_le_one 1)

variable {Φ hΦ hΦs a}

/-- The translation operator is the action of the vector field `-d/dt`. -/
theorem vacuumTranslation_def (hh : 0 ≤ (-1 : R⸨X⸩).orderTop) :
    vacuumTranslation Φ hΦ hΦs a = vacuumVectorField Φ hΦ hΦs a (-1) hh := by
  rw [vacuumTranslation]

/-- The degree operator is the action of the vector field `-t d/dt`. -/
theorem vacuumDegreeOperator_def (hh : 0 ≤ (-HahnSeries.single 1 1 : R⸨X⸩).orderTop) :
    vacuumDegreeOperator Φ hΦ hΦs a = vacuumVectorField Φ hΦ hΦs a (-HahnSeries.single 1 1) hh := by
  rw [vacuumDegreeOperator]

/-- **Translation kills the vacuum.** -/
@[simp]
theorem vacuumTranslation_vacuum :
    vacuumTranslation Φ hΦ hΦs a (vacuum Φ hΦ hΦs a) = 0 :=
  vacuumVectorField_vacuum _

/-- **The degree operator kills the vacuum.** -/
@[simp]
theorem vacuumDegreeOperator_vacuum :
    vacuumDegreeOperator Φ hΦ hΦs a (vacuum Φ hΦ hΦs a) = 0 :=
  vacuumVectorField_vacuum _

/-- **Translation covariance of the current fields**: `[T, J^x[[n]]] = -n J^x[[n - 1]]`, the
coefficient form of `[T, J^x(z)] = ∂_z J^x(z)`. -/
theorem lie_vacuumTranslation_ncoeff_currentField (x : L) (n : ℤ) :
    ⁅vacuumTranslation Φ hΦ hΦs a, (J x)[[n]]⁆ = -((n : R) • (J x)[[n - 1]]) := by
  -- The commutator with a current, then the translation `d/dt` on modes.
  rw [ncoeff_currentField, ncoeff_currentField, vacuumTranslation,
    lie_vacuumVectorField_envelopingAction]
  simp only [vectorFieldDerivation_neg, LieDerivation.neg_apply,
    vectorFieldDerivation_one_single_tmul, map_neg, map_smul, ← Int.cast_smul_eq_zsmul R]

/-- Translation of a vector `xₙ v`: `T(xₙ v) = xₙ T(v) - n xₙ₋₁ v`. -/
theorem vacuumTranslation_ncoeff_currentField_apply (x : L) (n : ℤ)
    (v : VacuumModule Φ hΦ hΦs a) :
    vacuumTranslation Φ hΦ hΦs a (((J x)[[n]]) v) =
      ((J x)[[n]]) (vacuumTranslation Φ hΦ hΦs a v) - (n : R) • ((J x)[[n - 1]]) v := by
  have h := LinearMap.congr_fun (lie_vacuumTranslation_ncoeff_currentField (Φ := Φ) (hΦ := hΦ)
    (hΦs := hΦs) (a := a) x n) v
  simp only [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, LinearMap.neg_apply,
    LinearMap.smul_apply] at h
  rw [sub_eq_iff_eq_add, neg_add_eq_sub] at h
  exact h

/-- **The translation property of the generating states**: `T^k x₋₁|0⟩ = k! x₋ₖ₋₁|0⟩`, over any
commutative ring `R`. When `R` is a `ℚ`-algebra, dividing by `k!` shows that the vector
`J^x(z)|0⟩ = ∑ₖ x₋ₖ₋₁|0⟩ zᵏ` is `e^{zT} x₋₁|0⟩`. -/
theorem pow_vacuumTranslation_ncoeff_currentField_vacuum (x : L) (k : ℕ) :
    (vacuumTranslation Φ hΦ hΦs a ^ k) (((J x)[[-1]]) (vacuum Φ hΦ hΦs a)) =
      (k.factorial : R) • ((J x)[[-k - 1]]) (vacuum Φ hΦ hΦs a) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hT := vacuumTranslation_ncoeff_currentField_apply (Φ := Φ) (hΦ := hΦ) (hΦs := hΦs)
      (a := a) x (-k - 1) (vacuum Φ hΦ hΦs a)
    rw [vacuumTranslation_vacuum, map_zero, zero_sub, ← neg_smul,
      show -(((-k - 1 : ℤ)) : R) = ((k + 1 : ℕ) : R) by push_cast; ring,
      show -(k : ℤ) - 1 - 1 = -((k + 1 : ℕ) : ℤ) - 1 by push_cast; ring] at hT
    rw [pow_succ', mul_apply_eq_comp]
    refine (congrArg _ ih).trans ?_
    simp only [map_smul, hT, smul_smul, Nat.factorial_succ, Nat.cast_mul, mul_comm]

/-- **The degree of the modes**: `[L₀, J^x[[n]]] = -n J^x[[n]]`. -/
theorem lie_vacuumDegreeOperator_ncoeff_currentField (x : L) (n : ℤ) :
    ⁅vacuumDegreeOperator Φ hΦ hΦs a, (J x)[[n]]⁆ = -((n : R) • (J x)[[n]]) := by
  -- The commutator with a current, then the degree derivation `t d/dt` on modes.
  rw [ncoeff_currentField, vacuumDegreeOperator, lie_vacuumVectorField_envelopingAction]
  simp only [vectorFieldDerivation_neg, LieDerivation.neg_apply,
    vectorFieldDerivation_single_one_single_tmul, map_neg, map_smul, ← Int.cast_smul_eq_zsmul R]

/-- **Translation raises the degree by one**: `[L₀, T] = T`. -/
theorem lie_vacuumDegreeOperator_vacuumTranslation :
    ⁅vacuumDegreeOperator Φ hΦ hΦs a, vacuumTranslation Φ hΦ hΦs a⁆ =
      vacuumTranslation Φ hΦ hΦs a := by
  -- The commutator of the vector fields `-t d/dt` and `-d/dt` is `-d/dt`.
  have h₁ : LaurentSeries.derivative R (1 : R⸨X⸩) = 0 := by
    rw [LaurentSeries.derivative_apply, ← HahnSeries.single_zero_one,
      LaurentSeries.hasseDeriv_single]
    simp
  have ht : LaurentSeries.derivative R (HahnSeries.single 1 1 : R⸨X⸩) = 1 := by
    rw [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_single]
    simp
  have key : -HahnSeries.single 1 1 * LaurentSeries.derivative R (-1) -
      -1 * LaurentSeries.derivative R (-HahnSeries.single 1 1) = (-1 : R⸨X⸩) := by
    rw [map_neg, map_neg, h₁, ht]
    ring
  rw [vacuumDegreeOperator, vacuumTranslation, lie_vacuumVectorField]
  -- The remaining goal is `key`, which `congr` closes.
  congr 1

/-- **The vacuum has degree `0`.** -/
theorem vacuum_mem_eigenspace_vacuumDegreeOperator :
    vacuum Φ hΦ hΦs a ∈ (vacuumDegreeOperator Φ hΦ hΦs a).eigenspace 0 := by
  rw [Module.End.mem_eigenspace_iff, vacuumDegreeOperator_vacuum, zero_smul]

/-- **The mode `xₙ` lowers the degree by `n`**: it maps the `μ`-eigenspace of `L₀` to the
`(μ - n)`-eigenspace. -/
theorem ncoeff_currentField_apply_mem_eigenspace_vacuumDegreeOperator (x : L) (n : ℤ) {μ : R}
    {v : VacuumModule Φ hΦ hΦs a} (hv : v ∈ (vacuumDegreeOperator Φ hΦ hΦs a).eigenspace μ) :
    ((J x)[[n]]) v ∈ (vacuumDegreeOperator Φ hΦ hΦs a).eigenspace (μ - n) := by
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  have h := LinearMap.congr_fun (lie_vacuumDegreeOperator_ncoeff_currentField (Φ := Φ) (hΦ := hΦ)
    (hΦs := hΦs) (a := a) x n) v
  simp only [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, hv, map_smul,
    LinearMap.neg_apply, LinearMap.smul_apply] at h
  rw [sub_eq_iff_eq_add, neg_add_eq_sub] at h
  rw [sub_smul]
  exact h

/-- **Translation raises the degree by one**: `T` maps the `μ`-eigenspace of `L₀` to the
`(μ + 1)`-eigenspace. -/
theorem vacuumTranslation_mem_eigenspace_vacuumDegreeOperator {μ : R}
    {v : VacuumModule Φ hΦ hΦs a} (hv : v ∈ (vacuumDegreeOperator Φ hΦ hΦs a).eigenspace μ) :
    vacuumTranslation Φ hΦ hΦs a v ∈ (vacuumDegreeOperator Φ hΦ hΦs a).eigenspace (μ + 1) := by
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  have h := LinearMap.congr_fun (lie_vacuumDegreeOperator_vacuumTranslation (Φ := Φ) (hΦ := hΦ)
    (hΦs := hΦs) (a := a)) v
  simp only [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, hv, map_smul] at h
  rw [sub_eq_iff_eq_add] at h
  rw [add_smul, one_smul, add_comm]
  exact h

end TranslationDegree

end TauCeti.CurrentAlgebra
