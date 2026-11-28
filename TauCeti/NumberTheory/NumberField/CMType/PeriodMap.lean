/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import TauCeti.NumberTheory.NumberField.CMType.Basic
import TauCeti.Geometry.Symplectic.Complex.Module.Basic
import TauCeti.LinearAlgebra.Complex.Finrank

/-!
# Period maps for a CM type

Let `Φ` be a CM type on a commutative ring `E`, `φ₀ ∈ Φ` a base embedding and `n` a finite index
set. Everything here is built on the complex space `Φ → n → ℂ`. When `E` is a CM field, `Φ` holds
one embedding above each infinite place, and `Φ → n → ℂ` is the real vector space `(E ⊗ ℝ)ⁿ`
written in the coordinates `ℂ^Φ` of `E ⊗ ℝ`, taken `n` times. For a matrix `J ∈ Mₙ(ℂ)`, the
*period structure* `𝒥` acts on `Φ → n → ℂ` as `i·J` in the coordinate `φ₀` and as multiplication
by `i` in every other coordinate. A *period map for `J`* is a real-linear isomorphism
`Q : (Φ → n → ℂ) ≃ₗ[ℝ] V` onto a complex vector space `V` (with compatible real structure) that
carries `𝒥` to multiplication by `i`.

`𝒥` squares to `-1` exactly when `J² = 1`; so a period map for `J` exists exactly when `J² = 1`,
the space `V = Φ → n → ℂ` with the complex structure `𝒥` giving one. For a period map,
`Module.finrank ℂ V = Fintype.card n * Nat.card Φ`, the dimension count `dim_ℂ V = |n|·|Φ|` for
finite `Φ` (for infinite `Φ` both sides are `0` by convention). For a number field `E` this reads
`2 * Module.finrank ℂ V = Fintype.card n * Module.finrank ℚ E`.

## Main definitions

* `TauCeti.CMType.periodStructure Φ φ₀ J`: the complex-linear endomorphism `𝒥` of `Φ → n → ℂ`.
* `TauCeti.CMType.IsPeriodMap Φ φ₀ J Q`: `Q ∘ 𝒥 = i • Q`.

## Main results

* `TauCeti.CMType.periodStructure_comp_self_eq_neg_id_iff`: `𝒥 ∘ 𝒥 = -1 ↔ J * J = 1`.
* `TauCeti.CMType.IsPeriodMap.mul_self_eq_one`: a period map for `J` exists only if `J * J = 1`.
* `TauCeti.CMType.exists_isPeriodMap`: for `J * J = 1` a period map for `J` exists.
* `TauCeti.CMType.IsPeriodMap.finrank_complex_eq`: for a period map,
  `Module.finrank ℂ V = Fintype.card n * Nat.card Φ`, by `LinearEquiv.finrank_complex_eq_nat_card`.
* `TauCeti.CMType.IsPeriodMap.two_mul_finrank_eq`: over a number field `K`,
  `2 * Module.finrank ℂ V = Fintype.card n * Module.finrank ℚ K`.

## References

* The folder `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207, file `Lib/Shimura/Uniformisation/AdelicFrames`
  (`New.Variety.IsPeriodMap`, `New.Variety.IsPeriodMap.finrank_eq_abelianDim`).
-/

public section
noncomputable section

open Complex Matrix

universe u v

namespace TauCeti.CMType

variable {E : Type u} [CommRing E] (Φ : CMType E) (φ₀ : Φ) {n : Type v} [Fintype n]

open scoped Classical in
/-- The **period structure** of `J` on `Φ → n → ℂ` (for a CM field `E`, the coordinates of
`(E ⊗ ℝ)ⁿ` through `Φ`): `y ↦ i • J y` in the coordinate `φ₀` and `y ↦ i • y` in every other
coordinate. -/
def periodStructure (J : Matrix n n ℂ) : (Φ → n → ℂ) →ₗ[ℂ] Φ → n → ℂ :=
  LinearMap.pi fun φ ↦ I • if φ = φ₀ then J.mulVecLin ∘ₗ LinearMap.proj φ else LinearMap.proj φ

variable {Φ φ₀}

/-- In the base coordinate `φ₀` the period structure of `J` acts as `i·J`. -/
@[simp]
theorem periodStructure_apply_self (J : Matrix n n ℂ) (y : Φ → n → ℂ) :
    Φ.periodStructure φ₀ J y φ₀ = I • J *ᵥ y φ₀ := by
  simp [periodStructure]

/-- In a coordinate `φ ≠ φ₀` the period structure acts as multiplication by `i`. -/
@[simp]
theorem periodStructure_apply_of_ne (J : Matrix n n ℂ) (y : Φ → n → ℂ) {φ : Φ} (h : φ ≠ φ₀) :
    Φ.periodStructure φ₀ J y φ = I • y φ := by
  simp [periodStructure, h]

/-- The period structure of `J` is a complex structure, `𝒥 ∘ 𝒥 = -1`, exactly when `J * J = 1`. -/
theorem periodStructure_comp_self_eq_neg_id_iff [DecidableEq n] (J : Matrix n n ℂ) :
    Φ.periodStructure φ₀ J ∘ₗ Φ.periodStructure φ₀ J = -LinearMap.id ↔ J * J = 1 := by
  have key (y : Φ → n → ℂ) : Φ.periodStructure φ₀ J (Φ.periodStructure φ₀ J y) φ₀ =
      -((J * J) *ᵥ y φ₀) := by
    simp [Matrix.mulVec_smul, ← smul_assoc, Matrix.mulVec_mulVec]
  constructor
  · intro h
    refine Matrix.toLin'.injective (LinearMap.ext fun v ↦ ?_)
    simpa [key] using congr($h (fun _ ↦ v) φ₀)
  · intro h
    ext y φ i
    by_cases hφ : φ = φ₀
    · subst hφ
      simp [key, h]
    · simp [hφ, ← mul_assoc]

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [Module ℂ V]

/-- A **period map for `J`**: a real-linear isomorphism `Q` from `Φ → n → ℂ` (for a CM field `E`,
the coordinates of `(E ⊗ ℝ)ⁿ` through `Φ`) onto a complex vector space `V` whose real structure
is the restriction of its complex one, carrying the period structure of `J` (`i·J` at `φ₀`, `i`
elsewhere) to multiplication by `i`. -/
structure IsPeriodMap (Φ : CMType E) (φ₀ : Φ) (J : Matrix n n ℂ) [IsScalarTower ℝ ℂ V]
    (Q : (Φ → n → ℂ) ≃ₗ[ℝ] V) : Prop where
  /-- `Q` carries the period structure to multiplication by `i`. -/
  map_periodStructure (y : Φ → n → ℂ) : Q (Φ.periodStructure φ₀ J y) = I • Q y

/-- Unfolding `IsPeriodMap`: `Q (𝒥 y) = i • Q y` for every `y`. -/
theorem isPeriodMap_iff [IsScalarTower ℝ ℂ V] {J : Matrix n n ℂ} {Q : (Φ → n → ℂ) ≃ₗ[ℝ] V} :
    IsPeriodMap Φ φ₀ J Q ↔ ∀ y, Q (Φ.periodStructure φ₀ J y) = I • Q y :=
  ⟨fun h ↦ h.map_periodStructure, fun h ↦ ⟨h⟩⟩

/-- A period map for `J` exists only if `J * J = 1`: applying it twice, `𝒥 ∘ 𝒥` becomes
multiplication by `i² = -1`. -/
theorem IsPeriodMap.mul_self_eq_one [DecidableEq n] [IsScalarTower ℝ ℂ V] {J : Matrix n n ℂ}
    {Q : (Φ → n → ℂ) ≃ₗ[ℝ] V} (hQ : IsPeriodMap Φ φ₀ J Q) : J * J = 1 := by
  refine (periodStructure_comp_self_eq_neg_id_iff (Φ := Φ) (φ₀ := φ₀) J).1 <|
    LinearMap.ext fun y ↦ Q.injective ?_
  simp [hQ.map_periodStructure, smul_smul]

/-- For `J * J = 1` a period map for `J` exists: the identity of `Φ → n → ℂ`, onto the same real
space with the complex structure in which `i` acts as the period structure of `J`. -/
theorem exists_isPeriodMap [DecidableEq n] {J : Matrix n n ℂ} (hJ : J * J = 1) :
    ∃ (W : Type (max u v)) (_ : AddCommGroup W) (_ : Module ℝ W) (_ : Module ℂ W)
      (_ : IsScalarTower ℝ ℂ W) (Q : (Φ → n → ℂ) ≃ₗ[ℝ] W), IsPeriodMap Φ φ₀ J Q := by
  let A : AlmostComplexStructure (Φ → n → ℂ) :=
    ⟨(Φ.periodStructure φ₀ J).restrictScalars ℝ, by
      ext1 y
      exact congr($((periodStructure_comp_self_eq_neg_id_iff J).2 hJ) y)⟩
  let := A.complexModule
  have := A.complexModule_isScalarTower
  exact ⟨Φ → n → ℂ, inferInstance, inferInstance, A.complexModule, A.complexModule_isScalarTower,
    .refl ℝ _, ⟨fun y ↦ (A.complexModule_I_smul y).symm⟩⟩

/-- For a period map `Q` for `J`, `Module.finrank ℂ V = Fintype.card n * Nat.card Φ`: the
dimension count `dim_ℂ V = |n|·|Φ|` for finite `Φ`; for infinite `Φ` both sides are `0`. Only the
real-linear isomorphism `Q` is used (`LinearEquiv.finrank_complex_eq_nat_card`). -/
theorem IsPeriodMap.finrank_complex_eq [IsScalarTower ℝ ℂ V] {J : Matrix n n ℂ}
    {Q : (Φ → n → ℂ) ≃ₗ[ℝ] V} (_ : IsPeriodMap Φ φ₀ J Q) :
    Module.finrank ℂ V = Fintype.card n * Nat.card Φ := by
  rw [((LinearEquiv.curry ℝ ℂ Φ n).trans Q).finrank_complex_eq_nat_card, Nat.card_prod,
    Nat.card_eq_fintype_card (α := n), mul_comm]

/-- For a period map `Q` for `J` over a number field `K`,
`2 * Module.finrank ℂ V = Fintype.card n * Module.finrank ℚ K`, that is `2 · dim_ℂ V = |n|·[K : ℚ]`.
-/
theorem IsPeriodMap.two_mul_finrank_eq {K : Type*} [Field K] [NumberField K] {Ψ : CMType K}
    {ψ₀ : Ψ} [IsScalarTower ℝ ℂ V] {J : Matrix n n ℂ} {Q : (Ψ → n → ℂ) ≃ₗ[ℝ] V}
    (hQ : IsPeriodMap Ψ ψ₀ J Q) :
    2 * Module.finrank ℂ V = Fintype.card n * Module.finrank ℚ K := by
  rw [hQ.finrank_complex_eq, ← Ψ.two_mul_card_eq_finrank]
  ring

end TauCeti.CMType
