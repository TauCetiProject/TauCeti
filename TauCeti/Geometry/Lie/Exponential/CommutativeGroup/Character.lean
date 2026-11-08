/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.ContinuousFunctor
public import TauCeti.Geometry.Lie.Exponential.Circle
public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Basic
public import TauCeti.Geometry.Toric.Algebraic.Lattice
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The period lattice and the real weights of circle characters

Let `G` be a commutative finite-dimensional real Lie group with Lie algebra `𝔤` and exponential
`exp : 𝔤 → G`. With the circle period `2π` of `Circle.exp t = e^{it}`, the **period lattice** of
`G` is

`Λ_ℤ = (2π)⁻¹ ker(exp) = {X ∈ 𝔤 | exp(2π X) = 1}`

(`TauCeti.periodLattice`). It is a discrete subgroup of `𝔤`, and for compact `G` it is a full
lattice, which exhibits `𝔤` as the real scalar extension of `Λ_ℤ`
(`TauCeti.isIntegralLattice_periodLattice`).

A continuous character `χ : G → Circle` has a **real weight** `α_χ = (1/i) dχ`
(`ContinuousMonoidHom.lieWeight`), the real-linear functional on `𝔤` obtained from the Lie map of
`χ` through the identification of the Lie algebra of the circle with `ℝ` under which the abstract
exponential of the circle is `Circle.exp`. It is characterized by

`χ (exp X) = Circle.exp (α_χ X)`

(`ContinuousMonoidHom.apply_lieExp_eq_circleExp_lieWeight`, `ContinuousMonoidHom.eq_lieWeight`).
The weight of a product of characters is the sum of the weights, and the weight of `χ ∘ f` is
`α_χ ∘ df`. On the period lattice weights take integer values: for `λ ∈ ker(exp)` the number
`α_χ(λ) / (2π)` is an integer.

For connected `G` these weights are exactly the integral functionals: a character is determined
by its weight, and every real-linear functional taking integer values on `Λ_ℤ` is the weight of a
character (`ContinuousMonoidHom.range_lieWeight`). So the character group of a torus is the
lattice dual to `Λ_ℤ`. For the circle itself `Λ_ℤ` corresponds to `ℤ ⊆ ℝ` and the identity
character has weight one, which fixes the normalization.

This is the normalization of weights of torus actions: a commutative group acting on `ℂ` through
a character `χ` acts by `exp(ξ) · z = e^{i α_χ(ξ)} z`.

## Main definitions

* `TauCeti.periodLattice I G`: the period lattice `Λ_ℤ = (2π)⁻¹ ker(exp)`.
* `ContinuousMonoidHom.lieWeight χ`: the real weight `α_χ` of a circle character.

## Main results

* `TauCeti.mem_periodLattice`: `X ∈ Λ_ℤ ↔ exp(2π X) = 1`.
* `TauCeti.isZLattice_periodLattice`, `TauCeti.isIntegralLattice_periodLattice`: for compact `G`,
  the period lattice is a full lattice, and `𝔤` is its real scalar extension.
* `ContinuousMonoidHom.lieMap_mem_periodLattice`: continuous homomorphisms preserve period lattices.
* `ContinuousMonoidHom.apply_lieExp_eq_circleExp_lieWeight`, `ContinuousMonoidHom.eq_lieWeight`:
  the defining identity `χ (exp X) = Circle.exp (α_χ X)`, and uniqueness of a functional
  satisfying it.
* `ContinuousMonoidHom.lieWeight_mul`, `ContinuousMonoidHom.lieWeight_comp`: weights are additive
  in the character and natural in the group.
* `ContinuousMonoidHom.exists_lieWeight_apply_eq_intCast_mul_of_mem_ker`,
  `ContinuousMonoidHom.exists_lieWeight_apply_eq_intCast_of_mem_periodLattice`: integrality of
  weights on the kernel of the exponential and on the period lattice.
* `ContinuousMonoidHom.lieWeight_injective`, `ContinuousMonoidHom.range_lieWeight`: for connected
  `G`, characters correspond exactly to functionals taking integer values on `Λ_ℤ`.
* `TauCeti.mem_periodLattice_circle`, `ContinuousMonoidHom.lieWeight_id_circle`: the circle case.

## References

* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapter 15 (Tori).
* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter I, § 3 (The Exponential Map).
-/

public section

noncomputable section

open Real
open scoped ContDiff Manifold

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
  [IsMulCommutative G]

/-! ### The period lattice -/

variable (I G) in
/-- The **period lattice** `Λ_ℤ = (2π)⁻¹ ker(exp)` of a commutative Lie group: the elements `X` of
the Lie algebra with `exp(2π X) = 1`. -/
def periodLattice : AddSubgroup (LeftInvariantDerivation I G) :=
  (lieExpAddMonoidHom (I := I) (G := G)).ker.comap
    (DistribSMul.toAddMonoidHom (LeftInvariantDerivation I G) (2 * π))

/-- Membership in the period lattice: `X ∈ Λ_ℤ` exactly when `exp(2π X) = 1`. -/
@[simp]
theorem mem_periodLattice {X : LeftInvariantDerivation I G} :
    X ∈ periodLattice I G ↔ lieExp ((2 * π) • X) = 1 := by
  rw [periodLattice, AddSubgroup.mem_comap, DistribSMul.toAddMonoidHom_apply,
    mem_ker_lieExpAddMonoidHom]

/-- An element of the kernel of the exponential is `2π` times an element of the period lattice. -/
theorem inv_two_pi_smul_mem_periodLattice_iff {X : LeftInvariantDerivation I G} :
    (2 * π)⁻¹ • X ∈ periodLattice I G ↔ X ∈ (lieExpAddMonoidHom (I := I) (G := G)).ker := by
  rw [mem_periodLattice, smul_inv_smul₀ two_pi_pos.ne', mem_ker_lieExpAddMonoidHom]

/-- The period lattice is the kernel of the exponential scaled by `(2π)⁻¹`. -/
theorem periodLattice_eq_map :
    periodLattice I G = (lieExpAddMonoidHom (I := I) (G := G)).ker.map
      (DistribSMul.toAddMonoidHom (LeftInvariantDerivation I G) (2 * π)⁻¹) := by
  ext X
  rw [AddSubgroup.mem_map]
  refine ⟨fun hX ↦ ⟨(2 * π) • X, mem_ker_lieExpAddMonoidHom.2 (mem_periodLattice.1 hX), ?_⟩, ?_⟩
  · rw [DistribSMul.toAddMonoidHom_apply, inv_smul_smul₀ two_pi_pos.ne']
  · rintro ⟨Y, hY, rfl⟩
    exact inv_two_pi_smul_mem_periodLattice_iff.2 hY

/-- **The period lattice is discrete.** -/
instance discreteTopology_periodLattice : DiscreteTopology (periodLattice I G) :=
  DiscreteTopology.of_continuous_injective
    (f := fun X : periodLattice I G ↦
      (⟨(2 * π) • (X : LeftInvariantDerivation I G),
        mem_ker_lieExpAddMonoidHom.2 (mem_periodLattice.1 X.2)⟩ :
        (lieExpAddMonoidHom (I := I) (G := G)).ker))
    (by fun_prop)
    (fun X Y h ↦ Subtype.ext (smul_right_injective _ two_pi_pos.ne' (congrArg Subtype.val h)))

section Compact

variable [IsTopologicalGroup G] [CompactSpace G]

/-- The Lie algebra is finite-dimensional; a local instance for this section. -/
local instance : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
  finiteDimensional_leftInvariantDerivation
    (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))

/-- **The period lattice of a compact commutative Lie group spans the Lie algebra.** -/
theorem span_periodLattice_eq_top :
    Submodule.span ℝ (periodLattice I G : Set (LeftInvariantDerivation I G)) = ⊤ := by
  rw [eq_top_iff, ← span_ker_lieExpAddMonoidHom_eq_top (I := I) (G := G), Submodule.span_le]
  intro X hX
  rw [← smul_inv_smul₀ two_pi_pos.ne' X]
  exact Submodule.smul_mem _ _
    (Submodule.subset_span (inv_two_pi_smul_mem_periodLattice_iff.2 hX))

/-- **The period lattice of a compact commutative Lie group is a full lattice.** -/
instance isZLattice_periodLattice : IsZLattice ℝ (periodLattice I G).toIntSubmodule where
  span_top := by
    rw [AddSubgroup.coe_toIntSubmodule]
    exact span_periodLattice_eq_top

/-- **The Lie algebra of a compact commutative Lie group is the real scalar extension of its
period lattice.** -/
theorem isIntegralLattice_periodLattice :
    Toric.IsIntegralLattice (periodLattice I G).subtype :=
  Toric.isIntegralLattice_subtype_of_isZLattice (periodLattice I G).toIntSubmodule

end Compact

/-- **The period lattice of the circle** corresponds to `ℤ ⊆ ℝ` under the identification of the
Lie algebra of the circle with `ℝ` normalized by `Circle.exp`. -/
theorem mem_periodLattice_circle {X : LeftInvariantDerivation (𝓡 1) Circle} :
    X ∈ periodLattice (𝓡 1) Circle ↔ ∃ n : ℤ, circleLieAlgebraEquiv X = n := by
  rw [mem_periodLattice, ← circleLieAlgebraEquiv.symm_apply_apply X, ← map_smul, lieExp_circle,
    LinearEquiv.apply_symm_apply, smul_eq_mul, Circle.exp_eq_one]
  refine exists_congr fun n ↦ ?_
  constructor <;> intro h <;> nlinarith [two_pi_pos]

end TauCeti

namespace ContinuousMonoidHom

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G]

/-! ### Period lattices under homomorphisms -/

/-- **Continuous homomorphisms preserve period lattices.** -/
theorem lieMap_mem_periodLattice
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G']
    [FiniteDimensional ℝ E'] [LieGroup I' ∞ G'] [T2Space G'] [BoundarylessManifold I' G']
    [T2Space G] [BoundarylessManifold I G]
    [IsMulCommutative G] [IsMulCommutative G'] (f : G →ₜ* G') {X : LeftInvariantDerivation I G}
    (hX : X ∈ periodLattice I G) :
    lieMap (I := I) (I' := I') f X ∈ periodLattice I' G' := by
  rw [mem_periodLattice] at hX ⊢
  rw [← map_smul, ← map_lieExp, hX, map_one]

/-! ### The real weight of a circle character -/

/-- The **real weight** `α_χ = (1/i) dχ` of a continuous character `χ : G → Circle`: the Lie map of
`χ` followed by the identification of the Lie algebra of the circle with `ℝ` under which the
abstract exponential of the circle is `Circle.exp`. It is characterized by
`χ (exp X) = Circle.exp (α_χ X)` (`ContinuousMonoidHom.apply_lieExp_eq_circleExp_lieWeight`). -/
def lieWeight (χ : G →ₜ* Circle) : Module.Dual ℝ (LeftInvariantDerivation I G) :=
  circleLieAlgebraEquiv.toLinearMap ∘ₗ (lieMap (I := I) (I' := 𝓡 1) χ).toLinearMap

theorem lieWeight_apply (χ : G →ₜ* Circle) (X : LeftInvariantDerivation I G) :
    lieWeight χ X = circleLieAlgebraEquiv (lieMap (I := I) (I' := 𝓡 1) χ X) :=
  (rfl)

/-- **Naturality of weights.** The weight of `χ ∘ f` is the weight of `χ` composed with the Lie
map of `f`. -/
theorem lieWeight_comp
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G']
    [FiniteDimensional ℝ E'] [LieGroup I' ∞ G'] (χ : G' →ₜ* Circle) (f : G →ₜ* G') :
    lieWeight (I := I) (χ.comp f) =
      lieWeight (I := I') (G := G') χ ∘ₗ (lieMap (I := I) (I' := I') f).toLinearMap := by
  ext X
  rw [lieWeight_apply (I := I), lieMap_comp (I := I) (I' := I') (I'' := 𝓡 1),
    LinearMap.comp_apply, LieHom.coe_toLinearMap, lieWeight_apply (I := I'), LieHom.comp_apply]

/-- **Characters are determined by their weights** on a connected Lie group. -/
theorem lieWeight_injective [PreconnectedSpace G] :
    Function.Injective (lieWeight (I := I) : (G →ₜ* Circle) → _) := by
  intro χ ψ h
  apply lieMap_injective (I := I) (I' := 𝓡 1)
  refine LieHom.coe_injective (funext fun X ↦ circleLieAlgebraEquiv.injective ?_)
  exact LinearMap.congr_fun h X

variable [T2Space G] [BoundarylessManifold I G]

/-- **The defining identity of the real weight**: `χ (exp X) = Circle.exp (α_χ X)`. -/
@[simp]
theorem apply_lieExp_eq_circleExp_lieWeight (χ : G →ₜ* Circle)
    (X : LeftInvariantDerivation I G) :
    χ (lieExp X) = Circle.exp (lieWeight χ X) := by
  rw [map_lieExp (I' := 𝓡 1), lieWeight_apply, ← lieExp_circle,
    LinearEquiv.symm_apply_apply]

/-- **Uniqueness of the real weight.** A real-linear functional `α` with
`χ (exp X) = Circle.exp (α X)` for every `X` is the weight of `χ`. -/
theorem eq_lieWeight {χ : G →ₜ* Circle} {α : Module.Dual ℝ (LeftInvariantDerivation I G)}
    (h : ∀ X, χ (lieExp X) = Circle.exp (α X)) : α = lieWeight χ := by
  ext X
  by_contra hne
  have hc : α X - lieWeight χ X ≠ 0 := sub_ne_zero.2 hne
  -- At `(π / c) • X`, where `c = α X - α_χ X`, the two exponentials differ by `Circle.exp π`.
  have hX := h ((π / (α X - lieWeight χ X)) • X)
  rw [apply_lieExp_eq_circleExp_lieWeight, LinearMap.map_smul, LinearMap.map_smul, smul_eq_mul,
    smul_eq_mul] at hX
  have hπ : Circle.exp π = 1 := by
    rw [show π = π / (α X - lieWeight χ X) * α X - π / (α X - lieWeight χ X) * lieWeight χ X by
      field_simp, Circle.exp_sub, ← hX, div_self']
  exact Circle.exp_pi_ne_one hπ

/-- The trivial character has weight zero. -/
@[simp]
theorem lieWeight_one : lieWeight (I := I) (1 : G →ₜ* Circle) = 0 :=
  (eq_lieWeight fun X ↦ by rw [LinearMap.zero_apply, Circle.exp_zero, one_toFun]).symm

/-- **Weights are additive**: the weight of a product of characters is the sum of the weights. -/
@[simp]
theorem lieWeight_mul (χ ψ : G →ₜ* Circle) :
    lieWeight (I := I) (χ * ψ) = lieWeight χ + lieWeight ψ :=
  (eq_lieWeight fun X ↦ by
    rw [mul_apply, apply_lieExp_eq_circleExp_lieWeight, apply_lieExp_eq_circleExp_lieWeight,
      LinearMap.add_apply, Circle.exp_add]).symm

/-- The weight of the inverse character is the negative weight. -/
@[simp]
theorem lieWeight_inv (χ : G →ₜ* Circle) : lieWeight (I := I) χ⁻¹ = -lieWeight χ := by
  rw [eq_neg_iff_add_eq_zero, ← lieWeight_mul, inv_mul_cancel, lieWeight_one]

/-- The weight of a power of a character is the corresponding multiple of its weight. -/
@[simp]
theorem lieWeight_pow (χ : G →ₜ* Circle) (n : ℕ) :
    lieWeight (I := I) (χ ^ n) = n • lieWeight χ := by
  induction n with
  | zero => rw [pow_zero, lieWeight_one, zero_smul]
  | succ n ih => rw [pow_succ, lieWeight_mul, ih, succ_nsmul]

/-- The weight of an integer power of a character is the corresponding multiple of its weight. -/
@[simp]
theorem lieWeight_zpow (χ : G →ₜ* Circle) (n : ℤ) :
    lieWeight (I := I) (χ ^ n) = n • lieWeight χ := by
  cases n with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast, lieWeight_pow, natCast_zsmul]
  | negSucc n => rw [zpow_negSucc, lieWeight_inv, lieWeight_pow, negSucc_zsmul]

/-- The identity character of the circle has weight one: its weight is the identification of the
Lie algebra of the circle with `ℝ`. -/
@[simp]
theorem lieWeight_id_circle :
    lieWeight (I := 𝓡 1) (ContinuousMonoidHom.id Circle) = circleLieAlgebraEquiv.toLinearMap :=
  (eq_lieWeight fun X ↦ by
    rw [coe_id, id_eq, LinearEquiv.coe_coe, ← lieExp_circle, LinearEquiv.symm_apply_apply]).symm

/-! ### Integrality of weights -/

section Integral

variable [IsMulCommutative G]

/-- **Weights are integral on the kernel of the exponential**: for `exp λ = 1`, the number
`α_χ(λ) / (2π)` is an integer. -/
theorem exists_lieWeight_apply_eq_intCast_mul_of_mem_ker (χ : G →ₜ* Circle)
    {X : LeftInvariantDerivation I G} (hX : X ∈ (lieExpAddMonoidHom (I := I) (G := G)).ker) :
    ∃ n : ℤ, lieWeight χ X = n * (2 * π) := by
  rw [← Circle.exp_eq_one, ← apply_lieExp_eq_circleExp_lieWeight,
    (mem_ker_lieExpAddMonoidHom (I := I)).1 hX, map_one]

/-- **Weights take integer values on the period lattice.** -/
theorem exists_lieWeight_apply_eq_intCast_of_mem_periodLattice (χ : G →ₜ* Circle)
    {X : LeftInvariantDerivation I G} (hX : X ∈ periodLattice I G) :
    ∃ n : ℤ, lieWeight χ X = n := by
  obtain ⟨n, hn⟩ := exists_lieWeight_apply_eq_intCast_mul_of_mem_ker χ
    ((mem_ker_lieExpAddMonoidHom (I := I)).2 (mem_periodLattice.1 hX))
  refine ⟨n, mul_right_cancel₀ two_pi_pos.ne' ?_⟩
  rw [← hn, map_smul, smul_eq_mul, mul_comm]

variable [IsTopologicalGroup G] [PreconnectedSpace G]

/-- The Lie algebra is finite-dimensional; a local instance for this section. -/
local instance : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
  finiteDimensional_leftInvariantDerivation
    (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))

/-- **Every integral functional is a weight.** On a connected commutative Lie group, a real-linear
functional taking integer values on the period lattice is the weight of a continuous character. -/
theorem exists_lieWeight_eq {α : Module.Dual ℝ (LeftInvariantDerivation I G)}
    (hα : ∀ X ∈ periodLattice I G, ∃ n : ℤ, α X = n) :
    ∃ χ : G →ₜ* Circle, lieWeight χ = α := by
  -- `X ↦ Circle.exp (α X)` kills the kernel of the exponential, so it factors through
  -- `𝔤 ⧸ ker(exp) ≃ G`.
  let N := (lieExpAddMonoidHom (I := I) (G := G)).ker
  let φ : LeftInvariantDerivation I G →+ Additive Circle :=
    Circle.expHom.comp α.toAddMonoidHom
  have hN : N ≤ φ.ker := by
    intro X hX
    obtain ⟨n, hn⟩ := hα _ (inv_two_pi_smul_mem_periodLattice_iff.2 hX)
    rw [map_smul, smul_eq_mul] at hn
    have hαX : α X = n * (2 * π) := by
      field_simp at hn
      linarith
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, hαX]
    exact Circle.exp_int_mul_two_pi n
  let ψ := QuotientAddGroup.lift N φ hN
  have hψmk : ⇑ψ ∘ QuotientAddGroup.mk = Additive.ofMul ∘ Circle.exp ∘ α := by
    funext X
    simp only [ψ, φ, Function.comp_apply, QuotientAddGroup.lift_mk, AddMonoidHom.comp_apply,
      Circle.expHom_apply, LinearMap.toAddMonoidHom_coe]
  have hψ : Continuous ψ := by
    rw [(QuotientAddGroup.isQuotientMap_mk N).continuous_iff, hψmk]
    exact continuous_ofMul.comp (Circle.exp.continuous.comp α.continuous_of_finiteDimensional)
  let e := lieExpQuotientKerContinuousAddEquiv (I := I) (G := G)
  let χ : G →ₜ* Circle :=
    { toFun := fun g ↦ Additive.toMul (ψ (e.symm (Additive.ofMul g)))
      map_one' := by rw [ofMul_one, map_zero, map_zero, toMul_zero]
      map_mul' := fun g h ↦ by rw [ofMul_mul, map_add, map_add, toMul_add]
      continuous_toFun := continuous_toMul.comp
        (hψ.comp (e.symm.continuous.comp continuous_ofMul)) }
  have hχ (g : G) : χ g = Additive.toMul (ψ (e.symm (Additive.ofMul g))) := rfl
  refine ⟨χ, (eq_lieWeight fun X ↦ ?_).symm⟩
  rw [hχ, lieExpQuotientKerContinuousAddEquiv_symm_apply, ← Function.comp_apply (f := ⇑ψ), hψmk,
    Function.comp_apply, Function.comp_apply, toMul_ofMul]

/-- **The character lattice is dual to the period lattice.** On a connected commutative Lie group,
the weights of continuous characters are exactly the real-linear functionals taking integer values
on the period lattice. -/
theorem range_lieWeight :
    Set.range (lieWeight (I := I) : (G →ₜ* Circle) → _) =
      {α : Module.Dual ℝ (LeftInvariantDerivation I G) |
        ∀ X ∈ periodLattice I G, ∃ n : ℤ, α X = n} := by
  ext α
  exact ⟨by rintro ⟨χ, rfl⟩ X hX; exact exists_lieWeight_apply_eq_intCast_of_mem_periodLattice χ hX,
    exists_lieWeight_eq⟩

end Integral

end ContinuousMonoidHom
