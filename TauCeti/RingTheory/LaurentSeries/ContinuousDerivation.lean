/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import TauCeti.RingTheory.Derivation.Localization
public import TauCeti.RingTheory.LaurentSeries.Derivative

/-!
# Continuous derivations of formal Laurent series

Let `K` be a field and `F = K⸨X⸩`, with the valuation topology, and let `D` be the formal
derivative `TauCeti.laurentSeriesDerivation K`. This file shows that the continuous
`K`-derivations `F → F` are exactly the multiples `a • D` with `a : F`, and that `a = δ X` is
the value of such a derivation `δ` at the parameter `X = single 1 1`.

The algebraic part of the argument holds for every derivation: `δ` agrees with `δ X • D` on the
rational functions `K(X)`, since both are derivations of the fraction field of `K[X]` with the
same value at `X`. Continuity then extends the agreement from `K(X)` to `F`, because `K(X)` is
dense in `F` (`LaurentSeries.coe_range_dense`) and two continuous maps to the Hausdorff space `F`
that agree on a dense subset are equal.

The continuous derivations form an `F`-submodule `TauCeti.continuousDerivations K` of
`Derivation K F F`, which `TauCeti.continuousDerivationsEquiv K` identifies with `F` itself.
Their commutator makes them a Lie subalgebra of the Laurent derivations, whose Lie structure
and coefficient formula are defined in `LaurentSeries.Derivative`. The subalgebras preserving the
embedded power-series ring and its maximal ideal are respectively `K⟦X⟧ D` and `X K⟦X⟧ D`. These
classifications hold in every characteristic.

## Main results

* `Polynomial.aeval_single_one_eq_algebraMap`: a polynomial evaluated at `X = single 1 1` is its
  image as a Laurent series.
* `Derivation.apply_coe_ratFunc`: on rational functions every `K`-derivation `δ` is `δ X • D`.
* `Derivation.eq_smul_laurentSeriesDerivation`: a continuous derivation `δ` equals `δ X • D`.
* `TauCeti.continuous_smul_laurentSeriesDerivation`: conversely every `a • D` is continuous.
* `Derivation.continuous_iff_exists_eq_smul_laurentSeriesDerivation`: a derivation is continuous
  if and only if it is a multiple of `D`, and `TauCeti.smul_laurentSeriesDerivation_inj`: the
  multiple is unique.
* `Derivation.apply_eq_laurentSeriesDerivation_smul` and
  `Derivation.continuous_iff_exists_apply_eq_laurentSeriesDerivation_smul`: the same
  classification for derivations into any `F`-module with its module topology, `δ f = D f • δ X`.
* `TauCeti.continuousDerivations`: the `F`-submodule of continuous derivations, and
  `TauCeti.continuousDerivationsEquiv`: its identification with `F` sending `a` to `a • D`.
* `TauCeti.continuousDerivationsLieSubalgebra`: continuous derivations as a Lie subalgebra.
* `TauCeti.mem_powerSeriesPreservingDerivations_iff` and
  `TauCeti.mem_maximalIdealPreservingDerivations_iff`: the two coefficient classifications.
-/

public section

open HahnSeries Polynomial RatFunc
open scoped LaurentSeries PowerSeries

/-- A polynomial evaluated at the parameter `X = single 1 1` of `R⸨X⸩` is its image as a Laurent
series. -/
theorem Polynomial.aeval_single_one_eq_algebraMap {R : Type*} [CommSemiring R] (p : R[X]) :
    aeval (single 1 1 : R⸨X⸩) p = algebraMap R[X] R⸨X⸩ p := by
  induction p using Polynomial.induction_on with
  | C a =>
    simp [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, PowerSeries.algebraMap_apply']
  | add p q hp hq => simp [hp, hq]
  | monomial n a h => simp_all [pow_succ, ← mul_assoc]

namespace TauCeti

/-- A multiple of the formal derivative determines the multiplier. -/
@[simp]
theorem smul_laurentSeriesDerivation_inj {R : Type*} [CommRing R] {a b : R⸨X⸩} :
    a • laurentSeriesDerivation R = b • laurentSeriesDerivation R ↔ a = b := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  simpa using congr($h (single 1 1))

variable {K : Type*} [Field K]

/-- Every multiple of the formal derivative is continuous for the valuation topology. -/
theorem continuous_smul_laurentSeriesDerivation (a : K⸨X⸩) :
    Continuous (a • laurentSeriesDerivation K) := by
  refine continuous_const.mul ?_
  -- The body of `laurentSeriesDerivation` is not exposed, so match its coercion explicitly.
  convert LaurentSeries.continuous_derivative (K := K) using 1
  exact funext (laurentSeriesDerivation_apply K)

end TauCeti

variable {K : Type*} [Field K]

namespace Derivation

/-- On rational functions, every `K`-derivation `δ` of `K⸨X⸩` agrees with `δ X • D`, where `D` is
the formal derivative: both are derivations of `K(X)` with the same value at `X`. -/
theorem apply_coe_ratFunc (δ : Derivation K K⸨X⸩ K⸨X⸩) (r : RatFunc K) :
    δ r = δ (single 1 1) * TauCeti.laurentSeriesDerivation K r := by
  set δ' := δ (single 1 1) • TauCeti.laurentSeriesDerivation K
  have hX : δ (single 1 1) = δ' (single 1 1) := by simp [δ']
  have h := IsLocalization.eq_of_leibniz (nonZeroDivisors K[X])
    (δ₁ := fun r : RatFunc K ↦ δ r) (δ₂ := fun r : RatFunc K ↦ δ' r)
    (fun x y ↦ by simp only [map_mul, leibniz, Algebra.smul_def, Algebra.algebraMap_self,
      RingHom.id_apply])
    (fun x y ↦ by simp only [map_mul, leibniz, Algebra.smul_def, Algebra.algebraMap_self,
      RingHom.id_apply])
    fun p ↦ by
      simp only [← IsScalarTower.algebraMap_apply, ← aeval_single_one_eq_algebraMap, map_aeval,
        hX]
  simpa [δ'] using congrFun h r

/-- **Continuous derivations of Laurent series.** A `K`-derivation `δ` of `K⸨X⸩` that is continuous
for the valuation topology is the multiple `δ X • D` of the formal derivative `D`. -/
theorem eq_smul_laurentSeriesDerivation (δ : Derivation K K⸨X⸩ K⸨X⸩) (hδ : Continuous δ) :
    δ = δ (single 1 1) • TauCeti.laurentSeriesDerivation K := by
  refine DFunLike.coe_injective <|
    LaurentSeries.coe_range_dense.equalizer hδ
      (TauCeti.continuous_smul_laurentSeriesDerivation _) ?_
  funext r
  rw [Function.comp_apply, Function.comp_apply, apply_coe_ratFunc, smul_apply, smul_eq_mul]

/-- A `K`-derivation of `K⸨X⸩` is continuous for the valuation topology if and only if it is a
multiple of the formal derivative. -/
theorem continuous_iff_exists_eq_smul_laurentSeriesDerivation {δ : Derivation K K⸨X⸩ K⸨X⸩} :
    Continuous δ ↔ ∃ a : K⸨X⸩, δ = a • TauCeti.laurentSeriesDerivation K := by
  refine ⟨fun hδ ↦ ⟨_, δ.eq_smul_laurentSeriesDerivation hδ⟩, ?_⟩
  rintro ⟨a, rfl⟩
  exact TauCeti.continuous_smul_laurentSeriesDerivation a

variable {M : Type*} [AddCommGroup M] [Module K⸨X⸩ M] [Module K M]
  [IsScalarTower K K⸨X⸩ M] [TopologicalSpace M] [IsModuleTopology K⸨X⸩ M]

/-- **Continuous derivations of Laurent series into a topological module.** A `K`-derivation
`δ : K⸨X⸩ → M` into a `K⸨X⸩`-module with its module topology that is continuous for the valuation
topology satisfies `δ f = D f • δ X`, where `D` is the formal derivative. -/
theorem apply_eq_laurentSeriesDerivation_smul (δ : Derivation K K⸨X⸩ M) (hδ : Continuous δ)
    (f : K⸨X⸩) : δ f = TauCeti.laurentSeriesDerivation K f • δ (single 1 1) := by
  let b := Module.Free.chooseBasis K⸨X⸩ M
  refine b.ext_elem fun i ↦ ?_
  -- Each coordinate of `δ` is a continuous derivation of `K⸨X⸩` into itself.
  have hc : Continuous ((b.coord i).compDer δ) :=
    (IsModuleTopology.continuous_of_linearMap (b.coord i)).comp hδ
  simpa [mul_comm] using congr($(((b.coord i).compDer δ).eq_smul_laurentSeriesDerivation hc) f)

/-- A `K`-derivation of `K⸨X⸩` into a `K⸨X⸩`-module with its module topology is continuous if and
only if it is `f ↦ D f • m` for some `m`, where `D` is the formal derivative. -/
theorem continuous_iff_exists_apply_eq_laurentSeriesDerivation_smul {δ : Derivation K K⸨X⸩ M} :
    Continuous δ ↔ ∃ m : M, ∀ f, δ f = TauCeti.laurentSeriesDerivation K f • m := by
  refine ⟨fun hδ ↦ ⟨_, δ.apply_eq_laurentSeriesDerivation_smul hδ⟩, ?_⟩
  rintro ⟨m, hm⟩
  have h : (δ : K⸨X⸩ → M) = fun f ↦ LaurentSeries.derivative K f • m :=
    funext fun f ↦ by simp [hm]
  rw [h]
  exact LaurentSeries.continuous_derivative.smul continuous_const

end Derivation

namespace TauCeti

variable (K) in
/-- The `K⸨X⸩`-submodule of `K`-derivations of `K⸨X⸩` that are continuous for the valuation
topology. -/
def continuousDerivations : Submodule K⸨X⸩ (Derivation K K⸨X⸩ K⸨X⸩) where
  carrier := {δ | Continuous δ}
  add_mem' hδ hδ' := hδ.add hδ'
  zero_mem' := continuous_zero
  smul_mem' _ _ hδ := continuous_const.mul hδ

@[simp]
theorem mem_continuousDerivations {δ : Derivation K K⸨X⸩ K⸨X⸩} :
    δ ∈ continuousDerivations K ↔ Continuous δ :=
  Iff.rfl

variable (K) in
/-- **The continuous derivations of `K⸨X⸩` form a free module of rank one** with basis the formal
derivative `D`: the equivalence sends `a` to `a • D`, and its inverse evaluates a derivation at the
parameter `X`. -/
noncomputable def continuousDerivationsEquiv : K⸨X⸩ ≃ₗ[K⸨X⸩] continuousDerivations K where
  toFun a := ⟨a • laurentSeriesDerivation K, continuous_smul_laurentSeriesDerivation a⟩
  map_add' a b := Subtype.ext (add_smul a b _)
  map_smul' a b := Subtype.ext (smul_assoc a b _)
  invFun δ := (δ : Derivation K K⸨X⸩ K⸨X⸩) (single 1 1)
  left_inv a := by simp
  right_inv δ := Subtype.ext (δ.1.eq_smul_laurentSeriesDerivation δ.2).symm

@[simp]
theorem coe_continuousDerivationsEquiv_apply (a : K⸨X⸩) :
    (continuousDerivationsEquiv K a : Derivation K K⸨X⸩ K⸨X⸩) = a • laurentSeriesDerivation K :=
  (rfl)

@[simp]
theorem continuousDerivationsEquiv_symm_apply (δ : continuousDerivations K) :
    (continuousDerivationsEquiv K).symm δ = (δ : Derivation K K⸨X⸩ K⸨X⸩) (single 1 1) :=
  (rfl)

variable (K) in
/-- Continuous Laurent derivations, with their commutator Lie algebra structure over `K`. -/
noncomputable def continuousDerivationsLieSubalgebra :
    LieSubalgebra K (Derivation K K⸨X⸩ K⸨X⸩) where
  toSubmodule := (continuousDerivations K).restrictScalars K
  lie_mem' {δ ε} hδ hε :=
    ((hδ.comp hε).sub (hε.comp hδ)).congr
      (fun f ↦ (Derivation.laurentSeries_commutator_apply δ ε f).symm)

@[simp]
theorem mem_continuousDerivationsLieSubalgebra {δ : Derivation K K⸨X⸩ K⸨X⸩} :
    δ ∈ continuousDerivationsLieSubalgebra K ↔ Continuous δ :=
  Iff.rfl

variable (K) in
/-- Continuous Laurent vector fields preserving the power-series ring `K⟦X⟧`. -/
noncomputable def powerSeriesPreservingDerivations :
    LieSubalgebra K (Derivation K K⸨X⸩ K⸨X⸩) where
  carrier := {δ | Continuous δ ∧ ∀ f : K⟦X⟧, ∃ g : K⟦X⟧, δ (f : K⸨X⸩) = g}
  zero_mem' := ⟨continuous_zero, fun _ ↦ ⟨0, by simp⟩⟩
  add_mem' := by
    rintro δ ε ⟨hδ, hδp⟩ ⟨hε, hεp⟩
    refine ⟨hδ.add hε, fun f ↦ ?_⟩
    obtain ⟨g, hg⟩ := hδp f
    obtain ⟨h, hh⟩ := hεp f
    exact ⟨g + h, by simp [hg, hh]⟩
  smul_mem' := by
    rintro c δ ⟨hδ, hδp⟩
    refine ⟨?_, fun f ↦ ?_⟩
    · exact (continuousDerivationsLieSubalgebra K).smul_mem c hδ
    · obtain ⟨g, hg⟩ := hδp f
      exact ⟨c • g, by simp only [Derivation.smul_apply, hg, PowerSeries.coe_smul]⟩
  lie_mem' := by
    rintro δ ε ⟨hδ, hδp⟩ ⟨hε, hεp⟩
    refine ⟨?_, fun f ↦ ?_⟩
    · exact (continuousDerivationsLieSubalgebra K).lie_mem hδ hε
    · obtain ⟨g, hg⟩ := hδp f
      obtain ⟨h, hh⟩ := hεp f
      obtain ⟨i, hi⟩ := hδp h
      obtain ⟨j, hj⟩ := hεp g
      exact ⟨i - j, by simp [Derivation.laurentSeries_commutator_apply, hg, hh, hi, hj]⟩

/-- Membership in the power-series-preserving Lie subalgebra means continuity and preservation
of the embedded power-series ring. -/
@[simp]
theorem mem_powerSeriesPreservingDerivations {δ : Derivation K K⸨X⸩ K⸨X⸩} :
    δ ∈ powerSeriesPreservingDerivations K ↔
      Continuous δ ∧ ∀ f : K⟦X⟧, ∃ g : K⟦X⟧, δ (f : K⸨X⸩) = g :=
  Iff.rfl

/-- A continuous Laurent vector field preserves power series exactly when its coefficient
is a power series: the subalgebra is `K⟦X⟧ D`. -/
theorem mem_powerSeriesPreservingDerivations_iff {δ : Derivation K K⸨X⸩ K⸨X⸩} :
    δ ∈ powerSeriesPreservingDerivations K ↔
      ∃ a : K⟦X⟧, δ = (a : K⸨X⸩) • laurentSeriesDerivation K := by
  rw [mem_powerSeriesPreservingDerivations]
  constructor
  · rintro ⟨hδ, hp⟩
    obtain ⟨a, ha⟩ := hp PowerSeries.X
    refine ⟨a, ?_⟩
    rw [δ.eq_smul_laurentSeriesDerivation hδ, ← ha, PowerSeries.coe_X]
  · rintro ⟨a, rfl⟩
    refine ⟨continuous_smul_laurentSeriesDerivation _, fun f ↦ ?_⟩
    exact ⟨a * PowerSeries.derivative f, by
      simp only [Derivation.smul_apply, smul_eq_mul, laurentSeriesDerivation_apply,
        PowerSeries.coe_mul, PowerSeries.coe_derivative]⟩

variable (K) in
/-- Continuous Laurent vector fields preserving the maximal ideal `X K⟦X⟧` of `K⟦X⟧`.
The ideal is presented by its multiples of `X`, avoiding a new carrier for the embedded ideal. -/
noncomputable def maximalIdealPreservingDerivations :
    LieSubalgebra K (Derivation K K⸨X⸩ K⸨X⸩) where
  carrier := {δ | Continuous δ ∧ ∀ f : K⟦X⟧, ∃ g : K⟦X⟧,
    δ ((PowerSeries.X * f : K⟦X⟧) : K⸨X⸩) = ((PowerSeries.X * g : K⟦X⟧) : K⸨X⸩)}
  zero_mem' := ⟨continuous_zero, fun _ ↦ ⟨0, by simp⟩⟩
  add_mem' := by
    rintro δ ε ⟨hδ, hδp⟩ ⟨hε, hεp⟩
    refine ⟨hδ.add hε, fun f ↦ ?_⟩
    obtain ⟨g, hg⟩ := hδp f
    obtain ⟨h, hh⟩ := hεp f
    exact ⟨g + h, by simp only [Derivation.add_apply, hg, hh, mul_add, PowerSeries.coe_add]⟩
  smul_mem' := by
    rintro c δ ⟨hδ, hδp⟩
    refine ⟨?_, fun f ↦ ?_⟩
    · exact (continuousDerivationsLieSubalgebra K).smul_mem c hδ
    · obtain ⟨g, hg⟩ := hδp f
      exact ⟨c • g, by
        simp only [Derivation.smul_apply, hg, mul_smul_comm, PowerSeries.coe_smul]⟩
  lie_mem' := by
    rintro δ ε ⟨hδ, hδp⟩ ⟨hε, hεp⟩
    refine ⟨?_, fun f ↦ ?_⟩
    · exact (continuousDerivationsLieSubalgebra K).lie_mem hδ hε
    · obtain ⟨g, hg⟩ := hδp f
      obtain ⟨h, hh⟩ := hεp f
      obtain ⟨i, hi⟩ := hδp h
      obtain ⟨j, hj⟩ := hεp g
      exact ⟨i - j, by
        simp only [Derivation.laurentSeries_commutator_apply, hg, hh, hi, hj, mul_sub,
          PowerSeries.coe_sub]⟩

/-- Membership in the maximal-ideal-preserving Lie subalgebra means continuity and
preservation of all power-series multiples of `X`. -/
@[simp]
theorem mem_maximalIdealPreservingDerivations {δ : Derivation K K⸨X⸩ K⸨X⸩} :
    δ ∈ maximalIdealPreservingDerivations K ↔
      Continuous δ ∧ ∀ f : K⟦X⟧, ∃ g : K⟦X⟧,
        δ ((PowerSeries.X * f : K⟦X⟧) : K⸨X⸩) =
          ((PowerSeries.X * g : K⟦X⟧) : K⸨X⸩) :=
  Iff.rfl

/-- A continuous Laurent vector field preserves the maximal ideal exactly when its coefficient
is a multiple of `X` in the power-series ring: the subalgebra is `X K⟦X⟧ D`. -/
theorem mem_maximalIdealPreservingDerivations_iff {δ : Derivation K K⸨X⸩ K⸨X⸩} :
    δ ∈ maximalIdealPreservingDerivations K ↔
      ∃ a : K⟦X⟧, δ =
        ((PowerSeries.X * a : K⟦X⟧) : K⸨X⸩) • laurentSeriesDerivation K := by
  rw [mem_maximalIdealPreservingDerivations]
  constructor
  · rintro ⟨hδ, hp⟩
    obtain ⟨a, ha⟩ := hp 1
    refine ⟨a, ?_⟩
    rw [δ.eq_smul_laurentSeriesDerivation hδ]
    simpa using congrArg (· • laurentSeriesDerivation K) ha
  · rintro ⟨a, rfl⟩
    refine ⟨continuous_smul_laurentSeriesDerivation _, fun f ↦ ?_⟩
    refine ⟨a * PowerSeries.derivative (PowerSeries.X * f), ?_⟩
    simp only [Derivation.smul_apply, smul_eq_mul, laurentSeriesDerivation_apply,
      PowerSeries.coe_mul, PowerSeries.coe_derivative, mul_assoc]

/-- Maximal-ideal-preserving continuous Laurent vector fields preserve power series. -/
theorem maximalIdealPreservingDerivations_le_powerSeriesPreservingDerivations :
    maximalIdealPreservingDerivations K ≤ powerSeriesPreservingDerivations K := by
  intro δ hδ
  obtain ⟨a, rfl⟩ := mem_maximalIdealPreservingDerivations_iff.mp hδ
  exact mem_powerSeriesPreservingDerivations_iff.mpr ⟨PowerSeries.X * a, rfl⟩

end TauCeti
