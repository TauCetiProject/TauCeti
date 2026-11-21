/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.VonNeumannAlgebra.Basic
public import TauCeti.Analysis.VonNeumannAlgebra.NormalFunctional
public import Mathlib.Algebra.Order.Nonneg.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Normal traces on the positive cone

A normal trace takes values in `ℝ≥0∞` on the positive elements of a concrete von Neumann
algebra. It is additive, positively homogeneous and tracial, and preserves increasing strong
operator limits. Values may be infinite, including at the identity. Faithfulness and
semifiniteness are separate properties, so in particular the zero trace is semifinite.

`NormalTrace.ofLinearMap` connects normal positive tracial complex linear functionals to this
positive-cone formulation. Finite trace at the identity implies finiteness everywhere and
semifiniteness. This formulation allows spectral projections to be measured by an unbounded
trace when defining noncommutative distribution functions.

## References

* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, Definition 8.3.1.
-/

public section

open Filter Topology
open scoped ENNReal NNReal ComplexOrder
open ContinuousLinearMap (toPointwiseConvergenceCLM)

universe u

namespace VonNeumannAlgebra

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An extended nonnegative trace on the positive cone, normal for increasing strong operator
limits. Index types use the universe of `H`, as in `IsNormalFunctional`. -/
structure NormalTrace (M : VonNeumannAlgebra H) extends (Nonneg M.toStarSubalgebra →+ ℝ≥0∞) where
  map_nnreal_smul' (c : ℝ≥0) (x : Nonneg M.toStarSubalgebra) :
    toAddMonoidHom ⟨(c : ℝ) • (x : M.toStarSubalgebra), smul_nonneg c.property x.property⟩ =
      (c : ℝ≥0∞) * toAddMonoidHom x
  map_star_mul_self' (x : M.toStarSubalgebra) :
    toAddMonoidHom ⟨star x * x, star_mul_self_nonneg x⟩ =
      toAddMonoidHom ⟨x * star x, mul_star_self_nonneg x⟩
  normal' : ∀ (ι : Type u) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (x : ι → Nonneg M.toStarSubalgebra) (y : Nonneg M.toStarSubalgebra),
    Monotone x →
    Tendsto (fun i => toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
      ((x i : M.toStarSubalgebra) : H →L[ℂ] H)) atTop
      (𝓝 (toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
        ((y : M.toStarSubalgebra) : H →L[ℂ] H))) →
    Tendsto (fun i => toAddMonoidHom (x i)) atTop (𝓝 (toAddMonoidHom y))

namespace NormalTrace

variable {M : VonNeumannAlgebra H}

instance : FunLike (NormalTrace M) (Nonneg M.toStarSubalgebra) ℝ≥0∞ where
  coe τ := τ.toAddMonoidHom
  coe_injective τ σ h := by
    cases τ
    cases σ
    congr 1
    exact DFunLike.coe_injective h

instance : AddMonoidHomClass (NormalTrace M) (Nonneg M.toStarSubalgebra) ℝ≥0∞ where
  map_zero τ := τ.toAddMonoidHom.map_zero
  map_add τ := τ.toAddMonoidHom.map_add

@[simp]
theorem toAddMonoidHom_apply (τ : NormalTrace M) (x : Nonneg M.toStarSubalgebra) :
    τ.toAddMonoidHom x = τ x :=
  (rfl)

/-- Positive homogeneity, including the extended-real convention `0 * ∞ = 0`. -/
theorem map_nnreal_smul (τ : NormalTrace M) (c : ℝ≥0) (x : Nonneg M.toStarSubalgebra) :
    τ ⟨(c : ℝ) • (x : M.toStarSubalgebra), smul_nonneg c.property x.property⟩ = (c : ℝ≥0∞) * τ x :=
  τ.map_nnreal_smul' c x

/-- The trace takes equal values on `x⋆x` and `xx⋆`. -/
theorem map_star_mul_self (τ : NormalTrace M) (x : M.toStarSubalgebra) :
    τ ⟨star x * x, star_mul_self_nonneg x⟩ = τ ⟨x * star x, mul_star_self_nonneg x⟩ :=
  τ.map_star_mul_self' x

@[ext] theorem ext {τ σ : NormalTrace M} (h : ∀ x, τ x = σ x) : τ = σ :=
  DFunLike.ext τ σ h

/-- Additivity implies monotonicity on the positive cone. -/
theorem monotone (τ : NormalTrace M) : Monotone τ := by
  intro x y hxy
  let z : Nonneg M.toStarSubalgebra := ⟨(y : M.toStarSubalgebra) - x, sub_nonneg.mpr hxy⟩
  have hy : y = x + z := Subtype.ext (by simp [z])
  rw [hy, map_add]
  exact le_add_of_nonneg_right bot_le

/-- Normality evaluated on an increasing net with a strong operator limit. -/
theorem tendsto (τ : NormalTrace M) {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]
    [Nonempty ι] {x : ι → Nonneg M.toStarSubalgebra} {y : Nonneg M.toStarSubalgebra}
    (hmono : Monotone x)
    (hlim : Tendsto (fun i => toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
      ((x i : M.toStarSubalgebra) : H →L[ℂ] H)) atTop
      (𝓝 (toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
        ((y : M.toStarSubalgebra) : H →L[ℂ] H)))) :
    Tendsto (fun i => τ (x i)) atTop (𝓝 (τ y)) := τ.normal' ι x y hmono hlim

/-- Normality as preservation of the supremum of trace values along an increasing strongly
convergent net. -/
theorem iSup_eq (τ : NormalTrace M) {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]
    [Nonempty ι] {x : ι → Nonneg M.toStarSubalgebra} {y : Nonneg M.toStarSubalgebra}
    (hmono : Monotone x)
    (hlim : Tendsto (fun i => toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
      ((x i : M.toStarSubalgebra) : H →L[ℂ] H)) atTop
      (𝓝 (toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
        ((y : M.toStarSubalgebra) : H →L[ℂ] H)))) :
    (⨆ i, τ (x i)) = τ y :=
  (isLUB_of_tendsto_atTop (τ.monotone.comp hmono) (τ.tendsto hmono hlim)).iSup_eq

/-- A trace is faithful if a positive element of trace zero is zero. -/
def Faithful (τ : NormalTrace M) : Prop := ∀ x, τ x = 0 → x = 0

/-- Semifiniteness means that every nonzero positive element dominates a nonzero positive
finite-trace element. -/
def Semifinite (τ : NormalTrace M) : Prop :=
  ∀ x : Nonneg M.toStarSubalgebra, x ≠ 0 → ∃ y, y ≤ x ∧ y ≠ 0 ∧ τ y ≠ ⊤

theorem faithful_iff (τ : NormalTrace M) : τ.Faithful ↔ ∀ x, τ x = 0 → x = 0 := Iff.rfl

theorem semifinite_iff (τ : NormalTrace M) :
    τ.Semifinite ↔ ∀ x : Nonneg M.toStarSubalgebra,
      x ≠ 0 → ∃ y, y ≤ x ∧ y ≠ 0 ∧ τ y ≠ ⊤ := Iff.rfl

@[simp] theorem Faithful.map_eq_zero_iff {τ : NormalTrace M} (hτ : τ.Faithful)
    (x : Nonneg M.toStarSubalgebra) : τ x = 0 ↔ x = 0 :=
  ⟨hτ x, fun h => h ▸ map_zero τ⟩

/-- Consume semifiniteness at a nonzero positive element. -/
theorem Semifinite.exists_le {τ : NormalTrace M} (hτ : τ.Semifinite)
    {x : Nonneg M.toStarSubalgebra} (hx : x ≠ 0) :
    ∃ y, y ≤ x ∧ y ≠ 0 ∧ τ y ≠ ⊤ := hτ x hx

/-- A trace that is finite on every positive element is semifinite. -/
theorem semifinite_of_forall_ne_top (τ : NormalTrace M) (h : ∀ x, τ x ≠ ⊤) :
    τ.Semifinite := fun x hx => ⟨x, le_rfl, hx, h x⟩

/-- A positive value is bounded by the operator norm times the trace of the identity. -/
theorem le_nnnorm_mul_apply_one (τ : NormalTrace M) (x : Nonneg M.toStarSubalgebra) :
    τ x ≤ (‖(x : M.toStarSubalgebra)‖₊ : ℝ≥0∞) * τ 1 := by
  have hx : x ≤ (⟨‖(x : M.toStarSubalgebra)‖ • (1 : M.toStarSubalgebra),
      smul_nonneg (norm_nonneg _) zero_le_one⟩ : Nonneg M.toStarSubalgebra) := by
    exact (x.property.isSelfAdjoint.le_algebraMap_norm_self).trans_eq
      (Algebra.algebraMap_eq_smul_one _)
  exact (τ.monotone hx).trans_eq (τ.map_nnreal_smul ‖(x : M.toStarSubalgebra)‖₊ 1)

/-- Finite trace at the identity implies finite trace on every positive element. -/
theorem map_ne_top_of_one (τ : NormalTrace M) (hτ : τ 1 ≠ ⊤)
    (x : Nonneg M.toStarSubalgebra) : τ x ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hτ)
    (τ.le_nnnorm_mul_apply_one x)

/-- In particular every normal trace finite at the identity is semifinite. -/
theorem semifinite_of_one_ne_top (τ : NormalTrace M) (hτ : τ 1 ≠ ⊤) : τ.Semifinite :=
  τ.semifinite_of_forall_ne_top (τ.map_ne_top_of_one hτ)

/-- A normal positive tracial complex linear functional defines an extended nonnegative trace.
Positivity is only required on star squares; continuous functional calculus supplies all other
positive elements. The resulting trace is finite everywhere. -/
noncomputable def ofLinearMap (τ : M.toStarSubalgebra →ₗ[ℂ] ℂ)
    (hpos : ∀ x, 0 ≤ τ (star x * x))
    (htr : ∀ x, τ (star x * x) = τ (x * star x))
    (hnormal : M.IsNormalFunctional τ) : NormalTrace M := by
  have hpos' (x : M.toStarSubalgebra) (hx : 0 ≤ x) : 0 ≤ τ x := by
    obtain ⟨y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx
    exact hpos y
  exact
    { toAddMonoidHom :=
        { toFun := fun x => ENNReal.ofReal (τ x).re
          map_zero' := by simp
          map_add' := fun x y => by
            simp only [Nonneg.coe_add, map_add, Complex.add_re]
            exact ENNReal.ofReal_add (Complex.nonneg_iff.mp (hpos' x x.property)).1
              (Complex.nonneg_iff.mp (hpos' y y.property)).1 }
      map_nnreal_smul' := fun c x => by
        simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
        simp [← Complex.coe_smul, map_smul, Complex.mul_re]
      map_star_mul_self' := fun x => by
        simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
        rw [htr]
      normal' := fun ι _ _ _ x y hmono hlim =>
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp
          (Complex.continuous_re.continuousAt.tendsto.comp
            (hnormal.tendsto (fun i j hij => hmono hij) hlim)) }

@[simp]
theorem ofLinearMap_apply (τ : M.toStarSubalgebra →ₗ[ℂ] ℂ)
    (hpos : ∀ x, 0 ≤ τ (star x * x))
    (htr : ∀ x, τ (star x * x) = τ (x * star x))
    (hnormal : M.IsNormalFunctional τ) (x : Nonneg M.toStarSubalgebra) :
    ofLinearMap τ hpos htr hnormal x = ENNReal.ofReal (τ x).re := (rfl)

/-- A normal positive linear functional with trivial star-square kernel induces a faithful trace.
This kernel condition is available, for example, for the canonical trace of a group algebra. -/
theorem faithful_ofLinearMap (τ : M.toStarSubalgebra →ₗ[ℂ] ℂ)
    (hpos : ∀ x, 0 ≤ τ (star x * x))
    (htr : ∀ x, τ (star x * x) = τ (x * star x))
    (hnormal : M.IsNormalFunctional τ)
    (hfaithful : ∀ x, τ (star x * x) = 0 → x = 0) :
    (ofLinearMap τ hpos htr hnormal).Faithful := by
  intro x hx
  obtain ⟨y, hy⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp x.property
  rw [ofLinearMap_apply, hy] at hx
  have hre : (τ (star y * y)).re = 0 :=
    le_antisymm (ENNReal.ofReal_eq_zero.mp hx) (Complex.nonneg_iff.mp (hpos y)).1
  have hzero : τ (star y * y) = 0 := by
    rw [Complex.eq_re_of_ofReal_le (hpos y), hre]
    rfl
  apply Subtype.ext
  simpa [hfaithful y hzero] using hy

/-- The zero trace is normal and semifinite. -/
noncomputable instance : Zero (NormalTrace M) :=
  ⟨ofLinearMap 0 (by simp) (by simp) (by
    rw [isNormalFunctional_def]
    intro ι _ _ _ x y _ _
    exact tendsto_const_nhds)⟩

@[simp] theorem zero_apply (x : Nonneg M.toStarSubalgebra) : (0 : NormalTrace M) x = 0 := by
  exact ENNReal.ofReal_zero

/-- The zero trace is semifinite: the original positive element itself has finite trace. -/
theorem semifinite_zero : (0 : NormalTrace M).Semifinite :=
  semifinite_of_forall_ne_top 0 (by simp)

end NormalTrace
end VonNeumannAlgebra
