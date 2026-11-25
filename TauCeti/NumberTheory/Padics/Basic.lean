/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Basic instances for the `p`-adic numbers

This file provides a direct instance for the nontriviality of `ℚ_[p]`, already implied by
its field structure, and an instance expressing that `2` is invertible. These instances support
finite-dimensional constructions and algebraic trace and norm calculations over the `p`-adic field.

It also records that the scalar action of `ℤ_[p]` on `ℚ_[p]` multiplies norms,
`‖a • x‖ = ‖a‖ * ‖x‖`. In particular the action is contractive, so `ℚ_[p]` itself is a
coefficient ring for Mathlib's Mahler isometry `PadicInt.mahlerEquiv` and for the Amice transform
of measures on `ℤ_p`.

Finally, it records that the inclusion `PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]` is the structure
map of the `ℤ_[p]`-algebra `ℚ_[p]`, and that it is a topological embedding of norm at most `1` whose
range is the closed unit ball (`TauCeti.range_padicInt_coe_ringHom`). These are the hypotheses
under which `ℚ_[p]`-valued measures of norm at most `1` come from `ℤ_[p]`-valued measures. It also
maps exactly the maximal ideal of `ℤ_[p]` into the open unit ball
(`PadicInt.norm_coe_ringHom_lt_one_iff`); together with the norm bound, this is the hypothesis under
which formal and normed Weierstrass degrees over `ℤ_[p]` are compared. A `ℚ_[p]`-linear form bounded
by `r` on a set is bounded by `r` on its `ℤ_[p]`-span
(`PadicInt.norm_apply_le_of_mem_span_subring`).

For a `ℚ_[p]`-algebra `K`, the composite structure map
`TauCeti.padicIntAlgebraMap p K : ℤ_[p] →+* K` is injective when `K` is nontrivial, and continuous
when the structure map `ℚ_[p] → K` is. For a seminormed `ℚ_[p]`-algebra `K` with `‖1‖ ≤ 1`
(including the zero seminorm) it maps `ℤ_[p]` into the closed unit ball of `K`; when `‖1‖ = 1` it
is an isometry (`TauCeti.isometry_padicIntAlgebraMap`), the norm of a natural number in `K` is its
`p`-adic norm (`TauCeti.norm_natCast_eq_norm_padic`), so `p` itself has norm `p⁻¹`
(`TauCeti.norm_natCast_p`), and a nonzero integer `n` has norm at least
`1 / |n|` in `K` (`TauCeti.inv_abs_le_norm_intCast`).

Two continuous ring homomorphisms from `ℚ_[p]` to a Hausdorff semiring are equal
(`RingHom.ext_padic_of_continuous`), since they agree on the dense subfield `ℚ`; for instance a
continuous Frobenius lift on a `p`-adic field fixes `ℚ_[p]`.
-/

public section

noncomputable section

namespace TauCeti

/-- A direct instance of the existing fact that the `p`-adic field has distinct zero and one. -/
-- Avoid backtracking through Henselian-ring instances during rank and freeness synthesis.
instance (p : ℕ) [Fact (Nat.Prime p)] : Nontrivial ℚ_[p] :=
  @DivisionRing.toNontrivial _ (instFieldPadic p).toDivisionRing

/-- Two is invertible in the `p`-adic field, including when `p = 2`. -/
instance instInvertibleTwoPadic (p : ℕ) [Fact (Nat.Prime p)] : Invertible (2 : ℚ_[p]) :=
  invertibleOfNonzero two_ne_zero

/-- The scalar action of `ℤ_[p]` on `ℚ_[p]` is multiplication by the inclusion, so it multiplies
norms. This also provides the contractive action `IsBoundedSMul ℤ_[p] ℚ_[p]`. -/
instance normSMulClass_padicInt_padic (p : ℕ) [Fact (Nat.Prime p)] :
    NormSMulClass ℤ_[p] ℚ_[p] :=
  ⟨fun a x ↦ by rw [Algebra.smul_def, norm_mul, PadicInt.algebraMap_apply, PadicInt.norm_coe]⟩

end TauCeti

namespace PadicInt

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The structure map of the `ℤ_[p]`-algebra `ℚ_[p]` is the inclusion `PadicInt.Coe.ringHom`. -/
theorem algebraMap_eq_coe_ringHom : algebraMap ℤ_[p] ℚ_[p] = Coe.ringHom :=
  RingHom.ext algebraMap_apply

/-- The inclusion `ℤ_[p] → ℚ_[p]` takes values in the closed unit ball. -/
theorem norm_coe_ringHom_le_one (a : ℤ_[p]) : ‖Coe.ringHom a‖ ≤ 1 := by
  simpa using a.norm_le_one

/-- The inclusion `ℤ_[p] → ℚ_[p]` maps exactly the maximal ideal of `ℤ_[p]` into the open unit
ball. -/
theorem norm_coe_ringHom_lt_one_iff {a : ℤ_[p]} :
    ‖Coe.ringHom a‖ < 1 ↔ a ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits]
  simp

/-- The inclusion `ℤ_[p] → ℚ_[p]` is a topological embedding. -/
theorem isEmbedding_coe_ringHom : Topology.IsEmbedding (Coe.ringHom (p := p)) :=
  isometry_subtypeVal.isEmbedding

/-- A `ℚ_[p]`-linear form whose values on a set `s` have absolute value at most `r` has values of
absolute value at most `r` on the whole `ℤ_[p]`-span of `s`, by the ultrametric inequality. -/
theorem norm_apply_le_of_mem_span_subring {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
    {f : V →ₗ[ℚ_[p]] ℚ_[p]} {s : Set V} {r : ℝ} (hr : 0 ≤ r) (hf : ∀ y ∈ s, ‖f y‖ ≤ r) {x : V}
    (hx : x ∈ Submodule.span (subring p) s) : ‖f x‖ ≤ r := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hf x hx
  | zero => simpa using hr
  | add x y _ _ hx hy =>
    rw [map_add]
    exact (Padic.nonarchimedean _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    rw [Subring.smul_def, map_smul, smul_eq_mul, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) ((mem_subring_iff p).mp c.property)).trans hx

end PadicInt

namespace TauCeti

/-- The image of the inclusion `ℤ_[p] → ℚ_[p]` is the closed unit ball. -/
@[simp]
theorem range_padicInt_coe_ringHom {p : ℕ} [Fact (Nat.Prime p)] :
    Set.range (PadicInt.Coe.ringHom (p := p)) = Metric.closedBall 0 1 := by
  rw [funext PadicInt.Coe.ringHom_apply]
  exact Subtype.range_coe_subtype.trans (Set.ext fun _ ↦ mem_closedBall_zero_iff.symm)

section Algebra

variable (p : ℕ) [Fact (Nat.Prime p)] (K : Type*) [Semiring K] [Algebra ℚ_[p] K]

/-- The structure map `ℤ_p → K` of a `ℚ_p`-algebra `K`, through `ℚ_p`. For a seminormed
`ℚ_p`-algebra with `‖1‖ = 1` it is an isometry (`TauCeti.isometry_padicIntAlgebraMap`). -/
def padicIntAlgebraMap : ℤ_[p] →+* K :=
  (algebraMap ℚ_[p] K).comp PadicInt.Coe.ringHom

variable {p K}

/-- The structure map `ℤ_p → K` is the composite of the inclusion `ℤ_p → ℚ_p` with the structure
map `ℚ_p → K`. -/
theorem padicIntAlgebraMap_def :
    padicIntAlgebraMap p K = (algebraMap ℚ_[p] K).comp PadicInt.Coe.ringHom :=
  (rfl)

@[simp]
theorem padicIntAlgebraMap_apply (a : ℤ_[p]) :
    padicIntAlgebraMap p K a = algebraMap ℚ_[p] K a := by
  rw [padicIntAlgebraMap_def, RingHom.comp_apply, PadicInt.Coe.ringHom_apply]

/-- The structure map `ℤ_p → K` is injective when `K` is nontrivial. -/
theorem padicIntAlgebraMap_injective [Nontrivial K] :
    Function.Injective (padicIntAlgebraMap p K) := by
  rw [padicIntAlgebraMap_def, RingHom.coe_comp]
  exact (algebraMap ℚ_[p] K).injective.comp PadicInt.isEmbedding_coe_ringHom.injective

/-- The structure map `ℤ_p → K` is continuous when the structure map `ℚ_p → K` is. -/
theorem continuous_padicIntAlgebraMap [TopologicalSpace K] (h : Continuous (algebraMap ℚ_[p] K)) :
    Continuous (padicIntAlgebraMap p K) := by
  rw [padicIntAlgebraMap_def, RingHom.coe_comp]
  exact h.comp PadicInt.isEmbedding_coe_ringHom.continuous

end Algebra

section NormedAlgebra

variable {p : ℕ} [Fact (Nat.Prime p)] {K : Type*} [SeminormedRing K] [NormedAlgebra ℚ_[p] K]

/-- In a seminormed `ℚ_p`-algebra with `‖1‖ = 1`, the structure map `ℤ_p → K` preserves norms. -/
theorem norm_padicIntAlgebraMap [NormOneClass K] (a : ℤ_[p]) :
    ‖padicIntAlgebraMap p K a‖ = ‖a‖ := by
  simp [norm_algebraMap']

/-- In a seminormed `ℚ_p`-algebra with `‖1‖ = 1`, the structure map `ℤ_p → K` is an isometry. -/
theorem isometry_padicIntAlgebraMap [NormOneClass K] : Isometry (padicIntAlgebraMap p K) :=
  AddMonoidHomClass.isometry_of_norm _ norm_padicIntAlgebraMap

/-- In a seminormed `ℚ_p`-algebra with `‖1‖ ≤ 1`, the structure map `ℤ_p → K` takes values in the
closed unit ball. This includes the zero seminorm, where `‖1‖ = 0`. -/
theorem norm_padicIntAlgebraMap_le_one (h : ‖(1 : K)‖ ≤ 1) (a : ℤ_[p]) :
    ‖padicIntAlgebraMap p K a‖ ≤ 1 := by
  rw [padicIntAlgebraMap_apply, norm_algebraMap, PadicInt.norm_coe]
  exact (mul_le_of_le_one_left (norm_nonneg _) a.norm_le_one).trans h

/-- The norm of a natural number in a seminormed `ℚ_p`-algebra with `‖1‖ = 1` is its `p`-adic
norm. -/
theorem norm_natCast_eq_norm_padic [NormOneClass K] (m : ℕ) : ‖(m : K)‖ = ‖(m : ℚ_[p])‖ := by
  rw [← map_natCast (algebraMap ℚ_[p] K), norm_algebraMap']

/-- In a seminormed `ℚ_p`-algebra with `‖1‖ = 1`, the prime `p` has norm `p⁻¹`. -/
theorem norm_natCast_p [NormOneClass K] : ‖(p : K)‖ = (p : ℝ)⁻¹ := by
  rw [norm_natCast_eq_norm_padic (p := p), Padic.norm_p]

/-- In a seminormed `ℚ_p`-algebra with `‖1‖ = 1`, an integer `n` has norm at least `1 / |n|`,
because the `p`-part of `n` divides `n`. For `n = 0` both sides are `0` by the convention
`0⁻¹ = 0`. -/
theorem inv_abs_le_norm_intCast (p : ℕ) [Fact (Nat.Prime p)] {K : Type*} [SeminormedRing K]
    [NormedAlgebra ℚ_[p] K] [NormOneClass K] (n : ℤ) : (|n| : ℝ)⁻¹ ≤ ‖(n : K)‖ := by
  rw [← norm_natAbs n, norm_natCast_eq_norm_padic (p := p), ← Int.cast_abs, ← Nat.cast_natAbs]
  exact Padic.inv_natCast_le_norm_natCast n.natAbs

end NormedAlgebra

end TauCeti

namespace RingHom

variable {p : ℕ} [Fact (Nat.Prime p)] {F L : Type*} [Semiring L] [TopologicalSpace L] [T2Space L]
  [FunLike F ℚ_[p] L] [RingHomClass F ℚ_[p] L]

/-- Two continuous ring homomorphisms from `ℚ_[p]` to a Hausdorff semiring are equal: they agree
on the dense subfield `ℚ`. -/
theorem ext_padic_of_continuous (f g : F) (hf : Continuous f) (hg : Continuous g) : f = g := by
  have hℚ : ∀ r : ℚ, f r = g r := fun r ↦ by
    simpa using DFunLike.congr_fun (RingHom.ext_rat
      ((f : ℚ_[p] →+* L).comp (Rat.castHom ℚ_[p])) ((g : ℚ_[p] →+* L).comp (Rat.castHom ℚ_[p]))) r
  exact DFunLike.coe_injective ((Padic.denseRange_ratCast p).equalizer hf hg (funext hℚ))

end RingHom
