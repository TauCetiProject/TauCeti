/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import TauCeti.Analysis.CStarAlgebra.GNS.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The GNS commutant Radon–Nikodym theorem

Let `f` and `g` be positive linear functionals on a possibly nonunital C⋆-algebra `A` such that
`g` is dominated by a scalar multiple of `f`: `g a ≤ C * f a` for all `0 ≤ a`. Then the map
`[a]_f ↦ [a]_g` between GNS classes is bounded by `√C` and extends uniquely to a bounded
intertwiner `V : f.GNS →L[ℂ] g.GNS`. The positive operator `T = V† ∘L V` on `f.GNS`, defined here
as `PositiveLinearMap.gnsRadonNikodym f g`, lies in the commutant of the GNS representation of `f`,
satisfies `0 ≤ T ≤ C • 1` and `‖T‖ ≤ C`, and represents `g` by
`⟪[a]_f, T [b]_f⟫ = g (a⋆ b)`. It is uniquely determined by this inner-product identity.

For a unital C⋆-algebra `B`, every operator `T` on `f.GNS` defines a continuous linear functional
`PositiveLinearMap.gnsVectorFunctional f T`, sending `a` to `⟪Ω_f, T (π_f(a) Ω_f)⟫`. When `T` lies
in the commutant of `π_f(B)` and is positive, this functional is positive and dominated by
`‖T‖ * f`, and the two constructions are inverse to each other. This establishes the order
bijection between dominated positive functionals and positive operators in the GNS commutant.

## Main definitions

* `PositiveLinearMap.gnsRadonNikodym`: the Radon–Nikodym operator `T : f.GNS →L[ℂ] f.GNS` of a
  positive functional `g` relative to `f`.
* `PositiveLinearMap.gnsVectorFunctional`: the continuous linear functional
  `a ↦ ⟪Ω_f, T (π_f(a) Ω_f)⟫` associated to an operator `T` on `f.GNS`.

## Main statements

* `PositiveLinearMap.inner_gnsRadonNikodym_toGNS`: `⟪[a]_f, T [b]_f⟫ = g (a⋆ b)`.
* `PositiveLinearMap.gnsRadonNikodym_mem_centralizer`: `T` lies in the commutant of the GNS
  representation of `f`.
* `PositiveLinearMap.existsUnique_gnsRadonNikodym`: existence and uniqueness of the positive
  commutant operator representing a dominated positive functional.
* `PositiveLinearMap.gnsVectorFunctional_nonneg`: positive commutant operators induce positive
  functionals.
* `PositiveLinearMap.gnsVectorFunctional_gnsRadonNikodym` and
  `PositiveLinearMap.gnsRadonNikodym_gnsVectorFunctional`: inverse laws for unital algebras.

## References

* O. Bratteli and D. W. Robinson, *Operator Algebras and Quantum Statistical Mechanics 1*,
  second edition, Theorem 2.3.19.
-/

public section

noncomputable section

open ContinuousLinearMap UniformSpace
open scoped ComplexOrder InnerProductSpace

namespace PositiveLinearMap

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The bounded intertwiner `f.GNS →L[ℂ] g.GNS` extending `[a]_f ↦ [a]_g` whenever `g` is
dominated by a scalar multiple of `f`. -/
private def gnsDominationMap (f g : A →ₚ[ℂ] ℂ) : f.GNS →L[ℂ] g.GNS :=
  g.toGNS.toLinearMap.extendOfNorm f.toGNS.toLinearMap

/-- Domination `g ≤ C • f` yields the GNS class-norm bound `‖[a]_g‖ ≤ √(max C 0) * ‖[a]_f‖`. -/
private theorem norm_toGNS_le_of_dominated {f g : A →ₚ[ℂ] ℂ} {C : ℝ}
    (hfg : ∀ a, 0 ≤ a → g a ≤ (C : ℂ) * f a) (a : A) :
    ‖g.toGNS a‖ ≤ Real.sqrt (max C 0) * ‖f.toGNS a‖ := by
  have hf_re : 0 ≤ (f (star a * a)).re :=
    (Complex.le_def.mp (f.map_nonneg (star_mul_self_nonneg a))).1
  have h1 := (Complex.le_def.mp (hfg (star a * a) (star_mul_self_nonneg a))).1
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h1
  calc ‖g.toGNS a‖ = Real.sqrt (g (star a * a)).re := by simp [toGNS_apply, preGNS_norm_def]
    _ ≤ Real.sqrt (max C 0 * (f (star a * a)).re) :=
        Real.sqrt_le_sqrt (h1.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) hf_re))
    _ = Real.sqrt (max C 0) * ‖f.toGNS a‖ := by
        rw [Real.sqrt_mul (le_max_right C 0)]; simp [toGNS_apply, preGNS_norm_def]

private theorem gnsDominationMap_apply_toGNS {f g : A →ₚ[ℂ] ℂ} {C : ℝ}
    (hfg : ∀ a, 0 ≤ a → g a ≤ (C : ℂ) * f a) (a : A) :
    f.gnsDominationMap g (f.toGNS a) = g.toGNS a :=
  LinearMap.extendOfNorm_eq f.denseRange_toGNS
    ⟨Real.sqrt (max C 0), norm_toGNS_le_of_dominated hfg⟩ a

private theorem opNorm_gnsDominationMap_le {f g : A →ₚ[ℂ] ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hfg : ∀ a, 0 ≤ a → g a ≤ (C : ℂ) * f a) :
    ‖f.gnsDominationMap g‖ ≤ Real.sqrt C :=
  LinearMap.opNorm_extendOfNorm_le f.denseRange_toGNS (Real.sqrt_nonneg C) fun a => by
    simpa [max_eq_left hC] using norm_toGNS_le_of_dominated hfg a

private theorem gnsDominationMap_intertwines {f g : A →ₚ[ℂ] ℂ} {C : ℝ}
    (hfg : ∀ a, 0 ≤ a → g a ≤ (C : ℂ) * f a) (a : A) :
    (f.gnsDominationMap g).comp (f.gnsNonUnitalStarAlgHom a) =
      (g.gnsNonUnitalStarAlgHom a).comp (f.gnsDominationMap g) := by
  ext v
  refine f.denseRange_toGNS.induction_on v (isClosed_eq (by fun_prop) (by fun_prop)) fun b => ?_
  have hL : f.gnsNonUnitalStarAlgHom a (f.toGNS b) = f.toGNS (a * b) := by
    simp [toGNS_apply, gnsNonUnitalStarAlgHom_apply_coe]
  have hR : g.gnsNonUnitalStarAlgHom a (g.toGNS b) = g.toGNS (a * b) := by
    simp [toGNS_apply, gnsNonUnitalStarAlgHom_apply_coe]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, hL,
    gnsDominationMap_apply_toGNS hfg, hR]

/-- The **GNS Radon–Nikodym operator** of a positive functional `g` relative to `f`: the positive
operator `V† ∘L V` on `f.GNS`, where `V : f.GNS →L[ℂ] g.GNS` extends `[a]_f ↦ [a]_g`. When `g` is
dominated by `C • f`, it is the unique operator in the commutant of `f.gnsNonUnitalStarAlgHom`
satisfying `⟪[a]_f, T [b]_f⟫ = g (a⋆ b)`. -/
def gnsRadonNikodym (f g : A →ₚ[ℂ] ℂ) : f.GNS →L[ℂ] f.GNS :=
  (f.gnsDominationMap g).adjoint.comp (f.gnsDominationMap g)

/-- The GNS Radon–Nikodym operator is positive. -/
theorem isPositive_gnsRadonNikodym (f g : A →ₚ[ℂ] ℂ) : (f.gnsRadonNikodym g).IsPositive :=
  ContinuousLinearMap.isPositive_adjoint_comp_self (f.gnsDominationMap g)

/-- The GNS Radon–Nikodym operator is self-adjoint. -/
theorem isSelfAdjoint_gnsRadonNikodym (f g : A →ₚ[ℂ] ℂ) : IsSelfAdjoint (f.gnsRadonNikodym g) :=
  (f.isPositive_gnsRadonNikodym g).isSelfAdjoint

/-- **Representing identity of the GNS Radon–Nikodym operator.** If `g` is dominated by a scalar
multiple of `f`, then `⟪[a]_f, T [b]_f⟫ = g (a⋆ b)` for all `a, b : A`. -/
theorem inner_gnsRadonNikodym_toGNS {f g : A →ₚ[ℂ] ℂ} {C : ℝ}
    (hfg : ∀ a, 0 ≤ a → g a ≤ (C : ℂ) * f a) (a b : A) :
    ⟪f.toGNS a, f.gnsRadonNikodym g (f.toGNS b)⟫_ℂ = g (star a * b) := by
  rw [gnsRadonNikodym, ContinuousLinearMap.coe_comp, Function.comp_apply, adjoint_inner_right,
    gnsDominationMap_apply_toGNS hfg, gnsDominationMap_apply_toGNS hfg]
  simp [toGNS_apply, Completion.inner_coe, preGNS_inner_def]

/-- If `g ≤ C • f` with `0 ≤ C`, then the GNS Radon–Nikodym operator has norm at most `C`. -/
theorem opNorm_gnsRadonNikodym_le {f g : A →ₚ[ℂ] ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hfg : ∀ a, 0 ≤ a → g a ≤ (C : ℂ) * f a) : ‖f.gnsRadonNikodym g‖ ≤ C := by
  rw [gnsRadonNikodym, norm_adjoint_comp_self]
  have h := opNorm_gnsDominationMap_le hC hfg
  exact (mul_le_mul h h (norm_nonneg (f.gnsDominationMap g))
    (Real.sqrt_nonneg C)).trans_eq (Real.mul_self_sqrt hC)

/-- If `g ≤ C • f` with `0 ≤ C`, then `C • 1 - T` is positive. -/
theorem isPositive_smul_one_sub_gnsRadonNikodym {f g : A →ₚ[ℂ] ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hfg : ∀ a, 0 ≤ a → g a ≤ (C : ℂ) * f a) :
    ((C : ℂ) • (1 : f.GNS →L[ℂ] f.GNS) - f.gnsRadonNikodym g).IsPositive := by
  rw [Complex.coe_smul, ← Algebra.algebraMap_eq_smul_one, ← ContinuousLinearMap.le_def]
  refine (IsSelfAdjoint.le_algebraMap_norm_self (f.gnsRadonNikodym g)
    (f.isSelfAdjoint_gnsRadonNikodym g)).trans ?_
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
  exact smul_le_smul_of_nonneg_right (opNorm_gnsRadonNikodym_le hC hfg)
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr ContinuousLinearMap.isPositive_one)

/-- **Commutant membership.** If `g` is dominated by a scalar multiple of `f`, then its GNS
Radon–Nikodym operator commutes with the GNS representation of `f`. -/
theorem gnsRadonNikodym_mem_centralizer {f g : A →ₚ[ℂ] ℂ} {C : ℝ}
    (hfg : ∀ a, 0 ≤ a → g a ≤ (C : ℂ) * f a) :
    f.gnsRadonNikodym g ∈ Set.centralizer (Set.range f.gnsNonUnitalStarAlgHom) := by
  rintro _ ⟨a, rfl⟩
  have h1 : f.gnsNonUnitalStarAlgHom a ∘L (f.gnsDominationMap g).adjoint =
      (f.gnsDominationMap g).adjoint ∘L g.gnsNonUnitalStarAlgHom a := by
    simpa only [adjoint_comp, ← star_eq_adjoint, ← map_star, star_star] using
      congrArg ContinuousLinearMap.adjoint (gnsDominationMap_intertwines hfg (star a))
  ext v; simp only [mul_apply_eq_comp, gnsRadonNikodym, ContinuousLinearMap.coe_comp,
    Function.comp_apply]
  have h1' := DFunLike.congr_fun h1 (f.gnsDominationMap g v)
  have h2' := DFunLike.congr_fun (gnsDominationMap_intertwines hfg a) v
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply] at h1' h2'
  rw [h1', ← h2']

/-- **Uniqueness of the GNS Radon–Nikodym operator.** Any bounded operator on `f.GNS` satisfying
`⟪[a]_f, T [b]_f⟫ = g (a⋆ b)` for all `a, b : A` equals `f.gnsRadonNikodym g`. -/
theorem eq_gnsRadonNikodym_of_inner_eq {f g : A →ₚ[ℂ] ℂ} {C : ℝ}
    (hfg : ∀ a, 0 ≤ a → g a ≤ (C : ℂ) * f a) {T : f.GNS →L[ℂ] f.GNS}
    (hT : ∀ a b, ⟪f.toGNS a, T (f.toGNS b)⟫_ℂ = g (star a * b)) :
    T = f.gnsRadonNikodym g := by
  ext v; refine ext_inner_left ℂ fun u => ?_
  refine f.denseRange_toGNS.induction_on u (isClosed_eq (by fun_prop) (by fun_prop)) fun a => ?_
  refine f.denseRange_toGNS.induction_on v (isClosed_eq (by fun_prop) (by fun_prop)) fun b => ?_
  rw [hT a b, inner_gnsRadonNikodym_toGNS hfg a b]

/-- **GNS commutant Radon–Nikodym theorem.** If `g` is a positive linear functional dominated by
`C • f` with `0 ≤ C`, there is a unique bounded operator `T` in the commutant of the GNS
representation of `f` such that `T` is positive, `‖T‖ ≤ C`, and `⟪[a]_f, T [b]_f⟫ = g (a⋆ b)` for
all `a, b : A`. -/
theorem existsUnique_gnsRadonNikodym {f g : A →ₚ[ℂ] ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hfg : ∀ a, 0 ≤ a → g a ≤ (C : ℂ) * f a) :
    ∃! T : f.GNS →L[ℂ] f.GNS,
      T ∈ Set.centralizer (Set.range f.gnsNonUnitalStarAlgHom) ∧ T.IsPositive ∧ ‖T‖ ≤ C ∧
        ∀ a b, ⟪f.toGNS a, T (f.toGNS b)⟫_ℂ = g (star a * b) :=
  ⟨f.gnsRadonNikodym g,
    ⟨gnsRadonNikodym_mem_centralizer hfg, f.isPositive_gnsRadonNikodym g,
      opNorm_gnsRadonNikodym_le hC hfg, inner_gnsRadonNikodym_toGNS hfg⟩,
    fun _ ⟨_, _, _, hinner⟩ => eq_gnsRadonNikodym_of_inner_eq hfg hinner⟩

end NonUnital

section Unital

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- For a unital C⋆-algebra, evaluating the vector functional of the GNS Radon–Nikodym operator on
`a` recovers `g a`. -/
theorem inner_gnsVector_gnsRadonNikodym {f g : B →ₚ[ℂ] ℂ} {C : ℝ}
    (hfg : ∀ a, 0 ≤ a → g a ≤ (C : ℂ) * f a) (a : B) :
    ⟪f.gnsVector, f.gnsRadonNikodym g (f.gnsStarAlgHom a f.gnsVector)⟫_ℂ = g a := by
  simpa [gnsVector_def, toGNS_apply] using inner_gnsRadonNikodym_toGNS hfg 1 a

/-- The continuous linear functional `a ↦ ⟪Ω_f, T (π_f(a) Ω_f)⟫` on a unital C⋆-algebra associated
to a bounded operator `T` on the GNS space `f.GNS`. -/
def gnsVectorFunctional (f : B →ₚ[ℂ] ℂ) (T : f.GNS →L[ℂ] f.GNS) : B →L[ℂ] ℂ :=
  ((innerSL ℂ f.gnsVector).comp T).comp f.toGNS

/-- The vector functional of `T` evaluates as `⟪Ω_f, T (π_f(a) Ω_f)⟫`. -/
@[simp]
theorem gnsVectorFunctional_apply (f : B →ₚ[ℂ] ℂ) (T : f.GNS →L[ℂ] f.GNS) (a : B) :
    f.gnsVectorFunctional T a = ⟪f.gnsVector, T (f.gnsStarAlgHom a f.gnsVector)⟫_ℂ := by
  simp [gnsVectorFunctional, toGNS_apply]

/-- The vector functional of the identity operator is `f`. -/
-- Not a simp lemma: `gnsVectorFunctional_apply` already simplifies `f.gnsVectorFunctional 1 a`.
theorem gnsVectorFunctional_one (f : B →ₚ[ℂ] ℂ) (a : B) :
    f.gnsVectorFunctional 1 a = f a := by simp

/-- The vector functional of the zero operator is `0`. -/
@[simp] theorem gnsVectorFunctional_zero (f : B →ₚ[ℂ] ℂ) :
    f.gnsVectorFunctional 0 = 0 := by ext a; simp

/-- The vector functional is additive in the operator. -/
@[simp] theorem gnsVectorFunctional_add (f : B →ₚ[ℂ] ℂ) (S T : f.GNS →L[ℂ] f.GNS) :
    f.gnsVectorFunctional (S + T) = f.gnsVectorFunctional S + f.gnsVectorFunctional T := by
  ext a; simp [inner_add_right]

/-- The vector functional negates with the operator. -/
@[simp] theorem gnsVectorFunctional_neg (f : B →ₚ[ℂ] ℂ) (T : f.GNS →L[ℂ] f.GNS) :
    f.gnsVectorFunctional (-T) = -f.gnsVectorFunctional T := by ext a; simp [inner_neg_right]

/-- The vector functional is subtractive in the operator. -/
@[simp] theorem gnsVectorFunctional_sub (f : B →ₚ[ℂ] ℂ) (S T : f.GNS →L[ℂ] f.GNS) :
    f.gnsVectorFunctional (S - T) = f.gnsVectorFunctional S - f.gnsVectorFunctional T := by
  ext a; simp [inner_sub_right]

/-- The vector functional is linear in scalar multiples of the operator. -/
@[simp] theorem gnsVectorFunctional_smul (f : B →ₚ[ℂ] ℂ) (c : ℂ) (T : f.GNS →L[ℂ] f.GNS) :
    f.gnsVectorFunctional (c • T) = c • f.gnsVectorFunctional T := by ext a; simp [inner_smul_right]

/-- For an operator `T` in the GNS commutant, the star pairing of `f.gnsVectorFunctional T` is
the matrix coefficient `⟪[a]_f, T [b]_f⟫`. -/
theorem gnsVectorFunctional_star_mul (f : B →ₚ[ℂ] ℂ) {T : f.GNS →L[ℂ] f.GNS}
    (hT : T ∈ Set.centralizer (Set.range f.gnsNonUnitalStarAlgHom)) (a b : B) :
    f.gnsVectorFunctional T (star a * b) = ⟪f.toGNS a, T (f.toGNS b)⟫_ℂ := by
  have hcomm := hT _ ⟨star a, rfl⟩
  calc f.gnsVectorFunctional T (star a * b)
      = ⟪f.gnsVector, (T * f.gnsNonUnitalStarAlgHom (star a))
          (f.gnsNonUnitalStarAlgHom b f.gnsVector)⟫_ℂ := by
        simp [map_mul, mul_apply_eq_comp]
    _ = ⟪f.gnsVector, f.gnsNonUnitalStarAlgHom (star a)
          (T (f.gnsNonUnitalStarAlgHom b f.gnsVector))⟫_ℂ := by
        rw [← hcomm, mul_apply_eq_comp]
    _ = ⟪f.toGNS a, T (f.toGNS b)⟫_ℂ := by
        rw [map_star, star_eq_adjoint, adjoint_inner_right]; simp [toGNS_apply]

/-- A positive operator in the GNS commutant defines a nonnegative functional on nonnegative
elements of `B`. -/
theorem gnsVectorFunctional_nonneg (f : B →ₚ[ℂ] ℂ) {T : f.GNS →L[ℂ] f.GNS}
    (hT : T ∈ Set.centralizer (Set.range f.gnsNonUnitalStarAlgHom)) (hTpos : T.IsPositive)
    {a : B} (ha : 0 ≤ a) : 0 ≤ f.gnsVectorFunctional T a := by
  rw [StarOrderedRing.nonneg_iff] at ha
  refine AddSubmonoid.closure_induction ?_ (by simp)
    (fun _ _ _ _ hx hy => by rw [map_add]; exact add_nonneg hx hy) ha
  rintro _ ⟨x, rfl⟩; rw [gnsVectorFunctional_star_mul f hT x x]
  exact hTpos.inner_nonneg_right (f.toGNS x)

/-- If `T` lies in the GNS commutant and `C • 1 - T` is positive, then the vector functional of `T`
is dominated by `C • f`. -/
theorem gnsVectorFunctional_le (f : B →ₚ[ℂ] ℂ) {T : f.GNS →L[ℂ] f.GNS}
    (hT : T ∈ Set.centralizer (Set.range f.gnsNonUnitalStarAlgHom)) {C : ℝ}
    (hTC : ((C : ℂ) • (1 : f.GNS →L[ℂ] f.GNS) - T).IsPositive) {a : B} (ha : 0 ≤ a) :
    f.gnsVectorFunctional T a ≤ (C : ℂ) * f a := by
  have hmem : (C : ℂ) • (1 : f.GNS →L[ℂ] f.GNS) - T ∈
      Set.centralizer (Set.range f.gnsNonUnitalStarAlgHom) := fun S hS => by
    rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, hT S hS]
  have h := gnsVectorFunctional_nonneg f hmem hTC ha
  simp only [gnsVectorFunctional_sub, gnsVectorFunctional_smul, sub_apply, smul_apply,
    gnsVectorFunctional_one, smul_eq_mul, sub_nonneg] at h
  exact h

/-- For a self-adjoint operator `T` in the GNS commutant, its vector functional is dominated by
`‖T‖ • f`. -/
theorem gnsVectorFunctional_le_opNorm_mul (f : B →ₚ[ℂ] ℂ) {T : f.GNS →L[ℂ] f.GNS}
    (hT : T ∈ Set.centralizer (Set.range f.gnsNonUnitalStarAlgHom)) (hTsa : IsSelfAdjoint T)
    {a : B} (ha : 0 ≤ a) : f.gnsVectorFunctional T a ≤ (‖T‖ : ℂ) * f a := by
  refine gnsVectorFunctional_le f hT ?_ ha
  rw [Complex.coe_smul, ← Algebra.algebraMap_eq_smul_one, ← ContinuousLinearMap.le_def]
  exact IsSelfAdjoint.le_algebraMap_norm_self T hTsa

/-- An operator in the GNS commutant whose vector functional vanishes kills the cyclic vector. -/
theorem apply_gnsVector_eq_zero_of_gnsVectorFunctional_eq_zero (f : B →ₚ[ℂ] ℂ)
    {T : f.GNS →L[ℂ] f.GNS} (hT : T ∈ Set.centralizer (Set.range f.gnsNonUnitalStarAlgHom))
    (hvan : f.gnsVectorFunctional T = 0) : T f.gnsVector = 0 := by
  refine ext_inner_left ℂ fun u =>
    f.denseRange_toGNS.induction_on u (isClosed_eq (by fun_prop) (by fun_prop)) fun a => ?_
  calc ⟪f.toGNS a, T f.gnsVector⟫_ℂ
      = ⟪f.gnsVector, (f.gnsNonUnitalStarAlgHom (star a) * T) f.gnsVector⟫_ℂ := by
        rw [mul_apply_eq_comp, map_star, star_eq_adjoint, adjoint_inner_right]; simp [toGNS_apply]
    _ = f.gnsVectorFunctional T (star a) := by
        rw [hT _ ⟨star a, rfl⟩, mul_apply_eq_comp]; simp [gnsVectorFunctional_apply]
    _ = ⟪f.toGNS a, 0⟫_ℂ := by simp [hvan]

/-- The vector functional of the GNS Radon–Nikodym operator of `g` recovers `g`. -/
theorem gnsVectorFunctional_gnsRadonNikodym {f g : B →ₚ[ℂ] ℂ} {C : ℝ}
    (hfg : ∀ a, 0 ≤ a → g a ≤ (C : ℂ) * f a) (a : B) :
    f.gnsVectorFunctional (f.gnsRadonNikodym g) a = g a :=
  (gnsVectorFunctional_apply f _ a).trans (inner_gnsVector_gnsRadonNikodym hfg a)

/-- The GNS Radon–Nikodym operator of the vector functional of a positive commutant operator `T`
recovers `T`. -/
theorem gnsRadonNikodym_gnsVectorFunctional (f : B →ₚ[ℂ] ℂ) {T : f.GNS →L[ℂ] f.GNS}
    (hT : T ∈ Set.centralizer (Set.range f.gnsNonUnitalStarAlgHom)) (hTpos : T.IsPositive) :
    f.gnsRadonNikodym (.mk₀ (f.gnsVectorFunctional T).toLinearMap fun _ =>
        gnsVectorFunctional_nonneg f hT hTpos) = T :=
  (eq_gnsRadonNikodym_of_inner_eq (C := ‖T‖)
    (fun _ ha => gnsVectorFunctional_le_opNorm_mul f hT hTpos.isSelfAdjoint ha)
    fun a b => (gnsVectorFunctional_star_mul f hT a b).symm).symm

end Unital

end PositiveLinearMap
