/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Basic
public import TauCeti.Analysis.Semigroups.Group.Generator
public import TauCeti.Analysis.Semigroups.Generator.ComplexLinear
public import Mathlib.Algebra.Star.NonUnitalSubalgebra
public import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Generators of C⋆-algebra actions

The generator of a point-norm continuous real action on a possibly nonunital C⋆-algebra
is a closed, densely defined complex `LinearPMap`. Its domain is a nonunital star
subalgebra, and the generator satisfies the Leibniz rule and commutes with star.
The domain is invariant under the action, which commutes with the generator.

Time is written as `Multiplicative ℝ` to use the existing `CStarAction` interface.
The construction uses `StronglyContinuousGroup` and its forward semigroup's
`complexGenerator` to connect the derivation with the existing unbounded-operator API.
Domain membership is characterized by differentiability of the orbit at zero.

## References

Bratteli--Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*,
second edition, Section 5.3, for generators of one-parameter automorphism groups.
-/

public section

noncomputable section

open scoped Topology
open TauCeti.Semigroups

namespace TauCeti.CStarAction

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- A continuous real C⋆-action, viewed as a strongly continuous group of real operators. -/
def toStronglyContinuousGroup (α : CStarAction (Multiplicative ℝ) A) :
    StronglyContinuousGroup A where
  toFun t := (α.toContinuousLinearMap (Multiplicative.ofAdd t)).restrictScalars ℝ
  map_zero' := by
    ext a
    simp
  map_add' s t := by
    ext a
    simp [ofAdd_add, mul_apply]
  continuousAt_zero' a := by
    simp only [ContinuousLinearMap.coe_restrictScalars', toContinuousLinearMap_apply]
    exact ((α.continuous_orbit a).comp continuous_ofAdd).continuousAt

@[simp]
theorem toStronglyContinuousGroup_apply (α : CStarAction (Multiplicative ℝ) A)
    (t : ℝ) (a : A) : α.toStronglyContinuousGroup t a = α (Multiplicative.ofAdd t) a :=
  toContinuousLinearMap_apply α _ a

/-- The operators of a C⋆-action are complex linear. -/
theorem toStronglyContinuousGroup_isComplexLinear
    (α : CStarAction (Multiplicative ℝ) A) :
    α.toStronglyContinuousGroup.toSemigroup.IsComplexLinear := by
  apply (StronglyContinuousSemigroup.isComplexLinear_iff _).mpr
  intro t z a
  simp [map_smul]

/-- The infinitesimal generator of a real C⋆-action, as a complex linear partial map. -/
def generator (α : CStarAction (Multiplicative ℝ) A) : A →ₗ.[ℂ] A :=
  α.toStronglyContinuousGroup.toSemigroup.complexGenerator
    α.toStronglyContinuousGroup_isComplexLinear

theorem generator_def (α : CStarAction (Multiplicative ℝ) A) :
    α.generator = α.toStronglyContinuousGroup.toSemigroup.complexGenerator
      α.toStronglyContinuousGroup_isComplexLinear :=
  (rfl)

/-- The complex generator domain is the domain of the underlying real group generator. -/
private theorem mem_generator_domain_iff (α : CStarAction (Multiplicative ℝ) A) (a : A) :
    a ∈ α.generator.domain ↔ a ∈ α.toStronglyContinuousGroup.domain := by
  simp [generator_def, StronglyContinuousGroup.domain_def]

/-- Restricting the generator to real scalars recovers the underlying group generator. -/
@[simp]
theorem generator_restrictScalars (α : CStarAction (Multiplicative ℝ) A) :
    α.generator.restrictScalars ℝ = α.toStronglyContinuousGroup.generator := by
  rw [generator_def, StronglyContinuousSemigroup.complexGenerator_restrictScalars,
    StronglyContinuousGroup.generator_def]

/-- The complex generator agrees with the underlying real group generator. -/
private theorem generator_apply (α : CStarAction (Multiplicative ℝ) A)
    (a : α.generator.domain) :
    α.generator a = α.toStronglyContinuousGroup.generator
      ⟨(a : A), by
        rw [α.toStronglyContinuousGroup.generator_domain]
        exact (α.mem_generator_domain_iff _).mp a.property⟩ := by
  exact (LinearPMap.congr_fun_restrictScalars ℝ α.generator_restrictScalars.symm
    (by
      rw [α.toStronglyContinuousGroup.generator_domain]
      exact (α.mem_generator_domain_iff _).mp a.property) a.property).symm

/-- Every orbit of a domain element is differentiable at zero with derivative its generator. -/
theorem hasDerivAt_zero (α : CStarAction (Multiplicative ℝ) A) (a : α.generator.domain) :
    HasDerivAt (fun t : ℝ => α (Multiplicative.ofAdd t) (a : A)) (α.generator a) 0 := by
  simpa only [toStronglyContinuousGroup_apply, generator_apply] using
    α.toStronglyContinuousGroup.hasDerivAt_zero
      ⟨(a : A), (α.mem_generator_domain_iff _).mp a.property⟩

/-- An element belongs to the generator domain exactly when its orbit is differentiable at zero. -/
theorem mem_generator_domain_iff_differentiableAt
    (α : CStarAction (Multiplicative ℝ) A) (a : A) :
    a ∈ α.generator.domain ↔
      DifferentiableAt ℝ (fun t : ℝ => α (Multiplicative.ofAdd t) a) 0 := by
  constructor
  · intro ha
    exact (α.hasDerivAt_zero ⟨a, ha⟩).differentiableAt
  · intro ha
    rw [α.mem_generator_domain_iff]
    exact α.toStronglyContinuousGroup.mem_domain_of_hasDerivAt_zero
      (by simpa only [toStronglyContinuousGroup_apply] using ha.hasDerivAt)

/-- Any derivative of an orbit at zero is its generator value. -/
theorem generator_eq_of_hasDerivAt (α : CStarAction (Multiplicative ℝ) A)
    {a b : A} (ha : a ∈ α.generator.domain)
    (h : HasDerivAt (fun t : ℝ => α (Multiplicative.ofAdd t) a) b 0) :
    α.generator ⟨a, ha⟩ = b :=
  (α.hasDerivAt_zero ⟨a, ha⟩).unique h

/-- The generator domain is norm dense. -/
theorem dense_generator_domain (α : CStarAction (Multiplicative ℝ) A) :
    Dense (α.generator.domain : Set A) := by
  simpa [generator_def] using
    α.toStronglyContinuousGroup.toSemigroup.dense_complexDomain
      α.toStronglyContinuousGroup_isComplexLinear

/-- The infinitesimal generator is closed in the norm topology. -/
theorem isClosed_generator (α : CStarAction (Multiplicative ℝ) A) :
    α.generator.IsClosed :=
  α.toStronglyContinuousGroup.toSemigroup.isClosed_complexGenerator
    α.toStronglyContinuousGroup_isComplexLinear

/-- At every real time the derivative of an orbit is the action on its generator value. -/
theorem hasDerivAt (α : CStarAction (Multiplicative ℝ) A) (a : α.generator.domain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => α (Multiplicative.ofAdd s) (a : A))
      (α (Multiplicative.ofAdd t) (α.generator a)) t := by
  simpa only [toStronglyContinuousGroup_apply, generator_apply] using
    α.toStronglyContinuousGroup.hasDerivAt
      ⟨(a : A), (α.mem_generator_domain_iff _).mp a.property⟩ t

/-- Multiplication of domain elements has the derivative prescribed by the Leibniz rule. -/
private theorem hasDerivAt_zero_mul (α : CStarAction (Multiplicative ℝ) A)
    (a b : α.generator.domain) :
    HasDerivAt (fun t : ℝ => α (Multiplicative.ofAdd t) ((a : A) * b))
      (α.generator a * b + (a : A) * α.generator b) 0 := by
  -- The bilinear derivative API works for nonunital algebras as well.
  simpa [map_mul, add_comm] using
    (ContinuousLinearMap.mul ℝ A).hasDerivAt_of_bilinear
      (fun _ => α.hasDerivAt_zero a) (fun _ => α.hasDerivAt_zero b)

/-- The generator domain is closed under multiplication. -/
theorem mul_mem_generator_domain (α : CStarAction (Multiplicative ℝ) A)
    {a b : A} (ha : a ∈ α.generator.domain) (hb : b ∈ α.generator.domain) :
    a * b ∈ α.generator.domain :=
  (α.mem_generator_domain_iff_differentiableAt _).mpr
    (α.hasDerivAt_zero_mul ⟨a, ha⟩ ⟨b, hb⟩).differentiableAt

/-- The infinitesimal generator satisfies the Leibniz rule. -/
@[simp]
theorem generator_mul (α : CStarAction (Multiplicative ℝ) A)
    (a b : α.generator.domain) :
    α.generator ⟨(a : A) * b, α.mul_mem_generator_domain a.property b.property⟩ =
      α.generator a * b + (a : A) * α.generator b :=
  α.generator_eq_of_hasDerivAt _ (α.hasDerivAt_zero_mul a b)

/-- The generator domain is closed under star. -/
theorem star_mem_generator_domain (α : CStarAction (Multiplicative ℝ) A)
    {a : A} (ha : a ∈ α.generator.domain) : star a ∈ α.generator.domain := by
  rw [α.mem_generator_domain_iff_differentiableAt]
  simpa only [map_star] using (α.hasDerivAt_zero ⟨a, ha⟩).star.differentiableAt

/-- Star preserves the generator domain in both directions. -/
@[simp]
theorem star_mem_generator_domain_iff (α : CStarAction (Multiplicative ℝ) A) (a : A) :
    star a ∈ α.generator.domain ↔ a ∈ α.generator.domain :=
  ⟨fun h => by simpa using α.star_mem_generator_domain h, α.star_mem_generator_domain⟩

/-- The infinitesimal generator commutes with star. -/
@[simp]
theorem generator_star (α : CStarAction (Multiplicative ℝ) A) (a : α.generator.domain) :
    α.generator ⟨star (a : A), α.star_mem_generator_domain a.property⟩ =
      star (α.generator a) := by
  apply α.generator_eq_of_hasDerivAt
  simpa only [map_star] using (α.hasDerivAt_zero a).star

/-- The generator domain as a complex nonunital star subalgebra of the ambient algebra. -/
def generatorDomain (α : CStarAction (Multiplicative ℝ) A) : NonUnitalStarSubalgebra ℂ A where
  carrier := α.generator.domain
  zero_mem' := α.generator.domain.zero_mem
  add_mem' := α.generator.domain.add_mem
  smul_mem' c _ h := α.generator.domain.smul_mem c h
  mul_mem' := α.mul_mem_generator_domain
  star_mem' := α.star_mem_generator_domain

@[simp]
theorem mem_generatorDomain (α : CStarAction (Multiplicative ℝ) A) (a : A) :
    a ∈ α.generatorDomain ↔ a ∈ α.generator.domain :=
  Iff.rfl

@[simp]
theorem generatorDomain_toSubmodule (α : CStarAction (Multiplicative ℝ) A) :
    α.generatorDomain.toSubmodule = α.generator.domain :=
  (rfl)

/-- The generator domain is invariant under every time of the action. -/
theorem apply_mem_generator_domain (α : CStarAction (Multiplicative ℝ) A)
    {a : A} (ha : a ∈ α.generator.domain) (t : ℝ) :
    α (Multiplicative.ofAdd t) a ∈ α.generator.domain := by
  rw [α.mem_generator_domain_iff]
  simpa only [toStronglyContinuousGroup_apply] using
    α.toStronglyContinuousGroup.map_mem_domain
      ⟨a, (α.mem_generator_domain_iff _).mp ha⟩ t

/-- Acting at any real time preserves membership in the generator domain in both directions. -/
@[simp]
theorem apply_mem_generator_domain_iff (α : CStarAction (Multiplicative ℝ) A)
    (t : ℝ) (a : A) :
    α (Multiplicative.ofAdd t) a ∈ α.generator.domain ↔ a ∈ α.generator.domain := by
  refine ⟨fun h => ?_, fun h => α.apply_mem_generator_domain h t⟩
  simpa only [ofAdd_neg, inv_apply_apply] using
    α.apply_mem_generator_domain h (-t)

/-- The action commutes with its infinitesimal generator on the invariant domain. -/
theorem generator_apply_action (α : CStarAction (Multiplicative ℝ) A)
    (a : α.generator.domain) (t : ℝ) :
    α.generator ⟨α (Multiplicative.ofAdd t) (a : A),
      α.apply_mem_generator_domain a.property t⟩ =
      α (Multiplicative.ofAdd t) (α.generator a) := by
  simpa only [generator_apply, toStronglyContinuousGroup_apply] using
    α.toStronglyContinuousGroup.generator_map
      ⟨(a : A), (α.mem_generator_domain_iff _).mp a.property⟩ t

section Unital

variable {B : Type*} [CStarAlgebra B]

/-- In a unital algebra the identity belongs to the generator domain. -/
@[simp]
theorem one_mem_generator_domain (α : CStarAction (Multiplicative ℝ) B) :
    (1 : B) ∈ α.generator.domain := by
  rw [α.mem_generator_domain_iff_differentiableAt]
  simpa only [map_one] using (differentiableAt_const (1 : B) :
    DifferentiableAt ℝ (fun _ : ℝ => (1 : B)) 0)

/-- The generator of a unital action vanishes at the identity. -/
@[simp]
theorem generator_one (α : CStarAction (Multiplicative ℝ) B) :
    α.generator ⟨1, α.one_mem_generator_domain⟩ = 0 := by
  apply α.generator_eq_of_hasDerivAt
  simpa only [map_one] using (hasDerivAt_const (0 : ℝ) (1 : B))

end Unital

end TauCeti.CStarAction
