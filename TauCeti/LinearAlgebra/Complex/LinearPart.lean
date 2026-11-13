/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic.Module

/-!
# Complex-linear and complex-antilinear parts of a linear map

Fix modules `V` and `W` over a scalar ring `R` (in the motivating case `R = ℝ`) equipped with
almost complex structures, that is, linear endomorphisms `J : V →ₗ[R] V` and
`J' : W →ₗ[R] W` with `J ∘ J = -1` and `J' ∘ J' = -1`. A linear map `F : V →ₗ[R] W` is
**complex linear** (with respect to the pair `(J, J')`) when it commutes with the structures,
`F ∘ J = J' ∘ F`, and **complex antilinear** when it anticommutes, `F ∘ J = -(J' ∘ F)`.

Over a field `𝕜` in which `2 ≠ 0`, every linear map splits canonically as the sum of a
complex-linear and a complex-antilinear map,
```
F = complexLinearPart J J' F + complexAntilinearPart J J' F,
```
with `complexLinearPart J J' F = ½ (F - J' ∘ F ∘ J)` and
`complexAntilinearPart J J' F = ½ (F + J' ∘ F ∘ J)`. This is the pointwise linearization at the
heart of the holomorphic theory: a smooth map between almost complex manifolds is
`J`-holomorphic exactly when its differential is complex linear, equivalently when its
complex-antilinear part `∂̄` vanishes. This file develops the linear-algebra layer of that
statement, before any smoothness or bundle structure is introduced.

The two predicates are stated over an arbitrary semiring `R` (complex antilinearity needs
negation on the target `W`), the submodules over a commutative semiring, and the two parts over
a field `𝕜`. The hypothesis `[NeZero (2 : 𝕜)]` is assumed only where `½ + ½ = 1` is used.

## Main definitions

* `TauCeti.IsComplexLinear J J' F`: the commutation condition `F ∘ J = J' ∘ F`.
* `TauCeti.IsComplexAntilinear J J' F`: the anticommutation condition `F ∘ J = -(J' ∘ F)`.
* `TauCeti.complexLinearPart J J' F`: the complex-linear part `½ (F - J' ∘ F ∘ J)` (the `∂`
  operator).
* `TauCeti.complexAntilinearPart J J' F`: the complex-antilinear part `½ (F + J' ∘ F ∘ J)`
  (the `∂̄` operator).
* `TauCeti.complexLinearPartLinearMap J J'` /
  `TauCeti.complexAntilinearPartLinearMap J J'`: the corresponding linear operators on
  `V →ₗ[𝕜] W` (these become genuine projections only under `J ∘ J = -1` and `J' ∘ J' = -1`).
* `TauCeti.complexLinearMaps J J'` / `TauCeti.complexAntilinearMaps J J'`: the submodules of
  complex-linear and complex-antilinear maps.

## Main results

* `TauCeti.complexLinearPart_add_complexAntilinearPart`: the decomposition `∂ + ∂̄ = id`.
* `TauCeti.complexLinearPart_isComplexLinear` /
  `TauCeti.complexAntilinearPart_isComplexAntilinear`: the two parts land in their named classes.
* `TauCeti.isComplexLinear_iff_complexAntilinearPart_eq_zero`: `F` is complex linear iff its
  complex-antilinear part vanishes (the `∂̄ F = 0` characterization).
* `TauCeti.isCompl_complexLinearMaps`: the complex-linear and complex-antilinear maps are
  complementary submodules of all linear maps.
* `TauCeti.isComplexLinear_arrowCongr_iff`: complex-linearity is preserved and reflected by
  conjugating source, target, and map along linear equivalences.
* `TauCeti.IsComplexLinear.symm`, `TauCeti.IsComplexAntilinear.symm`: the inverse of a
  complex-linear (complex-antilinear) equivalence is complex linear (complex antilinear).
* `TauCeti.add_apply_eq_zero_iff_eq_apply`: for `K` with `K² = -1`, the equation `a + K b = 0`
  is `b = K a`.

The sign conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
2nd ed., Section 2.2, specialized to the pointwise linear setting.
-/

public section

namespace TauCeti

section Semiring

variable {R V W U : Type*} [Semiring R]
  [AddCommMonoid V] [Module R V]
  [AddCommMonoid W] [Module R W]
  [AddCommMonoid U] [Module R U]

/-- A linear map `F : V →ₗ[R] W` is complex linear for the pair of almost complex
structures `(J, J')` when it intertwines them: `F ∘ J = J' ∘ F`. -/
def IsComplexLinear (J : V →ₗ[R] V) (J' : W →ₗ[R] W) (F : V →ₗ[R] W) : Prop :=
  F ∘ₗ J = J' ∘ₗ F

variable {J : V →ₗ[R] V} {J' : W →ₗ[R] W} {J'' : U →ₗ[R] U}

/-- Complex linearity restated as its defining commutation equation `F ∘ J = J' ∘ F`. -/
@[simp, grind =]
theorem isComplexLinear_iff {F : V →ₗ[R] W} :
    IsComplexLinear J J' F ↔ F ∘ₗ J = J' ∘ₗ F := Iff.rfl

/-- The pointwise form of complex linearity: `F (J v) = J' (F v)`. -/
theorem IsComplexLinear.apply {F : V →ₗ[R] W} (h : IsComplexLinear J J' F) (v : V) :
    F (J v) = J' (F v) :=
  LinearMap.congr_fun h v

/-- A linear map intertwining `J` and `J'` pointwise is complex linear. -/
theorem isComplexLinear_of_apply {F : V →ₗ[R] W} (h : ∀ v, F (J v) = J' (F v)) :
    IsComplexLinear J J' F :=
  LinearMap.ext h

/-- The inverse of a complex-linear equivalence is complex linear. -/
theorem IsComplexLinear.symm {e : V ≃ₗ[R] W} (h : IsComplexLinear J J' (e : V →ₗ[R] W)) :
    IsComplexLinear J' J (e.symm : W →ₗ[R] V) :=
  isComplexLinear_of_apply fun w => by
    rw [LinearEquiv.coe_coe, e.symm_apply_eq, ← LinearEquiv.coe_coe, h.apply,
      LinearEquiv.coe_coe, e.apply_symm_apply]

/-- The identity map is complex linear. -/
theorem isComplexLinear_id : IsComplexLinear J J (LinearMap.id) := by
  simp

/-- The zero map is complex linear. -/
theorem isComplexLinear_zero : IsComplexLinear J J' (0 : V →ₗ[R] W) := by
  simp

/-- The sum of two complex-linear maps is complex linear. -/
theorem IsComplexLinear.add {F G : V →ₗ[R] W} (hF : IsComplexLinear J J' F)
    (hG : IsComplexLinear J J' G) : IsComplexLinear J J' (F + G) :=
  isComplexLinear_of_apply fun v => by
    simp only [LinearMap.add_apply, map_add, hF.apply v, hG.apply v]

/-- The composite of two complex-linear maps is complex linear. -/
theorem IsComplexLinear.comp {F : V →ₗ[R] W} {G : W →ₗ[R] U}
    (hG : IsComplexLinear J' J'' G) (hF : IsComplexLinear J J' F) :
    IsComplexLinear J J'' (G ∘ₗ F) :=
  isComplexLinear_of_apply fun v => by
    simp only [LinearMap.comp_apply, hF.apply v, hG.apply (F v)]

end Semiring

section CommSemiring

variable {R V W : Type*} [CommSemiring R]
  [AddCommMonoid V] [Module R V]
  [AddCommMonoid W] [Module R W]
  {J : V →ₗ[R] V} {J' : W →ₗ[R] W}

/-- Raw complex-linearity is preserved and reflected by conjugating source and target along
linear equivalences. -/
theorem isComplexLinear_arrowCongr_iff {V₂ W₂ : Type*}
    [AddCommMonoid V₂] [Module R V₂] [AddCommMonoid W₂] [Module R W₂]
    {F : V →ₗ[R] W} (eV : V ≃ₗ[R] V₂) (eW : W ≃ₗ[R] W₂) :
    IsComplexLinear (eV.conj J) (eW.conj J') (eV.arrowCongr eW F) ↔
      IsComplexLinear J J' F := by
  constructor
  · intro hF
    refine isComplexLinear_of_apply fun v => ?_
    have h := hF.apply (eV v)
    simpa [LinearEquiv.arrowCongr_apply] using congrArg eW.symm h
  · intro hF
    refine isComplexLinear_of_apply fun v => ?_
    simp [LinearEquiv.arrowCongr_apply, hF.apply]

/-- A scalar multiple of a complex-linear map is complex linear. -/
theorem IsComplexLinear.smul {F : V →ₗ[R] W} (c : R) (h : IsComplexLinear J J' F) :
    IsComplexLinear J J' (c • F) :=
  isComplexLinear_of_apply fun v => by
    simp only [LinearMap.smul_apply, map_smul, h.apply v]

/-- The submodule of complex-linear maps `V →ₗ[R] W` for the pair `(J, J')`. -/
def complexLinearMaps (J : V →ₗ[R] V) (J' : W →ₗ[R] W) : Submodule R (V →ₗ[R] W) where
  carrier := {F | IsComplexLinear J J' F}
  zero_mem' := isComplexLinear_zero
  add_mem' := IsComplexLinear.add
  smul_mem' c _ hF := hF.smul c

/-- Membership in `complexLinearMaps J J'` is complex linearity. -/
@[simp, grind =]
theorem mem_complexLinearMaps {F : V →ₗ[R] W} :
    F ∈ complexLinearMaps J J' ↔ IsComplexLinear J J' F := Iff.rfl

end CommSemiring

section AddCommGroup

variable {R V W U : Type*} [Semiring R]
  [AddCommMonoid V] [Module R V]
  [AddCommGroup W] [Module R W]
  [AddCommGroup U] [Module R U]

/-- A linear map `F : V →ₗ[R] W` is complex antilinear for the pair of almost complex
structures `(J, J')` when it anti-intertwines them: `F ∘ J = -(J' ∘ F)`. -/
def IsComplexAntilinear (J : V →ₗ[R] V) (J' : W →ₗ[R] W) (F : V →ₗ[R] W) : Prop :=
  F ∘ₗ J = -(J' ∘ₗ F)

variable {J : V →ₗ[R] V} {J' : W →ₗ[R] W} {J'' : U →ₗ[R] U}

/-- Complex antilinearity restated as its defining anticommutation equation
`F ∘ J = -(J' ∘ F)`. -/
@[simp, grind =]
theorem isComplexAntilinear_iff {F : V →ₗ[R] W} :
    IsComplexAntilinear J J' F ↔ F ∘ₗ J = -(J' ∘ₗ F) := Iff.rfl

/-- The pointwise form of complex antilinearity: `F (J v) = -(J' (F v))`. -/
theorem IsComplexAntilinear.apply {F : V →ₗ[R] W} (h : IsComplexAntilinear J J' F) (v : V) :
    F (J v) = -(J' (F v)) :=
  LinearMap.congr_fun h v

/-- A linear map anti-intertwining `J` and `J'` pointwise is complex antilinear. -/
theorem isComplexAntilinear_of_apply {F : V →ₗ[R] W} (h : ∀ v, F (J v) = -(J' (F v))) :
    IsComplexAntilinear J J' F :=
  LinearMap.ext h

/-- Pointwise anticommutation `F (J v) + J' (F v) = 0` is equivalent to `(J, J')`-complex
antilinearity of `F`. -/
theorem isComplexAntilinear_iff_apply_add_apply_eq_zero {F : V →ₗ[R] W} :
    IsComplexAntilinear J J' F ↔ ∀ v, F (J v) + J' (F v) = 0 :=
  ⟨fun h v ↦ by rw [h.apply v, neg_add_cancel],
    fun h ↦ isComplexAntilinear_of_apply fun v ↦ eq_neg_of_add_eq_zero_left (h v)⟩

/-- The zero map is complex antilinear. -/
theorem isComplexAntilinear_zero : IsComplexAntilinear J J' (0 : V →ₗ[R] W) := by
  simp

/-- The negation of a complex-linear map is complex linear. -/
theorem IsComplexLinear.neg {F : V →ₗ[R] W} (h : IsComplexLinear J J' F) :
    IsComplexLinear J J' (-F) :=
  isComplexLinear_of_apply fun v => by simp [h.apply v]

/-- The negation of a complex-antilinear map is complex antilinear. -/
theorem IsComplexAntilinear.neg {F : V →ₗ[R] W} (h : IsComplexAntilinear J J' F) :
    IsComplexAntilinear J J' (-F) :=
  isComplexAntilinear_of_apply fun v => by simp [h.apply v]

/-- The sum of two complex-antilinear maps is complex antilinear. -/
theorem IsComplexAntilinear.add {F G : V →ₗ[R] W} (hF : IsComplexAntilinear J J' F)
    (hG : IsComplexAntilinear J J' G) : IsComplexAntilinear J J' (F + G) :=
  isComplexAntilinear_of_apply fun v => by
    simp only [LinearMap.add_apply, map_add, hF.apply v, hG.apply v, neg_add]

/-- The difference of two complex-linear maps is complex linear. -/
theorem IsComplexLinear.sub {F G : V →ₗ[R] W} (hF : IsComplexLinear J J' F)
    (hG : IsComplexLinear J J' G) : IsComplexLinear J J' (F - G) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

/-- The difference of two complex-antilinear maps is complex antilinear. -/
theorem IsComplexAntilinear.sub {F G : V →ₗ[R] W} (hF : IsComplexAntilinear J J' F)
    (hG : IsComplexAntilinear J J' G) : IsComplexAntilinear J J' (F - G) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

/-- The composite of two complex-antilinear maps is complex linear. -/
theorem IsComplexAntilinear.comp {F : V →ₗ[R] W} {G : W →ₗ[R] U}
    (hG : IsComplexAntilinear J' J'' G) (hF : IsComplexAntilinear J J' F) :
    IsComplexLinear J J'' (G ∘ₗ F) :=
  isComplexLinear_of_apply fun v => by
    simp only [LinearMap.comp_apply, hF.apply v, map_neg, hG.apply (F v), _root_.neg_neg]

/-- A complex-linear map after a complex-antilinear map is complex antilinear. -/
theorem IsComplexLinear.comp_antilinear {F : V →ₗ[R] W} {G : W →ₗ[R] U}
    (hG : IsComplexLinear J' J'' G) (hF : IsComplexAntilinear J J' F) :
    IsComplexAntilinear J J'' (G ∘ₗ F) :=
  isComplexAntilinear_of_apply fun v => by
    simp only [LinearMap.comp_apply, hF.apply v, map_neg, hG.apply (F v)]

section Intermediate

variable {W : Type*} [AddCommMonoid W] [Module R W] {J' : W →ₗ[R] W}

/-- A complex-antilinear map after a complex-linear map is complex antilinear. -/
theorem IsComplexAntilinear.comp_linear {F : V →ₗ[R] W} {G : W →ₗ[R] U}
    (hG : IsComplexAntilinear J' J'' G) (hF : IsComplexLinear J J' F) :
    IsComplexAntilinear J J'' (G ∘ₗ F) :=
  isComplexAntilinear_of_apply fun v => by
    simp only [LinearMap.comp_apply, hF.apply v, hG.apply (F v)]

end Intermediate

section Source

variable {V : Type*} [AddCommGroup V] [Module R V] {J : V →ₗ[R] V}

/-- The inverse of a complex-antilinear equivalence is complex antilinear. -/
theorem IsComplexAntilinear.symm {e : V ≃ₗ[R] W}
    (h : IsComplexAntilinear J J' (e : V →ₗ[R] W)) :
    IsComplexAntilinear J' J (e.symm : W →ₗ[R] V) :=
  isComplexAntilinear_of_apply fun w => by
    rw [LinearEquiv.coe_coe, e.symm_apply_eq, map_neg, ← LinearEquiv.coe_coe, h.apply,
      LinearEquiv.coe_coe, e.apply_symm_apply, _root_.neg_neg]

/-- Complex-linearity is unchanged after negating both source and target endomorphisms. -/
theorem IsComplexLinear.neg_neg {F : V →ₗ[R] W} (h : IsComplexLinear J J' F) :
    IsComplexLinear (-J) (-J') F :=
  isComplexLinear_of_apply fun v => by simp [h.apply v]

/-- If a map is complex-linear after negating both endomorphisms, then it was complex-linear
before the sign change. -/
theorem IsComplexLinear.of_neg_neg {F : V →ₗ[R] W}
    (h : IsComplexLinear (-J) (-J') F) : IsComplexLinear J J' F :=
  isComplexLinear_of_apply fun v => by
    simpa using congrArg Neg.neg (h.apply v)

/-- Complex-antilinearity is unchanged after negating both source and target endomorphisms. -/
theorem IsComplexAntilinear.neg_neg {F : V →ₗ[R] W} (h : IsComplexAntilinear J J' F) :
    IsComplexAntilinear (-J) (-J') F :=
  isComplexAntilinear_of_apply fun v => by simp [h.apply v]

/-- If a map is complex-antilinear after negating both endomorphisms, then it was
complex-antilinear before the sign change. -/
theorem IsComplexAntilinear.of_neg_neg {F : V →ₗ[R] W}
    (h : IsComplexAntilinear (-J) (-J') F) : IsComplexAntilinear J J' F :=
  isComplexAntilinear_of_apply fun v => by
    simpa using congrArg Neg.neg (h.apply v)

/-- Applying an almost complex structure twice negates, in pointwise form. -/
private theorem sq_apply (hsq : J ∘ₗ J = -LinearMap.id) (v : V) : J (J v) = -v :=
  LinearMap.congr_fun hsq v

end Source

end AddCommGroup

section CommSemiringAddCommGroup

variable {R V W : Type*} [CommSemiring R]
  [AddCommMonoid V] [Module R V]
  [AddCommGroup W] [Module R W]
  {J : V →ₗ[R] V} {J' : W →ₗ[R] W}

/-- A scalar multiple of a complex-antilinear map is complex antilinear. -/
theorem IsComplexAntilinear.smul {F : V →ₗ[R] W} (c : R) (h : IsComplexAntilinear J J' F) :
    IsComplexAntilinear J J' (c • F) :=
  isComplexAntilinear_of_apply fun v => by
    simp only [LinearMap.smul_apply, map_smul, h.apply v, smul_neg]

/-- The submodule of complex-antilinear maps `V →ₗ[R] W` for the pair `(J, J')`. -/
def complexAntilinearMaps (J : V →ₗ[R] V) (J' : W →ₗ[R] W) : Submodule R (V →ₗ[R] W) where
  carrier := {F | IsComplexAntilinear J J' F}
  zero_mem' := isComplexAntilinear_zero
  add_mem' := IsComplexAntilinear.add
  smul_mem' c _ hF := hF.smul c

/-- Membership in `complexAntilinearMaps J J'` is complex antilinearity. -/
@[simp, grind =]
theorem mem_complexAntilinearMaps {F : V →ₗ[R] W} :
    F ∈ complexAntilinearMaps J J' ↔ IsComplexAntilinear J J' F := Iff.rfl

end CommSemiringAddCommGroup

section Field

variable {𝕜 V W : Type*} [Field 𝕜]
  [AddCommMonoid V] [Module 𝕜 V]
  [AddCommGroup W] [Module 𝕜 W]

/-- The complex-linear-part operator `F ↦ ∂F` as a linear map on `V →ₗ[𝕜] W`. -/
noncomputable def complexLinearPartLinearMap (J : V →ₗ[𝕜] V) (J' : W →ₗ[𝕜] W) :
    (V →ₗ[𝕜] W) →ₗ[𝕜] (V →ₗ[𝕜] W) :=
  (2⁻¹ : 𝕜) • (LinearMap.id - LinearMap.compRight 𝕜 J' ∘ₗ LinearMap.lcomp 𝕜 W J)

/-- The complex-antilinear-part operator `F ↦ ∂̄F` as a linear map on `V →ₗ[𝕜] W`. -/
noncomputable def complexAntilinearPartLinearMap (J : V →ₗ[𝕜] V) (J' : W →ₗ[𝕜] W) :
    (V →ₗ[𝕜] W) →ₗ[𝕜] (V →ₗ[𝕜] W) :=
  (2⁻¹ : 𝕜) • (LinearMap.id + LinearMap.compRight 𝕜 J' ∘ₗ LinearMap.lcomp 𝕜 W J)

/-- The complex-linear part `∂F = ½ (F - J' ∘ F ∘ J)` of a linear map. -/
noncomputable def complexLinearPart (J : V →ₗ[𝕜] V) (J' : W →ₗ[𝕜] W) (F : V →ₗ[𝕜] W) :
    V →ₗ[𝕜] W :=
  complexLinearPartLinearMap J J' F

/-- The complex-antilinear part `∂̄F = ½ (F + J' ∘ F ∘ J)` of a linear map. -/
noncomputable def complexAntilinearPart (J : V →ₗ[𝕜] V) (J' : W →ₗ[𝕜] W)
    (F : V →ₗ[𝕜] W) : V →ₗ[𝕜] W :=
  complexAntilinearPartLinearMap J J' F

/-- The complex-linear-part operator, as a function, is `complexLinearPart J J'`. -/
@[simp]
theorem coe_complexLinearPartLinearMap (J : V →ₗ[𝕜] V) (J' : W →ₗ[𝕜] W) :
    ⇑(complexLinearPartLinearMap J J') = complexLinearPart J J' :=
  (rfl)

/-- The complex-antilinear-part operator, as a function, is `complexAntilinearPart J J'`. -/
@[simp]
theorem coe_complexAntilinearPartLinearMap (J : V →ₗ[𝕜] V) (J' : W →ₗ[𝕜] W) :
    ⇑(complexAntilinearPartLinearMap J J') = complexAntilinearPart J J' :=
  (rfl)

/-- The complex-linear-part operator sends `F` to its complex-linear part. -/
theorem complexLinearPartLinearMap_apply (J : V →ₗ[𝕜] V) (J' : W →ₗ[𝕜] W) (F : V →ₗ[𝕜] W) :
    complexLinearPartLinearMap J J' F = complexLinearPart J J' F :=
  (rfl)

/-- The complex-antilinear-part operator sends `F` to its complex-antilinear part. -/
theorem complexAntilinearPartLinearMap_apply (J : V →ₗ[𝕜] V) (J' : W →ₗ[𝕜] W) (F : V →ₗ[𝕜] W) :
    complexAntilinearPartLinearMap J J' F = complexAntilinearPart J J' F :=
  (rfl)

/-- The defining formula for the complex-linear part as a linear-map equality. -/
theorem complexLinearPart_def (J : V →ₗ[𝕜] V) (J' : W →ₗ[𝕜] W) (F : V →ₗ[𝕜] W) :
    complexLinearPart J J' F = (2⁻¹ : 𝕜) • (F - J' ∘ₗ F ∘ₗ J) :=
  (rfl)

/-- The defining formula for the complex-antilinear part as a linear-map equality. -/
theorem complexAntilinearPart_def (J : V →ₗ[𝕜] V) (J' : W →ₗ[𝕜] W) (F : V →ₗ[𝕜] W) :
    complexAntilinearPart J J' F = (2⁻¹ : 𝕜) • (F + J' ∘ₗ F ∘ₗ J) :=
  (rfl)

/-- The pointwise formula for the complex-linear part:
`∂F v = 1/2 • (F v - J' (F (J v)))`. -/
@[simp]
theorem complexLinearPart_apply (J : V →ₗ[𝕜] V) (J' : W →ₗ[𝕜] W) (F : V →ₗ[𝕜] W) (v : V) :
    complexLinearPart J J' F v = (2⁻¹ : 𝕜) • (F v - J' (F (J v))) :=
  (rfl)

/-- The pointwise formula for the complex-antilinear part:
`∂̄F v = 1/2 • (F v + J' (F (J v)))`. -/
@[simp]
theorem complexAntilinearPart_apply (J : V →ₗ[𝕜] V) (J' : W →ₗ[𝕜] W) (F : V →ₗ[𝕜] W) (v : V) :
    complexAntilinearPart J J' F v = (2⁻¹ : 𝕜) • (F v + J' (F (J v))) :=
  (rfl)

/-- The canonical decomposition `∂F + ∂̄F = F`. -/
@[simp]
theorem complexLinearPart_add_complexAntilinearPart [NeZero (2 : 𝕜)] (J : V →ₗ[𝕜] V)
    (J' : W →ₗ[𝕜] W) (F : V →ₗ[𝕜] W) :
    complexLinearPart J J' F + complexAntilinearPart J J' F = F := by
  rw [complexLinearPart_def, complexAntilinearPart_def, ← smul_add, sub_add_add_cancel,
    ← two_smul 𝕜 F, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

/-- The complex-linear-part and complex-antilinear-part operators add to the identity. -/
@[simp]
theorem complexLinearPartLinearMap_add_complexAntilinearPartLinearMap [NeZero (2 : 𝕜)]
    (J : V →ₗ[𝕜] V) (J' : W →ₗ[𝕜] W) :
    complexLinearPartLinearMap J J' + complexAntilinearPartLinearMap J J' = LinearMap.id :=
  LinearMap.ext (complexLinearPart_add_complexAntilinearPart J J')

/-- The complex-linear part is additive in `F`. -/
@[simp]
theorem complexLinearPart_add (J : V →ₗ[𝕜] V) (J' : W →ₗ[𝕜] W) (F G : V →ₗ[𝕜] W) :
    complexLinearPart J J' (F + G)
      = complexLinearPart J J' F + complexLinearPart J J' G :=
  map_add (complexLinearPartLinearMap J J') F G

/-- The complex-antilinear part is additive in `F`. -/
@[simp]
theorem complexAntilinearPart_add (J : V →ₗ[𝕜] V) (J' : W →ₗ[𝕜] W) (F G : V →ₗ[𝕜] W) :
    complexAntilinearPart J J' (F + G)
      = complexAntilinearPart J J' F + complexAntilinearPart J J' G :=
  map_add (complexAntilinearPartLinearMap J J') F G

/-- The complex-linear part commutes with scalar multiplication in `F`. -/
@[simp]
theorem complexLinearPart_smul (J : V →ₗ[𝕜] V) (J' : W →ₗ[𝕜] W) (c : 𝕜) (F : V →ₗ[𝕜] W) :
    complexLinearPart J J' (c • F) = c • complexLinearPart J J' F :=
  map_smul (complexLinearPartLinearMap J J') c F

/-- The complex-antilinear part commutes with scalar multiplication in `F`. -/
@[simp]
theorem complexAntilinearPart_smul (J : V →ₗ[𝕜] V) (J' : W →ₗ[𝕜] W) (c : 𝕜) (F : V →ₗ[𝕜] W) :
    complexAntilinearPart J J' (c • F) = c • complexAntilinearPart J J' F :=
  map_smul (complexAntilinearPartLinearMap J J') c F

/-- The complex-linear part of the zero map is zero. -/
@[simp]
theorem complexLinearPart_zero (J : V →ₗ[𝕜] V) (J' : W →ₗ[𝕜] W) :
    complexLinearPart J J' (0 : V →ₗ[𝕜] W) = 0 :=
  map_zero (complexLinearPartLinearMap J J')

/-- The complex-antilinear part of the zero map is zero. -/
@[simp]
theorem complexAntilinearPart_zero (J : V →ₗ[𝕜] V) (J' : W →ₗ[𝕜] W) :
    complexAntilinearPart J J' (0 : V →ₗ[𝕜] W) = 0 :=
  map_zero (complexAntilinearPartLinearMap J J')

/-- The complex-linear part commutes with negation in `F`. -/
@[simp]
theorem complexLinearPart_neg (J : V →ₗ[𝕜] V) (J' : W →ₗ[𝕜] W) (F : V →ₗ[𝕜] W) :
    complexLinearPart J J' (-F) = -complexLinearPart J J' F :=
  map_neg (complexLinearPartLinearMap J J') F

/-- The complex-antilinear part commutes with negation in `F`. -/
@[simp]
theorem complexAntilinearPart_neg (J : V →ₗ[𝕜] V) (J' : W →ₗ[𝕜] W) (F : V →ₗ[𝕜] W) :
    complexAntilinearPart J J' (-F) = -complexAntilinearPart J J' F :=
  map_neg (complexAntilinearPartLinearMap J J') F

/-- The complex-linear part commutes with subtraction in `F`. -/
@[simp]
theorem complexLinearPart_sub (J : V →ₗ[𝕜] V) (J' : W →ₗ[𝕜] W) (F G : V →ₗ[𝕜] W) :
    complexLinearPart J J' (F - G) = complexLinearPart J J' F - complexLinearPart J J' G :=
  map_sub (complexLinearPartLinearMap J J') F G

/-- The complex-antilinear part commutes with subtraction in `F`. -/
@[simp]
theorem complexAntilinearPart_sub (J : V →ₗ[𝕜] V) (J' : W →ₗ[𝕜] W) (F G : V →ₗ[𝕜] W) :
    complexAntilinearPart J J' (F - G)
      = complexAntilinearPart J J' F - complexAntilinearPart J J' G :=
  map_sub (complexAntilinearPartLinearMap J J') F G

/-- For an additive endomorphism `K` with `K² = -1`, such as an almost complex structure, the
equation `a + K b = 0` is equivalent to `b = K a`. -/
theorem add_apply_eq_zero_iff_eq_apply {M F : Type*} [AddGroup M] [FunLike F M M]
    [AddMonoidHomClass F M M] {K : F} (hK : ∀ v, K (K v) = -v) (a b : M) :
    a + K b = 0 ↔ b = K a := by
  constructor
  · intro h
    have := congrArg K h
    rw [map_add, hK, map_zero] at this
    exact (add_neg_eq_zero.1 this).symm
  · rintro rfl
    rw [hK, add_neg_cancel]

variable {J : V →ₗ[𝕜] V} {J' : W →ₗ[𝕜] W}

/-- The complex-antilinear part of a complex-linear map vanishes. -/
theorem IsComplexLinear.complexAntilinearPart_eq_zero {F : V →ₗ[𝕜] W}
    (h : IsComplexLinear J J' F) (hJ' : J' ∘ₗ J' = -LinearMap.id) :
    complexAntilinearPart J J' F = 0 := by
  ext v
  simp [h.apply v, sq_apply hJ']

/-- The complex-linear part of a complex-antilinear map vanishes. -/
theorem IsComplexAntilinear.complexLinearPart_eq_zero {F : V →ₗ[𝕜] W}
    (h : IsComplexAntilinear J J' F) (hJ' : J' ∘ₗ J' = -LinearMap.id) :
    complexLinearPart J J' F = 0 := by
  ext v
  simp [h.apply v, sq_apply hJ']

/-- A linear map is complex linear exactly when its complex-antilinear part vanishes:
the linear-algebra shadow of "`F` is `J`-holomorphic iff `∂̄F = 0`". -/
theorem isComplexLinear_iff_complexAntilinearPart_eq_zero [NeZero (2 : 𝕜)]
    (hJ' : J' ∘ₗ J' = -LinearMap.id) (F : V →ₗ[𝕜] W) :
    IsComplexLinear J J' F ↔ complexAntilinearPart J J' F = 0 := by
  refine ⟨fun h => h.complexAntilinearPart_eq_zero hJ', fun h =>
    isComplexLinear_of_apply fun v => ?_⟩
  have hv : F v + J' (F (J v)) = 0 :=
    (inv_ne_zero (two_ne_zero (α := 𝕜))).isUnit.smul_eq_zero.mp (LinearMap.congr_fun h v)
  rw [eq_neg_of_add_eq_zero_left hv, map_neg, sq_apply hJ', neg_neg]

/-- A linear map is complex antilinear exactly when its complex-linear part vanishes. -/
theorem isComplexAntilinear_iff_complexLinearPart_eq_zero [NeZero (2 : 𝕜)]
    (hJ' : J' ∘ₗ J' = -LinearMap.id) (F : V →ₗ[𝕜] W) :
    IsComplexAntilinear J J' F ↔ complexLinearPart J J' F = 0 := by
  refine ⟨fun h => h.complexLinearPart_eq_zero hJ', fun h =>
    isComplexAntilinear_of_apply fun v => ?_⟩
  have hv : F v - J' (F (J v)) = 0 :=
    (inv_ne_zero (two_ne_zero (α := 𝕜))).isUnit.smul_eq_zero.mp (LinearMap.congr_fun h v)
  rw [sub_eq_zero.mp hv, sq_apply hJ', neg_neg]

/-- A complex-linear map equals its own complex-linear part. -/
theorem IsComplexLinear.complexLinearPart_eq [NeZero (2 : 𝕜)] {F : V →ₗ[𝕜] W}
    (h : IsComplexLinear J J' F) (hJ' : J' ∘ₗ J' = -LinearMap.id) :
    complexLinearPart J J' F = F := by
  simpa [h.complexAntilinearPart_eq_zero hJ'] using
    complexLinearPart_add_complexAntilinearPart J J' F

/-- A complex-antilinear map equals its own complex-antilinear part. -/
theorem IsComplexAntilinear.complexAntilinearPart_eq [NeZero (2 : 𝕜)] {F : V →ₗ[𝕜] W}
    (h : IsComplexAntilinear J J' F) (hJ' : J' ∘ₗ J' = -LinearMap.id) :
    complexAntilinearPart J J' F = F := by
  simpa [h.complexLinearPart_eq_zero hJ'] using
    complexLinearPart_add_complexAntilinearPart J J' F

/-- Uniqueness of the complex-linear/antilinear decomposition: if `F = A + B` with `A` complex
linear and `B` complex antilinear, then `A` and `B` are the canonical parts of `F`. -/
theorem complexLinearPart_eq_and_complexAntilinearPart_eq_of_decomp [NeZero (2 : 𝕜)]
    (hJ' : J' ∘ₗ J' = -LinearMap.id) {F A B : V →ₗ[𝕜] W}
    (hA : IsComplexLinear J J' A) (hB : IsComplexAntilinear J J' B) (hF : F = A + B) :
    A = complexLinearPart J J' F ∧ B = complexAntilinearPart J J' F := by
  refine ⟨?_, ?_⟩
  · rw [hF, complexLinearPart_add, hA.complexLinearPart_eq hJ',
      hB.complexLinearPart_eq_zero hJ', add_zero]
  · rw [hF, complexAntilinearPart_add, hA.complexAntilinearPart_eq_zero hJ',
      hB.complexAntilinearPart_eq hJ', zero_add]

section Source

variable {V : Type*} [AddCommGroup V] [Module 𝕜 V] {J : V →ₗ[𝕜] V}

/-- The complex-linear part really is complex linear. -/
theorem complexLinearPart_isComplexLinear (hJ : J ∘ₗ J = -LinearMap.id)
    (hJ' : J' ∘ₗ J' = -LinearMap.id) (F : V →ₗ[𝕜] W) :
    IsComplexLinear J J' (complexLinearPart J J' F) := by
  refine isComplexLinear_of_apply fun v => ?_
  simp only [complexLinearPart_apply, sq_apply hJ, sq_apply hJ', map_smul, map_sub, map_neg]
  module

/-- The complex-antilinear part really is complex antilinear. -/
theorem complexAntilinearPart_isComplexAntilinear (hJ : J ∘ₗ J = -LinearMap.id)
    (hJ' : J' ∘ₗ J' = -LinearMap.id) (F : V →ₗ[𝕜] W) :
    IsComplexAntilinear J J' (complexAntilinearPart J J' F) := by
  refine isComplexAntilinear_of_apply fun v => ?_
  simp only [complexAntilinearPart_apply, sq_apply hJ, sq_apply hJ', map_smul, map_add, map_neg]
  module

/-- For genuine almost complex structures, every linear map splits uniquely as a
complex-linear plus a complex-antilinear map: the two submodules are complementary. -/
theorem isCompl_complexLinearMaps [NeZero (2 : 𝕜)] (hJ : J ∘ₗ J = -LinearMap.id)
    (hJ' : J' ∘ₗ J' = -LinearMap.id) :
    IsCompl (complexLinearMaps J J') (complexAntilinearMaps J J') := by
  constructor
  · refine Submodule.disjoint_def.mpr fun F hlin hanti => ?_
    rw [← complexLinearPart_add_complexAntilinearPart J J' F,
      (mem_complexLinearMaps.mp hlin).complexAntilinearPart_eq_zero hJ',
      (mem_complexAntilinearMaps.mp hanti).complexLinearPart_eq_zero hJ', add_zero]
  · refine codisjoint_iff.mpr <| eq_top_iff.mpr fun F _ => Submodule.mem_sup.mpr ?_
    exact ⟨complexLinearPart J J' F, complexLinearPart_isComplexLinear hJ hJ' F,
      complexAntilinearPart J J' F, complexAntilinearPart_isComplexAntilinear hJ hJ' F,
      complexLinearPart_add_complexAntilinearPart J J' F⟩

end Source

end Field

end TauCeti
