/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IntersectionNumber.NumericallyTrivial

/-!
# Nef line-bundle classes

Let `X` be a scheme over a field `k`. A line-bundle class `a` on `X` is *nef* when its
intersection number `(a · C) = deg_k (a|_C)` is nonnegative for every integral closed curve
`C ⊆ X`, singular curves included. This is the positivity notion dual to the cone of curves: the
nef classes are those pairing nonnegatively with every effective curve, and ampleness criteria
such as Kleiman's are stated in terms of it.

When `X` is proper over `k`, every test curve is a proper integral curve, on which the
intersection number is additive. Hence the nef classes form a submonoid of `Pic X`, the nef cone
at the level of the Picard group, closed under positive powers, and nefness of a positive power
`aⁿ` is nefness of `a`. A class is numerically trivial exactly when it and its inverse are both
nef, so the numerically trivial classes are nef, and twisting by a numerically trivial class does
not change nefness: nefness depends only on the numerical class.

On an integral curve, the only integral closed curve is the curve itself, so a class is nef
exactly when its degree is nonnegative. On the projective line this gives that `𝒪(n)` is nef
exactly when `n ≥ 0`; in particular nefness is weaker than numerical triviality.

## Main declarations

* `LineBundleClass.IsNef k x a`: the class `a` on a scheme `X` with structure morphism
  `x : X ⟶ Spec k` has nonnegative degree on every integral closed curve of `X` over `k`;
* `LineBundleClass.NumericallyTrivial.isNef`: numerically trivial classes are nef;
* `LineBundleClass.IsNef.mul` and `LineBundleClass.IsNef.pow`: on a proper `k`-scheme, nef
  classes are closed under products and powers, and `LineBundleClass.isNef_pow_iff` says that
  `aⁿ` is nef for `n ≠ 0` exactly when `a` is;
* `LineBundleClass.nefClasses k x`: for `X` proper over `k`, the submonoid of nef classes, which
  contains `Pic^τ(X/k)` (`LineBundleClass.numericallyTrivialClasses_le_nefClasses`);
* `LineBundleClass.numericallyTrivial_iff_isNef_and_isNef_inv`: a class is numerically trivial
  exactly when it and its inverse are nef;
* `LineBundleClass.isNef_mul_iff_of_numericallyTrivial`: twisting by a numerically trivial class
  preserves and reflects nefness;
* `LineBundleClass.IsNef.pullback_of_isClosedImmersion`: nefness restricts to closed subschemes;
* `LineBundleClass.isNef_iff_eulerDegree_nonneg`: on an integral curve, a class is nef exactly
  when its degree is nonnegative;
* `projectiveLine.isNef_picardDegreeEquiv_symm_iff`: on `ℙ¹_k`, the class of `𝒪(n)` is nef
  exactly when `n ≥ 0`.

## References

* R. Lazarsfeld, *Positivity in Algebraic Geometry I*, Ergebnisse der Mathematik 48, Springer,
  2004, Definition 1.4.1 and Example 1.4.3.
* B. Bhatt et al., *Globally +-regular varieties and the minimal model program for threefolds in
  mixed characteristic*, Publ. Math. IHÉS 138 (2023), Section 2.5.
* J. Witaszek, *Keel's base point free theorem and quotients in mixed characteristic*, Ann. of
  Math. 195 (2022), Section 2.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

namespace LineBundleClass

variable (k : Type u) [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (.of k))

/-- A line-bundle class `a` on a scheme `X` with structure morphism `x : X ⟶ Spec k` is **nef**
when its intersection number over `k` with every integral closed curve `C ⊆ X` is nonnegative.
The curve is a `k`-scheme through its closed immersion `i : C ⟶ X`, and singular curves are
included. -/
def IsNef (a : LineBundleClass X) : Prop :=
  ∀ (C : Scheme.{u}) [IsIntegral C] [C.Over (Spec (.of k))] (i : C ⟶ X) [IsClosedImmersion i],
    C ↘ Spec (.of k) = i ≫ x → topologicalKrullDim C = 1 → 0 ≤ intersectionNumber k i a

/-- Nefness unfolded: nonnegativity of the intersection number with every integral closed curve
over `k`. -/
theorem isNef_iff (a : LineBundleClass X) :
    IsNef k x a ↔ ∀ (C : Scheme.{u}) [IsIntegral C] [C.Over (Spec (.of k))] (i : C ⟶ X)
      [IsClosedImmersion i], C ↘ Spec (.of k) = i ≫ x → topologicalKrullDim C = 1 →
        0 ≤ intersectionNumber k i a :=
  Iff.rfl

variable {k x}

/-- The intersection number of a nef class with an integral closed curve over `k` is
nonnegative. -/
theorem IsNef.intersectionNumber_nonneg {a : LineBundleClass X} (ha : IsNef k x a)
    {C : Scheme.{u}} [IsIntegral C] [C.Over (Spec (.of k))] (i : C ⟶ X) [IsClosedImmersion i]
    (hi : C ↘ Spec (.of k) = i ≫ x) (hC : topologicalKrullDim C = 1) :
    0 ≤ intersectionNumber k i a :=
  ha C i hi hC

/-- A numerically trivial class is nef: its intersection number with every integral closed curve
is zero. -/
theorem NumericallyTrivial.isNef {a : LineBundleClass X} (ha : NumericallyTrivial k x a) :
    IsNef k x a :=
  fun _ _ _ i _ hi hC ↦ (ha.intersectionNumber_eq_zero i hi hC).ge

variable (k x) in
/-- The trivial class is nef. -/
@[simp]
theorem isNef_one : IsNef k x (1 : LineBundleClass X) :=
  (numericallyTrivial_one k x).isNef

section Proper

variable [IsProper x] {a b : LineBundleClass X}

/-- On a proper `k`-scheme, a product of nef classes is nef. -/
theorem IsNef.mul (ha : IsNef k x a) (hb : IsNef k x b) : IsNef k x (a * b) :=
  fun _ _ _ i _ hi hC ↦ by
    rw [intersectionNumber_mul_of_isClosedImmersion k i hi hC]
    exact add_nonneg (ha.intersectionNumber_nonneg i hi hC) (hb.intersectionNumber_nonneg i hi hC)

/-- On a proper `k`-scheme, every power of a nef class is nef. -/
theorem IsNef.pow (ha : IsNef k x a) (n : ℕ) : IsNef k x (a ^ n) :=
  fun _ _ _ i _ hi hC ↦ by
    rw [intersectionNumber_pow_of_isClosedImmersion k i hi hC]
    exact mul_nonneg (Int.natCast_nonneg n) (ha.intersectionNumber_nonneg i hi hC)

/-- On a proper `k`-scheme, a positive power `aⁿ` of a class is nef exactly when `a` is: the
intersection numbers of `aⁿ` are `n` times those of `a`. -/
@[simp]
theorem isNef_pow_iff {n : ℕ} (hn : n ≠ 0) : IsNef k x (a ^ n) ↔ IsNef k x a := by
  refine ⟨fun ha C _ _ i _ hi hC ↦ ?_, fun ha ↦ ha.pow n⟩
  have h := ha.intersectionNumber_nonneg i hi hC
  rw [intersectionNumber_pow_of_isClosedImmersion k i hi hC] at h
  exact nonneg_of_mul_nonneg_right h (by positivity)

/-- On a proper `k`-scheme, a class is numerically trivial exactly when it and its inverse are
both nef. -/
theorem numericallyTrivial_iff_isNef_and_isNef_inv :
    NumericallyTrivial k x a ↔ IsNef k x a ∧ IsNef k x a⁻¹ := by
  refine ⟨fun ha ↦ ⟨ha.isNef, ha.inv.isNef⟩, fun ⟨ha, ha'⟩ ↦
    (numericallyTrivial_iff k x a).mpr fun C _ _ i _ hi hC ↦ ?_⟩
  have h := ha'.intersectionNumber_nonneg i hi hC
  rw [intersectionNumber_inv_of_isClosedImmersion k i hi hC] at h
  exact le_antisymm (neg_nonneg.mp h) (ha.intersectionNumber_nonneg i hi hC)

/-- On a proper `k`-scheme, nefness depends only on the numerical class: twisting by a
numerically trivial class `b` preserves and reflects nefness. -/
theorem isNef_mul_iff_of_numericallyTrivial (hb : NumericallyTrivial k x b) :
    IsNef k x (a * b) ↔ IsNef k x a :=
  ⟨fun h ↦ by simpa using h.mul hb.inv.isNef, fun ha ↦ ha.mul hb.isNef⟩

variable (k x) in
/-- The submonoid of nef classes on a proper `k`-scheme `X`: the nef cone at the level of the
Picard group. -/
def nefClasses : Submonoid (LineBundleClass X) where
  carrier := {a | IsNef k x a}
  mul_mem' := IsNef.mul
  one_mem' := isNef_one k x

/-- Membership in the submonoid of nef classes is nefness. -/
@[simp]
theorem mem_nefClasses : a ∈ nefClasses k x ↔ IsNef k x a :=
  Iff.rfl

variable (k x) in
/-- The numerically trivial classes `Pic^τ(X/k)` are nef. -/
theorem numericallyTrivialClasses_le_nefClasses :
    (numericallyTrivialClasses k x).toSubmonoid ≤ nefClasses k x :=
  fun _ ha ↦ (mem_numericallyTrivialClasses.mp ha).isNef

end Proper

/-- Nefness restricts to closed subschemes: if `a` is nef on `X` and `j : Z ⟶ X` is a closed
immersion, then `j^* a` is nef on `Z`. -/
theorem IsNef.pullback_of_isClosedImmersion {Z : Scheme.{u}} (j : Z ⟶ X) [IsClosedImmersion j]
    {a : LineBundleClass X} (ha : IsNef k x a) : IsNef k (j ≫ x) (pullback j a) :=
  fun C _ _ i _ hi hC ↦ by
    rw [intersectionNumber_pullback]
    exact ha.intersectionNumber_nonneg (i ≫ j) (hi.trans (Category.assoc _ _ _).symm) hC

/-- **Nefness on a curve.** On an integral `k`-scheme of dimension one, a class is nef exactly
when its degree is nonnegative: the scheme is its only integral closed curve. -/
theorem isNef_iff_eulerDegree_nonneg [X.Over (Spec (.of k))] [IsIntegral X]
    (hX : topologicalKrullDim X = 1) {a : LineBundleClass X} :
    IsNef k (X ↘ Spec (.of k)) a ↔ 0 ≤ eulerDegree k a := by
  refine ⟨fun ha ↦ ?_, fun ha C _ _ i _ hi hC ↦ ?_⟩
  · simpa [intersectionNumber_def] using
      ha.intersectionNumber_nonneg (𝟙 X) (Category.id_comp _).symm hX
  · rwa [intersectionNumber_eq_eulerDegree_of_isClosedImmersion k i hX.le hi hC]

end LineBundleClass

namespace projectiveLine

variable (k : Type u) [Field k]

/-- **Nefness on the projective line.** The class of the twisting sheaf `𝒪(n)` on `ℙ¹_k`, which is
`(picardDegreeEquiv k).symm n` (`projectiveLine.picardDegreeEquiv_symm_apply`), is nef exactly
when `n ≥ 0`: a class on `ℙ¹_k` is nef exactly when its degree is nonnegative. -/
theorem isNef_picardDegreeEquiv_symm_iff (n : ℤ) :
    LineBundleClass.IsNef k (projectiveLine k ↘ Spec (.of k))
      ((picardDegreeEquiv k).symm n).toMul ↔ 0 ≤ n := by
  rw [LineBundleClass.isNef_iff_eulerDegree_nonneg
    (Scheme.IsCurveOver.topologicalKrullDim_eq_one k), ← picardDegreeEquiv_apply,
    AddEquiv.apply_symm_apply]

end projectiveLine

end TauCeti.AlgebraicGeometry
