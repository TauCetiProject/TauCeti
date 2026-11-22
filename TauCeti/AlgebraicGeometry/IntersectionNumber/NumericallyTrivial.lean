/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Fibers.Composition
public import TauCeti.AlgebraicGeometry.IntersectionNumber.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.ProjectiveLine

/-!
# Numerically trivial line-bundle classes

Let `X` be a scheme over a field `k`. A line-bundle class `a` on `X` is *numerically trivial*,
`a ≡ 0`, when its intersection number `(a · C) = deg_k (a|_C)` vanishes for every integral closed
curve `C ⊆ X`, singular curves included. For a morphism `f : X ⟶ S`, a class `a` on `X` is
*relatively numerically trivial*, `a ≡_f 0`, when for every point `s` of `S` its pullback to the
scheme-theoretic fibre `X_s = X ×_S Spec κ(s)` is numerically trivial over the residue field
`κ(s)`; all fibres are tested, and degrees are always taken over `κ(s)`.

Both conditions are stated on the Picard group `Pic X` (`LineBundleClass X`), so they depend only
on the isomorphism class of an invertible sheaf. When `X` is proper over `k` (respectively `f` is
proper), every test curve is a proper integral curve, on which the intersection number is
additive; hence the numerically trivial classes form a subgroup `Pic^τ(X/k)` of `Pic X`
(respectively `Pic^τ(X/S)`). The quotients by these subgroups are the numerical groups
`Num(X/k)` and `Num(X/S)`.

Numerical triviality is weaker than triviality, but it is not vacuous: on the projective line a
class is numerically trivial exactly when it is trivial, since the degree of `𝒪(n)` is `n`. On
the other hand every class pulled back from the base is relatively numerically trivial, so that
`Pic^τ(S/S) = Pic S` for the identity of `S` even when `Pic S` is nontrivial.

## Main declarations

* `LineBundleClass.NumericallyTrivial k x a`: the class `a` on a scheme `X` with structure
  morphism `x : X ⟶ Spec k` has degree zero on every integral closed curve of `X` over `k`;
* `LineBundleClass.numericallyTrivialClasses k x`: for `X` proper over `k`, the subgroup
  `Pic^τ(X/k)` of numerically trivial classes;
* `LineBundleClass.NumericallyTrivial.pullback_of_isClosedImmersion`: numerical triviality
  restricts to closed subschemes;
* `LineBundleClass.NumericallyTrivial.eulerDegree_eq_zero`: on an integral curve, a numerically
  trivial class has degree zero;
* `projectiveLine.numericallyTrivial_iff_eq_one`: on `ℙ¹_k` the numerically trivial classes are
  exactly the trivial class;
* `LineBundleClass.RelNumericallyTrivial f a`: relative numerical triviality `a ≡_f 0`, tested
  on the scheme-theoretic fibres of `f`;
* `LineBundleClass.relNumericallyTrivialClasses f`: for proper `f`, the subgroup `Pic^τ(X/S)`;
* `LineBundleClass.relNumericallyTrivial_pullback`: `f^* N ≡_f 0` for every class `N` on `S`,
  so that `f^* (Pic S) ≤ Pic^τ(X/S)` (`LineBundleClass.range_pullbackHom_le`) and
  `Pic^τ(S/S) = Pic S` (`LineBundleClass.relNumericallyTrivialClasses_id`);
* `LineBundleClass.RelNumericallyTrivial.pullback_of_isClosedImmersion`: if `a ≡_f 0` and
  `j : Z ⟶ X` is a closed immersion then `j^* a ≡_{j ≫ f} 0`.

## References

* S. L. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry*, Mathematical Surveys
  and Monographs 123, AMS, 2005, Definition 6.1.
* B. Bhatt et al., *Globally +-regular varieties and the minimal model program for threefolds in
  mixed characteristic*, Publ. Math. IHÉS 138 (2023), Remark 2.22.
* [The Stacks Project, Section 33.45](https://stacks.math.columbia.edu/tag/0BEL): numerical
  intersections on proper schemes over a field.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

namespace LineBundleClass

section Absolute

variable (k : Type u) [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (.of k))

/-- A line-bundle class `a` on a scheme `X` with structure morphism `x : X ⟶ Spec k` is
**numerically trivial** when its intersection number over `k` with every integral closed curve
`C ⊆ X` vanishes. The curve is a `k`-scheme through its closed immersion `i : C ⟶ X`, and singular
curves are included. -/
def NumericallyTrivial (a : LineBundleClass X) : Prop :=
  ∀ (C : Scheme.{u}) [IsIntegral C] [C.Over (Spec (.of k))] (i : C ⟶ X) [IsClosedImmersion i],
    C ↘ Spec (.of k) = i ≫ x → topologicalKrullDim C = 1 → intersectionNumber k i a = 0

/-- Numerical triviality unfolded: vanishing of the intersection number with every integral closed
curve over `k`. -/
theorem numericallyTrivial_iff (a : LineBundleClass X) :
    NumericallyTrivial k x a ↔ ∀ (C : Scheme.{u}) [IsIntegral C] [C.Over (Spec (.of k))]
      (i : C ⟶ X) [IsClosedImmersion i], C ↘ Spec (.of k) = i ≫ x →
        topologicalKrullDim C = 1 → intersectionNumber k i a = 0 :=
  Iff.rfl

variable {k x}

/-- The intersection number of a numerically trivial class with an integral closed curve over `k`
vanishes. -/
theorem NumericallyTrivial.intersectionNumber_eq_zero {a : LineBundleClass X}
    (ha : NumericallyTrivial k x a) {C : Scheme.{u}} [IsIntegral C] [C.Over (Spec (.of k))]
    (i : C ⟶ X) [IsClosedImmersion i] (hi : C ↘ Spec (.of k) = i ≫ x)
    (hC : topologicalKrullDim C = 1) : intersectionNumber k i a = 0 :=
  ha C i hi hC

variable (k x) in
/-- The trivial class is numerically trivial. -/
@[simp]
theorem numericallyTrivial_one : NumericallyTrivial k x (1 : LineBundleClass X) :=
  fun _ _ _ i _ _ _ ↦ intersectionNumber_one k i

section Proper

variable [IsProper x] {a b : LineBundleClass X}

/-- On a proper `k`-scheme, a product of numerically trivial classes is numerically trivial. -/
theorem NumericallyTrivial.mul (ha : NumericallyTrivial k x a) (hb : NumericallyTrivial k x b) :
    NumericallyTrivial k x (a * b) := fun _ _ _ i _ hi hC ↦ by
  rw [intersectionNumber_mul_of_isClosedImmersion k i hi hC, ha.intersectionNumber_eq_zero i hi hC,
    hb.intersectionNumber_eq_zero i hi hC, add_zero]

/-- On a proper `k`-scheme, the inverse of a numerically trivial class is numerically
trivial. -/
theorem NumericallyTrivial.inv (ha : NumericallyTrivial k x a) : NumericallyTrivial k x a⁻¹ :=
  fun _ _ _ i _ hi hC ↦ by
    rw [intersectionNumber_inv_of_isClosedImmersion k i hi hC,
      ha.intersectionNumber_eq_zero i hi hC, neg_zero]

/-- On a proper `k`-scheme, a class is numerically trivial exactly when its inverse is. -/
@[simp]
theorem numericallyTrivial_inv_iff : NumericallyTrivial k x a⁻¹ ↔ NumericallyTrivial k x a :=
  ⟨fun h ↦ inv_inv a ▸ h.inv, NumericallyTrivial.inv⟩

variable (k x) in
/-- The subgroup `Pic^τ(X/k)` of numerically trivial classes on a proper `k`-scheme `X`. The
quotient by it is the numerical group `Num(X/k)`. -/
def numericallyTrivialClasses : Subgroup (LineBundleClass X) where
  carrier := {a | NumericallyTrivial k x a}
  mul_mem' := NumericallyTrivial.mul
  one_mem' := numericallyTrivial_one k x
  inv_mem' := NumericallyTrivial.inv

/-- Membership in `Pic^τ(X/k)` is numerical triviality. -/
@[simp]
theorem mem_numericallyTrivialClasses :
    a ∈ numericallyTrivialClasses k x ↔ NumericallyTrivial k x a :=
  Iff.rfl

end Proper

/-- Numerical triviality restricts to closed subschemes: if `a` is numerically trivial on `X` and
`j : Z ⟶ X` is a closed immersion, then `j^* a` is numerically trivial on `Z`. -/
theorem NumericallyTrivial.pullback_of_isClosedImmersion {Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] {a : LineBundleClass X} (ha : NumericallyTrivial k x a) :
    NumericallyTrivial k (j ≫ x) (pullback j a) := fun C _ _ i _ hi hC ↦ by
  rw [intersectionNumber_pullback]
  exact ha.intersectionNumber_eq_zero (i ≫ j) (hi.trans (Category.assoc _ _ _).symm) hC

/-- **Degree on a curve.** A numerically trivial class on an integral `k`-scheme of dimension one
has degree zero: the scheme is itself one of the test curves. -/
theorem NumericallyTrivial.eulerDegree_eq_zero [X.Over (Spec (.of k))] [IsIntegral X]
    (hX : topologicalKrullDim X = 1) {a : LineBundleClass X}
    (ha : NumericallyTrivial k (X ↘ Spec (.of k)) a) : eulerDegree k a = 0 := by
  simpa [intersectionNumber_def] using
    ha.intersectionNumber_eq_zero (𝟙 X) (Category.id_comp _).symm hX

end Absolute

section Relative

variable {X Y S : Scheme.{u}}

/-- **Relative numerical triviality** `a ≡_f 0` of a line-bundle class `a` on `X` for a morphism
`f : X ⟶ S`: for every point `s` of `S`, the pullback of `a` to the scheme-theoretic fibre
`X_s = X ×_S Spec κ(s)` is numerically trivial over the residue field `κ(s)`. -/
def RelNumericallyTrivial (f : X ⟶ S) (a : LineBundleClass X) : Prop :=
  ∀ s : S, NumericallyTrivial (S.residueField s) (f.fiberToSpecResidueField s)
    (pullback (f.fiberι s) a)

/-- Relative numerical triviality unfolded: numerical triviality over `κ(s)` on each fibre. -/
theorem relNumericallyTrivial_iff (f : X ⟶ S) (a : LineBundleClass X) :
    RelNumericallyTrivial f a ↔ ∀ s : S, NumericallyTrivial (S.residueField s)
      (f.fiberToSpecResidueField s) (pullback (f.fiberι s) a) :=
  Iff.rfl

/-- The trivial class is relatively numerically trivial. -/
@[simp]
theorem relNumericallyTrivial_one (f : X ⟶ S) : RelNumericallyTrivial f (1 : LineBundleClass X) :=
  fun s ↦ by
    rw [pullback_one]
    exact numericallyTrivial_one _ _

/-- **Pullbacks from the base are relatively numerically trivial**: `f^* N ≡_f 0` for every
line-bundle class `N` on `S`. Its pullback to each fibre comes from the one-point scheme
`Spec κ(s)`, whose Picard group is trivial. -/
theorem relNumericallyTrivial_pullback (f : X ⟶ S) (N : LineBundleClass S) :
    RelNumericallyTrivial f (pullback f N) := fun s ↦ by
  have hN : pullback (S.fromSpecResidueField s) N = 1 :=
    eq_one_of_forall_specializes (x := IsLocalRing.closedPoint (S.residueField s))
      (fun y ↦ (Subsingleton.elim (α := PrimeSpectrum (S.residueField s)) y _) ▸ specializes_rfl) _
  rw [pullback_comp, Scheme.Hom.fiber_fac, ← pullback_comp, hN, pullback_one]
  exact numericallyTrivial_one _ _

section Proper

variable {f : X ⟶ S} [IsProper f] {a b : LineBundleClass X}

/-- For proper `f`, a product of relatively numerically trivial classes is relatively
numerically trivial. -/
theorem RelNumericallyTrivial.mul (ha : RelNumericallyTrivial f a)
    (hb : RelNumericallyTrivial f b) : RelNumericallyTrivial f (a * b) := fun s ↦ by
  rw [pullback_mul]
  exact (ha s).mul (hb s)

/-- For proper `f`, the inverse of a relatively numerically trivial class is relatively
numerically trivial. -/
theorem RelNumericallyTrivial.inv (ha : RelNumericallyTrivial f a) :
    RelNumericallyTrivial f a⁻¹ := fun s ↦ by
  rw [pullback_inv]
  exact (ha s).inv

/-- For proper `f`, a class is relatively numerically trivial exactly when its inverse is. -/
@[simp]
theorem relNumericallyTrivial_inv_iff :
    RelNumericallyTrivial f a⁻¹ ↔ RelNumericallyTrivial f a :=
  forall_congr' fun s ↦ by rw [pullback_inv, numericallyTrivial_inv_iff]

variable (f) in
/-- The subgroup `Pic^τ(X/S)` of relatively numerically trivial classes for a proper morphism
`f : X ⟶ S`. The quotient by it is the relative numerical group `Num(X/S)`. -/
def relNumericallyTrivialClasses : Subgroup (LineBundleClass X) where
  carrier := {a | RelNumericallyTrivial f a}
  mul_mem' := RelNumericallyTrivial.mul
  one_mem' := relNumericallyTrivial_one f
  inv_mem' := RelNumericallyTrivial.inv

/-- Membership in `Pic^τ(X/S)` is relative numerical triviality. -/
@[simp]
theorem mem_relNumericallyTrivialClasses :
    a ∈ relNumericallyTrivialClasses f ↔ RelNumericallyTrivial f a :=
  Iff.rfl

variable (f) in
/-- Every class pulled back from the base lies in `Pic^τ(X/S)`. -/
theorem range_pullbackHom_le : (pullbackHom f).range ≤ relNumericallyTrivialClasses f := by
  rintro _ ⟨N, rfl⟩
  rw [pullbackHom_apply, mem_relNumericallyTrivialClasses]
  exact relNumericallyTrivial_pullback f N

end Proper

variable (S) in
/-- For the identity of `S` every class is relatively numerically trivial:
`Pic^τ(S/S) = Pic S`. -/
@[simp]
theorem relNumericallyTrivialClasses_id : relNumericallyTrivialClasses (𝟙 S) = ⊤ :=
  eq_top_iff.mpr fun N _ ↦ pullback_id N ▸ relNumericallyTrivial_pullback (𝟙 S) N

/-- Relative numerical triviality restricts to closed subschemes: if `a ≡_f 0` and `j : Z ⟶ X`
is a closed immersion, then `j^* a ≡_{j ≫ f} 0`. -/
theorem RelNumericallyTrivial.pullback_of_isClosedImmersion {f : X ⟶ S} (j : Y ⟶ X)
    [IsClosedImmersion j] {a : LineBundleClass X} (ha : RelNumericallyTrivial f a) :
    RelNumericallyTrivial (j ≫ f) (pullback j a) := fun s ↦ by
  rw [pullback_comp, ← Scheme.Hom.fiberCompMap_fiberι, ← pullback_comp,
    ← Scheme.Hom.fiberCompMap_fiberToSpecResidueField]
  exact (ha s).pullback_of_isClosedImmersion (j.fiberCompMap f s)

end Relative

end LineBundleClass

namespace projectiveLine

variable (k : Type u) [Field k]

/-- **Numerical triviality on the projective line.** A line-bundle class on `ℙ¹_k` is
numerically trivial exactly when it is trivial: `𝒪(n)` has degree `n` on `ℙ¹_k` itself. -/
@[simp]
theorem numericallyTrivial_iff_eq_one (a : LineBundleClass (projectiveLine k)) :
    LineBundleClass.NumericallyTrivial k (projectiveLine k ↘ Spec (.of k)) a ↔ a = 1 := by
  refine ⟨fun ha ↦ ?_, fun ha ↦ ha ▸ LineBundleClass.numericallyTrivial_one k _⟩
  have h := ha.eulerDegree_eq_zero (Scheme.IsCurveOver.topologicalKrullDim_eq_one k)
  apply Additive.ofMul.injective
  apply (picardDegreeEquiv k).injective
  simpa using h

end projectiveLine

end TauCeti.AlgebraicGeometry
