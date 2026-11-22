/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IntersectionNumber.NumericallyTrivial

/-!
# The numerical groups `Num(X/k)` and `Num(X/S)`

Let `X` be a proper scheme over a field `k`, with structure morphism `x : X ⟶ Spec k`. The
*numerical group* `Num(X/k)` is the quotient of the Picard group `Pic X` by the subgroup
`Pic^τ(X/k)` of numerically trivial classes; here it is the quotient group
`LineBundleClass X ⧸ numericallyTrivialClasses k x`. Likewise, for a proper morphism
`f : X ⟶ S`, the *relative numerical group* `Num(X/S)` is
`LineBundleClass X ⧸ relNumericallyTrivialClasses f`.

This file develops the basic structure of these quotients.

* The intersection number with an integral closed curve `C ⊆ X` descends to `Num(X/k)`, and a
  numerical class is determined by these intersection numbers: two line-bundle classes have the
  same image in `Num(X/k)` exactly when they have the same degree on every integral closed curve.
* Restriction to the scheme-theoretic fibre `X_s` over a point `s` of `S` induces a homomorphism
  `Num(X/S) ⟶ Num(X_s/κ(s))`, and these restrictions jointly separate the points of `Num(X/S)`.
  Two classes have the same image in `Num(X/S)` exactly when they have the same degree, over
  `κ(s)`, on every integral curve in every fibre `X_s`.
* Both groups are torsion-free: if `aⁿ` is numerically trivial for some `n ≠ 0`, then so is `a`,
  since the integer `n · (a · C)` vanishes only when `(a · C)` does.
* On the projective line every numerically trivial class is trivial, so `Num(ℙ¹_k/k) ≅ ℤ`
  through the degree; for the identity of `S` every class is relatively numerically trivial, so
  `Num(S/S)` is trivial whatever `Pic S` is.

## Main declarations

* `LineBundleClass.numericalIntersectionNumber`: the intersection number `(α · C)` of a numerical
  class `α ∈ Num(X/k)` with an integral closed curve `C ⊆ X`;
* `LineBundleClass.mk_eq_mk_iff_numericallyTrivial` and
  `LineBundleClass.mk_eq_mk_iff_relNumericallyTrivial`: `[a] = [b]` in `Num(X/k)`, respectively
  `Num(X/S)`, iff `a⁻¹ * b` is numerically trivial, respectively `a⁻¹ * b ≡_f 0`;
* `LineBundleClass.mk_eq_mk_iff_forall_intersectionNumber_eq`: two classes have the same image in
  `Num(X/k)` iff they have the same degree on every integral closed curve, and
  `LineBundleClass.eq_of_forall_numericalIntersectionNumber_eq` the corresponding statement on
  `Num(X/k)`;
* `LineBundleClass.numericalFiberRestriction`: the restriction `Num(X/S) →* Num(X_s/κ(s))` to the
  fibre over `s`, with `LineBundleClass.numericalFiberRestriction_injective` saying that the
  restrictions to all fibres jointly determine a relative numerical class;
* `LineBundleClass.mk_eq_mk_iff_forall_fiber_intersectionNumber_eq`: two classes have the same
  image in `Num(X/S)` iff they have the same degree on every integral curve in every fibre;
* the `HasUniqueRoots` instances on `Num(X/k)` and `Num(X/S)`: both groups are torsion-free;
* `projectiveLine.numericalClassDegreeEquiv`: `Num(ℙ¹_k/k) ≃+ ℤ` through the degree;
* the `Subsingleton` instance on `Num(S/S)` for the identity of `S`.

## References

* S. L. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry*, Mathematical Surveys
  and Monographs 123, AMS, 2005, Definition 6.1 and §6.
* B. Bhatt et al., *Globally +-regular varieties and the minimal model program for threefolds in
  mixed characteristic*, Publ. Math. IHÉS 138 (2023), Remark 2.22: the relative numerical group
  `Num(X/S)`.
* C. Hacon and J. Witaszek, *On the relative minimal model program for fourfolds in positive and
  mixed characteristic*, Forum Math. Pi 11 (2023), §1: `N¹(X) = Pic(X) ⊗ ℚ / ≡`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

namespace LineBundleClass

section Absolute

variable (k : Type u) [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (.of k)) [IsProper x]
  {C : Scheme.{u}} [IsIntegral C] [C.Over (Spec (.of k))] (i : C ⟶ X) [IsClosedImmersion i]

/-- Two classes on a proper `k`-scheme have the same image in `Num(X/k)` exactly when they have
the same degree on every integral closed curve over `k`. -/
theorem mk_eq_mk_iff_forall_intersectionNumber_eq (a b : LineBundleClass X) :
    (a : LineBundleClass X ⧸ numericallyTrivialClasses k x) = b ↔
      ∀ (C : Scheme.{u}) [IsIntegral C] [C.Over (Spec (.of k))] (i : C ⟶ X)
        [IsClosedImmersion i], C ↘ Spec (.of k) = i ≫ x → topologicalKrullDim C = 1 →
          intersectionNumber k i a = intersectionNumber k i b := by
  rw [QuotientGroup.eq, mem_numericallyTrivialClasses, numericallyTrivial_iff]
  refine forall_congr' fun C ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦ forall_congr' fun i ↦
    forall_congr' fun _ ↦ forall_congr' fun hi ↦ forall_congr' fun hC ↦ ?_
  rw [intersectionNumber_mul_of_isClosedImmersion k i hi hC,
    intersectionNumber_inv_of_isClosedImmersion k i hi hC, neg_add_eq_zero]

/-- Two classes on a proper `k`-scheme have the same image in `Num(X/k)` exactly when
`a⁻¹ * b` is numerically trivial. -/
theorem mk_eq_mk_iff_numericallyTrivial (a b : LineBundleClass X) :
    (a : LineBundleClass X ⧸ numericallyTrivialClasses k x) = b ↔
      NumericallyTrivial k x (a⁻¹ * b) := by
  rw [QuotientGroup.eq, mem_numericallyTrivialClasses]

/-- A class on a proper `k`-scheme is numerically trivial exactly when its image in `Num(X/k)`
is trivial. -/
theorem mk_eq_one_iff_numericallyTrivial (a : LineBundleClass X) :
    (a : LineBundleClass X ⧸ numericallyTrivialClasses k x) = 1 ↔ NumericallyTrivial k x a := by
  rw [QuotientGroup.eq_one_iff, mem_numericallyTrivialClasses]

variable {x i} in
/-- The **intersection number** `(α · C)` of a numerical class `α ∈ Num(X/k)` with an integral
closed curve `C ⊆ X` over `k`: the degree on `C` of any line-bundle class representing `α`. It is
well defined because numerically trivial classes have degree zero on `C`. -/
def numericalIntersectionNumber (hi : C ↘ Spec (.of k) = i ≫ x) (hC : topologicalKrullDim C = 1)
    (α : LineBundleClass X ⧸ numericallyTrivialClasses k x) : ℤ :=
  Quotient.liftOn' α (intersectionNumber k i) fun a b h ↦
    (mk_eq_mk_iff_forall_intersectionNumber_eq k x a b).mp (Quotient.sound' h) C i hi hC

variable {x i} (hi : C ↘ Spec (.of k) = i ≫ x) (hC : topologicalKrullDim C = 1)

/-- The intersection number of the numerical class of `a` is that of `a`. -/
@[simp]
theorem numericalIntersectionNumber_mk (a : LineBundleClass X) :
    numericalIntersectionNumber k hi hC (a : LineBundleClass X ⧸ numericallyTrivialClasses k x) =
      intersectionNumber k i a :=
  (rfl)

/-- The intersection number with an integral closed curve is additive on `Num(X/k)`. -/
@[simp]
theorem numericalIntersectionNumber_mul (α β : LineBundleClass X ⧸ numericallyTrivialClasses k x) :
    numericalIntersectionNumber k hi hC (α * β) =
      numericalIntersectionNumber k hi hC α + numericalIntersectionNumber k hi hC β := by
  induction α using QuotientGroup.induction_on
  induction β using QuotientGroup.induction_on
  rw [← QuotientGroup.mk_mul]
  simp only [numericalIntersectionNumber_mk]
  exact intersectionNumber_mul_of_isClosedImmersion k i hi hC _ _

/-- The trivial numerical class has intersection number zero with every integral closed curve. -/
@[simp]
theorem numericalIntersectionNumber_one :
    numericalIntersectionNumber k hi hC (1 : LineBundleClass X ⧸ numericallyTrivialClasses k x) =
      0 := by
  rw [← QuotientGroup.mk_one, numericalIntersectionNumber_mk, intersectionNumber_one]

/-- The intersection number with an integral closed curve, as a homomorphism
`Num(X/k) →+ ℤ` on the additively written numerical group. -/
def numericalIntersectionNumberHom :
    Additive (LineBundleClass X ⧸ numericallyTrivialClasses k x) →+ ℤ where
  toFun α := numericalIntersectionNumber k hi hC α.toMul
  map_zero' := numericalIntersectionNumber_one k hi hC
  map_add' α β := numericalIntersectionNumber_mul k hi hC α.toMul β.toMul

/-- The intersection-number homomorphism on `Num(X/k)` evaluates to the intersection number. -/
@[simp]
theorem numericalIntersectionNumberHom_apply
    (α : Additive (LineBundleClass X ⧸ numericallyTrivialClasses k x)) :
    numericalIntersectionNumberHom k hi hC α = numericalIntersectionNumber k hi hC α.toMul :=
  (rfl)

/-- The inverse numerical class has the opposite intersection number. -/
@[simp]
theorem numericalIntersectionNumber_inv (α : LineBundleClass X ⧸ numericallyTrivialClasses k x) :
    numericalIntersectionNumber k hi hC α⁻¹ = -numericalIntersectionNumber k hi hC α :=
  (numericalIntersectionNumberHom k hi hC).map_neg (Additive.ofMul α)

/-- The intersection number of an integer power of a numerical class is the corresponding
multiple. -/
@[simp]
theorem numericalIntersectionNumber_zpow
    (α : LineBundleClass X ⧸ numericallyTrivialClasses k x) (n : ℤ) :
    numericalIntersectionNumber k hi hC (α ^ n) = n * numericalIntersectionNumber k hi hC α :=
  (numericalIntersectionNumberHom k hi hC).map_zsmul n (Additive.ofMul α)

/-- The intersection number of a power of a numerical class is the corresponding multiple. -/
@[simp]
theorem numericalIntersectionNumber_pow
    (α : LineBundleClass X ⧸ numericallyTrivialClasses k x) (n : ℕ) :
    numericalIntersectionNumber k hi hC (α ^ n) = n * numericalIntersectionNumber k hi hC α :=
  (numericalIntersectionNumberHom k hi hC).map_nsmul n (Additive.ofMul α)

variable (x) in
/-- **Numerical classes are determined by their degrees.** Two elements of `Num(X/k)` with the
same intersection number with every integral closed curve over `k` are equal. -/
theorem eq_of_forall_numericalIntersectionNumber_eq
    {α β : LineBundleClass X ⧸ numericallyTrivialClasses k x}
    (h : ∀ (C : Scheme.{u}) [IsIntegral C] [C.Over (Spec (.of k))] (i : C ⟶ X)
      [IsClosedImmersion i] (hi : C ↘ Spec (.of k) = i ≫ x) (hC : topologicalKrullDim C = 1),
        numericalIntersectionNumber k hi hC α = numericalIntersectionNumber k hi hC β) :
    α = β := by
  induction α using QuotientGroup.induction_on
  induction β using QuotientGroup.induction_on
  exact (mk_eq_mk_iff_forall_intersectionNumber_eq k x _ _).mpr fun C _ _ i _ hi hC ↦ h C i hi hC

variable (x) in
/-- **`Num(X/k)` is torsion-free.** If `aⁿ` is numerically trivial for some `n ≠ 0`, then so is
`a`, since `(aⁿ · C) = n · (a · C)` on every integral closed curve `C`. -/
instance : HasUniqueRoots (LineBundleClass X ⧸ numericallyTrivialClasses k x) where
  pow_left_injective n hn α β h :=
    eq_of_forall_numericalIntersectionNumber_eq k x fun C _ _ i _ hi hC ↦ by
      have h' := congrArg (numericalIntersectionNumber k hi hC) h
      simp only [numericalIntersectionNumber_pow] at h'
      exact mul_left_cancel₀ (by exact_mod_cast hn) h'

end Absolute

section Relative

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]

/-- Two classes have the same image in `Num(X/S)` exactly when `a⁻¹ * b` is relatively
numerically trivial, `a⁻¹ * b ≡_f 0`. -/
theorem mk_eq_mk_iff_relNumericallyTrivial (a b : LineBundleClass X) :
    (a : LineBundleClass X ⧸ relNumericallyTrivialClasses f) = b ↔
      RelNumericallyTrivial f (a⁻¹ * b) := by
  rw [QuotientGroup.eq, mem_relNumericallyTrivialClasses]

/-- A class is relatively numerically trivial exactly when its image in `Num(X/S)` is trivial. -/
theorem mk_eq_one_iff_relNumericallyTrivial (a : LineBundleClass X) :
    (a : LineBundleClass X ⧸ relNumericallyTrivialClasses f) = 1 ↔ RelNumericallyTrivial f a := by
  rw [QuotientGroup.eq_one_iff, mem_relNumericallyTrivialClasses]

/-- Restriction of numerical classes to the scheme-theoretic fibre `X_s` over a point `s` of
`S`, a homomorphism `Num(X/S) →* Num(X_s/κ(s))`. It is well defined because a relatively
numerically trivial class restricts to a numerically trivial class on every fibre. -/
def numericalFiberRestriction (s : S) :
    LineBundleClass X ⧸ relNumericallyTrivialClasses f →*
      LineBundleClass (f.fiber s) ⧸
        numericallyTrivialClasses (S.residueField s) (f.fiberToSpecResidueField s) :=
  QuotientGroup.map _ _ (pullbackHom (f.fiberι s)) fun a ha ↦ by
    rw [Subgroup.mem_comap, pullbackHom_apply, mem_numericallyTrivialClasses]
    exact (relNumericallyTrivial_iff f a).mp (mem_relNumericallyTrivialClasses.mp ha) s

/-- The restriction of the numerical class of `a` to the fibre `X_s` is the numerical class of
the pullback of `a` to `X_s`. -/
@[simp]
theorem numericalFiberRestriction_mk (s : S) (a : LineBundleClass X) :
    numericalFiberRestriction f s (a : LineBundleClass X ⧸ relNumericallyTrivialClasses f) =
      (pullback (f.fiberι s) a : LineBundleClass (f.fiber s) ⧸
        numericallyTrivialClasses (S.residueField s) (f.fiberToSpecResidueField s)) := by
  rw [numericalFiberRestriction, QuotientGroup.map_mk, pullbackHom_apply]

/-- **Relative numerical classes are determined on the fibres.** The restrictions to all the
fibres `X_s` of `f` jointly embed `Num(X/S)` into `∏ₛ Num(X_s/κ(s))`. -/
theorem numericalFiberRestriction_injective :
    Function.Injective (MonoidHom.pi fun s ↦ numericalFiberRestriction f s) := by
  rw [injective_iff_map_eq_one]
  intro α hα
  induction α using QuotientGroup.induction_on with | H a => ?_
  rw [mk_eq_one_iff_relNumericallyTrivial, relNumericallyTrivial_iff]
  intro s
  rw [← mk_eq_one_iff_numericallyTrivial]
  simpa only [MonoidHom.pi_apply, numericalFiberRestriction_mk, Pi.one_apply] using
    congrFun hα s

/-- Two classes have the same image in `Num(X/S)` exactly when, for every point `s` of `S`, they
have the same degree over `κ(s)` on every integral curve in the fibre `X_s`. -/
theorem mk_eq_mk_iff_forall_fiber_intersectionNumber_eq (a b : LineBundleClass X) :
    (a : LineBundleClass X ⧸ relNumericallyTrivialClasses f) = b ↔
      ∀ (s : S) (C : Scheme.{u}) [IsIntegral C] [C.Over (Spec (.of (S.residueField s)))]
        (i : C ⟶ f.fiber s) [IsClosedImmersion i],
          C ↘ Spec (.of (S.residueField s)) = i ≫ f.fiberToSpecResidueField s →
            topologicalKrullDim C = 1 →
              intersectionNumber (S.residueField s) i (pullback (f.fiberι s) a) =
                intersectionNumber (S.residueField s) i (pullback (f.fiberι s) b) := by
  refine ⟨fun h s ↦ ?_, fun h ↦ (numericalFiberRestriction_injective f) (funext fun s ↦ ?_)⟩
  · rw [← mk_eq_mk_iff_forall_intersectionNumber_eq, ← numericalFiberRestriction_mk,
      ← numericalFiberRestriction_mk, h]
  · simpa only [MonoidHom.pi_apply, numericalFiberRestriction_mk] using
      (mk_eq_mk_iff_forall_intersectionNumber_eq _ _ _ _).mpr (h s)

/-- **`Num(X/S)` is torsion-free.** It embeds into the product of the torsion-free groups
`Num(X_s/κ(s))` over the points `s` of `S`. -/
instance : HasUniqueRoots (LineBundleClass X ⧸ relNumericallyTrivialClasses f) where
  pow_left_injective n hn α β h := numericalFiberRestriction_injective f <| funext fun s ↦
    pow_left_injective hn <| by
      simpa only [MonoidHom.pi_apply, map_pow] using congrFun (congrArg (MonoidHom.pi fun s ↦
        numericalFiberRestriction f s) h) s

variable (S) in
/-- For the identity of `S` the relative numerical group `Num(S/S)` is trivial: every class is
relatively numerically trivial. -/
instance : Subsingleton (LineBundleClass S ⧸ relNumericallyTrivialClasses (𝟙 S)) := by
  rw [relNumericallyTrivialClasses_id]
  exact QuotientGroup.subsingleton_quotient_top

end Relative

end LineBundleClass

namespace projectiveLine

variable (k : Type u) [Field k]

/-- **The numerical group of the projective line.** The degree identifies `Num(ℙ¹_k/k)` with
`ℤ`. -/
def numericalClassDegreeEquiv :
    Additive (LineBundleClass (projectiveLine k) ⧸
      LineBundleClass.numericallyTrivialClasses k (projectiveLine k ↘ Spec (.of k))) ≃+ ℤ :=
  (((QuotientGroup.quotientMulEquivOfEq (numericallyTrivialClasses_eq_bot k)).trans
    QuotientGroup.quotientBot).toAdditive).trans (picardDegreeEquiv k)

/-- The identification `Num(ℙ¹_k/k) ≃+ ℤ` evaluates to the degree of a representative. -/
@[simp]
theorem numericalClassDegreeEquiv_mk (a : LineBundleClass (projectiveLine k)) :
    numericalClassDegreeEquiv k (Additive.ofMul (a : LineBundleClass (projectiveLine k) ⧸
      LineBundleClass.numericallyTrivialClasses k (projectiveLine k ↘ Spec (.of k)))) =
        LineBundleClass.eulerDegree k a := by
  simp only [numericalClassDegreeEquiv, AddEquiv.trans_apply, MulEquiv.toAdditive_apply_apply,
    toMul_ofMul, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    ← QuotientGroup.quotientBot_symm_apply, MulEquiv.apply_symm_apply, picardDegreeEquiv_apply]

end projectiveLine

end

end TauCeti.AlgebraicGeometry
