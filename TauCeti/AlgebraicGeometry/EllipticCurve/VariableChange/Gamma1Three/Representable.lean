/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.AlgebraicGeometry.EllipticCurve.Gamma1ThreeNormalForm
public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Basic

/-!
# Coordinate algebras of strict `Γ₁(3)` Weierstrass variable changes

Over any commutative ring `B` and pair of coefficients `a₁, a₃ : B`, a strict change of variables
`C = (1, r, s, t)` carries `gamma1ThreeNormalForm a₁ a₃` (`Y² + a₁XY + a₃Y = X³`) to another curve
in `Γ₁(3)` normal form (`WeierstrassCurve.IsStrictGamma1ThreeChange`) if and only if the quadratic,
linear and constant coefficients of `C • gamma1ThreeNormalForm a₁ a₃` vanish:

* `3r - s² - a₁s = 0`,
* `3r² - a₁rs - a₃s - a₁t - 2st = 0`,
* `r³ - a₁rt - a₃t - t² = 0`.

This file defines the quotient `ArrowRingOf B a₁ a₃` of `B[r, s, t]` by these three relations and
proves its universal property (`ArrowRingOf.lift`), functoriality (`ArrowRingOf.mapOfEq`,
`ArrowRingOf.map`), pushout property (`ArrowRingOf.pushoutLiftOfEq`, `ArrowRingOf.isPushout`), and
groupoid torsor shearing isomorphism (`ArrowRingOf.shearEquiv`). No invertibility assumption on `3`
is imposed here.

Parallel to `TauCeti/AlgebraicGeometry/EllipticCurve/VariableChange/Representable.lean`, this
parameterized construction supplies in one uniform API the arrow ring `Γ'` of the `Γ₁(3)` Hopf
algebroid, its iterated fibered tensor powers `Γ' ⊗_{A'} Γ'` and `Γ' ⊗_{A'} Γ' ⊗_{A'} Γ'`, and the
torsor comparison used to show that the algebraic transfer lands in Hopf-algebroid invariants.

## Main definitions

* `WeierstrassCurve.IsStrictGamma1ThreeChange a₁ a₃ C`: `C` has `u = 1` and carries
  `gamma1ThreeNormalForm a₁ a₃` to another `Γ₁(3)` normal form.
* `TauCeti.Gamma1ThreeHopfAlgebroid.ArrowRingOf B a₁ a₃`: the quotient of `B[r, s, t]` classifying
  strict `Γ₁(3)` arrows out of `gamma1ThreeNormalForm a₁ a₃`.
* `TauCeti.Gamma1ThreeHopfAlgebroid.ArrowRingOf.lift`: the universal property of
  `ArrowRingOf B a₁ a₃`.
* `TauCeti.Gamma1ThreeHopfAlgebroid.ArrowRingOf.pushoutLiftOfEq`, `ArrowRingOf.pushoutLift`: the
  universal property of `ArrowRingOf B' a₁' a₃'` as a pushout over `B`.
* `TauCeti.Gamma1ThreeHopfAlgebroid.ArrowRingOf.shearEquiv`: the `B`-algebra isomorphism induced by
  precomposing with a strict `Γ₁(3)` arrow over `B`.

## References

* T. Bauer, *Computation of the homotopy of the spectrum tmf*, in *Groups, homotopy and
  configuration spaces*, Geom. Topol. Monogr. 13 (2008), §7.
* K. Carrick, J. Davies and S. van Nigtevecht, *Topological modular forms with level structure:
  deformations, transfers, and differentials*, §4.2.
-/

public section

noncomputable section

universe u

namespace WeierstrassCurve

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A change of variables `C` is a **strict `Γ₁(3)` arrow** out of `gamma1ThreeNormalForm a₁ a₃`
when `C.u = 1` and `C • gamma1ThreeNormalForm a₁ a₃` again has `a₂ = a₄ = a₆ = 0`. -/
def IsStrictGamma1ThreeChange (a₁ a₃ : R) (C : VariableChange R) : Prop :=
  C.u = 1 ∧ (C • gamma1ThreeNormalForm a₁ a₃).a₂ = 0 ∧
    (C • gamma1ThreeNormalForm a₁ a₃).a₄ = 0 ∧ (C • gamma1ThreeNormalForm a₁ a₃).a₆ = 0

/-- Explicit unfolding of `IsStrictGamma1ThreeChange`. -/
theorem isStrictGamma1ThreeChange_iff {a₁ a₃ : R} {C : VariableChange R} :
    IsStrictGamma1ThreeChange a₁ a₃ C ↔
      C.u = 1 ∧ (C • gamma1ThreeNormalForm a₁ a₃).a₂ = 0 ∧
        (C • gamma1ThreeNormalForm a₁ a₃).a₄ = 0 ∧ (C • gamma1ThreeNormalForm a₁ a₃).a₆ = 0 :=
  Iff.rfl

/-- Characterization of `IsStrictGamma1ThreeChange a₁ a₃ ⟨1, r, s, t⟩` by the three defining
polynomial equations in `(r, s, t)`. -/
theorem isStrictGamma1ThreeChange_mk_iff {a₁ a₃ r s t : R} :
    IsStrictGamma1ThreeChange a₁ a₃ ⟨1, r, s, t⟩ ↔
      3 * r - s ^ 2 - a₁ * s = 0 ∧
        3 * r ^ 2 - a₁ * r * s - a₃ * s - a₁ * t - 2 * s * t = 0 ∧
        r ^ 3 - a₁ * r * t - a₃ * t - t ^ 2 = 0 := by
  simp [IsStrictGamma1ThreeChange]

namespace IsStrictGamma1ThreeChange

/-- A strict `Γ₁(3)` arrow `C` equals `⟨1, C.r, C.s, C.t⟩`. -/
theorem eq_mk {a₁ a₃ : R} {C : VariableChange R} (h : IsStrictGamma1ThreeChange a₁ a₃ C) :
    C = ⟨1, C.r, C.s, C.t⟩ :=
  VariableChange.ext h.1 rfl rfl rfl

/-- Acting by a strict `Γ₁(3)` arrow produces `gamma1ThreeNormalForm (a₁ + 2s) (a₃ + a₁r + 2t)`. -/
theorem smul_eq {a₁ a₃ : R} {C : VariableChange R} (h : IsStrictGamma1ThreeChange a₁ a₃ C) :
    C • gamma1ThreeNormalForm a₁ a₃ =
      gamma1ThreeNormalForm (a₁ + 2 * C.s) (a₃ + a₁ * C.r + 2 * C.t) := by
  have hW := (eq_gamma1ThreeNormalForm_iff (C • gamma1ThreeNormalForm a₁ a₃)).mpr ⟨h.2.1, h.2.2⟩
  conv_lhs => rw [hW]
  conv_lhs => rw [h.eq_mk]
  simp

/-- The identity change of variables is a strict `Γ₁(3)` arrow. -/
theorem one (a₁ a₃ : R) : IsStrictGamma1ThreeChange a₁ a₃ 1 := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp

/-- Strict `Γ₁(3)` arrows are closed under composition. -/
theorem mul {a₁ a₃ : R} {C₁ C₂ : VariableChange R}
    (h₁ : IsStrictGamma1ThreeChange a₁ a₃ C₁)
    (h₂ : IsStrictGamma1ThreeChange (a₁ + 2 * C₁.s) (a₃ + a₁ * C₁.r + 2 * C₁.t) C₂) :
    IsStrictGamma1ThreeChange a₁ a₃ (C₂ * C₁) := by
  refine ⟨by rw [VariableChange.mul_def, h₂.1, h₁.1, mul_one], ?_⟩
  rw [mul_smul, h₁.smul_eq]
  exact h₂.2

/-- The inverse of a strict `Γ₁(3)` arrow is a strict `Γ₁(3)` arrow from its target back to its
source. -/
theorem inv {a₁ a₃ : R} {C : VariableChange R} (h : IsStrictGamma1ThreeChange a₁ a₃ C) :
    IsStrictGamma1ThreeChange (a₁ + 2 * C.s) (a₃ + a₁ * C.r + 2 * C.t) C⁻¹ := by
  refine ⟨by simp [VariableChange.inv_def, h.1], ?_⟩
  rw [← h.smul_eq, inv_smul_smul]
  exact ⟨gamma1ThreeNormalForm_a₂ a₁ a₃, gamma1ThreeNormalForm_a₄ a₁ a₃,
    gamma1ThreeNormalForm_a₆ a₁ a₃⟩

/-- Strict `Γ₁(3)` arrows are preserved along ring homomorphisms. -/
theorem map {a₁ a₃ : R} {C : VariableChange R} (h : IsStrictGamma1ThreeChange a₁ a₃ C)
    (f : R →+* S) : IsStrictGamma1ThreeChange (f a₁) (f a₃) (C.map f) := by
  refine ⟨by simp [h.1], ?_⟩
  have hsmul : C.map f • gamma1ThreeNormalForm (f a₁) (f a₃) =
      (C • gamma1ThreeNormalForm a₁ a₃).map f := by
    rw [← map_gamma1ThreeNormalForm, map_variableChange]
  rw [hsmul]
  simp [h.2.1, h.2.2.1, h.2.2.2]

end IsStrictGamma1ThreeChange

end WeierstrassCurve

namespace TauCeti.Gamma1ThreeHopfAlgebroid

open MvPolynomial _root_.WeierstrassCurve

variable (B : Type*) [CommRing B] (a₁ a₃ : B)

namespace ArrowRingOf

/-- The universal strict change of variables `⟨1, X 0, X 1, X 2⟩` over `B[r, s, t]`. -/
def polyChange : VariableChange (MvPolynomial (Fin 3) B) :=
  ⟨1, X 0, X 1, X 2⟩

/-- The ideal of `B[r, s, t]` generated by the `a₂`, `a₄` and `a₆` coefficients of
`⟨1, r, s, t⟩ • gamma1ThreeNormalForm a₁ a₃`. -/
def ideal : Ideal (MvPolynomial (Fin 3) B) :=
  Ideal.span
    { (polyChange B • gamma1ThreeNormalForm (C a₁) (C a₃)).a₂,
      (polyChange B • gamma1ThreeNormalForm (C a₁) (C a₃)).a₄,
      (polyChange B • gamma1ThreeNormalForm (C a₁) (C a₃)).a₆ }

end ArrowRingOf

/-- The quotient of `B[r, s, t]` cutting out strict changes of variables `⟨1, r, s, t⟩` that carry
`gamma1ThreeNormalForm a₁ a₃` to another `Γ₁(3)` normal form. -/
abbrev ArrowRingOf : Type _ :=
  MvPolynomial (Fin 3) B ⧸ ArrowRingOf.ideal B a₁ a₃

namespace ArrowRingOf

/-- The translation coordinate `r` in `ArrowRingOf B a₁ a₃`. -/
def r : ArrowRingOf B a₁ a₃ :=
  Ideal.Quotient.mk (ideal B a₁ a₃) (X 0)

/-- The shear coordinate `s` in `ArrowRingOf B a₁ a₃`. -/
def s : ArrowRingOf B a₁ a₃ :=
  Ideal.Quotient.mk (ideal B a₁ a₃) (X 1)

/-- The vertical translation coordinate `t` in `ArrowRingOf B a₁ a₃`. -/
def t : ArrowRingOf B a₁ a₃ :=
  Ideal.Quotient.mk (ideal B a₁ a₃) (X 2)

/-- The universal strict `Γ₁(3)` change of variables `⟨1, r, s, t⟩` over `ArrowRingOf B a₁ a₃`. -/
def universalChange : VariableChange (ArrowRingOf B a₁ a₃) :=
  ⟨1, r B a₁ a₃, s B a₁ a₃, t B a₁ a₃⟩

@[simp]
theorem universalChange_u : (universalChange B a₁ a₃).u = 1 :=
  (rfl)

@[simp]
theorem universalChange_r : (universalChange B a₁ a₃).r = r B a₁ a₃ :=
  (rfl)

@[simp]
theorem universalChange_s : (universalChange B a₁ a₃).s = s B a₁ a₃ :=
  (rfl)

@[simp]
theorem universalChange_t : (universalChange B a₁ a₃).t = t B a₁ a₃ :=
  (rfl)

private theorem polyChange_map_mk :
    (polyChange B).map (Ideal.Quotient.mk (ideal B a₁ a₃)) = universalChange B a₁ a₃ :=
  VariableChange.ext (by simp [polyChange, universalChange]) (rfl) (rfl) (rfl)

/-- The universal change of variables over `ArrowRingOf B a₁ a₃` is a strict `Γ₁(3)` arrow. -/
theorem isStrictGamma1ThreeChange_universalChange :
    IsStrictGamma1ThreeChange (algebraMap B (ArrowRingOf B a₁ a₃) a₁)
      (algebraMap B (ArrowRingOf B a₁ a₃) a₃) (universalChange B a₁ a₃) := by
  have hW : gamma1ThreeNormalForm (algebraMap B (ArrowRingOf B a₁ a₃) a₁)
      (algebraMap B (ArrowRingOf B a₁ a₃) a₃) =
      (gamma1ThreeNormalForm (C a₁) (C a₃)).map (Ideal.Quotient.mk (ideal B a₁ a₃)) := by
    rw [map_gamma1ThreeNormalForm]
    rfl
  have hsmul : universalChange B a₁ a₃ •
      gamma1ThreeNormalForm (algebraMap B (ArrowRingOf B a₁ a₃) a₁)
        (algebraMap B (ArrowRingOf B a₁ a₃) a₃) =
      (polyChange B • gamma1ThreeNormalForm (C a₁) (C a₃)).map
        (Ideal.Quotient.mk (ideal B a₁ a₃)) := by
    rw [hW, ← polyChange_map_mk, map_variableChange]
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> rw [hsmul]
  · exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  · exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  · exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

/-- Relation `3r - s² - a₁s = 0` in `ArrowRingOf B a₁ a₃`. -/
theorem three_mul_r_sub_s_sq_sub_a₁_mul_s :
    3 * r B a₁ a₃ - s B a₁ a₃ ^ 2 - algebraMap B (ArrowRingOf B a₁ a₃) a₁ * s B a₁ a₃ = 0 := by
  simpa [universalChange] using (isStrictGamma1ThreeChange_universalChange B a₁ a₃).2.1

/-- Relation `3r² - a₁rs - a₃s - a₁t - 2st = 0` in `ArrowRingOf B a₁ a₃`. -/
theorem relation_a₄ :
    3 * r B a₁ a₃ ^ 2 -
      algebraMap B (ArrowRingOf B a₁ a₃) a₁ * r B a₁ a₃ * s B a₁ a₃ -
      algebraMap B (ArrowRingOf B a₁ a₃) a₃ * s B a₁ a₃ -
      algebraMap B (ArrowRingOf B a₁ a₃) a₁ * t B a₁ a₃ -
      2 * s B a₁ a₃ * t B a₁ a₃ = 0 := by
  simpa [universalChange] using (isStrictGamma1ThreeChange_universalChange B a₁ a₃).2.2.1

/-- Relation `r³ - a₁rt - a₃t - t² = 0` in `ArrowRingOf B a₁ a₃`. -/
theorem relation_a₆ :
    r B a₁ a₃ ^ 3 -
      algebraMap B (ArrowRingOf B a₁ a₃) a₁ * r B a₁ a₃ * t B a₁ a₃ -
      algebraMap B (ArrowRingOf B a₁ a₃) a₃ * t B a₁ a₃ -
      t B a₁ a₃ ^ 2 = 0 := by
  simpa [universalChange] using (isStrictGamma1ThreeChange_universalChange B a₁ a₃).2.2.2

variable {B a₁ a₃} {B' S : Type*} [CommRing B'] [CommRing S]

private def evalPolyHom (f : B →+* S) (D : VariableChange S) : MvPolynomial (Fin 3) B →+* S :=
  eval₂Hom f ![D.r, D.s, D.t]

private theorem polyChange_map_evalPolyHom (f : B →+* S) {D : VariableChange S} (hu : D.u = 1) :
    (polyChange B).map (evalPolyHom f D) = D := by
  ext
  · simp [polyChange, hu]
  · simp [polyChange, evalPolyHom]
  · simp [polyChange, evalPolyHom]
  · simp [polyChange, evalPolyHom]

private theorem ideal_le_ker_evalPolyHom {f : B →+* S} {D : VariableChange S}
    (hD : IsStrictGamma1ThreeChange (f a₁) (f a₃) D) :
    ideal B a₁ a₃ ≤ RingHom.ker (evalPolyHom f D) := by
  rw [ideal, Ideal.span_le]
  have hsmul : (polyChange B • gamma1ThreeNormalForm (C a₁) (C a₃)).map (evalPolyHom f D) =
      D • gamma1ThreeNormalForm (f a₁) (f a₃) := by
    rw [← map_variableChange, polyChange_map_evalPolyHom f hD.1, map_gamma1ThreeNormalForm]
    simp [evalPolyHom]
  rintro _ (rfl | rfl | rfl)
  · rw [SetLike.mem_coe, RingHom.mem_ker, ← map_a₂, hsmul, hD.2.1]
  · rw [SetLike.mem_coe, RingHom.mem_ker, ← map_a₄, hsmul, hD.2.2.1]
  · rw [SetLike.mem_coe, RingHom.mem_ker, ← map_a₆, hsmul, hD.2.2.2]

/-- **Universal property of `ArrowRingOf B a₁ a₃`**: ring homomorphisms out of
`ArrowRingOf B a₁ a₃` classify pairs `(f, D)` of a ring homomorphism `f : B →+* S` and a strict
`Γ₁(3)` arrow `D` out of `gamma1ThreeNormalForm (f a₁) (f a₃)`. -/
def lift :
    {p : (B →+* S) × VariableChange S // IsStrictGamma1ThreeChange (p.1 a₁) (p.1 a₃) p.2} ≃
      (ArrowRingOf B a₁ a₃ →+* S) where
  toFun p := Ideal.Quotient.lift (ideal B a₁ a₃) (evalPolyHom p.1.1 p.1.2)
    (ideal_le_ker_evalPolyHom p.2)
  invFun k := ⟨(k.comp (algebraMap B _), (universalChange B a₁ a₃).map k),
    (isStrictGamma1ThreeChange_universalChange B a₁ a₃).map k⟩
  left_inv p := by
    refine Subtype.ext (Prod.ext (RingHom.ext fun b ↦ ?_) ?_)
    · simp [IsScalarTower.algebraMap_apply B (MvPolynomial (Fin 3) B) (ArrowRingOf B a₁ a₃),
        evalPolyHom]
    · ext
      · simp [universalChange, p.2.1]
      · simp [universalChange, r, evalPolyHom]
      · simp [universalChange, s, evalPolyHom]
      · simp [universalChange, t, evalPolyHom]
  right_inv k := by
    refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun b ↦ ?_) fun i ↦ ?_)
    · simp [evalPolyHom,
        IsScalarTower.algebraMap_apply B (MvPolynomial (Fin 3) B) (ArrowRingOf B a₁ a₃)]
    · fin_cases i <;> simp [evalPolyHom, universalChange, r, s, t]

@[simp]
theorem lift_comp_algebraMap
    (p : {p : (B →+* S) × VariableChange S // IsStrictGamma1ThreeChange (p.1 a₁) (p.1 a₃) p.2}) :
    (lift p).comp (algebraMap B _) = p.1.1 :=
  congrArg (fun q ↦ q.1.1) (lift.left_inv p)

@[simp]
theorem lift_algebraMap
    (p : {p : (B →+* S) × VariableChange S // IsStrictGamma1ThreeChange (p.1 a₁) (p.1 a₃) p.2})
    (b : B) :
    lift p (algebraMap B _ b) = p.1.1 b :=
  RingHom.congr_fun (lift_comp_algebraMap p) b

@[simp]
theorem map_lift
    (p : {p : (B →+* S) × VariableChange S // IsStrictGamma1ThreeChange (p.1 a₁) (p.1 a₃) p.2}) :
    (universalChange B a₁ a₃).map (lift p) = p.1.2 :=
  congrArg (fun q ↦ q.1.2) (lift.left_inv p)

@[simp]
theorem lift_r
    (p : {p : (B →+* S) × VariableChange S // IsStrictGamma1ThreeChange (p.1 a₁) (p.1 a₃) p.2}) :
    lift p (r B a₁ a₃) = p.1.2.r :=
  congrArg VariableChange.r (map_lift p)

@[simp]
theorem lift_s
    (p : {p : (B →+* S) × VariableChange S // IsStrictGamma1ThreeChange (p.1 a₁) (p.1 a₃) p.2}) :
    lift p (s B a₁ a₃) = p.1.2.s :=
  congrArg VariableChange.s (map_lift p)

@[simp]
theorem lift_t
    (p : {p : (B →+* S) × VariableChange S // IsStrictGamma1ThreeChange (p.1 a₁) (p.1 a₃) p.2}) :
    lift p (t B a₁ a₃) = p.1.2.t :=
  congrArg VariableChange.t (map_lift p)

@[simp]
theorem lift_symm_apply (k : ArrowRingOf B a₁ a₃ →+* S) :
    (lift.symm k).1 = (k.comp (algebraMap B _), (universalChange B a₁ a₃).map k) :=
  (rfl)

/-- A ring homomorphism out of `ArrowRingOf B a₁ a₃` is determined by its restriction to `B` and
its image of `universalChange B a₁ a₃`. -/
theorem ringHom_ext {k k' : ArrowRingOf B a₁ a₃ →+* S}
    (h₁ : k.comp (algebraMap B _) = k'.comp (algebraMap B _))
    (h₂ : (universalChange B a₁ a₃).map k = (universalChange B a₁ a₃).map k') : k = k' :=
  lift.symm.injective (Subtype.ext (Prod.ext h₁ h₂))

/-- Coefficient extension `ArrowRingOf B a₁ a₃ →+* ArrowRingOf B' a₁' a₃'` along `f : B →+* B'`
when `f a₁ = a₁'` and `f a₃ = a₃'`. -/
def mapOfEq {a₁' a₃' : B'} (f : B →+* B') (ha₁ : f a₁ = a₁') (ha₃ : f a₃ = a₃') :
    ArrowRingOf B a₁ a₃ →+* ArrowRingOf B' a₁' a₃' :=
  lift ⟨((algebraMap B' _).comp f, universalChange B' a₁' a₃'), by
    simpa [ha₁, ha₃] using isStrictGamma1ThreeChange_universalChange B' a₁' a₃'⟩

@[simp]
theorem mapOfEq_comp_algebraMap {a₁' a₃' : B'} (f : B →+* B') (ha₁ : f a₁ = a₁')
    (ha₃ : f a₃ = a₃') :
    (mapOfEq f ha₁ ha₃).comp (algebraMap B _) = (algebraMap B' _).comp f :=
  lift_comp_algebraMap _

@[simp]
theorem mapOfEq_algebraMap {a₁' a₃' : B'} (f : B →+* B') (ha₁ : f a₁ = a₁') (ha₃ : f a₃ = a₃')
    (b : B) :
    mapOfEq f ha₁ ha₃ (algebraMap B _ b) = algebraMap B' _ (f b) :=
  lift_algebraMap _ b

@[simp]
theorem universalChange_map_mapOfEq {a₁' a₃' : B'} (f : B →+* B') (ha₁ : f a₁ = a₁')
    (ha₃ : f a₃ = a₃') :
    (universalChange B a₁ a₃).map (mapOfEq f ha₁ ha₃) = universalChange B' a₁' a₃' :=
  map_lift _

@[simp]
theorem mapOfEq_r {a₁' a₃' : B'} (f : B →+* B') (ha₁ : f a₁ = a₁') (ha₃ : f a₃ = a₃') :
    mapOfEq f ha₁ ha₃ (r B a₁ a₃) = r B' a₁' a₃' :=
  lift_r _

@[simp]
theorem mapOfEq_s {a₁' a₃' : B'} (f : B →+* B') (ha₁ : f a₁ = a₁') (ha₃ : f a₃ = a₃') :
    mapOfEq f ha₁ ha₃ (s B a₁ a₃) = s B' a₁' a₃' :=
  lift_s _

@[simp]
theorem mapOfEq_t {a₁' a₃' : B'} (f : B →+* B') (ha₁ : f a₁ = a₁') (ha₃ : f a₃ = a₃') :
    mapOfEq f ha₁ ha₃ (t B a₁ a₃) = t B' a₁' a₃' :=
  lift_t _

/-- Coefficient extension `ArrowRingOf B a₁ a₃ →+* ArrowRingOf B' (f a₁) (f a₃)` along
`f : B →+* B'`. -/
abbrev map (f : B →+* B') : ArrowRingOf B a₁ a₃ →+* ArrowRingOf B' (f a₁) (f a₃) :=
  mapOfEq f rfl rfl

@[simp]
theorem map_id : map (RingHom.id B) (a₁ := a₁) (a₃ := a₃) = RingHom.id (ArrowRingOf B a₁ a₃) :=
  ringHom_ext (by simp) (by simp)

@[simp]
theorem map_comp {B'' : Type*} [CommRing B''] (g : B' →+* B'') (f : B →+* B') :
    map (g.comp f) (a₁ := a₁) (a₃ := a₃) = (map g).comp (map f) :=
  ringHom_ext (RingHom.ext fun b ↦ by simp) (by simp [← VariableChange.map_map])

/-- **Universal property of `ArrowRingOf B' a₁' a₃'` as the pushout `B' ⊗_B ArrowRingOf B a₁ a₃`**
along `f : B →+* B'` (with `f a₁ = a₁'`, `f a₃ = a₃'`) and `algebraMap`. -/
def pushoutLiftOfEq {a₁' a₃' : B'} (f : B →+* B') (ha₁ : f a₁ = a₁') (ha₃ : f a₃ = a₃') :
    {p : (B' →+* S) × (ArrowRingOf B a₁ a₃ →+* S) //
      p.1.comp f = p.2.comp (algebraMap B _)} ≃
      (ArrowRingOf B' a₁' a₃' →+* S) where
  toFun p := lift ⟨(p.1.1, (universalChange B a₁ a₃).map p.1.2), by
    have h₁ : p.1.1 a₁' = p.1.2 (algebraMap B _ a₁) := by
      rw [← ha₁]
      exact RingHom.congr_fun p.2 a₁
    have h₃ : p.1.1 a₃' = p.1.2 (algebraMap B _ a₃) := by
      rw [← ha₃]
      exact RingHom.congr_fun p.2 a₃
    rw [h₁, h₃]
    exact (isStrictGamma1ThreeChange_universalChange B a₁ a₃).map p.1.2⟩
  invFun k := ⟨(k.comp (algebraMap B' _), k.comp (mapOfEq f ha₁ ha₃)), by
    rw [RingHom.comp_assoc, RingHom.comp_assoc, mapOfEq_comp_algebraMap]⟩
  left_inv p := by
    refine Subtype.ext (Prod.ext (lift_comp_algebraMap _) (ringHom_ext ?_ ?_))
    · rw [RingHom.comp_assoc, mapOfEq_comp_algebraMap, ← RingHom.comp_assoc, lift_comp_algebraMap,
        p.2]
    · rw [← VariableChange.map_map, universalChange_map_mapOfEq, map_lift]
  right_inv k := ringHom_ext (lift_comp_algebraMap _) (by
    rw [map_lift]
    dsimp only
    rw [← VariableChange.map_map, universalChange_map_mapOfEq])

/-- Pushout universal property for `ArrowRingOf B' (f a₁) (f a₃)`. -/
abbrev pushoutLift (f : B →+* B') :=
  pushoutLiftOfEq (S := S) (a₁ := a₁) (a₃ := a₃) f rfl rfl

@[simp]
theorem pushoutLiftOfEq_symm_apply_fst {a₁' a₃' : B'} (f : B →+* B') (ha₁ : f a₁ = a₁')
    (ha₃ : f a₃ = a₃') (k : ArrowRingOf B' a₁' a₃' →+* S) :
    ((pushoutLiftOfEq f ha₁ ha₃).symm k).1.1 = k.comp (algebraMap B' _) :=
  (rfl)

@[simp]
theorem pushoutLiftOfEq_symm_apply_snd {a₁' a₃' : B'} (f : B →+* B') (ha₁ : f a₁ = a₁')
    (ha₃ : f a₃ = a₃') (k : ArrowRingOf B' a₁' a₃' →+* S) :
    ((pushoutLiftOfEq f ha₁ ha₃).symm k).1.2 = k.comp (mapOfEq f ha₁ ha₃) :=
  (rfl)

section PushoutLemmas

variable {a₁' a₃' : B'} (f : B →+* B') (ha₁ : f a₁ = a₁') (ha₃ : f a₃ = a₃')
  (p : {p : (B' →+* S) × (ArrowRingOf B a₁ a₃ →+* S) //
    p.1.comp f = p.2.comp (algebraMap B _)})

@[simp]
theorem pushoutLiftOfEq_comp_algebraMap :
    (pushoutLiftOfEq f ha₁ ha₃ p).comp (algebraMap B' _) = p.1.1 :=
  congrArg (fun q ↦ q.1.1) ((pushoutLiftOfEq f ha₁ ha₃).left_inv p)

@[simp]
theorem pushoutLiftOfEq_comp_mapOfEq :
    (pushoutLiftOfEq f ha₁ ha₃ p).comp (mapOfEq f ha₁ ha₃) = p.1.2 :=
  congrArg (fun q ↦ q.1.2) ((pushoutLiftOfEq f ha₁ ha₃).left_inv p)

@[simp]
theorem pushoutLiftOfEq_algebraMap (b : B') :
    pushoutLiftOfEq f ha₁ ha₃ p (algebraMap B' _ b) = p.1.1 b :=
  RingHom.congr_fun (pushoutLiftOfEq_comp_algebraMap f ha₁ ha₃ p) b

@[simp]
theorem pushoutLiftOfEq_mapOfEq (x : ArrowRingOf B a₁ a₃) :
    pushoutLiftOfEq f ha₁ ha₃ p (mapOfEq f ha₁ ha₃ x) = p.1.2 x :=
  RingHom.congr_fun (pushoutLiftOfEq_comp_mapOfEq f ha₁ ha₃ p) x

@[simp]
theorem universalChange_map_pushoutLiftOfEq :
    (universalChange B' a₁' a₃').map (pushoutLiftOfEq f ha₁ ha₃ p) =
      (universalChange B a₁ a₃).map p.1.2 :=
  map_lift _

end PushoutLemmas

open CategoryTheory CategoryTheory.Limits in
/-- The coefficient-extension square for `ArrowRingOf` is a pushout in `CommRingCat`. -/
theorem isPushout {B B' : Type u} [CommRing B] [CommRing B'] {a₁ a₃ : B} (f : B →+* B') :
    CategoryTheory.IsPushout (CommRingCat.ofHom f)
      (CommRingCat.ofHom (algebraMap B (ArrowRingOf B a₁ a₃)))
      (CommRingCat.ofHom (algebraMap B' (ArrowRingOf B' (f a₁) (f a₃))))
      (CommRingCat.ofHom (map f)) := by
  have comm : CommRingCat.ofHom f ≫
      CommRingCat.ofHom (algebraMap B' (ArrowRingOf B' (f a₁) (f a₃))) =
      CommRingCat.ofHom (algebraMap B (ArrowRingOf B a₁ a₃)) ≫ CommRingCat.ofHom (map f) :=
    congrArg CommRingCat.ofHom (mapOfEq_comp_algebraMap (a₁ := a₁) (a₃ := a₃) f rfl rfl).symm
  let desc (c : PushoutCocone (CommRingCat.ofHom f)
      (CommRingCat.ofHom (algebraMap B (ArrowRingOf B a₁ a₃)))) :=
    CommRingCat.ofHom (pushoutLift (a₁ := a₁) (a₃ := a₃) f ⟨(c.inl.hom, c.inr.hom),
      congrArg CommRingCat.Hom.hom c.condition⟩)
  refine ⟨⟨comm⟩, ⟨PushoutCocone.IsColimit.mk comm desc ?_ ?_ ?_⟩⟩
  · intro c
    exact congrArg CommRingCat.ofHom (pushoutLiftOfEq_comp_algebraMap f rfl rfl _)
  · intro c
    exact congrArg CommRingCat.ofHom (pushoutLiftOfEq_comp_mapOfEq f rfl rfl _)
  · intro c m hm hn
    apply CommRingCat.hom_ext
    apply (pushoutLift (a₁ := a₁) (a₃ := a₃) f).symm.injective
    apply Subtype.ext
    apply Prod.ext
    · simpa only [pushoutLiftOfEq_symm_apply_fst, desc, CommRingCat.hom_ofHom,
        CommRingCat.hom_comp, pushoutLiftOfEq_comp_algebraMap] using congrArg CommRingCat.Hom.hom hm
    · simpa only [pushoutLiftOfEq_symm_apply_snd, desc, CommRingCat.hom_ofHom,
        CommRingCat.hom_comp, pushoutLiftOfEq_comp_mapOfEq] using congrArg CommRingCat.Hom.hom hn

/-- Forward homomorphism of `shearEquiv`: precomposing the universal strict arrow over `(a₁', a₃')`
with `C₀`. -/
def shearHom {a₁' a₃' : B} {C₀ : VariableChange B} (hC₀ : IsStrictGamma1ThreeChange a₁ a₃ C₀)
    (ha₁ : a₁' = a₁ + 2 * C₀.s) (ha₃ : a₃' = a₃ + a₁ * C₀.r + 2 * C₀.t) :
    ArrowRingOf B a₁ a₃ →+* ArrowRingOf B a₁' a₃' :=
  lift ⟨(algebraMap B _,
    universalChange B a₁' a₃' * C₀.map (algebraMap B (ArrowRingOf B a₁' a₃'))), by
    have h₀ := hC₀.map (algebraMap B (ArrowRingOf B a₁' a₃'))
    have ha₁' : algebraMap B (ArrowRingOf B a₁' a₃') a₁ +
        2 * (C₀.map (algebraMap B (ArrowRingOf B a₁' a₃'))).s =
        algebraMap B (ArrowRingOf B a₁' a₃') a₁' := by
      simp [ha₁, map_ofNat]
    have ha₃' : algebraMap B (ArrowRingOf B a₁' a₃') a₃ +
        algebraMap B (ArrowRingOf B a₁' a₃') a₁ *
          (C₀.map (algebraMap B (ArrowRingOf B a₁' a₃'))).r +
        2 * (C₀.map (algebraMap B (ArrowRingOf B a₁' a₃'))).t =
        algebraMap B (ArrowRingOf B a₁' a₃') a₃' := by
      simp [ha₃, map_ofNat]
    refine h₀.mul ?_
    rw [ha₁', ha₃']
    exact isStrictGamma1ThreeChange_universalChange B a₁' a₃'⟩

@[simp]
theorem shearHom_comp_algebraMap {a₁' a₃' : B} {C₀ : VariableChange B}
    (hC₀ : IsStrictGamma1ThreeChange a₁ a₃ C₀)
    (ha₁ : a₁' = a₁ + 2 * C₀.s) (ha₃ : a₃' = a₃ + a₁ * C₀.r + 2 * C₀.t) :
    (shearHom hC₀ ha₁ ha₃).comp (algebraMap B _) = algebraMap B _ :=
  lift_comp_algebraMap _

@[simp]
theorem shearHom_algebraMap {a₁' a₃' : B} {C₀ : VariableChange B}
    (hC₀ : IsStrictGamma1ThreeChange a₁ a₃ C₀)
    (ha₁ : a₁' = a₁ + 2 * C₀.s) (ha₃ : a₃' = a₃ + a₁ * C₀.r + 2 * C₀.t) (b : B) :
    shearHom hC₀ ha₁ ha₃ (algebraMap B _ b) = algebraMap B _ b :=
  lift_algebraMap _ b

@[simp]
theorem universalChange_map_shearHom {a₁' a₃' : B} {C₀ : VariableChange B}
    (hC₀ : IsStrictGamma1ThreeChange a₁ a₃ C₀)
    (ha₁ : a₁' = a₁ + 2 * C₀.s) (ha₃ : a₃' = a₃ + a₁ * C₀.r + 2 * C₀.t) :
    (universalChange B a₁ a₃).map (shearHom hC₀ ha₁ ha₃) =
      universalChange B a₁' a₃' * C₀.map (algebraMap B _) :=
  map_lift _

/-- **Groupoid shearing equivalence**: if `C₀` is a strict `Γ₁(3)` arrow over `B` from
`gamma1ThreeNormalForm a₁ a₃` to `gamma1ThreeNormalForm a₁' a₃'`, then precomposing with `C₀`
gives an isomorphism of `B`-algebras `ArrowRingOf B a₁ a₃ ≃ₐ[B] ArrowRingOf B a₁' a₃'`. -/
def shearEquiv {a₁' a₃' : B} {C₀ : VariableChange B} (hC₀ : IsStrictGamma1ThreeChange a₁ a₃ C₀)
    (ha₁ : a₁' = a₁ + 2 * C₀.s) (ha₃ : a₃' = a₃ + a₁ * C₀.r + 2 * C₀.t) :
    ArrowRingOf B a₁ a₃ ≃ₐ[B] ArrowRingOf B a₁' a₃' := by
  have hC₀' : IsStrictGamma1ThreeChange a₁' a₃' C₀⁻¹ := by
    rw [ha₁, ha₃]
    exact hC₀.inv
  have ha₁' : a₁ = a₁' + 2 * C₀⁻¹.s := by
    simp [ha₁, VariableChange.inv_def, hC₀.1]
  have ha₃' : a₃ = a₃' + a₁' * C₀⁻¹.r + 2 * C₀⁻¹.t := by
    simp [ha₁, ha₃, VariableChange.inv_def, hC₀.1]
    ring
  let fwd := shearHom hC₀ ha₁ ha₃
  let bwd := shearHom hC₀' ha₁' ha₃'
  have hbwd_fwd : bwd.comp fwd = RingHom.id _ := by
    refine ringHom_ext (RingHom.ext fun b ↦ by simp [fwd, bwd]) ?_
    rw [← VariableChange.map_map, universalChange_map_shearHom, VariableChange.map_mul,
      universalChange_map_shearHom, VariableChange.map_map, shearHom_comp_algebraMap, mul_assoc,
      ← VariableChange.map_mul, inv_mul_cancel, VariableChange.map_one, mul_one,
      VariableChange.map_id]
  have hfwd_bwd : fwd.comp bwd = RingHom.id _ := by
    refine ringHom_ext (RingHom.ext fun b ↦ by simp [fwd, bwd]) ?_
    rw [← VariableChange.map_map, universalChange_map_shearHom, VariableChange.map_mul,
      universalChange_map_shearHom, VariableChange.map_map, shearHom_comp_algebraMap, mul_assoc,
      ← VariableChange.map_mul, mul_inv_cancel, VariableChange.map_one, mul_one,
      VariableChange.map_id]
  exact AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom fwd bwd hfwd_bwd hbwd_fwd)
    (fun b ↦ shearHom_algebraMap hC₀ ha₁ ha₃ b)

theorem shearEquiv_toRingHom {a₁' a₃' : B} {C₀ : VariableChange B}
    (hC₀ : IsStrictGamma1ThreeChange a₁ a₃ C₀)
    (ha₁ : a₁' = a₁ + 2 * C₀.s) (ha₃ : a₃' = a₃ + a₁ * C₀.r + 2 * C₀.t) :
    (shearEquiv hC₀ ha₁ ha₃).toRingHom = shearHom hC₀ ha₁ ha₃ :=
  (rfl)

end ArrowRingOf

end TauCeti.Gamma1ThreeHopfAlgebroid

end
