/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.PointMap
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Commute
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PointHom.Kernel
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Separability

/-!
# The dual of a separable isogeny over a separably closed field

Over a separably closed field the kernel of a separable isogeny `φ : W₁ → W₂` has exactly `deg φ`
points (`TauCeti.Isogeny.card_ker_eq_degree`). So `[deg φ]` factors through `φ` by a unique
isogeny (`TauCeti.Isogeny.existsUnique_comp_eq_mulByIntIsogenyOfNeZero_degree`). This factor is
the **dual isogeny** `φ̂ : W₂ → W₁` (Silverman III.6.1), and this file names it and proves its
basic properties (Silverman III.6.2(a), (d), (e), (f)):

* `φ̂ ∘ φ = [deg φ]` on `W₁`, and `φ̂` is the only isogeny with this property;
* `φ ∘ φ̂ = [deg φ]` on `W₂`;
* `deg φ̂ = deg φ`;
* `φ̂̂ = φ` whenever `φ̂` is itself separable;
* `[n]̂ = [n]` whenever `n` is nonzero in the base field.

The identity `φ ∘ φ̂ = [deg φ]` needs `φ ∘ [n] = [n] ∘ φ`. This holds because composition with a
separable isogeny over a separably closed field is additive in the inner morphism
(`TauCeti.Isogeny.Hom.ofIsogeny_comp_add`). Precomposing with `φ` is injective, so it cancels from
`φ ∘ φ̂ ∘ φ = φ ∘ [deg φ] = [deg φ] ∘ φ`.

## Main definitions

* `TauCeti.Isogeny.dual`: the dual `φ̂` of a separable isogeny `φ` over a separably closed field.

## Main results

* `TauCeti.Isogeny.dual_comp` and `TauCeti.Isogeny.eq_dual_iff_comp_eq`: `φ̂ ∘ φ = [deg φ]`, and
  this characterises `φ̂`.
* `TauCeti.Isogeny.comp_dual`: `φ ∘ φ̂ = [deg φ]`.
* `TauCeti.Isogeny.degree_dual`: `deg φ̂ = deg φ`.
* `TauCeti.Isogeny.ofIsogeny_dual_comp_ofIsogeny` and
  `TauCeti.Isogeny.ofIsogeny_comp_ofIsogeny_dual`: the two composites are `deg φ • 1` in the
  additive groups of morphisms.
* `TauCeti.Isogeny.pointMap_dual_pointMap` and `TauCeti.Isogeny.pointMap_pointMap_dual`: on points,
  `φ̂ (φ P) = deg φ • P` and `φ (φ̂ Q) = deg φ • Q`.
* `TauCeti.Isogeny.dual_dual`: `φ̂̂ = φ` when `φ̂` is separable.
* `TauCeti.Isogeny.dual_mulByIntIsogeny`: `[n]` is self-dual when it is separable.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.8, III.4.10, III.6.1 and
  III.6.2.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [IsSepClosed F] {W₁ W₂ : WeierstrassCurve.Affine F}
  [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁ W₂) [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField]

/-- **The dual isogeny** `φ̂ : W₂ → W₁` of a separable isogeny `φ : W₁ → W₂` over a separably
closed field: the unique isogeny with `φ̂ ∘ φ = [deg φ]` (Silverman III.6.1). -/
noncomputable def dual : Isogeny W₂ W₁ := by
  classical
  exact (existsUnique_comp_eq_mulByIntIsogenyOfNeZero_degree φ.card_ker_eq_degree).exists.choose

/-- **The dual of `φ` composed with `φ` is multiplication by `deg φ`** on `W₁`
(Silverman III.6.1, III.6.2(a)). -/
@[simp]
theorem dual_comp :
    φ.dual.comp φ = mulByIntIsogenyOfNeZero W₁ (n := φ.degree) (mod_cast φ.degree_ne_zero) := by
  classical
  exact
    (existsUnique_comp_eq_mulByIntIsogenyOfNeZero_degree φ.card_ker_eq_degree).exists.choose_spec

/-- **`φ̂` is the only isogeny `χ` with `χ ∘ φ = [deg φ]`.** -/
theorem eq_dual_iff_comp_eq {χ : Isogeny W₂ W₁} :
    χ = φ.dual ↔
      χ.comp φ = mulByIntIsogenyOfNeZero W₁ (n := φ.degree) (mod_cast φ.degree_ne_zero) :=
  ⟨fun h ↦ h ▸ φ.dual_comp, fun h ↦ comp_right_injective φ (h.trans φ.dual_comp.symm)⟩

/-- **The dual has the same degree** (Silverman III.6.2(e)). -/
@[simp]
theorem degree_dual : φ.dual.degree = φ.degree :=
  degree_eq_of_comp_eq_mulByIntIsogenyOfNeZero_degree φ.dual_comp

/-- **`φ` composed with its dual is multiplication by `deg φ`** on `W₂` (Silverman III.6.2(a)). -/
@[simp]
theorem comp_dual :
    φ.comp φ.dual = mulByIntIsogenyOfNeZero W₂ (n := φ.degree) (mod_cast φ.degree_ne_zero) :=
  comp_right_inj.mp <| by rw [comp_assoc, dual_comp, comp_mulByIntIsogenyOfNeZero]

/-- **`φ̂ ∘ φ = deg φ • 1`** in the additive group of morphisms of `W₁`. -/
theorem ofIsogeny_dual_comp_ofIsogeny :
    (Hom.ofIsogeny φ.dual).comp (Hom.ofIsogeny φ) = φ.degree • Hom.id W₁ := by
  rw [Hom.ofIsogeny_comp_ofIsogeny, dual_comp, ofIsogeny_mulByIntIsogeny, natCast_zsmul]

/-- **`φ ∘ φ̂ = deg φ • 1`** in the additive group of morphisms of `W₂`. -/
theorem ofIsogeny_comp_ofIsogeny_dual :
    (Hom.ofIsogeny φ).comp (Hom.ofIsogeny φ.dual) = φ.degree • Hom.id W₂ := by
  rw [Hom.ofIsogeny_comp_ofIsogeny, comp_dual, ofIsogeny_mulByIntIsogeny, natCast_zsmul]

/-- **On points, `φ̂ (φ P) = deg φ • P`.** -/
@[simp]
theorem pointMap_dual_pointMap [DecidableEq F] (P : W₁.Point) :
    (Hom.ofIsogeny φ.dual).pointMap ((Hom.ofIsogeny φ).pointMap P) = φ.degree • P := by
  rw [← Hom.comp_pointMap, ofIsogeny_dual_comp_ofIsogeny, Hom.nsmul_pointMap, Hom.id_pointMap]

/-- **On points, `φ (φ̂ Q) = deg φ • Q`.** -/
@[simp]
theorem pointMap_pointMap_dual [DecidableEq F] (Q : W₂.Point) :
    (Hom.ofIsogeny φ).pointMap ((Hom.ofIsogeny φ.dual).pointMap Q) = φ.degree • Q := by
  rw [← Hom.comp_pointMap, ofIsogeny_comp_ofIsogeny_dual, Hom.nsmul_pointMap, Hom.id_pointMap]

/-- **The dual of the dual is the original isogeny**, when the dual is separable
(Silverman III.6.2(f)). -/
@[simp]
theorem dual_dual [Algebra.IsSeparable φ.dual.fieldPullback.fieldRange W₂.FunctionField] :
    φ.dual.dual = φ :=
  ((eq_dual_iff_comp_eq φ.dual).mpr <| by
    rw [comp_dual, mulByIntIsogeny_inj, degree_dual]).symm

variable (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- **Multiplication by `n` is self-dual** when it is separable, that is, when `n` is nonzero in
`F` (`isSeparable_mulByIntIsogeny_iff`; Silverman III.6.2(d)). -/
@[simp]
theorem dual_mulByIntIsogeny {n : ℤ} (hn : psiFunctionField W n ≠ 0)
    [Algebra.IsSeparable (mulByIntIsogeny W hn).fieldPullback.fieldRange W.FunctionField] :
    (mulByIntIsogeny W hn).dual = mulByIntIsogeny W hn :=
  ((eq_dual_iff_comp_eq _).mpr <| by
    have hchar := (isSeparable_mulByIntIsogeny_iff W hn).mp ‹_›
    rw [mulByIntIsogeny_comp_mulByIntIsogeny W hn hn
        (psiFunctionField_ne_zero W (by push_cast; exact mul_ne_zero hchar hchar)),
      mulByIntIsogeny_inj, degree_mulByIntIsogeny, Nat.cast_pow, Int.natAbs_sq, sq]).symm

end TauCeti.Isogeny

end
