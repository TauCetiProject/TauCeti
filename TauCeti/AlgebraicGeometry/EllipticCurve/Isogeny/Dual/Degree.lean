/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Add
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Degree
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Ring

/-!
# The degree is a quadratic form

For morphisms `f, g : W₁ → W₂` of elliptic curves over a field, the symmetric cross-composite of
duals is the polarisation of the degree:

    f̂ ∘ g + ĝ ∘ f = [deg (f + g) − deg f − deg g].

Indeed, expanding `(f + g)^ ∘ (f + g) = [deg (f + g)]` by additivity of the dual
(`TauCeti.Isogeny.Hom.dual_add`) and biadditivity of composition leaves
`[deg f] + f̂ ∘ g + ĝ ∘ f + [deg g]`. The cross-composite is additive in each variable, and
`n ↦ [n]` is injective, so the polarisation is bilinear. Together with `deg (n f) = n² deg f`
(`TauCeti.Isogeny.Hom.degree_zsmul`), this makes the degree, extended by `deg 0 = 0`, a quadratic
form on `Hom W₁ W₂`, positive definite since only the zero map has degree zero
(Silverman III.6.3). No separability or closure hypothesis is made.

## Main definitions

* `TauCeti.Isogeny.Hom.degreeForm`: the degree as a `ℤ`-valued quadratic form on `Hom W₁ W₂`.

## Main results

* `TauCeti.Isogeny.Hom.dual_comp_add_dual_comp`: `f̂ ∘ g + ĝ ∘ f` is multiplication by the degree
  polarisation.
* `TauCeti.Isogeny.Hom.polar_degree_add_left` and `TauCeti.Isogeny.Hom.polar_degree_add_right`:
  the degree polarisation is additive in each variable.
* `TauCeti.Isogeny.Hom.degreeForm_posDef`: the degree form is positive definite.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.2–3.
-/

public section

namespace TauCeti.Isogeny.Hom

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- **The symmetric dual composite is the polarisation of the degree**:
`f̂ ∘ g + ĝ ∘ f = [deg (f + g) − deg f − deg g]` (Silverman III.6.3). -/
theorem dual_comp_add_dual_comp (f g : Hom W₁ W₂) :
    f.dual.comp g + g.dual.comp f =
      QuadraticMap.polar (fun h : Hom W₁ W₂ ↦ (h.degree : ℤ)) f g • id W₁ := by
  have h := (f + g).dual_comp_self
  rw [dual_add, add_comp, comp_add, comp_add, dual_comp_self, dual_comp_self] at h
  rw [QuadraticMap.polar, sub_smul, sub_smul, natCast_zsmul, natCast_zsmul, natCast_zsmul, ← h]
  abel

/-- **The degree polarisation is additive in the left variable.** -/
theorem polar_degree_add_left (f f' g : Hom W₁ W₂) :
    QuadraticMap.polar (fun h : Hom W₁ W₂ ↦ (h.degree : ℤ)) (f + f') g =
      QuadraticMap.polar (fun h : Hom W₁ W₂ ↦ (h.degree : ℤ)) f g +
        QuadraticMap.polar (fun h : Hom W₁ W₂ ↦ (h.degree : ℤ)) f' g := by
  refine zsmul_id_injective (W₁ := W₁) ?_
  simp only [add_smul, ← dual_comp_add_dual_comp, dual_add, add_comp, comp_add]
  abel

/-- **The degree polarisation is additive in the right variable.** -/
theorem polar_degree_add_right (f g g' : Hom W₁ W₂) :
    QuadraticMap.polar (fun h : Hom W₁ W₂ ↦ (h.degree : ℤ)) f (g + g') =
      QuadraticMap.polar (fun h : Hom W₁ W₂ ↦ (h.degree : ℤ)) f g +
        QuadraticMap.polar (fun h : Hom W₁ W₂ ↦ (h.degree : ℤ)) f g' := by
  simp only [QuadraticMap.polar_comm _ f, polar_degree_add_left]

variable (W₁ W₂) in
/-- **The degree is a quadratic form** on the morphisms `W₁ → W₂` (Silverman III.6.3), with the
zero map of degree zero. -/
noncomputable def degreeForm : QuadraticMap ℤ (Hom W₁ W₂) ℤ :=
  QuadraticMap.ofPolar (fun f ↦ (f.degree : ℤ))
    (fun n f ↦ by simp [sq])
    polar_degree_add_left
    (fun n f g ↦ by
      refine zsmul_id_injective (W₁ := W₁) ?_
      simp only [← dual_comp_add_dual_comp, smul_eq_mul, mul_smul, dual_zsmul, zsmul_comp,
        comp_zsmul, smul_add])

@[simp]
theorem degreeForm_apply (f : Hom W₁ W₂) : degreeForm W₁ W₂ f = f.degree :=
  (rfl)

/-- **The degree form is positive definite**: every nonzero morphism has positive degree. -/
theorem degreeForm_posDef : (degreeForm W₁ W₂).PosDef := fun f hf ↦ by
  simpa [Nat.pos_iff_ne_zero] using hf

end TauCeti.Isogeny.Hom

end
