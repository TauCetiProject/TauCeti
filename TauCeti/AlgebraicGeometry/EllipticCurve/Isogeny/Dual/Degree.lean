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
# Degree polarisation for separable isogenies

For separable isogenies `φ, ψ : W₁ → W₂` over a separably closed field, the symmetric
cross-composite

    φ̂ ∘ ψ + ψ̂ ∘ φ

is the polarisation of the degree. More precisely, if the sum `φ + ψ` is represented by a
separable isogeny `χ`, then

    φ̂ ∘ ψ + ψ̂ ∘ φ = [deg χ − deg φ − deg ψ].

This is the separable part of the quadraticity of the degree on the group of morphisms
(Silverman III.6.3). The cross-composite is additive in either variable whenever the relevant
sum is again a separable isogeny. These identities isolate the algebraic step used to construct
the bilinear degree pairing once the dual is available for arbitrary, possibly inseparable,
isogenies.

## Main results

* `TauCeti.Isogeny.ofIsogeny_dual_comp_add_dual_comp_eq_polar_degree`: the symmetric
  cross-composite is multiplication by the degree polarisation.
* `TauCeti.Isogeny.ofIsogeny_dual_comp_add_dual_comp_add_right` and
  `TauCeti.Isogeny.ofIsogeny_dual_comp_add_dual_comp_add_left`: the cross-composite is additive
  in each variable on separable sums.
* `TauCeti.Isogeny.polar_degree_add_right_of_isSeparable` and
  `TauCeti.Isogeny.polar_degree_add_left_of_isSeparable`: the resulting numerical polarisation is
  additive on separable sums.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.2–3.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [IsSepClosed F]
  {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

variable (φ ψ χ : Isogeny W₁ W₂)
  [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField]
  [Algebra.IsSeparable ψ.fieldPullback.fieldRange W₁.FunctionField]
  [Algebra.IsSeparable χ.fieldPullback.fieldRange W₁.FunctionField]

/-- **The symmetric dual composite is the polarisation of the degree.** If the separable
isogeny `χ` represents the sum `φ + ψ`, then
`φ̂ ∘ ψ + ψ̂ ∘ φ = [deg χ − deg φ − deg ψ]` (Silverman III.6.3). -/
theorem ofIsogeny_dual_comp_add_dual_comp_eq_polar_degree
    (hχ : Hom.ofIsogeny χ = Hom.ofIsogeny φ + Hom.ofIsogeny ψ) :
    (Hom.ofIsogeny φ.dual).comp (Hom.ofIsogeny ψ) +
        (Hom.ofIsogeny ψ.dual).comp (Hom.ofIsogeny φ) =
      QuadraticMap.polar (fun f : Hom W₁ W₂ ↦ (f.degree : ℤ))
        (Hom.ofIsogeny φ) (Hom.ofIsogeny ψ) • Hom.id W₁ := by
  have hdual := ofIsogeny_dual_add φ ψ χ hχ
  have hdegree := χ.ofIsogeny_dual_comp_ofIsogeny
  rw [hdual, hχ, Hom.add_comp, Hom.comp_add, Hom.comp_add,
    φ.ofIsogeny_dual_comp_ofIsogeny, ψ.ofIsogeny_dual_comp_ofIsogeny] at hdegree
  rw [← natCast_zsmul (Hom.id W₁) χ.degree, ← natCast_zsmul (Hom.id W₁) φ.degree,
    ← natCast_zsmul (Hom.id W₁) ψ.degree] at hdegree
  rw [QuadraticMap.polar, ← hχ, Hom.degree_ofIsogeny, Hom.degree_ofIsogeny,
    Hom.degree_ofIsogeny]
  rw [sub_smul, sub_smul, ← hdegree]
  abel

variable {ρ η : Isogeny W₁ W₂}
  [Algebra.IsSeparable ρ.fieldPullback.fieldRange W₁.FunctionField]
  [Algebra.IsSeparable η.fieldPullback.fieldRange W₁.FunctionField]

omit [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField] in
/-- **The symmetric dual composite is additive in the right variable** on separable isogenies:
if `η = ψ + ρ`, then
`φ̂ ∘ η + η̂ ∘ φ = (φ̂ ∘ ψ + ψ̂ ∘ φ) + (φ̂ ∘ ρ + ρ̂ ∘ φ)`. -/
theorem ofIsogeny_dual_comp_add_dual_comp_add_right
    (hη : Hom.ofIsogeny η = Hom.ofIsogeny ψ + Hom.ofIsogeny ρ) :
    (Hom.ofIsogeny φ.dual).comp (Hom.ofIsogeny η) +
        (Hom.ofIsogeny η.dual).comp (Hom.ofIsogeny φ) =
      ((Hom.ofIsogeny φ.dual).comp (Hom.ofIsogeny ψ) +
        (Hom.ofIsogeny ψ.dual).comp (Hom.ofIsogeny φ)) +
      ((Hom.ofIsogeny φ.dual).comp (Hom.ofIsogeny ρ) +
        (Hom.ofIsogeny ρ.dual).comp (Hom.ofIsogeny φ)) := by
  rw [hη, ofIsogeny_dual_add ψ ρ η hη, Hom.comp_add, Hom.add_comp]
  abel

omit [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField] in
/-- **The symmetric dual composite is additive in the left variable** on separable isogenies.
This is the left-variable form of
`ofIsogeny_dual_comp_add_dual_comp_add_right`. -/
theorem ofIsogeny_dual_comp_add_dual_comp_add_left
    (hη : Hom.ofIsogeny η = Hom.ofIsogeny ψ + Hom.ofIsogeny ρ) :
    (Hom.ofIsogeny η.dual).comp (Hom.ofIsogeny φ) +
        (Hom.ofIsogeny φ.dual).comp (Hom.ofIsogeny η) =
      ((Hom.ofIsogeny ψ.dual).comp (Hom.ofIsogeny φ) +
        (Hom.ofIsogeny φ.dual).comp (Hom.ofIsogeny ψ)) +
      ((Hom.ofIsogeny ρ.dual).comp (Hom.ofIsogeny φ) +
        (Hom.ofIsogeny φ.dual).comp (Hom.ofIsogeny ρ)) := by
  rw [hη, ofIsogeny_dual_add ψ ρ η hη, Hom.comp_add, Hom.add_comp]
  abel

/-- **The numerical degree polarisation is additive in the right variable** whenever all four
sums involved are represented by separable isogenies. This is the integer-valued consequence of
the two cross-composite identities above. -/
theorem polar_degree_add_right_of_isSeparable
    {χψ χρ χη : Isogeny W₁ W₂}
    [Algebra.IsSeparable χψ.fieldPullback.fieldRange W₁.FunctionField]
    [Algebra.IsSeparable χρ.fieldPullback.fieldRange W₁.FunctionField]
    [Algebra.IsSeparable χη.fieldPullback.fieldRange W₁.FunctionField]
    (hη : Hom.ofIsogeny η = Hom.ofIsogeny ψ + Hom.ofIsogeny ρ)
    (hχψ : Hom.ofIsogeny χψ = Hom.ofIsogeny φ + Hom.ofIsogeny ψ)
    (hχρ : Hom.ofIsogeny χρ = Hom.ofIsogeny φ + Hom.ofIsogeny ρ)
    (hχη : Hom.ofIsogeny χη = Hom.ofIsogeny φ + Hom.ofIsogeny η) :
    QuadraticMap.polar (fun f : Hom W₁ W₂ ↦ (f.degree : ℤ))
        (Hom.ofIsogeny φ) (Hom.ofIsogeny η) =
      QuadraticMap.polar (fun f : Hom W₁ W₂ ↦ (f.degree : ℤ))
          (Hom.ofIsogeny φ) (Hom.ofIsogeny ψ) +
        QuadraticMap.polar (fun f : Hom W₁ W₂ ↦ (f.degree : ℤ))
          (Hom.ofIsogeny φ) (Hom.ofIsogeny ρ) := by
  apply Hom.zsmul_id_injective (W₁ := W₁)
  -- Applying injectivity leaves a beta-redex around scalar multiplication; expose the two
  -- multiples so the cross-composite identities can rewrite them.
  change QuadraticMap.polar (fun f : Hom W₁ W₂ ↦ (f.degree : ℤ))
      (Hom.ofIsogeny φ) (Hom.ofIsogeny η) • Hom.id W₁ =
    (QuadraticMap.polar (fun f : Hom W₁ W₂ ↦ (f.degree : ℤ))
        (Hom.ofIsogeny φ) (Hom.ofIsogeny ψ) +
      QuadraticMap.polar (fun f : Hom W₁ W₂ ↦ (f.degree : ℤ))
        (Hom.ofIsogeny φ) (Hom.ofIsogeny ρ)) • Hom.id W₁
  rw [← ofIsogeny_dual_comp_add_dual_comp_eq_polar_degree φ η χη hχη,
    ofIsogeny_dual_comp_add_dual_comp_add_right φ ψ hη,
    ofIsogeny_dual_comp_add_dual_comp_eq_polar_degree φ ψ χψ hχψ,
    ofIsogeny_dual_comp_add_dual_comp_eq_polar_degree φ ρ χρ hχρ, add_smul]

/-- **The numerical degree polarisation is additive in the left variable** whenever all four
sums involved are represented by separable isogenies. -/
theorem polar_degree_add_left_of_isSeparable
    {χψ χρ χη : Isogeny W₁ W₂}
    [Algebra.IsSeparable χψ.fieldPullback.fieldRange W₁.FunctionField]
    [Algebra.IsSeparable χρ.fieldPullback.fieldRange W₁.FunctionField]
    [Algebra.IsSeparable χη.fieldPullback.fieldRange W₁.FunctionField]
    (hη : Hom.ofIsogeny η = Hom.ofIsogeny ψ + Hom.ofIsogeny ρ)
    (hχψ : Hom.ofIsogeny χψ = Hom.ofIsogeny φ + Hom.ofIsogeny ψ)
    (hχρ : Hom.ofIsogeny χρ = Hom.ofIsogeny φ + Hom.ofIsogeny ρ)
    (hχη : Hom.ofIsogeny χη = Hom.ofIsogeny φ + Hom.ofIsogeny η) :
    QuadraticMap.polar (fun f : Hom W₁ W₂ ↦ (f.degree : ℤ))
        (Hom.ofIsogeny η) (Hom.ofIsogeny φ) =
      QuadraticMap.polar (fun f : Hom W₁ W₂ ↦ (f.degree : ℤ))
          (Hom.ofIsogeny ψ) (Hom.ofIsogeny φ) +
        QuadraticMap.polar (fun f : Hom W₁ W₂ ↦ (f.degree : ℤ))
          (Hom.ofIsogeny ρ) (Hom.ofIsogeny φ) := by
  rw [QuadraticMap.polar_comm _ (Hom.ofIsogeny η),
    QuadraticMap.polar_comm _ (Hom.ofIsogeny ψ),
    QuadraticMap.polar_comm _ (Hom.ofIsogeny ρ)]
  exact polar_degree_add_right_of_isSeparable φ ψ hη hχψ hχρ hχη

end TauCeti.Isogeny

end
