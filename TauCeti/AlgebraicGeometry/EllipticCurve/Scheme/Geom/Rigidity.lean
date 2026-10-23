/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.NaiveLevel
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Neg
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.ZeroSection

/-!
# Automorphisms of an elliptic curve fixing a full level structure

Let `E` be an elliptic curve over a scheme `S` and let `σ : E ⟶ E` be an automorphism of `E` over
`S` fixing the zero section, given as a cartesian square over the identity of `S`. Let
`φ : A →* E(S)` be a homomorphism injective on every fibre
(`EllipticCurveGeom.IsFiberwiseInjective`), and let `a, b ∈ A` with `a² ≠ 1`, `b ≠ 1` and
`b ≠ a^{±1}`, so that `P = φ a` and `Q = φ b` satisfy `P ≠ -P` and `Q ∉ {0, P, -P}` in every
fibre. If `σ` fixes `P` and `Q`, then `σ` is the identity
(`EllipticCurveGeom.IsFiberwiseInjective.eq_id_of_isPullback`). For a naive full level `N`
structure `φ : (ℤ/Nℤ)² →* E(S)` with `N ≥ 3`, the two basis vectors qualify, which gives the
rigidity of the naive moduli problem `[Γ(N)]` (Katz–Mazur 2.7.2). No hypothesis is made on `S`: it
may be nonreduced or non-affine. (A naive `[Γ(N)]`-structure forces `N` to be invertible on `S`,
since `(ℤ/pℤ)²` does not embed into the `p`-torsion of an elliptic curve in characteristic `p`.)

The bound `N ≥ 3` is sharp, and both sections are needed. For `N ≤ 2`, the automorphism `[-1]`
fixes every section killed by `N`. On `Y² + Y = X³` over a field containing a primitive cube root
of unity `ζ`, the automorphism `(X, Y) ↦ (ζX, Y)` fixes `P = (0, 0)` and `-P = (0, -1)`, and
`P ≠ -P`.

**The projective model.** Over `Spec R`, an automorphism of `projModel W` over `Spec R` fixing the
zero section is a change of variables `C = (u, r, s, t)` with `C • W = W`
(`WeierstrassCurve.existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom`). It commutes with
negation, so if it fixes `(x₁, y₁)` and `(x₂, y₂)` it also fixes `(x₁, -y₁ - a₁x₁ - a₃)`. When
`x₁ - x₂` and `2y₁ + a₁x₁ + a₃` are units, these three fixed points force `C = 1`
(`WeierstrassCurve.VariableChange.eq_one_of_isUnit_sub`), so the automorphism is the identity
(`WeierstrassCurve.eq_id_of_projModelAffinePoint_comp_eq`).

**Over a scheme.** On a pointed Weierstrass chart `c` of `E`, a section `P` of `E` induces a
section of the projective model of the equation of `c` (`PointedWeierstrassChart.modelPoint`),
and `σ` induces an automorphism of that model (`PointedWeierstrassChart.modelMap`). If `P` misses
the zero section, its model point is an affine point `(x, y)`. The two unit conditions are checked
modulo the maximal ideals of the coefficient ring of the chart: over a field, two points with the
same `x`-coordinate are equal or opposite, and the fibrewise conditions on `P` and `Q` exclude
both.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsFiberwiseInjective.eq_id_of_isPullback`: an
  automorphism of `E` over `S` fixing the zero section, `φ a` and `φ b` is the identity.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, 2.7.2 and Chapter 4.
* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1 (the change of
  variables).
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllipticCurveGeom

variable {S : Scheme.{u}} {E : EllipticCurveGeom S}

/-! ### Rigidity -/

variable {A : Type*} [Group A] {φ : A →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)}

-- Two sections whose model points on a chart agree modulo a maximal ideal of its coefficient ring
-- agree on the corresponding field-valued point of `S`.
private theorem comp_eq_of_modelPoint (c : PointedWeierstrassChart E.structureMap E.zero)
    {P Q : S ⟶ E.carrier} (hP : P ≫ E.structureMap = 𝟙 S) (hQ : Q ≫ E.structureMap = 𝟙 S)
    {x y x' y' : c.ring} {h : c.equation.toAffine.Equation x y}
    {h' : c.equation.toAffine.Equation x' y'}
    (hPx : c.modelPoint hP = c.equation.projModelAffinePoint h)
    (hQx : c.modelPoint hQ = c.equation.projModelAffinePoint h') {K : Type u} [Field K]
    (ψ : c.ring →+* K) (hx : ψ x = ψ x') (hy : ψ y = ψ y') :
    (Spec.map (CommRingCat.ofHom ψ) ≫ c.baseIso.inv ≫ c.baseMap) ≫ P =
      (Spec.map (CommRingCat.ofHom ψ) ≫ c.baseIso.inv ≫ c.baseMap) ≫ Q := by
  have hψ : Spec.map (CommRingCat.ofHom ψ) ≫ c.equation.projModelAffinePoint h =
      Spec.map (CommRingCat.ofHom ψ) ≫ c.equation.projModelAffinePoint h' := by
    have : (c.equation.map ψ).projModelAffinePoint (h.map ψ) =
        (c.equation.map ψ).projModelAffinePoint (h'.map ψ) :=
      (WeierstrassCurve.projModelAffinePoint_inj _).mpr ⟨hx, hy⟩
    rw [← WeierstrassCurve.projModelAffinePoint_projModelBaseChange,
      ← WeierstrassCurve.projModelAffinePoint_projModelBaseChange, this]
  calc (Spec.map (CommRingCat.ofHom ψ) ≫ c.baseIso.inv ≫ c.baseMap) ≫ P
      = Spec.map (CommRingCat.ofHom ψ) ≫ c.modelPoint hP ≫ c.modelIso.inv ≫ c.toTotal := by
        rw [c.modelPoint_modelIso_inv_toTotal]; simp only [Category.assoc]
    _ = Spec.map (CommRingCat.ofHom ψ) ≫ c.modelPoint hQ ≫ c.modelIso.inv ≫ c.toTotal := by
        rw [hPx, reassoc_of% hψ, hQx]
    _ = (Spec.map (CommRingCat.ofHom ψ) ≫ c.baseIso.inv ≫ c.baseMap) ≫ Q := by
        rw [c.modelPoint_modelIso_inv_toTotal]; simp only [Category.assoc]

/-- **Automorphisms fixing a full level structure are trivial.** Let `φ : A →* E(S)` be injective
on every fibre, and let `a, b ∈ A` with `a² ≠ 1`, `b ≠ 1`, `b ≠ a` and `b ≠ a⁻¹`. An endomorphism
`σ` of `E` over `S`, cartesian over the identity of `S` (so an automorphism), which fixes the zero
section, `φ a` and `φ b` is the identity. For a naive `[Γ(N)]`-structure `(ℤ/Nℤ)² →* E(S)` with
`N ≥ 3`, the two basis vectors are such `a` and `b`. -/
theorem IsFiberwiseInjective.eq_id_of_isPullback (hφ : E.IsFiberwiseInjective φ) {a b : A}
    (ha : a * a ≠ 1) (hb : b ≠ 1) (hba : b ≠ a) (hba' : b ≠ a⁻¹) {σ : E.carrier ⟶ E.carrier}
    (hσ : IsPullback σ E.structureMap E.structureMap (𝟙 S)) (h0 : E.zero ≫ σ = E.zero)
    (hσa : (φ a).left ≫ σ = (φ a).left) (hσb : (φ b).left ≫ σ = (φ b).left) : σ = 𝟙 _ := by
  obtain ⟨Atl⟩ := E.localModel
  refine Atl.hom_ext_of_toTotal _ _ fun i ↦ ?_
  set c := Atl.chart i
  have hh : 𝟙 c.base ≫ c.baseMap = c.baseMap ≫ 𝟙 S := by simp
  -- it suffices that the endomorphism of the projective model of `c` induced by `σ` is trivial
  suffices hm : PointedWeierstrassChart.modelMap hσ hh = 𝟙 _ by
    have : PointedWeierstrassChart.carrierMap hσ hh = 𝟙 _ := by
      rw [← cancel_mono c.modelIso.hom, ← PointedWeierstrassChart.modelIso_hom_modelMap, hm]
      simp
    rw [Category.comp_id, ← PointedWeierstrassChart.carrierMap_toTotal hσ hh, this,
      Category.id_comp]
  have ha1 : a ≠ 1 := by rintro rfl; simp at ha
  -- the model points of `φ a`, `φ b` and `φ a⁻¹` are affine points
  have hP (c' : A) : (φ c').left ≫ E.structureMap = 𝟙 S := by simp
  obtain ⟨x₁, y₁, h₁, hP₁⟩ := c.equation.exists_eq_projModelAffinePoint
    (c.modelPoint_projModelOver (hP a))
    (c.modelPoint_apply_ne (hP a) (isFiberwiseInjective_iff.mp hφ a ha1))
  obtain ⟨x₂, y₂, h₂, hP₂⟩ := c.equation.exists_eq_projModelAffinePoint
    (c.modelPoint_projModelOver (hP b))
    (c.modelPoint_apply_ne (hP b) (isFiberwiseInjective_iff.mp hφ b hb))
  have hP₁' : c.modelPoint (hP a⁻¹) =
      c.equation.projModelAffinePoint ((c.equation.toAffine.equation_neg x₁ y₁).mpr h₁) := by
    simp only [map_inv, hom_inv_left, modelPoint_neg c (hP a), hP₁,
      WeierstrassCurve.projModelAffinePoint_projModelNeg]
  -- distinct elements of `A` give points which differ modulo every maximal ideal
  have hne {x y x' y' : c.ring} {h : c.equation.toAffine.Equation x y}
      {h' : c.equation.toAffine.Equation x' y'} {c₁ c₂ : A} (hc : c₁ ≠ c₂)
      (hPx : c.modelPoint (hP c₁) = c.equation.projModelAffinePoint h)
      (hQx : c.modelPoint (hP c₂) = c.equation.projModelAffinePoint h') (m : Ideal c.ring)
      [m.IsMaximal] (hx : x - x' ∈ m) (hy : y - y' ∈ m) : False := by
    let _ := Ideal.Quotient.field m
    refine hc (hφ.eq_of_comp_left_eq _ (comp_eq_of_modelPoint c (hP c₁) (hP c₂) hPx hQx
      (Ideal.Quotient.mk m) ?_ ?_))
    · rwa [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    · rwa [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  refine WeierstrassCurve.eq_id_of_projModelAffinePoint_comp_eq
    (by simpa using PointedWeierstrassChart.isPullback_modelMap hσ hh)
    (by simpa using PointedWeierstrassChart.projModelZero_modelMap hσ hh (by simpa using h0))
    h₁ h₂ ?_ ?_ (hP₁ ▸ c.modelPoint_modelMap_of_comp_eq (hP a) hσ hσa)
    (hP₂ ▸ c.modelPoint_modelMap_of_comp_eq (hP b) hσ hσb)
  · -- modulo a maximal ideal containing `x₁ - x₂`, `φ b` would be `φ a` or `φ a⁻¹`
    by_contra hx
    obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits hx
    let _ := Ideal.Quotient.field m
    have hX : Ideal.Quotient.mk m x₂ = Ideal.Quotient.mk m x₁ := by
      rw [eq_comm, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact hxm
    rcases WeierstrassCurve.Affine.Y_eq_of_X_eq (h₂.map _) (h₁.map _) hX with hY | hY
    · refine hne hba hP₂ hP₁ m (by rw [← neg_sub]; exact neg_mem hxm) ?_
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hY, sub_self]
    · refine hne hba' hP₂ hP₁' m (by rw [← neg_sub]; exact neg_mem hxm) ?_
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hY,
        WeierstrassCurve.Affine.map_negY, sub_self]
  · -- modulo a maximal ideal containing `y₁ - negY x₁ y₁`, `φ a` would be `φ a⁻¹`
    by_contra hy
    obtain ⟨m, hm, hym⟩ := exists_max_ideal_of_mem_nonunits hy
    refine hne (fun h ↦ ha ?_) hP₁ hP₁' m (by simp) hym
    calc a * a = a * a⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel a

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
