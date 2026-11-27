/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Cokernel
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.VariableChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.MapEquiv
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.BaseChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Factorisation
import TauCeti.GroupTheory.Index.Comp

/-!
# The Kummer ratio of an isogeny

Over a field `F`, the Kummer ratio of `φ : E₁ → E₂` is
`[E₂(F) : φ E₁(F)] / #E₁(F)[φ]`. The kernel is always finite. The ratio is positive when the
image has finite index, and zero otherwise, following the convention for subgroup indices.
It is multiplicative under composition, without a finite-index hypothesis, and equals `1` on
isogenies of degree one and hence on changes of variables. The Kummer ratio of a base change
depends on the extension field only up to isomorphism over the ground field
(`TauCeti.Isogeny.kummerRatio_baseChange_congr`), so it can be computed in any model of a
completion, such as `ℝ` for the completion of `ℚ` at its infinite place.

Over completions of a global field, these ratios are the local factors in the global Selmer-ratio
formula used in Cassels' proof of isogeny invariance of the Birch–Swinnerton-Dyer quotient.
Over `ℚ`, they are assembled in `TauCeti.Isogeny.kummerRatioProduct`.
For a separable isogeny, the numerator `[E₂(F) : φ E₁(F)]` is the order of the
Galois-cohomological Kummer image (`TauCeti.Isogeny.natCard_range_kummerMap`, with infinite
orders read as zero). The ratio itself requires no separability hypothesis.

## References

* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199.
-/

public noncomputable section

namespace TauCeti.Isogeny

variable {F : Type*} [Field F] {W₁ W₂ W₃ : WeierstrassCurve.Affine F}
  [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]

/-- The cokernel/kernel ratio on the `F`-rational points of an isogeny. -/
def kummerRatio (φ : Isogeny W₁ W₂) : ℚ := by
  letI := Classical.typeDecidableEq F
  exact ((Hom.ofIsogeny φ).pointMapHom.range.index : ℚ) /
    Nat.card (Hom.ofIsogeny φ).pointMapHom.ker

/-- The Kummer ratio in terms of the point homomorphism, for any decidable equality on `F`. -/
theorem kummerRatio_def [d : DecidableEq F] (φ : Isogeny W₁ W₂) :
    φ.kummerRatio = ((Hom.ofIsogeny φ).pointMapHom.range.index : ℚ) /
      Nat.card (Hom.ofIsogeny φ).pointMapHom.ker := by
  cases Subsingleton.elim d (Classical.typeDecidableEq F)
  rfl

/-- The Kummer ratio is positive exactly when the cokernel on rational points is finite. -/
theorem kummerRatio_pos_iff [DecidableEq F] (φ : Isogeny W₁ W₂) :
    0 < φ.kummerRatio ↔ (Hom.ofIsogeny φ).pointMapHom.range.FiniteIndex := by
  have := (Hom.ofIsogeny φ).finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero φ)
  rw [kummerRatio_def, div_pos_iff_of_pos_right (Nat.cast_pos.mpr Nat.card_pos),
    Nat.cast_pos, AddSubgroup.finiteIndex_iff, Nat.pos_iff_ne_zero]

/-- The Kummer ratio is positive when the cokernel on rational points is finite. -/
theorem kummerRatio_pos [DecidableEq F] (φ : Isogeny W₁ W₂)
    [(Hom.ofIsogeny φ).pointMapHom.range.FiniteIndex] : 0 < φ.kummerRatio := by
  exact (kummerRatio_pos_iff φ).mpr inferInstance

/-- Kummer ratios multiply under composition, even when the point images have infinite index. -/
@[simp]
theorem kummerRatio_comp (ψ : Isogeny W₂ W₃) (φ : Isogeny W₁ W₂) :
    (ψ.comp φ).kummerRatio = ψ.kummerRatio * φ.kummerRatio := by
  classical
  have := (Hom.ofIsogeny φ).finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero φ)
  have := (Hom.ofIsogeny ψ).finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero ψ)
  simp only [kummerRatio_def, ← Hom.ofIsogeny_comp_ofIsogeny, Hom.comp_pointMapHom]
  exact (Hom.ofIsogeny φ).pointMapHom.index_range_div_card_ker_comp
    (Hom.ofIsogeny ψ).pointMapHom

/-- The identity isogeny has Kummer ratio one. -/
@[simp]
theorem kummerRatio_id (W : WeierstrassCurve.Affine F) [W.IsElliptic] :
    (Isogeny.id W).kummerRatio = 1 := by
  classical
  have hrange : (AddMonoidHom.id W.Point).range = ⊤ :=
    AddMonoidHom.range_eq_top.mpr Function.surjective_id
  simp [kummerRatio_def, ← Hom.id_def, Hom.id_pointMapHom, hrange]

/-- An isogeny of degree one is an isomorphism on rational points and therefore has Kummer ratio
one. -/
theorem kummerRatio_eq_one_of_degree_eq_one (φ : Isogeny W₁ W₂) (hφ : φ.degree = 1) :
    φ.kummerRatio = 1 := by
  classical
  obtain ⟨ψ, hψφ, hφψ⟩ := φ.exists_comp_eq_id_and_comp_eq_id_of_degree_eq_one hφ
  have hleft :
      Function.LeftInverse (Hom.ofIsogeny ψ).pointMapHom (Hom.ofIsogeny φ).pointMapHom :=
    fun P ↦ by
      rw [← AddMonoidHom.comp_apply, ← Hom.comp_pointMapHom, Hom.ofIsogeny_comp_ofIsogeny,
        hψφ, ← Hom.id_def, Hom.id_pointMapHom, AddMonoidHom.id_apply]
  have hright :
      Function.RightInverse (Hom.ofIsogeny ψ).pointMapHom (Hom.ofIsogeny φ).pointMapHom :=
    fun P ↦ by
      rw [← AddMonoidHom.comp_apply, ← Hom.comp_pointMapHom, Hom.ofIsogeny_comp_ofIsogeny,
        hφψ, ← Hom.id_def, Hom.id_pointMapHom, AddMonoidHom.id_apply]
  have hrange : (Hom.ofIsogeny φ).pointMapHom.range = ⊤ :=
    AddMonoidHom.range_eq_top.mpr hright.surjective
  have hker : (Hom.ofIsogeny φ).pointMapHom.ker = ⊥ :=
    (AddMonoidHom.ker_eq_bot_iff _).mpr hleft.injective
  simp [kummerRatio_def, hrange, hker]

/-- The isomorphism induced by a change of variables has Kummer ratio one. -/
@[simp]
theorem kummerRatio_variableChangeIsogeny (C : WeierstrassCurve.VariableChange F)
    (h : C • W₁ = W₂) :
    (variableChangeIsogeny C h).kummerRatio = 1 :=
  kummerRatio_eq_one_of_degree_eq_one _ (degree_variableChangeIsogeny C h)

/-- `Isogeny.baseChange` is `Isogeny.map (algebraMap F K)` typed between the `WeierstrassCurve`
base changes, so both have the same Kummer ratio. -/
theorem kummerRatio_baseChange {K : Type*} [Field K] [Algebra F K]
    {E₁ E₂ : WeierstrassCurve F} [E₁.IsElliptic] [E₂.IsElliptic]
    (φ : Isogeny E₁.toAffine E₂.toAffine) :
    (φ.baseChange K).kummerRatio = (φ.map (algebraMap F K)).kummerRatio :=
  (rfl)

/-- **The Kummer ratio of a base change is invariant under isomorphism of the extension**: along
an `F`-algebra isomorphism `e : L ≃ₐ[F] M`, the base changes of `φ` to `L` and to `M` have the same
Kummer ratio. Transport of points along `e` identifies the two point maps, hence their images and
kernels. -/
theorem kummerRatio_baseChange_congr {L M : Type*} [Field L] [Field M] [Algebra F L]
    [Algebra F M] {E₁ E₂ : WeierstrassCurve F} [E₁.IsElliptic] [E₂.IsElliptic]
    (φ : Isogeny E₁.toAffine E₂.toAffine) (e : L ≃ₐ[F] M) :
    (φ.baseChange L).kummerRatio = (φ.baseChange M).kummerRatio := by
  classical
  rw [kummerRatio_def, kummerRatio_def]
  set f := (Hom.ofIsogeny (φ.baseChange L)).pointMapHom
  set g := (Hom.ofIsogeny (φ.baseChange M)).pointMapHom
  set e₁ := WeierstrassCurve.Affine.Point.mapEquiv E₁ e
  set e₂ := WeierstrassCurve.Affine.Point.mapEquiv E₂ e
  -- transport of points along `e` intertwines the two point maps
  have hcomm : g.comp (e₁ : _ →+ _) = (e₂ : _ →+ _).comp f := AddMonoidHom.ext fun P ↦ by
    have h := Hom.pointMap_map_algebraMap_map (Hom.ofIsogeny φ) e.toAlgHom P
    rw [Hom.ofIsogeny_map, Hom.ofIsogeny_map] at h
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_ofClass, e₁, e₂,
      WeierstrassCurve.Affine.Point.mapEquiv_apply]
    exact (Hom.pointMapHom_apply _ _).trans (h.trans (congrArg _ (Hom.pointMapHom_apply _ _).symm))
  -- so `e₂` carries the image of `f` onto that of `g`, and `e₁⁻¹` carries `ker g` onto `ker f`
  have hrange : g.range = f.range.map (e₂ : _ →+ _) := by
    have he₁ : (e₁ : _ →+ _).range = ⊤ := AddMonoidHom.range_eq_top.mpr fun Q ↦ ⟨e₁.symm Q, by simp⟩
    rw [← AddMonoidHom.range_comp, ← hcomm, AddMonoidHom.range_comp, he₁,
      ← AddMonoidHom.range_eq_map]
  have hker : g.ker.map (e₁.symm : _ →+ _) = f.ker := by
    rw [← AddMonoidHom.ker_comp_addEquiv, hcomm,
      AddMonoidHom.ker_comp_of_injective _ _ e₂.injective]
  rw [hrange, ← hker, AddSubgroup.index_map_equiv,
    Nat.card_congr (g.ker.equivMapOfInjective _ e₁.symm.injective).toEquiv.symm]

end TauCeti.Isogeny
