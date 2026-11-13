/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Cokernel
import TauCeti.GroupTheory.Index.Comp

/-!
# The Kummer ratio of an isogeny

Over a field `F`, the Kummer ratio of `φ : E₁ → E₂` is
`[E₂(F) : φ E₁(F)] / #E₁(F)[φ]`. The kernel is always finite. The ratio is positive when the
image has finite index, and zero otherwise, following the convention for subgroup indices.
It is multiplicative under composition, without a finite-index hypothesis.

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

/-- The Kummer ratio is positive when the cokernel on rational points is finite. -/
theorem kummerRatio_pos [DecidableEq F] (φ : Isogeny W₁ W₂)
    [(Hom.ofIsogeny φ).pointMapHom.range.FiniteIndex] : 0 < φ.kummerRatio := by
  have := (Hom.ofIsogeny φ).finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero φ)
  rw [kummerRatio_def]
  exact div_pos (Nat.cast_pos.mpr (Hom.ofIsogeny φ).pointMapHom.range.index_pos)
    (Nat.cast_pos.mpr Nat.card_pos)

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
  have h : (Hom.ofIsogeny (Isogeny.id W)).pointMapHom = AddMonoidHom.id W.Point := by
    ext P
    simpa only [Hom.pointMapHom_apply, ← Hom.id_def, AddMonoidHom.id_apply] using
      Hom.id_pointMap P
  have hrange : (AddMonoidHom.id W.Point).range = ⊤ :=
    AddMonoidHom.range_eq_top.mpr Function.surjective_id
  simp [kummerRatio_def, h, hrange]

end TauCeti.Isogeny
