/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.BirchSwinnertonDyer.Quotient
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Isogeny.Finite
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.Regulator.Isogeny
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Cokernel

/-!
# The Birch–Swinnerton-Dyer quotient along an isogeny

Let `K` be a field with a theory of heights, and `E₁`, `E₂` elliptic curves over `K` whose
groups of rational points are finitely generated modulo torsion. Let `ψ : E₁ → E₂` be a separable
isogeny with separable dual `ψ̂`, and fix a family of field extensions of `K` along which
Shafarevich–Tate groups and Selmer groups are cut out. The descent sequences of `ψ` and `ψ̂` read

  `#Sel_ψ = [E₂(K) : ψ E₁(K)] · #Sha(E₁)[ψ]`,   `#Sel_ψ̂ = [E₁(K) : ψ̂ E₂(K)] · #Sha(E₂)[ψ̂]`,

and combined with the transformation of `Reg / #tors²` under `ψ`
(`TauCeti.Isogeny.Hom.regulator_div_card_torsion_sq_mul_index_dual_div_card_ker_eq`) they give

  `Reg(E₁) · #Sha(E₁)[ψ] / #E₁(K)_tors² · (#Sel_ψ̂ / #E₂(K)[ψ̂]) =
    (#Sel_ψ / #E₁(K)[ψ]) · Reg(E₂) · #Sha(E₂)[ψ̂] / #E₂(K)_tors²`.

If moreover `ψ` and `ψ̂` induce the zero map on Shafarevich–Tate groups, then `Sha(E₁)[ψ]` and
`Sha(E₂)[ψ̂]` are the whole groups `Sha(E₁)` and `Sha(E₂)`. When `Sha(E₂)` is finite, every
nonzero morphism `f : E₁ → E₂` has a multiple that is an isogeny killing Sha in both directions,
namely `ψ = #Sha(E₂) • f` (`TauCeti.Isogeny.Hom.exists_isogeny_shafarevichTateMap_eq_zero`). In
characteristic zero this `ψ` and its dual are separable, as every isogeny is.

Over `ℚ`, with `Sha` finite, this expresses the ratio of the Birch–Swinnerton-Dyer quotients of
`E₁` and `E₂` through `ψ`:

  `BSD(E₁) / BSD(E₂) = (#Sel_ψ / #Sel_ψ̂) / (#E₁(ℚ)[ψ] / #E₂(ℚ)[ψ̂]) ·
    (Ω(E₁) · ∏_p c_p(E₁)) / (Ω(E₂) · ∏_p c_p(E₂))`.

So Cassels' theorem that `BSD(E₁) = BSD(E₂)` is equivalent to the identity

  `#Sel_ψ / #Sel_ψ̂ = (#E₁(ℚ)[ψ] / #E₂(ℚ)[ψ̂]) · (Ω(E₂) · ∏_p c_p(E₂)) / (Ω(E₁) · ∏_p c_p(E₁))`

for this one isogeny `ψ`. This is the shape of Cassels' formula for the ratio of the orders of the
Selmer groups of an isogeny and its dual, once the product of its local factors is evaluated
through real periods and Tamagawa numbers. Working with `ψ` rather than with `f` brings in the
orders of the whole Shafarevich–Tate groups, and not only of their parts killed by `f` and `f̂`.

## Main results

* `regulator_mul_card_shafarevichTateGroupKer_div_card_torsion_sq_mul_card_selmerGroup_dual_eq`:
  the regulator, Sha-kernel and torsion factors along a separable isogeny.
* `regulator_mul_card_shafarevichTateGroup_div_card_torsion_sq_mul_card_selmerGroup_dual_eq`:
  the regulator, Sha and torsion factors along an isogeny that kills Sha in both directions.
* `TauCeti.Isogeny.bsdQuotient_div_bsdQuotient`: the ratio of Birch–Swinnerton-Dyer quotients over
  `ℚ` along such an isogeny.
* `TauCeti.Isogeny.Hom.exists_isogeny_bsdQuotient_div_bsdQuotient`: for every nonzero morphism
  over `ℚ`, the same ratio along the isogeny `#Sha(E₂) • f`.

## References

* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.4.
-/

public section

noncomputable section

namespace TauCeti.Isogeny

open Height WeierstrassCurve WeierstrassCurve.Affine TauCeti.ContCohomology
open Hom (ofIsogeny)

section Regulator

variable {F : Type*} [Field F] [DecidableEq F] [AdmissibleAbsValues F]
  {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
  [Module.Finite ℤ (PointModTorsion W₁.toAffine)] [Module.Finite ℤ (PointModTorsion W₂.toAffine)]
  {ι : Type*} {L : ι → Type*} [∀ i, Field (L i)] [∀ i, Algebra F (L i)]
  (τ : ∀ i, SeparableClosure F →ₐ[F] SeparableClosure (L i))
  (ψ : Isogeny W₁.toAffine W₂.toAffine)
  [Algebra.IsSeparable ψ.fieldPullback.fieldRange W₁.toAffine.FunctionField]
  [Algebra.IsSeparable ψ.dual.fieldPullback.fieldRange W₂.toAffine.FunctionField]

/-- **The regulator, Sha-kernel and torsion factors along an isogeny**: for a separable isogeny
`ψ : W₁ → W₂` with separable dual `ψ̂`,

  `Reg(W₁) · #Sha(W₁)[ψ] / #W₁(F)_tors² · (#Sel_ψ̂ / #W₂(F)[ψ̂]) =
    (#Sel_ψ / #W₁(F)[ψ]) · Reg(W₂) · #Sha(W₂)[ψ̂] / #W₂(F)_tors²`,

where `W₁(F)[ψ]` is the kernel of `ψ` on rational points and `Sha(W₁)[ψ]` its kernel on
Shafarevich–Tate groups. Orders are read as `0` when infinite. -/
theorem regulator_mul_card_shafarevichTateGroupKer_div_card_torsion_sq_mul_card_selmerGroup_dual_eq
    : regulator W₁.toAffine * Nat.card (ψ.shafarevichTateGroupKer τ) /
          Nat.card (AddCommGroup.torsion W₁.toAffine.Point) ^ 2 *
        (Nat.card (ψ.dual.selmerGroup τ) / Nat.card (ofIsogeny ψ.dual).pointMapHom.ker) =
      Nat.card (ψ.selmerGroup τ) / Nat.card (ofIsogeny ψ).pointMapHom.ker *
        (regulator W₂.toAffine * Nat.card (ψ.dual.shafarevichTateGroupKer τ) /
          Nat.card (AddCommGroup.torsion W₂.toAffine.Point) ^ 2) := by
  have h := Hom.regulator_div_card_torsion_sq_mul_index_dual_div_card_ker_eq
    (Hom.ofIsogeny_ne_zero ψ)
  rw [Hom.dual_ofIsogeny] at h
  rw [card_selmerGroup ψ τ, card_selmerGroup ψ.dual τ]
  push_cast
  linear_combination (Nat.card (ψ.shafarevichTateGroupKer τ) : ℝ) *
    Nat.card (ψ.dual.shafarevichTateGroupKer τ) * h

/-- **The regulator, Sha and torsion factors along an isogeny killing Sha**: if a separable
isogeny `ψ : W₁ → W₂` with separable dual `ψ̂` induces the zero map on Shafarevich–Tate groups, as
does `ψ̂`, then

  `Reg(W₁) · #Sha(W₁) / #W₁(F)_tors² · (#Sel_ψ̂ / #W₂(F)[ψ̂]) =
    (#Sel_ψ / #W₁(F)[ψ]) · Reg(W₂) · #Sha(W₂) / #W₂(F)_tors²`,

where `W₁(F)[ψ]` is the kernel of `ψ` on rational points. Orders are read as `0` when infinite. -/
theorem regulator_mul_card_shafarevichTateGroup_div_card_torsion_sq_mul_card_selmerGroup_dual_eq
    (h₁ : (ofIsogeny ψ).shafarevichTateMap τ = 0)
    (h₂ : (ofIsogeny ψ.dual).shafarevichTateMap τ = 0) :
    regulator W₁.toAffine * Nat.card (W₁.shafarevichTateGroup τ) /
          Nat.card (AddCommGroup.torsion W₁.toAffine.Point) ^ 2 *
        (Nat.card (ψ.dual.selmerGroup τ) / Nat.card (ofIsogeny ψ.dual).pointMapHom.ker) =
      Nat.card (ψ.selmerGroup τ) / Nat.card (ofIsogeny ψ).pointMapHom.ker *
        (regulator W₂.toAffine * Nat.card (W₂.shafarevichTateGroup τ) /
          Nat.card (AddCommGroup.torsion W₂.toAffine.Point) ^ 2) := by
  have h :=
    regulator_mul_card_shafarevichTateGroupKer_div_card_torsion_sq_mul_card_selmerGroup_dual_eq τ ψ
  rwa [shafarevichTateGroupKer_eq_ker_shafarevichTateMap,
    shafarevichTateGroupKer_eq_ker_shafarevichTateMap, AddMonoidHom.ker_eq_top_iff.2 h₁,
    AddMonoidHom.ker_eq_top_iff.2 h₂, AddSubgroup.card_top, AddSubgroup.card_top] at h

end Regulator

section Rat

variable {E₁ E₂ : WeierstrassCurve ℚ} [E₁.IsElliptic] [E₂.IsElliptic] [Finite E₁.sha]
  [Finite E₂.sha]
  (τ : ∀ v : GlobalNumberFields.Place ℚ, SeparableClosure ℚ →ₐ[ℚ] SeparableClosure v.Completion)

/-- **The ratio of Birch–Swinnerton-Dyer quotients along an isogeny killing Sha**: let `E₁` and
`E₂` be elliptic curves over `ℚ` with finite Shafarevich–Tate groups. If an isogeny
`ψ : E₁ → E₂` and its dual `ψ̂` induce the zero map on Shafarevich–Tate groups, then

  `BSD(E₁) / BSD(E₂) = (#Sel_ψ / #Sel_ψ̂) / (#E₁(ℚ)[ψ] / #E₂(ℚ)[ψ̂]) ·
    (Ω(E₁) · ∏_p c_p(E₁)) / (Ω(E₂) · ∏_p c_p(E₂))`,

with `Ω` the real period of a global minimal equation and `c_p` the local Tamagawa numbers. The
Selmer groups are cut out at every place of `ℚ`. -/
theorem bsdQuotient_div_bsdQuotient (ψ : Isogeny E₁.toAffine E₂.toAffine)
    (h₁ : (ofIsogeny ψ).shafarevichTateMap τ = 0)
    (h₂ : (ofIsogeny ψ.dual).shafarevichTateMap τ = 0) :
    E₁.bsdQuotient / E₂.bsdQuotient =
      (Nat.card (ψ.selmerGroup τ) / Nat.card (ψ.dual.selmerGroup τ)) /
          (Nat.card (ofIsogeny ψ).pointMapHom.ker / Nat.card (ofIsogeny ψ.dual).pointMapHom.ker) *
        (E₁.minimalRealPeriod * E₁.tamagawaProduct (R := ℤ) /
          (E₂.minimalRealPeriod * E₂.tamagawaProduct (R := ℤ))) := by
  have h :=
    regulator_mul_card_shafarevichTateGroup_div_card_torsion_sq_mul_card_selmerGroup_dual_eq
      τ ψ h₁ h₂
  rw [← E₁.sha_eq_shafarevichTateGroup τ, ← E₂.sha_eq_shafarevichTateGroup τ] at h
  -- every factor is positive, so the identity can be cleared of denominators
  have := ψ.finite_selmerGroup_place τ
  have := ψ.dual.finite_selmerGroup_place τ
  have := (ofIsogeny ψ).finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero ψ)
  have := (ofIsogeny ψ.dual).finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero ψ.dual)
  have := finite_torsion (W := E₁.toAffine)
  have := finite_torsion (W := E₂.toAffine)
  have := E₁.minimalRealPeriod_pos
  have := E₂.minimalRealPeriod_pos
  have := E₁.tamagawaProduct_pos (R := ℤ)
  have := E₂.tamagawaProduct_pos (R := ℤ)
  have := E₂.toAffine.regulator_pos
  have : 0 < Nat.card E₁.sha := Nat.card_pos
  have : 0 < Nat.card E₂.sha := Nat.card_pos
  have : 0 < Nat.card (ψ.selmerGroup τ) := Nat.card_pos
  have : 0 < Nat.card (ψ.dual.selmerGroup τ) := Nat.card_pos
  have : 0 < Nat.card (ofIsogeny ψ).pointMapHom.ker := Nat.card_pos
  have : 0 < Nat.card (ofIsogeny ψ.dual).pointMapHom.ker := Nat.card_pos
  have : 0 < Nat.card (AddCommGroup.torsion E₁.toAffine.Point) := Nat.card_pos
  have : 0 < Nat.card (AddCommGroup.torsion E₂.toAffine.Point) := Nat.card_pos
  rw [bsdQuotient_def, bsdQuotient_def, div_eq_iff (by positivity)]
  field_simp at h ⊢
  linear_combination h

/-- **The ratio of Birch–Swinnerton-Dyer quotients along an isogeny**: let `E₁` and `E₂` be
elliptic curves over `ℚ` with finite Shafarevich–Tate groups. For every nonzero morphism
`f : E₁ → E₂`, the multiple `ψ = #Sha(E₂) • f` is an isogeny along which

  `BSD(E₁) / BSD(E₂) = (#Sel_ψ / #Sel_ψ̂) / (#E₁(ℚ)[ψ] / #E₂(ℚ)[ψ̂]) ·
    (Ω(E₁) · ∏_p c_p(E₁)) / (Ω(E₂) · ∏_p c_p(E₂))`.

So `BSD(E₁) = BSD(E₂)` holds exactly when

  `#Sel_ψ / #Sel_ψ̂ = (#E₁(ℚ)[ψ] / #E₂(ℚ)[ψ̂]) · (Ω(E₂) · ∏_p c_p(E₂)) / (Ω(E₁) · ∏_p c_p(E₁))`. -/
theorem Hom.exists_isogeny_bsdQuotient_div_bsdQuotient {f : Hom E₁.toAffine E₂.toAffine}
    (hf : f ≠ 0) :
    ∃ ψ : Isogeny E₁.toAffine E₂.toAffine, ofIsogeny ψ = Nat.card E₂.sha • f ∧
      E₁.bsdQuotient / E₂.bsdQuotient =
        (Nat.card (ψ.selmerGroup τ) / Nat.card (ψ.dual.selmerGroup τ)) /
            (Nat.card (ofIsogeny ψ).pointMapHom.ker /
              Nat.card (ofIsogeny ψ.dual).pointMapHom.ker) *
          (E₁.minimalRealPeriod * E₁.tamagawaProduct (R := ℤ) /
            (E₂.minimalRealPeriod * E₂.tamagawaProduct (R := ℤ))) := by
  have : Finite (E₂.shafarevichTateGroup τ) := by rwa [← E₂.sha_eq_shafarevichTateGroup τ]
  obtain ⟨ψ, hψ, h₁, h₂⟩ := f.exists_isogeny_shafarevichTateMap_eq_zero τ hf
  rw [← E₂.sha_eq_shafarevichTateGroup τ] at hψ
  exact ⟨ψ, hψ, bsdQuotient_div_bsdQuotient τ ψ h₁ h₂⟩

end Rat

end TauCeti.Isogeny
