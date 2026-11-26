/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import TauCeti.Algebra.Category.ModuleCat.SpanSingleton
public import TauCeti.Algebra.Homology.Ext.Presentation
public import TauCeti.RingTheory.Regular.Category

/-!
# `Ext` out of the quotient by a regular element

Let `f` be an element of a commutative ring `R` that is regular on `R`, that is, not a zero
divisor. Multiplication by `f` gives the free resolution `0 → R → R → R ⧸ f R → 0`
(`ModuleCat.smulShortComplex`), so for every `R`-module `X`, `Ext(R ⧸ f R, X)` is computed by the
two-term complex `X → X` of multiplication by `f`:

* `Ext¹(R ⧸ f R, X) ≃ X ⧸ f X` (`ModuleCat.extOneQuotSMulTopEquiv`), naturally in `X`
  (`ModuleCat.extOneQuotSMulTopEquiv_comp_mk₀`);
* `Extⁿ(R ⧸ f R, X) = 0` for `n ≥ 2` (`ModuleCat.ext_quotSMulTop_add_two_eq_zero`).

The class of `x ∈ X` corresponds to the extension class of the resolution pushed forward along
`R → X`, `r ↦ r • x` (`ModuleCat.extOneQuotSMulTopEquiv_symm_mk`). Over `ℤ` and with `f = n ≠ 0`,
this is `Ext¹(ℤ ⧸ n, ℤ) ≃ ℤ ⧸ n`, the computation behind the `Ext` term of the universal
coefficient theorem for groups with cyclic torsion.

## Main results

* `ModuleCat.extOneQuotSMulTopEquiv`: `Ext¹(R ⧸ f R, X) ≃ₗ[R] X ⧸ f X` for `f` regular on `R`.
* `ModuleCat.extOneQuotSMulTopEquiv_comp_mk₀`: its naturality in `X`.
* `ModuleCat.ext_quotSMulTop_add_two_eq_zero`: `Extⁿ⁺²(R ⧸ f R, X) = 0` for `f` regular on `R`.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Section 3.3 (`Ext` from a projective
  presentation).
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Abelian Pointwise

universe u

namespace ModuleCat

variable {R : Type u} [CommRing R] {f : R}

/-- Under evaluation at `1`, the maps `R → X` that factor through multiplication by `f` are the
elements of `f X`. -/
private theorem map_homSelfLinearEquiv_range (X : ModuleCat.{u} R) (f : R) :
    (Linear.leftComp R X (smulShortComplex (of R R) f).f).range.map
        (homSelfLinearEquiv R X).toLinearMap = f • (⊤ : Submodule R X) := by
  have key (g : of R R ⟶ X) :
      homSelfLinearEquiv R X ((f • 𝟙 (of R R)) ≫ g) = f • homSelfLinearEquiv R X g := by
    rw [Linear.smul_comp, Category.id_comp, map_smul]
  ext x
  simp only [Submodule.mem_map, LinearMap.mem_range, Linear.leftComp_apply,
    smulShortComplex_f_eq_smul_id, LinearEquiv.coe_coe, Submodule.mem_smul_pointwise_iff_exists,
    Submodule.mem_top, true_and]
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨homSelfLinearEquiv R X g, (key g).symm⟩
  · rintro ⟨y, rfl⟩
    exact ⟨_, ⟨(homSelfLinearEquiv R X).symm y, rfl⟩, by rw [key, LinearEquiv.apply_symm_apply]⟩

/-- **`Ext¹` against `R ⧸ f R`.** For an element `f` of `R` regular on `R`, `Ext¹(R ⧸ f R, X)` is
`X ⧸ f X`. The class of `x` is the extension class of `0 → R → R → R ⧸ f R → 0` pushed forward
along `r ↦ r • x` (`ModuleCat.extOneQuotSMulTopEquiv_symm_mk`). -/
def extOneQuotSMulTopEquiv (hf : IsSMulRegular R f) (X : ModuleCat.{u} R) :
    Ext.{u} (of R (QuotSMulTop f R)) X 1 ≃ₗ[R] QuotSMulTop f X :=
  (TauCeti.homCokernelEquivExt R (hf.smulShortComplex_shortExact (M := of R R)) X).symm.trans
    (Submodule.Quotient.equiv _ _ (homSelfLinearEquiv R X) (map_homSelfLinearEquiv_range X f))

/-- `ModuleCat.extOneQuotSMulTopEquiv` sends the extension class of `0 → R → R → R ⧸ f R → 0`
pushed forward along `g : R → X` to the class of `g 1`. -/
@[simp]
theorem extOneQuotSMulTopEquiv_extClass_comp (hf : IsSMulRegular R f) {X : ModuleCat.{u} R}
    (g : of R R ⟶ X) :
    extOneQuotSMulTopEquiv hf X
        ((hf.smulShortComplex_shortExact (M := of R R)).extClass.comp (Ext.mk₀ g) (add_zero 1)) =
      Submodule.Quotient.mk (g.hom 1) := by
  -- `simp` does not find `homCokernelEquivExt_symm_comp_mk₀` here, as the goal writes the terms
  -- of `smulShortComplex (of R R) f` as `of R R`; unfolding `smulShortComplex` makes the
  -- remaining quotient classes match.
  rw [extOneQuotSMulTopEquiv, LinearEquiv.trans_apply, TauCeti.homCokernelEquivExt_symm_comp_mk₀]
  simp [smulShortComplex]

/-- The inverse of `ModuleCat.extOneQuotSMulTopEquiv` sends the class of `x` to the extension
class of `0 → R → R → R ⧸ f R → 0` pushed forward along `r ↦ r • x`. -/
theorem extOneQuotSMulTopEquiv_symm_mk (hf : IsSMulRegular R f) (X : ModuleCat.{u} R) (x : X) :
    (extOneQuotSMulTopEquiv hf X).symm (Submodule.Quotient.mk x) =
      (hf.smulShortComplex_shortExact (M := of R R)).extClass.comp
        (Ext.mk₀ (ofHom (LinearMap.toSpanSingleton R X x))) (add_zero 1) := by
  rw [LinearEquiv.symm_apply_eq, extOneQuotSMulTopEquiv_extClass_comp]
  simp

/-- **Naturality.** The identification `Ext¹(R ⧸ f R, X) ≃ X ⧸ f X` is natural in `X`: a map
`g : X ⟶ Y` acts on `Ext¹` by postcomposition and on `X ⧸ f X` by `QuotSMulTop.map`. -/
theorem extOneQuotSMulTopEquiv_comp_mk₀ (hf : IsSMulRegular R f) {X Y : ModuleCat.{u} R}
    (g : X ⟶ Y) (e : Ext.{u} (of R (QuotSMulTop f R)) X 1) :
    extOneQuotSMulTopEquiv hf Y (e.comp (Ext.mk₀ g) (add_zero 1)) =
      QuotSMulTop.map f g.hom (extOneQuotSMulTopEquiv hf X e) := by
  obtain ⟨y, rfl⟩ := (extOneQuotSMulTopEquiv hf X).symm.surjective e
  induction y using Submodule.Quotient.induction_on with
  | _ x =>
    simp [extOneQuotSMulTopEquiv_symm_mk, Ext.comp_assoc_of_second_deg_zero]

/-- **Vanishing of higher `Ext`.** For an element `f` of `R` regular on `R`,
`Extⁿ(R ⧸ f R, X) = 0` for `n ≥ 2`. -/
theorem ext_quotSMulTop_add_two_eq_zero (hf : IsSMulRegular R f) (X : ModuleCat.{u} R) (n : ℕ)
    (e : Ext.{u} (of R (QuotSMulTop f R)) X (n + 2)) : e = 0 :=
  (hf.smulShortComplex_shortExact (M := of R R)).ext_X₃_eq_zero_of_ext_X₁_eq_zero
    (fun _ ↦ Ext.eq_zero_of_projective _) e

end ModuleCat
