/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.QuotientRing
public import TauCeti.AlgebraicTopology.Singular.MappingTorus.BaseCircle

/-!
# `H₁` of a mapping torus whose monodromy reverses a circle

In degree one the Wang sequence of the mapping torus `T_φ` of a homeomorphism `φ` of a
path-connected space `F` is the short exact sequence

`0 ⟶ H₁(F) ⧸ (𝟙 - φ_*) ⟶ H₁(T_φ) ⟶ H₀(F) ⟶ 0`

(`TauCeti.MappingTorus.wangCokernelShortComplex_shortExact`). When `φ` acts by `-1` on
`H₁(F; ℤ) ≃ ℤ`, the cokernel of `𝟙 - φ_* = 2` is `ℤ/2`, and the sequence splits because
`H₀(F; ℤ) ≃ ℤ` is free, so `H₁(T_φ; ℤ) ≃ ℤ × ℤ/2`
(`TauCeti.MappingTorus.homologyOneLinearEquivOfNeg`). The splitting is fixed by a class
`x₀ ∈ H₁(T_φ; ℤ)` of Wang class `1`, which goes to `(1, 0)`
(`TauCeti.MappingTorus.homologyOneLinearEquivOfNeg_self`). The `ℤ` coordinate is the Wang class
`ε ∘ δ : H₁(T_φ) → ℤ` (`TauCeti.MappingTorus.homologyOneLinearEquivOfNeg_apply_fst`), and the
image of `y ∈ H₁(F)` under the fibre inclusion goes to `(0, e y mod 2)`
(`TauCeti.MappingTorus.homologyOneLinearEquivOfNeg_homologyMap_fibreInclusionChainMap`).

The basic example is the Klein bottle, the mapping torus of complex conjugation of the unit
circle.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2: Example 2.48 for the Wang sequence of a mapping
  torus.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology HomologicalComplex

namespace TauCeti

namespace MappingTorus

variable {F : Type} [TopologicalSpace F] (φ : F ≃ₜ F)
  (e : (((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of F)).homology 1 ≃ₗ[ℤ] ℤ)
  (hφ : homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1 = -𝟙 _)

include hφ in
/-- If `φ` acts by `-1` on `H₁(F; ℤ) ≃ ℤ`, the image of `𝟙 - φ_*` corresponds to the even
integers. -/
private theorem map_range_id_sub_homologyMap_monodromyChainMap_of_neg :
    (LinearMap.range (LinearMap.id -
        (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom)).map (e : _ →ₗ[ℤ] ℤ) =
      Ideal.span {((2 : ℕ) : ℤ)} := by
  rw [hφ]
  ext x
  simp only [ModuleCat.hom_neg, ModuleCat.hom_id, sub_neg_eq_add, Submodule.mem_map,
    LinearMap.mem_range, LinearMap.add_apply, LinearMap.id_apply, Nat.cast_ofNat,
    Ideal.mem_span_singleton]
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨e y, by simp [two_mul]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨_, ⟨e.symm y, rfl⟩, by simp [two_mul]⟩

include hφ in
/-- The cokernel of `𝟙 - φ_*` on `H₁(F; ℤ) ≃ ℤ`, the first term of the Wang short complex in degree
one, is `ℤ/2` when `φ` acts by `-1`. -/
private def wangCokernelAddEquivOfNeg :
    (wangCokernelShortComplex (k := ℤ) φ 0).X₁ ≃+ ZMod 2 :=
  (AddEquivClass.toAddEquiv (Submodule.Quotient.equiv _ _ e
    (map_range_id_sub_homologyMap_monodromyChainMap_of_neg φ e hφ))).trans
    (Int.quotientSpanNatEquivZMod 2).toAddEquiv

include hφ in
/-- The class of `y` in the cokernel of `𝟙 - φ_*` corresponds to `e y mod 2`. -/
private theorem wangCokernelAddEquivOfNeg_mk (y) :
    wangCokernelAddEquivOfNeg φ e hφ (Submodule.Quotient.mk y) = (e y : ZMod 2) :=
  rfl

variable [PathConnectedSpace F]

/-- The Wang sequence `H₁(F) ⧸ (𝟙 - φ_*) → H₁(T_φ) → H₀(F)` of a mapping torus with path-connected
fibre, as an exact sequence of linear maps. -/
private theorem exact_wangCokernelShortComplex_zero :
    Function.Exact (wangCokernelShortComplex (k := ℤ) φ 0).f.hom
      (wangCokernelShortComplex (k := ℤ) φ 0).g.hom :=
  LinearMap.exact_iff.2
    (wangCokernelShortComplex_shortExact (k := ℤ) φ 0).exact.moduleCat_range_eq_ker.symm

variable (x₀ : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of (MappingTorus φ)))
  (hx₀ : (wangClass (ModuleCat.of ℤ ℤ) φ).hom x₀ = 1)

/-- The map `H₀(F; ℤ) → H₁(T_φ; ℤ)`, `h ↦ ε h • x₀`, through the augmentation `ε`. -/
private def wangSection :
    (wangCokernelShortComplex (k := ℤ) φ 0).X₃ →ₗ[ℤ] (wangCokernelShortComplex (k := ℤ) φ 0).X₂ :=
  LinearMap.toSpanSingleton ℤ _ x₀ ∘ₗ ((TopCat.of F).singularHomology₀ε (ModuleCat.of ℤ ℤ)).hom

omit [PathConnectedSpace F] in
include hx₀ in
/-- The Wang connecting morphism sends `x₀` to a class of augmentation `1`. -/
private theorem singularHomology₀ε_wangδ_self :
    ((TopCat.of F).singularHomology₀ε (ModuleCat.of ℤ ℤ)).hom
      ((wangCokernelShortComplex (k := ℤ) φ 0).g.hom x₀) = 1 :=
  (wangClass_hom_apply φ (ModuleCat.of ℤ ℤ) x₀).symm.trans hx₀

include hx₀ in
/-- A class `x₀` of Wang class `1` spans a section `h ↦ ε h • x₀` of the Wang connecting morphism
`H₁(T_φ; ℤ) → H₀(F; ℤ) ≃ ℤ`. -/
private theorem wangδ_comp_wangSection :
    (wangCokernelShortComplex (k := ℤ) φ 0).g.hom ∘ₗ wangSection φ x₀ = LinearMap.id := by
  -- On `ℤ`, the map `n ↦ ε (δ (n • x₀))` is the identity, since it sends `1` to `ε (δ x₀) = 1`.
  have key : ((TopCat.of F).singularHomology₀ε (ModuleCat.of ℤ ℤ)).hom ∘ₗ
      (wangCokernelShortComplex (k := ℤ) φ 0).g.hom ∘ₗ
        LinearMap.toSpanSingleton ℤ (wangCokernelShortComplex (k := ℤ) φ 0).X₂ x₀ = LinearMap.id :=
    LinearMap.ext_ring <| (congrArg _ (congrArg _ (LinearMap.toSpanSingleton_apply_one ℤ
      (wangCokernelShortComplex (k := ℤ) φ 0).X₂ x₀))).trans
        (singularHomology₀ε_wangδ_self φ x₀ hx₀)
  exact LinearMap.ext fun h ↦ ((ModuleCat.mono_iff_injective
    ((TopCat.of F).singularHomology₀ε (ModuleCat.of ℤ ℤ))).1 inferInstance)
    (LinearMap.congr_fun key _)

/-- The splitting `H₁(T_φ; ℤ) ≃ (H₁(F) ⧸ (𝟙 - φ_*)) × H₀(F)` of the Wang sequence given by the
section `h ↦ ε h • x₀`. -/
private def wangSplitting :=
  (exact_wangCokernelShortComplex_zero φ).splitSurjectiveEquiv
    (wangCokernelShortComplex_shortExact (k := ℤ) φ 0).moduleCat_injective_f
    ⟨_, wangδ_comp_wangSection φ x₀ hx₀⟩

/-- The splitting of the Wang sequence sends `x₀` into the summand `H₀(F)`. -/
private theorem wangSplitting_self_fst : ((wangSplitting φ x₀ hx₀).val x₀).1 = 0 := by
  -- The inverse of the splitting is `(a, b) ↦ f a + wangSection b`, and `x₀` is the image of
  -- `δ x₀` under `wangSection`.
  have hl := LinearMap.congr_fun (congrArg Subtype.val
    (((exact_wangCokernelShortComplex_zero φ).splitSurjectiveEquiv
      (wangCokernelShortComplex_shortExact (k := ℤ) φ 0).moduleCat_injective_f).symm_apply_apply
        ⟨_, wangδ_comp_wangSection φ x₀ hx₀⟩)) ((wangCokernelShortComplex (k := ℤ) φ 0).g.hom x₀)
  have hx : (wangSplitting φ x₀ hx₀).val.symm (0, (wangCokernelShortComplex (k := ℤ) φ 0).g.hom x₀)
      = x₀ :=
    hl.trans <| (congrArg
      (LinearMap.toSpanSingleton ℤ (wangCokernelShortComplex (k := ℤ) φ 0).X₂ x₀)
        (singularHomology₀ε_wangδ_self φ x₀ hx₀)).trans
      (LinearMap.toSpanSingleton_apply_one ℤ (wangCokernelShortComplex (k := ℤ) φ 0).X₂ x₀)
  exact (congrArg (fun y ↦ ((wangSplitting φ x₀ hx₀).val y).1) hx).symm.trans
    (congrArg Prod.fst (LinearEquiv.apply_symm_apply _ _))

include e hφ hx₀ in
/-- **`H₁` of a mapping torus whose monodromy reverses a circle.** If `F` is path-connected,
`H₁(F; ℤ) ≃ ℤ` and `φ` acts on it by `-1`, then `H₁(T_φ; ℤ) ≃ ℤ × ℤ/2`. The equivalence splits the
Wang sequence along a class `x₀ ∈ H₁(T_φ; ℤ)` of Wang class `1`, which it sends to `(1, 0)`
(`TauCeti.MappingTorus.homologyOneLinearEquivOfNeg_self`). Its `ℤ` coordinate is the Wang class
(`TauCeti.MappingTorus.homologyOneLinearEquivOfNeg_apply_fst`) and the fibre classes map to
`0 × ℤ/2`
(`TauCeti.MappingTorus.homologyOneLinearEquivOfNeg_homologyMap_fibreInclusionChainMap`), so these
three properties determine it. -/
def homologyOneLinearEquivOfNeg :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of (MappingTorus φ)) ≃ₗ[ℤ] ℤ × ZMod 2 :=
  let s : _ ≃+ ℤ × ZMod 2 :=
    (AddEquivClass.toAddEquiv (wangSplitting φ x₀ hx₀).val).trans
      (((wangCokernelAddEquivOfNeg φ e hφ).prodCongr (AddEquivClass.toAddEquiv
        (asIso ((TopCat.of F).singularHomology₀ε (ModuleCat.of ℤ ℤ))).toLinearEquiv)).trans
        AddEquiv.prodComm)
  s.toLinearEquiv fun c x ↦ by
    -- the two `ℤ`-module structures on the target agree with its `ℤ`-multiplication `zsmul`
    convert map_zsmul s c x using 2
    exact int_smul_eq_zsmul _ _ _

include e hφ hx₀ in
/-- `TauCeti.MappingTorus.homologyOneLinearEquivOfNeg` is the splitting of the Wang sequence,
followed by `ℤ/2` on the cokernel of `𝟙 - φ_*` and the augmentation on `H₀(F)`. -/
private theorem homologyOneLinearEquivOfNeg_apply (x) :
    homologyOneLinearEquivOfNeg φ e hφ x₀ hx₀ x =
      ((TopCat.of F).singularHomology₀ε (ModuleCat.of ℤ ℤ) ((wangSplitting φ x₀ hx₀).val x).2,
        wangCokernelAddEquivOfNeg φ e hφ ((wangSplitting φ x₀ hx₀).val x).1) :=
  rfl

include e hφ hx₀ in
/-- The `ℤ` coordinate of `TauCeti.MappingTorus.homologyOneLinearEquivOfNeg` is the Wang class
`ε ∘ δ : H₁(T_φ; ℤ) → ℤ`. -/
@[simp]
theorem homologyOneLinearEquivOfNeg_apply_fst (x) :
    (homologyOneLinearEquivOfNeg φ e hφ x₀ hx₀ x).1 = (wangClass (ModuleCat.of ℤ ℤ) φ).hom x := by
  have : ((wangSplitting φ x₀ hx₀).val x).2 = wangδ φ (ModuleCat.of ℤ ℤ) 0 x :=
    (LinearMap.congr_fun (wangSplitting φ x₀ hx₀).property.2 x).symm
  rw [homologyOneLinearEquivOfNeg_apply, this, wangClass_hom_apply]

include e hφ in
/-- `TauCeti.MappingTorus.homologyOneLinearEquivOfNeg` sends the class `x₀` along which it splits
the Wang sequence to `(1, 0)`. -/
@[simp]
theorem homologyOneLinearEquivOfNeg_self : homologyOneLinearEquivOfNeg φ e hφ x₀ hx₀ x₀ = (1, 0) :=
  Prod.ext ((homologyOneLinearEquivOfNeg_apply_fst φ e hφ x₀ hx₀ x₀).trans hx₀) <|
    (congrArg (wangCokernelAddEquivOfNeg φ e hφ) (wangSplitting_self_fst φ x₀ hx₀)).trans
      (map_zero _)

include hφ hx₀ in
/-- `TauCeti.MappingTorus.homologyOneLinearEquivOfNeg` sends the image of `y ∈ H₁(F; ℤ)` under the
fibre inclusion to `(0, e y mod 2)`. -/
@[simp]
theorem homologyOneLinearEquivOfNeg_homologyMap_fibreInclusionChainMap (y) :
    homologyOneLinearEquivOfNeg φ e hφ x₀ hx₀
        (homologyMap (fibreInclusionChainMap φ (ModuleCat.of ℤ ℤ)) 1 y) = (0, (e y : ZMod 2)) := by
  have : (wangSplitting φ x₀ hx₀).val
      (homologyMap (fibreInclusionChainMap φ (ModuleCat.of ℤ ℤ)) 1 y) =
        (Submodule.Quotient.mk y, 0) := by
    have h := LinearMap.congr_fun (wangSplitting φ x₀ hx₀).property.1 (Submodule.Quotient.mk y)
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe,
      wangCokernelShortComplex_f_mk] at h
    rw [h]
    exact LinearEquiv.apply_symm_apply _ _
  -- The argument lies in the homology of the singular chain complex, the source of
  -- `homologyOneLinearEquivOfNeg` only by unfolding `singularHomologyFunctor`.
  refine (homologyOneLinearEquivOfNeg_apply φ e hφ x₀ hx₀ _).trans ?_
  rw [this, wangCokernelAddEquivOfNeg_mk]
  exact Prod.ext (map_zero _) rfl

end MappingTorus

end TauCeti
