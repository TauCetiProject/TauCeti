/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.LinearAlgebra.Complex.Determinant
public import TauCeti.AlgebraicTopology.Singular.MappingTorus.BaseCircle
public import TauCeti.AlgebraicTopology.Singular.Sphere
public import TauCeti.Geometry.Manifold.Instances.KleinBottle

/-!
# The integral homology of the Klein bottle

The Klein bottle `K` (`TauCeti.KleinBottle`) is the mapping torus of complex conjugation of the unit
circle `S¹ ⊆ ℂ`, a reflection, which acts by `-1` on `H₁(S¹; ℤ) ≃ ℤ`. This file computes its
integral homology from the Wang sequence of the mapping torus:

* `H₀(K; ℤ) ≃ ℤ` (`TauCeti.KleinBottle.singularHomologyZeroLinearEquiv`);
* `H₁(K; ℤ) ≃ ℤ × ℤ/2` (`TauCeti.KleinBottle.singularHomologyOneLinearEquiv`);
* `Hₖ(K; ℤ) = 0` for `k ≥ 2` (`TauCeti.KleinBottle.isZero_singularHomology_of_two_le`).

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
(`TauCeti.MappingTorus.homologyOneLinearEquivOfNeg_homologyMap_fibreInclusionChainMap`). For the
Klein bottle, `x₀` comes from the closed orbit `t ↦ [t, 1]` through the fixed point `1` of
conjugation, so the equivalence involves no choice. Loops `t ↦ [t, 1]` land in the free summand
`ℤ × 0`
(`TauCeti.KleinBottle.singularHomologyOneLinearEquiv_singularHomologyMap_of_apply_eq_mk_one`).
The `ℤ` coordinate of a class is the Wang class of its projection to the base circle
(`TauCeti.KleinBottle.singularHomologyOneLinearEquiv_apply_fst`). The fibre circle carries the
torsion summand `0 × ℤ/2` (`TauCeti.KleinBottle.map_range_singularHomologyMap_mk_zero`): a class of
`H₁(S¹; ℤ) ≅ ℤ` with value `n` goes to `(0, n mod 2)`
(`TauCeti.KleinBottle.singularHomologyOneLinearEquiv_singularHomologyMap_mk_zero`).

In degree two, `𝟙 - φ_*` is injective on `H₁(S¹; ℤ)`, so the Wang connecting morphism vanishes and
`H₂(K; ℤ)` is a quotient of `H₂(S¹; ℤ) = 0`.

For the torus, the mapping torus of the identity, `𝟙 - φ_*` vanishes and `H₁ = ℤ²`; the summand
`ℤ/2` of the Klein bottle is the cokernel of `𝟙 - φ_* = 2`. These groups are the target of the
comparison with the Morse–Bott complex of the height function `[t, z] ↦ Re z` on `K`
(`TauCeti.KleinBottle.height`), whose critical circle of index one has a nonorientable negative
normal line.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2: Example 2.37 for the homology of the Klein bottle
  and Example 2.48 for the Wang sequence of a mapping torus.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology HomologicalComplex Metric

universe v u

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

namespace KleinBottle

attribute [local instance] finrank_real_complex_fact'

/-- Complex conjugation acts by `-1` on `H₁(S¹)`: the monodromy of the Klein bottle, as the
topological mapping torus `TauCeti.SmoothMappingTorus.homeomorphMappingTorus`, reverses the
orientation of the fibre circle. -/
theorem homologyMap_monodromyChainMap_one_eq_neg {A : Type u} [Category.{v} A]
    [HasCoproducts.{0} A] [Abelian A] (R : A) :
    homologyMap (MappingTorus.monodromyChainMap conjCircleDiffeomorph.toHomeomorph.symm R) 1 =
      -𝟙 _ := by
  have h : (TopCat.ofHom ⟨conjCircleDiffeomorph.toHomeomorph.symm,
      conjCircleDiffeomorph.toHomeomorph.symm.continuous⟩ : TopCat.of (sphere (0 : ℂ) 1) ⟶ _) =
      TopCat.ofHom ⟨Complex.conjLIE.toLinearIsometry.unitSphereMap,
        Complex.conjLIE.toLinearIsometry.continuous_unitSphereMap⟩ := by
    ext z
    simp
  have hdet : LinearMap.det Complex.conjLIE.toLinearIsometry.toLinearMap = -1 := by
    have : Complex.conjLIE.toLinearIsometry.toLinearMap =
        Complex.conjAe.toLinearEquiv.toLinearMap :=
      LinearMap.ext fun z ↦ by simp
    rw [this, Complex.det_conjAe]
  rw [MappingTorus.monodromyChainMap_def, h, ← singularHomologyFunctor_obj_map_eq_homologyMap,
    singularHomologyFunctor_map_unitSphereMap R (n := 0) Complex.finrank_real_complex, hdet,
    sign_neg neg_one_lt_zero, SignType.coe_neg_one, neg_one_zsmul]
  -- The two sides are `-𝟙` of the singular homology object and of the homology of the singular
  -- chain complex. These objects agree by unfolding `singularHomologyFunctor`, an identification
  -- of objects rather than morphisms, so no rewrite closes the goal.
  rfl

/-- `H₁(S¹; ℤ) ≃ ℤ` for the unit circle of `ℂ`. -/
private def circleHomologyOneLinearEquiv :
    (((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of (sphere (0 : ℂ) 1))).homology 1 ≃ₗ[ℤ] ℤ :=
  ((ContinuousMap.HomotopyEquiv.refl _).singularHomologySphereIso (ModuleCat.of ℤ ℤ)
    Complex.finrank_real_complex le_rfl).toLinearEquiv

/-- The Klein bottle as the topological mapping torus, as an isomorphism in `TopCat`. -/
private def isoMappingTorus :
    TopCat.of KleinBottle ≅ TopCat.of (MappingTorus conjCircleDiffeomorph.toHomeomorph.symm) :=
  TopCat.isoOfHomeo (SmoothMappingTorus.homeomorphMappingTorus conjCircleDiffeomorph)

/-- The loop `t ↦ [1, t]` of the topological mapping torus through the point `1`, which
conjugation fixes, read on the circle `ℝ/ℤ` as the mapping torus of the identity of a point. -/
private def baseLoop : C(UnitAddCircle, MappingTorus conjCircleDiffeomorph.toHomeomorph.symm) :=
  (MappingTorus.map (Homeomorph.refl PUnit.{1}) _ (ContinuousMap.const _ 1) fun _ ↦
    (conjCircleDiffeomorph.toHomeomorph.symm_apply_eq.2 conjCircleDiffeomorph_one.symm).symm).comp
    MappingTorus.projPUnitHomeomorph.symm

/-- The loop through `1` sends `t` to `[1, t]`. -/
private theorem baseLoop_coe (t : ℝ) :
    baseLoop t = MappingTorus.mk conjCircleDiffeomorph.toHomeomorph.symm 1 t := by
  have : MappingTorus.projPUnitHomeomorph.symm (t : UnitAddCircle) =
      MappingTorus.mk _ PUnit.unit t :=
    MappingTorus.projPUnitHomeomorph.symm_apply_eq.2 (by simp)
  simp [baseLoop, this]

/-- The loop through `1` is a section of the projection to the base circle. -/
private theorem baseLoop_comp_proj :
    TopCat.ofHom baseLoop ≫ TopCat.ofHom ⟨MappingTorus.proj _,
      MappingTorus.continuous_proj conjCircleDiffeomorph.toHomeomorph.symm⟩ = 𝟙 _ :=
  ConcreteCategory.hom_ext _ _ fun θ ↦ by
    induction θ using QuotientAddGroup.induction_on with
    | H t => simp [baseLoop_coe]

/-- The class of the loop through `1` whose projection to the base circle has Wang class `1`. -/
private def baseLoopClass :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of (MappingTorus conjCircleDiffeomorph.toHomeomorph.symm)) :=
  (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)).map
    (TopCat.ofHom baseLoop)).hom
      ((asIso (MappingTorus.circleWangClass (ModuleCat.of ℤ ℤ))).inv.hom 1)

/-- On the classes of the loop through `1`, the Wang class is the Wang class of the circle. -/
private theorem singularHomologyMap_baseLoop_comp_wangClass :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom baseLoop) ≫
      MappingTorus.wangClass (ModuleCat.of ℤ ℤ) conjCircleDiffeomorph.toHomeomorph.symm =
        MappingTorus.circleWangClass (ModuleCat.of ℤ ℤ) := by
  rw [MappingTorus.wangClass_eq_singularHomologyMap_proj_comp_circleWangClass,
    ← Functor.map_comp_assoc, baseLoop_comp_proj, CategoryTheory.Functor.map_id,
    Category.id_comp]

/-- The class of the loop through `1` has Wang class `1`, so it splits the Wang sequence. -/
private theorem wangClass_baseLoopClass :
    (MappingTorus.wangClass (ModuleCat.of ℤ ℤ) conjCircleDiffeomorph.toHomeomorph.symm).hom
      baseLoopClass = 1 :=
  (ConcreteCategory.congr_hom singularHomologyMap_baseLoop_comp_wangClass _).trans
    (Iso.inv_hom_id_apply (asIso (MappingTorus.circleWangClass (ModuleCat.of ℤ ℤ))) 1)

/-- **`H₀` of the Klein bottle.** The Klein bottle is path-connected, so `H₀(K; ℤ) ≃ ℤ`. -/
def singularHomologyZeroLinearEquiv :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of KleinBottle) ≃ₗ[ℤ] ℤ :=
  (asIso ((TopCat.of KleinBottle).singularHomology₀ε (ModuleCat.of ℤ ℤ))).toLinearEquiv

/-- `H₀(K; ℤ) ≃ ℤ` is the augmentation. -/
@[simp]
theorem singularHomologyZeroLinearEquiv_apply (x) :
    singularHomologyZeroLinearEquiv x =
      (TopCat.of KleinBottle).singularHomology₀ε (ModuleCat.of ℤ ℤ) x :=
  (rfl)

/-- **`H₁` of the Klein bottle.** `H₁(K; ℤ) ≃ ℤ × ℤ/2`. The Wang sequence is split along the closed
orbit `t ↦ [t, 1]` through the fixed point `1` of conjugation. -/
def singularHomologyOneLinearEquiv :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of KleinBottle) ≃ₗ[ℤ] ℤ × ZMod 2 :=
  (((singularHomologyFunctor _ 1).obj _).mapIso isoMappingTorus).toLinearEquiv ≪≫ₗ
    MappingTorus.homologyOneLinearEquivOfNeg _ circleHomologyOneLinearEquiv
      (homologyMap_monodromyChainMap_one_eq_neg _) baseLoopClass wangClass_baseLoopClass

/-- `singularHomologyOneLinearEquiv` transports along the homeomorphism with the topological
mapping torus, then applies `TauCeti.MappingTorus.homologyOneLinearEquivOfNeg`. -/
private theorem singularHomologyOneLinearEquiv_apply (x) :
    singularHomologyOneLinearEquiv x =
          MappingTorus.homologyOneLinearEquivOfNeg _ circleHomologyOneLinearEquiv
        (homologyMap_monodromyChainMap_one_eq_neg _) baseLoopClass wangClass_baseLoopClass
        ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)).map
          isoMappingTorus.hom).hom x) :=
  rfl

/-- **The fibre circle of the Klein bottle in `H₁`.** Under `H₁(K; ℤ) ≃ ℤ × ℤ/2`, the image of
`y ∈ H₁(S¹; ℤ)` under the fibre inclusion `z ↦ [0, z]` is `(0, n mod 2)`, where `n ∈ ℤ` is the
class of `y` under `H₁(S¹; ℤ) ≅ ℤ`
(`ContinuousMap.HomotopyEquiv.singularHomologySphereIso`). -/
@[simp]
theorem singularHomologyOneLinearEquiv_singularHomologyMap_mk_zero (y) :
    singularHomologyOneLinearEquiv ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom ⟨mk 0,
          (SmoothMappingTorus.isClosedEmbedding_mk _ 0).continuous⟩)).hom y) =
      (0, (((ContinuousMap.HomotopyEquiv.refl _).singularHomologySphereIso (ModuleCat.of ℤ ℤ)
        Complex.finrank_real_complex le_rfl).hom.hom y : ZMod 2)) := by
  have h : TopCat.ofHom ⟨mk 0, (SmoothMappingTorus.isClosedEmbedding_mk _ 0).continuous⟩ ≫
      isoMappingTorus.hom =
        TopCat.ofHom (MappingTorus.incl conjCircleDiffeomorph.toHomeomorph.symm) :=
    ConcreteCategory.hom_ext _ _ fun z ↦ by
      simp [isoMappingTorus]
  have key := congrArg (fun f ↦ ModuleCat.Hom.hom f y)
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)).map_comp
      (TopCat.ofHom ⟨mk 0, (SmoothMappingTorus.isClosedEmbedding_mk _ 0).continuous⟩)
      isoMappingTorus.hom)
  rw [h] at key
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at key
  rw [singularHomologyOneLinearEquiv_apply]
  have hfib := MappingTorus.homologyOneLinearEquivOfNeg_homologyMap_fibreInclusionChainMap _
    circleHomologyOneLinearEquiv (homologyMap_monodromyChainMap_one_eq_neg _) baseLoopClass
    wangClass_baseLoopClass y
  rw [MappingTorus.fibreInclusionChainMap_def,
    ← singularHomologyFunctor_obj_map_eq_homologyMap] at hfib
  rw [← key]
  exact hfib

/-- **The free coordinate of `H₁` of the Klein bottle is the degree over the base circle.** The
first coordinate of `H₁(K; ℤ) ≃ ℤ × ℤ/2` is the map induced by the projection `K → ℝ/ℤ`, followed
by the isomorphism `TauCeti.MappingTorus.circleWangClass : H₁(ℝ/ℤ; ℤ) ≅ ℤ`. -/
theorem singularHomologyOneLinearEquiv_apply_fst (x) :
    (singularHomologyOneLinearEquiv x).1 =
      (MappingTorus.circleWangClass (ModuleCat.of ℤ ℤ)).hom
        ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)).map
          (TopCat.ofHom ⟨SmoothMappingTorus.proj conjCircleDiffeomorph,
            SmoothMappingTorus.continuous_proj _⟩)).hom x) := by
  have h : isoMappingTorus.hom ≫ TopCat.ofHom ⟨MappingTorus.proj _, MappingTorus.continuous_proj
      conjCircleDiffeomorph.toHomeomorph.symm⟩ =
        TopCat.ofHom ⟨SmoothMappingTorus.proj conjCircleDiffeomorph,
          SmoothMappingTorus.continuous_proj _⟩ :=
    ConcreteCategory.hom_ext _ _ fun z ↦ by
      simp [isoMappingTorus]
  rw [singularHomologyOneLinearEquiv_apply, MappingTorus.homologyOneLinearEquivOfNeg_apply_fst,
    MappingTorus.wangClass_eq_singularHomologyMap_proj_comp_circleWangClass, ← h,
    Functor.map_comp, ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
    LinearMap.comp_apply]

/-- **The closed orbit through `1` carries the free summand of `H₁` of the Klein bottle.** Under
`H₁(K; ℤ) ≃ ℤ × ℤ/2`, the image of `c ∈ H₁(ℝ/ℤ; ℤ)` under a loop `γ : ℝ/ℤ → K` of the form
`t ↦ [t, 1]` is `(circleWangClass c, 0)`, where `1` is a fixed point of conjugation. -/
theorem singularHomologyOneLinearEquiv_singularHomologyMap_of_apply_eq_mk_one
    (γ : C(UnitAddCircle, KleinBottle)) (hγ : ∀ t : ℝ, γ t = mk t 1) (c) :
    singularHomologyOneLinearEquiv ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom γ)).hom c) =
      ((MappingTorus.circleWangClass (ModuleCat.of ℤ ℤ)).hom c, 0) := by
  have h : TopCat.ofHom γ ≫ isoMappingTorus.hom = TopCat.ofHom baseLoop :=
    ConcreteCategory.hom_ext _ _ fun θ ↦ by
      induction θ using QuotientAddGroup.induction_on with
      | H t => simp [isoMappingTorus, hγ, baseLoop_coe]
  have hγ₁ := congrArg (fun f ↦ ModuleCat.Hom.hom f
      ((asIso (MappingTorus.circleWangClass (ModuleCat.of ℤ ℤ))).inv.hom 1))
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)).map_comp
      (TopCat.ofHom γ) isoMappingTorus.hom)
  rw [h, ModuleCat.hom_comp, LinearMap.comp_apply] at hγ₁
  -- Both sides are `ℤ`-linear in `circleWangClass c ∈ ℤ`, and agree on `1`, the Wang class of the
  -- class of the loop through `1`.
  have key : singularHomologyOneLinearEquiv.toLinearMap ∘ₗ
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom γ)).hom ∘ₗ
        (asIso (MappingTorus.circleWangClass (ModuleCat.of ℤ ℤ))).inv.hom =
      LinearMap.inl ℤ ℤ (ZMod 2) :=
    LinearMap.ext_ring <| (singularHomologyOneLinearEquiv_apply _).trans <|
      (congrArg _ hγ₁.symm).trans (MappingTorus.homologyOneLinearEquivOfNeg_self _ _ _ _ _)
  exact (congrArg _ (congrArg _ (Iso.hom_inv_id_apply
    (asIso (MappingTorus.circleWangClass (ModuleCat.of ℤ ℤ))) c).symm)).trans
    (LinearMap.congr_fun key _)

/-- **The fibre circle of the Klein bottle carries the torsion of `H₁`.** Under
`H₁(K; ℤ) ≃ ℤ × ℤ/2`, the image of `H₁(S¹; ℤ)` under the fibre inclusion `z ↦ [0, z]` is the
torsion summand `0 × ℤ/2`. -/
theorem map_range_singularHomologyMap_mk_zero :
    (LinearMap.range (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom ⟨mk 0,
          (SmoothMappingTorus.isClosedEmbedding_mk _ 0).continuous⟩)).hom).map
        (singularHomologyOneLinearEquiv : _ →ₗ[ℤ] ℤ × ZMod 2) =
      LinearMap.range (LinearMap.inr ℤ ℤ (ZMod 2)) := by
  ext ⟨a, b⟩
  simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe, LinearMap.inr_apply]
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, h⟩
    rw [singularHomologyOneLinearEquiv_singularHomologyMap_mk_zero] at h
    exact ⟨_, h⟩
  · rintro ⟨c, h⟩
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective c
    exact ⟨_, ⟨circleHomologyOneLinearEquiv.symm n, rfl⟩,
      (singularHomologyOneLinearEquiv_singularHomologyMap_mk_zero _).trans <|
        (congrArg (fun m : ℤ ↦ ((0 : ℤ), (m : ZMod 2)))
          (circleHomologyOneLinearEquiv.apply_symm_apply n)).trans h⟩

/-- **Higher homology of the Klein bottle.** `Hₖ(K; ℤ) = 0` for `k ≥ 2`. -/
theorem isZero_singularHomology_of_two_le {k : ℕ} (hk : 2 ≤ k) :
    IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of KleinBottle)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hk
  refine IsZero.of_iso ?_ (((singularHomologyFunctor _ (n + 2)).obj _).mapIso isoMappingTorus)
  have hF : ∀ m, IsZero ((((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of (sphere (0 : ℂ) 1))).homology (m + 2)) := fun m ↦
    (ContinuousMap.HomotopyEquiv.refl _).isZero_singularHomology_of_sphere_of_ne
      (ModuleCat.of ℤ ℤ) Complex.finrank_real_complex (by lia) (by lia)
  -- `𝟙 - φ_*` is multiplication by `2` on `H₁(S¹; ℤ) ≃ ℤ`, and the zero map on `Hₙ₊₂(S¹; ℤ) = 0`.
  have : Mono (homologyMap (MappingTorus.wangEndomorphism
      conjCircleDiffeomorph.toHomeomorph.symm (ModuleCat.of ℤ ℤ)) (n + 1)) := by
    rcases n with _ | n
    · rw [MappingTorus.mono_homologyMap_wangEndomorphism_iff,
        homologyMap_monodromyChainMap_one_eq_neg]
      intro x y hxy
      apply circleHomologyOneLinearEquiv.injective
      have := congrArg circleHomologyOneLinearEquiv hxy
      simp only [ModuleCat.hom_neg, ModuleCat.hom_id, sub_neg_eq_add, LinearMap.add_apply,
        LinearMap.id_apply, map_add] at this
      lia
    · exact ⟨fun _ _ _ ↦ (hF n).eq_of_tgt _ _⟩
  exact MappingTorus.isZero_homology_succ _ _ (n + 1) (hF n)

end KleinBottle

end TauCeti
