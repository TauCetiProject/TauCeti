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
(`TauCeti.MappingTorus.homologyOneLinearEquivOfNeg`). The splitting is a choice, but the
equivalence is pinned down where it is canonical: its `ℤ` coordinate is the Wang class
`ε ∘ δ : H₁(T_φ) → ℤ` (`TauCeti.MappingTorus.homologyOneLinearEquivOfNeg_apply_fst`), and it sends
the image of `y ∈ H₁(F)` under the fibre inclusion to `(0, e y mod 2)`
(`TauCeti.MappingTorus.homologyOneLinearEquivOfNeg_homologyMap_fibreInclusionChainMap`). For the
Klein bottle this says that the `ℤ` coordinate of a class is the degree of its projection to the
base circle (`TauCeti.KleinBottle.singularHomologyOneLinearEquiv_apply_fst`), and that the fibre
circle carries the torsion summand `0 × ℤ/2`
(`TauCeti.KleinBottle.map_range_singularHomologyMap_mk_zero`). In degree two, `𝟙 - φ_*` is
injective on `H₁(S¹; ℤ)`, so the Wang connecting morphism vanishes and `H₂(K; ℤ)` is a quotient of
`H₂(S¹; ℤ) = 0`.

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

/-- The Wang connecting morphism `H₁(T_φ; ℤ) → H₀(F; ℤ) ≃ ℤ` has a section, since `ℤ` is free. -/
private theorem exists_wangδ_comp_eq_id :
    ∃ l, (wangCokernelShortComplex (k := ℤ) φ 0).g.hom ∘ₗ l = LinearMap.id := by
  have : Module.Projective ℤ (wangCokernelShortComplex (k := ℤ) φ 0).X₃ :=
    .of_equiv (asIso ((TopCat.of F).singularHomology₀ε (ModuleCat.of ℤ ℤ))).toLinearEquiv.symm
  exact Module.projective_lifting_property _ _
    (wangCokernelShortComplex_shortExact (k := ℤ) φ 0).moduleCat_surjective_g

/-- A splitting `H₁(T_φ; ℤ) ≃ (H₁(F) ⧸ (𝟙 - φ_*)) × H₀(F)` of the Wang sequence. -/
private def wangSplitting :=
  (exact_wangCokernelShortComplex_zero φ).splitSurjectiveEquiv
    (wangCokernelShortComplex_shortExact (k := ℤ) φ 0).moduleCat_injective_f
    ⟨_, (exists_wangδ_comp_eq_id φ).choose_spec⟩

include e hφ in
/-- **`H₁` of a mapping torus whose monodromy reverses a circle.** If `F` is path-connected,
`H₁(F; ℤ) ≃ ℤ` and `φ` acts on it by `-1`, then `H₁(T_φ; ℤ) ≃ ℤ × ℤ/2`. The equivalence depends
on a choice of splitting of the Wang sequence; its `ℤ` coordinate is the Wang class
(`TauCeti.MappingTorus.homologyOneLinearEquivOfNeg_apply_fst`) and the fibre classes map to
`0 × ℤ/2`
(`TauCeti.MappingTorus.homologyOneLinearEquivOfNeg_homologyMap_fibreInclusionChainMap`). -/
def homologyOneLinearEquivOfNeg :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of (MappingTorus φ)) ≃ₗ[ℤ] ℤ × ZMod 2 :=
  let s : _ ≃+ ℤ × ZMod 2 :=
    (AddEquivClass.toAddEquiv (wangSplitting φ).val).trans
      (((wangCokernelAddEquivOfNeg φ e hφ).prodCongr (AddEquivClass.toAddEquiv
        (asIso ((TopCat.of F).singularHomology₀ε (ModuleCat.of ℤ ℤ))).toLinearEquiv)).trans
        AddEquiv.prodComm)
  s.toLinearEquiv fun c x ↦ by
    -- the two `ℤ`-module structures on the target agree with its `ℤ`-multiplication `zsmul`
    convert map_zsmul s c x using 2
    exact int_smul_eq_zsmul _ _ _

include e hφ in
/-- `TauCeti.MappingTorus.homologyOneLinearEquivOfNeg` is the splitting of the Wang sequence,
followed by `ℤ/2` on the cokernel of `𝟙 - φ_*` and the augmentation on `H₀(F)`. -/
private theorem homologyOneLinearEquivOfNeg_apply (x) :
    homologyOneLinearEquivOfNeg φ e hφ x =
      ((TopCat.of F).singularHomology₀ε (ModuleCat.of ℤ ℤ) ((wangSplitting φ).val x).2,
        wangCokernelAddEquivOfNeg φ e hφ ((wangSplitting φ).val x).1) :=
  rfl

include e hφ in
/-- The `ℤ` coordinate of `TauCeti.MappingTorus.homologyOneLinearEquivOfNeg` is the Wang class
`ε ∘ δ : H₁(T_φ; ℤ) → ℤ`. -/
theorem homologyOneLinearEquivOfNeg_apply_fst (x) :
    (homologyOneLinearEquivOfNeg φ e hφ x).1 = (wangClass (ModuleCat.of ℤ ℤ) φ).hom x := by
  have : ((wangSplitting φ).val x).2 = wangδ φ (ModuleCat.of ℤ ℤ) 0 x :=
    (LinearMap.congr_fun (wangSplitting φ).property.2 x).symm
  rw [homologyOneLinearEquivOfNeg_apply, this, wangClass_hom_apply]

include hφ in
/-- `TauCeti.MappingTorus.homologyOneLinearEquivOfNeg` sends the image of `y ∈ H₁(F; ℤ)` under the
fibre inclusion to `(0, e y mod 2)`. -/
theorem homologyOneLinearEquivOfNeg_homologyMap_fibreInclusionChainMap (y) :
    homologyOneLinearEquivOfNeg φ e hφ
        (homologyMap (fibreInclusionChainMap φ (ModuleCat.of ℤ ℤ)) 1 y) = (0, (e y : ZMod 2)) := by
  have : (wangSplitting φ).val (homologyMap (fibreInclusionChainMap φ (ModuleCat.of ℤ ℤ)) 1 y) =
      (Submodule.Quotient.mk y, 0) := by
    have h := LinearMap.congr_fun (wangSplitting φ).property.1 (Submodule.Quotient.mk y)
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe,
      wangCokernelShortComplex_f_mk] at h
    rw [h]
    exact LinearEquiv.apply_symm_apply _ _
  -- The argument lies in the homology of the singular chain complex, the source of
  -- `homologyOneLinearEquivOfNeg` only by unfolding `singularHomologyFunctor`.
  refine (homologyOneLinearEquivOfNeg_apply φ e hφ _).trans ?_
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
  rw [MappingTorus.monodromyChainMap_def, h]
  -- The homology map of the singular chain map is by definition the map on singular homology,
  -- so the two identities below agree up to unfolding `singularHomologyFunctor`.
  exact (singularHomologyFunctor_map_unitSphereMap R (n := 0) Complex.finrank_real_complex
    _).trans (by simp [hdet]; rfl)

/-- The unit circle of `ℂ` is path-connected. -/
private theorem pathConnectedSpace_sphere : PathConnectedSpace (sphere (0 : ℂ) 1) :=
  isPathConnected_iff_pathConnectedSpace.1 <|
    isPathConnected_sphere (by simp [Complex.rank_real_complex]) 0 zero_le_one

attribute [local instance] pathConnectedSpace_sphere

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

/-- **`H₀` of the Klein bottle.** The Klein bottle is path-connected, so `H₀(K; ℤ) ≃ ℤ`. -/
def singularHomologyZeroLinearEquiv :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of KleinBottle) ≃ₗ[ℤ] ℤ :=
  have : PathConnectedSpace KleinBottle :=
    (SmoothMappingTorus.homeomorphMappingTorus conjCircleDiffeomorph).symm.surjective
      |>.pathConnectedSpace (SmoothMappingTorus.homeomorphMappingTorus _).symm.continuous
  (asIso ((TopCat.of KleinBottle).singularHomology₀ε (ModuleCat.of ℤ ℤ))).toLinearEquiv

/-- **`H₁` of the Klein bottle.** `H₁(K; ℤ) ≃ ℤ × ℤ/2`. -/
def singularHomologyOneLinearEquiv :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of KleinBottle) ≃ₗ[ℤ] ℤ × ZMod 2 :=
  (((singularHomologyFunctor _ 1).obj _).mapIso isoMappingTorus).toLinearEquiv ≪≫ₗ
    MappingTorus.homologyOneLinearEquivOfNeg _ circleHomologyOneLinearEquiv
      (homologyMap_monodromyChainMap_one_eq_neg _)

/-- `singularHomologyOneLinearEquiv` transports along the homeomorphism with the topological
mapping torus, then applies `TauCeti.MappingTorus.homologyOneLinearEquivOfNeg`. -/
private theorem singularHomologyOneLinearEquiv_apply (x) :
    singularHomologyOneLinearEquiv x =
          MappingTorus.homologyOneLinearEquivOfNeg _ circleHomologyOneLinearEquiv
        (homologyMap_monodromyChainMap_one_eq_neg _)
        ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)).map
          isoMappingTorus.hom).hom x) :=
  rfl

/-- The fibre circle `z ↦ [0, z]` of the Klein bottle, read in `H₁(K; ℤ) ≃ ℤ × ℤ/2`. -/
private theorem singularHomologyOneLinearEquiv_singularHomologyMap_mk_zero (y) :
    singularHomologyOneLinearEquiv (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom ⟨mk 0,
          (SmoothMappingTorus.isClosedEmbedding_mk _ 0).continuous⟩) y) =
      (0, (circleHomologyOneLinearEquiv y : ZMod 2)) := by
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
    circleHomologyOneLinearEquiv (homologyMap_monodromyChainMap_one_eq_neg _) y
  rw [MappingTorus.fibreInclusionChainMap_def] at hfib
  -- The homology map of the singular chain map is by definition the map on singular homology.
  exact (congrArg (MappingTorus.homologyOneLinearEquivOfNeg _ _ _) key.symm).trans hfib

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
    Functor.map_comp]
  rfl

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
      (singularHomologyOneLinearEquiv_singularHomologyMap_mk_zero _).trans (by simp [h])⟩

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
