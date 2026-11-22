/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.AddCircle
public import TauCeti.AlgebraicTopology.Singular.MappingTorus.Refl
public import TauCeti.AlgebraicTopology.Singular.Reduced

/-!
# The Wang class of a mapping torus comes from the base circle

Let `φ : F ≃ₜ F` be a homeomorphism and `T_φ` its mapping torus. The Wang sequence ends with
`H₁(T_φ) ⟶ H₀(F) ⟶ 0`, where the first map is the Wang connecting morphism `δ`
(`TauCeti.MappingTorus.wangδ`). Composing with the augmentation `ε : H₀(F) ⟶ R` gives the
**Wang class** `ε ∘ δ : H₁(T_φ) ⟶ R` (`TauCeti.MappingTorus.wangClass`). Under the hypotheses
of `TauCeti.MappingTorus.cohomologyOneEquiv` (coefficients in an integral domain `k`, a
path-connected fibre, `H₁(F; k)` free of finite rank, `det (𝟙 - φ_*) ≠ 0` on it and a torsion-free
module `M`), `H¹(T_φ; M) ≃ M`, and the class corresponding to `m` evaluates on `c ∈ H₁(T_φ)` to
`ε(δ c) • m`. This file shows that the Wang class is pulled back from the circle along the
projection `T_φ → ℝ/ℤ` (`TauCeti.MappingTorus.proj`).

* **Naturality.** For a map `g : F → G` with `g ∘ φ = ψ ∘ g`, the Wang class of `T_φ` is the
  pullback of the Wang class of `T_ψ` along the induced map of mapping tori
  (`TauCeti.MappingTorus.singularHomologyMap_map_comp_wangClass`), because the Wang connecting
  morphism (`TauCeti.MappingTorus.singularHomologyMap_map_comp_wangδ`) and the augmentation are
  natural.
* **The circle.** For the mapping torus of the identity of a point, the Wang sequence reads
  `0 = H₁(pt) ⟶ H₁(T) ⟶ H₀(pt) ⟶ 0`, so its Wang connecting morphism and its Wang class are
  isomorphisms (`TauCeti.MappingTorus.isIso_wangδ_refl_punit`,
  `TauCeti.MappingTorus.isIso_wangClass_refl_punit`). This mapping torus is a circle: its
  projection onto `ℝ/ℤ` is a homeomorphism (`TauCeti.MappingTorus.projPUnitHomeomorph`). The Wang
  class transported along it is an isomorphism `H₁(ℝ/ℤ; R) ⟶ R`
  (`TauCeti.MappingTorus.circleWangClass`, `TauCeti.MappingTorus.isIso_circleWangClass`).
* **Every mapping torus.** The map from `F` to a point intertwines `φ` with the identity of the
  point, and the induced map of mapping tori covers the identity of `ℝ/ℤ`. So for a fibre in
  `Type`, the Wang class of `T_φ` is the map `proj_* : H₁(T_φ) ⟶ H₁(ℝ/ℤ)` followed by
  `circleWangClass R`
  (`TauCeti.MappingTorus.wangClass_eq_singularHomologyMap_proj_comp_circleWangClass`). Thus the
  Wang class factors through `proj_*` via the isomorphism `circleWangClass R`. Reading it as the
  pullback of a generator of `H¹(ℝ/ℤ; ℤ)` needs the universal coefficient identification
  `Hom(H₁(ℝ/ℤ), ℤ) ≅ H¹(ℝ/ℤ; ℤ)`, which is not made here.

With integer coefficients, `circleWangClass` is the winding number times the constant
`TauCeti.MappingTorus.circleWangSign`, its value on the circuit class `AddCircle.fundamentalClass 1`
(`TauCeti.MappingTorus.circleWangClass_hom_apply`), and this constant is `1` or `-1`
(`TauCeti.MappingTorus.circleWangSign_eq_one_or_eq_neg_one`). Which of the two it is, that is,
which generator of `Hom(H₁(ℝ/ℤ; ℤ), ℤ)` the Wang class is, is not computed here.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, Example 2.48, for the Wang sequence of a mapping
  torus.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology HomologicalComplex

universe w v u

namespace TauCeti.MappingTorus

section General

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  {F : Type w} [TopologicalSpace F] (φ : F ≃ₜ F)

/-- **The Wang class** `ε ∘ δ : H₁(T_φ) ⟶ R` of the mapping torus of `φ`: the Wang connecting
morphism `H₁(T_φ) ⟶ H₀(F)` followed by the augmentation `H₀(F) ⟶ R`. -/
def wangClass : ((singularHomologyFunctor A 1).obj R).obj (TopCat.of (MappingTorus φ)) ⟶ R :=
  wangδ φ R 0 ≫ (TopCat.of F).singularHomology₀ε R

/-- The Wang class is the Wang connecting morphism followed by the augmentation. -/
lemma wangClass_def : wangClass R φ = wangδ φ R 0 ≫ (TopCat.of F).singularHomology₀ε R :=
  (rfl)

/-- With module coefficients, the Wang class of a class `c ∈ H₁(T_φ)` is the augmentation of its
image `δ c ∈ H₀(F)` under the Wang connecting morphism. -/
theorem wangClass_hom_apply {k : Type*} [Ring k] [HasCoproducts.{w} (ModuleCat.{v} k)]
    (U : ModuleCat.{v} k)
    (c : ((singularHomologyFunctor (ModuleCat.{v} k) 1).obj U).obj (TopCat.of (MappingTorus φ))) :
    (wangClass U φ).hom c = ((TopCat.of F).singularHomology₀ε U).hom ((wangδ φ U 0).hom c) :=
  -- The source of `wangδ` is the homology in degree `0 + 1`, which is the degree `1` of
  -- `wangClass` only definitionally, so `rw [wangClass_def]` cannot form the motive.
  (rfl)

/-- **Naturality of the Wang class.** For a map `g : F → G` intertwining the monodromies,
`g ∘ φ = ψ ∘ g`, the Wang class of `T_φ` is the pullback of the Wang class of `T_ψ` along the
induced map of mapping tori. -/
@[reassoc (attr := simp)]
theorem singularHomologyMap_map_comp_wangClass {G : Type w} [TopologicalSpace G] (ψ : G ≃ₜ G)
    (g : C(F, G)) (h : Function.Semiconj g φ ψ) :
    ((singularHomologyFunctor A 1).obj R).map (TopCat.ofHom (map φ ψ g h)) ≫ wangClass R ψ =
      wangClass R φ := by
  -- The Wang connecting morphism and the augmentation are natural.
  have hδ : ((singularHomologyFunctor A 1).obj R).map (TopCat.ofHom (map φ ψ g h)) ≫
      wangδ ψ R 0 = wangδ φ R 0 ≫ ((singularHomologyFunctor A 0).obj R).map (TopCat.ofHom g) :=
    -- The degree `0 + 1` of the naturality lemma reduces to `1`.
    singularHomologyMap_map_comp_wangδ φ R ψ g h 0
  -- `wangδ` has chain-complex homology as source and target, while `singularHomology₀ε` and
  -- `wangClass` are stated with `singularHomologyFunctor`. The composites are therefore only
  -- type-correct up to the same unfolding, and `rw` cannot form the motive, so the equalities
  -- are chained in term mode.
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hδ).trans <|
    (Category.assoc _ _ _).trans <|
      congrArg (wangδ φ R 0 ≫ ·) (singularHomologyMap_singularHomology₀ε R (TopCat.ofHom g))

/-- **The Wang sequence of a circle.** For the mapping torus of the identity of a point, the Wang
connecting morphism `H₁(T) ⟶ H₀(pt)` is an isomorphism, since `H₁(pt)` vanishes. -/
instance isIso_wangδ_refl_punit : IsIso (wangδ (Homeomorph.refl PUnit.{w + 1}) R 0) :=
  (shortExact_wang_refl PUnit.{w + 1} R 0).isIso_g_iff.2
    (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace A 1 R
      (TopCat.of PUnit.{w + 1}) one_ne_zero)

/-- For the mapping torus of the identity of a point, a circle, the Wang class is an isomorphism
`H₁(T) ≅ R`. -/
instance isIso_wangClass_refl_punit : IsIso (wangClass R (Homeomorph.refl PUnit.{w + 1})) :=
  IsIso.comp_isIso' (isIso_wangδ_refl_punit R)
    (inferInstanceAs (IsIso ((TopCat.of PUnit.{w + 1}).singularHomology₀ε R)))

end General

section Circle

variable {A : Type u} [Category.{v} A] [HasCoproducts.{0} A] [Abelian A] (R : A)

/-- The projection of the mapping torus of the identity of a point onto the circle `ℝ/ℤ`, as a
homeomorphism. -/
def projPUnitHomeomorph : MappingTorus (Homeomorph.refl PUnit.{1}) ≃ₜ UnitAddCircle :=
  reflHomeomorph.trans (Homeomorph.punitProd UnitAddCircle)

@[simp]
lemma projPUnitHomeomorph_apply (z : MappingTorus (Homeomorph.refl PUnit.{1})) :
    projPUnitHomeomorph z = proj _ z :=
  snd_reflHomeomorph z

/-- The projection of the mapping torus of the identity of a point onto `ℝ/ℤ` induces an isomorphism
on singular homology, since it is a homeomorphism. -/
instance isIso_singularHomologyMap_proj_refl_punit (n : ℕ) :
    IsIso (((singularHomologyFunctor A n).obj R).map
      (TopCat.ofHom ⟨proj (Homeomorph.refl PUnit.{1}), continuous_proj _⟩)) := by
  have : IsIso (TopCat.ofHom ⟨proj (Homeomorph.refl PUnit.{1}), continuous_proj _⟩) := by
    rw [TopCat.isIso_iff_isHomeomorph]
    convert projPUnitHomeomorph.isHomeomorph using 1
    exact funext fun z ↦ (projPUnitHomeomorph_apply z).symm
  infer_instance

/-- **The Wang class of the circle** `H₁(ℝ/ℤ; R) ⟶ R`: the Wang class of the mapping torus of the
identity of a point, transported to `ℝ/ℤ` along the projection, which is a homeomorphism. -/
def circleWangClass : ((singularHomologyFunctor A 1).obj R).obj (TopCat.of UnitAddCircle) ⟶ R :=
  inv (((singularHomologyFunctor A 1).obj R).map
      (TopCat.ofHom ⟨proj (Homeomorph.refl PUnit.{1}), continuous_proj _⟩)) ≫
    wangClass R (Homeomorph.refl PUnit.{1})

/-- The Wang class of the circle is the inverse of the isomorphism induced by the projection of
the mapping torus of the identity of a point, followed by the Wang class of that mapping torus. -/
lemma circleWangClass_def :
    circleWangClass R = inv (((singularHomologyFunctor A 1).obj R).map
        (TopCat.ofHom ⟨proj (Homeomorph.refl PUnit.{1}), continuous_proj _⟩)) ≫
      wangClass R (Homeomorph.refl PUnit.{1}) :=
  (rfl)

/-- The Wang class of the circle is an isomorphism `H₁(ℝ/ℤ; R) ≅ R`. -/
instance isIso_circleWangClass : IsIso (circleWangClass R) :=
  inferInstanceAs (IsIso (_ ≫ _))

/-- The Wang class of the mapping torus of the identity of a point is the Wang class of the circle,
pulled back along the projection. -/
@[reassoc (attr := simp)]
theorem singularHomologyMap_proj_comp_circleWangClass :
    ((singularHomologyFunctor A 1).obj R).map
        (TopCat.ofHom ⟨proj (Homeomorph.refl PUnit.{1}), continuous_proj _⟩) ≫
      circleWangClass R = wangClass R (Homeomorph.refl PUnit.{1}) := by
  rw [circleWangClass_def, IsIso.hom_inv_id_assoc]

/-- **The Wang class of a mapping torus is pulled back from the circle.** For a homeomorphism `φ`
of a space `F`, the Wang class `ε ∘ δ : H₁(T_φ) ⟶ R` is the map induced on `H₁` by the projection
`T_φ → ℝ/ℤ`, followed by the isomorphism `circleWangClass R : H₁(ℝ/ℤ; R) ⟶ R`. -/
theorem wangClass_eq_singularHomologyMap_proj_comp_circleWangClass {F : Type}
    [TopologicalSpace F] (φ : F ≃ₜ F) :
    wangClass R φ =
      ((singularHomologyFunctor A 1).obj R).map
          (TopCat.ofHom ⟨proj φ, continuous_proj φ⟩) ≫ circleWangClass R := by
  -- The projection of `T_φ` factors through the mapping torus of the identity of a point, since
  -- the map to the point intertwines `φ` with the identity.
  have h : Function.Semiconj (ContinuousMap.const F PUnit.unit) φ (Homeomorph.refl PUnit.{1}) :=
    fun _ ↦ rfl
  rw [← proj_comp_map φ (Homeomorph.refl PUnit.{1}) (ContinuousMap.const F PUnit.unit) h,
    TopCat.ofHom_comp, Functor.map_comp, Category.assoc,
    singularHomologyMap_proj_comp_circleWangClass, singularHomologyMap_map_comp_wangClass]

end Circle

/-! ### The integral Wang class of the circle -/

/-- **The sign of the Wang class of the circle**: the value of the integral Wang class
`H₁(ℝ/ℤ; ℤ) ⟶ ℤ` of the circle on the circuit class `AddCircle.fundamentalClass 1`. It is `1` or
`-1` (`TauCeti.MappingTorus.circleWangSign_eq_one_or_eq_neg_one`). -/
def circleWangSign : ℤ :=
  (circleWangClass (ModuleCat.of ℤ ℤ)).hom (AddCircle.fundamentalClass 1)

/-- The integral Wang class of the circle takes the value `circleWangSign` on the circuit class. -/
theorem circleWangClass_hom_fundamentalClass :
    (circleWangClass (ModuleCat.of ℤ ℤ)).hom (AddCircle.fundamentalClass 1) = circleWangSign :=
  (rfl)

/-- The integral Wang class of the circle is the winding number times `circleWangSign`. -/
theorem circleWangClass_hom_apply
    (c : ((singularChains ℤ).obj (TopCat.of UnitAddCircle)).homology 1) :
    (circleWangClass (ModuleCat.of ℤ ℤ)).hom c =
      AddCircle.firstHomologyAddEquiv 1 c * circleWangSign := by
  -- The source of `circleWangClass` is `H₁(ℝ/ℤ; ℤ)` written through `singularHomologyFunctor`,
  -- definitionally the homology of `singularChains ℤ` used by `AddCircle.fundamentalClass`; `rw`
  -- cannot form the motive across the two spellings, so the steps are chained in term mode.
  exact (congrArg _ (AddCircle.eq_firstHomologyAddEquiv_zsmul_fundamentalClass 1 c)).trans
    ((map_zsmul _ _ _).trans (smul_eq_mul _ _))

/-- **The Wang class of the circle is a generator**: its value `circleWangSign` on the circuit
class is `1` or `-1`, since it is an isomorphism `H₁(ℝ/ℤ; ℤ) ≅ ℤ`. -/
theorem circleWangSign_eq_one_or_eq_neg_one : circleWangSign = 1 ∨ circleWangSign = -1 := by
  obtain ⟨c, hc⟩ := (ConcreteCategory.bijective_of_isIso (circleWangClass (ModuleCat.of ℤ ℤ))).2 1
  exact Int.eq_one_or_neg_one_of_mul_eq_one
    ((mul_comm _ _).trans ((circleWangClass_hom_apply c).symm.trans hc))

/-- The square of `circleWangSign` is `1`. -/
@[simp]
theorem circleWangSign_mul_self : circleWangSign * circleWangSign = 1 := by
  rcases circleWangSign_eq_one_or_eq_neg_one with h | h <;> rw [h] <;> norm_num

/-- `circleWangSign` is nonzero. -/
theorem circleWangSign_ne_zero : circleWangSign ≠ 0 :=
  left_ne_zero_of_mul_eq_one circleWangSign_mul_self

end TauCeti.MappingTorus
