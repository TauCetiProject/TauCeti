/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.AddCircle
public import TauCeti.AlgebraicTopology.Singular.MappingTorus.FirstCohomology
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
  Wang class factors through `proj_*` via the isomorphism `circleWangClass R`.

**The base class.** With integer coefficients the Wang class is read as a cohomology class. The
**base class** `[dt] ∈ H¹(T_φ; ℤ)` (`TauCeti.MappingTorus.baseClass`) is the pullback along the
projection of the angular class `θ_1 ∈ H¹(ℝ/ℤ; ℤ)` (`AddCircle.angularClass`), the integral class
of the closed one-form `dt` of the base circle. Its Kronecker evaluation is the period homomorphism
`H₁(T_φ; ℤ) → ℤ`, `h ↦ ∫_h dt`: the winding number of the projection of `h`
(`TauCeti.MappingTorus.singularKronecker_baseClass`). For a smooth mapping torus the de Rham
version of this homomorphism, with real values, is `TauCeti.SmoothMappingTorus.timePeriodHom`;
the angular class and the time form of the circle are compared by
`AddCircle.homologyPeriodHom_timeForm_eq_singularKronecker_angularClass_mul`.

* **Naturality.** A map of mapping tori induced by `g : F → G` with `g ∘ φ = ψ ∘ g` covers the
  identity of `ℝ/ℤ`, so it pulls the base class back to the base class
  (`TauCeti.MappingTorus.singularCohomologyMap_map_baseClass`).
* **Comparison with the Wang class.** `circleWangClass` and the winding number are both
  isomorphisms `H₁(ℝ/ℤ; ℤ) ≅ ℤ`, so they differ by a sign `s = ±1`
  (`TauCeti.MappingTorus.exists_circleWangClass_eq_zsmul`), and `⟨[dt], h⟩ = s ε(δ h)` on every
  mapping torus, with the same `s`
  (`TauCeti.MappingTorus.exists_singularKronecker_baseClass_eq_zsmul`,
  `TauCeti.MappingTorus.exists_singularKronecker_baseClass_apply`). The value of `s`, that is
  the value of `circleWangClass` on the circuit class `AddCircle.fundamentalClass`, is not
  computed here; the base class itself involves no choice of sign.
* **The period homomorphism.** For a path-connected fibre the periods `⟨[dt], h⟩` take every
  integer value (`TauCeti.MappingTorus.singularKronecker_baseClass_surjective`). If moreover
  `H₁(F; ℤ)` is free of finite rank and `det (𝟙 - φ_*) ≠ 0` on it, the period of `h` vanishes
  exactly when `h` has finite order
  (`TauCeti.MappingTorus.singularKronecker_baseClass_eq_zero_iff`): the kernel of the period
  homomorphism is the torsion of `H₁(T_φ; ℤ)`, so it is injective only when `H₁(T_φ; ℤ)` is
  torsion-free.
* **A generator.** Under the same hypotheses the identification `H¹(T_φ; ℤ) ≃ ℤ` of
  `TauCeti.MappingTorus.cohomologyOneEquiv` sends `[dt]` to `±1`
  (`TauCeti.MappingTorus.cohomologyOneEquiv_baseClass_eq_one_or_eq_neg_one`), so every class of
  `H¹(T_φ; ℤ)` is an integer multiple of `[dt]` (`TauCeti.MappingTorus.exists_eq_zsmul_baseClass`)
  and `[dt]` is a basis of `H¹(T_φ; ℤ)` (`TauCeti.MappingTorus.basisBaseClass`). With the angular
  class `[ds]` of a circle factor it gives the basis `([ds], [dt])` of `H¹((ℝ / pℤ) × T_φ; ℤ)`
  (`TauCeti.MappingTorus.basisAddCircleProd`).

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, Example 2.48, for the Wang sequence of a mapping
  torus.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology HomologicalComplex MonoidalCategory

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

section ModuleCat

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k) {F : Type u} [TopologicalSpace F]
  (φ : F ≃ₜ F)

/-- With module coefficients, the Wang class applies the Wang connecting morphism and then the
augmentation. -/
lemma wangClass_apply
    (c : ((singularHomologyFunctor (ModuleCat.{u} k) 1).obj R).obj (TopCat.of (MappingTorus φ))) :
    (wangClass R φ).hom c = (TopCat.of F).singularHomology₀ε R ((wangδ φ R 0).hom c) := by
  rw [wangClass_def]
  exact ModuleCat.comp_apply _ _ c

end ModuleCat

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

section Integral

-- As in `TauCeti.AlgebraicTopology.Cohomology.AddCircle`, morphisms of `ℤ`-modules are scaled
-- through the linear structure of `ModuleCat ℤ`, under which the Kronecker maps are linear.
attribute [local instance 1100] ModuleCat.instLinear

/-- **The Wang class of the circle is the winding number up to sign.** With integer coefficients,
`circleWangClass` is `s` times the Kronecker evaluation of the angular class, that is `s` times the
winding number, for some `s = ±1`. -/
theorem exists_circleWangClass_eq_zsmul :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ circleWangClass (ModuleCat.of ℤ ℤ) =
      s • (TopCat.of UnitAddCircle).singularKronecker ℤ 1 (AddCircle.angularClass 1) := by
  -- Both maps are additive on `H₁(ℝ/ℤ; ℤ) ≅ ℤ`, so they are determined by their values on the
  -- circuit class, which the winding number sends to `1`.
  have h c : (circleWangClass (ModuleCat.of ℤ ℤ)).hom c =
      (circleWangClass (ModuleCat.of ℤ ℤ)).hom (AddCircle.fundamentalClass 1) *
        AddCircle.firstHomologyAddEquiv 1 c := by
    have hc := AddCircle.eq_firstHomologyAddEquiv_zsmul_fundamentalClass 1 c
    have hs := map_zsmul (circleWangClass (ModuleCat.of ℤ ℤ)).hom
      (AddCircle.firstHomologyAddEquiv 1 c) (AddCircle.fundamentalClass 1)
    rw [smul_eq_mul, mul_comm] at hs
    exact (congrArg _ hc).trans hs
  refine ⟨(circleWangClass (ModuleCat.of ℤ ℤ)).hom (AddCircle.fundamentalClass 1), ?_,
    ModuleCat.hom_ext (LinearMap.ext fun c ↦ ?_)⟩
  · -- The Wang class of the circle is onto `ℤ`, so its value on the generator is a unit.
    obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective (circleWangClass (ModuleCat.of ℤ ℤ))).1
      inferInstance 1
    rw [h c] at hc
    exact Int.eq_one_or_neg_one_of_mul_eq_one hc
  · rw [h c, ModuleCat.hom_smul, LinearMap.smul_apply, smul_eq_mul]
    exact congrArg _ (AddCircle.singularKronecker_angularClass 1 c).symm

variable {F : Type} [TopologicalSpace F] (φ : F ≃ₜ F)

/-- **The base class** `[dt] ∈ H¹(T_φ; ℤ)` of a mapping torus: the pullback of the angular class
`θ_1 ∈ H¹(ℝ/ℤ; ℤ)` along the projection `T_φ → ℝ/ℤ`. It is the integral class of the closed
one-form `dt` of the base circle, and its Kronecker evaluation `h ↦ ⟨[dt], h⟩` is the period
homomorphism `H₁(T_φ; ℤ) → ℤ`, `h ↦ ∫_h dt`, the winding number of the projection of `h`
(`TauCeti.MappingTorus.singularKronecker_baseClass`). -/
def baseClass : (TopCat.of (MappingTorus φ)).singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ
    (ModuleCat.of ℤ ℤ) 1 :=
  TopCat.singularCohomologyMap (TopCat.ofHom ⟨proj φ, continuous_proj φ⟩) 1
    (AddCircle.angularClass 1)

/-- The base class is the pullback of the angular class along the projection. -/
lemma baseClass_def :
    baseClass φ = TopCat.singularCohomologyMap (TopCat.ofHom ⟨proj φ, continuous_proj φ⟩) 1
      (AddCircle.angularClass 1) :=
  (rfl)

/-- **Naturality of the base class.** For a map `g : F → G` with `g ∘ φ = ψ ∘ g`, the induced map
of mapping tori covers the identity of `ℝ/ℤ`, so it pulls the base class of `T_ψ` back to the base
class of `T_φ`. -/
@[simp]
theorem singularCohomologyMap_map_baseClass {G : Type} [TopologicalSpace G] (ψ : G ≃ₜ G)
    (g : C(F, G)) (h : Function.Semiconj g φ ψ) :
    TopCat.singularCohomologyMap (TopCat.ofHom (map φ ψ g h)) 1 (baseClass ψ) = baseClass φ := by
  rw [baseClass, baseClass, ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
    ← TopCat.ofHom_comp, proj_comp_map]

/-- **The periods of the base class**: `⟨[dt], h⟩` is the winding number of the projection of `h`
to the base circle `ℝ/ℤ`. -/
@[simp]
theorem singularKronecker_baseClass
    (c : ((singularChains ℤ).obj (TopCat.of (MappingTorus φ))).homology 1) :
    (TopCat.of (MappingTorus φ)).singularKronecker ℤ 1 (baseClass φ) c =
      AddCircle.firstHomologyAddEquiv 1
        (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (𝟙_ (ModuleCat.{0} ℤ))).map
          (TopCat.ofHom ⟨proj φ, continuous_proj φ⟩) c) := by
  rw [baseClass, TopCat.singularKronecker_naturality]
  exact AddCircle.singularKronecker_angularClass 1 _

/-- **The base class evaluates through the Wang class.** There is a sign `s = ±1`, the same for
every mapping torus, with `⟨[dt], h⟩ = s ε(δ h)` for the Wang class `ε ∘ δ`. The sign is that of
the Wang class of the circle on the circuit class (`exists_circleWangClass_eq_zsmul`). -/
theorem exists_singularKronecker_baseClass_eq_zsmul :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ {F : Type} [TopologicalSpace F] (φ : F ≃ₜ F),
        (TopCat.of (MappingTorus φ)).singularKronecker ℤ 1 (baseClass φ) =
          s • wangClass (ModuleCat.of ℤ ℤ) φ := by
  obtain ⟨s, hs, h⟩ := exists_circleWangClass_eq_zsmul
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> rfl
  refine ⟨s, hs, fun φ ↦ ?_⟩
  rw [wangClass_eq_singularHomologyMap_proj_comp_circleWangClass, h, Linear.comp_smul, smul_smul,
    hss, one_smul, baseClass, TopCat.singularKronecker_naturality]
  -- The chain coefficients `𝟙_ (ModuleCat ℤ)` and `ModuleCat.of ℤ ℤ` agree by definition.
  rfl

/-- **The periods of the base class through the Wang sequence**: there is a sign `s = ±1`, the same
for every mapping torus, with `⟨[dt], h⟩ = s ε(δ h)` for the Wang connecting morphism `δ` and the
augmentation `ε` of `H₀(F)`. -/
theorem exists_singularKronecker_baseClass_apply :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ {F : Type} [TopologicalSpace F] (φ : F ≃ₜ F)
      (c : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)).obj
        (TopCat.of (MappingTorus φ))),
        (TopCat.of (MappingTorus φ)).singularKronecker ℤ 1 (baseClass φ) c =
          s * (TopCat.of F).singularHomology₀ε (ModuleCat.of ℤ ℤ)
            ((wangδ φ (ModuleCat.of ℤ ℤ) 0).hom c) := by
  obtain ⟨s, hs, h⟩ := exists_singularKronecker_baseClass_eq_zsmul
  refine ⟨s, hs, fun φ c ↦ (congrArg (fun f ↦ f.hom c) (h φ)).trans ?_⟩
  rw [ModuleCat.hom_smul, LinearMap.smul_apply, smul_eq_mul, wangClass_apply]

variable [PathConnectedSpace F]

/-- **The period homomorphism is onto.** For a path-connected fibre, every integer is the period
`⟨[dt], h⟩` of some class `h ∈ H₁(T_φ; ℤ)`. -/
theorem singularKronecker_baseClass_surjective :
    Function.Surjective ((TopCat.of (MappingTorus φ)).singularKronecker ℤ 1 (baseClass φ)) := by
  obtain ⟨s, hs, h⟩ := exists_singularKronecker_baseClass_apply
  -- The Wang connecting morphism is onto `H₀(F)`, which the augmentation identifies with `ℤ`.
  have hδ := (ModuleCat.epi_iff_surjective (wangδ φ (ModuleCat.of ℤ ℤ) 0)).1 inferInstance
  have hε := (ModuleCat.epi_iff_surjective
    ((TopCat.of F).singularHomology₀ε (ModuleCat.of ℤ ℤ))).1 inferInstance
  intro n
  obtain ⟨x, hx⟩ := hε (s * n)
  obtain ⟨c, rfl⟩ := hδ x
  refine ⟨c, (h φ c).trans ?_⟩
  rw [hx, ← mul_assoc]
  rcases hs with rfl | rfl <;> simp

variable [Module.Free ℤ ((((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of F)).homology 1)]
  [Module.Finite ℤ ((((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of F)).homology 1)]

/-- **The kernel of the period homomorphism is the torsion.** If `F` is path-connected, `H₁(F; ℤ)`
is free of finite rank and `det (𝟙 - φ_*) ≠ 0` on it, a class `h ∈ H₁(T_φ; ℤ)` has period
`⟨[dt], h⟩ = 0` exactly when it has finite order. -/
theorem singularKronecker_baseClass_eq_zero_iff
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0)
    (c : (((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of (MappingTorus φ))).homology 1) :
    (TopCat.of (MappingTorus φ)).singularKronecker ℤ 1 (baseClass φ) c = 0 ↔
      c ∈ Submodule.torsion ℤ ((((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of (MappingTorus φ))).homology 1) := by
  obtain ⟨s, hs, h⟩ := exists_singularKronecker_baseClass_apply
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> decide
  -- The augmentation `H₀(F) ⟶ ℤ` is an isomorphism, so `ε(δ c) = 0` exactly when `δ c = 0`.
  have hε : Function.Injective ((TopCat.of F).singularHomology₀ε (ModuleCat.of ℤ ℤ)) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hker : (wangδ φ (ModuleCat.of ℤ ℤ) 0).hom c = 0 ↔ c ∈ Submodule.torsion ℤ _ := by
    rw [← LinearMap.mem_ker, ker_wangδ_zero_eq_torsion φ hdet]
  refine (Eq.congr_left (h φ c)).trans ?_
  rw [mul_eq_zero, or_iff_right hs0, ← hker]
  exact hε.eq_iff' (map_zero _)

/-- **The base class corresponds to `±1`.** Under the hypotheses of `cohomologyOneEquiv`, the
identification `H¹(T_φ; ℤ) ≃ ℤ` sends the base class `[dt]` to `1` or `-1`. -/
theorem cohomologyOneEquiv_baseClass_eq_one_or_eq_neg_one
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0) :
    cohomologyOneEquiv φ (ModuleCat.of ℤ ℤ) hdet (baseClass φ) = 1 ∨
      cohomologyOneEquiv φ (ModuleCat.of ℤ ℤ) hdet (baseClass φ) = -1 := by
  obtain ⟨s, hs, h⟩ := exists_singularKronecker_baseClass_eq_zsmul
  suffices baseClass φ = (cohomologyOneEquiv φ (ModuleCat.of ℤ ℤ) hdet).symm s by
    rw [this, LinearEquiv.apply_symm_apply]
    exact hs
  -- Both classes evaluate to `s ε(δ c)`, and the Kronecker map is injective in degree one since
  -- `H₀(T_φ; ℤ)` is free.
  refine ((TopCat.of (MappingTorus φ)).singularKronecker_bijective_of_projective_homology_lt
    (R := ModuleCat.of ℤ ℤ) (ModuleCat.of ℤ ℤ) 1 (fun j hj ↦ ?_)).1
    (ModuleCat.hom_ext (LinearMap.ext fun c ↦ ?_))
  · obtain rfl : j = 0 := by omega
    exact ModuleCat.projective_of_free (Module.Free.chooseBasis ℤ _)
  · refine (congrArg (fun f ↦ f.hom c) (h φ)).trans (Eq.trans ?_
      (singularKronecker_cohomologyOneEquiv_symm_apply φ (ModuleCat.of ℤ ℤ) hdet s c).symm)
    rw [ModuleCat.hom_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm,
      wangClass_apply]

/-- **The base class generates `H¹(T_φ; ℤ)`.** If `F` is path-connected, `H₁(F; ℤ)` is free of
finite rank and `det (𝟙 - φ_*) ≠ 0` on it, every class of `H¹(T_φ; ℤ)` is an integer multiple of
the base class `[dt]`. -/
theorem exists_eq_zsmul_baseClass
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0)
    (x : (TopCat.of (MappingTorus φ)).singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ
      (ModuleCat.of ℤ ℤ) 1) : ∃ m : ℤ, x = m • baseClass φ := by
  set e := cohomologyOneEquiv φ (ModuleCat.of ℤ ℤ) hdet
  have hss : e (baseClass φ) * e (baseClass φ) = 1 := by
    rcases cohomologyOneEquiv_baseClass_eq_one_or_eq_neg_one φ hdet with h | h <;> rw [h] <;> rfl
  refine ⟨e x * e (baseClass φ), e.injective ?_⟩
  rw [map_zsmul, smul_eq_mul, mul_assoc, hss, mul_one]

/-- **The basis `[dt]` of `H¹(T_φ; ℤ)`.** If `F` is path-connected, `H₁(F; ℤ)` is free of finite
rank and `det (𝟙 - φ_*) ≠ 0` on it, the base class alone is a basis of `H¹(T_φ; ℤ)`. -/
def basisBaseClass
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0) :
    Module.Basis (Fin 1) ℤ
      ((TopCat.of (MappingTorus φ)).singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ
        (ModuleCat.of ℤ ℤ) 1) :=
  .mk (v := ![baseClass φ])
    (LinearIndependent.of_comp (cohomologyOneEquiv φ (ModuleCat.of ℤ ℤ) hdet).toLinearMap (by
      rcases cohomologyOneEquiv_baseClass_eq_one_or_eq_neg_one φ hdet with h | h <;>
        simp [Function.comp_def, h]))
    fun x _ ↦ by
      obtain ⟨m, rfl⟩ := exists_eq_zsmul_baseClass φ hdet x
      exact zsmul_mem (Submodule.subset_span (Set.mem_range_self 0)) m

/-- The vector of `basisBaseClass` is the base class. -/
@[simp]
lemma basisBaseClass_apply
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0) (i : Fin 1) :
    basisBaseClass φ hdet i = baseClass φ := by
  simp [basisBaseClass, Fin.fin_one_eq_zero i]

end Integral

end TauCeti.MappingTorus
