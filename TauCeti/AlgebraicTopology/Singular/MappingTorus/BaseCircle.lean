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
import TauCeti.AlgebraicTopology.Singular.ModuleChains.HomologyZero

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
  isomorphisms `H₁(ℝ/ℤ; ℤ) ≅ ℤ`, so they differ by a sign, the value of `circleWangClass` on the
  circuit class `AddCircle.fundamentalClass 1`. This value is `-1`
  (`TauCeti.MappingTorus.circleWangClass_hom_fundamentalClass`), computed on the chains of the
  cyclic cover `pt × ℝ` of the circle: the circuit lifts to the path from height `0` to height
  `1`, whose boundary is `(𝟙 - τ_*)(-[0])` for the deck transformation `τ` raising the height by
  one, so the Wang connecting morphism sends the circuit class to `-[pt]`. Thus the Wang class of
  the circle is minus the winding number (`TauCeti.MappingTorus.circleWangClass_hom_apply`,
  `TauCeti.MappingTorus.circleWangClass_eq_neg_singularKronecker_angularClass`), and
  `⟨[dt], h⟩ = -ε(δ h)` on every mapping torus
  (`TauCeti.MappingTorus.singularKronecker_baseClass_eq_neg_wangClass`,
  `TauCeti.MappingTorus.singularKronecker_baseClass_apply_eq_neg`).
* **The period homomorphism.** For a path-connected fibre the periods `⟨[dt], h⟩` take every
  integer value (`TauCeti.MappingTorus.singularKronecker_baseClass_surjective`). If moreover
  `H₁(F; ℤ)` is free of finite rank and `det (𝟙 - φ_*) ≠ 0` on it, the period of `h` vanishes
  exactly when `h` has finite order
  (`TauCeti.MappingTorus.singularKronecker_baseClass_eq_zero_iff`): the kernel of the period
  homomorphism is the torsion of `H₁(T_φ; ℤ)`, so it is injective only when `H₁(T_φ; ℤ)` is
  torsion-free.
* **A generator.** Under the same hypotheses the identification `H¹(T_φ; ℤ) ≃ ℤ` of
  `TauCeti.MappingTorus.cohomologyOneEquiv` sends `[dt]` to `-1`
  (`TauCeti.MappingTorus.cohomologyOneEquiv_baseClass`), so every class of
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

/-- With module coefficients, the Wang class of a class `c ∈ H₁(T_φ)` is the augmentation of its
image `δ c ∈ H₀(F)` under the Wang connecting morphism. -/
theorem wangClass_hom_apply {k : Type*} [Ring k] [HasCoproducts.{w} (ModuleCat.{v} k)]
    (U : ModuleCat.{v} k)
    (c : ((singularHomologyFunctor (ModuleCat.{v} k) 1).obj U).obj (TopCat.of (MappingTorus φ))) :
    (wangClass U φ).hom c = ((TopCat.of F).singularHomology₀ε U).hom ((wangδ φ U 0).hom c) :=
  -- The source of `wangδ` is the homology in degree `0 + 1`, which is the degree `1` of
  -- `wangClass` only definitionally, so `rw [wangClass_def]` cannot form the motive.
  (rfl)

/-- `TauCeti.MappingTorus.wangClass_hom_apply` for a class of `H₁(T_φ; k)` written as the homology
of `TauCeti.singularChains k`, the spelling of `ContinuousMap.singularHomologyMap`. -/
theorem wangClass_hom_apply_singularChains {k : Type w} [Ring k]
    (c : ((singularChains k).obj (TopCat.of (MappingTorus φ))).homology 1) :
    (wangClass (ModuleCat.of k k) φ).hom c =
      ((TopCat.of F).singularHomology₀ε (ModuleCat.of k k)).hom
        ((wangδ φ (ModuleCat.of k k) 0).hom c) :=
  (rfl)

/-- For a path-connected fibre, the Wang class of a class `c ∈ H₁(T_φ)` vanishes exactly when its
image `δ c ∈ H₀(F)` under the Wang connecting morphism does, since the augmentation is injective. -/
theorem wangClass_hom_eq_zero_iff {k : Type*} [Ring k] [HasCoproducts.{w} (ModuleCat.{v} k)]
    (U : ModuleCat.{v} k) [PathConnectedSpace F]
    (c : ((singularHomologyFunctor (ModuleCat.{v} k) 1).obj U).obj (TopCat.of (MappingTorus φ))) :
    (wangClass U φ).hom c = 0 ↔ (wangδ φ U 0).hom c = 0 := by
  rw [wangClass_hom_apply, ← map_zero ((TopCat.of F).singularHomology₀ε U).hom]
  exact ((ModuleCat.mono_iff_injective _).1 inferInstance).eq_iff

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

/-! The value of the integral Wang class `H₁(ℝ/ℤ; ℤ) ⟶ ℤ` of the circle on the circuit class
`AddCircle.fundamentalClass 1` is computed on the mapping torus `T` of the identity of a point,
the circle of `circleWangClass`. The loop `t ↦ [⋆, t]` of `T` lifts to the path `t ↦ (⋆, t)` of the
cylinder `pt × ℝ`, whose boundary `[⋆, 1] - [⋆, 0]` is `(𝟙 - τ_*)(-[⋆, 0])` for the deck
transformation `τ` raising the height by one. So the Wang connecting morphism sends the class of
the loop to the class of `-[⋆]`, of augmentation `-1`, while the projection to `ℝ/ℤ` sends it to the
circuit class. -/

/-- The path `t ↦ (⋆, t)` of the cylinder `pt × ℝ`, from height `0` to height `1`. -/
private def unitHeightPath : C(unitInterval, PUnit.{1} × ℝ) :=
  ⟨fun t ↦ (PUnit.unit, (t : ℝ)), by fun_prop⟩

/-- The image of `unitHeightPath` in the mapping torus of the identity of a point is a loop, so its
chain is a cycle. -/
private lemma d_pathChain_coverMap_comp_unitHeightPath :
    ((singularChains ℤ).obj (TopCat.of (MappingTorus (Homeomorph.refl PUnit.{1})))).d 1 0
      (pathChain ℤ (X := TopCat.of (MappingTorus (Homeomorph.refl PUnit.{1})))
        ((coverMap (Homeomorph.refl PUnit.{1})).comp unitHeightPath)) = 0 := by
  have h : mk (Homeomorph.refl PUnit.{1}) PUnit.unit 1 = mk _ PUnit.unit 0 := by
    simpa using mk_apply_add_one (Homeomorph.refl PUnit.{1}) PUnit.unit 0
  simp [unitHeightPath, h]

/-- The cycle of `T` given by the loop `t ↦ [⋆, t]` of the mapping torus `T` of the identity of a
point. -/
private def unitLoopCycle :
    ((singularChains ℤ).obj (TopCat.of (MappingTorus (Homeomorph.refl PUnit.{1})))).cycles 1 :=
  ((singularChains ℤ).obj (TopCat.of (MappingTorus (Homeomorph.refl PUnit.{1})))).cyclesMk
    (pathChain ℤ (X := TopCat.of (MappingTorus (Homeomorph.refl PUnit.{1})))
      ((coverMap (Homeomorph.refl PUnit.{1})).comp unitHeightPath)) 0 (by simp)
    d_pathChain_coverMap_comp_unitHeightPath

/-- The class in `H₁(T; ℤ)` of the loop `t ↦ [⋆, t]` of the mapping torus `T` of the identity of a
point. -/
private def unitLoopClass :
    ((singularChains ℤ).obj (TopCat.of (MappingTorus (Homeomorph.refl PUnit.{1})))).homology 1 :=
  ((singularChains ℤ).obj (TopCat.of (MappingTorus (Homeomorph.refl PUnit.{1})))).homologyπ 1
    unitLoopCycle

/-- The Wang class of the mapping torus of the identity of a point is `-1` on the class of the loop
`t ↦ [⋆, t]`: the deck transformation raises the height of the cylinder by one. -/
private lemma wangClass_unitLoopClass :
    (wangClass (ModuleCat.of ℤ ℤ) (Homeomorph.refl PUnit.{1})).hom unitLoopClass = -1 := by
  let φ := Homeomorph.refl PUnit.{1}
  let x₂ := pathChain ℤ (X := TopCat.of (PUnit.{1} × ℝ)) unitHeightPath
  let x₁ := -pointChain ℤ (X := TopCat.of (PUnit.{1} × ℝ)) (PUnit.unit, (0 : ℝ))
  -- The lift `x₂` of the loop has boundary `(𝟙 - τ_*) x₁`.
  have hx₂ : (coverChainMap φ (ModuleCat.of ℤ ℤ)).f 1 x₂ =
      pathChain ℤ (X := TopCat.of (MappingTorus φ)) ((coverMap φ).comp unitHeightPath) := by
    rw [coverChainMap_def]
    exact singularChains_map_f_pathChain _ _
  have hτ : ((deckChainMap φ (ModuleCat.of ℤ ℤ)).f 0).hom x₁ =
      -pointChain ℤ (X := TopCat.of (PUnit.{1} × ℝ)) (PUnit.unit, (1 : ℝ)) := by
    have hdeck : deck φ ((PUnit.unit, 0) : PUnit.{1} × ℝ) = (PUnit.unit, 1) := by simp
    rw [deckChainMap_def, map_neg, singularChains_map_f_simplexChain,
      TopCat.toSSet_map_app_toSSetObj₀Equiv_symm]
    simp [hdeck]
  have hx₁ : ((𝟙 _ - deckChainMap φ (ModuleCat.of ℤ ℤ)).f 0) x₁ =
      ((singularChains ℤ).obj (TopCat.of (PUnit.{1} × ℝ))).d 1 0 x₂ := by
    rw [singularChains_d_pathChain, HomologicalComplex.sub_f_apply, HomologicalComplex.id_f]
    simp only [ModuleCat.hom_sub, LinearMap.sub_apply, ModuleCat.hom_id, LinearMap.id_apply, hτ]
    simp [x₁, unitHeightPath, sub_eq_add_neg, add_comm]
  have hδ := (cyclicCoverShortComplex_shortExact φ (ModuleCat.of ℤ ℤ)).δ_apply 1 0 (by simp) _
    d_pathChain_coverMap_comp_unitHeightPath x₂ hx₂ x₁ hx₁ 0 ChainComplex.next_nat_zero
  -- The Wang class is the augmentation of the connecting morphism, read in `pt × ℝ`.
  rw [wangClass_hom_apply_singularChains, wangδ_def, ConcreteCategory.comp_apply]
  refine (ConcreteCategory.congr_hom (singularHomologyMap_singularHomology₀ε (ModuleCat.of ℤ ℤ)
    (TopCat.ofHom (ContinuousMap.HomotopyEquiv.prodZeroSection PUnit.{1} ℝ).symm.toFun)) _).trans
    ((congrArg _ hδ).trans ((singularHomology₀ε_homologyπ_cyclesMk x₁ _).trans ?_))
  rw [map_neg, singularAugment_simplexChain]

/-- The projection of the mapping torus of the identity of a point to `ℝ/ℤ` sends the class of the
loop `t ↦ [⋆, t]` to the circuit class. -/
private lemma homologyMap_proj_unitLoopClass :
    (homologyMap ((singularChains ℤ).map (TopCat.ofHom
      ⟨proj (Homeomorph.refl PUnit.{1}), continuous_proj _⟩)) 1).hom unitLoopClass =
      AddCircle.fundamentalClass 1 := by
  let P := (singularChains ℤ).map
    (TopCat.ofHom ⟨proj (Homeomorph.refl PUnit.{1}), continuous_proj _⟩)
  rw [AddCircle.fundamentalClass_eq_homologyπ 1 ((cyclesMap P 1).hom unitLoopCycle) ?_]
  · exact ConcreteCategory.congr_hom (homologyπ_naturality P 1) _
  · rw [← ConcreteCategory.comp_apply, cyclesMap_i, ConcreteCategory.comp_apply]
    refine (congrArg _ (HomologicalComplex.i_cyclesMk (C := ModuleCat ℤ) _ _ _ _ _)).trans ?_
    rw [singularChains_map_f_pathChain, AddCircle.circuitSimplex_def]
    congr 2
    ext t
    simp only [unitHeightPath, ConcreteCategory.hom_ofHom, ContinuousMap.comp_apply,
      coverMap_apply, ContinuousMap.coe_mk, proj_mk, Path.coe_toContinuousMap,
      AddCircle.zsmulLoop_zero_apply_eq_coe]
    simp

/-- **The sign of the Wang class of the circle is `-1`.** The integral Wang class `ε ∘ δ` of the
circle takes the value `-1` on the circuit class `AddCircle.fundamentalClass 1`, so it is minus the
winding number (`circleWangClass_eq_neg_singularKronecker_angularClass`). -/
@[simp]
theorem circleWangClass_hom_fundamentalClass :
    (circleWangClass (ModuleCat.of ℤ ℤ)).hom (AddCircle.fundamentalClass 1) = -1 :=
  (congrArg (circleWangClass (ModuleCat.of ℤ ℤ)).hom homologyMap_proj_unitLoopClass.symm).trans
    ((ConcreteCategory.congr_hom
      (singularHomologyMap_proj_comp_circleWangClass (ModuleCat.of ℤ ℤ)) unitLoopClass).trans
      wangClass_unitLoopClass)

/-- The integral Wang class of the circle is minus the winding number, since its value on the
circuit class is `-1`. -/
theorem circleWangClass_hom_apply
    (c : ((singularChains ℤ).obj (TopCat.of UnitAddCircle)).homology 1) :
    (circleWangClass (ModuleCat.of ℤ ℤ)).hom c = -AddCircle.firstHomologyAddEquiv 1 c := by
  -- The source of `circleWangClass` is `H₁(ℝ/ℤ; ℤ)` written through `singularHomologyFunctor`,
  -- definitionally the homology of `singularChains ℤ` used by `AddCircle.fundamentalClass`; `rw`
  -- cannot form the motive across the two spellings, so these steps are chained in term mode.
  refine (congrArg _ (AddCircle.eq_firstHomologyAddEquiv_zsmul_fundamentalClass 1 c)).trans
    ((map_zsmul _ _ _).trans ((smul_eq_mul _ _).trans ?_))
  rw [circleWangClass_hom_fundamentalClass, mul_neg_one]

section Integral

-- As in `TauCeti.AlgebraicTopology.Cohomology.AddCircle`, morphisms of `ℤ`-modules are scaled
-- through the linear structure of `ModuleCat ℤ`, under which the Kronecker maps are linear.
attribute [local instance 1100] ModuleCat.instLinear

/-- **The Wang class of the circle is minus the winding number.** With integer coefficients,
`circleWangClass` is minus the Kronecker evaluation of the angular class, that is minus the winding
number. -/
theorem circleWangClass_eq_neg_singularKronecker_angularClass :
    circleWangClass (ModuleCat.of ℤ ℤ) =
      -(TopCat.of UnitAddCircle).singularKronecker ℤ 1 (AddCircle.angularClass 1) :=
  ModuleCat.hom_ext (LinearMap.ext fun c ↦ (circleWangClass_hom_apply c).trans (by
    rw [ModuleCat.hom_neg, LinearMap.neg_apply]
    exact congrArg _ (AddCircle.singularKronecker_angularClass 1 c).symm))

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

/-- **The base class evaluates through the Wang class.** On every mapping torus,
`⟨[dt], h⟩ = -ε(δ h)` for the Wang class `ε ∘ δ`, since the Wang class of the circle is minus the
winding number (`circleWangClass_eq_neg_singularKronecker_angularClass`). -/
theorem singularKronecker_baseClass_eq_neg_wangClass :
    (TopCat.of (MappingTorus φ)).singularKronecker ℤ 1 (baseClass φ) =
      -wangClass (ModuleCat.of ℤ ℤ) φ := by
  rw [wangClass_eq_singularHomologyMap_proj_comp_circleWangClass,
    circleWangClass_eq_neg_singularKronecker_angularClass, Preadditive.comp_neg, neg_neg, baseClass,
    TopCat.singularKronecker_naturality]
  -- The chain coefficients `𝟙_ (ModuleCat ℤ)` and `ModuleCat.of ℤ ℤ` agree by definition.
  rfl

/-- **The periods of the base class through the Wang sequence**: `⟨[dt], h⟩ = -ε(δ h)` for the
Wang connecting morphism `δ` and the augmentation `ε` of `H₀(F)`. -/
theorem singularKronecker_baseClass_apply_eq_neg
    (c : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of (MappingTorus φ))) :
    (TopCat.of (MappingTorus φ)).singularKronecker ℤ 1 (baseClass φ) c =
      -(TopCat.of F).singularHomology₀ε (ModuleCat.of ℤ ℤ) ((wangδ φ (ModuleCat.of ℤ ℤ) 0).hom c) :=
  (congrArg (fun f ↦ f.hom c) (singularKronecker_baseClass_eq_neg_wangClass φ)).trans (by
    rw [ModuleCat.hom_neg, LinearMap.neg_apply, wangClass_hom_apply])

variable [PathConnectedSpace F]

/-- **The period homomorphism is onto.** For a path-connected fibre, every integer is the period
`⟨[dt], h⟩` of some class `h ∈ H₁(T_φ; ℤ)`. -/
theorem singularKronecker_baseClass_surjective :
    Function.Surjective ((TopCat.of (MappingTorus φ)).singularKronecker ℤ 1 (baseClass φ)) := by
  -- The Wang connecting morphism is onto `H₀(F)`, which the augmentation identifies with `ℤ`.
  have hδ := (ModuleCat.epi_iff_surjective (wangδ φ (ModuleCat.of ℤ ℤ) 0)).1 inferInstance
  have hε := (ModuleCat.epi_iff_surjective
    ((TopCat.of F).singularHomology₀ε (ModuleCat.of ℤ ℤ))).1 inferInstance
  intro n
  obtain ⟨x, hx⟩ := hε (-n)
  obtain ⟨c, rfl⟩ := hδ x
  exact ⟨c, (singularKronecker_baseClass_apply_eq_neg φ c).trans (by rw [hx, neg_neg])⟩

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
  -- The augmentation `H₀(F) ⟶ ℤ` is an isomorphism, so `ε(δ c) = 0` exactly when `δ c = 0`.
  have hε : Function.Injective ((TopCat.of F).singularHomology₀ε (ModuleCat.of ℤ ℤ)) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hker : (wangδ φ (ModuleCat.of ℤ ℤ) 0).hom c = 0 ↔ c ∈ Submodule.torsion ℤ _ := by
    rw [← LinearMap.mem_ker, ker_wangδ_zero_eq_torsion φ hdet]
  refine (Eq.congr_left (singularKronecker_baseClass_apply_eq_neg φ c)).trans ?_
  rw [neg_eq_zero, ← hker]
  exact hε.eq_iff' (map_zero _)

/-- **The base class corresponds to `-1`.** Under the hypotheses of `cohomologyOneEquiv`, the
identification `H¹(T_φ; ℤ) ≃ ℤ`, under which a class evaluates to `ε(δ h)` times its image, sends
the base class `[dt]` to `-1`. -/
theorem cohomologyOneEquiv_baseClass
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0) :
    cohomologyOneEquiv φ (ModuleCat.of ℤ ℤ) hdet (baseClass φ) = -1 := by
  rw [← (cohomologyOneEquiv φ (ModuleCat.of ℤ ℤ) hdet).apply_symm_apply (-1)]
  congr 1
  -- Both classes evaluate to `-ε(δ c)`, and the Kronecker map is injective in degree one since
  -- `H₀(T_φ; ℤ)` is free.
  refine ((TopCat.of (MappingTorus φ)).singularKronecker_bijective_of_projective_homology_lt
    (R := ModuleCat.of ℤ ℤ) (ModuleCat.of ℤ ℤ) 1 (fun j hj ↦ ?_)).1
    (ModuleCat.hom_ext (LinearMap.ext fun c ↦ ?_))
  · obtain rfl : j = 0 := by omega
    exact ModuleCat.projective_of_free (Module.Free.chooseBasis ℤ _)
  · refine (singularKronecker_baseClass_apply_eq_neg φ c).trans (Eq.trans ?_
      (singularKronecker_cohomologyOneEquiv_symm_apply φ (ModuleCat.of ℤ ℤ) hdet (-1) c).symm)
    rw [smul_eq_mul, mul_neg_one]

/-- **The base class generates `H¹(T_φ; ℤ)`.** If `F` is path-connected, `H₁(F; ℤ)` is free of
finite rank and `det (𝟙 - φ_*) ≠ 0` on it, every class of `H¹(T_φ; ℤ)` is an integer multiple of
the base class `[dt]`. -/
theorem exists_eq_zsmul_baseClass
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0)
    (x : (TopCat.of (MappingTorus φ)).singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ
      (ModuleCat.of ℤ ℤ) 1) : ∃ m : ℤ, x = m • baseClass φ := by
  refine ⟨-cohomologyOneEquiv φ (ModuleCat.of ℤ ℤ) hdet x,
    (cohomologyOneEquiv φ (ModuleCat.of ℤ ℤ) hdet).injective ?_⟩
  rw [map_zsmul, cohomologyOneEquiv_baseClass, smul_eq_mul, neg_mul_neg, mul_one]

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
      simp only [Function.comp_def, Matrix.cons_val_fin_one, LinearEquiv.coe_coe,
        linearIndependent_unique_iff]
      rw [cohomologyOneEquiv_baseClass]
      exact neg_ne_zero.2 one_ne_zero))
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
