/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.Leray.Edge

/-!
# The first terms of the five-term exact sequence of the Leray spectral sequence

Let `pb : Sheaf J Ab ⥤ Sheaf K Ab` be an exact functor between categories of abelian sheaves on
sites `(C, J)` and `(D, K)` with right adjoint `pf`, and `c : ℤ_K ⟶ pb ℤ_J` an isomorphism of
constant sheaves; for a morphism of sites, `pb = f⁻¹`, `pf = f_*`. The Leray spectral sequence
`E₂^{p,q} = Hᵖ(C, R^q f_* F) ⇒ H^{p+q}(D, F)` (Stacks, Lemma 21.14.5 (0732)) has the five-term
exact sequence

`0 ⟶ H¹(C, f_* F) ⟶ H¹(D, F) ⟶ H⁰(C, R¹ f_* F) ⟶ H²(C, f_* F) ⟶ H²(D, F)`.

This file constructs its third map and proves exactness of the
first three terms, independently of spectral-sequence machinery. The first map is the edge map
`Sheaf.H.lerayEdge`, injective in degree one (`Sheaf.H.lerayEdge_one_injective`).

Choose a short exact sequence `0 ⟶ F ⟶ I ⟶ Q ⟶ 0` with `I` injective. Then `H¹(I) = 0`, so every
class of `H¹(D, F)` is `δ y` for a section `y` of `Q`, and `R¹ f_* F` is the cokernel of
`f_* I ⟶ f_* Q` (`Functor.rightDerivedOneIsoCokernel`, for any left exact functor). The map
`H¹(D, F) ⟶ H⁰(C, R¹ f_* F)` sends `δ y` to the image in the cokernel of `y`, read as a section of
`f_* Q` (`Sheaf.H.lerayFiveTermMap`). Exactness at `H¹(D, F)` uses the short exact sequences
`0 ⟶ f_* F ⟶ f_* I ⟶ f_* I / f_* F ⟶ 0` and
`0 ⟶ f_* I / f_* F ⟶ f_* Q ⟶ coker (f_* I ⟶ f_* Q) ⟶ 0` on `C`, the second from left exactness of
`f_*` (`Functor.shortExact_cokernelMapFToMapX₃`), and the compatibility of the edge map with the
connecting maps (`Sheaf.H.lerayEdge_one_δ_cokernelSequence`).

## Main declarations

* `CategoryTheory.Functor.rightDerivedOneIsoCokernel`: for a left exact functor `G` and a short
  exact sequence `0 ⟶ X ⟶ I ⟶ Q ⟶ 0` with `I` injective, `R¹ G (X) ≅ coker (G I ⟶ G Q)`.
* `CategoryTheory.Functor.cokernelMapFToMapX₃` and
  `CategoryTheory.Functor.shortExact_cokernelMapFToMapX₃`: the short exact sequence
  `0 ⟶ coker (G X ⟶ G I) ⟶ G Q ⟶ coker (G I ⟶ G Q) ⟶ 0`.
* `CategoryTheory.Sheaf.H.lerayFiveTermMap`: the map `H¹(D, F) →+ H⁰(C, R¹ f_* F)`.
* `CategoryTheory.Sheaf.H.exact_lerayEdge_one_lerayFiveTermMap`: exactness of
  `H¹(C, f_* F) ⟶ H¹(D, F) ⟶ H⁰(C, R¹ f_* F)`.
* `CategoryTheory.Sheaf.H.exact_lerayEdge_one_sheafAdjunctionContinuous`: the exact sequence
  `0 ⟶ H¹(C, f_* F) ⟶ H¹(D, F) ⟶ H⁰(C, R¹ f_* F)` for a morphism of sites.

## References

* [The Stacks Project, Section 21.14](https://stacks.math.columbia.edu/tag/072X), especially
  Tag 0732.
-/

public section

open CategoryTheory Abelian Limits

universe u v

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type*} [Category* D] [Abelian D]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] {S : ShortComplex C} (hS : S.ShortExact)
  [Injective S.X₂]

include hS in
/-- **The first right derived functor as a cokernel.** For a left exact functor `G` and a short
exact sequence `0 ⟶ X ⟶ I ⟶ Q ⟶ 0` with `I` injective, `R¹ G (X)` is the cokernel of
`G I ⟶ G Q`. -/
noncomputable def rightDerivedOneIsoCokernel :
    (G.rightDerived 1).obj S.X₁ ≅ cokernel (G.map S.g) :=
  let R := injectiveResolution S.X₃
  -- `G (R⁰)` has kernel `G Q` along `G (R⁰ ⟶ R¹)`, as `G` is left exact.
  let T := ShortComplex.mk (G.map R.ι₀) (G.map (R.cocomplex.d 0 1))
    (by rw [← G.map_comp]; simp)
  have hT : T.Exact := R.exact_ι₀.map_of_mono_of_preservesKernel G inferInstance inferInstance
  have : Mono T.f := inferInstanceAs (Mono (G.map R.ι₀))
  have : Epi (kernel.lift T.g T.f T.zero) := hT.epi_kernelLift
  have : IsIso (kernel.lift T.g T.f T.zero) := isIso_of_mono_of_epi _
  -- The complex computing `R¹ G (X)` is `G` applied to `I ⟶ R⁰ ⟶ R¹ ⟶ ⋯`, whose short complex
  -- in degree one is `G I ⟶ G (R⁰) ⟶ G (R¹)`.
  let T' := ShortComplex.mk (G.map (S.g ≫ R.ι₀)) (G.map (R.cocomplex.d 0 1))
    (by rw [← G.map_comp]; simp)
  let e : ((G.mapHomologicalComplex _).obj
      (R.cocomplex.augment (S.g ≫ R.ι₀) (by simp))).sc' 0 1 2 ≅ T' :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [T']) (by simp [T'])
  (R.ofShortExact hS).isoRightDerivedObj G 1 ≪≫
    eqToIso (Y := ((G.mapHomologicalComplex _).obj
        (R.cocomplex.augment (S.g ≫ R.ι₀) (by simp))).homology 1)
      (by rw [InjectiveResolution.ofShortExact_cocomplex]; rfl) ≪≫
    HomologicalComplex.homologyIsoSc' _ 0 1 2 (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso e ≪≫
    T'.homologyIsoCokernelLift ≪≫
    cokernelIsoOfEq (show kernel.lift T'.g T'.f T'.zero = G.map S.g ≫ kernel.lift T.g T.f T.zero by
      ext; simp [T, T']) ≪≫
    cokernelCompIsIso _ _

section CokernelComparison

variable {C' : Type*} [Category* C'] [Abelian C'] (G' : C' ⥤ D) [G'.Additive]
  [PreservesFiniteLimits G'] {S' : ShortComplex C'} (hS' : S'.ShortExact)

/-- For a short complex `X ⟶ I ⟶ Q`, the morphism `coker (G X ⟶ G I) ⟶ G Q` induced by
`G I ⟶ G Q`. -/
noncomputable def cokernelMapFToMapX₃ : cokernel (G'.map S'.f) ⟶ G'.obj S'.X₃ :=
  cokernel.desc _ (G'.map S'.g) (by rw [← G'.map_comp, S'.zero, G'.map_zero])

omit [PreservesFiniteLimits G'] in
/-- `coker (G X ⟶ G I) ⟶ G Q` restricts to `G I ⟶ G Q` along the projection. -/
@[reassoc (attr := simp)]
lemma π_cokernelMapFToMapX₃ :
    cokernel.π (G'.map S'.f) ≫ G'.cokernelMapFToMapX₃ (S' := S') = G'.map S'.g :=
  cokernel.π_desc _ _ _

include hS'

omit [G'.Additive] in
/-- For a left exact functor `G` and a short exact sequence `0 ⟶ X ⟶ I ⟶ Q ⟶ 0`, the sequence
`0 ⟶ G X ⟶ G I ⟶ coker (G X ⟶ G I) ⟶ 0` is short exact. -/
lemma shortExact_cokernelSequence_map_f :
    (ShortComplex.mk (G'.map S'.f) (cokernel.π (G'.map S'.f)) (cokernel.condition _)).ShortExact :=
  have := hS'.mono_f
  { exact := ShortComplex.cokernelSequence_exact _
    mono_f := inferInstanceAs (Mono (G'.map S'.f)) }

/-- For a left exact functor `G` and a short exact sequence `0 ⟶ X ⟶ I ⟶ Q ⟶ 0`, the sequence
`0 ⟶ coker (G X ⟶ G I) ⟶ G Q ⟶ coker (G I ⟶ G Q) ⟶ 0` is short exact. -/
lemma shortExact_cokernelMapFToMapX₃ :
    (ShortComplex.mk (G'.cokernelMapFToMapX₃ (S' := S')) (cokernel.π (G'.map S'.g)) (by
        rw [← cancel_epi (cokernel.π (G'.map S'.f)), π_cokernelMapFToMapX₃_assoc]
        simp)).ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := inferInstanceAs (Epi (cokernel.π _)) }
  · -- It has the same image as `G I ⟶ G Q`, through the epimorphism `G I ⟶ coker (G X ⟶ G I)`.
    let φ : ShortComplex.mk (G'.map S'.g) (cokernel.π (G'.map S'.g)) (cokernel.condition _) ⟶
        ShortComplex.mk (G'.cokernelMapFToMapX₃ (S' := S')) (cokernel.π (G'.map S'.g)) (by
          rw [← cancel_epi (cokernel.π (G'.map S'.f)), π_cokernelMapFToMapX₃_assoc]
          simp) :=
      { τ₁ := cokernel.π (G'.map S'.f), τ₂ := 𝟙 _, τ₃ := 𝟙 _ }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1
      (ShortComplex.cokernelSequence_exact _)
  · exact (hS'.exact.map_of_mono_of_preservesKernel G' hS'.mono_f inferInstance).mono_cokernelDesc

end CokernelComparison

end CategoryTheory.Functor


namespace CategoryTheory.Sheaf.H

open AddCommGrpCat

universe w w₁ w₂

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  {D : Type*} [Category* D] {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasExt.{w₁} (Sheaf J AddCommGrpCat.{w})] [HasExt.{w₂} (Sheaf K AddCommGrpCat.{w})]
  {pb : Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w}} [pb.Additive]
  [PreservesFiniteLimits pb] [PreservesFiniteColimits pb]
  {pf : Sheaf K AddCommGrpCat.{w} ⥤ Sheaf J AddCommGrpCat.{w}} [pf.Additive]
  [PreservesFiniteLimits pf] (adj : pb ⊣ pf)
  (c : (constantSheaf K AddCommGrpCat.{w}).obj (of (ULift ℤ)) ⟶
    pb.obj ((constantSheaf J AddCommGrpCat.{w}).obj (of (ULift ℤ))))
  {S : ShortComplex (Sheaf K AddCommGrpCat.{w})} (hS : S.ShortExact)

noncomputable section

include hS in
/-- The edge map in degree one on a class `δ v`, for the short exact sequence
`0 ⟶ f_* F ⟶ f_* I ⟶ f_* I / f_* F ⟶ 0`, is `δ` of the edge map in degree zero on the image of
`v` in `H⁰(C, f_* Q)`, for the short exact sequence `0 ⟶ F ⟶ I ⟶ Q ⟶ 0`. -/
lemma lerayEdge_one_δ_cokernelSequence
    (v : H (cokernel (pf.map S.f)) 0) :
    lerayEdge adj c S.X₁ 1 (H.δ (pf.shortExact_cokernelSequence_map_f hS) 0 1 rfl v) =
      H.δ hS 0 1 rfl (lerayEdge adj c S.X₃ 0 (H.map pf.cokernelMapFToMapX₃ 0 v)) := by
  let φ : (ShortComplex.mk (pf.map S.f) (cokernel.π (pf.map S.f))
      (cokernel.condition _)).map pb ⟶ S :=
    { τ₁ := adj.counit.app S.X₁
      τ₂ := adj.counit.app S.X₂
      τ₃ := pb.map pf.cokernelMapFToMapX₃ ≫ adj.counit.app S.X₃
      comm₁₂ := (adj.counit.naturality S.f).symm
      comm₂₃ := by
        dsimp only [ShortComplex.map_g]
        rw [← pb.map_comp_assoc, Functor.π_cokernelMapFToMapX₃]
        exact (adj.counit.naturality S.g).symm }
  rw [lerayEdge_apply, lerayEdge_apply, pullback_naturality, ← H.map_comp_apply]
  exact map_pullback_δ pb c (pf.shortExact_cokernelSequence_map_f hS) hS φ 0 1 rfl v


section FiveTerm

variable [IsIso c]

omit [pf.Additive] [PreservesFiniteLimits pf] in
/-- When the comparison `c` of constant sheaves is an isomorphism, the edge map in degree zero
is an isomorphism `H⁰(C, f_* G) ≃+ H⁰(D, G)`. -/
def lerayEdgeZeroEquiv (G : Sheaf K AddCommGrpCat.{w}) : H (pf.obj G) 0 ≃+ H G 0 :=
  AddEquiv.ofBijective (lerayEdge adj c G 0) (lerayEdge_zero_bijective adj c G)

omit [pf.Additive] [PreservesFiniteLimits pf] in
/-- `lerayEdgeZeroEquiv` is the edge map in degree zero. -/
@[simp]
lemma lerayEdgeZeroEquiv_apply {G : Sheaf K AddCommGrpCat.{w}} (x : H (pf.obj G) 0) :
    lerayEdgeZeroEquiv adj c G x = lerayEdge adj c G 0 x :=
  (rfl)

/-- For a short complex `F ⟶ I ⟶ Q`, the map
`H⁰(D, Q) ≅ H⁰(C, f_* Q) ⟶ H⁰(C, coker (f_* I ⟶ f_* Q))`, through the inverse of the edge map in
degree zero. -/
def lerayFiveTermAux : H S.X₃ 0 →+ H (cokernel (pf.map S.g)) 0 :=
  (H.map (cokernel.π (pf.map S.g)) 0).comp (lerayEdgeZeroEquiv adj c S.X₃).symm.toAddMonoidHom

include hS in
/-- `lerayFiveTermAux` kills the image of `H⁰(D, I) ⟶ H⁰(D, Q)`, the kernel of
`δ : H⁰(D, Q) ⟶ H¹(D, F)`. -/
lemma ker_δ_le_ker_lerayFiveTermAux :
    (H.δ hS 0 1 rfl).ker ≤ (lerayFiveTermAux adj c (S := S)).ker := by
  intro y hy
  obtain ⟨z, rfl⟩ := (exact_map_δ hS 0 1 rfl y).1 hy
  obtain ⟨w, rfl⟩ := (lerayEdge_zero_bijective adj c S.X₂).2 z
  rw [AddMonoidHom.mem_ker, lerayFiveTermAux, AddMonoidHom.comp_apply, ← lerayEdge_naturality,
    ← lerayEdgeZeroEquiv_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_apply,
    show H.map (pf.map S.g) 0 w = H.map pf.cokernelMapFToMapX₃ 0
      (H.map (cokernel.π (pf.map S.f)) 0 w) by
        rw [← H.map_comp_apply, Functor.π_cokernelMapFToMapX₃]]
  exact (exact_map_map (pf.shortExact_cokernelMapFToMapX₃ hS) 0).apply_apply_eq_zero _

variable [Injective S.X₂]

/-- The map `H¹(D, F) ⟶ H⁰(C, coker (f_* I ⟶ f_* Q))` of the five-term exact sequence, for a
short exact sequence `0 ⟶ F ⟶ I ⟶ Q ⟶ 0` with `I` injective: every class of `H¹(D, F)` is `δ y`
for a section `y` of `Q`, sent to the image of `y` in the cokernel. -/
def lerayFiveTermCokernelMap : H S.X₁ 1 →+ H (cokernel (pf.map S.g)) 0 :=
  (H.δ hS 0 1 rfl).liftOfSurjective (δ_surjective hS 0 1 rfl inferInstance)
    ⟨lerayFiveTermAux adj c, ker_δ_le_ker_lerayFiveTermAux adj c hS⟩

/-- `lerayFiveTermCokernelMap` sends `δ y`, for a section `y` of `Q`, to the image of `y` in
`H⁰(C, coker (f_* I ⟶ f_* Q))`. -/
lemma lerayFiveTermCokernelMap_δ (y : H S.X₃ 0) :
    lerayFiveTermCokernelMap adj c hS (H.δ hS 0 1 rfl y) = lerayFiveTermAux adj c y :=
  AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ y

/-- **Exactness of `H¹(C, f_* F) ⟶ H¹(D, F) ⟶ H⁰(C, coker (f_* I ⟶ f_* Q))`**, the middle of the
first three terms of the five-term exact sequence of the Leray spectral sequence. -/
theorem exact_lerayEdge_one_lerayFiveTermCokernelMap :
    Function.Exact (lerayEdge adj c S.X₁ 1) (lerayFiveTermCokernelMap adj c hS) := by
  intro x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := δ_surjective hS 0 1 rfl inferInstance x
    rw [lerayFiveTermCokernelMap_δ, lerayFiveTermAux, AddMonoidHom.comp_apply] at hx
    obtain ⟨v, hv⟩ := (exact_map_map (pf.shortExact_cokernelMapFToMapX₃ hS) 0 _).1 hx
    refine ⟨H.δ (pf.shortExact_cokernelSequence_map_f hS) 0 1 rfl v, ?_⟩
    rw [lerayEdge_one_δ_cokernelSequence adj c hS, hv, ← lerayEdgeZeroEquiv_apply,
      AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply]
  · rintro ⟨x, rfl⟩
    have := subsingleton_H_succ_obj_of_injective adj S.X₂ 0
    obtain ⟨v, rfl⟩ := δ_surjective (pf.shortExact_cokernelSequence_map_f hS) 0 1 rfl this x
    rw [lerayEdge_one_δ_cokernelSequence adj c hS, lerayFiveTermCokernelMap_δ, lerayFiveTermAux,
      AddMonoidHom.comp_apply, ← lerayEdgeZeroEquiv_apply, AddEquiv.coe_toAddMonoidHom,
      AddEquiv.symm_apply_apply]
    exact (exact_map_map (pf.shortExact_cokernelMapFToMapX₃ hS) 0).apply_apply_eq_zero v

variable [EnoughInjectives (Sheaf K AddCommGrpCat.{w})]

/-- **The map `H¹(D, F) ⟶ H⁰(C, R¹ f_* F)` of the five-term exact sequence** of the Leray spectral
sequence, for a short exact sequence `0 ⟶ F ⟶ I ⟶ Q ⟶ 0` with `I` injective: the map to
`H⁰(C, coker (f_* I ⟶ f_* Q))` followed by the identification
`coker (f_* I ⟶ f_* Q) ≅ R¹ f_* F` (`Functor.rightDerivedOneIsoCokernel`). -/
def lerayFiveTermMap : H S.X₁ 1 →+ H ((pf.rightDerived 1).obj S.X₁) 0 :=
  (H.map (pf.rightDerivedOneIsoCokernel hS).inv 0).comp (lerayFiveTermCokernelMap adj c hS)

/-- **The five-term exact sequence of the Leray spectral sequence, first three terms**: when the
comparison `c` of constant sheaves is an isomorphism, the sequence
`0 ⟶ H¹(C, f_* F) ⟶ H¹(D, F) ⟶ H⁰(C, R¹ f_* F)` is exact: the edge map is injective
(`lerayEdge_one_injective`), and its image is the kernel of `lerayFiveTermMap`. -/
theorem exact_lerayEdge_one_lerayFiveTermMap :
    Function.Exact (lerayEdge adj c S.X₁ 1) (lerayFiveTermMap adj c hS) :=
  (exact_lerayEdge_one_lerayFiveTermCokernelMap adj c hS).comp_injective _
    (H.map_injective (pf.rightDerivedOneIsoCokernel hS).inv) (map_zero _)

end FiveTerm

end

section Sites

/-- **The five-term exact sequence for a morphism of sites, first three terms.** For a morphism
of sites given by `u : C ⥤ D`, with pushforward `f_* = u.sheafPushforwardContinuous` and exact
inverse image `f⁻¹ = u.sheafPullback`, and a short exact sequence `0 ⟶ F ⟶ I ⟶ Q ⟶ 0` of abelian
sheaves on `D` with `I` injective, the sequence `0 ⟶ H¹(C, f_* F) ⟶ H¹(D, F) ⟶ H⁰(C, R¹ f_* F)`
is exact: the start of the five-term exact sequence of the Leray spectral sequence (Stacks,
Lemma 21.14.5 (0732)). -/
theorem exact_lerayEdge_one_sheafAdjunctionContinuous
    (u : C ⥤ D) [u.IsContinuous J K]
    [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint] [u.Final]
    [PreservesFiniteLimits (u.sheafPullback AddCommGrpCat.{w} J K)]
    [EnoughInjectives (Sheaf K AddCommGrpCat.{w})] [Injective S.X₂] :
    Function.Injective (lerayEdge (u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K)
      (u.sheafPullbackConstantSheafIso AddCommGrpCat.{w} J K (of (ULift ℤ))).inv S.X₁ 1) ∧
    Function.Exact (lerayEdge (u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K)
        (u.sheafPullbackConstantSheafIso AddCommGrpCat.{w} J K (of (ULift ℤ))).inv S.X₁ 1)
      (lerayFiveTermMap (u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K)
        (u.sheafPullbackConstantSheafIso AddCommGrpCat.{w} J K (of (ULift ℤ))).inv hS) :=
  ⟨lerayEdge_one_injective _ _ _, exact_lerayEdge_one_lerayFiveTermMap _ _ hS⟩

end Sites

end CategoryTheory.Sheaf.H
