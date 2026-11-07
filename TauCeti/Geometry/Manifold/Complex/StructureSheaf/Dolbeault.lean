/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.Analysis.Complex.Wirtinger.DolbeaultLemma
public import TauCeti.Analysis.Complex.Wirtinger.Holomorphic
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Basic
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype
public import TauCeti.Geometry.Manifold.Sheaf.Smooth.Cech
public import TauCeti.Topology.Sheaves.Cech.OneVanishing

/-!
# The Dolbeault sequence and `H¹(D, 𝒪) = 0` on discs

On an open set `U` of the complex plane, the holomorphic functions are the smooth functions
annihilated by the Cauchy-Riemann operator `\bar∂`. This file packages this as an exact
sequence of sheaves of complex vector spaces on `U`,
`0 ⟶ 𝒪 ⟶ ℰ ⟶ ℰ`, where `𝒪` is the holomorphic structure sheaf, `ℰ` is the sheaf of smooth
complex-valued functions and the last map is `f ↦ \bar∂ f` (`TauCeti.dolbeaultSequence`).

The sheaf `ℰ` is fine, so it has no higher Čech cohomology. If moreover the equation
`\bar∂ g = f` can be solved with `g` smooth on `U` for every smooth `f` on `U`, then the
structure sheaf of `U` has zero degree one Čech cohomology. By the Dolbeault lemma this applies to
every disc, including the whole plane: `H¹(D, 𝒪) = 0`. In the theory of Riemann surfaces this
is the acyclicity of coordinate discs for the structure sheaf in degree one.

Sections of the sheaves over an open set `V` of `U` are functions on `V`. Their Wirtinger
derivatives are computed after extending them by zero to the whole plane, which does not change
them near the points of the open set `V`.

## Main definitions

* `TauCeti.dolbeaultInclusion U`: the inclusion `𝒪 ⟶ ℰ` of holomorphic into smooth functions.
* `TauCeti.dolbeaultDbar U`: the Cauchy-Riemann operator `ℰ ⟶ ℰ`, `f ↦ \bar∂ f`.
* `TauCeti.dolbeaultSequence U`: the sequence `𝒪 ⟶ ℰ ⟶ ℰ`.

## Main results

* `TauCeti.dolbeaultSequence_exact`: the sequence is exact, and its first map is a monomorphism.
* `TauCeti.isZero_cechCohomology_one_holomorphicStructureSheafModules`: `H¹(U, 𝒪) = 0` when
  `\bar∂ g = f` is smoothly solvable on `U`.
* `TauCeti.isZero_cechCohomology_one_holomorphicStructureSheafModules_eball`: `H¹(D, 𝒪) = 0` for
  every disc `D = eball c R`, `R ≤ ∞`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  Theorem 13.4 (`H¹(X, 𝒪) = 0` for discs) and Corollary 13.3.
-/

public noncomputable section

open CategoryTheory Filter Limits Opposite Set TopologicalSpace Topology
open scoped ContDiff Manifold

namespace TauCeti

variable (U : Opens ℂ)

/-! ### Functions on open sets of `U` as functions on the plane -/

section Ambient

variable {U} {V : Opens (TopCat.of U)}

/-- A function on an open set `V` of `U`, extended by zero to the whole plane. -/
private abbrev amb (f : V → ℂ) : ℂ → ℂ :=
  Subtype.val.extend (Subtype.val.extend f 0 : U → ℂ) 0

private lemma amb_apply (f : V → ℂ) (y : V) : amb f ((y : U) : ℂ) = f y := by
  rw [amb, Subtype.val_injective.extend_apply, Subtype.val_injective.extend_apply]

/-- The points of the plane lying in `V`. -/
private def planeSet (V : Opens (TopCat.of U)) : Set ℂ :=
  Subtype.val '' (V : Set U)

private lemma isOpen_planeSet (V : Opens (TopCat.of U)) : IsOpen (planeSet V) :=
  U.isOpen.isOpenMap_subtype_val _ V.isOpen

private lemma mem_planeSet (y : V) : ((y : U) : ℂ) ∈ planeSet V := ⟨y, y.2, rfl⟩

private lemma planeSet_nhds (y : V) : planeSet V ∈ 𝓝 ((y : U) : ℂ) :=
  (isOpen_planeSet V).mem_nhds (mem_planeSet y)

private lemma exists_of_mem_planeSet {z : ℂ} (hz : z ∈ planeSet V) :
    ∃ y : V, ((y : U) : ℂ) = z := by
  obtain ⟨w, hw, rfl⟩ := hz
  exact ⟨⟨w, hw⟩, rfl⟩

/-- Smoothness of a function on `V` at a point is smoothness of its extension by zero. -/
private lemma contMDiffAt_iff {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 ℂ]
    {n : ℕ∞ω} (f : V → ℂ) (y : V) :
    ContMDiffAt 𝓘(𝕜, ℂ) 𝓘(𝕜, ℂ) n f y ↔ ContDiffAt 𝕜 n (amb f) ((y : U) : ℂ) := by
  rw [← contMDiffAt_extend_subtypeVal_iff (0 : TopCat.of U → ℂ),
    ← contMDiffAt_extend_subtypeVal_iff (U := U) (x := (y : U)) (0 : ℂ → ℂ),
    contMDiffAt_iff_contDiffAt]

/-- Restriction to a smaller open set does not change the extension by zero near its points. -/
private lemma amb_comp_inclusion_eventuallyEq {V' : Opens (TopCat.of U)} (h : V' ≤ V)
    (f : V → ℂ) (y : V') :
    amb (f ∘ Opens.inclusion h) =ᶠ[𝓝 ((y : U) : ℂ)] amb f := by
  filter_upwards [planeSet_nhds y] with z hz
  obtain ⟨w, rfl⟩ := exists_of_mem_planeSet hz
  rw [amb_apply, Function.comp_apply]
  exact (amb_apply f (Opens.inclusion h w)).symm

private lemma amb_add (f g : V → ℂ) : amb (f + g) = amb f + amb g := by
  rw [amb, ← add_zero (0 : TopCat.of U → ℂ), Function.extend_add, ← add_zero (0 : ℂ → ℂ),
    Function.extend_add]

private lemma amb_smul (c : ℂ) (f : V → ℂ) : amb (c • f) = c • amb f := by
  rw [amb, ← smul_zero (A := TopCat.of U → ℂ) c, Function.extend_smul,
    ← smul_zero (A := ℂ → ℂ) c, Function.extend_smul]

end Ambient

/-! ### The Cauchy-Riemann operator on sections -/

section Sections

variable {U} {V : Opens (TopCat.of U)}

/-- The Cauchy-Riemann operator `f ↦ \bar∂ f` on functions on `V`, computed on the extension by
zero. -/
private def dbarFun (f : V → ℂ) (y : V) : ℂ :=
  conjWirtingerDeriv (amb f) ((y : U) : ℂ) 1

private lemma contMDiff_dbarFun {f : V → ℂ} (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (dbarFun f) := fun y ↦ by
  rw [contMDiffAt_iff]
  -- near `y`, the Wirtinger derivative of the extension is the extension of `dbarFun f`
  refine (((contMDiffAt_iff f y).1 (hf y)).conjWirtingerDeriv_apply (m := ∞) le_rfl
    1).congr_of_eventuallyEq ?_
  filter_upwards [planeSet_nhds y] with z hz
  obtain ⟨w, rfl⟩ := exists_of_mem_planeSet hz
  rw [amb_apply]
  rfl

private lemma differentiableAt_amb {f : V → ℂ} (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f) (y : V) :
    DifferentiableAt ℝ (amb f) ((y : U) : ℂ) :=
  ((contMDiffAt_iff f y).1 (hf y)).differentiableAt (by simp)

private lemma dbarFun_add {f g : V → ℂ} (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ g) : dbarFun (f + g) = dbarFun f + dbarFun g := by
  funext y
  rw [dbarFun, amb_add, conjWirtingerDeriv_add (differentiableAt_amb hf y)
    (differentiableAt_amb hg y)]
  rfl

private lemma dbarFun_smul (c : ℂ) {f : V → ℂ} (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f) :
    dbarFun (c • f) = c • dbarFun f := by
  funext y
  rw [Pi.smul_apply, dbarFun, dbarFun, amb_smul, conjWirtingerDeriv_apply, conjWirtingerDeriv_apply,
    fderiv_const_smul (differentiableAt_amb hf y), smul_apply,
    smul_apply, smul_comm Complex.I c, ← smul_add, smul_comm]

/-- A smooth function on `V` with vanishing `\bar∂` is holomorphic. -/
private lemma contMDiff_of_dbarFun_eq_zero {f : V → ℂ} (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f)
    (h : dbarFun f = 0) : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f := fun y ↦ by
  rw [contMDiffAt_iff]
  refine (Complex.analyticAt_iff_eventually_differentiableAt.2 ?_).contDiffAt
  filter_upwards [planeSet_nhds y] with z hz
  obtain ⟨w, rfl⟩ := exists_of_mem_planeSet hz
  exact (differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero (differentiableAt_amb hf w)).2
    (congrFun h w)

private lemma dbarFun_eq_zero {f : V → ℂ} (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) :
    dbarFun f = 0 := by
  funext y
  exact congrFun (congrArg DFunLike.coe
    (((contMDiffAt_iff f y).1 (hf y)).differentiableAt (by simp)).conjWirtingerDeriv_eq_zero) 1

private lemma contMDiff_real_of_holomorphic {f : V → ℂ} (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f := fun y ↦ by
  rw [contMDiffAt_iff]
  exact (((contMDiffAt_iff f y).1 (hf y)).restrict_scalars ℝ).of_le le_top

end Sections

/-! ### The Dolbeault sequence -/

section Sequence

/-- The sections of the sheaf of smooth functions on `U`, as smooth functions. -/
private abbrev secE (V : Opens (TopCat.of U)) :=
  smoothSheafModule.sectionsEquiv 𝓘(ℝ, ℂ) ℂ ℂ (M := U) V

/-- The Cauchy-Riemann operator on the smooth sections over `V`. -/
private def dbarLinear (V : Opens (TopCat.of U)) :
    (smoothSheafModule 𝓘(ℝ, ℂ) U ℂ ℂ).obj.obj (op V) →ₗ[ℂ]
      (smoothSheafModule 𝓘(ℝ, ℂ) U ℂ ℂ).obj.obj (op V) where
  toFun s := (secE U V).symm ⟨dbarFun (secE U V s).1,
    mem_smoothSections_iff.2 (contMDiff_dbarFun (mem_smoothSections_iff.1 (secE U V s).2))⟩
  map_add' s t := by
    refine smoothSheafModule.ext fun y ↦ ?_
    simp only [LinearEquiv.apply_symm_apply, map_add, Submodule.coe_add]
    rw [dbarFun_add (mem_smoothSections_iff.1 (secE U V s).2)
      (mem_smoothSections_iff.1 (secE U V t).2)]
  map_smul' c s := by
    refine smoothSheafModule.ext fun y ↦ ?_
    simp only [LinearEquiv.apply_symm_apply, map_smul, Submodule.coe_smul, RingHom.id_apply]
    rw [dbarFun_smul c (mem_smoothSections_iff.1 (secE U V s).2)]

private lemma secE_dbarLinear (V : Opens (TopCat.of U))
    (s : (smoothSheafModule 𝓘(ℝ, ℂ) U ℂ ℂ).obj.obj (op V)) :
    (secE U V (dbarLinear U V s)).1 = dbarFun (secE U V s).1 := by
  simp [dbarLinear]

/-- **The Cauchy-Riemann operator** `f ↦ \bar∂ f` on the sheaf of smooth functions on an open set
`U` of the complex plane. -/
def dolbeaultDbar :
    (smoothSheafModule 𝓘(ℝ, ℂ) U ℂ ℂ).obj ⟶ (smoothSheafModule 𝓘(ℝ, ℂ) U ℂ ℂ).obj where
  app V := ModuleCat.ofHom (dbarLinear U V.unop)
  naturality V V' h := by
    induction V using Opposite.rec
    induction V' using Opposite.rec
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    refine smoothSheafModule.ext fun y ↦ ?_
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
    rw [← Quiver.Hom.op_unop h, smoothSheafModule.sectionsEquiv_map, secE_dbarLinear,
      secE_dbarLinear, smoothSheafModule.sectionsEquiv_map]
    -- the extensions by zero of a function and of its restriction agree near `y`
    exact congrFun (congrArg DFunLike.coe
      (amb_comp_inclusion_eventuallyEq h.unop.le _ y).conjWirtingerDeriv_eq) 1

/-- The Cauchy-Riemann operator on sections: the Wirtinger derivative `\bar∂ f` of a smooth
function `f` on `V`, computed after extending `f` by zero to the plane. -/
theorem sectionsEquiv_dolbeaultDbar_app (V : Opens (TopCat.of U))
    (s : (smoothSheafModule 𝓘(ℝ, ℂ) U ℂ ℂ).obj.obj (op V)) (y : V) :
    (smoothSheafModule.sectionsEquiv 𝓘(ℝ, ℂ) ℂ ℂ V ((dolbeaultDbar U).app (op V) s)).1 y =
      conjWirtingerDeriv (Subtype.val.extend (Subtype.val.extend
        (smoothSheafModule.sectionsEquiv 𝓘(ℝ, ℂ) ℂ ℂ V s).1 0 : U → ℂ) 0) ((y : U) : ℂ) 1 :=
  congrFun (secE_dbarLinear U V s) y

private lemma secE_dolbeaultDbar_app (V : Opens (TopCat.of U))
    (s : (smoothSheafModule 𝓘(ℝ, ℂ) U ℂ ℂ).obj.obj (op V)) :
    (secE U V ((dolbeaultDbar U).app (op V) s)).1 = dbarFun (secE U V s).1 :=
  secE_dbarLinear U V s

/-- The inclusion of the holomorphic sections over `V` into the smooth sections. -/
private def inclLinear (V : Opens (TopCat.of U)) :
    (holomorphicStructureSheafModules 𝓘(ℂ) U).obj.obj (op V) →ₗ[ℂ]
      (smoothSheafModule 𝓘(ℝ, ℂ) U ℂ ℂ).obj.obj (op V) where
  toFun s := (secE U V).symm ⟨s, mem_smoothSections_iff.2 (contMDiff_real_of_holomorphic
    (holomorphicStructureSheafModules.contMDiff s))⟩
  map_add' s t := by
    refine smoothSheafModule.ext fun y ↦ ?_
    simp
  map_smul' c s := by
    refine smoothSheafModule.ext fun y ↦ ?_
    simp

private lemma secE_inclLinear (V : Opens (TopCat.of U))
    (s : (holomorphicStructureSheafModules 𝓘(ℂ) U).obj.obj (op V)) :
    (secE U V (inclLinear U V s)).1 = s := by
  simp [inclLinear]

/-- **The inclusion of holomorphic into smooth functions** on an open set `U` of the complex
plane, as a morphism from the structure sheaf `𝒪` to the sheaf `ℰ` of smooth functions. -/
def dolbeaultInclusion :
    (holomorphicStructureSheafModules 𝓘(ℂ) U).obj ⟶ (smoothSheafModule 𝓘(ℝ, ℂ) U ℂ ℂ).obj where
  app V := ModuleCat.ofHom (inclLinear U V.unop)
  naturality V V' h := by
    induction V using Opposite.rec
    induction V' using Opposite.rec
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    refine smoothSheafModule.ext fun y ↦ ?_
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
    rw [← Quiver.Hom.op_unop h, smoothSheafModule.sectionsEquiv_map, secE_inclLinear,
      secE_inclLinear]
    exact holomorphicStructureSheafModules.map_apply _ _ _ _ _

/-- The inclusion of holomorphic into smooth functions does not change the function. -/
@[simp]
theorem sectionsEquiv_dolbeaultInclusion_app (V : Opens (TopCat.of U))
    (s : (holomorphicStructureSheafModules 𝓘(ℂ) U).obj.obj (op V)) :
    (smoothSheafModule.sectionsEquiv 𝓘(ℝ, ℂ) ℂ ℂ V ((dolbeaultInclusion U).app (op V) s)).1 =
      s :=
  secE_inclLinear U V s

/-- **The Dolbeault sequence** `𝒪 ⟶ ℰ ⟶ ℰ` on an open set `U` of the complex plane: holomorphic
functions include into smooth functions, followed by the Cauchy-Riemann operator. -/
def dolbeaultSequence : ShortComplex ((Opens (TopCat.of U))ᵒᵖ ⥤ ModuleCat.{0} ℂ) :=
  ShortComplex.mk (dolbeaultInclusion U) (dolbeaultDbar U) <| by
    ext V s
    induction V using Opposite.rec with | op V
    refine smoothSheafModule.ext fun y ↦ ?_
    rw [NatTrans.comp_app, ConcreteCategory.comp_apply, secE_dolbeaultDbar_app,
      sectionsEquiv_dolbeaultInclusion_app, NatTrans.app_zero, ModuleCat.hom_zero,
      LinearMap.zero_apply, map_zero,
      dbarFun_eq_zero (holomorphicStructureSheafModules.contMDiff s)]
    rfl

instance : Mono (dolbeaultSequence U).f := by
  have (V : (Opens (TopCat.of U))ᵒᵖ) : Mono ((dolbeaultSequence U).f.app V) := by
    refine (ModuleCat.mono_iff_injective _).2 fun s t h ↦ ?_
    induction V using Opposite.rec with | op V
    have h' : (secE U V (inclLinear U V s)).1 = (secE U V (inclLinear U V t)).1 :=
      congrArg (fun r ↦ (secE U V r).1) h
    exact holomorphicStructureSheafModules.ext (congrFun
      ((secE_inclLinear U V s).symm.trans (h'.trans (secE_inclLinear U V t))))
  exact NatTrans.mono_of_mono_app _

/-- The first object of the Dolbeault sequence is the structure sheaf. -/
@[simp]
theorem dolbeaultSequence_X₁ :
    (dolbeaultSequence U).X₁ = (holomorphicStructureSheafModules 𝓘(ℂ) U).obj := (rfl)

/-- The middle object of the Dolbeault sequence is the sheaf of smooth functions. -/
@[simp]
theorem dolbeaultSequence_X₂ :
    (dolbeaultSequence U).X₂ = (smoothSheafModule 𝓘(ℝ, ℂ) U ℂ ℂ).obj := (rfl)

/-- The last object of the Dolbeault sequence is the sheaf of smooth functions. -/
@[simp]
theorem dolbeaultSequence_X₃ :
    (dolbeaultSequence U).X₃ = (smoothSheafModule 𝓘(ℝ, ℂ) U ℂ ℂ).obj := (rfl)

/-- The first map of the Dolbeault sequence is the inclusion of holomorphic functions, up to the
identifications `dolbeaultSequence_X₁` and `dolbeaultSequence_X₂` of its objects. -/
@[simp]
theorem dolbeaultSequence_f :
    (dolbeaultSequence U).f = eqToHom (dolbeaultSequence_X₁ U) ≫ dolbeaultInclusion U ≫
      eqToHom (dolbeaultSequence_X₂ U).symm := by
  -- the objects agree definitionally, so both `eqToHom`s are identities
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- The second map of the Dolbeault sequence is the Cauchy-Riemann operator, up to the
identifications `dolbeaultSequence_X₂` and `dolbeaultSequence_X₃` of its objects. -/
@[simp]
theorem dolbeaultSequence_g :
    (dolbeaultSequence U).g = eqToHom (dolbeaultSequence_X₂ U) ≫ dolbeaultDbar U ≫
      eqToHom (dolbeaultSequence_X₃ U).symm := by
  -- the objects agree definitionally, so both `eqToHom`s are identities
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- **Exactness of the Dolbeault sequence.** A smooth function on an open set of the complex plane
is holomorphic exactly when its Wirtinger derivative `\bar∂ f` vanishes. -/
theorem dolbeaultSequence_exact : (dolbeaultSequence U).Exact := by
  refine ShortComplex.exact_of_forall_evaluation _ fun V ↦ ?_
  induction V using Opposite.rec with | op V
  rw [ShortComplex.moduleCat_exact_iff]
  intro s hs
  have hs' : dbarFun (secE U V s).1 = 0 := by
    have h : (secE U V (dbarLinear U V s)).1 = (secE U V 0).1 :=
      congrArg (fun r ↦ (secE U V r).1) hs
    exact (secE_dbarLinear U V s).symm.trans (h.trans (by rw [map_zero]; rfl))
  refine ⟨holomorphicStructureSheafModules.ofContMDiff (secE U V s).1
    (contMDiff_of_dbarFun_eq_zero (mem_smoothSections_iff.1 (secE U V s).2) hs'),
    smoothSheafModule.ext fun y ↦ ?_⟩
  exact (congrFun (sectionsEquiv_dolbeaultInclusion_app U V _) y).trans
    (holomorphicStructureSheafModules.ofContMDiff_apply _ _ y)

end Sequence

/-! ### Degree one cohomology of the structure sheaf -/

section Cohomology

/-- A smooth function on `U` is the restriction of a function on the plane that is smooth on
`U`. -/
private lemma contDiffOn_amb {f : (⊤ : Opens (TopCat.of U)) → ℂ}
    (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f) : ContDiffOn ℝ ∞ (amb f) U :=
  fun z hz ↦ ((contMDiffAt_iff f ⟨⟨z, hz⟩, trivial⟩).1 (hf _)).contDiffWithinAt

/-- A function on the plane that is smooth on `U` restricts to a smooth function on `U`. -/
private lemma contMDiff_restrict {g : ℂ → ℂ} (hg : ContDiffOn ℝ ∞ g U) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ fun y : (⊤ : Opens (TopCat.of U)) ↦ g ((y : U) : ℂ) :=
  fun y ↦ (contMDiffAt_iff _ y).2 <|
    (hg.contDiffAt (U.isOpen.mem_nhds (y : U).2)).congr_of_eventuallyEq (by
      filter_upwards [planeSet_nhds y] with z hz
      obtain ⟨w, rfl⟩ := exists_of_mem_planeSet hz
      exact amb_apply _ w)

/-- If `\bar∂ g = f` has a smooth solution `g` on `U` for every smooth `f` on `U`, then the
Cauchy-Riemann operator is surjective on global smooth sections. -/
private lemma surjective_dolbeaultDbar_app_top
    (hU : ∀ f : ℂ → ℂ, ContDiffOn ℝ ∞ f U →
      ∃ g : ℂ → ℂ, ContDiffOn ℝ ∞ g U ∧ ∀ z ∈ U, conjWirtingerDeriv g z 1 = f z) :
    Function.Surjective ((dolbeaultSequence U).g.app (op ⊤)) := by
  intro (s : (smoothSheafModule 𝓘(ℝ, ℂ) U ℂ ℂ).obj.obj (op ⊤))
  obtain ⟨g, hg, hgf⟩ := hU _ (contDiffOn_amb U (mem_smoothSections_iff.1 (secE U ⊤ s).2))
  refine ⟨(secE U ⊤).symm ⟨_, mem_smoothSections_iff.2 (contMDiff_restrict U hg)⟩,
    smoothSheafModule.ext fun y ↦ ?_⟩
  have h : (secE U ⊤ (dbarLinear U ⊤ ((secE U ⊤).symm
      ⟨_, mem_smoothSections_iff.2 (contMDiff_restrict U hg)⟩))).1 y = (secE U ⊤ s).1 y := by
    rw [secE_dbarLinear, LinearEquiv.apply_symm_apply, dbarFun, ← amb_apply (secE U ⊤ s).1 y,
      ← hgf _ (y : U).2]
    -- the extension by zero of the restriction of `g` agrees with `g` near `y`
    refine congrFun (congrArg DFunLike.coe (Filter.EventuallyEq.conjWirtingerDeriv_eq ?_)) 1
    filter_upwards [planeSet_nhds y] with z hz
    obtain ⟨w, rfl⟩ := exists_of_mem_planeSet hz
    exact amb_apply _ w
  exact h

/-- **The structure sheaf of a plane domain has no degree one Čech cohomology** as soon as the
equation `\bar∂ g = f` has a smooth solution `g` on `U` for every smooth `f` on `U`. -/
theorem isZero_cechCohomology_one_holomorphicStructureSheafModules
    (hU : ∀ f : ℂ → ℂ, ContDiffOn ℝ ∞ f U →
      ∃ g : ℂ → ℂ, ContDiffOn ℝ ∞ g U ∧ ∀ z ∈ U, conjWirtingerDeriv g z 1 = f z) :
    IsZero ((Topology.cechCohomology (TopCat.of U) (ModuleCat.{0} ℂ) 1).obj
      (holomorphicStructureSheafModules 𝓘(ℂ) U).obj) := by
  have : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  exact Topology.isZero_cechCohomology_one_of_exact (dolbeaultSequence U)
    (dolbeaultSequence_exact U) (smoothSheafModule 𝓘(ℝ, ℂ) U ℂ ℂ).property
    (smoothSheafModule 𝓘(ℝ, ℂ) U ℂ ℂ).property (surjective_dolbeaultDbar_app_top U hU)
    (smoothSheafModule.isZero_cechCohomology_obj_succ 𝓘(ℝ, ℂ) U ℂ ℂ 0)

/-- **`H¹(D, 𝒪) = 0` for discs.** The structure sheaf of an open disc `eball c R` of radius
`R ≤ ∞`, in particular of the whole plane, has no degree one Čech cohomology. -/
theorem isZero_cechCohomology_one_holomorphicStructureSheafModules_eball (c : ℂ) (R : ENNReal) :
    IsZero ((Topology.cechCohomology (TopCat.of (⟨Metric.eball c R, Metric.isOpen_eball⟩ :
      Opens ℂ)) (ModuleCat.{0} ℂ) 1).obj
      (holomorphicStructureSheafModules 𝓘(ℂ) (⟨Metric.eball c R, Metric.isOpen_eball⟩ :
        Opens ℂ)).obj) :=
  isZero_cechCohomology_one_holomorphicStructureSheafModules _ fun _ hf ↦
    exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_of_eball (c := c) (R := R) (n := ⊤) le_top hf

end Cohomology

end TauCeti
