/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.AB
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Comparison
public import TauCeti.Geometry.Manifold.Sheaf.Smooth.Basic
public import TauCeti.Logic.Function.Extend
public import TauCeti.Topology.Sheaves.Cech.Colimit

/-!
# The sheaf of smooth functions has no higher Čech cohomology

Let `M` be a Hausdorff, `σ`-compact real manifold, modelled on a finite-dimensional space, and let
`V` be a normed space over a normed field `𝕜` which is a normed `ℝ`-algebra. This file shows that
the sheaf `TauCeti.smoothSheafModule I M 𝕜 V` of smooth `V`-valued functions is acyclic for every
open cover of `M`: the augmented Čech complex `0 ⟶ ℰ(M) ⟶ Č⁰(U, ℰ) ⟶ Č¹(U, ℰ) ⟶ ⋯` is exact.
Hence its Čech cohomology vanishes in every positive degree, while in degree `0` it is the space of
global smooth functions (`TauCeti.Topology.cechCohomologyZeroIso`). For a Riemann surface, viewed
as a real surface, and `𝕜 = V = ℂ`, this is the vanishing `H¹(X, ℰ) = 0` used with the
Dolbeault lemma to compute `H¹(X, 𝒪)` on discs.

Smooth functions form a fine sheaf. Given a smooth partition of unity `ρ i` subordinate to the
cover `U`, a family of smooth functions `sᵢ` on the opens `U i ∩ W` glues to the smooth function
`∑ᵢ ρ i • sᵢ` on `W`, each term extended by zero off `U i`; the sum is locally finite. Restricting
a function `s` on `W` to the opens `U i ∩ W` and gluing back gives `∑ᵢ ρ i • s = s`. So the sheaf
is a retract of the product of its restrictions to the members of the cover, and the Čech
acyclicity of such retracts (`TauCeti.CategoryTheory.quasiIso_cechAugmentation_of_retract_pi`)
applies. In cochain terms this is the classical contracting homotopy
`(h c)_{i₀ ⋯ iₙ} = ∑ₖ ρ k • c_{k i₀ ⋯ iₙ}`.

## Main results

* `TauCeti.smoothSheafModule.retractPiRestrict`: the sheaf of smooth functions is a retract of the
  product of its restrictions to the members of an open cover with a subordinate smooth partition
  of unity. Its inclusion is restriction (`retractPiRestrict_i_app_π`) and its retraction is
  gluing with the partition of unity (`sectionsEquiv_retractPiRestrict_r_app`).
* `TauCeti.smoothSheafModule.quasiIso_cechAugmentation`: the sheaf of smooth functions is acyclic
  for every open cover.
* `TauCeti.smoothSheafModule.isZero_cechCohomology_obj_succ`: the Čech cohomology of the sheaf of
  smooth functions vanishes in every positive degree.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  Theorem 12.6 (`H¹(X, ℰ) = 0`, by the same partition-of-unity formula).
* R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*, Graduate Texts in Mathematics 82,
  Springer, 1982, Proposition 8.5 (the contracting homotopy of the Čech complex of a sheaf with
  partitions of unity, in all degrees).
-/

public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

universe u v

namespace smoothSheafModule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  {V : Type v} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V]

/-! ### Gluing with a partition of unity -/

section Retract

variable {ι : Type u} (U : ι → Opens (TopCat.of M)) (ρ : SmoothPartitionOfUnity ι I M)
  (hρ : ρ.IsSubordinate fun i ↦ (U i : Set M))

/-- The categorical product of two opens is their intersection. -/
private lemma mem_prod_iff {W W' : Opens (TopCat.of M)} {y : M} :
    y ∈ (W ⨯ W' : Opens (TopCat.of M)) ↔ y ∈ W ∧ y ∈ W' := by
  rw [CompleteLattice.prod_eq_inf]
  exact Iff.rfl

variable {U} in
/-- The components, as functions, of a section of the product of the restrictions of the sheaf of
smooth functions to the members of `U`. -/
private abbrev component {W : Opens (TopCat.of M)}
    (x : (∏ᶜ fun i ↦ (prod.functor.obj (U i)).op ⋙ (smoothSheafModule I M 𝕜 V).obj).obj (op W))
    (i : ι) : (U i ⨯ W : Opens (TopCat.of M)) → V :=
  (sectionsEquiv I 𝕜 V (U i ⨯ W) ((Pi.π _ i : (∏ᶜ fun i ↦
    (prod.functor.obj (U i)).op ⋙ (smoothSheafModule I M 𝕜 V).obj) ⟶ _).app (op W) x)).1

variable {U} in
private lemma component_add {W : Opens (TopCat.of M)}
    (x x' : (∏ᶜ fun i ↦ (prod.functor.obj (U i)).op ⋙ (smoothSheafModule I M 𝕜 V).obj).obj
      (op W)) (i : ι) : component (x + x') i = component x i + component x' i := by
  simp [component]

variable {U} in
private lemma component_smul {W : Opens (TopCat.of M)} (c : 𝕜)
    (x : (∏ᶜ fun i ↦ (prod.functor.obj (U i)).op ⋙ (smoothSheafModule I M 𝕜 V).obj).obj
      (op W)) (i : ι) : component (c • x) i = c • component x i := by
  simp [component]

/-- The glued function `∑ᵢ ρ i • sᵢ` of a family of functions `sᵢ` on the opens `U i ∩ W`, each
extended by zero. -/
private def glueFun {W : Opens (TopCat.of M)} (s : ∀ i, (U i ⨯ W : Opens (TopCat.of M)) → V)
    (y : M) : V :=
  ∑ᶠ i, ρ i y • Subtype.val.extend (s i) 0 y

include hρ in
private lemma contMDiff_glueFun {W : Opens (TopCat.of M)}
    {s : ∀ i, (U i ⨯ W : Opens (TopCat.of M)) → V} (hs : ∀ i, ContMDiff I 𝓘(ℝ, V) ∞ (s i)) :
    ContMDiff I 𝓘(ℝ, V) ∞ fun y : W ↦ glueFun U ρ s y := fun y ↦
  contMDiffAt_subtype_iff.2 <| ρ.contMDiffAt_finsum fun i hy ↦
    ContMDiffAt.extend_subtypeVal (hs i ⟨y, mem_prod_iff.2 ⟨hρ i hy, y.2⟩⟩) 0

/-- Only finitely many terms of the glued sum are nonzero at each point. -/
private lemma finite_support_glue {W : Opens (TopCat.of M)}
    (s : ∀ i, (U i ⨯ W : Opens (TopCat.of M)) → V) (y : M) :
    (Function.support fun i ↦ ρ i y • Subtype.val.extend (s i) 0 y).Finite :=
  (ρ.locallyFinite.point_finite y).subset fun _ hi ↦ left_ne_zero_of_smul hi

private lemma glueFun_add {W : Opens (TopCat.of M)}
    (s s' : ∀ i, (U i ⨯ W : Opens (TopCat.of M)) → V) (y : M) :
    glueFun U ρ (s + s') y = glueFun U ρ s y + glueFun U ρ s' y := by
  have h (i : ι) : ρ i y • Subtype.val.extend ((s + s') i) 0 y =
      ρ i y • Subtype.val.extend (s i) 0 y + ρ i y • Subtype.val.extend (s' i) 0 y := by
    have he := congrFun (Function.extend_add Subtype.val (s i) (s' i) (0 : M → V) 0) y
    rw [add_zero] at he
    rw [← smul_add, ← Pi.add_apply (Subtype.val.extend (s i) 0), ← he]
    rfl
  exact (finsum_congr h).trans
    (finsum_add_distrib (finite_support_glue U ρ s y) (finite_support_glue U ρ s' y))

private lemma glueFun_smul {W : Opens (TopCat.of M)} (c : 𝕜)
    (s : ∀ i, (U i ⨯ W : Opens (TopCat.of M)) → V) (y : M) :
    glueFun U ρ (c • s) y = c • glueFun U ρ s y := by
  have h (i : ι) : ρ i y • Subtype.val.extend ((c • s) i) 0 y =
      c • (ρ i y • Subtype.val.extend (s i) 0 y) := by
    have he := congrFun (Function.extend_smul c Subtype.val (s i) (0 : M → V)) y
    rw [smul_zero] at he
    rw [smul_comm c (ρ i y), ← Pi.smul_apply c (Subtype.val.extend (s i) 0), ← he]
    rfl
  exact (finsum_congr h).trans (smul_finsum' c (finite_support_glue U ρ s y)).symm

/-- Gluing over `W`: the section `∑ᵢ ρ i • sᵢ` of the sheaf of smooth functions over `W`
determined by a section `(sᵢ)ᵢ` of the product of its restrictions to the members of `U`. -/
private def glue (W : Opens (TopCat.of M)) :
    (∏ᶜ fun i ↦ (prod.functor.obj (U i)).op ⋙ (smoothSheafModule I M 𝕜 V).obj).obj (op W) →ₗ[𝕜]
      (smoothSheafModule I M 𝕜 V).obj.obj (op W) where
  toFun x := (sectionsEquiv I 𝕜 V W).symm ⟨fun y ↦ glueFun U ρ (component x) y,
    mem_smoothSections_iff.2 <| contMDiff_glueFun U ρ hρ fun i ↦
      mem_smoothSections_iff.1 (sectionsEquiv I 𝕜 V _ _).2⟩
  map_add' x x' := by
    rw [← map_add]
    congr 1
    refine Subtype.ext (funext fun y ↦ ?_)
    simp only [Submodule.coe_add, Pi.add_apply]
    rw [← glueFun_add]
    exact congrArg (glueFun U ρ · y) (funext (component_add x x'))
  map_smul' c x := by
    rw [RingHom.id_apply, ← map_smul]
    congr 1
    refine Subtype.ext (funext fun y ↦ ?_)
    simp only [Submodule.coe_smul, Pi.smul_apply]
    rw [← glueFun_smul]
    exact congrArg (glueFun U ρ · y) (funext (component_smul c x))

private lemma sectionsEquiv_glue (W : Opens (TopCat.of M))
    (x : (∏ᶜ fun i ↦ (prod.functor.obj (U i)).op ⋙ (smoothSheafModule I M 𝕜 V).obj).obj
      (op W)) :
    (sectionsEquiv I 𝕜 V W (glue U ρ hρ W x)).1 = fun y : W ↦ glueFun U ρ (component x) y := by
  simp only [glue, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply]

variable {U} in
private lemma component_map {W W' : Opens (TopCat.of M)} (h : W' ⟶ W)
    (x : (∏ᶜ fun i ↦ (prod.functor.obj (U i)).op ⋙ (smoothSheafModule I M 𝕜 V).obj).obj
      (op W)) (i : ι) :
    component ((∏ᶜ fun i ↦ (prod.functor.obj (U i)).op ⋙ (smoothSheafModule I M 𝕜 V).obj).map
      h.op x) i = component x i ∘ Opens.inclusion ((prod.functor.obj (U i)).map h).le := by
  -- the projection to the `i`-th factor is natural
  have := ConcreteCategory.congr_hom ((Pi.π (fun i ↦ (prod.functor.obj (U i)).op ⋙
    (smoothSheafModule I M 𝕜 V).obj) i).naturality h.op) x
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
  rw [component, this]
  exact sectionsEquiv_map ((prod.functor.obj (U i)).map h) _

/-- The gluing maps `(sᵢ)ᵢ ↦ ∑ᵢ ρ i • sᵢ`, as a morphism of presheaves. -/
private def glueHom :
    (∏ᶜ fun i ↦ (prod.functor.obj (U i)).op ⋙ (smoothSheafModule I M 𝕜 V).obj) ⟶
      (smoothSheafModule I M 𝕜 V).obj where
  app W := ModuleCat.ofHom (glue U ρ hρ W.unop)
  naturality W W' h := by
    induction W using Opposite.rec
    induction W' using Opposite.rec
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    refine smoothSheafModule.ext fun y ↦ ?_
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
    rw [← Quiver.Hom.op_unop h, sectionsEquiv_map, sectionsEquiv_glue, sectionsEquiv_glue]
    -- at a point of the smaller open, the extended components agree
    refine finsum_congr fun i ↦ congrArg (ρ i y • ·) ?_
    rw [component_map]
    exact Function.extend_subtypeVal_comp_inclusion _ _ _ fun hy ↦
      mem_prod_iff.2 ⟨(mem_prod_iff.1 hy).1, y.2⟩

private lemma sectionsEquiv_glueHom_app (W : Opens (TopCat.of M))
    (x : (∏ᶜ fun i ↦ (prod.functor.obj (U i)).op ⋙ (smoothSheafModule I M 𝕜 V).obj).obj
      (op W)) :
    (sectionsEquiv I 𝕜 V W ((glueHom U ρ hρ).app (op W) x)).1 =
      fun y : W ↦ glueFun U ρ (component x) y :=
  sectionsEquiv_glue U ρ hρ W x

variable {U} in
/-- The restriction of the sheaf of smooth functions to a member of `U`. -/
private def restrictHom (i : ι) :
    (smoothSheafModule I M 𝕜 V).obj ⟶
      (prod.functor.obj (U i)).op ⋙ (smoothSheafModule I M 𝕜 V).obj where
  app W := (smoothSheafModule I M 𝕜 V).obj.map (prod.snd : U i ⨯ W.unop ⟶ W.unop).op
  naturality _ _ _ := by
    rw [Functor.comp_map, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ (Subsingleton.elim _ _)

variable {U} in
private lemma component_restrictHom {W : Opens (TopCat.of M)}
    (s : (smoothSheafModule I M 𝕜 V).obj.obj (op W)) (i : ι) :
    component ((Pi.lift (restrictHom (U := U))).app (op W) s) i =
      (sectionsEquiv I 𝕜 V W s).1 ∘ Opens.inclusion (prod.snd : U i ⨯ W ⟶ W).le := by
  rw [component, ← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
    Pi.lift_comp_π]
  exact sectionsEquiv_map _ _

/-- **The sheaf of smooth functions is a retract of the product of its restrictions** to the
members of an open cover `U` with a subordinate smooth partition of unity `ρ`: the restrictions
are split by gluing, `(sᵢ)ᵢ ↦ ∑ᵢ ρ i • sᵢ` with each term extended by zero. -/
def retractPiRestrict : Retract (smoothSheafModule I M 𝕜 V).obj
    (∏ᶜ fun i ↦ (prod.functor.obj (U i)).op ⋙ (smoothSheafModule I M 𝕜 V).obj) where
  i := Pi.lift restrictHom
  r := glueHom U ρ hρ
  retract := by
    ext W s
    induction W using Opposite.rec with | op W
    refine smoothSheafModule.ext fun y ↦ ?_
    rw [NatTrans.comp_app, ConcreteCategory.comp_apply, NatTrans.id_app,
      ConcreteCategory.id_apply, sectionsEquiv_glueHom_app]
    -- the terms with `ρ i y ≠ 0` have `y ∈ U i`, so they are `ρ i y • s y`
    have h (i : ι) : ρ i y • Subtype.val.extend (component ((Pi.lift (restrictHom (U := U))).app
        (op W) s) i) 0 y = ρ i y • (sectionsEquiv I 𝕜 V W s).1 y := by
      by_cases hi : ρ i y = 0
      · simp [hi]
      · have hy : (y : M) ∈ (U i ⨯ W : Opens (TopCat.of M)) :=
          mem_prod_iff.2 ⟨hρ i (subset_closure hi), y.2⟩
        rw [component_restrictHom]
        exact congrArg _ (Subtype.val_injective.extend_apply _ (0 : M → V) ⟨y, hy⟩)
    simp only [glueFun]
    rw [finsum_congr h, ← finsum_smul' (ρ.locallyFinite.point_finite y),
      ρ.sum_eq_one (Set.mem_univ _), one_smul]

/-- The inclusion of `retractPiRestrict` is restriction: its component at `i` sends a section over
`W` to its restriction to `U i ∩ W`. -/
theorem retractPiRestrict_i_app_π (W : Opens (TopCat.of M))
    (s : (smoothSheafModule I M 𝕜 V).obj.obj (op W)) (i : ι) :
    (Pi.π (fun i ↦ (prod.functor.obj (U i)).op ⋙ (smoothSheafModule I M 𝕜 V).obj) i).app (op W)
        ((retractPiRestrict U ρ hρ).i.app (op W) s) =
      (smoothSheafModule I M 𝕜 V).obj.map (prod.snd : U i ⨯ W ⟶ W).op s := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app]
  exact congrArg (fun f ↦ f s) (congrArg (fun α ↦ ConcreteCategory.hom (NatTrans.app α (op W)))
    (Pi.lift_comp_π (restrictHom (U := U)) i))

/-- The retraction of `retractPiRestrict` is gluing with the partition of unity: it sends a family
of sections `sᵢ` over the opens `U i ∩ W` to the function `∑ᵢ ρ i • sᵢ` on `W`, each `sᵢ` extended
by zero. -/
theorem sectionsEquiv_retractPiRestrict_r_app (W : Opens (TopCat.of M))
    (x : (∏ᶜ fun i ↦ (prod.functor.obj (U i)).op ⋙ (smoothSheafModule I M 𝕜 V).obj).obj
      (op W)) (y : W) :
    (sectionsEquiv I 𝕜 V W ((retractPiRestrict U ρ hρ).r.app (op W) x)).1 y =
      ∑ᶠ i, ρ i y • Subtype.val.extend (sectionsEquiv I 𝕜 V (U i ⨯ W)
        ((Pi.π (fun i ↦ (prod.functor.obj (U i)).op ⋙ (smoothSheafModule I M 𝕜 V).obj) i).app
          (op W) x)).1 0 (y : M) :=
  congrFun (sectionsEquiv_glueHom_app U ρ hρ W x) y

end Retract

/-! ### Čech acyclicity -/

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

variable (I 𝕜 V) in
/-- **The sheaf of smooth functions is acyclic for every open cover.** For an open cover `U` of a
Hausdorff, `σ`-compact manifold modelled on a finite-dimensional space, the augmented Čech complex
`0 ⟶ ℰ(M) ⟶ Č⁰(U, ℰ) ⟶ Č¹(U, ℰ) ⟶ ⋯` of the sheaf `ℰ` of smooth `V`-valued functions is exact. -/
theorem quasiIso_cechAugmentation {ι : Type u} (U : ι → Opens (TopCat.of M))
    (hU : IsOpenCover U) :
    QuasiIso (CategoryTheory.cechAugmentation U isTerminalTop (smoothSheafModule I M 𝕜 V).obj) := by
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ
    (fun i ↦ (U i : Set M)) (fun i ↦ (U i).isOpen) hU.iSup_set_eq_univ.ge
  exact CategoryTheory.quasiIso_cechAugmentation_of_retract_pi U isTerminalTop _
    (retractPiRestrict U ρ hρ)

variable (I M 𝕜 V) in
/-- **The sheaf of smooth functions has no higher Čech cohomology.** On a Hausdorff, `σ`-compact
manifold modelled on a finite-dimensional space, the Čech cohomology of the sheaf of smooth
`V`-valued functions vanishes in every positive degree. -/
theorem isZero_cechCohomology_obj_succ (n : ℕ) :
    IsZero ((Topology.cechCohomology (TopCat.of M) (ModuleCat.{max u v} 𝕜) (n + 1)).obj
      (smoothSheafModule I M 𝕜 V).obj) :=
  CategoryTheory.isZero_cechCohomology_obj_succ_of_quasiIso _ _ n isTerminalTop _ fun U ↦
    quasiIso_cechAugmentation I 𝕜 V U.opens U.isOpenCover

end smoothSheafModule

end TauCeti
