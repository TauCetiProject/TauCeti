/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Geometry.Manifold.Sheaf.Smooth.Basic
public import TauCeti.Geometry.Manifold.Sheaf.Smooth.Restrict
public import TauCeti.Topology.Sheaves.Fine

/-!
# Fineness and sheaf cohomology of smooth functions on a manifold

Smooth partitions of unity make the sheaves of smooth vector-valued functions on a Hausdorff,
`σ`-compact finite-dimensional real manifold *fine* (`TopCat.Sheaf.IsFine`), both as sheaves of
abelian groups (`smoothSheafAddCommGroup I 𝓘(ℝ, V) M V`) and as sheaves of `𝕜`-modules
(`TauCeti.smoothSheafModule I M 𝕜 V`). By the general acyclicity of fine sheaves
(`TauCeti.Topology.Sheaves.Fine`), their sheaf cohomology vanishes in every positive degree, with
no boundarylessness assumption on the model with corners `I`.

When `M` is Hausdorff and second countable, every open subset `U` of `M` is itself a Hausdorff,
`σ`-compact smooth manifold whose restricted sheaf `U.sheafRestrict.obj _` is isomorphic to the
sheaf of smooth functions on `U` (`TauCeti.smoothSheafAddCommGroup.restrictIso`). Consequently the
cohomology `Sheaf.H'` vanishes in positive degrees over every open subset `U` of `M` as well as
globally (`TauCeti.subsingleton_H'_smoothSheafAddCommGroup`,
`TauCeti.subsingleton_H_smoothSheafAddCommGroup`). For Čech acyclicity of
`TauCeti.smoothSheafModule` with respect to individual open covers, see
`TauCeti.Geometry.Manifold.Sheaf.Smooth.Cech`.

## Main declarations

* `TauCeti.smoothSheafAddCommGroup.smulEnd`, `TauCeti.smoothSheafModule.smulEnd`: pointwise scalar
  multiplication of smooth vector-valued sections by a global smooth scalar function.
* `TauCeti.smoothSheafModule.forgetAddCommGrpIso`: forgetting the `𝕜`-module structure on
  `TauCeti.smoothSheafModule I M 𝕜 V` recovers `smoothSheafAddCommGroup I 𝓘(ℝ, V) M V`.
* `SmoothPartitionOfUnity.isPartitionOfUnity_smoothSheafAddCommGroup`,
  `SmoothPartitionOfUnity.isPartitionOfUnity_smoothSheafModule`: a subordinate smooth partition of
  unity induces a sheaf partition of unity on smooth functions.
* `TauCeti.smoothSheafAddCommGroup.isFine`, `TauCeti.smoothSheafModule.isFine`: sheaves of smooth
  vector-valued functions on Hausdorff, `σ`-compact finite-dimensional manifolds are fine.
* `TauCeti.smoothSheafModule.isZero_rightDerived_Γ_of_pos`: positive right derived global sections
  of `TauCeti.smoothSheafModule I M 𝕜 V` vanish.
* `TauCeti.subsingleton_H'_smoothSheafAddCommGroup`,
  `TauCeti.subsingleton_H_smoothSheafAddCommGroup`: positive-degree sheaf cohomology of
  `smoothSheafAddCommGroup I 𝓘(ℝ, V) M V` vanishes over every open subset and globally on any
  Hausdorff, second-countable finite-dimensional smooth manifold.

## References

* R. Godement, *Topologie algébrique et théorie des faisceaux*, Hermann, Paris, 1958, Chapitre II,
  §3.7 and §4.4.
* Frank W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer, 1983, Chapter 5, §5.11 and §5.25.
-/

public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace Topology
open scoped ContDiff Manifold

universe u v

namespace TauCeti

/-! ### Scalar multiplication by global smooth functions -/

/-- Restricting smooth scalar functions on `M` to an open subset `W`, as a ring homomorphism. -/
private def restrictScalarRingHom {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
    {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}
    {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
    (W : Opens M) : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯ →+* C^∞⟮IM, W; 𝓘(𝕜), 𝕜⟯ where
  toFun g := ⟨fun x ↦ g x.1, g.contMDiff.comp contMDiff_subtype_val⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

namespace smoothSheafAddCommGroup

section ScalarField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)
  {M : Type u} [TopologicalSpace M] [ChartedSpace HM M]
  (V : Type u) [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- Pointwise multiplication on sections over `W` as an additive homomorphism from smooth scalar
functions on `W` to endomorphisms of `(smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V).obj.obj (op W)`. -/
private def smulAppHom (W : Opens (TopCat.of M)) :
    C^∞⟮IM, W; 𝓘(𝕜), 𝕜⟯ →+
      ((smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V).obj.obj (op W) ⟶
        (smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V).obj.obj (op W)) :=
  (AddCommGrpCat.homAddEquiv
    (M := (smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V).obj.obj (op W))
    (N := (smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V).obj.obj (op W))).symm.toAddMonoidHom.comp
      (Module.toAddMonoidEnd C^∞⟮IM, W; 𝓘(𝕜), 𝕜⟯ C^∞⟮IM, W; 𝓘(𝕜, V), V⟯).toAddMonoidHom

private theorem smulAppHom_one (W : Opens (TopCat.of M)) :
    smulAppHom IM V W 1 = 𝟙 ((smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V).obj.obj (op W)) :=
  congrArg
    (AddCommGrpCat.homAddEquiv
      (M := (smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V).obj.obj (op W))
      (N := (smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V).obj.obj (op W))).symm
    (map_one (Module.toAddMonoidEnd C^∞⟮IM, W; 𝓘(𝕜), 𝕜⟯ C^∞⟮IM, W; 𝓘(𝕜, V), V⟯))

/-- Pointwise multiplication by a global smooth scalar function `g : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯` as an
endomorphism of `smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V`. -/
def smulEnd (g : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯) :
    smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V ⟶ smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V :=
  ObjectProperty.homMk
    { app U := smulAppHom IM V U.unop (restrictScalarRingHom U.unop g)
      naturality _ _ _ :=
        AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun _ ↦ ContMDiffMap.ext fun _ ↦ rfl }

private theorem smulEnd_hom_app (g : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯) (W : Opens (TopCat.of M)) :
    (smulEnd IM V g).hom.app (op W) = smulAppHom IM V W (restrictScalarRingHom W g) :=
  rfl

/-- Evaluating `smulEnd IM V g` at a section over `W` multiplies pointwise by `g`. -/
@[simp]
theorem smulEnd_hom_app_apply (g : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯) (W : Opens (TopCat.of M))
    (f : C^∞⟮IM, W; 𝓘(𝕜, V), V⟯) (x : W) :
    @DFunLike.coe (no_index C^∞⟮IM, W; 𝓘(𝕜, V), V⟯) (no_index ↥W) (fun _ ↦ V) _
        (no_index ((smulEnd IM V g).hom.app (op W) f)) x =
      g x.1 • f x :=
  (rfl)

/-- Multiplication by the zero smooth function is the zero sheaf endomorphism. -/
@[simp]
theorem smulEnd_zero :
    smulEnd IM V (0 : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯) = 0 :=
  Sheaf.hom_ext <| NatTrans.ext <| funext fun ⟨W⟩ ↦ by
    rw [smulEnd_hom_app, map_zero, map_zero]
    rfl

/-- Multiplication by the constant smooth function `1` is the identity sheaf endomorphism. -/
@[simp]
theorem smulEnd_one :
    smulEnd IM V (1 : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯) = 𝟙 (smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V) :=
  Sheaf.hom_ext <| NatTrans.ext <| funext fun ⟨W⟩ ↦ by
    rw [smulEnd_hom_app, map_one, smulAppHom_one]
    rfl

/-- Pointwise multiplication by `g₁ + g₂` is the sum of the corresponding sheaf endomorphisms. -/
theorem smulEnd_add (g₁ g₂ : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯) :
    smulEnd IM V (g₁ + g₂) = smulEnd IM V g₁ + smulEnd IM V g₂ :=
  Sheaf.hom_ext <| NatTrans.ext <| funext fun ⟨W⟩ ↦ by
    rw [Sheaf.Hom.add_app, smulEnd_hom_app, map_add, map_add, smulEnd_hom_app, smulEnd_hom_app]

end ScalarField

end smoothSheafAddCommGroup

namespace smoothSheafModule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]

section ModuleEnd

variable (V : Type v) [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V]
  [IsScalarTower ℝ 𝕜 V]

/-- Pointwise multiplication of smooth `V`-valued functions on `W` by a real-valued smooth function
`g` on `W`, as a `𝕜`-linear endomorphism of `smoothSections I 𝕜 V W`. -/
private def smulLinearMap {W : Opens M} (g : C^∞⟮I, W; 𝓘(ℝ), ℝ⟯) :
    smoothSections I 𝕜 V W →ₗ[𝕜] smoothSections I 𝕜 V W where
  toFun f := ⟨fun x ↦ g x • f.1 x,
    mem_smoothSections_iff.2 (g.contMDiff.smul (mem_smoothSections_iff.1 f.2))⟩
  map_add' f₁ f₂ := Subtype.ext <| funext fun x ↦ smul_add (g x) (f₁.1 x) (f₂.1 x)
  map_smul' c f := Subtype.ext <| funext fun x ↦ by
    simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
    rw [← algebraMap_smul 𝕜 (g x), ← algebraMap_smul 𝕜 (g x), smul_smul, mul_comm, smul_smul]

/-- Conjugate of `smulLinearMap` across `sectionsEquiv` on sections over `W`. -/
private def smulSectionsLinearMap {W : Opens M} (g : C^∞⟮I, W; 𝓘(ℝ), ℝ⟯) :
    (smoothSheafModule I M 𝕜 V).obj.obj (op W) →ₗ[𝕜]
      (smoothSheafModule I M 𝕜 V).obj.obj (op W) :=
  (sectionsEquiv I 𝕜 V W).symm.toLinearMap.comp
    ((smulLinearMap I 𝕜 V g).comp (sectionsEquiv I 𝕜 V W).toLinearMap)

private theorem sectionsEquiv_smulSectionsLinearMap_apply {W : Opens M}
    (g : C^∞⟮I, W; 𝓘(ℝ), ℝ⟯) (f : (smoothSheafModule I M 𝕜 V).obj.obj (op W)) (x : W) :
    (sectionsEquiv I 𝕜 V W (smulSectionsLinearMap I 𝕜 V g f)).1 x =
      g x • (sectionsEquiv I 𝕜 V W f).1 x := by
  simp [smulSectionsLinearMap, smulLinearMap]

/-- Pointwise multiplication on sections over `W` as an additive homomorphism from smooth real
functions on `W` to endomorphisms of `(smoothSheafModule I M 𝕜 V).obj.obj (op W)`. -/
private def smulAppHom (W : Opens M) :
    C^∞⟮I, W; 𝓘(ℝ), ℝ⟯ →+
      ((smoothSheafModule I M 𝕜 V).obj.obj (op W) ⟶
        (smoothSheafModule I M 𝕜 V).obj.obj (op W)) where
  toFun g := ModuleCat.ofHom (smulSectionsLinearMap I 𝕜 V g)
  map_zero' := by
    refine ModuleCat.hom_ext <| LinearMap.ext fun (f : (smoothSheafModule I M 𝕜 V).obj.obj (op W)) ↦
      smoothSheafModule.ext fun x ↦ ?_
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_zero, LinearMap.zero_apply, map_zero,
      Submodule.coe_zero, Pi.zero_apply]
    rw [sectionsEquiv_smulSectionsLinearMap_apply, ContMDiffMap.coe_zero, Pi.zero_apply, zero_smul]
  map_add' g₁ g₂ := by
    refine ModuleCat.hom_ext <| LinearMap.ext fun (f : (smoothSheafModule I M 𝕜 V).obj.obj (op W)) ↦
      smoothSheafModule.ext fun x ↦ ?_
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_add, LinearMap.add_apply, map_add,
      Submodule.coe_add, Pi.add_apply]
    rw [sectionsEquiv_smulSectionsLinearMap_apply, sectionsEquiv_smulSectionsLinearMap_apply,
      sectionsEquiv_smulSectionsLinearMap_apply, ContMDiffMap.coe_add, Pi.add_apply, add_smul]

private theorem smulAppHom_one (W : Opens M) :
    smulAppHom I 𝕜 V W 1 = 𝟙 ((smoothSheafModule I M 𝕜 V).obj.obj (op W)) := by
  refine ModuleCat.hom_ext <| LinearMap.ext fun f ↦ smoothSheafModule.ext fun x ↦ ?_
  simp only [smulAppHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ModuleCat.hom_ofHom,
    ModuleCat.hom_id, LinearMap.id_apply]
  rw [sectionsEquiv_smulSectionsLinearMap_apply, ContMDiffMap.coe_one, Pi.one_apply, one_smul]

/-- Pointwise multiplication by a global smooth function `g : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯` as an
endomorphism of the sheaf of `𝕜`-modules `smoothSheafModule I M 𝕜 V`. -/
def smulEnd (g : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) :
    smoothSheafModule I M 𝕜 V ⟶ smoothSheafModule I M 𝕜 V :=
  ObjectProperty.homMk
    { app U := smulAppHom I 𝕜 V U.unop (restrictScalarRingHom U.unop g)
      naturality W₁ W₂ h := by
        induction W₁ using Opposite.rec with | op W₁ =>
        induction W₂ using Opposite.rec with | op W₂ =>
        refine ModuleCat.hom_ext <| LinearMap.ext fun f ↦ smoothSheafModule.ext fun x ↦ ?_
        simp only [smulAppHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ModuleCat.hom_comp,
          LinearMap.comp_apply, ModuleCat.hom_ofHom]
        rw [← Quiver.Hom.op_unop h, sectionsEquiv_map, sectionsEquiv_smulSectionsLinearMap_apply,
          sectionsEquiv_map, Function.comp_apply, Function.comp_apply,
          sectionsEquiv_smulSectionsLinearMap_apply]
        rfl }

private theorem smulEnd_hom_app (g : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) (W : Opens M) :
    (smulEnd I 𝕜 V g).hom.app (op W) = smulAppHom I 𝕜 V W (restrictScalarRingHom W g) :=
  rfl

/-- Evaluating `smulEnd I 𝕜 V g` on a section over `W` multiplies pointwise by `g`. -/
@[simp]
theorem sectionsEquiv_smulEnd_hom_app (g : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) (W : Opens M)
    (f : (smoothSheafModule I M 𝕜 V).obj.obj (op W)) (x : W) :
    (sectionsEquiv I 𝕜 V W ((smulEnd I 𝕜 V g).hom.app (op W) f)).1 x =
      g x.1 • (sectionsEquiv I 𝕜 V W f).1 x :=
  sectionsEquiv_smulSectionsLinearMap_apply I 𝕜 V (restrictScalarRingHom W g) f x

/-- Multiplication by `0` is the zero endomorphism of `smoothSheafModule I M 𝕜 V`. -/
@[simp]
theorem smulEnd_zero :
    smulEnd I 𝕜 V (0 : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) = 0 :=
  Sheaf.hom_ext <| NatTrans.ext <| funext fun ⟨W⟩ ↦ by
    rw [smulEnd_hom_app, map_zero, map_zero]
    rfl

/-- Multiplication by `1` is the identity endomorphism of `smoothSheafModule I M 𝕜 V`. -/
@[simp]
theorem smulEnd_one :
    smulEnd I 𝕜 V (1 : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) = 𝟙 (smoothSheafModule I M 𝕜 V) :=
  Sheaf.hom_ext <| NatTrans.ext <| funext fun ⟨W⟩ ↦ by
    rw [smulEnd_hom_app, map_one, smulAppHom_one]
    rfl

/-- Multiplication by `g₁ + g₂` is the sum of the corresponding module-sheaf endomorphisms. -/
theorem smulEnd_add (g₁ g₂ : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) :
    smulEnd I 𝕜 V (g₁ + g₂) = smulEnd I 𝕜 V g₁ + smulEnd I 𝕜 V g₂ :=
  Sheaf.hom_ext <| NatTrans.ext <| funext fun ⟨W⟩ ↦ by
    rw [Sheaf.Hom.add_app, smulEnd_hom_app, map_add, map_add, smulEnd_hom_app, smulEnd_hom_app]

end ModuleEnd

section ForgetComparison

variable (V : Type u) [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V]
  [IsScalarTower ℝ 𝕜 V]

/-- Additive equivalence between sections of `smoothSheafModule I M 𝕜 V` over `W` and
`C^∞⟮I, W; 𝓘(ℝ, V), V⟯`. -/
private def sectionsObjAddEquiv (W : Opens (TopCat.of M)) :
    (smoothSheafModule I M 𝕜 V).obj.obj (op W) ≃+ C^∞⟮I, W; 𝓘(ℝ, V), V⟯ :=
  (sectionsEquiv I 𝕜 V W).toAddEquiv.trans
    { toFun f := ⟨f.1, mem_smoothSections_iff.1 f.2⟩
      invFun f := ⟨f, mem_smoothSections_iff.2 f.contMDiff⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl }

variable (M) in
/-- Forgetting the `𝕜`-module structure on `smoothSheafModule I M 𝕜 V` yields Mathlib's abelian
sheaf `smoothSheafAddCommGroup I 𝓘(ℝ, V) M V` of smooth `V`-valued functions. -/
def forgetAddCommGrpIso :
    (sheafCompose (Opens.grothendieckTopology (TopCat.of M))
        (forget₂ (ModuleCat.{u} 𝕜) AddCommGrpCat.{u})).obj (smoothSheafModule I M 𝕜 V) ≅
      smoothSheafAddCommGroup I 𝓘(ℝ, V) M V :=
  ObjectProperty.isoMk _ <| NatIso.ofComponents
    (fun U ↦ AddEquiv.toAddCommGrpIso
      (X := ((sheafCompose (Opens.grothendieckTopology (TopCat.of M))
        (forget₂ (ModuleCat.{u} 𝕜) AddCommGrpCat.{u})).obj
          (smoothSheafModule I M 𝕜 V)).obj.obj U)
      (Y := (smoothSheafAddCommGroup I 𝓘(ℝ, V) M V).obj.obj U)
      (sectionsObjAddEquiv I 𝕜 V U.unop))
    (fun {W₁ W₂} h ↦ by
      induction W₁ using Opposite.rec with | op W₁ =>
      induction W₂ using Opposite.rec with | op W₂ =>
      exact AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun f ↦
        ContMDiffMap.ext fun x ↦ congr_fun (sectionsEquiv_map h.unop f) x)

/-- Evaluating `forgetAddCommGrpIso` in the forward direction preserves underlying functions. -/
@[simp]
theorem forgetAddCommGrpIso_hom_app_apply (W : Opens (TopCat.of M))
    (f : (smoothSheafModule I M 𝕜 V).obj.obj (op W)) (x : W) :
    @DFunLike.coe (no_index C^∞⟮I, W; 𝓘(ℝ, V), V⟯) (no_index ↥W) (fun _ ↦ V) _
        (no_index ((forgetAddCommGrpIso I M 𝕜 V).hom.hom.app (op W) f)) x =
      (sectionsEquiv I 𝕜 V W f).1 x :=
  (rfl)

/-- Evaluating `forgetAddCommGrpIso` in the inverse direction preserves underlying functions. -/
@[simp]
theorem sectionsEquiv_forgetAddCommGrpIso_inv_app (W : Opens (TopCat.of M))
    (f : C^∞⟮I, W; 𝓘(ℝ, V), V⟯) (x : W) :
    (sectionsEquiv I 𝕜 V W ((forgetAddCommGrpIso I M 𝕜 V).inv.hom.app (op W) f)).1 x = f x :=
  congr_fun (congrArg Subtype.val
    ((sectionsEquiv I 𝕜 V W).apply_symm_apply ⟨f, mem_smoothSections_iff.2 f.contMDiff⟩)) x

end ForgetComparison

end smoothSheafModule

end TauCeti

/-! ### Sheaf partitions of unity from smooth partitions of unity -/

namespace SmoothPartitionOfUnity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type*} {U : ι → Opens (TopCat.of M)}

/-- The open complement `(tsupport (ρ i))ᶜ` of the topological support of the `i`-th function in a
smooth partition of unity `ρ`. -/
private def complSupport (ρ : SmoothPartitionOfUnity ι I M) (i : ι) : Opens (TopCat.of M) :=
  ⟨(tsupport (ρ i))ᶜ, (isClosed_tsupport _).isOpen_compl⟩

private theorem sup_complSupport_eq_top {ρ : SmoothPartitionOfUnity ι I M}
    (hρ : ρ.IsSubordinate fun i ↦ (U i : Set M)) (i : ι) :
    U i ⊔ complSupport ρ i = ⊤ := by
  ext x
  simp only [Opens.coe_sup, Opens.coe_top, Set.mem_union, Set.mem_univ, iff_true]
  by_cases hx : x ∈ tsupport (ρ i)
  · exact Or.inl (hρ i hx)
  · exact Or.inr hx

private theorem restrictScalar_eq_zero_of_le_complSupport (ρ : SmoothPartitionOfUnity ι I M) (i : ι)
    {W : Opens (TopCat.of M)} (hW : W ≤ complSupport ρ i) :
    TauCeti.restrictScalarRingHom W (ρ i) = 0 :=
  ContMDiffMap.ext fun y ↦ image_eq_zero_of_notMem_tsupport (f := ρ i) (hW y.2)

private theorem sum_restrictScalar_eq_one (ρ : SmoothPartitionOfUnity ι I M) {s : Finset ι}
    {W : Opens (TopCat.of M)} (hsum : ∀ y : W, ∑ i ∈ s, ρ i y.1 = 1) :
    ∑ i ∈ s, TauCeti.restrictScalarRingHom W (ρ i) = 1 :=
  ContMDiffMap.ext fun y ↦
    (map_sum (ContMDiffMap.evalRingHom y : C^∞⟮I, W; 𝓘(ℝ), ℝ⟯ →+* ℝ)
      (fun i ↦ TauCeti.restrictScalarRingHom W (ρ i)) s).trans (hsum y)

private theorem exists_local_finset (ρ : SmoothPartitionOfUnity ι I M) (x : M) :
    ∃ (N : Opens (TopCat.of M)) (_ : x ∈ N) (s : Finset ι),
      (∀ i, i ∉ s → N ≤ complSupport ρ i) ∧
      ∀ ⦃W : Opens (TopCat.of M)⦄, W ≤ N → ∀ y : W, ∑ i ∈ s, ρ i y.1 = 1 := by
  obtain ⟨O, hO_sub, hO_open, hxO⟩ := mem_nhds_iff.1 (ρ.eventually_fintsupport_subset x)
  refine ⟨⟨O, hO_open⟩, hxO, ρ.fintsupport x,
    fun i hi y hy hmem ↦ hi (hO_sub hy ((ρ.mem_fintsupport_iff y i).2 hmem)), fun W hW y ↦ ?_⟩
  exact ρ.sum_finsupport' y.1 (Set.mem_univ y.1)
    ((ρ.finsupport_subset_fintsupport y.1).trans (hO_sub (hW y.2)))

/-- A smooth partition of unity `ρ` subordinate to an open family `U` induces a sheaf partition of
unity on `smoothSheafAddCommGroup I 𝓘(ℝ, V) M V` by pointwise multiplication. -/
theorem isPartitionOfUnity_smoothSheafAddCommGroup (ρ : SmoothPartitionOfUnity ι I M)
    (hρ : ρ.IsSubordinate fun i ↦ (U i : Set M))
    (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    (smoothSheafAddCommGroup I 𝓘(ℝ, V) M V).IsPartitionOfUnity U
      (fun i ↦ TauCeti.smoothSheafAddCommGroup.smulEnd I V (ρ i)) := by
  refine TopCat.Sheaf.isPartitionOfUnity_iff.2
    ⟨complSupport ρ, sup_complSupport_eq_top hρ, fun i W hW ↦ ?_, fun x ↦ ?_⟩
  · rw [TauCeti.smoothSheafAddCommGroup.smulEnd_hom_app,
      restrictScalar_eq_zero_of_le_complSupport ρ i hW, map_zero]
  · obtain ⟨N, hxN, s, hs, hsum⟩ := exists_local_finset ρ x
    refine ⟨N, hxN, s, hs, fun W hW ↦ ?_⟩
    rw [Finset.sum_congr rfl fun i _ ↦
        TauCeti.smoothSheafAddCommGroup.smulEnd_hom_app I V (ρ i) W,
      ← map_sum, sum_restrictScalar_eq_one ρ (hsum hW),
      TauCeti.smoothSheafAddCommGroup.smulAppHom_one]

/-- A smooth partition of unity `ρ` subordinate to an open family `U` induces a sheaf partition of
unity on `TauCeti.smoothSheafModule I M 𝕜 V` by pointwise multiplication. -/
theorem isPartitionOfUnity_smoothSheafModule (ρ : SmoothPartitionOfUnity ι I M)
    (hρ : ρ.IsSubordinate fun i ↦ (U i : Set M))
    (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    (V : Type v) [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V]
    [IsScalarTower ℝ 𝕜 V] :
    (TauCeti.smoothSheafModule I M 𝕜 V).IsPartitionOfUnity U
      (fun i ↦ TauCeti.smoothSheafModule.smulEnd I 𝕜 V (ρ i)) := by
  refine TopCat.Sheaf.isPartitionOfUnity_iff.2
    ⟨complSupport ρ, sup_complSupport_eq_top hρ, fun i W hW ↦ ?_, fun x ↦ ?_⟩
  · rw [TauCeti.smoothSheafModule.smulEnd_hom_app,
      restrictScalar_eq_zero_of_le_complSupport ρ i hW, map_zero]
  · obtain ⟨N, hxN, s, hs, hsum⟩ := exists_local_finset ρ x
    refine ⟨N, hxN, s, hs, fun W hW ↦ ?_⟩
    rw [Finset.sum_congr rfl fun i _ ↦
        TauCeti.smoothSheafModule.smulEnd_hom_app I 𝕜 V (ρ i) W,
      ← map_sum, sum_restrictScalar_eq_one ρ (hsum hW),
      TauCeti.smoothSheafModule.smulAppHom_one]

end SmoothPartitionOfUnity

/-! ### Fineness and positive-degree sheaf cohomology vanishing -/

namespace TauCeti

section SigmaCompact

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-- Every open cover of `TopCat.of M` in the `Opens` lattice admits a subordinate smooth partition
of unity. -/
private theorem exists_smoothPartitionOfUnity_of_iSup_eq_top {ι : Type u}
    {U : ι → Opens (TopCat.of M)} (hU : ⨆ i, U i = ⊤) :
    ∃ ρ : SmoothPartitionOfUnity ι I M Set.univ,
      ρ.IsSubordinate (fun i ↦ (U i : Set M)) := by
  refine SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ
    (fun i ↦ (U i : Set M)) (fun i ↦ (U i).isOpen) fun x _ ↦ ?_
  have hx : x ∈ (⨆ i, U i : Opens (TopCat.of M)) := by
    rw [hU]
    exact Set.mem_univ x
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.1 hx
  exact Set.mem_iUnion.2 ⟨i, hxi⟩

namespace smoothSheafAddCommGroup

/-- On a Hausdorff, `σ`-compact finite-dimensional smooth real manifold (possibly with boundary or
corners), the sheaf `smoothSheafAddCommGroup I 𝓘(ℝ, V) M V` of smooth `V`-valued functions is
fine. -/
instance isFine (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    (smoothSheafAddCommGroup I 𝓘(ℝ, V) M V).IsFine where
  exists_isPartitionOfUnity _ U hU := by
    obtain ⟨ρ, hρ⟩ := exists_smoothPartitionOfUnity_of_iSup_eq_top I hU
    exact ⟨_, ρ.isPartitionOfUnity_smoothSheafAddCommGroup hρ V⟩

/-- On a Hausdorff, `σ`-compact finite-dimensional smooth real manifold, the sheaf cohomology of
`smoothSheafAddCommGroup I 𝓘(ℝ, V) M V` vanishes in every positive degree. -/
theorem subsingleton_H_of_pos {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (hn : 0 < n) :
    Subsingleton ((smoothSheafAddCommGroup I 𝓘(ℝ, V) M V).H n) :=
  TopCat.Sheaf.IsFine.subsingleton_H_of_pos inferInstance n hn

end smoothSheafAddCommGroup

namespace smoothSheafModule

/-- On a Hausdorff, `σ`-compact finite-dimensional smooth real manifold (possibly with boundary or
corners), the module sheaf `smoothSheafModule I M 𝕜 V` of smooth `V`-valued functions is fine. -/
instance isFine (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    (V : Type v) [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V]
    [IsScalarTower ℝ 𝕜 V] :
    (smoothSheafModule I M 𝕜 V).IsFine where
  exists_isPartitionOfUnity _ U hU := by
    obtain ⟨ρ, hρ⟩ := exists_smoothPartitionOfUnity_of_iSup_eq_top I hU
    exact ⟨_, ρ.isPartitionOfUnity_smoothSheafModule hρ 𝕜 V⟩

/-- On a Hausdorff, `σ`-compact finite-dimensional smooth real manifold, the right derived global
sections of `smoothSheafModule I M 𝕜 V` vanish in every positive degree. -/
theorem isZero_rightDerived_Γ_of_pos (𝕜 : Type u) [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    (V : Type u) [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V]
    [IsScalarTower ℝ 𝕜 V] (n : ℕ) (hn : 0 < n) :
    IsZero (((Sheaf.Γ (Opens.grothendieckTopology (TopCat.of M))
      (ModuleCat.{u} 𝕜)).rightDerived n).obj (smoothSheafModule I M 𝕜 V)) :=
  TauCeti.Topology.isZero_rightDerived_Γ_of_isFine_of_pos (smoothSheafModule I M 𝕜 V) n hn

end smoothSheafModule

end SigmaCompact

section OpenSubset

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Over any Hausdorff, `σ`-compact open subset `U` of a finite-dimensional smooth real manifold
`M` (without requiring `M` itself to be Hausdorff or `σ`-compact), the sheaf cohomology
`Sheaf.H'` of `smoothSheafAddCommGroup I 𝓘(ℝ, V) M V` vanishes in every positive degree. -/
theorem smoothSheafAddCommGroup.subsingleton_H'_of_sigmaCompactSpace
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (U : Opens (TopCat.of M)) [T2Space U] [SigmaCompactSpace U] (n : ℕ) (hn : 0 < n) :
    Subsingleton ((smoothSheafAddCommGroup I 𝓘(ℝ, V) M V).H' n U) := by
  have hFine : TopCat.Sheaf.IsFine (X := TopCat.of U)
      (U.sheafRestrict.obj (smoothSheafAddCommGroup I 𝓘(ℝ, V) M V)) :=
    TopCat.Sheaf.IsFine.of_iso (X := TopCat.of U)
      (smoothSheafAddCommGroup.restrictIso I 𝓘(ℝ, V) V U).symm
  exact TopCat.Sheaf.IsFine.subsingleton_H'_of_sheafRestrict_of_pos
    (F := smoothSheafAddCommGroup I 𝓘(ℝ, V) M V) (U := U) hFine n hn

end OpenSubset

section SecondCountable

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SecondCountableTopology M]
  {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Open-subset acyclicity of smooth functions.** On a Hausdorff, second-countable
finite-dimensional smooth real manifold (possibly with boundary or corners), the sheaf cohomology
`Sheaf.H'` of `smoothSheafAddCommGroup I 𝓘(ℝ, V) M V` vanishes in every positive degree over every
open subset `U` of `M`. -/
theorem subsingleton_H'_smoothSheafAddCommGroup (U : Opens (TopCat.of M)) (n : ℕ) (hn : 0 < n) :
    Subsingleton ((smoothSheafAddCommGroup I 𝓘(ℝ, V) M V).H' n U) := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace U := ChartedSpace.locallyCompactSpace H U
  exact smoothSheafAddCommGroup.subsingleton_H'_of_sigmaCompactSpace I U n hn

/-- **Acyclicity of the sheaf of smooth functions.** On a Hausdorff, second-countable
finite-dimensional smooth real manifold (possibly with boundary or corners), the sheaf cohomology
`Sheaf.H` of `smoothSheafAddCommGroup I 𝓘(ℝ, V) M V` vanishes in every positive degree. -/
theorem subsingleton_H_smoothSheafAddCommGroup (n : ℕ) (hn : 0 < n) :
    Subsingleton ((smoothSheafAddCommGroup I 𝓘(ℝ, V) M V).H n) := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  exact smoothSheafAddCommGroup.subsingleton_H_of_pos I n hn

end SecondCountable

end TauCeti
