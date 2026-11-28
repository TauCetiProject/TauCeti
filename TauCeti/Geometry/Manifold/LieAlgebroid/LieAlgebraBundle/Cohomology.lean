/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import TauCeti.Algebra.Lie.Cohomology.ChevalleyEilenberg
public import TauCeti.Algebra.Lie.Cohomology.Map
public import TauCeti.Geometry.Manifold.LieAlgebroid.ChevalleyEilenberg
public import TauCeti.Geometry.Manifold.LieAlgebroid.LieAlgebraBundle.Basic
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Chevalley–Eilenberg cohomology of a trivial Lie algebra bundle over a point

Over a one-point base manifold `[Unique M]`, sections of the trivial Lie algebra bundle
algebroid `TauCeti.LieAlgebroid.trivialLieAlgebra I M 𝔤` identify Lie-algebra-linearly with `𝔤`
via `TauCeti.LieAlgebroid.trivialLieAlgebraEvalEquiv`, smooth real functions `C^∞⟮I, M; ℝ⟯` identify
with the trivial `𝔤`-module `TrivialLieModule ℝ 𝔤 ℝ` (`trivialLieAlgebraFunctionEquiv`), and every
`ℝ`-multilinear alternating map on sections is automatically `C^∞(M)`-multilinear.

Consequently:
* `TauCeti.LieAlgebroid.trivialLieAlgebraCochainEquiv`: degree-`k` cochains of
  `trivialLieAlgebra I M 𝔤` identify `ℝ`-linearly with the Chevalley–Eilenberg cochains
  `𝔤 [⋀^Fin k]→ₗ[ℝ] TrivialLieModule ℝ 𝔤 ℝ`;
* `TauCeti.LieAlgebroid.trivialLieAlgebraCochainComplexIso`: the algebroid cochain complex
  `(trivialLieAlgebra I M 𝔤).cochainComplex` is canonically isomorphic to the universe lift along
  `ModuleCat.uliftFunctor` of
  `TauCeti.LieModule.Cohomology.cochainComplex ℝ 𝔤 (TrivialLieModule ℝ 𝔤 ℝ)` for arbitrary universes
  of the base manifold and Lie algebra;
* `TauCeti.LieAlgebroid.trivialLieAlgebraCohomologyIso`: induced isomorphism on degree-`k`
  cohomology.

## References

* K. C. H. Mackenzie, *General theory of Lie groupoids and Lie algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), §3.3 and §7.1.
* C. Chevalley and S. Eilenberg, *Cohomology theory of Lie groups and Lie algebras*, Trans. Amer.
  Math. Soc. 63 (1948), 85–124.
-/

public section

noncomputable section

open Bundle CategoryTheory Function Manifold
open scoped ContDiff

namespace TauCeti.LieAlgebroid

section Point

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
  [ChartedSpace H M] [Unique M] [IsManifold I ∞ M] (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  [TopologicalSpace 𝔤] [IsTopologicalAddGroup 𝔤] [ContinuousSMul ℝ 𝔤] [T2Space 𝔤]
  [FiniteDimensional ℝ 𝔤]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [TopologicalSpace 𝔤]
  [IsTopologicalAddGroup 𝔤] [ContinuousSMul ℝ 𝔤] [T2Space 𝔤] [FiniteDimensional ℝ 𝔤] in
/-- Over a one-point manifold, evaluation at `default` identifies `C^∞⟮I, M; ℝ⟯` linearly with
the trivial `𝔤`-module `TrivialLieModule ℝ 𝔤 ℝ`. -/
def trivialLieAlgebraFunctionEquiv : C^∞⟮I, M; ℝ⟯ ≃ₗ[ℝ] TrivialLieModule ℝ 𝔤 ℝ where
  toFun f := (TrivialLieModule.equiv ℝ 𝔤 ℝ).symm (f default)
  invFun m := algebraMap ℝ C^∞⟮I, M; ℝ⟯ (TrivialLieModule.equiv ℝ 𝔤 ℝ m)
  map_add' _ _ := by simp
  map_smul' c f := (TrivialLieModule.equiv ℝ 𝔤 ℝ).symm.map_smul c (f default)
  left_inv f := by
    ext x
    rw [Unique.eq_default x]
    simp [ContMDiffMap.algebraMap_apply]
  right_inv _ := by simp

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [TopologicalSpace 𝔤]
  [IsTopologicalAddGroup 𝔤] [ContinuousSMul ℝ 𝔤] [T2Space 𝔤] [FiniteDimensional ℝ 𝔤] in
/-- Evaluating `trivialLieAlgebraFunctionEquiv` on a smooth function evaluates it at `default`. -/
@[simp]
theorem trivialLieAlgebraFunctionEquiv_apply (f : C^∞⟮I, M; ℝ⟯) :
    trivialLieAlgebraFunctionEquiv I M 𝔤 f = (TrivialLieModule.equiv ℝ 𝔤 ℝ).symm (f default) :=
  (rfl)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [TopologicalSpace 𝔤]
  [IsTopologicalAddGroup 𝔤] [ContinuousSMul ℝ 𝔤] [T2Space 𝔤] [FiniteDimensional ℝ 𝔤] in
/-- The inverse of `trivialLieAlgebraFunctionEquiv` produces the constant smooth function. -/
@[simp]
theorem trivialLieAlgebraFunctionEquiv_symm_apply (m : TrivialLieModule ℝ 𝔤 ℝ) :
    (trivialLieAlgebraFunctionEquiv I M 𝔤).symm m =
      algebraMap ℝ C^∞⟮I, M; ℝ⟯ (TrivialLieModule.equiv ℝ 𝔤 ℝ m) := (rfl)

/-- `trivialLieAlgebraFunctionEquiv` intertwines the anchor-derivation action of constant sections
with the trivial `𝔤`-module action. -/
theorem trivialLieAlgebraFunctionEquiv_lie (ξ : 𝔤) (f : C^∞⟮I, M; ℝ⟯) :
    trivialLieAlgebraFunctionEquiv I M 𝔤
        ⁅(trivialLieAlgebraEvalEquiv I M 𝔤).symm ξ, f⁆ =
      ⁅ξ, trivialLieAlgebraFunctionEquiv I M 𝔤 f⁆ := by
  have h0 : ⁅(trivialLieAlgebraEvalEquiv I M 𝔤).symm ξ, f⁆ = 0 := by
    ext x
    simp [Sections.lie_def]
  rw [h0, map_zero, trivial_lie_zero]

omit [FiniteDimensional ℝ E] in
/-- Over a one-point manifold, every `ℝ`-multilinear alternating map on sections of
`trivialLieAlgebra I M 𝔤` is automatically `C^∞(M)`-multilinear. -/
private theorem trivialLieAlgebra_map_update_smul {k : ℕ}
    (α : (trivialLieAlgebra I M 𝔤).Sections [⋀^Fin k]→ₗ[ℝ] C^∞⟮I, M; ℝ⟯)
    (v : Fin k → (trivialLieAlgebra I M 𝔤).Sections) (i : Fin k)
    (f : C^∞⟮I, M; ℝ⟯) (y : (trivialLieAlgebra I M 𝔤).Sections) :
    α (update v i (f • y)) = f • α (update v i y) := by
  have hf : f = algebraMap ℝ C^∞⟮I, M; ℝ⟯ (f default) := by
    ext x
    rw [Unique.eq_default x]
    simp [ContMDiffMap.algebraMap_apply]
  have hfy : f • y = (f default) • y := by
    conv_lhs => rw [hf]
    rw [algebraMap_smul]
  rw [hfy, α.map_update_smul]
  conv_rhs => rw [hf]
  rw [algebraMap_smul]

/-- Over a one-point manifold, scalar restriction from `C^∞⟮I, M; ℝ⟯` to `ℝ` is a linear
equivalence on alternating cochains of `trivialLieAlgebra I M 𝔤`. -/
private def trivialLieAlgebraRestrictEquiv (k : ℕ) :
    ((trivialLieAlgebra I M 𝔤).Sections [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) ≃ₗ[ℝ]
      ((trivialLieAlgebra I M 𝔤).Sections [⋀^Fin k]→ₗ[ℝ] C^∞⟮I, M; ℝ⟯) where
  toLinearMap := AlternatingMap.restrictScalarsₗ ℝ ℝ
  invFun α := α.ofRestrictScalars C^∞⟮I, M; ℝ⟯ (trivialLieAlgebra_map_update_smul I M 𝔤 α)
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

/-- Over a one-point manifold, degree-`k` cochains of `trivialLieAlgebra I M 𝔤` identify
`ℝ`-linearly with Chevalley–Eilenberg `k`-cochains of `𝔤` with trivial coefficients `ℝ`. -/
def trivialLieAlgebraCochainEquiv (k : ℕ) :
    Cₛ^∞⟮I; TrivialModel ℝ 𝔤 [⋀^Fin k]→L[ℝ] ℝ,
        fun x ↦ Bundle.Trivial M 𝔤 x [⋀^Fin k]→L[ℝ] ℝ⟯ ≃ₗ[ℝ]
      (𝔤 [⋀^Fin k]→ₗ[ℝ] TrivialLieModule ℝ 𝔤 ℝ) :=
  (((trivialLieAlgebra I M 𝔤).cochainEquiv k).restrictScalars ℝ).trans <|
    (trivialLieAlgebraRestrictEquiv I M 𝔤 k).trans <|
      TauCeti.LieModule.Cohomology.cochainEquiv
        (trivialLieAlgebraFunctionEquiv I M 𝔤) (trivialLieAlgebraEvalEquiv I M 𝔤).symm k

/-- Evaluating `trivialLieAlgebraCochainEquiv I M 𝔤 k φ` on `ξ : Fin k → 𝔤` evaluates `φ` at
`default` on `ξ`. -/
@[simp]
theorem trivialLieAlgebraCochainEquiv_apply (k : ℕ)
    (φ : Cₛ^∞⟮I; TrivialModel ℝ 𝔤 [⋀^Fin k]→L[ℝ] ℝ,
      fun x ↦ Bundle.Trivial M 𝔤 x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ξ : Fin k → 𝔤) :
    trivialLieAlgebraCochainEquiv I M 𝔤 k φ ξ =
      (TrivialLieModule.equiv ℝ 𝔤 ℝ).symm (φ default fun i ↦ ξ i) := by
  simp [trivialLieAlgebraCochainEquiv, trivialLieAlgebraRestrictEquiv]

/-- The inverse of `trivialLieAlgebraCochainEquiv I M 𝔤 k` constructs the constant alternating
section determined by a Lie-algebra cochain. -/
@[simp]
theorem trivialLieAlgebraCochainEquiv_symm_apply (k : ℕ)
    (α : 𝔤 [⋀^Fin k]→ₗ[ℝ] TrivialLieModule ℝ 𝔤 ℝ) (x : M) (v : Fin k → 𝔤) :
    ((trivialLieAlgebraCochainEquiv I M 𝔤 k).symm α) x v =
      TrivialLieModule.equiv ℝ 𝔤 ℝ (α v) := by
  have h2 := congrArg (fun ψ ↦ (TrivialLieModule.equiv ℝ 𝔤 ℝ) (ψ v))
    ((trivialLieAlgebraCochainEquiv I M 𝔤 k).apply_symm_apply α)
  rw [trivialLieAlgebraCochainEquiv_apply, LinearEquiv.apply_symm_apply,
    ← Unique.eq_default x] at h2
  exact h2

/-- Under `trivialLieAlgebraCochainEquiv`, the algebroid exterior derivative on
`trivialLieAlgebra I M 𝔤` corresponds to the Lie-algebra Chevalley–Eilenberg differential `d`. -/
theorem trivialLieAlgebraCochainEquiv_extDeriv (k : ℕ)
    (φ : Cₛ^∞⟮I; TrivialModel ℝ 𝔤 [⋀^Fin k]→L[ℝ] ℝ,
      fun x ↦ Bundle.Trivial M 𝔤 x [⋀^Fin k]→L[ℝ] ℝ⟯) :
    trivialLieAlgebraCochainEquiv I M 𝔤 (k + 1) ((trivialLieAlgebra I M 𝔤).extDeriv k φ) =
      TauCeti.LieModule.Cohomology.d ℝ 𝔤 (TrivialLieModule ℝ 𝔤 ℝ) k
        (trivialLieAlgebraCochainEquiv I M 𝔤 k φ) := by
  have h1 :
      AlternatingMap.restrictScalars ℝ
          ((trivialLieAlgebra I M 𝔤).cochainEquiv (k + 1)
            ((trivialLieAlgebra I M 𝔤).extDeriv k φ)) =
        TauCeti.LieModule.Cohomology.d ℝ (trivialLieAlgebra I M 𝔤).Sections C^∞⟮I, M; ℝ⟯ k
          (AlternatingMap.restrictScalars ℝ ((trivialLieAlgebra I M 𝔤).cochainEquiv k φ)) :=
    (trivialLieAlgebra I M 𝔤).restrictScalars_cochainEquiv_extDeriv k φ
  have h2 := TauCeti.LieModule.Cohomology.cochainMap_d
    (trivialLieAlgebraFunctionEquiv I M 𝔤).toLinearMap
    (trivialLieAlgebraEvalEquiv I M 𝔤).symm.toLieHom
    (trivialLieAlgebraFunctionEquiv_lie I M 𝔤) k
    (AlternatingMap.restrictScalars ℝ ((trivialLieAlgebra I M 𝔤).cochainEquiv k φ))
  simpa [trivialLieAlgebraCochainEquiv, trivialLieAlgebraRestrictEquiv,
    TauCeti.LieModule.Cohomology.cochainEquiv_toLinearMap] using (congrArg _ h1).trans h2

end Point

section Complex

universe uM uG

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (M : Type uM) [TopologicalSpace M]
  [ChartedSpace H M] [Unique M] [IsManifold I ∞ M] (𝔤 : Type uG) [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  [TopologicalSpace 𝔤] [IsTopologicalAddGroup 𝔤] [ContinuousSMul ℝ 𝔤] [T2Space 𝔤]
  [FiniteDimensional ℝ 𝔤]

private def uliftCochainComplexXIso (𝔤 : Type uG) [LieRing 𝔤] [LieAlgebra ℝ 𝔤] (k : ℕ) :
    (((ModuleCat.uliftFunctor.{uM, uG} ℝ).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (TauCeti.LieModule.Cohomology.cochainComplex ℝ 𝔤 (TrivialLieModule ℝ 𝔤 ℝ))).X k ≅
        ModuleCat.of ℝ (ULift.{uM, uG} (𝔤 [⋀^Fin k]→ₗ[ℝ] TrivialLieModule ℝ 𝔤 ℝ)) :=
  Iso.refl _

private theorem uliftCochainComplexXIso_inv_apply (𝔤 : Type uG) [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    (k : ℕ) (x : ULift.{uM, uG} (𝔤 [⋀^Fin k]→ₗ[ℝ] TrivialLieModule ℝ 𝔤 ℝ)) :
    (uliftCochainComplexXIso.{uM, uG} 𝔤 k).inv x = x := rfl

/-- Over a one-point manifold, the Chevalley–Eilenberg cochain complex of `trivialLieAlgebra I M 𝔤`
is canonically isomorphic to the universe lift of the Lie-algebra Chevalley–Eilenberg cochain
complex of `𝔤` with trivial coefficients `ℝ`. -/
def trivialLieAlgebraCochainComplexIso :
    (trivialLieAlgebra I M 𝔤).cochainComplex ≅
      ((ModuleCat.uliftFunctor.{uM, uG} ℝ).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (TauCeti.LieModule.Cohomology.cochainComplex ℝ 𝔤 (TrivialLieModule ℝ 𝔤 ℝ)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun k ↦ (trivialLieAlgebra I M 𝔤).cochainComplexXIso k ≪≫
      ((trivialLieAlgebraCochainEquiv I M 𝔤 k).trans ULift.moduleEquiv.symm).toModuleIso ≪≫
      (uliftCochainComplexXIso.{uM, uG} 𝔤 k).symm) <| by
    rintro k _ rfl
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [(trivialLieAlgebra I M 𝔤).cochainComplex_d_succ_assoc k]
    simp only [Functor.mapHomologicalComplex_obj_d,
      TauCeti.LieModule.Cohomology.cochainComplex_d_succ]
    refine ModuleCat.hom_ext <| LinearMap.ext fun φ ↦ ?_
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      LinearEquiv.toModuleIso_hom, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      ULift.moduleEquiv_symm_apply]
    have h := trivialLieAlgebraCochainEquiv_extDeriv I M 𝔤 k
      (((trivialLieAlgebra I M 𝔤).cochainComplexXIso k).hom φ)
    exact congrArg ULift.up h.symm

/-- On degree-`k` components, `(trivialLieAlgebraCochainComplexIso I M 𝔤).hom.f k` lifts
`trivialLieAlgebraCochainEquiv I M 𝔤 k` applied to `cochainComplexXIso.hom`. -/
theorem trivialLieAlgebraCochainComplexIso_hom_f_apply (k : ℕ)
    (x : (trivialLieAlgebra I M 𝔤).cochainComplex.X k) :
    (trivialLieAlgebraCochainComplexIso I M 𝔤).hom.f k x =
      ULift.up (trivialLieAlgebraCochainEquiv I M 𝔤 k
        (((trivialLieAlgebra I M 𝔤).cochainComplexXIso k).hom x)) := by
  simp only [trivialLieAlgebraCochainComplexIso, HomologicalComplex.Hom.isoOfComponents_hom_f,
    Iso.trans_hom, Iso.symm_hom]
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, LinearEquiv.toModuleIso_hom,
    ModuleCat.ofHom_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    ULift.moduleEquiv_symm_apply, uliftCochainComplexXIso_inv_apply]

/-- On degree-`k` components, `(trivialLieAlgebraCochainComplexIso I M 𝔤).inv.f k` inserts
`(trivialLieAlgebraCochainEquiv I M 𝔤 k).symm α.down` via `cochainComplexXIso.inv`. -/
theorem trivialLieAlgebraCochainComplexIso_inv_f_apply (k : ℕ)
    (α : ULift.{uM, uG} (𝔤 [⋀^Fin k]→ₗ[ℝ] TrivialLieModule ℝ 𝔤 ℝ)) :
    (trivialLieAlgebraCochainComplexIso I M 𝔤).inv.f k α =
      ((trivialLieAlgebra I M 𝔤).cochainComplexXIso k).inv
        ((trivialLieAlgebraCochainEquiv I M 𝔤 k).symm α.down) := by
  have h1 :
      (trivialLieAlgebraCochainComplexIso I M 𝔤).inv.f k α =
        ((trivialLieAlgebra I M 𝔤).cochainComplexXIso k).inv
          (((trivialLieAlgebraCochainEquiv I M 𝔤 k).trans
            ULift.moduleEquiv.symm).toModuleIso.inv α) := by
    simp only [trivialLieAlgebraCochainComplexIso, HomologicalComplex.Hom.isoOfComponents_inv_f,
      Iso.trans_inv, Iso.symm_inv, Category.assoc]
    -- `uliftCochainComplexXIso` is `Iso.refl _`, identifying `(...).X k` with `ULift`.
    rfl
  rw [h1, LinearEquiv.toModuleIso_inv, ModuleCat.ofHom_apply]
  simp

/-- Evaluating `(trivialLieAlgebraCochainComplexIso I M 𝔤).hom.f k` on a section inserted via
`cochainComplexXIso` gives `ULift.up` of `trivialLieAlgebraCochainEquiv I M 𝔤 k`. -/
theorem trivialLieAlgebraCochainComplexIso_hom_f_inv_apply (k : ℕ)
    (φ : Cₛ^∞⟮I; TrivialModel ℝ 𝔤 [⋀^Fin k]→L[ℝ] ℝ,
      fun x ↦ Bundle.Trivial M 𝔤 x [⋀^Fin k]→L[ℝ] ℝ⟯) :
    (trivialLieAlgebraCochainComplexIso I M 𝔤).hom.f k
        (((trivialLieAlgebra I M 𝔤).cochainComplexXIso k).inv φ) =
      ULift.up (trivialLieAlgebraCochainEquiv I M 𝔤 k φ) := by
  rw [trivialLieAlgebraCochainComplexIso_hom_f_apply, Iso.inv_hom_id_apply]

/-- Reading `(trivialLieAlgebraCochainComplexIso I M 𝔤).inv.f k α` through `cochainComplexXIso.hom`
gives `(trivialLieAlgebraCochainEquiv I M 𝔤 k).symm α.down`. -/
theorem cochainComplexXIso_hom_trivialLieAlgebraCochainComplexIso_inv_f (k : ℕ)
    (α : ULift.{uM, uG} (𝔤 [⋀^Fin k]→ₗ[ℝ] TrivialLieModule ℝ 𝔤 ℝ)) :
    ((trivialLieAlgebra I M 𝔤).cochainComplexXIso k).hom
        ((trivialLieAlgebraCochainComplexIso I M 𝔤).inv.f k α) =
      (trivialLieAlgebraCochainEquiv I M 𝔤 k).symm α.down := by
  rw [trivialLieAlgebraCochainComplexIso_inv_f_apply, Iso.inv_hom_id_apply]

/-- Over a one-point manifold, the `k`-th Lie algebroid cohomology of `trivialLieAlgebra I M 𝔤`
is canonically isomorphic to the universe lift of the `k`-th Lie algebra cohomology of `𝔤` with
trivial coefficients `ℝ`. -/
def trivialLieAlgebraCohomologyIso (k : ℕ) :
    (trivialLieAlgebra I M 𝔤).cohomology k ≅
      (ModuleCat.uliftFunctor.{uM, uG} ℝ).obj
        (TauCeti.LieModule.Cohomology.cohomology ℝ 𝔤 (TrivialLieModule ℝ 𝔤 ℝ) k) :=
  (HomologicalComplex.homologyFunctor _ _ k).mapIso (trivialLieAlgebraCochainComplexIso I M 𝔤) ≪≫
    ((TauCeti.LieModule.Cohomology.cochainComplex ℝ 𝔤 (TrivialLieModule ℝ 𝔤 ℝ)).sc k).mapHomologyIso
      (ModuleCat.uliftFunctor.{uM, uG} ℝ)

end Complex

end TauCeti.LieAlgebroid
