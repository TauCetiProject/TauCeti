/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.LieAlgebroid.ChevalleyEilenberg
public import TauCeti.Geometry.Manifold.LieAlgebroid.Tangent
import TauCeti.Geometry.Manifold.DifferentialForm.VectorField

/-!
# Comparison of the tangent Lie algebroid complex and the de Rham complex

Specializing the Chevalley–Eilenberg complex (`TauCeti.LieAlgebroid.cochainComplex`) of a Lie
algebroid to the tangent Lie algebroid `TauCeti.LieAlgebroid.tangent I M` recovers the de Rham
complex `TauCeti.deRhamComplex I M` of smooth real-valued differential forms:

* `TauCeti.LieAlgebroid.tangent_extDeriv_toContMDiffSection`: under `SmoothForm.toContMDiffSection`,
  the algebroid exterior derivative `(tangent I M).extDeriv k` coincides with `mextDerivₗ I k`;
* `TauCeti.LieAlgebroid.tangentCochainComplexIso`: canonical isomorphism of cochain complexes
  `(tangent I M).cochainComplex ≅ deRhamComplex I M` built from
  `SmoothBundleForm.toContMDiffSectionEquiv`;
* `TauCeti.LieAlgebroid.tangentCohomologyIso`: induced isomorphism between Lie algebroid
  cohomology `(tangent I M).cohomology k` and de Rham cohomology `(deRhamComplex I M).homology k`.

## References

* K. C. H. Mackenzie, *General theory of Lie groupoids and Lie algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), §7.1.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer (2013), Chapter 17.
-/

public section

noncomputable section

open Bundle CategoryTheory Manifold VectorField
open scoped ContDiff

namespace TauCeti.LieAlgebroid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-- On the tangent Lie algebroid `TauCeti.LieAlgebroid.tangent I M`, the algebroid exterior
derivative `extDeriv` coincides with the manifold exterior derivative `TauCeti.mextDerivₗ` via
`SmoothForm.toContMDiffSection`. -/
theorem tangent_extDeriv_toContMDiffSection (k : ℕ) (φ : SmoothForm I M ℝ k) :
    (tangent I M).extDeriv k (SmoothForm.toContMDiffSection φ) =
      SmoothForm.toContMDiffSection (mextDerivₗ I k φ) := by
  refine ContMDiffSection.eq_of_evalAlternating_eq <| AlternatingMap.ext fun s ↦ ?_
  ext x
  cases k with
  | zero =>
    have hs : (fun i : Fin 1 ↦ s i x) = ![s 0 x] := funext fun i ↦ by fin_cases i; rfl
    have hφ0 : ⇑((SmoothForm.toContMDiffSection φ).evalAlternating ![]) = fun y ↦ φ.val y 0 := by
      ext y; rw [ContMDiffSection.evalAlternating_apply, SmoothForm.toContMDiffSection_apply]
      exact congrArg (φ.val y) (Subsingleton.elim _ _)
    rw [evalAlternating_extDeriv_zero, anchorDeriv_apply, tangent_anchor_apply, hφ0,
      ContMDiffSection.evalAlternating_apply, SmoothForm.toContMDiffSection_apply, hs,
      mextDerivₗ_zero_apply]
  | succ n =>
    have hV (i : Fin (n + 2)) :
        MDifferentiableAt I I.tangent (fun y ↦ (s i y : TangentBundle I M)) x :=
      (s i).contMDiff.mdifferentiableAt (by simp)
    have heval (i : Fin (n + 2)) :
        ⇑((SmoothForm.toContMDiffSection φ).evalAlternating (i.removeNth s)) =
          fun y ↦ φ.val y (i.removeNth (fun r ↦ s r y)) := by
      ext y; rw [ContMDiffSection.evalAlternating_apply, SmoothForm.toContMDiffSection_apply]
      congr 1
    have hcons (i j : Fin (n + 1)) :
        (fun r ↦
          Matrix.vecCons ((tangent I M).bracket (s i.castSucc) (s j.succ))
            (j.removeNth (i.castSucc.removeNth s)) r x) =
          Matrix.vecCons (mlieBracket I (s i.castSucc) (s j.succ) x)
            (j.removeNth (i.castSucc.removeNth (fun r ↦ s r x))) := by
      funext r; exact Fin.cases (by simp) (fun _ ↦ by simp [Fin.removeNth]) r
    rw [← ContMDiffMap.evalAlgHom_apply ℝ x, evalAlternating_extDeriv_succ,
      ContMDiffSection.evalAlternating_apply, SmoothForm.toContMDiffSection_apply,
      mextDerivₗ_apply, SmoothForm.mextDeriv_apply_vectorField hV]
    simp only [map_add, map_sum, map_zsmul, ContMDiffMap.evalAlgHom_apply]
    simp only [anchorDeriv_apply, tangent_anchor_apply, heval,
      ContMDiffSection.evalAlternating_apply, SmoothForm.toContMDiffSection_apply, hcons,
      zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, pow_succ (-1 : ℝ), mul_neg_one,
      neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg]

variable (I M) in
/-- The Chevalley–Eilenberg cochain complex of the tangent Lie algebroid `tangent I M` is
canonically isomorphic to the de Rham complex `deRhamComplex I M`, via
`SmoothBundleForm.toContMDiffSectionEquiv`. -/
def tangentCochainComplexIso : (tangent I M).cochainComplex ≅ deRhamComplex I M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun k ↦ (tangent I M).cochainComplexXIso k ≪≫
      (SmoothBundleForm.toContMDiffSectionEquiv I ℝ (Bundle.Trivial M ℝ) k).symm.toModuleIso ≪≫
      (deRhamComplexXIso I k).symm) <| by
    rintro k _ rfl
    have hcomm :
        (SmoothBundleForm.toContMDiffSectionEquiv I ℝ
              (Bundle.Trivial M ℝ) k).symm.toModuleIso.hom ≫
            ModuleCat.ofHom (mextDerivₗ I (F := ℝ) k) =
          ModuleCat.ofHom ((tangent I M).extDeriv k) ≫
            (SmoothBundleForm.toContMDiffSectionEquiv I ℝ
              (Bundle.Trivial M ℝ) (k + 1)).symm.toModuleIso.hom := by
      ext s : 2
      apply SmoothForm.toContMDiffSection_injective
      simp only [ModuleCat.hom_comp, LinearEquiv.toModuleIso_hom, LinearMap.comp_apply,
        ModuleCat.hom_ofHom, LinearEquiv.coe_coe, SmoothForm.toContMDiffSectionEquiv_symm_apply]
      rw [← tangent_extDeriv_toContMDiffSection, SmoothForm.toContMDiffSection_ofContMDiffSection,
        SmoothForm.toContMDiffSection_ofContMDiffSection]
    rw [(Iso.eq_comp_inv _).mpr (deRhamComplex_d I (M := M) k),
      (Iso.eq_comp_inv _).mpr ((tangent I M).cochainComplex_d_succ k)]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hcomm]

/-- On degree-`k` components read through `cochainComplexXIso` and `deRhamComplexXIso`, the
forward isomorphism `(tangentCochainComplexIso I M).hom.f k` is `SmoothForm.ofContMDiffSection`. -/
@[simp]
theorem deRhamComplexXIso_hom_tangentCochainComplexIso_hom_f (k : ℕ)
    (x : (tangent I M).cochainComplex.X k) :
    (deRhamComplexXIso I k).hom ((tangentCochainComplexIso I M).hom.f k x) =
      SmoothForm.ofContMDiffSection (((tangent I M).cochainComplexXIso k).hom x) := by
  simp [tangentCochainComplexIso, -SmoothBundleForm.toContMDiffSectionEquiv_symm_apply,
    SmoothForm.toContMDiffSectionEquiv_symm_apply]

/-- On degree-`k` components read through `deRhamComplexXIso` and `cochainComplexXIso`, the
inverse isomorphism `(tangentCochainComplexIso I M).inv.f k` is `SmoothForm.toContMDiffSection`. -/
@[simp]
theorem cochainComplexXIso_hom_tangentCochainComplexIso_inv_f (k : ℕ)
    (x : (deRhamComplex I M).X k) :
    ((tangent I M).cochainComplexXIso k).hom ((tangentCochainComplexIso I M).inv.f k x) =
      SmoothForm.toContMDiffSection ((deRhamComplexXIso I k).hom x) := by
  simp [tangentCochainComplexIso, -SmoothBundleForm.toContMDiffSectionEquiv_apply,
    SmoothForm.toContMDiffSectionEquiv_apply]

/-- Evaluating `(tangentCochainComplexIso I M).hom.f k` on a section inserted via
`cochainComplexXIso` yields `SmoothForm.ofContMDiffSection` inserted via `deRhamComplexXIso`. -/
@[simp]
theorem tangentCochainComplexIso_hom_f_inv_apply (k : ℕ)
    (s : Cₛ^∞⟮I; E [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ⟯) :
    (tangentCochainComplexIso I M).hom.f k (((tangent I M).cochainComplexXIso k).inv s) =
      (deRhamComplexXIso I k).inv (SmoothForm.ofContMDiffSection s) := by
  simp [tangentCochainComplexIso, -SmoothBundleForm.toContMDiffSectionEquiv_symm_apply,
    SmoothForm.toContMDiffSectionEquiv_symm_apply]

/-- Evaluating `(tangentCochainComplexIso I M).inv.f k` on a smooth form inserted via
`deRhamComplexXIso` yields `SmoothForm.toContMDiffSection` inserted via `cochainComplexXIso`. -/
@[simp]
theorem tangentCochainComplexIso_inv_f_inv_apply (k : ℕ) (φ : SmoothForm I M ℝ k) :
    (tangentCochainComplexIso I M).inv.f k ((deRhamComplexXIso I k).inv φ) =
      ((tangent I M).cochainComplexXIso k).inv (SmoothForm.toContMDiffSection φ) := by
  simp [tangentCochainComplexIso, -SmoothBundleForm.toContMDiffSectionEquiv_apply,
    SmoothForm.toContMDiffSectionEquiv_apply]

variable (I M) in
/-- The `k`-th Chevalley–Eilenberg cohomology of the tangent Lie algebroid `tangent I M` is
canonically isomorphic to the `k`-th de Rham cohomology of `M`. -/
def tangentCohomologyIso (k : ℕ) :
    (tangent I M).cohomology k ≅ (deRhamComplex I M).homology k :=
  (HomologicalComplex.homologyFunctor _ _ k).mapIso (tangentCochainComplexIso I M)

end TauCeti.LieAlgebroid
