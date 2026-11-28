/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorPower.BaseChange
public import TauCeti.NumberTheory.NumberField.HermitianBundle.BaseChange
public import TauCeti.NumberTheory.NumberField.HermitianBundle.ExteriorPower

/-!
# Base change of hermitian determinants

`TauCeti.HermitianMetric.exteriorPowerBaseChangeIso` upgrades the scalar-extension comparison
`TauCeti.exteriorPower.equivBaseChange` to an isometry for the Gram-determinant metrics, using
`TauCeti.HermitianMetric.exteriorPower_form_tmul_ιMulti`.
In particular, `TauCeti.HermitianBundle.detBaseChangeIso` identifies the base change of a
determinant with the determinant of the base-changed bundle, including the metrics.

See Bost, *Périodes et isogénies des variétés abéliennes sur les corps des nombres*,
Séminaire Bourbaki 795, Appendice A.2–A.3.
-/

public noncomputable section

open scoped TensorProduct
open NumberField NumberField.ComplexEmbedding

namespace TauCeti.HermitianMetric

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]

/-- Extension of scalars commutes isometrically with exterior powers. The underlying
equivalence is the canonical exterior-power comparison for scalar extension. -/
def exteriorPowerBaseChangeIso [Module.Finite (𝓞 K) E] (h : HermitianMetric K E) (n : ℕ) :
    IsometryEquiv ((h.exteriorPower n).baseChange (L := L)) (h.baseChange.exteriorPower n) where
  toLinearEquiv := (TauCeti.exteriorPower.equivBaseChange (𝓞 L) n (R := 𝓞 K) (M := E)).symm
  form_tmul τ x y := by
    let W := ⋀[𝓞 K]^n E
    let v (a : Fin n → E) : Codomain τ ⊗[𝓞 L] (𝓞 L ⊗[𝓞 K] W) :=
      1 ⊗ₜ ((1 : 𝓞 L) ⊗ₜ exteriorPower.ιMulti (𝓞 K) n a)
    have hspan : Submodule.span ℂ (Set.range v) = ⊤ := by
      let w (a : Fin n → E) : 𝓞 L ⊗[𝓞 K] W :=
        1 ⊗ₜ exteriorPower.ιMulti (𝓞 K) n a
      have hw : Submodule.span (𝓞 L) (Set.range w) = ⊤ := by
        have hs := congrArg (Submodule.baseChange (𝓞 L)) (exteriorPower.ιMulti_span (𝓞 K) n E)
        simpa only [Submodule.baseChange_span, Submodule.baseChange_top, ← Set.range_comp,
          Function.comp_def, TensorProduct.mk_apply] using hs
      have hs := congrArg (Submodule.baseChange (Codomain τ)) hw
      have hv : Submodule.span (Codomain τ) (Set.range v) = ⊤ := by
        simpa only [Submodule.baseChange_span, Submodule.baseChange_top, ← Set.range_comp,
          Function.comp_def, TensorProduct.mk_apply] using hs
      -- `Codomain τ` and `ℂ` act on the fibre by the same scalar action.
      exact hv
    let e := (TauCeti.exteriorPower.equivBaseChange (𝓞 L) n (R := 𝓞 K) (M := E)).symm
    let f := (e.toLinearMap.baseChange (Codomain τ)).restrictScalars ℂ
    have he (a : Fin n → E) :
        e ((1 : 𝓞 L) ⊗ₜ exteriorPower.ιMulti (𝓞 K) n a) =
          exteriorPower.ιMulti (𝓞 L) n (fun i ↦ (1 : 𝓞 L) ⊗ₜ a i) :=
      (TauCeti.exteriorPower.equivBaseChange_symm_tmul_ιMulti (𝓞 L) 1 a).trans (one_smul _ _)
    have hform : (((h.baseChange.exteriorPower n).form τ).comp f).compl₂ f =
        ((h.exteriorPower n).baseChange (L := L)).form τ := by
      apply LinearMap.ext_on_range hspan
      intro a
      apply LinearMap.ext_on_range hspan
      intro b
      simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, v, f,
        LinearMap.restrictScalars_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe, he,
        exteriorPower_form_tmul_ιMulti, baseChange_form_tmul_tmul, map_one, one_mul]
    have hxy := DFunLike.congr_fun (DFunLike.congr_fun hform (1 ⊗ₜ x)) (1 ⊗ₜ y)
    simpa only [f, e, LinearMap.compl₂_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearMap.baseChange_tmul, LinearEquiv.coe_coe] using hxy

/-- The underlying linear equivalence is the scalar-extension comparison for exterior powers. -/
@[simp]
theorem toLinearEquiv_exteriorPowerBaseChangeIso [Module.Finite (𝓞 K) E]
    (h : HermitianMetric K E) (n : ℕ) :
    (h.exteriorPowerBaseChangeIso (L := L) n).toLinearEquiv =
      (TauCeti.exteriorPower.equivBaseChange (𝓞 L) n (R := 𝓞 K) (M := E)).symm :=
  (rfl)

/-- The exterior-power isometry sends a tensor of a wedge to the scaled wedge of the images. -/
@[simp]
theorem exteriorPowerBaseChangeIso_tmul_ιMulti [Module.Finite (𝓞 K) E]
    (h : HermitianMetric K E) (n : ℕ) (a : 𝓞 L) (x : Fin n → E) :
    h.exteriorPowerBaseChangeIso n (a ⊗ₜ exteriorPower.ιMulti (𝓞 K) n x) =
      a • exteriorPower.ιMulti (𝓞 L) n (fun i ↦ (1 : 𝓞 L) ⊗ₜ x i) :=
  TauCeti.exteriorPower.equivBaseChange_symm_tmul_ιMulti (𝓞 L) a x

end TauCeti.HermitianMetric

namespace TauCeti.HermitianBundle

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The determinant of a hermitian vector bundle commutes isometrically with base change.
The comparison is the scalar-extension equivalence in top degree, reindexed by rank
invariance. -/
def detBaseChangeIso (E : HermitianBundle K) :
    HermitianMetric.IsometryEquiv (E.det.baseChange (L := L)).metric
      (E.baseChange.det).metric where
  toLinearEquiv :=
    (E.metric.exteriorPowerBaseChangeIso (L := L) E.rank).toLinearEquiv.trans <|
      LinearEquiv.ofEq _ _ (congrArg (⋀[𝓞 L]^· (𝓞 L ⊗[𝓞 K] E))
        (E.rank_baseChange (L := L)).symm)
  form_tmul τ x y := by
    have form_ofEq (m : ℕ) (hm : E.rank = m)
        (u v : ⋀[𝓞 L]^E.rank (𝓞 L ⊗[𝓞 K] E)) :
        ((E.metric.baseChange (L := L)).exteriorPower m).form τ
          (1 ⊗ₜ LinearEquiv.ofEq _ _
            (congrArg (⋀[𝓞 L]^· (𝓞 L ⊗[𝓞 K] E)) hm) u)
          (1 ⊗ₜ LinearEquiv.ofEq _ _
            (congrArg (⋀[𝓞 L]^· (𝓞 L ⊗[𝓞 K] E)) hm) v) =
        (E.metric.baseChange.exteriorPower E.rank).form τ (1 ⊗ₜ u) (1 ⊗ₜ v) := by
      subst m
      rfl
    let e := E.metric.exteriorPowerBaseChangeIso (L := L) E.rank
    have hform := (form_ofEq _ (E.rank_baseChange (L := L)).symm (e x) (e y)).trans
      (e.form_tmul τ x y)
    exact hform

/-- The underlying determinant comparison is the exterior-power comparison
in top degree, reindexed by rank invariance. -/
theorem toLinearEquiv_detBaseChangeIso (E : HermitianBundle K) :
    (E.detBaseChangeIso (L := L)).toLinearEquiv =
      (E.metric.exteriorPowerBaseChangeIso (L := L) E.rank).toLinearEquiv.trans
        (LinearEquiv.ofEq _ _ (congrArg (⋀[𝓞 L]^· (𝓞 L ⊗[𝓞 K] E))
          (E.rank_baseChange (L := L)).symm)) :=
  (rfl)

/-- On a tensor of a top wedge, the determinant isometry wedges the base-changed vectors in
the same order. -/
@[simp]
theorem detBaseChangeIso_tmul_ιMulti (E : HermitianBundle K) (a : 𝓞 L) (x : Fin E.rank → E) :
    E.detBaseChangeIso (a ⊗ₜ exteriorPower.ιMulti (𝓞 K) E.rank x) =
      a • exteriorPower.ιMulti (𝓞 L) (E.baseChange (L := L)).rank
        (fun i ↦ (1 : 𝓞 L) ⊗ₜ x (Fin.cast (E.rank_baseChange (L := L)) i)) := by
  have happly :
      E.detBaseChangeIso (a ⊗ₜ exteriorPower.ιMulti (𝓞 K) E.rank x) =
        LinearEquiv.ofEq _ _ (congrArg (⋀[𝓞 L]^· (𝓞 L ⊗[𝓞 K] E))
          (E.rank_baseChange (L := L)).symm)
          (E.metric.exteriorPowerBaseChangeIso E.rank
            (a ⊗ₜ exteriorPower.ιMulti (𝓞 K) E.rank x)) :=
    DFunLike.congr_fun (E.toLinearEquiv_detBaseChangeIso (L := L)) _
  refine happly.trans ?_
  rw [HermitianMetric.exteriorPowerBaseChangeIso_tmul_ιMulti, map_smul,
    exteriorPower.ofEq_ιMulti (E.rank_baseChange (L := L)).symm]
  rfl

end TauCeti.HermitianBundle
