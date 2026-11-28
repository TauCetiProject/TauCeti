/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.HermitianBundle.ExteriorPower

/-!
# Base change of hermitian determinants

`TauCeti.HermitianBundle.detBaseChangeIso` identifies the base change of a determinant with
the determinant of the base-changed bundle, including the metrics. It specializes
`TauCeti.HermitianMetric.exteriorPowerBaseChangeIso` to top degree and uses rank invariance to
reindex the target. The formula `TauCeti.HermitianBundle.detBaseChangeIso_tmul_ιMulti` computes
this isometry on decomposable wedges.

See Bost, *Périodes et isogénies des variétés abéliennes sur les corps des nombres*,
Séminaire Bourbaki 795, Appendice A.2–A.3.
-/

public noncomputable section

open scoped TensorProduct
open NumberField NumberField.ComplexEmbedding

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
@[simp]
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
