/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.BaseChange
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Naturality

/-!
# Descent of normal closed subgroups

Normality of a closed subgroup can be checked after extending the ground field. The
pointwise criterion for normality is reflected by the injective map from any value algebra
into its scalar extension. This permits descent of the normality condition in the
construction of solvable radicals.
-/

public section

open WithConv
open scoped TensorProduct

namespace TauCeti.CommHopfAlgCat

universe u v w

variable {k : Type u} {K : Type w} [Field k] [Field K] [Algebra k K]
variable {H : _root_.CommHopfAlgCat.{v} k}

/-- Normality of a closed subgroup is reflected by extension of the ground field. -/
theorem isNormal_of_baseChangeHopfIdeal {I : HopfIdeal k H}
    (hI : (baseChangeHopfIdeal (K := K) I).IsNormal) : I.IsNormal := by
  rw [isNormal_iff_quotientPointsSubgroup_normal]
  intro A
  refine ⟨fun n hn g ↦ ?_⟩
  let B := K ⊗[k] A
  let j : A →ₐ[k] B := Algebra.TensorProduct.includeRight
  let _ : Algebra K B := Algebra.TensorProduct.leftAlgebra
  let _ : IsScalarTower k K B := inferInstance
  let e := AlgHom.baseChangePointsMulEquiv (k := k) (K := K) (A := H) (R := B)
  have hn' : e (AlgHom.mapValue j n) ∈
      quotientPointsSubgroup (baseChange (K := K) H)
        (baseChangeHopfIdeal (K := K) I) (CommAlgCat.of K B) :=
    (mem_quotientPointsSubgroup_iff_baseChangePointsMulEquiv_mem I _).mp
      (mapValue_mem_quotientPointsSubgroup H I j hn)
  have hconj : e (AlgHom.mapValue j (g * n * g⁻¹)) ∈
      quotientPointsSubgroup (baseChange (K := K) H)
        (baseChangeHopfIdeal (K := K) I) (CommAlgCat.of K B) := by
    simpa only [map_mul, map_inv] using
      (quotientPointsSubgroup_normal _ _ hI (CommAlgCat.of K B)).conj_mem
        _ hn' (e (AlgHom.mapValue j g))
  have hmap :=
    (mem_quotientPointsSubgroup_iff_baseChangePointsMulEquiv_mem I _).mpr hconj
  rw [mem_quotientPointsSubgroup_iff] at hmap ⊢
  intro x hx
  have hinj : Function.Injective j :=
    Algebra.TensorProduct.includeRight_injective (algebraMap k K).injective
  have hz : j ((g * n * g⁻¹).ofConv x) = 0 := by
    simpa only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply] using hmap x hx
  exact hinj (hz.trans (map_zero j).symm)

/-- A closed subgroup is normal exactly when its base change to a field extension is normal. -/
@[simp]
theorem isNormal_baseChangeHopfIdeal_iff (I : HopfIdeal k H) :
    (baseChangeHopfIdeal (K := K) I).IsNormal ↔ I.IsNormal :=
  ⟨isNormal_of_baseChangeHopfIdeal, isNormal_baseChangeHopfIdeal⟩

end TauCeti.CommHopfAlgCat
