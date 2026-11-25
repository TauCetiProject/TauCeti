/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ACL.Basic

/-!
# Operations on `ACL` maps

Let `Ω ⊆ ℝⁿ` and let `F`, `F'` be real normed spaces. The class of maps `u : ℝⁿ → F` that are
`ACL` on `Ω` (`TauCeti.IsACLOn`) is stable under the pointwise operations, since the line function
of a combination is the combination of the line functions and absolute continuity on an interval
is stable under them:

* sums, negatives and differences (`TauCeti.IsACLOn.add`, `TauCeti.IsACLOn.neg`,
  `TauCeti.IsACLOn.sub`), and finite sums (`TauCeti.IsACLOn.sum`);
* multiplication by a constant scalar (`TauCeti.IsACLOn.const_smul`), and by a scalar `ACL` map
  (`TauCeti.IsACLOn.smul`); hence linear combinations;
* composition with Lipschitz maps `F → F'` (`LipschitzWith.comp_isACLOn`), in particular with
  continuous linear maps (`ContinuousLinearMap.comp_isACLOn`) and isometries.

Constant maps are `ACL` on every set (`TauCeti.isACLOn_const`).
-/

public section

open MeasureTheory Set Filter
open scoped NNReal

noncomputable section

namespace TauCeti

variable {n : ℕ} {F F' : Type*} [NormedAddCommGroup F] [NormedAddCommGroup F']
  {u v : EuclideanSpace ℝ (Fin n) → F} {Ω : Set (EuclideanSpace ℝ (Fin n))}

/-- Constant maps are `ACL` on every set. -/
theorem isACLOn_const (c : F) : IsACLOn (fun _ : EuclideanSpace ℝ (Fin n) ↦ c) Ω where
  continuousOn := continuousOn_const
  ae_absolutelyContinuousOnInterval a b _ _ i :=
    .of_forall fun x ↦ by
      convert (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval using 1
      funext t
      simp [lineFunction_apply]

/-- The sum of two maps `ACL` on `Ω` is `ACL` on `Ω`. -/
theorem IsACLOn.add (hu : IsACLOn u Ω) (hv : IsACLOn v Ω) : IsACLOn (u + v) Ω where
  continuousOn := hu.continuousOn.add hv.continuousOn
  ae_absolutelyContinuousOnInterval a b hab hQ i := by
    filter_upwards [hu.ae_absolutelyContinuousOnInterval a b hab hQ i,
      hv.ae_absolutelyContinuousOnInterval a b hab hQ i] with x hux hvx
    convert hux.add hvx using 1
    funext t
    simp [lineFunction_apply]

/-- The negative of a map `ACL` on `Ω` is `ACL` on `Ω`. -/
theorem IsACLOn.neg (hu : IsACLOn u Ω) : IsACLOn (-u) Ω where
  continuousOn := hu.continuousOn.neg
  ae_absolutelyContinuousOnInterval a b hab hQ i := by
    filter_upwards [hu.ae_absolutelyContinuousOnInterval a b hab hQ i] with x hux
    convert hux.neg using 1
    funext t
    simp [lineFunction_apply]

/-- The difference of two maps `ACL` on `Ω` is `ACL` on `Ω`. -/
theorem IsACLOn.sub (hu : IsACLOn u Ω) (hv : IsACLOn v Ω) : IsACLOn (u - v) Ω := by
  simpa [sub_eq_add_neg] using hu.add hv.neg

/-- A finite sum of maps `ACL` on `Ω` is `ACL` on `Ω`. -/
theorem IsACLOn.sum {ι : Type*} {s : Finset ι} {w : ι → EuclideanSpace ℝ (Fin n) → F}
    (hw : ∀ k ∈ s, IsACLOn (w k) Ω) : IsACLOn (∑ k ∈ s, w k) Ω := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Finset.sum_empty (f := w) ▸ isACLOn_const (0 : F)
  | insert k s hk ih =>
    rw [Finset.sum_insert hk]
    exact (hw k (Finset.mem_insert_self k s)).add
      (ih fun j hj ↦ hw j (Finset.mem_insert_of_mem hj))

/-- A constant multiple of a map `ACL` on `Ω` is `ACL` on `Ω`. -/
theorem IsACLOn.const_smul [NormedSpace ℝ F] (hu : IsACLOn u Ω) (c : ℝ) : IsACLOn (c • u) Ω where
  continuousOn := hu.continuousOn.const_smul c
  ae_absolutelyContinuousOnInterval a b hab hQ i := by
    filter_upwards [hu.ae_absolutelyContinuousOnInterval a b hab hQ i] with x hux
    convert hux.const_smul c using 1
    funext t
    simp [lineFunction_apply]

/-- The product of a scalar map `ACL` on `Ω` and a map `ACL` on `Ω` is `ACL` on `Ω`. -/
theorem IsACLOn.smul [NormedSpace ℝ F] {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : IsACLOn g Ω)
    (hu : IsACLOn u Ω) :
    IsACLOn (g • u) Ω where
  continuousOn := hg.continuousOn.smul hu.continuousOn
  ae_absolutelyContinuousOnInterval a b hab hQ i := by
    filter_upwards [hg.ae_absolutelyContinuousOnInterval a b hab hQ i,
      hu.ae_absolutelyContinuousOnInterval a b hab hQ i] with x hgx hux
    convert hgx.smul hux using 1
    funext t
    simp [lineFunction_apply]

/-- The composition of a map `ACL` on `Ω` with a Lipschitz map is `ACL` on `Ω`. -/
theorem _root_.LipschitzWith.comp_isACLOn {L : F → F'} {K : ℝ≥0} (hL : LipschitzWith K L)
    (hu : IsACLOn u Ω) : IsACLOn (L ∘ u) Ω where
  continuousOn := hL.continuous.comp_continuousOn hu.continuousOn
  ae_absolutelyContinuousOnInterval a b hab hQ i := by
    filter_upwards [hu.ae_absolutelyContinuousOnInterval a b hab hQ i] with x hux
    convert hL.comp_absolutelyContinuousOnInterval hux using 1
    funext t
    simp [lineFunction_apply]

/-- The composition of a map `ACL` on `Ω` with a continuous linear map is `ACL` on `Ω`. -/
theorem _root_.ContinuousLinearMap.comp_isACLOn [NormedSpace ℝ F] [NormedSpace ℝ F']
    (L : F →L[ℝ] F') (hu : IsACLOn u Ω) :
    IsACLOn (L ∘ u) Ω :=
  L.lipschitzWith.comp_isACLOn hu

end TauCeti
