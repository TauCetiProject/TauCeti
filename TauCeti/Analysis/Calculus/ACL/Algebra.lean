/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ACL.Basic

/-!
# Operations on `ACL` maps

Let `Ω ⊆ ℝⁿ` and let `F`, `F'` be normed groups. The class of maps `u : ℝⁿ → F` that are `ACL` on
`Ω` (`TauCeti.IsACLOn`) is stable under the pointwise operations, since the line function of a
combination is the combination of the line functions (`TauCeti.lineFunction_add`, ...) and
absolute continuity on an interval is stable under them:

* sums, negatives and differences (`TauCeti.IsACLOn.add`, `TauCeti.IsACLOn.neg`,
  `TauCeti.IsACLOn.sub`), and finite sums (`TauCeti.IsACLOn.sum`);
* multiplication by a constant scalar (`TauCeti.IsACLOn.const_smul`), and by a scalar `ACL` map
  (`TauCeti.IsACLOn.smul`), with scalars in a normed ring; hence linear combinations;
* composition with maps `F → F'` Lipschitz on a set containing `u '' Ω`
  (`LipschitzOnWith.comp_isACLOn`) or Lipschitz everywhere (`LipschitzWith.comp_isACLOn`), in
  particular with continuous (semi)linear maps (`ContinuousLinearMap.comp_isACLOn`) and
  isometries.

Constant maps, in particular the zero map, are `ACL` on every set (`TauCeti.isACLOn_const`,
`TauCeti.isACLOn_zero`).
-/

public section

open MeasureTheory Set Filter
open scoped NNReal

noncomputable section

namespace TauCeti

variable {n : ℕ} {F F' : Type*} [NormedAddCommGroup F] [NormedAddCommGroup F']
  {u v : EuclideanSpace ℝ (Fin n) → F} {Ω : Set (EuclideanSpace ℝ (Fin n))}

/-- Constant maps are `ACL` on every set. -/
theorem isACLOn_const (c : F) : IsACLOn (fun _ : EuclideanSpace ℝ (Fin n) ↦ c) Ω :=
  (LocallyLipschitz.const c).locallyLipschitzOn.isACLOn

/-- The zero map is `ACL` on every set. -/
theorem isACLOn_zero : IsACLOn (0 : EuclideanSpace ℝ (Fin n) → F) Ω :=
  isACLOn_const 0

/-- The sum of two maps `ACL` on `Ω` is `ACL` on `Ω`. -/
theorem IsACLOn.add (hu : IsACLOn u Ω) (hv : IsACLOn v Ω) : IsACLOn (u + v) Ω where
  continuousOn := hu.continuousOn.add hv.continuousOn
  ae_absolutelyContinuousOnInterval a b hab hQ i := by
    filter_upwards [hu.ae_absolutelyContinuousOnInterval a b hab hQ i,
      hv.ae_absolutelyContinuousOnInterval a b hab hQ i] with x hux hvx
    rw [lineFunction_add]
    exact hux.add hvx

/-- The negative of a map `ACL` on `Ω` is `ACL` on `Ω`. -/
theorem IsACLOn.neg (hu : IsACLOn u Ω) : IsACLOn (-u) Ω where
  continuousOn := hu.continuousOn.neg
  ae_absolutelyContinuousOnInterval a b hab hQ i := by
    filter_upwards [hu.ae_absolutelyContinuousOnInterval a b hab hQ i] with x hux
    rw [lineFunction_neg]
    exact hux.neg

/-- The difference of two maps `ACL` on `Ω` is `ACL` on `Ω`. -/
theorem IsACLOn.sub (hu : IsACLOn u Ω) (hv : IsACLOn v Ω) : IsACLOn (u - v) Ω := by
  simpa [sub_eq_add_neg] using hu.add hv.neg

/-- A finite sum of maps `ACL` on `Ω` is `ACL` on `Ω`. -/
theorem IsACLOn.sum {ι : Type*} {s : Finset ι} {w : ι → EuclideanSpace ℝ (Fin n) → F}
    (hw : ∀ k ∈ s, IsACLOn (w k) Ω) : IsACLOn (∑ k ∈ s, w k) Ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isACLOn_zero
  | insert k s hk ih =>
    rw [Finset.sum_insert hk]
    exact (hw k (Finset.mem_insert_self k s)).add
      (ih fun j hj ↦ hw j (Finset.mem_insert_of_mem hj))

/-- A constant multiple of a map `ACL` on `Ω` is `ACL` on `Ω`. -/
theorem IsACLOn.const_smul {M : Type*} [SeminormedRing M] [Module M F] [NormSMulClass M F]
    (hu : IsACLOn u Ω) (c : M) : IsACLOn (c • u) Ω where
  continuousOn := hu.continuousOn.const_smul c
  ae_absolutelyContinuousOnInterval a b hab hQ i := by
    filter_upwards [hu.ae_absolutelyContinuousOnInterval a b hab hQ i] with x hux
    rw [lineFunction_const_smul]
    exact hux.const_smul c

/-- The product of a scalar map `ACL` on `Ω` and a map `ACL` on `Ω` is `ACL` on `Ω`. -/
theorem IsACLOn.smul {M : Type*} [NormedRing M] [Module M F] [NormSMulClass M F]
    {g : EuclideanSpace ℝ (Fin n) → M} (hg : IsACLOn g Ω) (hu : IsACLOn u Ω) :
    IsACLOn (g • u) Ω where
  continuousOn := hg.continuousOn.smul hu.continuousOn
  ae_absolutelyContinuousOnInterval a b hab hQ i := by
    filter_upwards [hg.ae_absolutelyContinuousOnInterval a b hab hQ i,
      hu.ae_absolutelyContinuousOnInterval a b hab hQ i] with x hgx hux
    rw [lineFunction_smul]
    exact hgx.smul hux

/-- The composition of a map `ACL` on `Ω` with a map Lipschitz on a set containing `u '' Ω` is
`ACL` on `Ω`. -/
theorem _root_.LipschitzOnWith.comp_isACLOn {L : F → F'} {K : ℝ≥0} {t : Set F}
    (hL : LipschitzOnWith K L t) (hut : MapsTo u Ω t) (hu : IsACLOn u Ω) :
    IsACLOn (L ∘ u) Ω where
  continuousOn := hL.continuousOn.comp hu.continuousOn hut
  ae_absolutelyContinuousOnInterval a b hab hQ i := by
    filter_upwards [hu.ae_absolutelyContinuousOnInterval a b hab hQ i,
      ae_restrict_mem (measurableSet_coordinateBox a b)] with x hux hx
    rw [lineFunction_comp]
    refine hL.comp_absolutelyContinuousOnInterval (fun s hs ↦ ?_) hux
    rw [uIcc_of_le (hab i).le] at hs
    rw [lineFunction_apply]
    exact hut (hQ (add_sub_smul_single_mem_coordinateBox hx hs))

/-- The composition of a map `ACL` on `Ω` with a Lipschitz map is `ACL` on `Ω`. -/
theorem _root_.LipschitzWith.comp_isACLOn {L : F → F'} {K : ℝ≥0} (hL : LipschitzWith K L)
    (hu : IsACLOn u Ω) : IsACLOn (L ∘ u) Ω :=
  hL.lipschitzOnWith.comp_isACLOn (mapsTo_univ u Ω) hu

/-- The composition of a map `ACL` on `Ω` with a continuous semilinear map is `ACL` on `Ω`. -/
theorem _root_.ContinuousLinearMap.comp_isACLOn {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜'] {σ : 𝕜 →+* 𝕜'} [RingHomIsometric σ] [NormedSpace 𝕜 F]
    [NormedSpace 𝕜' F'] (L : F →SL[σ] F') (hu : IsACLOn u Ω) :
    IsACLOn (L ∘ u) Ω :=
  L.lipschitzWith.comp_isACLOn hu

end TauCeti
