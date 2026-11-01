/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Germ
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.LocalRing

/-!
# Pullback of holomorphic stalks by local analytic functions

`stalkPullback` pulls back holomorphic germs along a function analytic only at the chosen
point. Unlike the sheaf morphism `stalkPrecomp`, this requires no globally holomorphic
extension of the function. Equality, evaluation and composition are characterized through
the injective comparison with function germs. The two pullbacks agree when both apply.
-/

public noncomputable section

open Filter Topology
open scoped Manifold ContDiff

namespace TauCeti.holomorphicStructureSheaf

variable {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a)

private theorem exists_stalkPullback
    (s : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk (f a)) :
    ∃ t, toFilterGerm 𝓘(ℂ) ℂ a (𝓝 a) le_rfl t =
      (toFilterGerm 𝓘(ℂ) ℂ (f a) (𝓝 (f a)) le_rfl s).compTendsto f hf.continuousAt.tendsto := by
  obtain ⟨u, hu, hus⟩ := exists_toFilterGerm_eq (f a) s
  have hua : AnalyticAt ℂ u (f a) :=
    (contMDiffAt_iff_contDiffAt.mp hu.self_of_nhds).analyticAt
  obtain ⟨t, ht⟩ := exists_toFilterGerm_eq_of_eventually_contMDiffAt
    ((hua.comp hf).eventually_analyticAt.mono fun _ hz ↦
      contMDiffAt_iff_contDiffAt.mpr hz.contDiffAt)
  exact ⟨t, by rw [ht, hus, Germ.coe_compTendsto]⟩

/-- Pullback of holomorphic germs by a function analytic at the base point. -/
def stalkPullback :
    (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk (f a) →+*
      (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a where
  toFun s := (exists_stalkPullback hf s).choose
  map_one' := by
    apply toFilterGerm_nhds_injective a
    rw [(exists_stalkPullback hf 1).choose_spec, map_one, map_one]
    rfl
  map_mul' s t := by
    apply toFilterGerm_nhds_injective a
    rw [(exists_stalkPullback hf (s * t)).choose_spec, map_mul, map_mul,
      (exists_stalkPullback hf s).choose_spec, (exists_stalkPullback hf t).choose_spec]
    exact Germ.inductionOn₂ (toFilterGerm 𝓘(ℂ) ℂ (f a) (𝓝 (f a)) le_rfl s)
      (toFilterGerm 𝓘(ℂ) ℂ (f a) (𝓝 (f a)) le_rfl t) fun _ _ ↦ rfl
  map_zero' := by
    apply toFilterGerm_nhds_injective a
    rw [(exists_stalkPullback hf 0).choose_spec, map_zero, map_zero]
    rfl
  map_add' s t := by
    apply toFilterGerm_nhds_injective a
    rw [(exists_stalkPullback hf (s + t)).choose_spec, map_add, map_add,
      (exists_stalkPullback hf s).choose_spec, (exists_stalkPullback hf t).choose_spec]
    exact Germ.inductionOn₂ (toFilterGerm 𝓘(ℂ) ℂ (f a) (𝓝 (f a)) le_rfl s)
      (toFilterGerm 𝓘(ℂ) ℂ (f a) (𝓝 (f a)) le_rfl t) fun _ _ ↦ rfl

/-- The function germ of a pulled-back holomorphic germ is its composition with the map. -/
@[simp]
theorem toFilterGerm_stalkPullback
    (s : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk (f a)) :
    toFilterGerm 𝓘(ℂ) ℂ a (𝓝 a) le_rfl (stalkPullback hf s) =
      (toFilterGerm 𝓘(ℂ) ℂ (f a) (𝓝 (f a)) le_rfl s).compTendsto f hf.continuousAt.tendsto :=
  (exists_stalkPullback hf s).choose_spec

/-- Pullback preserves the value of a holomorphic germ. -/
@[simp]
theorem eval_stalkPullback
    (s : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk (f a)) :
    eval 𝓘(ℂ) ℂ a (stalkPullback hf s) = eval 𝓘(ℂ) ℂ (f a) s := by
  obtain ⟨u, _, hus⟩ := exists_toFilterGerm_eq (f a) s
  have h := toFilterGerm_stalkPullback hf s
  rw [hus, Germ.coe_compTendsto] at h
  exact (eval_eq_of_toFilterGerm_eq h).trans (eval_eq_of_toFilterGerm_eq (hus _ le_rfl)).symm

/-- Local analytic pullback is a local ring homomorphism. -/
instance isLocalHom_stalkPullback : IsLocalHom (stalkPullback hf) where
  map_nonunit s hs := (isUnit_stalk_iff 𝓘(ℂ) ℂ s).mpr (by
    simpa only [eval_stalkPullback] using ((isUnit_stalk_iff 𝓘(ℂ) ℂ _).mp hs))

/-- On globally analytic functions, local pullback is the structure-sheaf stalk map. -/
theorem stalkPullback_eq_stalkPrecomp (f : ℂ → ℂ)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (a : ℂ) :
    stalkPullback (contMDiffAt_iff_contDiffAt.mp hf.contMDiffAt).analyticAt =
      stalkPrecomp 𝓘(ℂ) ℂ f hf a := by
  ext s
  apply toFilterGerm_nhds_injective a
  rw [toFilterGerm_stalkPullback, toFilterGerm_stalkPrecomp]

/-- Pullback by the identity fixes every germ. -/
@[simp]
theorem stalkPullback_id (a : ℂ) :
    stalkPullback (analyticAt_id : AnalyticAt ℂ (id : ℂ → ℂ) a) = RingHom.id _ := by
  rw [stalkPullback_eq_stalkPrecomp id contMDiff_id a, stalkPrecomp_id]

/-- Pullback by a composite is the composite of the pullbacks, in reverse order. -/
theorem stalkPullback_comp {g : ℂ → ℂ} (hg : AnalyticAt ℂ g (f a))
    (s : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk (g (f a))) :
    stalkPullback (hg.comp hf) s = stalkPullback hf (stalkPullback hg s) := by
  apply toFilterGerm_nhds_injective a
  simp only [toFilterGerm_stalkPullback]
  exact Germ.inductionOn
    (toFilterGerm 𝓘(ℂ) ℂ (g (f a)) (𝓝 (g (f a))) le_rfl s) fun _ ↦ rfl

end TauCeti.holomorphicStructureSheaf
