/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Topology.Algebra.ContinuousMonoidHom

public import Mathlib.Order.DirectedInverseSystem
public import TauCeti.Topology.Algebra.Group.Profinite.EmbeddingProblem.Level

/-!
# Transition maps between finite solutions

Solutions at a finer quotient restrict to solutions at a coarser quotient.
If `G` solves finite embedding problems with `p`-group kernel, every coarse
solution has a fine lift. This statement does not require finite generation
of `G`; finiteness of the solution sets is a separate hypothesis for a
subsequent compactness argument.
-/

public section

namespace TauCeti

universe u v w

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {A : Type v} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [CompactSpace A]
variable {B : Type w} [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [T2Space B]

/-- The image of an open normal subgroup under `α` is monotone in the subgroup. -/
theorem levelImage_mono (α : A →ₜ* B) (hα : Function.Surjective α) :
    Monotone (levelImage α hα) := by
  intro V U h
  rw [← OpenNormalSubgroup.toSubgroup_le, levelImage_toSubgroup, levelImage_toSubgroup]
  exact Subgroup.map_mono h

/-- Restrict a solution at `V` to the coarser quotient at `U`. -/
def levelSolutionMap (α : A →ₜ* B) (hα : Function.Surjective α) (f : G →ₜ* B)
    {V U : OpenNormalSubgroup A} (hVU : V ≤ U) (β : LevelSolution α hα f V) :
    LevelSolution α hα f U := by
  refine ⟨(⟨QuotientGroup.mapOfLE hVU, continuous_of_discreteTopology⟩ :
    A ⧸ V.toSubgroup →ₜ* A ⧸ U.toSubgroup).comp β.1, ?_⟩
  intro g
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (β.1 g)
  have hβ := β.2 g
  rw [← ha, levelMap_mk] at hβ
  rw [ContinuousMonoidHom.coe_comp, Function.comp_apply, ContinuousMonoidHom.coe_mk, ← ha,
    QuotientGroup.mapOfLE_mk, levelMap_mk]
  simpa only [QuotientGroup.mk'_apply, QuotientGroup.mapOfLE_mk] using
    congrArg (QuotientGroup.mapOfLE (levelImage_mono α hα hVU)) hβ

@[simp]
theorem levelSolutionMap_apply (α : A →ₜ* B) (hα : Function.Surjective α) (f : G →ₜ* B)
    {V U : OpenNormalSubgroup A} (hVU : V ≤ U) (β : LevelSolution α hα f V) (g : G) :
    (levelSolutionMap α hα f hVU β).1 g = QuotientGroup.mapOfLE hVU (β.1 g) :=
  (rfl)

@[simp]
theorem levelSolutionMap_refl (α : A →ₜ* B) (hα : Function.Surjective α) (f : G →ₜ* B)
    {U : OpenNormalSubgroup A} (β : LevelSolution α hα f U) :
    levelSolutionMap α hα f (le_refl U) β = β := by
  apply Subtype.ext
  ext g
  simp only [levelSolutionMap_apply, QuotientGroup.mapOfLE_refl, MonoidHom.id_apply]

@[simp]
theorem levelSolutionMap_comp (α : A →ₜ* B) (hα : Function.Surjective α) (f : G →ₜ* B)
    {W V U : OpenNormalSubgroup A} (hWV : W ≤ V) (hVU : V ≤ U)
    (β : LevelSolution α hα f W) :
    levelSolutionMap α hα f hVU (levelSolutionMap α hα f hWV β) =
      levelSolutionMap α hα f (hWV.trans hVU) β := by
  apply Subtype.ext
  ext g
  simp only [levelSolutionMap_apply]
  exact DFunLike.congr_fun (QuotientGroup.mapOfLE_comp hWV hVU) (β.1 g)

instance (α : A →ₜ* B) (hα : Function.Surjective α) (f : G →ₜ* B) :
    DirectedSystem (LevelSolution α hα f) (fun _ _ h ↦ levelSolutionMap α hα f h) where
  map_self := fun _ β ↦ levelSolutionMap_refl α hα f β
  map_map := fun _ _ _ hWV hVU β ↦ levelSolutionMap_comp α hα f hWV hVU β

variable [IsTopologicalGroup G]

/-- Every solution at a coarse level extends to a solution at any finer level. -/
theorem levelSolutionMap_surjective {p : ℕ} (hG : HasPGroupSolutions p G)
    (hA : IsProP p A) (α : A →ₜ* B) (hα : Function.Surjective α) (f : G →ₜ* B)
    {V U : OpenNormalSubgroup A} (hVU : V ≤ U) :
    Function.Surjective (levelSolutionMap α hα f hVU) := by
  intro β
  let φ := (QuotientGroup.mapOfLE hVU).prod (levelMap α hα V)
  let γ := β.1.toMonoidHom.prod
    ((QuotientGroup.mk' (levelImage α hα V).toSubgroup).comp f.toMonoidHom)
  have hmem : ∀ g, γ g ∈ φ.range := by
    intro g
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (β.1 g)
    have hβ := β.2 g
    rw [← ha, levelMap_mk] at hβ
    have hm : (α a)⁻¹ * f g ∈ U.toSubgroup.map α.toMonoidHom := by
      rw [← levelImage_toSubgroup α hα U]
      exact QuotientGroup.eq.mp hβ
    obtain ⟨t, ht, hat⟩ := Subgroup.mem_map.mp hm
    rw [ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_ofClass] at hat
    refine ⟨((a * t : A) : A ⧸ V.toSubgroup), ?_⟩
    simp only [φ, γ, MonoidHom.prod_apply, MonoidHom.comp_apply,
      ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_ofClass, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [QuotientGroup.mapOfLE_mk, ← ha, QuotientGroup.mk_mul,
        (QuotientGroup.eq_one_iff t).mpr ht, mul_one]
    · rw [levelMap_mk, map_mul, hat, mul_inv_cancel_left, QuotientGroup.mk'_apply]
  let γ' : G →* φ.range := γ.codRestrict _ hmem
  have hγ : IsOpen (γ'.ker : Set G) := (MonoidHom.continuous_iff_isOpen_ker _).mp
    ((β.1.continuous.prodMk (QuotientGroup.continuous_mk.comp f.continuous)).subtype_mk _)
  obtain ⟨δ, hδ, hcomp⟩ := hG.exists_comp_eq φ.rangeRestrict φ.rangeRestrict_surjective
    ((isProP_iff.mp hA V).to_subgroup _) γ' hγ
  have hpair (g : G) : φ (δ g) = γ g :=
    congrArg Subtype.val (DFunLike.congr_fun hcomp g)
  refine ⟨⟨⟨δ, δ.continuous_iff_isOpen_ker.mpr hδ⟩, ?_⟩, ?_⟩
  · intro g
    exact congrArg Prod.snd (hpair g)
  · apply Subtype.ext
    ext g
    exact congrArg Prod.fst (hpair g)

end TauCeti
