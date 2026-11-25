/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.LineBundle.FiniteDimensional
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic

/-!
# Finite determination on native compact complex curves

The trivial line on the Riemann sphere has a nonzero constant holomorphic section. The
trivial line on two disjoint Riemann spheres has a section with different constant values on
its components. The rank-zero bundle and empty complex curve retain finite determination.
-/

noncomputable section

open Bundle OnePoint
open scoped Manifold ContDiff

namespace TauCeti

private abbrev Sphere := OnePoint ℂ

private def oneSection : Cₛ^ω⟮𝓘(ℂ); ℂ, Trivial Sphere ℂ⟯ :=
  ⟨fun _ ↦ 1, Trivial.contMDiff_mk_iff.mpr ⟨contMDiff_id, contMDiff_const⟩⟩

/-- The trivial holomorphic line on the native Riemann sphere has a nonzero section. -/
public theorem exists_ne_zero_holomorphicSection_trivial_onePoint :
    ∃ s : Cₛ^ω⟮𝓘(ℂ); ℂ, Trivial (OnePoint ℂ) ℂ⟯, s ≠ 0 := by
  refine ⟨oneSection, ?_⟩
  intro h
  have hval : (1 : ℂ) = 0 := congrArg (fun s : Cₛ^ω⟮𝓘(ℂ); ℂ, Trivial Sphere ℂ⟯ ↦ s ∞) h
  exact one_ne_zero hval

example : FiniteDimensional ℂ Cₛ^ω⟮𝓘(ℂ); ℂ, Trivial Sphere ℂ⟯ := inferInstance

example : FiniteDimensional ℂ Cₛ^((⊤ : ℕ∞) : ℕ∞ω)⟮𝓘(ℂ); ℂ, Trivial Sphere ℂ⟯ := inferInstance

example : FiniteDimensional ℂ
    Cₛ^ω⟮𝓘(ℂ); ℂ, (TangentSpace 𝓘(ℂ) : Sphere → Type)⟯ := inferInstance

example : ∃ P : Finset Sphere,
    Function.Injective (LinearMap.pi fun x : P ↦
      ContMDiffSection.evalLinearMap 𝓘(ℂ) ℂ ω (Trivial Sphere ℂ) x) :=
  ContMDiffSection.exists_finset_eval_injective_of_compactSpace (by simp)

-- Finite determination also applies to an infinite-dimensional model of continuous functions.
example : ∃ P : Finset Sphere,
    Function.Injective (LinearMap.pi fun x : P ↦
      ContMDiffSection.evalLinearMap 𝓘(ℂ) (C(Set.Icc (0 : ℝ) 1, ℂ)) ω
        (Trivial Sphere (C(Set.Icc (0 : ℝ) 1, ℂ))) x) :=
  ContMDiffSection.exists_finset_eval_injective_of_compactSpace (by simp)

example : FiniteDimensional ℂ
    (holomorphicSectionCechCohomology 𝓘(ℂ) ℂ (Trivial Sphere ℂ) 0) := inferInstance

private def componentSection : Cₛ^ω⟮𝓘(ℂ); ℂ, Trivial (Sphere ⊕ Sphere) ℂ⟯ :=
  ⟨Sum.elim (fun _ ↦ 0) (fun _ ↦ 1), Trivial.contMDiff_mk_iff.mpr
    ⟨contMDiff_id, contMDiff_const.sumElim contMDiff_const⟩⟩

example : componentSection (.inl ∞) = 0 ∧ componentSection (.inr ∞) = 1 := ⟨rfl, rfl⟩

example : FiniteDimensional ℂ Cₛ^ω⟮𝓘(ℂ); ℂ, Trivial (Sphere ⊕ Sphere) ℂ⟯ := inferInstance

example : 2 ≤ Module.finrank ℂ Cₛ^ω⟮𝓘(ℂ); ℂ, Trivial (Sphere ⊕ Sphere) ℂ⟯ := by
  let L := (ContMDiffSection.evalLinearMap 𝓘(ℂ) ℂ ω (Trivial (Sphere ⊕ Sphere) ℂ)
    (.inl ∞)).prod
      (ContMDiffSection.evalLinearMap 𝓘(ℂ) ℂ ω (Trivial (Sphere ⊕ Sphere) ℂ) (.inr ∞))
  have hL : Function.Surjective L := by
    rintro ⟨a, b⟩
    exact ⟨⟨Sum.elim (fun _ ↦ a) (fun _ ↦ b), Trivial.contMDiff_mk_iff.mpr
      ⟨contMDiff_id, contMDiff_const.sumElim contMDiff_const⟩⟩, by
        simp [L, ContMDiffSection.evalLinearMap_apply]⟩
  simpa using LinearMap.finrank_le_finrank_of_surjective hL

example : FiniteDimensional ℂ Cₛ^ω⟮𝓘(ℂ); Fin 2 → ℂ, Trivial Sphere (Fin 2 → ℂ)⟯ :=
  inferInstance

example : FiniteDimensional ℂ Cₛ^ω⟮𝓘(ℂ); Fin 0 → ℂ, Trivial Sphere (Fin 0 → ℂ)⟯ :=
  inferInstance

example : Module.finrank ℂ Cₛ^ω⟮𝓘(ℂ); Fin 0 → ℂ, Trivial Sphere (Fin 0 → ℂ)⟯ = 0 := by
  let : Subsingleton Cₛ^ω⟮𝓘(ℂ); Fin 0 → ℂ, Trivial Sphere (Fin 0 → ℂ)⟯ :=
    ⟨fun s t ↦ ContMDiffSection.ext fun _ ↦ Subsingleton.elim _ _⟩
  exact Module.finrank_zero_of_subsingleton

private instance : ChartedSpace ℂ PEmpty.{1} := ChartedSpace.empty ℂ PEmpty.{1}

example : FiniteDimensional ℂ Cₛ^ω⟮𝓘(ℂ); ℂ, Trivial PEmpty.{1} ℂ⟯ := inferInstance

example : Module.finrank ℂ Cₛ^ω⟮𝓘(ℂ); ℂ, Trivial PEmpty.{1} ℂ⟯ = 0 :=
  Module.finrank_zero_of_subsingleton

example : ∃ P : Finset PEmpty.{1},
    Function.Injective (LinearMap.pi fun x : P ↦
      ContMDiffSection.evalLinearMap 𝓘(ℂ) ℂ ω (Trivial PEmpty.{1} ℂ) x) :=
  ContMDiffSection.exists_finset_eval_injective_of_compactSpace (by simp)

end TauCeti
