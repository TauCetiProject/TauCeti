/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.Basic
public import TauCeti.Topology.ContinuousMap.ZeroExtendClopen

/-!
# Clopen restriction and decomposition of abstract measures

`TauCeti.restrictClopen` restricts a measure to a clopen subtype by dualizing extension
by zero of test functions. The inclusion pushforward is a section of restriction.
Its image consists exactly of measures annihilating tests that vanish on the clopen.
`TauCeti.clopenDecomposition` identifies ambient measures with pairs of measures on
complementary clopens, with inverse given by the sum of inclusion pushforwards.
Restriction is natural under pushforward and preimages.

All constructions use Mathlib's `AbstractMeasure` carrier and its pushforward `map`;
no topology or norm is installed on that carrier. The coefficient ring need not be a field,
complete, or ultrametric, and either clopen may be empty.

See Rodrigues Jacinto and Williams, *An introduction to p-adic L-functions*, §3.5.3,
Remark 3.31, for restriction to open compact subsets in p-adic integration.
-/

public section

open TopologicalSpace AbstractMeasure
open scoped AbstractMeasure

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
variable (s : Clopens X) (R : Type*) [NormedCommRing R]

/-- Restrict a measure to a clopen subtype by evaluating on zero-extended tests. -/
noncomputable def restrictClopen : D(X, R) →ₗ[R] D(s, R) where
  toFun μ := toCLMEquiv.symm ((toCLMEquiv μ).comp (zeroExtendClopen s R))
  map_add' := by intro μ ν; ext f; simp
  map_smul' := by intro a μ; ext f; simp

@[simp]
theorem restrictClopen_apply (μ : D(X, R)) (f : C(s, R)) :
    restrictClopen s R μ f = μ (zeroExtendClopen s R f) :=
  by simp [restrictClopen, ContinuousLinearMap.comp_apply]

@[simp]
theorem restrictClopen_map_subtype (ν : D(s, R)) :
    restrictClopen s R (map (X := s) (ContinuousMap.subtypeVal (s : Set X)) ν) = ν := by
  ext f
  simp only [restrictClopen_apply, map_apply]
  congr 1
  ext x
  exact zeroExtendClopen_apply_mem s R f x

/-- Pushing a clopen restriction back to the ambient space gives its test-function projector. -/
theorem map_subtype_restrictClopen_apply (μ : D(X, R)) (f : C(X, R)) :
    map (ContinuousMap.subtypeVal s) (restrictClopen s R μ) f =
      μ ((LocallyConstant.charFn R s.isClopen).toContinuousMap * f) := by
  rw [map_apply, restrictClopen_apply, comp_subtypeVal_eq_restrict,
    zeroExtendClopen_restrict]

@[simp]
theorem restrictClopen_dirac_mem (x : s) :
    restrictClopen s R (dirac R (x : X)) = dirac R x := by
  ext f
  rw [restrictClopen_apply, dirac_apply, dirac_apply]
  exact zeroExtendClopen_apply_mem s R f x

@[simp]
theorem restrictClopen_dirac_not_mem {x : X} (hx : x ∉ s) :
    restrictClopen s R (dirac R x) = 0 := by
  ext f
  rw [restrictClopen_apply, dirac_apply, zero_apply]
  exact zeroExtendClopen_apply_not_mem s R f hx

/-- Every measure restricts to zero on the empty clopen. -/
@[simp]
theorem restrictClopen_bot (μ : D(X, R)) : restrictClopen (⊥ : Clopens X) R μ = 0 := by
  ext f
  rw [restrictClopen_apply, zero_apply]
  have hf : f = 0 := by
    ext x
    exact False.elim (by simpa only [← SetLike.mem_coe, Clopens.coe_bot,
      Set.mem_empty_iff_false] using x.property)
  simp [hf]

/-- A measure comes uniquely from the clopen subtype exactly when it annihilates
all ambient tests vanishing on that clopen. The preimage is its clopen restriction. -/
theorem existsUnique_map_subtype_iff (μ : D(X, R)) :
    (∃! ν : D(s, R), map (ContinuousMap.subtypeVal s) ν = μ) ↔
      ∀ f : C(X, R), (∀ x : s, f x = 0) → μ f = 0 := by
  constructor
  · rintro ⟨ν, rfl, _⟩ f hf
    rw [map_apply]
    have hzero : f.comp (ContinuousMap.subtypeVal s) = 0 := by
      ext x
      exact hf x
    simp [hzero]
  · intro hμ
    have hmap : map (ContinuousMap.subtypeVal s) (restrictClopen s R μ) = μ := by
      ext f
      rw [map_apply, restrictClopen_apply]
      have hzero := hμ (f - zeroExtendClopen s R
        (f.comp (ContinuousMap.subtypeVal (s : Set X))))
        (fun x ↦ by simp [ContinuousMap.subtypeVal])
      rw [map_sub, sub_eq_zero] at hzero
      exact hzero.symm
    refine ⟨restrictClopen s R μ, hmap, fun ν hν ↦ ?_⟩
    rw [← hν, restrictClopen_map_subtype]

/-- Restricting a measure carried by a disjoint clopen gives zero. -/
@[simp]
theorem restrictClopen_map_of_disjoint (t : Clopens X) (hst : Disjoint s t)
    (ν : D(t, R)) :
    restrictClopen s R (map (X := t) (ContinuousMap.subtypeVal (t : Set X)) ν) = 0 := by
  ext f
  simp only [restrictClopen_apply, map_apply, zero_apply]
  have hzero : (zeroExtendClopen s R f).comp
      (ContinuousMap.subtypeVal t) = 0 := by
    ext x
    exact zeroExtendClopen_apply_not_mem s R f
      (fun hx ↦ Set.disjoint_left.mp (Clopens.coe_disjoint.mpr hst) hx x.property)
  rw [hzero, map_zero]

/-- Recombining the two complementary restrictions recovers the ambient measure. -/
theorem map_subtype_restrictClopen_add_compl (μ : D(X, R)) :
    map (ContinuousMap.subtypeVal s) (restrictClopen s R μ) +
      map (ContinuousMap.subtypeVal (sᶜ : Clopens X)) (restrictClopen sᶜ R μ) = μ := by
  ext f
  rw [add_apply, map_apply, map_apply, restrictClopen_apply, restrictClopen_apply, ← map_add]
  rw [comp_subtypeVal_eq_restrict, comp_subtypeVal_eq_restrict,
    zeroExtendClopen_restrict_add_compl]

/-- Measures on a compact space decompose into measures on complementary clopens. -/
noncomputable def clopenDecomposition : D(X, R) ≃ₗ[R] D(s, R) × D((sᶜ : Clopens X), R) where
  toLinearMap := (restrictClopen s R).prod (restrictClopen sᶜ R)
  invFun (νη : D(s, R) × D((sᶜ : Clopens X), R)) := map (ContinuousMap.subtypeVal s) νη.1 +
    map (ContinuousMap.subtypeVal (sᶜ : Clopens X)) νη.2
  left_inv := by
    intro μ
    exact map_subtype_restrictClopen_add_compl s R μ
  right_inv := by
    intro νη
    -- The constructor presents the forward map as the coerced product linear map.
    change (restrictClopen s R (map (ContinuousMap.subtypeVal s) νη.1 +
      map (ContinuousMap.subtypeVal (sᶜ : Clopens X)) νη.2),
      restrictClopen sᶜ R (map (ContinuousMap.subtypeVal s) νη.1 +
      map (ContinuousMap.subtypeVal (sᶜ : Clopens X)) νη.2)) = νη
    apply Prod.ext
    · dsimp only
      rw [map_add, restrictClopen_map_subtype,
        restrictClopen_map_of_disjoint s R sᶜ disjoint_compl_right, add_zero]
    · dsimp only
      rw [map_add, restrictClopen_map_of_disjoint sᶜ R s disjoint_compl_left,
        restrictClopen_map_subtype, zero_add]

@[simp]
theorem clopenDecomposition_apply (μ : D(X, R)) :
    clopenDecomposition s R μ = (restrictClopen s R μ, restrictClopen sᶜ R μ) :=
  (rfl)

@[simp]
theorem clopenDecomposition_symm_apply (νη : D(s, R) × D((sᶜ : Clopens X), R)) :
    (clopenDecomposition s R).symm νη =
      map (ContinuousMap.subtypeVal s) νη.1 +
        map (ContinuousMap.subtypeVal (sᶜ : Clopens X)) νη.2 :=
  (rfl)

/-- Clopen restriction commutes with pushforward along the map restricted to the preimage. -/
theorem restrictClopen_map_preimage {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (t : Clopens Y) (f : C(X, Y)) (μ : D(X, R)) :
    let s : Clopens X := ⟨f ⁻¹' (t : Set Y), t.isClopen.preimage f.continuous⟩
    restrictClopen t R (map f μ) = map (f.restrictPreimage t) (restrictClopen s R μ) := by
  intro s
  ext g
  rw [restrictClopen_apply, map_apply, map_apply, restrictClopen_apply]
  exact congrArg μ (zeroExtendClopen_comp_restrictPreimage R t f g)

end TauCeti
