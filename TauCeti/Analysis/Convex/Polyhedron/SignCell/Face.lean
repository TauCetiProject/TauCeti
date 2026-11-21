/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.SignCell.Basic
public import TauCeti.Analysis.Convex.Polyhedron.Face

/-!
# Faces of affine arrangements

Every nonempty convex extreme subset of a weak cell of a finite affine
arrangement is a weak zero-specialization with a realized strict cell. Under continuous
addition and scalar multiplication it is the closure of that strict cell. Thus the
finite family of closures of realized sign cells is closed under nonempty
convex extreme subsets. These are statements about continuous real affine rows;
no rationality assumption or bundled polyhedral-complex structure is introduced.

Adapted from `Mei/Geometry/Convex/Polyhedron/SignCell/Face.lean` at commit
`bf3986029ff4d3eb4025d4067489511b0724374e` of
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei) (Apache 2.0).
-/

public section

open TauCeti.Convex (SignSpecializes closure_signCell
  mem_signCell_sign mem_weakSignCell_iff_rows
  mem_weakSignCell_iff_specializes realizedSignCellClosures signCell signSpecializes_iff
  weakSignCell weakSignCellRows weakSignCellRows_eq_zero_iff weakSignCell_eq_setOf_rows
  weakSignCell_subset_of_specializes)

namespace IsExtreme


variable {V ι : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [Finite ι]

/-- Every nonempty convex extreme subset of a weak arrangement cell is a weak cell of a
realized zero-specialization. No continuity of the module operations is needed. -/
theorem exists_zeroSpecialization_weakSignCell {g : ι → (V →ᴬ[ℝ] ℝ)}
    {σ : ι → SignType} {F : Set V} (hF : IsExtreme ℝ (weakSignCell g σ) F)
    (hconv : Convex ℝ F) (hne : F.Nonempty) :
    ∃ τ : ι → SignType, SignSpecializes τ σ ∧ (signCell g τ).Nonempty ∧
      F = weakSignCell g τ := by
  have hrows : IsExtreme ℝ {x | ∀ p, weakSignCellRows g σ p x ≤ 0} F := by
    rwa [← weakSignCell_eq_setOf_rows]
  obtain ⟨I, hI⟩ := hrows.eq_setOf_active
    (fun j => (weakSignCellRows g σ j).toAffineMap) hconv hne
  obtain ⟨p, hp, hpoint⟩ := hconv.exists_mem_zero_iff_forall hne
    (fun j => (weakSignCellRows g σ j).toAffineMap)
    (fun j x hx => mem_weakSignCell_iff_rows.mp (hF.subset hx) j)
  let τ : ι → SignType := fun j => SignType.sign (g j p)
  have hτ : SignSpecializes τ σ := mem_weakSignCell_iff_specializes.mp (hF.subset hp)
  have hτne : (signCell g τ).Nonempty := ⟨p, mem_signCell_sign g p⟩
  refine ⟨τ, hτ, hτne, ?_⟩
  apply Set.Subset.antisymm
  · intro x hx
    apply TauCeti.Convex.mem_weakSignCell.mpr
    intro j
    by_cases hj : τ j = 0
    · have hpj : g j p = 0 := sign_eq_zero_iff.mp hj
      have hprow : weakSignCellRows g σ (j, true) p = 0 :=
        weakSignCellRows_eq_zero_iff.mpr hpj
      have hxrow := (hpoint (j, true)).mp hprow x hx
      have hxj := weakSignCellRows_eq_zero_iff.mp hxrow
      simp [hj, hxj]
    · have heq : τ j = σ j := (signSpecializes_iff.mp hτ j).resolve_left hj
      simpa only [heq] using TauCeti.Convex.mem_weakSignCell.mp (hF.subset hx) j
  · intro x hx
    rw [hI]
    refine ⟨mem_weakSignCell_iff_rows.mp (weakSignCell_subset_of_specializes hτ hx), ?_⟩
    intro j hj
    have hpI := (hI ▸ hp).2 j hj
    have hpj : g j.1 p = 0 := weakSignCellRows_eq_zero_iff.mp hpI
    have hτj : τ j.1 = 0 := sign_eq_zero_iff.mpr hpj
    have hxj := (TauCeti.Convex.mem_weakSignCell.mp hx j.1).1 hτj
    exact weakSignCellRows_eq_zero_iff.mpr hxj

variable [ContinuousAdd V] [ContinuousSMul ℝ V]

/-- Nonempty faces of realized closed sign cells are themselves realized closed
sign cells, with a zero-specialized assignment. -/
theorem exists_zeroSpecialization_closure_signCell {g : ι → (V →ᴬ[ℝ] ℝ)}
    {σ : ι → SignType} {F : Set V} (hF : IsExtreme ℝ (closure (signCell g σ)) F)
    (hconv : Convex ℝ F) (hne : F.Nonempty) :
    ∃ τ : ι → SignType, SignSpecializes τ σ ∧ (signCell g τ).Nonempty ∧
      F = closure (signCell g τ) := by
  have hσ := (hne.mono hF.subset).of_closure
  rw [closure_signCell hσ] at hF
  obtain ⟨τ, hτ, hτne, heq⟩ := hF.exists_zeroSpecialization_weakSignCell hconv hne
  exact ⟨τ, hτ, hτne, by rw [closure_signCell hτne]; exact heq⟩

end IsExtreme

namespace TauCeti.Convex

variable {V ι : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [ContinuousAdd V] [ContinuousSMul ℝ V]

/-- The full realized closure family is closed under all nonempty convex extreme subsets. -/
theorem _root_.IsExtreme.mem_realizedSignCellClosures [Finite ι]
    {g : ι → (V →ᴬ[ℝ] ℝ)} {P F : Set V} (hF : IsExtreme ℝ P F)
    (hP : P ∈ realizedSignCellClosures g) (hconv : Convex ℝ F) (hne : F.Nonempty) :
    F ∈ realizedSignCellClosures g := by
  obtain ⟨σ, _, rfl⟩ := TauCeti.Convex.mem_realizedSignCellClosures.mp hP
  obtain ⟨τ, _, hτ, heq⟩ := hF.exists_zeroSpecialization_closure_signCell hconv hne
  exact TauCeti.Convex.mem_realizedSignCellClosures.mpr ⟨τ, hτ, heq⟩

end TauCeti.Convex
