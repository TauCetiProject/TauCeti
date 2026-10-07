/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Analytic

/-!
# Analytic submanifolds in polynomial stacks

Every sector of a continuous ordered stack over a `d`-dimensional real analytic
submanifold is an analytic submanifold of dimension `d + 1`. Only continuity of
the boundaries is needed: the sector is relatively open in the ambient cylinder.
This includes the two unbounded sectors and the whole cylinder of a stack without
sections.

Together with the analytic section theorem, this proves that every cell of a
delineation with intrinsically analytic coefficients has dimension either `d` or
`d + 1` and is an analytic submanifold. These are the bases needed for successive
analytic polynomial liftings.

## References

S. McCallum, *An improved projection operation for cylindrical algebraic
decomposition*, Springer (1998), 242–268 (analytic delineability and lifting).
-/

public section

open Function Polynomial Set

namespace TauCeti

variable {n d k : ℕ} {S : Set (Fin n → ℝ)} {θ : Fin k → S → ℝ}

/-- Every sector of a continuous strictly ordered stack over an analytic
submanifold is an analytic submanifold of dimension one more than its base.
No analyticity of the boundary functions is required. -/
theorem isAnalyticSubmanifold_image_cylinder_sectorSet
    (hS : IsAnalyticSubmanifold d S) (hc : ∀ i, Continuous (θ i))
    (hθ : ∀ x, StrictMono fun i ↦ θ i x) (j : Fin (k + 1)) :
    IsAnalyticSubmanifold (d + 1) (cylinder S '' sectorSet θ j) := by
  have hsub : cylinder S '' sectorSet θ j ⊆ {v | Fin.tail v ∈ S} := by
    rintro _ ⟨z, _, rfl⟩
    simpa only [mem_ofPred_eq, tail_cylinder] using z.1.property
  have hne : (cylinder S '' sectorSet θ j).Nonempty := by
    obtain ⟨x, hx⟩ := hS.nonempty
    obtain ⟨σ, _, hσ⟩ := exists_continuous_forall_mem_sectorSet hc hθ j
    exact ⟨_, ⟨(⟨x, hx⟩, σ ⟨x, hx⟩), hσ _, rfl⟩⟩
  refine hS.cylinder.of_isOpen_preimage_val hsub ?_ hne
  -- The inverse cylinder coordinates identify the relative sector with the
  -- open sector in `S × ℝ`; the subtype carries exactly the cylinder topology.
  let f : {v : Fin (n + 1) → ℝ | Fin.tail v ∈ S} → S × ℝ :=
    fun v ↦ (⟨Fin.tail v.val, v.property⟩, v.val 0)
  have hf : Continuous f :=
    (continuous_subtype_val.finTail.subtype_mk _).prodMk
      ((continuous_apply 0).comp continuous_subtype_val)
  convert (isOpen_sectorSet hc j).preimage hf using 1
  ext v
  simp only [mem_preimage, mem_image_cylinder, f]
  exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨v.property, h⟩⟩

namespace Delineation

variable {ι : Type*} {P : ι → (Fin n → ℝ) → ℝ[X]}
  (D : Delineation fun i (x : S) ↦ P i x)

/-- Every cell of a delineation with intrinsically analytic coefficients over
a `d`-dimensional analytic submanifold is an analytic submanifold. Sections have
dimension `d`, while sectors have dimension `d + 1`. -/
theorem exists_isAnalyticSubmanifold_of_mem_stackCells
    (hS : IsAnalyticSubmanifold d S)
    (hcoeff : ∀ i j, AnalyticOnSubmanifold d (fun x ↦ (P i x).coeff j) S)
    {E : Set (Fin (n + 1) → ℝ)} (hE : E ∈ stackCells S D.root) :
    ∃ e, (e = d ∨ e = d + 1) ∧ IsAnalyticSubmanifold e E := by
  rcases mem_stackCells.1 hE with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · exact ⟨d, Or.inl rfl, D.isAnalyticSubmanifold_sectionSet hS hcoeff i⟩
  · exact ⟨d + 1, Or.inr rfl, isAnalyticSubmanifold_image_cylinder_sectorSet hS
      D.continuous_root D.strictMono_root j⟩

end Delineation
end TauCeti
