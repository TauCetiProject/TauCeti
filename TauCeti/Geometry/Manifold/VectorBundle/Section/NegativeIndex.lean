/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Parametric

/-!
# Generic absence of negative-index section zeros

A regular zero has surjective linearization, so its index is the nonnegative dimension of
its kernel. Consequently, if the linearizations of a parameter slice have negative index at
all zeros, regularity of that parameter is equivalent to absence of zeros. Parametric
transversality then implies that zero-free parameters form a residual, dense set.

These results complement the regular-zero manifold theorem: a negative expected dimension
means an empty moduli space, not a manifold modelled on a truncated natural-number dimension.
The index need not be constant, and its sign is required only at actual zeros. The analytic
hypotheses and differentiability threshold are those of the parametric section theorem.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Appendix A.3 (generic regularity and the dimension of zero sets).
-/

public section

open Bundle Filter Function Module Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {X Λ M B F EB HB : Type*} {E : B → Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [TopologicalSpace M] [ChartedSpace X M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB}
  [TopologicalSpace B] [ChartedSpace HB B]
  [∀ a, TopologicalSpace (E a)] [TopologicalSpace (TotalSpace F E)]
  [∀ a, AddCommGroup (E a)] [∀ a, Module ℝ (E a)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  {b : M × Λ → B} {s : ∀ z, E (b z)}

/-- When every zero of a parameter slice has negative index, the parameter is regular if and
only if that slice has no zeros. This implication needs no smoothness or Fredholm assumption:
surjectivity alone forces the algebraic index to be nonnegative. -/
theorem isRegularSectionParameter_iff_forall_ne_zero_of_index_neg {l : Λ}
    (hindex : ∀ x, s (x, l) = 0 → LinearMap.index
      (sectionLinearization (F := F) 𝓘(ℝ, X) (fun y ↦ b (y, l))
        (fun y ↦ s (y, l)) x).toLinearMap < 0) :
    IsRegularSectionParameter (F := F) X b s l ↔ ∀ x, s (x, l) ≠ 0 := by
  rw [isRegularSectionParameter_iff]
  constructor
  · intro hl x hx
    have hi := hindex x hx
    rw [LinearMap.index_of_surjective (hl x hx)] at hi
    exact (not_lt_of_ge (Int.natCast_nonneg _)) hi
  · intro hl x hx
    exact (hl x hx).elim

variable [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [CompleteSpace X] [CompleteSpace Λ]
  [CompleteSpace F] [IsManifold 𝓘(ℝ, X) 1 M]
  [SecondCountableTopology ↥{z | s z = 0}] {n : ℕ∞ω}
  (hcont : ∀ z, s z = 0 → ContMDiffAt (𝓘(ℝ, X).prod 𝓘(ℝ, Λ)) (I.prod 𝓘(ℝ, F)) n
    (fun w ↦ (⟨b w, s w⟩ : TotalSpace F E)) z)
  (hFred : ∀ z, s z = 0 → ContinuousLinearMap.IsFredholm
    (sectionLinearization (F := F) 𝓘(ℝ, X) (fun y ↦ b (y, z.2)) (fun y ↦ s (y, z.2)) z.1))
  (htotal : ∀ z, s z = 0 →
    Surjective (sectionLinearization (F := F) (𝓘(ℝ, X).prod 𝓘(ℝ, Λ)) b s z))
  (hn : ∀ z, s z = 0 → ((finrank ℝ (sectionLinearization (F := F) 𝓘(ℝ, X)
    (fun y ↦ b (y, z.2)) (fun y ↦ s (y, z.2)) z.1).ker ^ 2 + 1 : ℕ) : ℕ∞ω) ≤ n)
  (hindex : ∀ z, s z = 0 → LinearMap.index (sectionLinearization (F := F) 𝓘(ℝ, X)
    (fun y ↦ b (y, z.2)) (fun y ↦ s (y, z.2)) z.1).toLinearMap < 0)

include hcont hFred htotal hn hindex

/-- **Generic absence of negative-index zeros.** If the slice linearization is Fredholm of
negative index at each zero and the total section is transverse to zero, zero-free parameters
form a residual set. Second countability is needed only for the universal zero set. -/
theorem mem_residual_setOf_forall_section_ne_zero_of_index_neg :
    {l | ∀ x, s (x, l) ≠ 0} ∈ residual Λ := by
  filter_upwards [mem_residual_setOf_isRegularSectionParameter hcont hFred htotal hn] with l hl
  exact (isRegularSectionParameter_iff_forall_ne_zero_of_index_neg
    (fun x hx ↦ hindex (x, l) hx)).mp hl

/-- Zero-free parameters of a transverse universal section with negative slice indices are
dense in the Banach parameter space. In particular they occur arbitrarily near any prescribed
parameter, without a constant-index assumption. -/
theorem dense_setOf_forall_section_ne_zero_of_index_neg :
    Dense {l | ∀ x, s (x, l) ≠ 0} :=
  dense_of_mem_residual
    (mem_residual_setOf_forall_section_ne_zero_of_index_neg hcont hFred htotal hn hindex)

end TauCeti
