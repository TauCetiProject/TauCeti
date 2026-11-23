/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.LinearPMap.Conj
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Basic

/-!
# Resolvents of a partial linear map conjugated by a continuous linear equivalence

For a continuous linear equivalence `e : E ≃L[R] F`, conjugation `A ↦ e A e⁻¹` (see
`TauCeti.Topology.Algebra.Module.LinearPMap.Conj`) transports continuous inverses of the shifts
`z • I - A`, so `e A e⁻¹` and `A` have the same resolvent set and spectrum, with resolvents
`e R(z, A) e⁻¹`.

## Main results

* `LinearPMap.IsResolventAt.conj`: `e T e⁻¹` inverts `z • I - e A e⁻¹` when `T` inverts
  `z • I - A`.
* `LinearPMap.resolventSet_conj` and `LinearPMap.spectrum_conj`: resolvent sets and spectra.
* `LinearPMap.resolvent_conj`: `R(z, e A e⁻¹) = e R(z, A) e⁻¹`.

## References

K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Section 2.2.
-/

public section

namespace LinearPMap

variable {R E F : Type*} [Ring R] [AddCommGroup E] [Module R E] [TopologicalSpace E]
  [AddCommGroup F] [Module R F] [TopologicalSpace F]

variable {A : E →ₗ.[R] E} (e : E ≃L[R] F)

/-- If `T` inverts `z • I - A`, then `e T e⁻¹` inverts `z • I - e A e⁻¹`. -/
theorem IsResolventAt.conj {z : R} {T : E →L[R] E} (h : A.IsResolventAt z T) :
    (A.conj (e : E ≃ₗ[R] F)).IsResolventAt z
      ((e : E →L[R] F) ∘L T ∘L (e.symm : F →L[R] E)) := by
  rw [isResolventAt_iff_forall_mem_graph] at h ⊢
  refine ⟨fun y ↦ ?_, fun p hp ↦ ?_⟩
  · rw [mem_graph_conj_iff]
    simpa using h.1 (e.symm y)
  · have := h.2 _ (mem_graph_conj_iff.1 hp)
    simpa using congrArg e this

/-- Conjugation by a continuous linear equivalence preserves the resolvent set. -/
@[simp]
theorem resolventSet_conj (A : E →ₗ.[R] E) :
    (A.conj (e : E ≃ₗ[R] F)).resolventSet = A.resolventSet := by
  ext z
  refine ⟨fun hz ↦ ?_, fun hz ↦ ?_⟩
  · obtain ⟨T, hT⟩ := mem_resolventSet_iff.1 hz
    have := hT.conj e.symm
    rw [ContinuousLinearEquiv.toLinearEquiv_symm, conj_conj_symm] at this
    exact this.mem_resolventSet
  · obtain ⟨T, hT⟩ := mem_resolventSet_iff.1 hz
    exact (hT.conj e).mem_resolventSet

/-- Conjugation by a continuous linear equivalence preserves the spectrum. -/
@[simp]
theorem spectrum_conj (A : E →ₗ.[R] E) : (A.conj (e : E ≃ₗ[R] F)).spectrum = A.spectrum := by
  ext z
  rw [mem_spectrum_iff, mem_spectrum_iff, resolventSet_conj]

/-- The resolvent of `e A e⁻¹` is `e R(z, A) e⁻¹`. -/
theorem resolvent_conj {z : R} (hz : z ∈ A.resolventSet) :
    (A.conj (e : E ≃ₗ[R] F)).resolvent z =
      (e : E →L[R] F) ∘L A.resolvent z ∘L (e.symm : F →L[R] E) :=
  resolvent_eq_of_isResolventAt ((isResolventAt_resolvent hz).conj e)

end LinearPMap
