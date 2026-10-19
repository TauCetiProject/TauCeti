/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.CAD.Basic
public import TauCeti.Analysis.Analytic.Submanifold.Transport
import Mathlib.Topology.Algebra.Module.Equiv.Pi
import Mathlib.Topology.Algebra.Module.Equiv.Prod

/-!
# Changing the base of a cylindrical stack

Pulling a stack back along a map of its base pulls every section and sector back along the
corresponding map of the cylinder, leaving the distinguished coordinate unchanged. Polynomial
base maps preserve semialgebraic stacks. When the base map is a coordinate permutation,
analyticity of the ambient cells is preserved as well.

These results transport the geometric output of polynomial lifting between coordinate orders.
They do not assert that arbitrary coordinate permutations preserve cylindrical decompositions,
or that Lazard valuations are invariant under coordinate permutations.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 5.3.
-/

public section

open Set Function MvPolynomial

namespace TauCeti

variable {n m k : ℕ}

/-- A polynomial change of base preserves semialgebraic stacks. This uses only inverse images,
not closure of semialgebraic sets under projection. -/
theorem IsSemialgebraicStack.comp {C : Set (Fin n → ℝ)} {θ : Fin k → C → ℝ}
    (hθ : IsSemialgebraicStack C θ) (p : Fin n → MvPolynomial (Fin m) ℝ) :
    IsSemialgebraicStack ((fun x i ↦ eval x (p i)) ⁻¹' C)
      (fun i x ↦ θ i ⟨(fun j ↦ eval x.1 (p j)), x.2⟩) := by
  let f : (Fin m → ℝ) → Fin n → ℝ := fun x i ↦ eval x (p i)
  have hf : Continuous f := continuous_pi fun i ↦ continuous_eval (p i)
  let q : Fin (n + 1) → MvPolynomial (Fin (m + 1)) ℝ :=
    Fin.cons (X 0) (fun i ↦ rename Fin.succ (p i))
  have hq (y : Fin (m + 1) → ℝ) :
      (fun i ↦ eval y (q i)) = Fin.cons (y 0) (f (Fin.tail y)) := by
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [q, f, eval_rename, Fin.tail_def, Function.comp_def]
  refine ⟨fun i ↦ (hθ.continuous i).comp ((hf.comp continuous_subtype_val).subtype_mk fun x ↦ x.2),
    fun x ↦ hθ.strictMono ⟨f x.1, x.2⟩, fun i ↦ ?_, fun j ↦ ?_⟩
  · rw [image_cylinder_sectionSet_comp]
    convert (hθ.isSemialgebraic_sectionSet i).preimage_eval q using 1
    ext y
    simp only [mem_preimage, hq, f]
  · rw [image_cylinder_sectorSet_comp]
    convert (hθ.isSemialgebraic_sectorSet j).preimage_eval q using 1
    ext y
    simp only [mem_preimage, hq, f]

/-- Reordering only the base coordinates preserves a semialgebraic stack and analyticity
of its cells. The newly lifted coordinate remains first. -/
theorem IsSemialgebraicStack.reindex {C : Set (Fin n → ℝ)} {θ : Fin k → C → ℝ}
    (hθ : IsSemialgebraicStack C θ) (e : Equiv.Perm (Fin n))
    (ha : ∀ E ∈ stackCells C θ, ∃ d, IsAnalyticSubmanifold d E) :
    IsSemialgebraicStack ((fun x ↦ x ∘ e) ⁻¹' C)
        (fun i x ↦ θ i ⟨x.1 ∘ e, x.2⟩) ∧
      ∀ E ∈ stackCells ((fun x ↦ x ∘ e) ⁻¹' C) (fun i x ↦ θ i ⟨x.1 ∘ e, x.2⟩),
        ∃ d, IsAnalyticSubmanifold d E := by
  refine ⟨?_, ?_⟩
  · have hf : (fun x i ↦ eval x (X (e i) : MvPolynomial (Fin n) ℝ)) =
        (fun x ↦ x ∘ e) := by
      ext x i
      simp
    exact (congrArg (fun f : (Fin n → ℝ) → Fin n → ℝ ↦
      IsSemialgebraicStack (f ⁻¹' C) (fun i x ↦ θ i ⟨f x.1, x.2⟩)) hf).mp
        (hθ.comp (fun i ↦ X (e i)))
  · intro E hE
    rw [stackCells_comp] at hE
    obtain ⟨E, hE, rfl⟩ := hE
    obtain ⟨d, hd⟩ := ha E hE
    let c := Fin.consEquivL ℝ (fun _ : Fin (n + 1) ↦ ℝ)
    let b := ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin n ↦ ℝ) e.symm
    let L := (c.symm.trans ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr b)).trans c
    have hL (y : Fin (n + 1) → ℝ) : L y = Fin.cons (y 0) (Fin.tail y ∘ e) := by
      ext i
      refine Fin.cases ?_ (fun j ↦ ?_) i <;>
        simp [L, c, b, ContinuousLinearEquiv.piCongrLeft, Equiv.piCongrLeft_apply,
          Function.comp_def]
    refine ⟨d, ?_⟩
    convert hd.preimage L.toHomeomorph (fun y _ ↦ L.analyticAt y)
      (fun y _ ↦ L.symm.analyticAt y) using 1
    ext y
    simp only [mem_preimage, ContinuousLinearEquiv.coe_toHomeomorph, hL]

end TauCeti
