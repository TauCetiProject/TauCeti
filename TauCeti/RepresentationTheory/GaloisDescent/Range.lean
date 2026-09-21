/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RepresentationTheory.Invariants
import Mathlib.RingTheory.Trace.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Recognizing the invariant vectors by scalar extension

An invariant subspace of a semilinear representation over a finite Galois extension is the
whole space of invariants if its scalar extension surjects onto the representation. This
criterion identifies tensor products of descended vector spaces with invariant tensors.
It works in arbitrary characteristic, using an element of field trace one instead of dividing
by the order of the Galois group.

## References

* J. S. Milne, *Algebraic Groups* (2017), Appendix A.64 (Galois descent).
-/

public section

open scoped TensorProduct

namespace TauCeti.GaloisDescent

variable {k L V W : Type*} [Field k] [Field L] [Algebra k L]
variable [AddCommGroup V] [Module k V] [Module L V] [IsScalarTower k L V]
variable [AddCommGroup W] [Module k W]
variable [FiniteDimensional k L] [IsGalois k L]

/-- An invariant linear map whose scalar extension is surjective has image equal to all the
invariant vectors. Neither vector space needs to be finite-dimensional. -/
theorem range_eq_invariants_of_liftBaseChange_surjective
    {ρ : Representation k (L ≃ₐ[k] L) V} {f : W →ₗ[k] V}
    (hsemi : ∀ (σ : L ≃ₐ[k] L) (a : L) (v : V),
      ρ σ (a • v) = σ a • ρ σ v)
    (hinv : ∀ (σ : L ≃ₐ[k] L) (w : W), ρ σ (f w) = f w)
    (hf : Function.Surjective (f.liftBaseChange L)) :
    LinearMap.range f = ρ.invariants := by
  classical
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    exact (Representation.mem_invariants _ _).mpr (fun σ ↦ hinv σ w)
  · intro v hv
    obtain ⟨a, ha⟩ := Algebra.trace_surjective k L 1
    have hnorm (b : L) (w : W) :
        ρ.norm (b • f w) = Algebra.trace k L b • f w := by
      simp only [Representation.norm, LinearMap.sum_apply, hsemi, hinv]
      rw [← Finset.sum_smul, ← trace_eq_sum_automorphisms,
        IsScalarTower.algebraMap_smul]
    have hmem (x : L ⊗[k] W) :
        ρ.norm (a • f.liftBaseChange L x) ∈ LinearMap.range f := by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul b w =>
          rw [LinearMap.liftBaseChange_tmul, smul_smul, hnorm]
          exact ⟨Algebra.trace k L (a * b) • w, f.map_smul _ _⟩
      | add x y hx hy =>
          simpa only [map_add, smul_add] using (LinearMap.range f).add_mem hx hy
    obtain ⟨x, rfl⟩ := hf v
    have hfixed := (Representation.mem_invariants _ _).mp hv
    have hnorm_v : ρ.norm (a • f.liftBaseChange L x) = f.liftBaseChange L x := by
      simp only [Representation.norm, LinearMap.sum_apply, hsemi, hfixed]
      rw [← Finset.sum_smul, ← trace_eq_sum_automorphisms,
        IsScalarTower.algebraMap_smul, ha, one_smul]
    exact hnorm_v ▸ hmem x

end TauCeti.GaloisDescent
