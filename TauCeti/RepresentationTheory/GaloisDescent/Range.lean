/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RingTheory.TensorProduct.Basic
import TauCeti.FieldTheory.Galois.Trace

/-!
# Recognizing the invariant vectors by scalar extension

Let `G` be a finite Galois group for a field extension `L/k` (`IsGaloisGroup G k L`), for
instance `Gal(L/k)` itself when `L/k` is finite Galois. An invariant subspace of a semilinear
representation of `G` is the whole space of invariants if its scalar extension surjects onto the
representation. This criterion identifies tensor products of descended vector spaces with
invariant tensors. It works in arbitrary characteristic, using an element of field trace one
instead of dividing by the order of `G`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Appendix A.64 (Galois descent).
-/

public section

open scoped TensorProduct

namespace TauCeti.GaloisDescent

variable {k G L V W : Type*} [Field k] [Group G] [Field L] [Algebra k L]
variable [MulSemiringAction G L] [IsGaloisGroup G k L] [Finite G]
variable [AddCommGroup V] [Module k V] [Module L V] [IsScalarTower k L V]
variable [AddCommGroup W] [Module k W]

/-- An invariant linear map into a semilinear representation of a finite Galois group `G` of
`L/k` whose scalar extension is surjective has image equal to all the invariant vectors. Neither
vector space needs to be finite-dimensional. -/
theorem range_eq_invariants_of_liftBaseChange_surjective
    {ρ : Representation k G V} {f : W →ₗ[k] V}
    (hsemi : ∀ (g : G) (a : L) (v : V), ρ g (a • v) = (g • a) • ρ g v)
    (hinv : ∀ (g : G) (w : W), ρ g (f w) = f w)
    (hf : Function.Surjective (f.liftBaseChange L)) :
    LinearMap.range f = ρ.invariants := by
  classical
  have := IsGaloisGroup.finiteDimensional G k L
  have := IsGaloisGroup.isGalois G k L
  let := Fintype.ofFinite G
  -- The orbit sum of `b • v` for an invariant vector `v` is `Tr(b) • v`.
  have hnorm (b : L) {v : V} (hv : v ∈ ρ.invariants) :
      ρ.norm (b • v) = Algebra.trace k L b • v := by
    simp only [Representation.norm, LinearMap.sum_apply, hsemi, (ρ.mem_invariants v).mp hv]
    rw [← Finset.sum_smul, ← IsGaloisGroup.algebraMap_trace_eq_sum G k,
      IsScalarTower.algebraMap_smul]
  have hfw (w : W) : f w ∈ ρ.invariants := (ρ.mem_invariants _).mpr (hinv · w)
  refine le_antisymm (by rintro _ ⟨w, rfl⟩; exact hfw w) fun v hv ↦ ?_
  obtain ⟨a, ha⟩ := Algebra.trace_surjective k L 1
  -- Applying `x ↦ ρ.norm (a • x)` to the scalar extension of `f` lands in the range of `f`.
  have hmem (x : L ⊗[k] W) : ρ.norm (a • f.liftBaseChange L x) ∈ LinearMap.range f := by
    induction x using TensorProduct.inductionOn with
    | tmul b w =>
      rw [LinearMap.liftBaseChange_tmul, smul_smul, hnorm _ (hfw w)]
      exact ⟨Algebra.trace k L (a * b) • w, f.map_smul _ _⟩
    | add x y hx hy => simpa only [map_add, smul_add] using add_mem hx hy
  obtain ⟨x, rfl⟩ := hf v
  simpa only [hnorm a hv, ha, one_smul] using hmem x

end TauCeti.GaloisDescent
