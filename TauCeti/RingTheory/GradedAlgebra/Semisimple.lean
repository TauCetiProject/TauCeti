/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Semisimple degree-zero parts of graded algebras

This file gives a criterion for the degree-zero part of a graded algebra to be semisimple. If it
is spanned over a field by a complete family of orthogonal idempotents, it is a quotient of a
finite product of copies of the field and hence is semisimple.

## Main results

* `TauCeti.isSemisimpleRing_gradeZero_of_completeOrthogonalIdempotents`: a degree-zero piece
  spanned by a complete family of orthogonal idempotents is a semisimple ring.
-/

public section

namespace TauCeti

universe uk uA uI

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} {I : Type uI} {e : I → A} [Fintype I]
  (hcomplete : CompleteOrthogonalIdempotents e) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hspan : 𝒜 0 ≤ Submodule.span k (Set.range e))

include hcomplete he₀ hspan in
/-- A degree-zero piece spanned by a complete family of orthogonal idempotents is a semisimple
ring: `c ↦ ∑ cᵢ eᵢ` is a surjective ring homomorphism from `I → k` onto `𝒜 0`. Thus split
degree-zero parts satisfy the semisimplicity hypothesis of minimal graded resolution theory. -/
theorem isSemisimpleRing_gradeZero_of_completeOrthogonalIdempotents [SetLike.GradedMonoid 𝒜] :
    IsSemisimpleRing (𝒜 0) := by
  let f : (I → k) →+* 𝒜 0 :=
    { toFun c := ⟨∑ i, c i • e i, Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (he₀ i)⟩
      map_one' := Subtype.ext <| by simpa using hcomplete.complete
      map_mul' c c' := Subtype.ext <| by
        simp only [SetLike.GradeZero.coe_mul, Pi.mul_apply, Finset.sum_mul_sum, smul_mul_smul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_eq_single i (fun j _ hj => by rw [hcomplete.ortho (Ne.symm hj), smul_zero])
          (by simp), (hcomplete.idem i).eq]
      map_zero' := Subtype.ext <| by simp
      map_add' c c' := Subtype.ext <| by simp [add_smul, Finset.sum_add_distrib] }
  refine RingHom.isSemisimpleRing_of_surjective f fun x => ?_
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp (hspan x.2)
  exact ⟨c, Subtype.ext hc⟩

end TauCeti
