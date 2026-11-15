/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Signature

/-!
# Indices of inertia under pullback along a surjection

Let `p : M →ₗ[K] M'` be a surjective linear map of vector spaces over an ordered field and `Q` a
quadratic form on `M'`. The pullback `Q.comp p` vanishes on `ker p` together with its polar form,
so `ker p` lies in its radical, and the induced form on `M ⧸ ker p ≃ M'` is `Q` itself. Since
quotienting by a subspace of the radical preserves both indices of inertia
(`QuadraticForm.sigPos_lift`, `QuadraticForm.sigNeg_lift`), the pullback has the same indices of
inertia as `Q`.

This is the linear algebra behind the Morse indices of a function `f ∘ π` pulled back along a
submersion `π`: the Hessian of `f ∘ π` at a critical point is the Hessian of `f` pulled back along
the surjective derivative of `π`, so it has the Morse index of `f`.

## Main results

* `QuadraticMap.ker_le_radical_comp`: the kernel of `p` lies in the radical of `Q.comp p`.
* `QuadraticForm.sigPos_comp_of_surjective`, `QuadraticForm.sigNeg_comp_of_surjective`: pulling back
  along a surjective linear map preserves both indices of inertia.
-/

public section

namespace QuadraticMap

variable {R M M' P : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R M'] [AddCommGroup P] [Module R P]

/-- The kernel of a linear map `p` lies in the radical of the pullback `Q.comp p`. -/
theorem ker_le_radical_comp (Q : QuadraticMap R M' P) (p : M →ₗ[R] M') :
    LinearMap.ker p ≤ (Q.comp p).radical := fun x hx ↦
  mem_radical_iff'.2 ⟨by simp [LinearMap.mem_ker.1 hx], fun y ↦ by simp [LinearMap.mem_ker.1 hx]⟩

end QuadraticMap

namespace QuadraticForm

variable {K M M' : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup M]
  [Module K M] [FiniteDimensional K M] [AddCommGroup M'] [Module K M']
  (Q : _root_.QuadraticForm K M') {p : M →ₗ[K] M'}

/-- **Pulling back along a surjection preserves the positive index of inertia.** -/
theorem sigPos_comp_of_surjective (hp : Function.Surjective p) : sigPos (Q.comp p) = sigPos Q := by
  rw [← sigPos_lift _ _ (QuadraticMap.ker_le_radical_comp Q p)]
  exact QuadraticMap.Equivalent.sigPos_eq
    ⟨{ p.quotKerEquivOfSurjective hp with
      map_app' := fun x ↦ by
        induction x using Submodule.Quotient.induction_on with
        | H x =>
          simp [LinearMap.quotKerEquivOfSurjective_apply_mk, QuadraticMap.lift_mk] }⟩

/-- **Pulling back along a surjection preserves the negative index of inertia.** -/
theorem sigNeg_comp_of_surjective (hp : Function.Surjective p) : sigNeg (Q.comp p) = sigNeg Q := by
  have hneg : (-Q).comp p = -(Q.comp p) := QuadraticMap.ext fun _ ↦ rfl
  rw [← sigPos_neg, ← sigPos_neg, ← sigPos_comp_of_surjective (-Q) hp, hneg]

end QuadraticForm
