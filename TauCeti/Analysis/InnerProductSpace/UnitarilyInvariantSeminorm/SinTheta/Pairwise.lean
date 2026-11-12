/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.SinTheta.Basic
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Sylvester.Pairwise

/-!
# The pairwise `π / 2` Davis–Kahan `sin Θ` theorem

Let `A` and `B` be symmetric operators on a finite-dimensional inner product space `E`, let `U`
be invariant under `A` and `V` invariant under `B`. If every eigenvalue of `A` on `U` is at
distance at least `δ` from every eigenvalue of `B` on `Vᗮ`, with no ordering or interval
structure assumed, then the directed sine map `P_{Vᗮ} P_U` from `U` towards `V` satisfies

  `δ N(P_{Vᗮ} P_U) ≤ (π / 2) N(B - A)`

for every unitarily invariant seminorm `N`. Compared with the interval/exterior form in
`TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.SinTheta.Basic`, which has
constant `1`, the hypothesis is weaker and the constant is the sharp one of Bhatia, Davis and
McIntosh.

The map `Y = P_{Vᗮ} P_U` takes values in the `B`-invariant subspace `Vᗮ`, vanishes on `Uᗮ`, and
solves `B Y - Y A = P_{Vᗮ} (B - A) P_U`. The pairwise Sylvester bound on invariant subspaces gives
`δ N(Y) ≤ (π / 2) N(P_{Vᗮ} (B - A) P_U) ≤ (π / 2) N(B - A)`.

## Main results

In the namespace `TauCeti.UnitarilyInvariantSeminorm`:

* `mul_map_starProjection_comp_starProjection_le_pi_div_two_mul_map_sub`: the pairwise
  perturbation `sin Θ` theorem `δ N(P_{Vᗮ} P_U) ≤ (π / 2) N(B - A)`.

## References

* R. Bhatia, C. Davis, A. McIntosh, *Perturbation of spectral subspaces and solution of linear
  operator equations*, Linear Algebra Appl. **52/53** (1983), 45–67.
* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer (1997), §VII.3.
-/

public section

open Module
open scoped Real

namespace TauCeti.UnitarilyInvariantSeminorm

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {δ : ℝ}

/-- **The pairwise `π / 2` Davis–Kahan `sin Θ` theorem.** Let `A` and `B` be symmetric operators
on a finite-dimensional inner product space, let `U` be invariant under `A` and `V` invariant
under `B`. If every eigenvalue of `A` on `U` is at distance at least `δ` from every eigenvalue of
`B` on `Vᗮ`, then the directed sine map `P_{Vᗮ} P_U` from `U` towards `V` satisfies
`δ N(P_{Vᗮ} P_U) ≤ (π / 2) N(B - A)` for every unitarily invariant seminorm `N`. -/
theorem mul_map_starProjection_comp_starProjection_le_pi_div_two_mul_map_sub
    (N : UnitarilyInvariantSeminorm 𝕜 E E) {A B : E →L[𝕜] E} (hA : (A : E →ₗ[𝕜] E).IsSymmetric)
    (hB : (B : E →ₗ[𝕜] E).IsSymmetric) {U V : Submodule 𝕜 E} (hU : ∀ x ∈ U, A x ∈ U)
    (hV : ∀ x ∈ V, B x ∈ V)
    (h : End.PointSpectraSeparated (A : E →ₗ[𝕜] E) U (B : E →ₗ[𝕜] E) Vᗮ δ) :
    δ * N (Vᗮ.starProjection ∘L U.starProjection) ≤ π / 2 * N (B - A) :=
  calc δ * N (Vᗮ.starProjection ∘L U.starProjection)
      ≤ π / 2 * N (B.sylvester A (Vᗮ.starProjection ∘L U.starProjection)) :=
        N.mul_map_le_pi_div_two_mul_map_sylvester_apply_of_mem (S := Vᗮ) hB hA
          (fun _ hx ↦ hB.orthogonalComplement_mem_invtSubmodule (p := V) (fun y hy ↦ hV y hy) hx)
          hU h.symm (fun x ↦ Vᗮ.starProjection_apply_mem _)
          fun x hx ↦ by simp [U.starProjection_apply_eq_zero_iff.mpr hx]
    _ ≤ π / 2 * N (B - A) := by
        gcongr
        exact N.map_sylvester_starProjection_comp_starProjection_le hA hB hU hV

end TauCeti.UnitarilyInvariantSeminorm
