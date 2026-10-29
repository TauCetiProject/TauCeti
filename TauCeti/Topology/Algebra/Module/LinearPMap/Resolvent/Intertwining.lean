/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.LinearPMap.Intertwining
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Basic

/-!
# Intertwining partial operators through their resolvents

A domain-aware intertwiner of two partial operators intertwines their continuous
resolvents at every common resolvent point. Conversely, intertwining at just one common
resolvent point recovers both domain transport and the operator identity. Thus bounded
resolvents characterize an intertwining relation between possibly unbounded operators.

The statements first use arbitrary inverse witnesses `LinearPMap.IsResolventAt` and
then specialize to the chosen resolvents. They apply between different topological
modules over a ring, without completeness, closedness, or self-adjointness assumptions.

## References

K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Sections 1.1 and 2.2;
K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
Section IV.1. The inverse identities are those of `LinearPMap.IsResolventAt`.
-/

public section

namespace TauCeti

variable {𝕜 E F : Type*} [Ring 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
  [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F]
  {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F} {X : E →L[𝕜] F} {z : 𝕜}
  {R : E →L[𝕜] E} {S : F →L[𝕜] F}

/-- Intertwining partial operators passes through continuous inverses of their shifts. -/
theorem _root_.LinearPMap.Intertwines.comp_eq_of_isResolventAt
    (h : A.Intertwines B X) (hR : A.IsResolventAt z R) (hS : B.IsResolventAt z S) :
    X ∘L R = S ∘L X := by
  ext y
  have hleft := hS.apply_smul_sub ⟨X (R y), h.mem_domain ⟨R y, hR.mem_domain y⟩⟩
  rw [← h.apply_eq ⟨R y, hR.mem_domain y⟩, ← X.map_smul,
    ← X.map_sub, hR.smul_sub_apply y] at hleft
  simpa only [ContinuousLinearMap.comp_apply] using hleft.symm

/-- Intertwining two continuous inverses at the same parameter recovers the full
domain-aware intertwining relation of the partial operators. -/
theorem _root_.LinearPMap.intertwines_of_comp_eq_of_isResolventAt
    (hR : A.IsResolventAt z R) (hS : B.IsResolventAt z S) (h : X ∘L R = S ∘L X) :
    A.Intertwines B X := by
  have hpoint (y : E) : X (R y) = S (X y) := by
    simpa only [ContinuousLinearMap.comp_apply] using DFunLike.congr_fun h y
  have hrecover (x : A.domain) : S (X (z • (x : E) - A x)) = X x := by
    rw [← hpoint, hR.apply_smul_sub x]
  have hmem (x : A.domain) : X x ∈ B.domain :=
    hrecover x ▸ hS.mem_domain (X (z • (x : E) - A x))
  refine ⟨hmem, fun x => ?_⟩
  have hright := hS.smul_sub_apply (X (z • (x : E) - A x))
  have hx : (⟨S (X (z • (x : E) - A x)), hS.mem_domain _⟩ : B.domain) =
      ⟨X x, hmem x⟩ := Subtype.ext (hrecover x)
  rw [hx, hrecover x, X.map_sub, X.map_smul] at hright
  exact (sub_right_inj.mp hright).symm

/-- At a common resolvent point, intertwining the operators is equivalent to
intertwining their bounded resolvents. A single such point suffices. -/
theorem _root_.LinearPMap.intertwines_iff_comp_resolvent_eq
    (hA : z ∈ A.resolventSet) (hB : z ∈ B.resolventSet) :
    A.Intertwines B X ↔ X ∘L A.resolvent z = B.resolvent z ∘L X :=
  ⟨fun h => h.comp_eq_of_isResolventAt (LinearPMap.isResolventAt_resolvent hA)
      (LinearPMap.isResolventAt_resolvent hB),
    LinearPMap.intertwines_of_comp_eq_of_isResolventAt
      (LinearPMap.isResolventAt_resolvent hA) (LinearPMap.isResolventAt_resolvent hB)⟩

end TauCeti
