/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ComplexProjectiveSpace.Homogeneous
public import TauCeti.Topology.ComplexProjectiveSpace.Hopf.Exact

/-!
# Unitary invariance of the boundary map of the Hopf fibration

A unitary matrix `A ∈ U(n + 1)` acts on the unit sphere `S²ⁿ⁺¹ ⊂ ℂⁿ⁺¹` and on `CPⁿ`
(`TauCeti.ComplexProjectiveSpace.smul_mk`), and the Hopf projection `mk : S²ⁿ⁺¹ → CPⁿ` intertwines
the two actions. So `A` is a map of the Hopf fibration to itself. On the fibres it is complex
linear: it carries `u • v` to `u • A v` for a unit scalar `u`. In the circle coordinates
`u ↦ u • v` and `u ↦ u • A v` of the fibres over `[v]` and `[A v]`
(`TauCeti.ComplexProjectiveSpace.hopfFiberHomeomorph`) it is therefore the identity of the circle.

By the naturality of the boundary map of the Hopf fibration
(`TauCeti.ComplexProjectiveSpace.hopfBoundary_homotopyGroupMap_of_smul_comm`), the boundary map
`π_{k+1}(CPⁿ, [v]) → π_k(S¹, 1)` of the Hopf fibration is invariant under `A`
(`TauCeti.ComplexProjectiveSpace.hopfBoundary_homotopyGroupMap_smul`). In particular, for `n ≥ 1`
the isomorphism `π₂(CPⁿ, [v]) ≃* ℤ` of the Hopf fibration does not change when a class is moved by
a unitary matrix (`TauCeti.ComplexProjectiveSpace.pi2MulEquivInt_homotopyGroupMap_smul`). As
`U(n + 1)` acts transitively on the unit sphere, this compares the isomorphisms `π₂(CPⁿ) ≃* ℤ` at
any two base points.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 4.41 and Example 4.45.
-/

public section

noncomputable section

open CategoryTheory Matrix Metric
open scoped Topology.Homotopy

namespace TauCeti.ComplexProjectiveSpace

variable {n : ℕ} (A : unitaryGroup (Fin (n + 1)) ℂ)
  (v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)

/-- **The boundary map of the Hopf fibration is invariant under unitary matrices.** For a unitary
`A`, the boundary map `π_{k+1}(CPⁿ, [A v]) → π_k(S¹, 1)` applied to the image under `A` of a class
of `π_{k+1}(CPⁿ, [v])` agrees with the boundary map at `[v]` applied to the class itself. -/
@[simp]
theorem hopfBoundary_homotopyGroupMap_smul (N : Type*) [Finite N]
    (a : HomotopyGroup (Option N) (ComplexProjectiveSpace n) (mk n v)) :
    hopfBoundary (UnitaryGroup.toLinearIsometryEquiv A • v) N
        (HomotopyGroup.map ⟨(A • ·), continuous_const_smul A⟩ (smul_mk A v) a) =
      hopfBoundary v N a :=
  -- On the sphere, `A` is complex linear, so it commutes with unit complex scalars.
  hopfBoundary_homotopyGroupMap_of_smul_comm
    (F := ⟨(UnitaryGroup.toLinearIsometryEquiv A • ·), continuous_const_smul _⟩)
    (fun u x ↦ Subtype.ext <| by simp [Sphere.coe_sphere_smul]) (smul_mk A) v rfl _ a

/-- **The isomorphism `π₂(CPⁿ) ≃* ℤ` of the Hopf fibration is invariant under unitary matrices.**
For `n ≥ 1` and a unitary `A`, the image under `A` of a class of `π₂(CPⁿ, [v])` has, at the base
point `[A v]`, the same image in `ℤ` as the class itself at `[v]`. -/
@[simp]
theorem pi2MulEquivInt_homotopyGroupMap_smul (hn : n ≠ 0)
    (a : HomotopyGroup (Fin 2) (ComplexProjectiveSpace n) (mk n v)) :
    pi2MulEquivInt (UnitaryGroup.toLinearIsometryEquiv A • v) hn
        (HomotopyGroup.map ⟨(A • ·), continuous_const_smul A⟩ (smul_mk A v) a) =
      pi2MulEquivInt v hn a := by
  rw [pi2MulEquivInt_apply, pi2MulEquivInt_apply, ← HomotopyGroup.map_congrEquiv,
    hopfBoundary_homotopyGroupMap_smul]

end TauCeti.ComplexProjectiveSpace
