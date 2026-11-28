/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Basic
public import TauCeti.Topology.Algebra.Module.LinearPMap.Sylvester

/-!
# Resolvent identities for domain-aware Sylvester equations

For partial linear maps `A` and `B` and continuous linear maps `X, C : F →L[𝕜] E` satisfying
the domain-aware Sylvester equation `A X - X B = C` (`LinearPMap.SylvesterEquation A B X C`),
every common resolvent point `z` of `A` and `B` satisfies the bounded commutator identity

`R_A(z) ∘L X - X ∘L R_B(z) = R_A(z) ∘L C ∘L R_B(z)`

(`LinearPMap.SylvesterEquation.resolvent_comp_sub_comp_resolvent`). When `A = B`, this takes the
algebraic form `A.resolvent z * X - X * A.resolvent z = A.resolvent z * C * A.resolvent z`
(`LinearPMap.SylvesterEquation.resolvent_mul_sub_mul_resolvent`).
-/

public section

namespace LinearPMap

variable {𝕜 E F : Type*} [Ring 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E] [IsTopologicalAddGroup E]
  [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F]

/-- **Resolvent identity for a domain-aware Sylvester equation.** If `A X - X B = C` on the
domain of `B` and `z` lies in the resolvent sets of both `A` and `B`, then
`R_A(z) X - X R_B(z) = R_A(z) C R_B(z)`. -/
theorem SylvesterEquation.resolvent_comp_sub_comp_resolvent
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F} {X C : F →L[𝕜] E}
    (hXC : SylvesterEquation A B X C) {z : 𝕜}
    (hzA : z ∈ A.resolventSet) (hzB : z ∈ B.resolventSet) :
    A.resolvent z ∘L X - X ∘L B.resolvent z = A.resolvent z ∘L C ∘L B.resolvent z := by
  ext y
  simp only [_root_.sub_apply, ContinuousLinearMap.comp_apply]
  have hmem : B.resolvent z y ∈ B.domain := resolvent_mem_domain hzB y
  have hXmem : X (B.resolvent z y) ∈ A.domain := hXC.mapsTo_domain ⟨B.resolvent z y, hmem⟩
  have hstep : z • X (B.resolvent z y) - A ⟨X (B.resolvent z y), hXmem⟩ =
      X y - C (B.resolvent z y) := by
    have hC := hXC.equation ⟨B.resolvent z y, hmem⟩
    dsimp only at hC
    conv_rhs =>
      arg 1; rw [← smul_sub_apply_resolvent hzB y, X.map_sub, ContinuousLinearMap.map_smul]
    rw [← hC]
    abel
  have happ := congrArg (A.resolvent z) hstep
  rw [resolvent_smul_sub_apply hzA ⟨X (B.resolvent z y), hXmem⟩, (A.resolvent z).map_sub] at happ
  exact sub_eq_iff_eq_add'.2 (eq_add_of_sub_eq happ.symm)

/-- **Endomorphism form of the Sylvester resolvent identity.** If `A X - X A = C` on the domain
of `A` and `z ∈ A.resolventSet`, then
`A.resolvent z * X - X * A.resolvent z = A.resolvent z * C * A.resolvent z`. -/
theorem SylvesterEquation.resolvent_mul_sub_mul_resolvent
    {A : E →ₗ.[𝕜] E} {X C : E →L[𝕜] E}
    (hXC : SylvesterEquation A A X C) {z : 𝕜} (hz : z ∈ A.resolventSet) :
    A.resolvent z * X - X * A.resolvent z = A.resolvent z * C * A.resolvent z :=
  hXC.resolvent_comp_sub_comp_resolvent hz hz

end LinearPMap
