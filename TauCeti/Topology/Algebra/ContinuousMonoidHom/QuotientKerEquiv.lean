/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic
import TauCeti.GroupTheory.QuotientGroup.KerEquiv

/-!
# The topological first isomorphism theorem for a compact group

A continuous surjection from a compact group to a Hausdorff group identifies the target
with the quotient by its kernel by a continuous multiplicative equivalence. This bundles the
algebraic first isomorphism theorem
`QuotientGroup.quotientKerEquivOfSurjective` with the homeomorphism supplied by compactness.
It permits changing the quotient model in profinite extensions.
-/

public section

namespace ContinuousMonoidHom

variable {G H : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
  [Group H] [TopologicalSpace H] [T2Space H]
  (f : G →ₜ* H) (hf : Function.Surjective f)

/-- The first isomorphism theorem for a continuous surjection from a compact group to a
Hausdorff group, with the quotient topology on the source. -/
noncomputable def quotientKerEquivOfSurjective : (G ⧸ (f : G →* H).ker) ≃ₜ* H := by
  let e := QuotientGroup.quotientKerEquivOfSurjective f.toMonoidHom hf
  have hc : Continuous e :=
    (QuotientGroup.isQuotientMap_mk (f : G →* H).ker).continuous_iff.mpr <| by
    simpa [e, Function.comp_def,
      TauCeti.QuotientGroup.quotientKerEquivOfSurjective_apply_mk] using f.continuous
  let h := Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv) hc
  exact
    { e with
      continuous_toFun := h.continuous_toFun
      continuous_invFun := h.continuous_invFun }

/-- The topological first isomorphism theorem sends the class of `x` to `f x`. -/
@[simp]
theorem quotientKerEquivOfSurjective_apply_mk (x : G) :
    f.quotientKerEquivOfSurjective hf (QuotientGroup.mk x) = f x :=
  TauCeti.QuotientGroup.quotientKerEquivOfSurjective_apply_mk f.toMonoidHom hf x

/-- The inverse of the topological first isomorphism theorem sends `f x` to the class of `x`. -/
@[simp]
theorem quotientKerEquivOfSurjective_symm_apply (x : G) :
    (f.quotientKerEquivOfSurjective hf).symm (f x) = QuotientGroup.mk x := by
  rw [← f.quotientKerEquivOfSurjective_apply_mk hf x, ContinuousMulEquiv.symm_apply_apply]

end ContinuousMonoidHom
