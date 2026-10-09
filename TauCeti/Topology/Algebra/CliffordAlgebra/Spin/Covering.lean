/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Basic
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.Descent
public import Mathlib.Topology.Covering.Quotient

/-!
# The compact real Spin double cover

The projection from the compact real Spin group to the special orthogonal group is a covering map
whenever its domain is compact. Indeed, the projection is a continuous surjection from a compact
space to a Hausdorff space, hence a quotient map. Its kernel is the finite image of the included
group `Multiplicative (ZMod 2)`, so the standard quotient-covering construction applies.

## Main results

* `CliffordAlgebra.isQuotientCoveringMap_realCliffordSpinDoubleCoverZero_rightHom` packages the
  compact real Spin projection as a quotient covering map by its kernel.
* `CliffordAlgebra.isCoveringMap_realCliffordSpinDoubleCoverZero_rightHom` packages the projection
  as an ordinary covering map.
* `CliffordAlgebra.realCliffordSpinHomEquivKer` identifies continuous homomorphisms out of
  `SO(n)` with continuous homomorphisms out of `Spin(n)` that kill the double-cover kernel.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Section 2.
-/

public section

namespace CliffordAlgebra

open TauCeti

/-- The compact real Spin projection, bundled as a continuous homomorphism. -/
noncomputable def realCliffordSpinProjectionZero (n : ℕ) [NeZero n] :
    realCliffordSpinGroupZero n →ₜ*
      QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0) :=
  ⟨(realCliffordSpinDoubleCoverZero n).rightHom,
    continuous_realCliffordSpinDoubleCoverZero_rightHom n⟩

/-- The bundled compact real Spin projection agrees with the projection of the double-cover
extension. -/
@[simp]
theorem realCliffordSpinProjectionZero_apply (n : ℕ) [NeZero n]
    (x : realCliffordSpinGroupZero n) :
    realCliffordSpinProjectionZero n x = (realCliffordSpinDoubleCoverZero n).rightHom x := by
  rw [realCliffordSpinProjectionZero]
  rfl

/-- The compact real Spin projection has the same underlying monoid homomorphism as the projection
of the double-cover extension. -/
@[simp]
theorem coeMonoidHom_realCliffordSpinProjectionZero (n : ℕ) [NeZero n] :
    (realCliffordSpinProjectionZero n : realCliffordSpinGroupZero n →*
      QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)) =
        (realCliffordSpinDoubleCoverZero n).rightHom := by
  rw [realCliffordSpinProjectionZero]
  rfl

/-- The compact real Spin projection has the same underlying function as the projection of the
double-cover extension. -/
theorem coe_realCliffordSpinProjectionZero (n : ℕ) [NeZero n] :
    (realCliffordSpinProjectionZero n : realCliffordSpinGroupZero n →
      QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)) =
        (realCliffordSpinDoubleCoverZero n).rightHom :=
  funext (realCliffordSpinProjectionZero_apply n)

/-- The compact real Spin projection is a quotient covering map by its kernel. -/
theorem isQuotientCoveringMap_realCliffordSpinDoubleCoverZero_rightHom
    (n : ℕ) [NeZero n] [CompactSpace (realCliffordSpinGroupZero n)] :
    IsQuotientCoveringMap (realCliffordSpinDoubleCoverZero n).rightHom
      (realCliffordSpinDoubleCoverZero n).rightHom.ker := by
  let S := realCliffordSpinDoubleCoverZero n
  have hquot : Topology.IsQuotientMap S.rightHom :=
    Topology.IsQuotientMap.of_surjective_continuous S.rightHom_surjective
      (continuous_realCliffordSpinDoubleCoverZero_rightHom n)
  apply hquot.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom
  rw [← S.range_inl_eq_ker_rightHom]
  exact (Set.finite_range S.inl).isDiscrete

/-- The projection from the compact real Spin group to the special orthogonal group is a covering
map. -/
theorem isCoveringMap_realCliffordSpinDoubleCoverZero_rightHom
    (n : ℕ) [NeZero n] [CompactSpace (realCliffordSpinGroupZero n)] :
    IsCoveringMap (realCliffordSpinDoubleCoverZero n).rightHom :=
  (isQuotientCoveringMap_realCliffordSpinDoubleCoverZero_rightHom n).isCoveringMap

/-- Continuous homomorphisms out of `SO(n)` are equivalent to continuous homomorphisms out of
compact `Spin(n)` that kill the kernel of the double-cover projection. -/
noncomputable def realCliffordSpinHomEquivKer (n : ℕ) [NeZero n]
    [CompactSpace (realCliffordSpinGroupZero n)]
    {H : Type*} [Monoid H] [TopologicalSpace H] :
    (QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0) →ₜ* H) ≃
      {f : realCliffordSpinGroupZero n →ₜ* H //
        (realCliffordSpinDoubleCoverZero n).rightHom.ker ≤
          (f : realCliffordSpinGroupZero n →* H).ker} := by
  simpa only [coeMonoidHom_realCliffordSpinProjectionZero] using
    ContinuousMonoidHom.homEquivOfIsQuotientMap (realCliffordSpinProjectionZero n) <| by
      rw [coe_realCliffordSpinProjectionZero]
      exact
        (isQuotientCoveringMap_realCliffordSpinDoubleCoverZero_rightHom n).toIsQuotientMap

/-- The compact Spin correspondence sends a homomorphism on `SO(n)` to its composition with the
Spin projection. -/
@[simp]
theorem realCliffordSpinHomEquivKer_apply_coe (n : ℕ) [NeZero n]
    [CompactSpace (realCliffordSpinGroupZero n)]
    {H : Type*} [Monoid H] [TopologicalSpace H]
    (f : QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0) →ₜ* H) :
    ((realCliffordSpinHomEquivKer n f :
      {g : realCliffordSpinGroupZero n →ₜ* H //
        (realCliffordSpinDoubleCoverZero n).rightHom.ker ≤
          (g : realCliffordSpinGroupZero n →* H).ker}) :
      realCliffordSpinGroupZero n →ₜ* H) =
        f.comp (realCliffordSpinProjectionZero n) := by
  rw [realCliffordSpinHomEquivKer]
  exact ContinuousMonoidHom.homEquivOfIsQuotientMap_apply_coe _ _ f

/-- Descending a homomorphism from compact `Spin(n)` and composing again with the Spin projection
recovers the original homomorphism. -/
@[simp]
theorem realCliffordSpinHomEquivKer_symm_apply_comp (n : ℕ) [NeZero n]
    [CompactSpace (realCliffordSpinGroupZero n)]
    {H : Type*} [Monoid H] [TopologicalSpace H]
    (f : {g : realCliffordSpinGroupZero n →ₜ* H //
      (realCliffordSpinDoubleCoverZero n).rightHom.ker ≤
        (g : realCliffordSpinGroupZero n →* H).ker}) :
    ((realCliffordSpinHomEquivKer n).symm f).comp (realCliffordSpinProjectionZero n) = f.1 := by
  have h := congrArg Subtype.val ((realCliffordSpinHomEquivKer n).apply_symm_apply f)
  rw [realCliffordSpinHomEquivKer_apply_coe] at h
  exact h

end CliffordAlgebra
