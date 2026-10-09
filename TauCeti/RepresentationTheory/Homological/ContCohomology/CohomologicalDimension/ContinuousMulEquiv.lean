/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.Basic
import TauCeti.RepresentationTheory.Homological.ContCohomology.Additive

/-!
# Cohomological dimension is invariant under topological group isomorphisms

For an isomorphism of topological groups `e : G ≃ₜ* H`, the `p`-cohomological dimensions of `G`
and `H` agree (`TauCeti.cohomologicalDimensionAt_congr`), and so do the strict ones
(`TauCeti.strictCohomologicalDimensionAt_congr`). A discrete `G`-module `M` becomes one over `H`
by letting `h` act as `e⁻¹ h`, and the map `Hⁱ(H, M) → Hⁱ(G, M)` along `e` and the identity of `M`
is bijective (`map_ofDiscreteModulePair_bijective_of_continuousMulEquiv`); so vanishing of
`Hⁱ(H, M)`, or of its `p`-primary component, transfers to `Hⁱ(G, M)`.

This is how the cohomological dimension of an absolute Galois group is read on either of its two
models, Mathlib's `Field.absoluteGaloisGroup F` of an algebraic closure and Tau Ceti's
`TauCeti.AbsoluteGaloisGroup F` of a separable closure, which are isomorphic as topological groups
by `TauCeti.absoluteGaloisGroupRestrictEquiv`.

## Main results

* `TauCeti.CohomologicalDimensionLE.of_continuousMulEquiv`: the vanishing predicate transfers
  along a topological group isomorphism.
* `TauCeti.cohomologicalDimensionAt_le_of_continuousMulEquiv`: `cd_p G ≤ cd_p H` for `G ≃ₜ* H`.
* `TauCeti.cohomologicalDimensionAt_congr`: **`cd_p G = cd_p H`** for `G ≃ₜ* H`.
* `TauCeti.StrictCohomologicalDimensionLE.of_continuousMulEquiv`,
  `TauCeti.strictCohomologicalDimensionAt_le_of_continuousMulEquiv` and
  `TauCeti.strictCohomologicalDimensionAt_congr`: the same for the strict `p`-cohomological
  dimension, **`scd_p G = scd_p H`** for `G ≃ₜ* H`.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §3.
-/

public section

namespace TauCeti

open CategoryTheory _root_.TauCeti.ContinuousCohomology

universe u v

variable {p : ℕ} {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- **The vanishing predicate transfers along a topological group isomorphism**: for
`e : G ≃ₜ* H`, `CohomologicalDimensionLE p H n` implies `CohomologicalDimensionLE p G n`. -/
theorem CohomologicalDimensionLE.of_continuousMulEquiv (e : G ≃ₜ* H) {n : ℕ}
    (h : CohomologicalDimensionLE.{v} p H n) : CohomologicalDimensionLE.{v} p G n := by
  rw [cohomologicalDimensionLE_iff] at h ⊢
  intro M _ _ _ _ _ hM i hi
  let : DistribMulAction H M := DistribMulAction.compHom M (e.symm : H →* G)
  have : ContinuousSMul H M := ⟨(continuous_smul (M := G) (X := M)).comp
    ((e.symm.continuous.comp continuous_fst).prodMk continuous_snd)⟩
  have := h M hM i hi
  refine subsingleton_continuousCohomology_ofDiscreteModule_of_continuousMulEquiv e
    (LinearEquiv.refl ℤ M) (fun g m => ?_) i
  simp [MulAction.compHom_smul_def]

/-- **`cd_p G ≤ cd_p H` for `G ≃ₜ* H`.** -/
theorem cohomologicalDimensionAt_le_of_continuousMulEquiv (e : G ≃ₜ* H) :
    cohomologicalDimensionAt.{v} p G ≤ cohomologicalDimensionAt.{v} p H := by
  induction hcd : cohomologicalDimensionAt.{v} p H using ENat.recTopCoe with
  | top => exact le_top
  | coe n =>
    exact (cohomologicalDimensionAt_le_iff p G n).2
      (((cohomologicalDimensionAt_le_iff p H n).1 hcd.le).of_continuousMulEquiv e)

/-- **The `p`-cohomological dimension is invariant under topological group isomorphisms**:
`cd_p G = cd_p H` for `G ≃ₜ* H`. -/
theorem cohomologicalDimensionAt_congr (e : G ≃ₜ* H) :
    cohomologicalDimensionAt.{v} p G = cohomologicalDimensionAt.{v} p H :=
  (cohomologicalDimensionAt_le_of_continuousMulEquiv e).antisymm
    (cohomologicalDimensionAt_le_of_continuousMulEquiv e.symm)

/-- **The strict vanishing predicate transfers along a topological group isomorphism**: for
`e : G ≃ₜ* H`, `StrictCohomologicalDimensionLE p H n` implies
`StrictCohomologicalDimensionLE p G n`. -/
theorem StrictCohomologicalDimensionLE.of_continuousMulEquiv (e : G ≃ₜ* H) {n : ℕ}
    (h : StrictCohomologicalDimensionLE.{v} p H n) : StrictCohomologicalDimensionLE.{v} p G n := by
  rw [strictCohomologicalDimensionLE_iff] at h ⊢
  intro M _ _ _ _ _ i hi
  let : DistribMulAction H M := DistribMulAction.compHom M (e.symm : H →* G)
  have : ContinuousSMul H M := ⟨(continuous_smul (M := G) (X := M)).comp
    ((e.symm.continuous.comp continuous_fst).prodMk continuous_snd)⟩
  -- the map `Hⁱ(H, M) → Hⁱ(G, M)` along `e` and the identity of `M` is an additive bijection
  have hF := map_ofDiscreteModulePair_bijective_of_continuousMulEquiv e (LinearEquiv.refl ℤ M)
    (fun g m => by
      rw [LinearEquiv.refl_apply, LinearEquiv.refl_apply, MulAction.compHom_smul_def]
      simp) i
  refine (AddSubgroup.eq_bot_iff_forall _).2 fun x ⟨k, hk⟩ => ?_
  obtain ⟨y, rfl⟩ := hF.2 x
  have hy : y ∈ AddCommGroup.primaryComponent
      (continuousCohomology i (ofDiscreteModule ℤ H M)) p :=
    ⟨k, hF.1 (by rw [_root_.map_nsmul, hk, _root_.map_zero])⟩
  rw [h M i hi, AddSubgroup.mem_bot] at hy
  rw [hy, _root_.map_zero]

/-- **`scd_p G ≤ scd_p H` for `G ≃ₜ* H`.** -/
theorem strictCohomologicalDimensionAt_le_of_continuousMulEquiv (e : G ≃ₜ* H) :
    strictCohomologicalDimensionAt.{v} p G ≤ strictCohomologicalDimensionAt.{v} p H := by
  induction hcd : strictCohomologicalDimensionAt.{v} p H using ENat.recTopCoe with
  | top => exact le_top
  | coe n =>
    exact (strictCohomologicalDimensionAt_le_iff p G n).2
      (((strictCohomologicalDimensionAt_le_iff p H n).1 hcd.le).of_continuousMulEquiv e)

/-- **The strict `p`-cohomological dimension is invariant under topological group
isomorphisms**: `scd_p G = scd_p H` for `G ≃ₜ* H`. -/
theorem strictCohomologicalDimensionAt_congr (e : G ≃ₜ* H) :
    strictCohomologicalDimensionAt.{v} p G = strictCohomologicalDimensionAt.{v} p H :=
  (strictCohomologicalDimensionAt_le_of_continuousMulEquiv e).antisymm
    (strictCohomologicalDimensionAt_le_of_continuousMulEquiv e.symm)

end TauCeti
