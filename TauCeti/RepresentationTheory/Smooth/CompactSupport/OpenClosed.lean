/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.CompactSupport
public import TauCeti.Topology.LocallyConstant.CompactSupport.OpenClosed

/-!
# The equivariant open-closed exact sequence

Let a group `G` act on a Hausdorff space `X` by homeomorphisms, and let `U` be a `G`-stable open
subset, given as a `SubMulAction G X` whose carrier is open. Its complement `Z = X ∖ U` is
`G`-stable and closed (Mathlib's `SubMulAction` complement). Then `G` acts by translation on
`C_c^∞(U, M)`, `C_c^∞(X, M)` and `C_c^∞(Z, M)` (`TauCeti.compactlySupportedRep`), and extension by
zero `C_c^∞(U, M) → C_c^∞(X, M)` and restriction `C_c^∞(X, M) → C_c^∞(Z, M)`
(`LocallyConstant.compactlySupported.extendByZero`, `LocallyConstant.compactlySupported.restrict`)
are intertwining maps. Together with the exactness of the underlying sequence, proved in
`TauCeti.Topology.LocallyConstant.CompactSupport.OpenClosed`, this is the open-closed exact
sequence as a sequence of representations, and for a jointly continuous action of a topological
group all three representations are smooth (`TauCeti.isSmooth_compactlySupportedRep`, applied to
the `G`-spaces `U` and `Z`).

## Main definitions

* `TauCeti.compactlySupportedExtendByZero`: extension by zero from a `G`-stable open subset, as an
  intertwining map.
* `TauCeti.compactlySupportedRestrict`: restriction to a `G`-stable closed subset, as an
  intertwining map.

## Main results

* `TauCeti.compactlySupportedExtendByZero_injective`,
  `TauCeti.exact_compactlySupportedExtendByZero_restrict` and
  `TauCeti.compactlySupportedRestrict_surjective`: the sequence
  `0 → C_c^∞(U, M) → C_c^∞(X, M) → C_c^∞(Uᶜ, M) → 0` of representations is exact, the last for an
  l-space `X`.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §1.2, Proposition 2, p. 8.
-/

public section

noncomputable section

open Function

namespace TauCeti

variable {R G X M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [Group G]
  [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]

/-- **Extension by zero is equivariant**: for a `G`-stable open subset `U` of a Hausdorff
`G`-space `X`, extension by zero `C_c^∞(U, M) → C_c^∞(X, M)` intertwines the translation
representations. -/
def compactlySupportedExtendByZero [T2Space X] (U : SubMulAction G X)
    (hU : IsOpen (U : Set X)) :
    (compactlySupportedRep R G U M).IntertwiningMap (compactlySupportedRep R G X M) where
  toLinearMap := LocallyConstant.compactlySupported.extendByZero R M hU
  isIntertwining' g := LinearMap.ext fun f ↦ LocallyConstant.compactlySupported.ext fun x ↦ by
    by_cases hx : x ∈ U
    · lift x to U using hx
      -- `extendByZero_apply_coe` is stated for a `Set`, so simp needs it instantiated at `hU`;
      -- `h` states its value at `g⁻¹ • x` with the simp-normal argument `g⁻¹ • ↑x`.
      have h := LocallyConstant.compactlySupported.extendByZero_apply_coe hU f (g⁻¹ • x)
      rw [SubMulAction.val_smul] at h
      simp [LocallyConstant.compactlySupported.extendByZero_apply_coe hU, h]
    · have hx' : g⁻¹ • x ∉ U := fun h ↦ hx (by simpa using U.smul_mem g h)
      simp [LocallyConstant.compactlySupported.extendByZero_apply_of_notMem hU, hx, hx']

@[simp]
theorem coe_compactlySupportedExtendByZero [T2Space X] (U : SubMulAction G X)
    (hU : IsOpen (U : Set X)) :
    ⇑(compactlySupportedExtendByZero (R := R) (M := M) U hU) =
      LocallyConstant.compactlySupported.extendByZero R M hU :=
  (rfl)

@[simp]
theorem toLinearMap_compactlySupportedExtendByZero [T2Space X] (U : SubMulAction G X)
    (hU : IsOpen (U : Set X)) :
    (compactlySupportedExtendByZero (R := R) (M := M) U hU).toLinearMap =
      LocallyConstant.compactlySupported.extendByZero R M hU :=
  (rfl)

/-- **Restriction is equivariant**: for a `G`-stable closed subset `Z` of a `G`-space `X`,
restriction `C_c^∞(X, M) → C_c^∞(Z, M)` intertwines the translation representations. -/
def compactlySupportedRestrict (Z : SubMulAction G X) (hZ : IsClosed (Z : Set X)) :
    (compactlySupportedRep R G X M).IntertwiningMap (compactlySupportedRep R G Z M) where
  toLinearMap := LocallyConstant.compactlySupported.restrict R M hZ
  isIntertwining' g := LinearMap.ext fun f ↦ LocallyConstant.compactlySupported.ext fun z ↦ by
    simp [LocallyConstant.compactlySupported.restrict_apply hZ]

@[simp]
theorem coe_compactlySupportedRestrict (Z : SubMulAction G X) (hZ : IsClosed (Z : Set X)) :
    ⇑(compactlySupportedRestrict (R := R) (M := M) Z hZ) =
      LocallyConstant.compactlySupported.restrict R M hZ :=
  (rfl)

@[simp]
theorem toLinearMap_compactlySupportedRestrict (Z : SubMulAction G X)
    (hZ : IsClosed (Z : Set X)) :
    (compactlySupportedRestrict (R := R) (M := M) Z hZ).toLinearMap =
      LocallyConstant.compactlySupported.restrict R M hZ :=
  (rfl)

/-- The equivariant open-closed sequence is exact at `C_c^∞(U, M)`. -/
theorem compactlySupportedExtendByZero_injective [T2Space X] (U : SubMulAction G X)
    (hU : IsOpen (U : Set X)) :
    Injective (compactlySupportedExtendByZero (R := R) (M := M) U hU) := by
  rw [coe_compactlySupportedExtendByZero]
  exact LocallyConstant.compactlySupported.extendByZero_injective hU

/-- **The equivariant open-closed exact sequence**, exactness at `C_c^∞(X, M)`: for a `G`-stable
open subset `U` of a Hausdorff `G`-space `X`, the kernel of restriction to the complement `Uᶜ` is
the image of extension by zero. -/
theorem exact_compactlySupportedExtendByZero_restrict [T2Space X] (U : SubMulAction G X)
    (hU : IsOpen (U : Set X)) :
    Exact (compactlySupportedExtendByZero (R := R) (M := M) U hU)
      (compactlySupportedRestrict (R := R) (M := M) Uᶜ hU.isClosed_compl) := by
  rw [coe_compactlySupportedExtendByZero, coe_compactlySupportedRestrict]
  exact LocallyConstant.compactlySupported.exact_extendByZero_restrict hU

/-- The equivariant open-closed sequence is exact at `C_c^∞(Z, M)` when `X` is an l-space. -/
theorem compactlySupportedRestrict_surjective [T2Space X] [WeaklyLocallyCompactSpace X]
    [TotallyDisconnectedSpace X] (Z : SubMulAction G X) (hZ : IsClosed (Z : Set X)) :
    Surjective (compactlySupportedRestrict (R := R) (M := M) Z hZ) := by
  rw [coe_compactlySupportedRestrict]
  exact LocallyConstant.compactlySupported.restrict_surjective hZ

end TauCeti
