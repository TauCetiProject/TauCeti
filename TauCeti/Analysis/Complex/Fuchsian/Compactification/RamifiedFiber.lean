/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Fiber

/-!
# Ramified interior fibres of Fuchsian quotient maps

For an inclusion `Δ ≤ Γ` of projective subgroups, the fibre of the induced compactified
quotient map over the orbit of an interior point `z` is canonically the orbit space of the
stabilizer of `z` in `Γ` acting on the cosets `Γ / Δ`.

This gives the exact point count for every interior fibre. At a free point the stabilizer action
is trivial and the count is the subgroup index. In general, stabilizer orbits record exactly which
cosets represent the same fibre point. Under the relevant geometric hypotheses, non-singleton
orbits describe the resulting ramification identifications.
-/

public noncomputable section

open MulAction UpperHalfPlane
open scoped MatrixGroups

namespace Subgroup

variable {Δ Γ : Subgroup PSL(2, ℝ)}

/-- The fibre of a compactified Fuchsian quotient map over the interior orbit of `z` is the
orbit space of the stabilizer of `z` acting on the subgroup cosets. -/
noncomputable def stabilizerOrbitQuotientEquivCompactifiedFiber (h : Δ ≤ Γ) (z : ℍ) :
    orbitRel.Quotient (stabilizer Γ z) (Γ ⧸ Δ.subgroupOf Γ) ≃
      {y : Δ.CompactifiedQuotient //
        compactifiedQuotientMap h y = .ofQuotient (Quotient.mk'' z)} :=
  (TauCeti.stabilizerOrbitQuotientEquivOrbitRelMapFiber h z).trans
    (orbitFiberEquivCompactifiedFiber h (Quotient.mk'' z))

/-- The stabilizer-orbit equivalence sends the orbit of a coset to the compactified point
represented by the corresponding inverse translate of `z`. -/
@[simp]
theorem stabilizerOrbitQuotientEquivCompactifiedFiber_mk (h : Δ ≤ Γ) (z : ℍ)
    (q : Γ ⧸ Δ.subgroupOf Γ) :
    (stabilizerOrbitQuotientEquivCompactifiedFiber h z (Quotient.mk'' q)).1 =
      .ofQuotient (TauCeti.orbitOfCosetTranslate z q) :=
  by simp [stabilizerOrbitQuotientEquivCompactifiedFiber]

/-- The cardinality of a compactified interior fibre is the number of stabilizer-orbits on
the subgroup coset space. In particular, this counts elliptic fibres without treating the
quotient map as a covering at a ramified point. -/
theorem card_fiber_compactifiedQuotientMap_eq_card_stabilizerOrbitQuotient
    (h : Δ ≤ Γ) (z : ℍ) :
    Nat.card {y : Δ.CompactifiedQuotient //
      compactifiedQuotientMap h y = .ofQuotient (Quotient.mk'' z)} =
      Nat.card (orbitRel.Quotient (stabilizer Γ z) (Γ ⧸ Δ.subgroupOf Γ)) :=
  Nat.card_congr (stabilizerOrbitQuotientEquivCompactifiedFiber h z).symm

end Subgroup
