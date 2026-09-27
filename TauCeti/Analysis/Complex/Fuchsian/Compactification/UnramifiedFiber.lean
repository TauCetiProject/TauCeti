/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Fiber

/-!
# Fibres over free points of Fuchsian quotient maps

At a point of the upper half-plane with trivial stabilizer in the larger group, the fibre of
an induced map of compactified quotients has exactly the subgroup index many points. Such
fibres give the unramified count used in the global degree formula. For an infinite index,
both sides of the cardinality theorem are zero by Mathlib's `Nat.card` and subgroup-index
conventions. The group-theoretic coset equivalence is in
`TauCeti.GroupTheory.DoubleCoset.Fiber`.
-/

public noncomputable section

open MulAction UpperHalfPlane
open scoped MatrixGroups

namespace Subgroup

variable {Δ Γ : Subgroup PSL(2, ℝ)}

/-- Over an interior point, the compactified fibre is the corresponding fibre of the map
on ordinary orbit spaces. -/
def compactifiedFiberEquivOrbitFiber (h : Δ ≤ Γ) (p : orbitRel.Quotient Γ ℍ) :
    {q : orbitRel.Quotient Δ ℍ //
      Setoid.map_of_le (TauCeti.MulAction.orbitRel_le_of_subgroup_le (X := ℍ) h) q = p} ≃
    {y : Δ.CompactifiedQuotient //
      compactifiedQuotientMap h y = .ofQuotient p} where
  toFun q := ⟨CompactifiedQuotient.ofQuotient q.1, by
    simpa only [compactifiedQuotientMap_ofQuotient] using
      congrArg CompactifiedQuotient.ofQuotient q.2
  ⟩
  invFun y := by
    obtain ⟨y, hy⟩ := y
    cases y with
    | ofQuotient p =>
        simp only [compactifiedQuotientMap_ofQuotient] at hy
        exact ⟨p, CompactifiedQuotient.ofQuotient.inj hy⟩
    | ofCusp C =>
        simp only [compactifiedQuotientMap_ofCusp] at hy
        cases hy
  left_inv q := by cases q; rfl
  right_inv y := by
    obtain ⟨y, hy⟩ := y
    cases y with
    | ofQuotient p => rfl
    | ofCusp C =>
        simp only [compactifiedQuotientMap_ofCusp] at hy
        cases hy

/-- The interior-fibre equivalence inserts an ordinary orbit into the compactification. -/
@[simp]
theorem compactifiedFiberEquivOrbitFiber_apply (h : Δ ≤ Γ)
    (p : orbitRel.Quotient Γ ℍ)
    (q : {q : orbitRel.Quotient Δ ℍ //
      Setoid.map_of_le (TauCeti.MulAction.orbitRel_le_of_subgroup_le (X := ℍ) h) q = p}) :
    (compactifiedFiberEquivOrbitFiber h p q).1 = .ofQuotient q.1 :=
  (rfl)

/-- The fibre of the compactified quotient map over a free interior point has cardinality
`[Γ : Δ]`. -/
theorem card_fiber_compactifiedQuotientMap_of_stabilizer_eq_bot (h : Δ ≤ Γ)
    (z : ℍ) (hz : stabilizer Γ z = ⊥) :
    Nat.card {y : Δ.CompactifiedQuotient //
      compactifiedQuotientMap h y = .ofQuotient (Quotient.mk'' z)} =
      (Δ.subgroupOf Γ).index := by
  rw [← Nat.card_congr (compactifiedFiberEquivOrbitFiber h (Quotient.mk'' z))]
  exact TauCeti.card_fiber_orbitRel_map_of_stabilizer_eq_bot h z hz

end Subgroup
