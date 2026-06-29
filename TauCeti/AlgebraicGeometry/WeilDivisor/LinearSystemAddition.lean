/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.LinearSystem
import Mathlib.Tactic.Abel

/-!
# Addition in complete linear systems of Weil divisors

This file adds the additive calculus for the complete linear systems defined in
`TauCeti.AlgebraicGeometry.WeilDivisor.LinearSystem`.

For an order system `S`, linear equivalence is compatible with addition of divisors. Hence
members of complete linear systems add:

`E ∈ |D|`, `F ∈ |D'|` imply `E + F ∈ |D + D'|`.

The finite-sum version is the formal divisor bookkeeping used before symmetric powers and Abel
maps are available: a finite collection of effective representatives in divisor classes adds to
an effective representative in the sum class. The file also records that translating the
indexing divisor of a complete linear system by a principal divisor does not change the system.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, "Divisors on a curve" and
"Degree", by extending the existing abstract complete-linear-system API needed before the
scheme-theoretic symmetric-power and Abel-map layers. No external mathematics is vendored; the
proofs use Tau Ceti's `WeilDivisor`/`OrderSystem` API and Mathlib's additive subgroup and
finite-sum lemmas.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

namespace OrderSystem

variable {X G ι : Type*} [AddCommGroup G] (S : OrderSystem X G)

/-! ### Linear equivalence and addition -/

variable {D D' E E' F : WeilDivisor X}

/-- Linear equivalence is compatible with adding equivalent divisors on both sides. -/
lemma LinearlyEquivalent.add (hD : S.LinearlyEquivalent D D')
    (hE : S.LinearlyEquivalent E E') : S.LinearlyEquivalent (D + E) (D' + E') := by
  rw [linearlyEquivalent_iff] at hD hE ⊢
  have hsum := S.principalSubgroup.add_mem hD hE
  convert hsum using 1
  abel

/-- Adding the same divisor on the right preserves linear equivalence. -/
lemma LinearlyEquivalent.add_right (hD : S.LinearlyEquivalent D D') (E : WeilDivisor X) :
    S.LinearlyEquivalent (D + E) (D' + E) :=
  LinearlyEquivalent.add S hD (LinearlyEquivalent.refl S E)

/-- Adding the same divisor on the left preserves linear equivalence. -/
lemma LinearlyEquivalent.add_left (hE : S.LinearlyEquivalent E E') (D : WeilDivisor X) :
    S.LinearlyEquivalent (D + E) (D + E') :=
  LinearlyEquivalent.add S (LinearlyEquivalent.refl S D) hE

/-- A divisor plus a principal divisor is linearly equivalent to the original divisor. -/
lemma linearlyEquivalent_add_principalDivisor (D : WeilDivisor X) (g : G) :
    S.LinearlyEquivalent (D + S.principalDivisor g) D := by
  rw [linearlyEquivalent_iff]
  convert S.principalDivisor_mem_principalSubgroup g using 1
  abel

/-- Subtracting a principal divisor from a divisor is linearly equivalent to the original
divisor. -/
lemma linearlyEquivalent_sub_principalDivisor (D : WeilDivisor X) (g : G) :
    S.LinearlyEquivalent (D - S.principalDivisor g) D := by
  rw [linearlyEquivalent_iff]
  convert S.principalDivisor_mem_principalSubgroup (-g) using 1
  rw [S.principalDivisor_neg]
  abel

/-! ### Addition of complete linear systems -/

/-- Members of complete linear systems add to a member of the complete linear system of the sum
class. -/
lemma add_mem_completeLinearSystem {D D' E E' : WeilDivisor X}
    (hE : E ∈ S.completeLinearSystem D) (hE' : E' ∈ S.completeLinearSystem D') :
    E + E' ∈ S.completeLinearSystem (D + D') := by
  rw [mem_completeLinearSystem] at hE hE' ⊢
  exact ⟨hE.1.add hE'.1, LinearlyEquivalent.add S hE.2 hE'.2⟩

/-- Right addition by a fixed member of `|D'|` sends `|D|` into `|D + D'|`. -/
lemma add_mem_completeLinearSystem_right {D D' E E' : WeilDivisor X}
    (hE : E ∈ S.completeLinearSystem D) :
    E' ∈ S.completeLinearSystem D' → E + E' ∈ S.completeLinearSystem (D + D') :=
  S.add_mem_completeLinearSystem hE

/-- Left addition by a fixed member of `|D|` sends `|D'|` into `|D + D'|`. -/
lemma add_mem_completeLinearSystem_left {D D' E E' : WeilDivisor X}
    (hE' : E' ∈ S.completeLinearSystem D') :
    E ∈ S.completeLinearSystem D → E + E' ∈ S.completeLinearSystem (D + D') :=
  fun hE => S.add_mem_completeLinearSystem hE hE'

/-- If two complete linear systems are nonempty, then the complete linear system of the sum of
their divisor classes is nonempty. -/
lemma nonempty_completeLinearSystem_add {D D' : WeilDivisor X}
    (hD : (S.completeLinearSystem D).Nonempty)
    (hD' : (S.completeLinearSystem D').Nonempty) :
    (S.completeLinearSystem (D + D')).Nonempty := by
  rcases hD with ⟨E, hE⟩
  rcases hD' with ⟨E', hE'⟩
  exact ⟨E + E', S.add_mem_completeLinearSystem hE hE'⟩

/-- A finite sum of members of complete linear systems is a member of the complete linear system
of the finite sum of the indexing divisors. -/
lemma sum_mem_completeLinearSystem (s : Finset ι) {D E : ι → WeilDivisor X}
    (h : ∀ i ∈ s, E i ∈ S.completeLinearSystem (D i)) :
    (∑ i ∈ s, E i) ∈ S.completeLinearSystem (∑ i ∈ s, D i) := by
  classical
  rw [S.mem_completeLinearSystem_iff_divisorClass]
  refine ⟨?_, ?_⟩
  · rw [isEffective_iff]
    intro x
    change 0 ≤ (∑ i ∈ s, E i) x
    rw [Finset.sum_apply']
    exact Finset.sum_nonneg fun i hi =>
      (isEffective_iff (E i)).mp (S.isEffective_of_mem_completeLinearSystem (h i hi)) x
  · rw [map_sum, map_sum]
    exact Finset.sum_congr rfl fun i hi =>
      (S.mem_completeLinearSystem_iff_divisorClass.mp (h i hi)).2

/-! ### Principal translates -/

/-- Adding a principal divisor to the indexing divisor does not change the complete linear
system. -/
lemma completeLinearSystem_add_principalDivisor_eq (D : WeilDivisor X) (g : G) :
    S.completeLinearSystem (D + S.principalDivisor g) = S.completeLinearSystem D :=
  S.completeLinearSystem_eq_of_linearlyEquivalent (S.linearlyEquivalent_add_principalDivisor D g)

/-- Subtracting a principal divisor from the indexing divisor does not change the complete
linear system. -/
lemma completeLinearSystem_sub_principalDivisor_eq (D : WeilDivisor X) (g : G) :
    S.completeLinearSystem (D - S.principalDivisor g) = S.completeLinearSystem D :=
  S.completeLinearSystem_eq_of_linearlyEquivalent (S.linearlyEquivalent_sub_principalDivisor D g)

/-- An effective principal translate of `D` is a member of the complete linear system `|D|`. -/
lemma add_principalDivisor_mem_completeLinearSystem (D : WeilDivisor X) (g : G)
    (hEff : IsEffective (D + S.principalDivisor g)) :
    D + S.principalDivisor g ∈ S.completeLinearSystem D := by
  rw [← S.completeLinearSystem_add_principalDivisor_eq D g]
  exact S.self_mem_completeLinearSystem hEff

/-- An effective negative principal translate of `D` is a member of the complete linear system
`|D|`. -/
lemma sub_principalDivisor_mem_completeLinearSystem (D : WeilDivisor X) (g : G)
    (hEff : IsEffective (D - S.principalDivisor g)) :
    D - S.principalDivisor g ∈ S.completeLinearSystem D := by
  rw [← S.completeLinearSystem_sub_principalDivisor_eq D g]
  exact S.self_mem_completeLinearSystem hEff

end OrderSystem

end WeilDivisor

end AlgebraicGeometry

end TauCeti
