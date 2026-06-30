/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.LinearSystemAddition
public import TauCeti.AlgebraicGeometry.WeilDivisor.FiniteSum
public import TauCeti.AlgebraicGeometry.WeilDivisor.Order
import Mathlib.Tactic.Abel

/-!
# Effective monotonicity of complete linear systems

This file records the elementary monotonicity calculus for complete linear systems of Weil
divisors.  If `A` is effective, then adding `A` sends `|D|` into `|D + A|`.  Equivalently, if
`D ≤ D'` coefficientwise, then adding the effective difference `D' - D` sends `|D|` into
`|D'|`; in particular nonemptiness of complete linear systems is monotone under the divisor
order.

This is the divisor-level bookkeeping behind the later symmetric-power and Abel-map lane in
the Jacobian roadmap: increasing an effective divisor by fixed effective base conditions
should not destroy the existence of effective representatives.  It advances
`TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, "Divisors on a curve" and "Degree", as
a clean prerequisite for the Layer C/D Abel-map construction from symmetric powers.  No
external mathematics is vendored; the proofs reuse Tau Ceti's existing complete-linear-system
addition API and the coefficientwise order on formal Weil divisors.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

namespace OrderSystem

variable {X G : Type*} [AddCommGroup G] (S : OrderSystem X G)

/-! ### Adding an effective divisor -/

/-- Adding an effective divisor to a member of `|D|` gives a member of `|D + A|`. -/
lemma add_effective_mem_completeLinearSystem {D E A : WeilDivisor X}
    (hE : E ∈ S.completeLinearSystem D) (hA : IsEffective A) :
    E + A ∈ S.completeLinearSystem (D + A) :=
  S.add_mem_completeLinearSystem hE (S.self_mem_completeLinearSystem hA)

/-- Left-adding an effective divisor to a member of `|D|` gives a member of `|A + D|`. -/
lemma effective_add_mem_completeLinearSystem {D E A : WeilDivisor X}
    (hA : IsEffective A) (hE : E ∈ S.completeLinearSystem D) :
    A + E ∈ S.completeLinearSystem (A + D) :=
  S.add_mem_completeLinearSystem (S.self_mem_completeLinearSystem hA) hE

/-- Right translation by an effective divisor maps `|D|` into `|D + A|`. -/
lemma mapsTo_add_effective_completeLinearSystem (D A : WeilDivisor X) (hA : IsEffective A) :
    Set.MapsTo (fun E => E + A) (S.completeLinearSystem D) (S.completeLinearSystem (D + A)) :=
  fun _ hE => S.add_effective_mem_completeLinearSystem hE hA

/-- Left translation by an effective divisor maps `|D|` into `|A + D|`. -/
lemma mapsTo_effective_add_completeLinearSystem (D A : WeilDivisor X) (hA : IsEffective A) :
    Set.MapsTo (fun E => A + E) (S.completeLinearSystem D) (S.completeLinearSystem (A + D)) :=
  fun _ hE => S.effective_add_mem_completeLinearSystem hA hE

/-- Adding an effective divisor preserves nonemptiness of complete linear systems. -/
lemma nonempty_completeLinearSystem_add_effective {D A : WeilDivisor X}
    (hA : IsEffective A) (hD : (S.completeLinearSystem D).Nonempty) :
    (S.completeLinearSystem (D + A)).Nonempty := by
  rcases hD with ⟨E, hE⟩
  exact ⟨E + A, S.add_effective_mem_completeLinearSystem hE hA⟩

/-- Left-adding an effective divisor preserves nonemptiness of complete linear systems. -/
lemma nonempty_completeLinearSystem_effective_add {D A : WeilDivisor X}
    (hA : IsEffective A) (hD : (S.completeLinearSystem D).Nonempty) :
    (S.completeLinearSystem (A + D)).Nonempty := by
  rcases hD with ⟨E, hE⟩
  exact ⟨A + E, S.effective_add_mem_completeLinearSystem hA hE⟩

/-! ### Monotonicity for the divisor order -/

/-- If `D ≤ D'`, then translating a member of `|D|` by the effective difference `D' - D`
gives a member of `|D'|`. -/
lemma add_sub_mem_completeLinearSystem_of_le {D D' E : WeilDivisor X} (hDD' : D ≤ D')
    (hE : E ∈ S.completeLinearSystem D) :
    E + (D' - D) ∈ S.completeLinearSystem D' := by
  have hdiff : IsEffective (D' - D) := le_iff_isEffective_sub.mp hDD'
  have hmem : E + (D' - D) ∈ S.completeLinearSystem (D + (D' - D)) :=
    S.add_effective_mem_completeLinearSystem hE hdiff
  convert hmem using 2
  abel

/-- The order-induced translation map sends `|D|` into `|D'|` whenever `D ≤ D'`. -/
lemma mapsTo_add_sub_completeLinearSystem_of_le {D D' : WeilDivisor X} (hDD' : D ≤ D') :
    Set.MapsTo (fun E => E + (D' - D)) (S.completeLinearSystem D)
      (S.completeLinearSystem D') :=
  fun _ hE => S.add_sub_mem_completeLinearSystem_of_le hDD' hE

/-- Nonemptiness of complete linear systems is monotone for the divisor order. -/
lemma nonempty_completeLinearSystem_of_le {D D' : WeilDivisor X} (hDD' : D ≤ D')
    (hD : (S.completeLinearSystem D).Nonempty) :
    (S.completeLinearSystem D').Nonempty := by
  rcases hD with ⟨E, hE⟩
  exact ⟨E + (D' - D), S.add_sub_mem_completeLinearSystem_of_le hDD' hE⟩

/-- If `D ≤ D'` and `E ∈ |D|`, then the divisor `E + D' - D` is an effective representative
of the class of `D'`. -/
lemma add_sub_mem_completeLinearSystem_of_le' {D D' E : WeilDivisor X} (hDD' : D ≤ D')
    (hE : E ∈ S.completeLinearSystem D) :
    E + D' - D ∈ S.completeLinearSystem D' := by
  convert S.add_sub_mem_completeLinearSystem_of_le hDD' hE using 1
  abel

/-! ### Point and finite effective translates -/

/-- Adding a point divisor sends `|D|` into `|D + [x]|`. -/
lemma add_ofPoint_mem_completeLinearSystem {D E : WeilDivisor X}
    (hE : E ∈ S.completeLinearSystem D) (x : X) :
    E + ofPoint x ∈ S.completeLinearSystem (D + ofPoint x) :=
  S.add_effective_mem_completeLinearSystem hE (isEffective_ofPoint x)

/-- If `|D|` is nonempty, then `|D + [x]|` is nonempty. -/
lemma nonempty_completeLinearSystem_add_ofPoint {D : WeilDivisor X}
    (hD : (S.completeLinearSystem D).Nonempty) (x : X) :
    (S.completeLinearSystem (D + ofPoint x)).Nonempty :=
  S.nonempty_completeLinearSystem_add_effective (isEffective_ofPoint x) hD

/-! ### Finite effective translates -/

/-- Adding a divisor from finitely supported natural multiplicities sends `|D|` into
`|D + Σ mₓ[x]|`. -/
lemma add_ofFinsupp_mem_completeLinearSystem {D E : WeilDivisor X}
    (hE : E ∈ S.completeLinearSystem D) (m : X →₀ ℕ) :
    E + ofFinsupp m ∈ S.completeLinearSystem (D + ofFinsupp m) :=
  S.add_effective_mem_completeLinearSystem hE (isEffective_ofFinsupp m)

/-- Nonemptiness of `|D|` implies nonemptiness after adding a finitely supported effective
divisor. -/
lemma nonempty_completeLinearSystem_add_ofFinsupp {D : WeilDivisor X}
    (hD : (S.completeLinearSystem D).Nonempty) (m : X →₀ ℕ) :
    (S.completeLinearSystem (D + ofFinsupp m)).Nonempty :=
  S.nonempty_completeLinearSystem_add_effective (isEffective_ofFinsupp m) hD

/-- Adding a finite-set divisor with multiplicities sends `|D|` into
`|D + Σ x ∈ s, m x [x]|`. -/
lemma add_ofFinsetWithMultiplicity_mem_completeLinearSystem {D E : WeilDivisor X}
    (hE : E ∈ S.completeLinearSystem D) (s : Finset X) (m : X → ℕ) :
    E + ofFinsetWithMultiplicity s m ∈
      S.completeLinearSystem (D + ofFinsetWithMultiplicity s m) :=
  S.add_effective_mem_completeLinearSystem hE (isEffective_ofFinsetWithMultiplicity s m)

/-- Nonemptiness of `|D|` implies nonemptiness after adding a finite-set divisor with
multiplicities. -/
lemma nonempty_completeLinearSystem_add_ofFinsetWithMultiplicity {D : WeilDivisor X}
    (hD : (S.completeLinearSystem D).Nonempty) (s : Finset X) (m : X → ℕ) :
    (S.completeLinearSystem (D + ofFinsetWithMultiplicity s m)).Nonempty :=
  S.nonempty_completeLinearSystem_add_effective (isEffective_ofFinsetWithMultiplicity s m) hD

/-- Adding a coefficient-one finite-set divisor sends `|D|` into `|D + Σ x ∈ s, [x]|`. -/
lemma add_ofFinset_mem_completeLinearSystem {D E : WeilDivisor X}
    (hE : E ∈ S.completeLinearSystem D) (s : Finset X) :
    E + ofFinset s ∈ S.completeLinearSystem (D + ofFinset s) :=
  S.add_effective_mem_completeLinearSystem hE (isEffective_ofFinset s)

/-- Nonemptiness of `|D|` implies nonemptiness after adding a coefficient-one finite-set
divisor. -/
lemma nonempty_completeLinearSystem_add_ofFinset {D : WeilDivisor X}
    (hD : (S.completeLinearSystem D).Nonempty) (s : Finset X) :
    (S.completeLinearSystem (D + ofFinset s)).Nonempty :=
  S.nonempty_completeLinearSystem_add_effective (isEffective_ofFinset s) hD

end OrderSystem

end WeilDivisor

end AlgebraicGeometry

end TauCeti
