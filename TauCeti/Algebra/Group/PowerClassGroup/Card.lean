/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorization.Defs
public import TauCeti.Algebra.Group.PowerClassGroup.Basic
import Mathlib.GroupTheory.Sylow

/-!
# The order of the `p`-power classes of a finite commutative group

Let `G` be a finite commutative group and `p` a prime. Once `p ^ m` contains the full power of `p`
dividing `#G`, the `p ^ m`-th power map kills exactly the Sylow `p`-subgroup of `G`, so the power
class group `G ⧸ G^(p^m)` has the order of that Sylow subgroup. It is the maximal `p`-quotient of
`G`, and it no longer depends on `m`.

## Main results

* `TauCeti.natCard_powerClassQuotient_prime_pow`: `#(G ⧸ G^(p^m)) = p ^ v_p(#G)` whenever
  `v_p(#G) ≤ m`.
-/

public section

namespace TauCeti

/-- **The `p`-power classes of a finite commutative group.** If `p ^ m` contains the full power
of `p` dividing `#G`, then `G ⧸ G^(p^m)` has order that power of `p`, the order of a Sylow
`p`-subgroup of `G`. -/
theorem natCard_powerClassQuotient_prime_pow (G : Type*) [CommGroup G] [Finite G] {p : ℕ}
    [Fact p.Prime] {m : ℕ} (hm : (Nat.card G).factorization p ≤ m) :
    Nat.card (powerClassQuotient G (p ^ m)) = p ^ (Nat.card G).factorization p := by
  rw [← Subgroup.index, powerSubgroup_eq_range_powMonoidHom, Subgroup.index_range]
  -- The kernel of the `p ^ m`-th power map is a `p`-group containing a Sylow `p`-subgroup.
  have hker : IsPGroup p (powMonoidHom (p ^ m) : G →* G).ker :=
    fun x ↦ ⟨m, Subtype.ext (MonoidHom.mem_ker.1 x.2)⟩
  obtain ⟨Q, hQ⟩ := hker.exists_le_sylow
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  refine le_antisymm ?_ ?_
  · rw [← Sylow.card_eq_multiplicity Q]
    exact Subgroup.card_le_of_le hQ
  · rw [← Sylow.card_eq_multiplicity P]
    refine Subgroup.card_le_of_le fun x hx ↦ ?_
    rw [MonoidHom.mem_ker, powMonoidHom_apply, ← orderOf_dvd_iff_pow_eq_one]
    refine (Subgroup.orderOf_dvd_natCard P hx).trans ?_
    rw [Sylow.card_eq_multiplicity P]
    exact pow_dvd_pow p hm

end TauCeti
