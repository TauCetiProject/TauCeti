/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Points

/-!
# Points of infinitesimal diagonalizable groups over reduced rings

Let `p` be a prime and `G` a finitely generated commutative group killed by `p`, so that the
diagonalizable group scheme `D(G)` is a product of copies of `μ_p`. Over a reduced ring `A` of
characteristic `p`, the only `A`-valued point of `D(G)` is the identity: a point is a character
`χ : G → Aˣ`, and each value `u = χ g` satisfies `(u - 1)^p = u^p - 1 = 0`, so `u = 1`. In
particular every geometric point of `μ_p` over a field of characteristic `p` is the identity,
although `μ_p` has nonidentity points over nonreduced rings such as `𝔽_p[ε]/(ε²)`.

## Main results

* `TauCeti.DiagonalizableGroup.subsingleton_schemePoints_of_isReduced`: over a reduced ring of
  characteristic `p`, the diagonalizable group scheme of a group killed by `p` has only one
  point.
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace TauCeti.DiagonalizableGroup

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- **Points of `μ_p` over a reduced ring of characteristic `p`.** If every element of `G` is
killed by the prime `p`, a reduced ring `A` of characteristic `p` has only the identity as an
`A`-valued point of `D(G)`: every value `u` of a character satisfies `(u - 1)^p = 0`. -/
theorem subsingleton_schemePoints_of_isReduced (p : ℕ) [Fact p.Prime] [CharP A p] [IsReduced A]
    (G : FGCommGrpCat.{u}) (hG : ∀ g : G, g ^ p = 1) :
    Subsingleton ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R G).X) := by
  refine (schemePointsMulEquiv (R := R) (A := A) G).toEquiv.subsingleton_congr.mpr ⟨fun χ ψ ↦ ?_⟩
  -- Every character is trivial.
  have h (χ : G →* Aˣ) : χ = 1 := by
    ext g
    have hu : ((χ g : A) - 1) ^ p = 0 := by
      rw [sub_pow_char, one_pow, ← Units.val_pow_eq_pow_val, ← map_pow, hG, map_one,
        Units.val_one, sub_self]
    simpa [sub_eq_zero] using IsReduced.eq_zero _ ⟨p, hu⟩
  rw [h χ, h ψ]

end TauCeti.DiagonalizableGroup
