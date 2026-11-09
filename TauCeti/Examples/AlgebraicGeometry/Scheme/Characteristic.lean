/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.Characteristic
public import Mathlib.Algebra.DualNumber

/-!
# Checks for intrinsic scheme characteristic

The examples include nonreduced schemes, empty opens and the empty scheme, and distinguish
characteristic `p` from the weaker assertion that all residue fields have characteristic `p`.
They also use the intrinsic hypothesis with the existing absolute Frobenius and prime-field
structure morphism, without unfolding the new predicate.
-/

public section

open AlgebraicGeometry TauCeti.AlgebraicGeometry CategoryTheory CategoryTheory.Limits

-- Nonreduced schemes are allowed.
example : SchemeCharP (Spec (.of (DualNumber (ZMod 2)))) 2 := by
  rw [SchemeCharP.spec_iff_natCast_eq_zero]
  have h : (2 : ZMod 2) = 0 := by decide
  simpa only [map_ofNat, map_zero, Nat.cast_ofNat] using
    congr((TrivSqZeroExt.inlHom (R := ZMod 2) (M := ZMod 2)) $h)

-- Vanishing of the prime, not just nilpotence of the prime, is essential.
example : ¬ SchemeCharP (Spec (.of (ZMod 4))) 2 := by
  rw [SchemeCharP.spec_iff_natCast_eq_zero]
  decide

-- The empty scheme has all characteristics; its section rings are zero rings.
example (p : ℕ) : SchemeCharP (∅ : Scheme) p := inferInstance

example (X : Scheme) (p : ℕ) (h : SchemeCharP X p) :
    (p : Γ(X, ⊥)) = 0 := h.natCast_eq_zero ⊥

-- Isomorphisms and open restrictions preserve every natural characteristic, not just primes.
example {X Y : Scheme} (p : ℕ) (e : X ≅ Y) :
    SchemeCharP X p ↔ SchemeCharP Y p := SchemeCharP.iff_of_iso e

example {X : Scheme} (p : ℕ) [SchemeCharP X p] (U : X.Opens) :
    SchemeCharP U p := inferInstance

-- The intrinsic hypothesis supplies exactly what the existing Frobenius needs.
example (X : Scheme) (p : ℕ) [Fact p.Prime] (h : SchemeCharP X p)
    (s : Γ(X, ⊤)) : (X.frobenius p (h.natCast_eq_zero ⊤)).appTop s = s ^ p := by
  simp

-- Structure maps are the existing ones and commute with every scheme morphism.
example {X Y : Scheme} (p : ℕ) (hX : SchemeCharP X p) (hY : SchemeCharP Y p)
    (f : X ⟶ Y) :
    f ≫ Y.toSpecZMod (hY.natCast_eq_zero ⊤) = X.toSpecZMod (hX.natCast_eq_zero ⊤) :=
  Subsingleton.elim _ _

-- Arbitrary base change and products need no reducedness or finiteness assumptions.
example {X Y S : Scheme} (p : ℕ) [Fact p.Prime] [SchemeCharP X p]
    (f : X ⟶ S) (g : Y ⟶ S) : SchemeCharP (pullback f g) p := inferInstance

example {X Y : Scheme} (p : ℕ) [Fact p.Prime] [SchemeCharP X p] :
    SchemeCharP (X ⨯ Y) p := inferInstance

-- Restricting to a nonempty open gives the actual characteristic of its section ring.
example {X : Scheme} {p : ℕ} (h : SchemeCharP X p) (U : X.Opens) [Nonempty U] :
    CharP Γ(X, U) p := h.charP_sections U
