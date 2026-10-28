/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Submodule.Essential
public import TauCeti.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.RingTheory.Filtration

/-!
# Ideal-power torsion in essential extensions

Over a commutative Noetherian ring, an essential extension of an ideal-power-torsion module
is again ideal-power torsion. No uniform annihilating power is required for the essential
submodule or its extension. When the ambient module is finitely generated, a single power
annihilates the whole module.

These results apply in particular to injective envelopes. The argument uses Mathlib's
Artin–Rees lemma and `Ideal.exists_le_torsionBySet_pow_of_le_primaryComponent` to find a
power whose image misses the essential submodule, and hence vanishes.

## References

* The Stacks Project, Section 47.7, Tag 08Z1, on injective hulls of residue fields.
-/

public section

namespace TauCeti

open Submodule

variable {R M : Type*} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]

/-- A finite module with an essential ideal-power-torsion submodule is annihilated by a
single power of the ideal. -/
theorem IsEssential.exists_pow_smul_eq_bot [Module.Finite R M] {N : Submodule R M}
    (hN : IsEssential N) (I : Ideal R) (hNI : N ≤ I.primaryComponent M) :
    ∃ n : ℕ, I ^ n • (⊤ : Submodule R M) = ⊥ := by
  obtain ⟨n, hn⟩ := I.exists_le_torsionBySet_pow_of_le_primaryComponent
    (IsNoetherian.noetherian N) hNI
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul N
  have hkill : I ^ n • N = ⊥ := by
    apply le_bot_iff.mp
    refine Submodule.smul_le.mpr fun r hr x hx => ?_
    exact (mem_bot R).mpr ((mem_torsionBySet_iff _ _).mp (hn hx) ⟨r, hr⟩)
  -- A sufficiently deep power meets the essential submodule only in zero.
  refine ⟨n + k, isEssential_iff.mp hN _ ?_⟩
  rw [inf_comm, hk (n + k) (Nat.le_add_left k n), Nat.add_sub_cancel]
  exact le_bot_iff.mp ((Submodule.smul_mono le_rfl inf_le_right).trans hkill.le)

/-- An essential extension of an ideal-power-torsion module over a Noetherian ring is
ideal-power torsion. The extension need not be finitely generated. -/
theorem IsEssential.primaryComponent_eq_top {N : Submodule R M} (hN : IsEssential N)
    (I : Ideal R) (hNI : N ≤ I.primaryComponent M) : I.primaryComponent M = ⊤ := by
  apply top_unique
  intro x _
  -- Work in a cyclic submodule to avoid requiring a uniform bound on the ambient module.
  let P := Submodule.span R {x}
  have : Module.Finite R P := Module.Finite.iff_fg.mpr (fg_span_singleton x)
  have htrace : N.comap P.subtype ≤ I.primaryComponent P := by
    intro y hy
    obtain ⟨n, hn⟩ := (I.primaryComponent_mem M (y : M)).mp (hNI hy)
    refine (I.primaryComponent_mem P y).mpr ⟨n, ?_⟩
    rw [mem_torsionBySet_iff] at hn ⊢
    intro r
    exact Subtype.ext (hn r)
  obtain ⟨n, hn⟩ := (hN.comap P.subtype).exists_pow_smul_eq_bot I htrace
  refine (I.primaryComponent_mem M x).mpr ⟨n, ?_⟩
  rw [mem_torsionBySet_iff]
  intro r
  have hx : x ∈ P := mem_span_singleton_self x
  have hz : (r : R) • (⟨x, hx⟩ : P) ∈ I ^ n • (⊤ : Submodule R P) :=
    Submodule.smul_mem_smul r.prop (mem_top : (⟨x, hx⟩ : P) ∈ (⊤ : Submodule R P))
  rw [hn, mem_bot] at hz
  exact congrArg P.subtype hz

end TauCeti
