/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# The extra coset representative of the level descent

Miyake's level descent at a prime `p` exactly dividing `N` uses, besides the `p` upper-triangular
representatives, one further coset representative: an element of `Γ₀(N / p)` that reduces to
`S = [[0, -1], [1, 0]]` modulo `p` and to the identity modulo `N / p`. This file records that
matrix's **existence**, which is what strong approximation supplies.

The matrix comes from strong approximation at a coprime pair of levels,
`CongruenceSubgroup.exists_mem_Gamma_map_intCast_zmod_eq`: for coprime `d` and `d'` the principal
congruence subgroup `Γ(d')` still surjects onto `SL₂(ℤ/dℤ)`. The descent is that statement at
`d = p` and `d' = N / p` — a coprime pair exactly because `p` divides `N` while `p²` does not —
with `S` as the prescribed reduction modulo `p`. Approximation returns membership in `Γ(N / p)`,
which is stronger than the `Γ₀(N / p)` the descent asks for, so the second reduction is the
identity rather than merely lower-triangular.

## Main results

* `TauCeti.exists_mem_Gamma0_map_intCast_zmod_eq_S`: for a prime `p` with `p ∣ N` and `p² ∤ N`,
  some `γ ∈ Γ₀(N / p)` reduces to `S` modulo `p` and to the identity modulo `N / p`.

## Scope

Existence and the two reductions are all that is claimed. The coset system is not formalized
here, so nothing enumerates the representatives or asserts that the list of them is complete.

Specializes `descendExtraGamma_exists` of the AINTLIB `LeanModularForms` project
(`LeanModularForms/StrongMultiplicityOne/DescentCosets.lean`, Chris Birkbeck, commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), which proves the
same existence directly; here it is read off the general coprime-level statement instead.
-/

public section

open CongruenceSubgroup

open scoped MatrixGroups

namespace TauCeti

/-- **A matrix with prescribed reductions at `p` and at `N / p`.** For a prime `p` with `p ∣ N` but
`p² ∤ N`, there is a `γ ∈ Γ₀(N / p)` reducing to `S = [[0, -1], [1, 0]]` modulo `p` and to the
identity modulo `N / p`.

`p² ∤ N` is exactly what makes `p` coprime to `N / p`; the target modulo `p` is `S`, and membership
in `Γ₀(N / p)` comes from the stronger `Γ(N / p)` that
`CongruenceSubgroup.exists_mem_Gamma_map_intCast_zmod_eq` already delivers.

This is the matrix Miyake's Lemma 4.5.11 takes as its extra coset representative for the level
descent when `p` exactly divides `N`. Only existence and the two reductions are proved here: the
coset system is not formalized, so nothing is claimed about enumerating or completing it. -/
theorem exists_mem_Gamma0_map_intCast_zmod_eq_S {p N : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (hpsq : ¬ p ^ 2 ∣ N) :
    ∃ γ ∈ Gamma0 (N / p),
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod p)) γ =
          Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod p)) ModularGroup.S ∧
        Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (N / p))) γ = 1 := by
  have hcop : Nat.Coprime p (N / p) := hp.coprime_iff_not_dvd.mpr fun h ↦ hpsq <| by
    have hmul := Nat.mul_dvd_mul_left p h
    rwa [Nat.mul_div_cancel' hpN, ← sq] at hmul
  obtain ⟨γ, hγ, hγp⟩ := exists_mem_Gamma_map_intCast_zmod_eq hcop
    (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod p)) ModularGroup.S)
  exact ⟨γ, Gamma_le_Gamma0 _ hγ, hγp, Gamma_mem'.mp hγ⟩

end TauCeti
