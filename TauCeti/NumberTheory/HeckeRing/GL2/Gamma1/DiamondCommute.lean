/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.DiamondCosets
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.UpperTriCosets

import TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.Gamma0Conjugation

/-!
# The diamond operators commute with `Tₚ` in the Hecke ring

`⟨d⟩` and `Tₚ` are both elements of the Hecke algebra `𝕋 Δ₀(N) Γ₁(N) ℤ`, and the spectral theory
of newforms needs them to commute: a simultaneous eigenvector for the `Tₙ` is only a newform once
it is also an eigenvector for the diamonds.

## Main results

* `HeckeRing.GL2.commute_diamondCosetGamma1_diagCosetGamma1_of_prime`: for `p` prime, the basis
  element of a diamond double coset commutes with the basis element of `diagCosetGamma1 N p`,
  over any coefficient semiring.
* `HeckeRing.GL2.commute_diamondHeckeElem_diagCosetGamma1_of_prime`: the same commutation read at
  the unit-indexed diamond `⟨d⟩`, which is the shape the theory of newforms consumes.

## Implementation notes

The commutation is *not* proved by computing either product, and after the opening unfolding
this file mentions no `GL₂` object at all: the whole argument is the general Hecke-ring lemma
`HeckeCosetModule.commute_single_of_conj_mem_doubleCoset`, which turns conjugation-stability of
`y`'s double coset under a normalising `x` into the commutation. What is specific to this file is
only the input — a diamond representative normalises `Γ₁(N)`
(`mapGL_mem_normalizer_Gamma1_map`), and `conj_natDiagGL_mem_doubleCoset_of_prime` supplies the
stability. So the only arithmetic was already made in `Gamma1/Gamma0Conjugation.lean`, which is
imported for the proof alone.

Primality is inherited from that input, where it is used only to make the dichotomy `p ∣ e` or
`IsCoprime e p` exhaustive. A general-level statement would need the intermediate case
`1 < gcd(e, n) < n`, which is genuinely more work rather than a weakening of this proof.
-/

open Matrix.SpecialLinearGroup CongruenceSubgroup DoubleCoset HeckeRing.GLn
open scoped MatrixGroups Pointwise HeckeCosetModule

namespace HeckeRing.GL2

variable {N p : ℕ} [NeZero N] (R : Type*) [Semiring R]

@[expose] public section

/-- **A diamond basis element commutes with the basis element of `Γ₁(N) diag(1, p) Γ₁(N)`**, for
`p` prime, in the Hecke ring of the pair `(Γ₁(N), Δ₀(N))` over any coefficient semiring.

Indexed by a matrix `g ∈ Γ₀(N)`; `commute_diamondHeckeElem_diagCosetGamma1_of_prime` is the
unit-indexed form `⟨d⟩ Tₚ = Tₚ ⟨d⟩`. Unlike
`single_diamondCosetGamma1_mul_single_diamondCosetGamma1`, which multiplies two diamonds, neither
of the two products here is itself a basis element — only their equality is claimed. -/
theorem commute_diamondCosetGamma1_diagCosetGamma1_of_prime (hp : p.Prime) (g : ↥(Gamma0 N)) :
    Commute (HeckeCosetModule.single R (diamondCosetGamma1 N g) 1)
      (HeckeCosetModule.single R (diagCosetGamma1 N p) 1) := by
  rw [diamondCosetGamma1_def, diagCosetGamma1_def]
  refine HeckeCosetModule.commute_single_of_conj_mem_doubleCoset R
    (mapGL_mem_normalizer_Gamma1_map ℚ g) ?_
  simpa using conj_natDiagGL_mem_doubleCoset_of_prime (N := N) hp g.2

/-- **The diamond operator `⟨d⟩` commutes with the basis element of `Γ₁(N) diag(1, p) Γ₁(N)`**,
for `p` prime: `commute_diamondCosetGamma1_diagCosetGamma1_of_prime` read at the unit-indexed
diamond, so that no choice of matrix representative has to be made at the call site. -/
theorem commute_diamondHeckeElem_diagCosetGamma1_of_prime (hp : p.Prime) (d : (ZMod N)ˣ) :
    Commute (diamondHeckeElem N d) (HeckeCosetModule.single ℤ (diagCosetGamma1 N p) 1) := by
  obtain ⟨g, hg⟩ := Gamma0Map_toHomUnits_surjective d
  rw [diamondHeckeElem_eq_single g hg]
  exact commute_diamondCosetGamma1_diagCosetGamma1_of_prime ℤ hp g

end

end HeckeRing.GL2
