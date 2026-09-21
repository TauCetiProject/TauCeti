/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.UpperTriFactorization
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.Sum

/-!
# Equivariance of the upper-triangular Hecke sum at level-supported indices

`UpperTri/Sum.lean` defines `heckeSlashUpperTri k p f = ∑_{b < p} f ∣[k] !![1, b; 0, p]`, and
`UpperTri/Periodic.lean` shows it preserves invariance under the single matrix `T`. That is far
short of an operator: to act on `M_k(Γ₁(N))` the sum has to preserve invariance under the whole
group. This file proves the basic case when `p` divides the level, then obtains every index
supported on the level by composing those basic sums.

## The permutation

Write `γ = !![a, b; c, d] ∈ Γ₀(N)`, so `N ∣ c` and hence `p ∣ c`. Then

`!![1, j; 0, p] · γ = !![a + jc, b + jd; pc, pd]`,

and one asks for a factorisation `γ' · !![1, j'; 0, p]` with `γ' ∈ Γ₀(N)`. Matching entries forces
`γ' = !![a + jc, b'; pc, d - cj']` and `p b' = b + jd - (a + jc) j'`, so `j'` must solve

`(a + jc) j' ≡ b + jd (mod p)`.

That has a unique solution in `[0, p)` exactly when `a + jc` is invertible modulo `p`, and
`upperTriShift p γ j` is it. On `Γ₀(p)` invertibility is automatic and uniform in `j`: `p ∣ c`
collapses `a + jc` to `a`, and the determinant identity `ad - bc = 1` reduces to `ad ≡ 1 (mod p)`,
exhibiting `d` as the inverse of `a`, so the solution takes the closed form

`j' = d b + j d² mod p`.

It is a bijection of `Fin p` there, because `d²` is again invertible modulo `p`. Slashing
therefore permutes the summands, and the sum is unchanged up to the scalar by which `γ'` acts
on `f`.

The map is defined by the general formula rather than the closed one because the closed form is
false off `Γ₀(p)`: when `p ∤ c` the entry `a + jc` varies with `j` and can vanish, and then the
congruence has no solution at all. The definition and the general factorisation
`HeckeRing.GL2.exists_mem_Gamma0_upperTriRep_mul_of_isUnit`, both imported from
`TauCeti/NumberTheory/HeckeRing/GL2/Gamma0/UpperTriFactorization.lean`, are stated at exactly the
offsets where it does — those with `a + jc` invertible.

Two facts make that scalar behave. The new lower-right entry is `d - c j' ≡ d (mod N)`, so `γ'`
has the *same* `Gamma0Map` value as `γ`; and if `γ ∈ Γ₁(N)` then `γ' ∈ Γ₁(N)`. So the hypothesis
on `f` is only ever used at matrices congruent to `γ` in the relevant sense, which is what lets
the nebentypus version below carry a fixed character.

⚠ `p ∣ N` is essential to the direct permutation argument, not a convenience. The general
level-supported theorem below instead composes sums at prime divisors of `N`. When `p` is prime
and `p ∤ N`, the classical double coset has one further left coset, represented by
`!![p, 0; 0, 1]` up to a `Γ₀(N)` twist, and the sum over the upper-triangular representatives
alone is *not* invariant.

## Where the factorisation lives

The offset map `HeckeRing.GL2.upperTriShift` and the coset factorisation it feeds —
`exists_mem_Gamma0_upperTriRep_mul` and its two variants — are statements about matrices and
congruence subgroups, with no slash action in them, and live in
`NumberTheory/HeckeRing/GL2/Gamma0/UpperTriFactorization.lean`. This file imports them and
supplies the analytic half.

## Main results

* `HeckeRing.GL2.heckeSlashUpperTri_slash_mapGL_of_mem_Gamma0`: the equivariance, stated with an
  arbitrary scalar so that both corollaries below are instances of it.
* `HeckeRing.GL2.heckeSlashUpperTri_slash_mapGL_of_mem_Gamma1`: the sum of a `Γ₁(N)`-invariant
  function is `Γ₁(N)`-invariant.
* `HeckeRing.GL2.heckeSlashUpperTri_slash_mapGL_of_nebentypus`: the sum of a function with
  nebentypus `χ` has nebentypus `χ`.
* `HeckeRing.GL2.heckeSlashUpperTri_slash_mapGL_of_nebentypus_of_primeFactors_subset`: the same
  conclusion for every index whose prime factors divide `N`.

## References

The generality of the offset map follows the descent formalisation in the AINTLIB
`LeanModularForms` project (`LeanModularForms/StrongMultiplicityOne/DescentCosets.lean`, Chris
Birkbeck, commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), whose
`descend_exists_fin_isUnit_mul_eq` and `descendCosetList_action_upper_tri_extra` solve the same
congruence at each call site. No code is adapted from it.

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.2.
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.5.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane HeckeRing.GLn CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N p : ℕ}

/-- **The upper-triangular sum is `Γ₀(N)`-equivariant at `p ∣ N`.** The hypothesis is imposed
only at matrices of `Γ₀(N)` with the same lower-right entry modulo `N` as `γ`, which is all the
factorisation ever produces; the scalar `u` is left free so that the two corollaries below —
`Γ₁(N)`-invariance and nebentypus transport — are both instances. -/
theorem heckeSlashUpperTri_slash_mapGL_of_mem_Gamma0 (k : ℤ) [NeZero p] (hpN : p ∣ N)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) {f : ℍ → ℂ} {u : ℂ}
    (hf : ∀ δ ∈ Gamma0 N, ((δ 1 1 : ℤ) : ZMod N) = ((γ 1 1 : ℤ) : ZMod N) →
      f ∣[k] (mapGL ℚ δ : GL (Fin 2) ℚ) = u • f) :
    heckeSlashUpperTri k p f ∣[k] (mapGL ℚ γ : GL (Fin 2) ℚ)
      = u • heckeSlashUpperTri k p f := by
  rw [heckeSlashUpperTri_def, SlashAction.sum_slash, Finset.smul_sum]
  have key : ∀ j : Fin p,
      (f ∣[k] (upperTriRep p j : GL (Fin 2) ℚ)) ∣[k] (mapGL ℚ γ : GL (Fin 2) ℚ)
        = u • (f ∣[k] (upperTriRep p (upperTriShift p γ j) : GL (Fin 2) ℚ)) := fun j ↦ by
    obtain ⟨γ', hγ', hdd, hmul⟩ := exists_mem_Gamma0_upperTriRep_mul_of_mem_Gamma0 hpN hγ j
    rw [← SlashAction.slash_mul, hmul, SlashAction.slash_mul, hf γ' hγ' hdd,
      ModularForm.rat_smul_slash_of_det_pos k (det_upperTriRep_pos p _) f u]
  rw [Finset.sum_congr rfl fun j _ ↦ key j]
  exact Fintype.sum_bijective (upperTriShift p γ)
    (upperTriShift_bijective (Gamma0_le_Gamma0_of_dvd hpN hγ))
    (fun j ↦ u • (f ∣[k] (upperTriRep p (upperTriShift p γ j) : GL (Fin 2) ℚ)))
    (fun j ↦ u • (f ∣[k] (upperTriRep p j : GL (Fin 2) ℚ))) fun _ ↦ rfl

/-- **The upper-triangular sum preserves `Γ₁(N)`-invariance at `p ∣ N`** — the invariance that
turns it into an operator on `M_k(Γ₁(N))`. -/
theorem heckeSlashUpperTri_slash_mapGL_of_mem_Gamma1 (k : ℤ) [NeZero p] (hpN : p ∣ N)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 N) {f : ℍ → ℂ}
    (hf : ∀ δ ∈ Gamma1 N, f ∣[k] (mapGL ℚ δ : GL (Fin 2) ℚ) = f) :
    heckeSlashUpperTri k p f ∣[k] (mapGL ℚ γ : GL (Fin 2) ℚ) = heckeSlashUpperTri k p f := by
  have h11 : ((γ 1 1 : ℤ) : ZMod N) = 1 := (mem_Gamma1_iff.mp hγ).2
  have h := heckeSlashUpperTri_slash_mapGL_of_mem_Gamma0 (u := 1) k hpN
    (Gamma1_in_Gamma0 N hγ) (f := f) fun δ hδ hd ↦ by
      rw [hf δ (mem_Gamma1_iff.mpr ⟨hδ, hd.trans h11⟩), one_smul]
  rwa [one_smul] at h

/-- **The upper-triangular sum preserves the nebentypus at `p ∣ N`**: if `f` transforms under
`Γ₀(N)` by the character `χ`, so does `heckeSlashUpperTri k p f`. This is the function-level
statement behind the fact that the operator preserves `M_k(N, χ)`. -/
theorem heckeSlashUpperTri_slash_mapGL_of_nebentypus (k : ℤ) [NeZero p] (hpN : p ∣ N)
    (χ : (ZMod N)ˣ →* ℂˣ) (γ : ↥(Gamma0 N)) {f : ℍ → ℂ}
    (hf : ∀ δ : ↥(Gamma0 N), f ∣[k] (mapGL ℚ (δ : SL(2, ℤ)) : GL (Fin 2) ℚ)
      = (↑(χ ((Gamma0Map N).toHomUnits δ)) : ℂ) • f) :
    heckeSlashUpperTri k p f ∣[k] (mapGL ℚ (γ : SL(2, ℤ)) : GL (Fin 2) ℚ)
      = (↑(χ ((Gamma0Map N).toHomUnits γ)) : ℂ) • heckeSlashUpperTri k p f := by
  apply heckeSlashUpperTri_slash_mapGL_of_mem_Gamma0 k hpN γ.2
  intro δ hδ hd
  have hmap : (Gamma0Map N).toHomUnits ⟨δ, hδ⟩ = (Gamma0Map N).toHomUnits γ := Units.ext hd
  rw [hf ⟨δ, hδ⟩, hmap]

/-- **The upper-triangular sum preserves the nebentypus at every index supported on the level.**
If `f` transforms under `Γ₀(N)` by the character `χ`, so does `heckeSlashUpperTri k n f`.

The divisor case above does not apply directly at `n = q ^ 2`, since `Γ₀(N)` need not lie in
`Γ₀(q ^ 2)`. Instead the index is peeled apart one prime at a time, and the composition law for
upper-triangular sums reduces to the divisor case. -/
theorem heckeSlashUpperTri_slash_mapGL_of_nebentypus_of_primeFactors_subset (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) (n : ℕ) (hn0 : n ≠ 0)
    (hn : n.primeFactors ⊆ N.primeFactors) (γ : ↥(Gamma0 N)) {f : ℍ → ℂ}
    (hf : ∀ δ : ↥(Gamma0 N), f ∣[k] (mapGL ℚ (δ : SL(2, ℤ)) : GL (Fin 2) ℚ)
      = (↑(χ ((Gamma0Map N).toHomUnits δ)) : ℂ) • f) :
    heckeSlashUpperTri k n f ∣[k] (mapGL ℚ (γ : SL(2, ℤ)) : GL (Fin 2) ℚ)
      = (↑(χ ((Gamma0Map N).toHomUnits γ)) : ℂ) • heckeSlashUpperTri k n f := by
  induction n using Nat.strong_induction_on generalizing γ with
  | _ n ih =>
    rcases eq_or_ne n 1 with rfl | hn1
    · rw [heckeSlashUpperTri_one]
      exact hf γ
    · have hq : n.minFac.Prime := Nat.minFac_prime hn1
      have hqn : n.minFac ∣ n := Nat.minFac_dvd n
      have hqN : n.minFac ∣ N :=
        (Nat.mem_primeFactors.mp (hn (Nat.mem_primeFactors.mpr ⟨hq, hqn, hn0⟩))).2.1
      have hm0 : n / n.minFac ≠ 0 :=
        (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hqn) hq.pos).ne'
      have hmlt : n / n.minFac < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn0) hq.one_lt
      have hmn : (n / n.minFac).primeFactors ⊆ N.primeFactors :=
        (Nat.primeFactors_mono (Nat.div_dvd_of_dvd hqn) hn0).trans hn
      have _ : NeZero n.minFac := ⟨hq.ne_zero⟩
      have key : heckeSlashUpperTri k n f
          = heckeSlashUpperTri k n.minFac (heckeSlashUpperTri k (n / n.minFac) f) := by
        rw [heckeSlashUpperTri_heckeSlashUpperTri k n.minFac (n / n.minFac) f,
          Nat.div_mul_cancel hqn]
      rw [key]
      exact heckeSlashUpperTri_slash_mapGL_of_nebentypus k hqN χ γ
        fun δ ↦ ih _ hmlt hm0 hmn δ

end HeckeRing.GL2

end
