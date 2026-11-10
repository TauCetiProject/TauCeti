/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Data.ZMod.Coprime
import TauCeti.Data.ZMod.PrincipalUnits
import TauCeti.NumberTheory.DirichletCharacter.Quadratic

/-!
# Quadratic Dirichlet characters at an odd prime-power level

For an odd prime `p` and every `k`, the quadratic Dirichlet characters modulo `p ^ k` are the
principal character and, when `k ≥ 1`, the lift by `changeLevel` of the Legendre character
`quadraticChar (ZMod p)`.

The route avoids the primitive character. A character `χ` with `χ ^ 2 = 1` is trivial on squares
of units, and every unit of `ZMod (p ^ (k + 1))` that reduces to `1` modulo `p` is a square
(`ZMod.isSquare_of_unitsMap_eq_one`), so `χ` factors through `p`. At the prime level `p`, a
nonprincipal quadratic character takes the value `-1` at some unit, which is then a nonsquare;
since the product of two nonsquares is a square, it takes the value `-1` at every nonsquare, and
so it is the Legendre character.

The descent is proved for characters of order dividing two with values in any commutative monoid
with zero, and the classification for values in any commutative ring.

## Main results

* `DirichletCharacter.factorsThrough_prime_of_sq_eq_one`: a character of order dividing two at
  level `p ^ k`, `k ≠ 0`, factors through `p`.
* `DirichletCharacter.conductor_eq_one_or_eq_prime_of_sq_eq_one`: its conductor is `1` or `p`.
* `DirichletCharacter.isQuadratic_iff_eq_one_or_eq_quadraticChar`: at a prime level, the quadratic
  characters are the principal one and the Legendre character.
* `DirichletCharacter.isQuadratic_iff_eq_one_or_eq_changeLevel_quadraticChar`: the classification
  at level `p ^ k` (the roadmap's `odd_prime_power_classification`).
* `DirichletCharacter.conductor_changeLevel_quadraticChar`: the lifted Legendre character has
  conductor `p` when `ringChar R ≠ 2`.
* `DirichletCharacter.IsQuadratic.apply_intCast_eq_legendreSym`: a nonprincipal quadratic
  character at level `p ^ k` takes the value `legendreSym p n` at every integer `n`.
* `DirichletCharacter.natCard_isQuadratic_prime_pow`: there are two quadratic characters at level
  `p ^ k` for `k ≠ 0` and one at level `1`. They form a group under multiplication by
  `MulChar.IsQuadratic.mul`.
* `DirichletCharacter.isQuadratic_of_forall_im_eq_zero`: a complex Dirichlet character with real
  values is quadratic.

## References

H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I. Classical Theory*,
Cambridge University Press, 2007, §9.3, pp. 295–296.
-/

public section

namespace DirichletCharacter

variable {R : Type*}

section Descent

variable [CommMonoidWithZero R] {p k : ℕ}

/-- **Descent to the prime.** For an odd prime `p` and `k ≠ 0`, a character of level `p ^ k`
whose square is trivial factors through `p`: it is trivial on the units reducing to `1` modulo
`p`, which are squares. -/
theorem factorsThrough_prime_of_sq_eq_one (hp : p.Prime) (hp2 : p ≠ 2) (hk : k ≠ 0)
    (χ : DirichletCharacter R (p ^ k)) (hχ : χ ^ 2 = 1) : χ.FactorsThrough p := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  have : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  refine (factorsThrough_iff_ker_unitsMap (dvd_pow_self p k.succ_ne_zero)).mpr fun u hu ↦ ?_
  obtain ⟨v, rfl⟩ := ZMod.isSquare_of_unitsMap_eq_one hp hp2 (MonoidHom.mem_ker.mp hu)
  refine MonoidHom.mem_ker.mpr (Units.ext ?_)
  rw [MulChar.coe_toUnitHom, Units.val_one, Units.val_mul, map_mul, ← sq,
    ← MulChar.pow_apply' χ two_ne_zero, hχ, MulChar.one_apply_coe]

/-- The conductor of a character of order dividing two at level `p ^ k`, for an odd prime `p`,
divides `p`. -/
theorem conductor_dvd_prime_of_sq_eq_one (hp : p.Prime) (hp2 : p ≠ 2)
    (χ : DirichletCharacter R (p ^ k)) (hχ : χ ^ 2 = 1) : χ.conductor ∣ p := by
  rcases eq_or_ne k 0 with rfl | hk
  · exact χ.conductor_dvd_level.trans (by simp)
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  exact conductor_dvd_of_mem_conductorSet χ (factorsThrough_prime_of_sq_eq_one hp hp2 hk χ hχ)

/-- The conductor of a character of order dividing two at level `p ^ k`, for an odd prime `p`, is
`1` or `p`. -/
theorem conductor_eq_one_or_eq_prime_of_sq_eq_one (hp : p.Prime) (hp2 : p ≠ 2)
    (χ : DirichletCharacter R (p ^ k)) (hχ : χ ^ 2 = 1) : χ.conductor = 1 ∨ χ.conductor = p :=
  (Nat.dvd_prime hp).mp (conductor_dvd_prime_of_sq_eq_one hp hp2 χ hχ)

end Descent

section Classification

variable [CommRing R] {p : ℕ} [Fact p.Prime]

private theorem isQuadratic_one {n : ℕ} : (1 : DirichletCharacter R n).IsQuadratic := by
  intro a
  by_cases ha : IsUnit a
  · exact Or.inr (Or.inl (MulChar.one_apply ha))
  · exact Or.inl (MulChar.map_nonunit _ ha)

/-- **The quadratic characters at a prime level.** A quadratic Dirichlet character modulo a prime
`p` is either principal or the Legendre character `quadraticChar (ZMod p)`, with values pushed to
`R`. -/
theorem isQuadratic_iff_eq_one_or_eq_quadraticChar (ψ : DirichletCharacter R p) :
    ψ.IsQuadratic ↔
      ψ = 1 ∨ ψ = (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom R) := by
  refine ⟨fun hψ ↦ or_iff_not_imp_left.mpr fun h1 ↦ ?_, ?_⟩
  · -- `ψ` is `1` at every square unit.
    have hsq (x : (ZMod p)ˣ) (hx : IsSquare (x : ZMod p)) : ψ x = 1 := by
      obtain ⟨s, hs⟩ := hx
      have hs' : IsUnit s := isUnit_of_mul_isUnit_left (hs ▸ x.isUnit)
      rw [hs, map_mul, ← sq, ← MulChar.pow_apply' ψ two_ne_zero, hψ.sq_eq_one,
        MulChar.one_apply hs']
    obtain ⟨u, hu⟩ := MulChar.ne_one_iff.mp h1
    have hu' : ψ u = -1 := by
      rcases hψ u with h | h | h
      · have : Subsingleton R := subsingleton_of_zero_eq_one
          (isUnit_zero_iff.mp (h ▸ u.isUnit.map ψ))
        exact absurd (Subsingleton.elim _ _) hu
      · exact absurd h hu
      · exact h
    have hun : ¬IsSquare (u : ZMod p) := fun h ↦ hu (hsq u h)
    refine MulChar.ext fun x ↦ ?_
    rw [MulChar.ringHomComp_apply, eq_intCast]
    by_cases hx : IsSquare (x : ZMod p)
    · rw [hsq x hx, (quadraticChar_one_iff_isSquare x.ne_zero).mpr hx, Int.cast_one]
    · rw [quadraticChar_neg_one_iff_not_isSquare.mpr hx]
      have hxu : ψ ↑(x * u) = 1 := by
        refine hsq _ ((quadraticChar_one_iff_isSquare (x * u).ne_zero).mp ?_)
        rw [Units.val_mul, map_mul, quadraticChar_neg_one_iff_not_isSquare.mpr hx,
          quadraticChar_neg_one_iff_not_isSquare.mpr hun]
        norm_num
      rw [Units.val_mul, map_mul, hu'] at hxu
      push_cast
      linear_combination -hxu
  · rintro (rfl | rfl)
    · exact isQuadratic_one
    · exact quadraticChar_isQuadratic _ |>.comp _

/-- **The quadratic characters at an odd prime-power level.** For an odd prime `p` and every
`k`, a Dirichlet character modulo `p ^ k` is quadratic exactly when it is principal or the lift by
`changeLevel` of the Legendre character `quadraticChar (ZMod p)`. The lift exists only for
`k ≥ 1`; at `k = 0` the level is `1` and the only character is principal (Montgomery–Vaughan,
§9.3, pp. 295–296). -/
theorem isQuadratic_iff_eq_one_or_eq_changeLevel_quadraticChar (hp2 : p ≠ 2) (k : ℕ)
    (χ : DirichletCharacter R (p ^ k)) :
    χ.IsQuadratic ↔ χ = 1 ∨ ∃ h : p ∣ p ^ k,
      χ = changeLevel h ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom R)) := by
  have hp : p.Prime := Fact.out
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  refine ⟨fun hχ ↦ ?_, ?_⟩
  · rcases eq_or_ne k 0 with rfl | hk
    · exact Or.inl (level_one' χ (pow_zero p))
    obtain ⟨hd, ψ, rfl⟩ := factorsThrough_prime_of_sq_eq_one hp hp2 hk χ hχ.sq_eq_one
    rcases (isQuadratic_iff_eq_one_or_eq_quadraticChar ψ).mp
      ((isQuadratic_changeLevel_iff hd).mp hχ) with rfl | rfl
    · exact Or.inl (changeLevel_one hd)
    · exact Or.inr ⟨hd, rfl⟩
  · rintro (rfl | ⟨h, rfl⟩)
    · exact isQuadratic_one
    · exact (quadraticChar_isQuadratic _ |>.comp _).changeLevel h

/-- The Legendre character with values in a nontrivial ring `R` of characteristic other than `2`
is not principal. -/
theorem quadraticChar_ringHomComp_ne_one [Nontrivial R] (hR : ringChar R ≠ 2) (hp2 : p ≠ 2) :
    (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom R) ≠ 1 := by
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
  refine MulChar.ne_one_iff.mpr ⟨a, ?_⟩
  rw [MulChar.ringHomComp_apply, ha, map_neg, map_one]
  exact mt neg_one_eq_one_iff.mp hR

/-- The Legendre character with values in a nontrivial ring `R` of characteristic other than `2`,
lifted to level `p ^ k`, has conductor `p`. -/
theorem conductor_changeLevel_quadraticChar [Nontrivial R] (hR : ringChar R ≠ 2) (hp2 : p ≠ 2)
    {k : ℕ} (h : p ∣ p ^ k) :
    (changeLevel h ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom R))).conductor = p := by
  have hp : p.Prime := Fact.out
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [conductor_changeLevel]
  refine ((Nat.dvd_prime hp).mp (conductor_dvd_level _)).resolve_left fun h1 ↦ ?_
  exact quadraticChar_ringHomComp_ne_one hR hp2 (eq_one_iff_conductor_eq_one.mpr h1)

/-- The value of a nonprincipal quadratic character at level `p ^ k` at an integer `n` is the
Legendre symbol `legendreSym p n`, including the value `0` when `p ∣ n`. (A nonprincipal
character exists only for `k ≠ 0`.) -/
theorem IsQuadratic.apply_intCast_eq_legendreSym (hp2 : p ≠ 2) {k : ℕ}
    {χ : DirichletCharacter R (p ^ k)} (hχ : χ.IsQuadratic) (h1 : χ ≠ 1) (n : ℤ) :
    χ n = legendreSym p n := by
  have hp : p.Prime := Fact.out
  obtain ⟨h, rfl⟩ :=
    ((isQuadratic_iff_eq_one_or_eq_changeLevel_quadraticChar hp2 k χ).mp hχ).resolve_left h1
  by_cases hn : (n : ZMod p) = 0
  · rw [(legendreSym.eq_zero_iff p n).mpr hn, Int.cast_zero]
    refine MulChar.map_nonunit _ fun hu ↦ ?_
    have := hu.map (ZMod.castHom h (ZMod p))
    rw [map_intCast, hn] at this
    exact not_isUnit_zero this
  · have hcop : IsCoprime n p :=
      Int.isCoprime_iff_gcd_eq_one.mpr (by_contra fun hg ↦ hn (ZMod.eq_zero_of_gcd_ne_one hp hg))
    rw [changeLevel_eq_cast_of_dvd' _ h (by simpa using hcop.pow_right (n := k)),
      MulChar.ringHomComp_apply, eq_intCast, legendreSym]

/-- **The number of quadratic characters at an odd prime-power level.** With values in a
nontrivial ring of characteristic other than `2`, there are two quadratic characters modulo
`p ^ k` for `k ≠ 0`, and one modulo `p ^ 0 = 1`. -/
theorem natCard_isQuadratic_prime_pow [Nontrivial R] (hR : ringChar R ≠ 2) (hp2 : p ≠ 2)
    (k : ℕ) :
    Nat.card {χ : DirichletCharacter R (p ^ k) // χ.IsQuadratic} = if k = 0 then 1 else 2 := by
  have hp : p.Prime := Fact.out
  split_ifs with hk
  · subst hk
    exact Nat.card_eq_one_iff_exists.mpr
      ⟨⟨1, isQuadratic_one⟩, fun χ ↦ Subtype.ext (level_one' χ.1 (pow_zero p))⟩
  · have h : p ∣ p ^ k := dvd_pow_self p hk
    have hset : {χ : DirichletCharacter R (p ^ k) | χ.IsQuadratic} =
        {1, changeLevel h ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom R))} := by
      ext χ
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
        isQuadratic_iff_eq_one_or_eq_changeLevel_quadraticChar hp2 k χ, exists_prop_of_true h]
    have hne : (1 : DirichletCharacter R (p ^ k)) ≠
        changeLevel h ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom R)) := by
      rw [← changeLevel_one h]
      exact fun h' ↦ quadraticChar_ringHomComp_ne_one hR hp2 (changeLevel_injective h h').symm
    change Nat.card {χ : DirichletCharacter R (p ^ k) | χ.IsQuadratic} = 2
    rw [Nat.card_coe_set_eq, hset, Set.ncard_pair hne]

end Classification

/-- **A real character is quadratic.** A Dirichlet character with complex values whose values are
all real is quadratic: its values at units have absolute value one. -/
theorem isQuadratic_of_forall_im_eq_zero {N : ℕ} (χ : DirichletCharacter ℂ N)
    (hχ : ∀ a, (χ a).im = 0) : χ.IsQuadratic := by
  intro a
  by_cases ha : IsUnit a
  · have hnorm : |(χ a).re| = 1 := by
      rw [Complex.abs_re_eq_norm.mpr (hχ a), ← ha.unit_spec]
      exact χ.unit_norm_eq_one ha.unit
    have hre : χ a = ((χ a).re : ℂ) := Complex.ext rfl (by simp [hχ a])
    rcases abs_eq (zero_le_one' ℝ) |>.mp hnorm with h | h
    · exact Or.inr (Or.inl (by rw [hre, h, Complex.ofReal_one]))
    · exact Or.inr (Or.inr (by rw [hre, h, Complex.ofReal_neg, Complex.ofReal_one]))
  · exact Or.inl (MulChar.map_nonunit χ ha)

end DirichletCharacter
