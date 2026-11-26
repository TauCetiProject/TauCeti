/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.Char
import TauCeti.Algebra.BigOperators.ModEq
import TauCeti.Data.ZMod.Units
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# The Jacobi symbol on the class of `1`

For a modulus `m₀` and an odd squarefree `s > 1` prime to `m₀`, the Jacobi symbol `u ↦ J(u | s)`
takes the value `-1` at some natural number `u ≡ 1 (mod m₀)` prime to `m₀ s`: it is a nontrivial
character of the unit classes modulo `m₀ s` that lie above the class of `1` modulo `m₀`.
Two distinct odd squarefree numbers `s₁`, `s₂` prime to `m₀` are separated in the same way: some
`u ≡ 1 (mod m₀)` prime to `m₀ s₁ s₂` has `J(u | s₁) ≠ J(u | s₂)`. As a consequence, the sum of
`J(b | s)` over the residues `b` modulo `m₀ s` that are prime to `m₀ s` and lie in a fixed class
modulo `m₀` vanishes.

The first two facts are also stated in group form, for the Jacobi character `jacobiChar R s`
lifted to modulus `m₀ s` (or `m₀ s₁ s₂`) and restricted to the units that reduce to `1`
modulo `m₀`, the kernel of `ZMod.unitsMap`.

The construction is the Chinese remainder theorem: `u ≡ 1` modulo `m₀` and modulo the other
primes, and `u` a quadratic nonresidue modulo one prime `p` that divides exactly one of the
numbers to the first power.

## Main statements

* `TauCeti.exists_modEq_one_jacobiSym_eq_neg_one_jacobiSym_eq_one`: if an odd prime `p` coprime
  to `m₀` divides `s₁` exactly once and does not divide `s₂`, some `u ≡ 1 (mod m₀)` prime to
  `m₀ s₁ s₂` has `J(u | s₁) = -1` and `J(u | s₂) = 1`.
* `TauCeti.exists_modEq_one_jacobiSym_eq_neg_one_of_squarefree`: nontriviality on the class
  of `1`, for odd squarefree `s > 1` prime to `m₀`.
* `TauCeti.exists_modEq_one_jacobiSym_ne_of_squarefree`: separation on the class of `1`, for
  distinct odd squarefree `s₁`, `s₂` prime to `m₀`.
* `TauCeti.sum_filter_modEq_jacobiSym_eq_zero_of_squarefree`: for odd squarefree `s > 1` prime
  to `m₀`, the sum of `J(b | s)` over `b < m₀ s` with `b ≡ a₀ (mod m₀)` and `b` prime to `m₀ s`
  is `0`.
* `TauCeti.exists_mem_ker_unitsMap_changeLevel_jacobiChar_eq_neg_one`: a value witness:
  `J(· | s)`, lifted to modulus `m₀ s`, takes the value `-1` at some unit in the kernel of
  `(ZMod (m₀ * s))ˣ →* (ZMod m₀)ˣ`.
* `TauCeti.domRestrict_ker_unitsMap_toUnitHom_changeLevel_jacobiChar_ne_one`: nontriviality on
  the class of `1`, group form: for `(-1 : R) ≠ 1` the restriction of the lifted character to
  that kernel is not the trivial homomorphism.
* `TauCeti.exists_mem_ker_unitsMap_changeLevel_jacobiChar_ne`: the group form of separation, with
  values in a nontrivial ring of characteristic not `2`.

## References

* [FormalProof] L. Alpöge, Lean formalization of the Riemann hypothesis for Dirichlet
  L-functions, <https://github.com/leanprover-community/riemann-hypothesis>: the source of the
  nontriviality and separation statements.
-/

public section

namespace TauCeti

/-- Let `p` be an odd prime coprime to `m₀` that divides `s₁` exactly once and does not divide
`s₂`. Then some natural number `u ≡ 1 (mod m₀)` prime to `m₀ s₁ s₂` has `J(u | s₁) = -1` and
`J(u | s₂) = 1`. -/
theorem exists_modEq_one_jacobiSym_eq_neg_one_jacobiSym_eq_one {m₀ s₁ s₂ p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpm : p.Coprime m₀) (hps₁ : p ∣ s₁) (hpps₁ : ¬ p ^ 2 ∣ s₁)
    (hps₂ : ¬ p ∣ s₂) :
    ∃ u : ℕ, u ≡ 1 [MOD m₀] ∧ u.Coprime (m₀ * s₁ * s₂) ∧ jacobiSym u s₁ = -1 ∧
      jacobiSym u s₂ = 1 := by
  obtain ⟨t, rfl⟩ := hps₁
  have hpt : ¬ p ∣ t := fun h ↦ hpps₁ (by rw [sq]; exact mul_dvd_mul_left p h)
  have hcop : p.Coprime (m₀ * t * s₂) :=
    (hpm.mul_right ((hp.coprime_iff_not_dvd).2 hpt)).mul_right ((hp.coprime_iff_not_dvd).2 hps₂)
  obtain ⟨u, hu, hJ⟩ := exists_modEq_one_jacobiSym_eq_neg_one_of_prime hp hp2 hcop
  -- `J(u | b) = 1` for every divisor `b` of `m₀ t s₂`, as `u ≡ 1 (mod b)`
  have hone : ∀ b, b ∣ m₀ * t * s₂ → jacobiSym u b = 1 := fun b hb ↦ by
    rw [jacobiSym.mod_left' (Int.natCast_modEq_iff.2 (hu.of_dvd hb)), Nat.cast_one,
      jacobiSym.one_left]
  have hup : u.Coprime p := by
    have h := mt (jacobiSym.eq_zero_iff (a := u) (b := p)).2 (by rw [hJ]; decide)
    simpa [Int.gcd_natCast_natCast, hp.ne_zero] using h
  have hun : u.Coprime (m₀ * t * s₂) := by
    rw [Nat.coprime_iff_gcd_eq_one, hu.gcd_eq, Nat.gcd_one_left]
  refine ⟨u, hu.of_dvd (dvd_mul_of_dvd_left (dvd_mul_right _ _) _), ?_, ?_,
    hone s₂ (dvd_mul_left _ _)⟩
  · exact (Nat.Coprime.mul_right hup hun).coprime_dvd_right (dvd_of_eq (by ring))
  · rw [jacobiSym.mul_right' _ hp.ne_zero (by rintro rfl; exact hpt (dvd_zero p)), hJ,
      hone t (dvd_mul_of_dvd_left (dvd_mul_left _ _) _), mul_one]

/-- **Nontriviality on the class of `1`.** For odd squarefree `s > 1` prime to `m₀`, some natural
number `u ≡ 1 (mod m₀)` prime to `m₀ s` has `J(u | s) = -1`: the Jacobi symbol `J(· | s)` is a
nontrivial character of the unit classes modulo `m₀ s` above the class of `1` modulo `m₀`. -/
theorem exists_modEq_one_jacobiSym_eq_neg_one_of_squarefree {m₀ s : ℕ} (hs : Odd s) (hs1 : 1 < s)
    (hsq : Squarefree s) (hsm : s.Coprime m₀) :
    ∃ u : ℕ, u ≡ 1 [MOD m₀] ∧ u.Coprime (m₀ * s) ∧ jacobiSym u s = -1 := by
  have hp := Nat.minFac_prime hs1.ne'
  have hp2 : s.minFac ≠ 2 := fun h ↦ hs.not_two_dvd_nat (h ▸ s.minFac_dvd)
  obtain ⟨u, hu, hcop, hJ, -⟩ := exists_modEq_one_jacobiSym_eq_neg_one_jacobiSym_eq_one hp hp2
    (hsm.coprime_dvd_left s.minFac_dvd) s.minFac_dvd
    (by rw [sq]; exact Nat.squarefree_iff_prime_squarefree.1 hsq _ hp) (s₂ := 1) hp.not_dvd_one
  exact ⟨u, hu, by simpa using hcop, hJ⟩

/-- **Separation on the class of `1`.** For distinct odd squarefree `s₁`, `s₂` prime to `m₀`,
some natural number `u ≡ 1 (mod m₀)` prime to `m₀ s₁ s₂` has `J(u | s₁) ≠ J(u | s₂)`. -/
theorem exists_modEq_one_jacobiSym_ne_of_squarefree {m₀ s₁ s₂ : ℕ} (hs₁ : Odd s₁)
    (hs₂ : Odd s₂) (hsq₁ : Squarefree s₁) (hsq₂ : Squarefree s₂) (hsm₁ : s₁.Coprime m₀)
    (hsm₂ : s₂.Coprime m₀) (hne : s₁ ≠ s₂) :
    ∃ u : ℕ, u ≡ 1 [MOD m₀] ∧ u.Coprime (m₀ * s₁ * s₂) ∧ jacobiSym u s₁ ≠ jacobiSym u s₂ := by
  -- a prime dividing exactly one of `s₁`, `s₂`
  obtain ⟨p, hp, hp'⟩ : ∃ p, p.Prime ∧ ¬ (p ∣ s₁ ↔ p ∣ s₂) := by
    simpa [Nat.prime_iff] using mt (Nat.Squarefree.ext_iff hsq₁ hsq₂).2 hne
  have key : ∀ {a b : ℕ}, Odd a → Squarefree a → a.Coprime m₀ → p ∣ a → ¬ p ∣ b →
      ∃ u : ℕ, u ≡ 1 [MOD m₀] ∧ u.Coprime (m₀ * a * b) ∧ jacobiSym u a = -1 ∧
        jacobiSym u b = 1 := fun ha hsq hsm hpa hpb ↦
    exists_modEq_one_jacobiSym_eq_neg_one_jacobiSym_eq_one hp
      (fun h ↦ ha.not_two_dvd_nat (h ▸ hpa)) (hsm.coprime_dvd_left hpa) hpa
      (by rw [sq]; exact Nat.squarefree_iff_prime_squarefree.1 hsq _ hp) hpb
  by_cases h₁ : p ∣ s₁
  · obtain ⟨u, hu, hcop, h₁, h₂⟩ := key hs₁ hsq₁ hsm₁ h₁ (fun h ↦ hp' ⟨fun _ ↦ h, fun _ ↦ h₁⟩)
    exact ⟨u, hu, hcop, by rw [h₁, h₂]; decide⟩
  · obtain ⟨u, hu, hcop, h₂, h₁⟩ := key hs₂ hsq₂ hsm₂ (by tauto) h₁
    exact ⟨u, hu, by rwa [mul_right_comm], by rw [h₁, h₂]; decide⟩

/-- **Cancellation on a class modulo `m₀`.** For odd squarefree `s > 1` prime to `m₀` and any
`a₀`, the sum of `J(b | s)` over the residues `b < m₀ s` that are prime to `m₀ s` and satisfy
`b ≡ a₀ (mod m₀)` is `0`. -/
theorem sum_filter_modEq_jacobiSym_eq_zero_of_squarefree {m₀ s a₀ : ℕ} (hs : Odd s) (hs1 : 1 < s)
    (hsq : Squarefree s) (hsm : s.Coprime m₀) :
    ∑ b ∈ (Finset.range (m₀ * s)).filter (fun b ↦ b ≡ a₀ [MOD m₀] ∧ b.Coprime (m₀ * s)),
      jacobiSym b s = 0 := by
  obtain ⟨u, hu, huc, hJ⟩ := exists_modEq_one_jacobiSym_eq_neg_one_of_squarefree hs hs1 hsq hsm
  -- multiplication by `u` modulo `m₀ s` preserves the conditions and negates `J(· | s)`
  have hcond (b : ℕ) : (u * b % (m₀ * s) ≡ a₀ [MOD m₀] ∧ (u * b % (m₀ * s)).Coprime (m₀ * s)) ↔
      (b ≡ a₀ [MOD m₀] ∧ b.Coprime (m₀ * s)) := by
    have h1 : u * b % (m₀ * s) ≡ b [MOD m₀] :=
      calc u * b % (m₀ * s) ≡ u * b [MOD m₀] := (Nat.mod_modEq _ _).of_dvd (dvd_mul_right m₀ s)
        _ ≡ 1 * b [MOD m₀] := hu.mul_right b
        _ = b := one_mul b
    rw [Nat.coprime_iff_gcd_eq_one, (Nat.mod_modEq _ _).gcd_eq, ← Nat.coprime_iff_gcd_eq_one,
      Nat.coprime_mul_iff_left]
    exact and_congr ⟨h1.symm.trans, h1.trans⟩ (and_iff_right huc)
  have hneg (b : ℕ) : jacobiSym ((u * b % (m₀ * s) : ℕ) : ℤ) s = -jacobiSym b s := by
    have h := Int.natCast_modEq_iff.2 ((Nat.mod_modEq (u * b) _).of_dvd (dvd_mul_left s m₀))
    rw [jacobiSym.mod_left' h, Nat.cast_mul, jacobiSym.mul_left, hJ, neg_one_mul]
  -- the summand as a function on `range (m₀ s)`, reindexed by `b ↦ u b mod m₀ s`
  let f : ℕ → ℤ := fun b ↦ if b ≡ a₀ [MOD m₀] ∧ b.Coprime (m₀ * s) then jacobiSym b s else 0
  have hf (b : ℕ) : f (u * b % (m₀ * s)) = -f b := by
    simp only [f, hcond, hneg]
    split_ifs <;> simp
  have key := huc.sum_range_mul_mod f
  rw [Finset.sum_congr rfl fun b _ ↦ hf b, Finset.sum_neg_distrib] at key
  rw [Finset.sum_filter]
  linarith

/-! ### The group form

The unit classes modulo `m₀ s` above the class of `1` modulo `m₀` form the kernel of the
reduction `ZMod.unitsMap : (ZMod (m₀ * s))ˣ →* (ZMod m₀)ˣ`, and `u ↦ J(u | s)` on them is the
Jacobi character `jacobiChar R s` lifted to modulus `m₀ * s` by `DirichletCharacter.changeLevel`.
-/

/-- **A value `-1` on the class of `1`.** For odd squarefree `s > 1` prime to `m₀`, the Jacobi
character `J(· | s)`, lifted to modulus `m₀ s`, takes the value `-1` at some unit of
`ZMod (m₀ * s)` that reduces to `1` modulo `m₀`. When `(-1 : R) ≠ 1` this makes the restriction
to that subgroup nontrivial: see
`domRestrict_ker_unitsMap_toUnitHom_changeLevel_jacobiChar_ne_one`. -/
theorem exists_mem_ker_unitsMap_changeLevel_jacobiChar_eq_neg_one (R : Type*) [CommRing R]
    {m₀ s : ℕ} [NeZero s] (hs : Odd s) (hs1 : s ≠ 1) (hsq : Squarefree s)
    (hsm : s.Coprime m₀) :
    ∃ u ∈ (ZMod.unitsMap (dvd_mul_right m₀ s)).ker,
      (jacobiChar R s).changeLevel (dvd_mul_left s m₀) u = -1 := by
  obtain ⟨u, hu, huc, hJ⟩ := exists_modEq_one_jacobiSym_eq_neg_one_of_squarefree hs
    (Nat.one_lt_iff_ne_zero_and_ne_one.2 ⟨NeZero.ne s, hs1⟩) hsq hsm
  refine ⟨ZMod.unitOfCoprime u huc, ?_, ?_⟩
  · exact (ZMod.unitOfCoprime_mem_ker_unitsMap_iff _ huc).2 hu
  · simp [DirichletCharacter.changeLevel_natCast_of_coprime _ _ huc, hJ]

/-- **Nontriviality on the class of `1`, as a homomorphism.** For odd squarefree `s > 1` prime
to `m₀` and a ring `R` in which `-1 ≠ 1`, the Jacobi character `J(· | s)`, lifted to modulus
`m₀ s` and restricted to the units of `ZMod (m₀ * s)` that reduce to `1` modulo `m₀`, is not
the trivial homomorphism. -/
theorem domRestrict_ker_unitsMap_toUnitHom_changeLevel_jacobiChar_ne_one {R : Type*} [CommRing R]
    (hR : (-1 : R) ≠ 1) {m₀ s : ℕ} [NeZero s] (hs : Odd s) (hs1 : s ≠ 1) (hsq : Squarefree s)
    (hsm : s.Coprime m₀) :
    ((jacobiChar R s).changeLevel (dvd_mul_left s m₀)).toUnitHom.domRestrict
      (ZMod.unitsMap (dvd_mul_right m₀ s)).ker ≠ 1 := by
  obtain ⟨u, hu, hval⟩ :=
    exists_mem_ker_unitsMap_changeLevel_jacobiChar_eq_neg_one R hs hs1 hsq hsm
  intro h
  have h1 := congrArg Units.val (DFunLike.congr_fun h ⟨u, hu⟩)
  rw [MonoidHom.domRestrict_apply, MulChar.coe_toUnitHom, hval, MonoidHom.one_apply,
    Units.val_one] at h1
  exact hR h1

/-- **Separation on the class of `1`, group form.** For distinct odd squarefree `s₁`, `s₂` prime
to `m₀` and a nontrivial ring `R` of characteristic not `2`, the Jacobi characters `J(· | s₁)`
and `J(· | s₂)`, lifted to modulus `m₀ s₁ s₂`, differ at some unit of `ZMod (m₀ * s₁ * s₂)`
that reduces to `1` modulo `m₀`. -/
theorem exists_mem_ker_unitsMap_changeLevel_jacobiChar_ne (R : Type*) [CommRing R]
    [Nontrivial R] (hR : ringChar R ≠ 2) {m₀ s₁ s₂ : ℕ} [NeZero s₁] [NeZero s₂] (hs₁ : Odd s₁)
    (hs₂ : Odd s₂) (hsq₁ : Squarefree s₁) (hsq₂ : Squarefree s₂) (hsm₁ : s₁.Coprime m₀)
    (hsm₂ : s₂.Coprime m₀) (hne : s₁ ≠ s₂) :
    ∃ u ∈ (ZMod.unitsMap (dvd_mul_of_dvd_left (dvd_mul_right m₀ s₁) s₂)).ker,
      (jacobiChar R s₁).changeLevel (dvd_mul_of_dvd_left (dvd_mul_left s₁ m₀) s₂) u ≠
        (jacobiChar R s₂).changeLevel (dvd_mul_left s₂ (m₀ * s₁)) u := by
  obtain ⟨u, hu, huc, hJ⟩ :=
    exists_modEq_one_jacobiSym_ne_of_squarefree hs₁ hs₂ hsq₁ hsq₂ hsm₁ hsm₂ hne
  refine ⟨ZMod.unitOfCoprime u huc, ?_, ?_⟩
  · exact (ZMod.unitOfCoprime_mem_ker_unitsMap_iff _ huc).2 hu
  · simp only [ZMod.coe_unitOfCoprime, DirichletCharacter.changeLevel_natCast_of_coprime _ _ huc,
      jacobiChar_natCast]
    -- the two Jacobi symbols are distinct elements of `{0, 1, -1}`, which embeds in `R`
    have hmem (t : ℕ) : jacobiSym u t ∈ ({0, 1, -1} : Set ℤ) := by
      rcases jacobiSym.trichotomy u t with h | h | h <;> simp [h]
    exact fun h ↦ hJ (Int.cast_injOn_of_ringChar_ne_two hR (hmem s₁) (hmem s₂) h)

end TauCeti
