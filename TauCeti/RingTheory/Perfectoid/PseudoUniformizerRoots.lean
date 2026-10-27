/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Perfection
public import TauCeti.RingTheory.Huber.Basic
import Mathlib.Algebra.CharP.Reduced
import TauCeti.RingTheory.Perfect.Basic

/-!
# Pseudouniformisers with compatible `p`-power roots

Let `R` be a nonarchimedean topological ring, for instance a Tate ring, and `p` a natural number.
A *pseudouniformiser with compatible `p`-power roots* is an element
`ϖ♭ = (ϖ ^ (1 / p ^ n))ₙ` of the multiplicative monoid `lim_{x ↦ x ^ p} R` (Mathlib's
`Perfection R p`) whose zeroth term `ϖ` is a pseudouniformiser of `R` with `ϖ ^ p ∣ p` in the
power-bounded subring `R°`. Every perfectoid Tate ring admits one (Scholze, *Étale cohomology of
diamonds*, Lemma 3.10), and they are the parameters with which the tilt `R♭`, the sharp map and
the spectral norm of a perfectoid Tate ring are set up: the roots give a pseudouniformiser of the
tilt, and the powers `ϖ ^ q` with `q ∈ ℤ[1/p]` measure elements of `R`.

This file sets up the root system. Every root `ϖ ^ (1 / p ^ n)` is again a pseudouniformiser in
`R°` (`PseudoUniformizerRoots.isPseudoUniformizer_root`), and its `p`-th power still divides `p`
in `R°`. For `m : ℤ` and `n : ℕ` the unit `PseudoUniformizerRoots.zpow ϖ m n = ϖ ^ (m / p ^ n)`
depends only on the fraction `m / p ^ n` (`PseudoUniformizerRoots.zpow_eq_zpow`), is additive in
the exponent, lies in `R°` for `m ≥ 0` and is a pseudouniformiser for `m > 0`.

In characteristic `p` the roots are determined by `ϖ` as soon as `R` is reduced, as perfectoid
Tate rings are; if `R` is moreover perfect, every pseudouniformiser has compatible roots, so the
structure is equivalent to the choice of a pseudouniformiser
(`PseudoUniformizerRoots.equivOfPerfectRing`).

## Main definitions

* `TauCeti.Perfectoid.PseudoUniformizerRoots p R`: pseudouniformisers of `R` with compatible
  `p`-power roots whose `p`-th power divides `p` in `R°`.
* `TauCeti.Perfectoid.PseudoUniformizerRoots.root`: the root `ϖ ^ (1 / p ^ n)`, and
  `PseudoUniformizerRoots.rootPB`: the same root as an element of `R°`.
* `TauCeti.Perfectoid.PseudoUniformizerRoots.zpow`: the unit `ϖ ^ (m / p ^ n)` of `R`.
* `TauCeti.Perfectoid.PseudoUniformizerRoots.equivOfPerfectRing`: in a perfect ring of
  characteristic `p`, the structure is the choice of a pseudouniformiser.

## Main results

* `TauCeti.Perfectoid.PseudoUniformizerRoots.isPseudoUniformizer_root`: every root is a
  pseudouniformiser.
* `TauCeti.Perfectoid.PseudoUniformizerRoots.rootPB_pow_dvd`: the `p`-th power of every root
  divides `p` in `R°`.
* `TauCeti.Perfectoid.PseudoUniformizerRoots.zpow_eq_zpow`: `ϖ ^ (m / p ^ n)` depends only on
  `m / p ^ n`.
* `TauCeti.Perfectoid.PseudoUniformizerRoots.eq_of_root_zero_eq`: in a reduced ring of
  characteristic `p`, the roots of `ϖ` are unique.

## References

* P. Scholze, *Étale cohomology of diamonds*, §3, Lemma 3.10 and its proof.
* P. Scholze, *Perfectoid spaces*, Remark 3.5.
* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, Lemma 6.2.2 and its proof.
-/

public section

open TauCeti.Huber

namespace TauCeti.Perfectoid

variable (p : ℕ) (R : Type*) [CommRing R] [TopologicalSpace R] [NonarchimedeanRing R]

/-- A *pseudouniformiser with compatible `p`-power roots* of a nonarchimedean topological ring `R`:
a compatible system `ϖ♭ = (ϖ ^ (1 / p ^ n))ₙ` of `p`-power roots, an element of Mathlib's
`Perfection R p`, whose zeroth term `ϖ` is a pseudouniformiser with `ϖ ^ p ∣ p` in `R°`. The
pseudouniformiser `ϖ` lies in `R°`, being topologically nilpotent. -/
structure PseudoUniformizerRoots where
  /-- The compatible system `(ϖ ^ (1 / p ^ n))ₙ` of `p`-power roots. -/
  roots : Perfection R p
  /-- The zeroth term `ϖ` of the system is a pseudouniformiser. -/
  isPseudoUniformizer : IsPseudoUniformizer (Perfection.coeffMonoidHom R p 0 roots)
  /-- The `p`-th power of `ϖ` divides `p` in `R°`. -/
  pow_dvd : (⟨Perfection.coeffMonoidHom R p 0 roots, mem_powerBoundedSubring.mpr <|
    .of_isTopologicallyNilpotent isPseudoUniformizer.isTopologicallyNilpotent⟩ :
      powerBoundedSubring R) ^ p ∣ (p : powerBoundedSubring R)

namespace PseudoUniformizerRoots

variable {p R} (ϖ : PseudoUniformizerRoots p R)

/-- The root `ϖ ^ (1 / p ^ n)`: the `n`-th term of the compatible system. The pseudouniformiser
itself is `ϖ.root 0`. -/
def root (n : ℕ) : R :=
  Perfection.coeffMonoidHom R p n ϖ.roots

/-- The coordinates of the compatible system are the roots. -/
@[simp]
theorem coeffMonoidHom_roots (n : ℕ) : Perfection.coeffMonoidHom R p n ϖ.roots = ϖ.root n :=
  (rfl)

/-- A pseudouniformiser with compatible roots is determined by its roots. -/
@[ext]
theorem ext {ϖ ϖ' : PseudoUniformizerRoots p R} (h : ∀ n, ϖ.root n = ϖ'.root n) : ϖ = ϖ' := by
  have hr : ϖ.roots = ϖ'.roots := Perfection.extMonoid h
  cases ϖ
  cases ϖ'
  cases hr
  rfl

/-- Each root is the `p`-th power of the next one. -/
@[simp]
theorem root_succ_pow (n : ℕ) : ϖ.root (n + 1) ^ p = ϖ.root n :=
  Perfection.coeffMonoidHom_pow_p' ϖ.roots n

/-- `(ϖ ^ (1 / p ^ (m + n))) ^ (p ^ n) = ϖ ^ (1 / p ^ m)`. -/
@[simp]
theorem root_add_pow (m n : ℕ) : ϖ.root (m + n) ^ p ^ n = ϖ.root m :=
  Perfection.coeffMonoidHom_pow_p_pow' ϖ.roots m n

/-- `(ϖ ^ (1 / p ^ n)) ^ (p ^ n) = ϖ`. -/
@[simp]
theorem root_pow (n : ℕ) : ϖ.root n ^ p ^ n = ϖ.root 0 :=
  Perfection.coeffMonoidHom_pow_p_pow_self ϖ.roots n

/-- The zeroth root is the pseudouniformiser `ϖ`. -/
theorem isPseudoUniformizer_root_zero : IsPseudoUniformizer (ϖ.root 0) :=
  ϖ.isPseudoUniformizer

variable [NeZero p]

/-- **Every root `ϖ ^ (1 / p ^ n)` is a pseudouniformiser**: its `p ^ n`-th power `ϖ` is a
topologically nilpotent unit. -/
theorem isPseudoUniformizer_root (n : ℕ) : IsPseudoUniformizer (ϖ.root n) := by
  have hn : p ^ n ≠ 0 := pow_ne_zero n (NeZero.ne p)
  have h := ϖ.isPseudoUniformizer_root_zero
  rw [← ϖ.root_pow n] at h
  exact isPseudoUniformizer_iff.mpr
    ⟨(isUnit_pow_iff hn).mp h.isUnit, h.isTopologicallyNilpotent.of_pow hn⟩

/-- The root `ϖ ^ (1 / p ^ n)` as an element of the power-bounded subring `R°`. -/
def rootPB (n : ℕ) : powerBoundedSubring R :=
  ⟨ϖ.root n, mem_powerBoundedSubring.mpr <|
    .of_isTopologicallyNilpotent (ϖ.isPseudoUniformizer_root n).isTopologicallyNilpotent⟩

/-- The root in `R°` has underlying element the root in `R`. -/
@[simp, norm_cast]
theorem coe_rootPB (n : ℕ) : (ϖ.rootPB n : R) = ϖ.root n :=
  (rfl)

/-- In `R°`, each root is the `p`-th power of the next one. -/
@[simp]
theorem rootPB_succ_pow (n : ℕ) : ϖ.rootPB (n + 1) ^ p = ϖ.rootPB n :=
  Subtype.ext (by simp)

/-- In `R°`, `(ϖ ^ (1 / p ^ (m + n))) ^ (p ^ n) = ϖ ^ (1 / p ^ m)`. -/
@[simp]
theorem rootPB_add_pow (m n : ℕ) : ϖ.rootPB (m + n) ^ p ^ n = ϖ.rootPB m :=
  Subtype.ext (by simp)

/-- In `R°`, `(ϖ ^ (1 / p ^ n)) ^ (p ^ n) = ϖ`. -/
@[simp]
theorem rootPB_pow (n : ℕ) : ϖ.rootPB n ^ p ^ n = ϖ.rootPB 0 :=
  Subtype.ext (by simp)

/-- In `R°`, a deeper root divides a shallower one: `ϖ ^ (1 / p ^ n) ∣ ϖ ^ (1 / p ^ m)` for
`m ≤ n`. -/
theorem rootPB_dvd_rootPB {m n : ℕ} (h : m ≤ n) : ϖ.rootPB n ∣ ϖ.rootPB m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [← ϖ.rootPB_add_pow m k]
  exact dvd_pow_self _ (pow_ne_zero k (NeZero.ne p))

/-- **The `p`-th power of every root divides `p` in `R°`.** -/
theorem rootPB_pow_dvd (n : ℕ) : ϖ.rootPB n ^ p ∣ (p : powerBoundedSubring R) :=
  (pow_dvd_pow_of_dvd (ϖ.rootPB_dvd_rootPB n.zero_le) p).trans ϖ.pow_dvd

/-- The root `ϖ ^ (1 / p ^ n)` as a unit of `R`. -/
noncomputable def unitRoot (n : ℕ) : Rˣ :=
  (ϖ.isPseudoUniformizer_root n).isUnit.unit

/-- The root as a unit has underlying element the root. -/
@[simp, norm_cast]
theorem coe_unitRoot (n : ℕ) : (ϖ.unitRoot n : R) = ϖ.root n :=
  (ϖ.isPseudoUniformizer_root n).isUnit.unit_spec

/-- As units, each root is the `p`-th power of the next one. -/
@[simp]
theorem unitRoot_succ_pow (n : ℕ) : ϖ.unitRoot (n + 1) ^ p = ϖ.unitRoot n :=
  Units.ext (by simp)

/-- The unit `ϖ ^ (m / p ^ n)` of `R`, the `m`-th power of the root `ϖ ^ (1 / p ^ n)`. It depends
only on the fraction `m / p ^ n ∈ ℤ[1/p]` (`zpow_eq_zpow`). -/
noncomputable def zpow (m : ℤ) (n : ℕ) : Rˣ :=
  ϖ.unitRoot n ^ m

/-- Unfolding lemma for `zpow`. -/
theorem zpow_def (m : ℤ) (n : ℕ) : ϖ.zpow m n = ϖ.unitRoot n ^ m :=
  (rfl)

/-- For a natural exponent, `ϖ ^ (m / p ^ n)` is the `m`-th power of the root. -/
@[simp, norm_cast]
theorem coe_zpow_natCast (m n : ℕ) : (ϖ.zpow m n : R) = ϖ.root n ^ m := by
  simp [zpow_def]

/-- `ϖ ^ (0 / p ^ n) = 1`. -/
@[simp]
theorem zpow_zero (n : ℕ) : ϖ.zpow 0 n = 1 :=
  _root_.zpow_zero _

/-- `ϖ ^ (1 / p ^ n)` is the root. -/
@[simp]
theorem zpow_one (n : ℕ) : ϖ.zpow 1 n = ϖ.unitRoot n :=
  _root_.zpow_one _

/-- `ϖ ^ ((m + m') / p ^ n) = ϖ ^ (m / p ^ n) * ϖ ^ (m' / p ^ n)`. -/
theorem zpow_add (m m' : ℤ) (n : ℕ) : ϖ.zpow (m + m') n = ϖ.zpow m n * ϖ.zpow m' n :=
  _root_.zpow_add _ m m'

/-- `ϖ ^ (-m / p ^ n)` is the inverse of `ϖ ^ (m / p ^ n)`. -/
@[simp]
theorem zpow_neg (m : ℤ) (n : ℕ) : ϖ.zpow (-m) n = (ϖ.zpow m n)⁻¹ :=
  _root_.zpow_neg _ m

/-- Passing to the next root: `ϖ ^ (m p / p ^ (n + 1)) = ϖ ^ (m / p ^ n)`. -/
@[simp]
theorem zpow_mul_p (m : ℤ) (n : ℕ) : ϖ.zpow (m * p) (n + 1) = ϖ.zpow m n := by
  rw [zpow_def, zpow_def, mul_comm, zpow_mul, zpow_natCast, unitRoot_succ_pow]

/-- Passing to deeper roots: `ϖ ^ (m p ^ k / p ^ (n + k)) = ϖ ^ (m / p ^ n)`. -/
theorem zpow_mul_pow (m : ℤ) (n k : ℕ) : ϖ.zpow (m * p ^ k) (n + k) = ϖ.zpow m n := by
  induction k with
  | zero => simp
  | succ k ih => rw [← add_assoc, pow_succ, ← mul_assoc, zpow_mul_p, ih]

/-- **`ϖ ^ (m / p ^ n)` depends only on the fraction `m / p ^ n`.** -/
theorem zpow_eq_zpow {m m' : ℤ} {n n' : ℕ} (h : m * p ^ n' = m' * p ^ n) :
    ϖ.zpow m n = ϖ.zpow m' n' := by
  rw [← ϖ.zpow_mul_pow m n n', ← ϖ.zpow_mul_pow m' n' n, h, add_comm]

/-- For `m ≥ 0`, `ϖ ^ (m / p ^ n)` lies in `R°`. -/
theorem zpow_mem_powerBoundedSubring {m : ℤ} (hm : 0 ≤ m) (n : ℕ) :
    (ϖ.zpow m n : R) ∈ powerBoundedSubring R := by
  lift m to ℕ using hm
  rw [coe_zpow_natCast, ← coe_rootPB]
  exact pow_mem (ϖ.rootPB n).2 m

/-- For `m > 0`, `ϖ ^ (m / p ^ n)` is a pseudouniformiser. -/
theorem isPseudoUniformizer_zpow {m : ℤ} (hm : 0 < m) (n : ℕ) :
    IsPseudoUniformizer (ϖ.zpow m n : R) := by
  lift m to ℕ using hm.le
  refine isPseudoUniformizer_iff.mpr ⟨Units.isUnit _, ?_⟩
  rw [coe_zpow_natCast]
  exact (ϖ.isPseudoUniformizer_root n).isTopologicallyNilpotent.pow (by omega)

end PseudoUniformizerRoots

section Frobenius

namespace PseudoUniformizerRoots

variable {p R}

/-- **In a reduced ring of exponential characteristic `p`, the compatible roots of `ϖ` are
unique**: Frobenius is injective, so each root is determined by the previous one. This applies to
perfectoid Tate rings of characteristic `p`, which are reduced. -/
theorem eq_of_root_zero_eq [ExpChar R p] [IsReduced R] {ϖ ϖ' : PseudoUniformizerRoots p R}
    (h : ϖ.root 0 = ϖ'.root 0) : ϖ = ϖ' := by
  ext n
  induction n with
  | zero => exact h
  | succ n ih =>
    refine frobenius_inj R p ?_
    simpa [frobenius_def] using ih

variable (p R) [Fact p.Prime] [CharP R p] [PerfectRing R p]

/-- **In a perfect ring of characteristic `p`, a pseudouniformiser with compatible roots is the
choice of a pseudouniformiser**: every pseudouniformiser `ϖ` has the unique compatible system
`(ϖ ^ (1 / p ^ n))ₙ` of `p`-power roots given by inverting Frobenius, and `ϖ ^ p ∣ p = 0` holds
automatically. -/
noncomputable def equivOfPerfectRing :
    PseudoUniformizerRoots p R ≃ {ϖ : R // IsPseudoUniformizer ϖ} where
  toFun ϖ := ⟨ϖ.root 0, ϖ.isPseudoUniformizer⟩
  invFun ϖ :=
    { roots := Perfection.liftMonoidHom p R R (MonoidHom.id R) ϖ
      isPseudoUniformizer := by simpa using ϖ.2
      pow_dvd := by
        have hp : (p : powerBoundedSubring R) = 0 := Subtype.ext (CharP.cast_eq_zero R p)
        rw [hp]
        exact dvd_zero _ }
  left_inv ϖ := by
    have := isReduced_of_perfectRing R p
    exact eq_of_root_zero_eq (by simp [← coeffMonoidHom_roots])
  right_inv ϖ := Subtype.ext (by simp [← coeffMonoidHom_roots])

/-- The pseudouniformiser chosen by `equivOfPerfectRing` is the zeroth root. -/
@[simp]
theorem coe_equivOfPerfectRing_apply (ϖ : PseudoUniformizerRoots p R) :
    (equivOfPerfectRing p R ϖ : R) = ϖ.root 0 :=
  (rfl)

/-- The compatible roots attached to a pseudouniformiser `ϖ` by `equivOfPerfectRing` start at
`ϖ`. -/
@[simp]
theorem root_zero_equivOfPerfectRing_symm_apply (ϖ : {ϖ : R // IsPseudoUniformizer ϖ}) :
    ((equivOfPerfectRing p R).symm ϖ).root 0 = ϖ := by
  rw [← coe_equivOfPerfectRing_apply, Equiv.apply_symm_apply]

end PseudoUniformizerRoots

end Frobenius

end TauCeti.Perfectoid
