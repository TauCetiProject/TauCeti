/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.QuotSMulTop
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.RingTheory.Ideal.Colon
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.RingTheory.QuotSMulTop

/-!
# Ordinary and modified Tate lattices

Fix a prime `p` and a weight `r ≥ 0`, and write `a = ⌊r / (p - 1)⌋`. In the Fontaine–Messing
fundamental exact sequence of `p`-adic period rings, the kernel of `1 - φ / p ^ r` on `F^r A_cris`
is not the Tate lattice `ℤ_p(r) = ℤ_p t ^ r` itself but the larger *modified Tate lattice*
`(p ^ a a!)⁻¹ ℤ_p(r)`. Colmez and Nizioł instead record the lattice `p ^ (-a) ℤ_p(r)`. The
syntomic period maps of Ertl and Nizioł in weight `r` take values in the modified lattice, so
comparing error exponents between these sources requires comparing the two lattices.

All of these lattices are scalar multiples of one rank-one `ℚ_p`-line, so after choosing a generator
`t ^ r` of `ℤ_p(r)` they are realized as `ℤ_p`-submodules of `ℚ_p`:

* `TauCeti.invPowLattice p a = p ^ (-a) ℤ_p`, for every exponent `a`;
* `TauCeti.modifiedTateLattice p r = (p ^ a a!)⁻¹ ℤ_p`, spanned by
  `TauCeti.modifiedTateGenerator p r`.

Their reductions modulo `p ^ n` are the quotients `L ⧸ p ^ n L`, written `QuotSMulTop (p ^ n) L`,
not subgroups of `ℤ/p ^ n` obtained by dividing elements.

## Main results

* `TauCeti.mem_invPowLattice_iff`: `x ∈ p ^ (-a) ℤ_p` exactly when `‖x‖ ≤ p ^ a`.
* `TauCeti.invPowLattice_le_invPowLattice_iff`, `TauCeti.invPowLattice_mul_invPowLattice`:
  these lattices are ordered by their exponents and multiply by adding exponents. In particular
  the floor exponents `⌊r / (p - 1)⌋` are superadditive, so the lattices `p ^ (-⌊r / (p - 1)⌋) ℤ_p`
  are closed under products of weights (`TauCeti.invPowLattice_div_mul_invPowLattice_div_le`).
* `TauCeti.pow_sub_mem_annihilator_range_inclusion`: for `a ≤ b`, the inclusion
  `p ^ (-a) ℤ_p ⊆ p ^ (-b) ℤ_p` has cokernel killed by `p ^ (b - a)`; so do the kernel and cokernel
  of its reduction modulo `p ^ n`, by `QuotSMulTop.mem_annihilator_ker_map`.
* `TauCeti.injective_quotSMulTop_map_inclusion_iff`: that reduction modulo `p ^ n`, `n ≥ 1`, is
  injective only when the two lattices coincide.
* `TauCeti.modifiedTateLattice_eq_invPowLattice`: the modified lattice is
  `p ^ (-(a + v_p(a!))) ℤ_p`. Hence it contains `p ^ (-a) ℤ_p` with cokernel killed by
  `p ^ v_p(a!)` (`TauCeti.pow_multiplicity_factorial_mem_annihilator_range_inclusion`), with
  equality exactly when `a < p`, i.e. when `a!` is a `p`-adic unit
  (`TauCeti.modifiedTateLattice_eq_invPowLattice_iff`), and it is `ℤ_p` exactly in the weights
  `r < p - 1` (`TauCeti.modifiedTateLattice_eq_one_iff`).
* `TauCeti.factorial_smul_modifiedTateGenerator`,
  `TauCeti.pow_mul_factorial_smul_modifiedTateGenerator`: in the coordinate of the modified
  generator, the generator `p ^ (-a)` has coordinate `a!` and the ordinary generator `1` has
  coordinate `p ^ a a!`.
* `TauCeti.modifiedTateLattice_mul_modifiedTateLattice_le`: multiplication of Tate lines restricts
  to the modified lattices, `L(r) L(s) ⊆ L(r + s)`.

For example, at `p = 2` and `r = 2` the modified lattice `(1/8) ℤ_2` strictly contains
`(1/4) ℤ_2`, and the reduction modulo `2` of the inclusion is zero although both quotients are
`𝔽_2`; at `p = 3` and `r = 4` both lattices are `(1/9) ℤ_3`, because `2` is a `3`-adic unit.

## References

* V. Ertl and W. Nizioł, *Syntomic cohomology and p-adic motivic cohomology*,
  Algebraic Geometry 6 (2019), §2.2.
* P. Colmez and W. Nizioł, *Syntomic complexes and p-adic nearby cycles*, Invent. Math. 208
  (2017), §§1.1.1, 2.4.3.
* J. Nekovář and W. Nizioł, *Syntomic cohomology and p-adic regulators for varieties over p-adic
  fields*, Algebra Number Theory 10 (2016), §4.1.
-/

public section

open Submodule
open scoped Nat Pointwise

namespace TauCeti

noncomputable section

variable (p : ℕ) [hp : Fact p.Prime]

/-- The lattice `p ^ (-a) ℤ_p` in `ℚ_p`. At the floor exponent `a = ⌊r / (p - 1)⌋` it is the
coordinate form of Colmez–Nizioł's lattice `p ^ (-a) ℤ_p(r)`. -/
def invPowLattice (a : ℕ) : Submodule ℤ_[p] ℚ_[p] :=
  ℤ_[p] ∙ ((p : ℚ_[p]) ^ a)⁻¹

/-- The generator `(p ^ a a!)⁻¹`, with `a = ⌊r / (p - 1)⌋`, of the modified Tate lattice of
weight `r`, in the coordinate in which the ordinary Tate lattice is spanned by `1`. -/
def modifiedTateGenerator (r : ℕ) : ℚ_[p] :=
  ((p : ℚ_[p]) ^ (r / (p - 1)) * ((r / (p - 1))! : ℚ_[p]))⁻¹

/-- The modified Tate lattice `(p ^ a a!)⁻¹ ℤ_p` of weight `r`, with `a = ⌊r / (p - 1)⌋`: the
kernel lattice of the Fontaine–Messing fundamental exact sequence in weight `r`, in the coordinate
in which the ordinary Tate lattice `ℤ_p(r)` is `ℤ_p`. -/
def modifiedTateLattice (r : ℕ) : Submodule ℤ_[p] ℚ_[p] :=
  ℤ_[p] ∙ modifiedTateGenerator p r

variable {p}

theorem invPowLattice_def (a : ℕ) : invPowLattice p a = ℤ_[p] ∙ ((p : ℚ_[p]) ^ a)⁻¹ :=
  (rfl)

theorem modifiedTateLattice_def (r : ℕ) :
    modifiedTateLattice p r = ℤ_[p] ∙ modifiedTateGenerator p r :=
  (rfl)

theorem modifiedTateGenerator_mem_modifiedTateLattice (r : ℕ) :
    modifiedTateGenerator p r ∈ modifiedTateLattice p r :=
  mem_span_singleton_self _

/-! ### The lattices `p ^ (-a) ℤ_p` -/

/-- `p ^ (-a) ℤ_p` is the closed ball of radius `p ^ a` in `ℚ_p`. -/
theorem mem_invPowLattice_iff {a : ℕ} {x : ℚ_[p]} : x ∈ invPowLattice p a ↔ ‖x‖ ≤ (p : ℝ) ^ a := by
  rw [invPowLattice_def, PadicInt.mem_span_singleton_iff_norm_le]
  simp

theorem inv_p_pow_mem_invPowLattice (a : ℕ) : ((p : ℚ_[p]) ^ a)⁻¹ ∈ invPowLattice p a :=
  mem_span_singleton_self _

@[simp]
theorem invPowLattice_le_invPowLattice_iff {a b : ℕ} :
    invPowLattice p a ≤ invPowLattice p b ↔ a ≤ b := by
  rw [invPowLattice_def, span_singleton_le_iff_mem, mem_invPowLattice_iff]
  simpa using pow_le_pow_iff_right₀ (by exact_mod_cast hp.out.one_lt : 1 < (p : ℝ))

theorem invPowLattice_strictMono : StrictMono (invPowLattice p) :=
  strictMono_of_le_iff_le fun _ _ ↦ invPowLattice_le_invPowLattice_iff.symm

theorem invPowLattice_mono : Monotone (invPowLattice p) :=
  invPowLattice_strictMono.monotone

@[simp]
theorem invPowLattice_inj {a b : ℕ} : invPowLattice p a = invPowLattice p b ↔ a = b :=
  invPowLattice_strictMono.injective.eq_iff

/-- At exponent zero the lattice is `ℤ_p` itself, the unit of multiplication of submodules. -/
@[simp]
theorem invPowLattice_zero : invPowLattice p 0 = 1 := by
  rw [invPowLattice_def, pow_zero, inv_one, one_eq_span]

@[simp]
theorem invPowLattice_eq_one_iff {a : ℕ} : invPowLattice p a = 1 ↔ a = 0 := by
  rw [← invPowLattice_zero, invPowLattice_inj]

theorem one_le_invPowLattice (a : ℕ) : 1 ≤ invPowLattice p a :=
  invPowLattice_zero (p := p) ▸ invPowLattice_mono a.zero_le

/-- The simp-normal form of `TauCeti.one_le_invPowLattice`, by `Submodule.one_le`. -/
@[simp]
theorem one_mem_invPowLattice (a : ℕ) : (1 : ℚ_[p]) ∈ invPowLattice p a :=
  one_le.mp (one_le_invPowLattice a)

@[simp]
theorem invPowLattice_le_one_iff {a : ℕ} : invPowLattice p a ≤ 1 ↔ a = 0 := by
  rw [← invPowLattice_zero, invPowLattice_le_invPowLattice_iff, Nat.le_zero]

theorem invPowLattice_mul_invPowLattice (a b : ℕ) :
    invPowLattice p a * invPowLattice p b = invPowLattice p (a + b) := by
  rw [invPowLattice_def, invPowLattice_def, invPowLattice_def, span_mul_span,
    Set.singleton_mul_singleton, pow_add, mul_inv]

/-- The lattices `p ^ (-⌊r / (p - 1)⌋) ℤ_p` are closed under products of weights, because the floor
exponents are superadditive. An exponent smaller than `⌊(r + s) / (p - 1)⌋` in weight `r + s` can
fail this: by `TauCeti.invPowLattice_mul_invPowLattice` and
`TauCeti.invPowLattice_le_invPowLattice_iff`, `p ^ (-1) ℤ_p p ^ (-1) ℤ_p ⊄ p ^ (-1) ℤ_p`. -/
theorem invPowLattice_div_mul_invPowLattice_div_le (r s : ℕ) :
    invPowLattice p (r / (p - 1)) * invPowLattice p (s / (p - 1)) ≤
      invPowLattice p ((r + s) / (p - 1)) := by
  rw [invPowLattice_mul_invPowLattice, invPowLattice_le_invPowLattice_iff]
  exact Nat.div_add_div_le_add_div

/-- Multiplication by `p ^ c` carries `p ^ (-(a + c)) ℤ_p` into `p ^ (-a) ℤ_p`. -/
theorem pow_smul_mem_invPowLattice {a c : ℕ} {x : ℚ_[p]} (hx : x ∈ invPowLattice p (a + c)) :
    (p : ℤ_[p]) ^ c • x ∈ invPowLattice p a := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  obtain ⟨d, rfl⟩ := mem_span_singleton.mp hx
  refine mem_span_singleton.mpr ⟨d, ?_⟩
  simp only [Algebra.smul_def, PadicInt.algebraMap_apply, PadicInt.coe_pow, PadicInt.coe_natCast]
  field_simp
  ring

/-- For `a ≤ b`, the inclusion `p ^ (-a) ℤ_p ⊆ p ^ (-b) ℤ_p` has cokernel killed by
`p ^ (b - a)`. By `QuotSMulTop.mem_annihilator_ker_map` and `QuotSMulTop.mem_annihilator_range_map`
the same power kills the kernel and the cokernel of its reduction modulo every `p ^ n`. -/
theorem pow_sub_mem_annihilator_range_inclusion {a b : ℕ} (hab : a ≤ b) :
    (p : ℤ_[p]) ^ (b - a) ∈
      Module.annihilator ℤ_[p] (invPowLattice p b ⧸ LinearMap.range
        (inclusion (invPowLattice_mono hab))) := by
  rw [annihilator_quotient, mem_colon]
  rintro ⟨y, hy⟩ -
  rw [← Nat.add_sub_cancel' hab] at hy
  exact ⟨⟨_, pow_smul_mem_invPowLattice hy⟩, rfl⟩

/-- The reduction modulo `p ^ n`, `n ≥ 1`, of the inclusion `p ^ (-a) ℤ_p ⊆ p ^ (-b) ℤ_p` is
injective only when the lattices coincide. For `a < b` it kills the class of `p ^ (n - 1) p ^ (-a)`,
which is nonzero in `p ^ (-a) ℤ_p ⧸ p ^ n`. -/
theorem injective_quotSMulTop_map_inclusion_iff {a b n : ℕ} (hab : a ≤ b) (hn : n ≠ 0) :
    Function.Injective (QuotSMulTop.map ((p : ℤ_[p]) ^ n) (inclusion (invPowLattice_mono hab))) ↔
      a = b := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  constructor
  · intro hinj
    by_contra hne
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    -- The class of `x = p ^ n p ^ (-a)` is nonzero, but its image is `p ^ (n + 1) p ^ (-(a + 1))`.
    set x : invPowLattice p a := (p : ℤ_[p]) ^ n • ⟨_, inv_p_pow_mem_invPowLattice a⟩
    have hw : ((p : ℚ_[p]) ^ (a + 1))⁻¹ ∈ invPowLattice p b :=
      invPowLattice_mono (by omega) (inv_p_pow_mem_invPowLattice (a + 1))
    have hx : inclusion (invPowLattice_mono hab) x = (p : ℤ_[p]) ^ (n + 1) • ⟨_, hw⟩ := by
      ext
      simp only [x, coe_inclusion, SetLike.val_smul, Algebra.smul_def, PadicInt.algebraMap_apply,
        PadicInt.coe_pow, PadicInt.coe_natCast]
      field_simp
      ring
    have hzero : QuotSMulTop.map ((p : ℤ_[p]) ^ (n + 1)) (inclusion (invPowLattice_mono hab))
        (Submodule.Quotient.mk x) = 0 := by
      rw [QuotSMulTop.map_apply_mk, hx, Submodule.Quotient.mk_eq_zero]
      exact smul_mem_pointwise_smul _ _ ⊤ trivial
    rw [← map_zero (QuotSMulTop.map ((p : ℤ_[p]) ^ (n + 1)) (inclusion (invPowLattice_mono hab))),
      hinj.eq_iff, Submodule.Quotient.mk_eq_zero, mem_smul_pointwise_iff_exists] at hzero
    obtain ⟨⟨z, hz⟩, -, hzx⟩ := hzero
    obtain ⟨c, rfl⟩ := mem_span_singleton.mp hz
    -- Comparing coefficients of `p ^ (-a)` gives `p ^ n = p ^ (n + 1) c`, so `p` is a unit.
    have hg : ((p : ℚ_[p]) ^ a)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hp0)
    have hval := congrArg Subtype.val hzx
    simp only [x, SetLike.val_smul, Algebra.smul_def, PadicInt.algebraMap_apply,
      PadicInt.coe_pow, PadicInt.coe_natCast] at hval
    have hcoeff : (p : ℤ_[p]) ^ n * 1 = (p : ℤ_[p]) ^ n * ((p : ℤ_[p]) * c) := by
      apply PadicInt.ext
      push_cast
      apply mul_right_cancel₀ hg
      linear_combination -hval
    have hunit : IsUnit (p : ℤ_[p]) :=
      IsUnit.of_mul_eq_one c (mul_left_cancel₀ (pow_ne_zero n (by exact_mod_cast hp0)) hcoeff).symm
    exact PadicInt.not_isUnit_iff_dvd.mpr (dvd_refl _) hunit
  · rintro rfl
    -- The inclusion of a lattice in itself is the identity, hence so is its reduction.
    rw [show inclusion (invPowLattice_mono hab) = LinearMap.id from LinearMap.ext fun _ ↦ rfl,
      QuotSMulTop.map_id]
    exact Function.injective_id

/-! ### The modified Tate lattice -/

/-- The modified generator `(p ^ a a!)⁻¹` has norm `p ^ (a + v_p(a!))`. -/
theorem norm_modifiedTateGenerator (r : ℕ) :
    ‖modifiedTateGenerator p r‖ = (p : ℝ) ^ (r / (p - 1) + multiplicity p (r / (p - 1))!) := by
  rw [modifiedTateGenerator]
  generalize r / (p - 1) = a
  simp [Padic.norm_natCast_eq_zpow a.factorial_ne_zero, Nat.padicValNat_def, zpow_neg]
  ring

/-- The modified Tate lattice of weight `r` is `p ^ (-(a + v_p(a!))) ℤ_p`, where
`a = ⌊r / (p - 1)⌋`. -/
theorem modifiedTateLattice_eq_invPowLattice (r : ℕ) :
    modifiedTateLattice p r =
      invPowLattice p (r / (p - 1) + multiplicity p (r / (p - 1))!) := by
  rw [modifiedTateLattice_def, invPowLattice_def,
    PadicInt.span_singleton_eq_span_singleton_iff_norm_eq, norm_modifiedTateGenerator]
  generalize r / (p - 1) + _ = n
  simp

/-- The modified Tate lattice of weight `r` is the closed ball of radius `p ^ (a + v_p(a!))`. -/
theorem mem_modifiedTateLattice_iff {r : ℕ} {x : ℚ_[p]} :
    x ∈ modifiedTateLattice p r ↔
      ‖x‖ ≤ (p : ℝ) ^ (r / (p - 1) + multiplicity p (r / (p - 1))!) := by
  rw [modifiedTateLattice_eq_invPowLattice, mem_invPowLattice_iff]

/-- The modified Tate lattice is `ℤ_p` exactly in the weights `r < p - 1`, where `a = 0`. -/
@[simp]
theorem modifiedTateLattice_eq_one_iff {r : ℕ} : modifiedTateLattice p r = 1 ↔ r < p - 1 := by
  rw [modifiedTateLattice_eq_invPowLattice, invPowLattice_eq_one_iff, Nat.add_eq_zero_iff,
    Nat.div_eq_zero_iff]
  have : p - 1 ≠ 0 := by have := hp.out.two_le; omega
  constructor
  · rintro ⟨h | h, -⟩
    · exact absurd h this
    · exact h
  · intro h
    have h0 : r / (p - 1) = 0 := Nat.div_eq_of_lt h
    exact ⟨Or.inr h, by rw [h0, Nat.factorial_zero, multiplicity_one_right]⟩

@[simp]
theorem modifiedTateLattice_zero : modifiedTateLattice p 0 = 1 :=
  modifiedTateLattice_eq_one_iff.mpr (by have := hp.out.two_le; omega)

/-- The ordinary Tate lattice `ℤ_p(r)`, spanned by `1`, is contained in the modified Tate
lattice. -/
theorem one_le_modifiedTateLattice (r : ℕ) : 1 ≤ modifiedTateLattice p r := by
  rw [modifiedTateLattice_eq_invPowLattice]
  exact one_le_invPowLattice _

/-- The simp-normal form of `TauCeti.one_le_modifiedTateLattice`, by `Submodule.one_le`. -/
@[simp]
theorem one_mem_modifiedTateLattice (r : ℕ) : (1 : ℚ_[p]) ∈ modifiedTateLattice p r :=
  one_le.mp (one_le_modifiedTateLattice r)

/-- Colmez–Nizioł's lattice `p ^ (-a) ℤ_p` is contained in the modified Tate lattice. -/
theorem invPowLattice_le_modifiedTateLattice (r : ℕ) :
    invPowLattice p (r / (p - 1)) ≤ modifiedTateLattice p r := by
  rw [modifiedTateLattice_eq_invPowLattice, invPowLattice_le_invPowLattice_iff]
  exact Nat.le_add_right _ _

/-- The inclusion of `p ^ (-a) ℤ_p` in the modified Tate lattice `(p ^ a a!)⁻¹ ℤ_p` has cokernel
killed by `p ^ v_p(a!)`. -/
theorem pow_multiplicity_factorial_mem_annihilator_range_inclusion (r : ℕ) :
    (p : ℤ_[p]) ^ multiplicity p (r / (p - 1))! ∈
      Module.annihilator ℤ_[p] (modifiedTateLattice p r ⧸ LinearMap.range
        (inclusion (invPowLattice_le_modifiedTateLattice (p := p) r))) := by
  -- Transport `TauCeti.pow_sub_mem_annihilator_range_inclusion` along the equality of lattices.
  have key : ∀ (L : Submodule ℤ_[p] ℚ_[p])
      (_ : L = invPowLattice p (r / (p - 1) + multiplicity p (r / (p - 1))!))
      (h : invPowLattice p (r / (p - 1)) ≤ L),
      (p : ℤ_[p]) ^ multiplicity p (r / (p - 1))! ∈
        Module.annihilator ℤ_[p] (L ⧸ LinearMap.range (inclusion h)) := by
    rintro _ rfl _
    simpa using pow_sub_mem_annihilator_range_inclusion (p := p) (Nat.le_add_right _ _)
  exact key _ (modifiedTateLattice_eq_invPowLattice r) _

/-- The modified Tate lattice agrees with `p ^ (-a) ℤ_p` exactly when `a < p`, i.e. when `a!` is a
`p`-adic unit. -/
theorem modifiedTateLattice_eq_invPowLattice_iff {r : ℕ} :
    modifiedTateLattice p r = invPowLattice p (r / (p - 1)) ↔ r / (p - 1) < p := by
  rw [modifiedTateLattice_eq_invPowLattice, invPowLattice_inj, Nat.add_eq_left,
    Nat.multiplicity_eq_zero_iff, hp.out.dvd_factorial]
  simp [hp.out.ne_one, Nat.factorial_ne_zero]

/-- The generator `p ^ (-a)` of `p ^ (-a) ℤ_p` is `a!` times the modified generator. -/
theorem factorial_smul_modifiedTateGenerator (r : ℕ) :
    ((r / (p - 1))! : ℤ_[p]) • modifiedTateGenerator p r = ((p : ℚ_[p]) ^ (r / (p - 1)))⁻¹ := by
  have : ((r / (p - 1))! : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [modifiedTateGenerator, Algebra.smul_def, map_natCast, mul_inv, mul_comm,
    mul_assoc, inv_mul_cancel₀ this, mul_one]

/-- The ordinary generator `1` of `ℤ_p(r)` is `p ^ a a!` times the modified generator. -/
theorem pow_mul_factorial_smul_modifiedTateGenerator (r : ℕ) :
    ((p : ℤ_[p]) ^ (r / (p - 1)) * (r / (p - 1))!) • modifiedTateGenerator p r = 1 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have : ((p : ℚ_[p]) ^ (r / (p - 1)) * (r / (p - 1))!) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hp0) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  rw [modifiedTateGenerator, Algebra.smul_def, map_mul, map_pow, map_natCast, map_natCast,
    mul_inv_cancel₀ this]

/-- Multiplication of Tate lines restricts to the modified lattices:
`L(r) L(s) ⊆ L(r + s)`. -/
theorem modifiedTateLattice_mul_modifiedTateLattice_le (r s : ℕ) :
    modifiedTateLattice p r * modifiedTateLattice p s ≤ modifiedTateLattice p (r + s) := by
  rw [modifiedTateLattice_eq_invPowLattice, modifiedTateLattice_eq_invPowLattice,
    modifiedTateLattice_eq_invPowLattice, invPowLattice_mul_invPowLattice,
    invPowLattice_le_invPowLattice_iff]
  have hdiv : r / (p - 1) + s / (p - 1) ≤ (r + s) / (p - 1) := Nat.div_add_div_le_add_div
  -- `v_p(a_r!) + v_p(a_s!) ≤ v_p(a_{r+s}!)`, as `a_r! a_s!` divides `(a_r + a_s)!` and hence
  -- `a_{r+s}!`.
  have hv : multiplicity p (r / (p - 1))! + multiplicity p (s / (p - 1))! ≤
      multiplicity p ((r + s) / (p - 1))! := by
    rw [← Nat.pow_dvd_iff_le_multiplicity hp.out.ne_one (Nat.factorial_ne_zero _), pow_add]
    exact (Nat.mul_dvd_mul (pow_multiplicity_dvd _ _) (pow_multiplicity_dvd _ _)).trans
      ((Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans (Nat.factorial_dvd_factorial hdiv))
  omega

end

end TauCeti
