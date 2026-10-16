/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Normed

/-!
# Multiplicative pseudo-uniformisers of seminormed rings

A *multiplicative pseudo-uniformiser* of a seminormed ring `R` is a unit `ϖ` with
`0 < ‖ϖ‖ < 1` such that multiplication by `ϖ` scales the norm exactly:
`‖ϖ * x‖ = ‖ϖ‖ * ‖x‖` for every `x`. A seminormed ring is *Tate* (for its given norm) when it
has one. These are the quantitative counterparts of the topological notions
`TauCeti.Huber.IsPseudoUniformizer` and `TauCeti.Huber.IsTateRing`: the topological Tate property
of a ring does not imply that an arbitrary compatible norm admits a multiplicative
pseudo-uniformiser, so the normed notion records a property of the specified norm.

The exact scaling law propagates to every module with contractive scalar action: for
`IsBoundedSMul R M` and every integer `n`,
`‖ϖ ^ n • m‖ = ‖ϖ‖ ^ n * ‖m‖`. Consequently every vector `m` of nonzero norm has a unique
rescaling `ϖ ^ n • m` into the shell `‖ϖ‖ < ‖ϖ ^ n • m‖ ≤ 1`. These are the shell arguments
used throughout nonarchimedean functional analysis over Banach–Tate rings, for instance to turn
topological statements about bounded maps into norm estimates. The inverse norm formula and the
scaling law hold more generally for any unit `u` of positive norm with `‖u * x‖ = ‖u‖ * ‖x‖`,
whatever the size of `‖u‖`.

The existence of a multiplicative pseudo-uniformiser forces `‖1‖ = 1`, so a Tate ring is
nonzero. An ultrametric Tate commutative ring is a Tate ring in the topological sense. A
seminormed algebra with `‖1‖ = 1` over a normed field has a multiplicative pseudo-uniformiser
given by any scalar `c` with `0 < ‖c‖ < 1`; in particular nontrivially normed fields are Tate.

## Main definitions

* `TauCeti.NormedRing.PseudoUniformizer R`: a chosen multiplicative pseudo-uniformiser.
* `TauCeti.NormedRing.IsTate R`: the given norm on `R` admits a multiplicative
  pseudo-uniformiser.

## Main results

* `TauCeti.NormedRing.norm_units_inv_of_norm_mul` and
  `TauCeti.NormedRing.norm_units_zpow_smul_of_norm_mul`: the inverse norm formula and exact
  scaling `‖u ^ n • m‖ = ‖u‖ ^ n * ‖m‖` for a unit `u` scaling the norm exactly.
* `TauCeti.NormedRing.PseudoUniformizer.norm_zpow_smul`: exact scaling
  `‖ϖ ^ n • m‖ = ‖ϖ‖ ^ n * ‖m‖` on modules with contractive action.
* `TauCeti.NormedRing.PseudoUniformizer.existsUnique_norm_zpow_smul_mem_Ioc`: the shell
  `‖ϖ‖ < ‖ϖ ^ n • m‖ ≤ 1` determines `n` uniquely.
* `TauCeti.NormedRing.PseudoUniformizer.isPseudoUniformizer` and
  `TauCeti.NormedRing.IsTate.isTateRing`: comparison with the topological notions.
* `TauCeti.NormedRing.PseudoUniformizer.ofAlgebraMap`: small nonzero scalars of a normed field
  are multiplicative pseudo-uniformisers of norm-one algebras.

## References

* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.1.
-/

public section

open Set NNReal

namespace TauCeti.NormedRing

section Units

/-! ### Units scaling the norm exactly -/

variable {R : Type*} [SeminormedRing R] {u : Rˣ} (hu0 : 0 < ‖(u : R)‖)
  (hu : ∀ x : R, ‖(u : R) * x‖ = ‖(u : R)‖ * ‖x‖)
include hu0 hu

/-- A unit of positive norm by which left multiplication scales the norm exactly forces
`‖1‖ = 1`. -/
theorem norm_one_of_norm_units_mul : ‖(1 : R)‖ = 1 :=
  (mul_eq_left₀ hu0.ne').mp (by simpa using (hu 1).symm)

/-- A unit of positive norm by which left multiplication scales the norm exactly has inverse
of norm `‖u‖⁻¹`. -/
theorem norm_units_inv_of_norm_mul : ‖((u⁻¹ : Rˣ) : R)‖ = ‖(u : R)‖⁻¹ := by
  have h := hu ((u⁻¹ : Rˣ) : R)
  rw [Units.mul_inv, norm_one_of_norm_units_mul hu0 hu] at h
  exact eq_inv_of_mul_eq_one_right h.symm

section Module

variable {M : Type*} [SeminormedAddGroup M] [MulActionWithZero R M] [IsBoundedSMul R M]

/-- **Exact scaling on modules**: a unit of positive norm by which left multiplication scales
the norm exactly scales the norm of every vector exactly under a contractive scalar action. -/
theorem norm_units_smul_of_norm_mul (m : M) : ‖(u : R) • m‖ = ‖(u : R)‖ * ‖m‖ := by
  refine le_antisymm (norm_smul_le _ _) ?_
  calc ‖(u : R)‖ * ‖m‖ = ‖(u : R)‖ * ‖((u⁻¹ : Rˣ) : R) • (u : R) • m‖ := by simp [smul_smul]
    _ ≤ ‖(u : R)‖ * (‖((u⁻¹ : Rˣ) : R)‖ * ‖(u : R) • m‖) := by gcongr; exact norm_smul_le _ _
    _ = ‖(u : R) • m‖ := by
        rw [norm_units_inv_of_norm_mul hu0 hu]
        field_simp

/-- The inverse of a unit of positive norm by which left multiplication scales the norm exactly
scales the norm of every vector by `‖u‖⁻¹` under a contractive scalar action. -/
theorem norm_units_inv_smul_of_norm_mul (m : M) :
    ‖((u⁻¹ : Rˣ) : R) • m‖ = ‖(u : R)‖⁻¹ * ‖m‖ := by
  rw [eq_inv_mul_iff_mul_eq₀ hu0.ne', ← norm_units_smul_of_norm_mul hu0 hu]
  simp [smul_smul]

/-- **Exact scaling by integer powers**: `‖u ^ n • m‖ = ‖u‖ ^ n * ‖m‖` for every integer `n`,
for a unit `u` of positive norm by which left multiplication scales the norm exactly, under a
contractive scalar action. -/
theorem norm_units_zpow_smul_of_norm_mul (n : ℤ) (m : M) :
    ‖((u ^ n : Rˣ) : R) • m‖ = ‖(u : R)‖ ^ n * ‖m‖ := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    simp only [zpow_add_one, Units.val_mul, mul_smul, ih, norm_units_smul_of_norm_mul hu0 hu,
      zpow_add_one₀ hu0.ne']
    ring
  | pred n ih =>
    simp only [zpow_sub_one, Units.val_mul, mul_smul, ih, norm_units_inv_smul_of_norm_mul hu0 hu,
      zpow_sub_one₀ hu0.ne']
    ring

end Module

/-- An integer power of a unit of positive norm by which left multiplication scales the norm
exactly has the corresponding power of its norm. -/
theorem norm_units_zpow_of_norm_mul (n : ℤ) : ‖((u ^ n : Rˣ) : R)‖ = ‖(u : R)‖ ^ n := by
  simpa [norm_one_of_norm_units_mul hu0 hu] using norm_units_zpow_smul_of_norm_mul hu0 hu n (1 : R)

/-- A natural power of a unit of positive norm by which left multiplication scales the norm
exactly has the corresponding power of its norm. -/
theorem norm_units_pow_of_norm_mul (n : ℕ) : ‖(u : R) ^ n‖ = ‖(u : R)‖ ^ n := by
  simpa using norm_units_zpow_of_norm_mul hu0 hu n

end Units

/-- A **multiplicative pseudo-uniformiser** of a seminormed ring `R`: a unit `ϖ` with
`0 < ‖ϖ‖ < 1` by which left multiplication scales the norm exactly, `‖ϖ * x‖ = ‖ϖ‖ * ‖x‖`.
This is data: it records a choice of such a unit for the given norm. -/
structure PseudoUniformizer (R : Type*) [SeminormedRing R] where
  /-- The chosen unit. -/
  unit : Rˣ
  /-- Left multiplication by the chosen unit scales the norm exactly. -/
  norm_mul : ∀ x : R, ‖(unit : R) * x‖ = ‖(unit : R)‖ * ‖x‖
  /-- The chosen unit has positive norm. -/
  norm_pos : 0 < ‖(unit : R)‖
  /-- The chosen unit has norm less than one. -/
  norm_lt_one : ‖(unit : R)‖ < 1

/-- A seminormed ring is **Tate** for its given norm when it admits a multiplicative
pseudo-uniformiser. This is a property of the specified norm; for an ultrametric commutative
ring it is stronger than the topological `TauCeti.Huber.IsTateRing` (`IsTate.isTateRing`).
Neither completeness nor the ultrametric inequality is included. -/
class IsTate (R : Type*) [SeminormedRing R] : Prop where
  /-- The given norm admits a multiplicative pseudo-uniformiser. -/
  nonempty_pseudoUniformizer : Nonempty (PseudoUniformizer R)

namespace PseudoUniformizer

variable {R : Type*} [SeminormedRing R] (ϖ : PseudoUniformizer R)

include ϖ in
/-- The existence of a multiplicative pseudo-uniformiser forces `‖1‖ = 1`. -/
theorem norm_one : ‖(1 : R)‖ = 1 := norm_one_of_norm_units_mul ϖ.norm_pos ϖ.norm_mul

include ϖ in
/-- A seminormed ring with a multiplicative pseudo-uniformiser satisfies `‖1‖ = 1`. -/
theorem normOneClass : NormOneClass R := ⟨ϖ.norm_one⟩

include ϖ in
/-- A seminormed ring with a multiplicative pseudo-uniformiser is nonzero. -/
theorem nontrivial : Nontrivial R :=
  have := ϖ.normOneClass
  NormOneClass.nontrivial

/-- The inverse of a multiplicative pseudo-uniformiser has the inverse norm. -/
@[simp]
theorem norm_inv : ‖((ϖ.unit⁻¹ : Rˣ) : R)‖ = ‖(ϖ.unit : R)‖⁻¹ :=
  norm_units_inv_of_norm_mul ϖ.norm_pos ϖ.norm_mul

section Module

variable {M : Type*} [SeminormedAddGroup M] [MulActionWithZero R M] [IsBoundedSMul R M]

/-- **Exact scaling on modules**: a multiplicative pseudo-uniformiser scales the norm of every
vector exactly under a contractive scalar action. -/
@[simp]
theorem norm_smul (m : M) : ‖(ϖ.unit : R) • m‖ = ‖(ϖ.unit : R)‖ * ‖m‖ :=
  norm_units_smul_of_norm_mul ϖ.norm_pos ϖ.norm_mul m

/-- The inverse of a multiplicative pseudo-uniformiser scales the norm of every vector by
`‖ϖ‖⁻¹` under a contractive scalar action. -/
@[simp]
theorem norm_inv_smul (m : M) :
    ‖((ϖ.unit⁻¹ : Rˣ) : R) • m‖ = ‖(ϖ.unit : R)‖⁻¹ * ‖m‖ :=
  norm_units_inv_smul_of_norm_mul ϖ.norm_pos ϖ.norm_mul m

/-- **Exact scaling by integer powers**: `‖ϖ ^ n • m‖ = ‖ϖ‖ ^ n * ‖m‖` for every integer `n`,
under a contractive scalar action. -/
@[simp]
theorem norm_zpow_smul (n : ℤ) (m : M) :
    ‖((ϖ.unit ^ n : Rˣ) : R) • m‖ = ‖(ϖ.unit : R)‖ ^ n * ‖m‖ :=
  norm_units_zpow_smul_of_norm_mul ϖ.norm_pos ϖ.norm_mul n m

/-- **The shell**: every vector `m` of nonzero norm has a unique rescaling `ϖ ^ n • m`, `n ∈ ℤ`,
with `‖ϖ‖ < ‖ϖ ^ n • m‖ ≤ 1`. -/
theorem existsUnique_norm_zpow_smul_mem_Ioc {m : M} (hm : ‖m‖ ≠ 0) :
    ∃! n : ℤ, ‖((ϖ.unit ^ n : Rˣ) : R) • m‖ ∈ Ioc ‖(ϖ.unit : R)‖ 1 := by
  -- Package `‖ϖ‖` and `‖m‖` as units of `ℝ≥0`; the shell is then a fundamental domain for
  -- multiplication by the powers of `‖ϖ‖⁻¹`.
  let q : ℝ≥0ˣ := Units.mk0 ‖(ϖ.unit : R)‖₊ (by simpa [← NNReal.coe_ne_zero] using ϖ.norm_pos.ne')
  let u : ℝ≥0ˣ := Units.mk0 ‖m‖₊ (by simpa [← NNReal.coe_ne_zero] using hm)
  have hq : 1 < q⁻¹ := one_lt_inv'.mpr <| by
    simpa [← Units.val_lt_val, q, ← NNReal.coe_lt_coe] using ϖ.norm_lt_one
  convert existsUnique_sub_zpow_mem_Ioc hq u q using 2 with n
  simp [← Units.val_lt_val, ← Units.val_le_val, ← NNReal.coe_lt_coe, ← NNReal.coe_le_coe, q, u,
    mul_comm]

end Module

/-- An integer power of a multiplicative pseudo-uniformiser has the corresponding power of its
norm. -/
@[simp]
theorem norm_zpow (n : ℤ) : ‖((ϖ.unit ^ n : Rˣ) : R)‖ = ‖(ϖ.unit : R)‖ ^ n :=
  norm_units_zpow_of_norm_mul ϖ.norm_pos ϖ.norm_mul n

/-- A natural power of a multiplicative pseudo-uniformiser has the corresponding power of its
norm. -/
@[simp]
theorem norm_pow (n : ℕ) : ‖(ϖ.unit : R) ^ n‖ = ‖(ϖ.unit : R)‖ ^ n :=
  norm_units_pow_of_norm_mul ϖ.norm_pos ϖ.norm_mul n

/-- A positive power of a multiplicative pseudo-uniformiser is again one. -/
def pow (n : ℕ) (hn : n ≠ 0) : PseudoUniformizer R where
  unit := ϖ.unit ^ n
  norm_mul x := by
    simpa [ϖ.norm_pow] using ϖ.norm_zpow_smul n x
  norm_pos := by simpa [ϖ.norm_pow] using pow_pos ϖ.norm_pos n
  norm_lt_one := by simpa [ϖ.norm_pow] using pow_lt_one₀ ϖ.norm_pos.le ϖ.norm_lt_one hn

/-- The unit of `ϖ.pow n hn` is `ϖ.unit ^ n`. -/
@[simp]
theorem pow_unit (n : ℕ) (hn : n ≠ 0) : (ϖ.pow n hn).unit = ϖ.unit ^ n := (rfl)

/-- **A multiplicative pseudo-uniformiser is a pseudo-uniformiser** in the topological sense of
`TauCeti.Huber.IsPseudoUniformizer`: a topologically nilpotent unit. -/
theorem isPseudoUniformizer : Huber.IsPseudoUniformizer (ϖ.unit : R) :=
  Huber.IsPseudoUniformizer.of_norm_lt_one ϖ.unit.isUnit ϖ.norm_lt_one

/-- **Small nonzero scalars are multiplicative pseudo-uniformisers** of a seminormed algebra with
`‖1‖ = 1` over a normed field: the image of `c` with `c ≠ 0` and `‖c‖ < 1`. -/
noncomputable def ofAlgebraMap {K A : Type*} [NormedField K] [SeminormedRing A]
    [NormedAlgebra K A] [NormOneClass A] {c : K} (hc : c ≠ 0) (hc1 : ‖c‖ < 1) :
    PseudoUniformizer A where
  unit := Units.map (algebraMap K A).toMonoidHom (Units.mk0 c hc)
  norm_mul x := by
    simp [← Algebra.smul_def, _root_.norm_smul, norm_algebraMap']
  norm_pos := by simpa [norm_algebraMap'] using hc
  norm_lt_one := by simpa [norm_algebraMap'] using hc1

/-- The unit of `ofAlgebraMap hc hc1` is the image of `c`. -/
@[simp]
theorem coe_unit_ofAlgebraMap {K A : Type*} [NormedField K] [SeminormedRing A]
    [NormedAlgebra K A] [NormOneClass A] {c : K} (hc : c ≠ 0) (hc1 : ‖c‖ < 1) :
    (((ofAlgebraMap hc hc1 : PseudoUniformizer A).unit : Aˣ) : A) = algebraMap K A c := (rfl)

end PseudoUniformizer

namespace IsTate

variable {R : Type*} [SeminormedRing R]

/-- A Tate seminormed ring satisfies `‖1‖ = 1`. -/
instance (priority := 100) normOneClass [IsTate R] : NormOneClass R :=
  (nonempty_pseudoUniformizer (R := R)).some.normOneClass

/-- **An ultrametric Tate seminormed commutative ring is a Tate ring** in the topological sense:
its closed unit ball is a ring of definition and a multiplicative pseudo-uniformiser is a
topologically nilpotent unit (`TauCeti.Huber.IsTateRing.of_isUnit_norm_lt_one`). -/
instance (priority := 100) isTateRing {R : Type*} [SeminormedCommRing R] [IsUltrametricDist R]
    [IsTate R] : Huber.IsTateRing R :=
  let ϖ := (nonempty_pseudoUniformizer (R := R)).some
  Huber.IsTateRing.of_isUnit_norm_lt_one ϖ.unit.isUnit ϖ.norm_lt_one

/-- **A seminormed algebra with `‖1‖ = 1` over a nontrivially normed field is Tate**, by a scalar
`c` with `0 < ‖c‖ < 1` (`PseudoUniformizer.ofAlgebraMap`). -/
theorem of_normedAlgebra (K : Type*) {A : Type*} [NontriviallyNormedField K] [SeminormedRing A]
    [NormedAlgebra K A] [NormOneClass A] : IsTate A := by
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one K
  exact ⟨⟨PseudoUniformizer.ofAlgebraMap (norm_pos_iff.mp hc0) hc1⟩⟩

/-- **A nontrivially normed field is Tate**; for instance `ℚ_[p]`. -/
instance of_nontriviallyNormedField (K : Type*) [NontriviallyNormedField K] : IsTate K :=
  of_normedAlgebra K

end IsTate

end TauCeti.NormedRing
