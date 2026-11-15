/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Lattice
public import Mathlib.Algebra.Module.Submodule.Pointwise

/-!
# Power-series lattices in module-valued Laurent series

Convolution makes `HahnModule ℤ R V` a module over `R⟦X⟧`. The series whose coefficients
vanish below `a` form a power-series submodule `powerSeriesLattice R V a`, with underlying
`R`-submodule `TauCeti.HahnModule.lattice R V a`. Multiplication by the invertible Laurent
monomial `X^k` identifies the lattice at `a` with the lattice at `a + k`.

In particular, multiplication by `X^n` takes `U_a(V)` onto `U_(a+n)(V)`. Thus the lattice
filtration is the `X`-adic filtration on every fixed lattice, and its finite-jet quotients
inherit the power-series action. No freeness or finite-dimensionality of `V` is needed.
-/

public section

open scoped LaurentSeries PowerSeries Pointwise

namespace HahnModule

variable {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]

/-- Power series act on module-valued Laurent series by their scalar Laurent-series images. -/
noncomputable instance powerSeriesModule : Module R⟦X⟧ (HahnModule ℤ R V) :=
  Module.compHom _ (HahnSeries.ofPowerSeries ℤ R)

/-- The power-series action is convolution through the power-series inclusion. -/
theorem powerSeries_smul (p : R⟦X⟧) (f : HahnModule ℤ R V) :
    p • f = (p : R⸨X⸩) • f := rfl

/-- Constant power series act by the original coefficient action. -/
@[simp]
theorem C_smul (r : R) (f : HahnModule ℤ R V) : PowerSeries.C r • f = r • f := by
  rw [powerSeries_smul, PowerSeries.coe_C, HahnSeries.C_apply, single_zero_smul_eq_smul]
  -- `instBaseModule` uses the coefficient action transported from `V⟦ℤ⟧`;
  -- the action in `single_zero_smul_eq_smul` uses its underlying `SMulWithZero` instance.
  rfl

instance powerSeriesScalarTower : IsScalarTower R R⟦X⟧ (HahnModule ℤ R V) where
  smul_assoc r p f := by
    rw [powerSeries_smul, powerSeries_smul, PowerSeries.coe_smul, smul_assoc]

end HahnModule

namespace HahnModule

variable {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]

/-- The power-series action is compatible with the full Laurent-series action. -/
instance powerSeriesLaurentSeriesScalarTower :
    IsScalarTower R⟦X⟧ R⸨X⸩ (HahnModule ℤ R V) where
  smul_assoc p f g := by
    simp only [powerSeries_smul, Algebra.smul_def, LaurentSeries.coe_algebraMap, mul_smul]

end HahnModule

namespace TauCeti.HahnModule

open _root_.HahnModule HahnSeries

section Semiring

variable (R V : Type*) [Semiring R] [AddCommMonoid V] [Module R V]

/-- The power-series submodule `U_a(V)` of module-valued Laurent series vanishing below `a`. -/
noncomputable def powerSeriesLattice (a : ℤ) : Submodule R⟦X⟧ (HahnModule ℤ R V) where
  carrier := lattice R V a
  zero_mem' := (lattice R V a).zero_mem
  add_mem' := (lattice R V a).add_mem
  smul_mem' p f hf := by
    rw [_root_.HahnModule.powerSeries_smul]
    simpa using smul_mem_lattice (LaurentSeries.coe_powerSeries_mem_lattice_zero p) hf

/-- The power-series lattice has the same elements as the coefficient-linear lattice. -/
@[simp]
theorem mem_powerSeriesLattice {a : ℤ} {f : HahnModule ℤ R V} :
    f ∈ powerSeriesLattice R V a ↔ f ∈ lattice R V a := Iff.rfl

/-- Restricting the power-series lattice to coefficient scalars recovers the original lattice. -/
@[simp]
theorem restrictScalars_powerSeriesLattice (a : ℤ) :
    (powerSeriesLattice R V a).restrictScalars R = lattice R V a := (rfl)

/-- The power-series lattices decrease with their exponent bound. -/
theorem powerSeriesLattice_antitone : Antitone (powerSeriesLattice R V) :=
  fun _ _ h _ hf ↦ lattice_antitone R V h hf

end Semiring

end TauCeti.HahnModule

namespace HahnModule

open TauCeti.HahnModule

variable {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]

/-- Multiplying by a power of `X` translates the power-series lattice bound. -/
theorem X_pow_smul_mem_powerSeriesLattice_iff (a : ℤ) (n : ℕ) (f : HahnModule ℤ R V) :
    (PowerSeries.X ^ n : R⟦X⟧) • f ∈ powerSeriesLattice R V (a + n) ↔
      f ∈ powerSeriesLattice R V a := by
  rw [_root_.HahnModule.powerSeries_smul, HahnSeries.ofPowerSeries_X_pow]
  simp only [mem_powerSeriesLattice, single_smul_mem_lattice_iff]

end HahnModule

namespace TauCeti.HahnModule

open _root_.HahnModule HahnSeries

section Semiring

variable {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]

/-- Laurent-monomial multiplication identifies any two shifted power-series lattices. -/
noncomputable def powerSeriesLatticeShift (a k : ℤ) :
    powerSeriesLattice R V a ≃ₗ[R⟦X⟧] powerSeriesLattice R V (a + k) where
  toFun f := ⟨single k 1 • f.1, by
    simpa only [mem_powerSeriesLattice] using (single_smul_mem_lattice_iff k a f.1).2 f.2⟩
  invFun f := ⟨single (-k) 1 • f.1, by
    have h := (single_smul_mem_lattice_iff (-k) (a + k) f.1).2 f.2
    simpa only [mem_powerSeriesLattice, add_neg_cancel_right] using h⟩
  left_inv f := Subtype.ext (single_neg_smul_single_smul k f.1)
  right_inv f := Subtype.ext (by
    simpa using single_neg_smul_single_smul (-k) f.1)
  map_add' f g := Subtype.ext (_root_.smul_add _ _ _)
  map_smul' p f := Subtype.ext (by
    simp only [Submodule.coe_smul_of_tower, _root_.HahnModule.powerSeries_smul]
    rw [← mul_smul, ← mul_smul]
    congr 1
    ext n
    simp only [coeff_single_mul, coeff_mul_single, one_mul, mul_one, RingHom.id_apply])

/-- The lattice-shift equivalence acts by the specified Laurent monomial. -/
@[simp]
theorem powerSeriesLatticeShift_apply (a k : ℤ) (f : powerSeriesLattice R V a) :
    (powerSeriesLatticeShift a k f : HahnModule ℤ R V) =
      single k (1 : R) • (f : HahnModule ℤ R V) :=
  (rfl)

/-- The inverse lattice-shift equivalence acts by the inverse Laurent monomial. -/
@[simp]
theorem powerSeriesLatticeShift_symm_apply (a k : ℤ)
    (f : powerSeriesLattice R V (a + k)) :
    ((powerSeriesLatticeShift a k).symm f : HahnModule ℤ R V) =
      single (-k) (1 : R) • (f : HahnModule ℤ R V) :=
  (rfl)

end Semiring

section CommSemiring

variable {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]

/-- Multiplication by `X^n` carries a lattice onto the lattice shifted by `n`. -/
theorem X_pow_smul_powerSeriesLattice (a : ℤ) (n : ℕ) :
    (PowerSeries.X ^ n : R⟦X⟧) • powerSeriesLattice R V a =
      powerSeriesLattice R V (a + n) := by
  ext f
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (X_pow_smul_mem_powerSeriesLattice_iff a n g).2 hg
  · intro hf
    let g := (powerSeriesLatticeShift a (n : ℤ)).symm ⟨f, hf⟩
    refine ⟨g.1, g.2, ?_⟩
    have h := congrArg Subtype.val ((powerSeriesLatticeShift a (n : ℤ)).apply_symm_apply ⟨f, hf⟩)
    rw [_root_.HahnModule.powerSeries_smul, HahnSeries.ofPowerSeries_X_pow]
    simpa only [powerSeriesLatticeShift_apply] using h

end CommSemiring

section Ring

variable (R V : Type*) [Ring R] [AddCommGroup V] [Module R V]

/-- Finite jets retain the power-series action on the lattices. The underlying quotient
and its coefficient-ring module structure are the existing `latticeQuotient`. -/
noncomputable instance latticeQuotientPowerSeriesModule (a b : ℤ) :
    Module R⟦X⟧ (latticeQuotient R V a b) :=
  -- Restriction of scalars does not change the underlying additive quotient.
  inferInstanceAs (Module R⟦X⟧ (powerSeriesLattice R V a ⧸
    (powerSeriesLattice R V b).comap (powerSeriesLattice R V a).subtype))

/-- The power-series action on jets extends their coefficient-ring action. -/
instance latticeQuotientPowerSeriesScalarTower (a b : ℤ) :
    IsScalarTower R R⟦X⟧ (latticeQuotient R V a b) :=
  inferInstanceAs (IsScalarTower R R⟦X⟧ (powerSeriesLattice R V a ⧸
    (powerSeriesLattice R V b).comap (powerSeriesLattice R V a).subtype))

/-- The power-series action on a finite jet can be computed on any representative. -/
@[simp]
theorem smul_latticeQuotient_mk (a b : ℤ) (p : R⟦X⟧) (f : lattice R V a) :
    p • (Submodule.Quotient.mk f : latticeQuotient R V a b) =
      Submodule.Quotient.mk ⟨p • (f : HahnModule ℤ R V),
        (mem_powerSeriesLattice R V).mp ((powerSeriesLattice R V a).smul_mem p
          ((mem_powerSeriesLattice R V).mpr f.2))⟩ := (rfl)

/-- Constant power series act on finite jets by the original coefficient action. -/
@[simp]
theorem C_smul_latticeQuotient (a b : ℤ) (r : R) (q : latticeQuotient R V a b) :
    PowerSeries.C r • q = r • q := by
  induction q using Submodule.Quotient.induction_on with
  | _ f =>
    rw [smul_latticeQuotient_mk, ← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (_root_.HahnModule.C_smul r f.1)

/-- A jet on `[a,b)` is killed by `X^n` whenever `b ≤ a + n`. -/
theorem X_pow_smul_latticeQuotient_eq_zero (a b : ℤ) (n : ℕ) (h : b ≤ a + n)
    (f : latticeQuotient R V a b) : (PowerSeries.X ^ n : R⟦X⟧) • f = 0 := by
  induction f using Submodule.Quotient.induction_on with
  | _ f =>
    rw [smul_latticeQuotient_mk, Submodule.Quotient.mk_eq_zero]
    rw [Submodule.mem_comap, Submodule.subtype_apply, ← mem_powerSeriesLattice]
    exact powerSeriesLattice_antitone R V h
      ((X_pow_smul_mem_powerSeriesLattice_iff a n f.1).2
        ((mem_powerSeriesLattice R V).mpr f.2))

end Ring

end TauCeti.HahnModule
