/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Basis
public import TauCeti.RingTheory.DividedPowers.Basis

/-!
# Ordered divided-power PBW bases

For an ordered basis of a rational Lie algebra, the increasing products of divided powers
of its canonical generators form a rational basis of its universal enveloping algebra.
They also form an integral basis of their integral span. In particular this supplies the
independence of the ordered root factors for a positive or negative nilpotent Lie algebra.
No commutation relations beyond the Lie algebra laws are needed for independence.

The integral span here is a module, not asserted to be a subring: arbitrary rational Lie
structure constants need not give integral multiplication coefficients. Nor is this the
Kostant form of a reductive Lie algebra, whose toral factors use binomial polynomials instead
of divided powers. Integral straightening and the toral factors are separate questions.

The construction rescales `Module.Basis.pbwBasis` and follows the one-generator normalization
in `TauCeti.RingTheory.DividedPowers.Basis`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., II.1.
-/

public section

namespace Module.Basis

open TauCeti.Associative TauCeti.UniversalEnvelopingAlgebra

universe u v

variable {L : Type u} {ι : Type v} [LieRing L] [LieAlgebra ℚ L] [LinearOrder ι]
  (b : Basis ι ℚ L)

local notation "U" => _root_.UniversalEnvelopingAlgebra ℚ L

private noncomputable def pbwDividedPowerScale (n : ι →₀ ℕ) : ℚˣ :=
  n.prod fun _ k ↦ invFactorialUnit k

/-- The rational PBW basis normalized as increasing products of divided powers. -/
noncomputable def pbwDividedPowerBasis : Basis (ι →₀ ℕ) ℚ U :=
  b.pbwBasis.unitsSMul pbwDividedPowerScale

/-- A divided-power PBW vector is the ordinary PBW vector scaled by the inverse product of
its exponent factorials. -/
theorem pbwDividedPowerBasis_eq_smul_pbwBasis (n : ι →₀ ℕ) :
    b.pbwDividedPowerBasis n =
      (n.prod fun _ k ↦ (k.factorial : ℚ))⁻¹ • b.pbwBasis n := by
  simp [pbwDividedPowerBasis, unitsSMul_apply, Units.smul_def, pbwDividedPowerScale,
    Finsupp.prod, Units.coe_prod, ← Finset.prod_inv_distrib]

/-- Divided-power PBW coordinates are ordinary PBW coordinates multiplied by the product of
the exponent factorials. -/
theorem pbwDividedPowerBasis_repr (x : U) (n : ι →₀ ℕ) :
    b.pbwDividedPowerBasis.repr x n =
      (n.prod fun _ k ↦ (k.factorial : ℚ)) * b.pbwBasis.repr x n := by
  simp [pbwDividedPowerBasis, repr_unitsSMul, Units.smul_def, pbwDividedPowerScale,
    Finsupp.prod, Units.coe_prod, ← Finset.prod_inv_distrib]

/-- A normalized PBW vector is the increasing product of the divided powers specified by its
finitely supported exponent vector. -/
theorem pbwDividedPowerBasis_eq_prod (n : ι →₀ ℕ) :
    b.pbwDividedPowerBasis n = ((n.support.sort (· ≤ ·)).map
      (fun i ↦ dividedPower (n i) (_root_.UniversalEnvelopingAlgebra.ι ℚ (b i)))).prod := by
  rw [pbwDividedPowerBasis, unitsSMul_apply, b.pbwBasis_eq_prod_pow]
  have hscale : pbwDividedPowerScale n =
      ((n.support.sort (· ≤ ·)).map fun i ↦ invFactorialUnit (n i)).prod := by
    simp only [pbwDividedPowerScale, Finsupp.prod, ← Multiset.prod_coe,
      ← Multiset.map_coe, Finset.sort_eq, Finset.prod_eq_multiset_prod]
  rw [hscale]
  simpa only [invFactorialUnit_smul_pow] using
    (List.prod_hom₂ (n.support.sort (· ≤ ·)) (fun (a : ℚˣ) (x : U) ↦ a • x)
      (fun a b c d ↦ (smul_mul_smul_comm a c b d).symm) (by simp)
      (fun i ↦ invFactorialUnit (n i))
      (fun i ↦ _root_.UniversalEnvelopingAlgebra.ι ℚ (b i) ^ n i)).symm

@[simp]
theorem pbwDividedPowerBasis_zero : b.pbwDividedPowerBasis 0 = 1 := by
  simp [pbwDividedPowerBasis_eq_prod]

/-- An exponent supported at one generator gives its divided power. -/
@[simp]
theorem pbwDividedPowerBasis_single (i : ι) (n : ℕ) :
    b.pbwDividedPowerBasis (Finsupp.single i n) =
      dividedPower n (_root_.UniversalEnvelopingAlgebra.ι ℚ (b i)) := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [pbwDividedPowerBasis_eq_prod]
    simp [Finsupp.support_single _ hn]

/-- Ordered divided-power monomials are linearly independent over the integers. -/
theorem linearIndependent_pbwDividedPowerBasis_int :
    LinearIndependent ℤ (fun n ↦ b.pbwDividedPowerBasis n) :=
  b.pbwDividedPowerBasis.linearIndependent.restrict_scalars (smul_left_injective ℤ one_ne_zero)

/-- The integral span of the ordered divided-power monomials. It is not in general a subring. -/
noncomputable def pbwDividedPowerLattice : Submodule ℤ U :=
  Submodule.span ℤ (Set.range b.pbwDividedPowerBasis)

/-- The defining span of the ordered divided-power lattice. -/
theorem pbwDividedPowerLattice_def :
    b.pbwDividedPowerLattice = Submodule.span ℤ (Set.range b.pbwDividedPowerBasis) :=
  (rfl)

/-- Every ordered divided-power monomial belongs to the integral lattice. -/
@[simp]
theorem pbwDividedPowerBasis_mem_pbwDividedPowerLattice (n : ι →₀ ℕ) :
    b.pbwDividedPowerBasis n ∈ b.pbwDividedPowerLattice :=
  Submodule.subset_span (Set.mem_range_self n)

/-- A submodule contains the divided-power lattice exactly when it contains all its ordered
monomials. -/
@[simp]
theorem pbwDividedPowerLattice_le_iff (N : Submodule ℤ U) :
    b.pbwDividedPowerLattice ≤ N ↔ ∀ n, b.pbwDividedPowerBasis n ∈ N := by
  rw [pbwDividedPowerLattice_def, Submodule.span_le, Set.range_subset_iff]
  rfl

/-- The ordered divided-power monomials form an integral basis of their lattice. -/
noncomputable def pbwDividedPowerLatticeBasis :
    Basis (ι →₀ ℕ) ℤ b.pbwDividedPowerLattice :=
  Basis.span b.linearIndependent_pbwDividedPowerBasis_int

/-- The integral basis vector is the corresponding rational divided-power PBW vector. -/
@[simp]
theorem coe_pbwDividedPowerLatticeBasis_apply (n : ι →₀ ℕ) :
    (b.pbwDividedPowerLatticeBasis n : U) = b.pbwDividedPowerBasis n :=
  Basis.coe_span_apply b.linearIndependent_pbwDividedPowerBasis_int n

/-- Integral lattice coordinates cast to the corresponding rational divided-power coordinates. -/
@[simp]
theorem pbwDividedPowerLatticeBasis_repr (x : b.pbwDividedPowerLattice) (n : ι →₀ ℕ) :
    ((b.pbwDividedPowerLatticeBasis.repr x n : ℤ) : ℚ) =
      b.pbwDividedPowerBasis.repr (x : U) n := by
  exact b.pbwDividedPowerBasis.restrictScalars_repr_apply ℤ x n

/-- An element belongs to the integral lattice exactly when all its rational divided-power
coordinates are integers. -/
theorem mem_pbwDividedPowerLattice_iff_repr (x : U) :
    x ∈ b.pbwDividedPowerLattice ↔
      ∀ n, b.pbwDividedPowerBasis.repr x n ∈ Set.range (Int.cast : ℤ → ℚ) := by
  exact b.pbwDividedPowerBasis.mem_span_iff_repr_mem ℤ x

/-- Membership in the integral lattice is equivalent to a unique finite integral expansion in
ordered divided-power monomials. -/
theorem mem_pbwDividedPowerLattice_iff_existsUnique (x : U) :
    x ∈ b.pbwDividedPowerLattice ↔
      ∃! c : (ι →₀ ℕ) →₀ ℤ, c.sum (fun n a ↦ a • b.pbwDividedPowerBasis n) = x := by
  rw [pbwDividedPowerLattice_def]
  exact b.linearIndependent_pbwDividedPowerBasis_int.mem_span_range_iff_existsUnique x

end Module.Basis

namespace Module.Basis

open TauCeti.Associative TauCeti.UniversalEnvelopingAlgebra

variable {L M ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] [LinearOrder ι] [LinearOrder κ]

/-- An order-preserving inclusion of Lie bases carries divided-power PBW vectors to the
corresponding ambient vectors, extending their exponents by zero. This applies in particular
to the inclusion of a positive or negative root Lie algebra in a larger Lie algebra. -/
theorem map_pbwDividedPowerBasis (b : Basis ι ℚ L) (c : Basis κ ℚ M)
    (f : L →ₗ⁅ℚ⁆ M) (e : ι ↪o κ) (h : ∀ i, f (b i) = c (e i)) (n : ι →₀ ℕ) :
    map ℚ f (b.pbwDividedPowerBasis n) =
      c.pbwDividedPowerBasis (n.embDomain e.toEmbedding) := by
  simp only [pbwDividedPowerBasis, unitsSMul_apply, Units.smul_def, map_smul,
    b.map_pbwBasis c f e h n, pbwDividedPowerScale, Finsupp.prod_embDomain]

end Module.Basis
