/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic
public import TauCeti.LinearAlgebra.IntegralLattice.StandardCoordinates
import Mathlib.LinearAlgebra.Matrix.Transvection
import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Cardinality
import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots

/-!
# The two ten-curve lattices of an `I₄*` fibre on an Enriques surface

Let `C₀ + C₁ + 2 (C₂ + ⋯ + C₆) + C₇ + C₈` be a fibre of Kodaira type `I₄*` (affine `D₈`) of a
genus-one fibration on an Enriques surface. The components `C₁, …, C₈` span a copy of `D₈(-1)`:
in the order `C₁, …, C₈` they have square `-2` and meet exactly along the edges

```text
(C₁, C₂), (C₂, C₃), (C₃, C₄), (C₄, C₅), (C₅, C₆), (C₆, C₇), (C₆, C₈).
```

Schröer's exclusion of `I₄*` fibres on Enriques surfaces over `𝔽₂` uses two rank-ten extensions of
this configuration:

* `N₁ = TauCeti.EnriquesTenCurve.firstGram`, the Gram matrix of `(C₁, …, C₈, R, F)` for a
  `(-2)`-curve `R` meeting only `C₄`, once, and a half-fibre `F` of the pencil, with `R · F = 1`;
* `N₂ = TauCeti.EnriquesTenCurve.secondGram`, the Gram matrix of `(C₁, …, C₈, F', F)` for two
  half-fibres with `F · F' = 1`, both orthogonal to the components; this is `D₈(-1) ⊕ U`.

This file realizes both on the standard coordinate space `ℚ¹⁰` with carrier `ℤ¹⁰`, and computes
their discriminant forms. Both matrices have determinant `-4`, and `2 N⁻¹` is an integer matrix,
so the discriminant group has order four and exponent two: it is `(ℤ/2)²`. Its nonzero classes are
those of the dual basis vectors `C₁*`, `C₇*` and `C₈*`. The vector class `C₁*` has full norm `-1`,
so the half-norm discriminant form takes the value `1/2` on it, while the two spinor classes `C₇*`
and `C₈*` have full norm `-2` and are isotropic. Consequently each lattice has exactly three
isotropic discriminant classes, including zero. Since an even overlattice of index two is obtained
by gluing an isotropic class, this is the input for locating the numerical lattice of the surface,
which contains each configuration with index two, among the overlattices of `N₁` and `N₂`.

The inverses `N₁⁻¹` and `N₂⁻¹` are Schröer's matrices `(14)` and `(16)`; this file records the
integer matrices `2 N₁⁻¹` and `2 N₂⁻¹`.

## Main definitions

* `TauCeti.EnriquesTenCurve.firstGram`, `TauCeti.EnriquesTenCurve.secondGram`: the matrices `N₁`
  and `N₂`.
* `TauCeti.EnriquesTenCurve.firstLattice`, `TauCeti.EnriquesTenCurve.secondLattice`: the integral
  lattices they present on `ℚ¹⁰`.
* `TauCeti.EnriquesTenCurve.firstGramTwiceInverse`,
  `TauCeti.EnriquesTenCurve.secondGramTwiceInverse`: the integer matrices `2 N₁⁻¹` and `2 N₂⁻¹`.
* `TauCeti.EnriquesTenCurve.firstDualVector`, `TauCeti.EnriquesTenCurve.secondDualVector`: the
  dual basis vectors, the columns of `N⁻¹`.
* `TauCeti.EnriquesTenCurve.firstDualClass`, `TauCeti.EnriquesTenCurve.secondDualClass`: their
  discriminant classes.

## Main results

* `TauCeti.EnriquesTenCurve.det_firstGram`, `TauCeti.EnriquesTenCurve.det_secondGram`: both
  determinants are `-4`.
* `TauCeti.EnriquesTenCurve.isEven_firstLattice`, `TauCeti.EnriquesTenCurve.isEven_secondLattice`:
  both lattices are even.
* `TauCeti.EnriquesTenCurve.natCard_discriminantGroup_firstLattice` and
  `TauCeti.EnriquesTenCurve.exponent_discriminantGroup_firstLattice`, with their `secondLattice`
  counterparts: the discriminant groups have order four and exponent two.
* `TauCeti.EnriquesTenCurve.bijective_firstDualClass`,
  `TauCeti.EnriquesTenCurve.bijective_secondDualClass`: the discriminant group consists of the four
  distinct classes `0`, `C₁*`, `C₇*`, `C₈*`.
* `TauCeti.EnriquesTenCurve.setOf_discriminantQuadraticMap_firstLattice_eq_zero` and
  `TauCeti.EnriquesTenCurve.ncard_setOf_discriminantQuadraticMap_firstLattice_eq_zero`, with their
  `secondLattice` counterparts: the isotropic classes are `0`, `C₇*` and `C₈*`, three in all.

## Implementation notes

The determinant of `N₂` is read off from its block decomposition `D₈(-1) ⊕ U` and
`CartanMatrix.D_det`. The matrix `N₁` is congruent to `N₂` under a product of two transvections:
in a lattice with Gram matrix `N₂` in the basis `(C₁, …, C₈, F', F)`, replacing `C₄` by `C₄ + F`
and `F'` by `F' - F` gives a basis with Gram matrix `N₁`. The two Gram matrices are therefore
integrally congruent; the lattices are kept separate because their bases carry different geometric
meaning.

## References

* S. Schröer, *There is no Enriques surface over the integers*, Annals of Mathematics 197 (2023),
  §12, Propositions 12.2 and 12.3, matrices (14) and (16).
-/

public section

open Matrix

namespace TauCeti.EnriquesTenCurve

open IntegralLattice

/-! ## Helpers -/

/-- Four pairwise distinct elements of a type with four elements enumerate it. -/
private theorem bijective_vecCons_of_pairwise_ne {α : Type*} (h : Nat.card α = 4)
    {a b c d : α} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) : Function.Bijective ![a, b, c, d] := by
  have : Finite α := Nat.finite_of_card_ne_zero (by simp [h])
  refine Function.Injective.bijective_of_nat_card_le (fun i j hij ↦ ?_) (by simp [h])
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

/-- A rational number of the form `(2m + 1) / 2` is not an integer. -/
private theorem not_exists_intCast_eq_half_odd {q : ℚ} (m : ℤ) (hq : q = (2 * m + 1) / 2) :
    ¬∃ z : ℤ, (z : ℚ) = q := by
  rintro ⟨z, hz⟩
  have h : ((2 * z : ℤ) : ℚ) = ((2 * m + 1 : ℤ) : ℚ) := by
    push_cast
    rw [hz, hq]
    ring
  have h' : 2 * z = 2 * m + 1 := by exact_mod_cast h
  omega

/-- The class of `1/2` in `ℚ / ℤ` is not zero. -/
private theorem half_ne_zero_addCircle : ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) ≠ 0 := by
  rw [Ne, AddCircle.coe_eq_zero_iff]
  rintro ⟨n, hn⟩
  rw [zsmul_eq_mul, mul_one] at hn
  exact not_exists_intCast_eq_half_odd 0 (by norm_num) ⟨n, hn⟩

variable {G : Matrix (Fin 10) (Fin 10) ℤ} {hG : G.IsSymm}

/-- Two dual vectors of a standard-coordinate Gram lattice whose difference has a half-odd
coordinate have distinct discriminant classes. -/
private theorem mk_ne_mk_of_sub_eq_half_odd
    {x y : (ofGramMatrix (Pi.basisFun ℚ (Fin 10)) G hG).dualCarrier} (j : Fin 10) (m : ℤ)
    (h : (x : Fin 10 → ℚ) j - (y : Fin 10 → ℚ) j = (2 * m + 1) / 2) :
    (Submodule.Quotient.mk x : (ofGramMatrix (Pi.basisFun ℚ (Fin 10)) G hG).DiscriminantGroup) ≠
      Submodule.Quotient.mk y := by
  rw [Ne, discriminantGroup_mk_eq_iff, mem_ofGramMatrix_basisFun_carrier_iff]
  exact fun hxy ↦ not_exists_intCast_eq_half_odd m h (hxy j)

/-- A dual vector of a standard-coordinate Gram lattice with a half-odd coordinate has a nonzero
discriminant class. -/
private theorem mk_ne_zero_of_eq_half_odd
    {x : (ofGramMatrix (Pi.basisFun ℚ (Fin 10)) G hG).dualCarrier} (j : Fin 10) (m : ℤ)
    (h : (x : Fin 10 → ℚ) j = (2 * m + 1) / 2) :
    (Submodule.Quotient.mk x : (ofGramMatrix (Pi.basisFun ℚ (Fin 10)) G hG).DiscriminantGroup) ≠
      0 := by
  rw [Ne, discriminantGroup_mk_eq_zero_iff, mem_ofGramMatrix_basisFun_carrier_iff]
  exact fun hx ↦ not_exists_intCast_eq_half_odd m h (hx j)

/-- A dual vector of a standard-coordinate Gram lattice whose double has integer coordinates
has a discriminant class killed by two. -/
private theorem two_nsmul_mk_eq_zero
    {x : (ofGramMatrix (Pi.basisFun ℚ (Fin 10)) G hG).dualCarrier}
    (h : ∀ j, ∃ z : ℤ, (z : ℚ) = 2 * (x : Fin 10 → ℚ) j) :
    2 • (Submodule.Quotient.mk x :
      (ofGramMatrix (Pi.basisFun ℚ (Fin 10)) G hG).DiscriminantGroup) = 0 := by
  rw [← Submodule.Quotient.mk_smul, discriminantGroup_mk_eq_zero_iff,
    mem_ofGramMatrix_basisFun_carrier_iff]
  intro j
  simpa [two_smul, two_mul] using h j

/-- If `0, a, b, c` enumerate an additive monoid, `a ≠ 0`, and `a`, `b`, `c` are killed by two, then
the monoid has exponent two. -/
private theorem exponent_eq_two_of_bijective {α : Type*} [AddMonoid α] {a b c : α}
    (hbij : Function.Bijective ![0, a, b, c]) (ha : a ≠ 0) (h2a : 2 • a = 0) (h2b : 2 • b = 0)
    (h2c : 2 • c = 0) : AddMonoid.exponent α = 2 := by
  have hdvd : AddMonoid.exponent α ∣ 2 := by
    refine AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero fun x ↦ ?_
    obtain ⟨k, rfl⟩ := hbij.2 x
    fin_cases k <;> simp [h2a, h2b, h2c]
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · have := AddMonoid.exp_eq_one_iff.mp h1
    exact absurd (Subsingleton.elim a 0) ha
  · exact h2

/-- If `0, a, b, c` enumerate a type and `q` vanishes at `0`, `b` and `c` but not at `a`, then the
zero set of `q` is `{0, b, c}`. -/
private theorem setOf_eq_zero_of_bijective {α β : Type*} [Zero α] [Zero β] {q : α → β}
    {a b c : α} (hbij : Function.Bijective ![0, a, b, c]) (h0 : q 0 = 0) (ha : q a ≠ 0)
    (hb : q b = 0) (hc : q c = 0) : {x | q x = 0} = {0, b, c} := by
  have hab : a ≠ b := fun h ↦ ha (h ▸ hb)
  have hac : a ≠ c := fun h ↦ ha (h ▸ hc)
  have ha0 : a ≠ 0 := fun h ↦ ha (h ▸ h0)
  ext x
  obtain ⟨k, rfl⟩ := hbij.2 x
  fin_cases k <;> simp [h0, ha, hb, hc, hab, hac, ha0]

/-! ## The Gram matrices -/

/-- The Gram matrix `N₁` of the ten curves `(C₁, …, C₈, R, F)`: the components `C₁, …, C₈` of an
`I₄*` fibre forming `D₈(-1)`, a `(-2)`-curve `R` meeting only `C₄`, once, and a half-fibre `F`
of square zero meeting only `R`, once. -/
@[expose] def firstGram : Matrix (Fin 10) (Fin 10) ℤ :=
  !![-2, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    1, -2, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, -2, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, -2, 1, 0, 0, 0, 1, 0;
    0, 0, 0, 1, -2, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, -2, 1, 1, 0, 0;
    0, 0, 0, 0, 0, 1, -2, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, -2, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, -2, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0]

/-- The Gram matrix `N₂ = D₈(-1) ⊕ U` of the ten curves `(C₁, …, C₈, F', F)`: the components
`C₁, …, C₈` of an `I₄*` fibre forming `D₈(-1)`, and two half-fibres `F'` and `F` of square zero,
orthogonal to the components and meeting each other once. -/
@[expose] def secondGram : Matrix (Fin 10) (Fin 10) ℤ :=
  !![-2, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    1, -2, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, -2, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, -2, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, -2, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, -2, 1, 1, 0, 0;
    0, 0, 0, 0, 0, 1, -2, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, -2, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0]

/-- The matrix `N₁` is symmetric. -/
theorem firstGram_isSymm : firstGram.IsSymm := by
  decide

/-- The matrix `N₂` is symmetric. -/
theorem secondGram_isSymm : secondGram.IsSymm := by
  decide

/-- `N₂` is the orthogonal sum of the negated Cartan matrix of type `D₈` and the hyperbolic
plane. -/
private theorem secondGram_eq_reindex_fromBlocks :
    secondGram = reindex finSumFinEquiv finSumFinEquiv
      (fromBlocks (-CartanMatrix.D 8) 0 0 !![0, 1; 1, 0]) := by
  decide

/-- `N₁` is congruent to `N₂`: replacing `C₄` by `C₄ + F` and `F'` by `F' - F` in a basis with
Gram matrix `N₂` gives a basis with Gram matrix `N₁`. -/
private theorem firstGram_eq_transpose_mul_secondGram_mul :
    firstGram = (transvection 9 3 1 * transvection 9 8 (-1))ᵀ * secondGram *
      (transvection 9 3 1 * transvection 9 8 (-1)) := by
  decide

/-- The determinant of `N₂ = D₈(-1) ⊕ U` is `-4`. -/
theorem det_secondGram : secondGram.det = -4 := by
  rw [secondGram_eq_reindex_fromBlocks, det_reindex_self, det_fromBlocks_zero₂₁, det_neg,
    CartanMatrix.D_det (by norm_num), det_fin_two_of]
  norm_num

/-- The determinant of `N₁` is `-4`. -/
theorem det_firstGram : firstGram.det = -4 := by
  rw [firstGram_eq_transpose_mul_secondGram_mul, det_mul, det_mul, det_transpose, det_mul,
    det_transvection_of_ne _ _ (by decide), det_transvection_of_ne _ _ (by decide), det_secondGram]
  norm_num

/-! ## Dual vectors and discriminant classes of a ten-curve Gram lattice

In this section `A` is an integer matrix with `G A = 2`, so that the columns of `A / 2` are the
dual basis vectors of the standard-coordinate lattice presented by `G`. The two ten-curve lattices
share the entries of `A` used below, which locate the vector class and the two spinor classes. -/

section HalfColumn

variable {G A : Matrix (Fin 10) (Fin 10) ℤ} {hG : G.IsSymm}
  (hGA : ∀ i k, ∑ j, G k j * A j i = if k = i then 2 else 0)
include hGA

private theorem sum_mul_halfColumn (i k : Fin 10) :
    ∑ j, ((G k j : ℤ) : ℚ) * ((A j i : ℚ) / 2) = if k = i then 1 else 0 := by
  have h := Matrix.sum_mul_div_eq_ite G (fun j ↦ A j i) 2 two_ne_zero i (hGA i) k
  simpa only [Int.cast_ofNat] using h

private theorem halfColumn_mem_dualCarrier (i : Fin 10) :
    (fun j ↦ (A j i : ℚ) / 2) ∈ (ofGramMatrix (Pi.basisFun ℚ (Fin 10)) G hG).dualCarrier :=
  mem_ofGramMatrix_basisFun_dualCarrier_of_sum_eq_ite _ _ _ i (sum_mul_halfColumn hGA i)

private theorem form_halfColumn (y : Fin 10 → ℚ) (i : Fin 10) :
    (ofGramMatrix (Pi.basisFun ℚ (Fin 10)) G hG).form y (fun j ↦ (A j i : ℚ) / 2) = y i :=
  form_ofGramMatrix_basisFun_of_sum_eq_ite _ _ _ i (sum_mul_halfColumn hGA i) y

/-- The discriminant class of the `i`-th column of `A / 2`. -/
private noncomputable def halfColumnClass (i : Fin 10) :
    (ofGramMatrix (Pi.basisFun ℚ (Fin 10)) G hG).DiscriminantGroup :=
  Submodule.Quotient.mk ⟨_, halfColumn_mem_dualCarrier hGA i⟩

private theorem two_nsmul_halfColumnClass (i : Fin 10) :
    2 • (halfColumnClass hGA i : (ofGramMatrix (Pi.basisFun ℚ (Fin 10)) G hG).DiscriminantGroup) =
      0 :=
  two_nsmul_mk_eq_zero fun j ↦ ⟨A j i, by simp; ring⟩

private theorem discriminantQuadraticMap_halfColumnClass
    (hL : (ofGramMatrix (Pi.basisFun ℚ (Fin 10)) G hG).IsEven) (i : Fin 10) :
    (ofGramMatrix (Pi.basisFun ℚ (Fin 10)) G hG).discriminantQuadraticMap hL
      (halfColumnClass hGA i) = ((A i i / 4 : ℚ) : AddCircle (1 : ℚ)) := by
  rw [halfColumnClass, discriminantQuadraticMap_mk, form_halfColumn hGA]
  ring_nf

/-- A column of `A / 2` with diagonal entry `-1` has quadratic value `1/2`. -/
private theorem discriminantQuadraticMap_halfColumnClass_of_eq_neg_two
    (hL : (ofGramMatrix (Pi.basisFun ℚ (Fin 10)) G hG).IsEven) {i : Fin 10} (hi : A i i = -2) :
    (ofGramMatrix (Pi.basisFun ℚ (Fin 10)) G hG).discriminantQuadraticMap hL
      (halfColumnClass hGA i) = ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) := by
  rw [discriminantQuadraticMap_halfColumnClass hGA hL, hi,
    ← AddCircle.coe_add_period (1 : ℚ) (((-2 : ℤ) : ℚ) / 4)]
  norm_num

/-- A column of `A / 2` with diagonal entry `-2` is isotropic. -/
private theorem discriminantQuadraticMap_halfColumnClass_of_eq_neg_four
    (hL : (ofGramMatrix (Pi.basisFun ℚ (Fin 10)) G hG).IsEven) {i : Fin 10} (hi : A i i = -4) :
    (ofGramMatrix (Pi.basisFun ℚ (Fin 10)) G hG).discriminantQuadraticMap hL
      (halfColumnClass hGA i) = 0 := by
  rw [discriminantQuadraticMap_halfColumnClass hGA hL, hi, AddCircle.coe_eq_zero_iff]
  exact ⟨-1, by norm_num⟩

/-- The classes of the columns `0`, `6` and `7` of `A / 2` are nonzero and pairwise distinct. -/
private theorem halfColumnClass_pairwise_ne (h00 : A 0 0 = -2) (h06 : A 0 6 = -1)
    (h07 : A 0 7 = -1) (h60 : A 6 0 = -1) (h66 : A 6 6 = -4) (h67 : A 6 7 = -3) :
    (halfColumnClass hGA 0 : (ofGramMatrix (Pi.basisFun ℚ (Fin 10)) G hG).DiscriminantGroup) ≠ 0 ∧
      (halfColumnClass hGA 6 :
        (ofGramMatrix (Pi.basisFun ℚ (Fin 10)) G hG).DiscriminantGroup) ≠ 0 ∧
      (halfColumnClass hGA 7 :
        (ofGramMatrix (Pi.basisFun ℚ (Fin 10)) G hG).DiscriminantGroup) ≠ 0 ∧
      (halfColumnClass hGA 0 :
        (ofGramMatrix (Pi.basisFun ℚ (Fin 10)) G hG).DiscriminantGroup) ≠
        halfColumnClass hGA 6 ∧
      (halfColumnClass hGA 0 :
        (ofGramMatrix (Pi.basisFun ℚ (Fin 10)) G hG).DiscriminantGroup) ≠
        halfColumnClass hGA 7 ∧
      (halfColumnClass hGA 6 :
        (ofGramMatrix (Pi.basisFun ℚ (Fin 10)) G hG).DiscriminantGroup) ≠
        halfColumnClass hGA 7 :=
  ⟨mk_ne_zero_of_eq_half_odd 6 (-1) (by simp [h60]; norm_num),
    mk_ne_zero_of_eq_half_odd 0 (-1) (by simp [h06]; norm_num),
    mk_ne_zero_of_eq_half_odd 0 (-1) (by simp [h07]; norm_num),
    mk_ne_mk_of_sub_eq_half_odd 0 (-1) (by simp [h00, h06]; norm_num),
    mk_ne_mk_of_sub_eq_half_odd 0 (-1) (by simp [h00, h07]; norm_num),
    mk_ne_mk_of_sub_eq_half_odd 6 (-1) (by simp [h66, h67]; norm_num)⟩

end HalfColumn

/-! ## The first ten-curve lattice -/

/-- The first ten-curve lattice: the integral lattice on `ℚ¹⁰` with Gram matrix `N₁` in the
standard coordinate basis. Its carrier is `ℤ¹⁰`. -/
noncomputable def firstLattice : IntegralLattice (Fin 10 → ℚ) :=
  ofGramMatrix (Pi.basisFun ℚ (Fin 10)) firstGram firstGram_isSymm

/-- The first ten-curve lattice is even. -/
theorem isEven_firstLattice : firstLattice.IsEven := by
  rw [firstLattice, isEven_ofGramMatrix_iff]
  decide

instance : firstLattice.IsNondegenerate :=
  isNondegenerate_ofGramMatrix _ _ _
    (by convert (by norm_num [det_firstGram] : firstGram.det ≠ 0))

/-- The discriminant group of the first ten-curve lattice has order four. -/
@[simp]
theorem natCard_discriminantGroup_firstLattice :
    Nat.card firstLattice.DiscriminantGroup = 4 := by
  rw [firstLattice, natCard_discriminantGroup_ofGramMatrix]
  convert congrArg Int.natAbs det_firstGram
  rfl

/-- Twice the inverse of `N₁`, an integer matrix; `N₁⁻¹` is Schröer's matrix (14). -/
@[expose] def firstGramTwiceInverse : Matrix (Fin 10) (Fin 10) ℤ :=
  !![-2, -2, -2, -2, -2, -2, -1, -1, 0, 2;
    -2, -4, -4, -4, -4, -4, -2, -2, 0, 4;
    -2, -4, -6, -6, -6, -6, -3, -3, 0, 6;
    -2, -4, -6, -8, -8, -8, -4, -4, 0, 8;
    -2, -4, -6, -8, -10, -10, -5, -5, 0, 8;
    -2, -4, -6, -8, -10, -12, -6, -6, 0, 8;
    -1, -2, -3, -4, -5, -6, -4, -3, 0, 4;
    -1, -2, -3, -4, -5, -6, -3, -4, 0, 4;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 2;
    2, 4, 6, 8, 8, 8, 4, 4, 2, -4]

/-- `N₁⁻¹` has denominator two: `N₁ (2 N₁⁻¹) = 2`. -/
theorem firstGram_mul_firstGramTwiceInverse :
    firstGram * firstGramTwiceInverse = (2 : ℤ) • 1 := by
  decide

private theorem sum_firstGram_mul_firstGramTwiceInverse (i k : Fin 10) :
    ∑ j, firstGram k j * firstGramTwiceInverse j i = if k = i then 2 else 0 := by
  revert i k
  decide

/-- The vector of `ℚ¹⁰` dual to the `i`-th coordinate vector for the first ten-curve lattice:
the `i`-th column of `N₁⁻¹`. -/
def firstDualVector (i : Fin 10) : Fin 10 → ℚ :=
  fun j ↦ (firstGramTwiceInverse j i : ℚ) / 2

/-- The coordinates of `firstDualVector i` are the entries of the `i`-th column of `N₁⁻¹`. -/
@[simp]
theorem firstDualVector_apply (i j : Fin 10) :
    firstDualVector i j = (firstGramTwiceInverse j i : ℚ) / 2 :=
  (rfl)

/-- The vector `firstDualVector i` lies in the dual of the first ten-curve lattice. -/
theorem firstDualVector_mem_dualCarrier (i : Fin 10) :
    firstDualVector i ∈ firstLattice.dualCarrier :=
  halfColumn_mem_dualCarrier sum_firstGram_mul_firstGramTwiceInverse i

/-- `firstDualVector i` pairs every vector with its `i`-th coordinate. -/
@[simp]
theorem form_firstDualVector (y : Fin 10 → ℚ) (i : Fin 10) :
    firstLattice.form y (firstDualVector i) = y i :=
  form_halfColumn sum_firstGram_mul_firstGramTwiceInverse y i

/-- The discriminant class of the dual basis vector `firstDualVector i`. For `i = 0, 6, 7` these
are the classes of `C₁*`, `C₇*` and `C₈*`. -/
noncomputable def firstDualClass (i : Fin 10) : firstLattice.DiscriminantGroup :=
  Submodule.Quotient.mk ⟨firstDualVector i, firstDualVector_mem_dualCarrier i⟩

/-- The class of `firstDualVector i` in the discriminant group is `firstDualClass i`. -/
@[simp]
theorem mk_firstDualVector (i : Fin 10) :
    (Submodule.Quotient.mk ⟨firstDualVector i, firstDualVector_mem_dualCarrier i⟩ :
      firstLattice.DiscriminantGroup) = firstDualClass i :=
  (rfl)

/-- Every dual basis class of the first ten-curve lattice is killed by two. -/
theorem two_nsmul_firstDualClass (i : Fin 10) : 2 • firstDualClass i = 0 :=
  two_nsmul_halfColumnClass sum_firstGram_mul_firstGramTwiceInverse i

private theorem firstDualClass_pairwise_ne :
    firstDualClass 0 ≠ 0 ∧ firstDualClass 6 ≠ 0 ∧ firstDualClass 7 ≠ 0 ∧
      firstDualClass 0 ≠ firstDualClass 6 ∧ firstDualClass 0 ≠ firstDualClass 7 ∧
      firstDualClass 6 ≠ firstDualClass 7 :=
  halfColumnClass_pairwise_ne sum_firstGram_mul_firstGramTwiceInverse rfl rfl rfl rfl rfl rfl

/-- **The discriminant group of the first ten-curve lattice** consists of the four distinct
classes `0`, `C₁*`, `C₇*` and `C₈*`. -/
theorem bijective_firstDualClass :
    Function.Bijective ![0, firstDualClass 0, firstDualClass 6, firstDualClass 7] := by
  obtain ⟨h0, h6, h7, h06, h07, h67⟩ := firstDualClass_pairwise_ne
  exact bijective_vecCons_of_pairwise_ne natCard_discriminantGroup_firstLattice h0.symm h6.symm
    h7.symm h06 h07 h67

/-- The discriminant group of the first ten-curve lattice has exponent two. Together with
`natCard_discriminantGroup_firstLattice`, it is `(ℤ/2)²` rather than `ℤ/4`. -/
@[simp]
theorem exponent_discriminantGroup_firstLattice :
    AddMonoid.exponent firstLattice.DiscriminantGroup = 2 :=
  exponent_eq_two_of_bijective bijective_firstDualClass firstDualClass_pairwise_ne.1
    (two_nsmul_firstDualClass 0) (two_nsmul_firstDualClass 6) (two_nsmul_firstDualClass 7)

/-- The vector class `C₁*` of the first ten-curve lattice has full norm `-1`, so its quadratic
value is `1/2`. -/
@[simp]
theorem discriminantQuadraticMap_firstDualClass_zero :
    firstLattice.discriminantQuadraticMap isEven_firstLattice (firstDualClass 0) =
      ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) :=
  discriminantQuadraticMap_halfColumnClass_of_eq_neg_two sum_firstGram_mul_firstGramTwiceInverse
    isEven_firstLattice rfl

/-- The spinor class `C₇*` of the first ten-curve lattice has full norm `-2` and is
isotropic. -/
@[simp]
theorem discriminantQuadraticMap_firstDualClass_six :
    firstLattice.discriminantQuadraticMap isEven_firstLattice (firstDualClass 6) = 0 :=
  discriminantQuadraticMap_halfColumnClass_of_eq_neg_four sum_firstGram_mul_firstGramTwiceInverse
    isEven_firstLattice rfl

/-- The spinor class `C₈*` of the first ten-curve lattice has full norm `-2` and is
isotropic. -/
@[simp]
theorem discriminantQuadraticMap_firstDualClass_seven :
    firstLattice.discriminantQuadraticMap isEven_firstLattice (firstDualClass 7) = 0 :=
  discriminantQuadraticMap_halfColumnClass_of_eq_neg_four sum_firstGram_mul_firstGramTwiceInverse
    isEven_firstLattice rfl

/-- The isotropic discriminant classes of the first ten-curve lattice are `0` and the two spinor
classes `C₇*` and `C₈*`. -/
theorem setOf_discriminantQuadraticMap_firstLattice_eq_zero :
    {a | firstLattice.discriminantQuadraticMap isEven_firstLattice a = 0} =
      {0, firstDualClass 6, firstDualClass 7} :=
  setOf_eq_zero_of_bijective bijective_firstDualClass (map_zero _)
    (by rw [discriminantQuadraticMap_firstDualClass_zero]; exact half_ne_zero_addCircle)
    discriminantQuadraticMap_firstDualClass_six discriminantQuadraticMap_firstDualClass_seven

/-- The first ten-curve lattice has exactly three isotropic discriminant classes. -/
theorem ncard_setOf_discriminantQuadraticMap_firstLattice_eq_zero :
    {a | firstLattice.discriminantQuadraticMap isEven_firstLattice a = 0}.ncard = 3 := by
  obtain ⟨-, h6, h7, -, -, h67⟩ := firstDualClass_pairwise_ne
  rw [setOf_discriminantQuadraticMap_firstLattice_eq_zero]
  exact Set.ncard_eq_three.mpr ⟨0, _, _, h6.symm, h7.symm, h67, rfl⟩

/-! ## The second ten-curve lattice -/

/-- The second ten-curve lattice: the integral lattice on `ℚ¹⁰` with Gram matrix `N₂` in the
standard coordinate basis. Its carrier is `ℤ¹⁰`. -/
noncomputable def secondLattice : IntegralLattice (Fin 10 → ℚ) :=
  ofGramMatrix (Pi.basisFun ℚ (Fin 10)) secondGram secondGram_isSymm

/-- The second ten-curve lattice is even. -/
theorem isEven_secondLattice : secondLattice.IsEven := by
  rw [secondLattice, isEven_ofGramMatrix_iff]
  decide

instance : secondLattice.IsNondegenerate :=
  isNondegenerate_ofGramMatrix _ _ _
    (by convert (by norm_num [det_secondGram] : secondGram.det ≠ 0))

/-- The discriminant group of the second ten-curve lattice has order four. -/
@[simp]
theorem natCard_discriminantGroup_secondLattice :
    Nat.card secondLattice.DiscriminantGroup = 4 := by
  rw [secondLattice, natCard_discriminantGroup_ofGramMatrix]
  convert congrArg Int.natAbs det_secondGram
  rfl

/-- Twice the inverse of `N₂`, an integer matrix; `N₂⁻¹` is Schröer's matrix (16). -/
@[expose] def secondGramTwiceInverse : Matrix (Fin 10) (Fin 10) ℤ :=
  !![-2, -2, -2, -2, -2, -2, -1, -1, 0, 0;
    -2, -4, -4, -4, -4, -4, -2, -2, 0, 0;
    -2, -4, -6, -6, -6, -6, -3, -3, 0, 0;
    -2, -4, -6, -8, -8, -8, -4, -4, 0, 0;
    -2, -4, -6, -8, -10, -10, -5, -5, 0, 0;
    -2, -4, -6, -8, -10, -12, -6, -6, 0, 0;
    -1, -2, -3, -4, -5, -6, -4, -3, 0, 0;
    -1, -2, -3, -4, -5, -6, -3, -4, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 2;
    0, 0, 0, 0, 0, 0, 0, 0, 2, 0]

/-- `N₂⁻¹` has denominator two: `N₂ (2 N₂⁻¹) = 2`. -/
theorem secondGram_mul_secondGramTwiceInverse :
    secondGram * secondGramTwiceInverse = (2 : ℤ) • 1 := by
  decide

private theorem sum_secondGram_mul_secondGramTwiceInverse (i k : Fin 10) :
    ∑ j, secondGram k j * secondGramTwiceInverse j i = if k = i then 2 else 0 := by
  revert i k
  decide

/-- The vector of `ℚ¹⁰` dual to the `i`-th coordinate vector for the second ten-curve lattice:
the `i`-th column of `N₂⁻¹`. -/
def secondDualVector (i : Fin 10) : Fin 10 → ℚ :=
  fun j ↦ (secondGramTwiceInverse j i : ℚ) / 2

/-- The coordinates of `secondDualVector i` are the entries of the `i`-th column of `N₂⁻¹`. -/
@[simp]
theorem secondDualVector_apply (i j : Fin 10) :
    secondDualVector i j = (secondGramTwiceInverse j i : ℚ) / 2 :=
  (rfl)

/-- The vector `secondDualVector i` lies in the dual of the second ten-curve lattice. -/
theorem secondDualVector_mem_dualCarrier (i : Fin 10) :
    secondDualVector i ∈ secondLattice.dualCarrier :=
  halfColumn_mem_dualCarrier sum_secondGram_mul_secondGramTwiceInverse i

/-- `secondDualVector i` pairs every vector with its `i`-th coordinate. -/
@[simp]
theorem form_secondDualVector (y : Fin 10 → ℚ) (i : Fin 10) :
    secondLattice.form y (secondDualVector i) = y i :=
  form_halfColumn sum_secondGram_mul_secondGramTwiceInverse y i

/-- The discriminant class of the dual basis vector `secondDualVector i`. For `i = 0, 6, 7` these
are the classes of `C₁*`, `C₇*` and `C₈*`. -/
noncomputable def secondDualClass (i : Fin 10) : secondLattice.DiscriminantGroup :=
  Submodule.Quotient.mk ⟨secondDualVector i, secondDualVector_mem_dualCarrier i⟩

/-- The class of `secondDualVector i` in the discriminant group is `secondDualClass i`. -/
@[simp]
theorem mk_secondDualVector (i : Fin 10) :
    (Submodule.Quotient.mk ⟨secondDualVector i, secondDualVector_mem_dualCarrier i⟩ :
      secondLattice.DiscriminantGroup) = secondDualClass i :=
  (rfl)

/-- Every dual basis class of the second ten-curve lattice is killed by two. -/
theorem two_nsmul_secondDualClass (i : Fin 10) : 2 • secondDualClass i = 0 :=
  two_nsmul_halfColumnClass sum_secondGram_mul_secondGramTwiceInverse i

private theorem secondDualClass_pairwise_ne :
    secondDualClass 0 ≠ 0 ∧ secondDualClass 6 ≠ 0 ∧ secondDualClass 7 ≠ 0 ∧
      secondDualClass 0 ≠ secondDualClass 6 ∧ secondDualClass 0 ≠ secondDualClass 7 ∧
      secondDualClass 6 ≠ secondDualClass 7 :=
  halfColumnClass_pairwise_ne sum_secondGram_mul_secondGramTwiceInverse rfl rfl rfl rfl rfl rfl

/-- **The discriminant group of the second ten-curve lattice** consists of the four distinct
classes `0`, `C₁*`, `C₇*` and `C₈*`. -/
theorem bijective_secondDualClass :
    Function.Bijective ![0, secondDualClass 0, secondDualClass 6, secondDualClass 7] := by
  obtain ⟨h0, h6, h7, h06, h07, h67⟩ := secondDualClass_pairwise_ne
  exact bijective_vecCons_of_pairwise_ne natCard_discriminantGroup_secondLattice h0.symm h6.symm
    h7.symm h06 h07 h67

/-- The discriminant group of the second ten-curve lattice has exponent two. Together with
`natCard_discriminantGroup_secondLattice`, it is `(ℤ/2)²` rather than `ℤ/4`. -/
@[simp]
theorem exponent_discriminantGroup_secondLattice :
    AddMonoid.exponent secondLattice.DiscriminantGroup = 2 :=
  exponent_eq_two_of_bijective bijective_secondDualClass secondDualClass_pairwise_ne.1
    (two_nsmul_secondDualClass 0) (two_nsmul_secondDualClass 6) (two_nsmul_secondDualClass 7)

/-- The vector class `C₁*` of the second ten-curve lattice has full norm `-1`, so its quadratic
value is `1/2`. -/
@[simp]
theorem discriminantQuadraticMap_secondDualClass_zero :
    secondLattice.discriminantQuadraticMap isEven_secondLattice (secondDualClass 0) =
      ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) :=
  discriminantQuadraticMap_halfColumnClass_of_eq_neg_two sum_secondGram_mul_secondGramTwiceInverse
    isEven_secondLattice rfl

/-- The spinor class `C₇*` of the second ten-curve lattice has full norm `-2` and is
isotropic. -/
@[simp]
theorem discriminantQuadraticMap_secondDualClass_six :
    secondLattice.discriminantQuadraticMap isEven_secondLattice (secondDualClass 6) = 0 :=
  discriminantQuadraticMap_halfColumnClass_of_eq_neg_four sum_secondGram_mul_secondGramTwiceInverse
    isEven_secondLattice rfl

/-- The spinor class `C₈*` of the second ten-curve lattice has full norm `-2` and is
isotropic. -/
@[simp]
theorem discriminantQuadraticMap_secondDualClass_seven :
    secondLattice.discriminantQuadraticMap isEven_secondLattice (secondDualClass 7) = 0 :=
  discriminantQuadraticMap_halfColumnClass_of_eq_neg_four sum_secondGram_mul_secondGramTwiceInverse
    isEven_secondLattice rfl

/-- The isotropic discriminant classes of the second ten-curve lattice are `0` and the two spinor
classes `C₇*` and `C₈*`. -/
theorem setOf_discriminantQuadraticMap_secondLattice_eq_zero :
    {a | secondLattice.discriminantQuadraticMap isEven_secondLattice a = 0} =
      {0, secondDualClass 6, secondDualClass 7} :=
  setOf_eq_zero_of_bijective bijective_secondDualClass (map_zero _)
    (by rw [discriminantQuadraticMap_secondDualClass_zero]; exact half_ne_zero_addCircle)
    discriminantQuadraticMap_secondDualClass_six discriminantQuadraticMap_secondDualClass_seven

/-- The second ten-curve lattice has exactly three isotropic discriminant classes. -/
theorem ncard_setOf_discriminantQuadraticMap_secondLattice_eq_zero :
    {a | secondLattice.discriminantQuadraticMap isEven_secondLattice a = 0}.ncard = 3 := by
  obtain ⟨-, h6, h7, -, -, h67⟩ := secondDualClass_pairwise_ne
  rw [setOf_discriminantQuadraticMap_secondLattice_eq_zero]
  exact Set.ncard_eq_three.mpr ⟨0, _, _, h6.symm, h7.symm, h67, rfl⟩

end TauCeti.EnriquesTenCurve
