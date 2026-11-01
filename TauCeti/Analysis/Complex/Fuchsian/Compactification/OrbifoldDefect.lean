/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Elliptic.Finite
public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Degree
public import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.Analysis.Complex.Fuchsian.Compactification.Fiber

/-!
# Orbifold defects on compactified Fuchsian quotients

The defect at an interior orbit with stabilizer order `m` is `1 - 1/m`; the defect at an
adjoined cusp is `1`. Thus the sum of defects is the elliptic correction plus the cusp count
in the orbifold Euler characteristic. The orders are those of the effective projective action.

Under a subgroup inclusion, local multiplicity times the complementary target defect equals
the complementary source defect. This identity relates analytic ramification to the elliptic
and cusp corrections in the Riemann–Hurwitz formula.

## References

* Svetlana Katok, *Fuchsian Groups*, §4.3.
* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, §3.1.
-/

public noncomputable section

open Function MulAction Set TauCeti TauCeti.RiemannSurface UpperHalfPlane
open scoped MatrixGroups

namespace Subgroup.CompactifiedQuotient

variable {Δ Γ : Subgroup PSL(2, ℝ)}

/-- The orbifold defect is `1 - 1/m` at an interior orbit of stabilizer order `m`, and `1` at
a cusp. Its sum is the correction to the Euler characteristic of the compactified surface. -/
def orbifoldDefect : Γ.CompactifiedQuotient → ℝ
  | ofQuotient q => 1 - (cardStabilizerOnOrbit q : ℝ)⁻¹
  | ofCusp _ => 1

/-- At an interior orbit the defect uses the effective stabilizer order. -/
@[simp]
theorem orbifoldDefect_ofQuotient (q : orbitRel.Quotient Γ ℍ) :
    orbifoldDefect (ofQuotient q) = 1 - (cardStabilizerOnOrbit q : ℝ)⁻¹ := (rfl)

/-- Each adjoined cusp contributes one to the orbifold defect. -/
@[simp]
theorem orbifoldDefect_ofCusp (C : Γ.CuspOrbit) :
    orbifoldDefect (ofCusp C) = 1 := (rfl)

/-- The interior defect is nonzero exactly at the elliptic orbits. This is a rewrite lemma:
the evaluation simp lemma first expands the defect into the stabilizer-order expression. -/
theorem orbifoldDefect_ofQuotient_ne_zero_iff (q : orbitRel.Quotient Γ ℍ) :
    orbifoldDefect (ofQuotient q) ≠ 0 ↔ q ∈ Γ.ellipticOrbits := by
  induction q using Quotient.inductionOn' with
  | _ z =>
    simp only [orbifoldDefect_ofQuotient, cardStabilizerOnOrbit_mk,
      quotientMk_mem_ellipticOrbits_iff, mem_freeLocus, ne_eq, sub_eq_zero, one_eq_inv,
      Nat.cast_eq_one, Subgroup.card_eq_one]

/-- The defect has finite support when there are finitely many elliptic and cusp orbits. -/
theorem finite_support_orbifoldDefect [Finite Γ.CuspOrbit] (hE : Γ.ellipticOrbits.Finite) :
    (support (orbifoldDefect (Γ := Γ))).Finite := by
  refine ((hE.image ofQuotient).union (finite_range (ofCusp (Γ := Γ)))).subset ?_
  intro x hx
  cases x with
  | ofQuotient q => exact Or.inl ⟨q, (orbifoldDefect_ofQuotient_ne_zero_iff q).mp hx, rfl⟩
  | ofCusp C => exact Or.inr ⟨C, rfl⟩

/-- The total defect is the cusp count plus the sum of elliptic corrections. -/
theorem finsum_orbifoldDefect [Finite Γ.CuspOrbit] (hE : Γ.ellipticOrbits.Finite) :
    ∑ᶠ x : Γ.CompactifiedQuotient, orbifoldDefect x =
      (Nat.card Γ.CuspOrbit : ℝ) +
        ∑ᶠ q ∈ Γ.ellipticOrbits, (1 - (cardStabilizerOnOrbit q : ℝ)⁻¹) := by
  classical
  have hI : (support fun q : orbitRel.Quotient Γ ℍ =>
      orbifoldDefect (ofQuotient q)).Finite :=
    hE.subset fun q hq => (orbifoldDefect_ofQuotient_ne_zero_iff q).mp hq
  let := Fintype.ofFinite Γ.CuspOrbit
  rw [← finsum_comp_equiv (equivSum Γ).symm]
  rw [TauCeti.finsum_sum_type (fun s => orbifoldDefect ((equivSum Γ).symm s))
    (by simpa only [HasFiniteSupport, Function.comp_def, equivSum_symm_inl] using hI)
    (Set.toFinite _)]
  simp only [equivSum_symm_inl, equivSum_symm_inr, orbifoldDefect_ofQuotient,
    orbifoldDefect_ofCusp]
  have hrestrict : (∑ᶠ q : orbitRel.Quotient Γ ℍ, (1 - (cardStabilizerOnOrbit q : ℝ)⁻¹)) =
      ∑ᶠ q ∈ Γ.ellipticOrbits, (1 - (cardStabilizerOnOrbit q : ℝ)⁻¹) := by
    have hs : support (fun q : orbitRel.Quotient Γ ℍ =>
        (1 - (cardStabilizerOnOrbit q : ℝ)⁻¹)) = Γ.ellipticOrbits :=
      Set.ext fun q => orbifoldDefect_ofQuotient_ne_zero_iff q
    rw [← hs, finsum_mem_support]
  rw [hrestrict, finsum_eq_sum_of_fintype (f := fun _ : Γ.CuspOrbit => (1 : ℝ))]
  simp [add_comm, Nat.card_eq_fintype_card]

variable [DiscreteTopology Γ] [DiscreteTopology Δ]

/-- A quotient map induced by inclusion preserves complementary defects after weighting by its local
multiplicity. At cusps both complementary defects vanish; at interior points this is the
multiplication formula for the two effective stabilizer orders. No finite-index assumption is
needed for this local identity. -/
theorem localMultiplicity_mul_one_sub_orbifoldDefect (h : Δ ≤ Γ)
    (x : Δ.CompactifiedQuotient) :
    (localMultiplicity (compactifiedQuotientMap h) x : ℝ) *
        (1 - orbifoldDefect (compactifiedQuotientMap h x)) = 1 - orbifoldDefect x := by
  cases x with
  | ofCusp C => simp
  | ofQuotient q =>
    induction q using Quotient.inductionOn' with
    | _ z =>
      simp only [compactifiedQuotientMap_ofQuotient, TauCeti.Setoid.map_of_le_mk,
        orbifoldDefect_ofQuotient, cardStabilizerOnOrbit_mk, sub_sub_cancel,
        localMultiplicity_compactifiedQuotientMap_ofQuotient_eq_ellipticRamificationIndex]
      have hcard := card_stabilizer_mul_ellipticRamificationIndex h z
      have hΔ : (Nat.card (stabilizer Δ z) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
      have hΓ : (Nat.card (stabilizer Γ z) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
      have hcard' : (Nat.card (stabilizer Δ z) : ℝ) * ellipticRamificationIndex h z =
          Nat.card (stabilizer Γ z) := by exact_mod_cast hcard
      field_simp
      nlinarith

/-- Summing target defects upstairs with local-multiplicity weights multiplies their sum by
the subgroup index. Only finiteness of the target's cusp and elliptic sets is needed. -/
theorem finsum_localMultiplicity_mul_orbifoldDefect (h : Δ ≤ Γ) [Δ.IsFiniteRelIndex Γ]
    [Finite Γ.CuspOrbit] (hE : Γ.ellipticOrbits.Finite) :
    (∑ᶠ x : Δ.CompactifiedQuotient,
      (localMultiplicity (compactifiedQuotientMap h) x : ℝ) *
        orbifoldDefect (compactifiedQuotientMap h x)) =
      (Δ.subgroupOf Γ).index * ∑ᶠ y : Γ.CompactifiedQuotient, orbifoldDefect y := by
  let w (x : Δ.CompactifiedQuotient) : ℝ :=
    (localMultiplicity (compactifiedQuotientMap h) x : ℝ) *
      orbifoldDefect (compactifiedQuotientMap h x)
  have hw : (support w).Finite := by
    refine ((finite_support_orbifoldDefect hE).preimage'
      (f := compactifiedQuotientMap h) fun y _ => ?_).subset ?_
    · have := finite_fiber_compactifiedQuotientMap h y
      have hy : {x | compactifiedQuotientMap h x = y}.Finite := Set.toFinite _
      simpa only [Set.preimage_singleton] using hy
    · exact fun x hx => (mul_ne_zero_iff.mp hx).2
  have hfiber (y : Γ.CompactifiedQuotient) :
      (∑ᶠ x : {x // compactifiedQuotientMap h x = y}, w x) =
        (Δ.subgroupOf Γ).index * orbifoldDefect y := by
    have := finite_fiber_compactifiedQuotientMap h y
    let := Fintype.ofFinite {x // compactifiedQuotientMap h x = y}
    have hy (x : {x // compactifiedQuotientMap h x = y}) : compactifiedQuotientMap h x = y :=
      x.property
    simp_rw [w, hy]
    rw [finsum_eq_sum_of_fintype, ← Finset.sum_mul, ← Nat.cast_sum,
      ← finsum_eq_sum_of_fintype]
    have he := fiberMultiplicitySum_compactifiedQuotientMap h y
    rw [fiberMultiplicitySum_def, ← finsum_subtype_eq_finsum_cond] at he
    exact congrArg (fun n : ℕ => (n : ℝ) * orbifoldDefect y) he
  rw [← TauCeti.finsum_fiberwise (compactifiedQuotientMap h) w hw]
  simp_rw [hfiber]
  exact (mul_finsum _ _).symm

end Subgroup.CompactifiedQuotient
