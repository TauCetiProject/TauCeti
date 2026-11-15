/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import TauCeti.RingTheory.LaurentSeries.Lattice

/-!
# Residue duality for Laurent series

For Laurent series over a commutative ring `R`, this file studies the symmetric bilinear form

`(f, g) ↦ Res(f g dX) = (f * g).coeff (-1)`,

the residue analogue of the trace form `Algebra.traceForm`, and its interaction with the lattices
`U_a = Xᵃ R⟦X⟧` of `TauCeti.LaurentSeries.lattice`.

The form is nondegenerate, since pairing with the monomial `X⁻¹⁻ⁿ` reads off the coefficient of
`Xⁿ`. The orthogonal complement of `U_a` is exactly `U_{-a}`: the product of a series in `U_a`
and a series in `U_{-a}` has no negative exponents, and the monomials `Xᵏ`, `k ≥ a`, detect every
coefficient below `-a`. Consequently the form descends to a pairing
`U_a / U_b × U_{-b} / U_{-a} → R`, which is perfect over every commutative ring. We use the
coefficient identification `TauCeti.LaurentSeries.latticeQuotientEquiv` from
`TauCeti.RingTheory.LaurentSeries.Lattice`. In these coordinates the pairing matches the
coefficient of `Xⁿ` with that of `X⁻¹⁻ⁿ`. This finite-level duality is the input for describing
continuous linear functionals on a Laurent-series field, which vanish on some `U_a`, through
the residue form.

## Main definitions

* `TauCeti.LaurentSeries.residueForm R`: the bilinear form `Res(f g dX)`.
* `TauCeti.LaurentSeries.residueFormQuotientPairing R a b`: the induced pairing
  `U_a / U_b × U_{-b} / U_{-a} → R`.

## Main results

* `TauCeti.LaurentSeries.residueForm_nondegenerate`: the residue form is nondegenerate.
* `TauCeti.LaurentSeries.residueForm_orthogonal_lattice`: the orthogonal complement of `U_a` is
  `U_{-a}`.
* `TauCeti.LaurentSeries.residueFormQuotientPairing_nondegenerate`: the induced pairing is
  nondegenerate.
* `TauCeti.LaurentSeries.residueFormQuotientPairing.instIsPerfPair`: the induced pairing is
  perfect.
-/

public section

open HahnSeries
open scoped LaurentSeries PowerSeries

namespace TauCeti.LaurentSeries

section Form

variable (R : Type*) [CommSemiring R]

/-- The residue form `(f, g) ↦ Res(f g dX)`, the coefficient of `X⁻¹` in `f * g`. -/
noncomputable def residueForm : LinearMap.BilinForm R R⸨X⸩ :=
  LinearMap.mk₂ R (fun f g ↦ (f * g).coeff (-1))
    (fun f₁ f₂ g ↦ by rw [add_mul, coeff_add])
    (fun r f g ↦ by rw [smul_mul_assoc, coeff_smul, smul_eq_mul])
    (fun f g₁ g₂ ↦ by rw [mul_add, coeff_add])
    (fun r f g ↦ by rw [mul_smul_comm, coeff_smul, smul_eq_mul])

variable {R}

/-- The residue form evaluates as the coefficient of `X⁻¹` in the product. -/
@[simp]
theorem residueForm_apply (f g : R⸨X⸩) : residueForm R f g = (f * g).coeff (-1) := (rfl)

/-- The residue form is symmetric. -/
theorem residueForm_isSymm : (residueForm R).IsSymm :=
  ⟨fun f g ↦ by rw [residueForm_apply, residueForm_apply, mul_comm]⟩

/-- Pairing with the monomial `r Xⁿ` reads off the coefficient of `X⁻¹⁻ⁿ`. -/
theorem residueForm_single_right (f : R⸨X⸩) (n : ℤ) (r : R) :
    residueForm R f (single n r) = f.coeff (-1 - n) * r := by
  simpa using coeff_mul_single_add (r := r) (x := f) (a := -1 - n) (b := n)

/-- Pairing the monomial `r Xⁿ` with `f` reads off the coefficient of `X⁻¹⁻ⁿ`. -/
theorem residueForm_single_left (n : ℤ) (r : R) (f : R⸨X⸩) :
    residueForm R (single n r) f = r * f.coeff (-1 - n) := by
  simpa using coeff_single_mul_add (r := r) (x := f) (a := -1 - n) (b := n)

/-- The residue form is nondegenerate on both sides. -/
theorem residueForm_nondegenerate : (residueForm R).Nondegenerate := by
  have hleft : (residueForm R).SeparatingLeft := fun f hf ↦ by
    ext n
    have := hf (single (-1 - n) 1)
    rwa [residueForm_single_right, sub_sub_cancel, mul_one] at this
  exact ⟨hleft, fun g hg ↦ hleft g fun f ↦ by rw [residueForm_isSymm.eq, hg]⟩

/-- Series in `U_a` and `U_b` with `0 ≤ a + b` have zero residue pairing. -/
theorem residueForm_eq_zero_of_mem_lattice {a b : ℤ} {f g : R⸨X⸩} (hf : f ∈ lattice R R a)
    (hg : g ∈ lattice R R b) (hab : 0 ≤ a + b) : residueForm R f g = 0 :=
  coeff_eq_zero_of_mem_lattice (mul_mem_lattice hf hg) (by omega)

/-- The orthogonal complement of the lattice `U_a` for the residue form is `U_{-a}`. -/
theorem residueForm_orthogonal_lattice (a : ℤ) :
    (residueForm R).orthogonal (lattice R R a) = lattice R R (-a) := by
  ext g
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  refine ⟨fun hg ↦ mem_lattice_iff.mpr fun n hn ↦ ?_,
    fun hg f hf ↦ residueForm_eq_zero_of_mem_lattice hf hg (by omega)⟩
  have := hg (single (-1 - n) 1) (single_mem_lattice (by omega) 1)
  rwa [residueForm_single_left, sub_sub_cancel, one_mul] at this

end Form

section Pairing

variable (R : Type*) [CommRing R]

/-- The residue form descends to a pairing `U_a / U_b × U_{-b} / U_{-a} → R`: series in `U_a` and
`U_{-a}`, or in `U_b` and `U_{-b}`, have zero residue pairing. -/
noncomputable def residueFormQuotientPairing (a b : ℤ) :
    latticeQuotient R R a b →ₗ[R]
      latticeQuotient R R (-b) (-a) →ₗ[R] R :=
  ((residueForm R).compl₁₂ (lattice R R a).subtype (lattice R R (-b)).subtype).liftQ₂ _ _
    (fun f hf ↦ LinearMap.mem_ker.mpr <| LinearMap.ext fun g ↦
      residueForm_eq_zero_of_mem_lattice (R := R) hf g.2 (by omega))
    (fun g hg ↦ LinearMap.mem_ker.mpr <| LinearMap.ext fun f ↦
      residueForm_eq_zero_of_mem_lattice (R := R) f.2 hg (by omega))

/-- On classes of series, the induced pairing is the residue form. -/
@[simp]
theorem residueFormQuotientPairing_mk_mk (a b : ℤ) (f : lattice R R a) (g : lattice R R (-b)) :
    residueFormQuotientPairing R a b (Submodule.Quotient.mk f) (Submodule.Quotient.mk g) =
      residueForm R f g := by
  rw [residueFormQuotientPairing, LinearMap.liftQ₂_mk, LinearMap.compl₁₂_apply,
    Submodule.subtype_apply, Submodule.subtype_apply]

/-- The pairing `U_a / U_b × U_{-b} / U_{-a} → R` induced by the residue form is nondegenerate on
both sides. -/
theorem residueFormQuotientPairing_nondegenerate (a b : ℤ) :
    (residueFormQuotientPairing R a b).Nondegenerate := by
  constructor
  · rintro ⟨f⟩ hf
    refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
    rw [Submodule.mem_comap, Submodule.subtype_apply, ← neg_neg b, ← residueForm_orthogonal_lattice,
      LinearMap.BilinForm.mem_orthogonal_iff]
    intro g hg
    rw [residueForm_isSymm.eq]
    exact hf (Submodule.Quotient.mk ⟨g, hg⟩)
  · rintro ⟨g⟩ hg
    refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
    rw [Submodule.mem_comap, Submodule.subtype_apply, ← residueForm_orthogonal_lattice,
      LinearMap.BilinForm.mem_orthogonal_iff]
    intro f hf
    exact hg (Submodule.Quotient.mk ⟨f, hf⟩)

private theorem residueForm_sum_single_right (a b j : ℤ) (c : Finset.Ico a b → R)
    (hj : -1 - j ∈ Finset.Ico a b) (r : R) :
    residueForm R (∑ k : Finset.Ico a b, single (k : ℤ) (c k)) (single j r) =
      c ⟨-1 - j, hj⟩ * r := by
  rw [residueForm_single_right, coeff_sum,
    Finset.sum_eq_single ⟨_, hj⟩ (fun k _ hk ↦ coeff_single_of_ne ?_) (by simp),
    coeff_single_same]
  exact fun h ↦ hk (Subtype.ext h.symm)

/-- The residue form induces a perfect pairing between the finite free quotients `U_a / U_b` and
`U_{-b} / U_{-a}`: every functional `φ` on `U_{-b} / U_{-a}` is the residue pairing with the
class of `∑ₖ φ(X⁻¹⁻ᵏ) Xᵏ`, the sum over `a ≤ k < b`. -/
instance residueFormQuotientPairing.instIsPerfPair (a b : ℤ) :
    (residueFormQuotientPairing R a b).IsPerfPair := by
  refine .of_bijective _ ⟨LinearMap.ker_eq_bot.mp (LinearMap.separatingLeft_iff_ker_eq_bot.mp
    (residueFormQuotientPairing_nondegenerate R a b).1), fun φ ↦ ?_⟩
  have hmem (k : Finset.Ico a b) : single (-1 - (k : ℤ)) (1 : R) ∈ lattice R R (-b) :=
    single_mem_lattice (by have := (Finset.mem_Ico.mp k.2).2; omega) 1
  refine ⟨Submodule.Quotient.mk ⟨∑ k : Finset.Ico a b,
    single (k : ℤ) (φ (Submodule.Quotient.mk ⟨_, hmem k⟩)), Submodule.sum_mem _ fun k _ ↦
      single_mem_lattice (Finset.mem_Ico.mp k.2).1 _⟩, ?_⟩
  refine (LinearMap.cancel_right (latticeQuotientEquiv R R (-b) (-a)).symm.surjective).mp
    (LinearMap.pi_ext fun j r ↦ ?_)
  have hj := Finset.mem_Ico.mp j.2
  have hk : -1 - (j : ℤ) ∈ Finset.Ico a b := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hsmul : (⟨single (j : ℤ) r, single_mem_lattice hj.1 r⟩ : lattice R R (-b)) =
      r • ⟨_, hmem ⟨_, hk⟩⟩ := Subtype.ext <| by ext n; simp [coeff_single]
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    latticeQuotientEquiv_symm_single, residueFormQuotientPairing_mk_mk,
    residueForm_sum_single_right R a b (j : ℤ) _ hk, hsmul, Submodule.Quotient.mk_smul,
    map_smul, smul_eq_mul, mul_comm]

end Pairing

end TauCeti.LaurentSeries
