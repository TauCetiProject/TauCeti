/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.RingTheory.LaurentSeries
public import TauCeti.RingTheory.HahnSeries.Multiplication

/-!
# Residue duality for Laurent series

For Laurent series over a commutative ring `R`, this file studies the symmetric bilinear form

`(f, g) ↦ Res(f g dX) = (f * g).coeff (-1)`,

the residue analogue of the trace form `Algebra.traceForm`, together with the lattices
`U_a = Xᵃ R⟦X⟧` of Laurent series whose coefficients vanish below `a`. Over a field these are the
closed balls of the valuation topology.

The form is nondegenerate, since pairing with the monomial `X⁻¹⁻ⁿ` reads off the coefficient of
`Xⁿ`. The orthogonal complement of `U_a` is exactly `U_{-a}`: the product of a series in `U_a`
and a series in `U_{-a}` has no negative exponents, and the monomials `Xᵏ`, `k ≥ a`, detect every
coefficient below `-a`. Consequently the form descends to a pairing
`U_a / U_b × U_{-b} / U_{-a} → R`, which is nondegenerate over every commutative ring and perfect
over a field. The coefficients at the exponents `a ≤ n < b` identify `U_a / U_b` with `R^{b - a}`,
so these quotients are finite free of rank `b - a`. This finite-level duality is the input for
describing continuous linear functionals on a Laurent-series field, which vanish on some `U_a`,
through the residue form.

## Main definitions

* `TauCeti.LaurentSeries.lattice R a`: the `R`-submodule `U_a = Xᵃ R⟦X⟧`.
* `TauCeti.LaurentSeries.residueForm R`: the bilinear form `Res(f g dX)`.
* `TauCeti.LaurentSeries.latticeQuotientEquiv R a b`: the coefficient identification of
  `U_a / U_b` with functions on the exponents `a ≤ n < b`.
* `TauCeti.LaurentSeries.residueQuotientPairing R a b`: the induced pairing
  `U_a / U_b × U_{-b} / U_{-a} → R`.

## Main results

* `TauCeti.LaurentSeries.residueForm_nondegenerate`: the residue form is nondegenerate.
* `TauCeti.LaurentSeries.orthogonal_lattice`: the orthogonal complement of `U_a` is `U_{-a}`.
* `TauCeti.LaurentSeries.finrank_latticeQuotient`: `U_a / U_b` has rank `b - a`.
* `TauCeti.LaurentSeries.residueQuotientPairing_nondegenerate`: the induced pairing is
  nondegenerate.
* `TauCeti.LaurentSeries.residueQuotientPairing.instIsPerfPair`: over a field it is perfect.
-/

public section

open HahnSeries
open scoped LaurentSeries PowerSeries

namespace TauCeti.LaurentSeries

section Lattice

variable (R : Type*) [Semiring R]

/-- The lattice `U_a = Xᵃ R⟦X⟧` of Laurent series whose coefficients vanish at every exponent
below `a`, as an `R`-submodule of `R⸨X⸩`. -/
def lattice (a : ℤ) : Submodule R R⸨X⸩ where
  carrier := {f | ∀ n < a, f.coeff n = 0}
  add_mem' hf hg n hn := by rw [coeff_add, hf n hn, hg n hn, add_zero]
  zero_mem' _ _ := coeff_zero
  smul_mem' r f hf n hn := by rw [coeff_smul, hf n hn, smul_zero]

variable {R}

/-- Membership in `U_a` is the vanishing of every coefficient below `a`. -/
theorem mem_lattice_iff {a : ℤ} {f : R⸨X⸩} : f ∈ lattice R a ↔ ∀ n < a, f.coeff n = 0 :=
  Iff.rfl

/-- Membership in `U_a` is the order bound `a ≤ ord f`. -/
theorem mem_lattice_iff_le_orderTop {a : ℤ} {f : R⸨X⸩} :
    f ∈ lattice R a ↔ (a : WithTop ℤ) ≤ f.orderTop := by
  rw [mem_lattice_iff, le_orderTop_iff_forall]
  simp only [WithTop.coe_lt_coe]

/-- A series in `U_a` has zero coefficient at every exponent below `a`. -/
theorem coeff_eq_zero_of_mem_lattice {a n : ℤ} {f : R⸨X⸩} (hf : f ∈ lattice R a) (hn : n < a) :
    f.coeff n = 0 :=
  hf n hn

/-- The monomial `r Xⁿ` lies in `U_a` once `a ≤ n`. -/
theorem single_mem_lattice {a n : ℤ} (h : a ≤ n) (r : R) : single n r ∈ lattice R a :=
  fun _ hm ↦ coeff_single_of_ne (by omega)

/-- The lattices decrease as the exponent bound increases. -/
theorem lattice_antitone : Antitone (lattice R) :=
  fun _ _ h _ hf n hn ↦ hf n (hn.trans_le h)

/-- Over a nontrivial semiring, `U_b ⊆ U_a` exactly when `a ≤ b`. -/
theorem lattice_le_lattice_iff [Nontrivial R] {a b : ℤ} : lattice R b ≤ lattice R a ↔ a ≤ b := by
  refine ⟨fun h ↦ ?_, fun h ↦ lattice_antitone h⟩
  by_contra! hba
  have := h (single_mem_lattice le_rfl 1) b hba
  rw [coeff_single_same] at this
  exact one_ne_zero this

/-- Every Laurent series lies in some lattice `U_a`. -/
theorem iSup_lattice : ⨆ a, lattice R a = ⊤ :=
  eq_top_iff.mpr fun f _ ↦ Submodule.mem_iSup_of_mem f.order fun _ hn ↦
    coeff_eq_zero_of_lt_order hn

/-- Only `0` lies in every lattice `U_a`. -/
theorem iInf_lattice : ⨅ a, lattice R a = ⊥ := by
  refine eq_bot_iff.mpr fun f hf ↦ ?_
  rw [Submodule.mem_iInf] at hf
  rw [Submodule.mem_bot]
  ext n
  exact hf (n + 1) n (Int.lt_succ n)

/-- A formal power series lies in `U_0`. -/
theorem coe_powerSeries_mem_lattice_zero (p : R⟦X⟧) : (p : R⸨X⸩) ∈ lattice R 0 := fun n hn ↦ by
  rw [PowerSeries.coeff_coe, ite_eq_left hn]

/-- The lattices multiply as `U_a U_b ⊆ U_{a + b}`. -/
theorem mul_mem_lattice {a b : ℤ} {f g : R⸨X⸩} (hf : f ∈ lattice R a) (hg : g ∈ lattice R b) :
    f * g ∈ lattice R (a + b) := by
  rw [mem_lattice_iff_le_orderTop] at hf hg ⊢
  exact (WithTop.coe_add a b ▸ add_le_add hf hg).trans orderTop_add_le_mul

/-- Over a field, `U_a` is the closed valuation ball `{f | v f ≤ exp (-a)}`. -/
theorem mem_lattice_iff_valuation_le {K : Type*} [Field K] {a : ℤ} {f : K⸨X⸩} :
    f ∈ lattice K a ↔ Valued.v f ≤ WithZero.exp (-a) :=
  (_root_.LaurentSeries.valuation_le_iff_coeff_lt_eq_zero K).symm

end Lattice

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
theorem residueForm_eq_zero_of_mem_lattice {a b : ℤ} {f g : R⸨X⸩} (hf : f ∈ lattice R a)
    (hg : g ∈ lattice R b) (hab : 0 ≤ a + b) : residueForm R f g = 0 :=
  coeff_eq_zero_of_mem_lattice (mul_mem_lattice hf hg) (by omega)

/-- The orthogonal complement of the lattice `U_a` for the residue form is `U_{-a}`. -/
theorem orthogonal_lattice (a : ℤ) : (residueForm R).orthogonal (lattice R a) = lattice R (-a) := by
  ext g
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  refine ⟨fun hg n hn ↦ ?_, fun hg f hf ↦ residueForm_eq_zero_of_mem_lattice hf hg (by omega)⟩
  have := hg (single (-1 - n) 1) (single_mem_lattice (by omega) 1)
  rwa [residueForm_single_left, sub_sub_cancel, one_mul] at this

end Form

section Quotient

variable (R : Type*) [CommRing R]

/-- The coefficient map `U_a → R^{[a, b)}`, whose kernel is `U_b`. -/
private noncomputable def latticeCoeff (a b : ℤ) : lattice R a →ₗ[R] Finset.Ico a b → R :=
  LinearMap.pi fun k ↦ (coeff.linearMap (k : ℤ)).comp (lattice R a).subtype

private theorem latticeCoeff_apply (a b : ℤ) (f : lattice R a) (k : Finset.Ico a b) :
    latticeCoeff R a b f k = (f : R⸨X⸩).coeff k := by
  simp [latticeCoeff]

private theorem ker_latticeCoeff (a b : ℤ) :
    LinearMap.ker (latticeCoeff R a b) = (lattice R b).comap (lattice R a).subtype := by
  ext ⟨f, hf⟩
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, mem_lattice_iff,
    funext_iff, latticeCoeff_apply, Pi.zero_apply, Subtype.forall,
    Finset.mem_Ico]
  exact ⟨fun h n hn ↦ (lt_or_ge n a).elim (hf n) fun han ↦ h n ⟨han, hn⟩,
    fun h n hn ↦ h n hn.2⟩

private theorem latticeCoeff_surjective (a b : ℤ) : Function.Surjective (latticeCoeff R a b) := by
  intro c
  refine ⟨⟨∑ k : Finset.Ico a b, single (k : ℤ) (c k), Submodule.sum_mem _ fun k _ ↦
    single_mem_lattice (Finset.mem_Ico.mp k.2).1 _⟩, funext fun k ↦ ?_⟩
  rw [latticeCoeff_apply, coeff_sum, Finset.sum_eq_single k
    (fun j _ hj ↦ coeff_single_of_ne (Subtype.coe_ne_coe.mpr hj.symm)) (by simp), coeff_single_same]

/-- The coefficients at the exponents `a ≤ n < b` identify the quotient `U_a / U_b` with the
functions on these exponents. -/
noncomputable def latticeQuotientEquiv (a b : ℤ) :
    (lattice R a ⧸ (lattice R b).comap (lattice R a).subtype) ≃ₗ[R] (Finset.Ico a b → R) :=
  (Submodule.quotEquivOfEq _ _ (ker_latticeCoeff R a b).symm).trans
    ((latticeCoeff R a b).quotKerEquivOfSurjective (latticeCoeff_surjective R a b))

/-- The class of `f ∈ U_a` in `U_a / U_b` corresponds to the coefficients of `f` at the
exponents `a ≤ n < b`. -/
@[simp]
theorem latticeQuotientEquiv_mk (a b : ℤ) (f : lattice R a) (k : Finset.Ico a b) :
    latticeQuotientEquiv R a b (Submodule.Quotient.mk f) k = (f : R⸨X⸩).coeff k := by
  rw [latticeQuotientEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk, latticeCoeff_apply]

/-- `U_a / U_b` is a free module, via its coefficients at the exponents `a ≤ n < b`. -/
instance (a b : ℤ) : Module.Free R (lattice R a ⧸ (lattice R b).comap (lattice R a).subtype) :=
  .of_equiv (latticeQuotientEquiv R a b).symm

/-- `U_a / U_b` is a finite module, via its coefficients at the exponents `a ≤ n < b`. -/
instance (a b : ℤ) : Module.Finite R (lattice R a ⧸ (lattice R b).comap (lattice R a).subtype) :=
  .equiv (latticeQuotientEquiv R a b).symm

/-- The quotient `U_a / U_b` has rank `b - a` (and is zero when `b ≤ a`). -/
theorem finrank_latticeQuotient [Nontrivial R] (a b : ℤ) :
    Module.finrank R (lattice R a ⧸ (lattice R b).comap (lattice R a).subtype) = (b - a).toNat := by
  rw [(latticeQuotientEquiv R a b).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_coe, Int.card_Ico]

/-- The residue form descends to a pairing `U_a / U_b × U_{-b} / U_{-a} → R`: series in `U_a` and
`U_{-a}`, or in `U_b` and `U_{-b}`, have zero residue pairing. -/
noncomputable def residueQuotientPairing (a b : ℤ) :
    (lattice R a ⧸ (lattice R b).comap (lattice R a).subtype) →ₗ[R]
      (lattice R (-b) ⧸ (lattice R (-a)).comap (lattice R (-b)).subtype) →ₗ[R] R :=
  ((residueForm R).compl₁₂ (lattice R a).subtype (lattice R (-b)).subtype).liftQ₂ _ _
    (fun f hf ↦ LinearMap.mem_ker.mpr <| LinearMap.ext fun g ↦
      residueForm_eq_zero_of_mem_lattice (R := R) hf g.2 (by omega))
    (fun g hg ↦ LinearMap.mem_ker.mpr <| LinearMap.ext fun f ↦
      residueForm_eq_zero_of_mem_lattice (R := R) f.2 hg (by omega))

/-- On classes of series, the induced pairing is the residue form. -/
@[simp]
theorem residueQuotientPairing_mk_mk (a b : ℤ) (f : lattice R a) (g : lattice R (-b)) :
    residueQuotientPairing R a b (Submodule.Quotient.mk f) (Submodule.Quotient.mk g) =
      residueForm R f g := by
  rw [residueQuotientPairing, LinearMap.liftQ₂_mk, LinearMap.compl₁₂_apply,
    Submodule.subtype_apply, Submodule.subtype_apply]

/-- The pairing `U_a / U_b × U_{-b} / U_{-a} → R` induced by the residue form is nondegenerate on
both sides. -/
theorem residueQuotientPairing_nondegenerate (a b : ℤ) :
    (residueQuotientPairing R a b).Nondegenerate := by
  constructor
  · rintro ⟨f⟩ hf
    refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
    rw [Submodule.mem_comap, Submodule.subtype_apply, ← neg_neg b, ← orthogonal_lattice,
      LinearMap.BilinForm.mem_orthogonal_iff]
    intro g hg
    rw [residueForm_isSymm.eq]
    exact hf (Submodule.Quotient.mk ⟨g, hg⟩)
  · rintro ⟨g⟩ hg
    refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
    rw [Submodule.mem_comap, Submodule.subtype_apply, ← orthogonal_lattice,
      LinearMap.BilinForm.mem_orthogonal_iff]
    intro f hf
    exact hg (Submodule.Quotient.mk ⟨f, hf⟩)

/-- Over a field, the residue form induces a perfect pairing between the finite-dimensional
quotients `U_a / U_b` and `U_{-b} / U_{-a}`. -/
instance residueQuotientPairing.instIsPerfPair (K : Type*) [Field K] (a b : ℤ) :
    (residueQuotientPairing K a b).IsPerfPair := by
  have h := residueQuotientPairing_nondegenerate K a b
  exact .of_injective (LinearMap.ker_eq_bot.mp (LinearMap.separatingLeft_iff_ker_eq_bot.mp h.1))
    (LinearMap.ker_eq_bot.mp (LinearMap.separatingRight_iff_flip_ker_eq_bot.mp h.2))

end Quotient

end TauCeti.LaurentSeries
