/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Quadratic
public import TauCeti.Analysis.SpecialFunctions.Elliptic.Period.Lattice
public import TauCeti.RingTheory.IntegralOrder.LeftOrder
import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Sphere

/-!
# Homothety classes and complex multiplication orders of period lattices

Two complex period pairs `L` and `L'` are **homothetic** (`PeriodPair.Homothetic`) when
`L'.lattice = (c • L).lattice` for some nonzero complex scalar `c ∈ ℂˣ`. By the classification of
lattice Weierstrass curves (`PeriodPair.weierstrassCurve_j_eq_iff`), homothety classes
(`PeriodPair.HomothetyClass`) correspond bijectively to complex `j`-invariants
(`PeriodPair.HomothetyClass.jEquiv`), while on upper-half-plane lattices `ℤ τ + ℤ` homothety is
exactly the `SL(2, ℤ)`-orbit relation (`UpperHalfPlane.homothetic_periodPair_iff`).

The complex endomorphism ring of a period lattice `Λ` is its left order `Λ.leftOrder`
(`Submodule.leftOrder`), the `ℤ`-subalgebra of `ℂ` consisting of all `α` with `α Λ ⊆ Λ`. Rescaling a
lattice preserves its left order (`PeriodPair.leftOrder_lattice_smul`), so `leftOrder` descends to
homothety classes (`PeriodPair.HomothetyClass.leftOrder`), is invariant under `SL(2, ℤ)` on `ℍ`,
and is invariant under changes of Weierstrass coordinates on complex elliptic curves
(`WeierstrassCurve.leftOrder_variableChange_periodLattice`).

For `τ ∈ ℍ` the left order of `ℤ τ + ℤ` is either `ℤ` (`⊥`) or an imaginary quadratic order:
`τ.periodPair.lattice.leftOrder ≠ ⊥` if and only if `τ` satisfies an integral quadratic equation
`a τ² + b τ + c = 0` with `a > 0` (`UpperHalfPlane.leftOrder_lattice_periodPair_ne_bot_iff`), and
when `(a, b, c)` has coprime coefficients the left order is `ℤ[a τ]` with integral basis `1, a τ`
(`UpperHalfPlane.mem_leftOrder_lattice_periodPair_iff_of_quadratic`,
`UpperHalfPlane.leftOrder_lattice_periodPair_of_quadratic`).

## Main definitions

* `PeriodPair.Homothetic`: homothety `∃ c : ℂˣ, L'.lattice = (c • L).lattice` between period pairs.
* `PeriodPair.homotheticSetoid`, `PeriodPair.HomothetyClass`: the quotient of `PeriodPair` by
  homothety.
* `PeriodPair.HomothetyClass.j`, `PeriodPair.HomothetyClass.jEquiv`: the `j`-invariant on homothety
  classes and the bijection `PeriodPair.HomothetyClass ≃ ℂ`.
* `PeriodPair.HomothetyClass.leftOrder`: the complex multiplier order of a homothety class.

## Main results

* `UpperHalfPlane.homothetic_periodPair_iff`: `ℤ τ + ℤ` and `ℤ τ' + ℤ` are homothetic iff `τ'` lies
  in the `SL(2, ℤ)`-orbit of `τ`.
* `PeriodPair.leftOrder_lattice_smul`, `WeierstrassCurve.leftOrder_variableChange_periodLattice`,
  `WeierstrassCurve.leftOrder_periodLattice_eq_of_j_eq`: homothety and isomorphism invariance of the
  complex endomorphism order.
* `UpperHalfPlane.leftOrder_lattice_periodPair_ne_bot_iff`,
  `UpperHalfPlane.leftOrder_lattice_periodPair_eq_bot_iff`: `ℤ τ + ℤ` has complex multiplication iff
  `τ` is imaginary quadratic over `ℚ`.
* `UpperHalfPlane.mem_leftOrder_lattice_periodPair_iff_of_quadratic`,
  `UpperHalfPlane.leftOrder_lattice_periodPair_of_quadratic`: for a primitive quadratic relation
  `a τ² + b τ + c = 0`, the left order of `ℤ τ + ℤ` is `ℤ + ℤ a τ = ℤ[a τ]`.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in Mathematics
  106, Springer, 2009, Theorem VI.4.1(b) and Theorem VI.6.1.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Graduate Texts in
  Mathematics 151, Springer, 1994, Proposition II.1.1.
* D. A. Cox, *Primes of the Form x² + ny²*, §10B and §11A.
-/

public noncomputable section

open Complex UpperHalfPlane WeierstrassCurve
open scoped MatrixGroups

/-! ### Homothety of period lattices -/

namespace PeriodPair

/-- Two period pairs `L` and `L'` are **homothetic** when `L'.lattice = (c • L).lattice` for some
nonzero complex number `c ∈ ℂˣ`. -/
def Homothetic (L L' : PeriodPair) : Prop :=
  ∃ c : ℂˣ, L'.lattice = (c • L).lattice

/-- Unfolding `PeriodPair.Homothetic`. -/
theorem homothetic_def {L L' : PeriodPair} :
    L.Homothetic L' ↔ ∃ c : ℂˣ, L'.lattice = (c • L).lattice :=
  Iff.rfl

/-- Period pairs with the same underlying lattice are homothetic. -/
theorem Homothetic.of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    L.Homothetic L' :=
  ⟨1, by rw [one_smul, h]⟩

/-- Homothety of period pairs is reflexive. -/
@[refl]
theorem Homothetic.refl (L : PeriodPair) : L.Homothetic L :=
  .of_lattice_eq rfl

/-- Homothety of period pairs is symmetric. -/
@[symm]
theorem Homothetic.symm {L L' : PeriodPair} (h : L.Homothetic L') : L'.Homothetic L := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c⁻¹, by rw [lattice_smul_eq_of_lattice_eq c⁻¹ hc, inv_smul_smul]⟩

/-- Homothety of period pairs is transitive. -/
@[trans]
theorem Homothetic.trans {L₁ L₂ L₃ : PeriodPair}
    (h₁ : L₁.Homothetic L₂) (h₂ : L₂.Homothetic L₃) : L₁.Homothetic L₃ := by
  obtain ⟨c₁, hc₁⟩ := h₁
  obtain ⟨c₂, hc₂⟩ := h₂
  exact ⟨c₂ * c₁, by rw [hc₂, lattice_smul_eq_of_lattice_eq c₂ hc₁, mul_smul]⟩

/-- Homothety of period pairs is equivalent to equality of the `j`-invariants of their Weierstrass
curves. -/
theorem homothetic_iff_weierstrassCurve_j_eq {L L' : PeriodPair} :
    L.Homothetic L' ↔ L.weierstrassCurve.j = L'.weierstrassCurve.j :=
  weierstrassCurve_j_eq_iff.symm

/-- Every period pair is homothetic to any nonzero complex rescaling of itself. -/
@[simp]
theorem homothetic_smul_right (c : ℂˣ) (L : PeriodPair) : L.Homothetic (c • L) :=
  ⟨c, rfl⟩

/-- Any nonzero complex rescaling of a period pair is homothetic to the original pair. -/
@[simp]
theorem homothetic_smul_left (c : ℂˣ) (L : PeriodPair) : (c • L).Homothetic L :=
  (L.homothetic_smul_right c).symm

/-- The equivalence relation of homothety on `PeriodPair`. -/
def homotheticSetoid : Setoid PeriodPair where
  r := Homothetic
  iseqv := ⟨Homothetic.refl, Homothetic.symm, Homothetic.trans⟩

/-- A **homothety class** of complex period lattices: the quotient of `PeriodPair` by
`PeriodPair.homotheticSetoid`. -/
def HomothetyClass : Type :=
  Quotient homotheticSetoid

namespace HomothetyClass

/-- The homothety class of a period pair `L`. -/
def mk (L : PeriodPair) : HomothetyClass :=
  Quotient.mk homotheticSetoid L

/-- Every homothety class is represented by a period pair. -/
theorem mk_surjective : Function.Surjective mk :=
  Quotient.mk_surjective

/-- Induction principle for `PeriodPair.HomothetyClass`. -/
@[elab_as_elim]
protected theorem ind {motive : HomothetyClass → Prop} (h : ∀ L, motive (mk L))
    (x : HomothetyClass) : motive x :=
  Quotient.ind h x

/-- Two period pairs determine the same homothety class if and only if they are homothetic. -/
theorem mk_eq_mk_iff {L L' : PeriodPair} : mk L = mk L' ↔ L.Homothetic L' :=
  Quotient.eq

/-- Rescaling a period pair does not change its homothety class. -/
@[simp]
theorem mk_smul (c : ℂˣ) (L : PeriodPair) : mk (c • L) = mk L :=
  mk_eq_mk_iff.mpr (homothetic_smul_left c L)

/-- Period pairs with the same lattice determine the same homothety class. -/
theorem mk_eq_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) : mk L = mk L' :=
  mk_eq_mk_iff.mpr (.of_lattice_eq h)

/-- Every homothety class is represented by `ℤ τ + ℤ` for some `τ ∈ ℍ`. -/
theorem mk_periodPair_surjective : Function.Surjective fun τ : ℍ ↦ mk τ.periodPair := by
  intro x
  obtain ⟨L, rfl⟩ := mk_surjective x
  obtain ⟨c, τ, hL⟩ := L.exists_lattice_eq_smul_periodPair
  exact ⟨τ, (mk_smul c τ.periodPair).symm.trans (mk_eq_of_lattice_eq hL.symm)⟩

/-- The `j`-invariant of a homothety class of complex lattices. -/
def j : HomothetyClass → ℂ :=
  Quotient.lift (fun L ↦ L.weierstrassCurve.j) fun _ _ h ↦ homothetic_iff_weierstrassCurve_j_eq.mp h

/-- On the homothety class of `L`, `j` is the `j`-invariant of `L.weierstrassCurve`. -/
@[simp]
theorem j_mk (L : PeriodPair) : (mk L).j = L.weierstrassCurve.j :=
  (rfl)

/-- On the homothety class of `ℤ τ + ℤ`, `j` is the modular invariant `TauCeti.ModularForm.j τ`. -/
theorem j_mk_periodPair (τ : ℍ) : (mk τ.periodPair).j = TauCeti.ModularForm.j τ :=
  weierstrassCurve_j_periodPair τ

/-- **The `j`-invariant separates homothety classes of complex lattices.** -/
theorem j_injective : Function.Injective j :=
  Quotient.ind₂ fun _ _ h ↦ Quotient.sound (homothetic_iff_weierstrassCurve_j_eq.mpr h)

/-- Every complex number is the `j`-invariant of a homothety class of complex lattices. -/
theorem j_surjective : Function.Surjective j := fun z ↦ by
  obtain ⟨τ, hτ⟩ := TauCeti.ModularForm.j_surjective z
  exact ⟨mk τ.periodPair, (j_mk_periodPair τ).trans hτ⟩

/-- **Classification of complex lattices up to homothety by the `j`-invariant.** -/
def jEquiv : HomothetyClass ≃ ℂ :=
  Equiv.ofBijective j ⟨j_injective, j_surjective⟩

/-- Applying `HomothetyClass.jEquiv` evaluates `HomothetyClass.j`. -/
@[simp]
theorem jEquiv_apply (x : HomothetyClass) : jEquiv x = x.j :=
  (rfl)

/-- The `j`-invariant of `jEquiv.symm z` is `z`. -/
@[simp]
theorem j_jEquiv_symm (z : ℂ) : (jEquiv.symm z).j = z :=
  jEquiv.apply_symm_apply z

/-- `jEquiv.symm` recovers a homothety class from its `j`-invariant. -/
@[simp]
theorem jEquiv_symm_j (x : HomothetyClass) : jEquiv.symm x.j = x :=
  jEquiv.symm_apply_apply x

end HomothetyClass

end PeriodPair

namespace UpperHalfPlane

/-- **Two upper-half-plane lattices `ℤ τ + ℤ` and `ℤ τ' + ℤ` are homothetic if and only if `τ'`
lies in the `SL(2, ℤ)`-orbit of `τ`.** -/
theorem homothetic_periodPair_iff {τ τ' : ℍ} :
    τ.periodPair.Homothetic τ'.periodPair ↔ ∃ γ : SL(2, ℤ), γ • τ = τ' := by
  refine ⟨fun ⟨c, hc⟩ ↦ ?_, fun ⟨γ, hγ⟩ ↦ ?_⟩
  · obtain ⟨γ, hγ, -⟩ := exists_smul_eq_and_denom_eq_of_lattice_periodPair_eq hc
    exact ⟨γ⁻¹, by rw [← hγ, inv_smul_smul]⟩
  · rw [← hγ]
    exact ⟨(Units.mk0 (denom γ τ) (denom_ne_zero γ τ))⁻¹, lattice_periodPair_smul γ τ⟩

/-- The Möbius action of `SL(2, ℤ)` preserves the homothety class of `ℤ τ + ℤ`. -/
theorem mk_homothetyClass_periodPair_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    PeriodPair.HomothetyClass.mk (γ • τ).periodPair = PeriodPair.HomothetyClass.mk τ.periodPair :=
  PeriodPair.HomothetyClass.mk_eq_mk_iff.mpr
    (homothetic_periodPair_iff.mpr ⟨γ⁻¹, inv_smul_smul γ τ⟩)

/-- Upper-half-plane points have the same lattice homothety class iff they lie in the same
`SL(2, ℤ)`-orbit. -/
theorem mk_homothetyClass_periodPair_eq_iff {τ τ' : ℍ} :
    PeriodPair.HomothetyClass.mk τ.periodPair = PeriodPair.HomothetyClass.mk τ'.periodPair ↔
      ∃ γ : SL(2, ℤ), γ • τ = τ' :=
  PeriodPair.HomothetyClass.mk_eq_mk_iff.trans homothetic_periodPair_iff

end UpperHalfPlane

/-! ### Invariance of the complex multiplier order -/

namespace PeriodPair

/-- Rescaling a period pair by `c ∈ ℂˣ` does not change the left order of its lattice. -/
@[simp]
theorem leftOrder_lattice_smul (c : ℂˣ) (L : PeriodPair) :
    (c • L).lattice.leftOrder = L.lattice.leftOrder := by
  ext x
  simp only [Submodule.mem_leftOrder_iff]
  refine ⟨fun h m hm ↦ ?_, fun h m hm ↦ ?_⟩
  · rw [← L.mul_mem_lattice_smul_iff c, mul_left_comm]
    exact h _ ((L.mul_mem_lattice_smul_iff c).mpr hm)
  · have hm' : (c⁻¹ : ℂˣ) * m ∈ L.lattice := by
      rw [← L.mul_mem_lattice_smul_iff c, ← mul_assoc, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, one_mul]
      exact hm
    have hx := (L.mul_mem_lattice_smul_iff c).mpr (h _ hm')
    simpa [mul_left_comm, ← mul_assoc] using hx

/-- Homothetic period pairs have the same complex multiplier order. -/
theorem Homothetic.leftOrder_lattice_eq {L L' : PeriodPair} (h : L.Homothetic L') :
    L.lattice.leftOrder = L'.lattice.leftOrder := by
  obtain ⟨c, hc⟩ := h
  rw [hc, leftOrder_lattice_smul]

/-- Period pairs whose Weierstrass curves have the same `j`-invariant have the same complex
multiplier order. -/
theorem leftOrder_lattice_eq_of_weierstrassCurve_j_eq {L L' : PeriodPair}
    (h : L.weierstrassCurve.j = L'.weierstrassCurve.j) :
    L.lattice.leftOrder = L'.lattice.leftOrder :=
  (homothetic_iff_weierstrassCurve_j_eq.mpr h).leftOrder_lattice_eq

namespace HomothetyClass

/-- The complex multiplier order (`Submodule.leftOrder`) of a homothety class of period lattices. -/
def leftOrder : HomothetyClass → Subalgebra ℤ ℂ :=
  Quotient.lift (fun L ↦ L.lattice.leftOrder) fun _ _ h ↦ h.leftOrder_lattice_eq

/-- On the homothety class of `L`, `leftOrder` is the left order of `L.lattice`. -/
@[simp]
theorem leftOrder_mk (L : PeriodPair) : (mk L).leftOrder = L.lattice.leftOrder :=
  (rfl)

end HomothetyClass

end PeriodPair

namespace UpperHalfPlane

/-- The complex multiplier order of `ℤ τ + ℤ` is invariant under the Möbius action of
`SL(2, ℤ)`. -/
theorem leftOrder_lattice_periodPair_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    (γ • τ).periodPair.lattice.leftOrder = τ.periodPair.lattice.leftOrder := by
  rw [lattice_periodPair_smul, PeriodPair.leftOrder_lattice_smul]

end UpperHalfPlane

namespace WeierstrassCurve

/-- Isomorphic complex elliptic curves have the same period-lattice multiplier order. -/
@[simp]
theorem leftOrder_variableChange_periodLattice (E : WeierstrassCurve ℂ) [E.IsElliptic]
    (C : VariableChange ℂ) :
    (C • E).periodLattice.leftOrder = E.periodLattice.leftOrder := by
  obtain ⟨L, hL⟩ := E.exists_periodPair_lattice_eq_periodLattice
  rw [variableChange_periodLattice, ← hL, ← PeriodPair.lattice_smul,
    PeriodPair.leftOrder_lattice_smul]

/-- Complex elliptic curves with the same `j`-invariant have the same period-lattice multiplier
order. -/
theorem leftOrder_periodLattice_eq_of_j_eq {E E' : WeierstrassCurve ℂ}
    [E.IsElliptic] [E'.IsElliptic] (h : E.j = E'.j) :
    E.periodLattice.leftOrder = E'.periodLattice.leftOrder := by
  obtain ⟨L, C, hu, rfl⟩ := E.exists_periodPair_variableChange_smul_eq
  obtain ⟨L', C', hu', rfl⟩ := E'.exists_periodPair_variableChange_smul_eq
  rw [periodLattice_eq_iff.mpr ⟨C, hu, rfl⟩, periodLattice_eq_iff.mpr ⟨C', hu', rfl⟩]
  rw [variableChange_j, variableChange_j] at h
  exact PeriodPair.leftOrder_lattice_eq_of_weierstrassCurve_j_eq h

end WeierstrassCurve

/-! ### The complex multiplier order of `ℤ τ + ℤ` -/

namespace UpperHalfPlane

/-- A complex number `x` preserves `ℤ τ + ℤ` under multiplication if and only if `x` and `x τ` both
lie in `ℤ τ + ℤ`. -/
theorem mem_leftOrder_lattice_periodPair_iff {τ : ℍ} {x : ℂ} :
    x ∈ τ.periodPair.lattice.leftOrder ↔
      x ∈ τ.periodPair.lattice ∧ x * (τ : ℂ) ∈ τ.periodPair.lattice := by
  rw [Submodule.mem_leftOrder_iff]
  refine ⟨fun h ↦ ⟨by simpa using h 1 (periodPair_ω₂ τ ▸ τ.periodPair.ω₂_mem_lattice),
    h (τ : ℂ) (periodPair_ω₁ τ ▸ τ.periodPair.ω₁_mem_lattice)⟩, fun ⟨hx₁, hxτ⟩ m hm ↦ ?_⟩
  obtain ⟨r, s, rfl⟩ := PeriodPair.mem_lattice.mp hm
  simp only [periodPair_ω₁, periodPair_ω₂, mul_one]
  have hmem : (r : ℂ) * (x * (τ : ℂ)) + (s : ℂ) * x ∈ τ.periodPair.lattice := by
    simpa [zsmul_eq_mul] using add_mem (τ.periodPair.lattice.smul_mem r hxτ)
      (τ.periodPair.lattice.smul_mem s hx₁)
  convert hmem using 1
  ring

/-- If `(a : ℂ) * τ² + b * τ + c = 0` for integers `a, b, c`, then `(a : ℂ) * τ` preserves the
lattice `ℤ τ + ℤ`. -/
theorem intCast_mul_mem_leftOrder_lattice_periodPair {τ : ℍ} {a b c : ℤ}
    (hrel : (a : ℂ) * (τ : ℂ) ^ 2 + b * (τ : ℂ) + c = 0) :
    (a : ℂ) * (τ : ℂ) ∈ τ.periodPair.lattice.leftOrder := by
  rw [mem_leftOrder_lattice_periodPair_iff]
  refine ⟨by simpa using intCast_mul_add_intCast_mem_lattice_periodPair τ a 0, ?_⟩
  have hmul : (a : ℂ) * (τ : ℂ) * (τ : ℂ) = ((-b : ℤ) : ℂ) * (τ : ℂ) + (-c : ℤ) := by
    push_cast
    linear_combination hrel
  rw [hmul]
  exact intCast_mul_add_intCast_mem_lattice_periodPair τ (-b) (-c)

/-- **Complex multiplication dichotomy for `ℤ τ + ℤ`** (Silverman, *AEC*, Theorem VI.6.1):
the multiplier order of `ℤ τ + ℤ` is strictly larger than `ℤ` if and only if `τ` satisfies an
integral quadratic equation `a τ² + b τ + c = 0` with `a > 0`. -/
theorem leftOrder_lattice_periodPair_ne_bot_iff {τ : ℍ} :
    τ.periodPair.lattice.leftOrder ≠ ⊥ ↔
      ∃ a b c : ℤ, 0 < a ∧ (a : ℂ) * (τ : ℂ) ^ 2 + b * (τ : ℂ) + c = 0 := by
  constructor
  · intro hne
    have hnot : ¬ τ.periodPair.lattice.leftOrder ≤ ⊥ := fun hle ↦
      hne (le_antisymm hle bot_le)
    obtain ⟨x, hx, hxbot⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
    obtain ⟨hx₁, hxτ⟩ := mem_leftOrder_lattice_periodPair_iff.mp hx
    obtain ⟨s, t, rfl⟩ := PeriodPair.mem_lattice.mp hx₁
    obtain ⟨p, q, hpq⟩ := PeriodPair.mem_lattice.mp hxτ
    simp only [periodPair_ω₁, periodPair_ω₂, mul_one] at hpq hxbot ⊢
    have hs : s ≠ 0 := fun hs0 ↦ hxbot (Algebra.mem_bot.mpr ⟨t, by simp [hs0]⟩)
    rcases lt_or_gt_of_ne hs with hneg | hpos
    · refine ⟨-s, p - t, q, neg_pos.mpr hneg, ?_⟩
      push_cast
      linear_combination hpq
    · refine ⟨s, t - p, -q, hpos, ?_⟩
      push_cast
      linear_combination -hpq
  · rintro ⟨a, b, c, ha, hrel⟩ hbot
    have hmem : (a : ℂ) * (τ : ℂ) ∈ (⊥ : Subalgebra ℤ ℂ) :=
      hbot ▸ intCast_mul_mem_leftOrder_lattice_periodPair hrel
    obtain ⟨m, hm⟩ := Algebra.mem_bot.mp hmem
    have him := congrArg Complex.im hm
    simp only [Algebra.algebraMap_eq_smul_one, zsmul_one, intCast_im, mul_im, intCast_re,
      zero_mul, add_zero, coe_im] at him
    have haR : (0 : ℝ) < a := Int.cast_pos.mpr ha
    exact (mul_pos haR τ.im_pos).ne him

/-- The multiplier order of `ℤ τ + ℤ` is `ℤ` (`⊥`) if and only if `τ` satisfies no nontrivial
integral quadratic equation. -/
theorem leftOrder_lattice_periodPair_eq_bot_iff {τ : ℍ} :
    τ.periodPair.lattice.leftOrder = ⊥ ↔
      ∀ a b c : ℤ, 0 < a → (a : ℂ) * (τ : ℂ) ^ 2 + b * (τ : ℂ) + c ≠ 0 := by
  rw [← not_iff_not, ← ne_eq, leftOrder_lattice_periodPair_ne_bot_iff]
  push Not
  rfl

/-- **Exact multiplier order of an imaginary quadratic lattice**: if `τ ∈ ℍ` satisfies an integral
quadratic relation `a τ² + b τ + c = 0` whose coefficients `(a, b, c)` generate the unit ideal of
`ℤ`, then the multipliers of `ℤ τ + ℤ` are precisely the integral combinations `m + k (a τ)`. -/
theorem mem_leftOrder_lattice_periodPair_iff_of_quadratic {τ : ℍ} {a b c : ℤ}
    (hrel : (a : ℂ) * (τ : ℂ) ^ 2 + b * (τ : ℂ) + c = 0)
    (hprim : ∃ u v w : ℤ, u * a + v * b + w * c = 1) {x : ℂ} :
    x ∈ τ.periodPair.lattice.leftOrder ↔ ∃ m k : ℤ, x = m + k * ((a : ℂ) * (τ : ℂ)) := by
  constructor
  · intro hx
    obtain ⟨u, v, w, huvw⟩ := hprim
    obtain ⟨hx₁, hxτ⟩ := mem_leftOrder_lattice_periodPair_iff.mp hx
    obtain ⟨s, t, rfl⟩ := PeriodPair.mem_lattice.mp hx₁
    obtain ⟨p, q, hpq⟩ := PeriodPair.mem_lattice.mp hxτ
    simp only [periodPair_ω₁, periodPair_ω₂, mul_one] at hpq ⊢
    -- Comparing coefficients of `τ` and `1` in `a (x τ - (s τ + t) τ) + s (a τ² + b τ + c) = 0`.
    have hlin : ((a * p - a * t + s * b : ℤ) : ℂ) * (τ : ℂ) + ((a * q + s * c : ℤ) : ℂ) = 0 := by
      push_cast
      linear_combination (a : ℂ) * hpq + s * hrel
    obtain ⟨h₁, h₂⟩ := intCast_mul_add_intCast_eq_zero_iff.mp hlin
    have hsb : s * b = (t - p) * a := by linear_combination h₁
    have hsc : s * c = -q * a := by linear_combination h₂
    have hs : s = (u * s + v * (t - p) - w * q) * a := by
      linear_combination -s * huvw + v * hsb + w * hsc
    refine ⟨t, u * s + v * (t - p) - w * q, ?_⟩
    have hsC : (s : ℂ) = ((u * s + v * (t - p) - w * q : ℤ) : ℂ) * a := by exact_mod_cast hs
    rw [hsC]
    push_cast
    ring
  · rintro ⟨m, k, rfl⟩
    have hθ := intCast_mul_mem_leftOrder_lattice_periodPair hrel
    simpa [zsmul_eq_mul] using add_mem (τ.periodPair.lattice.leftOrder.algebraMap_mem m)
      (τ.periodPair.lattice.leftOrder.smul_mem hθ k)

/-- If `τ ∈ ℍ` satisfies a primitive integral quadratic relation `a τ² + b τ + c = 0`, then the
left order of `ℤ τ + ℤ` is `ℤ[a τ]`. -/
theorem leftOrder_lattice_periodPair_of_quadratic {τ : ℍ} {a b c : ℤ}
    (hrel : (a : ℂ) * (τ : ℂ) ^ 2 + b * (τ : ℂ) + c = 0)
    (hprim : ∃ u v w : ℤ, u * a + v * b + w * c = 1) :
    τ.periodPair.lattice.leftOrder = Algebra.adjoin ℤ {(a : ℂ) * (τ : ℂ)} := by
  refine le_antisymm (fun x hx ↦ ?_) (Algebra.adjoin_le ?_)
  · obtain ⟨m, k, rfl⟩ := (mem_leftOrder_lattice_periodPair_iff_of_quadratic hrel hprim).mp hx
    have hθ : (a : ℂ) * (τ : ℂ) ∈ Algebra.adjoin ℤ {(a : ℂ) * (τ : ℂ)} :=
      Algebra.subset_adjoin (Set.mem_singleton _)
    simpa [zsmul_eq_mul] using add_mem ((Algebra.adjoin ℤ _).algebraMap_mem m)
      ((Algebra.adjoin ℤ _).smul_mem hθ k)
  · rw [Set.singleton_subset_iff]
    exact intCast_mul_mem_leftOrder_lattice_periodPair hrel

/-- For a monic quadratic point `τ² + B τ + C = 0`, the left order of `ℤ τ + ℤ` agrees with
`UpperHalfPlane.quadraticOrder`. -/
theorem leftOrder_lattice_periodPair_eq_quadraticOrder {τ : ℍ} {B C : ℤ}
    (hτ : (τ : ℂ) ^ 2 + B * τ + C = 0) :
    τ.periodPair.lattice.leftOrder = τ.quadraticOrder hτ := by
  ext x
  rw [Submodule.mem_leftOrder_iff]
  exact (τ.mem_quadraticOrder_iff_mul_mem hτ x).symm

end UpperHalfPlane
