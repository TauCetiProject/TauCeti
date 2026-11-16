/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Basic

/-!
# Regular standard quadratic equations

A standard quadratic equation `S = 1` over `G`, with solutions sought in a group `H` receiving
the coefficients through `ι : G →* H`, is *regular* when its coefficients stay nontrivial in `H`,
it has a solution in `H`, and either `κ(S) ≥ 4` and `S` has a non-commutative solution, or `S` is
`[x, y] d = 1`, or `S` is `[x₁, y₁][x₂, y₂] = 1`. Here `κ(S)` is the number of variables of `S`,
plus one when the coefficient `d` occurs.

This is the second formulation of [IFT], Definition 6, with three changes. First, the genus-two
equation `[x₁, y₁][x₂, y₂] = 1` is listed explicitly: it has `κ = 4`, but all its solutions are
commutative, so the clause on non-commutative solutions does not cover it, although the first
formulation of Definition 6 names it as regular. Second, a regular equation must have a solution in
every case, also when it is `[x, y] d = 1`: over `F(a, b)`, the equation `[x, y] = a` has none.
Third, [IFT] takes `H = G` with `ι` the identity, where the coefficients are nontrivial by the
definition of a standard equation; for a general coefficient map this has to be required. Otherwise
`[x, y] d = 1` with `ι d = 1`, which is the equation `[x, y] = 1` over `H`, would be regular, and so
would `z₁⁻¹ c₁ z₁ z₂⁻¹ c₂ z₂ z₃⁻¹ c₃ z₃ d = 1` with `ι c₁ = 1`, which over `H` is the equation
`z₂⁻¹ c₂ z₂ z₃⁻¹ c₃ z₃ d = 1` with `κ = 3`.

## Main definitions

* `TauCeti.GroupAlgGeom.Quadratic.Standard.IsRegular`: regular standard quadratic equations.

## Main results

* `TauCeti.GroupAlgGeom.Quadratic.Standard.isRegular_iff_of_injective`: when the coefficients
  embed in `H`, the condition on the coefficients is automatic.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.IsRegular.map`: regularity passes along an injective
  `G`-homomorphism, for instance from `G` to a group containing it.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.isRegular_of_isGeneralPosition`: an equation whose
  coefficients stay nontrivial in `H`, with `κ(S) ≥ 4` and a solution in general position in `H`,
  is regular.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.isRegular_orientableCoeff_one_zero_iff`: `[x, y] d = 1`
  is regular exactly when `d` stays nontrivial in `H` and the equation has a solution.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.isRegular_genusTwo`: `[x₁, y₁][x₂, y₂] = 1` is regular.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.not_isRegular_commutator`: `[x, y] = 1` is not regular.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.IsRegular.four_le_kappa_of_not_isOrientable`: a regular
  non-orientable equation has `κ(S) ≥ 4`; so `x₁² ⋯ xₙ² = 1` with `n ≤ 3`, for instance
  `x₁² x₂² x₃² = 1`, is not regular
  (`TauCeti.GroupAlgGeom.Quadratic.Standard.not_isRegular_nonorientable_of_le_three`).
* `TauCeti.GroupAlgGeom.Quadratic.isRegular_commutator_eq_commutator`,
  `TauCeti.GroupAlgGeom.Quadratic.not_isRegular_commutator_eq_basis`,
  `TauCeti.GroupAlgGeom.Quadratic.isRegular_genusThree`: over `F(a, b)`, the equations
  `[x, y] = [a, b]` and `[x₁, y₁][x₂, y₂][x₃, y₃] = 1` are regular, and `[x, y] = a`, which has
  no solution, is not.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.7, Definition 6.
-/

public section

namespace TauCeti.GroupAlgGeom.Quadratic

open scoped commutatorElement

variable {G H K X : Type*} [Group G] [Group H] [Group K]

namespace Standard

/-! ### Regular equations -/

/-- A standard quadratic equation `S = 1` over `G` is regular over `H` when its coefficients are
nontrivial in `H`, it has a solution in `H`, and either `κ(S) ≥ 4` and `S` has a non-commutative
solution in `H`, or `S` is `[x, y] d = 1`, or `S` is `[x₁, y₁][x₂, y₂] = 1`. -/
def IsRegular (ι : G →* H) (S : Standard G X) : Prop :=
  (∀ g ∈ S.coeffs, ι g ≠ 1) ∧ (V ι {S.toWord}).Nonempty ∧
    ((4 ≤ S.kappa ∧ ∃ v ∈ V ι {S.toWord}, ¬S.IsCommutative ι v) ∨
      (S.IsOrientable ∧ S.genus = 1 ∧ S.atomicRank = 1 ∧ S.constant ≠ 1) ∨
      (S.IsOrientable ∧ S.genus = 2 ∧ S.constant = 1))

theorem isRegular_def {ι : G →* H} {S : Standard G X} :
    S.IsRegular ι ↔ (∀ g ∈ S.coeffs, ι g ≠ 1) ∧ (V ι {S.toWord}).Nonempty ∧
      ((4 ≤ S.kappa ∧ ∃ v ∈ V ι {S.toWord}, ¬S.IsCommutative ι v) ∨
        (S.IsOrientable ∧ S.genus = 1 ∧ S.atomicRank = 1 ∧ S.constant ≠ 1) ∨
        (S.IsOrientable ∧ S.genus = 2 ∧ S.constant = 1)) :=
  Iff.rfl

/-- When the coefficients embed in `H`, a standard quadratic equation is regular if and only if it
has a solution in `H` and either `κ(S) ≥ 4` and `S` has a non-commutative solution, or `S` is
`[x, y] d = 1`, or `S` is `[x₁, y₁][x₂, y₂] = 1`. -/
theorem isRegular_iff_of_injective {ι : G →* H} (hι : Function.Injective ι) {S : Standard G X} :
    S.IsRegular ι ↔ (V ι {S.toWord}).Nonempty ∧
      ((4 ≤ S.kappa ∧ ∃ v ∈ V ι {S.toWord}, ¬S.IsCommutative ι v) ∨
        (S.IsOrientable ∧ S.genus = 1 ∧ S.atomicRank = 1 ∧ S.constant ≠ 1) ∨
        (S.IsOrientable ∧ S.genus = 2 ∧ S.constant = 1)) :=
  and_iff_right fun _ hg => (map_ne_one_iff ι hι).2 (ne_one_of_mem_coeffs hg)

/-- The coefficients of a regular equation stay nontrivial in the group where it is solved. -/
theorem IsRegular.map_ne_one {ι : G →* H} {S : Standard G X} (h : S.IsRegular ι) {g : G}
    (hg : g ∈ S.coeffs) : ι g ≠ 1 :=
  h.1 g hg

/-- A regular equation has a solution. -/
theorem IsRegular.nonempty_V {ι : G →* H} {S : Standard G X} (h : S.IsRegular ι) :
    (V ι {S.toWord}).Nonempty :=
  h.2.1

/-- A standard quadratic equation with `κ(S) ≥ 4` whose coefficients stay nontrivial in `H` and
which has a non-commutative solution in `H` is regular. -/
theorem isRegular_of_not_isCommutative {ι : G →* H} {S : Standard G X} {v : X → H}
    (hS : ∀ g ∈ S.coeffs, ι g ≠ 1) (hκ : 4 ≤ S.kappa) (hv : v ∈ V ι {S.toWord})
    (hc : ¬S.IsCommutative ι v) : S.IsRegular ι :=
  ⟨hS, ⟨v, hv⟩, .inl ⟨hκ, v, hv, hc⟩⟩

/-- A standard quadratic equation with `κ(S) ≥ 4` whose coefficients stay nontrivial in `H` and
which has a solution in general position in `H` is regular. -/
theorem isRegular_of_isGeneralPosition {ι : G →* H} {S : Standard G X} {v : X → H}
    (hS : ∀ g ∈ S.coeffs, ι g ≠ 1) (hκ : 4 ≤ S.kappa) (hv : v ∈ V ι {S.toWord})
    (hg : S.IsGeneralPosition ι v) : S.IsRegular ι :=
  isRegular_of_not_isCommutative hS hκ hv
    (hg.not_isCommutative (two_le_atomicRank_of_four_le_kappa hκ))

/-- Regularity passes along an injective `G`-homomorphism `f : H → K`. -/
theorem IsRegular.map {ι : G →* H} {ιK : G →* K} {S : Standard G X} (h : S.IsRegular ι)
    (f : GHom ι ιK) (hf : Function.Injective f) : S.IsRegular ιK := by
  have hV {v : X → H} (hv : v ∈ V ι {S.toWord}) : f ∘ v ∈ V ιK {S.toWord} := by
    simp_all [← map_eval]
  have hc (g : G) (hg : g ∈ S.coeffs) : ιK g ≠ 1 := by
    rw [← f.map_coeff]
    exact (map_ne_one_iff f hf).2 (h.map_ne_one hg)
  obtain ⟨-, ⟨v, hv⟩, ⟨hκ, w, hw, hw'⟩ | h | h⟩ := h
  · exact isRegular_of_not_isCommutative hc hκ (hV hw) ((isCommutative_comp_iff f hf).not.2 hw')
  all_goals exact ⟨hc, ⟨f ∘ v, hV hv⟩, by simp [h]⟩

/-- Regularity is invariant under bijective `G`-homomorphisms. -/
theorem isRegular_congr {ι : G →* H} {ιK : G →* K} {S : Standard G X} (f : GHom ι ιK)
    (hf : Function.Bijective f) : S.IsRegular ι ↔ S.IsRegular ιK :=
  ⟨(·.map f hf.1), (·.map _ (f.symmOfBijective_injective hf))⟩

/-- An equation regular over `G` is regular over every group containing `G`. -/
theorem IsRegular.map_of_injective {S : Standard G X} (h : S.IsRegular (.id G)) {ι : G →* H}
    (hι : Function.Injective ι) : S.IsRegular ι :=
  h.map ⟨ι, fun _ => rfl⟩ hι

/-- The equation `[x, y] d = 1` is regular exactly when `d` stays nontrivial in `H` and the
equation has a solution in `H`. -/
@[simp]
theorem isRegular_orientableCoeff_one_zero_iff {ι : G →* H} {x y : Fin 1 → X} {z : Fin 0 → X}
    {c : Fin 0 → G} {d : G} (hnm : 0 < 1 + 0) (inj : (Sum.elim (Sum.elim x y) z).Injective)
    (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    (orientableCoeff 1 0 hnm x y z inj c hc d hd).IsRegular ι ↔
      ι d ≠ 1 ∧ (V ι {(orientableCoeff 1 0 hnm x y z inj c hc d hd).toWord}).Nonempty := by
  simp [isRegular_def, hd]

/-- The genus-two equation `[x₁, y₁][x₂, y₂] = 1` is regular over every group. -/
@[simp]
theorem isRegular_genusTwo (ι : G →* H) {x y : Fin 2 → X} (inj : (Sum.elim x y).Injective) :
    (orientable 2 two_pos x y inj).IsRegular ι :=
  ⟨by simp, ⟨1, one_mem_V_orientable ι two_pos inj⟩, by simp⟩

/-- The equation `[x, y] = 1` is not regular. -/
@[simp]
theorem not_isRegular_commutator (ι : G →* H) {x y : Fin 1 → X} (inj : (Sum.elim x y).Injective) :
    ¬(orientable 1 one_pos x y inj).IsRegular ι := by
  simp [isRegular_def]

/-- A regular non-orientable equation has `κ(S) ≥ 4`. -/
theorem IsRegular.four_le_kappa_of_not_isOrientable {ι : G →* H} {S : Standard G X}
    (h : S.IsRegular ι) (ho : ¬S.IsOrientable) : 4 ≤ S.kappa := by
  obtain ⟨-, -, ⟨hκ, -⟩ | ⟨ho', -⟩ | ⟨ho', -⟩⟩ := h
  exacts [hκ, absurd ho' ho, absurd ho' ho]

/-- The equation `x₁² ⋯ xₙ² = 1` with `n ≤ 3`, for instance `x₁² x₂² x₃² = 1`, is not regular. -/
@[simp]
theorem not_isRegular_nonorientable_of_le_three (ι : G →* H) {n : ℕ} {x : Fin n → X} (hn : 0 < n)
    (hn3 : n ≤ 3) (inj : x.Injective) : ¬(nonorientable n hn x inj).IsRegular ι := fun h =>
  absurd (h.four_le_kappa_of_not_isOrientable (by simp)) (by simp only [kappa_nonorientable]; lia)

/-- A regular equation has `κ(S) ≥ 3`. -/
theorem IsRegular.three_le_kappa {ι : G →* H} {S : Standard G X} (h : S.IsRegular ι) :
    3 ≤ S.kappa := by
  obtain ⟨-, -, ⟨hκ, -⟩ | ⟨ho, h1, h2, h3⟩ | ⟨ho, h2, h3⟩⟩ := h <;> cases S <;> simp_all <;> lia

/-- A regular equation of genus zero has at least three coefficient atoms. -/
theorem IsRegular.three_le_atomicRank_of_genus_eq_zero {ι : G →* H} {S : Standard G X}
    (h : S.IsRegular ι) (hg : S.genus = 0) : 3 ≤ S.atomicRank := by
  obtain ⟨-, -, ⟨hκ, -⟩ | ⟨-, h1, -⟩ | ⟨-, h2, -⟩⟩ := h <;> cases S <;> simp_all

end Standard

/-! ### Examples over the free group of rank two -/

section Examples

/-- Over `F(a, b)`, the equation `[x, y] = [a, b]` is regular. -/
theorem isRegular_commutator_eq_commutator :
    (Standard.orientableCoeff 1 0 one_pos ![0] ![1] Fin.elim0 (by decide) Fin.elim0 (by simp)
      ⁅(FreeGroup.of 0 : FreeGroup (Fin 2))⁻¹, (FreeGroup.of 1)⁻¹⁆⁻¹ (by decide) :
        Standard (FreeGroup (Fin 2)) (Fin 2)).IsRegular (.id _) := by
  refine (Standard.isRegular_orientableCoeff_one_zero_iff ..).2 ⟨by decide, FreeGroup.of, ?_⟩
  simp [Standard.toWord_def, commutatorElement_def, mul_assoc]

/-- Over `F(a, b)`, the equation `[x, y] = a` has no solution, so it is not regular, although its
constant is nontrivial. -/
theorem not_isRegular_commutator_eq_basis :
    ¬(Standard.orientableCoeff 1 0 one_pos ![0] ![1] Fin.elim0 (by decide) Fin.elim0 (by simp)
      (FreeGroup.of 0)⁻¹ (by decide) :
        Standard (FreeGroup (Fin 2)) (Fin 2)).IsRegular (.id _) := by
  intro h
  obtain ⟨v, hv⟩ := h.nonempty_V
  have key := congrArg (FreeGroup.lift ![Multiplicative.ofAdd (1 : ℤ), 1]) (mem_V.1 hv _ rfl)
  simp [Standard.toWord_def, commutatorElement_def, mul_comm] at key

/-- Over `F(a, b)`, the genus-three equation `[x₁, y₁][x₂, y₂][x₃, y₃] = 1` is regular. -/
theorem isRegular_genusThree :
    (Standard.orientable 3 (by lia) Sum.inl Sum.inr (by simp [Function.injective_id]) :
      Standard (FreeGroup (Fin 2)) (Fin 3 ⊕ Fin 3)).IsRegular (.id _) :=
  Standard.isRegular_of_isGeneralPosition (by simp) (by simp) isGeneralPosition_genusThree.1
    isGeneralPosition_genusThree.2

end Examples

end TauCeti.GroupAlgGeom.Quadratic
