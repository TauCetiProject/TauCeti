/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic
public import TauCeti.LinearAlgebra.End.MonodromyFiltration.Basic
public import TauCeti.NumberTheory.GaloisRepresentation.LocalMonodromyDatum
public import TauCeti.NumberTheory.WeilNumber.GradedPure
public import TauCeti.RingTheory.Nilpotent.Log
public import TauCeti.Topology.Algebra.Group.ContinuousAut.Basic

/-!
# Weight–monodromy purity relative to a local monodromy datum

Let `D` be a local monodromy datum on a profinite group `H`: an inertia subgroup `I`, a tame
character `t : I → ℚ_ℓ`, an integer `q ≥ 2` and a Frobenius coset, with `t(Φ σ Φ⁻¹) = q⁻¹ t(σ)`
for `Φ` Frobenius. Let `ρ` be a representation of `H` on a finite-dimensional vector space `V`
over a field `E` over `ℚ_ℓ`.

A *monodromy operator* of `ρ` for `D` is a nilpotent endomorphism `N` of `V` such that some open
subgroup of inertia acts through `σ ↦ exp(t(σ) N)`. By Grothendieck's monodromy theorem every
continuous `ℓ`-adic representation of the Galois group of a local field has one for the standard
datum. The representation `ρ` is *weight–monodromy pure of weight `w`* if it has a monodromy
operator `N` such that, for every Frobenius element `Φ`, every eigenvalue of `ρ(Φ)` on the
graded piece `gr_j` of the monodromy filtration of `N`, centred at `0`, is a Weil `q`-number of
weight `w + j`. For the Galois group of a local field and its standard datum this is the
conclusion of the weight–monodromy conjecture; relative to an arbitrary datum, the inertia and
the tame character need not come from a discretely valued field.

The exponential `IsNilpotent.exp` of an endomorphism of `V` uses a `ℚ`-module structure on `V`,
which is assumed as `[Module ℚ V]`; such a structure is unique when it exists.

The definition determines an actual operator and graded action: the monodromy operator is unique
(`IsMonodromyOperator.unique`), because a value `a = t(σ) ≠ 0` on the common open subgroup
recovers `N` as `a⁻¹ log ρ(σ)`, and the twist of the tame character forces
`ρ(Φ) N ρ(Φ)⁻¹ = q⁻¹ N` (`IsMonodromyOperator.conj_frobenius`), so `ρ(Φ)` preserves the
monodromy filtration. Rescaling the tame character by `c` replaces `N` by `c⁻¹ N`, which has the
same monodromy filtration, so purity does not depend on the normalization of the tame character.

## Main definitions

* `TauCeti.LocalMonodromyDatum.IsMonodromyOperator D ρ N`: `N` is nilpotent and an open subgroup
  of inertia acts through `exp(t(σ) N)`.
* `TauCeti.LocalMonodromyDatum.IsWeightMonodromyPure D ρ w`: `ρ` has a monodromy operator `N`, and
  every Frobenius element is pure of weight `w + j` on the `j`-th graded piece of the monodromy
  filtration of `N`.

## Main results

* `TauCeti.LocalMonodromyDatum.IsMonodromyOperator.unique`: the monodromy operator is unique.
* `TauCeti.LocalMonodromyDatum.IsMonodromyOperator.conj_frobenius`: `ρ(Φ) N ρ(Φ)⁻¹ = q⁻¹ N` for
  every Frobenius element `Φ`.
* `TauCeti.LocalMonodromyDatum.IsMonodromyOperator.monodromyFiltration_le_comap`: Frobenius elements
  preserve the monodromy filtration.
* `TauCeti.LocalMonodromyDatum.isWeightMonodromyPure_iff_of_isMonodromyOperator`: purity may be
  tested on any monodromy operator.
* `TauCeti.LocalMonodromyDatum.isWeightMonodromyPure_smul_iff`: purity relative to `c • D` is
  purity relative to `D`.
* `TauCeti.LocalMonodromyDatum.isWeightMonodromyPure_of_subsingleton`: the zero representation is
  pure of every weight.
* `TauCeti.LocalMonodromyDatum.isWeightMonodromyPure_iff_of_isMonodromyOperator_zero`: when an open
  subgroup of inertia acts trivially, purity of weight `w` means that every Frobenius element is
  pure of weight `w`.

## References

* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §9: Proposition 9.1,
  Definition/Proposition 9.2 and Conjecture 9.3.
* P. Deligne, *La conjecture de Weil. II*, Publ. Math. IHÉS 52 (1980), §1.6 and §1.7.
-/

public section

noncomputable section

open Module

namespace TauCeti

namespace LocalMonodromyDatum

universe u

variable {ℓ : ℕ} [Fact ℓ.Prime]
  {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [T2Space H]
  [TotallyDisconnectedSpace H] (D : LocalMonodromyDatum ℓ H)
  {E V : Type*} [Field E] [Algebra ℚ_[ℓ] E] [AddCommGroup V] [Module E V] [Module ℚ V]
  (ρ : Representation E H V)

/-- `N` is a **monodromy operator** of the representation `ρ` for the local monodromy datum `D`:
`N` is nilpotent and some open subgroup of inertia acts through `σ ↦ exp(t(σ) N)`, where `t` is
the tame character of `D`. It is unique when it exists (`IsMonodromyOperator.unique`). -/
structure IsMonodromyOperator (N : End E V) : Prop where
  isNilpotent : IsNilpotent N
  exists_isOpen : ∃ U : Subgroup D.inertia, IsOpen (U : Set D.inertia) ∧
    ∀ σ ∈ U, ρ σ = IsNilpotent.exp (algebraMap ℚ_[ℓ] E (D.tame σ).toAdd • N)

variable {D ρ} {N N' : End E V}

/-- On the open subgroup of inertia where `ρ(σ) = exp(t(σ) N)`, the logarithm of `ρ(σ)` is
`t(σ) N`. -/
theorem IsMonodromyOperator.exists_isOpen_log (h : D.IsMonodromyOperator ρ N) :
    ∃ U : Subgroup D.inertia, IsOpen (U : Set D.inertia) ∧
      ∀ σ ∈ U, IsNilpotent.log (ρ σ) = algebraMap ℚ_[ℓ] E (D.tame σ).toAdd • N := by
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[ℓ] E).injective
  obtain ⟨U, hU, hρ⟩ := h.exists_isOpen
  exact ⟨U, hU, fun σ hσ ↦ by rw [hρ σ hσ, IsNilpotent.log_exp (h.isNilpotent.smul _)]⟩

/-- **The monodromy operator is unique**: two monodromy operators, possibly defined on different
open subgroups of inertia, agree. -/
theorem IsMonodromyOperator.unique (h : D.IsMonodromyOperator ρ N)
    (h' : D.IsMonodromyOperator ρ N') : N = N' := by
  -- On the open subgroup `U ⊓ U'` the tame character takes a nonzero value `a = t(σ)`, and
  -- `a N = log ρ(σ) = a N'`.
  obtain ⟨U, hU, hρ⟩ := h.exists_isOpen_log
  obtain ⟨U', hU', hρ'⟩ := h'.exists_isOpen_log
  obtain ⟨σ, hσ, ha⟩ := D.exists_algebraMap_tame_ne_zero_of_isOpen (E := E) (U ⊓ U')
    (hU.inter hU')
  exact smul_right_injective _ ha ((hρ σ hσ.1).symm.trans (hρ' σ hσ.2))

/-- **Frobenius twists the monodromy operator by `q⁻¹`**: `ρ(Φ) N ρ(Φ)⁻¹ = q⁻¹ N` for every
Frobenius element `Φ`. -/
theorem IsMonodromyOperator.conj_frobenius (h : D.IsMonodromyOperator ρ N) {Φ : H}
    (hΦ : Φ ∈ D.frobenius) : ρ Φ * N * ρ Φ⁻¹ = (D.q : E)⁻¹ • N := by
  -- Take `σ` with `t(σ) ≠ 0` in `U` and with `Φ σ Φ⁻¹ ∈ U`. Then `log ρ(Φ σ Φ⁻¹)` is both
  -- `ρ(Φ) (t(σ) N) ρ(Φ)⁻¹` and `t(Φ σ Φ⁻¹) N = q⁻¹ t(σ) N`.
  obtain ⟨U, hU, hρ⟩ := h.exists_isOpen_log
  have hc : Continuous (MulAut.conjNormal Φ : MulAut D.inertia) := by
    rw [← ContinuousAut.toMulAut_conjNormal, ContinuousAut.coe_toMulAut]
    exact map_continuous _
  obtain ⟨σ, hσ, ha⟩ := D.exists_algebraMap_tame_ne_zero_of_isOpen (E := E)
    (U ⊓ U.comap (MulAut.conjNormal Φ : MulAut D.inertia).toMonoidHom) (hU.inter (hU.preimage hc))
  -- The left side: `ρ(Φ σ Φ⁻¹)` is the conjugate of `ρ(σ)` by the unit `ρ(Φ)`.
  have hconj : IsNilpotent.log (ρ (MulAut.conjNormal Φ σ)) =
      algebraMap ℚ_[ℓ] E (D.tame σ).toAdd • (ρ Φ * N * ρ Φ⁻¹) := by
    simpa [hρ σ hσ.1, ← map_inv] using Units.log_conj (ρ.toHomUnits Φ) (ρ σ)
  -- The right side: the twist `t(Φ σ Φ⁻¹) = q⁻¹ t(σ)`.
  have htwist : IsNilpotent.log (ρ (MulAut.conjNormal Φ σ)) =
      algebraMap ℚ_[ℓ] E (D.tame σ).toAdd • ((D.q : E)⁻¹ • N) := by
    refine (hρ _ hσ.2).trans ?_
    simp only [MulEquiv.coe_toMonoidHom, D.tame_conj Φ (mem_frobenius.1 hΦ) σ, map_mul, map_inv₀,
      map_natCast]
    module
  exact smul_right_injective _ ha (hconj.symm.trans htwist)

/-- The commutation relation `N ρ(Φ) = q ρ(Φ) N` of the monodromy operator with a Frobenius
element `Φ`. -/
theorem IsMonodromyOperator.mul_frobenius (h : D.IsMonodromyOperator ρ N) {Φ : H}
    (hΦ : Φ ∈ D.frobenius) : N * ρ Φ = (D.q : E) • (ρ Φ * N) := by
  have hq : (D.q : E) ≠ 0 := D.natCast_q_ne_zero
  have h' := congrArg (· * ρ Φ) (h.conj_frobenius hΦ)
  simp only [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one, smul_mul_assoc] at h'
  rw [h', smul_smul, mul_inv_cancel₀ hq, one_smul]

/-- **Frobenius elements preserve the monodromy filtration** of the monodromy operator. -/
theorem IsMonodromyOperator.monodromyFiltration_le_comap (h : D.IsMonodromyOperator ρ N)
    {Φ : H} (hΦ : Φ ∈ D.frobenius) (a : ℤ) :
    N.monodromyFiltration a ≤ (N.monodromyFiltration a).comap (ρ Φ) := by
  have hq : (D.q : E)⁻¹ ≠ 0 := inv_ne_zero D.natCast_q_ne_zero
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.toHomUnits Φ)
  have he : e.conj N = (D.q : E)⁻¹ • N := by
    rw [← h.conj_frobenius hΦ]
    ext x
    simp [e, LinearEquiv.conj_apply_apply, ← LinearEquiv.coe_inv,
      ← LinearMap.GeneralLinearGroup.toLinearEquiv_inv, ← map_inv]
  rw [← Submodule.map_le_iff_le_comap]
  exact (N.map_monodromyFiltration_of_conj_eq_smul e hq he a).le

/-- Rescaling the tame character by `c` turns a monodromy operator `c N` for `D` into the
monodromy operator `N` for `c • D`. -/
theorem isMonodromyOperator_smul_iff (c : ℚ_[ℓ]ˣ) :
    (c • D).IsMonodromyOperator ρ N ↔ D.IsMonodromyOperator ρ (algebraMap ℚ_[ℓ] E c • N) := by
  have hc : algebraMap ℚ_[ℓ] E c ≠ 0 := (map_ne_zero _).2 c.ne_zero
  have hexp : ∀ σ : D.inertia, algebraMap ℚ_[ℓ] E ((c • D).tame σ).toAdd • N =
      algebraMap ℚ_[ℓ] E (D.tame σ).toAdd • algebraMap ℚ_[ℓ] E c • N := fun σ ↦ by
    rw [toAdd_smul_tame, map_mul, mul_comm, mul_smul]
  refine ⟨fun ⟨hN, U, hU, hρ⟩ ↦ ⟨hN.smul _, U, hU, fun σ hσ ↦ by rw [hρ σ hσ, hexp]⟩,
    fun ⟨hN, U, hU, hρ⟩ ↦ ⟨?_, U, hU, fun σ hσ ↦ by rw [hρ σ hσ, hexp]⟩⟩
  simpa [smul_smul, inv_mul_cancel₀ hc] using hN.smul (algebraMap ℚ_[ℓ] E c)⁻¹

/-- The zero endomorphism is a monodromy operator exactly when an open subgroup of inertia acts
trivially. -/
theorem isMonodromyOperator_zero_iff :
    D.IsMonodromyOperator ρ 0 ↔
      ∃ U : Subgroup D.inertia, IsOpen (U : Set D.inertia) ∧ ∀ σ ∈ U, ρ σ = 1 := by
  refine ⟨fun ⟨_, U, hU, hρ⟩ ↦ ⟨U, hU, fun σ hσ ↦ ?_⟩, fun ⟨U, hU, hρ⟩ ↦
    ⟨IsNilpotent.zero, U, hU, fun σ hσ ↦ ?_⟩⟩
  · rw [hρ σ hσ, smul_zero, IsNilpotent.exp_zero]
  · rw [hρ σ hσ, smul_zero, IsNilpotent.exp_zero]

/-- Every endomorphism of the zero space is a monodromy operator. -/
@[simp]
theorem isMonodromyOperator_of_subsingleton [Subsingleton V] : D.IsMonodromyOperator ρ N :=
  ⟨⟨1, Subsingleton.elim _ _⟩, ⊤, isOpen_univ, fun _ _ ↦ Subsingleton.elim _ _⟩

variable (D ρ)

/-- `ρ` is **weight–monodromy pure of weight `w`** relative to the local monodromy datum `D` if it
has a monodromy operator `N` and, for every Frobenius element `Φ` and every `j`, every eigenvalue
of `ρ(Φ)` on the graded piece `gr_j` of the monodromy filtration of `N` is a Weil `q`-number of
weight `w + j`. The operator `N` is unique (`IsMonodromyOperator.unique`), so purity may be tested
on any monodromy operator (`isWeightMonodromyPure_iff_of_isMonodromyOperator`). -/
def IsWeightMonodromyPure [CharZero E] [FiniteDimensional E V] (w : ℤ) : Prop :=
  ∃ N : End E V, D.IsMonodromyOperator ρ N ∧
    ∀ Φ ∈ D.frobenius, IsGradedPure (D.q : ℝ) w N.monodromyFiltration (ρ Φ)

variable {D ρ} [CharZero E] [FiniteDimensional E V] {w : ℤ}

/-- Unfolding weight–monodromy purity: `ρ` has a monodromy operator `N` such that every Frobenius
element is pure of weight `w + j` on the `j`-th graded piece of the monodromy filtration of `N`. -/
theorem isWeightMonodromyPure_iff :
    D.IsWeightMonodromyPure ρ w ↔ ∃ N : End E V, D.IsMonodromyOperator ρ N ∧
      ∀ Φ ∈ D.frobenius, IsGradedPure (D.q : ℝ) w N.monodromyFiltration (ρ Φ) :=
  Iff.rfl

/-- Purity may be tested on any monodromy operator. -/
theorem isWeightMonodromyPure_iff_of_isMonodromyOperator (hN : D.IsMonodromyOperator ρ N) :
    D.IsWeightMonodromyPure ρ w ↔
      ∀ Φ ∈ D.frobenius, IsGradedPure (D.q : ℝ) w N.monodromyFiltration (ρ Φ) :=
  ⟨fun ⟨_, hN', h⟩ ↦ hN'.unique hN ▸ h, fun h ↦ ⟨N, hN, h⟩⟩

/-- **Purity does not depend on the normalization of the tame character**: purity relative to
`c • D` is purity relative to `D`, the monodromy operator `N` being replaced by `c⁻¹ N`, which has
the same monodromy filtration. -/
@[simp]
theorem isWeightMonodromyPure_smul_iff (c : ℚ_[ℓ]ˣ) :
    (c • D).IsWeightMonodromyPure ρ w ↔ D.IsWeightMonodromyPure ρ w := by
  have hc : algebraMap ℚ_[ℓ] E c ≠ 0 := (map_ne_zero _).2 c.ne_zero
  constructor
  · rintro ⟨N, hN, h⟩
    refine ⟨_, (isMonodromyOperator_smul_iff c).1 hN, fun Φ hΦ ↦ ?_⟩
    rw [Module.End.monodromyFiltration_smul N hc]
    exact h Φ (by rwa [smul_frobenius])
  · rintro ⟨N, hN, h⟩
    refine ⟨(algebraMap ℚ_[ℓ] E c)⁻¹ • N, (isMonodromyOperator_smul_iff c).2 ?_, fun Φ hΦ ↦ ?_⟩
    · rwa [smul_smul, mul_inv_cancel₀ hc, one_smul]
    · rw [Module.End.monodromyFiltration_smul N (inv_ne_zero hc), smul_q]
      exact h Φ (by rwa [smul_frobenius] at hΦ)

/-- The zero representation is pure of every weight. -/
@[simp]
theorem isWeightMonodromyPure_of_subsingleton [Subsingleton V] : D.IsWeightMonodromyPure ρ w :=
  ⟨0, isMonodromyOperator_of_subsingleton, fun _ _ ↦ isGradedPure_of_subsingleton⟩

/-- If an open subgroup of inertia acts trivially, the monodromy operator is zero, its monodromy
filtration is concentrated in degree `0`, and purity of weight `w` means that every Frobenius
element is pure of weight `w`: all its eigenvalues are Weil `q`-numbers of weight `w`. -/
theorem isWeightMonodromyPure_iff_of_isMonodromyOperator_zero
    (h0 : D.IsMonodromyOperator ρ 0) :
    D.IsWeightMonodromyPure ρ w ↔ ∀ Φ ∈ D.frobenius, IsPure (D.q : ℝ) w (ρ Φ) := by
  rw [isWeightMonodromyPure_iff_of_isMonodromyOperator h0]
  refine forall₂_congr fun Φ _ ↦ isGradedPure_iff_isPure_of_eq_bot_of_eq_top
    (fun a ha ↦ Module.End.monodromyFiltration_zero_eq_bot_of_neg ha)
    (fun a ha ↦ Module.End.monodromyFiltration_zero_eq_top_of_nonneg ha)

end LocalMonodromyDatum

end TauCeti
