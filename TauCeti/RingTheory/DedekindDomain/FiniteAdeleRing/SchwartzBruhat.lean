/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyConstant.Basic
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Basic

/-!
# Schwartz–Bruhat functions above an idempotent of the finite adeles

Let `𝔸_f` be the finite adele ring of a Dedekind domain `R` with fraction field `K`, and
`Ô = ∏_v 𝒪_v` its integral finite adeles. An idempotent `e` of `𝔸_f` cuts out the components at a
set `S` of finite places: `e` has component `1` at the places of `S` and `0` elsewhere, so that
`e x` is the part of `x` at `S`. Every idempotent of `𝔸_f` is of this form, so stating things for
an idempotent `e` is the same as stating them for a set of places.

A function `Ψ` on `𝔸_f^n` is **Schwartz–Bruhat above `e`**
(`IsDedekindDomain.FiniteAdeleRing.IsSchwartzBruhatAbove e Ψ`) if it only sees the part at `S`
(`Ψ (e x) = Ψ x`), is locally constant, and the parts `e x` of the points of its support lie in a
compact set. The model example is the indicator of the **box** `B_e = {x : e x ∈ Ô^n}`
(`IsDedekindDomain.FiniteAdeleRing.integralBox n e`), the vectors that are integral at the places
of `S`.

Such a function is a finite combination of indicators of cosets of `t B_e`, for any finite idele
`t` such that `Ψ` is constant on the cosets of `t B_e` through its support, with coefficients its
values (`IsDedekindDomain.FiniteAdeleRing.IsSchwartzBruhatAbove.exists_eq_sum_indicator`). These
functions are the Schrödinger model of the Heisenberg group of `𝔸_f^n` above a set of places
disjoint from its conjugate, developed over a CM field in
`TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.SchrodingerModel`.

## Main definitions

* `IsDedekindDomain.FiniteAdeleRing.integralBox n e`: the box `B_e = {x : e x ∈ Ô^n}`.
* `IsDedekindDomain.FiniteAdeleRing.IsSchwartzBruhatAbove e Ψ`: `Ψ` is Schwartz–Bruhat above
  `e`.

## Main results

* `IsDedekindDomain.FiniteAdeleRing.isSchwartzBruhatAbove_indicator_integralBox`: the indicator
  of the box is Schwartz–Bruhat above an idempotent `e`.
* `IsDedekindDomain.FiniteAdeleRing.IsSchwartzBruhatAbove.comp_add` and
  `IsDedekindDomain.FiniteAdeleRing.IsSchwartzBruhatAbove.mul_left`: translates, and products with
  a locally constant function that only sees the part at `S`, are again Schwartz–Bruhat.
* `IsDedekindDomain.FiniteAdeleRing.IsSchwartzBruhatAbove.exists_eq_sum_indicator`: the
  decomposition into coset indicators.

## Provenance

The definitions and the coset decomposition correspond to `New.integralBox`,
`New.IsSchwartzBruhat` and `New.IsSchwartzBruhat.eq_sum_cosetIndicator` in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Weil/MixedModel/SchwartzBruhat.lean`, which works with the indicator of a set of places
of a CM field. Here the set of places is replaced by an idempotent, the base by any Dedekind
domain, and the values by any additive commutative monoid; the proof of the decomposition follows
grh-lean's: the function factors through the discrete quotient by the open subgroup `t B_e`, where
its support is finite.

## References

* F. Bruhat, *Distributions sur un groupe localement compact et applications à l'étude des
  représentations des groupes p-adiques*, Bull. Soc. Math. France 89 (1961), 43–75.
* A. Weil, *Sur certains groupes d'opérateurs unitaires*, Acta Math. 111 (1964), 143–211.
-/

public section

noncomputable section

open Set

namespace IsDedekindDomain.FiniteAdeleRing

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {n : Type*}

/-- An idempotent finite adele is integral: each of its components is `0` or `1`. -/
theorem _root_.IsIdempotentElem.mem_integralAdeles {e : FiniteAdeleRing R K}
    (he : IsIdempotentElem e) : e ∈ integralAdeles R K := by
  refine FiniteAdeleRing.mem_integralAdeles.2 fun v ↦ ?_
  have hv : IsIdempotentElem (e v) := by
    rw [IsIdempotentElem, ← mul_apply, he.eq]
  rcases IsIdempotentElem.iff_eq_zero_or_one.1 hv with h | h <;> rw [h]
  exacts [zero_mem _, one_mem _]

/-! ### The box -/

variable (n) in
/-- The **box** `B_e = {x : e x ∈ Ô^n}` of an element `e` of the finite adeles: the vectors of
`𝔸_f^n` whose coordinates times `e` are integral. For the idempotent `e` of a set `S` of places,
these are the vectors that are integral at every place of `S`. -/
def integralBox (e : FiniteAdeleRing R K) : AddSubgroup (n → FiniteAdeleRing R K) where
  carrier := {x | ∀ i, e * x i ∈ integralAdeles R K}
  add_mem' {x y} hx hy i := by
    rw [Pi.add_apply, mul_add]
    exact add_mem (hx i) (hy i)
  zero_mem' i := by
    rw [Pi.zero_apply, mul_zero]
    exact zero_mem _
  neg_mem' {x} hx i := by
    rw [Pi.neg_apply, mul_neg]
    exact neg_mem (hx i)

/-- A vector lies in the box of `e` exactly when its coordinates times `e` are integral. -/
@[simp]
theorem mem_integralBox {e : FiniteAdeleRing R K} {x : n → FiniteAdeleRing R K} :
    x ∈ integralBox n e ↔ ∀ i, e * x i ∈ integralAdeles R K :=
  Iff.rfl

/-- For an idempotent `e`, a vector lies in the box exactly when its part `e x` does. -/
theorem smul_mem_integralBox_iff {e : FiniteAdeleRing R K} (he : IsIdempotentElem e)
    {x : n → FiniteAdeleRing R K} : e • x ∈ integralBox n e ↔ x ∈ integralBox n e := by
  simp only [mem_integralBox, Pi.smul_apply, smul_eq_mul, ← mul_assoc, he.eq]

/-- The box of `a` lies in the box of `b a` for every integral `b`. -/
theorem integralBox_le_integralBox_mul {a b : FiniteAdeleRing R K}
    (hb : b ∈ integralAdeles R K) : integralBox n a ≤ integralBox n (b * a) := fun x hx ↦
  mem_integralBox.2 fun i ↦ by
    rw [mul_assoc]
    exact mul_mem hb (mem_integralBox.1 hx i)

/-- The box of `e` is open in `𝔸_f^n`. -/
theorem isOpen_integralBox [Finite n] (e : FiniteAdeleRing R K) :
    IsOpen (integralBox n e : Set (n → FiniteAdeleRing R K)) := by
  have h : (integralBox n e : Set (n → FiniteAdeleRing R K)) =
      ⋂ i, (fun x : n → FiniteAdeleRing R K ↦ e * x i) ⁻¹' integralAdeles R K := by
    ext x
    simp
  rw [h]
  exact isOpen_iInter_of_finite fun i ↦ (isOpen_integralAdeles R K).preimage (by fun_prop)

/-! ### Schwartz–Bruhat functions -/

/-- A function `Ψ` on `𝔸_f^n` is **Schwartz–Bruhat above `e`** if it only sees the part `e x` of
its argument, is locally constant, and the parts `e x` of the points of its support lie in a
compact set. For the idempotent `e` of a set `S` of places, `Ψ` depends only on the components at
`S`, and is a Schwartz–Bruhat function of these components. -/
structure IsSchwartzBruhatAbove {M : Type*} [Zero M] (e : FiniteAdeleRing R K)
    (Ψ : (n → FiniteAdeleRing R K) → M) : Prop where
  /-- `Ψ` only sees the part `e x` of its argument. -/
  apply_smul (x : n → FiniteAdeleRing R K) : Ψ (e • x) = Ψ x
  /-- `Ψ` is locally constant. -/
  isLocallyConstant : IsLocallyConstant Ψ
  /-- The parts `e x` of the points of the support of `Ψ` lie in a compact set. -/
  exists_isCompact :
    ∃ C : Set (n → FiniteAdeleRing R K), IsCompact C ∧ ∀ x, Ψ x ≠ 0 → e • x ∈ C

/-- **The indicator of the box is Schwartz–Bruhat** above an idempotent `e`, when the local
integer rings are compact. -/
theorem isSchwartzBruhatAbove_indicator_integralBox [Finite n] {M : Type*} [One M] [Zero M]
    [∀ v : HeightOneSpectrum R, CompactSpace (v.adicCompletionIntegers K)]
    {e : FiniteAdeleRing R K} (he : IsIdempotentElem e) :
    IsSchwartzBruhatAbove e ((integralBox n e : Set (n → FiniteAdeleRing R K)).indicator
      (1 : (n → FiniteAdeleRing R K) → M)) := by
  classical
  refine ⟨fun x ↦ ?_, ?_, ?_⟩
  · simp only [indicator_apply, SetLike.mem_coe, smul_mem_integralBox_iff he, Pi.one_apply]
  · -- The box is an open subgroup, hence clopen.
    have hU : IsClopen (integralBox n e : Set (n → FiniteAdeleRing R K)) :=
      ⟨AddSubgroup.isClosed_of_isOpen _ (isOpen_integralBox e), isOpen_integralBox e⟩
    exact (LocallyConstant.indicator (LocallyConstant.const _ (1 : M)) hU).isLocallyConstant
  · refine ⟨univ.pi fun _ ↦ (integralAdeles R K : Set (FiniteAdeleRing R K)),
      isCompact_univ_pi fun _ ↦ isCompact_integralAdeles, fun x hx i _ ↦ ?_⟩
    have hx' : x ∈ integralBox n e := by
      by_contra h
      exact hx (indicator_of_notMem h _)
    exact hx' i

namespace IsSchwartzBruhatAbove

variable {M : Type*} {e : FiniteAdeleRing R K}

/-- A **translate** of a Schwartz–Bruhat function above `e` is Schwartz–Bruhat above `e`. -/
theorem comp_add [Zero M] {Ψ : (n → FiniteAdeleRing R K) → M} (he : IsIdempotentElem e)
    (hΨ : IsSchwartzBruhatAbove e Ψ) (y : n → FiniteAdeleRing R K) :
    IsSchwartzBruhatAbove e fun x ↦ Ψ (x + y) := by
  obtain ⟨C, hC, hCΨ⟩ := hΨ.exists_isCompact
  refine ⟨fun x ↦ ?_, hΨ.isLocallyConstant.comp_continuous (continuous_id.add continuous_const),
    (· - e • y) '' C, hC.image (continuous_sub_right _), fun x hx ↦ ⟨_, hCΨ _ hx, ?_⟩⟩
  · rw [← hΨ.apply_smul (e • x + y), ← hΨ.apply_smul (x + y), smul_add, smul_add, smul_smul,
      he.eq]
  · simp only [smul_add, add_sub_cancel_right]

/-- The product of a Schwartz–Bruhat function above `e` with a locally constant function `φ` that
only sees the part `e x` of its argument is Schwartz–Bruhat above `e`. -/
theorem mul_left [MulZeroClass M] {Ψ : (n → FiniteAdeleRing R K) → M}
    (hΨ : IsSchwartzBruhatAbove e Ψ) {φ : (n → FiniteAdeleRing R K) → M}
    (hφ : IsLocallyConstant φ) (hφe : ∀ x, φ (e • x) = φ x) :
    IsSchwartzBruhatAbove e fun x ↦ φ x * Ψ x := by
  obtain ⟨C, hC, hCΨ⟩ := hΨ.exists_isCompact
  exact ⟨fun x ↦ by rw [hφe, hΨ.apply_smul], hφ.mul hΨ.isLocallyConstant,
    C, hC, fun x hx ↦ hCΨ x (right_ne_zero_of_mul hx)⟩

/-- The classes modulo `t B_e` on which a Schwartz–Bruhat function above `e` does not vanish are
finitely many: sending the class of `x` to the class of `e x` modulo the open subgroup `t Ô^n` is
injective, and the classes of the parts `e x` of the points of the support lie in the image of a
compact set, which is finite in the discrete quotient. -/
private theorem finite_support_out [Finite n] [Zero M] {Ψ : (n → FiniteAdeleRing R K) → M}
    (hΨ : IsSchwartzBruhatAbove e Ψ) (t : (FiniteAdeleRing R K)ˣ) :
    (Function.support fun q : (n → FiniteAdeleRing R K) ⧸
      (integralBox n e).comap (DistribSMul.toAddMonoidHom _ (↑t⁻¹ : FiniteAdeleRing R K)) ↦
        Ψ q.out).Finite := by
  let H' : AddSubgroup (n → FiniteAdeleRing R K) :=
    (integralBox n 1).comap (DistribSMul.toAddMonoidHom _ (↑t⁻¹ : FiniteAdeleRing R K))
  have hH' : IsOpen (H' : Set (n → FiniteAdeleRing R K)) := by
    rw [AddSubgroup.coe_comap]
    exact (isOpen_integralBox 1).preimage (continuous_const_smul _)
  have : DiscreteTopology ((n → FiniteAdeleRing R K) ⧸ H') :=
    QuotientAddGroup.discreteTopology hH'
  have hHH' (x : n → FiniteAdeleRing R K) :
      x ∈ (integralBox n e).comap (DistribSMul.toAddMonoidHom _ (↑t⁻¹ : FiniteAdeleRing R K)) ↔
        e • x ∈ H' := by
    simp only [H', AddSubgroup.mem_comap, DistribSMul.toAddMonoidHom_apply, mem_integralBox,
      Pi.smul_apply, smul_eq_mul, one_mul, mul_left_comm]
  obtain ⟨C, hC, hCΨ⟩ := hΨ.exists_isCompact
  refine Set.Finite.of_finite_image (f := fun q ↦
    ((e • q.out : n → FiniteAdeleRing R K) : (n → FiniteAdeleRing R K) ⧸ H')) ?_ ?_
  · refine (hC.image QuotientAddGroup.continuous_mk).finite_of_discrete.subset ?_
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨_, hCΨ _ hq, rfl⟩
  · intro q _ q' _ hqq'
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q']
    refine QuotientAddGroup.eq_iff_sub_mem.2 ((hHH' _).2 ?_)
    rw [smul_sub]
    exact QuotientAddGroup.eq_iff_sub_mem.1 hqq'

/-- **Coset decomposition.** Let `Ψ` be Schwartz–Bruhat above `e` and `t` a finite
idele such that `Ψ` is constant on the coset `x + t B_e` of every point `x` of its support. Then
`Ψ` is a finite sum of indicators of such cosets, with coefficients its values: there is a finite
set `A` of points of the support of `Ψ` with `Ψ = ∑_{q ∈ A} Ψ(q) · 1_{q + t B_e}`. -/
theorem exists_eq_sum_indicator [Finite n] [AddCommMonoid M] {Ψ : (n → FiniteAdeleRing R K) → M}
    (hΨ : IsSchwartzBruhatAbove e Ψ) (t : (FiniteAdeleRing R K)ˣ)
    (hper : ∀ x, Ψ x ≠ 0 → ∀ y, (↑t⁻¹ : FiniteAdeleRing R K) • (y - x) ∈ integralBox n e →
      Ψ y = Ψ x) :
    ∃ A : Finset (n → FiniteAdeleRing R K), (∀ q ∈ A, Ψ q ≠ 0) ∧
      Ψ = ∑ q ∈ A, {x | (↑t⁻¹ : FiniteAdeleRing R K) • (x - q) ∈ integralBox n e}.indicator
        fun _ ↦ Ψ q := by
  classical
  -- The open subgroup `H = t B_e`; `Ψ` is invariant under it and factors through the discrete
  -- quotient by it.
  let H : AddSubgroup (n → FiniteAdeleRing R K) :=
    (integralBox n e).comap (DistribSMul.toAddMonoidHom _ (↑t⁻¹ : FiniteAdeleRing R K))
  have hH : IsOpen (H : Set (n → FiniteAdeleRing R K)) := by
    rw [AddSubgroup.coe_comap]
    exact (isOpen_integralBox e).preimage (continuous_const_smul _)
  have : DiscreteTopology ((n → FiniteAdeleRing R K) ⧸ H) := QuotientAddGroup.discreteTopology hH
  have hmk {x y : n → FiniteAdeleRing R K} :
      (↑t⁻¹ : FiniteAdeleRing R K) • (y - x) ∈ integralBox n e ↔
        (y : (n → FiniteAdeleRing R K) ⧸ H) = x := by
    rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_comap, DistribSMul.toAddMonoidHom_apply]
  -- `Ψ` is constant on every coset of `H`, not only on those through its support.
  have hinv {x y : n → FiniteAdeleRing R K} (hxy : (y : (n → FiniteAdeleRing R K) ⧸ H) = x) :
      Ψ y = Ψ x := by
    by_cases hx : Ψ x = 0
    · rw [hx]
      by_contra hy
      exact hy ((hper y hy x (hmk.2 hxy.symm)).symm.trans hx)
    · exact hper x hx y (hmk.2 hxy)
  have hfin := hΨ.finite_support_out t
  refine ⟨hfin.toFinset.image Quotient.out, by simp, funext fun x ↦ ?_⟩
  rw [Finset.sum_apply, Finset.sum_image fun _ _ _ _ h ↦ Quotient.out_injective h]
  -- Only the class of `x` can contribute, through its representative.
  have hx : x ∈ {y | (↑t⁻¹ : FiniteAdeleRing R K) •
      (y - (x : (n → FiniteAdeleRing R K) ⧸ H).out) ∈ integralBox n e} :=
    hmk.2 (QuotientAddGroup.out_eq' _).symm
  refine Eq.symm <| (Finset.sum_eq_single (x : (n → FiniteAdeleRing R K) ⧸ H) ?_ ?_).trans ?_
  · intro q _ hq
    refine indicator_of_notMem (fun h ↦ hq ?_) _
    exact (QuotientAddGroup.out_eq' q).symm.trans (hmk.1 h).symm
  · intro hxA
    rw [indicator_of_mem hx]
    simpa using hxA
  · rw [indicator_of_mem hx]
    exact hinv (QuotientAddGroup.out_eq' _)

end IsSchwartzBruhatAbove

end IsDedekindDomain.FiniteAdeleRing
