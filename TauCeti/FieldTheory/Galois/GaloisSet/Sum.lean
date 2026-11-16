/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Sum
public import TauCeti.FieldTheory.Galois.GaloisSet.Basic
import Mathlib.GroupTheory.Perm.Finite

/-!
# Disjoint unions and orbit splitting of labelled Galois sets

Given a bijection `e : Fin n₁ ⊕ Fin n₂ ≃ Fin n`, two labelled Galois sets of sizes `n₁` and `n₂`
combine into a labelled Galois set `TauCeti.GaloisSet.sumCongr e ρ₁ ρ₂` of size `n` whose action is
transported from the sum action along `e`.

Conversely, a labelled Galois set of size `n` that preserves the left block `e '' range Sum.inl`
splits uniquely into a pair of labelled Galois sets on the two blocks
(`TauCeti.GaloisSet.sumCongrEquiv`). When `0 < n₁`, requiring that the left block be a single orbit
of the Galois set corresponds precisely to requiring that the left factor be transitive
(`TauCeti.GaloisSet.orbitSplitEquiv`). This decomposition is the algebraic core of splitting off
one orbit at a time in mass formulas for Galois sets.

## Main definitions and results

* `TauCeti.GaloisSet.sumCongr`: the disjoint union of two labelled Galois sets along a bijection
  `Fin n₁ ⊕ Fin n₂ ≃ Fin n`.
* `TauCeti.GaloisSet.sumCongrEquiv`: labelled Galois sets preserving a prescribed block correspond
  to pairs of labelled Galois sets on the block and its complement.
* `TauCeti.GaloisSet.orbitSplitEquiv`: labelled Galois sets together with an orbit occupying a
  prescribed nonempty block correspond to pairs of a transitive Galois set on the block and an
  arbitrary Galois set on its complement.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, §2.
* K. S. Kedlaya, *Mass formulas for local Galois representations*, IMRN **2007**, rnm021.
-/

public section

noncomputable section

namespace TauCeti.GaloisSet

universe u

variable {K : Type u} [Field K] {n₁ n₂ n : ℕ}

/-- The disjoint union of two labelled Galois sets, transported to `Fin n` along a bijection
`e : Fin n₁ ⊕ Fin n₂ ≃ Fin n`. Its kernel is the intersection of the two kernels, hence open. -/
def sumCongr (e : Fin n₁ ⊕ Fin n₂ ≃ Fin n) (ρ₁ : GaloisSet K n₁) (ρ₂ : GaloisSet K n₂) :
    GaloisSet K n :=
  ⟨e.permCongrHom.toMonoidHom.comp
      ((Equiv.Perm.sumCongrHom (Fin n₁) (Fin n₂)).comp (ρ₁.val.prod ρ₂.val)), by
    rw [MonoidHom.ker_comp_of_injective _ _ e.permCongrHom.injective,
      MonoidHom.ker_comp_of_injective _ _ Equiv.Perm.sumCongrHom_injective,
      MonoidHom.ker_prod, Subgroup.coe_inf]
    exact ρ₁.property.inter ρ₂.property⟩

/-- On the left summand, `sumCongr e ρ₁ ρ₂` acts through `ρ₁`. -/
@[simp]
theorem sumCongr_val_apply_inl (e : Fin n₁ ⊕ Fin n₂ ≃ Fin n) (ρ₁ : GaloisSet K n₁)
    (ρ₂ : GaloisSet K n₂) (σ : Gal(SeparableClosure K/K)) (i : Fin n₁) :
    (sumCongr e ρ₁ ρ₂).val σ (e (Sum.inl i)) = e (Sum.inl (ρ₁.val σ i)) := by
  simp [sumCongr]

/-- On the right summand, `sumCongr e ρ₁ ρ₂` acts through `ρ₂`. -/
@[simp]
theorem sumCongr_val_apply_inr (e : Fin n₁ ⊕ Fin n₂ ≃ Fin n) (ρ₁ : GaloisSet K n₁)
    (ρ₂ : GaloisSet K n₂) (σ : Gal(SeparableClosure K/K)) (j : Fin n₂) :
    (sumCongr e ρ₁ ρ₂).val σ (e (Sum.inr j)) = e (Sum.inr (ρ₂.val σ j)) := by
  simp [sumCongr]

/-- The bijection `e : Fin n₁ ⊕ Fin n₂ ≃ Fin n` is equivariant from the sum action of `ρ₁` and `ρ₂`
to the action of `sumCongr e ρ₁ ρ₂`. -/
theorem sumCongr_map_smul (e : Fin n₁ ⊕ Fin n₂ ≃ Fin n) (ρ₁ : GaloisSet K n₁)
    (ρ₂ : GaloisSet K n₂) (σ : Gal(SeparableClosure K/K)) (x : Fin n₁ ⊕ Fin n₂) :
    letI := ρ₁.mulAction
    letI := ρ₂.mulAction
    letI := (sumCongr e ρ₁ ρ₂).mulAction
    e (σ • x) = σ • e x := by
  let := ρ₁.mulAction
  let := ρ₂.mulAction
  let := (sumCongr e ρ₁ ρ₂).mulAction
  cases x with
  | inl i => exact (sumCongr_val_apply_inl e ρ₁ ρ₂ σ i).symm
  | inr j => exact (sumCongr_val_apply_inr e ρ₁ ρ₂ σ j).symm

/-- Two disjoint unions along the same bijection agree exactly when both factors agree. -/
@[simp]
theorem sumCongr_eq_iff (e : Fin n₁ ⊕ Fin n₂ ≃ Fin n) (ρ₁ τ₁ : GaloisSet K n₁)
    (ρ₂ τ₂ : GaloisSet K n₂) :
    sumCongr e ρ₁ ρ₂ = sumCongr e τ₁ τ₂ ↔ ρ₁ = τ₁ ∧ ρ₂ = τ₂ := by
  refine ⟨fun h ↦ ⟨ext fun σ i ↦ ?_, ext fun σ j ↦ ?_⟩, ?_⟩
  · have hi := congrArg (fun μ : GaloisSet K n ↦ μ.val σ (e (Sum.inl i))) h
    simpa only [sumCongr_val_apply_inl, EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq] using hi
  · have hj := congrArg (fun μ : GaloisSet K n ↦ μ.val σ (e (Sum.inr j))) h
    simpa only [sumCongr_val_apply_inr, EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq] using hj
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem sumCongr_surj_of_mapsTo_inl (e : Fin n₁ ⊕ Fin n₂ ≃ Fin n) (ρ : GaloisSet K n)
    (hρ : ∀ (σ : Gal(SeparableClosure K/K)) (i : Fin n₁),
      ∃ j : Fin n₁, ρ.val σ (e (Sum.inl i)) = e (Sum.inl j)) :
    ∃ p : GaloisSet K n₁ × GaloisSet K n₂, sumCongr e p.1 p.2 = ρ := by
  let π : Gal(SeparableClosure K/K) →* Equiv.Perm (Fin n₁ ⊕ Fin n₂) :=
    e.symm.permCongrHom.toMonoidHom.comp ρ.val
  have hrange : ∀ σ, π σ ∈ (Equiv.Perm.sumCongrHom (Fin n₁) (Fin n₂)).range := fun σ ↦ by
    apply Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl
    rintro _ ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hρ σ i
    exact ⟨j, by simp [π, hj]⟩
  let ψ : Gal(SeparableClosure K/K) →* Equiv.Perm (Fin n₁) × Equiv.Perm (Fin n₂) :=
    (MonoidHom.ofInjective Equiv.Perm.sumCongrHom_injective).symm.toMonoidHom.comp
      (π.codRestrict _ hrange)
  have hψ : ∀ σ, Equiv.Perm.sumCongrHom (Fin n₁) (Fin n₂) (ψ σ) = π σ := fun σ ↦
    congrArg Subtype.val ((MonoidHom.ofInjective
      (f := Equiv.Perm.sumCongrHom (Fin n₁) (Fin n₂))
      Equiv.Perm.sumCongrHom_injective).apply_symm_apply ⟨π σ, hrange σ⟩)
  have hker : ρ.val.ker ≤ ψ.ker := fun σ hσ ↦ by
    rw [MonoidHom.mem_ker] at hσ ⊢
    apply Equiv.Perm.sumCongrHom_injective
    rw [hψ, map_one, MonoidHom.comp_apply, hσ, map_one]
  let ρ₁ : GaloisSet K n₁ :=
    ⟨(MonoidHom.fst _ _).comp ψ,
      Subgroup.isOpen_mono (hker.trans fun σ hσ ↦ by simp [MonoidHom.mem_ker.mp hσ]) ρ.property⟩
  let ρ₂ : GaloisSet K n₂ :=
    ⟨(MonoidHom.snd _ _).comp ψ,
      Subgroup.isOpen_mono (hker.trans fun σ hσ ↦ by simp [MonoidHom.mem_ker.mp hσ]) ρ.property⟩
  refine ⟨(ρ₁, ρ₂), ext fun σ k ↦ ?_⟩
  obtain ⟨x, rfl⟩ := e.surjective k
  have hx := congrArg (fun f : Equiv.Perm (Fin n₁ ⊕ Fin n₂) ↦ e (f x)) (hψ σ)
  cases x with
  | inl i => simpa [π, ρ₁] using hx
  | inr j => simpa [π, ρ₂] using hx

/-- **Block decomposition of labelled Galois sets**: the labelled Galois sets of size `n` that
preserve the block `e '' range Sum.inl` correspond to pairs of labelled Galois sets on the two
blocks. -/
def sumCongrEquiv (e : Fin n₁ ⊕ Fin n₂ ≃ Fin n) :
    GaloisSet K n₁ × GaloisSet K n₂ ≃
      {ρ : GaloisSet K n // ∀ (σ : Gal(SeparableClosure K/K)) (i : Fin n₁),
        ∃ j : Fin n₁, ρ.val σ (e (Sum.inl i)) = e (Sum.inl j)} :=
  Equiv.ofBijective
    (fun p ↦ ⟨sumCongr e p.1 p.2, fun σ i ↦ ⟨p.1.val σ i, sumCongr_val_apply_inl e p.1 p.2 σ i⟩⟩)
    ⟨fun p q h ↦ Prod.ext_iff.2 ((sumCongr_eq_iff e p.1 q.1 p.2 q.2).1 (congrArg Subtype.val h)),
      fun ⟨ρ, hρ⟩ ↦
        let ⟨p, hp⟩ := sumCongr_surj_of_mapsTo_inl e ρ hρ
        ⟨p, Subtype.ext hp⟩⟩

/-- `sumCongrEquiv` sends `(ρ₁, ρ₂)` to `sumCongr e ρ₁ ρ₂`. -/
@[simp]
theorem sumCongrEquiv_apply (e : Fin n₁ ⊕ Fin n₂ ≃ Fin n) (p : GaloisSet K n₁ × GaloisSet K n₂) :
    (sumCongrEquiv e p).1 = sumCongr e p.1 p.2 :=
  (rfl)

/-- The inverse of `sumCongrEquiv` recovers `(ρ₁, ρ₂)` from `sumCongr e ρ₁ ρ₂`. -/
@[simp]
theorem sumCongrEquiv_symm_sumCongr (e : Fin n₁ ⊕ Fin n₂ ≃ Fin n) (ρ₁ : GaloisSet K n₁)
    (ρ₂ : GaloisSet K n₂)
    (h : ∀ (σ : Gal(SeparableClosure K/K)) (i : Fin n₁),
      ∃ j : Fin n₁, (sumCongr e ρ₁ ρ₂).val σ (e (Sum.inl i)) = e (Sum.inl j)) :
    (sumCongrEquiv e).symm ⟨sumCongr e ρ₁ ρ₂, h⟩ = (ρ₁, ρ₂) :=
  (sumCongrEquiv e).symm_apply_apply (ρ₁, ρ₂)

/-- Recombining the factors produced by `(sumCongrEquiv e).symm` recovers the original Galois
set. -/
@[simp]
theorem sumCongr_sumCongrEquiv_symm (e : Fin n₁ ⊕ Fin n₂ ≃ Fin n)
    (ρ : {ρ : GaloisSet K n // ∀ (σ : Gal(SeparableClosure K/K)) (i : Fin n₁),
      ∃ j : Fin n₁, ρ.val σ (e (Sum.inl i)) = e (Sum.inl j)}) :
    sumCongr e ((sumCongrEquiv e).symm ρ).1 ((sumCongrEquiv e).symm ρ).2 = ρ.1 :=
  congrArg Subtype.val ((sumCongrEquiv e).apply_symm_apply ρ)

/-- When `ρ₁` is transitive, the orbit of `e (Sum.inl j₀)` in `sumCongr e ρ₁ ρ₂` is precisely the
left block `e '' range Sum.inl`. -/
theorem mk_eq_mk_sumCongr_inl_iff (e : Fin n₁ ⊕ Fin n₂ ≃ Fin n) (ρ₁ : GaloisSet K n₁)
    (hρ₁ : ρ₁.IsTransitive) (ρ₂ : GaloisSet K n₂) (j₀ : Fin n₁) (i : Fin n) :
    letI := (sumCongr e ρ₁ ρ₂).mulAction
    (Quotient.mk'' i : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) =
      Quotient.mk'' (e (Sum.inl j₀)) ↔ ∃ j : Fin n₁, e (Sum.inl j) = i := by
  let := (sumCongr e ρ₁ ρ₂).mulAction
  rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨ρ₁.val σ j₀, (sumCongr_val_apply_inl e ρ₁ ρ₂ σ j₀).symm⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨σ, hσ⟩ := (isTransitive_iff ρ₁).1 hρ₁ j₀ j
    exact ⟨σ, by rw [smul_def, sumCongr_val_apply_inl, hσ]⟩

private theorem orbitSplit_surj (e : Fin n₁ ⊕ Fin n₂ ≃ Fin n)
    (ρ : GaloisSet K n)
    (ω : letI := ρ.mulAction; MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
    (hω : letI := ρ.mulAction
      ∀ i : Fin n,
        (Quotient.mk'' i : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = ω ↔
        ∃ j : Fin n₁, e (Sum.inl j) = i) :
    ∃ (ρ₁ : GaloisSet K n₁) (ρ₂ : GaloisSet K n₂), ρ₁.IsTransitive ∧ sumCongr e ρ₁ ρ₂ = ρ := by
  have hinv : ∀ (σ : Gal(SeparableClosure K/K)) (i : Fin n₁),
      ∃ j : Fin n₁, ρ.val σ (e (Sum.inl i)) = e (Sum.inl j) := by
    intro σ i
    let := ρ.mulAction
    have hi : (Quotient.mk'' (e (Sum.inl i)) :
        MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = ω :=
      (hω (e (Sum.inl i))).2 ⟨i, rfl⟩
    have hσi : (Quotient.mk'' (ρ.val σ (e (Sum.inl i))) :
        MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = ω :=
      (Quotient.sound' (MulAction.orbitRel_apply.2 ⟨σ, rfl⟩)).trans hi
    obtain ⟨j, hj⟩ := (hω (ρ.val σ (e (Sum.inl i)))).1 hσi
    exact ⟨j, hj.symm⟩
  obtain ⟨⟨ρ₁, ρ₂⟩, hsum⟩ := sumCongr_surj_of_mapsTo_inl e ρ hinv
  have htrans : ρ₁.IsTransitive := by
    rw [isTransitive_iff]
    intro j₁ j₂
    let := ρ.mulAction
    have hq : (Quotient.mk'' (e (Sum.inl j₂)) :
        MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) =
        Quotient.mk'' (e (Sum.inl j₁)) :=
      ((hω (e (Sum.inl j₂))).2 ⟨j₂, rfl⟩).trans ((hω (e (Sum.inl j₁))).2 ⟨j₁, rfl⟩).symm
    obtain ⟨σ, hσ⟩ :=
      MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 (Quotient.exact' hq))
    refine ⟨σ, ?_⟩
    rw [smul_def, ← hsum, sumCongr_val_apply_inl] at hσ
    exact Sum.inl.inj (e.injective hσ)
  exact ⟨ρ₁, ρ₂, htrans, hsum⟩

/-- **Splitting off a single orbit**: for a bijection `e : Fin n₁ ⊕ Fin n₂ ≃ Fin n` with `0 < n₁`,
a labelled Galois set of size `n` together with an orbit occupying the block `e '' range Sum.inl`
corresponds bijectively to a transitive labelled Galois set on `Fin n₁` and an arbitrary labelled
Galois set on `Fin n₂`. -/
def orbitSplitEquiv (e : Fin n₁ ⊕ Fin n₂ ≃ Fin n) (hn₁ : 0 < n₁) :
    {ρ₁ : GaloisSet K n₁ // ρ₁.IsTransitive} × GaloisSet K n₂ ≃
      {p : Σ ρ : GaloisSet K n,
          letI := ρ.mulAction
          MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n) //
        letI := p.1.mulAction
        ∀ i : Fin n,
          (Quotient.mk'' i :
            MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = p.2 ↔
          ∃ j : Fin n₁, e (Sum.inl j) = i} :=
  Equiv.ofBijective
    (fun p ↦
      ⟨⟨sumCongr e p.1.1 p.2,
          letI := (sumCongr e p.1.1 p.2).mulAction
          Quotient.mk'' (e (Sum.inl ⟨0, hn₁⟩))⟩,
        mk_eq_mk_sumCongr_inl_iff e p.1.1 p.1.2 p.2 ⟨0, hn₁⟩⟩)
    ⟨by
      rintro ⟨⟨ρ₁, hρ₁⟩, ρ₂⟩ ⟨⟨τ₁, hτ₁⟩, τ₂⟩ h
      have h1 : sumCongr e ρ₁ ρ₂ = sumCongr e τ₁ τ₂ := congrArg (fun q ↦ q.1.1) h
      obtain ⟨rfl, rfl⟩ := (sumCongr_eq_iff e ρ₁ τ₁ ρ₂ τ₂).1 h1
      rfl, by
      rintro ⟨⟨ρ, ω⟩, hω⟩
      obtain ⟨ρ₁, ρ₂, htrans, hsum⟩ := orbitSplit_surj e ρ ω hω
      refine ⟨(⟨ρ₁, htrans⟩, ρ₂), Subtype.ext ?_⟩
      subst hsum
      have hω' : (letI := (sumCongr e ρ₁ ρ₂).mulAction
          (Quotient.mk'' (e (Sum.inl ⟨0, hn₁⟩)) :
            MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))) = ω :=
        (hω (e (Sum.inl ⟨0, hn₁⟩))).2 ⟨⟨0, hn₁⟩, rfl⟩
      exact Sigma.ext rfl (heq_of_eq hω')⟩

/-- The Galois-set component of `orbitSplitEquiv` is `sumCongr e ρ₁ ρ₂`. -/
@[simp]
theorem orbitSplitEquiv_apply_fst (e : Fin n₁ ⊕ Fin n₂ ≃ Fin n) (hn₁ : 0 < n₁)
    (p : {ρ₁ : GaloisSet K n₁ // ρ₁.IsTransitive} × GaloisSet K n₂) :
    (orbitSplitEquiv e hn₁ p).1.1 = sumCongr e p.1.1 p.2 :=
  (rfl)

/-- The orbit component of `orbitSplitEquiv` is heterogeneously equal to the orbit of
`e (Sum.inl ⟨0, hn₁⟩)` in `sumCongr e p.1.1 p.2`. -/
theorem orbitSplitEquiv_apply_snd (e : Fin n₁ ⊕ Fin n₂ ≃ Fin n) (hn₁ : 0 < n₁)
    (p : {ρ₁ : GaloisSet K n₁ // ρ₁.IsTransitive} × GaloisSet K n₂) :
    HEq (orbitSplitEquiv e hn₁ p).1.2
      (letI := (sumCongr e p.1.1 p.2).mulAction
      (Quotient.mk'' (e (Sum.inl ⟨0, hn₁⟩)) :
        MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))) :=
  HEq.rfl

/-- Recombining the factors produced by `(orbitSplitEquiv e hn₁).symm` recovers the original Galois
set. -/
@[simp]
theorem sumCongr_orbitSplitEquiv_symm (e : Fin n₁ ⊕ Fin n₂ ≃ Fin n) (hn₁ : 0 < n₁)
    (p : {p : Σ ρ : GaloisSet K n,
          letI := ρ.mulAction
          MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n) //
        letI := p.1.mulAction
        ∀ i : Fin n,
          (Quotient.mk'' i :
            MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = p.2 ↔
          ∃ j : Fin n₁, e (Sum.inl j) = i}) :
    sumCongr e ((orbitSplitEquiv e hn₁).symm p).1.1 ((orbitSplitEquiv e hn₁).symm p).2 = p.1.1 :=
  congrArg (fun q ↦ q.1.1) ((orbitSplitEquiv e hn₁).apply_symm_apply p)

end TauCeti.GaloisSet
