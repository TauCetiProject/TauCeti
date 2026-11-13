/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.GaloisSet.Basic

/-!
# Disjoint unions and invariant restrictions of labelled Galois sets

Two labelled Galois sets `ρ₁ : TauCeti.GaloisSet K m` and `ρ₂ : TauCeti.GaloisSet K l`, together
with a bijection `Fin m ⊕ Fin l ≃ Fin n`, assemble into a labelled Galois set `GaloisSet.sum` of
size `n`: its kernel contains the intersection of the two open kernels and is therefore open.

In the opposite direction, a Galois-invariant predicate on `Fin n` and a labelling of its support by
`Fin m` cut out a restricted Galois set `GaloisSet.restrict` of size `m`. Restricting to a single
orbit yields a transitive Galois set (`GaloisSet.isTransitive_restrict_of_orbit`).

Combining the two operations along the decomposition `Equiv.sumCompl` of `Fin n` into an orbit `s`
containing a chosen base label `i₀` and its complement gives `GaloisSet.orbitSumEquiv`: the
labelled Galois sets of size `n` in which `i₀` has orbit `s` are in bijection with pairs of a
transitive Galois set on `Fin m` and an arbitrary Galois set on `Fin l`.

Only a field structure on `K` is needed here.

## Main definitions and results

* `TauCeti.GaloisSet.sum`: disjoint union of two labelled Galois sets along `Fin m ⊕ Fin l ≃ Fin n`.
* `TauCeti.GaloisSet.orbit_sum_inl_of_isTransitive`, `TauCeti.GaloisSet.stabilizer_sum_inl`, and
  `TauCeti.GaloisSet.stabilizer_sum_inr`: orbits and point stabilizers in a disjoint union.
* `TauCeti.GaloisSet.restrict`: restriction of a labelled Galois set to an invariant subset.
* `TauCeti.GaloisSet.isTransitive_restrict_of_orbit`: restricting to a single orbit produces a
  transitive Galois set.
* `TauCeti.GaloisSet.orbitSumEquiv`: decomposition of Galois sets with a prescribed orbit at `i₀`
  into a transitive Galois set and a complementary Galois set.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, §2.
* K. S. Kedlaya, *Mass formulas for local Galois representations*, IMRN **2007**, rnm021.
-/

public section

noncomputable section

namespace TauCeti.GaloisSet

universe u

variable {K : Type u} [Field K] {m l n : ℕ}

/-! ### Disjoint unions of Galois sets -/

/-- The disjoint union of two labelled Galois sets along a bijection `Fin m ⊕ Fin l ≃ Fin n`,
acting through `ρ₁` on the left summand and `ρ₂` on the right summand. -/
def sum (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K l) (e : Fin m ⊕ Fin l ≃ Fin n) :
    GaloisSet K n :=
  ⟨e.permCongrHom.toMonoidHom.comp
      ((Equiv.Perm.sumCongrHom (Fin m) (Fin l)).comp (ρ₁.val.prod ρ₂.val)), by
    rw [MonoidHom.ker_comp_of_injective _ _ e.permCongrHom.injective,
      MonoidHom.ker_comp_of_injective _ _ Equiv.Perm.sumCongrHom_injective,
      MonoidHom.ker_prod]
    exact ρ₁.property.inter ρ₂.property⟩

/-- On a label coming from the left summand, `sum` acts through `ρ₁`. -/
@[simp]
theorem sum_val_apply_inl (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K l)
    (e : Fin m ⊕ Fin l ≃ Fin n) (σ : Gal(SeparableClosure K/K)) (i : Fin m) :
    (sum ρ₁ ρ₂ e).val σ (e (Sum.inl i)) = e (Sum.inl (ρ₁.val σ i)) := by
  simp [sum]

/-- On a label coming from the right summand, `sum` acts through `ρ₂`. -/
@[simp]
theorem sum_val_apply_inr (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K l)
    (e : Fin m ⊕ Fin l ≃ Fin n) (σ : Gal(SeparableClosure K/K)) (j : Fin l) :
    (sum ρ₁ ρ₂ e).val σ (e (Sum.inr j)) = e (Sum.inr (ρ₂.val σ j)) := by
  simp [sum]

/-- If `ρ₁` is transitive, the orbit of any left-summand label `e (Sum.inl i)` in `sum ρ₁ ρ₂ e` is
precisely the image of the left summand. -/
theorem orbit_sum_inl_of_isTransitive {ρ₁ : GaloisSet K m} (h₁ : ρ₁.IsTransitive)
    (ρ₂ : GaloisSet K l) (e : Fin m ⊕ Fin l ≃ Fin n) (i : Fin m) :
    letI := (sum ρ₁ ρ₂ e).mulAction
    MulAction.orbit Gal(SeparableClosure K/K) (e (Sum.inl i)) =
      Set.range (fun j ↦ e (Sum.inl j)) := by
  let := (sum ρ₁ ρ₂ e).mulAction
  ext k
  simp only [MulAction.mem_orbit_iff, smul_def, Set.mem_range]
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨ρ₁.val σ i, (sum_val_apply_inl ρ₁ ρ₂ e σ i).symm⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨σ, hσ⟩ := (ρ₁.isTransitive_iff.1 h₁) i j
    exact ⟨σ, by rw [sum_val_apply_inl, hσ]⟩

/-- The stabilizer in `sum ρ₁ ρ₂ e` of a left-summand label `e (Sum.inl i)` is its stabilizer in
`ρ₁`. -/
@[simp]
theorem stabilizer_sum_inl (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K l)
    (e : Fin m ⊕ Fin l ≃ Fin n) (i : Fin m) :
    (letI := (sum ρ₁ ρ₂ e).mulAction;
    MulAction.stabilizer Gal(SeparableClosure K/K) (e (Sum.inl i))) =
      (letI := ρ₁.mulAction;
      MulAction.stabilizer Gal(SeparableClosure K/K) i) := by
  let := (sum ρ₁ ρ₂ e).mulAction
  let := ρ₁.mulAction
  ext σ
  simp [MulAction.mem_stabilizer_iff, e.injective.eq_iff]

/-- The stabilizer in `sum ρ₁ ρ₂ e` of a right-summand label `e (Sum.inr j)` is its stabilizer in
`ρ₂`. -/
@[simp]
theorem stabilizer_sum_inr (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K l)
    (e : Fin m ⊕ Fin l ≃ Fin n) (j : Fin l) :
    (letI := (sum ρ₁ ρ₂ e).mulAction;
    MulAction.stabilizer Gal(SeparableClosure K/K) (e (Sum.inr j))) =
      (letI := ρ₂.mulAction;
      MulAction.stabilizer Gal(SeparableClosure K/K) j) := by
  let := (sum ρ₁ ρ₂ e).mulAction
  let := ρ₂.mulAction
  ext σ
  simp [MulAction.mem_stabilizer_iff, e.injective.eq_iff]

/-! ### Restriction to an invariant subset -/

/-- Restrict a labelled Galois set to an invariant predicate `p` on `Fin n`, transported to `Fin m`
along a bijection `e`. -/
def restrict (ρ : GaloisSet K n) {p : Fin n → Prop}
    (hp : ∀ σ i, p (ρ.val σ i) ↔ p i) (e : Fin m ≃ {i : Fin n // p i}) : GaloisSet K m :=
  ⟨e.symm.permCongrHom.toMonoidHom.comp
      { toFun := fun σ ↦ (ρ.val σ).subtypePerm (hp σ)
        map_one' := by
          ext x
          simp
        map_mul' := fun σ τ ↦ by
          ext x
          simp [Equiv.Perm.subtypePerm_apply, Equiv.Perm.mul_def] }, by
    refine Subgroup.isOpen_mono (H₁ := ρ.val.ker) (fun σ hσ ↦ ?_) ρ.property
    rw [MonoidHom.mem_ker] at hσ ⊢
    ext i
    simp [hσ]⟩

/-- The permutation of a restricted Galois set transports the subtype permutation along `e`. -/
@[simp]
theorem restrict_val_apply (ρ : GaloisSet K n) {p : Fin n → Prop}
    (hp : ∀ σ i, p (ρ.val σ i) ↔ p i) (e : Fin m ≃ {i : Fin n // p i})
    (σ : Gal(SeparableClosure K/K)) (i : Fin m) :
    (ρ.restrict hp e).val σ i = e.symm ⟨ρ.val σ (e i).1, (hp σ (e i).1).2 (e i).2⟩ := by
  simp [restrict]

/-- Embedding a restricted Galois set back into `Fin n` along `e` intertwines the actions. -/
theorem coe_apply_restrict_val_apply (ρ : GaloisSet K n) {p : Fin n → Prop}
    (hp : ∀ σ i, p (ρ.val σ i) ↔ p i) (e : Fin m ≃ {i : Fin n // p i})
    (σ : Gal(SeparableClosure K/K)) (i : Fin m) :
    (e ((ρ.restrict hp e).val σ i) : Fin n) = ρ.val σ (e i) := by
  simp

/-- Restricting a labelled Galois set to a single orbit yields a transitive Galois set. -/
theorem isTransitive_restrict_of_orbit (ρ : GaloisSet K n) {i₀ : Fin n} {s : Set (Fin n)}
    (hs : letI := ρ.mulAction; MulAction.orbit Gal(SeparableClosure K/K) i₀ = s)
    (hp : ∀ σ j, ρ.val σ j ∈ s ↔ j ∈ s) (e : Fin m ≃ s) :
    (ρ.restrict hp e).IsTransitive := by
  let := ρ.mulAction
  rw [isTransitive_iff]
  intro a b
  have ha : (e a : Fin n) ∈ MulAction.orbit Gal(SeparableClosure K/K) i₀ := hs ▸ (e a).2
  have hb : (e b : Fin n) ∈ MulAction.orbit Gal(SeparableClosure K/K) i₀ := hs ▸ (e b).2
  obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.1
    (MulAction.mem_orbit_trans hb (MulAction.mem_orbit_symm.1 ha))
  refine ⟨σ, e.injective (Subtype.ext ?_)⟩
  rw [coe_apply_restrict_val_apply, ← smul_def, hσ]

/-! ### Decomposition along a chosen orbit -/

/-- Decompose the labelled Galois sets of size `n` in which a base label `i₀` has orbit `s` into a
transitive Galois set on `Fin m` (labelling `s` via `e₁`) and a Galois set on `Fin l` (labelling the
complement via `e₂`). -/
def orbitSumEquiv {i₀ : Fin n} {s : Set (Fin n)} [DecidablePred (· ∈ s)]
    (hi₀ : i₀ ∈ s) (e₁ : Fin m ≃ s) (e₂ : Fin l ≃ {j : Fin n // j ∉ s}) :
    {ρ₁ : GaloisSet K m // ρ₁.IsTransitive} × GaloisSet K l ≃
      {ρ : GaloisSet K n //
        letI := ρ.mulAction
        MulAction.orbit Gal(SeparableClosure K/K) i₀ = s} where
  toFun p :=
    let e := (Equiv.sumCongr e₁ e₂).trans (Equiv.sumCompl (· ∈ s))
    ⟨sum p.1.1 p.2 e, by
      have ha₀ : e (Sum.inl (e₁.symm ⟨i₀, hi₀⟩)) = i₀ := by simp [e]
      have horb := orbit_sum_inl_of_isTransitive p.1.2 p.2 e (e₁.symm ⟨i₀, hi₀⟩)
      rw [ha₀] at horb
      refine horb.trans ?_
      ext j
      simp only [Set.mem_range, e, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
        Equiv.sumCompl_apply_inl]
      exact ⟨by rintro ⟨a, rfl⟩; exact (e₁ a).2, fun hj ↦ ⟨e₁.symm ⟨j, hj⟩, by simp⟩⟩⟩
  invFun := fun ⟨ρ, horb⟩ ↦
    have hp₁ : ∀ σ j, ρ.val σ j ∈ s ↔ j ∈ s := by
      let := ρ.mulAction
      intro σ j
      rw [← horb, ← smul_def, ← MulAction.orbit_eq_iff, MulAction.orbit_smul,
        MulAction.orbit_eq_iff]
    have hp₂ : ∀ σ j, ρ.val σ j ∉ s ↔ j ∉ s := fun σ j ↦ not_congr (hp₁ σ j)
    (⟨ρ.restrict hp₁ e₁, isTransitive_restrict_of_orbit ρ horb hp₁ e₁⟩, ρ.restrict hp₂ e₂)
  left_inv := by
    rintro ⟨⟨ρ₁, h₁⟩, ρ₂⟩
    set e := (Equiv.sumCongr e₁ e₂).trans (Equiv.sumCompl (· ∈ s))
    refine Prod.ext (Subtype.ext (ext fun σ a ↦ ?_)) (ext fun σ b ↦ ?_)
    · apply e₁.injective
      apply Subtype.ext
      rw [coe_apply_restrict_val_apply]
      have ha : ((e₁ a : s) : Fin n) = e (Sum.inl a) := by simp [e]
      have ha' : ((e₁ (ρ₁.val σ a) : s) : Fin n) = e (Sum.inl (ρ₁.val σ a)) := by simp [e]
      rw [ha, sum_val_apply_inl, ← ha']
    · apply e₂.injective
      apply Subtype.ext
      rw [coe_apply_restrict_val_apply]
      have hb : ((e₂ b : {j : Fin n // j ∉ s}) : Fin n) = e (Sum.inr b) := by simp [e]
      have hb' : ((e₂ (ρ₂.val σ b) : {j : Fin n // j ∉ s}) : Fin n) =
          e (Sum.inr (ρ₂.val σ b)) := by simp [e]
      rw [hb, sum_val_apply_inr, ← hb']
  right_inv := by
    rintro ⟨ρ, horb⟩
    set e := (Equiv.sumCongr e₁ e₂).trans (Equiv.sumCompl (· ∈ s))
    refine Subtype.ext (ext fun σ k ↦ ?_)
    obtain ⟨a | b, rfl⟩ := e.surjective k
    · rw [sum_val_apply_inl]
      simp [e]
    · rw [sum_val_apply_inr]
      simp [e]

/-- The forward direction of `orbitSumEquiv` is `GaloisSet.sum` along the induced bijection
`Fin m ⊕ Fin l ≃ Fin n`. -/
@[simp]
theorem coe_orbitSumEquiv_apply {i₀ : Fin n} {s : Set (Fin n)} [DecidablePred (· ∈ s)]
    (hi₀ : i₀ ∈ s) (e₁ : Fin m ≃ s) (e₂ : Fin l ≃ {j : Fin n // j ∉ s})
    (p : {ρ₁ : GaloisSet K m // ρ₁.IsTransitive} × GaloisSet K l) :
    (orbitSumEquiv hi₀ e₁ e₂ p : GaloisSet K n) =
      sum p.1.1 p.2 ((Equiv.sumCongr e₁ e₂).trans (Equiv.sumCompl (· ∈ s))) :=
  (rfl)

end TauCeti.GaloisSet
