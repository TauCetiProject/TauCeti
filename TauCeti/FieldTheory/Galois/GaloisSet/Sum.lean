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
`Fin m` cut out a restricted Galois set `GaloisSet.restrict` of size `m`. Restricting to an
invariant predicate is transitive precisely when the ambient action is transitive on that predicate
(`GaloisSet.isTransitive_restrict_iff`), and in particular restricting to a single orbit yields a
transitive Galois set (`GaloisSet.isTransitive_restrict_of_orbit`).

Combining the two operations along `Equiv.sumCompl` gives `GaloisSet.sumComplEquiv`, identifying
the labelled Galois sets preserving a decidable predicate `p` with pairs of Galois sets on its
support and complement. Specializing to `p := (· ∈ s)` at a chosen base label `i₀ ∈ s` and
restricting the first factor to transitive actions gives `GaloisSet.orbitSumEquiv`.

Only a field structure on `K` is needed here.

## Main definitions and results

* `TauCeti.GaloisSet.sum`: disjoint union of two labelled Galois sets along `Fin m ⊕ Fin l ≃ Fin n`.
* `TauCeti.GaloisSet.orbit_sum_inl`, `TauCeti.GaloisSet.orbit_sum_inr`,
  `TauCeti.GaloisSet.stabilizer_sum_inl`, and `TauCeti.GaloisSet.stabilizer_sum_inr`: orbits and
  point stabilizers in a disjoint union.
* `TauCeti.GaloisSet.restrict`: restriction of a labelled Galois set to an invariant subset, with
  `TauCeti.GaloisSet.stabilizer_restrict`, `TauCeti.GaloisSet.orbit_restrict`, and
  `TauCeti.GaloisSet.isTransitive_restrict_iff`.
* `TauCeti.GaloisSet.sumComplEquiv`: decomposition of Galois sets preserving a decidable predicate
  into Galois sets on the predicate and its complement.
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

/-- The orbit in `sum ρ₁ ρ₂ e` of a left-summand label `e (Sum.inl i)` is the image under
`e ∘ Sum.inl` of its orbit in `ρ₁`. -/
@[simp]
theorem orbit_sum_inl (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K l)
    (e : Fin m ⊕ Fin l ≃ Fin n) (i : Fin m) :
    (letI := (sum ρ₁ ρ₂ e).mulAction
    MulAction.orbit Gal(SeparableClosure K/K) (e (Sum.inl i))) =
      (fun j ↦ e (Sum.inl j)) ''
        (letI := ρ₁.mulAction; MulAction.orbit Gal(SeparableClosure K/K) i) := by
  let := (sum ρ₁ ρ₂ e).mulAction
  let := ρ₁.mulAction
  ext k
  simp only [MulAction.mem_orbit_iff, smul_def, Set.mem_image]
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨ρ₁.val σ i, ⟨σ, rfl⟩, (sum_val_apply_inl ρ₁ ρ₂ e σ i).symm⟩
  · rintro ⟨j, ⟨σ, rfl⟩, rfl⟩
    exact ⟨σ, sum_val_apply_inl ρ₁ ρ₂ e σ i⟩

/-- The orbit in `sum ρ₁ ρ₂ e` of a right-summand label `e (Sum.inr j)` is the image under
`e ∘ Sum.inr` of its orbit in `ρ₂`. -/
@[simp]
theorem orbit_sum_inr (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K l)
    (e : Fin m ⊕ Fin l ≃ Fin n) (j : Fin l) :
    (letI := (sum ρ₁ ρ₂ e).mulAction
    MulAction.orbit Gal(SeparableClosure K/K) (e (Sum.inr j))) =
      (fun k ↦ e (Sum.inr k)) ''
        (letI := ρ₂.mulAction; MulAction.orbit Gal(SeparableClosure K/K) j) := by
  let := (sum ρ₁ ρ₂ e).mulAction
  let := ρ₂.mulAction
  ext k
  simp only [MulAction.mem_orbit_iff, smul_def, Set.mem_image]
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨ρ₂.val σ j, ⟨σ, rfl⟩, (sum_val_apply_inr ρ₁ ρ₂ e σ j).symm⟩
  · rintro ⟨j', ⟨σ, rfl⟩, rfl⟩
    exact ⟨σ, sum_val_apply_inr ρ₁ ρ₂ e σ j⟩

/-- If `ρ₁` is transitive, the orbit of any left-summand label `e (Sum.inl i)` in `sum ρ₁ ρ₂ e` is
precisely the image of the left summand. -/
theorem orbit_sum_inl_of_isTransitive {ρ₁ : GaloisSet K m} (h₁ : ρ₁.IsTransitive)
    (ρ₂ : GaloisSet K l) (e : Fin m ⊕ Fin l ≃ Fin n) (i : Fin m) :
    letI := (sum ρ₁ ρ₂ e).mulAction
    MulAction.orbit Gal(SeparableClosure K/K) (e (Sum.inl i)) =
      Set.range (fun j ↦ e (Sum.inl j)) := by
  let := ρ₁.mulAction
  have : MulAction.IsPretransitive Gal(SeparableClosure K/K) (Fin m) := ρ₁.isTransitive_def.1 h₁
  rw [orbit_sum_inl, MulAction.orbit_eq_univ, Set.image_univ]

/-- If `ρ₂` is transitive, the orbit of any right-summand label `e (Sum.inr j)` in `sum ρ₁ ρ₂ e` is
precisely the image of the right summand. -/
theorem orbit_sum_inr_of_isTransitive (ρ₁ : GaloisSet K m) {ρ₂ : GaloisSet K l}
    (h₂ : ρ₂.IsTransitive) (e : Fin m ⊕ Fin l ≃ Fin n) (j : Fin l) :
    letI := (sum ρ₁ ρ₂ e).mulAction
    MulAction.orbit Gal(SeparableClosure K/K) (e (Sum.inr j)) =
      Set.range (fun k ↦ e (Sum.inr k)) := by
  let := ρ₂.mulAction
  have : MulAction.IsPretransitive Gal(SeparableClosure K/K) (Fin l) := ρ₂.isTransitive_def.1 h₂
  rw [orbit_sum_inr, MulAction.orbit_eq_univ, Set.image_univ]

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

/-- The stabilizer in `ρ.restrict hp e` of a label `i` is the stabilizer in `ρ` of `(e i : Fin n)`.
-/
@[simp]
theorem stabilizer_restrict (ρ : GaloisSet K n) {p : Fin n → Prop}
    (hp : ∀ σ i, p (ρ.val σ i) ↔ p i) (e : Fin m ≃ {i : Fin n // p i}) (i : Fin m) :
    (letI := (ρ.restrict hp e).mulAction;
    MulAction.stabilizer Gal(SeparableClosure K/K) i) =
      (letI := ρ.mulAction;
      MulAction.stabilizer Gal(SeparableClosure K/K) (e i : Fin n)) := by
  let := (ρ.restrict hp e).mulAction
  let := ρ.mulAction
  ext σ
  simp only [MulAction.mem_stabilizer_iff, smul_def, restrict_val_apply, Equiv.symm_apply_eq,
    Subtype.ext_iff]

/-- The orbit in `ρ.restrict hp e` of a label `i` is the preimage under `Subtype.val ∘ e` of the
orbit in `ρ` of `(e i : Fin n)`. -/
@[simp]
theorem orbit_restrict (ρ : GaloisSet K n) {p : Fin n → Prop}
    (hp : ∀ σ i, p (ρ.val σ i) ↔ p i) (e : Fin m ≃ {i : Fin n // p i}) (i : Fin m) :
    (letI := (ρ.restrict hp e).mulAction;
    MulAction.orbit Gal(SeparableClosure K/K) i) =
      (fun j : Fin m ↦ (e j : Fin n)) ⁻¹'
        (letI := ρ.mulAction; MulAction.orbit Gal(SeparableClosure K/K) (e i : Fin n)) := by
  let := (ρ.restrict hp e).mulAction
  let := ρ.mulAction
  ext j
  simp only [MulAction.mem_orbit_iff, Set.mem_preimage, smul_def, restrict_val_apply,
    Equiv.symm_apply_eq, Subtype.ext_iff]

/-- A restricted Galois set `ρ.restrict hp e` is transitive if and only if `ρ` acts transitively on
the support of `p`. -/
theorem isTransitive_restrict_iff (ρ : GaloisSet K n) {p : Fin n → Prop}
    (hp : ∀ σ i, p (ρ.val σ i) ↔ p i) (e : Fin m ≃ {i : Fin n // p i}) :
    (ρ.restrict hp e).IsTransitive ↔
      ∀ i j : Fin n, p i → p j → ∃ σ : Gal(SeparableClosure K/K), ρ.val σ i = j := by
  rw [isTransitive_iff]
  constructor
  · intro h i j hi hj
    obtain ⟨σ, hσ⟩ := h (e.symm ⟨i, hi⟩) (e.symm ⟨j, hj⟩)
    refine ⟨σ, ?_⟩
    have hσ' := congrArg (fun k ↦ (e k : Fin n)) hσ
    simpa [coe_apply_restrict_val_apply] using hσ'
  · intro h a b
    obtain ⟨σ, hσ⟩ := h (e a).1 (e b).1 (e a).2 (e b).2
    refine ⟨σ, e.injective (Subtype.ext ?_)⟩
    rw [coe_apply_restrict_val_apply, hσ]

/-- Restricting a labelled Galois set to a single orbit yields a transitive Galois set. -/
theorem isTransitive_restrict_of_orbit (ρ : GaloisSet K n) {i₀ : Fin n} {s : Set (Fin n)}
    (hs : letI := ρ.mulAction; MulAction.orbit Gal(SeparableClosure K/K) i₀ = s)
    (hp : ∀ σ j, ρ.val σ j ∈ s ↔ j ∈ s) (e : Fin m ≃ s) :
    (ρ.restrict hp e).IsTransitive := by
  let := ρ.mulAction
  rw [isTransitive_restrict_iff]
  intro i j hi hj
  have hi' : i ∈ MulAction.orbit Gal(SeparableClosure K/K) i₀ := hs ▸ hi
  have hj' : j ∈ MulAction.orbit Gal(SeparableClosure K/K) i₀ := hs ▸ hj
  exact MulAction.mem_orbit_iff.1
    (MulAction.mem_orbit_trans hj' (MulAction.mem_orbit_symm.1 hi'))

/-! ### Decomposition along an invariant predicate and a chosen orbit -/

/-- Decompose the labelled Galois sets of size `n` preserving a decidable predicate `p` into a
Galois set on `Fin m` (labelling `{i // p i}` via `e₁`) and a Galois set on `Fin l` (labelling
`{j // ¬ p j}` via `e₂`). -/
def sumComplEquiv {p : Fin n → Prop} [DecidablePred p]
    (e₁ : Fin m ≃ {i : Fin n // p i}) (e₂ : Fin l ≃ {j : Fin n // ¬ p j}) :
    GaloisSet K m × GaloisSet K l ≃
      {ρ : GaloisSet K n // ∀ σ i, p (ρ.val σ i) ↔ p i} where
  toFun q :=
    let e := (Equiv.sumCongr e₁ e₂).trans (Equiv.sumCompl p)
    ⟨sum q.1 q.2 e, fun σ k ↦ by
      obtain ⟨a | b, rfl⟩ := e.surjective k
      · rw [sum_val_apply_inl]
        simpa [e] using iff_of_true (e₁ (q.1.val σ a)).2 (e₁ a).2
      · rw [sum_val_apply_inr]
        simpa [e] using iff_of_false (e₂ (q.2.val σ b)).2 (e₂ b).2⟩
  invFun := fun ⟨ρ, hp⟩ ↦ (ρ.restrict hp e₁, ρ.restrict (fun σ j ↦ not_congr (hp σ j)) e₂)
  left_inv := by
    rintro ⟨ρ₁, ρ₂⟩
    set e := (Equiv.sumCongr e₁ e₂).trans (Equiv.sumCompl p)
    refine Prod.ext (ext fun σ a ↦ ?_) (ext fun σ b ↦ ?_)
    · apply e₁.injective
      apply Subtype.ext
      rw [coe_apply_restrict_val_apply]
      have ha : ((e₁ a : {i : Fin n // p i}) : Fin n) = e (Sum.inl a) := by simp [e]
      have ha' : ((e₁ (ρ₁.val σ a) : {i : Fin n // p i}) : Fin n) =
          e (Sum.inl (ρ₁.val σ a)) := by simp [e]
      rw [ha, sum_val_apply_inl, ← ha']
    · apply e₂.injective
      apply Subtype.ext
      rw [coe_apply_restrict_val_apply]
      have hb : ((e₂ b : {j : Fin n // ¬ p j}) : Fin n) = e (Sum.inr b) := by simp [e]
      have hb' : ((e₂ (ρ₂.val σ b) : {j : Fin n // ¬ p j}) : Fin n) =
          e (Sum.inr (ρ₂.val σ b)) := by simp [e]
      rw [hb, sum_val_apply_inr, ← hb']
  right_inv := by
    rintro ⟨ρ, hp⟩
    set e := (Equiv.sumCongr e₁ e₂).trans (Equiv.sumCompl p)
    refine Subtype.ext (ext fun σ k ↦ ?_)
    obtain ⟨a | b, rfl⟩ := e.surjective k
    · rw [sum_val_apply_inl]
      simp [e]
    · rw [sum_val_apply_inr]
      simp [e]

/-- The forward direction of `sumComplEquiv` is `GaloisSet.sum` along `Equiv.sumCompl p`. -/
@[simp]
theorem coe_sumComplEquiv_apply {p : Fin n → Prop} [DecidablePred p]
    (e₁ : Fin m ≃ {i : Fin n // p i}) (e₂ : Fin l ≃ {j : Fin n // ¬ p j})
    (q : GaloisSet K m × GaloisSet K l) :
    (sumComplEquiv e₁ e₂ q : GaloisSet K n) =
      sum q.1 q.2 ((Equiv.sumCongr e₁ e₂).trans (Equiv.sumCompl p)) :=
  (rfl)

/-- The first component of `sumComplEquiv.symm` restricts along `e₁`. -/
@[simp]
theorem fst_sumComplEquiv_symm_apply {p : Fin n → Prop} [DecidablePred p]
    (e₁ : Fin m ≃ {i : Fin n // p i}) (e₂ : Fin l ≃ {j : Fin n // ¬ p j})
    (ρ : {ρ : GaloisSet K n // ∀ σ i, p (ρ.val σ i) ↔ p i}) :
    ((sumComplEquiv e₁ e₂).symm ρ).1 = ρ.1.restrict ρ.2 e₁ :=
  (rfl)

/-- The second component of `sumComplEquiv.symm` restricts along `e₂`. -/
@[simp]
theorem snd_sumComplEquiv_symm_apply {p : Fin n → Prop} [DecidablePred p]
    (e₁ : Fin m ≃ {i : Fin n // p i}) (e₂ : Fin l ≃ {j : Fin n // ¬ p j})
    (ρ : {ρ : GaloisSet K n // ∀ σ i, p (ρ.val σ i) ↔ p i}) :
    ((sumComplEquiv e₁ e₂).symm ρ).2 =
      ρ.1.restrict (fun σ j ↦ not_congr (ρ.2 σ j)) e₂ :=
  (rfl)

/-- Any set equal to an orbit of `ρ` is invariant under the permutations of `ρ`. -/
theorem val_apply_mem_iff_of_orbit_eq {ρ : GaloisSet K n} {i₀ : Fin n} {s : Set (Fin n)}
    (hs : letI := ρ.mulAction; MulAction.orbit Gal(SeparableClosure K/K) i₀ = s)
    (σ : Gal(SeparableClosure K/K)) (j : Fin n) :
    ρ.val σ j ∈ s ↔ j ∈ s := by
  let := ρ.mulAction
  rw [← hs, ← smul_def, ← MulAction.orbit_eq_iff, MulAction.orbit_smul, MulAction.orbit_eq_iff]

/-- Decompose the labelled Galois sets of size `n` in which a base label `i₀` has orbit `s` into a
transitive Galois set on `Fin m` (labelling `s` via `e₁`) and a Galois set on `Fin l` (labelling the
complement via `e₂`). -/
def orbitSumEquiv {i₀ : Fin n} {s : Set (Fin n)} [DecidablePred (· ∈ s)]
    (hi₀ : i₀ ∈ s) (e₁ : Fin m ≃ s) (e₂ : Fin l ≃ {j : Fin n // j ∉ s}) :
    {ρ₁ : GaloisSet K m // ρ₁.IsTransitive} × GaloisSet K l ≃
      {ρ : GaloisSet K n //
        letI := ρ.mulAction
        MulAction.orbit Gal(SeparableClosure K/K) i₀ = s} :=
  let a₀ : Fin m := e₁.symm ⟨i₀, hi₀⟩
  let e : Fin m ⊕ Fin l ≃ Fin n := (Equiv.sumCongr e₁ e₂).trans (Equiv.sumCompl (· ∈ s))
  have ha₀ : e (Sum.inl a₀) = i₀ := by simp [e, a₀]
  have hrange : Set.range (fun a ↦ e (Sum.inl a)) = s := by
    ext j
    simp only [Set.mem_range, e, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.sumCompl_apply_inl]
    exact ⟨by rintro ⟨a, rfl⟩; exact (e₁ a).2, fun hj ↦ ⟨e₁.symm ⟨j, hj⟩, by simp⟩⟩
  have htrans : ∀ q : GaloisSet K m × GaloisSet K l,
      q.1.IsTransitive ↔
        (letI := (sumComplEquiv e₁ e₂ q : GaloisSet K n).mulAction
        MulAction.orbit Gal(SeparableClosure K/K) i₀ = s) := by
    intro q
    let := q.1.mulAction
    rw [coe_sumComplEquiv_apply, ← ha₀, orbit_sum_inl,
      q.1.isTransitive_def, MulAction.isPretransitive_iff_orbit_eq_univ a₀, ← hrange,
      ← Set.image_univ,
      ← Set.image_eq_image (f := fun j ↦ e (Sum.inl j)) (e.injective.comp Sum.inl_injective)]
  (Equiv.prodSubtypeFstEquivSubtypeProd.symm.trans
    ((sumComplEquiv e₁ e₂).subtypeEquiv htrans)).trans
    (Equiv.subtypeSubtypeEquivSubtype fun {_} horb ↦ val_apply_mem_iff_of_orbit_eq horb)

/-- The forward direction of `orbitSumEquiv` is `GaloisSet.sum` along the induced bijection
`Fin m ⊕ Fin l ≃ Fin n`. -/
@[simp]
theorem coe_orbitSumEquiv_apply {i₀ : Fin n} {s : Set (Fin n)} [DecidablePred (· ∈ s)]
    (hi₀ : i₀ ∈ s) (e₁ : Fin m ≃ s) (e₂ : Fin l ≃ {j : Fin n // j ∉ s})
    (p : {ρ₁ : GaloisSet K m // ρ₁.IsTransitive} × GaloisSet K l) :
    (orbitSumEquiv hi₀ e₁ e₂ p : GaloisSet K n) =
      sum p.1.1 p.2 ((Equiv.sumCongr e₁ e₂).trans (Equiv.sumCompl (· ∈ s))) :=
  (rfl)

/-- The first component of `orbitSumEquiv.symm` restricts to `s` along `e₁`. -/
@[simp]
theorem coe_fst_orbitSumEquiv_symm_apply {i₀ : Fin n} {s : Set (Fin n)} [DecidablePred (· ∈ s)]
    (hi₀ : i₀ ∈ s) (e₁ : Fin m ≃ s) (e₂ : Fin l ≃ {j : Fin n // j ∉ s})
    (ρ : {ρ : GaloisSet K n //
      letI := ρ.mulAction; MulAction.orbit Gal(SeparableClosure K/K) i₀ = s}) :
    (((orbitSumEquiv hi₀ e₁ e₂).symm ρ).1 : GaloisSet K m) =
      ρ.1.restrict (val_apply_mem_iff_of_orbit_eq ρ.2) e₁ :=
  (rfl)

/-- The second component of `orbitSumEquiv.symm` restricts to `sᶜ` along `e₂`. -/
@[simp]
theorem snd_orbitSumEquiv_symm_apply {i₀ : Fin n} {s : Set (Fin n)} [DecidablePred (· ∈ s)]
    (hi₀ : i₀ ∈ s) (e₁ : Fin m ≃ s) (e₂ : Fin l ≃ {j : Fin n // j ∉ s})
    (ρ : {ρ : GaloisSet K n //
      letI := ρ.mulAction; MulAction.orbit Gal(SeparableClosure K/K) i₀ = s}) :
    ((orbitSumEquiv hi₀ e₁ e₂).symm ρ).2 =
      ρ.1.restrict (fun σ j ↦ not_congr (val_apply_mem_iff_of_orbit_eq ρ.2 σ j)) e₂ :=
  (rfl)

end TauCeti.GaloisSet
