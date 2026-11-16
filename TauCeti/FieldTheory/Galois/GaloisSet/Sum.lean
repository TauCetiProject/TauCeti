/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.GaloisSet.Basic
public import Mathlib.Algebra.Group.Action.Sum

/-!
# Disjoint unions and invariant decompositions of labelled Galois sets

Given a bijection `e : Fin m ⊕ Fin n ≃ Fin k`, two labelled Galois sets `ρ₁ : GaloisSet K m` and
`ρ₂ : GaloisSet K n` combine into a labelled Galois set `ofSumEquiv e ρ₁ ρ₂ : GaloisSet K k` on
which the absolute Galois group acts independently on the left and right summands. Conversely, any
labelled Galois set preserving a subset of labels restricts to a labelled Galois set on that subset
(`restrict`), and pairs `(ρ₁, ρ₂)` correspond bijectively to labelled Galois sets of size `k`
preserving `Set.range (e ∘ Sum.inl)` (`sumEquiv`).

When `0 < m`, `Set.range (e ∘ Sum.inl)` is a single orbit of `ofSumEquiv e ρ₁ ρ₂` if and only if
`ρ₁` is transitive (`exists_orbit_ofSumEquiv_eq_range_inl_iff`). This is the decomposition step
used to peel off one orbit at a time when factoring masses of labelled Galois sets by splitting
symbol.

Only a field structure on `K` is needed here.

## Main definitions and results

* `TauCeti.GaloisSet.ofSumEquiv`: disjoint union of two labelled Galois sets along a sum
  equivalence `Fin m ⊕ Fin n ≃ Fin k`.
* `TauCeti.GaloisSet.restrict`: restriction of a labelled Galois set to an invariant subset of
  labels.
* `TauCeti.GaloisSet.sumEquiv`: bijection between `GaloisSet K m × GaloisSet K n` and labelled
  Galois sets of size `k` preserving `Set.range (e ∘ Sum.inl)`.
* `TauCeti.GaloisSet.exists_orbit_ofSumEquiv_eq_range_inl_iff`: for `0 < m`, the left summand is a
  single orbit of `ofSumEquiv e ρ₁ ρ₂` iff `ρ₁` is transitive.
-/

public section

noncomputable section

namespace TauCeti.GaloisSet

variable {K : Type*} [Field K] {m n k : ℕ}

/-- The disjoint union of two labelled Galois sets `ρ₁` and `ρ₂`, transported to `Fin k` along an
equivalence `e : Fin m ⊕ Fin n ≃ Fin k`. Its kernel is the intersection of the kernels of `ρ₁` and
`ρ₂`, hence open. -/
def ofSumEquiv (e : Fin m ⊕ Fin n ≃ Fin k) (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K n) :
    GaloisSet K k :=
  ⟨e.permCongrHom.toMonoidHom.comp
    ((Equiv.Perm.sumCongrHom (Fin m) (Fin n)).comp (ρ₁.val.prod ρ₂.val)), by
    rw [MonoidHom.ker_comp_of_injective _ _ e.permCongrHom.injective,
      MonoidHom.ker_comp_of_injective _ _ Equiv.Perm.sumCongrHom_injective,
      MonoidHom.ker_prod]
    exact ρ₁.property.inter ρ₂.property⟩

/-- On labels coming from the left summand, `ofSumEquiv` acts through `ρ₁`. -/
@[simp]
theorem ofSumEquiv_val_apply_inl (e : Fin m ⊕ Fin n ≃ Fin k)
    (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K n)
    (σ : Gal(SeparableClosure K/K)) (i : Fin m) :
    (ofSumEquiv e ρ₁ ρ₂).val σ (e (.inl i)) = e (.inl (ρ₁.val σ i)) := by
  simp [ofSumEquiv]

/-- On labels coming from the right summand, `ofSumEquiv` acts through `ρ₂`. -/
@[simp]
theorem ofSumEquiv_val_apply_inr (e : Fin m ⊕ Fin n ≃ Fin k)
    (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K n)
    (σ : Gal(SeparableClosure K/K)) (j : Fin n) :
    (ofSumEquiv e ρ₁ ρ₂).val σ (e (.inr j)) = e (.inr (ρ₂.val σ j)) := by
  simp [ofSumEquiv]

/-- The bijection `e : Fin m ⊕ Fin n ≃ Fin k` is equivariant from the summandwise action of `ρ₁`
and `ρ₂` to the action of `ofSumEquiv e ρ₁ ρ₂`. -/
theorem ofSumEquiv_val_apply_eq_smul (e : Fin m ⊕ Fin n ≃ Fin k)
    (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K n)
    (σ : Gal(SeparableClosure K/K)) (x : Fin m ⊕ Fin n) :
    letI := ρ₁.mulAction
    letI := ρ₂.mulAction
    e (σ • x) = (ofSumEquiv e ρ₁ ρ₂).val σ (e x) := by
  let := ρ₁.mulAction
  let := ρ₂.mulAction
  cases x with
  | inl i => simp
  | inr j => simp

/-- The kernel of `ofSumEquiv e ρ₁ ρ₂` is the intersection of the kernels of `ρ₁` and `ρ₂`. -/
@[simp]
theorem ker_ofSumEquiv (e : Fin m ⊕ Fin n ≃ Fin k) (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K n) :
    (ofSumEquiv e ρ₁ ρ₂).val.ker = ρ₁.val.ker ⊓ ρ₂.val.ker := by
  rw [ofSumEquiv, MonoidHom.ker_comp_of_injective _ _ e.permCongrHom.injective,
    MonoidHom.ker_comp_of_injective _ _ Equiv.Perm.sumCongrHom_injective,
    MonoidHom.ker_prod]

/-- `ofSumEquiv e ρ₁ ρ₂` preserves the left summand `Set.range (e ∘ Sum.inl)`. -/
theorem ofSumEquiv_mapsTo_range_inl (e : Fin m ⊕ Fin n ≃ Fin k)
    (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K n) (σ : Gal(SeparableClosure K/K))
    {x : Fin k} (hx : x ∈ Set.range (e ∘ Sum.inl)) :
    (ofSumEquiv e ρ₁ ρ₂).val σ x ∈ Set.range (e ∘ Sum.inl) := by
  rcases hx with ⟨i, rfl⟩
  exact ⟨ρ₁.val σ i, by simp⟩

/-- The stabilizer in `ofSumEquiv e ρ₁ ρ₂` of a left-summand label equals its stabilizer in
`ρ₁`. -/
@[simp]
theorem stabilizer_ofSumEquiv_inl (e : Fin m ⊕ Fin n ≃ Fin k)
    (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K n) (i : Fin m) :
    (letI := (ofSumEquiv e ρ₁ ρ₂).mulAction;
      MulAction.stabilizer Gal(SeparableClosure K/K) (e (.inl i))) =
      (letI := ρ₁.mulAction;
      MulAction.stabilizer Gal(SeparableClosure K/K) i) := by
  ext σ
  simp [MulAction.mem_stabilizer_iff]

/-- The stabilizer in `ofSumEquiv e ρ₁ ρ₂` of a right-summand label equals its stabilizer in
`ρ₂`. -/
@[simp]
theorem stabilizer_ofSumEquiv_inr (e : Fin m ⊕ Fin n ≃ Fin k)
    (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K n) (j : Fin n) :
    (letI := (ofSumEquiv e ρ₁ ρ₂).mulAction;
      MulAction.stabilizer Gal(SeparableClosure K/K) (e (.inr j))) =
      (letI := ρ₂.mulAction;
      MulAction.stabilizer Gal(SeparableClosure K/K) j) := by
  ext σ
  simp [MulAction.mem_stabilizer_iff]

/-- The orbit of a left-summand label in `ofSumEquiv e ρ₁ ρ₂` is the image of its orbit in `ρ₁`. -/
theorem orbit_ofSumEquiv_inl (e : Fin m ⊕ Fin n ≃ Fin k)
    (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K n) (i : Fin m) :
    (letI := (ofSumEquiv e ρ₁ ρ₂).mulAction;
      MulAction.orbit Gal(SeparableClosure K/K) (e (.inl i))) =
      (e ∘ Sum.inl) '' (letI := ρ₁.mulAction; MulAction.orbit Gal(SeparableClosure K/K) i) := by
  ext x
  simp only [MulAction.mem_orbit_iff, smul_def, ofSumEquiv_val_apply_inl, Set.mem_image,
    Function.comp_apply]
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨ρ₁.val σ i, ⟨σ, rfl⟩, rfl⟩
  · rintro ⟨j, ⟨σ, rfl⟩, rfl⟩
    exact ⟨σ, rfl⟩

/-- The orbit of a right-summand label in `ofSumEquiv e ρ₁ ρ₂` is the image of its orbit in
`ρ₂`. -/
theorem orbit_ofSumEquiv_inr (e : Fin m ⊕ Fin n ≃ Fin k)
    (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K n) (j : Fin n) :
    (letI := (ofSumEquiv e ρ₁ ρ₂).mulAction;
      MulAction.orbit Gal(SeparableClosure K/K) (e (.inr j))) =
      (e ∘ Sum.inr) '' (letI := ρ₂.mulAction; MulAction.orbit Gal(SeparableClosure K/K) j) := by
  ext x
  simp only [MulAction.mem_orbit_iff, smul_def, ofSumEquiv_val_apply_inr, Set.mem_image,
    Function.comp_apply]
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨ρ₂.val σ j, ⟨σ, rfl⟩, rfl⟩
  · rintro ⟨i, ⟨σ, rfl⟩, rfl⟩
    exact ⟨σ, rfl⟩

/-- When `0 < m`, the left summand `Set.range (e ∘ Sum.inl)` is a single orbit of
`ofSumEquiv e ρ₁ ρ₂` if and only if `ρ₁` is transitive. -/
theorem exists_orbit_ofSumEquiv_eq_range_inl_iff (e : Fin m ⊕ Fin n ≃ Fin k)
    (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K n) (hm : 0 < m) :
    (letI := (ofSumEquiv e ρ₁ ρ₂).mulAction;
      ∃ x : Fin k, MulAction.orbit Gal(SeparableClosure K/K) x = Set.range (e ∘ Sum.inl)) ↔
      ρ₁.IsTransitive := by
  let := (ofSumEquiv e ρ₁ ρ₂).mulAction
  let i₀ : Fin m := ⟨0, hm⟩
  constructor
  · rintro ⟨x, hx⟩
    have hi₀ : e (.inl i₀) ∈ MulAction.orbit Gal(SeparableClosure K/K) x := by
      rw [hx]
      exact ⟨i₀, rfl⟩
    rw [← MulAction.orbit_eq_iff.2 hi₀, orbit_ofSumEquiv_inl] at hx
    rw [isTransitive_iff]
    intro i j
    have him : e (.inl i) ∈ (e ∘ Sum.inl) '' (letI := ρ₁.mulAction;
        MulAction.orbit Gal(SeparableClosure K/K) i₀) := hx ▸ ⟨i, rfl⟩
    have hjm : e (.inl j) ∈ (e ∘ Sum.inl) '' (letI := ρ₁.mulAction;
        MulAction.orbit Gal(SeparableClosure K/K) i₀) := hx ▸ ⟨j, rfl⟩
    obtain ⟨i', ⟨σ₁, hσ₁⟩, hi'⟩ := him
    obtain ⟨j', ⟨σ₂, hσ₂⟩, hj'⟩ := hjm
    have hi'' : i' = i := Sum.inl.inj (e.injective hi')
    have hj'' : j' = j := Sum.inl.inj (e.injective hj')
    subst hi'' hj''
    refine ⟨σ₂ * σ₁⁻¹, ?_⟩
    rw [map_mul, Equiv.Perm.mul_apply, map_inv]
    have h1 : ρ₁.val σ₁ i₀ = i' := hσ₁
    have h2 : ρ₁.val σ₂ i₀ = j' := hσ₂
    rw [← h1, Equiv.Perm.inv_def, Equiv.symm_apply_apply, h2]
  · intro hρ₁
    refine ⟨e (.inl i₀), ?_⟩
    rw [orbit_ofSumEquiv_inl]
    let := ρ₁.mulAction
    have : MulAction.IsPretransitive Gal(SeparableClosure K/K) (Fin m) := ρ₁.isTransitive_def.1 hρ₁
    rw [MulAction.orbit_eq_univ, Set.image_univ]

private theorem invariant_iff (ρ : GaloisSet K k) {p : Fin k → Prop}
    (hp : ∀ (σ : Gal(SeparableClosure K/K)) (i : Fin k), p i → p (ρ.val σ i))
    (σ : Gal(SeparableClosure K/K)) (i : Fin k) :
    p (ρ.val σ i) ↔ p i :=
  ⟨fun h ↦ by simpa using hp σ⁻¹ (ρ.val σ i) h, hp σ i⟩

/-- Restrict a labelled Galois set to an invariant subset of labels, relabelled by `e`. -/
def restrict (ρ : GaloisSet K k) {p : Fin k → Prop}
    (hp : ∀ (σ : Gal(SeparableClosure K/K)) (i : Fin k), p i → p (ρ.val σ i))
    (e : Fin m ≃ {i : Fin k // p i}) : GaloisSet K m :=
  ⟨{ toFun σ := e.symm.permCongr ((ρ.val σ).subtypePerm (invariant_iff ρ hp σ))
     map_one' := by
       ext i
       simp
     map_mul' σ τ := by
       ext i
       simp }, by
    refine Subgroup.isOpen_mono (fun σ hσ ↦ ?_) ρ.property
    rw [MonoidHom.mem_ker] at hσ ⊢
    ext i
    simp [hσ]⟩

/-- Evaluating `ρ.restrict hp e` applies `ρ` through the relabelling `e`. -/
@[simp]
theorem restrict_val_apply (ρ : GaloisSet K k) {p : Fin k → Prop}
    (hp : ∀ (σ : Gal(SeparableClosure K/K)) (i : Fin k), p i → p (ρ.val σ i))
    (e : Fin m ≃ {i : Fin k // p i}) (σ : Gal(SeparableClosure K/K)) (i : Fin m) :
    (ρ.restrict hp e).val σ i = e.symm ⟨ρ.val σ (e i), hp σ (e i) (e i).2⟩ :=
  (rfl)

/-- The image under `e` of `(ρ.restrict hp e).val σ i` is `ρ.val σ (e i)`. -/
theorem coe_apply_restrict_val_apply (ρ : GaloisSet K k) {p : Fin k → Prop}
    (hp : ∀ (σ : Gal(SeparableClosure K/K)) (i : Fin k), p i → p (ρ.val σ i))
    (e : Fin m ≃ {i : Fin k // p i}) (σ : Gal(SeparableClosure K/K)) (i : Fin m) :
    (e ((ρ.restrict hp e).val σ i) : Fin k) = ρ.val σ (e i) := by
  simp

/-- **Decomposition along an invariant subset.** Given `e : Fin m ⊕ Fin n ≃ Fin k`, pairs of
labelled Galois sets of sizes `m` and `n` correspond bijectively to labelled Galois sets of size
`k` preserving `Set.range (e ∘ Sum.inl)`. -/
def sumEquiv (e : Fin m ⊕ Fin n ≃ Fin k) :
    GaloisSet K m × GaloisSet K n ≃
      {ρ : GaloisSet K k //
        ∀ (σ : Gal(SeparableClosure K/K)) (x : Fin k),
          x ∈ Set.range (e ∘ Sum.inl) → ρ.val σ x ∈ Set.range (e ∘ Sum.inl)} :=
  let e₁ : Fin m ≃ {x : Fin k // x ∈ Set.range (e ∘ Sum.inl)} :=
    Equiv.ofInjective (e ∘ Sum.inl) (e.injective.comp Sum.inl_injective)
  let e₂ : Fin n ≃ {x : Fin k // x ∉ Set.range (e ∘ Sum.inl)} :=
    (Equiv.ofInjective (e ∘ Sum.inr) (e.injective.comp Sum.inr_injective)).trans <|
      Equiv.subtypeEquivRight fun x ↦ by
        constructor
        · rintro ⟨j, rfl⟩ ⟨i, hi⟩
          exact Sum.inl_ne_inr (e.injective hi)
        · intro hx
          rcases h : e.symm x with i | j
          · exact (hx ⟨i, by rw [Function.comp_apply, ← h, Equiv.apply_symm_apply]⟩).elim
          · exact ⟨j, by rw [Function.comp_apply, ← h, Equiv.apply_symm_apply]⟩
  { toFun p := ⟨ofSumEquiv e p.1 p.2, ofSumEquiv_mapsTo_range_inl e p.1 p.2⟩
    invFun ρ :=
      (ρ.1.restrict ρ.2 e₁,
        ρ.1.restrict (fun σ x hx hmem ↦ hx ((invariant_iff ρ.1 ρ.2 σ x).1 hmem)) e₂)
    left_inv p := by
      rcases p with ⟨ρ₁, ρ₂⟩
      have he₁ : ∀ i, (e₁ i : Fin k) = e (.inl i) := fun _ ↦ rfl
      have he₂ : ∀ j, (e₂ j : Fin k) = e (.inr j) := fun _ ↦ rfl
      refine Prod.ext (ext fun σ i ↦ ?_) (ext fun σ j ↦ ?_)
      · apply e.injective.comp Sum.inl_injective
        rw [Function.comp_apply, Function.comp_apply, ← he₁, coe_apply_restrict_val_apply, he₁,
          ofSumEquiv_val_apply_inl]
      · apply e.injective.comp Sum.inr_injective
        rw [Function.comp_apply, Function.comp_apply, ← he₂, coe_apply_restrict_val_apply, he₂,
          ofSumEquiv_val_apply_inr]
    right_inv ρ := by
      have he₁ : ∀ i, (e₁ i : Fin k) = e (.inl i) := fun _ ↦ rfl
      have he₂ : ∀ j, (e₂ j : Fin k) = e (.inr j) := fun _ ↦ rfl
      refine Subtype.ext (ext fun σ x ↦ ?_)
      rw [← e.apply_symm_apply x]
      rcases e.symm x with i | j
      · rw [ofSumEquiv_val_apply_inl, ← he₁, coe_apply_restrict_val_apply, he₁]
      · rw [ofSumEquiv_val_apply_inr, ← he₂, coe_apply_restrict_val_apply, he₂] }

/-- The underlying Galois set of `sumEquiv e (ρ₁, ρ₂)` is `ofSumEquiv e ρ₁ ρ₂`. -/
@[simp]
theorem coe_sumEquiv_apply (e : Fin m ⊕ Fin n ≃ Fin k) (p : GaloisSet K m × GaloisSet K n) :
    (sumEquiv e p : GaloisSet K k) = ofSumEquiv e p.1 p.2 :=
  (rfl)

end TauCeti.GaloisSet
