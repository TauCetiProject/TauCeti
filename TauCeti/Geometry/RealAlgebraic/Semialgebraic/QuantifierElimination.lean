/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Formula

/-!
# Quantifier elimination from projection closure

Let `R` be a commutative ring with a compatible linear order, regarded as a structure in the
first-order language of ordered rings `Language.ring.sum Language.order`. Suppose that semialgebraic
sets are closed under projection: for every semialgebraic `s ⊆ R ^ (n + 1)`, the image
`Fin.tail '' s ⊆ R ^ n` forgetting coordinate `0` is semialgebraic
(`TauCeti.HasSemialgebraicProjections R`). For `ℝ` this is the Tarski–Seidenberg theorem, an
instance proved in `TauCeti.Geometry.RealAlgebraic.CAD.Existence`, so every result below holds
over `ℝ` unconditionally. This file shows that projection closure gives quantifier elimination in
the language of ordered rings, with parameters from `R`.

The argument is by induction on formulas. Atomic formulas define semialgebraic sets, and so do
implications of semialgebraic conditions. An existential quantifier over the last bound variable
is a projection of a semialgebraic set; a universal quantifier is the complement of the existential
quantifier of the complement. The projection hypothesis concerns `R ^ (n + 1)` only, but formulas
may have infinitely many free variables (the parameters are free variables indexed by `R`). Since
membership in a semialgebraic set depends on only finitely many coordinates
(`TauCeti.IsSemialgebraic.exists_finset_mem_iff_of_eqOn`), projections in arbitrary dimension
reduce to the finite-dimensional case.

## Main results

All results but the last assume projection closure, `[TauCeti.HasSemialgebraicProjections R]`.

* `TauCeti.IsSemialgebraic.image_comp_some`: semialgebraic subsets of `Option σ → R` have
  semialgebraic projections to `σ → R`, for every index type `σ`.
* `FirstOrder.Language.BoundedFormula.isSemialgebraic_setOf_realize`,
  `FirstOrder.Language.Formula.isSemialgebraic_setOf_realize`: every formula of ordered rings
  defines a semialgebraic set, and so does every formula whose free variables `Sum.inl a` are
  assigned parameters from `R`
  (`FirstOrder.Language.Formula.isSemialgebraic_setOf_realize_sumElim`).
* `Set.Definable.isSemialgebraic`: every set definable with parameters is semialgebraic, and so
  `TauCeti.isSemialgebraic_iff_definable` identifies the semialgebraic sets with the sets
  definable with parameters from `R`.
* `TauCeti.exists_isQF_realize_iff`: **quantifier elimination**. Every formula of ordered rings
  with parameters from `R` is equivalent, under every assignment of its free variables, to a
  quantifier-free formula with parameters.
* `TauCeti.hasSemialgebraicProjections_iff_forall_definable_isSemialgebraic`: conversely, if every
  definable subset of `R ^ n` is semialgebraic then semialgebraic sets are closed under projection.
  So the projection hypothesis is exactly what quantifier elimination needs.

## References

* S. Basu, R. Pollack, and M.-F. Roy,
  [Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
  second edition, Sections 2.3 and 2.4: Tarski–Seidenberg and quantifier elimination.
* D. Marker, *Model Theory: An Introduction*, Graduate Texts in Mathematics 217, Springer (2002),
  Section 3.3.
-/

public section

open FirstOrder FirstOrder.Language MvPolynomial Set TauCeti

section Projection

variable {R : Type*} [CommRing R] [LinearOrder R] [HasSemialgebraicProjections R]

namespace TauCeti

/-- **Projection in arbitrary dimension.** If semialgebraic subsets of `R ^ (n + 1)` have
semialgebraic projections to `R ^ n`, then for every index type `σ` the projection of a
semialgebraic subset of `Option σ → R`, forgetting the coordinate `none`, is semialgebraic. -/
theorem IsSemialgebraic.image_comp_some
    {σ : Type*} {s : Set (Option σ → R)} (hs : IsSemialgebraic s) :
    IsSemialgebraic ((fun x : Option σ → R => x ∘ some) '' s) := by
  classical
  -- `s` only depends on the coordinate `none` and the coordinates in a finite set `F`.
  obtain ⟨G, hG⟩ := hs.exists_finset_mem_iff_of_eqOn
  set F := G.eraseNone
  set e := F.equivFin
  -- Read off a point of `Option σ → R` from its coordinates `none` and `F`, listed in
  -- `Fin (F.card + 1)`; the other coordinates are set to zero.
  let g : Option σ → MvPolynomial (Fin (F.card + 1)) R := fun o =>
    o.elim (X 0) fun i => if h : i ∈ F then X (e ⟨i, h⟩).succ else 0
  set t := (fun y i => eval y (g i)) ⁻¹' s
  have hg (x : Option σ → R) (y : Fin (F.card + 1) → R) (h0 : y 0 = x none)
      (hF : ∀ i : F, y (e i).succ = x (some i)) : (fun i => eval y (g i)) ∈ s ↔ x ∈ s := by
    refine hG _ _ fun o ho => ?_
    cases o with
    | none => simpa [g] using h0
    | some i =>
      have hi : i ∈ F := Finset.mem_eraseNone.2 ho
      simpa [g, hi] using hF ⟨i, hi⟩
  convert (HasSemialgebraicProjections.isSemialgebraic_image_tail
    (hs.preimage_eval g)).preimage_comp fun j => (e.symm j : σ) using 1
  ext x
  simp only [mem_image, mem_preimage]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨Fin.cons (z none) (z ∘ some ∘ fun j => (e.symm j : σ)),
      (hg z _ rfl fun i => by simp).2 hz, Fin.tail_cons _ _⟩
  · rintro ⟨y, hy, hyx⟩
    refine ⟨fun o => o.elim (y 0) x, (hg _ y rfl fun i => ?_).1 hy, rfl⟩
    simpa [Fin.tail] using congrFun hyx (e i)

end TauCeti

/-- The existential quantifier over the last of `n + 1` bound variables preserves
semialgebraicity, given projection closure. -/
private theorem TauCeti.IsSemialgebraic.setOf_exists_sumElim_snoc
    {α : Type*} {n : ℕ} {S : Set (α ⊕ Fin (n + 1) → R)} (hS : IsSemialgebraic S) :
    IsSemialgebraic
      {x : α ⊕ Fin n → R | ∃ a, Sum.elim (x ∘ Sum.inl) (Fin.snoc (x ∘ Sum.inr) a) ∈ S} := by
  -- Single out the last bound variable as the coordinate `none` of `Option (α ⊕ Fin n)`.
  let g : α ⊕ Fin (n + 1) → Option (α ⊕ Fin n) :=
    Sum.elim (some ∘ Sum.inl) (Fin.snoc (some ∘ Sum.inr) none)
  have hg (z : Option (α ⊕ Fin n) → R) :
      z ∘ g = Sum.elim (z ∘ some ∘ Sum.inl) (Fin.snoc (z ∘ some ∘ Sum.inr) (z none)) := by
    simp [g, Sum.comp_elim, Fin.comp_snoc]
  convert (hS.preimage_comp g).image_comp_some using 1
  ext x
  simp only [mem_ofPred_eq, mem_image, mem_preimage, hg]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨fun o => o.elim a x, ha, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z none, hz⟩

end Projection

variable {R : Type*} [CommRing R] [Ring.CompatibleRing R] [Language.order.Structure R]
  [LinearOrder R] [IsOrderedAddMonoid R] [(Language.ring.sum Language.order).OrderedStructure R]
  [HasSemialgebraicProjections R]

namespace FirstOrder.Language.BoundedFormula

/-- Given projection closure, a formula of ordered rings with free variables `α` and `n` bound
variables defines a semialgebraic subset of `α ⊕ Fin n → R`. -/
theorem isSemialgebraic_setOf_realize
    {α : Type*} {n : ℕ} (φ : (Language.ring.sum Language.order).BoundedFormula α n) :
    IsSemialgebraic {x : α ⊕ Fin n → R | φ.Realize (x ∘ Sum.inl) (x ∘ Sum.inr)} := by
  induction φ with
  | falsum => exact isQF_bot.isSemialgebraic_setOf_realize
  | equal t₁ t₂ => exact (IsAtomic.equal t₁ t₂).isQF.isSemialgebraic_setOf_realize
  | rel r ts => exact (IsAtomic.rel r ts).isQF.isSemialgebraic_setOf_realize
  | imp φ ψ ihφ ihψ =>
    simpa [Set.ofPred_or, imp_iff_not_or, Set.compl_ofPred] using ihφ.compl.union ihψ
  | all φ ih =>
    -- `∀ a, φ` is the complement of `∃ a, ¬ φ`.
    convert (IsSemialgebraic.setOf_exists_sumElim_snoc ih.compl).compl using 1
    ext x
    simp

end FirstOrder.Language.BoundedFormula

/-- Given projection closure, a formula of ordered rings with free variables `α` defines a
semialgebraic subset of `α → R`. -/
theorem FirstOrder.Language.Formula.isSemialgebraic_setOf_realize
    {α : Type*} (φ : (Language.ring.sum Language.order).Formula α) :
    IsSemialgebraic {v : α → R | φ.Realize v} := by
  convert (BoundedFormula.isSemialgebraic_setOf_realize (R := R) φ).preimage_comp
    (Sum.elim id finZeroElim : α ⊕ Fin 0 → α) using 1
  ext v
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Formula.Realize, Function.comp_assoc,
    Sum.elim_comp_inl, Function.comp_id]
  exact iff_of_eq (congrArg _ (Subsingleton.elim _ _))

/-- Given projection closure, a formula of ordered rings with free variables `A ⊕ σ` defines a
semialgebraic subset of `σ → R` once the variables `Sum.inl a` are assigned parameters `f a`. -/
theorem FirstOrder.Language.Formula.isSemialgebraic_setOf_realize_sumElim
    {A σ : Type*} (φ : (Language.ring.sum Language.order).Formula (A ⊕ σ)) (f : A → R) :
    IsSemialgebraic {v : σ → R | φ.Realize (Sum.elim f v)} := by
  -- Substituting the parameters is a polynomial map.
  have h := φ.isSemialgebraic_setOf_realize.preimage_eval
    (Sum.elim (fun a => C (f a)) X : A ⊕ σ → MvPolynomial σ R)
  have hf : (fun (v : σ → R) (i : A ⊕ σ) => eval v (Sum.elim (fun a => C (f a)) X i)) =
      fun v => Sum.elim f v := by
    ext v (a | i) <;> simp
  rwa [hf] at h

/-- Given projection closure, a subset of `σ → R` definable with parameters from a set `A ⊆ R` in
the language of ordered rings is semialgebraic. -/
theorem Set.Definable.isSemialgebraic
    {σ : Type*} {A : Set R} {s : Set (σ → R)}
    (hs : A.Definable (Language.ring.sum Language.order) s) : IsSemialgebraic s := by
  obtain ⟨φ, rfl⟩ := Set.definable_iff_exists_formula_sum.1 hs
  exact φ.isSemialgebraic_setOf_realize_sumElim _

namespace TauCeti

/-- Given projection closure, a subset of `σ → R` is semialgebraic if and only if it is definable
in the language of ordered rings with parameters from `R`. -/
theorem isSemialgebraic_iff_definable {σ : Type*} {s : Set (σ → R)} :
    IsSemialgebraic s ↔ (Set.univ : Set R).Definable (Language.ring.sum Language.order) s :=
  ⟨IsSemialgebraic.definable, Set.Definable.isSemialgebraic⟩

/-- **Quantifier elimination**, given projection closure. Every formula of ordered rings whose
free variables `Sum.inl r` are assigned the parameters `r ∈ R` is equivalent, for every
assignment `v` of the remaining free variables, to a quantifier-free formula with parameters. -/
theorem exists_isQF_realize_iff {σ : Type*}
    (φ : (Language.ring.sum Language.order).Formula (R ⊕ σ)) :
    ∃ ψ : (Language.ring.sum Language.order).Formula (R ⊕ σ), ψ.IsQF ∧
      ∀ v : σ → R, φ.Realize (Sum.elim id v) ↔ ψ.Realize (Sum.elim id v) := by
  obtain ⟨ψ, hψ, hs⟩ :=
    isSemialgebraic_iff_exists_isQF.1 (φ.isSemialgebraic_setOf_realize_sumElim id)
  exact ⟨ψ, hψ, fun v => Set.ext_iff.1 hs v⟩

omit [HasSemialgebraicProjections R] in
/-- **Projection closure is equivalent to quantifier elimination.** Semialgebraic subsets of
`R ^ (n + 1)` have semialgebraic projections to `R ^ n`, for every `n`, if and only if every
subset of every `R ^ n` definable with parameters in the language of ordered rings is
semialgebraic. -/
theorem hasSemialgebraicProjections_iff_forall_definable_isSemialgebraic :
    HasSemialgebraicProjections R ↔ ∀ (n : ℕ) (s : Set (Fin n → R)),
      (Set.univ : Set R).Definable (Language.ring.sum Language.order) s → IsSemialgebraic s := by
  refine ⟨fun _ _ _ => Set.Definable.isSemialgebraic, fun h => ⟨fun hs => ?_⟩⟩
  -- Definable sets are closed under projection.
  exact h _ _ (hs.definable.image_comp Fin.succ)

end TauCeti
