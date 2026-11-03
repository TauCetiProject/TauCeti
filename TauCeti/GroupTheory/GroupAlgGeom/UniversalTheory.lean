/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Discrimination
public import TauCeti.ModelTheory.Algebra.Group.Basic
public import Mathlib.ModelTheory.Complexity

/-!
# Discrimination preserves universal sentences

Let `K` and `H` receive coefficients from `G`, and read the group language with coefficient names
`A` in both through a map `c : A → G`. If `K` is discriminated by `H` over `G`, then every
universal sentence that holds in `H` also holds in `K`.

A quantifier-free formula evaluated at a tuple of `K` keeps its truth value under every
coefficient-preserving homomorphism `K →* H` that keeps finitely many nontrivial elements of `K`,
determined by the tuple, nontrivial; discrimination provides such a homomorphism. A
counterexample in `K` to a universal sentence is therefore carried to a counterexample in `H`.

With trivial coefficients this says that a fully residually free group satisfies every universal
sentence true in the free group of rank two
(`TauCeti.LimitGroup.IsFullyResiduallyFree.realize_of_isUniversal`).

## Main results

* `TauCeti.GroupAlgGeom.IsDiscriminatedBy.realize_of_isUniversal`: universal sentences with
  coefficients from `G` pass from `H` to `K`.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.6.
-/

public section

namespace TauCeti.GroupAlgGeom

open FirstOrder FirstOrder.Language

variable {G K H : Type*} [Group G] [Group K] [Group H] {ιK : G →* K} {ιH : G →* H}
  {A : Type*} {α : Type*} {n : ℕ}

/-- A coefficient-preserving homomorphism commutes with evaluation of group terms with
coefficient names `A`, read through `c : A → G`. -/
private theorem realize_term_comp (f : GHom ιK ιH) (c : A → G)
    {β : Type*} (t : Language.group[[A]].Term β) (w : β → K) :
    letI : Language.group.Structure K := TauCeti.Group.structureOfGroup K
    letI : (Language.constantsOn A).Structure K := Language.constantsOn.structure (ιK ∘ c)
    letI : Language.group.Structure H := TauCeti.Group.structureOfGroup H
    letI : (Language.constantsOn A).Structure H := Language.constantsOn.structure (ιH ∘ c)
    t.realize (f ∘ w) = f (t.realize w) := by
  let : Language.group.Structure K := TauCeti.Group.structureOfGroup K
  let : (Language.constantsOn A).Structure K := Language.constantsOn.structure (ιK ∘ c)
  let : Language.group.Structure H := TauCeti.Group.structureOfGroup H
  let : (Language.constantsOn A).Structure H := Language.constantsOn.structure (ιH ∘ c)
  let g := MonoidHom.coeffGroupLanguageHom (f : K →* H) (ιK ∘ c) (ιH ∘ c)
    fun a => f.map_coeff (c a)
  have hg : ⇑g = ⇑f := funext fun x => MonoidHom.coeffGroupLanguageHom_apply _ _ _ _ x
  rw [← hg]
  exact HomClass.realize_term g

/-- A quantifier-free formula keeps its truth value under every coefficient-preserving
homomorphism that keeps finitely many nontrivial elements, depending on the assignment,
nontrivial. -/
private theorem exists_finset_realize_comp_iff (c : A → G)
    {φ : Language.group[[A]].BoundedFormula α n} (hφ : φ.IsQF) (v : α → K) (xs : Fin n → K) :
    letI : Language.group.Structure K := TauCeti.Group.structureOfGroup K
    letI : (Language.constantsOn A).Structure K := Language.constantsOn.structure (ιK ∘ c)
    letI : Language.group.Structure H := TauCeti.Group.structureOfGroup H
    letI : (Language.constantsOn A).Structure H := Language.constantsOn.structure (ιH ∘ c)
    ∃ s : Finset K, (∀ k ∈ s, k ≠ 1) ∧ ∀ f : GHom ιK ιH, (∀ k ∈ s, f k ≠ 1) →
      (φ.Realize (f ∘ v) (f ∘ xs) ↔ φ.Realize v xs) := by
  classical
  let : Language.group.Structure K := TauCeti.Group.structureOfGroup K
  let : (Language.constantsOn A).Structure K := Language.constantsOn.structure (ιK ∘ c)
  let : Language.group.Structure H := TauCeti.Group.structureOfGroup H
  let : (Language.constantsOn A).Structure H := Language.constantsOn.structure (ιH ∘ c)
  induction hφ with
  | falsum => exact ⟨∅, by simp, fun _ _ => Iff.rfl⟩
  | of_isAtomic h =>
    cases h with
    | equal t₁ t₂ =>
      -- The only element to keep nontrivial is the quotient of the two sides.
      let x := t₁.realize (Sum.elim v xs) * (t₂.realize (Sum.elim v xs))⁻¹
      refine ⟨({x} : Finset K).filter (· ≠ 1), by simp, fun f hf => ?_⟩
      simp only [BoundedFormula.realize_bdEqual, ← Sum.comp_elim, realize_term_comp]
      refine ⟨fun hfx => ?_, fun hx => by rw [hx]⟩
      by_contra hx
      exact hf x (by simpa [x, mul_inv_eq_one] using hx) (by simp [x, hfx])
    | rel R _ =>
      -- The coefficient extension has two empty relation-symbol summands.
      change Empty ⊕ Empty at R
      rcases R with r | r <;> exact isEmptyElim r
  | imp _ _ ih₁ ih₂ =>
    obtain ⟨s₁, hs₁, h₁⟩ := ih₁
    obtain ⟨s₂, hs₂, h₂⟩ := ih₂
    refine ⟨s₁ ∪ s₂, fun k hk => (Finset.mem_union.1 hk).elim (hs₁ k) (hs₂ k), fun f hf => ?_⟩
    rw [BoundedFormula.realize_imp, BoundedFormula.realize_imp,
      h₁ f fun k hk => hf k (Finset.mem_union_left _ hk),
      h₂ f fun k hk => hf k (Finset.mem_union_right _ hk)]

-- The reduction `FirstOrder.Language.group.universal_iff_no_solution` to word systems fixes one
-- universe for the groups it describes, while `K` and `H` may live in different universes, so
-- the transfer is proved by induction on the formula instead.
/-- If `K` is discriminated by `H` over `G`, a universal formula holds at an assignment in `K`
as soon as it holds at its image under every coefficient-preserving homomorphism to `H`. -/
private theorem realize_of_forall_realize_comp (h : IsDiscriminatedBy ιK ιH) (c : A → G)
    {φ : Language.group[[A]].BoundedFormula α n} (hφ : φ.IsUniversal) (v : α → K)
    (xs : Fin n → K) :
    letI : Language.group.Structure K := TauCeti.Group.structureOfGroup K
    letI : (Language.constantsOn A).Structure K := Language.constantsOn.structure (ιK ∘ c)
    letI : Language.group.Structure H := TauCeti.Group.structureOfGroup H
    letI : (Language.constantsOn A).Structure H := Language.constantsOn.structure (ιH ∘ c)
    (∀ f : GHom ιK ιH, φ.Realize (f ∘ v) (f ∘ xs)) → φ.Realize v xs := by
  let : Language.group.Structure K := TauCeti.Group.structureOfGroup K
  let : (Language.constantsOn A).Structure K := Language.constantsOn.structure (ιK ∘ c)
  let : Language.group.Structure H := TauCeti.Group.structureOfGroup H
  let : (Language.constantsOn A).Structure H := Language.constantsOn.structure (ιH ∘ c)
  induction hφ with
  | of_isQF hφ =>
    intro hf
    obtain ⟨s, hs, hsf⟩ := exists_finset_realize_comp_iff (ιK := ιK) (ιH := ιH) c hφ v xs
    obtain ⟨f, hf'⟩ := (isDiscriminatedBy_def ιK ιH).1 h s hs
    exact (hsf f hf').1 (hf f)
  | all _ ih =>
    intro hf
    rw [BoundedFormula.realize_all]
    intro x
    refine ih (Fin.snoc xs x) fun f => ?_
    rw [Fin.comp_snoc]
    exact (BoundedFormula.realize_all.1 (hf f)) (f x)

namespace IsDiscriminatedBy

/-- If `K` is discriminated by `H` over `G`, every universal sentence of the group language with
coefficient names `A`, read through `c : A → G`, that holds in `H` also holds in `K`. -/
theorem realize_of_isUniversal (h : IsDiscriminatedBy ιK ιH) (c : A → G)
    {σ : Language.group[[A]].Sentence} (hσ : σ.IsUniversal) :
    letI : Language.group.Structure K := TauCeti.Group.structureOfGroup K
    letI : (Language.constantsOn A).Structure K := Language.constantsOn.structure (ιK ∘ c)
    letI : Language.group.Structure H := TauCeti.Group.structureOfGroup H
    letI : (Language.constantsOn A).Structure H := Language.constantsOn.structure (ιH ∘ c)
    H ⊨ σ → K ⊨ σ := by
  let : Language.group.Structure K := TauCeti.Group.structureOfGroup K
  let : (Language.constantsOn A).Structure K := Language.constantsOn.structure (ιK ∘ c)
  let : Language.group.Structure H := TauCeti.Group.structureOfGroup H
  let : (Language.constantsOn A).Structure H := Language.constantsOn.structure (ιH ∘ c)
  intro hH
  refine realize_of_forall_realize_comp h c hσ default default fun f => ?_
  -- A sentence has no free or bound variables, so every assignment is the default one.
  rwa [Subsingleton.elim (f ∘ default) default, Subsingleton.elim (f ∘ default) default]

end IsDiscriminatedBy

end TauCeti.GroupAlgGeom
