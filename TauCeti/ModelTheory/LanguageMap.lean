/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.LanguageMap

/-!
# Expansions along composite language maps, and language maps for adjoining constants

Additions to Mathlib's `Mathlib.ModelTheory.LanguageMap`: expansions compose along composite
language maps, and the reduct of an expansion along a composite `h.comp g` along the outer map `h`
is an expansion along the inner map `g`. Together they say that an `L''`-structure expands an
`L`-structure along `h.comp g` exactly when it expands, along `h`, some `L'`-structure that expands
the `L`-structure along `g`; the `L'`-structure can be taken to be the reduct.

## Main results

* `FirstOrder.Language.LHom.comp_isExpansionOn`: expansions along `g` and along `h` compose to an
  expansion along `h.comp g`.
* `FirstOrder.Language.LHom.isExpansionOn_reduct_of_comp`: the reduct along `h` of an expansion
  along `h.comp g` is an expansion along `g`.
* `FirstOrder.Language.LHom.id_isExpansionOn_reduct`: the reduct of an expansion along the map
  it expands along is the original structure.
* `FirstOrder.Language.LHom.sumMap_isExpansionOn_of_reduct`: a structure on a sum language is
  expanded along `ϕ.sumMap ψ` by a sum structure expanding its two parts along `ϕ` and `ψ`.
* `FirstOrder.Language.LHom.mem_range_sumInl_onFunction_of_mem_range_sumMap` and
  `FirstOrder.Language.LHom.mem_range_sumInl_onRelation_of_mem_range_sumMap`: the symbols of
  `L.sum (L₁.sum L₂)` shared by the images of `L.sum L₁` and `L.sum L₂` come from `L`.

Adjoining constants to an algebraic language gives an algebraic language
(`FirstOrder.Language.isAlgebraic_withConstants`).

The relation map of `lhomWithConstants` inverts the elimination of the empty summand of
`L[[γ]].Relations n` by `Equiv.sumEmpty`
(`FirstOrder.Language.lhomWithConstants_onRelation_sumEmpty`), symbol sets of `L[[γ]]` avoiding the
added constants lie in the range of `lhomWithConstants`
(`FirstOrder.Language.subset_range_lhomWithConstants_onFunction`,
`FirstOrder.Language.subset_range_lhomWithConstants_onRelation`), and every `L[[γ]]`-structure is
the expansion of its `L`-reduct by the interpretations of the added constants
(`FirstOrder.Language.withConstantsStructure_reduct_eq`).

A function symbol of `L[[γ]]` is a function symbol of `L` or one of the added constants
(`FirstOrder.Language.sigmaFunctionsWithConstantsEquiv`).

A language equivalence `e : L ≃ᴸ L'` induces equivalences on function and relation symbols of each
arity (`FirstOrder.Language.LEquiv.onFunction`, `FirstOrder.Language.LEquiv.onRelation`), so both
its forward and inverse language homomorphisms are injective
(`FirstOrder.Language.LEquiv.toLHom_injective`, `FirstOrder.Language.LEquiv.invLHom_injective`).
Every language `L : Language.{u, v}` lifts to `L.ulift.{u', v'} : Language.{max u u', max v v'}`
along a language equivalence `L.uliftEquiv.{u', v'}`, preserving relationality, algebraicity and
symbol countability; for `L₀ : Language.{0, 0}` this presents `L₀` in any target universes `u', v'`.
-/

public section

universe u v u' v' u'' v'' w

namespace FirstOrder

namespace Language

namespace LHom

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {L'' : Language.{u'', v''}}

/-- Expansions compose: if the `L'`-structure on `M` expands its `L`-structure along `g`, and the
`L''`-structure expands the `L'`-structure along `h`, then the `L''`-structure expands the
`L`-structure along `h.comp g`. -/
instance comp_isExpansionOn (h : L' →ᴸ L'') (g : L →ᴸ L') (M : Type w) [L.Structure M]
    [L'.Structure M] [L''.Structure M] [g.IsExpansionOn M] [h.IsExpansionOn M] :
    (h.comp g).IsExpansionOn M where
  map_onFunction f x := (h.map_onFunction (g.onFunction f) x).trans (g.map_onFunction f x)
  map_onRelation R x := (h.map_onRelation (g.onRelation R) x).trans (g.map_onRelation R x)

/-- If the `L''`-structure on `M` expands its `L`-structure along `h.comp g`, then its reduct
along `h` expands the `L`-structure along `g`. -/
theorem isExpansionOn_reduct_of_comp (h : L' →ᴸ L'') (g : L →ᴸ L') (M : Type w) [L.Structure M]
    [L''.Structure M] [(h.comp g).IsExpansionOn M] :
    @IsExpansionOn L L' g M _ (h.reduct M) :=
  @IsExpansionOn.mk L L' g M _ (h.reduct M) (fun f x => (h.comp g).map_onFunction f x)
    (fun R x => (h.comp g).map_onRelation R x)

/-- If the `L'`-structure on `M` expands its `L`-structure along `g`, then its reduct along `g` is
the `L`-structure again, in the sense that the identity map expands the reduct to it. -/
theorem id_isExpansionOn_reduct (g : L →ᴸ L') (M : Type w) [L.Structure M] [L'.Structure M]
    [g.IsExpansionOn M] : @IsExpansionOn L L (LHom.id L) M (g.reduct M) _ :=
  @IsExpansionOn.mk L L (LHom.id L) M (g.reduct M) _ (fun f x => (g.map_onFunction f x).symm)
    (fun R x => (g.map_onRelation R x).symm)

/-- A structure on `L.sum L₁` is expanded along `ϕ.sumMap ψ` by the sum of an `L₀`-structure and
an `L₁'`-structure that expand, along `ϕ` and `ψ`, its parts on `L` and on `L₁`. Mathlib's
`LHom.sumMap_isExpansionOn` is the case of a source that is itself a sum structure. -/
theorem sumMap_isExpansionOn_of_reduct {L₀ : Language.{u', v'}} {L₁ : Language.{u'', v''}}
    {L₁' : Language} (ϕ : L →ᴸ L₀) (ψ : L₁ →ᴸ L₁') (M : Type w) [(L.sum L₁).Structure M]
    [L₀.Structure M] [L₁'.Structure M]
    [@IsExpansionOn L L₀ ϕ M ((LHom.sumInl : L →ᴸ L.sum L₁).reduct M) _]
    [@IsExpansionOn L₁ L₁' ψ M ((LHom.sumInr : L₁ →ᴸ L.sum L₁).reduct M) _] :
    (ϕ.sumMap ψ).IsExpansionOn M where
  map_onFunction
    | .inl f, x => @map_onFunction L L₀ ϕ M ((LHom.sumInl : L →ᴸ L.sum L₁).reduct M) _ _ _ f x
    | .inr f, x => @map_onFunction L₁ L₁' ψ M ((LHom.sumInr : L₁ →ᴸ L.sum L₁).reduct M) _ _ _ f x
  map_onRelation
    | .inl R, x => @map_onRelation L L₀ ϕ M ((LHom.sumInl : L →ᴸ L.sum L₁).reduct M) _ _ _ R x
    | .inr R, x => @map_onRelation L₁ L₁' ψ M ((LHom.sumInr : L₁ →ᴸ L.sum L₁).reduct M) _ _ _ R x

section SumMap

variable {L₁ : Language.{u', v'}} {L₂ : Language.{u'', v''}}

/-- A function symbol of `L.sum (L₁.sum L₂)` that is the image of a function symbol of `L.sum L₁`
along `(LHom.id L).sumMap LHom.sumInl` and of a function symbol of `L.sum L₂` along
`(LHom.id L).sumMap LHom.sumInr` is the image of a function symbol of `L` along `LHom.sumInl`. -/
theorem mem_range_sumInl_onFunction_of_mem_range_sumMap {s : Σ k, (L.sum (L₁.sum L₂)).Functions k}
    (h₁ : s ∈ Set.range fun t : Σ k, (L.sum L₁).Functions k =>
      (⟨t.1, ((LHom.id L).sumMap LHom.sumInl).onFunction t.2⟩ :
        Σ k, (L.sum (L₁.sum L₂)).Functions k))
    (h₂ : s ∈ Set.range fun t : Σ k, (L.sum L₂).Functions k =>
      (⟨t.1, ((LHom.id L).sumMap LHom.sumInr).onFunction t.2⟩ :
        Σ k, (L.sum (L₁.sum L₂)).Functions k)) :
    s ∈ Set.range fun t : Σ k, L.Functions k =>
      (⟨t.1, LHom.sumInl.onFunction t.2⟩ : Σ k, (L.sum (L₁.sum L₂)).Functions k) := by
  obtain ⟨⟨k, f | f⟩, rfl⟩ := h₁
  · exact ⟨⟨k, f⟩, rfl⟩
  · obtain ⟨⟨k', f' | f'⟩, h⟩ := h₂ <;> obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 h <;> cases h

/-- A relation symbol of `L.sum (L₁.sum L₂)` that is the image of a relation symbol of `L.sum L₁`
along `(LHom.id L).sumMap LHom.sumInl` and of a relation symbol of `L.sum L₂` along
`(LHom.id L).sumMap LHom.sumInr` is the image of a relation symbol of `L` along `LHom.sumInl`. -/
theorem mem_range_sumInl_onRelation_of_mem_range_sumMap {s : Σ k, (L.sum (L₁.sum L₂)).Relations k}
    (h₁ : s ∈ Set.range fun t : Σ k, (L.sum L₁).Relations k =>
      (⟨t.1, ((LHom.id L).sumMap LHom.sumInl).onRelation t.2⟩ :
        Σ k, (L.sum (L₁.sum L₂)).Relations k))
    (h₂ : s ∈ Set.range fun t : Σ k, (L.sum L₂).Relations k =>
      (⟨t.1, ((LHom.id L).sumMap LHom.sumInr).onRelation t.2⟩ :
        Σ k, (L.sum (L₁.sum L₂)).Relations k)) :
    s ∈ Set.range fun t : Σ k, L.Relations k =>
      (⟨t.1, LHom.sumInl.onRelation t.2⟩ : Σ k, (L.sum (L₁.sum L₂)).Relations k) := by
  obtain ⟨⟨k, R | R⟩, rfl⟩ := h₁
  · exact ⟨⟨k, R⟩, rfl⟩
  · obtain ⟨⟨k', R' | R'⟩, h⟩ := h₂ <;> obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 h <;> cases h

end SumMap

end LHom

end Language

end FirstOrder

namespace FirstOrder.Language

variable {L : Language} {γ : Type*}

/-- Adjoining constants to a language without relation symbols adds no relation symbols. -/
instance isAlgebraic_withConstants [L.IsAlgebraic] : L[[γ]].IsAlgebraic :=
  isAlgebraic_sum

theorem lhomWithConstants_onRelation_sumEmpty {l : ℕ} (R : L[[γ]].Relations l) :
    (L.lhomWithConstants γ).onRelation ((Equiv.sumEmpty _ _) R) = R := by
  -- lhomWithConstants is sumInl, so its relation map restores the left summand.
  cases R with
  | inl R => rfl
  | inr R => exact R.elim

/-- Any set of arity-tagged function symbols of `L[[γ]]` containing none of the added constants
`L.con c` lies in the range of `(L.lhomWithConstants γ).onFunction`. -/
theorem subset_range_lhomWithConstants_onFunction {X : Set (Σ k, L[[γ]].Functions k)}
    (hX : ∀ c, (⟨0, L.con c⟩ : Σ k, L[[γ]].Functions k) ∉ X) :
    X ⊆ Set.range fun s : Σ k, L.Functions k =>
      (⟨s.1, (L.lhomWithConstants γ).onFunction s.2⟩ : Σ k, L[[γ]].Functions k) := by
  rintro ⟨k, f | c⟩ hf
  · exact ⟨⟨k, f⟩, rfl⟩
  · cases k with
    | zero => exact (hX c hf).elim
    | succ k => exact c.elim

/-- Every set of arity-tagged relation symbols of `L[[γ]]` lies in the range of
`(L.lhomWithConstants γ).onRelation`. -/
theorem subset_range_lhomWithConstants_onRelation (Y : Set (Σ k, L[[γ]].Relations k)) :
    Y ⊆ Set.range fun s : Σ k, L.Relations k =>
      (⟨s.1, (L.lhomWithConstants γ).onRelation s.2⟩ : Σ k, L[[γ]].Relations k) := by
  rintro ⟨k, R | R⟩ -
  · exact ⟨⟨k, R⟩, rfl⟩
  · exact R.elim

/-- Every `L[[γ]]`-structure on `M` is the expansion of its `L`-reduct interpreting each `c : γ`
as `(L.con c : M)`. -/
theorem withConstantsStructure_reduct_eq (M : Type*) [S : L[[γ]].Structure M] :
    @withConstantsStructure L M ((L.lhomWithConstants γ).reduct M) γ
      (constantsOn.structure fun c => (L.con c : M)) = S := by
  refine Structure.ext (funext fun k => funext fun f => funext fun xs => ?_)
    (funext fun _ => funext fun | .inl _ => funext fun _ => rfl | .inr R => R.elim)
  rcases f with f | c
  · rfl
  · cases k with | zero => rw [Unique.eq_default xs]; rfl | succ _ => exact c.elim

section WithConstantsSymbols

variable {L : Language.{u, v}} (A : Type w)

/-- A function symbol of `L[[A]]` is a function symbol of `L` or a constant from `A`. -/
def sigmaFunctionsWithConstantsEquiv :
    (Σ n, L[[A]].Functions n) ≃ (Σ n, L.Functions n) ⊕ A where
  toFun
    | ⟨n, Sum.inl f⟩ => Sum.inl ⟨n, f⟩
    | ⟨0, Sum.inr a⟩ => Sum.inr a
  invFun := Sum.elim (fun f => ⟨f.1, Sum.inl f.2⟩) fun a => ⟨0, Sum.inr a⟩
  left_inv := by rintro ⟨_ | _, f | f⟩ <;> first | rfl | exact isEmptyElim f
  right_inv := by rintro (f | a) <;> rfl

@[simp]
theorem sigmaFunctionsWithConstantsEquiv_inl {n : ℕ} (f : L.Functions n) :
    sigmaFunctionsWithConstantsEquiv A ⟨n, (Sum.inl f : L[[A]].Functions n)⟩ = Sum.inl ⟨n, f⟩ :=
  (rfl)

@[simp]
theorem sigmaFunctionsWithConstantsEquiv_con (a : A) :
    sigmaFunctionsWithConstantsEquiv A ⟨0, L.con a⟩ = Sum.inr a :=
  (rfl)

@[simp]
theorem sigmaFunctionsWithConstantsEquiv_inr (a : A) :
    sigmaFunctionsWithConstantsEquiv A ⟨0, (Sum.inr a : L[[A]].Functions 0)⟩ = Sum.inr a :=
  (rfl)

@[simp]
theorem sigmaFunctionsWithConstantsEquiv_symm_inl (f : Σ n, L.Functions n) :
    (sigmaFunctionsWithConstantsEquiv A).symm (Sum.inl f) = ⟨f.1, Sum.inl f.2⟩ :=
  (rfl)

@[simp]
theorem sigmaFunctionsWithConstantsEquiv_symm_inr (a : A) :
    (sigmaFunctionsWithConstantsEquiv (L := L) A).symm (Sum.inr a) = ⟨0, L.con a⟩ :=
  (rfl)

/-- The arity of a function symbol of `L[[A]]`, read off its description as a function symbol
of `L` or a constant from `A`. -/
theorem sumElim_fst_sigmaFunctionsWithConstantsEquiv (s : Σ n, L[[A]].Functions n) :
    Sum.elim Sigma.fst (fun _ => 0) (sigmaFunctionsWithConstantsEquiv A s) = s.1 := by
  rcases s with ⟨_ | _, f | f⟩ <;> first | rfl | exact isEmptyElim f

end WithConstantsSymbols

namespace LEquiv

variable {L : Language.{u, v}} {L' : Language.{u', v'}} (e : L ≃ᴸ L')

/-- The equivalence of arity-`n` function symbols induced by a language equivalence. -/
def onFunction (n : ℕ) : L.Functions n ≃ L'.Functions n where
  toFun f := e.toLHom.onFunction f
  invFun f := e.invLHom.onFunction f
  left_inv f := by
    simpa only [← LHom.comp_onFunction, LHom.id_onFunction, id_eq] using
      congrFun (congrFun (congrArg LHom.onFunction e.left_inv) n) f
  right_inv f := by
    simpa only [← LHom.comp_onFunction, LHom.id_onFunction, id_eq] using
      congrFun (congrFun (congrArg LHom.onFunction e.right_inv) n) f

/-- `LEquiv.onFunction` applies the forward homomorphism on function symbols. -/
@[simp]
theorem onFunction_apply {n : ℕ} (f : L.Functions n) :
    e.onFunction n f = e.toLHom.onFunction f :=
  (rfl)

/-- The inverse of `LEquiv.onFunction` applies the inverse homomorphism on function symbols. -/
@[simp]
theorem onFunction_symm_apply {n : ℕ} (f : L'.Functions n) :
    (e.onFunction n).symm f = e.invLHom.onFunction f :=
  (rfl)

/-- The equivalence of arity-`n` relation symbols induced by a language equivalence. -/
def onRelation (n : ℕ) : L.Relations n ≃ L'.Relations n where
  toFun R := e.toLHom.onRelation R
  invFun R := e.invLHom.onRelation R
  left_inv R := by
    simpa only [← LHom.comp_onRelation, LHom.id_onRelation, id_eq] using
      congrFun (congrFun (congrArg LHom.onRelation e.left_inv) n) R
  right_inv R := by
    simpa only [← LHom.comp_onRelation, LHom.id_onRelation, id_eq] using
      congrFun (congrFun (congrArg LHom.onRelation e.right_inv) n) R

/-- `LEquiv.onRelation` applies the forward homomorphism on relation symbols. -/
@[simp]
theorem onRelation_apply {n : ℕ} (R : L.Relations n) :
    e.onRelation n R = e.toLHom.onRelation R :=
  (rfl)

/-- The inverse of `LEquiv.onRelation` applies the inverse homomorphism on relation symbols. -/
@[simp]
theorem onRelation_symm_apply {n : ℕ} (R : L'.Relations n) :
    (e.onRelation n).symm R = e.invLHom.onRelation R :=
  (rfl)

/-- The forward homomorphism of a language equivalence is injective. -/
theorem toLHom_injective : e.toLHom.Injective where
  onFunction {n} := (LEquiv.onFunction e n).injective
  onRelation {n} := (LEquiv.onRelation e n).injective

/-- The inverse homomorphism of a language equivalence is injective. -/
theorem invLHom_injective : e.invLHom.Injective :=
  e.symm.toLHom_injective

end LEquiv

section ULift

/-- The **universe-lifted presentation** of a language `L : Language.{u, v}`: the language in
`Language.{max u u', max v v'}` whose function and relation symbols of each arity are `ULift`s of
those of `L`. When `L : Language.{0, 0}`, `L.ulift.{u', v'}` has type `Language.{u', v'}`. -/
@[expose] def ulift.{u₁, v₁, u₂, v₂} (L : Language.{u₂, v₂}) :
    Language.{max u₂ u₁, max v₂ v₁} where
  Functions n := ULift.{u₁} (L.Functions n)
  Relations n := ULift.{v₁} (L.Relations n)

/-- The function symbols of `L.ulift` of each arity are `ULift`s of those of `L`. -/
theorem ulift_functions.{u₁, v₁, u₂, v₂} (L : Language.{u₂, v₂}) (n : ℕ) :
    L.ulift.{u₁, v₁}.Functions n = ULift.{u₁} (L.Functions n) :=
  (rfl)

/-- The relation symbols of `L.ulift` of each arity are `ULift`s of those of `L`. -/
theorem ulift_relations.{u₁, v₁, u₂, v₂} (L : Language.{u₂, v₂}) (n : ℕ) :
    L.ulift.{u₁, v₁}.Relations n = ULift.{v₁} (L.Relations n) :=
  (rfl)

/-- The canonical equivalence between `L` and its universe-lifted presentation `L.ulift`. -/
def uliftEquiv.{u₁, v₁, u₂, v₂} (L : Language.{u₂, v₂}) : L ≃ᴸ L.ulift.{u₁, v₁} where
  toLHom := ⟨fun {_} => ULift.up, fun {_} => ULift.up⟩
  invLHom := ⟨fun {_} => ULift.down, fun {_} => ULift.down⟩
  left_inv := LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)
  right_inv := LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)

/-- The forward map of `uliftEquiv` lifts a function symbol with `ULift.up`. -/
@[simp]
theorem uliftEquiv_toLHom_onFunction.{u₁, v₁, u₂, v₂} (L : Language.{u₂, v₂}) {n : ℕ}
    (f : L.Functions n) :
    L.uliftEquiv.{u₁, v₁}.toLHom.onFunction f = ULift.up f :=
  (rfl)

/-- The forward map of `uliftEquiv` lifts a relation symbol with `ULift.up`. -/
@[simp]
theorem uliftEquiv_toLHom_onRelation.{u₁, v₁, u₂, v₂} (L : Language.{u₂, v₂}) {n : ℕ}
    (R : L.Relations n) :
    L.uliftEquiv.{u₁, v₁}.toLHom.onRelation R = ULift.up R :=
  (rfl)

/-- The inverse map of `uliftEquiv` lowers a lifted function symbol with `ULift.down`. -/
@[simp]
theorem uliftEquiv_invLHom_onFunction.{u₁, v₁, u₂, v₂} (L : Language.{u₂, v₂}) {n : ℕ}
    (f : L.ulift.{u₁, v₁}.Functions n) :
    L.uliftEquiv.{u₁, v₁}.invLHom.onFunction f = ULift.down f :=
  (rfl)

/-- The inverse map of `uliftEquiv` lowers a lifted relation symbol with `ULift.down`. -/
@[simp]
theorem uliftEquiv_invLHom_onRelation.{u₁, v₁, u₂, v₂} (L : Language.{u₂, v₂}) {n : ℕ}
    (R : L.ulift.{u₁, v₁}.Relations n) :
    L.uliftEquiv.{u₁, v₁}.invLHom.onRelation R = ULift.down R :=
  (rfl)

/-- Lifting the symbol universes of a relational language preserves `IsRelational`. -/
instance isRelational_ulift.{u₁, v₁, u₂, v₂} (L : Language.{u₂, v₂}) [L.IsRelational] :
    L.ulift.{u₁, v₁}.IsRelational :=
  fun _ => Equiv.ulift.isEmpty

/-- Lifting the symbol universes of an algebraic language preserves `IsAlgebraic`. -/
instance isAlgebraic_ulift.{u₁, v₁, u₂, v₂} (L : Language.{u₂, v₂}) [L.IsAlgebraic] :
    L.ulift.{u₁, v₁}.IsAlgebraic :=
  fun _ => Equiv.ulift.isEmpty

/-- Lifting the symbol universes preserves countability of the arity-tagged function symbols. -/
instance countable_functions_ulift.{u₁, v₁, u₂, v₂} (L : Language.{u₂, v₂})
    [Countable (Σ n, L.Functions n)] :
    Countable (Σ n, L.ulift.{u₁, v₁}.Functions n) :=
  Countable.of_equiv _ (Equiv.sigmaCongrRight fun _ => Equiv.ulift.symm)

/-- Lifting the symbol universes preserves countability of the arity-tagged relation symbols. -/
instance countable_relations_ulift.{u₁, v₁, u₂, v₂} (L : Language.{u₂, v₂})
    [Countable (Σ n, L.Relations n)] :
    Countable (Σ n, L.ulift.{u₁, v₁}.Relations n) :=
  Countable.of_equiv _ (Equiv.sigmaCongrRight fun _ => Equiv.ulift.symm)

end ULift

end FirstOrder.Language
