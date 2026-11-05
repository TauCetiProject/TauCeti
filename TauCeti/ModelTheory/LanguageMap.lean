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

The relation map of `lhomWithConstants` inverts the elimination of the empty summand of
`L[[γ]].Relations n` by `Equiv.sumEmpty`
(`FirstOrder.Language.lhomWithConstants_onRelation_sumEmpty`), symbol sets of `L[[γ]]` avoiding the
added constants lie in the range of `lhomWithConstants`
(`FirstOrder.Language.subset_range_lhomWithConstants_onFunction`,
`FirstOrder.Language.subset_range_lhomWithConstants_onRelation`), and every `L[[γ]]`-structure is
the expansion of its `L`-reduct by the interpretations of the added constants
(`FirstOrder.Language.withConstantsStructure_reduct_eq`).
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

end LHom

end Language

end FirstOrder

namespace FirstOrder.Language

variable {L : Language} {γ : Type*}

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

end FirstOrder.Language
