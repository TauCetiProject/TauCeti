/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.Isomorphism
public import TauCeti.ModelTheory.Infinitary.LanguageMap

/-!
# Relational configurations along language maps

A language map `g : L →ᴸ L'` renames relation symbols arity by arity, so it renames the atoms
`R(v₁, …, vₙ)` over a carrier `V` (`LHom.onAtom`), and every configuration of `L'` on `V` pulls
back to a configuration of `L` on `V` (`LHom.reductConfiguration`): the atom `R(x)` of the reduct
takes the value of the atom `(g R)(x)`. For relational languages this is the coded form of
Mathlib's `LHom.reduct`: the reduct configuration decodes to the reduct of the decoded structure.
It is continuous and measurable on every carrier, commutes with relabelling by permutations of
the carrier, preserves isomorphism, and the reduct satisfies an infinitary formula `φ` of `L`
exactly when the original configuration satisfies its translation `g.onBoundedFormulaInf φ`.

A language equivalence `e : L ≃ᴸ L'` transports configurations both ways
(`LEquiv.onConfiguration`, the reduct along `e.invLHom`), giving a homeomorphism of configuration
spaces that preserves and reflects isomorphism and carries the configurations satisfying a
formula of `L` exactly onto those satisfying its translation. These are the facts that make
counting the models of a sentence up to isomorphism, or finding perfect sets of non-isomorphic
ones, independent of the presentation of the language; with `smallPresentationEquiv`, every
countable relational language can be presented in universe `0`.

## Main definitions

* `FirstOrder.Language.LHom.reductConfiguration`: the reduct of a configuration along a language
  map.
* `FirstOrder.Language.LEquiv.onConfiguration`: the homeomorphism of configuration spaces induced
  by a language equivalence.

## Main results

* `FirstOrder.Language.LHom.toStructure_reductConfiguration`: the reduct configuration decodes to
  the reduct structure.
* `FirstOrder.Language.LHom.reductConfiguration_perm_smul`: reducts commute with the logic action.
* `FirstOrder.Language.LHom.isoSetoid_reductConfiguration`: reducts preserve isomorphism.
* `FirstOrder.Language.LHom.realize_reductConfiguration` and
  `FirstOrder.Language.LHom.realize_sentenceInf_reductConfiguration`: the reduct realizes a
  formula exactly when the configuration realizes its translation.
* `FirstOrder.Language.LHom.reductConfiguration_encodeVia`: reducts commute with encoding a
  structure along a bijection of carriers.
* `FirstOrder.Language.LEquiv.isoSetoid_onConfiguration_iff`: transport along a language
  equivalence preserves and reflects isomorphism.
* `FirstOrder.Language.LEquiv.realize_onConfiguration` and
  `FirstOrder.Language.LEquiv.realize_sentenceInf_onConfiguration`: the transported
  configuration realizes the translation of a formula exactly when the original realizes the
  formula.
-/

public section

universe u v u' v' u'' v'' w w' uι uα

open TauCeti TauCeti.RelationalConfiguration

namespace FirstOrder.Language

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {L'' : Language.{u'', v''}} {V : Type w}

namespace LHom

variable (g : L →ᴸ L')

/-! ### Reducts of configurations -/

/-- The reduct of a configuration of `L'` along a language map `g : L →ᴸ L'`: the configuration of
`L` whose atom `R(x)` takes the value of the atom `(g R)(x)`. -/
def reductConfiguration (c : RelationalConfiguration L' V) : RelationalConfiguration L V :=
  RelationalConfiguration.mk fun a => c.eval (g.onAtom a)

/-- The reduct reads each atom at its renaming along `g`. -/
@[simp]
theorem eval_reductConfiguration (c : RelationalConfiguration L' V) (a : Atom L V) :
    (g.reductConfiguration c).eval a = c.eval (g.onAtom a) :=
  eval_mk _ _

/-- The reduct along the identity map is the configuration itself. -/
@[simp]
theorem id_reductConfiguration (c : RelationalConfiguration L V) :
    (LHom.id L).reductConfiguration c = c :=
  ext fun a => by simp

/-- The reduct along a composite map is the composite of the reducts, in the opposite order. -/
theorem comp_reductConfiguration (g' : L' →ᴸ L'') (c : RelationalConfiguration L'' V) :
    (g'.comp g).reductConfiguration c = g.reductConfiguration (g'.reductConfiguration c) :=
  ext fun a => by simp [comp_onAtom]

/-- Reducts are continuous. -/
@[fun_prop]
theorem continuous_reductConfiguration :
    Continuous (g.reductConfiguration (V := V)) :=
  continuous_iff.2 fun a => by simpa using continuous_eval (g.onAtom a)

/-- Reducts are measurable for the product σ-algebras, on every carrier. -/
@[fun_prop]
theorem measurable_reductConfiguration : Measurable (g.reductConfiguration (V := V)) :=
  measurable_iff.2 fun a => by simpa using measurable_eval (g.onAtom a)

/-- Reducts commute with relabelling by permutations of the carrier: they are equivariant for the
logic action. -/
theorem reductConfiguration_perm_smul (σ : Equiv.Perm V) (c : RelationalConfiguration L' V) :
    g.reductConfiguration (σ • c) = σ • g.reductConfiguration c :=
  ext fun a => by simp [onAtom_map]

/-- Reducts commute with encoding: the reduct of the encoding of a structure along a bijection of
carriers is the encoding of its reduct. -/
theorem reductConfiguration_encodeVia {M : Type w'} [L'.Structure M] (f : M ≃ V) :
    g.reductConfiguration (f.encodeVia (L := L')) = @Equiv.encodeVia L M V (g.reduct M) f := by
  classical
  let := g.reduct M
  ext a
  induction a using Atom.induction_atom with
  | h R x =>
    -- Both sides decide the relation `g R` at `f.symm ∘ x` in `M`.
    simp only [eval_reductConfiguration, onAtom_atom, Equiv.eval_encodeVia]
    rfl

/-! ### Decoding reducts -/

variable [L.IsRelational] [L'.IsRelational]

/-- The reduct configuration decodes to the reduct of the decoded structure along `g`. -/
theorem toStructure_reductConfiguration (c : RelationalConfiguration L' V) :
    (g.reductConfiguration c).toStructure = @LHom.reduct L L' g V c.toStructure := by
  apply Structure.ext
  · funext n f
    exact isEmptyElim f
  · funext n R x
    apply propext
    rw [toStructure_relMap, eval_reductConfiguration, onAtom_atom, ← toStructure_relMap]
    -- `LHom.reduct` reads `R` as `g.onRelation R`; Mathlib states no unfolding lemma for it.
    rfl

/-- Reducts preserve isomorphism of decoded structures. -/
theorem isoSetoid_reductConfiguration {c d : RelationalConfiguration L' V}
    (h : isoSetoid L' V c d) :
    isoSetoid L V (g.reductConfiguration c) (g.reductConfiguration d) := by
  obtain ⟨σ, rfl⟩ := isoSetoid_iff_exists_perm_smul_eq.1 h
  rw [reductConfiguration_perm_smul]
  exact isoSetoid_perm_smul σ _

/-- **Realization in a reduct.** A configuration realizes the translation of an infinitary formula
along `g` exactly when its reduct realizes the formula. -/
theorem realize_reductConfiguration {ι : Type uι} {α : Type uα} {n : ℕ}
    (c : RelationalConfiguration L' V) (φ : L.BoundedFormulaInf ι α n) (v : α → V)
    (xs : Fin n → V) :
    @BoundedFormulaInf.Realize L' ι α V c.toStructure n (g.onBoundedFormulaInf φ) v xs ↔
      @BoundedFormulaInf.Realize L ι α V (g.reductConfiguration c).toStructure n φ v xs := by
  rw [toStructure_reductConfiguration]
  let := c.toStructure
  let := g.reduct V
  exact g.realize_onBoundedFormulaInf φ v xs

/-- **Model classes of reducts.** A configuration satisfies the translation of an infinitary
sentence along `g` exactly when its reduct satisfies the sentence. -/
theorem realize_sentenceInf_reductConfiguration {ι : Type uι} (c : RelationalConfiguration L' V)
    (φ : L.SentenceInf ι) :
    @SentenceInf.Realize L' ι (g.onBoundedFormulaInf φ) V c.toStructure ↔
      @SentenceInf.Realize L ι φ V (g.reductConfiguration c).toStructure := by
  simp only [SentenceInf.realize_def, FormulaInf.realize_def]
  exact g.realize_reductConfiguration c φ _ _

end LHom

namespace LEquiv

variable (e : L ≃ᴸ L')

/-! ### Transport along a language equivalence -/

/-- A language equivalence transports configurations: the atom `(e R)(x)` of the image takes the
value of the atom `R(x)`. The transport is the reduct along `e.invLHom`
(`coe_onConfiguration`), and on every carrier it is a homeomorphism of configuration spaces, with
inverse the transport along `e.symm`. -/
def onConfiguration : RelationalConfiguration L V ≃ₜ RelationalConfiguration L' V where
  toFun := e.invLHom.reductConfiguration
  invFun := e.toLHom.reductConfiguration
  left_inv c := by rw [← LHom.comp_reductConfiguration, e.left_inv, LHom.id_reductConfiguration]
  right_inv c := by rw [← LHom.comp_reductConfiguration, e.right_inv, LHom.id_reductConfiguration]
  continuous_toFun := e.invLHom.continuous_reductConfiguration
  continuous_invFun := e.toLHom.continuous_reductConfiguration

/-- Transport along `e` is the reduct along the inverse map `e.invLHom`. -/
theorem coe_onConfiguration :
    ⇑(e.onConfiguration (V := V)) = e.invLHom.reductConfiguration := (rfl)

/-- The transported configuration reads each atom at its renaming back along `e`. -/
@[simp]
theorem eval_onConfiguration (c : RelationalConfiguration L V) (a : Atom L' V) :
    (e.onConfiguration c).eval a = c.eval (e.invLHom.onAtom a) :=
  e.invLHom.eval_reductConfiguration c a

/-- The reduct along `e.toLHom` undoes transport along `e`. -/
@[simp]
theorem toLHom_reductConfiguration_onConfiguration (c : RelationalConfiguration L V) :
    e.toLHom.reductConfiguration (e.onConfiguration c) = c :=
  e.onConfiguration.symm_apply_apply c

/-- Transport along `e` undoes the reduct along `e.toLHom`. -/
@[simp]
theorem onConfiguration_toLHom_reductConfiguration (d : RelationalConfiguration L' V) :
    e.onConfiguration (e.toLHom.reductConfiguration d) = d :=
  e.onConfiguration.apply_symm_apply d

/-- Transport back along a language equivalence is transport along the inverse equivalence. -/
@[simp]
theorem onConfiguration_symm : (e.onConfiguration (V := V)).symm = e.symm.onConfiguration :=
  (rfl)

/-- Transport along the identity equivalence is the identity. -/
@[simp]
theorem onConfiguration_refl : (LEquiv.refl L).onConfiguration (V := V) = Homeomorph.refl _ :=
  Homeomorph.ext fun c => LHom.id_reductConfiguration c

/-- Transport along a composite equivalence is the composite of the transports. -/
theorem onConfiguration_trans (e' : L' ≃ᴸ L'') :
    (e.trans e').onConfiguration (V := V) = e.onConfiguration.trans e'.onConfiguration :=
  Homeomorph.ext fun c => LHom.comp_reductConfiguration e'.invLHom e.invLHom c

/-- Transport is measurable for the product σ-algebras, on every carrier. Its inverse is the
transport along `e.symm`, so it is measurable too. -/
@[fun_prop]
theorem measurable_onConfiguration : Measurable (e.onConfiguration (V := V)) :=
  e.invLHom.measurable_reductConfiguration

variable [L.IsRelational] [L'.IsRelational]

/-- Transport preserves and reflects isomorphism of decoded structures. -/
theorem isoSetoid_onConfiguration_iff {c d : RelationalConfiguration L V} :
    isoSetoid L' V (e.onConfiguration c) (e.onConfiguration d) ↔ isoSetoid L V c d := by
  refine ⟨fun h => ?_, e.invLHom.isoSetoid_reductConfiguration⟩
  simpa using e.toLHom.isoSetoid_reductConfiguration h

/-- **Realization along transport.** The transported configuration realizes the translation of an
infinitary formula exactly when the original configuration realizes the formula. -/
@[simp]
theorem realize_onConfiguration {ι : Type uι} {α : Type uα} {n : ℕ}
    (c : RelationalConfiguration L V) (φ : L.BoundedFormulaInf ι α n) (v : α → V)
    (xs : Fin n → V) :
    @BoundedFormulaInf.Realize L' ι α V (e.onConfiguration c).toStructure n
        (e.toLHom.onBoundedFormulaInf φ) v xs ↔
      @BoundedFormulaInf.Realize L ι α V c.toStructure n φ v xs := by
  rw [e.toLHom.realize_reductConfiguration, toLHom_reductConfiguration_onConfiguration]

/-- **Model classes along transport.** The transported configuration satisfies the translation of
an infinitary sentence exactly when the original configuration satisfies the sentence. -/
@[simp]
theorem realize_sentenceInf_onConfiguration {ι : Type uι} (c : RelationalConfiguration L V)
    (φ : L.SentenceInf ι) :
    @SentenceInf.Realize L' ι (e.toLHom.onBoundedFormulaInf φ) V
        (e.onConfiguration c).toStructure ↔
      @SentenceInf.Realize L ι φ V c.toStructure := by
  simp only [SentenceInf.realize_def, FormulaInf.realize_def]
  exact e.realize_onConfiguration c φ _ _

end LEquiv

end FirstOrder.Language
