/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.Isomorphism
public import TauCeti.ModelTheory.Infinitary.LanguageMap
public import TauCeti.ModelTheory.RelationalConfiguration.ModelsOf
public import TauCeti.ModelTheory.Sublanguage

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

For symbol sublanguages `symbSublang F R`, the reduct map along `symbSublangIncl F R` is
surjective on configurations (`reductConfiguration_symbSublang_surjective`), and every measurable
set in the product σ-algebra on `RelationalConfiguration L V` is the preimage of a measurable set
in some countable relational symbol sublanguage (`exists_countable_sublanguage_of_measurableSet`).
Disjoint analytic classes also have disjoint reducts in a countable sublanguage. The
coordinate-disagreement argument adapts `exists_countable_relations_separating_continuous`,
formerly a private theorem in `LopezEscobar.lean`. On a countable carrier the reduction can
preserve disjointness of orbits.

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
* `FirstOrder.Language.LHom.modelsOf_onBoundedFormulaInf`: model classes of translated sentences
  are preimages along reduct maps.
* `FirstOrder.Language.LHom.reductConfiguration_encodeVia`: reducts commute with encoding a
  structure along a bijection of carriers.
* `FirstOrder.Language.LEquiv.isoSetoid_onConfiguration_iff`: transport along a language
  equivalence preserves and reflects isomorphism.
* `FirstOrder.Language.LEquiv.realize_onConfiguration` and
  `FirstOrder.Language.LEquiv.realize_sentenceInf_onConfiguration`: the transported
  configuration realizes the translation of a formula exactly when the original realizes the
  formula.
* `FirstOrder.Language.LEquiv.preimage_onConfiguration_modelsOf` and
  `FirstOrder.Language.LEquiv.image_onConfiguration_modelsOf`: transport carries the model class
  of a sentence exactly onto the model class of its translation.
* `TauCeti.RelationalConfiguration.reductConfiguration_symbSublang_surjective`: the reduct map
  along a symbol-sublanguage inclusion is surjective on configurations.
* `TauCeti.RelationalConfiguration.exists_countable_sublanguage_of_measurableSet`: every measurable
  set of configurations is the preimage of a measurable set in a countable relational symbol
  sublanguage.
* `TauCeti.RelationalConfiguration.exists_countable_sublanguage_separating` and
  `TauCeti.RelationalConfiguration.exists_countable_sublanguage_separating_orbits`: a countable
  symbol sublanguage can preserve disjointness or disjointness of orbits of analytic classes.
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

/-- The models of the translation of a sentence along `g` are the configurations whose reduct
along `g` models the sentence. -/
theorem modelsOf_onBoundedFormulaInf {ι : Type uι} (φ : L.SentenceInf ι) :
    modelsOf (V := V) (g.onBoundedFormulaInf φ) = g.reductConfiguration ⁻¹' modelsOf φ :=
  Set.ext fun c => by
    rw [Set.mem_preimage, mem_modelsOf, mem_modelsOf, g.realize_sentenceInf_reductConfiguration]

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

/-- The configurations whose transport along `e` is a model of the translation of `φ` form the
model class of `φ`. -/
@[simp]
theorem preimage_onConfiguration_modelsOf {ι : Type uι} (φ : L.SentenceInf ι) :
    e.onConfiguration ⁻¹' modelsOf (V := V) (e.toLHom.onBoundedFormulaInf φ) = modelsOf φ :=
  Set.ext fun c => by
    rw [Set.mem_preimage, mem_modelsOf, mem_modelsOf, e.realize_sentenceInf_onConfiguration]

/-- Transport along `e` carries the model class of `φ` onto the model class of its translation. -/
@[simp]
theorem image_onConfiguration_modelsOf {ι : Type uι} (φ : L.SentenceInf ι) :
    e.onConfiguration '' modelsOf (V := V) φ = modelsOf (e.toLHom.onBoundedFormulaInf φ) := by
  rw [← e.preimage_onConfiguration_modelsOf φ,
    Set.image_preimage_eq _ e.onConfiguration.surjective]

end LEquiv

end FirstOrder.Language

namespace TauCeti.RelationalConfiguration

open FirstOrder FirstOrder.Language MeasureTheory Set TopologicalSpace
open scoped Pointwise

variable {L : Language.{u, v}} {V : Type w}

/-! ### Symbol-sublanguage reducts -/

/-- Every symbol-sublanguage reduct map on relational configurations is surjective. -/
theorem reductConfiguration_symbSublang_surjective
    (F : Set (Σ n, L.Functions n)) (R : Set (Σ n, L.Relations n)) :
    Function.Surjective ((symbSublangIncl F R).reductConfiguration (V := V)) := by
  classical
  intro c₀
  let S : L.Structure (Option V) :=
    { funMap := fun _ _ => none
      RelMap := fun {n} r x =>
        ∃ (y : Fin n → V) (hr : (⟨n, r⟩ : Σ k, L.Relations k) ∈ R),
          Option.some ∘ y = x ∧ c₀.eval (atom ⟨r, hr⟩ y) = true }
  refine ⟨(@ofStructure L (Option V) S).restrict Option.some, ext fun a => ?_⟩
  induction a using Atom.induction_atom with
  | h r x =>
    have hiff : @Structure.RelMap L (Option V) S _ r.val (Option.some ∘ x) ↔
        c₀.eval (atom r x) = true :=
      ⟨fun ⟨y, _, hy, hc⟩ => by cases (Option.some_injective V).comp_left hy; exact hc,
        fun hc => ⟨x, r.property, rfl, hc⟩⟩
    simp [LHom.eval_reductConfiguration, @eval_ofStructure L (Option V) S, hiff]

/-- Every set in the product σ-algebra on `RelationalConfiguration L V` is the preimage of a
measurable set in a countable relational symbol sublanguage. -/
theorem exists_countable_sublanguage_of_measurableSet
    {D : Set (RelationalConfiguration L V)} (hD : MeasurableSet D) :
    ∃ (R₀ : Set (Σ n, L.Relations n)), R₀.Countable ∧
      ∃ D₀ : Set (RelationalConfiguration (symbSublang ∅ R₀) V),
        MeasurableSet D₀ ∧ D = (symbSublangIncl ∅ R₀).reductConfiguration ⁻¹' D₀ := by
  let m : MeasurableSpace (RelationalConfiguration L V) :=
    { MeasurableSet' E :=
        ∃ (R₀ : Set (Σ n, L.Relations n)), R₀.Countable ∧
          ∃ E₀ : Set (RelationalConfiguration (symbSublang ∅ R₀) V),
            MeasurableSet E₀ ∧ E = (symbSublangIncl ∅ R₀).reductConfiguration ⁻¹' E₀
      measurableSet_empty := ⟨∅, countable_empty, ∅, .empty, rfl⟩
      measurableSet_compl := fun E ⟨R₀, hR₀, E₀, hE₀, hEq⟩ =>
        ⟨R₀, hR₀, E₀ᶜ, hE₀.compl, congrArg compl hEq⟩
      measurableSet_iUnion := fun f hf => by
        choose Rᵢ hRᵢ Eᵢ hEᵢ hEq using hf
        let R₀ : Set (Σ n, L.Relations n) := ⋃ i : ℕ, Rᵢ i
        let incl (i : ℕ) : symbSublang (L := L) ∅ (Rᵢ i) →ᴸ symbSublang ∅ R₀ :=
          { onFunction := fun _ fn => ⟨fn.val, fn.property⟩
            onRelation := fun _ r => ⟨r.val, mem_iUnion_of_mem i r.property⟩ }
        have hcomp (i : ℕ) :
            (symbSublangIncl (L := L) ∅ R₀).comp (incl i) = symbSublangIncl ∅ (Rᵢ i) :=
          LHom.funext (funext fun _ => funext fun _ => by simp [incl])
            (funext fun _ => funext fun _ => by simp [incl])
        refine ⟨R₀, countable_iUnion hRᵢ,
          ⋃ i : ℕ, (incl i).reductConfiguration ⁻¹' Eᵢ i,
          .iUnion fun i => (incl i).measurable_reductConfiguration (hEᵢ i), ?_⟩
        ext c
        simp only [mem_iUnion, mem_preimage, hEq, ← hcomp, LHom.comp_reductConfiguration] }
  have hmeas :
      @Measurable (RelationalConfiguration L V) (RelationalConfiguration L V) m
        instMeasurableSpace id := by
    refine (@measurable_iff L V _ m id).2 fun a => ?_
    induction a using Atom.induction_atom with
    | h R x =>
      intro s hs
      let R₀ : Set (Σ n, L.Relations n) := {⟨_, R⟩}
      let a₀ : Atom (symbSublang (L := L) ∅ R₀) V := atom ⟨R, rfl⟩ x
      refine ⟨R₀, countable_singleton _,
        {c₀ | c₀.eval a₀ ∈ s}, (measurable_eval a₀) hs, ?_⟩
      ext c
      simp [a₀]
  exact hmeas hD

/-- Disjoint analytic classes of configurations have disjoint images in some countable relational
symbol sublanguage. The language and the carrier can both be uncountable. -/
theorem exists_countable_sublanguage_separating
    {A B : Set (RelationalConfiguration L V)} (hA : AnalyticSet A) (hB : AnalyticSet B)
    (hAB : Disjoint A B) :
    ∃ R : Set (Σ n, L.Relations n), R.Countable ∧
      Disjoint ((symbSublangIncl ∅ R).reductConfiguration '' A)
        ((symbSublangIncl ∅ R).reductConfiguration '' B) := by
  obtain ⟨X, _, _, f, hf, rfl⟩ := analyticSet_iff_exists_polishSpace_range.1 hA
  obtain ⟨Y, _, _, g, hg, rfl⟩ := analyticSet_iff_exists_polishSpace_range.1 hB
  let U : Atom L V → Set (X × Y) := fun p =>
    {z | (f z.1).eval p ≠ (g z.2).eval p}
  have hU_open (p : Atom L V) : IsOpen (U p) :=
    isOpen_ne_fun ((continuous_eval _).comp (hf.comp continuous_fst))
      ((continuous_eval _).comp (hg.comp continuous_snd))
  have hU_cover : (⋃ p, U p) = univ := by
    refine eq_univ_iff_forall.2 fun ⟨x, y⟩ => ?_
    have hne : f x ≠ g y := fun h =>
      disjoint_left.1 hAB (h ▸ mem_range_self x) (mem_range_self y)
    obtain ⟨a, ha⟩ : ∃ a : Atom L V, (f x).eval a ≠ (g y).eval a := by
      by_contra! hall
      exact hne (RelationalConfiguration.ext hall)
    exact mem_iUnion.2 ⟨a, ha⟩
  obtain ⟨S, hS, hS_eq⟩ := isOpen_iUnion_countable U hU_open
  rw [hU_cover] at hS_eq
  refine ⟨Atom.symbol '' S, hS.image _, disjoint_left.2 ?_⟩
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩ ⟨_, ⟨y, rfl⟩, hxy⟩
  have hz : (x, y) ∈ ⋃ p ∈ S, U p := hS_eq.symm ▸ mem_univ (x, y)
  obtain ⟨p, hpS, hzp⟩ := mem_iUnion₂.1 hz
  induction p using Atom.induction_atom with
  | h R t =>
    let r : (symbSublang ∅ (Atom.symbol '' S)).Relations _ :=
      ⟨R, ⟨atom R t, hpS, Atom.symbol_atom R t⟩⟩
    have heval := congrArg (fun c => c.eval (atom r t)) hxy
    simp only [LHom.eval_reductConfiguration, LHom.onAtom_atom, symbSublangIncl_onRelation, r]
      at heval
    exact hzp heval.symm

/-- On a countable carrier, analytic classes sharing no orbit have reducts to a countable
relational symbol sublanguage that still share no orbit. Neither class need be invariant. -/
theorem exists_countable_sublanguage_separating_orbits [Countable V]
    {A B : Set (RelationalConfiguration L V)} (hA : AnalyticSet A) (hB : AnalyticSet B)
    (hAB : ∀ a ∈ A, ∀ b ∈ B,
      ¬ MulAction.orbitRel (Equiv.Perm V) (RelationalConfiguration L V) a b) :
    ∃ R : Set (Σ n, L.Relations n), R.Countable ∧
      ∀ a ∈ A, ∀ b ∈ B,
        ¬ MulAction.orbitRel (Equiv.Perm V) (RelationalConfiguration (symbSublang ∅ R) V)
          ((symbSublangIncl ∅ R).reductConfiguration a)
          ((symbSublangIncl ∅ R).reductConfiguration b) := by
  have hdisj : Disjoint A (⋃ σ : Equiv.Perm V, σ • B) := by
    refine disjoint_left.2 fun a ha hb => ?_
    obtain ⟨σ, hσ⟩ := mem_iUnion.1 hb
    obtain ⟨b, hbB, rfl⟩ := mem_smul_set.1 hσ
    exact hAB _ ha b hbB (MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2 ⟨σ, rfl⟩))
  obtain ⟨R, hR, hsep⟩ :=
    exists_countable_sublanguage_separating hA (analyticSet_iUnion_smul hB) hdisj
  refine ⟨R, hR, fun a ha b hb hab => ?_⟩
  obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hab)
  exact disjoint_left.1 hsep ⟨a, ha, rfl⟩
    ⟨σ • b, mem_iUnion.2 ⟨σ, smul_mem_smul_set hb⟩,
      ((symbSublangIncl ∅ R).reductConfiguration_perm_smul σ b).trans hσ⟩

end TauCeti.RelationalConfiguration
