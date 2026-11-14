/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Interpolation.Craig
public import TauCeti.ModelTheory.RelationalConfiguration.Isomorphism
public import TauCeti.ModelTheory.RelationalConfiguration.ModelsOf
import TauCeti.ModelTheory.Infinitary.CodedConnectives

/-!
# The López–Escobar theorem and analytic invariant separation

On a countable carrier `V` in a relational language `L`, the model class `modelsOf θ` of every
`L_{ω₁ω}` sentence `θ` is Borel (`measurableSet_modelsOf`) and invariant under isomorphism
(`isomorphismInvariant_modelsOf`). E. G. K. López-Escobar's theorem (1965) proves the converse when
`L` has countably many relation symbols of each arity: every isomorphism-invariant Borel set of
configurations on `V` is `modelsOf θ` for a single `L_{ω₁ω}` sentence `θ`
(`measurableSet_and_isomorphismInvariant_iff_exists_modelsOf`).

Following Marker, we deduce López-Escobar's theorem from a stronger separation theorem for analytic
sets (`exists_sentence_separating`): if `A` and `B` are analytic sets of configurations on `V` and
no isomorphism class meets both, then some `L_{ω₁ω}` sentence `θ` holds on all of `A` and fails on
all of `B`. In particular, if either `A` or `B` is isomorphism invariant and `Disjoint A B`, a
single `L_{ω₁ω}` sentence separates them (`exists_sentence_separating_of_isomorphismInvariant`), and
an isomorphism-invariant bi-analytic set is the model class of a sentence
(`exists_modelsOf_eq_of_analyticSet_compl`).

The proof of `exists_sentence_separating` splits into two cases according to whether `V` is empty:

* On an empty carrier (`[IsEmpty V]`), every permutation is trivial, so isomorphism of
  configurations is equality (`isoSetoid_eq_bot_of_isEmpty`). Moreover, positive-arity atoms do not
  exist, and each nullary atom coordinate is read by a quantifier-free relational sentence; hence
  every set in the product σ-algebra on `RelationalConfiguration L V` is already `modelsOf θ` for
  some `θ : L.Sentenceω` (`exists_modelsOf_eq_of_measurableSet_of_isEmpty`), with no countability
  assumption on `L`. In a countable relational vocabulary, Lusin's separation theorem
  (`MeasureTheory.AnalyticSet.measurablySeparable`) separates `A` and `B` by a Borel set, which is
  then `modelsOf θ`.
* On a nonempty countable carrier (`[Nonempty V]`), non-trivial analytic sets `A` and `B` are
  continuous images `Set.range f` and `Set.range g` of Baire space `ℕ → ℕ`. Adjoining constants for
  the elements of `V` and nullary predicates for the graph of a Baire-space witness `z : ℕ → ℕ`
  expresses the isomorphism saturation of `Set.range f` as a `PC_{ω₁ω}` class: constants name the
  carrier bijectively, nullary predicates trace out a single function `z : ℕ → ℕ`, and for each atom
  `R(x)` the open preimage `{z | (f z).eval (atom R x) = true}` is a countable union of basic
  cylinders. Disjointness of isomorphism saturations means the two `PC_{ω₁ω}` classes share no
  countable nonempty model, so projective-class separation (`FirstOrder.Language.pcSeparation`)
  produces a separating `L_{ω₁ω}` sentence.

Finally, pulling analytic sets forward along a measurable map `f : X → RelationalConfiguration L V`
from an arbitrary standard Borel space `X` (`MeasurableSet.analyticSet_image`) yields **relative
separation** (`exists_sentence_separating_preimage`) and **relative López–Escobar**
(`exists_modelsOf_preimage_eq`): any Borel subset `U ⊆ X` closed under `f`-isomorphism is the
preimage `f ⁻¹' modelsOf θ` of a single `L_{ω₁ω}` sentence `θ`.

## Main results

* `TauCeti.RelationalConfiguration.isomorphismInvariant_modelsOf`: model classes of infinitary
  sentences are isomorphism invariant.
* `TauCeti.RelationalConfiguration.exists_modelsOf_eq_of_measurableSet_of_isEmpty`: on an empty
  carrier, every measurable set of configurations is `modelsOf θ` for some `θ : L.Sentenceω`.
* `TauCeti.RelationalConfiguration.exists_sentence_separating` and
  `TauCeti.RelationalConfiguration.exists_sentence_separating_of_isomorphismInvariant`: analytic
  sets with disjoint isomorphism saturations are separated by a single `L_{ω₁ω}` sentence.
* `TauCeti.RelationalConfiguration.exists_modelsOf_eq_of_analyticSet_compl`: isomorphism-invariant
  bi-analytic sets are model classes of `L_{ω₁ω}` sentences.
* `TauCeti.RelationalConfiguration.measurableSet_and_isomorphismInvariant_iff_exists_modelsOf`:
  **the López–Escobar theorem**.
* `TauCeti.RelationalConfiguration.exists_sentence_separating_preimage` and
  `TauCeti.RelationalConfiguration.exists_modelsOf_preimage_eq`: relative separation and relative
  López–Escobar along measurable maps from standard Borel spaces.

## References

* E. G. K. López-Escobar, *An interpolation theorem for denumerably long formulas*, Fund. Math. 57
  (1965), 253–272.
* David Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46, Cambridge
  University Press, 2016, Chapter 4 (López-Escobar's theorem via `PC_{ω₁ω}` separation).
* Su Gao, *Invariant Descriptive Set Theory*, Chapman & Hall/CRC, 2009, §11.3.
* Alexander S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, Theorem 16.8.
* Related formalizations of López-Escobar's theorem and its relative form on `ℕ` appear in
  `InfinitaryLogic/ModelTheory/LopezEscobar.lean` and
  `InfinitaryLogic/ModelTheory/RelativeLopezEscobar.lean` of Cameron Freer's
  `cameronfreer/infinitary-logic` (checkpoint `518a366cba97b1ae8c4dc64a297a396939bc3e0b`,
  Apache-2.0). Here the theorem is proved directly on `RelationalConfiguration L V` for any
  countable carrier `V` (empty, finite, or infinite) in any universe, from analytic invariant
  separation via `pcSeparation`, and relativized to arbitrary standard Borel parameter spaces.
-/

public section

universe u v w uι

open FirstOrder FirstOrder.Language MeasureTheory Set

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w} {ι : Type uι}

/-! ### Isomorphism invariance of model classes and disjointness of saturations -/

/-- The model class of an infinitary sentence is invariant under isomorphism of configurations. -/
theorem isomorphismInvariant_modelsOf (φ : L.SentenceInf ι) :
    IsomorphismInvariant (modelsOf (V := V) φ) := by
  rw [isomorphismInvariant_iff]
  rintro c d h hc
  obtain ⟨e⟩ := isoSetoid_apply.1 h
  exact (Language.Equiv.mem_modelsOf_iff e φ).mp hc

/-- If `B` is isomorphism invariant and disjoint from `A`, no isomorphism class meets both `A` and
`B`. -/
theorem IsomorphismInvariant.disjoint_image_quotientMk_right
    {A B : Set (RelationalConfiguration L V)} (hB : IsomorphismInvariant B) (hAB : Disjoint A B) :
    Disjoint (Quotient.mk (isoSetoid L V) '' A) (Quotient.mk (isoSetoid L V) '' B) := by
  rwa [disjoint_image_left, isomorphismInvariant_iff_preimage_image_quotientMk.1 hB]

/-- If `A` is isomorphism invariant and disjoint from `B`, no isomorphism class meets both `A` and
`B`. -/
theorem IsomorphismInvariant.disjoint_image_quotientMk_left
    {A B : Set (RelationalConfiguration L V)} (hA : IsomorphismInvariant A) (hAB : Disjoint A B) :
    Disjoint (Quotient.mk (isoSetoid L V) '' A) (Quotient.mk (isoSetoid L V) '' B) :=
  (hA.disjoint_image_quotientMk_right hAB.symm).symm

/-! ### Empty carriers -/

/-- On an empty carrier, two relational configurations are isomorphic if and only if they are
equal. -/
@[simp]
theorem isoSetoid_iff_eq_of_isEmpty [IsEmpty V] {c d : RelationalConfiguration L V} :
    isoSetoid L V c d ↔ c = d := by
  rw [isoSetoid_iff_exists_perm_smul_eq]
  refine ⟨fun ⟨σ, hσ⟩ => ?_, fun h => ⟨1, by simp [h]⟩⟩
  have hσ1 : σ = 1 := Equiv.ext isEmptyElim
  simpa [hσ1] using hσ

/-- On an empty carrier, the isomorphism setoid on relational configurations is equality. -/
theorem isoSetoid_eq_bot_of_isEmpty [IsEmpty V] : isoSetoid L V = ⊥ := by
  ext c d
  exact isoSetoid_iff_eq_of_isEmpty

/-- On an empty carrier, every set of configurations in the product σ-algebra is the model class of
an `L_{ω₁ω}` sentence. No countability assumption on `L` is needed. -/
theorem exists_modelsOf_eq_of_measurableSet_of_isEmpty [IsEmpty V]
    {A : Set (RelationalConfiguration L V)} (hA : MeasurableSet A) :
    ∃ θ : L.Sentenceω, modelsOf (V := V) θ = A := by
  -- The subsets of `RelationalConfiguration L V` defined by `L_{ω₁ω}` sentences form a σ-algebra.
  let m : MeasurableSpace (RelationalConfiguration L V) :=
    { MeasurableSet' S := ∃ θ : L.Sentenceω, modelsOf (V := V) θ = S
      measurableSet_empty := ⟨⊥, modelsOf_bot⟩
      measurableSet_compl := fun S ⟨θ, hθ⟩ => ⟨θ.not, by rw [modelsOf_not, hθ]⟩
      measurableSet_iUnion := fun f hf => by
        choose θ hθ using hf
        exact ⟨BoundedFormulaInf.iSup θ, by simp [hθ]⟩ }
  suffices hid : @Measurable (RelationalConfiguration L V) (RelationalConfiguration L V)
      m instMeasurableSpace id from hid hA
  rw [@measurable_iff L V (RelationalConfiguration L V) m id]
  intro a
  induction a using Atom.induction_atom with
  | h R x =>
    rename_i k
    cases k with
    | succ k => exact isEmptyElim (x 0)
    | zero =>
      have hx : x = Fin.elim0 := Subsingleton.elim _ _
      subst hx
      let φ₀ : L.Sentenceω := .rel R Fin.elim0
      have hφ₀ (c : RelationalConfiguration L V) :
          c ∈ modelsOf φ₀ ↔ c.eval (atom R Fin.elim0) = true := by
        let : L.Structure V := c.toStructure
        rw [mem_modelsOf, SentenceInf.realize_def, FormulaInf.realize_def,
          BoundedFormulaInf.realize_rel, ← toStructure_relMap]
        exact iff_of_eq (congrArg _ (Subsingleton.elim _ _))
      intro s _
      by_cases ht : true ∈ s <;> by_cases hf : false ∈ s
      · refine ⟨⊤, ?_⟩
        ext c
        simp only [modelsOf_top, mem_univ, mem_preimage, id_eq, true_iff]
        cases hc : c.eval (atom R Fin.elim0) <;> simp [ht, hf]
      · refine ⟨φ₀, ?_⟩
        ext c
        rw [hφ₀, mem_preimage, id_eq]
        cases hc : c.eval (atom R Fin.elim0) <;> simp [ht, hf]
      · refine ⟨φ₀.not, ?_⟩
        ext c
        rw [modelsOf_not, mem_compl_iff, hφ₀, mem_preimage, id_eq]
        cases hc : c.eval (atom R Fin.elim0) <;> simp [ht, hf]
      · refine ⟨⊥, ?_⟩
        ext c
        simp only [modelsOf_bot, mem_empty_iff_false, mem_preimage, id_eq, false_iff]
        cases hc : c.eval (atom R Fin.elim0) <;> simp [ht, hf]

/-! ### `PC_{ω₁ω}` presentation of continuous Baire-space images -/

section PCSentence

omit [L.IsRelational] in
/-- Every nonempty analytic set in a topological space is the range of a continuous map from Baire
space `ℕ → ℕ`. -/
private theorem exists_continuous_range_eq_of_analyticSet {α : Type*} [TopologicalSpace α]
    {s : Set α} (hs : AnalyticSet s) (hne : s.Nonempty) :
    ∃ f : (ℕ → ℕ) → α, Continuous f ∧ range f = s := by
  obtain ⟨γ, _, _, f, hf, rfl⟩ := analyticSet_iff_exists_polishSpace_range.1 hs
  obtain ⟨_, x₀, -⟩ := hne
  have : Nonempty γ := ⟨x₀⟩
  obtain ⟨g, hg, hgs⟩ := PolishSpace.exists_nat_nat_continuous_surjective γ
  exact ⟨f ∘ g, hf.comp hg, hgs.range_comp f⟩

/-- Basic clopen cylinder in Baire space `ℕ → ℕ` determined by a finite set of coordinate-value
pairs. -/
private def baireCylinder (p : Finset (ℕ × ℕ)) : Set (ℕ → ℕ) :=
  {z | ∀ q ∈ p, z q.1 = q.2}

omit [L.IsRelational] in
/-- An open subset of Baire space `ℕ → ℕ` is the union of the finite coordinate cylinders contained
in it. -/
private theorem mem_open_iff_exists_baireCylinder {U : Set (ℕ → ℕ)} (hU : IsOpen U) (z : ℕ → ℕ) :
    z ∈ U ↔ ∃ p : {p : Finset (ℕ × ℕ) // baireCylinder p ⊆ U}, z ∈ baireCylinder p.1 := by
  refine ⟨fun hz => ?_, fun ⟨p, hp⟩ => p.2 hp⟩
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 hU z hz
  refine ⟨⟨I.image fun i => (i, z i), fun z' hz' => hsub fun i hi => ?_⟩, ?_⟩
  · rw [hz' (i, z i) (Finset.mem_image_of_mem _ hi)]
    exact (hu i hi).2
  · rintro _ hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    rfl

/-- Auxiliary vocabulary naming the vertices of `V` by constants and the graph of a Baire-space
point `z : ℕ → ℕ` by nullary relation symbols indexed by `ℕ × ℕ`. -/
private abbrev witnessLang (V : Type w) : Language.{w, 0} where
  Functions
    | 0 => V
    | _ + 1 => PEmpty.{w + 1}
  Relations
    | 0 => ℕ × ℕ
    | _ + 1 => PEmpty.{1}

/-- The constant symbol in `L.sum (witnessLang V)` naming `v : V`. -/
private abbrev vSym (v : V) : (L.sum (witnessLang V)).Functions 0 :=
  (LHom.sumInr : witnessLang V →ᴸ L.sum (witnessLang V)).onFunction (n := 0) v

/-- The nullary relation symbol in `L.sum (witnessLang V)` naming `q : ℕ × ℕ`. -/
private abbrev qSym (q : ℕ × ℕ) : (L.sum (witnessLang V)).Relations 0 :=
  (LHom.sumInr : witnessLang V →ᴸ L.sum (witnessLang V)).onRelation (n := 0) q

/-- The constant term in `L.sum (witnessLang V)` naming `v : V`. -/
private def vConst {n : ℕ} (v : V) : (L.sum (witnessLang V)).Term (Empty ⊕ Fin n) :=
  .func (vSym v) Fin.elim0

omit [L.IsRelational] in
@[simp]
private theorem realize_vConst {M : Type*} [(L.sum (witnessLang V)).Structure M]
    {n : ℕ} (v : V) (e : Empty ⊕ Fin n → M) :
    (vConst (L := L) v).realize e =
      Structure.funMap (vSym (L := L) v) (Fin.elim0 : Fin 0 → M) := by
  rw [vConst, Term.realize_func]
  exact congrArg _ (Subsingleton.elim _ _)

/-- Nullary atomic sentence in `L.sum (witnessLang V)` asserting `z q.1 = q.2`. -/
private def baireAtom (q : ℕ × ℕ) : (L.sum (witnessLang V)).Sentenceω :=
  .rel (qSym q) Fin.elim0

omit [L.IsRelational] in
@[simp]
private theorem realize_baireAtom {M : Type*} [(L.sum (witnessLang V)).Structure M] (q : ℕ × ℕ) :
    SentenceInf.Realize (baireAtom (L := L) (V := V) q) M ↔
      Structure.RelMap (qSym (L := L) (V := V) q) (Fin.elim0 : Fin 0 → M) := by
  rw [baireAtom, SentenceInf.realize_def, FormulaInf.realize_def, BoundedFormulaInf.realize_rel]
  exact iff_of_eq (congrArg _ (Subsingleton.elim _ _))

/-- Atomic sentence in `L.sum (witnessLang V)` evaluating an `L`-relation `R` on the constants
naming a tuple `x`. -/
private def relOnConsts {k : ℕ} (R : L.Relations k) (x : Fin k → V) :
    (L.sum (witnessLang V)).Sentenceω :=
  .rel ((LHom.sumInl : L →ᴸ L.sum (witnessLang V)).onRelation R) fun i => vConst (x i)

omit [L.IsRelational] in
@[simp]
private theorem realize_relOnConsts {M : Type*} [iM : L.Structure M]
    [S : (L.sum (witnessLang V)).Structure M]
    [@LHom.IsExpansionOn L (L.sum (witnessLang V)) LHom.sumInl M iM S]
    {k : ℕ} (R : L.Relations k) (x : Fin k → V) :
    @SentenceInf.Realize _ ℕ (relOnConsts (V := V) R x) M S ↔
      @Structure.RelMap L M iM k R
        (fun i => @Structure.funMap (L.sum (witnessLang V)) M S 0 (vSym (x i)) Fin.elim0) := by
  rw [relOnConsts, SentenceInf.realize_def, FormulaInf.realize_def, BoundedFormulaInf.realize_rel]
  simp only [realize_vConst]
  exact iff_of_eq <| @LHom.map_onRelation L (L.sum (witnessLang V)) LHom.sumInl M iM S _ k R
    (fun i => @Structure.funMap (L.sum (witnessLang V)) M S 0 (vSym (x i)) Fin.elim0)

/-- Noncomputable index coding into `ℕ` for any countable index type. -/
private noncomputable def natCoding (α : Type*) [Countable α] : IndexCoding α ℕ :=
  IndexCoding.ofEncodableWith (Encodable.ofCountable α)

/-- Sentence in `L.sum (witnessLang V)` expressing membership of the encoded Baire-space point in an
open set `U ⊆ (ℕ → ℕ)` as a countable disjunction of finite conjunctions of `baireAtom`s. -/
private noncomputable def openSetSentence (U : Set (ℕ → ℕ)) :
    (L.sum (witnessLang V)).Sentenceω :=
  BoundedFormulaInf.iSupAlong (natCoding {p : Finset (ℕ × ℕ) // baireCylinder p ⊆ U})
    fun p => (p.1.toList.map baireAtom).foldr (· ⊓ ·) ⊤

omit [L.IsRelational] in
private theorem realize_openSetSentence_iff {M : Type*} [(L.sum (witnessLang V)).Structure M]
    {U : Set (ℕ → ℕ)} (hU : IsOpen U) {z : ℕ → ℕ}
    (hz : ∀ q : ℕ × ℕ,
      Structure.RelMap (qSym (L := L) (V := V) q) (Fin.elim0 : Fin 0 → M) ↔ z q.1 = q.2) :
    SentenceInf.Realize (openSetSentence (L := L) (V := V) U) M ↔ z ∈ U := by
  rw [openSetSentence, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_iSupAlong, mem_open_iff_exists_baireCylinder hU z]
  refine exists_congr fun p => ?_
  rw [BoundedFormulaInf.realize_foldr_inf]
  simp only [List.mem_map, Finset.mem_toList, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  refine forall₂_congr fun q _ => ?_
  have hba := realize_baireAtom (L := L) (V := V) (M := M) q
  simpa [SentenceInf.realize_def, FormulaInf.realize_def] using hba.trans (hz q)

/-- `L_{ω₁ω}` sentence in `L.sum (witnessLang V)` presenting the isomorphism saturation of
`Set.range f` as a `PC_{ω₁ω}` class: the constants `V` biject with the carrier, the nullary
relations `ℕ × ℕ` form the graph of a point `z : ℕ → ℕ`, and every atom `R(x)` holds on the named
elements iff `z` lies in `{z' | (f z').eval (atom R x) = true}`. -/
private noncomputable def pcSentence [∀ n, Countable (L.Relations n)] [Countable V]
    (f : (ℕ → ℕ) → RelationalConfiguration L V) : (L.sum (witnessLang V)).Sentenceω :=
  let injSent : (L.sum (witnessLang V)).Sentenceω :=
    BoundedFormulaInf.iInfAlong (natCoding {p : V × V // p.1 ≠ p.2})
      fun p => (BoundedFormulaInf.equal (vConst p.1.1) (vConst p.1.2)).not
  let surjSent : (L.sum (witnessLang V)).Sentenceω :=
    BoundedFormulaInf.all <|
      BoundedFormulaInf.iSupAlong (natCoding V) fun v =>
        BoundedFormulaInf.equal (.var (Sum.inr 0)) (vConst v)
  let funcSent : (L.sum (witnessLang V)).Sentenceω :=
    BoundedFormulaInf.iInf fun m : ℕ =>
      (BoundedFormulaInf.iSup fun n : ℕ => baireAtom (m, n)) ⊓
        BoundedFormulaInf.iInf fun n₁ : ℕ =>
          BoundedFormulaInf.iInf fun n₂ : ℕ =>
            if n₁ = n₂ then ⊤ else (baireAtom (m, n₁) ⊓ baireAtom (m, n₂)).not
  let atomSent : (L.sum (witnessLang V)).Sentenceω :=
    BoundedFormulaInf.iInf fun k : ℕ =>
      BoundedFormulaInf.iInfAlong (natCoding (L.Relations k × (Fin k → V))) fun p =>
        (relOnConsts p.1 p.2).iff
          (openSetSentence {z : ℕ → ℕ | (f z).eval (atom p.1 p.2) = true})
  (injSent ⊓ surjSent) ⊓ (funcSent ⊓ atomSent)

/-- An `L`-structure `M` belongs to the projective class of `pcSentence f` along `LHom.sumInl` if
and only if `M` is isomorphic to `(f z).toStructure` for some `z : ℕ → ℕ`. -/
private theorem pcMem_pcSentence_iff [∀ n, Countable (L.Relations n)] [Countable V]
    {f : (ℕ → ℕ) → RelationalConfiguration L V} (hf : Continuous f)
    {M : Type*} [iM : L.Structure M] :
    (LHom.sumInl : L →ᴸ L.sum (witnessLang V)).PCMem (pcSentence f) M ↔
      ∃ c ∈ range f, Nonempty (@Language.Equiv L V M c.toStructure iM) := by
  have hOpen (a : Atom L V) : IsOpen {z : ℕ → ℕ | (f z).eval a = true} :=
    (isOpen_discrete ({true} : Set Bool)).preimage ((continuous_eval a).comp hf)
  rw [LHom.pcMem_iff]
  constructor
  · rintro ⟨S, hS, hΘ⟩
    let : (L.sum (witnessLang V)).Structure M := S
    let : @LHom.IsExpansionOn L (L.sum (witnessLang V)) LHom.sumInl M iM S := hS
    rw [pcSentence, SentenceInf.realize_inf, SentenceInf.realize_inf, SentenceInf.realize_inf] at hΘ
    obtain ⟨⟨hinjS, hsurjS⟩, ⟨hfuncS, hatomS⟩⟩ := hΘ
    let val : V → M := fun v =>
      @Structure.funMap (L.sum (witnessLang V)) M S 0 (vSym v) Fin.elim0
    -- Constants `v : V` interpret injectively and surjectively in `M`.
    have hinj : Function.Injective val := by
      intro u w huw
      by_contra hne
      rw [SentenceInf.realize_def, FormulaInf.realize_def,
        BoundedFormulaInf.realize_iInfAlong] at hinjS
      have hp := hinjS ⟨(u, w), hne⟩
      simp only [BoundedFormulaInf.realize_not, BoundedFormulaInf.realize_equal,
        realize_vConst] at hp
      exact hp huw
    have hsurj : Function.Surjective val := by
      intro m
      rw [SentenceInf.realize_def, FormulaInf.realize_def, BoundedFormulaInf.realize_all] at hsurjS
      have hm := hsurjS m
      rw [BoundedFormulaInf.realize_iSupAlong] at hm
      obtain ⟨v, hv⟩ := hm
      simp only [BoundedFormulaInf.realize_equal, Term.realize_var, Sum.elim_inr,
        realize_vConst] at hv
      exact ⟨v, hv.symm⟩
    -- Nullary predicates `ℕ × ℕ` define the graph of a single point `z : ℕ → ℕ`.
    rw [SentenceInf.realize_iInf] at hfuncS
    have htot (m : ℕ) : ∃ n : ℕ,
        @Structure.RelMap (L.sum (witnessLang V)) M S 0 (qSym (m, n)) Fin.elim0 := by
      have hm := (SentenceInf.realize_inf.1 (hfuncS m)).1
      rw [SentenceInf.realize_iSup] at hm
      obtain ⟨n, hn⟩ := hm
      exact ⟨n, (realize_baireAtom (L := L) (V := V) (M := M) (m, n)).1 hn⟩
    choose z hz using htot
    have hgraph (q : ℕ × ℕ) :
        @Structure.RelMap (L.sum (witnessLang V)) M S 0 (qSym q) Fin.elim0 ↔ z q.1 = q.2 := by
      rcases q with ⟨m, n⟩
      refine ⟨fun hq => ?_, fun hmn => ?_⟩
      · by_contra hne
        have hm := (SentenceInf.realize_inf.1 (hfuncS m)).2
        rw [SentenceInf.realize_iInf] at hm
        have hm₁ := hm (z m)
        rw [SentenceInf.realize_iInf] at hm₁
        have hm₂ := hm₁ n
        simp only [hne, ↓reduceIte, SentenceInf.realize_not, SentenceInf.realize_inf,
          realize_baireAtom] at hm₂
        exact hm₂ ⟨hz m, hq⟩
      · dsimp only at hmn
        exact hmn ▸ hz m
    -- Assemble the `L`-isomorphism `(f z).toStructure ≃[L] M` from `Equiv.ofBijective val`.
    let eV : V ≃ M := Equiv.ofBijective val ⟨hinj, hsurj⟩
    refine ⟨f z, mem_range_self z, ⟨?_⟩⟩
    let : L.Structure V := (f z).toStructure
    refine
      { toEquiv := eV
        map_fun' := fun {k} fn _ => isEmptyElim fn
        map_rel' := fun {k} R x => ?_ }
    rw [SentenceInf.realize_iInf] at hatomS
    have hk := hatomS k
    rw [SentenceInf.realize_def, FormulaInf.realize_def,
      BoundedFormulaInf.realize_iInfAlong] at hk
    have ha : @SentenceInf.Realize _ ℕ (relOnConsts (V := V) R x) M S ↔
        @SentenceInf.Realize _ ℕ
          (openSetSentence (L := L) (V := V) {z : ℕ → ℕ | (f z).eval (atom R x) = true}) M S := by
      simpa [SentenceInf.realize_def, FormulaInf.realize_def] using hk (R, x)
    have hrel := (realize_relOnConsts (V := V) R x).symm.trans <|
      ha.trans (realize_openSetSentence_iff (L := L) (V := V) (hOpen (atom R x)) hgraph)
    simpa [eV, val, Function.comp_def, toStructure_relMap] using hrel
  · rintro ⟨_, ⟨z, rfl⟩, ⟨e⟩⟩
    -- Expand `M` by interpreting constants via `e` and nullary predicates via the graph of `z`.
    let : L.Structure V := (f z).toStructure
    let : (witnessLang V).Structure M :=
      { funMap := fun {k} fn _ =>
          match k, fn with
          | 0, v => e v
          | _ + 1, p => p.elim
        RelMap := fun {k} rl _ =>
          match k, rl with
          | 0, q => z q.1 = q.2
          | _ + 1, p => p.elim }
    refine ⟨_, inferInstance, ?_⟩
    have hval (v : V) :
        @Structure.funMap (L.sum (witnessLang V)) M _ 0 (vSym v) Fin.elim0 = e v := rfl
    have hgraph (q : ℕ × ℕ) :
        @Structure.RelMap (L.sum (witnessLang V)) M _ 0 (qSym q) Fin.elim0 ↔ z q.1 = q.2 :=
      Iff.rfl
    rw [pcSentence, SentenceInf.realize_inf, SentenceInf.realize_inf, SentenceInf.realize_inf]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [SentenceInf.realize_def, FormulaInf.realize_def, BoundedFormulaInf.realize_iInfAlong]
      rintro ⟨⟨u, w⟩, hne⟩
      simp only [BoundedFormulaInf.realize_not, BoundedFormulaInf.realize_equal, realize_vConst,
        hval]
      exact fun heq => hne (e.injective heq)
    · rw [SentenceInf.realize_def, FormulaInf.realize_def, BoundedFormulaInf.realize_all]
      intro m
      rw [BoundedFormulaInf.realize_iSupAlong]
      refine ⟨e.symm m, ?_⟩
      simp only [BoundedFormulaInf.realize_equal, Term.realize_var, Sum.elim_inr,
        realize_vConst, hval, e.apply_symm_apply]
      rfl
    · rw [SentenceInf.realize_iInf]
      intro m
      rw [SentenceInf.realize_inf, SentenceInf.realize_iSup]
      refine ⟨⟨z m, (realize_baireAtom (L := L) (V := V) (M := M) (m, z m)).2 rfl⟩, ?_⟩
      rw [SentenceInf.realize_iInf]
      intro n₁
      rw [SentenceInf.realize_iInf]
      intro n₂
      by_cases h : n₁ = n₂
      · simp [h, SentenceInf.realize_def, FormulaInf.realize_def]
      · simp only [h, ↓reduceIte, SentenceInf.realize_not, SentenceInf.realize_inf,
          realize_baireAtom]
        rintro ⟨h₁, h₂⟩
        exact h (((hgraph (m, n₁)).1 h₁).symm.trans ((hgraph (m, n₂)).1 h₂))
    · rw [SentenceInf.realize_iInf]
      intro k
      rw [SentenceInf.realize_def, FormulaInf.realize_def, BoundedFormulaInf.realize_iInfAlong]
      rintro ⟨R, x⟩
      simp only [BoundedFormulaInf.realize_iff]
      have htuple :
          (fun i => @Structure.funMap (L.sum (witnessLang V)) M _ 0 (vSym (x i)) Fin.elim0) =
            e ∘ x := funext fun i => hval (x i)
      have hrel : @SentenceInf.Realize _ ℕ (relOnConsts (V := V) R x) M _ ↔
          (f z).eval (atom R x) = true :=
        (@realize_relOnConsts L V M iM _ inferInstance k R x).trans <|
          (iff_of_eq (congrArg _ htuple)).trans <|
            (@Language.Equiv.map_rel L V M (f z).toStructure iM e _ R x).trans
              (toStructure_relMap (f z) R x)
      simpa [SentenceInf.realize_def, FormulaInf.realize_def] using
        hrel.trans (realize_openSetSentence_iff (L := L) (V := V) (hOpen (atom R x)) hgraph).symm

end PCSentence

/-! ### Analytic invariant separation and the López–Escobar theorem -/

/-- **Analytic invariant separation by an `L_{ω₁ω}` sentence.** In a relational language with
countably many relation symbols of each arity, on any countable carrier `V`, if `A` and `B` are
analytic sets of configurations and no isomorphism class meets both `A` and `B`, then there is an
`L_{ω₁ω}` sentence `θ` whose model class contains `A` and is disjoint from `B`. -/
theorem exists_sentence_separating [∀ n, Countable (L.Relations n)] [Countable V]
    {A B : Set (RelationalConfiguration L V)} (hA : AnalyticSet A) (hB : AnalyticSet B)
    (hAB : Disjoint (Quotient.mk (isoSetoid L V) '' A) (Quotient.mk (isoSetoid L V) '' B)) :
    ∃ θ : L.Sentenceω, A ⊆ modelsOf θ ∧ Disjoint (modelsOf θ) B := by
  rcases A.eq_empty_or_nonempty with rfl | hAne
  · exact ⟨⊥, empty_subset _, by simp⟩
  rcases B.eq_empty_or_nonempty with rfl | hBne
  · exact ⟨⊤, by simp, by simp⟩
  rcases isEmpty_or_nonempty V with hV | hV
  · -- Empty carrier: isomorphism is equality, Lusin separation gives a Borel separator, and every
    -- Borel set is `modelsOf θ`.
    have hdisj : Disjoint A B := disjoint_left.2 fun c hcA hcB =>
      hAB.le_bot ⟨mem_image_of_mem _ hcA, mem_image_of_mem _ hcB⟩
    obtain ⟨C, hAC, hBC, hC⟩ := hA.measurablySeparable hB hdisj
    obtain ⟨θ, rfl⟩ := exists_modelsOf_eq_of_measurableSet_of_isEmpty hC
    exact ⟨θ, hAC, hBC.symm⟩
  · -- Nonempty countable carrier: present the isomorphism saturations of `A` and `B` as `PC_{ω₁ω}`
    -- classes and separate them by `pcSeparation`.
    obtain ⟨f, hf, rfl⟩ := exists_continuous_range_eq_of_analyticSet hA hAne
    obtain ⟨g, hg, rfl⟩ := exists_continuous_range_eq_of_analyticSet hB hBne
    obtain ⟨θ, hθ₁, hθ₂⟩ := pcSeparation.{u, v, w, 0, w, 0, w, w} (pcSentence f) (pcSentence g)
      fun M iM _ _ hM₁ hM₂ => by
        obtain ⟨c, hc, ⟨e₁⟩⟩ := (pcMem_pcSentence_iff hf).1 hM₁
        obtain ⟨d, hd, ⟨e₂⟩⟩ := (pcMem_pcSentence_iff hg).1 hM₂
        have hcd : isoSetoid L V c d :=
          isoSetoid_apply.2 ⟨@Language.Equiv.comp L V M c.toStructure iM V d.toStructure
            (@Language.Equiv.symm L V M d.toStructure iM e₂) e₁⟩
        exact hAB.le_bot ⟨mem_image_of_mem _ hc, Quotient.sound hcd ▸ mem_image_of_mem _ hd⟩
    refine ⟨θ, fun c hc => ?_, disjoint_left.2 fun d hdθ hd => ?_⟩
    · let : L.Structure V := c.toStructure
      exact mem_modelsOf.2 <|
        hθ₁ V ((pcMem_pcSentence_iff hf).2 ⟨c, hc, ⟨@Language.Equiv.refl L V c.toStructure⟩⟩)
    · let : L.Structure V := d.toStructure
      exact hθ₂ V ((pcMem_pcSentence_iff hg).2 ⟨d, hd, ⟨@Language.Equiv.refl L V d.toStructure⟩⟩)
        (mem_modelsOf.1 hdθ)

/-- **Analytic separation against an isomorphism-invariant set.** In a countable relational
vocabulary on a countable carrier `V`, if `A` and `B` are disjoint analytic sets and `B` is
isomorphism invariant, then some `L_{ω₁ω}` sentence holds on `A` and fails on `B`. -/
theorem exists_sentence_separating_of_isomorphismInvariant
    [∀ n, Countable (L.Relations n)] [Countable V]
    {A B : Set (RelationalConfiguration L V)} (hA : AnalyticSet A) (hB : AnalyticSet B)
    (hBinv : IsomorphismInvariant B) (hAB : Disjoint A B) :
    ∃ θ : L.Sentenceω, A ⊆ modelsOf θ ∧ Disjoint (modelsOf θ) B :=
  exists_sentence_separating hA hB (hBinv.disjoint_image_quotientMk_right hAB)

/-- **Suslin–López–Escobar theorem.** An isomorphism-invariant bi-analytic set of configurations on
a countable carrier, in a countable relational vocabulary, is the model class of a single `L_{ω₁ω}`
sentence. -/
theorem exists_modelsOf_eq_of_analyticSet_compl [∀ n, Countable (L.Relations n)] [Countable V]
    {A : Set (RelationalConfiguration L V)} (hA : AnalyticSet A) (hAc : AnalyticSet Aᶜ)
    (hinv : IsomorphismInvariant A) :
    ∃ θ : L.Sentenceω, modelsOf (V := V) θ = A := by
  obtain ⟨θ, hsub, hdisj⟩ := exists_sentence_separating_of_isomorphismInvariant hA hAc
    hinv.compl disjoint_compl_right
  exact ⟨θ, Subset.antisymm (disjoint_compl_right_iff_subset.1 hdisj) hsub⟩

/-- **The López–Escobar theorem.** In a relational language with countably many relation symbols of
each arity, a set of configurations on a countable carrier `V` is Borel and isomorphism invariant
if and only if it is the model class `modelsOf θ` of an `L_{ω₁ω}` sentence `θ`. -/
theorem measurableSet_and_isomorphismInvariant_iff_exists_modelsOf
    [∀ n, Countable (L.Relations n)] [Countable V]
    {A : Set (RelationalConfiguration L V)} :
    MeasurableSet A ∧ IsomorphismInvariant A ↔
      ∃ θ : L.Sentenceω, modelsOf (V := V) θ = A := by
  refine ⟨fun ⟨hA, hinv⟩ =>
    exists_modelsOf_eq_of_analyticSet_compl hA.analyticSet hA.compl.analyticSet hinv, ?_⟩
  rintro ⟨θ, rfl⟩
  exact ⟨measurableSet_modelsOf θ, isomorphismInvariant_modelsOf θ⟩

/-! ### Relative separation and relative López–Escobar -/

/-- **Relative sentence separation along a Borel map.** Let `X` be a standard Borel space and
`f : X → RelationalConfiguration L V` a measurable map into configurations on a countable carrier
in a countable relational vocabulary. If `U` and `W` are measurable subsets of `X` whose `f`-images
contain no isomorphic pair, then some `L_{ω₁ω}` sentence `θ` satisfies `U ⊆ f ⁻¹' modelsOf θ` and
`Disjoint (f ⁻¹' modelsOf θ) W`. -/
theorem exists_sentence_separating_preimage [∀ n, Countable (L.Relations n)] [Countable V]
    {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    {f : X → RelationalConfiguration L V} (hf : Measurable f) {U W : Set X}
    (hU : MeasurableSet U) (hW : MeasurableSet W)
    (hUW : ∀ x ∈ U, ∀ y ∈ W, ¬ isoSetoid L V (f x) (f y)) :
    ∃ θ : L.Sentenceω, U ⊆ f ⁻¹' modelsOf θ ∧ Disjoint (f ⁻¹' modelsOf θ) W := by
  have hdisj : Disjoint (Quotient.mk (isoSetoid L V) '' (f '' U))
      (Quotient.mk (isoSetoid L V) '' (f '' W)) := by
    refine disjoint_left.2 ?_
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩ ⟨_, ⟨y, hy, rfl⟩, heq⟩
    exact hUW x hx y hy (Quotient.exact heq.symm)
  obtain ⟨θ, hsub, hθW⟩ := exists_sentence_separating
    (hU.analyticSet_image hf) (hW.analyticSet_image hf) hdisj
  exact ⟨θ, image_subset_iff.1 hsub, disjoint_image_right.1 hθW⟩

/-- **Relative López–Escobar theorem.** Let `X` be a standard Borel space and
`f : X → RelationalConfiguration L V` a measurable map into configurations on a countable carrier
in a countable relational vocabulary. Every measurable set `U ⊆ X` closed under `f`-isomorphism is
the preimage `f ⁻¹' modelsOf θ` of a single `L_{ω₁ω}` sentence `θ`. -/
theorem exists_modelsOf_preimage_eq [∀ n, Countable (L.Relations n)] [Countable V]
    {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    {f : X → RelationalConfiguration L V} (hf : Measurable f) {U : Set X}
    (hU : MeasurableSet U) (hinv : ∀ ⦃x y⦄, isoSetoid L V (f x) (f y) → x ∈ U → y ∈ U) :
    ∃ θ : L.Sentenceω, f ⁻¹' modelsOf θ = U := by
  obtain ⟨θ, hsub, hdisj⟩ := exists_sentence_separating_preimage hf hU hU.compl
    fun x hx y hy hxy => hy (hinv hxy hx)
  exact ⟨θ, Subset.antisymm (disjoint_compl_right_iff_subset.1 hdisj) hsub⟩

end TauCeti.RelationalConfiguration
