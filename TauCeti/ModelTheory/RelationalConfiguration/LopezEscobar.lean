/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.Isomorphism
public import TauCeti.ModelTheory.RelationalConfiguration.ModelsOf
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import TauCeti.ModelTheory.Interpolation.Craig
import TauCeti.ModelTheory.RelationalConfiguration.LanguageMap
import TauCeti.ModelTheory.Sublanguage
import TauCeti.Topology.Instances.CantorSpace

/-!
# The López–Escobar theorem and invariant analytic separation

On a countable carrier `V`, the model class `modelsOf φ` of any `L_{ω₁ω}` sentence `φ` in a
relational language `L` is measurable for the product σ-algebra (`measurableSet_modelsOf`) and
closed under isomorphism of decoded structures (`isomorphismInvariant_modelsOf`). López–Escobar's
theorem establishes the converse and its analytic separation strengthening:

* **Analytic separation** (`exists_sentence_separating_of_disjoint_image_quotientMk` and
  `exists_sentence_separating`): if `A` and `B` are analytic sets of configurations on `V` that
  meet no common isomorphism class (in particular, if `A` and `B` are disjoint and `B` is
  isomorphism invariant), then there is an `L_{ω₁ω}` sentence `θ` with `A ⊆ modelsOf θ` and
  `Disjoint B (modelsOf θ)`.
* **Invariant Borel definability** (`IsomorphismInvariant.exists_modelsOf_eq` and
  `exists_modelsOf_eq_iff`): a set of configurations on `V` is the model class of an `L_{ω₁ω}`
  sentence if and only if it is measurable and isomorphism invariant.
* **Relative López–Escobar** (`exists_sentence_mem_modelsOf_iff_of_analyticSet_image`,
  `exists_sentence_mem_modelsOf_iff_of_continuous`, and `exists_sentence_mem_modelsOf_iff`): if a
  subset `U ⊆ X` is saturated under isomorphism of fibers of `f : X → RelationalConfiguration L V`
  and `f '' U` and `f '' Uᶜ` are analytic — in particular, when `X` is Polish and `f` is continuous
  into any relational vocabulary, or when `X` is standard Borel and `f` is measurable into a
  countable relational vocabulary — then `U` is the preimage of `modelsOf θ` for some `L_{ω₁ω}`
  sentence `θ`.

Neither analytic separation, invariant Borel definability, nor continuous relative López–Escobar
requires countability of `L` or nonemptiness of `V` (whereas measurable relative López–Escobar
genuinely needs `[∀ n, Countable (L.Relations n)]`, since an injective measurable family indexed by
`ℝ` using uncountably many nullary relations can separate individual reals while any `L_{ω₁ω}`
sentence mentions only countably many symbols):

1. For a countable relational vocabulary and a nonempty countable carrier `V`, the isomorphism
   saturation of the range of a continuous map `f : (ℕ → ℕ) → RelationalConfiguration L V` is
   presented as a projective class `LHom.sumInl.PCMem Θ` over `L.sum (auxLang V)`, where
   `auxLang V` adds a constant symbol for each element of `V` (asserted bijective onto the model)
   and nullary relation symbols `ℕ × ℕ` (asserted to form the graph of a point `x : ℕ → ℕ` whose
   word-cylinder neighborhoods determine each atom of `f x`). Projective-class separation
   (`FirstOrder.Language.pcSeparation`, derived from Craig interpolation) then separates disjoint
   saturations by a single `L_{ω₁ω}` sentence.
2. On an empty carrier `V`, isomorphism is equality and only nullary relations yield atoms, so
   Lusin separation and induction on the coordinate generators of the product σ-algebra express
   every Borel separator directly as a model class.
3. For an arbitrary relational language `L`, the Lindelöf property of the second-countable product
   space `(ℕ → ℕ) × (ℕ → ℕ) × (V → V)` (with discrete `V`) extracts a countable symbol sublanguage
   `L.symbSublang ∅ R` on which the reducts remain non-isomorphic, lifting analytic separation
   without vocabulary bounds. Likewise, every set in the product σ-algebra depends on countably
   many relation symbols, reducing invariant Borel definability to that countable sublanguage.

## Main results

* `TauCeti.RelationalConfiguration.isomorphismInvariant_modelsOf`: model classes of infinitary
  sentences are isomorphism invariant.
* `TauCeti.RelationalConfiguration.exists_sentence_separating_of_disjoint_image_quotientMk` and
  `TauCeti.RelationalConfiguration.exists_sentence_separating`: analytic sets with disjoint
  isomorphism saturations are separated by an `L_{ω₁ω}` sentence.
* `TauCeti.RelationalConfiguration.IsomorphismInvariant.exists_modelsOf_eq` and
  `TauCeti.RelationalConfiguration.exists_modelsOf_eq_iff`: López–Escobar characterization of
  isomorphism-invariant measurable sets as `L_{ω₁ω}` model classes.
* `TauCeti.RelationalConfiguration.exists_sentence_mem_modelsOf_iff_of_analyticSet_image`,
  `TauCeti.RelationalConfiguration.exists_sentence_mem_modelsOf_iff_of_continuous`, and
  `TauCeti.RelationalConfiguration.exists_sentence_mem_modelsOf_iff`: relative López–Escobar for
  analytic-image, continuous, and measurable families.

## References

* E. G. K. López-Escobar, *An interpolation theorem for denumerably long formulas*, Fundamenta
  Mathematicae **57** (1965), 253–272.
* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46, Cambridge University
  Press, 2016, Theorem 4.2.6.
* S. Gao, *Invariant Descriptive Set Theory*, CRC Press, 2009, Section 11.3.
* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156, Springer,
  1995, Theorem 16.8.
* The projective-class presentation of continuous Baire-space families over `L.sum (auxLang V)` and
  its combination with `pcSeparation` follow `InfinitaryLogic/Descriptive/LopezEscobar.lean` in
  Cameron Freer's `cameronfreer/infinitary-logic` (checkpoint
  `518a366cba97b1ae8c4dc64a297a39bc3e0b`, Apache-2.0), generalized here from nonempty countable
  carriers in countable `Language.{0, 0}` to arbitrary countable carriers `V : Type w` (including
  empty carriers), arbitrary relational languages `L : Language.{u, v}` without vocabulary
  countability hypotheses via Lindelöf open-cover and coordinate-generator sublanguage reductions,
  quotient-disjoint analytic pairs, and relative López–Escobar.
-/

public section

universe u v w uι

open FirstOrder FirstOrder.Language MeasureTheory PiNat Set TopologicalSpace

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w}

/-- Model classes of infinitary sentences are invariant under isomorphism, on any carrier and for
any branching index type. -/
@[simp]
theorem isomorphismInvariant_modelsOf {ι : Type uι} (φ : L.SentenceInf ι) :
    IsomorphismInvariant (modelsOf (V := V) φ) :=
  isomorphismInvariant_iff.2 fun _ _ h =>
    (isoSetoid_apply.1 h).elim fun e => (e.mem_modelsOf_iff φ).mp

/-! ### Empty carrier -/

section EmptyCarrier

/-- On an empty carrier, a single-atom coordinate cylinder in any subset of `Bool` is the model
class of an `L_{ω₁ω}` sentence. -/
private theorem exists_modelsOf_eq_setOf_eval_of_isEmpty [IsEmpty V] (a : Atom L V)
    (s : Set Bool) :
    ∃ θ : L.Sentenceω,
      {c : RelationalConfiguration L V | c.eval a ∈ s} = modelsOf (V := V) θ := by
  induction a using Atom.induction_atom with
  | @h n R tup =>
    cases n with
    | succ m => exact isEmptyElim (tup 0)
    | zero =>
      have htup : tup = Fin.elim0 := Subsingleton.elim _ _
      let φ : L.Sentenceω := BoundedFormulaInf.rel R Fin.elim0
      have hφ (c : RelationalConfiguration L V) : c ∈ modelsOf φ ↔ c.eval (atom R tup) = true := by
        let : L.Structure V := c.toStructure
        rw [mem_modelsOf, SentenceInf.realize_def, FormulaInf.realize_def,
          BoundedFormulaInf.realize_rel, toStructure_relMap, htup]
        exact iff_of_eq (congrArg (fun x => c.eval (atom R x) = true) (Subsingleton.elim _ _))
      by_cases ht : true ∈ s <;> by_cases hf : false ∈ s
      · have hs : s = univ := Set.ext fun | true => by simp [ht] | false => by simp [hf]
        exact ⟨⊤, by simp [hs]⟩
      · have hs : s = {true} := Set.ext fun | true => by simp [ht] | false => by simp [hf]
        refine ⟨φ, Set.ext fun c => ?_⟩
        rw [hs, mem_ofPred_eq, mem_singleton_iff, hφ]
      · have hs : s = {false} := Set.ext fun | true => by simp [ht] | false => by simp [hf]
        refine ⟨φ.not, Set.ext fun c => ?_⟩
        rw [hs, modelsOf_not, mem_compl_iff, mem_ofPred_eq, mem_singleton_iff, hφ, Bool.not_eq_true]
      · have hs : s = ∅ := Set.ext fun | true => by simp [ht] | false => by simp [hf]
        exact ⟨⊥, by simp [hs]⟩

/-- On an empty carrier, every measurable set for the product σ-algebra is the model class of an
`L_{ω₁ω}` sentence. -/
private theorem exists_modelsOf_eq_of_isEmpty [IsEmpty V]
    {C : Set (RelationalConfiguration L V)} (hC : MeasurableSet C) :
    ∃ θ : L.Sentenceω, C = modelsOf θ := by
  -- The ambient σ-algebra on `RelationalConfiguration L V` is `MeasurableSpace.pi` by definition.
  change MeasurableSet[MeasurableSpace.pi] C at hC
  rw [MeasurableSpace.pi_eq_generateFrom_projections] at hC
  induction C, hC using MeasurableSpace.generateFrom_induction with
  | hC B hB _ =>
    obtain ⟨a, s, -, rfl⟩ := hB
    have hB_eq : (Function.eval a ⁻¹' s : Set (Atom L V → Bool)) =
        {c : RelationalConfiguration L V | c.eval a ∈ s} :=
      Set.ext fun c : RelationalConfiguration L V =>
        iff_of_eq (congrArg (· ∈ s) (eval_def c a).symm)
    rw [hB_eq]
    exact exists_modelsOf_eq_setOf_eval_of_isEmpty a s
  | empty => exact ⟨⊥, modelsOf_bot.symm⟩
  | compl B _ ih =>
    obtain ⟨θ, rfl⟩ := ih
    exact ⟨θ.not, (modelsOf_not θ).symm⟩
  | iUnion f _ ih =>
    choose θ hθ using ih
    exact ⟨BoundedFormulaInf.iSup θ, by simp [← hθ]⟩

/-- Disjoint analytic sets of configurations on an empty carrier in a countable relational
vocabulary are separated by an `L_{ω₁ω}` sentence. -/
private theorem exists_sentence_separating_of_isEmpty [∀ n, Countable (L.Relations n)] [IsEmpty V]
    {A B : Set (RelationalConfiguration L V)} (hA : AnalyticSet A) (hB : AnalyticSet B)
    (hAB : Disjoint (Quotient.mk (isoSetoid L V) '' A) (Quotient.mk (isoSetoid L V) '' B)) :
    ∃ θ : L.Sentenceω, A ⊆ modelsOf θ ∧ Disjoint B (modelsOf θ) := by
  have hdisj : Disjoint A B := disjoint_left.2 fun c hcA hcB =>
    disjoint_left.1 hAB (mem_image_of_mem _ hcA) (mem_image_of_mem _ hcB)
  obtain ⟨C, hAC, hCB, hC⟩ := hA.measurablySeparable hB hdisj
  obtain ⟨θ, rfl⟩ := exists_modelsOf_eq_of_isEmpty hC
  exact ⟨θ, hAC, hCB⟩

end EmptyCarrier

/-! ### Projective-class encoding of continuous Baire-space families -/

section PCEncoding

/-- Auxiliary signature for presenting a continuous Baire-space family of configurations on `V` as
a `PC_{ω₁ω}` class: constants `V` naming the carrier elements and nullary relations `ℕ × ℕ`
recording the graph of a Baire-space point `x : ℕ → ℕ`. -/
private abbrev auxLang (V : Type w) : Language.{w, 0} where
  Functions
    | 0 => V
    | _ + 1 => PEmpty
  Relations
    | 0 => ℕ × ℕ
    | _ + 1 => PEmpty

/-- The constant term in `L.sum (auxLang V)` associated to `v : V`. -/
private def constTerm {α : Type*} (v : V) : (L.sum (auxLang V)).Term α :=
  Term.func ((LHom.sumInr : auxLang V →ᴸ L.sum (auxLang V)).onFunction (n := 0) v) Fin.elim0

/-- The map `V → M` interpreting the added constants in an `(L.sum (auxLang V))`-structure. -/
private def constMap (M : Type*) [(L.sum (auxLang V)).Structure M] (v : V) : M :=
  Structure.funMap (L := L.sum (auxLang V))
    ((LHom.sumInr : auxLang V →ᴸ L.sum (auxLang V)).onFunction (n := 0) v) Fin.elim0

omit [L.IsRelational] in
@[simp]
private theorem realize_constTerm {α : Type*} {M : Type*} [(L.sum (auxLang V)).Structure M]
    (val : α → M) (v : V) :
    (constTerm (L := L) v).realize val = constMap (L := L) M v := by
  simp only [constTerm, constMap, Term.realize_func]
  exact congrArg _ (Subsingleton.elim _ _)

/-- Nullary atomic sentence asserting that coordinate `k` of the encoded sequence equals `m`. -/
private def graphAtom (k m : ℕ) : (L.sum (auxLang V)).Sentenceω :=
  BoundedFormulaInf.rel
    ((LHom.sumInr : auxLang V →ᴸ L.sum (auxLang V)).onRelation (n := 0) (k, m)) Fin.elim0

/-- Binary relation on `ℕ` interpreted by the added nullary symbols in `M`. -/
private def graphPred (M : Type*) [(L.sum (auxLang V)).Structure M] (k m : ℕ) : Prop :=
  Structure.RelMap (L := L.sum (auxLang V)) (M := M)
    ((LHom.sumInr : auxLang V →ᴸ L.sum (auxLang V)).onRelation (n := 0) (k, m)) Fin.elim0

omit [L.IsRelational] in
@[simp]
private theorem realize_graphAtom {M : Type*} [(L.sum (auxLang V)).Structure M] (k m : ℕ) :
    SentenceInf.Realize (graphAtom (L := L) (V := V) k m) M ↔
      graphPred (L := L) (V := V) M k m := by
  simp only [graphAtom, graphPred, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_rel]
  exact iff_of_eq (congrArg _ (Subsingleton.elim _ _))

/-- Sentence asserting that the encoded sequence begins with the finite word `w : List ℕ`. -/
private def wordSentence (w : List ℕ) : (L.sum (auxLang V)).Sentenceω :=
  BoundedFormulaInf.iInf fun i : ℕ => if h : i < w.length then graphAtom i w[i] else ⊤

omit [L.IsRelational] in
private theorem realize_wordSentence {M : Type*} [(L.sum (auxLang V)).Structure M] {x : ℕ → ℕ}
    (hx : ∀ k m, graphPred (L := L) (V := V) M k m ↔ x k = m) (w : List ℕ) :
    SentenceInf.Realize (wordSentence (L := L) (V := V) w) M ↔ x ∈ wordCylinder w := by
  rw [mem_wordCylinder_iff]
  simp only [wordSentence, SentenceInf.realize_iInf]
  refine forall_congr' fun i => ?_
  by_cases hi : i < w.length
  · simp [hi, hx]
  · simp [hi]

/-- Sentence asserting that the encoded sequence belongs to the union of word cylinders inside
`U`. -/
private noncomputable def openSetSentence (U : Set (ℕ → ℕ)) : (L.sum (auxLang V)).Sentenceω :=
  BoundedFormulaInf.iSupAlong (IndexCoding.ofEncodable (List ℕ)) fun w : List ℕ =>
    open Classical in if wordCylinder w ⊆ U then wordSentence w else ⊥

omit [L.IsRelational] in
private theorem realize_openSetSentence {M : Type*} [(L.sum (auxLang V)).Structure M] {x : ℕ → ℕ}
    (hx : ∀ k m, graphPred (L := L) (V := V) M k m ↔ x k = m) {U : Set (ℕ → ℕ)} (hU : IsOpen U) :
    SentenceInf.Realize (openSetSentence (L := L) (V := V) U) M ↔ x ∈ U := by
  have hmem : x ∈ U ↔ ∃ w : List ℕ, wordCylinder w ⊆ U ∧ x ∈ wordCylinder w := by
    refine ⟨fun hxU => ?_, fun ⟨_, hwU, hxw⟩ => hwU hxw⟩
    obtain ⟨t, ⟨y, n, rfl⟩, hxt, htU⟩ :=
      (isTopologicalBasis_cylinders (E := fun _ : ℕ => ℕ)).exists_subset_of_mem_open hxU hU
    exact ⟨(res y n).reverse, (wordCylinder_reverse_res y n).trans_subset htU,
      (wordCylinder_reverse_res y n).symm ▸ hxt⟩
  rw [hmem]
  simp only [openSetSentence, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_iSupAlong]
  refine exists_congr fun w => ?_
  by_cases hw : wordCylinder w ⊆ U
  · simp only [hw, ↓reduceIte, ← FormulaInf.realize_def, ← SentenceInf.realize_def,
      realize_wordSentence hx w, true_and]
  · simp [hw]

/-- Sentence asserting injectivity of `constMap M : V → M` on a countable carrier `V`. -/
private noncomputable def injSentence [Countable V] : (L.sum (auxLang V)).Sentenceω :=
  BoundedFormulaInf.iInfAlong (IndexCoding.ofEncodableWith (Encodable.ofCountable (V × V)))
    fun p : V × V =>
      open Classical in
      if p.1 = p.2 then ⊤ else (BoundedFormulaInf.equal (constTerm p.1) (constTerm p.2)).not

omit [L.IsRelational] in
private theorem realize_injSentence [Countable V] {M : Type*} [(L.sum (auxLang V)).Structure M] :
    SentenceInf.Realize (injSentence (L := L) (V := V)) M ↔
      Function.Injective (constMap (L := L) (V := V) M) := by
  simp only [injSentence, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_iInfAlong, Function.Injective, Prod.forall]
  refine forall₂_congr fun v₁ v₂ => ?_
  by_cases h : v₁ = v₂
  · subst h; simp
  · simp [h]

/-- Sentence asserting surjectivity of `constMap M : V → M` on a countable carrier `V`. -/
private noncomputable def surjSentence [Countable V] : (L.sum (auxLang V)).Sentenceω :=
  BoundedFormulaInf.all
    (BoundedFormulaInf.iSupAlong (IndexCoding.ofEncodableWith (Encodable.ofCountable V))
      fun v : V => BoundedFormulaInf.equal (constTerm v) (Term.var (Sum.inr 0)))

omit [L.IsRelational] in
private theorem realize_surjSentence [Countable V] {M : Type*} [(L.sum (auxLang V)).Structure M] :
    SentenceInf.Realize (surjSentence (L := L) (V := V)) M ↔
      Function.Surjective (constMap (L := L) (V := V) M) := by
  simp [surjSentence, SentenceInf.realize_def, FormulaInf.realize_def, Function.Surjective,
    Fin.snoc_zero]

/-- Sentence asserting that `graphPred M : ℕ → ℕ → Prop` is the graph of a total function
`ℕ → ℕ`. -/
private def funcSentence : (L.sum (auxLang V)).Sentenceω :=
  BoundedFormulaInf.iInf fun k : ℕ =>
    (BoundedFormulaInf.iSup fun m : ℕ => graphAtom k m) ⊓
      BoundedFormulaInf.iInf fun m₁ : ℕ =>
        BoundedFormulaInf.iInf fun m₂ : ℕ =>
          if m₁ = m₂ then ⊤ else (graphAtom k m₁ ⊓ graphAtom k m₂).not

omit [L.IsRelational] in
private theorem realize_funcSentence {M : Type*} [(L.sum (auxLang V)).Structure M] :
    SentenceInf.Realize (funcSentence (L := L) (V := V)) M ↔
      ∃ x : ℕ → ℕ, ∀ k m, graphPred (L := L) (V := V) M k m ↔ x k = m := by
  simp only [funcSentence, SentenceInf.realize_iInf, SentenceInf.realize_inf,
    SentenceInf.realize_iSup, realize_graphAtom]
  constructor
  · intro h
    choose x hx using fun k => (h k).1
    refine ⟨x, fun k m => ⟨fun hkm => ?_, fun hkm => hkm ▸ hx k⟩⟩
    by_contra hne
    have huniq := (h k).2 (x k) m
    simp only [hne, ↓reduceIte, SentenceInf.realize_not, SentenceInf.realize_inf,
      realize_graphAtom] at huniq
    exact huniq ⟨hx k, hkm⟩
  · rintro ⟨x, hx⟩ k
    refine ⟨⟨x k, (hx k (x k)).2 rfl⟩, fun m₁ m₂ => ?_⟩
    by_cases hm : m₁ = m₂
    · simp [hm]
    · simp only [hm, ↓reduceIte, SentenceInf.realize_not, SentenceInf.realize_inf,
        realize_graphAtom, hx]
      rintro ⟨rfl, rfl⟩
      exact hm rfl

/-- Sentence asserting the base relation symbol `R` at the constants naming `tup`. -/
private def atomRelSentence {n : ℕ} (R : L.Relations n) (tup : Fin n → V) :
    (L.sum (auxLang V)).Sentenceω :=
  BoundedFormulaInf.rel ((LHom.sumInl : L →ᴸ L.sum (auxLang V)).onRelation R)
    fun i => constTerm (tup i)

omit [L.IsRelational] in
private theorem realize_atomRelSentence {M : Type*} [L.Structure M]
    [(L.sum (auxLang V)).Structure M] [(LHom.sumInl : L →ᴸ L.sum (auxLang V)).IsExpansionOn M]
    {n : ℕ} (R : L.Relations n) (tup : Fin n → V) :
    SentenceInf.Realize (atomRelSentence (L := L) R tup) M ↔
      Structure.RelMap (L := L) R (constMap (L := L) M ∘ tup) := by
  rw [atomRelSentence, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_rel, (LHom.sumInl : L →ᴸ L.sum (auxLang V)).map_onRelation]
  simp only [realize_constTerm, Function.comp_def]

/-- Sentence asserting that for every relation symbol `R` and tuple `tup`, `R` holds at `constMap M`
precisely when the encoded sequence lies in `{x | (f x).eval (atom R tup) = true}`. -/
private noncomputable def relSentence [∀ n, Countable (L.Relations n)] [Countable V]
    (f : (ℕ → ℕ) → RelationalConfiguration L V) : (L.sum (auxLang V)).Sentenceω :=
  BoundedFormulaInf.iInfAlong
    (IndexCoding.ofEncodableWith (Encodable.ofCountable (Σ n, L.Relations n × (Fin n → V))))
    fun q => (atomRelSentence q.2.1 q.2.2).iff
      (openSetSentence {x | (f x).eval (atom q.2.1 q.2.2) = true})

private theorem realize_relSentence [∀ n, Countable (L.Relations n)] [Countable V]
    {f : (ℕ → ℕ) → RelationalConfiguration L V} (hf : Continuous f) {M : Type*} [L.Structure M]
    [(L.sum (auxLang V)).Structure M] [(LHom.sumInl : L →ᴸ L.sum (auxLang V)).IsExpansionOn M]
    {x : ℕ → ℕ} (hx : ∀ k m, graphPred (L := L) (V := V) M k m ↔ x k = m) :
    SentenceInf.Realize (relSentence f) M ↔
      ∀ {n : ℕ} (R : L.Relations n) (tup : Fin n → V),
        Structure.RelMap (L := L) R (constMap (L := L) M ∘ tup) ↔
          @Structure.RelMap L V (f x).toStructure n R tup := by
  rw [relSentence, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_iInfAlong]
  constructor
  · intro h n R tup
    have ha := h ⟨n, R, tup⟩
    have hopen : IsOpen {y : ℕ → ℕ | (f y).eval (atom R tup) = true} :=
      (isClopen_discrete {true}).2.preimage ((continuous_eval (atom R tup)).comp hf)
    rw [BoundedFormulaInf.realize_iff, ← FormulaInf.realize_def, ← FormulaInf.realize_def,
      ← SentenceInf.realize_def, ← SentenceInf.realize_def, realize_atomRelSentence,
      realize_openSetSentence hx hopen, mem_ofPred_eq, ← toStructure_relMap] at ha
    exact ha
  · rintro h ⟨n, R, tup⟩
    have hopen : IsOpen {y : ℕ → ℕ | (f y).eval (atom R tup) = true} :=
      (isClopen_discrete {true}).2.preimage ((continuous_eval (atom R tup)).comp hf)
    rw [BoundedFormulaInf.realize_iff, ← FormulaInf.realize_def, ← FormulaInf.realize_def,
      ← SentenceInf.realize_def, ← SentenceInf.realize_def, realize_atomRelSentence,
      realize_openSetSentence hx hopen, mem_ofPred_eq, ← toStructure_relMap]
    exact h R tup

/-- Full `PC_{ω₁ω}` defining sentence for the isomorphism saturation of `range f`. -/
private noncomputable def rangeSentence [∀ n, Countable (L.Relations n)] [Countable V]
    (f : (ℕ → ℕ) → RelationalConfiguration L V) : (L.sum (auxLang V)).Sentenceω :=
  injSentence ⊓ surjSentence ⊓ funcSentence ⊓ relSentence f

/-- Any `L`-structure in the projective class of `rangeSentence f` is isomorphic to
`(f x).toStructure` for some `x : ℕ → ℕ`. -/
private theorem exists_equiv_of_pcMem_rangeSentence [∀ n, Countable (L.Relations n)] [Countable V]
    {f : (ℕ → ℕ) → RelationalConfiguration L V} (hf : Continuous f) {M : Type*} [L.Structure M]
    (hM : (LHom.sumInl : L →ᴸ L.sum (auxLang V)).PCMem (rangeSentence f) M) :
    ∃ x : ℕ → ℕ, Nonempty (@Language.Equiv L M V _ (f x).toStructure) := by
  obtain ⟨S, hS, hΘ⟩ := LHom.pcMem_iff.1 hM
  let : (L.sum (auxLang V)).Structure M := S
  have : (LHom.sumInl : L →ᴸ L.sum (auxLang V)).IsExpansionOn M := hS
  simp only [rangeSentence, SentenceInf.realize_inf] at hΘ
  obtain ⟨⟨⟨hinj, hsurj⟩, hfunc⟩, hrel⟩ := hΘ
  rw [realize_injSentence] at hinj
  rw [realize_surjSentence] at hsurj
  obtain ⟨x, hx⟩ := realize_funcSentence.1 hfunc
  let := (f x).toStructure
  have hrel' {n : ℕ} (R : L.Relations n) (tup : Fin n → V) :=
    (realize_relSentence hf hx).1 hrel R tup
  let e : V ≃ M := Equiv.ofBijective (constMap (L := L) M) ⟨hinj, hsurj⟩
  refine ⟨x, ⟨Language.Equiv.symm
    { toEquiv := e
      map_fun' := fun {n} fn _ => isEmptyElim fn
      map_rel' := fun {n} R tup => hrel' R tup }⟩⟩

/-- `(auxLang V)`-structure on `M` built from an enumeration `cMap : V → M` and a sequence
`x : ℕ → ℕ`. -/
@[instance_reducible]
private def mkAuxStructure {M : Type*} (cMap : V → M) (x : ℕ → ℕ) : (auxLang V).Structure M where
  funMap {n} fn _ := match n, fn with
    | 0, v => cMap v
    | _ + 1, fn => fn.elim
  RelMap {n} r _ := match n, r with
    | 0, p => x p.1 = p.2
    | _ + 1, r => r.elim

/-- Any `L`-structure isomorphic to `(f x).toStructure` belongs to the projective class of
`rangeSentence f`. -/
private theorem pcMem_rangeSentence_of_equiv [∀ n, Countable (L.Relations n)] [Countable V]
    {f : (ℕ → ℕ) → RelationalConfiguration L V} (hf : Continuous f) {M : Type*} [L.Structure M]
    (x : ℕ → ℕ) (e : @Language.Equiv L M V _ (f x).toStructure) :
    (LHom.sumInl : L →ᴸ L.sum (auxLang V)).PCMem (rangeSentence f) M := by
  let := (f x).toStructure
  let : (auxLang V).Structure M := mkAuxStructure e.symm x
  refine LHom.pcMem_of_isExpansionOn ?_
  have hc : constMap (L := L) (V := V) M = e.symm := funext fun v =>
    (LHom.sumInr : auxLang V →ᴸ L.sum (auxLang V)).map_onFunction (n := 0) v Fin.elim0
  have hx (k m : ℕ) : graphPred (L := L) (V := V) M k m ↔ x k = m := by
    rw [graphPred, (LHom.sumInr : auxLang V →ᴸ L.sum (auxLang V)).map_onRelation (n := 0)]
    rfl
  simp only [rangeSentence, SentenceInf.realize_inf]
  refine ⟨⟨⟨realize_injSentence.2 (hc ▸ e.symm.injective),
    realize_surjSentence.2 (hc ▸ e.symm.surjective)⟩,
    realize_funcSentence.2 ⟨x, hx⟩⟩, (realize_relSentence hf hx).2 fun R tup => ?_⟩
  rw [hc]
  exact e.symm.map_rel R tup

/-- Two continuous Baire-space families on a nonempty countable carrier in a countable relational
vocabulary whose ranges meet no common isomorphism class are separated by an `L_{ω₁ω}` sentence. -/
private theorem exists_sentence_separating_countable_range [∀ n, Countable (L.Relations n)]
    [Countable V] [Nonempty V] {f g : (ℕ → ℕ) → RelationalConfiguration L V}
    (hf : Continuous f) (hg : Continuous g)
    (hAB : Disjoint (Quotient.mk (isoSetoid L V) '' range f)
      (Quotient.mk (isoSetoid L V) '' range g)) :
    ∃ θ : L.Sentenceω, range f ⊆ modelsOf θ ∧ Disjoint (range g) (modelsOf θ) := by
  obtain ⟨θ, hθ₁, hθ₂⟩ :=
    FirstOrder.Language.pcSeparation.{u, v, w, 0, w, 0, w, w} (rangeSentence f) (rangeSentence g)
      fun M _ _ _ hMf hMg => by
        obtain ⟨x, ⟨ex⟩⟩ := exists_equiv_of_pcMem_rangeSentence hf hMf
        obtain ⟨y, ⟨ey⟩⟩ := exists_equiv_of_pcMem_rangeSentence hg hMg
        have hiso : isoSetoid L V (f x) (g y) :=
          isoSetoid_apply.2 ⟨@Language.Equiv.comp L V M (f x).toStructure _ V (g y).toStructure ey
            (@Language.Equiv.symm L M V _ (f x).toStructure ex)⟩
        exact disjoint_left.1 hAB ⟨f x, mem_range_self x, rfl⟩
          ⟨g y, mem_range_self y, Quotient.sound ((isoSetoid L V).symm hiso)⟩
  refine ⟨θ, ?_, disjoint_left.2 ?_⟩
  · rintro _ ⟨x, rfl⟩
    rw [mem_modelsOf]
    exact @hθ₁ V (f x).toStructure _
      (@pcMem_rangeSentence_of_equiv L _ V _ _ f hf V (f x).toStructure x
        (@Language.Equiv.refl L V (f x).toStructure))
  · rintro _ ⟨y, rfl⟩ hθy
    rw [mem_modelsOf] at hθy
    exact @hθ₂ V (g y).toStructure _
      (@pcMem_rangeSentence_of_equiv L _ V _ _ g hg V (g y).toStructure y
        (@Language.Equiv.refl L V (g y).toStructure)) hθy

end PCEncoding

/-! ### Reduction from arbitrary relational languages to countable symbol sublanguages -/

section SublanguageReduction

omit [L.IsRelational] in
/-- Parameter locus where `(f z.1).restrict z.2.2` and `g z.2.1` disagree on relation symbol `s`. -/
private def disagreeSet (f g : (ℕ → ℕ) → RelationalConfiguration L V)
    (s : Σ n, L.Relations n) : Set ((ℕ → ℕ) × (ℕ → ℕ) × (V → V)) :=
  ⋃ tup : Fin s.1 → V,
    {z | ((f z.1).restrict z.2.2).eval (atom s.2 tup) ≠ (g z.2.1).eval (atom s.2 tup)}

omit [L.IsRelational] in
private theorem isOpen_disagreeSet [TopologicalSpace V] [DiscreteTopology V]
    {f g : (ℕ → ℕ) → RelationalConfiguration L V} (hf : Continuous f) (hg : Continuous g)
    (s : Σ n, L.Relations n) : IsOpen (disagreeSet f g s) := by
  refine isOpen_iUnion fun tup => isOpen_ne_fun ?_ ?_
  · exact (continuous_eval (atom s.2 tup)).comp
      (continuous_uncurry_restrict.comp
        ((continuous_snd.comp continuous_snd).prodMk (hf.comp continuous_fst)))
  · exact (continuous_eval (atom s.2 tup)).comp (hg.comp (continuous_fst.comp continuous_snd))

/-- If continuous families `f, g : (ℕ → ℕ) → RelationalConfiguration L V` on a countable carrier `V`
have ranges meeting no common isomorphism class, then some countable set `R` of relation symbols of
`L` keeps the reduct families non-isomorphic. -/
private theorem exists_countable_sublanguage_disjoint [Countable V]
    {f g : (ℕ → ℕ) → RelationalConfiguration L V} (hf : Continuous f) (hg : Continuous g)
    (hAB : Disjoint (Quotient.mk (isoSetoid L V) '' range f)
      (Quotient.mk (isoSetoid L V) '' range g)) :
    ∃ R : Set (Σ n, L.Relations n), R.Countable ∧
      Disjoint
        (Quotient.mk (isoSetoid (L.symbSublang ∅ R) V) ''
          range ((symbSublangIncl ∅ R).reductConfiguration ∘ f))
        (Quotient.mk (isoSetoid (L.symbSublang ∅ R) V) ''
          range ((symbSublangIncl ∅ R).reductConfiguration ∘ g)) := by
  let _ : TopologicalSpace V := ⊥
  have : DiscreteTopology V := ⟨rfl⟩
  obtain ⟨R, hRcount, hRcov⟩ := isOpen_iUnion_countable (disagreeSet f g) (isOpen_disagreeSet hf hg)
  refine ⟨R, hRcount, disjoint_left.2 ?_⟩
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩ ⟨_, ⟨y, rfl⟩, hq⟩
  obtain ⟨σ, hσ⟩ :=
    isoSetoid_iff_exists_perm_smul_eq.1 ((isoSetoid (L.symbSublang ∅ R) V).symm (Quotient.exact hq))
  simp only [Function.comp_apply, ← LHom.reductConfiguration_perm_smul] at hσ
  let z : (ℕ → ℕ) × (ℕ → ℕ) × (V → V) := (x, y, σ.symm)
  have hz_not : z ∉ ⋃ s ∈ R, disagreeSet f g s := by
    rintro ⟨_, ⟨s, rfl⟩, _, ⟨hsR, rfl⟩, _, ⟨tup, rfl⟩, hne⟩
    apply hne
    have heval := congrArg (fun c => c.eval (atom ⟨s.2, hsR⟩ tup)) hσ
    simpa [z, perm_smul_def, Equiv.Perm.inv_def] using heval
  have hz_in : z ∈ ⋃ s, disagreeSet f g s := by
    by_contra hz
    have heq : σ • f x = g y := ext fun a => by
      induction a using Atom.induction_atom with
      | @h n r tup =>
        by_contra hne
        exact hz (mem_iUnion.2 ⟨⟨n, r⟩, mem_iUnion.2
          ⟨tup, by simpa [z, perm_smul_def, Equiv.Perm.inv_def] using hne⟩⟩)
    exact disjoint_left.1 hAB ⟨f x, mem_range_self x, rfl⟩ ⟨g y, mem_range_self y,
      Quotient.sound ((isoSetoid L V).symm (isoSetoid_iff_exists_perm_smul_eq.2 ⟨σ, heq⟩))⟩
  exact hz_not (hRcov ▸ hz_in)

/-- **López–Escobar separation, quotient-disjoint form.** If `A` and `B` are analytic sets of
configurations on a countable carrier `V` that meet no common isomorphism class, then some
`L_{ω₁ω}` sentence `θ` satisfies `A ⊆ modelsOf θ` and `Disjoint B (modelsOf θ)`. Neither
countability of `L` nor nonemptiness of `V` is required. -/
theorem exists_sentence_separating_of_disjoint_image_quotientMk [Countable V]
    {A B : Set (RelationalConfiguration L V)} (hA : AnalyticSet A) (hB : AnalyticSet B)
    (hAB : Disjoint (Quotient.mk (isoSetoid L V) '' A) (Quotient.mk (isoSetoid L V) '' B)) :
    ∃ θ : L.Sentenceω, A ⊆ modelsOf θ ∧ Disjoint B (modelsOf θ) := by
  obtain ⟨γ, _, _, f₀, hf₀, rfl⟩ := analyticSet_iff_exists_polishSpace_range.1 hA
  rcases isEmpty_or_nonempty γ with hγ | hγ
  · exact ⟨⊥, by simp [range_eq_empty], by simp⟩
  obtain ⟨p, hp, hpsurj⟩ := PolishSpace.exists_nat_nat_continuous_surjective γ
  rw [← hpsurj.range_comp f₀] at hAB ⊢
  obtain ⟨δ, _, _, g₀, hg₀, rfl⟩ := analyticSet_iff_exists_polishSpace_range.1 hB
  rcases isEmpty_or_nonempty δ with hδ | hδ
  · exact ⟨⊤, by simp, by simp [range_eq_empty]⟩
  obtain ⟨q, hq, hqsurj⟩ := PolishSpace.exists_nat_nat_continuous_surjective δ
  rw [← hqsurj.range_comp g₀] at hAB ⊢
  have hf : Continuous (f₀ ∘ p) := hf₀.comp hp
  have hg : Continuous (g₀ ∘ q) := hg₀.comp hq
  obtain ⟨R, hRcount, hRdisj⟩ := exists_countable_sublanguage_disjoint hf hg hAB
  have : Countable R := hRcount.to_subtype
  have : ∀ n, Countable ((L.symbSublang ∅ R).Relations n) :=
    countable_relations_of_countable_sigma (L := L.symbSublang ∅ R)
  let ι := symbSublangIncl (L := L) ∅ R
  have hf' : Continuous (ι.reductConfiguration ∘ (f₀ ∘ p)) :=
    ι.continuous_reductConfiguration.comp hf
  have hg' : Continuous (ι.reductConfiguration ∘ (g₀ ∘ q)) :=
    ι.continuous_reductConfiguration.comp hg
  obtain ⟨θ₀, hθ₀A, hθ₀B⟩ :
      ∃ θ₀ : (L.symbSublang ∅ R).Sentenceω,
        range (ι.reductConfiguration ∘ (f₀ ∘ p)) ⊆ modelsOf θ₀ ∧
          Disjoint (range (ι.reductConfiguration ∘ (g₀ ∘ q))) (modelsOf θ₀) := by
    rcases isEmpty_or_nonempty V with hV | hV
    · exact exists_sentence_separating_of_isEmpty (analyticSet_range_of_polishSpace hf')
        (analyticSet_range_of_polishSpace hg') hRdisj
    · exact exists_sentence_separating_countable_range hf' hg' hRdisj
  refine ⟨ι.onBoundedFormulaInf θ₀, ?_, disjoint_left.2 ?_⟩
  · rintro _ ⟨x, rfl⟩
    rw [mem_modelsOf, ι.realize_sentenceInf_reductConfiguration, ← mem_modelsOf]
    exact hθ₀A ⟨x, rfl⟩
  · rintro _ ⟨y, rfl⟩ hdθ
    rw [mem_modelsOf, ι.realize_sentenceInf_reductConfiguration, ← mem_modelsOf] at hdθ
    exact disjoint_left.1 hθ₀B ⟨y, rfl⟩ hdθ

/-- **López–Escobar separation.** For analytic sets `A` and `B` of configurations on a countable
carrier `V`, if `B` is isomorphism invariant (equivalently, invariant under the logic action of
`Equiv.Perm V`) and `Disjoint A B`, then there exists an `L_{ω₁ω}` sentence `θ` with
`A ⊆ modelsOf θ` and `Disjoint B (modelsOf θ)`. -/
theorem exists_sentence_separating [Countable V]
    {A B : Set (RelationalConfiguration L V)} (hA : AnalyticSet A) (hB : AnalyticSet B)
    (hBinv : IsomorphismInvariant B) (hAB : Disjoint A B) :
    ∃ θ : L.Sentenceω, A ⊆ modelsOf θ ∧ Disjoint B (modelsOf θ) := by
  refine exists_sentence_separating_of_disjoint_image_quotientMk hA hB (disjoint_left.2 ?_)
  rintro _ ⟨c, hcA, rfl⟩ ⟨d, hdB, hcd⟩
  exact disjoint_left.1 hAB hcA ((hBinv.mem_iff (Quotient.exact hcd)).1 hdB)

omit [L.IsRelational] in
/-- Every measurable set of configurations in the product σ-algebra is the preimage of a measurable
set on a countable symbol sublanguage `L.symbSublang ∅ R`. -/
private theorem exists_countable_sublanguage_measurableSet
    {C : Set (RelationalConfiguration L V)} (hC : MeasurableSet C) :
    ∃ R : Set (Σ n, L.Relations n), R.Countable ∧
      ∃ C₀ : Set (RelationalConfiguration (L.symbSublang ∅ R) V),
        MeasurableSet C₀ ∧ C = (symbSublangIncl ∅ R).reductConfiguration ⁻¹' C₀ := by
  -- The ambient σ-algebra on `RelationalConfiguration L V` is `MeasurableSpace.pi` by definition.
  change MeasurableSet[MeasurableSpace.pi] C at hC
  rw [MeasurableSpace.pi_eq_generateFrom_projections] at hC
  induction C, hC using MeasurableSpace.generateFrom_induction with
  | hC B hB _ =>
    obtain ⟨a, s, hs, rfl⟩ := hB
    have hB_eq : (Function.eval a ⁻¹' s : Set (Atom L V → Bool)) =
        {c : RelationalConfiguration L V | c.eval a ∈ s} :=
      Set.ext fun c : RelationalConfiguration L V =>
        iff_of_eq (congrArg (· ∈ s) (eval_def c a).symm)
    rw [hB_eq]
    induction a using Atom.induction_atom with
    | @h n r tup =>
      refine ⟨{⟨n, r⟩}, countable_singleton _,
        (fun c₀ => c₀.eval (atom ⟨r, mem_singleton _⟩ tup)) ⁻¹' s,
        measurable_eval _ hs, ?_⟩
      ext c
      simp
  | empty => exact ⟨∅, countable_empty, ∅, MeasurableSet.empty, rfl⟩
  | compl B _ ih =>
    obtain ⟨R, hR, C₀, hC₀, rfl⟩ := ih
    exact ⟨R, hR, C₀ᶜ, hC₀.compl, rfl⟩
  | iUnion f _ ih =>
    choose R hR C₀ hC₀ hf_eq using ih
    have hex (k : ℕ) : ∃ j : L.symbSublang ∅ (R k) →ᴸ L.symbSublang ∅ (⋃ i, R i),
        (symbSublangIncl ∅ (⋃ i, R i)).comp j = symbSublangIncl ∅ (R k) :=
      (symbSublangIncl ∅ (⋃ i, R i)).exists_comp_eq_symbSublangIncl (empty_subset _)
        fun s hs => ⟨⟨s.1, ⟨s.2, mem_iUnion_of_mem k hs⟩⟩, by simp⟩
    choose j hj using hex
    refine ⟨⋃ i, R i, countable_iUnion hR,
      ⋃ k, (j k).reductConfiguration ⁻¹' C₀ k,
      MeasurableSet.iUnion fun k => (LHom.measurable_reductConfiguration _) (hC₀ k), ?_⟩
    ext c
    simp only [mem_iUnion, hf_eq, mem_preimage, ← hj, LHom.comp_reductConfiguration]

/-- **López–Escobar theorem (hard direction).** Every isomorphism-invariant measurable set of
configurations on a countable carrier `V` is the model class of an `L_{ω₁ω}` sentence, with no
countability assumption on `L`. -/
theorem IsomorphismInvariant.exists_modelsOf_eq [Countable V]
    {A : Set (RelationalConfiguration L V)} (hA : IsomorphismInvariant A) (hm : MeasurableSet A) :
    ∃ θ : L.Sentenceω, A = modelsOf θ := by
  obtain ⟨R, hRcount, A₀, hA₀m, rfl⟩ := exists_countable_sublanguage_measurableSet hm
  have : Countable R := hRcount.to_subtype
  have : ∀ n, Countable ((L.symbSublang ∅ R).Relations n) :=
    countable_relations_of_countable_sigma (L := L.symbSublang ∅ R)
  have hA₀inv : IsomorphismInvariant A₀ := isomorphismInvariant_iff.2 fun c₀ _ hcd hc₀ => by
    obtain ⟨σ, rfl⟩ := isoSetoid_iff_exists_perm_smul_eq.1 hcd
    let S : L.Structure V :=
      { funMap := fun fn => isEmptyElim fn
        RelMap := fun {n} r tup =>
          open Classical in
          if hr : ⟨n, r⟩ ∈ R then c₀.eval (atom ⟨r, hr⟩ tup) = true else False }
    let c : RelationalConfiguration L V := @ofStructure L V S
    have hrc : (symbSublangIncl ∅ R).reductConfiguration c = c₀ := by
      let : L.Structure V := S
      refine ext fun a => Atom.induction_atom (fun {n} r tup => ?_) a
      rw [LHom.eval_reductConfiguration, LHom.onAtom_atom, symbSublangIncl_onRelation,
        eval_ofStructure, Bool.eq_iff_iff, @decide_eq_true_eq _ (Classical.propDecidable _)]
      -- Unfold the class projection `@Structure.RelMap L V S` to `S`'s `RelMap` field.
      change (open Classical in
        if hr : ⟨n, r.1⟩ ∈ R then c₀.eval (atom ⟨r.1, hr⟩ tup) = true else False) ↔
          c₀.eval (atom r tup) = true
      simp [r.2]
    have hsmul := (hA.mem_iff (isoSetoid_perm_smul σ c)).1 (by simpa only [mem_preimage, hrc])
    simpa only [mem_preimage, LHom.reductConfiguration_perm_smul, hrc] using hsmul
  obtain ⟨θ₀, hA₀_sub, hA₀_disj⟩ :=
    exists_sentence_separating hA₀m.analyticSet hA₀m.compl.analyticSet hA₀inv.compl
      disjoint_compl_right
  have hA₀_eq : A₀ = modelsOf θ₀ :=
    Subset.antisymm hA₀_sub (disjoint_compl_left_iff_subset.1 hA₀_disj)
  refine ⟨(symbSublangIncl ∅ R).onBoundedFormulaInf θ₀, ?_⟩
  ext c
  rw [mem_preimage, hA₀_eq, mem_modelsOf, mem_modelsOf,
    (symbSublangIncl ∅ R).realize_sentenceInf_reductConfiguration]

/-- **The López–Escobar theorem.** On a countable carrier `V` in any relational language `L`, a
set of configurations is the model class of an `L_{ω₁ω}` sentence if and only if it is measurable
for the product σ-algebra and isomorphism invariant. -/
theorem exists_modelsOf_eq_iff [Countable V] {A : Set (RelationalConfiguration L V)} :
    (∃ θ : L.Sentenceω, A = modelsOf θ) ↔ MeasurableSet A ∧ IsomorphismInvariant A :=
  ⟨fun ⟨θ, hθ⟩ => hθ ▸ ⟨measurableSet_modelsOf θ, isomorphismInvariant_modelsOf θ⟩,
    fun ⟨hm, hinv⟩ => hinv.exists_modelsOf_eq hm⟩

/-- **Relative López–Escobar, analytic-image form.** For `f : X → RelationalConfiguration L V`
into configurations on a countable carrier in any relational language `L` and `U ⊆ X` saturated
under isomorphism of fibers, if `f '' U` and `f '' Uᶜ` are analytic, then some `L_{ω₁ω}` sentence
`θ` satisfies `f x ∈ modelsOf θ ↔ x ∈ U` for every `x : X`. -/
theorem exists_sentence_mem_modelsOf_iff_of_analyticSet_image [Countable V] {X : Type*}
    {f : X → RelationalConfiguration L V} {U : Set X}
    (hU : AnalyticSet (f '' U)) (hUc : AnalyticSet (f '' Uᶜ))
    (hinv : ∀ ⦃x y⦄, isoSetoid L V (f x) (f y) → (x ∈ U ↔ y ∈ U)) :
    ∃ θ : L.Sentenceω, ∀ x, f x ∈ modelsOf θ ↔ x ∈ U := by
  have hdisj : Disjoint (Quotient.mk (isoSetoid L V) '' (f '' U))
      (Quotient.mk (isoSetoid L V) '' (f '' Uᶜ)) := by
    refine disjoint_left.2 ?_
    rintro _ ⟨_, ⟨x, hxU, rfl⟩, rfl⟩ ⟨_, ⟨y, hyU, rfl⟩, hxy⟩
    exact hyU ((hinv (Quotient.exact hxy)).2 hxU)
  obtain ⟨θ, hθU, hθUc⟩ :=
    exists_sentence_separating_of_disjoint_image_quotientMk hU hUc hdisj
  refine ⟨θ, fun x => ⟨fun hxθ => by_contra fun hxU => ?_,
    fun hxU => hθU (mem_image_of_mem f hxU)⟩⟩
  exact disjoint_left.1 hθUc (mem_image_of_mem f hxU) hxθ

/-- **Relative López–Escobar for continuous families.** Let `X` be a Polish space with its Borel
σ-algebra and `f : X → RelationalConfiguration L V` a continuous map into configurations on a
countable carrier in any relational language `L`. Every measurable subset `U ⊆ X` saturated under
isomorphism of fibers is the preimage of `modelsOf θ` for some `L_{ω₁ω}` sentence `θ`. -/
theorem exists_sentence_mem_modelsOf_iff_of_continuous [Countable V]
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {f : X → RelationalConfiguration L V} (hf : Continuous f) {U : Set X} (hU : MeasurableSet U)
    (hinv : ∀ ⦃x y⦄, isoSetoid L V (f x) (f y) → (x ∈ U ↔ y ∈ U)) :
    ∃ θ : L.Sentenceω, ∀ x, f x ∈ modelsOf θ ↔ x ∈ U :=
  exists_sentence_mem_modelsOf_iff_of_analyticSet_image
    (hU.analyticSet.image_of_continuous hf) (hU.compl.analyticSet.image_of_continuous hf) hinv

/-- **Relative López–Escobar.** Let `X` be a standard Borel space and
`f : X → RelationalConfiguration L V` a measurable map into configurations on a countable carrier
in a countable relational vocabulary. If `U ⊆ X` is measurable and respects isomorphism of fibers
(`isoSetoid L V (f x) (f y) → (x ∈ U ↔ y ∈ U)`), then some `L_{ω₁ω}` sentence `θ` satisfies
`f x ∈ modelsOf θ ↔ x ∈ U` for every `x : X`. -/
theorem exists_sentence_mem_modelsOf_iff [∀ n, Countable (L.Relations n)] [Countable V]
    {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    {f : X → RelationalConfiguration L V} (hf : Measurable f) {U : Set X} (hU : MeasurableSet U)
    (hinv : ∀ ⦃x y⦄, isoSetoid L V (f x) (f y) → (x ∈ U ↔ y ∈ U)) :
    ∃ θ : L.Sentenceω, ∀ x, f x ∈ modelsOf θ ↔ x ∈ U :=
  exists_sentence_mem_modelsOf_iff_of_analyticSet_image
    (hU.analyticSet_image hf) (hU.compl.analyticSet_image hf) hinv

end SublanguageReduction

end TauCeti.RelationalConfiguration
