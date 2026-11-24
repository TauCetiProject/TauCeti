/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Basic
public import TauCeti.ModelTheory.Interpolation.Craig
public import TauCeti.ModelTheory.RelationalConfiguration.LanguageMap
import Mathlib.Topology.MetricSpace.PiNat
import TauCeti.Topology.Algebra.Group.Perm

/-!
# The López–Escobar theorem and invariant analytic separation

On a countable carrier `V`, the model class `modelsOf φ` of any `L_{ω₁ω}` sentence is Borel and
invariant under isomorphism (`measurableSet_modelsOf`, `isomorphismInvariant_modelsOf`). The
**López–Escobar theorem** establishes the converse, together with its analytic separation form: if
`A` and `B` are analytic sets of relational configurations on `V` containing no isomorphic pair
(for instance when `B` is isomorphism invariant and disjoint from `A`), some `L_{ω₁ω}` sentence `θ`
satisfies `A ⊆ modelsOf θ` and `Disjoint B (modelsOf θ)` (`exists_sentence_separating`). Taking
`B = Aᶜ` for an isomorphism-invariant Borel set recovers `modelsOf θ = A`
(`exists_modelsOf_eq_iff`).

Both the separation theorem (`exists_sentence_separating_of_forall_not_isoSetoid`,
`exists_sentence_separating`) and the Borel-definability equivalence (`exists_modelsOf_eq_iff`)
hold on any countable carrier `V` — finite, empty, or countably infinite — and for relational
languages `L` of arbitrary cardinality, without requiring countably many relation symbols.

Pulling back along a measurable family `f : X → RelationalConfiguration L V` parametrized by a
standard Borel space `X` yields **relative López–Escobar** (`exists_sentence_mem_modelsOf_iff`): in
a countable relational vocabulary, any measurable subset `U ⊆ X` saturated under isomorphism of `f`
is cut out by a single `L_{ω₁ω}` sentence `θ` via `f x ∈ modelsOf θ ↔ x ∈ U`. Here countability of
the vocabulary is essential: in an uncountable relational vocabulary, a measurable subset saturated
under isomorphism of `f` need not be cut out by a sentence.

## Main results

* `TauCeti.RelationalConfiguration.exists_sentence_separating_of_forall_not_isoSetoid` and
  `TauCeti.RelationalConfiguration.exists_sentence_separating`: **López–Escobar separation**,
  separating analytic sets with no isomorphic pair (or disjoint analytic sets with one side
  isomorphism invariant) by an `L_{ω₁ω}` sentence, for relational languages of arbitrary
  cardinality.
* `TauCeti.RelationalConfiguration.exists_modelsOf_eq_iff`: **López–Escobar's theorem**,
  characterizing model classes of `L_{ω₁ω}` sentences on a countable carrier as the
  isomorphism-invariant measurable sets, for relational languages of arbitrary cardinality.
* `TauCeti.RelationalConfiguration.exists_sentence_mem_modelsOf_iff`: **relative López–Escobar**
  along a measurable family parametrized by a standard Borel space, in a countable relational
  vocabulary.

## References

* E. G. K. López-Escobar, *An interpolation theorem for denumerably long formulas*, Fundamenta
  Mathematicae **57** (1965), 253–272.
* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46, Cambridge University
  Press, 2016, Theorem 4.2.7 (`PC_{ω₁ω}` proof of López–Escobar's theorem) and §2.4.
* S. Gao, *Invariant Descriptive Set Theory*, Chapman & Hall/CRC, 2009, Theorem 11.3.6.
* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156, Springer,
  1995, Theorem 16.8.
-/

public section

universe u v w w'

open FirstOrder FirstOrder.Language MeasureTheory Set TopologicalSpace
open scoped Pointwise

namespace TauCeti.RelationalConfiguration

/-! ### Empty carriers -/

section EmptyCarrier

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w}

/-- On an empty carrier, every measurable set of configurations is the model class of an `L_{ω₁ω}`
sentence. -/
private theorem exists_modelsOf_eq_of_isEmpty [IsEmpty V]
    {D : Set (RelationalConfiguration L V)} (hD : MeasurableSet D) :
    ∃ θ : L.Sentenceω, modelsOf (V := V) θ = D := by
  classical
  let m : MeasurableSpace (RelationalConfiguration L V) :=
    { MeasurableSet' E := ∃ θ : L.Sentenceω, modelsOf (V := V) θ = E
      measurableSet_empty := ⟨⊥, modelsOf_bot⟩
      measurableSet_compl := fun E ⟨θ, hθ⟩ => ⟨θ.not, by rw [modelsOf_not, hθ]⟩
      measurableSet_iUnion := fun f hf => by
        choose θ hθ using hf
        exact ⟨BoundedFormulaInf.iSup θ, by simp [modelsOf_iSup, hθ]⟩ }
  have hmeas :
      @Measurable (RelationalConfiguration L V) (RelationalConfiguration L V) m
        instMeasurableSpace id := by
    refine (@measurable_iff L V _ m id).2 fun a => ?_
    induction a using Atom.induction_atom with
    | @h n R x =>
      cases n with
      | zero =>
        obtain rfl : x = Fin.elim0 := Subsingleton.elim x Fin.elim0
        rintro s -
        let φ : L.Sentenceω := BoundedFormulaInf.rel R Fin.elim0
        have hφ : modelsOf (V := V) φ =
            {c : RelationalConfiguration L V | c.eval (atom R Fin.elim0) = true} := by
          ext c
          let _ : L.Structure V := c.toStructure
          rw [mem_modelsOf, SentenceInf.realize_def, FormulaInf.realize_def,
            BoundedFormulaInf.realize_rel, mem_ofPred_eq, ← toStructure_relMap]
          exact iff_of_eq (congrArg _ (Subsingleton.elim _ _))
        have heq : (fun c : RelationalConfiguration L V => c.eval (atom R Fin.elim0)) ⁻¹' s =
            (if true ∈ s then modelsOf (V := V) φ else ∅) ∪
              (if false ∈ s then (modelsOf (V := V) φ)ᶜ else ∅) := by
          rw [hφ]
          ext c
          cases hca : c.eval (atom R Fin.elim0) <;> simp [hca]
        simp only [id_eq, heq]
        refine @MeasurableSet.union _ m _ _ ?_ ?_
        · split_ifs <;> [exact ⟨φ, rfl⟩; exact @MeasurableSet.empty _ m]
        · split_ifs <;> [exact ⟨φ.not, modelsOf_not φ⟩; exact @MeasurableSet.empty _ m]
      | succ k => exact fun s _ => False.elim (isEmptyElim (x 0))
  exact hmeas hD

end EmptyCarrier

/-! ### `PC_{ω₁ω}` representation of continuous Baire images -/

section BairePC

/-- Auxiliary witness language naming each vertex of `V` by a constant symbol and each coordinate
value `(i, j) : ℕ × ℕ` of a Baire-space point by a nullary relation symbol. -/
private abbrev baireWitnessLang (V : Type w) : Language.{w, 0} where
  Functions
    | 0 => V
    | _ + 1 => PEmpty
  Relations
    | 0 => ℕ × ℕ
    | _ + 1 => PEmpty

/-- Constant term in `L.sum (baireWitnessLang V)` naming `v : V`. -/
private def constTerm (L : Language.{u, v}) {V : Type w} {α : Type*} (v : V) :
    (L.sum (baireWitnessLang V)).Term α :=
  .func ((LHom.sumInr : baireWitnessLang V →ᴸ L.sum (baireWitnessLang V)).onFunction
    (v : (baireWitnessLang V).Functions 0)) Fin.elim0

@[simp]
private theorem realize_constTerm {L : Language.{u, v}} {V : Type w} {α : Type*}
    {M : Type w'} [(L.sum (baireWitnessLang V)).Structure M] (v : V) (val : α → M) :
    (constTerm L v).realize val =
      @Structure.funMap (L.sum (baireWitnessLang V)) M _ 0 (Sum.inr v) Fin.elim0 := by
  rw [constTerm, Term.realize_func, LHom.sumInr_onFunction]
  exact congrArg _ (Subsingleton.elim _ _)

/-- Nullary sentence asserting that the `i`-th coordinate of the witnessed Baire point is `j`. -/
private def bitSentence (L : Language.{u, v}) (V : Type w) (i j : ℕ) :
    (L.sum (baireWitnessLang V)).Sentenceω :=
  .rel ((LHom.sumInr : baireWitnessLang V →ᴸ L.sum (baireWitnessLang V)).onRelation
    ((i, j) : (baireWitnessLang V).Relations 0)) Fin.elim0

@[simp]
private theorem realize_bitSentence {L : Language.{u, v}} {V : Type w}
    {M : Type w'} [(L.sum (baireWitnessLang V)).Structure M] (i j : ℕ) :
    SentenceInf.Realize (bitSentence L V i j) M ↔
      @Structure.RelMap (L.sum (baireWitnessLang V)) M _ 0 (Sum.inr (i, j)) Fin.elim0 := by
  rw [bitSentence, SentenceInf.realize_def, FormulaInf.realize_def, BoundedFormulaInf.realize_rel,
    LHom.sumInr_onRelation]
  exact iff_of_eq (congrArg _ (Subsingleton.elim _ _))

/-- Sentence asserting that for each `i : ℕ` there is a unique `j : ℕ` at which `bitSentence`
holds, encoding a point of Baire space `ℕ → ℕ`. -/
private def bairePointSentence (L : Language.{u, v}) (V : Type w) :
    (L.sum (baireWitnessLang V)).Sentenceω :=
  .iInf fun i : ℕ =>
    (.iSup fun j : ℕ => bitSentence L V i j) ⊓
      .iInf fun j₁ : ℕ => .iInf fun j₂ : ℕ =>
        if j₁ = j₂ then ⊤ else (bitSentence L V i j₁ ⊓ bitSentence L V i j₂).not

private theorem realize_bairePointSentence {L : Language.{u, v}} {V : Type w}
    {M : Type w'} [(L.sum (baireWitnessLang V)).Structure M] :
    SentenceInf.Realize (bairePointSentence L V) M ↔
      ∀ i : ℕ, ∃! j : ℕ,
        @Structure.RelMap (L.sum (baireWitnessLang V)) M _ 0 (Sum.inr (i, j)) Fin.elim0 := by
  simp only [bairePointSentence, SentenceInf.realize_iInf, SentenceInf.realize_inf,
    SentenceInf.realize_iSup, realize_bitSentence]
  refine forall_congr' fun i =>
    ⟨fun ⟨⟨j, hj⟩, huniq⟩ => ⟨j, hj, fun k hk => ?_⟩,
      fun ⟨j, hj, huniq⟩ => ⟨⟨j, hj⟩, fun j₁ j₂ => ?_⟩⟩
  · by_contra hkj
    have h1 := huniq k j
    simp only [hkj, ↓reduceIte, SentenceInf.realize_not, SentenceInf.realize_inf,
      realize_bitSentence] at h1
    exact h1 ⟨hk, hj⟩
  · by_cases h : j₁ = j₂
    · simp [h]
    · simp only [h, ↓reduceIte, SentenceInf.realize_not, SentenceInf.realize_inf,
        realize_bitSentence]
      rintro ⟨h₁, h₂⟩
      exact h ((huniq j₁ h₁).trans (huniq j₂ h₂).symm)

/-- Finite conjunction asserting that the witnessed Baire point begins with `w : List ℕ`. -/
private def wordSentence (L : Language.{u, v}) (V : Type w) (w : List ℕ) :
    (L.sum (baireWitnessLang V)).Sentenceω :=
  (List.ofFn fun i : Fin w.length => bitSentence L V i w[i]).foldr (· ⊓ ·) ⊤

private theorem realize_wordSentence {L : Language.{u, v}} {V : Type w}
    {M : Type w'} [(L.sum (baireWitnessLang V)).Structure M] {x : ℕ → ℕ}
    (hx : ∀ i j : ℕ,
      @Structure.RelMap (L.sum (baireWitnessLang V)) M _ 0 (Sum.inr (i, j)) Fin.elim0 ↔ x i = j)
    (w : List ℕ) :
    SentenceInf.Realize (wordSentence L V w) M ↔ ∀ i : Fin w.length, x i = w[i] := by
  simp only [wordSentence, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_foldr_inf]
  refine ⟨fun h i => ?_, fun h φ hφ => ?_⟩
  · have hi := h _ (List.mem_ofFn.2 ⟨i, rfl⟩)
    rwa [← FormulaInf.realize_def, ← SentenceInf.realize_def, realize_bitSentence, hx] at hi
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hφ
    simpa only [← FormulaInf.realize_def, ← SentenceInf.realize_def, realize_bitSentence, hx]
      using h i

/-- Countable disjunction over prefix cylinders contained in `U`, expressing `x ∈ U` for an open
subset `U ⊆ ℕ → ℕ`. -/
private noncomputable def openBaireSentence (L : Language.{u, v}) (V : Type w)
    (U : Set (ℕ → ℕ)) : (L.sum (baireWitnessLang V)).Sentenceω := by
  classical
  exact BoundedFormulaInf.iSupAlong (IndexCoding.ofEncodable (List ℕ)) fun w : List ℕ =>
    if {z : ℕ → ℕ | ∀ i : Fin w.length, z i = w[i]} ⊆ U then wordSentence L V w else ⊥

private theorem realize_openBaireSentence {L : Language.{u, v}} {V : Type w}
    {M : Type w'} [(L.sum (baireWitnessLang V)).Structure M] {x : ℕ → ℕ}
    (hx : ∀ i j : ℕ,
      @Structure.RelMap (L.sum (baireWitnessLang V)) M _ 0 (Sum.inr (i, j)) Fin.elim0 ↔ x i = j)
    {U : Set (ℕ → ℕ)} (hU : IsOpen U) :
    SentenceInf.Realize (openBaireSentence L V U) M ↔ x ∈ U := by
  classical
  simp only [openBaireSentence, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_iSupAlong]
  refine ⟨fun ⟨w, hw⟩ => ?_, fun hxU => ?_⟩
  · split_ifs at hw with hsub
    · rw [← FormulaInf.realize_def, ← SentenceInf.realize_def, realize_wordSentence hx] at hw
      exact hsub hw
    · simp at hw
  · obtain ⟨_, ⟨y, n, rfl⟩, hx_mem, hsub⟩ :=
      (PiNat.isTopologicalBasis_cylinders (fun _ : ℕ => ℕ)).exists_subset_of_mem_open hxU hU
    let w : List ℕ := List.ofFn fun i : Fin n => y i
    have hcyl : {z : ℕ → ℕ | ∀ i : Fin w.length, z i = w[i]} = PiNat.cylinder y n := by
      ext z
      simp only [w, List.length_ofFn, Fin.forall_iff, Fin.getElem_fin, List.getElem_ofFn,
        mem_ofPred_eq, PiNat.mem_cylinder_iff]
    refine ⟨w, ?_⟩
    split_ifs with hsub'
    · rw [← FormulaInf.realize_def, ← SentenceInf.realize_def, realize_wordSentence hx]
      exact mem_ofPred.1 (hcyl.symm ▸ hx_mem)
    · exact False.elim (hsub' (hcyl.trans_subset hsub))

/-- Sentence asserting that the witness constants `constTerm L v` are pairwise distinct. -/
private noncomputable def carrierInjectiveSentence (L : Language.{u, v}) (V : Type w)
    [Countable V] : (L.sum (baireWitnessLang V)).Sentenceω := by
  classical
  let cV : IndexCoding V ℕ := IndexCoding.ofEncodableWith (Encodable.ofCountable V)
  exact BoundedFormulaInf.iInfAlong cV fun v₁ : V =>
    BoundedFormulaInf.iInfAlong cV fun v₂ : V =>
      if v₁ = v₂ then ⊤ else (BoundedFormulaInf.equal (constTerm L v₁) (constTerm L v₂)).not

private theorem realize_carrierInjectiveSentence {L : Language.{u, v}} {V : Type w} [Countable V]
    {M : Type w'} [(L.sum (baireWitnessLang V)).Structure M] :
    SentenceInf.Realize (carrierInjectiveSentence L V) M ↔
      Function.Injective (fun v : V =>
        @Structure.funMap (L.sum (baireWitnessLang V)) M _ 0 (Sum.inr v) Fin.elim0) := by
  classical
  simp only [carrierInjectiveSentence, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_iInfAlong]
  refine ⟨fun h v₁ v₂ heq => by_contra fun hne => ?_, fun hinj v₁ v₂ => ?_⟩
  · have h1 := h v₁ v₂
    simp only [hne, ↓reduceIte, BoundedFormulaInf.realize_not, BoundedFormulaInf.realize_equal,
      realize_constTerm] at h1
    exact h1 heq
  · by_cases h : v₁ = v₂
    · simp [h]
    · simp only [h, ↓reduceIte, BoundedFormulaInf.realize_not, BoundedFormulaInf.realize_equal,
        realize_constTerm]
      exact fun heq => h (hinj heq)

/-- Sentence asserting that every element of the carrier is named by some constant
`constTerm L v`. -/
private noncomputable def carrierSurjectiveSentence (L : Language.{u, v}) (V : Type w)
    [Countable V] : (L.sum (baireWitnessLang V)).Sentenceω :=
  let cV : IndexCoding V ℕ := IndexCoding.ofEncodableWith (Encodable.ofCountable V)
  (BoundedFormulaInf.iSupAlong cV fun v : V =>
    BoundedFormulaInf.equal (Term.var (Sum.inr (0 : Fin 1))) (constTerm L v)).all

private theorem realize_carrierSurjectiveSentence {L : Language.{u, v}} {V : Type w} [Countable V]
    {M : Type w'} [(L.sum (baireWitnessLang V)).Structure M] :
    SentenceInf.Realize (carrierSurjectiveSentence L V) M ↔
      Function.Surjective (fun v : V =>
        @Structure.funMap (L.sum (baireWitnessLang V)) M _ 0 (Sum.inr v) Fin.elim0) := by
  simp only [carrierSurjectiveSentence, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_all, BoundedFormulaInf.realize_iSupAlong,
    BoundedFormulaInf.realize_equal, Term.realize_var, Sum.elim_inr, realize_constTerm]
  exact forall_congr' fun _ => exists_congr fun _ => eq_comm

/-- Sentence asserting that every atom of `L` over the witness constants agrees with `f x`. -/
private noncomputable def diagramSentence {L : Language.{u, v}} {V : Type w}
    [∀ n, Countable (L.Relations n)] [Countable V]
    (f : (ℕ → ℕ) → RelationalConfiguration L V) : (L.sum (baireWitnessLang V)).Sentenceω :=
  let cA : IndexCoding (Σ n, L.Relations n × (Fin n → V)) ℕ :=
    IndexCoding.ofEncodableWith (Encodable.ofCountable _)
  BoundedFormulaInf.iInfAlong cA fun p =>
    (BoundedFormulaInf.rel
      ((LHom.sumInl : L →ᴸ L.sum (baireWitnessLang V)).onRelation p.2.1)
      (fun r : Fin p.1 => constTerm L (p.2.2 r))).iff
      (openBaireSentence L V {x | (f x).eval (atom p.2.1 p.2.2) = true})

private theorem realize_diagramSentence {L : Language.{u, v}} {V : Type w}
    [∀ n, Countable (L.Relations n)] [Countable V]
    {M : Type w'} [(L.sum (baireWitnessLang V)).Structure M]
    (f : (ℕ → ℕ) → RelationalConfiguration L V) :
    SentenceInf.Realize (diagramSentence f) M ↔
      ∀ {n : ℕ} (R : L.Relations n) (t : Fin n → V),
        @Structure.RelMap (L.sum (baireWitnessLang V)) M _ n (Sum.inl R)
            (fun r => @Structure.funMap (L.sum (baireWitnessLang V)) M _ 0 (Sum.inr (t r))
              Fin.elim0) ↔
          SentenceInf.Realize (openBaireSentence L V {x | (f x).eval (atom R t) = true}) M := by
  simp only [diagramSentence, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_iInfAlong, Sigma.forall, Prod.forall,
    BoundedFormulaInf.realize_iff, BoundedFormulaInf.realize_rel, realize_constTerm]
  rfl

/-- Complete `L.sum (baireWitnessLang V)`-sentence cutting out the `PC_{ω₁ω}` class of structures
isomorphic to decoded configurations in `Set.range f`. -/
private noncomputable def baireImageSentence {L : Language.{u, v}} {V : Type w}
    [∀ n, Countable (L.Relations n)] [Countable V]
    (f : (ℕ → ℕ) → RelationalConfiguration L V) : (L.sum (baireWitnessLang V)).Sentenceω :=
  bairePointSentence L V ⊓ carrierInjectiveSentence L V ⊓ carrierSurjectiveSentence L V ⊓
    diagramSentence f

private theorem exists_equiv_of_pcMem_baireImageSentence {L : Language.{u, v}} [L.IsRelational]
    {V : Type w} [∀ n, Countable (L.Relations n)] [Countable V]
    {f : (ℕ → ℕ) → RelationalConfiguration L V} (hf : Continuous f)
    {M : Type w'} [L.Structure M]
    (hPC : (LHom.sumInl : L →ᴸ L.sum (baireWitnessLang V)).PCMem (baireImageSentence f) M) :
    ∃ x : ℕ → ℕ, Nonempty (@Language.Equiv L M V _ (f x).toStructure) := by
  obtain ⟨S, hS, hΘ⟩ := LHom.pcMem_iff.1 hPC
  let _ : (L.sum (baireWitnessLang V)).Structure M := S
  have _ : (LHom.sumInl : L →ᴸ L.sum (baireWitnessLang V)).IsExpansionOn M := hS
  simp only [baireImageSentence, SentenceInf.realize_inf, realize_bairePointSentence,
    realize_carrierInjectiveSentence, realize_carrierSurjectiveSentence,
    realize_diagramSentence] at hΘ
  obtain ⟨⟨⟨hb, hinj⟩, hsurj⟩, hdiag⟩ := hΘ
  choose x hx_true hx_uniq using hb
  have hx (i j : ℕ) :
      @Structure.RelMap (L.sum (baireWitnessLang V)) M _ 0 (Sum.inr (i, j)) Fin.elim0 ↔
        x i = j :=
    ⟨fun h => (hx_uniq i j h).symm, fun h => h ▸ hx_true i⟩
  let cMap : V → M := fun v =>
    @Structure.funMap (L.sum (baireWitnessLang V)) M _ 0 (Sum.inr v) Fin.elim0
  let e : V ≃ M := Equiv.ofBijective cMap ⟨hinj, hsurj⟩
  have hdiag' : ∀ {n : ℕ} (R : L.Relations n) (t : Fin n → V),
      Structure.RelMap R (e ∘ t) ↔ (f x).eval (atom R t) = true := by
    intro n R t
    have hopen : IsOpen {y : ℕ → ℕ | (f y).eval (atom R t) = true} :=
      (isClopen_setOf_eval (atom R t) true).isOpen.preimage hf
    have hrel : Structure.RelMap R (e ∘ t) ↔
        @Structure.RelMap (L.sum (baireWitnessLang V)) M _ n (Sum.inl R) (cMap ∘ t) :=
      Iff.of_eq ((LHom.sumInl : L →ᴸ L.sum (baireWitnessLang V)).map_onRelation R (cMap ∘ t)).symm
    exact hrel.trans ((hdiag R t).trans (realize_openBaireSentence hx hopen))
  let _ : L.Structure V := (f x).toStructure
  let iso : V ≃[L] M :=
    { toEquiv := e
      map_fun' := fun {_} fn => isEmptyElim fn
      map_rel' := fun {_} R t => (hdiag' R t).trans (toStructure_relMap (f x) R t).symm }
  exact ⟨x, ⟨iso.symm⟩⟩

private theorem pcMem_baireImageSentence_of_equiv {L : Language.{u, v}} [L.IsRelational]
    {V : Type w} [∀ n, Countable (L.Relations n)] [Countable V]
    {f : (ℕ → ℕ) → RelationalConfiguration L V} (hf : Continuous f)
    {M : Type w'} [L.Structure M] (x : ℕ → ℕ)
    (iso : @Language.Equiv L M V _ (f x).toStructure) :
    (LHom.sumInl : L →ᴸ L.sum (baireWitnessLang V)).PCMem (baireImageSentence f) M := by
  let _ : L.Structure V := (f x).toStructure
  rw [@StrongHomClass.pcMem_iff L (L.sum (baireWitnessLang V)) LHom.sumInl
    (baireImageSentence f) M V _ (f x).toStructure _ _ _ iso]
  let S_sum : (L.sum (baireWitnessLang V)).Structure V :=
    { funMap := fun {n} fn =>
        match fn with
        | Sum.inl g => isEmptyElim g
        | Sum.inr g =>
          match n with
          | 0 => fun _ => g
          | _ + 1 => PEmpty.elim g
      RelMap := fun {n} r =>
        match r with
        | Sum.inl R => @Structure.RelMap L V (f x).toStructure n R
        | Sum.inr r =>
          match n with
          | 0 => fun _ => x r.1 = r.2
          | _ + 1 => PEmpty.elim r }
  have hExp : @LHom.IsExpansionOn L (L.sum (baireWitnessLang V)) LHom.sumInl V
      (f x).toStructure S_sum :=
    { map_onFunction := fun {_} fn _ => isEmptyElim fn
      map_onRelation := fun {_} _ _ => rfl }
  refine LHom.pcMem_iff.2 ⟨S_sum, hExp, ?_⟩
  let _ : (L.sum (baireWitnessLang V)).Structure V := S_sum
  simp only [baireImageSentence, SentenceInf.realize_inf, realize_bairePointSentence,
    realize_carrierInjectiveSentence, realize_carrierSurjectiveSentence,
    realize_diagramSentence]
  have hx (i j : ℕ) :
      @Structure.RelMap (L.sum (baireWitnessLang V)) V _ 0 (Sum.inr (i, j)) Fin.elim0 ↔
        x i = j := Iff.rfl
  refine ⟨⟨⟨fun i => ⟨x i, rfl, fun j hj => hj.symm⟩, fun _ _ h => h⟩, fun v => ⟨v, rfl⟩⟩, ?_⟩
  intro n R t
  have hopen : IsOpen {y : ℕ → ℕ | (f y).eval (atom R t) = true} :=
    (isClopen_setOf_eval (atom R t) true).isOpen.preimage hf
  exact (toStructure_relMap (f x) R t).trans (realize_openBaireSentence hx hopen).symm

/-- A structure `M` lies in the projective class of `baireImageSentence f` exactly when `M` is
isomorphic to `(f x).toStructure` for some `x : ℕ → ℕ`. -/
private theorem pcMem_baireImageSentence_iff {L : Language.{u, v}} [L.IsRelational] {V : Type w}
    [∀ n, Countable (L.Relations n)] [Countable V]
    {f : (ℕ → ℕ) → RelationalConfiguration L V} (hf : Continuous f)
    (M : Type w') [L.Structure M] :
    (LHom.sumInl : L →ᴸ L.sum (baireWitnessLang V)).PCMem (baireImageSentence f) M ↔
      ∃ x : ℕ → ℕ, Nonempty (@Language.Equiv L M V _ (f x).toStructure) :=
  ⟨exists_equiv_of_pcMem_baireImageSentence hf,
    fun ⟨x, ⟨iso⟩⟩ => pcMem_baireImageSentence_of_equiv hf x iso⟩

/-- Countable-vocabulary case of López–Escobar separation: on a countable carrier in a countable
relational language, two analytic sets with no isomorphic pair are separated by an `L_{ω₁ω}`
sentence. -/
private theorem exists_sentence_separating_of_countable {L : Language.{u, v}} [L.IsRelational]
    [∀ n, Countable (L.Relations n)] {V : Type w} [Countable V]
    {A B : Set (RelationalConfiguration L V)} (hA : AnalyticSet A) (hB : AnalyticSet B)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, ¬ isoSetoid L V a b) :
    ∃ θ : L.Sentenceω, A ⊆ modelsOf θ ∧ Disjoint B (modelsOf θ) := by
  cases isEmpty_or_nonempty V with
  | inl _ =>
    have hd : Disjoint A B :=
      disjoint_left.2 fun a ha hb => hAB a ha a hb ((isoSetoid L V).refl a)
    obtain ⟨D, hAD, hBD, hD⟩ := hA.measurablySeparable hB hd
    obtain ⟨θ, rfl⟩ := exists_modelsOf_eq_of_isEmpty hD
    exact ⟨θ, hAD, hBD⟩
  | inr _ =>
    obtain ⟨X, _, _, f₀, hf₀, rfl⟩ := analyticSet_iff_exists_polishSpace_range.1 hA
    obtain ⟨Y, _, _, g₀, hg₀, rfl⟩ := analyticSet_iff_exists_polishSpace_range.1 hB
    cases isEmpty_or_nonempty X with
    | inl _ => exact ⟨⊥, by simp [range_eq_empty], by simp⟩
    | inr _ =>
      cases isEmpty_or_nonempty Y with
      | inl _ => exact ⟨⊤, by simp, by simp [range_eq_empty]⟩
      | inr _ =>
        obtain ⟨pX, hpX, hsurjX⟩ := PolishSpace.exists_nat_nat_continuous_surjective X
        obtain ⟨pY, hpY, hsurjY⟩ := PolishSpace.exists_nat_nat_continuous_surjective Y
        let f := f₀ ∘ pX
        let g := g₀ ∘ pY
        have hf : Continuous f := hf₀.comp hpX
        have hg : Continuous g := hg₀.comp hpY
        rw [← hsurjX.range_comp, ← hsurjY.range_comp] at hAB ⊢
        obtain ⟨θ, h₁, h₂⟩ :=
          pcSeparation.{u, v, w, 0, w, 0, w, w} (baireImageSentence f) (baireImageSentence g)
            (fun M _ _ _ hMf hMg => by
              obtain ⟨x, ⟨ef⟩⟩ := (pcMem_baireImageSentence_iff hf M).1 hMf
              obtain ⟨y, ⟨eg⟩⟩ := (pcMem_baireImageSentence_iff hg M).1 hMg
              exact hAB (f x) (mem_range_self x) (g y) (mem_range_self y)
                (isoSetoid_apply.2 ⟨@Language.Equiv.comp L V M (f x).toStructure _
                  V (g y).toStructure eg (@Language.Equiv.symm L M V _ (f x).toStructure ef)⟩))
        refine ⟨θ, ?_, disjoint_left.2 ?_⟩
        · rintro _ ⟨x, rfl⟩
          rw [mem_modelsOf]
          exact @h₁ V (f x).toStructure _
            ((@pcMem_baireImageSentence_iff L _ V _ _ f hf V (f x).toStructure).2
              ⟨x, ⟨@Language.Equiv.refl L V (f x).toStructure⟩⟩)
        · rintro _ ⟨y, rfl⟩ hθ
          rw [mem_modelsOf] at hθ
          exact @h₂ V (g y).toStructure _
            ((@pcMem_baireImageSentence_iff L _ V _ _ g hg V (g y).toStructure).2
              ⟨y, ⟨@Language.Equiv.refl L V (g y).toStructure⟩⟩) hθ

end BairePC

/-! ### Reduction from arbitrary relational languages and main theorems -/

section Main

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w}

/-- For continuous families `f : X → RelationalConfiguration L V` and
`g : Y → RelationalConfiguration L V` from Polish spaces on a countable carrier with no isomorphic
pair, Lindelöfness of `Equiv.Perm V × X × Y` isolates a countable set `R₀` of relation symbols whose
reducts already contain no isomorphic pair. -/
private theorem exists_countable_relations_separating_continuous [Countable V]
    {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [TopologicalSpace Y] [PolishSpace Y]
    {f : X → RelationalConfiguration L V} (hf : Continuous f)
    {g : Y → RelationalConfiguration L V} (hg : Continuous g)
    (hfg : ∀ x y, ¬ isoSetoid L V (f x) (g y)) :
    ∃ R₀ : Set (Σ n, L.Relations n), R₀.Countable ∧
      ∀ x y, ¬ isoSetoid (symbSublang ∅ R₀) V
        ((symbSublangIncl ∅ R₀).reductConfiguration (f x))
        ((symbSublangIncl ∅ R₀).reductConfiguration (g y)) := by
  let _ : TopologicalSpace V := ⊥
  have : DiscreteTopology V := ⟨rfl⟩
  let Z := Equiv.Perm V × X × Y
  let U : (Σ n, L.Relations n × (Fin n → V)) → Set Z := fun p =>
    {z | (z.1 • f z.2.1).eval (atom p.2.1 p.2.2) ≠ (g z.2.2).eval (atom p.2.1 p.2.2)}
  have hU_open (p : Σ n, L.Relations n × (Fin n → V)) : IsOpen (U p) := by
    have hinv : Continuous fun σ : Equiv.Perm V => (⇑(σ⁻¹) : V → V) :=
      Equiv.Perm.isEmbedding_prodMk_coe_coe_inv.continuous.snd
    have hleft : Continuous fun z : Z => (z.1 • f z.2.1).eval (atom p.2.1 p.2.2) := by
      simp only [perm_smul_def]
      exact (continuous_eval _).comp <| continuous_uncurry_restrict.comp <|
        (hinv.comp continuous_fst).prodMk (hf.comp (continuous_fst.comp continuous_snd))
    have hright : Continuous fun z : Z => (g z.2.2).eval (atom p.2.1 p.2.2) :=
      (continuous_eval _).comp (hg.comp (continuous_snd.comp continuous_snd))
    exact isOpen_ne_fun hleft hright
  have hU_cover : (⋃ p : Σ n, L.Relations n × (Fin n → V), U p) = univ := by
    refine eq_univ_iff_forall.2 fun ⟨σ, x, y⟩ => ?_
    have hne : σ • f x ≠ g y := fun heq => hfg x y (heq ▸ isoSetoid_perm_smul σ (f x))
    obtain ⟨a, ha⟩ : ∃ a : Atom L V, (σ • f x).eval a ≠ (g y).eval a := by
      by_contra! hall
      exact hne (RelationalConfiguration.ext hall)
    induction a using Atom.induction_atom with
    | h R t => exact mem_iUnion.2 ⟨⟨_, R, t⟩, ha⟩
  obtain ⟨A₀, hA₀_count, hA₀_eq⟩ := isOpen_iUnion_countable U hU_open
  rw [hU_cover] at hA₀_eq
  refine ⟨(fun p => ⟨p.1, p.2.1⟩) '' A₀, hA₀_count.image _, fun x y hxy => ?_⟩
  obtain ⟨σ, hσ⟩ := isoSetoid_iff_exists_perm_smul_eq.1 hxy
  rw [← (symbSublangIncl ∅ _).reductConfiguration_perm_smul] at hσ
  have hz : (σ, x, y) ∈ ⋃ p ∈ A₀, U p := hA₀_eq.symm ▸ mem_univ (σ, x, y)
  obtain ⟨⟨n, R, t⟩, hpA₀, hzp⟩ := mem_iUnion₂.1 hz
  let r₀ : (symbSublang ∅ ((fun p => ⟨p.1, p.2.1⟩) '' A₀)).Relations n :=
    ⟨R, ⟨⟨n, R, t⟩, hpA₀, rfl⟩⟩
  have heval := congrArg (fun c => c.eval (atom r₀ t)) hσ
  simp only [LHom.eval_reductConfiguration, LHom.onAtom_atom, symbSublangIncl_onRelation, r₀]
    at heval
  exact hzp heval

/-- **López–Escobar separation for disjoint-up-to-isomorphism analytic sets.** On a countable
carrier, in a relational language of arbitrary cardinality, if `A` and `B` are analytic sets of
configurations such that no member of `A` is isomorphic to a member of `B`, there is an `L_{ω₁ω}`
sentence `θ` with `A ⊆ modelsOf θ` and `Disjoint B (modelsOf θ)`. Neither `A` nor `B` need be
isomorphism invariant, and `L` need not have countably many relation symbols. -/
theorem exists_sentence_separating_of_forall_not_isoSetoid [Countable V]
    {A B : Set (RelationalConfiguration L V)} (hA : AnalyticSet A) (hB : AnalyticSet B)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, ¬ isoSetoid L V a b) :
    ∃ θ : L.Sentenceω, A ⊆ modelsOf θ ∧ Disjoint B (modelsOf θ) := by
  obtain ⟨X, _, _, f, hf, rfl⟩ := analyticSet_iff_exists_polishSpace_range.1 hA
  obtain ⟨Y, _, _, g, hg, rfl⟩ := analyticSet_iff_exists_polishSpace_range.1 hB
  obtain ⟨R₀, hR₀, hsep⟩ := exists_countable_relations_separating_continuous hf hg
    fun x y => hAB (f x) (mem_range_self x) (g y) (mem_range_self y)
  have : Countable R₀ := hR₀.to_subtype
  let ι₀ := symbSublangIncl (L := L) ∅ R₀
  have hA' : AnalyticSet (ι₀.reductConfiguration '' range f) :=
    (analyticSet_range_of_polishSpace hf).image_of_continuous ι₀.continuous_reductConfiguration
  have hB' : AnalyticSet (ι₀.reductConfiguration '' range g) :=
    (analyticSet_range_of_polishSpace hg).image_of_continuous ι₀.continuous_reductConfiguration
  obtain ⟨θ₀, hθ₀_sub, hθ₀_disj⟩ :=
    exists_sentence_separating_of_countable hA' hB' (fun _ hc₀ _ hd₀ hcd => by
      obtain ⟨_, ⟨x, rfl⟩, rfl⟩ := hc₀
      obtain ⟨_, ⟨y, rfl⟩, rfl⟩ := hd₀
      exact hsep x y hcd)
  refine ⟨ι₀.onBoundedFormulaInf θ₀, ?_, disjoint_left.2 ?_⟩
  · rintro c ⟨x, rfl⟩
    rw [mem_modelsOf, ι₀.realize_sentenceInf_reductConfiguration, ← mem_modelsOf]
    exact hθ₀_sub ⟨f x, mem_range_self x, rfl⟩
  · rintro c ⟨y, rfl⟩ hc
    rw [mem_modelsOf, ι₀.realize_sentenceInf_reductConfiguration, ← mem_modelsOf] at hc
    exact disjoint_left.1 hθ₀_disj ⟨g y, mem_range_self y, rfl⟩ hc

/-- **López–Escobar separation.** On a countable carrier, in a relational language of arbitrary
cardinality, if `A` and `B` are disjoint analytic sets of configurations and `B` is isomorphism
invariant, there is an `L_{ω₁ω}` sentence `θ` with `A ⊆ modelsOf θ` and
`Disjoint B (modelsOf θ)`. -/
theorem exists_sentence_separating [Countable V]
    {A B : Set (RelationalConfiguration L V)} (hA : AnalyticSet A) (hB : AnalyticSet B)
    (hB_inv : IsomorphismInvariant B) (hAB : Disjoint A B) :
    ∃ θ : L.Sentenceω, A ⊆ modelsOf θ ∧ Disjoint B (modelsOf θ) :=
  exists_sentence_separating_of_forall_not_isoSetoid hA hB fun _ ha _ hb hab =>
    disjoint_left.1 hAB ha ((hB_inv.mem_iff hab).2 hb)

/-- **López–Escobar's theorem.** On a countable carrier, in a relational language of arbitrary
cardinality, the subsets of `RelationalConfiguration L V` of the form `modelsOf θ` for an `L_{ω₁ω}`
sentence `θ` are precisely the isomorphism-invariant measurable sets. -/
theorem exists_modelsOf_eq_iff [Countable V] {B : Set (RelationalConfiguration L V)} :
    (∃ θ : L.Sentenceω, modelsOf (V := V) θ = B) ↔ MeasurableSet B ∧ IsomorphismInvariant B := by
  refine ⟨fun ⟨θ, hθ⟩ => hθ ▸ ⟨measurableSet_modelsOf θ, isomorphismInvariant_modelsOf θ⟩,
    fun ⟨hB_meas, hB_inv⟩ => ?_⟩
  obtain ⟨R₀, hR₀, B₀, hB₀_meas, rfl⟩ := exists_countable_sublanguage_of_measurableSet hB_meas
  have : Countable R₀ := hR₀.to_subtype
  let ι₀ := symbSublangIncl (L := L) ∅ R₀
  have hB₀_inv : IsomorphismInvariant B₀ := by
    rw [isomorphismInvariant_iff_isInvariantBlock] at hB_inv ⊢
    rintro σ _ ⟨c₀, hc₀, rfl⟩
    obtain ⟨c, rfl⟩ := reductConfiguration_symbSublang_surjective ∅ R₀ c₀
    have hsmul : σ • ι₀.reductConfiguration c = ι₀.reductConfiguration (σ • c) :=
      (ι₀.reductConfiguration_perm_smul σ c).symm
    dsimp only
    rw [hsmul]
    exact hB_inv σ (smul_mem_smul_set hc₀)
  obtain ⟨θ₀, hsub, hdisj⟩ := exists_sentence_separating hB₀_meas.analyticSet
    hB₀_meas.compl.analyticSet hB₀_inv.compl disjoint_compl_right
  have hθ₀ : modelsOf θ₀ = B₀ :=
    (disjoint_compl_left_iff_subset.1 hdisj).antisymm hsub
  refine ⟨ι₀.onBoundedFormulaInf θ₀, ?_⟩
  ext c
  rw [mem_modelsOf, ι₀.realize_sentenceInf_reductConfiguration, ← mem_modelsOf, hθ₀, mem_preimage]

/-- **Relative López–Escobar.** Let `X` be a standard Borel space and
`f : X → RelationalConfiguration L V` a measurable family of configurations on a countable carrier
in a countable relational vocabulary. For any measurable set `U ⊆ X` saturated under isomorphism of
`f`, there is an `L_{ω₁ω}` sentence `θ` such that `f x ∈ modelsOf θ ↔ x ∈ U` for every `x : X`. -/
theorem exists_sentence_mem_modelsOf_iff {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [∀ n, Countable (L.Relations n)] [Countable V]
    {f : X → RelationalConfiguration L V} (hf : Measurable f) {U : Set X} (hU : MeasurableSet U)
    (hinv : ∀ x y, isoSetoid L V (f x) (f y) → (x ∈ U ↔ y ∈ U)) :
    ∃ θ : L.Sentenceω, ∀ x, f x ∈ modelsOf θ ↔ x ∈ U := by
  have hAU : AnalyticSet (f '' U) := hU.analyticSet_image hf
  have hBU : AnalyticSet (f '' Uᶜ) := hU.compl.analyticSet_image hf
  obtain ⟨θ, hsub, hdisj⟩ := exists_sentence_separating_of_forall_not_isoSetoid hAU hBU
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
      exact hy ((hinv x y hxy).1 hx))
  refine ⟨θ, fun x => ⟨fun hθ => by_contra fun hx => ?_, fun hx => hsub ⟨x, hx, rfl⟩⟩⟩
  exact disjoint_left.1 hdisj ⟨x, mem_compl hx, rfl⟩ hθ

end Main

end TauCeti.RelationalConfiguration
