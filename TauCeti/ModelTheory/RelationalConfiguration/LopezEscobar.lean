/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Basic
public import TauCeti.ModelTheory.RelationalConfiguration.Isomorphism
public import TauCeti.ModelTheory.RelationalConfiguration.ModelsOf
import TauCeti.ModelTheory.Infinitary.CodedConnectives
import TauCeti.ModelTheory.Interpolation.Craig

/-!
# The López–Escobar separation and characterization theorems

On a countable carrier `V` in a relational language `L` with countably many relation symbols of
each arity, every `L_{ω₁ω}` model class `modelsOf θ` is Borel and isomorphism invariant
(`measurableSet_modelsOf`, `FirstOrder.Language.Equiv.mem_modelsOf_iff`). This file proves the
converse **López–Escobar separation theorem** (`exists_sentence_separating_of_disjoint_image`,
`exists_sentence_separating`) and its consequences:

* **Separation of analytic sets.** If `A` and `B` are analytic sets of configurations on `V` such
  that no configuration in `A` is isomorphic to a configuration in `B` (in particular, if `B` is
  isomorphism invariant and disjoint from `A`), then some sentence `θ : L.Sentenceω` satisfies
  `A ⊆ modelsOf θ` and `Disjoint B (modelsOf θ)`.
* **Classical López–Escobar theorem** (`exists_modelsOf_eq_iff`). A subset of
  `RelationalConfiguration L V` is `modelsOf θ` for some `θ : L.Sentenceω` if and only if it is
  Borel and isomorphism invariant.
* **Relative López–Escobar theorem** (`exists_sentence_mem_modelsOf_iff`,
  `exists_sentence_preimage_modelsOf_eq`). For a standard Borel space `X`, a Borel map
  `f : X → RelationalConfiguration L V`, and a Borel subset `U ⊆ X` closed under isomorphism of
  images under `f`, some sentence `θ : L.Sentenceω` satisfies `f x ∈ modelsOf θ ↔ x ∈ U` for all
  `x : X`.
* **Cantor recovery** (`exists_sentences_mem_modelsOf_iff`). For a Borel map
  `f : (ℕ → Bool) → RelationalConfiguration L V` sending distinct sequences to non-isomorphic
  configurations, there are sentences `θ : ℕ → L.Sentenceω` recovering every coordinate via
  `f x ∈ modelsOf (θ n) ↔ x n = true`.

## Proof outline

For a nonempty countable carrier `V`, a nonempty analytic subset `A` of the Polish space
`RelationalConfiguration L V` is the range of a continuous map `f : (ℕ → ℕ) →
RelationalConfiguration L V`. Expanding `L` by constants naming each vertex `v : V` and nullary
predicates `P(n, m)` naming the graph of a Baire-space witness `x : ℕ → ℕ`, a single
`(L.sum (auxLang V))`-sentence `analyticSentence f` expresses that the vertex constants biject
onto the carrier, `P` is the graph of a total function `x : ℕ → ℕ`, and each relational atom `a`
holds at the named vertices precisely when `x` lies in a basic prefix cylinder contained in the
clopen preimage `{y | (f y).eval a = true}`. An `L`-structure therefore belongs to the projective
class `LHom.sumInl.PCMem (analyticSentence f)` iff it is isomorphic to `(f x).toStructure` for some
`x : ℕ → ℕ`. Projective-class separation (`FirstOrder.Language.pcSeparation`) then separates any two
such saturations having no common countable nonempty model.

On an empty carrier `V`, isomorphism of configurations is equality, Lusin's separation theorem
(`MeasureTheory.AnalyticSet.measurablySeparable`) separates disjoint analytic sets by a Borel set,
and every Borel set of configurations is generated from nullary relational cylinders by complements
and countable unions, hence is already `modelsOf θ` for some `θ : L.Sentenceω`.

## Main results

* `TauCeti.RelationalConfiguration.isomorphismInvariant_modelsOf`: every infinitary model class
  `modelsOf φ` is isomorphism invariant, with no countability assumptions on `L`, `V`, or `ι`.
* `TauCeti.RelationalConfiguration.exists_sentence_separating_of_disjoint_image`: analytic sets on
  a countable carrier with disjoint isomorphism-class images are separated by an `L_{ω₁ω}` sentence.
* `TauCeti.RelationalConfiguration.exists_sentence_separating`: **López–Escobar separation**, when
  `B` is isomorphism invariant and disjoint from `A`.
* `TauCeti.RelationalConfiguration.exists_modelsOf_eq_iff`: **López–Escobar theorem**, a set of
  configurations is `modelsOf θ` for some `θ : L.Sentenceω` iff it is Borel and isomorphism
  invariant.
* `TauCeti.RelationalConfiguration.exists_sentence_mem_modelsOf_iff` and
  `TauCeti.RelationalConfiguration.exists_sentence_preimage_modelsOf_eq`: **relative López–Escobar**
  along a Borel map from a standard Borel space.
* `TauCeti.RelationalConfiguration.exists_sentences_mem_modelsOf_iff`: **Cantor recovery** of bits
  along a Borel antichain from `ℕ → Bool`.

## References

* E. G. K. Lopez-Escobar, *An interpolation theorem for denumerably long formulas*, Fundamenta
  Mathematicae 57 (1965), 253–272.
* David Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46, Cambridge
  University Press, 2016, Chapter 4 (López–Escobar's theorem via `PC_{ω₁ω}` separation).
* Su Gao, *Invariant Descriptive Set Theory*, Monographs and Surveys in Pure and Applied
  Mathematics 150, CRC Press, 2009, §11.3 (invariant Borel sets and separation).
* Adapted from `InfinitaryLogic/Descriptive/LopezEscobar.lean` and
  `InfinitaryLogic/Descriptive/SentenceRecovery.lean` in Cameron Freer's
  `cameronfreer/infinitary-logic` at checkpoint `518a366cba97b1ae8c4dc64a297a396939bc3e0b`
  (Apache-2.0), generalized here to arbitrary countable carriers (including finite and empty
  carriers), arbitrary language universes, and relative separation on arbitrary standard Borel
  spaces.
-/

public section

universe u v w w' uX

open FirstOrder FirstOrder.Language MeasureTheory Set

namespace TauCeti.RelationalConfiguration

/-! ### Baire-space cylinders and open sets -/

section BaireOpen

/-- Prefix cylinder in Baire space `ℕ → ℕ` cut out by a finite word `w : List ℕ`. -/
private def baireCyl (w : List ℕ) : Set (ℕ → ℕ) :=
  {x | ∀ i : Fin w.length, x i = w[i]}

/-- Every open set in `ℕ → ℕ` is covered by the prefix cylinders `baireCyl w` contained in it. -/
private theorem mem_iff_exists_baireCyl {U : Set (ℕ → ℕ)} (hU : IsOpen U) (x : ℕ → ℕ) :
    x ∈ U ↔ ∃ w : List ℕ, baireCyl w ⊆ U ∧ x ∈ baireCyl w := by
  refine ⟨fun hx => ?_, fun ⟨_, hwU, hxw⟩ => hwU hxw⟩
  obtain ⟨I, u, hu, hpi⟩ := isOpen_pi_iff.mp hU x hx
  set N := I.sup id + 1
  let w := List.ofFn fun i : Fin N => x i
  refine ⟨w, fun y hy => hpi fun n hn => ?_,
    fun i => by simp only [w, List.getElem_ofFn, Fin.getElem_fin]⟩
  have hlt : n < w.length := by
    rw [List.length_ofFn]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)
  have hyn : y n = x n := by
    simpa only [w, Fin.getElem_fin, List.getElem_ofFn] using hy ⟨n, hlt⟩
  rw [hyn]
  exact (hu n hn).2

end BaireOpen

/-! ### Projective-class presentation of continuous images of `ℕ → ℕ` -/

section AnalyticPresentation

variable {L : Language.{u, v}} {V : Type w}

/-- Auxiliary vocabulary naming each carrier vertex `v : V` by a constant symbol and naming pairs
`(n, m) : ℕ × ℕ` by nullary relation symbols for the graph of a Baire-space witness. -/
private def auxLang (V : Type w) : Language.{w, 0} where
  Functions
    | 0 => V
    | _ + 1 => PEmpty
  Relations
    | 0 => ℕ × ℕ
    | _ + 1 => PEmpty

/-- Auxiliary constant symbol in `auxLang V` naming `v : V`. -/
private def auxConst (v : V) : (auxLang V).Functions 0 := v

/-- Auxiliary nullary relation symbol in `auxLang V` naming `(n, m) : ℕ × ℕ`. -/
private def auxGraphRel (V : Type w) (n m : ℕ) : (auxLang V).Relations 0 := (n, m)

/-- Constant term in `L.sum (auxLang V)` naming `v : V`. -/
private def carrierConst {α : Type*} (v : V) : (L.sum (auxLang V)).Term α :=
  .func (LHom.sumInr.onFunction (auxConst v)) Fin.elim0

/-- Interpretation of the carrier constants in an `(L.sum (auxLang V))`-structure on `M`. -/
private def carrierInterp {M : Type w'} [(L.sum (auxLang V)).Structure M] (v : V) : M :=
  Structure.funMap ((LHom.sumInr : auxLang V →ᴸ L.sum (auxLang V)).onFunction (auxConst v))
    Fin.elim0

@[simp]
private theorem realize_carrierConst {M : Type w'} [(L.sum (auxLang V)).Structure M] {α : Type*}
    (val : α → M) (v : V) :
    (carrierConst (L := L) v).realize val = carrierInterp (L := L) (V := V) v := by
  rw [carrierConst, carrierInterp, Term.realize_func]
  exact congrArg _ (Subsingleton.elim _ _)

/-- Nullary atomic formula in `L.sum (auxLang V)` asserting `P(n, m)`. -/
private def graphAtom {k : ℕ} (n m : ℕ) : (L.sum (auxLang V)).BoundedFormulaω Empty k :=
  .rel (LHom.sumInr.onRelation (auxGraphRel V n m)) Fin.elim0

/-- Interpretation of the nullary graph predicates in an `(L.sum (auxLang V))`-structure on `M`. -/
private def graphInterp {M : Type w'} [(L.sum (auxLang V)).Structure M] (n m : ℕ) : Prop :=
  Structure.RelMap ((LHom.sumInr : auxLang V →ᴸ L.sum (auxLang V)).onRelation (auxGraphRel V n m))
    (Fin.elim0 : Fin 0 → M)

@[simp]
private theorem realize_graphAtom {M : Type w'} [(L.sum (auxLang V)).Structure M] {k : ℕ}
    (val : Empty → M) (xs : Fin k → M) (n m : ℕ) :
    (graphAtom (L := L) (V := V) (k := k) n m).Realize val xs ↔
      graphInterp (L := L) (V := V) (M := M) n m := by
  rw [graphAtom, graphInterp, BoundedFormulaInf.realize_rel]
  exact iff_of_eq (congrArg _ (Subsingleton.elim _ _))

/-- Sentence asserting injectivity of the carrier constants `c_v` (`v : V`). -/
private noncomputable def injSentence (V : Type w) [Countable V] :
    (L.sum (auxLang V)).Sentenceω :=
  open Classical in
  let cVV := IndexCoding.ofEncodableWith (Encodable.ofCountable (V × V))
  BoundedFormulaInf.iInfAlong cVV fun p =>
    if p.1 = p.2 then ⊤
    else (BoundedFormulaInf.equal (carrierConst (L := L) p.1) (carrierConst (L := L) p.2)).not

private theorem realize_injSentence {M : Type w'} [(L.sum (auxLang V)).Structure M] [Countable V] :
    SentenceInf.Realize (injSentence (L := L) V) M ↔
      Function.Injective (carrierInterp (L := L) (V := V) (M := M)) := by
  classical
  simp only [injSentence, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_iInfAlong]
  refine ⟨fun h v₁ v₂ heq => by_contra fun hne => ?_, fun hinj ⟨v₁, v₂⟩ => ?_⟩
  · have hp := h (v₁, v₂)
    simp only [hne, ↓reduceIte, BoundedFormulaInf.realize_not, BoundedFormulaInf.realize_equal,
      realize_carrierConst] at hp
    exact hp heq
  · by_cases h : v₁ = v₂
    · simp [h]
    · simp only [h, ↓reduceIte, BoundedFormulaInf.realize_not, BoundedFormulaInf.realize_equal,
        realize_carrierConst]
      exact fun heq => h (hinj heq)

/-- Sentence asserting surjectivity of the carrier constants `c_v` (`v : V`). -/
private noncomputable def surjSentence (V : Type w) [Countable V] :
    (L.sum (auxLang V)).Sentenceω :=
  let cV := IndexCoding.ofEncodableWith (Encodable.ofCountable V)
  (BoundedFormulaInf.iSupAlong cV fun v =>
    BoundedFormulaInf.equal (carrierConst (L := L) v) (.var (Sum.inr (Fin.last 0)))).all

private theorem realize_surjSentence {M : Type w'} [(L.sum (auxLang V)).Structure M] [Countable V] :
    SentenceInf.Realize (surjSentence (L := L) V) M ↔
      Function.Surjective (carrierInterp (L := L) (V := V) (M := M)) := by
  simp only [surjSentence, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_all, BoundedFormulaInf.realize_iSupAlong,
    BoundedFormulaInf.realize_equal, Term.realize_var, Sum.elim_inr, realize_carrierConst,
    Fin.snoc_last]
  rfl

/-- Sentence asserting that the nullary predicates `P(n, m)` form the graph of a function
`ℕ → ℕ`. -/
private def funcGraphSentence (V : Type w) : (L.sum (auxLang V)).Sentenceω :=
  BoundedFormulaInf.iInf fun n : ℕ =>
    (BoundedFormulaInf.iSup fun m : ℕ => graphAtom (L := L) (V := V) n m) ⊓
    (BoundedFormulaInf.iInf fun m₁ : ℕ => BoundedFormulaInf.iInf fun m₂ : ℕ =>
      if m₁ = m₂ then ⊤
      else (graphAtom (L := L) (V := V) n m₁).imp (graphAtom (L := L) (V := V) n m₂).not)

private theorem realize_funcGraphSentence {M : Type w'} [(L.sum (auxLang V)).Structure M] :
    SentenceInf.Realize (funcGraphSentence (L := L) V) M ↔
      ∃ x : ℕ → ℕ, ∀ n m, graphInterp (L := L) (V := V) (M := M) n m ↔ x n = m := by
  simp only [funcGraphSentence, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_iInf, BoundedFormulaInf.realize_inf, BoundedFormulaInf.realize_iSup,
    realize_graphAtom]
  constructor
  · intro h
    choose x hx using fun n => (h n).1
    refine ⟨x, fun n m => ⟨fun hnm => ?_, fun hnm => hnm ▸ hx n⟩⟩
    by_contra hne
    have hu := (h n).2 m (x n)
    simp only [Ne.symm hne, ↓reduceIte, BoundedFormulaInf.realize_imp,
      BoundedFormulaInf.realize_not, realize_graphAtom] at hu
    exact hu hnm (hx n)
  · rintro ⟨x, hx⟩ n
    refine ⟨⟨x n, (hx n (x n)).mpr rfl⟩, fun m₁ m₂ => ?_⟩
    by_cases heq : m₁ = m₂
    · simp [heq]
    · simp only [heq, ↓reduceIte, BoundedFormulaInf.realize_imp, BoundedFormulaInf.realize_not,
        realize_graphAtom, hx]
      rintro rfl rfl
      exact heq rfl

/-- Sentence asserting membership of the Baire-space witness in `baireCyl w`. -/
private def cylSentence (V : Type w) (w : List ℕ) : (L.sum (auxLang V)).Sentenceω :=
  BoundedFormulaInf.iInf fun k : ℕ =>
    if hk : k < w.length then graphAtom (L := L) (V := V) k w[k] else ⊤

private theorem realize_cylSentence_of_graph {M : Type w'} [(L.sum (auxLang V)).Structure M]
    {x : ℕ → ℕ} (hx : ∀ n m, graphInterp (L := L) (V := V) (M := M) n m ↔ x n = m)
    (w : List ℕ) :
    (cylSentence (L := L) V w).Realize Empty.elim (default : Fin 0 → M) ↔ x ∈ baireCyl w := by
  simp only [cylSentence, BoundedFormulaInf.realize_iInf, baireCyl, mem_ofPred_eq, Fin.getElem_fin]
  refine ⟨fun h i => ?_, fun h k => ?_⟩
  · simpa only [i.2, ↓reduceDIte, realize_graphAtom, hx] using h i.1
  · split_ifs with hk
    · simpa only [realize_graphAtom, hx] using h ⟨k, hk⟩
    · simp

/-- Sentence expressing membership of the Baire-space witness in an open set `U ⊆ (ℕ → ℕ)` as a
countable disjunction over prefix words `w : List ℕ` with `baireCyl w ⊆ U`. -/
private noncomputable def openSetSentence (V : Type w) (U : Set (ℕ → ℕ)) :
    (L.sum (auxLang V)).Sentenceω :=
  open Classical in
  BoundedFormulaInf.iSupAlong (IndexCoding.ofEncodable (List ℕ)) fun w =>
    if baireCyl w ⊆ U then cylSentence (L := L) V w else ⊥

private theorem realize_openSetSentence_of_graph {M : Type w'} [(L.sum (auxLang V)).Structure M]
    {x : ℕ → ℕ} (hx : ∀ n m, graphInterp (L := L) (V := V) (M := M) n m ↔ x n = m)
    {U : Set (ℕ → ℕ)} (hU : IsOpen U) :
    (openSetSentence (L := L) V U).Realize Empty.elim (default : Fin 0 → M) ↔ x ∈ U := by
  classical
  simp only [openSetSentence, BoundedFormulaInf.realize_iSupAlong]
  rw [mem_iff_exists_baireCyl hU]
  refine exists_congr fun w => ?_
  by_cases hw : baireCyl w ⊆ U
  · simp only [hw, ↓reduceIte, true_and]
    exact realize_cylSentence_of_graph hx w
  · simp [hw]

/-- Atomic sentence in `L.sum (auxLang V)` asserting that `R(t₀, …, t_{n-1})` holds at the carrier
constants `c_v`. -/
private def atomSentence {n : ℕ} (R : L.Relations n) (t : Fin n → V) :
    (L.sum (auxLang V)).Sentenceω :=
  .rel (LHom.sumInl.onRelation R) fun i => carrierConst (L := L) (t i)

private theorem realize_atomSentence {M : Type w'} [L.Structure M]
    [(L.sum (auxLang V)).Structure M] [(LHom.sumInl : L →ᴸ L.sum (auxLang V)).IsExpansionOn M]
    {n : ℕ} (R : L.Relations n) (t : Fin n → V) :
    (atomSentence R t).Realize Empty.elim (default : Fin 0 → M) ↔
      Structure.RelMap R (carrierInterp (L := L) (V := V) (M := M) ∘ t) := by
  simp only [atomSentence, BoundedFormulaInf.realize_rel, realize_carrierConst]
  exact Iff.of_eq ((LHom.sumInl : L →ᴸ L.sum (auxLang V)).map_onRelation R _)

/-- Sentence asserting that every `L`-atom on the carrier constants agrees with `(f x).eval`. -/
private noncomputable def atomAgreementSentence [∀ n, Countable (L.Relations n)] [Countable V]
    (f : (ℕ → ℕ) → RelationalConfiguration L V) : (L.sum (auxLang V)).Sentenceω :=
  BoundedFormulaInf.iInf fun n : ℕ =>
    let cRT := IndexCoding.ofEncodableWith (Encodable.ofCountable (L.Relations n × (Fin n → V)))
    BoundedFormulaInf.iInfAlong cRT fun p =>
      (atomSentence p.1 p.2).iff
        (openSetSentence (L := L) V {y | (f y).eval (atom p.1 p.2) = true})

private theorem realize_atomAgreementSentence_of_graph [∀ n, Countable (L.Relations n)]
    [Countable V] {f : (ℕ → ℕ) → RelationalConfiguration L V} (hf : Continuous f)
    {M : Type w'} [L.Structure M] [(L.sum (auxLang V)).Structure M]
    [(LHom.sumInl : L →ᴸ L.sum (auxLang V)).IsExpansionOn M] {x : ℕ → ℕ}
    (hx : ∀ n m, graphInterp (L := L) (V := V) (M := M) n m ↔ x n = m) :
    SentenceInf.Realize (atomAgreementSentence f) M ↔
      ∀ {n : ℕ} (R : L.Relations n) (t : Fin n → V),
        Structure.RelMap R (carrierInterp (L := L) (V := V) (M := M) ∘ t) ↔
          (f x).eval (atom R t) = true := by
  simp only [atomAgreementSentence, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_iInf, BoundedFormulaInf.realize_iInfAlong,
    BoundedFormulaInf.realize_iff]
  have hopen (a : Atom L V) : IsOpen {y : ℕ → ℕ | (f y).eval a = true} :=
    (isClopen_setOf_eval a true).isOpen.preimage hf
  refine ⟨fun h n R t => ?_, fun h n ⟨R, t⟩ => ?_⟩
  · have ha := h n (R, t)
    rwa [realize_atomSentence, realize_openSetSentence_of_graph hx (hopen (atom R t)),
      mem_ofPred_eq] at ha
  · rw [realize_atomSentence, realize_openSetSentence_of_graph hx (hopen (atom R t)),
      mem_ofPred_eq]
    exact h R t

/-- Full `(L.sum (auxLang V))`-sentence presenting the isomorphism saturation of `range f` for a
continuous `f : (ℕ → ℕ) → RelationalConfiguration L V`. -/
private noncomputable def analyticSentence [∀ n, Countable (L.Relations n)] [Countable V]
    (f : (ℕ → ℕ) → RelationalConfiguration L V) : (L.sum (auxLang V)).Sentenceω :=
  injSentence (L := L) V ⊓ surjSentence (L := L) V ⊓
    funcGraphSentence (L := L) V ⊓ atomAgreementSentence f

/-- Auxiliary `(auxLang V)`-structure induced by an equivalence `e : V ≃ M` and a point
`x : ℕ → ℕ`. -/
@[instance_reducible]
private def auxStructure {M : Type w'} (e : V ≃ M) (x : ℕ → ℕ) : (auxLang V).Structure M where
  funMap {n} := match n with
    | 0 => fun v _ => e v
    | _ + 1 => fun fn _ => fn.elim
  RelMap {n} := match n with
    | 0 => fun p _ => x p.1 = p.2
    | _ + 1 => fun r _ => r.elim

variable [L.IsRelational]

/-- An `L`-structure `M` lies in the projective class of `analyticSentence f` along `LHom.sumInl`
if and only if `M` is isomorphic to `(f x).toStructure` for some `x : ℕ → ℕ`. -/
private theorem pcMem_analyticSentence_iff [∀ n, Countable (L.Relations n)] [Countable V]
    {f : (ℕ → ℕ) → RelationalConfiguration L V} (hf : Continuous f)
    (M : Type w') [L.Structure M] :
    (LHom.sumInl : L →ᴸ L.sum (auxLang V)).PCMem (analyticSentence f) M ↔
      ∃ x : ℕ → ℕ, Nonempty (@Language.Equiv L V M (f x).toStructure _) := by
  rw [LHom.pcMem_iff]
  constructor
  · rintro ⟨S, hS, hΘ⟩
    let : (L.sum (auxLang V)).Structure M := S
    let : (LHom.sumInl : L →ᴸ L.sum (auxLang V)).IsExpansionOn M := hS
    simp only [analyticSentence, SentenceInf.realize_inf] at hΘ
    obtain ⟨⟨⟨hinj, hsurj⟩, hgraph⟩, hatom⟩ := hΘ
    rw [realize_injSentence] at hinj
    rw [realize_surjSentence] at hsurj
    obtain ⟨x, hx⟩ := realize_funcGraphSentence.mp hgraph
    refine ⟨x, ⟨@Language.Equiv.mk L V M (f x).toStructure _
      (Equiv.ofBijective _ ⟨hinj, hsurj⟩)
      (fun {n} fn => isEmptyElim fn)
      fun {n} R t => ?_⟩⟩
    rw [toStructure_relMap]
    exact (realize_atomAgreementSentence_of_graph hf hx).mp hatom R t
  · rintro ⟨x, ⟨e⟩⟩
    let : L.Structure V := (f x).toStructure
    let : (auxLang V).Structure M := auxStructure e.toEquiv x
    refine ⟨_, inferInstance, ?_⟩
    simp only [analyticSentence, SentenceInf.realize_inf]
    have hcar : carrierInterp (L := L) (V := V) (M := M) = ⇑e :=
      funext fun v => (LHom.sumInr : auxLang V →ᴸ L.sum (auxLang V)).map_onFunction
        (auxConst v) Fin.elim0
    have hgr (n m : ℕ) : graphInterp (L := L) (V := V) (M := M) n m ↔ x n = m :=
      Iff.of_eq ((LHom.sumInr : auxLang V →ᴸ L.sum (auxLang V)).map_onRelation
        (auxGraphRel V n m) Fin.elim0)
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [realize_injSentence, hcar]
      exact e.injective
    · rw [realize_surjSentence, hcar]
      exact e.surjective
    · exact realize_funcGraphSentence.mpr ⟨x, hgr⟩
    · rw [realize_atomAgreementSentence_of_graph hf hgr, hcar]
      intro n R t
      rw [← toStructure_relMap]
      exact e.map_rel R t

/-- Every nonempty analytic set in a topological space is the range of a continuous map from
`ℕ → ℕ`. -/
private theorem exists_nat_nat_continuous_range_of_nonempty {α : Type*} [TopologicalSpace α]
    {A : Set α} (hA : AnalyticSet A) (hne : A.Nonempty) :
    ∃ f : (ℕ → ℕ) → α, Continuous f ∧ range f = A := by
  obtain ⟨γ, _, _, g, hg, rfl⟩ := analyticSet_iff_exists_polishSpace_range.mp hA
  obtain ⟨_, ⟨z, rfl⟩⟩ := hne
  have : Nonempty γ := ⟨z⟩
  obtain ⟨p, hp, hsurj⟩ := PolishSpace.exists_nat_nat_continuous_surjective γ
  exact ⟨g ∘ p, hg.comp hp, by rw [hsurj.range_comp]⟩

/-- Separation on a nonempty countable carrier via `FirstOrder.Language.pcSeparation`. -/
private theorem exists_sentence_separating_of_nonempty [∀ n, Countable (L.Relations n)]
    [Countable V] [Nonempty V] {A B : Set (RelationalConfiguration L V)}
    (hA : AnalyticSet A) (hB : AnalyticSet B)
    (hdisj : ∀ a ∈ A, ∀ b ∈ B, ¬ isoSetoid L V a b) :
    ∃ θ : L.Sentenceω, A ⊆ modelsOf θ ∧ Disjoint B (modelsOf θ) := by
  rcases A.eq_empty_or_nonempty with rfl | hAne
  · exact ⟨⊥, by simp, by simp⟩
  rcases B.eq_empty_or_nonempty with rfl | hBne
  · exact ⟨⊤, by simp, by simp⟩
  obtain ⟨fA, hfA, rfl⟩ := exists_nat_nat_continuous_range_of_nonempty hA hAne
  obtain ⟨fB, hfB, rfl⟩ := exists_nat_nat_continuous_range_of_nonempty hB hBne
  obtain ⟨θ, hθA, hθB⟩ := pcSeparation.{u, v, w, 0, w, 0, w, w}
    (analyticSentence fA) (analyticSentence fB) fun M _ _ _ hMA hMB => by
      obtain ⟨x, ⟨eA⟩⟩ := (pcMem_analyticSentence_iff hfA M).mp hMA
      obtain ⟨y, ⟨eB⟩⟩ := (pcMem_analyticSentence_iff hfB M).mp hMB
      exact hdisj (fA x) (mem_range_self x) (fB y) (mem_range_self y)
        (isoSetoid_apply.mpr ⟨@Language.Equiv.comp L V M (fA x).toStructure _ V (fB y).toStructure
          (@Language.Equiv.symm L V M (fB y).toStructure _ eB) eA⟩)
  refine ⟨θ, ?_, disjoint_left.mpr ?_⟩
  · rintro _ ⟨x, rfl⟩
    let : L.Structure V := (fA x).toStructure
    exact mem_modelsOf.mpr (hθA V ((pcMem_analyticSentence_iff hfA V).mpr
      ⟨x, ⟨Language.Equiv.refl L V⟩⟩))
  · rintro _ ⟨y, rfl⟩ hmem
    let : L.Structure V := (fB y).toStructure
    exact hθB V ((pcMem_analyticSentence_iff hfB V).mpr ⟨y, ⟨Language.Equiv.refl L V⟩⟩)
      (mem_modelsOf.mp hmem)

end AnalyticPresentation

/-! ### Empty-carrier Borel presentation -/

section EmptyCarrier

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w}

/-- The σ-algebra of subsets of `RelationalConfiguration L V` cut out by `L_{ω₁ω}` sentences. -/
@[instance_reducible]
private def modelsMeasurableSpace (L : Language.{u, v}) [L.IsRelational] (V : Type w) :
    MeasurableSpace (RelationalConfiguration L V) where
  MeasurableSet' s := ∃ θ : L.Sentenceω, modelsOf (V := V) θ = s
  measurableSet_empty := ⟨⊥, modelsOf_bot⟩
  measurableSet_compl _ := fun ⟨θ, hθ⟩ => ⟨θ.not, by rw [modelsOf_not, hθ]⟩
  measurableSet_iUnion f hf := by
    choose θ hθ using hf
    exact ⟨BoundedFormulaInf.iSup θ, by simp [hθ]⟩

/-- On an empty carrier, every subset of `Bool` pulled back along a single atom coordinate is
`modelsOf θ` for some `θ : L.Sentenceω`. -/
private theorem exists_modelsOf_preimage_eval_of_isEmpty [IsEmpty V] (a : Atom L V)
    (s : Set Bool) : ∃ θ : L.Sentenceω, modelsOf (V := V) θ = (fun c => c.eval a) ⁻¹' s := by
  induction a using Atom.induction_atom with
  | h R t =>
    rcases R with _
    cases ‹ℕ› with
    | succ k => exact isEmptyElim (t 0)
    | zero =>
      have ht : t = Fin.elim0 := Subsingleton.elim t Fin.elim0
      subst ht
      have htrue : modelsOf (V := V) (.rel R Fin.elim0 : L.Sentenceω) =
          {c | c.eval (atom R Fin.elim0) = true} := by
        ext c
        simp only [mem_modelsOf, SentenceInf.realize_def, FormulaInf.realize_def,
          BoundedFormulaInf.realize_rel, toStructure_relMap, mem_ofPred_eq]
        exact iff_of_eq (congrArg (fun x => c.eval (atom R x) = true) (Subsingleton.elim _ _))
      by_cases ht_mem : true ∈ s <;> by_cases hf_mem : false ∈ s
      · refine ⟨⊤, ?_⟩
        ext c; cases h : c.eval (atom R Fin.elim0) <;> simp [h, ht_mem, hf_mem]
      · refine ⟨.rel R Fin.elim0, htrue.trans ?_⟩
        ext c; cases h : c.eval (atom R Fin.elim0) <;> simp [h, ht_mem, hf_mem]
      · refine ⟨(.rel R Fin.elim0 : L.Sentenceω).not, ?_⟩
        rw [modelsOf_not, htrue]
        ext c; cases h : c.eval (atom R Fin.elim0) <;> simp [h, ht_mem, hf_mem]
      · refine ⟨⊥, ?_⟩
        ext c; cases h : c.eval (atom R Fin.elim0) <;> simp [h, ht_mem, hf_mem]

/-- On an empty carrier, every measurable set in the product σ-algebra on
`RelationalConfiguration L V` is `modelsOf θ` for some `θ : L.Sentenceω`. -/
private theorem exists_modelsOf_eq_of_isEmpty [IsEmpty V]
    {C : Set (RelationalConfiguration L V)} (hC : MeasurableSet C) :
    ∃ θ : L.Sentenceω, modelsOf (V := V) θ = C := by
  have hid : @Measurable _ _ (modelsMeasurableSpace L V) inferInstance
      (id : RelationalConfiguration L V → RelationalConfiguration L V) :=
    (@measurable_iff L V _ (modelsMeasurableSpace L V) id).mpr fun a s _ =>
      exists_modelsOf_preimage_eval_of_isEmpty a s
  exact hid hC

/-- Separation on an empty carrier via Lusin's separation theorem and coordinate generation. -/
private theorem exists_sentence_separating_of_isEmpty [∀ n, Countable (L.Relations n)] [IsEmpty V]
    {A B : Set (RelationalConfiguration L V)} (hA : AnalyticSet A) (hB : AnalyticSet B)
    (hdisj : ∀ a ∈ A, ∀ b ∈ B, ¬ isoSetoid L V a b) :
    ∃ θ : L.Sentenceω, A ⊆ modelsOf θ ∧ Disjoint B (modelsOf θ) := by
  have hab : Disjoint A B := disjoint_left.mpr fun c hcA hcB =>
    hdisj c hcA c hcB ((isoSetoid L V).refl c)
  obtain ⟨C, hAC, hBC, hC⟩ := hA.measurablySeparable hB hab
  obtain ⟨θ, rfl⟩ := exists_modelsOf_eq_of_isEmpty hC
  exact ⟨θ, hAC, hBC⟩

end EmptyCarrier

/-! ### Public López–Escobar theorems -/

/-- Every infinitary model class `modelsOf φ` is isomorphism invariant, with no countability
assumptions on `L`, `V`, or the branching index `ι`. -/
theorem isomorphismInvariant_modelsOf {L : Language.{u, v}} [L.IsRelational] {V : Type w}
    {ι : Type*} (φ : L.SentenceInf ι) :
    IsomorphismInvariant (modelsOf (V := V) φ) := by
  refine isomorphismInvariant_iff.mpr fun c d hcd hc => ?_
  obtain ⟨e⟩ := isoSetoid_apply.mp hcd
  exact (e.mem_modelsOf_iff φ).mp hc

section MainResults

variable {L : Language.{u, v}} [L.IsRelational] [∀ n, Countable (L.Relations n)]
variable {V : Type w} [Countable V]

/-- **López–Escobar separation (disjoint isomorphism-class images).** Let `V` be countable and let
`L` be a relational language with countably many relation symbols of each arity. If `A` and `B` are
analytic sets of configurations on `V` whose images in `Quotient (isoSetoid L V)` are disjoint
(no configuration in `A` is isomorphic to a configuration in `B`), then there is an `L_{ω₁ω}`
sentence `θ` such that `A ⊆ modelsOf θ` and `Disjoint B (modelsOf θ)`. -/
theorem exists_sentence_separating_of_disjoint_image
    {A B : Set (RelationalConfiguration L V)} (hA : AnalyticSet A) (hB : AnalyticSet B)
    (hdisj : Disjoint (Quotient.mk (isoSetoid L V) '' A) (Quotient.mk (isoSetoid L V) '' B)) :
    ∃ θ : L.Sentenceω, A ⊆ modelsOf θ ∧ Disjoint B (modelsOf θ) := by
  have hnoiso : ∀ a ∈ A, ∀ b ∈ B, ¬ isoSetoid L V a b := fun a ha b hb hab =>
    disjoint_left.mp hdisj (mem_image_of_mem _ ha) (Quotient.sound hab ▸ mem_image_of_mem _ hb)
  rcases isEmpty_or_nonempty V with hV | hV
  · exact exists_sentence_separating_of_isEmpty hA hB hnoiso
  · exact exists_sentence_separating_of_nonempty hA hB hnoiso

/-- **López–Escobar separation.** Let `V` be countable and let `L` be a relational language with
countably many relation symbols of each arity. If `A` and `B` are disjoint analytic sets of
configurations on `V` and `B` is isomorphism invariant, then there is an `L_{ω₁ω}` sentence `θ`
such that `A ⊆ modelsOf θ` and `Disjoint B (modelsOf θ)`. -/
theorem exists_sentence_separating
    {A B : Set (RelationalConfiguration L V)} (hA : AnalyticSet A) (hB : AnalyticSet B)
    (hBinv : IsomorphismInvariant B) (hdisj : Disjoint A B) :
    ∃ θ : L.Sentenceω, A ⊆ modelsOf θ ∧ Disjoint B (modelsOf θ) := by
  refine exists_sentence_separating_of_disjoint_image hA hB (disjoint_left.mpr ?_)
  rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
  exact disjoint_left.mp hdisj ha ((hBinv.mem_iff (Quotient.exact hba)).mp hb)

/-- **The López–Escobar theorem.** On a countable carrier `V` in a relational language `L` with
countably many relation symbols of each arity, a set `B` of configurations is the model class of
some `L_{ω₁ω}` sentence if and only if `B` is Borel and isomorphism invariant. -/
theorem exists_modelsOf_eq_iff {B : Set (RelationalConfiguration L V)} :
    (∃ θ : L.Sentenceω, modelsOf (V := V) θ = B) ↔
      MeasurableSet B ∧ IsomorphismInvariant B := by
  refine ⟨?_, fun ⟨hB, hBinv⟩ => ?_⟩
  · rintro ⟨θ, rfl⟩
    exact ⟨measurableSet_modelsOf θ, isomorphismInvariant_modelsOf θ⟩
  · obtain ⟨θ, hsub, hdisj⟩ :=
      exists_sentence_separating hB.analyticSet hB.compl.analyticSet hBinv.compl
        disjoint_compl_right
    exact ⟨θ, Subset.antisymm (disjoint_compl_left_iff_subset.mp hdisj) hsub⟩

/-- **Relative López–Escobar theorem.** Let `X` be a standard Borel space,
`f : X → RelationalConfiguration L V` a Borel map into configurations on a countable carrier `V` in
a countable relational vocabulary, and `U ⊆ X` a Borel set closed under isomorphism of images under
`f`. Then some `L_{ω₁ω}` sentence `θ` satisfies `f x ∈ modelsOf θ ↔ x ∈ U` for every `x : X`. -/
theorem exists_sentence_mem_modelsOf_iff {X : Type uX} [MeasurableSpace X] [StandardBorelSpace X]
    {f : X → RelationalConfiguration L V} (hf : Measurable f) {U : Set X} (hU : MeasurableSet U)
    (hinv : ∀ ⦃x y⦄, isoSetoid L V (f x) (f y) → x ∈ U → y ∈ U) :
    ∃ θ : L.Sentenceω, ∀ x, f x ∈ modelsOf θ ↔ x ∈ U := by
  have hA : AnalyticSet (f '' U) := hU.analyticSet_image hf
  have hB : AnalyticSet (f '' Uᶜ) := hU.compl.analyticSet_image hf
  have hdisj : Disjoint (Quotient.mk (isoSetoid L V) '' (f '' U))
      (Quotient.mk (isoSetoid L V) '' (f '' Uᶜ)) := by
    refine disjoint_left.mpr ?_
    rintro _ ⟨_, ⟨x, hxU, rfl⟩, rfl⟩ ⟨_, ⟨y, hyU, rfl⟩, hxy⟩
    exact hyU (hinv ((isoSetoid L V).symm (Quotient.exact hxy)) hxU)
  obtain ⟨θ, hsub, hdisjθ⟩ := exists_sentence_separating_of_disjoint_image hA hB hdisj
  refine ⟨θ, fun x => ⟨fun hxθ => by_contra fun hxU => ?_,
    fun hxU => hsub (mem_image_of_mem f hxU)⟩⟩
  exact disjoint_left.mp hdisjθ (mem_image_of_mem f hxU) hxθ

/-- **Relative López–Escobar theorem (preimage form).** Under the hypotheses of
`exists_sentence_mem_modelsOf_iff`, `U` is the preimage `f ⁻¹' modelsOf θ` of the model class of a
single `L_{ω₁ω}` sentence `θ`. -/
theorem exists_sentence_preimage_modelsOf_eq {X : Type uX} [MeasurableSpace X]
    [StandardBorelSpace X] {f : X → RelationalConfiguration L V} (hf : Measurable f) {U : Set X}
    (hU : MeasurableSet U) (hinv : ∀ ⦃x y⦄, isoSetoid L V (f x) (f y) → x ∈ U → y ∈ U) :
    ∃ θ : L.Sentenceω, f ⁻¹' modelsOf θ = U := by
  obtain ⟨θ, hθ⟩ := exists_sentence_mem_modelsOf_iff hf hU hinv
  exact ⟨θ, Set.ext hθ⟩

/-- **Cantor recovery.** If `f : (ℕ → Bool) → RelationalConfiguration L V` is Borel and sends
distinct sequences to non-isomorphic configurations on a countable carrier `V`, then there is a
sequence of sentences `θ : ℕ → L.Sentenceω` such that `f x ∈ modelsOf (θ n) ↔ x n = true` for all
`x : ℕ → Bool` and `n : ℕ`. -/
theorem exists_sentences_mem_modelsOf_iff {f : (ℕ → Bool) → RelationalConfiguration L V}
    (hf : Measurable f) (hnoniso : ∀ ⦃x y⦄, x ≠ y → ¬ isoSetoid L V (f x) (f y)) :
    ∃ θ : ℕ → L.Sentenceω, ∀ (x : ℕ → Bool) (n : ℕ), f x ∈ modelsOf (θ n) ↔ x n = true := by
  have hcoord (n : ℕ) : ∃ ψ : L.Sentenceω, ∀ x : ℕ → Bool, f x ∈ modelsOf ψ ↔ x n = true := by
    refine exists_sentence_mem_modelsOf_iff hf
      ((measurable_pi_apply n) (measurableSet_singleton true)) fun x y hxy hx => ?_
    obtain rfl : x = y := by_contra fun hne => hnoniso hne hxy
    exact hx
  choose θ hθ using hcoord
  exact ⟨θ, fun x n => hθ n x⟩

end MainResults

end TauCeti.RelationalConfiguration
