/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.ConstantAbstraction
public import TauCeti.ModelTheory.Interpolation.PCClass
public import TauCeti.ModelTheory.ModelExistence.ModelExistence

/-!
# Relational Craig interpolation and projective-class separation for `L_{ω₁ω}`

López-Escobar's interpolation theorem gives a Craig interpolant for every valid implication
`φ ⊨ ψ` between sentences of `L_{ω₁ω}`. This file establishes the **relational core** of Craig
interpolation for relational languages `L : Language.{u, v}` of arbitrary cardinality and in
arbitrary universes, together with its countable-theory form and the relational projective-class
separation theorems.

The engine is a paired-inseparability consistency property over the Henkin expansion `L[[ℕ]]`
which itself requires **no** relational hypothesis on `L`. Given two relation-symbol budgets
`R₁, R₂ : Set (Σ n, L.Relations n)`, a member is a union `Γ ∪ Δ` of two finite sets of `L[[ℕ]]`
sentences whose occurring relation symbols lie in the images of `R₁` and `R₂` and whose constant
supports are finite, such that no `L[[ℕ]]` sentence `θ` in the shared relation symbols `R₁ ∩ R₂`
with constant support inside the combined constant support of `Γ` and `Δ` is entailed by `Γ` and
refuted on `Δ`. Bounding the separator's constant support by that of the pair makes two parts of
the proof immediate: countable disjunctions and negated countable conjunctions keep the bound when
joining countably many separators, and at the root `({φ'}, {¬ψ'})` any separator has empty
constant support and therefore descends to `L`. Clauses that temporarily introduce constants
outside the pair's support (`all`, `not_all`, `eq_refl`, `eq_name`) eliminate those constants from
a putative separator through `BoundedFormulaInf.abstractConst` followed by universal or
existential quantification; the mixed equality cases of `eq_subst` use that equality is logical
(`relationsIn_equal = ∅`).

For a relational language `L` with countably many relation symbols,
`ConsistencyProperty.model_existence` applied to `({φ'}, {¬ψ'})` refutes the absence of an
interpolant. Passing to the countable symbol sublanguage
`symbSublang ∅ (φ.relationsIn ∪ ψ.relationsIn)` removes all countability assumptions on `L`.
Replacing a countable theory `T` by `T.conjunction` gives interpolation for `T ⊨ ψ`.

Combining relational Craig interpolation in `L.sum (L₁.sum L₂)` with downward Löwenheim–Skolem
(`Sentenceω.entails_iff_countable`) and `LHom.PCMem.realize_of_entails` yields relational
projective-class separation: if two `PC_{ω₁ω}` classes over relational `L`, `L₁`, `L₂` have no
common countable nonempty member in `Type w₀`, a single `L`-sentence separates them on nonempty
structures of every cardinality and universe.

## Main results

* `FirstOrder.Language.craig_interpolation_relational`: relational Craig interpolation for
  `L_{ω₁ω}` sentences over a relational language of arbitrary cardinality.
* `FirstOrder.Language.Theoryω.craig_interpolation_relational`: relational Craig interpolation for
  a countable theory `T` entailing a sentence `ψ`.
* `FirstOrder.Language.craig_pcSeparation_relational`: separating the reducts of models of two
  mutually inconsistent sentences in their shared symbol sublanguage.
* `FirstOrder.Language.pcSeparation_entails_relational` and
  `FirstOrder.Language.pcSeparation_relational`: relational `PC_{ω₁ω}` separation from countable
  disjointness in `Type w₀` to arbitrary nonempty structures in `Type w`.
* `FirstOrder.Language.pcComplement_iff_realize_relational`: a `PC_{ω₁ω}` class over relational
  languages whose countable complement is also `PC_{ω₁ω}` is the class of countable nonempty
  models of a single `L_{ω₁ω}` sentence.

## References

* E. G. K. López-Escobar, *An interpolation theorem for denumerably long formulas*, Fundamenta
  Mathematicae **57** (1965), 253–272.
* H. J. Keisler, *Model Theory for Infinitary Logic*, North-Holland, 1971, §4.
* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46, Cambridge
  University Press, 2016, §4.2.
* `cameronfreer/infinitary-logic` at commit `518a366cba97b1ae8c4dc64a297a396939bc3e0b`,
  `InfinitaryLogic/Methods/Interpolation/{Craig,ConstantElimination,PCSeparation}.lean`.
  Divergences from that source: the paired-inseparability consistency property is formulated over
  `L[[ℕ]]` for arbitrary `L : Language.{u, v}` without assuming `[L.IsRelational]`, tracking
  explicit constant-support bounds and eliminating extra constants via
  `BoundedFormulaInf.abstractConst`; arbitrary-cardinality relational languages are handled by
  symbol-sublanguage restriction rather than restricting to countable `Language.{0, 0}`; and
  projective-class separation transfers countable disjointness in any universe `w₀` to models of
  arbitrary cardinality and universe `w`.
-/

public section

universe u v u₁ v₁ u₂ v₂ w₀ w w'

namespace FirstOrder.Language

open BoundedFormulaInf

section Engine

variable {L : Language.{u, v}}

/-- The image of a set of relation symbols of `L` in the Henkin expansion `L[[ℕ]]`. -/
private abbrev liftRel (R : Set (Σ n, L.Relations n)) : Set (Σ n, L[[ℕ]].Relations n) :=
  (fun s => ⟨s.1, (L.lhomWithConstants ℕ).onRelation s.2⟩) '' R

private theorem liftRel_inter (R₁ R₂ : Set (Σ n, L.Relations n)) :
    liftRel R₁ ∩ liftRel R₂ = liftRel (R₁ ∩ R₂) := by
  refine Set.Subset.antisymm ?_ (Set.image_inter_subset _ R₁ R₂)
  rintro _ ⟨⟨⟨n₁, r₁⟩, hr₁, h₁⟩, ⟨⟨n₂, r₂⟩, hr₂, h₂⟩⟩
  have h12 := h₁.trans h₂.symm
  obtain ⟨rfl, hr⟩ := Sigma.mk.inj_iff.1 h12
  have : r₁ = r₂ := (L.lhomWithConstants_injective ℕ).onRelation (eq_of_heq hr)
  subst this
  exact ⟨⟨n₁, r₁⟩, ⟨hr₁, hr₂⟩, h₁⟩

/-- Combined constant support of a pair `(Γ, Δ)` of theories over `L[[ℕ]]`. -/
private def pairSupport (Γ Δ : L[[ℕ]].Theoryω) : Set ℕ :=
  (⋃ χ ∈ Γ, χ.constantSupport) ∪ (⋃ χ ∈ Δ, χ.constantSupport)

private theorem subset_pairSupport_left {Γ Δ : L[[ℕ]].Theoryω} {χ : L[[ℕ]].Sentenceω}
    (hχ : χ ∈ Γ) : χ.constantSupport ⊆ pairSupport Γ Δ :=
  (Set.subset_biUnion_of_mem hχ).trans Set.subset_union_left

private theorem subset_pairSupport_right {Γ Δ : L[[ℕ]].Theoryω} {χ : L[[ℕ]].Sentenceω}
    (hχ : χ ∈ Δ) : χ.constantSupport ⊆ pairSupport Γ Δ :=
  (Set.subset_biUnion_of_mem hχ).trans Set.subset_union_right

private theorem pairSupport_insert_left {Γ Δ : L[[ℕ]].Theoryω} (χ : L[[ℕ]].Sentenceω) :
    pairSupport (insert χ Γ) Δ = pairSupport Γ Δ ∪ χ.constantSupport := by
  ext c
  simp only [pairSupport, Set.mem_union, Set.mem_iUnion, Set.mem_insert_iff]
  aesop

private theorem pairSupport_insert_right {Γ Δ : L[[ℕ]].Theoryω} (χ : L[[ℕ]].Sentenceω) :
    pairSupport Γ (insert χ Δ) = pairSupport Γ Δ ∪ χ.constantSupport := by
  ext c
  simp only [pairSupport, Set.mem_union, Set.mem_iUnion, Set.mem_insert_iff]
  aesop

private theorem pairSupport_insert_left_of_subset {Γ Δ : L[[ℕ]].Theoryω} {χ : L[[ℕ]].Sentenceω}
    (h : χ.constantSupport ⊆ pairSupport Γ Δ) :
    pairSupport (insert χ Γ) Δ = pairSupport Γ Δ := by
  rw [pairSupport_insert_left, Set.union_eq_self_of_subset_right h]

private theorem pairSupport_insert_right_of_subset {Γ Δ : L[[ℕ]].Theoryω} {χ : L[[ℕ]].Sentenceω}
    (h : χ.constantSupport ⊆ pairSupport Γ Δ) :
    pairSupport Γ (insert χ Δ) = pairSupport Γ Δ := by
  rw [pairSupport_insert_right, Set.union_eq_self_of_subset_right h]

private theorem entails_realize {T : L[[ℕ]].Theoryω} {φ : L[[ℕ]].Sentenceω} (h : T.Entails φ)
    (M : Type (max u v)) [L[[ℕ]].Structure M] [Nonempty M] (hM : T.Model M) :
    SentenceInf.Realize φ M :=
  (Theoryω.entails_iff.1 h) M hM

/-- A separator for `(Γ, Δ)` with relation budget `R` and constant budget `K`. -/
private def HasSep (R : Set (Σ n, L[[ℕ]].Relations n)) (K : Set ℕ)
    (Γ Δ : L[[ℕ]].Theoryω) : Prop :=
  ∃ θ : L[[ℕ]].Sentenceω, θ.relationsIn ⊆ R ∧ θ.constantSupport ⊆ K ∧
    Γ.Entails θ ∧ Δ.Entails θ.not

/-- Reinterpreting a single Henkin constant `c` that does not occur in `Γ` preserves modelhood of
`Γ`. -/
private theorem model_update_of_notMem_support {M : Type w} [L.Structure M] (e : ℕ → M)
    {Γ : L[[ℕ]].Theoryω} {c : ℕ} (hc : ∀ χ ∈ Γ, c ∉ χ.constantSupport) (m : M)
    (hM : @Theoryω.Model _ Γ M (@withConstantsStructure L M _ ℕ (constantsOn.structure e))) :
    @Theoryω.Model _ Γ M
      (@withConstantsStructure L M _ ℕ (constantsOn.structure (Function.update e c m))) := by
  let S₀ := @withConstantsStructure L M _ ℕ (constantsOn.structure e)
  let S₁ := @withConstantsStructure L M _ ℕ (constantsOn.structure (Function.update e c m))
  refine (@Theoryω.model_iff _ Γ M S₁).2 fun χ hχ => ?_
  have heq : Set.EqOn (Function.update e c m) e χ.constantSupport := fun (d : ℕ) hd =>
    Function.update_of_ne (fun h : d = c => hc χ hχ (h ▸ hd)) m e
  have hcongr := χ.realize_congr_of_eqOn_constantSupport heq Empty.elim default
  have h₀ : @SentenceInf.Realize _ ℕ χ M S₀ := @Theoryω.Model.realize_of_mem _ _ M S₀ hM _ hχ
  rw [@SentenceInf.realize_def _ _ _ M S₀, @FormulaInf.realize_def _ _ _ M S₀] at h₀
  rw [@SentenceInf.realize_def _ _ _ M S₁, @FormulaInf.realize_def _ _ _ M S₁]
  exact hcongr.2 h₀

/-- Instantiating `(abstractConst c θ).all` at `L.con c` recovers `θ` in every model. -/
private theorem realize_of_realize_all_abstractConst {M : Type w} [iM : L[[ℕ]].Structure M]
    (c : ℕ) (θ : L[[ℕ]].Sentenceω)
    (h : SentenceInf.Realize (abstractConst c θ).all M) :
    SentenceInf.Realize θ M := by
  let S_L : L.Structure M := (L.lhomWithConstants ℕ).reduct M
  let e : ℕ → M := fun d => (L.con d : M)
  have hS : iM = @withConstantsStructure L M S_L ℕ (constantsOn.structure e) :=
    (withConstantsStructure_reduct_eq (L := L) (γ := ℕ) (M := M)).symm
  rw [SentenceInf.realize_def, FormulaInf.realize_def, hS,
    @realize_all _ _ _ _ M (@withConstantsStructure L M S_L ℕ (constantsOn.structure e))] at h
  have hm := (realize_abstractConst e c θ Empty.elim default (e c)).1 (h (e c))
  rw [Function.update_eq_self] at hm
  rw [SentenceInf.realize_def, FormulaInf.realize_def, hS]
  exact hm

/-- Universal constant elimination: if `c` does not occur in `Γ`, replacing `θ` by
`(abstractConst c θ).all` removes `c` from the constant support while preserving `(Γ, Δ)`
separation. -/
private theorem entails_all_abstractConst {Γ : L[[ℕ]].Theoryω} {c : ℕ}
    (hc : ∀ χ ∈ Γ, c ∉ χ.constantSupport) {θ : L[[ℕ]].Sentenceω} (hΓ : Γ.Entails θ) :
    Γ.Entails (abstractConst c θ).all := by
  refine Theoryω.entails_iff.2 fun M iM _ hM => ?_
  let S_L : L.Structure M := (L.lhomWithConstants ℕ).reduct M
  let e : ℕ → M := fun d => (L.con d : M)
  have hS : iM = @withConstantsStructure L M S_L ℕ (constantsOn.structure e) :=
    (withConstantsStructure_reduct_eq (L := L) (γ := ℕ) M).symm
  rw [SentenceInf.realize_def, FormulaInf.realize_def, hS,
    @realize_all _ _ _ _ M (@withConstantsStructure L M S_L ℕ (constantsOn.structure e))]
  intro m
  rw [realize_abstractConst e c θ Empty.elim default m]
  let S₁ := @withConstantsStructure L M S_L ℕ (constantsOn.structure (Function.update e c m))
  have hM' : @Theoryω.Model _ Γ M S₁ := model_update_of_notMem_support e hc m (hS ▸ hM)
  have hθ := @entails_realize L Γ θ hΓ M S₁ ‹_› hM'
  rwa [@SentenceInf.realize_def _ _ _ M S₁, @FormulaInf.realize_def _ _ _ M S₁] at hθ

/-- Existential constant elimination on the right: if `c` does not occur in `Δ`, replacing `θ` by
`(abstractConst c θ).ex` keeps `Δ.Entails θ'.not`. -/
private theorem entails_not_ex_abstractConst {Δ : L[[ℕ]].Theoryω} {c : ℕ}
    (hc : ∀ χ ∈ Δ, c ∉ χ.constantSupport) {θ : L[[ℕ]].Sentenceω} (hΔ : Δ.Entails θ.not) :
    Δ.Entails (abstractConst c θ).ex.not := by
  refine Theoryω.entails_iff.2 fun M iM _ hM => ?_
  rw [SentenceInf.realize_not]
  intro hex
  let S_L : L.Structure M := (L.lhomWithConstants ℕ).reduct M
  let e : ℕ → M := fun d => (L.con d : M)
  have hS : iM = @withConstantsStructure L M S_L ℕ (constantsOn.structure e) :=
    (withConstantsStructure_reduct_eq (L := L) (γ := ℕ) M).symm
  rw [SentenceInf.realize_def, FormulaInf.realize_def, hS,
    @realize_ex _ _ _ _ M (@withConstantsStructure L M S_L ℕ (constantsOn.structure e))] at hex
  obtain ⟨m, hm⟩ := hex
  rw [realize_abstractConst e c θ Empty.elim default m] at hm
  let S₁ := @withConstantsStructure L M S_L ℕ (constantsOn.structure (Function.update e c m))
  have hM' : @Theoryω.Model _ Δ M S₁ := model_update_of_notMem_support e hc m (hS ▸ hM)
  have hθ := @entails_realize L Δ θ.not hΔ M S₁ ‹_› hM'
  rw [@SentenceInf.realize_not _ _ M S₁, @SentenceInf.realize_def _ _ _ M S₁,
    @FormulaInf.realize_def _ _ _ M S₁] at hθ
  exact hθ hm

/-- Eliminating finitely many extra constants outside `K` from a separator when `Γ`'s constants
already lie in `K`. -/
private theorem hasSep_of_finite_extra {R : Set (Σ n, L[[ℕ]].Relations n)} {K E : Set ℕ}
    (hE : E.Finite) {Γ Δ : L[[ℕ]].Theoryω} (hΓK : ∀ χ ∈ Γ, χ.constantSupport ⊆ K)
    (hsep : HasSep R (K ∪ E) Γ Δ) : HasSep R K Γ Δ := by
  classical
  have hfin : (E \ K).Finite := hE.subset Set.sdiff_subset
  suffices ∀ (S : Finset ℕ), (∀ c ∈ S, c ∉ K) → HasSep R (K ∪ ↑S) Γ Δ → HasSep R K Γ Δ by
    refine this hfin.toFinset (fun c hc => ((hfin.mem_toFinset).1 hc).2) ?_
    obtain ⟨θ, hrel, hsupp, hΓ, hΔ⟩ := hsep
    refine ⟨θ, hrel, hsupp.trans fun c hc => ?_, hΓ, hΔ⟩
    by_cases hcK : c ∈ K
    · exact .inl hcK
    · exact .inr (hfin.mem_toFinset.2 ⟨hc.resolve_left hcK, hcK⟩)
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ h
    simpa using h
  | @insert c S hcS ih =>
    intro hSK ⟨θ, hrel, hsupp, hΓ, hΔ⟩
    have hcK : c ∉ K := hSK c (Finset.mem_insert_self c S)
    have hcΓ : ∀ χ ∈ Γ, c ∉ χ.constantSupport := fun χ hχ h => hcK (hΓK χ hχ h)
    refine ih (fun d hd => hSK d (Finset.mem_insert_of_mem hd))
      ⟨(abstractConst c θ).all, ?_, ?_, entails_all_abstractConst hcΓ hΓ, ?_⟩
    · simpa using hrel
    · rw [constantSupport_all, constantSupport_abstractConst]
      intro d hd
      rw [Set.mem_sdiff, Set.mem_singleton_iff] at hd
      rcases hsupp hd.1 with hdK | hdS
      · exact .inl hdK
      · rw [Finset.coe_insert, Set.mem_insert_iff] at hdS
        exact .inr (hdS.resolve_left hd.2)
    · refine Theoryω.entails_iff.2 fun M _ _ hM => ?_
      rw [SentenceInf.realize_not]
      intro hall
      exact (SentenceInf.realize_not.1 (entails_realize hΔ M hM))
        (realize_of_realize_all_abstractConst c θ hall)

private theorem pairSupport_comm (Γ Δ : L[[ℕ]].Theoryω) :
    pairSupport Γ Δ = pairSupport Δ Γ :=
  Set.union_comm _ _

/-- Negating a separator for `(Γ, Δ)` gives a separator for `(Δ, Γ)`. -/
private theorem HasSep.symm {R : Set (Σ n, L[[ℕ]].Relations n)} {K : Set ℕ}
    {Γ Δ : L[[ℕ]].Theoryω} : HasSep R K Γ Δ → HasSep R K Δ Γ := by
  rintro ⟨θ, hrel, hsupp, hΓ, hΔ⟩
  refine ⟨θ.not, by simpa using hrel, by simpa using hsupp, hΔ,
    Theoryω.entails_iff.2 fun M _ _ hM => ?_⟩
  rw [SentenceInf.realize_not, SentenceInf.realize_not, not_not]
  exact entails_realize hΓ M hM

/-- A valid `(R₁, R₂)`-inseparable finite pair `(Γ, Δ)`. -/
private structure InsepPair (R₁ R₂ : Set (Σ n, L.Relations n)) (Γ Δ : L[[ℕ]].Theoryω) : Prop where
  finite_left : Γ.Finite
  finite_right : Δ.Finite
  rel_left : ∀ χ ∈ Γ, χ.relationsIn ⊆ liftRel R₁
  rel_right : ∀ χ ∈ Δ, χ.relationsIn ⊆ liftRel R₂
  supp_left : ∀ χ ∈ Γ, χ.constantSupport.Finite
  supp_right : ∀ χ ∈ Δ, χ.constantSupport.Finite
  insep : ¬ HasSep (liftRel (R₁ ∩ R₂)) (pairSupport Γ Δ) Γ Δ

private theorem InsepPair.finite_pairSupport {R₁ R₂ : Set (Σ n, L.Relations n)}
    {Γ Δ : L[[ℕ]].Theoryω} (h : InsepPair R₁ R₂ Γ Δ) : (pairSupport Γ Δ).Finite :=
  (h.finite_left.biUnion h.supp_left).union (h.finite_right.biUnion h.supp_right)

/-- Swapping the two sides of an inseparable pair preserves `InsepPair`. -/
private theorem InsepPair.symm {R₁ R₂ : Set (Σ n, L.Relations n)} {Γ Δ : L[[ℕ]].Theoryω}
    (h : InsepPair R₁ R₂ Γ Δ) : InsepPair R₂ R₁ Δ Γ where
  finite_left := h.finite_right
  finite_right := h.finite_left
  rel_left := h.rel_right
  rel_right := h.rel_left
  supp_left := h.supp_right
  supp_right := h.supp_left
  insep hsep := h.insep (by
    rw [Set.inter_comm, pairSupport_comm]
    exact hsep.symm)

/-- Extending `Γ` by a sentence already entailed by `Γ` whose symbols and constants stay inside
the existing bounds preserves `InsepPair`. -/
private theorem InsepPair.insert_left_of_entails {R₁ R₂ : Set (Σ n, L.Relations n)}
    {Γ Δ : L[[ℕ]].Theoryω} (h : InsepPair R₁ R₂ Γ Δ) {χ : L[[ℕ]].Sentenceω}
    (hrel : χ.relationsIn ⊆ liftRel R₁) (hsupp : χ.constantSupport ⊆ pairSupport Γ Δ)
    (hent : Γ.Entails χ) : InsepPair R₁ R₂ (insert χ Γ) Δ where
  finite_left := h.finite_left.insert χ
  finite_right := h.finite_right
  rel_left _ hψ := hψ.elim (fun e => e ▸ hrel) (h.rel_left _)
  rel_right := h.rel_right
  supp_left _ hψ := hψ.elim (fun e => e ▸ h.finite_pairSupport.subset hsupp) (h.supp_left _)
  supp_right := h.supp_right
  insep := by
    rw [pairSupport_insert_left_of_subset hsupp]
    rintro ⟨θ, hθrel, hθsupp, hΓθ, hΔθ⟩
    exact h.insep ⟨θ, hθrel, hθsupp, hent.cut hΓθ, hΔθ⟩

/-- If inserting a bounded sentence `χ` on the left breaks `InsepPair`, `(insert χ Γ, Δ)` admits
a separator within the existing constant budget. -/
private theorem InsepPair.hasSep_insert_left_of_not_insepPair
    {R₁ R₂ : Set (Σ n, L.Relations n)} {Γ Δ : L[[ℕ]].Theoryω} (h : InsepPair R₁ R₂ Γ Δ)
    {χ : L[[ℕ]].Sentenceω} (hrel : χ.relationsIn ⊆ liftRel R₁)
    (hsupp : χ.constantSupport ⊆ pairSupport Γ Δ)
    (hnot : ¬ InsepPair R₁ R₂ (insert χ Γ) Δ) :
    HasSep (liftRel (R₁ ∩ R₂)) (pairSupport Γ Δ) (insert χ Γ) Δ := by
  by_contra hsep
  refine hnot ⟨h.finite_left.insert χ, h.finite_right,
    fun _ hψ => hψ.elim (fun e => e ▸ hrel) (h.rel_left _), h.rel_right,
    fun _ hψ => hψ.elim (fun e => e ▸ h.finite_pairSupport.subset hsupp) (h.supp_left _),
    h.supp_right, ?_⟩
  rwa [pairSupport_insert_left_of_subset hsupp]

private theorem InsepPair.not_bot_left {R₁ R₂ : Set (Σ n, L.Relations n)}
    {Γ Δ : L[[ℕ]].Theoryω} (hp : InsepPair R₁ R₂ Γ Δ) (hbot : ⊥ ∈ Γ) : False :=
  hp.insep ⟨⊥, by simp, by simp, Theoryω.entails_of_mem hbot,
    Theoryω.entails_iff.2 fun _ _ _ _ => by simp [SentenceInf.realize_not]⟩

private theorem InsepPair.not_contradiction_same {R₁ R₂ : Set (Σ n, L.Relations n)}
    {Γ Δ : L[[ℕ]].Theoryω} (hp : InsepPair R₁ R₂ Γ Δ) {φ : L[[ℕ]].Sentenceω}
    (hφ : φ ∈ Γ) (hnφ : φ.not ∈ Γ) : False :=
  hp.insep ⟨⊥, by simp, by simp,
    Theoryω.entails_iff.2 fun _ _ _ hM =>
      (SentenceInf.realize_not.1 (hM.realize_of_mem hnφ) (hM.realize_of_mem hφ)).elim,
    Theoryω.entails_iff.2 fun _ _ _ _ => by simp [SentenceInf.realize_not]⟩

private theorem InsepPair.not_contradiction_cross {R₁ R₂ : Set (Σ n, L.Relations n)}
    {Γ Δ : L[[ℕ]].Theoryω} (hp : InsepPair R₁ R₂ Γ Δ) {φ : L[[ℕ]].Sentenceω}
    (hφ : φ ∈ Γ) (hnφ : φ.not ∈ Δ) : False := by
  refine hp.insep ⟨φ, ?_, subset_pairSupport_left hφ,
    Theoryω.entails_of_mem hφ, Theoryω.entails_of_mem hnφ⟩
  rw [← liftRel_inter]
  exact Set.subset_inter (hp.rel_left φ hφ) (by simpa using hp.rel_right φ.not hnφ)

private theorem InsepPair.imp_left {R₁ R₂ : Set (Σ n, L.Relations n)}
    {Γ Δ : L[[ℕ]].Theoryω} (hp : InsepPair R₁ R₂ Γ Δ) {φ ψ : L[[ℕ]].Sentenceω}
    (himp : φ.imp ψ ∈ Γ) :
    InsepPair R₁ R₂ (insert φ.not Γ) Δ ∨ InsepPair R₁ R₂ (insert ψ Γ) Δ := by
  by_contra! hboth
  have hrel := hp.rel_left (φ.imp ψ) himp
  rw [relationsIn_imp, Set.union_subset_iff] at hrel
  have hsupp := subset_pairSupport_left (Δ := Δ) himp
  rw [constantSupport_imp, Set.union_subset_iff] at hsupp
  obtain ⟨θ₁, hr₁, hs₁, hΓ₁, hΔ₁⟩ := hp.hasSep_insert_left_of_not_insepPair
    (by simpa using hrel.1) (by simpa using hsupp.1) hboth.1
  obtain ⟨θ₂, hr₂, hs₂, hΓ₂, hΔ₂⟩ := hp.hasSep_insert_left_of_not_insepPair
    hrel.2 hsupp.2 hboth.2
  refine hp.insep ⟨θ₁ ⊔ θ₂, by simp [hr₁, hr₂], by simp [hs₁, hs₂], ?_, ?_⟩
  · refine Theoryω.entails_iff.2 fun M _ _ hM => ?_
    have hm := hM.realize_of_mem himp
    simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_imp] at hm
    rw [SentenceInf.realize_sup]
    by_cases hφM : SentenceInf.Realize φ M
    · rw [SentenceInf.realize_def, FormulaInf.realize_def] at hφM
      exact .inr (entails_realize hΓ₂ M (Theoryω.model_insert_iff.2
        ⟨by simpa [SentenceInf.realize_def, FormulaInf.realize_def] using hm hφM, hM⟩))
    · exact .inl (entails_realize hΓ₁ M (Theoryω.model_insert_iff.2
        ⟨SentenceInf.realize_not.2 hφM, hM⟩))
  · refine Theoryω.entails_iff.2 fun M _ _ hM => ?_
    rw [SentenceInf.realize_not, SentenceInf.realize_sup, not_or]
    exact ⟨SentenceInf.realize_not.1 (entails_realize hΔ₁ M hM),
      SentenceInf.realize_not.1 (entails_realize hΔ₂ M hM)⟩

private theorem InsepPair.not_imp_left {R₁ R₂ : Set (Σ n, L.Relations n)}
    {Γ Δ : L[[ℕ]].Theoryω} (hp : InsepPair R₁ R₂ Γ Δ) {φ ψ : L[[ℕ]].Sentenceω}
    (hnimp : (φ.imp ψ).not ∈ Γ) :
    InsepPair R₁ R₂ (insert φ Γ) Δ ∧ InsepPair R₁ R₂ (insert ψ.not Γ) Δ := by
  have hrel := hp.rel_left (φ.imp ψ).not hnimp
  rw [relationsIn_not, relationsIn_imp, Set.union_subset_iff] at hrel
  have hsupp := subset_pairSupport_left (Δ := Δ) hnimp
  rw [constantSupport_not, constantSupport_imp, Set.union_subset_iff] at hsupp
  refine ⟨hp.insert_left_of_entails hrel.1 hsupp.1 ?_,
    hp.insert_left_of_entails (by simpa using hrel.2) (by simpa using hsupp.2) ?_⟩
  · refine Theoryω.entails_iff.2 fun M _ _ hM => ?_
    have hm := hM.realize_of_mem hnimp
    simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_not, realize_imp,
      Classical.not_imp] at hm ⊢
    exact hm.1
  · refine Theoryω.entails_iff.2 fun M _ _ hM => ?_
    have hm := hM.realize_of_mem hnimp
    simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_not, realize_imp,
      Classical.not_imp] at hm ⊢
    exact hm.2

private theorem InsepPair.iInf_left {R₁ R₂ : Set (Σ n, L.Relations n)}
    {Γ Δ : L[[ℕ]].Theoryω} (hp : InsepPair R₁ R₂ Γ Δ) {φs : ℕ → L[[ℕ]].Sentenceω}
    (hiInf : BoundedFormulaInf.iInf φs ∈ Γ) (k : ℕ) :
    InsepPair R₁ R₂ (insert (φs k) Γ) Δ := by
  have hrel : (φs k).relationsIn ⊆ liftRel R₁ :=
    ((Set.subset_iUnion (fun i => (φs i).relationsIn) k).trans
      (relationsIn_iInf φs).symm.subset).trans (hp.rel_left _ hiInf)
  have hsupp : (φs k).constantSupport ⊆ pairSupport Γ Δ :=
    ((Set.subset_iUnion (fun i => (φs i).constantSupport) k).trans
      (constantSupport_iInf φs).symm.subset).trans (subset_pairSupport_left hiInf)
  exact hp.insert_left_of_entails hrel hsupp (Theoryω.entails_iff.2 fun M _ _ hM =>
    SentenceInf.realize_iInf.1 (hM.realize_of_mem hiInf) k)

private theorem InsepPair.not_iInf_left {R₁ R₂ : Set (Σ n, L.Relations n)}
    {Γ Δ : L[[ℕ]].Theoryω} (hp : InsepPair R₁ R₂ Γ Δ) {φs : ℕ → L[[ℕ]].Sentenceω}
    (hniInf : (BoundedFormulaInf.iInf φs).not ∈ Γ) :
    ∃ k, InsepPair R₁ R₂ (insert (φs k).not Γ) Δ := by
  by_contra! hnone
  have hall : ∀ k, HasSep (liftRel (R₁ ∩ R₂)) (pairSupport Γ Δ) (insert (φs k).not Γ) Δ := fun k =>
    hp.hasSep_insert_left_of_not_insepPair
      (by rw [relationsIn_not]
          exact (Set.subset_iUnion (fun i => (φs i).relationsIn) k).trans
            (by simpa using hp.rel_left _ hniInf))
      (by rw [constantSupport_not]
          exact ((Set.subset_iUnion (fun i => (φs i).constantSupport) k).trans
            (constantSupport_iInf φs).symm.subset).trans
            (by simpa using subset_pairSupport_left (Δ := Δ) hniInf))
      (hnone k)
  choose θs hrel hsupp hΓ hΔ using hall
  refine hp.insep ⟨BoundedFormulaInf.iSup θs,
    by rw [relationsIn_iSup]; exact Set.iUnion_subset hrel,
    by rw [constantSupport_iSup]; exact Set.iUnion_subset hsupp, ?_, ?_⟩
  · refine Theoryω.entails_iff.2 fun M _ _ hM => ?_
    have hm := SentenceInf.realize_not.1 (hM.realize_of_mem hniInf)
    obtain ⟨k, hk⟩ := not_forall.1 (hm ∘ SentenceInf.realize_iInf.2)
    rw [SentenceInf.realize_def, FormulaInf.realize_def, realize_iSup]
    refine ⟨k, ?_⟩
    have hθk := entails_realize (hΓ k) M
      (Theoryω.model_insert_iff.2 ⟨SentenceInf.realize_not.2 hk, hM⟩)
    rwa [SentenceInf.realize_def, FormulaInf.realize_def] at hθk
  · refine Theoryω.entails_iff.2 fun M _ _ hM => ?_
    rw [SentenceInf.realize_not, SentenceInf.realize_def, FormulaInf.realize_def, realize_iSup]
    rintro ⟨k, hk⟩
    have hθk := SentenceInf.realize_not.1 (entails_realize (hΔ k) M hM)
    rw [SentenceInf.realize_def, FormulaInf.realize_def] at hθk
    exact hθk hk

private theorem InsepPair.iSup_left {R₁ R₂ : Set (Σ n, L.Relations n)}
    {Γ Δ : L[[ℕ]].Theoryω} (hp : InsepPair R₁ R₂ Γ Δ) {φs : ℕ → L[[ℕ]].Sentenceω}
    (hiSup : BoundedFormulaInf.iSup φs ∈ Γ) :
    ∃ k, InsepPair R₁ R₂ (insert (φs k) Γ) Δ := by
  by_contra! hnone
  have hall : ∀ k, HasSep (liftRel (R₁ ∩ R₂)) (pairSupport Γ Δ) (insert (φs k) Γ) Δ := fun k =>
    hp.hasSep_insert_left_of_not_insepPair
      (((Set.subset_iUnion (fun i => (φs i).relationsIn) k).trans
        (relationsIn_iSup φs).symm.subset).trans (hp.rel_left _ hiSup))
      (((Set.subset_iUnion (fun i => (φs i).constantSupport) k).trans
        (constantSupport_iSup φs).symm.subset).trans (subset_pairSupport_left hiSup))
      (hnone k)
  choose θs hrel hsupp hΓ hΔ using hall
  refine hp.insep ⟨BoundedFormulaInf.iSup θs,
    by rw [relationsIn_iSup]; exact Set.iUnion_subset hrel,
    by rw [constantSupport_iSup]; exact Set.iUnion_subset hsupp, ?_, ?_⟩
  · refine Theoryω.entails_iff.2 fun M _ _ hM => ?_
    have hm := hM.realize_of_mem hiSup
    rw [SentenceInf.realize_def, FormulaInf.realize_def, realize_iSup] at hm ⊢
    obtain ⟨k, hk⟩ := hm
    refine ⟨k, ?_⟩
    have hθk := entails_realize (hΓ k) M (Theoryω.model_insert_iff.2
      ⟨by rwa [SentenceInf.realize_def, FormulaInf.realize_def], hM⟩)
    rwa [SentenceInf.realize_def, FormulaInf.realize_def] at hθk
  · refine Theoryω.entails_iff.2 fun M _ _ hM => ?_
    rw [SentenceInf.realize_not, SentenceInf.realize_def, FormulaInf.realize_def, realize_iSup]
    rintro ⟨k, hk⟩
    have hθk := SentenceInf.realize_not.1 (entails_realize (hΔ k) M hM)
    rw [SentenceInf.realize_def, FormulaInf.realize_def] at hθk
    exact hθk hk

private theorem InsepPair.not_iSup_left {R₁ R₂ : Set (Σ n, L.Relations n)}
    {Γ Δ : L[[ℕ]].Theoryω} (hp : InsepPair R₁ R₂ Γ Δ) {φs : ℕ → L[[ℕ]].Sentenceω}
    (hniSup : (BoundedFormulaInf.iSup φs).not ∈ Γ) (k : ℕ) :
    InsepPair R₁ R₂ (insert (φs k).not Γ) Δ := by
  have hrel : (φs k).not.relationsIn ⊆ liftRel R₁ := by
    rw [relationsIn_not]
    exact (Set.subset_iUnion (fun i => (φs i).relationsIn) k).trans
      (by simpa using hp.rel_left _ hniSup)
  have hsupp : (φs k).not.constantSupport ⊆ pairSupport Γ Δ := by
    rw [constantSupport_not]
    exact ((Set.subset_iUnion (fun i => (φs i).constantSupport) k).trans
      (constantSupport_iSup φs).symm.subset).trans
      (by simpa using subset_pairSupport_left (Δ := Δ) hniSup)
  refine hp.insert_left_of_entails hrel hsupp (Theoryω.entails_iff.2 fun M _ _ hM => ?_)
  have hm := SentenceInf.realize_not.1 (hM.realize_of_mem hniSup)
  refine SentenceInf.realize_not.2 fun hk => hm ?_
  rw [SentenceInf.realize_def, FormulaInf.realize_def, realize_iSup]
  rw [SentenceInf.realize_def, FormulaInf.realize_def] at hk
  exact ⟨k, hk⟩

private theorem InsepPair.all_left {R₁ R₂ : Set (Σ n, L.Relations n)}
    {Γ Δ : L[[ℕ]].Theoryω} (hp : InsepPair R₁ R₂ Γ Δ) {φ : L[[ℕ]].BoundedFormulaω Empty 1}
    (hall : φ.all ∈ Γ) (c : ℕ) :
    InsepPair R₁ R₂ (insert (φ.inst (L.con c).term) Γ) Δ := by
  have hrel : (φ.inst (L.con c).term).relationsIn ⊆ liftRel R₁ := by
    simpa [inst_def] using hp.rel_left φ.all hall
  have hsupp : (φ.inst (L.con c).term).constantSupport ⊆ pairSupport Γ Δ ∪ {c} :=
    (constantSupport_inst_subset φ (L.con c).term).trans
      (Set.union_subset_union (by simpa using subset_pairSupport_left (Δ := Δ) hall) (by simp))
  refine ⟨hp.finite_left.insert _, hp.finite_right,
    fun _ hχ => hχ.elim (fun e => e ▸ hrel) (hp.rel_left _), hp.rel_right,
    fun _ hχ => hχ.elim (fun e => e ▸ (hp.finite_pairSupport.union (Set.finite_singleton c)).subset
      hsupp) (hp.supp_left _), hp.supp_right, ?_⟩
  rintro ⟨θ, hθrel, hθsupp, hΓθ, hΔθ⟩
  have hent : Γ.Entails (φ.inst (L.con c).term) :=
    Theoryω.entails_iff.2 fun M _ _ hM => by
      have hm := hM.realize_of_mem hall
      simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_all] at hm
      simp only [SentenceInf.realize_def, realize_inst, Term.realize_constants]
      simpa only [Fin.snoc_zero] using hm (L.con c)
  refine hp.insep (hasSep_of_finite_extra (Set.finite_singleton c)
    (fun _ => subset_pairSupport_left) ⟨θ, hθrel, ?_, hent.cut hΓθ, hΔθ⟩)
  exact hθsupp.trans (by
    rw [pairSupport_insert_left]
    exact Set.union_subset Set.subset_union_left hsupp)

private theorem InsepPair.not_all_left {R₁ R₂ : Set (Σ n, L.Relations n)}
    {Γ Δ : L[[ℕ]].Theoryω} (hp : InsepPair R₁ R₂ Γ Δ) {φ : L[[ℕ]].BoundedFormulaω Empty 1}
    (hnall : φ.all.not ∈ Γ) :
    ∃ c, InsepPair R₁ R₂ (insert (φ.inst (L.con c).term).not Γ) Δ := by
  classical
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset hp.finite_pairSupport.toFinset
  have hcK : c ∉ pairSupport Γ Δ := fun h => hc (hp.finite_pairSupport.mem_toFinset.2 h)
  have hφK : φ.constantSupport ⊆ pairSupport Γ Δ := by
    simpa using subset_pairSupport_left (Δ := Δ) hnall
  have hcφ : c ∉ φ.constantSupport := fun h => hcK (hφK h)
  have hrel : (φ.inst (L.con c).term).not.relationsIn ⊆ liftRel R₁ := by
    simpa [inst_def] using hp.rel_left φ.all.not hnall
  have hsupp : (φ.inst (L.con c).term).not.constantSupport ⊆ pairSupport Γ Δ ∪ {c} := by
    rw [constantSupport_not]
    exact (constantSupport_inst_subset φ (L.con c).term).trans
      (Set.union_subset_union hφK (by simp))
  refine ⟨c, hp.finite_left.insert _, hp.finite_right,
    fun _ hχ => hχ.elim (fun e => e ▸ hrel) (hp.rel_left _), hp.rel_right,
    fun _ hχ => hχ.elim (fun e => e ▸ (hp.finite_pairSupport.union (Set.finite_singleton c)).subset
      hsupp) (hp.supp_left _), hp.supp_right, ?_⟩
  rintro ⟨θ, hθrel, hθsupp, hΓθ, hΔθ⟩
  refine hp.insep ⟨(abstractConst c θ).ex, by simpa using hθrel, ?_, ?_,
    entails_not_ex_abstractConst (fun χ hχ h => hcK (subset_pairSupport_right hχ h)) hΔθ⟩
  · rw [constantSupport_ex, constantSupport_abstractConst]
    intro d hd
    rw [Set.mem_sdiff, Set.mem_singleton_iff] at hd
    have hd' : d ∈ pairSupport Γ Δ ∪ {c} :=
      (Set.union_subset Set.subset_union_left hsupp)
        ((pairSupport_insert_left _).subset (hθsupp hd.1))
    exact hd'.resolve_right hd.2
  · refine Theoryω.entails_iff.2 fun M iM _ hM => ?_
    let S_L : L.Structure M := (L.lhomWithConstants ℕ).reduct M
    let e : ℕ → M := fun d => (L.con d : M)
    have hS : iM = @withConstantsStructure L M S_L ℕ (constantsOn.structure e) :=
      (withConstantsStructure_reduct_eq (L := L) (γ := ℕ) M).symm
    have hm := SentenceInf.realize_not.1 (hM.realize_of_mem hnall)
    rw [SentenceInf.realize_def, FormulaInf.realize_def, realize_all, not_forall] at hm
    obtain ⟨m, hm⟩ := hm
    rw [SentenceInf.realize_def, FormulaInf.realize_def, hS,
      @realize_ex _ _ _ _ M (@withConstantsStructure L M S_L ℕ (constantsOn.structure e))]
    refine ⟨m, ?_⟩
    rw [realize_abstractConst e c θ Empty.elim default m]
    let S₁ := @withConstantsStructure L M S_L ℕ (constantsOn.structure (Function.update e c m))
    have hMΓ : @Theoryω.Model _ Γ M S₁ :=
      model_update_of_notMem_support e (fun χ hχ h => hcK (subset_pairSupport_left hχ h)) m
        (hS ▸ hM)
    have hMinst : @SentenceInf.Realize _ ℕ (φ.inst (L.con c).term).not M S₁ := by
      rw [@SentenceInf.realize_not _ _ M S₁, @SentenceInf.realize_def _ _ _ M S₁,
        @realize_inst _ _ _ M S₁]
      have hcon :
          @Term.realize _ M S₁ (Empty ⊕ Fin 0) (Sum.elim Empty.elim default)
            (L.con c).term = m := by
        rw [@Term.realize_constants _ M S₁]
        exact Function.update_self c m e
      rw [hcon]
      intro hφm
      have hcongr := φ.realize_congr_of_eqOn_constantSupport (e := Function.update e c m)
        (e' := e) (fun (d : ℕ) hd => Function.update_of_ne (fun h : d = c => hcφ (h ▸ hd)) m e)
        Empty.elim (fun _ => m)
      have hφm₀ := hcongr.1 hφm
      rw [← hS] at hφm₀
      exact hm (by simpa only [Fin.snoc_zero] using hφm₀)
    have hθ := @entails_realize L _ θ hΓθ M S₁ ‹_›
      (@Theoryω.model_insert_iff _ _ M S₁ _ |>.2 ⟨hMinst, hMΓ⟩)
    rwa [@SentenceInf.realize_def _ _ _ M S₁, @FormulaInf.realize_def _ _ _ M S₁] at hθ

private theorem InsepPair.eq_refl_left {R₁ R₂ : Set (Σ n, L.Relations n)}
    {Γ Δ : L[[ℕ]].Theoryω} (hp : InsepPair R₁ R₂ Γ Δ) (t : L[[ℕ]].Term (Empty ⊕ Fin 0)) :
    InsepPair R₁ R₂ (insert (equal t t) Γ) Δ := by
  refine ⟨hp.finite_left.insert _, hp.finite_right,
    fun _ hχ => hχ.elim (fun e => e ▸ by simp) (hp.rel_left _), hp.rel_right,
    fun _ hχ => hχ.elim (fun e => e ▸ by simpa using t.finite_constantSupport) (hp.supp_left _),
    hp.supp_right, ?_⟩
  rintro ⟨θ, hθrel, hθsupp, hΓθ, hΔθ⟩
  have hent : Γ.Entails (equal t t) := Theoryω.entails_iff.2 fun _ _ _ _ => by
    simp [SentenceInf.realize_def, FormulaInf.realize_def]
  refine hp.insep (hasSep_of_finite_extra t.finite_constantSupport
    (fun _ => subset_pairSupport_left) ⟨θ, hθrel, ?_, hent.cut hΓθ, hΔθ⟩)
  simpa [pairSupport_insert_left] using hθsupp

private theorem InsepPair.eq_subst_same {R₁ R₂ : Set (Σ n, L.Relations n)}
    {Γ Δ : L[[ℕ]].Theoryω} (hp : InsepPair R₁ R₂ Γ Δ)
    {t t' : L[[ℕ]].Term (Empty ⊕ Fin 0)} {φ : L[[ℕ]].BoundedFormulaω Empty 1}
    (heq : equal t t' ∈ Γ) (hinst : φ.inst t ∈ Γ) :
    InsepPair R₁ R₂ (insert (φ.inst t') Γ) Δ := by
  have htK := subset_pairSupport_left (Δ := Δ) heq
  rw [constantSupport_equal, Set.union_subset_iff] at htK
  have hφK : φ.constantSupport ⊆ pairSupport Γ Δ :=
    (constantSupport_subset_inst φ t).trans (subset_pairSupport_left hinst)
  have hsupp : (φ.inst t').constantSupport ⊆ pairSupport Γ Δ :=
    (constantSupport_inst_subset φ t').trans (Set.union_subset hφK htK.2)
  have hrel : (φ.inst t').relationsIn ⊆ liftRel R₁ := by
    simpa [inst_def] using hp.rel_left (φ.inst t) hinst
  refine hp.insert_left_of_entails hrel hsupp (Theoryω.entails_iff.2 fun M _ _ hM => ?_)
  have ht := hM.realize_of_mem heq
  have hφ := hM.realize_of_mem hinst
  simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_equal] at ht
  simp only [SentenceInf.realize_def, realize_inst] at hφ ⊢
  rwa [← ht]

/-- Mixed equality substitution (`equal t t' ∈ Γ` and `φ.inst t ∈ Δ`): equality is logical
(`relationsIn_equal = ∅`), so `θ ↦ equal t t' ⊓ θ` transfers any separator of
`(Γ, insert (φ.inst t') Δ)` back to `(Γ, Δ)`. -/
private theorem InsepPair.eq_subst_cross {R₁ R₂ : Set (Σ n, L.Relations n)}
    {Γ Δ : L[[ℕ]].Theoryω} (hp : InsepPair R₁ R₂ Γ Δ)
    {t t' : L[[ℕ]].Term (Empty ⊕ Fin 0)} {φ : L[[ℕ]].BoundedFormulaω Empty 1}
    (heq : equal t t' ∈ Γ) (hinst : φ.inst t ∈ Δ) :
    InsepPair R₁ R₂ Γ (insert (φ.inst t') Δ) := by
  have htK := subset_pairSupport_left (Δ := Δ) heq
  rw [constantSupport_equal, Set.union_subset_iff] at htK
  have hφK : φ.constantSupport ⊆ pairSupport Γ Δ :=
    (constantSupport_subset_inst φ t).trans (subset_pairSupport_right hinst)
  have hsupp : (φ.inst t').constantSupport ⊆ pairSupport Γ Δ :=
    (constantSupport_inst_subset φ t').trans (Set.union_subset hφK htK.2)
  have hrel : (φ.inst t').relationsIn ⊆ liftRel R₂ := by
    simpa [inst_def] using hp.rel_right (φ.inst t) hinst
  refine ⟨hp.finite_left, hp.finite_right.insert _, hp.rel_left,
    fun _ hχ => hχ.elim (fun e => e ▸ hrel) (hp.rel_right _), hp.supp_left,
    fun _ hχ => hχ.elim (fun e => e ▸ hp.finite_pairSupport.subset hsupp) (hp.supp_right _), ?_⟩
  rw [pairSupport_insert_right_of_subset hsupp]
  rintro ⟨θ, hθrel, hθsupp, hΓθ, hΔθ⟩
  refine hp.insep ⟨equal t t' ⊓ θ, by simpa using hθrel, by simp [htK.1, htK.2, hθsupp],
    Theoryω.entails_iff.2 fun M _ _ hM =>
      SentenceInf.realize_inf.2 ⟨hM.realize_of_mem heq, entails_realize hΓθ M hM⟩, ?_⟩
  refine Theoryω.entails_iff.2 fun M _ _ hM => ?_
  rw [SentenceInf.realize_not, SentenceInf.realize_inf, not_and]
  intro htM
  have hφM := hM.realize_of_mem hinst
  simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_equal] at htM
  simp only [SentenceInf.realize_def, realize_inst] at hφM
  have hφt' : SentenceInf.Realize (φ.inst t') M := by
    simp only [SentenceInf.realize_def, realize_inst]
    rwa [← htM]
  exact SentenceInf.realize_not.1
    (entails_realize hΔθ M (Theoryω.model_insert_iff.2 ⟨hφt', hM⟩))

private theorem InsepPair.eq_name_left {R₁ R₂ : Set (Σ n, L.Relations n)}
    {Γ Δ : L[[ℕ]].Theoryω} (hp : InsepPair R₁ R₂ Γ Δ) (t : L[[ℕ]].Term (Empty ⊕ Fin 0)) :
    ∃ c, InsepPair R₁ R₂ (insert (equal (L.con c).term t) Γ) Δ := by
  classical
  have hKt : (pairSupport Γ Δ ∪ t.constantSupport).Finite :=
    hp.finite_pairSupport.union t.finite_constantSupport
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset hKt.toFinset
  have hcKt : c ∉ pairSupport Γ Δ ∪ t.constantSupport := fun h => hc (hKt.mem_toFinset.2 h)
  have hcK : c ∉ pairSupport Γ Δ := fun h => hcKt (.inl h)
  have hct : c ∉ t.constantSupport := fun h => hcKt (.inr h)
  refine ⟨c, hp.finite_left.insert _, hp.finite_right,
    fun _ hχ => hχ.elim (fun e => e ▸ by simp) (hp.rel_left _), hp.rel_right,
    fun _ hχ => hχ.elim (fun e => e ▸ by
      rw [constantSupport_equal, Term.constantSupport_con]
      exact (Set.finite_singleton c).union t.finite_constantSupport) (hp.supp_left _),
    hp.supp_right, ?_⟩
  rintro ⟨θ, hθrel, hθsupp, hΓθ, hΔθ⟩
  -- Eliminate the fresh constant `c` existentially, then eliminate `t`'s extra constants.
  have hsep₁ : HasSep (liftRel (R₁ ∩ R₂)) (pairSupport Γ Δ ∪ t.constantSupport) Γ Δ := by
    refine ⟨(abstractConst c θ).ex, by simpa using hθrel, ?_, ?_,
      entails_not_ex_abstractConst (fun χ hχ h => hcK (subset_pairSupport_right hχ h)) hΔθ⟩
    · rw [constantSupport_ex, constantSupport_abstractConst]
      intro d hd
      rw [Set.mem_sdiff, Set.mem_singleton_iff] at hd
      have hd' := hθsupp hd.1
      rw [pairSupport_insert_left, constantSupport_equal, Term.constantSupport_con] at hd'
      rcases hd' with hdK | (hdc | hdt)
      · exact .inl hdK
      · exact (hd.2 hdc).elim
      · exact .inr hdt
    · refine Theoryω.entails_iff.2 fun M iM _ hM => ?_
      let S_L : L.Structure M := (L.lhomWithConstants ℕ).reduct M
      let e : ℕ → M := fun d => (L.con d : M)
      have hS : iM = @withConstantsStructure L M S_L ℕ (constantsOn.structure e) :=
        (withConstantsStructure_reduct_eq (L := L) (γ := ℕ) M).symm
      let m : M := t.realize (Sum.elim Empty.elim default)
      rw [SentenceInf.realize_def, FormulaInf.realize_def, hS,
        @realize_ex _ _ _ _ M (@withConstantsStructure L M S_L ℕ (constantsOn.structure e))]
      refine ⟨m, ?_⟩
      rw [realize_abstractConst e c θ Empty.elim default m]
      let S₁ := @withConstantsStructure L M S_L ℕ (constantsOn.structure (Function.update e c m))
      have hMΓ : @Theoryω.Model _ Γ M S₁ :=
        model_update_of_notMem_support e (fun χ hχ h => hcK (subset_pairSupport_left hχ h)) m
          (hS ▸ hM)
      have hMeq : @SentenceInf.Realize _ ℕ (equal (L.con c).term t) M S₁ := by
        rw [@SentenceInf.realize_def _ _ _ M S₁, @FormulaInf.realize_def _ _ _ M S₁,
          @realize_equal _ _ _ _ M S₁]
        have hcon :
            @Term.realize _ M S₁ (Empty ⊕ Fin 0) (Sum.elim Empty.elim default)
              (L.con c).term = m := by
          rw [@Term.realize_constants _ M S₁]
          exact Function.update_self c m e
        have htcongr := t.realize_congr_of_eqOn_constantSupport (e := Function.update e c m)
          (e' := e) (fun (d : ℕ) hd => Function.update_of_ne (fun h : d = c => hct (h ▸ hd)) m e)
          (Sum.elim Empty.elim default)
        have ht₀ : @Term.realize _ M
            (@withConstantsStructure L M S_L ℕ (constantsOn.structure e)) _
            (Sum.elim Empty.elim default) t = m := by
          rw [← hS]
        rw [hcon, htcongr, ht₀]
      have hθ := @entails_realize L _ θ hΓθ M S₁ ‹_›
        (@Theoryω.model_insert_iff _ _ M S₁ _ |>.2 ⟨hMeq, hMΓ⟩)
      rwa [@SentenceInf.realize_def _ _ _ M S₁, @FormulaInf.realize_def _ _ _ M S₁] at hθ
  exact hp.insep (hasSep_of_finite_extra t.finite_constantSupport
    (fun _ => subset_pairSupport_left) hsep₁)

/-- **The paired-inseparability consistency property** over `L[[ℕ]]`, requiring no relational or
countability assumption on `L`. Right-hand and symmetric mixed cases reduce to the left-hand
clauses via `InsepPair.symm`. -/
private def insepConsistencyProperty (R₁ R₂ : Set (Σ n, L.Relations n)) :
    ConsistencyProperty L where
  sets := {s | ∃ Γ Δ, s = Γ ∪ Δ ∧ InsepPair R₁ R₂ Γ Δ}
  no_falsum := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ (hbot | hbot)
    · exact hp.not_bot_left hbot
    · exact hp.symm.not_bot_left hbot
  no_contradiction := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φ (hφ | hφ) (hnφ | hnφ)
    · exact hp.not_contradiction_same hφ hnφ
    · exact hp.not_contradiction_cross hφ hnφ
    · exact hp.symm.not_contradiction_cross hφ hnφ
    · exact hp.symm.not_contradiction_same hφ hnφ
  imp := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φ ψ (himp | himp)
    · exact (hp.imp_left himp).imp
        (fun h => ⟨insert φ.not Γ, Δ, Set.insert_union.symm, h⟩)
        (fun h => ⟨insert ψ Γ, Δ, Set.insert_union.symm, h⟩)
    · exact (hp.symm.imp_left himp).imp
        (fun h => ⟨Γ, insert φ.not Δ, Set.union_insert.symm, h.symm⟩)
        (fun h => ⟨Γ, insert ψ Δ, Set.union_insert.symm, h.symm⟩)
  not_imp := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φ ψ (hnimp | hnimp)
    · obtain ⟨h₁, h₂⟩ := hp.not_imp_left hnimp
      exact ⟨⟨insert φ Γ, Δ, Set.insert_union.symm, h₁⟩,
        ⟨insert ψ.not Γ, Δ, Set.insert_union.symm, h₂⟩⟩
    · obtain ⟨h₁, h₂⟩ := hp.symm.not_imp_left hnimp
      exact ⟨⟨Γ, insert φ Δ, Set.union_insert.symm, h₁.symm⟩,
        ⟨Γ, insert ψ.not Δ, Set.union_insert.symm, h₂.symm⟩⟩
  iInf := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φs (hiInf | hiInf) k
    · exact ⟨insert (φs k) Γ, Δ, Set.insert_union.symm, hp.iInf_left hiInf k⟩
    · exact ⟨Γ, insert (φs k) Δ, Set.union_insert.symm, (hp.symm.iInf_left hiInf k).symm⟩
  not_iInf := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φs (hniInf | hniInf)
    · obtain ⟨k, hk⟩ := hp.not_iInf_left hniInf
      exact ⟨k, insert (φs k).not Γ, Δ, Set.insert_union.symm, hk⟩
    · obtain ⟨k, hk⟩ := hp.symm.not_iInf_left hniInf
      exact ⟨k, Γ, insert (φs k).not Δ, Set.union_insert.symm, hk.symm⟩
  iSup := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φs (hiSup | hiSup)
    · obtain ⟨k, hk⟩ := hp.iSup_left hiSup
      exact ⟨k, insert (φs k) Γ, Δ, Set.insert_union.symm, hk⟩
    · obtain ⟨k, hk⟩ := hp.symm.iSup_left hiSup
      exact ⟨k, Γ, insert (φs k) Δ, Set.union_insert.symm, hk.symm⟩
  not_iSup := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φs (hniSup | hniSup) k
    · exact ⟨insert (φs k).not Γ, Δ, Set.insert_union.symm, hp.not_iSup_left hniSup k⟩
    · exact ⟨Γ, insert (φs k).not Δ, Set.union_insert.symm, (hp.symm.not_iSup_left hniSup k).symm⟩
  all := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φ (hall | hall) c
    · exact ⟨insert (φ.inst (L.con c).term) Γ, Δ, Set.insert_union.symm, hp.all_left hall c⟩
    · exact ⟨Γ, insert (φ.inst (L.con c).term) Δ, Set.union_insert.symm,
        (hp.symm.all_left hall c).symm⟩
  not_all := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φ (hnall | hnall)
    · obtain ⟨c, hc⟩ := hp.not_all_left hnall
      exact ⟨c, insert (φ.inst (L.con c).term).not Γ, Δ, Set.insert_union.symm, hc⟩
    · obtain ⟨c, hc⟩ := hp.symm.not_all_left hnall
      exact ⟨c, Γ, insert (φ.inst (L.con c).term).not Δ, Set.union_insert.symm, hc.symm⟩
  eq_refl := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ t
    exact ⟨insert (equal t t) Γ, Δ, Set.insert_union.symm, hp.eq_refl_left t⟩
  eq_subst := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ t t' φ _ (heq | heq) (hinst | hinst)
    · exact ⟨insert (φ.inst t') Γ, Δ, Set.insert_union.symm, hp.eq_subst_same heq hinst⟩
    · exact ⟨Γ, insert (φ.inst t') Δ, Set.union_insert.symm, hp.eq_subst_cross heq hinst⟩
    · exact ⟨insert (φ.inst t') Γ, Δ, Set.insert_union.symm,
        (hp.symm.eq_subst_cross heq hinst).symm⟩
    · exact ⟨Γ, insert (φ.inst t') Δ, Set.union_insert.symm,
        (hp.symm.eq_subst_same heq hinst).symm⟩
  eq_name := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ t
    obtain ⟨c, hc⟩ := hp.eq_name_left t
    exact ⟨c, insert (equal (L.con c).term t) Γ, Δ, Set.insert_union.symm, hc⟩

private theorem mem_insepConsistencyProperty {R₁ R₂ : Set (Σ n, L.Relations n)}
    {Γ Δ : L[[ℕ]].Theoryω} (h : InsepPair R₁ R₂ Γ Δ) :
    Γ ∪ Δ ∈ (insepConsistencyProperty R₁ R₂).sets := by
  rw [insepConsistencyProperty]
  exact ⟨Γ, Δ, rfl, h⟩

end Engine

/-! ### Relational Craig interpolation -/

section Craig

variable {L : Language.{u, v}}

/-- Countable relational core: if `L` is relational with countably many relation symbols, any
valid entailment `φ ⊨ ψ` has a Craig interpolant. -/
private theorem craig_interpolation_relational_of_countable [L.IsRelational]
    [Countable (Σ n, L.Relations n)] (φ ψ : L.Sentenceω) (h : Sentenceω.Entails φ ψ) :
    ∃ θ : L.Sentenceω, θ.relationsIn ⊆ φ.relationsIn ∩ ψ.relationsIn ∧
      Sentenceω.Entails φ θ ∧ Sentenceω.Entails θ ψ := by
  have : IsEmpty (Σ n, L.Functions n) := ⟨fun s => isEmptyElim s.2⟩
  by_contra hno
  let g := L.lhomWithConstants ℕ
  let φ' : L[[ℕ]].Sentenceω := g.onBoundedFormulaInf φ
  let ψ' : L[[ℕ]].Sentenceω := g.onBoundedFormulaInf ψ
  have hs : ({φ'} : L[[ℕ]].Theoryω) ∪ {ψ'.not} ∈
      (insepConsistencyProperty φ.relationsIn ψ.relationsIn).sets := by
    refine mem_insepConsistencyProperty ⟨Set.finite_singleton _, Set.finite_singleton _,
      ?_, ?_, ?_, ?_, ?_⟩
    · intro χ hχ
      rw [Set.mem_singleton_iff.1 hχ, LHom.relationsIn_onBoundedFormulaInf]
    · intro χ hχ
      rw [Set.mem_singleton_iff.1 hχ, relationsIn_not, LHom.relationsIn_onBoundedFormulaInf]
    · intro χ hχ
      rw [Set.mem_singleton_iff.1 hχ]
      simp [φ', g]
    · intro χ hχ
      rw [Set.mem_singleton_iff.1 hχ]
      simp [ψ', g]
    · rintro ⟨θ', hθ'rel, hθ'supp, hφ'θ', hψ'θ'⟩
      have hK : pairSupport ({φ'} : L[[ℕ]].Theoryω) {ψ'.not} = ∅ := by
        simp [pairSupport, φ', ψ', g]
      rw [hK, Set.subset_empty_iff] at hθ'supp
      obtain ⟨θ, rfl⟩ := constantSupport_eq_empty_iff.1 hθ'supp
      refine hno ⟨θ, ?_, ?_, ?_⟩
      · intro ⟨n, r⟩ hr
        have hr' : (⟨n, g.onRelation r⟩ : Σ k, L[[ℕ]].Relations k) ∈
            liftRel (φ.relationsIn ∩ ψ.relationsIn) := by
          refine hθ'rel ?_
          rw [LHom.relationsIn_onBoundedFormulaInf]
          exact ⟨⟨n, r⟩, hr, rfl⟩
        obtain ⟨⟨m, r₀⟩, hr₀, hm⟩ := hr'
        obtain ⟨rfl, heq⟩ := Sigma.mk.inj_iff.1 hm
        have : r₀ = r := (L.lhomWithConstants_injective ℕ).onRelation (eq_of_heq heq)
        exact this ▸ hr₀
      · exact (Sentenceω.entails_onBoundedFormulaInf_iff (L.lhomWithConstants_injective ℕ)).1
          (Sentenceω.entails_def.2 hφ'θ')
      · have hnot : Sentenceω.Entails ψ.not θ.not := by
          refine (Sentenceω.entails_onBoundedFormulaInf_iff (L.lhomWithConstants_injective ℕ)).1 ?_
          simpa [ψ', g] using Sentenceω.entails_def.2 hψ'θ'
        rw [Sentenceω.entails_iff] at hnot ⊢
        intro M _ _ hθM
        by_contra hψM
        exact (SentenceInf.realize_not.1 (hnot M (SentenceInf.realize_not.2 hψM))) hθM
  have hsc : (({φ'} : L[[ℕ]].Theoryω) ∪ {ψ'.not}).Countable :=
    (Set.countable_singleton _).union (Set.countable_singleton _)
  obtain ⟨M, _, _, _, hM, _⟩ :=
    (insepConsistencyProperty φ.relationsIn ψ.relationsIn).model_existence.{u, v, max u v} hs hsc
  let : L.Structure M := g.reduct M
  have hφM : SentenceInf.Realize φ M :=
    (LHom.realize_sentenceInf_onBoundedFormulaInf g φ).1
      (hM.realize_of_mem (.inl (Set.mem_singleton _)))
  have hnψM : ¬ SentenceInf.Realize ψ M := fun hψM =>
    SentenceInf.realize_not.1 (hM.realize_of_mem (.inr (Set.mem_singleton _)))
      ((LHom.realize_sentenceInf_onBoundedFormulaInf g ψ).2 hψM)
  exact hnψM (h.realize M hφM)

/-- **Relational Craig interpolation for `L_{ω₁ω}`.** In any relational language `L` (of any
cardinality and in any universes), if an `L_{ω₁ω}` sentence `φ` entails `ψ`, there is an
`L_{ω₁ω}` sentence `θ` whose occurring relation symbols lie in `φ.relationsIn ∩ ψ.relationsIn`
such that `φ` entails `θ` and `θ` entails `ψ`. -/
theorem craig_interpolation_relational [L.IsRelational] (φ ψ : L.Sentenceω)
    (h : Sentenceω.Entails φ ψ) :
    ∃ θ : L.Sentenceω, θ.relationsIn ⊆ φ.relationsIn ∩ ψ.relationsIn ∧
      Sentenceω.Entails φ θ ∧ Sentenceω.Entails θ ψ := by
  let F : Set (Σ n, L.Functions n) := ∅
  let R : Set (Σ n, L.Relations n) := φ.relationsIn ∪ ψ.relationsIn
  have : Countable R := (φ.relationsIn_countable.union ψ.relationsIn_countable).to_subtype
  have hFφ : φ.functionsIn ⊆ F := fun s _ => isEmptyElim s.2
  have hFψ : ψ.functionsIn ⊆ F := fun s _ => isEmptyElim s.2
  let ι := symbSublangIncl F R
  let φ₀ := φ.restrictSymbols (R := R) hFφ Set.subset_union_left
  let ψ₀ := ψ.restrictSymbols (R := R) hFψ Set.subset_union_right
  have h₀ : Sentenceω.Entails φ₀ ψ₀ := by
    refine (Sentenceω.entails_onBoundedFormulaInf_iff (symbSublangIncl_injective F R)).1 ?_
    simpa [ι, φ₀, ψ₀] using h
  obtain ⟨θ₀, hrel₀, hφθ₀, hθψ₀⟩ := craig_interpolation_relational_of_countable φ₀ ψ₀ h₀
  refine ⟨ι.onBoundedFormulaInf θ₀, ?_, ?_, ?_⟩
  · rw [LHom.relationsIn_onBoundedFormulaInf]
    refine ((Set.image_mono hrel₀).trans (Set.image_inter_subset _ _ _)).trans ?_
    rw [← LHom.relationsIn_onBoundedFormulaInf, ← LHom.relationsIn_onBoundedFormulaInf,
      onBoundedFormulaInf_restrictSymbols, onBoundedFormulaInf_restrictSymbols]
  · simpa [ι, φ₀] using hφθ₀.onBoundedFormulaInf ι
  · simpa [ι, ψ₀] using hθψ₀.onBoundedFormulaInf ι

/-- **Countable-theory relational Craig interpolation.** Over a relational language `L`, if a
countable `L_{ω₁ω}` theory `T` entails `ψ`, there is an interpolant `θ` whose occurring relation
symbols appear both in some sentence of `T` and in `ψ`, with `T ⊨ θ` and `θ ⊨ ψ`. -/
theorem Theoryω.craig_interpolation_relational [L.IsRelational] {T : L.Theoryω}
    (hT : T.Countable) (ψ : L.Sentenceω) (h : T.Entails ψ) :
    ∃ θ : L.Sentenceω, θ.relationsIn ⊆ (⋃ φ ∈ T, φ.relationsIn) ∩ ψ.relationsIn ∧
      T.Entails θ ∧ Sentenceω.Entails θ ψ := by
  obtain ⟨θ, hrel, hTθ, hθψ⟩ := Language.craig_interpolation_relational (T.conjunction hT) ψ
    ((Theoryω.entails_iff_conjunction_entails hT).1 h)
  refine ⟨θ, hrel.trans (Set.inter_subset_inter_left _ ?_),
    (Theoryω.entails_iff_conjunction_entails hT).2 hTθ, hθψ⟩
  rw [Theoryω.conjunction_def, relationsIn_iInfAlong]
  intro s hs
  obtain ⟨⟨φ, hφ⟩, hs⟩ := Set.mem_iUnion.1 hs
  exact Set.mem_biUnion hφ hs

/-- **Relational projective-class separation from mutual inconsistency.** Over a relational
language `L`, if `ψ₁ ⊨ ¬ψ₂`, some sentence `θ` of the shared symbol sublanguage
`symbSublang (ψ₁.functionsIn ∩ ψ₂.functionsIn) (ψ₁.relationsIn ∩ ψ₂.relationsIn)` holds in the
reduct of every nonempty model of `ψ₁` and fails in the reduct of every nonempty model of `ψ₂`,
across arbitrary universes `w` and `w'`. -/
theorem craig_pcSeparation_relational [L.IsRelational] (ψ₁ ψ₂ : L.Sentenceω)
    (h : Sentenceω.Entails ψ₁ ψ₂.not) :
    ∃ θ : (symbSublang (ψ₁.functionsIn ∩ ψ₂.functionsIn)
        (ψ₁.relationsIn ∩ ψ₂.relationsIn)).Sentenceω,
      (∀ (M : Type w) [L.Structure M] [Nonempty M], SentenceInf.Realize ψ₁ M →
        @SentenceInf.Realize _ ℕ θ M
          ((symbSublangIncl (ψ₁.functionsIn ∩ ψ₂.functionsIn)
            (ψ₁.relationsIn ∩ ψ₂.relationsIn)).reduct M)) ∧
      (∀ (M : Type w') [L.Structure M] [Nonempty M], SentenceInf.Realize ψ₂ M →
        ¬ @SentenceInf.Realize _ ℕ θ M
          ((symbSublangIncl (ψ₁.functionsIn ∩ ψ₂.functionsIn)
            (ψ₁.relationsIn ∩ ψ₂.relationsIn)).reduct M)) := by
  obtain ⟨θ₀, hrel, h₁, h₂⟩ := craig_interpolation_relational ψ₁ ψ₂.not h
  rw [relationsIn_not] at hrel
  have hF : θ₀.functionsIn ⊆ ψ₁.functionsIn ∩ ψ₂.functionsIn := fun s _ => isEmptyElim s.2
  let ι := symbSublangIncl (ψ₁.functionsIn ∩ ψ₂.functionsIn) (ψ₁.relationsIn ∩ ψ₂.relationsIn)
  refine ⟨θ₀.restrictSymbols hF hrel, ?_, ?_⟩
  · intro M _ _ hM₁
    let := ι.reduct M
    simpa only [SentenceInf.realize_def, FormulaInf.realize_def, realize_restrictSymbols] using
      h₁.realize M hM₁
  · intro M _ _ hM₂ hθM
    let := ι.reduct M
    have hθ₀M : SentenceInf.Realize θ₀ M := by
      simpa only [SentenceInf.realize_def, FormulaInf.realize_def, realize_restrictSymbols] using
        hθM
    exact SentenceInf.realize_not.1 (h₂.realize M hθ₀M) hM₂

end Craig

/-! ### Relational projective-class separation -/

section PCSeparation

variable {L : Language.{u, v}} {L₁ : Language.{u₁, v₁}} {L₂ : Language.{u₂, v₂}}

/-- **Entailment form of relational `PC_{ω₁ω}` separation.** For relational languages `L`, `L₁`,
`L₂`, if no countable nonempty `L`-structure in `Type w₀` lies in both
`LHom.sumInl.PCMem Θ₁` and `LHom.sumInl.PCMem Θ₂`, there is a single sentence `θ : L.Sentenceω`
whose image in `L.sum L₁` is entailed by `Θ₁` and whose negated image in `L.sum L₂` is entailed
by `Θ₂`. -/
theorem pcSeparation_entails_relational [L.IsRelational] [L₁.IsRelational] [L₂.IsRelational]
    (Θ₁ : (L.sum L₁).Sentenceω) (Θ₂ : (L.sum L₂).Sentenceω)
    (h : ∀ (M : Type w₀) [L.Structure M] [Nonempty M] [Countable M],
      LHom.sumInl.PCMem Θ₁ M → ¬ LHom.sumInl.PCMem Θ₂ M) :
    ∃ θ : L.Sentenceω,
      Sentenceω.Entails Θ₁ (LHom.sumInl.onBoundedFormulaInf θ) ∧
      Sentenceω.Entails Θ₂ (LHom.sumInl.onBoundedFormulaInf θ).not := by
  let g₁ : L.sum L₁ →ᴸ L.sum (L₁.sum L₂) := (LHom.id L).sumMap LHom.sumInl
  let g₂ : L.sum L₂ →ᴸ L.sum (L₁.sum L₂) := (LHom.id L).sumMap LHom.sumInr
  have hg₁ : g₁.Injective :=
    ⟨fun h => (Function.injective_id.sumMap LHom.sumInl_injective.onFunction) h,
     fun h => (Function.injective_id.sumMap LHom.sumInl_injective.onRelation) h⟩
  have hg₂ : g₂.Injective :=
    ⟨fun h => (Function.injective_id.sumMap LHom.sumInr_injective.onFunction) h,
     fun h => (Function.injective_id.sumMap LHom.sumInr_injective.onRelation) h⟩
  let Θ₁' := g₁.onBoundedFormulaInf Θ₁
  let Θ₂' := g₂.onBoundedFormulaInf Θ₂
  have hent : Sentenceω.Entails Θ₁' Θ₂'.not := by
    rw [Sentenceω.entails_iff_countable.{_, _, w₀}]
    intro M _ _ _ hM₁
    rw [SentenceInf.realize_not]
    intro hM₂
    let : L.Structure M := (LHom.sumInl : L →ᴸ L.sum (L₁.sum L₂)).reduct M
    have hboth : (LHom.sumInl : L →ᴸ L.sum (L₁.sum L₂)).PCMem (Θ₁' ⊓ Θ₂') M :=
      LHom.pcMem_of_isExpansionOn (SentenceInf.realize_inf.2 ⟨hM₁, hM₂⟩)
    obtain ⟨h₁, h₂⟩ := LHom.pcMem_sumInl_inf_iff.1 hboth
    exact h M h₁ h₂
  obtain ⟨θ', hrel, h₁, h₂⟩ := craig_interpolation_relational Θ₁' Θ₂'.not hent
  have hF : θ'.functionsIn ⊆ Set.range fun s : Σ n, L.Functions n =>
      (⟨s.1, (LHom.sumInl : L →ᴸ L.sum (L₁.sum L₂)).onFunction s.2⟩ :
        Σ k, (L.sum (L₁.sum L₂)).Functions k) :=
    fun s _ => isEmptyElim s.2
  have hR : θ'.relationsIn ⊆ Set.range fun s : Σ n, L.Relations n =>
      (⟨s.1, (LHom.sumInl : L →ᴸ L.sum (L₁.sum L₂)).onRelation s.2⟩ :
        Σ k, (L.sum (L₁.sum L₂)).Relations k) := by
    intro ⟨k, R⟩ hR'
    obtain ⟨hR₁, hR₂⟩ := hrel hR'
    rw [relationsIn_not] at hR₂
    rw [LHom.relationsIn_onBoundedFormulaInf] at hR₁ hR₂
    obtain ⟨⟨k₁, r₁ | r₁⟩, -, hr₁⟩ := hR₁
    · dsimp only at hr₁
      obtain ⟨rfl, heq⟩ := Sigma.mk.inj_iff.1 hr₁
      cases heq
      exact ⟨⟨k₁, r₁⟩, rfl⟩
    · obtain ⟨⟨k₂, r₂ | r₂⟩, -, hr₂⟩ := hR₂
      · dsimp only at hr₁ hr₂
        obtain ⟨rfl, heq₁⟩ := Sigma.mk.inj_iff.1 hr₁
        obtain ⟨rfl, heq₂⟩ := Sigma.mk.inj_iff.1 hr₂
        exact (Sum.inr_ne_inl ((eq_of_heq heq₁).trans (eq_of_heq heq₂).symm)).elim
      · dsimp only at hr₁ hr₂
        obtain ⟨rfl, heq₁⟩ := Sigma.mk.inj_iff.1 hr₁
        obtain ⟨rfl, heq₂⟩ := Sigma.mk.inj_iff.1 hr₂
        have := Sum.inr.inj ((eq_of_heq heq₁).trans (eq_of_heq heq₂).symm)
        exact (Sum.inl_ne_inr this).elim
  obtain ⟨θ, hθ⟩ := LHom.exists_eq_onBoundedFormulaInf_of_subset_range
    (LHom.sumInl : L →ᴸ L.sum (L₁.sum L₂)) θ' hF hR
  have hcomp₁ : g₁.onBoundedFormulaInf (LHom.sumInl.onBoundedFormulaInf θ) = θ' := by
    rw [← LHom.comp_onBoundedFormulaInf, LHom.sumMap_comp_inl, LHom.comp_id, hθ]
  have hcomp₂ : g₂.onBoundedFormulaInf (LHom.sumInl.onBoundedFormulaInf θ) = θ' := by
    rw [← LHom.comp_onBoundedFormulaInf, LHom.sumMap_comp_inl, LHom.comp_id, hθ]
  refine ⟨θ, ?_, ?_⟩
  · refine (Sentenceω.entails_onBoundedFormulaInf_iff hg₁).1 ?_
    rwa [hcomp₁]
  · refine (Sentenceω.entails_onBoundedFormulaInf_iff hg₂).1 ?_
    rw [LHom.onBoundedFormulaInf_not, hcomp₂]
    rw [Sentenceω.entails_iff] at h₂ ⊢
    intro M _ _ hM₂
    rw [SentenceInf.realize_not]
    intro hθ'M
    exact SentenceInf.realize_not.1 (h₂ M hθ'M) hM₂

/-- **Relational projective-class separation.** For relational languages `L`, `L₁`, `L₂` (of any
cardinality and in any universes), if two `PC_{ω₁ω}` classes `LHom.sumInl.PCMem Θ₁` and
`LHom.sumInl.PCMem Θ₂` have no common countable nonempty member in `Type w₀`, there is a single
`L_{ω₁ω}` sentence `θ` over `L` that holds in every nonempty member of the first class and fails in
every nonempty member of the second class, in any universe `w`. -/
theorem pcSeparation_relational [L.IsRelational] [L₁.IsRelational] [L₂.IsRelational]
    (Θ₁ : (L.sum L₁).Sentenceω) (Θ₂ : (L.sum L₂).Sentenceω)
    (h : ∀ (M : Type w₀) [L.Structure M] [Nonempty M] [Countable M],
      LHom.sumInl.PCMem Θ₁ M → ¬ LHom.sumInl.PCMem Θ₂ M) :
    ∃ θ : L.Sentenceω,
      (∀ (M : Type w) [L.Structure M] [Nonempty M], LHom.sumInl.PCMem Θ₁ M →
        SentenceInf.Realize θ M) ∧
      (∀ (M : Type w) [L.Structure M] [Nonempty M], LHom.sumInl.PCMem Θ₂ M →
        ¬ SentenceInf.Realize θ M) := by
  obtain ⟨θ, h₁, h₂⟩ := pcSeparation_entails_relational Θ₁ Θ₂ h
  refine ⟨θ, fun M _ _ hM => hM.realize_of_entails h₁, fun M _ _ hM => ?_⟩
  simpa only [SentenceInf.realize_not] using
    hM.realize_of_entails (φ := θ.not) (by simpa using h₂)

/-- **Suslin–Kleene characterization for relational `PC_{ω₁ω}` classes.** If every countable
nonempty `L`-structure in `Type w₀` lies in exactly one of `LHom.sumInl.PCMem Θ₁` and
`LHom.sumInl.PCMem Θ₂` (with `L`, `L₁`, `L₂` relational), then `LHom.sumInl.PCMem Θ₁` on countable
nonempty structures is the model class of a single `L_{ω₁ω}` sentence `θ`. -/
theorem pcComplement_iff_realize_relational [L.IsRelational] [L₁.IsRelational] [L₂.IsRelational]
    (Θ₁ : (L.sum L₁).Sentenceω) (Θ₂ : (L.sum L₂).Sentenceω)
    (h : ∀ (M : Type w₀) [L.Structure M] [Nonempty M] [Countable M],
      LHom.sumInl.PCMem Θ₁ M ↔ ¬ LHom.sumInl.PCMem Θ₂ M) :
    ∃ θ : L.Sentenceω, ∀ (M : Type w₀) [L.Structure M] [Nonempty M] [Countable M],
      LHom.sumInl.PCMem Θ₁ M ↔ SentenceInf.Realize θ M := by
  obtain ⟨θ, h₁, h₂⟩ := pcSeparation_relational.{u, v, u₁, v₁, u₂, v₂, w₀, w₀} Θ₁ Θ₂
    fun M _ _ _ hM₁ => (h M).1 hM₁
  refine ⟨θ, fun M _ _ _ => ⟨h₁ M, fun hθM => ?_⟩⟩
  by_contra hM₁
  exact h₂ M ((h M).not_left.1 hM₁) hθM

end PCSeparation

end FirstOrder.Language
