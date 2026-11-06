/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Interpolation.ConstantElimination
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
    liftRel R₁ ∩ liftRel R₂ = liftRel (R₁ ∩ R₂) :=
  (Set.image_inter
    (Function.injective_id.sigma_map fun _ => (L.lhomWithConstants_injective ℕ).onRelation)).symm

/-- Combined constant support of a pair `(Γ, Δ)` of theories over `L[[ℕ]]`. -/
private def pairSupport (Γ Δ : L[[ℕ]].Theoryω) : Set ℕ :=
  (⋃ χ ∈ Γ, χ.constantSupport) ∪ (⋃ χ ∈ Δ, χ.constantSupport)

private theorem pairSupport_comm (Γ Δ : L[[ℕ]].Theoryω) : pairSupport Γ Δ = pairSupport Δ Γ :=
  Set.union_comm _ _

private theorem subset_pairSupport_left {Γ Δ : L[[ℕ]].Theoryω} {χ : L[[ℕ]].Sentenceω}
    (hχ : χ ∈ Γ) : χ.constantSupport ⊆ pairSupport Γ Δ :=
  (Set.subset_biUnion_of_mem hχ).trans Set.subset_union_left

private theorem subset_pairSupport_right {Γ Δ : L[[ℕ]].Theoryω} {χ : L[[ℕ]].Sentenceω}
    (hχ : χ ∈ Δ) : χ.constantSupport ⊆ pairSupport Γ Δ :=
  (Set.subset_biUnion_of_mem hχ).trans Set.subset_union_right

private theorem pairSupport_insert_left {Γ Δ : L[[ℕ]].Theoryω} (χ : L[[ℕ]].Sentenceω) :
    pairSupport (insert χ Γ) Δ = pairSupport Γ Δ ∪ χ.constantSupport := by
  ext; simp only [pairSupport, Set.mem_union, Set.mem_iUnion, Set.mem_insert_iff]; aesop

private theorem pairSupport_insert_left_of_subset {Γ Δ : L[[ℕ]].Theoryω} {χ : L[[ℕ]].Sentenceω}
    (h : χ.constantSupport ⊆ pairSupport Γ Δ) :
    pairSupport (insert χ Γ) Δ = pairSupport Γ Δ := by
  rw [pairSupport_insert_left, Set.union_eq_self_of_subset_right h]

private theorem pairSupport_insert_right_of_subset {Γ Δ : L[[ℕ]].Theoryω} {χ : L[[ℕ]].Sentenceω}
    (h : χ.constantSupport ⊆ pairSupport Γ Δ) :
    pairSupport Γ (insert χ Δ) = pairSupport Γ Δ := by
  rw [pairSupport_comm, pairSupport_insert_left_of_subset (pairSupport_comm Γ Δ ▸ h),
    pairSupport_comm]

private theorem entails_realize {T : L[[ℕ]].Theoryω} {φ : L[[ℕ]].Sentenceω} (h : T.Entails φ)
    (M : Type (max u v)) [L[[ℕ]].Structure M] [Nonempty M] (hM : T.Model M) :
    SentenceInf.Realize φ M :=
  (Theoryω.entails_iff.1 h) M hM

/-- A separator for `(Γ, Δ)` with relation budget `R` and constant budget `K`. -/
private def HasSep (R : Set (Σ n, L[[ℕ]].Relations n)) (K : Set ℕ)
    (Γ Δ : L[[ℕ]].Theoryω) : Prop :=
  ∃ θ : L[[ℕ]].Sentenceω, θ.relationsIn ⊆ R ∧ θ.constantSupport ⊆ K ∧
    Γ.Entails θ ∧ Δ.Entails θ.not

/-- Negating a separator for `(Γ, Δ)` gives a separator for `(Δ, Γ)`. -/
private theorem HasSep.symm {R : Set (Σ n, L[[ℕ]].Relations n)} {K : Set ℕ}
    {Γ Δ : L[[ℕ]].Theoryω} : HasSep R K Γ Δ → HasSep R K Δ Γ := fun ⟨θ, hr, hs, hΓ, hΔ⟩ =>
  ⟨θ.not, by simpa using hr, by simpa using hs, hΔ, Theoryω.entails_iff.2 fun M _ _ hM => by
    simpa [SentenceInf.realize_not] using entails_realize hΓ M hM⟩

/-- Reinterpret the single Henkin constant `c` as `m`, keeping `L` and all other constants fixed. -/
@[instance_reducible]
private def updateStructure {M : Type w} [L[[ℕ]].Structure M] (c : ℕ) (m : M) :
    L[[ℕ]].Structure M :=
  @withConstantsStructure L M ((L.lhomWithConstants ℕ).reduct M) ℕ
    (constantsOn.structure (Function.update (fun d => (L.con d : M)) c m))

private theorem realize_con_updateStructure_self {M : Type w} [L[[ℕ]].Structure M] {α : Type*}
    (c : ℕ) (m : M) (v : α → M) :
    @Term.realize _ M (updateStructure c m) _ v (L.con c).term = m := by
  rw [@Term.realize_constants _ M (updateStructure c m)]
  -- Under `withConstantsStructure` and `constantsOn.structure`, `L.con c` (`Sum.inr c`) evaluates
  -- the constant map at `c`.
  exact Function.update_self c m fun d => (L.con d : M)

private theorem term_realize_updateStructure_of_notMem {M : Type w} [iM : L[[ℕ]].Structure M]
    {α : Type*} {t : L[[ℕ]].Term α} {c : ℕ} (hc : c ∉ t.constantSupport) (m : M) (v : α → M) :
    @Term.realize _ M (updateStructure c m) _ v t = t.realize v := by
  let S_L : L.Structure M := (L.lhomWithConstants ℕ).reduct M
  have hS : iM = @withConstantsStructure L M S_L ℕ (constantsOn.structure fun d => (L.con d : M)) :=
    (withConstantsStructure_reduct_eq (L := L) (γ := ℕ) M).symm
  unfold updateStructure
  rw [t.realize_congr_of_eqOn_constantSupport
    (fun d hd => Function.update_of_ne (by rintro rfl; exact hc hd : d ≠ c) m
      (fun d => (L.con d : M))) v, ← hS]

private theorem realize_updateStructure_of_notMem {M : Type w} [iM : L[[ℕ]].Structure M]
    {α : Type*} {n : ℕ} {φ : L[[ℕ]].BoundedFormulaω α n} {c : ℕ}
    (hc : c ∉ φ.constantSupport) (m : M) (v : α → M) (xs : Fin n → M) :
    @Realize _ _ _ M (updateStructure c m) n φ v xs ↔ φ.Realize v xs := by
  let S_L : L.Structure M := (L.lhomWithConstants ℕ).reduct M
  have hS : iM = @withConstantsStructure L M S_L ℕ (constantsOn.structure fun d => (L.con d : M)) :=
    (withConstantsStructure_reduct_eq (L := L) (γ := ℕ) M).symm
  unfold updateStructure
  rw [φ.realize_congr_of_eqOn_constantSupport
    (fun d hd => Function.update_of_ne (by rintro rfl; exact hc hd : d ≠ c) m
      (fun d => (L.con d : M))) v xs, ← hS]

private theorem model_updateStructure {M : Type w} [iM : L[[ℕ]].Structure M]
    {Γ : L[[ℕ]].Theoryω} {c : ℕ} (hc : ∀ χ ∈ Γ, c ∉ χ.constantSupport) (m : M)
    (hM : Γ.Model M) : @Theoryω.Model _ Γ M (updateStructure c m) := by
  let S : L.Structure M := (L.lhomWithConstants ℕ).reduct M
  have hS : iM = @withConstantsStructure L M S ℕ
      (constantsOn.structure fun d => (L.con d : M)) :=
    (withConstantsStructure_reduct_eq (L := L) (γ := ℕ) M).symm
  unfold updateStructure
  exact (Theoryω.model_constantsOn_update_iff _ m hc).2 (hS ▸ hM)

private theorem realize_abstractConst_snoc {M : Type w} [iM : L[[ℕ]].Structure M]
    (c : ℕ) (θ : L[[ℕ]].Sentenceω) (m : M) :
    (abstractConst c θ).Realize Empty.elim (Fin.snoc default m) ↔
      @SentenceInf.Realize _ ℕ θ M (updateStructure c m) := by
  let S_L : L.Structure M := (L.lhomWithConstants ℕ).reduct M
  have hS : iM = @withConstantsStructure L M S_L ℕ (constantsOn.structure fun d => (L.con d : M)) :=
    (withConstantsStructure_reduct_eq (L := L) (γ := ℕ) M).symm
  unfold updateStructure
  simp only [SentenceInf.realize_def, FormulaInf.realize_def]
  rw [hS]
  exact realize_abstractConst _ c θ Empty.elim default m

/-- Eliminating finitely many extra constants outside `K` from a separator when `Γ`'s constants
already lie in `K`. -/
private theorem hasSep_of_finite_extra {R : Set (Σ n, L[[ℕ]].Relations n)} {K E : Set ℕ}
    (hE : E.Finite) {Γ Δ : L[[ℕ]].Theoryω} (hΓK : ∀ χ ∈ Γ, χ.constantSupport ⊆ K)
    (hsep : HasSep R (K ∪ E) Γ Δ) : HasSep R K Γ Δ := by
  obtain ⟨θ, hrel, hsupp, hΓ, hΔ⟩ := hsep
  obtain ⟨χ, hr, -, hk, hΓχ, hΔχ⟩ :=
    Theoryω.exists_separator_constantSupport_subset hE hΓK hsupp hΓ hΔ
  refine ⟨χ, ?_, hk, hΓχ, hΔχ⟩
  rw [← relationsInSigned_union_not true χ, hr true, hr (!true),
    relationsInSigned_union_not]
  exact hrel

/-- Existential witness elimination: if `c ∉ pairSupport Γ Δ` and every model of `Γ` admits an
interpretation of `c` satisfying `ψ`, any separator of `(insert ψ Γ, Δ)` with constant budget
`K ∪ {c}` yields `(abstractConst c θ).ex` separating `(Γ, Δ)` with budget `K`. -/
private theorem hasSep_elim_witness {R : Set (Σ n, L[[ℕ]].Relations n)} {K : Set ℕ}
    {Γ Δ : L[[ℕ]].Theoryω} {c : ℕ} (hc : c ∉ pairSupport Γ Δ) {ψ : L[[ℕ]].Sentenceω}
    (hwit : ∀ (M : Type (max u v)) [L[[ℕ]].Structure M] [Nonempty M], Γ.Model M →
      ∃ m : M, @SentenceInf.Realize _ ℕ ψ M (updateStructure c m)) :
    HasSep R (K ∪ {c}) (insert ψ Γ) Δ → HasSep R K Γ Δ := by
  rintro ⟨θ, hrel, hsupp, hΓθ, hΔθ⟩
  refine ⟨(abstractConst c θ).ex, by simpa using hrel, ?_, ?_, ?_⟩
  · rw [constantSupport_ex, constantSupport_abstractConst]
    exact fun d hd => (hsupp hd.1).resolve_right hd.2
  · refine Theoryω.entails_iff.2 fun M _ _ hM => ?_
    obtain ⟨m, hm⟩ := hwit M hM
    rw [SentenceInf.realize_def, FormulaInf.realize_def, realize_ex]
    exact ⟨m, (realize_abstractConst_snoc c θ m).2 <|
      @entails_realize L _ θ hΓθ M (updateStructure c m) ‹_›
        ((@Theoryω.model_insert_iff _ _ M (updateStructure c m) _).2
          ⟨hm, model_updateStructure (fun _ hχ h => hc (subset_pairSupport_left hχ h)) m hM⟩)⟩
  · exact hΔθ.not_ex_abstractConst (fun _ hχ h => hc (subset_pairSupport_right hχ h))

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
    (h : InsepPair R₁ R₂ Γ Δ) : InsepPair R₂ R₁ Δ Γ :=
  ⟨h.finite_right, h.finite_left, h.rel_right, h.rel_left, h.supp_right, h.supp_left, fun hsep =>
    h.insep (by rw [Set.inter_comm, pairSupport_comm]; exact hsep.symm)⟩

private theorem InsepPair.insert_left {R₁ R₂ : Set (Σ n, L.Relations n)}
    {Γ Δ : L[[ℕ]].Theoryω} (h : InsepPair R₁ R₂ Γ Δ) {χ : L[[ℕ]].Sentenceω}
    (hrel : χ.relationsIn ⊆ liftRel R₁) (hfin : χ.constantSupport.Finite)
    (hinsep : ¬ HasSep (liftRel (R₁ ∩ R₂)) (pairSupport (insert χ Γ) Δ) (insert χ Γ) Δ) :
    InsepPair R₁ R₂ (insert χ Γ) Δ :=
  ⟨h.finite_left.insert χ, h.finite_right,
    fun _ hψ => hψ.elim (fun e => e ▸ hrel) (h.rel_left _), h.rel_right,
    fun _ hψ => hψ.elim (fun e => e ▸ hfin) (h.supp_left _), h.supp_right, hinsep⟩

/-- Extending `Γ` by a sentence already entailed by `Γ` whose symbols and constants stay inside
the existing bounds preserves `InsepPair`. -/
private theorem InsepPair.insert_left_of_entails {R₁ R₂ : Set (Σ n, L.Relations n)}
    {Γ Δ : L[[ℕ]].Theoryω} (h : InsepPair R₁ R₂ Γ Δ) {χ : L[[ℕ]].Sentenceω}
    (hrel : χ.relationsIn ⊆ liftRel R₁) (hsupp : χ.constantSupport ⊆ pairSupport Γ Δ)
    (hent : Γ.Entails χ) : InsepPair R₁ R₂ (insert χ Γ) Δ :=
  h.insert_left hrel (h.finite_pairSupport.subset hsupp) <| by
    rw [pairSupport_insert_left_of_subset hsupp]
    exact fun ⟨θ, hr, hs, hΓθ, hΔθ⟩ => h.insep ⟨θ, hr, hs, hent.cut hΓθ, hΔθ⟩

/-- If inserting a bounded sentence `χ` on the left breaks `InsepPair`, `(insert χ Γ, Δ)` admits
a separator within the existing constant budget. -/
private theorem InsepPair.hasSep_insert_left_of_not_insepPair
    {R₁ R₂ : Set (Σ n, L.Relations n)} {Γ Δ : L[[ℕ]].Theoryω} (h : InsepPair R₁ R₂ Γ Δ)
    {χ : L[[ℕ]].Sentenceω} (hrel : χ.relationsIn ⊆ liftRel R₁)
    (hsupp : χ.constantSupport ⊆ pairSupport Γ Δ)
    (hnot : ¬ InsepPair R₁ R₂ (insert χ Γ) Δ) :
    HasSep (liftRel (R₁ ∩ R₂)) (pairSupport Γ Δ) (insert χ Γ) Δ := by
  by_contra hsep
  exact hnot (h.insert_left hrel (h.finite_pairSupport.subset hsupp)
    (pairSupport_insert_left_of_subset hsupp ▸ hsep))

private theorem InsepPair.exists_insert_left {R₁ R₂ : Set (Σ n, L.Relations n)}
    {Γ Δ : L[[ℕ]].Theoryω} (hp : InsepPair R₁ R₂ Γ Δ) (ψs : ℕ → L[[ℕ]].Sentenceω)
    (hrel : ∀ k, (ψs k).relationsIn ⊆ liftRel R₁)
    (hsupp : ∀ k, (ψs k).constantSupport ⊆ pairSupport Γ Δ)
    (hex : ∀ (M : Type (max u v)) [L[[ℕ]].Structure M] [Nonempty M], Γ.Model M →
      ∃ k, SentenceInf.Realize (ψs k) M) :
    ∃ k, InsepPair R₁ R₂ (insert (ψs k) Γ) Δ := by
  by_contra! hnone
  choose θs hr hs hΓ hΔ using fun k =>
    hp.hasSep_insert_left_of_not_insepPair (hrel k) (hsupp k) (hnone k)
  refine hp.insep ⟨.iSup θs, by rw [relationsIn_iSup]; exact Set.iUnion_subset hr,
    by rw [constantSupport_iSup]; exact Set.iUnion_subset hs,
    Theoryω.entails_iff.2 fun M _ _ hM => ?_, Theoryω.entails_iff.2 fun M _ _ hM => ?_⟩
  · obtain ⟨k, hk⟩ := hex M hM
    exact SentenceInf.realize_iSup.2
      ⟨k, entails_realize (hΓ k) M (Theoryω.model_insert_iff.2 ⟨hk, hM⟩)⟩
  · rw [SentenceInf.realize_not, SentenceInf.realize_iSup]
    exact fun ⟨k, hk⟩ => SentenceInf.realize_not.1 (entails_realize (hΔ k) M hM) hk

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
    (hφ : φ ∈ Γ) (hnφ : φ.not ∈ Δ) : False :=
  hp.insep ⟨φ, liftRel_inter R₁ R₂ ▸ Set.subset_inter (hp.rel_left φ hφ)
    (by simpa using hp.rel_right φ.not hnφ), subset_pairSupport_left hφ,
    Theoryω.entails_of_mem hφ, Theoryω.entails_of_mem hnφ⟩

private theorem InsepPair.imp_left {R₁ R₂ : Set (Σ n, L.Relations n)}
    {Γ Δ : L[[ℕ]].Theoryω} (hp : InsepPair R₁ R₂ Γ Δ) {φ ψ : L[[ℕ]].Sentenceω}
    (himp : φ.imp ψ ∈ Γ) :
    InsepPair R₁ R₂ (insert φ.not Γ) Δ ∨ InsepPair R₁ R₂ (insert ψ Γ) Δ := by
  by_contra! hboth
  have hrel := Set.union_subset_iff.1 (relationsIn_imp φ ψ ▸ hp.rel_left _ himp)
  have hsupp :=
    Set.union_subset_iff.1 (constantSupport_imp φ ψ ▸ subset_pairSupport_left (Δ := Δ) himp)
  obtain ⟨θ₁, hr₁, hs₁, hΓ₁, hΔ₁⟩ := hp.hasSep_insert_left_of_not_insepPair
    (by simpa using hrel.1) (by simpa using hsupp.1) hboth.1
  obtain ⟨θ₂, hr₂, hs₂, hΓ₂, hΔ₂⟩ := hp.hasSep_insert_left_of_not_insepPair hrel.2 hsupp.2 hboth.2
  refine hp.insep ⟨θ₁ ⊔ θ₂, by simp [hr₁, hr₂], by simp [hs₁, hs₂],
    Theoryω.entails_iff.2 fun M _ _ hM => SentenceInf.realize_sup.2 ?_,
    Theoryω.entails_iff.2 fun M _ _ hM => ?_⟩
  · have hm := hM.realize_of_mem himp
    simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_imp] at hm
    by_cases hφM : SentenceInf.Realize φ M
    · rw [SentenceInf.realize_def, FormulaInf.realize_def] at hφM
      exact .inr (entails_realize hΓ₂ M (Theoryω.model_insert_iff.2
        ⟨by simpa [SentenceInf.realize_def, FormulaInf.realize_def] using hm hφM, hM⟩))
    · exact .inl (entails_realize hΓ₁ M (Theoryω.model_insert_iff.2
        ⟨SentenceInf.realize_not.2 hφM, hM⟩))
  · rw [SentenceInf.realize_not, SentenceInf.realize_sup, not_or]
    exact ⟨SentenceInf.realize_not.1 (entails_realize hΔ₁ M hM),
      SentenceInf.realize_not.1 (entails_realize hΔ₂ M hM)⟩

private theorem InsepPair.not_imp_left {R₁ R₂ : Set (Σ n, L.Relations n)}
    {Γ Δ : L[[ℕ]].Theoryω} (hp : InsepPair R₁ R₂ Γ Δ) {φ ψ : L[[ℕ]].Sentenceω}
    (hnimp : (φ.imp ψ).not ∈ Γ) :
    InsepPair R₁ R₂ (insert φ Γ) Δ ∧ InsepPair R₁ R₂ (insert ψ.not Γ) Δ := by
  have hrel : φ.relationsIn ∪ ψ.relationsIn ⊆ liftRel R₁ := by simpa using hp.rel_left _ hnimp
  have hsupp : φ.constantSupport ∪ ψ.constantSupport ⊆ pairSupport Γ Δ := by
    simpa using subset_pairSupport_left (Δ := Δ) hnimp
  have hent (M : Type (max u v)) [L[[ℕ]].Structure M] (hM : Γ.Model M) :
      SentenceInf.Realize φ M ∧ SentenceInf.Realize ψ.not M := by
    have hm := hM.realize_of_mem hnimp
    simpa only [SentenceInf.realize_def, FormulaInf.realize_def, realize_not, realize_imp,
      Classical.not_imp] using hm
  exact ⟨hp.insert_left_of_entails (Set.union_subset_iff.1 hrel).1 (Set.union_subset_iff.1 hsupp).1
      (Theoryω.entails_iff.2 fun M _ _ hM => (hent M hM).1),
    hp.insert_left_of_entails (by simpa using (Set.union_subset_iff.1 hrel).2)
      (by simpa using (Set.union_subset_iff.1 hsupp).2)
      (Theoryω.entails_iff.2 fun M _ _ hM => (hent M hM).2)⟩

private theorem InsepPair.iInf_left {R₁ R₂ : Set (Σ n, L.Relations n)}
    {Γ Δ : L[[ℕ]].Theoryω} (hp : InsepPair R₁ R₂ Γ Δ) {φs : ℕ → L[[ℕ]].Sentenceω}
    (hiInf : BoundedFormulaInf.iInf φs ∈ Γ) (k : ℕ) :
    InsepPair R₁ R₂ (insert (φs k) Γ) Δ :=
  hp.insert_left_of_entails
    ((Set.subset_iUnion (fun i => (φs i).relationsIn) k).trans (by simpa using hp.rel_left _ hiInf))
    ((Set.subset_iUnion (fun i => (φs i).constantSupport) k).trans
      (by simpa using subset_pairSupport_left (Δ := Δ) hiInf))
    (Theoryω.entails_iff.2 fun _ _ _ hM => SentenceInf.realize_iInf.1 (hM.realize_of_mem hiInf) k)

private theorem InsepPair.not_iInf_left {R₁ R₂ : Set (Σ n, L.Relations n)}
    {Γ Δ : L[[ℕ]].Theoryω} (hp : InsepPair R₁ R₂ Γ Δ) {φs : ℕ → L[[ℕ]].Sentenceω}
    (hniInf : (BoundedFormulaInf.iInf φs).not ∈ Γ) :
    ∃ k, InsepPair R₁ R₂ (insert (φs k).not Γ) Δ :=
  hp.exists_insert_left (fun k => (φs k).not)
    (fun k => by
      simpa using (Set.subset_iUnion (fun i => (φs i).relationsIn) k).trans
        (by simpa using hp.rel_left _ hniInf))
    (fun k => by
      simpa using (Set.subset_iUnion (fun i => (φs i).constantSupport) k).trans
        (by simpa using subset_pairSupport_left (Δ := Δ) hniInf))
    fun _ _ _ hM => by
      simpa [SentenceInf.realize_not, SentenceInf.realize_iInf] using hM.realize_of_mem hniInf

private theorem InsepPair.iSup_left {R₁ R₂ : Set (Σ n, L.Relations n)}
    {Γ Δ : L[[ℕ]].Theoryω} (hp : InsepPair R₁ R₂ Γ Δ) {φs : ℕ → L[[ℕ]].Sentenceω}
    (hiSup : BoundedFormulaInf.iSup φs ∈ Γ) :
    ∃ k, InsepPair R₁ R₂ (insert (φs k) Γ) Δ :=
  hp.exists_insert_left φs
    (fun k => (Set.subset_iUnion (fun i => (φs i).relationsIn) k).trans
      (by simpa using hp.rel_left _ hiSup))
    (fun k => (Set.subset_iUnion (fun i => (φs i).constantSupport) k).trans
      (by simpa using subset_pairSupport_left (Δ := Δ) hiSup))
    fun _ _ _ hM => SentenceInf.realize_iSup.1 (hM.realize_of_mem hiSup)

private theorem InsepPair.not_iSup_left {R₁ R₂ : Set (Σ n, L.Relations n)}
    {Γ Δ : L[[ℕ]].Theoryω} (hp : InsepPair R₁ R₂ Γ Δ) {φs : ℕ → L[[ℕ]].Sentenceω}
    (hniSup : (BoundedFormulaInf.iSup φs).not ∈ Γ) (k : ℕ) :
    InsepPair R₁ R₂ (insert (φs k).not Γ) Δ :=
  hp.insert_left_of_entails
    (by
      simpa using (Set.subset_iUnion (fun i => (φs i).relationsIn) k).trans
        (by simpa using hp.rel_left _ hniSup))
    (by
      simpa using (Set.subset_iUnion (fun i => (φs i).constantSupport) k).trans
        (by simpa using subset_pairSupport_left (Δ := Δ) hniSup))
    (Theoryω.entails_iff.2 fun _ _ _ hM => SentenceInf.realize_not.2 fun hk =>
      SentenceInf.realize_not.1 (hM.realize_of_mem hniSup) (SentenceInf.realize_iSup.2 ⟨k, hk⟩))

private theorem InsepPair.all_left {R₁ R₂ : Set (Σ n, L.Relations n)}
    {Γ Δ : L[[ℕ]].Theoryω} (hp : InsepPair R₁ R₂ Γ Δ) {φ : L[[ℕ]].BoundedFormulaω Empty 1}
    (hall : φ.all ∈ Γ) (c : ℕ) :
    InsepPair R₁ R₂ (insert (φ.inst (L.con c).term) Γ) Δ := by
  have hsupp : (φ.inst (L.con c).term).constantSupport ⊆ pairSupport Γ Δ ∪ {c} :=
    (constantSupport_inst_subset φ (L.con c).term).trans
      (Set.union_subset_union (by simpa using subset_pairSupport_left (Δ := Δ) hall) (by simp))
  refine hp.insert_left (by simpa [inst_def] using hp.rel_left φ.all hall)
    ((hp.finite_pairSupport.union (Set.finite_singleton c)).subset hsupp) fun ⟨θ, hr, hs, hΓ, hΔ⟩ =>
      hp.insep <| hasSep_of_finite_extra (Set.finite_singleton c) (fun _ => subset_pairSupport_left)
        ⟨θ, hr, hs.trans (pairSupport_insert_left _ ▸ Set.union_subset Set.subset_union_left hsupp),
          (Theoryω.entails_iff.2 fun _ _ _ hM => ?_).cut hΓ, hΔ⟩
  have hm := hM.realize_of_mem hall
  simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_all] at hm
  simpa only [SentenceInf.realize_def, realize_inst, Term.realize_constants, Fin.snoc_zero] using
    hm (L.con c)

private theorem InsepPair.not_all_left {R₁ R₂ : Set (Σ n, L.Relations n)}
    {Γ Δ : L[[ℕ]].Theoryω} (hp : InsepPair R₁ R₂ Γ Δ) {φ : L[[ℕ]].BoundedFormulaω Empty 1}
    (hnall : φ.all.not ∈ Γ) :
    ∃ c, InsepPair R₁ R₂ (insert (φ.inst (L.con c).term).not Γ) Δ := by
  classical
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset hp.finite_pairSupport.toFinset
  have hcK : c ∉ pairSupport Γ Δ := fun h => hc (hp.finite_pairSupport.mem_toFinset.2 h)
  have hφK : φ.constantSupport ⊆ pairSupport Γ Δ := by
    simpa using subset_pairSupport_left (Δ := Δ) hnall
  have hsupp : (φ.inst (L.con c).term).not.constantSupport ⊆ pairSupport Γ Δ ∪ {c} := by
    rw [constantSupport_not]
    exact (constantSupport_inst_subset φ (L.con c).term).trans
      (Set.union_subset_union hφK (by simp))
  refine ⟨c, hp.insert_left (by simpa [inst_def] using hp.rel_left φ.all.not hnall)
    ((hp.finite_pairSupport.union (Set.finite_singleton c)).subset hsupp) fun ⟨θ, hr, hs, hΓ, hΔ⟩ =>
      hp.insep <| hasSep_elim_witness hcK ?_
        ⟨θ, hr, hs.trans (pairSupport_insert_left _ ▸ Set.union_subset Set.subset_union_left hsupp),
          hΓ, hΔ⟩⟩
  intro M _ _ hM
  have hm := SentenceInf.realize_not.1 (hM.realize_of_mem hnall)
  rw [SentenceInf.realize_def, FormulaInf.realize_def, realize_all, not_forall] at hm
  obtain ⟨m, hm⟩ := hm
  refine ⟨m, (@SentenceInf.realize_not _ _ M (updateStructure c m)).2 ?_⟩
  rw [@SentenceInf.realize_def _ _ _ M (updateStructure c m),
    @realize_inst _ _ _ M (updateStructure c m),
    realize_con_updateStructure_self,
    realize_updateStructure_of_notMem (fun h => hcK (hφK h)), ← Fin.snoc_zero default m]
  exact hm

private theorem InsepPair.eq_refl_left {R₁ R₂ : Set (Σ n, L.Relations n)}
    {Γ Δ : L[[ℕ]].Theoryω} (hp : InsepPair R₁ R₂ Γ Δ) (t : L[[ℕ]].Term (Empty ⊕ Fin 0)) :
    InsepPair R₁ R₂ (insert (equal t t) Γ) Δ :=
  hp.insert_left (by simp) (by simpa using t.finite_constantSupport) fun ⟨θ, hr, hs, hΓ, hΔ⟩ =>
    hp.insep <| hasSep_of_finite_extra t.finite_constantSupport (fun _ => subset_pairSupport_left)
      ⟨θ, hr, by simpa [pairSupport_insert_left] using hs,
        (Theoryω.entails_iff.2 fun _ _ _ _ => by
          simp [SentenceInf.realize_def, FormulaInf.realize_def]).cut hΓ, hΔ⟩

private theorem InsepPair.eq_subst_same {R₁ R₂ : Set (Σ n, L.Relations n)}
    {Γ Δ : L[[ℕ]].Theoryω} (hp : InsepPair R₁ R₂ Γ Δ)
    {t t' : L[[ℕ]].Term (Empty ⊕ Fin 0)} {φ : L[[ℕ]].BoundedFormulaω Empty 1}
    (heq : equal t t' ∈ Γ) (hinst : φ.inst t ∈ Γ) :
    InsepPair R₁ R₂ (insert (φ.inst t') Γ) Δ := by
  have htK :=
    Set.union_subset_iff.1 (constantSupport_equal t t' ▸ subset_pairSupport_left (Δ := Δ) heq)
  have hsupp : (φ.inst t').constantSupport ⊆ pairSupport Γ Δ :=
    (constantSupport_inst_subset φ t').trans
      (Set.union_subset
        ((constantSupport_subset_inst φ t).trans (subset_pairSupport_left (Δ := Δ) hinst)) htK.2)
  refine hp.insert_left_of_entails (by simpa [inst_def] using hp.rel_left (φ.inst t) hinst) hsupp
    (Theoryω.entails_iff.2 fun _ _ _ hM => ?_)
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
  have htK :=
    Set.union_subset_iff.1 (constantSupport_equal t t' ▸ subset_pairSupport_left (Δ := Δ) heq)
  have hsupp : (φ.inst t').constantSupport ⊆ pairSupport Γ Δ :=
    (constantSupport_inst_subset φ t').trans
      (Set.union_subset
        ((constantSupport_subset_inst φ t).trans (subset_pairSupport_right (Γ := Γ) hinst)) htK.2)
  refine (hp.symm.insert_left (by simpa [inst_def] using hp.rel_right (φ.inst t) hinst)
    (hp.finite_pairSupport.subset hsupp) ?_).symm
  rw [Set.inter_comm, pairSupport_comm, pairSupport_insert_right_of_subset hsupp]
  intro hsep
  obtain ⟨θ, hθrel, hθsupp, hΓθ, hΔθ⟩ := hsep.symm
  refine hp.insep ⟨equal t t' ⊓ θ, by simpa using hθrel, by simp [htK.1, htK.2, hθsupp],
    Theoryω.entails_iff.2 fun M _ _ hM =>
      SentenceInf.realize_inf.2 ⟨hM.realize_of_mem heq, entails_realize hΓθ M hM⟩,
    Theoryω.entails_iff.2 fun M _ _ hM => ?_⟩
  rw [SentenceInf.realize_not, SentenceInf.realize_inf, not_and]
  intro htM
  have hφM := hM.realize_of_mem hinst
  simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_equal] at htM
  simp only [SentenceInf.realize_def, realize_inst] at hφM
  exact SentenceInf.realize_not.1 (entails_realize hΔθ M (Theoryω.model_insert_iff.2
    ⟨by simp only [SentenceInf.realize_def, realize_inst]; rwa [← htM], hM⟩))

private theorem InsepPair.eq_name_left {R₁ R₂ : Set (Σ n, L.Relations n)}
    {Γ Δ : L[[ℕ]].Theoryω} (hp : InsepPair R₁ R₂ Γ Δ) (t : L[[ℕ]].Term (Empty ⊕ Fin 0)) :
    ∃ c, InsepPair R₁ R₂ (insert (equal (L.con c).term t) Γ) Δ := by
  classical
  have hKt := hp.finite_pairSupport.union t.finite_constantSupport
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset hKt.toFinset
  have hcKt : c ∉ pairSupport Γ Δ ∪ t.constantSupport := fun h => hc (hKt.mem_toFinset.2 h)
  refine ⟨c, hp.insert_left (by simp)
    (by rw [constantSupport_equal, Term.constantSupport_con]
        exact (Set.finite_singleton c).union t.finite_constantSupport)
    fun ⟨θ, hr, hs, hΓ, hΔ⟩ => ?_⟩
  have hs' : θ.constantSupport ⊆ (pairSupport Γ Δ ∪ t.constantSupport) ∪ {c} := by
    refine hs.trans ?_
    rw [pairSupport_insert_left, constantSupport_equal, Term.constantSupport_con]
    intro d hd; aesop
  refine hp.insep <| hasSep_of_finite_extra t.finite_constantSupport
    (fun _ => subset_pairSupport_left) <|
      hasSep_elim_witness (fun h => hcKt (.inl h)) ?_ ⟨θ, hr, hs', hΓ, hΔ⟩
  intro M _ _ _
  let m : M := t.realize (Sum.elim Empty.elim default)
  refine ⟨m, ?_⟩
  rw [@SentenceInf.realize_def _ _ _ M (updateStructure c m),
    @FormulaInf.realize_def _ _ _ M (updateStructure c m),
    @realize_equal _ _ _ _ M (updateStructure c m),
    realize_con_updateStructure_self,
    term_realize_updateStructure_of_notMem (fun h => hcKt (.inr h))]

/-- **The paired-inseparability consistency property** over `L[[ℕ]]`, requiring no relational or
countability assumption on `L`. Right-hand and symmetric mixed cases reduce to the left-hand
clauses via `InsepPair.symm`. -/
private def insepConsistencyProperty (R₁ R₂ : Set (Σ n, L.Relations n)) :
    ConsistencyProperty L where
  sets := {s | ∃ Γ Δ, s = Γ ∪ Δ ∧ InsepPair R₁ R₂ Γ Δ}
  no_falsum := by rintro _ ⟨_, _, rfl, hp⟩ h; exact h.elim hp.not_bot_left hp.symm.not_bot_left
  no_contradiction := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φ (hφ | hφ) (hnφ | hnφ)
    · exact hp.not_contradiction_same hφ hnφ
    · exact hp.not_contradiction_cross hφ hnφ
    · exact hp.symm.not_contradiction_cross hφ hnφ
    · exact hp.symm.not_contradiction_same hφ hnφ
  imp := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φ ψ (himp | himp)
    · exact (hp.imp_left himp).imp (⟨_, _, Set.insert_union.symm, ·⟩)
        (⟨_, _, Set.insert_union.symm, ·⟩)
    · exact (hp.symm.imp_left himp).imp (fun h => ⟨_, _, Set.union_insert.symm, h.symm⟩)
        (fun h => ⟨_, _, Set.union_insert.symm, h.symm⟩)
  not_imp := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φ ψ (hnimp | hnimp)
    · exact (hp.not_imp_left hnimp).imp (⟨_, _, Set.insert_union.symm, ·⟩)
        (⟨_, _, Set.insert_union.symm, ·⟩)
    · exact (hp.symm.not_imp_left hnimp).imp (fun h => ⟨_, _, Set.union_insert.symm, h.symm⟩)
        (fun h => ⟨_, _, Set.union_insert.symm, h.symm⟩)
  iInf := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φs (hiInf | hiInf) k
    · exact ⟨_, _, Set.insert_union.symm, hp.iInf_left hiInf k⟩
    · exact ⟨_, _, Set.union_insert.symm, (hp.symm.iInf_left hiInf k).symm⟩
  not_iInf := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φs (hniInf | hniInf)
    · exact (hp.not_iInf_left hniInf).imp fun _ hk => ⟨_, _, Set.insert_union.symm, hk⟩
    · exact (hp.symm.not_iInf_left hniInf).imp fun _ hk => ⟨_, _, Set.union_insert.symm, hk.symm⟩
  iSup := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φs (hiSup | hiSup)
    · exact (hp.iSup_left hiSup).imp fun _ hk => ⟨_, _, Set.insert_union.symm, hk⟩
    · exact (hp.symm.iSup_left hiSup).imp fun _ hk => ⟨_, _, Set.union_insert.symm, hk.symm⟩
  not_iSup := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φs (hniSup | hniSup) k
    · exact ⟨_, _, Set.insert_union.symm, hp.not_iSup_left hniSup k⟩
    · exact ⟨_, _, Set.union_insert.symm, (hp.symm.not_iSup_left hniSup k).symm⟩
  all := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φ (hall | hall) c
    · exact ⟨_, _, Set.insert_union.symm, hp.all_left hall c⟩
    · exact ⟨_, _, Set.union_insert.symm, (hp.symm.all_left hall c).symm⟩
  not_all := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φ (hnall | hnall)
    · exact (hp.not_all_left hnall).imp fun _ hc => ⟨_, _, Set.insert_union.symm, hc⟩
    · exact (hp.symm.not_all_left hnall).imp fun _ hc => ⟨_, _, Set.union_insert.symm, hc.symm⟩
  eq_refl := by rintro _ ⟨_, _, rfl, hp⟩ t; exact ⟨_, _, Set.insert_union.symm, hp.eq_refl_left t⟩
  eq_subst := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ t t' φ _ (heq | heq) (hinst | hinst)
    · exact ⟨_, _, Set.insert_union.symm, hp.eq_subst_same heq hinst⟩
    · exact ⟨_, _, Set.union_insert.symm, hp.eq_subst_cross heq hinst⟩
    · exact ⟨_, _, Set.insert_union.symm, (hp.symm.eq_subst_cross heq hinst).symm⟩
    · exact ⟨_, _, Set.union_insert.symm, (hp.symm.eq_subst_same heq hinst).symm⟩
  eq_name := by
    rintro _ ⟨_, _, rfl, hp⟩ t
    exact (hp.eq_name_left t).imp fun _ hc => ⟨_, _, Set.insert_union.symm, hc⟩

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
    refine ⟨{φ'}, {ψ'.not}, rfl, Set.finite_singleton _, Set.finite_singleton _,
      fun _ hχ => by rw [Set.mem_singleton_iff.1 hχ, LHom.relationsIn_onBoundedFormulaInf],
      fun _ hχ => by
        rw [Set.mem_singleton_iff.1 hχ, relationsIn_not, LHom.relationsIn_onBoundedFormulaInf],
      fun _ hχ => by rw [Set.mem_singleton_iff.1 hχ]; simp [φ', g],
      fun _ hχ => by rw [Set.mem_singleton_iff.1 hχ]; simp [ψ', g], ?_⟩
    rintro ⟨θ', hθ'rel, hθ'supp, hφ'θ', hψ'θ'⟩
    have hK : pairSupport ({φ'} : L[[ℕ]].Theoryω) {ψ'.not} = ∅ := by simp [pairSupport, φ', ψ', g]
    obtain ⟨θ, rfl⟩ := constantSupport_eq_empty_iff.1 (Set.subset_empty_iff.1 (hK ▸ hθ'supp))
    refine hno ⟨θ, fun ⟨n, r⟩ hr => ?_, ?_, ?_⟩
    · rw [LHom.relationsIn_onBoundedFormulaInf] at hθ'rel
      obtain ⟨⟨m, r₀⟩, hr₀, hm⟩ := hθ'rel ⟨⟨n, r⟩, hr, rfl⟩
      obtain ⟨rfl, heq⟩ := Sigma.mk.inj_iff.1 hm
      obtain rfl := (L.lhomWithConstants_injective ℕ).onRelation (eq_of_heq heq)
      exact hr₀
    · exact (Sentenceω.entails_onBoundedFormulaInf_iff (L.lhomWithConstants_injective ℕ)).1
        (Sentenceω.entails_def.2 hφ'θ')
    · have hnot : Sentenceω.Entails ψ.not θ.not :=
        (Sentenceω.entails_onBoundedFormulaInf_iff (L.lhomWithConstants_injective ℕ)).1
          (by simpa [ψ', g] using Sentenceω.entails_def.2 hψ'θ')
      exact Sentenceω.entails_iff.2 fun M _ _ hθM => by
        by_contra hψM
        exact SentenceInf.realize_not.1 (hnot.realize M (SentenceInf.realize_not.2 hψM)) hθM
  obtain ⟨M, _, _, _, hM, _⟩ :=
    (insepConsistencyProperty φ.relationsIn ψ.relationsIn).model_existence.{u, v, max u v} hs
      ((Set.countable_singleton _).union (Set.countable_singleton _))
  let : L.Structure M := g.reduct M
  have hφM : SentenceInf.Realize φ M :=
    (LHom.realize_sentenceInf_onBoundedFormulaInf g φ).1
      (hM.realize_of_mem (.inl (Set.mem_singleton _)))
  exact SentenceInf.realize_not.1 (hM.realize_of_mem (.inr (Set.mem_singleton _)))
    ((LHom.realize_sentenceInf_onBoundedFormulaInf g ψ).2 (h.realize M hφM))

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
  let φ₀ : (symbSublang F R).Sentenceω := φ.restrictSymbols hFφ Set.subset_union_left
  let ψ₀ : (symbSublang F R).Sentenceω := ψ.restrictSymbols hFψ Set.subset_union_right
  have hφ₀ : (symbSublangIncl F R).onBoundedFormulaInf φ₀ = φ :=
    onBoundedFormulaInf_restrictSymbols φ hFφ Set.subset_union_left
  have hψ₀ : (symbSublangIncl F R).onBoundedFormulaInf ψ₀ = ψ :=
    onBoundedFormulaInf_restrictSymbols ψ hFψ Set.subset_union_right
  have h₀ : Sentenceω.Entails φ₀ ψ₀ :=
    (Sentenceω.entails_onBoundedFormulaInf_iff (symbSublangIncl_injective F R)).1
      (by rwa [hφ₀, hψ₀])
  obtain ⟨θ₀, hrel₀, hφθ₀, hθψ₀⟩ := craig_interpolation_relational_of_countable φ₀ ψ₀ h₀
  refine ⟨(symbSublangIncl F R).onBoundedFormulaInf θ₀, ?_,
    hφ₀ ▸ hφθ₀.onBoundedFormulaInf (symbSublangIncl F R),
    hψ₀ ▸ hθψ₀.onBoundedFormulaInf (symbSublangIncl F R)⟩
  rw [LHom.relationsIn_onBoundedFormulaInf]
  refine ((Set.image_mono hrel₀).trans (Set.image_inter_subset _ _ _)).trans ?_
  rw [← LHom.relationsIn_onBoundedFormulaInf, ← LHom.relationsIn_onBoundedFormulaInf, hφ₀, hψ₀]

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
  exact Set.iUnion_subset fun φ => Set.subset_biUnion_of_mem φ.2

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
  refine ⟨θ₀.restrictSymbols hF hrel, ?_, ?_⟩
  · intro M _ _ hM₁
    let : (symbSublang (ψ₁.functionsIn ∩ ψ₂.functionsIn)
        (ψ₁.relationsIn ∩ ψ₂.relationsIn)).Structure M :=
      (symbSublangIncl _ _).reduct M
    have hM := h₁.realize M hM₁
    rw [SentenceInf.realize_def, FormulaInf.realize_def] at hM ⊢
    exact (realize_restrictSymbols θ₀ hF hrel Empty.elim default).2 hM
  · intro M _ _ hM₂ hθM
    let : (symbSublang (ψ₁.functionsIn ∩ ψ₂.functionsIn)
        (ψ₁.relationsIn ∩ ψ₂.relationsIn)).Structure M :=
      (symbSublangIncl _ _).reduct M
    rw [SentenceInf.realize_def, FormulaInf.realize_def] at hθM
    exact SentenceInf.realize_not.1 (h₂.realize M <| by
      rw [SentenceInf.realize_def, FormulaInf.realize_def]
      exact (realize_restrictSymbols θ₀ hF hrel Empty.elim default).1 hθM) hM₂

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
    refine SentenceInf.realize_not.2 fun hM₂ => ?_
    let : L.Structure M := (LHom.sumInl : L →ᴸ L.sum (L₁.sum L₂)).reduct M
    obtain ⟨h₁, h₂⟩ := LHom.pcMem_sumInl_inf_iff.1
      (LHom.pcMem_of_isExpansionOn (SentenceInf.realize_inf.2 ⟨hM₁, hM₂⟩))
    exact h M h₁ h₂
  obtain ⟨θ', hrel, h₁, h₂⟩ := craig_interpolation_relational Θ₁' Θ₂'.not hent
  have hR : θ'.relationsIn ⊆ Set.range fun s : Σ n, L.Relations n =>
      (⟨s.1, (LHom.sumInl : L →ᴸ L.sum (L₁.sum L₂)).onRelation s.2⟩ :
        Σ k, (L.sum (L₁.sum L₂)).Relations k) := by
    intro _ hR'
    obtain ⟨hR₁, hR₂⟩ := hrel hR'
    rw [relationsIn_not] at hR₂
    rw [LHom.relationsIn_onBoundedFormulaInf] at hR₁ hR₂
    obtain ⟨⟨k₁, r₁ | r₁⟩, -, rfl⟩ := hR₁
    · exact ⟨⟨k₁, r₁⟩, rfl⟩
    · obtain ⟨⟨k₂, r₂ | r₂⟩, -, hr₂⟩ := hR₂ <;> obtain ⟨rfl, heq⟩ := Sigma.mk.inj_iff.1 hr₂
      · exact (Sum.inl_ne_inr (eq_of_heq heq)).elim
      · exact (Sum.inr_ne_inl (Sum.inr.inj (eq_of_heq heq))).elim
  obtain ⟨θ, hθ⟩ := LHom.exists_eq_onBoundedFormulaInf_of_subset_range
    (LHom.sumInl : L →ᴸ L.sum (L₁.sum L₂)) θ' (fun s _ => isEmptyElim s.2) hR
  have hcomp₁ : g₁.onBoundedFormulaInf (LHom.sumInl.onBoundedFormulaInf θ) = θ' := by
    rw [← LHom.comp_onBoundedFormulaInf, LHom.sumMap_comp_inl, LHom.comp_id, hθ]
  have hcomp₂ : g₂.onBoundedFormulaInf (LHom.sumInl.onBoundedFormulaInf θ) = θ' := by
    rw [← LHom.comp_onBoundedFormulaInf, LHom.sumMap_comp_inl, LHom.comp_id, hθ]
  refine ⟨θ, (Sentenceω.entails_onBoundedFormulaInf_iff hg₁).1 (hcomp₁ ▸ h₁),
    (Sentenceω.entails_onBoundedFormulaInf_iff hg₂).1 ?_⟩
  rw [LHom.onBoundedFormulaInf_not, hcomp₂]
  exact Sentenceω.entails_iff.2 fun M _ _ hM₂ =>
    SentenceInf.realize_not.2 fun hθ'M => SentenceInf.realize_not.1 (h₂.realize M hθ'M) hM₂

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
  exact ⟨θ, fun M _ _ _ => ⟨h₁ M, fun hθM => by_contra fun hM₁ => h₂ M ((h M).not_left.1 hM₁) hθM⟩⟩

end PCSeparation

end FirstOrder.Language
