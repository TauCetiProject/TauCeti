/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import TauCeti.ModelTheory.RelationalConfiguration.BackAndForth
public import TauCeti.ModelTheory.RelationalConfiguration.ModelsOf
public import TauCeti.ModelTheory.Scott.Height
import Mathlib.Topology.Baire.LocallyCompactRegular
import TauCeti.Data.Set.Card
import TauCeti.GroupTheory.Perm.Basic
import all TauCeti.ModelTheory.RelationalConfiguration.Basic
import TauCeti.SetTheory.Descriptive.EZero
import TauCeti.Topology.Baire.Perfect
import TauCeti.Topology.Perfect

/-!
# Configurations of one unary predicate

A configuration in the language of one unary predicate is a Boolean function on its carrier.
This identification is a homeomorphism and takes relabelling to permutation of the coordinates.
On a countable carrier, the two extended natural cardinalities of the predicate and its
complement classify the orbits. Each orbit is Borel and defined by a sentence specifying the
two sizes. Back-and-forth equivalence at ω already decides isomorphism. The set of codes on ℕ
with a finite predicate is a Borel invariant set that is not Gδ.
-/

public section

open FirstOrder FirstOrder.Language Set
open scoped ENat Ordinal

namespace TauCeti.RelationalConfiguration.UnaryPredicate

/-- The only relation symbol in the language is a unary predicate. -/
inductive Relation : ℕ → Type
  | pred : Relation 1

/-- The language of one unary predicate. -/
@[expose] def language : Language := ⟨fun _ => Empty, Relation⟩
  deriving IsRelational

/-- There is at most one relation symbol of each arity. -/
instance (n : ℕ) : Countable (language.Relations n) := by
  have : Subsingleton (Relation n) := ⟨by rintro ⟨⟩ ⟨⟩; rfl⟩
  exact inferInstanceAs (Countable (Relation n))

universe u

variable {V : Type u}

private def atomEquiv : V ≃ Atom language V where
  toFun v := atom Relation.pred (fun _ => v)
  invFun a := by
    obtain ⟨n, r, x⟩ := a
    cases r
    exact x 0
  left_inv _ := rfl
  right_inv := by
    rintro ⟨n, r, x⟩
    cases r
    -- The tuple of a unary atom is determined by its entry at zero.
    have hx : (fun _ : Fin 1 => x 0) = x := funext fun i => congrArg x (Subsingleton.elim 0 i)
    simp only [atom]
    rw [hx]

/-- Reading the unary predicate at each point gives a homeomorphism to the Boolean product.
For carrier ℕ this product is Cantor space. -/
def coordinates : RelationalConfiguration language V ≃ₜ (V → Bool) :=
  (Homeomorph.piCongrLeft (Y := fun _ : Atom language V => Bool) atomEquiv).symm

/-- The coordinate at v is the truth value of the predicate at v. -/
@[simp]
theorem coordinates_apply (c : RelationalConfiguration language V) (v : V) :
    coordinates c v = c.eval (atom Relation.pred fun _ => v) := by
  rw [eval_def]
  rfl

/-- Coding a Boolean function assigns its value at v to the unary atom at v. -/
@[simp]
theorem eval_coordinates_symm (f : V → Bool) (v : V) :
    (coordinates.symm f).eval (atom Relation.pred fun _ => v) = f v := by
  rw [← coordinates_apply]
  exact congrFun (coordinates.apply_symm_apply f) v

/-- Relabelling permutes the coordinates by precomposition with the inverse permutation. -/
theorem coordinates_smul (σ : Equiv.Perm V) (c : RelationalConfiguration language V) (v : V) :
    coordinates (σ • c) v = coordinates c (σ.symm v) := by
  rw [coordinates_apply, eval_perm_smul,
    @Atom.map_atom language V V σ.symm 1 Relation.pred (fun _ => v), coordinates_apply]
  -- Composing the constant unary tuple with the permutation is pointwise evaluation.
  rfl

/-- The points at which the predicate holds. -/
def predicateSet (c : RelationalConfiguration language V) : Set V :=
  {v | coordinates c v = true}

/-- Predicate membership is truth of the corresponding Boolean coordinate. -/
@[simp]
theorem mem_predicateSet {c : RelationalConfiguration language V} {v : V} :
    v ∈ predicateSet c ↔ coordinates c v = true := Iff.rfl

/-- In the decoded structure a unary atom holds exactly when its entry belongs to the predicate. -/
@[simp]
theorem relMap_pred (c : RelationalConfiguration language V) (x : Fin 1 → V) :
    @Structure.RelMap language V c.toStructure 1 Relation.pred x ↔ x 0 ∈ predicateSet c := by
  have hx : x = fun _ => x 0 := funext fun i => congrArg x (Subsingleton.elim i 0)
  exact (toStructure_relMap (L := language) c (n := 1) Relation.pred x).trans (by
    rw [hx, mem_predicateSet, coordinates_apply])

noncomputable section

/-- The cardinalities of the predicate and its complement, using ⊤ for an infinite class. -/
def cardinalities (c : RelationalConfiguration language V) : ℕ∞ × ℕ∞ :=
  ((predicateSet c).encard, (predicateSet c)ᶜ.encard)

/-- The first coordinate counts the elements satisfying the predicate. -/
@[simp]
theorem cardinalities_fst (c : RelationalConfiguration language V) :
    (cardinalities c).1 = (predicateSet c).encard := by rfl

/-- The second coordinate counts the elements failing the predicate. -/
@[simp]
theorem cardinalities_snd (c : RelationalConfiguration language V) :
    (cardinalities c).2 = (predicateSet c)ᶜ.encard := by rfl

/-- The two cardinalities add to the cardinality of the carrier. -/
theorem cardinalities_add (c : RelationalConfiguration language V) :
    (cardinalities c).1 + (cardinalities c).2 = ENat.card V := by
  rw [cardinalities_fst, cardinalities_snd, encard_add_encard_compl]

/-- A pair of extended natural numbers occurs as predicate-class sizes on ℕ exactly when
their sum is infinite. -/
theorem range_cardinalities_nat :
    range (cardinalities (V := ℕ)) = {p | p.1 + p.2 = ⊤} := by
  classical
  have realize (s : Set ℕ) : (s.encard, sᶜ.encard) ∈ range (cardinalities (V := ℕ)) := by
    let c : RelationalConfiguration language ℕ := coordinates.symm fun n => decide (n ∈ s)
    have hc : predicateSet c = s := by
      ext n
      simp [c]
    exact ⟨c, by rw [cardinalities, hc]⟩
  have hfin (n : ℕ) : (Iio n).encard = n := by
    rw [← Finset.coe_range, encard_coe_eq_coe_finsetCard, Finset.card_range]
  have hinf (n : ℕ) : (Iio n)ᶜ.encard = ⊤ := (finite_Iio n).infinite_compl.encard_eq
  refine subset_antisymm ?_ ?_
  · rintro _ ⟨c, rfl⟩
    exact (cardinalities_add c).trans ENat.card_eq_top_of_infinite
  · rintro ⟨a, b⟩ hab
    simp only [mem_ofPred_eq] at hab
    by_cases ha : a = ⊤
    · subst a
      by_cases hb : b = ⊤
      · subst b
        -- The even and odd progressions give infinitely many points on each side.
        let s := range (fun n : ℕ => n + n)
        have hs : s.Infinite := infinite_range_of_injective (by
          intro i j h
          dsimp at h
          omega)
        have ht : sᶜ.Infinite := by
          refine (infinite_range_of_injective (f := fun n : ℕ => n + n + 1)
            (by
              intro i j h
              dsimp at h
              omega)).mono ?_
          rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
          dsimp at hj
          omega
        simpa only [hs.encard_eq, ht.encard_eq] using realize s
      · simpa only [compl_compl, hfin, hinf, ENat.natCast_toNat hb] using realize (Iio b.toNat)ᶜ
    · have hb := (ENat.add_eq_top.mp hab).resolve_left ha
      subst b
      simpa only [hfin, hinf, ENat.natCast_toNat ha] using realize (Iio a.toNat)

/-- Two configurations on a countable carrier are isomorphic exactly when their predicate
classes have the same cardinalities. -/
theorem isoSetoid_iff_cardinalities_eq [Countable V] {c d : RelationalConfiguration language V} :
    isoSetoid language V c d ↔ cardinalities c = cardinalities d := by
  classical
  rw [isoSetoid_iff_exists_perm_smul_eq]
  constructor
  · rintro ⟨σ, rfl⟩
    have h (v : V) : v ∈ predicateSet c ↔ σ v ∈ predicateSet (σ • c) := by
      simp only [mem_predicateSet, coordinates_smul, Equiv.symm_apply_apply]
    simp only [Prod.ext_iff, cardinalities_fst, cardinalities_snd]
    exact ⟨encard_congr (σ.subtypeEquiv h),
      encard_congr (σ.subtypeEquiv fun v => not_congr (h v))⟩
  · intro h
    simp only [Prod.ext_iff, cardinalities_fst, cardinalities_snd] at h
    obtain ⟨e⟩ := (encard_eq_iff_nonempty_equiv (to_countable _) (to_countable _)).mp h.1
    obtain ⟨f⟩ := (encard_eq_iff_nonempty_equiv (to_countable _) (to_countable _)).mp h.2
    let σ : Equiv.Perm V := Equiv.subtypeCongr e f
    have hσ (v : V) : v ∈ predicateSet c ↔ σ v ∈ predicateSet d := by
      by_cases hv : v ∈ predicateSet c
      · simp [σ, Equiv.subtypeCongr, hv]
      · have hd : (f ⟨v, hv⟩ : V) ∉ predicateSet d := (f ⟨v, hv⟩).2
        simpa [σ, Equiv.subtypeCongr, hv] using hd
    refine ⟨σ, coordinates.injective (funext fun v => ?_)⟩
    rw [coordinates_smul, Bool.eq_iff_iff]
    simpa only [mem_predicateSet, Equiv.apply_symm_apply] using hσ (σ.symm v)

/-- The unary predicate space on a countable carrier has only countably many orbits. -/
theorem countable_quotient_isoSetoid [Countable V] :
    Countable (Quotient (isoSetoid language V)) := by
  let f : Quotient (isoSetoid language V) → ℕ∞ × ℕ∞ :=
    Quotient.lift cardinalities (fun _ _ h => isoSetoid_iff_cardinalities_eq.mp h)
  refine Function.Injective.countable (f := f) ?_
  intro x y
  induction x using Quotient.inductionOn
  induction y using Quotient.inductionOn
  exact fun h => Quotient.sound (isoSetoid_iff_cardinalities_eq.mpr h)

end

-- A finite lower bound is expressed by a tuple of pairwise distinct elements of one color.
private noncomputable def cardAtLeast (b : Bool) (k : ℕ) : language.Sentence :=
  ((BoundedFormula.iInf fun i : Fin k =>
      let p := Relations.boundedFormula₁ (L := language) Relation.pred (&i)
      if b then p else p.not) ⊓
    (BoundedFormula.iInf fun ij : {ij : Fin k × Fin k // ij.1 ≠ ij.2} =>
      ((&ij.1.1).bdEqual (&ij.1.2)).not)).exs

private theorem realize_cardAtLeast (c : RelationalConfiguration language V) (b : Bool) (k : ℕ) :
    @Sentence.Realize language V c.toStructure (cardAtLeast b k) ↔
      (k : ℕ∞) ≤ {v | coordinates c v = b}.encard := by
  rw [le_encard_iff_exists_fin_injective, Sentence.Realize, cardAtLeast]
  simp only [BoundedFormula.realize_exs, BoundedFormula.realize_inf, BoundedFormula.realize_iInf,
    BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    Subtype.forall, Prod.forall, mem_ofPred_eq]
  apply exists_congr
  intro xs
  rw [Function.injective_iff_pairwise_ne]
  simp only [Pairwise, Function.onFun]
  apply and_congr_left
  intro _
  let := c.toStructure
  have hrel (i : Fin k) :
      (Relations.boundedFormula₁ (L := language) Relation.pred (&i)).Realize
          (default : Empty → V) xs ↔ coordinates c (xs i) = true := by
    refine BoundedFormula.realize_rel₁.trans ?_
    simpa only [Function.comp_apply, Term.realize_var, Sum.elim_inr, Matrix.cons_val_zero,
      mem_predicateSet] using relMap_pred c ![xs i]
  cases b
  · simp only [Bool.false_eq_true, ite_false, BoundedFormula.realize_not, hrel, ← Bool.eq_false_iff]
  · exact forall_congr' hrel

-- The size of a color class is specified by all its finite cardinal lower bounds.
private noncomputable def cardSentence (b : Bool) (k : ℕ∞) : language.Sentenceω :=
  .iInf fun n : ℕ =>
    if (n : ℕ∞) ≤ k then (cardAtLeast b n).toInf else (cardAtLeast b n).toInf.not

private theorem realize_cardSentence (c : RelationalConfiguration language V) (b : Bool)
    (k : ℕ∞) :
    @SentenceInf.Realize language ℕ (cardSentence b k) V c.toStructure ↔
      {v | coordinates c v = b}.encard = k := by
  let := c.toStructure
  have hn (n : ℕ) :
      SentenceInf.Realize (ι := ℕ)
        (if (n : ℕ∞) ≤ k then (cardAtLeast b n).toInf else (cardAtLeast b n).toInf.not) V ↔
        ((n : ℕ∞) ≤ {v | coordinates c v = b}.encard ↔ (n : ℕ∞) ≤ k) := by
    by_cases h : (n : ℕ∞) ≤ k <;>
      simp only [h, ite_true, ite_false, iff_true, iff_false, Sentence.realize_toInf,
        SentenceInf.realize_not, realize_cardAtLeast]
  simp only [cardSentence, SentenceInf.realize_iInf, hn]
  exact ⟨ENat.eq_of_forall_natCast_le_iff, fun h _ => h ▸ Iff.rfl⟩

/-- An explicit infinitary sentence specifying both predicate-class sizes. Finite size means that
the corresponding class has exactly that many elements, and ⊤ means it is infinite. -/
noncomputable def cardinalitiesSentence (sizes : ℕ∞ × ℕ∞) : language.Sentenceω :=
  cardSentence true sizes.1 ⊓ cardSentence false sizes.2

/-- The sentence for a pair of cardinalities has precisely the configurations with those
predicate-class sizes as models. -/
theorem mem_modelsOf_cardinalitiesSentence (c : RelationalConfiguration language V)
    (sizes : ℕ∞ × ℕ∞) :
    c ∈ modelsOf (cardinalitiesSentence sizes) ↔ cardinalities c = sizes := by
  have h : {v | coordinates c v = false} = (predicateSet c)ᶜ := by
    ext v
    simp only [mem_predicateSet, mem_compl_iff, mem_ofPred_eq]
    cases coordinates c v <;> decide
  have hp : {v | coordinates c v = true} = predicateSet c :=
    Set.ext fun _ => mem_predicateSet.symm
  rw [Prod.ext_iff]
  simp only [mem_modelsOf, cardinalitiesSentence, SentenceInf.realize_inf, realize_cardSentence,
    hp, h, cardinalities_fst, cardinalities_snd]

/-- On a countable carrier, each orbit is exactly the model class of its sizes sentence. -/
theorem modelsOf_cardinalitiesSentence_eq_isoClass [Countable V]
    (c : RelationalConfiguration language V) :
    modelsOf (V := V) (cardinalitiesSentence (cardinalities c)) =
      {d | isoSetoid language V c d} := by
  ext d
  rw [mem_modelsOf_cardinalitiesSentence, mem_ofPred_eq, isoSetoid_iff_cardinalities_eq, eq_comm]

/-- On a countable carrier, every unary orbit is Borel. -/
theorem measurableSet_isoClass [Countable V] (c : RelationalConfiguration language V) :
    MeasurableSet {d | isoSetoid language V c d} := by
  rw [← modelsOf_cardinalitiesSentence_eq_isoClass]
  exact measurableSet_modelsOf _

/-- A tuple's atomic type determines its orbit under the automorphism group of a unary structure. -/
private theorem exists_automorphism_of_sameAtomicType (c : RelationalConfiguration language V)
    {n : ℕ} {a b : Fin n → V}
    (hab : @SameAtomicType language n V V c.toStructure c.toStructure _ a b) :
    ∃ e : @Language.Equiv language V V c.toStructure c.toStructure, e ∘ a = b := by
  let := c.toStructure
  have h (i : Fin n) : coordinates c (a i) = coordinates c (b i) := by
    rw [Bool.eq_iff_iff]
    simpa only [relMap_pred, Function.comp_apply, mem_predicateSet]
      using hab.rel_iff Relation.pred (fun _ => i)
  obtain ⟨σ, hσ, hσab⟩ := exists_perm_apply_eq_of_eq_iff (coordinates c) hab.eq_iff h
  refine ⟨{ toEquiv := σ, map_fun' := fun f => isEmptyElim f, map_rel' := ?_ },
    funext hσab⟩
  intro k r x
  cases r
  simp only [relMap_pred, Function.comp_apply, mem_predicateSet, Equiv.toFun_as_coe, hσ]

/-- Every unary configuration has external Scott height at most ω. Agreement at level zero
already gives an automorphism taking one tuple to the other within the structure. -/
theorem scottHeight_le_omega0 (c : RelationalConfiguration language V) :
    @scottHeight language _ V c.toStructure ≤ ω := by
  let := c.toStructure
  have h : SelfStabilizesCompletely (L := language) V (0 : Ordinal) := by
    rw [selfStabilizesCompletely_def]
    intro n a b
    refine ⟨fun hab => ?_, fun hab => hab.mono le_self_add⟩
    obtain ⟨e, rfl⟩ := exists_automorphism_of_sameAtomicType c (BFEquiv.zero.mp hab)
    exact e.bfEquiv _ a
  exact scottHeight_le (by simpa only [zero_add] using h.stabilizesCompletely_add_omega0)

/-- On a countable carrier, back-and-forth equivalence at ω decides isomorphism of unary codes. -/
theorem isoSetoid_eq_bfEquivSetoid_omega0 [Countable V] :
    isoSetoid language V = bfEquivSetoid language V (ω : Ordinal.{u}) := by
  apply le_antisymm (isoSetoid_le_bfEquivSetoid _)
  intro c d h
  rw [bfEquivSetoid_apply] at h
  exact isoSetoid_apply.mpr (@nonempty_equiv_of_bfEquiv_of_scottHeight_le language _
    V c.toStructure _ V d.toStructure _ _ (scottHeight_le_omega0 c) h)

/-- The isomorphism relation on unary configurations on a countable carrier is Borel. -/
theorem measurableSet_isoSetoid [Countable V] :
    MeasurableSet {p : RelationalConfiguration language V × RelationalConfiguration language V |
      isoSetoid language V p.1 p.2} := by
  rw [isoSetoid_eq_bfEquivSetoid_omega0]
  exact measurableSet_setOf_bfEquivSetoid Ordinal.omega0_lt_omega_one

/-- The codes on ℕ with only finitely many positive instances of the predicate. -/
def finitePredicate : Set (RelationalConfiguration language ℕ) :=
  {c | (predicateSet c).Finite}

/-- A code belongs to the finite-predicate class exactly when its predicate is finite. -/
@[simp]
theorem mem_finitePredicate {c : RelationalConfiguration language ℕ} :
    c ∈ finitePredicate ↔ (predicateSet c).Finite := Iff.rfl

private theorem finitePredicate_eq_preimage_eZero :
    finitePredicate = coordinates ⁻¹' {f | eZero (fun _ => false) f} := by
  ext c
  have h : predicateSet c = {n | false ≠ coordinates c n} := by
    ext n
    simp only [mem_predicateSet, mem_ofPred_eq]
    cases coordinates c n <;> decide
  simp only [mem_finitePredicate, mem_ofPred_eq, mem_preimage, eZero_iff_finite, h]

/-- Only countably many codes on ℕ have a finite predicate. -/
theorem countable_finitePredicate : finitePredicate.Countable := by
  rw [finitePredicate_eq_preimage_eZero]
  exact (countable_setOf_eZero _).preimage coordinates.injective

/-- Being finite is invariant under isomorphism of unary codes. -/
theorem isomorphismInvariant_finitePredicate : IsomorphismInvariant finitePredicate := by
  apply isomorphismInvariant_iff.mpr
  intro c d h hc
  simp only [mem_finitePredicate] at hc ⊢
  have h' := congrArg Prod.fst (isoSetoid_iff_cardinalities_eq.mp h)
  rw [cardinalities_fst, cardinalities_fst] at h'
  exact encard_lt_top_iff.mp (h' ▸ hc.encard_lt_top)

/-- The finite-predicate class is the union of the orbits of its members, indexed by the
countable set of finite-predicate codes. -/
theorem finitePredicate_eq_iUnion_isoSetoid :
    finitePredicate = ⋃ c : finitePredicate, {d | isoSetoid language ℕ c.1 d} := by
  ext d
  simp only [mem_iUnion, mem_ofPred_eq, Subtype.exists]
  exact ⟨fun hd => ⟨d, hd, (isoSetoid language ℕ).refl d⟩,
    fun ⟨c, hc, hcd⟩ => isomorphismInvariant_iff.mp isomorphismInvariant_finitePredicate hcd hc⟩

/-- The finite-predicate class on ℕ is Borel. -/
theorem measurableSet_finitePredicate : MeasurableSet finitePredicate :=
  countable_finitePredicate.measurableSet

/-- The finite-predicate class on ℕ is not Gδ, since its image in Cantor space is the countable
dense eventual-equality class of the constantly false sequence. -/
theorem not_isGδ_finitePredicate : ¬ IsGδ finitePredicate := by
  intro h
  have h' : IsGδ {f | eZero (fun _ => false) f} := by
    convert h.preimage coordinates.symm.continuous using 1
    rw [finitePredicate_eq_preimage_eZero, preimage_preimage]
    simp
  exact not_isMeagre_of_isGδ_of_dense h' (dense_setOf_eZero _)
    (countable_setOf_eZero _).isMeagre

end TauCeti.RelationalConfiguration.UnaryPredicate
