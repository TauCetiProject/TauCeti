/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Enumeration.Relative.Code
public import TauCeti.Computability.Enumeration.Unpaused
public import TauCeti.Computability.Hierarchy.One
import TauCeti.Computability.SingleOracle.Staged.Search
import TauCeti.Data.PFun.Basic

/-!
# Total and injective ranges relative to an oracle

A domain program and a known member of its domain give a total range program.
The range program tests a single bounded computation on each input, using the
known member when that test fails.

For an injective enumeration, we serialize the domain stages and compile
the search `TauCeti.Enumeration.entryAt` for an element at a specified discovery
position. The search works also for finite domains, where it is undefined after
the final entry. Both index transformations are primitive recursive and work
uniformly for every total oracle.

This gives the total-range and injective total-range characterizations of relative
Σ⁰₁ sets, under nonemptiness and infinitude respectively.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter II.1.
-/

public section

open Encodable Denumerable
open TauCeti.Enumeration TauCeti.Oracle.Single

namespace TauCeti.Oracle.Single.Code

open Primrec in
private theorem primrec_mem_domStage_unpair :
    Primrec fun q : (List ℕ × Code) × ℕ =>
      decide (q.2.unpair.1 ∈ q.1.2.domStage (fun z => q.1.1[z]?) q.2.unpair.2) := by
  have hu := Primrec.unpair.comp (snd : Primrec (Prod.snd : (List ℕ × Code) × ℕ → ℕ))
  exact (primrecRel_mem_domStage list_getElem?).decide.comp
    ((fst.comp fst).pair ((snd.comp fst).pair (snd.comp hu))) (fst.comp hu)

private theorem exists_eval_rangeCode :
    ∃ u : Code, ∀ (O : ℕ → ℕ) (c : Code) (a n : ℕ),
      eval (O : ℕ →. ℕ) u (Nat.pair (Nat.pair (encode c) a) n) =
        Part.some (if n.unpair.1 ∈ c.domStage (fun z => some (O z)) n.unpair.2
          then n.unpair.1 else a) := by
  open Primrec in
  let decodeInput := fun q : ℕ × ℕ × List ℕ =>
    ((q.2.2, ofNat Code q.1.unpair.1.unpair.1), q.1.unpair.2)
  have hin : Primrec decodeInput :=
    ((snd.comp snd).pair ((Primrec.ofNat Code).comp
      (fst.comp (Primrec.unpair.comp (fst.comp (Primrec.unpair.comp fst)))))).pair
      (snd.comp (Primrec.unpair.comp fst))
  have hu : Primrec fun q : ℕ × ℕ × List ℕ => q.1.unpair :=
    Primrec.unpair.comp fst
  have h := Primrec.cond (primrec_mem_domStage_unpair.comp hin)
    (fst.comp (Primrec.unpair.comp (snd.comp hu))) (snd.comp (Primrec.unpair.comp (fst.comp hu)))
  obtain ⟨g, hg⟩ := exists_code_answers_apply h
  obtain ⟨reindex, hreindex⟩ := exists_code_of_computable (g := fun n =>
    Nat.pair n n.unpair.2.unpair.2)
    (Primrec₂.natPair.comp Primrec.id
      (snd.comp (Primrec.unpair.comp (snd.comp Primrec.unpair)))).to_comp
  refine ⟨comp g reindex, fun O c a n => ?_⟩
  rw [eval_comp, hreindex, PFun.some_bind, hg]
  simp only [Nat.unpair_pair, decodeInput, ofNat_encode, Bool.cond_eq_ite, decide_eq_true_eq,
    domStage_range_map]

/-- Compile the total function which tests input-stage pairs for domain membership,
using the fallback as the output where the bounded test fails. -/
noncomputable def rangeCode (c : Code) (a : ℕ) : Code :=
  exists_eval_rangeCode.choose.curry (Nat.pair (encode c) a)

/-- The range-program compiler is primitive recursive in the source program and fallback. -/
theorem primrec₂_rangeCode : Primrec₂ rangeCode :=
  primrec₂_curry.comp (Primrec.const _)
    (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst) Primrec.snd)

/-- The range program evaluates the domain stage at the input-stage pair coded by its input. -/
@[simp]
theorem eval_rangeCode (O : ℕ → ℕ) (c : Code) (a n : ℕ) :
    eval (O : ℕ →. ℕ) (c.rangeCode a) n =
      Part.some (if n.unpair.1 ∈ c.domStage (fun z => some (O z)) n.unpair.2
        then n.unpair.1 else a) := by
  rw [rangeCode, eval_curry]
  exact exists_eval_rangeCode.choose_spec O c a n

/-- The range program halts on every input relative to any total oracle. -/
@[simp]
theorem dom_eval_rangeCode (O : ℕ → ℕ) (c : Code) (a : ℕ) :
    (eval (O : ℕ →. ℕ) (c.rangeCode a)).Dom = Set.univ := by
  ext x
  simp [PFun.Dom]

/-- The range consists of the source domain together with the fallback, which is returned
at every pair with stage zero. -/
@[simp]
theorem ran_eval_rangeCode (O : ℕ → ℕ) (c : Code) (a : ℕ) :
    (eval (O : ℕ →. ℕ) (c.rangeCode a)).ran = insert a (eval (O : ℕ →. ℕ) c).Dom := by
  rw [← stageLimit_domStage_total]
  ext x
  simp only [PFun.ran, Set.mem_ofPred_eq, eval_rangeCode, Part.mem_some_iff, Set.mem_insert_iff]
  constructor
  · rintro ⟨n, rfl⟩
    split_ifs with h
    · exact Or.inr (mem_stageLimit.2 ⟨n.unpair.2, h⟩)
    · exact Or.inl rfl
  · rintro (rfl | hx)
    · exact ⟨Nat.pair x 0, by simp⟩
    · obtain ⟨s, hs⟩ := mem_stageLimit.1 hx
      exact ⟨Nat.pair x s, by simp [hs]⟩

/-- Relative to a set oracle, the range is the source domain with the fallback inserted. -/
@[simp]
theorem ran_eval_rangeCode_oracle (Z : Set ℕ) (c : Code) (a : ℕ) :
    (eval Z.oracle (c.rangeCode a)).ran = insert a (eval Z.oracle c).Dom := by
  simp only [Set.oracle_eq_indicator, ran_eval_rangeCode]

private theorem serializedDomStage_range_map (O : ℕ → ℕ) (c : Code) {s k : ℕ}
    (hsk : s ≤ k + 1) :
    serializedStage (c.domStage fun z => ((List.range k).map O)[z]?) s =
      serializedStage (c.domStage fun z => some (O z)) s := by
  apply serializedStage_eq_of_eqOn
  intro t ht
  have htk := Nat.lt_succ_iff.mp ((Set.mem_Iio.1 ht).trans_le hsk)
  apply domStage_eq_of_eqOn
  intro z hz
  simp [(Set.mem_Iio.1 hz).trans_le htk]

private theorem exists_eval_entryCode :
    ∃ u : Code, ∀ (O : ℕ → ℕ) (c : Code) (n : ℕ),
      eval (O : ℕ →. ℕ) u (Nat.pair (encode c) n) =
        entryAt (serializedStage (c.domStage fun z => some (O z))) n := by
  open Primrec in
  let param := fun q : ℕ × ℕ × List ℕ => (q.2.2, ofNat Code q.1.unpair.1)
  have hparam : Primrec param :=
    (snd.comp snd).pair ((Primrec.ofNat Code).comp (fst.comp (Primrec.unpair.comp fst)))
  have hstage := primrec_serializedStage
    (A := fun p : List ℕ × Code => p.2.domStage fun z => p.1[z]?)
    (primrec_domStage_list.comp ((fst.comp fst).pair ((snd.comp fst).pair snd)))
  have hnow := hstage.comp (hparam.pair (fst.comp snd))
  have hnext := hstage.comp (hparam.pair (Primrec.succ.comp (fst.comp snd)))
  have hcard := card_equivBitIndices.comp hnow
  have hpos := snd.comp (Primrec.unpair.comp (fst : Primrec (Prod.fst : ℕ × ℕ × List ℕ → ℕ)))
  have hmin := nat_leastBitIndex.comp (nat_ldiff.comp hnext hnow)
  obtain ⟨u, hu⟩ := exists_code_rfindOpt_answers
    (Primrec.cond (Primrec.eq.decide.comp hcard hpos) hmin (Primrec.const none))
  refine ⟨u, fun O c n => ?_⟩
  rw [hu, entryAt_def]
  congr 1
  funext s
  simp only [param, Nat.unpair_pair, ofNat_encode, Bool.cond_eq_ite, decide_eq_true_eq,
    Equiv.apply_symm_apply, serializedDomStage_range_map O c (Nat.le_succ s),
    serializedDomStage_range_map O c (le_refl (s + 1))]
  congr 2
  apply Finset.equivBitIndices.injective
  simp only [Finset.equivBitIndices_ldiff, Equiv.apply_symm_apply, fresh_eq_sdiff]

/-- Compile a program that returns the entries of the serialized domain in discovery order. -/
noncomputable def entryCode (c : Code) : Code :=
  exists_eval_entryCode.choose.curry (encode c)

/-- The entry-program compiler is primitive recursive in the source program. -/
theorem primrec_entryCode : Primrec entryCode :=
  primrec₂_curry.comp (Primrec.const _) Primrec.encode

/-- The entry program runs the serialized entry search relative to every total oracle. -/
@[simp]
theorem eval_entryCode (O : ℕ → ℕ) (c : Code) (n : ℕ) :
    eval (O : ℕ →. ℕ) c.entryCode n =
      entryAt (serializedStage (c.domStage fun z => some (O z))) n := by
  rw [entryCode, eval_curry]
  exact exists_eval_entryCode.choose_spec O c n

/-- Each member of the source domain is returned at a unique discovery position. -/
theorem existsUnique_mem_eval_entryCode_iff (O : ℕ → ℕ) (c : Code) (x : ℕ) :
    (∃! n, x ∈ eval (O : ℕ →. ℕ) c.entryCode n) ↔ (eval (O : ℕ →. ℕ) c x).Dom := by
  simp only [eval_entryCode]
  rw [existsUnique_mem_entryAt_iff (monotone_serializedStage _) (serializedStage_zero _)
    (card_fresh_serializedStage_le_one _), stageLimit_serializedStage, stageLimit_domStage_total]
  rfl

/-- The range of the entry program is the entire source domain, even when it is finite. -/
@[simp]
theorem ran_eval_entryCode (O : ℕ → ℕ) (c : Code) :
    (eval (O : ℕ →. ℕ) c.entryCode).ran = (eval (O : ℕ →. ℕ) c).Dom := by
  ext x
  constructor
  · rintro ⟨n, hn⟩
    rw [eval_entryCode] at hn
    obtain ⟨s, _, hs⟩ := (mem_entryAt (monotone_serializedStage _)
      (card_fresh_serializedStage_le_one _)).1 hn
    simpa only [stageLimit_serializedStage, stageLimit_domStage_total] using
      mem_stageLimit_of_mem_fresh hs
  · intro hx
    exact ((c.existsUnique_mem_eval_entryCode_iff O x).2 hx).exists

/-- Relative to a set oracle, the entry program enumerates exactly the source domain. -/
@[simp]
theorem ran_eval_entryCode_oracle (Z : Set ℕ) (c : Code) :
    (eval Z.oracle c.entryCode).ran = (eval Z.oracle c).Dom := by
  simp only [Set.oracle_eq_indicator, ran_eval_entryCode]

/-- The entry program halts at position `n` exactly when some serialized stage has more than
`n` entries. -/
theorem dom_eval_entryCode_iff (O : ℕ → ℕ) (c : Code) (n : ℕ) :
    (eval (O : ℕ →. ℕ) c.entryCode n).Dom ↔
      ∃ s, n < (serializedStage (c.domStage fun z => some (O z)) s).card := by
  rw [eval_entryCode, entryAt_dom (monotone_serializedStage _) (serializedStage_zero _)
    (card_fresh_serializedStage_le_one _)]

/-- The entry program halts at every position precisely when the source domain is infinite. -/
theorem forall_dom_eval_entryCode_iff (O : ℕ → ℕ) (c : Code) :
    (∀ n, (eval (O : ℕ →. ℕ) c.entryCode n).Dom) ↔ (eval (O : ℕ →. ℕ) c).Dom.Infinite := by
  simp only [dom_eval_entryCode_iff]
  rw [← stageLimit_domStage_total O c, ← stageLimit_serializedStage (c.domStage _),
    stageLimit_infinite_iff (monotone_serializedStage _)]
  exact ⟨fun h n => (h n).imp fun _ hs => hs.le,
    fun h n => (h (n + 1)).imp fun _ hs => hs⟩

end TauCeti.Oracle.Single.Code

namespace TauCeti.ArithmeticalHierarchy

variable {Z : Set ℕ} {α : Type*} [Primcodable α] {S : Set α}

private theorem exists_eval_indicator_dom {A : Set ℕ} (hA : IsSigma Z 1 (· ∈ A)) :
    ∃ c : Code, (Code.eval ↑(Z.indicator 1 : ℕ → ℕ) c).Dom = A := by
  obtain ⟨c, hc⟩ := isSigma_one_iff_exists_code.1 hA
  refine ⟨c, ?_⟩
  ext x
  simpa only [PFun.Dom, Set.mem_ofPred_eq, encode_nat, Set.oracle_eq_indicator Z] using (hc x).symm

private theorem exists_computableIn_range_nat {A : Set ℕ} (hA : IsSigma Z 1 (· ∈ A))
    (hne : A.Nonempty) : ∃ f : ℕ → ℕ, ComputableIn {Z.oracle} f ∧ Set.range f = A := by
  obtain ⟨c, hdom⟩ := exists_eval_indicator_dom hA
  obtain ⟨a, ha⟩ := hne
  let O : ℕ → ℕ := Z.indicator 1
  have hO : Z.oracle = (O : ℕ →. ℕ) := Set.oracle_eq_indicator Z
  let f (n : ℕ) :=
    if n.unpair.1 ∈ c.domStage (fun z => some (O z)) n.unpair.2 then n.unpair.1 else a
  have heval (n : ℕ) : Code.eval (O : ℕ →. ℕ) (c.rangeCode a) n = Part.some (f n) :=
    Code.eval_rangeCode O c a n
  have hf : ComputableIn {Z.oracle} f := RecursiveIn.iff_nat.2
    (hO ▸ (Code.recursiveIn_eval (O : ℕ →. ℕ) (c.rangeCode a)).of_eq heval)
  have hmem : a ∈ (Code.eval (O : ℕ →. ℕ) c).Dom := hdom.symm ▸ ha
  have hr := Code.ran_eval_rangeCode O c a
  have heq : Code.eval (O : ℕ →. ℕ) (c.rangeCode a) = (f : ℕ →. ℕ) := funext heval
  rw [heq, PFun.ran_coe, Set.insert_eq_of_mem hmem, hdom] at hr
  exact ⟨f, hf, hr⟩

private theorem exists_injective_computableIn_range_nat {A : Set ℕ}
    (hA : IsSigma Z 1 (· ∈ A)) (hinf : A.Infinite) :
    ∃ f : ℕ → ℕ, ComputableIn {Z.oracle} f ∧ Set.range f = A ∧ Function.Injective f := by
  obtain ⟨c, hdom⟩ := exists_eval_indicator_dom hA
  let O : ℕ → ℕ := Z.indicator 1
  have hO : Z.oracle = (O : ℕ →. ℕ) := Set.oracle_eq_indicator Z
  let p := Code.eval (O : ℕ →. ℕ) c.entryCode
  have hp (n : ℕ) : (p n).Dom :=
    (c.forall_dom_eval_entryCode_iff O).2 (hdom.symm ▸ hinf) n
  let f (n : ℕ) := (p n).get (hp n)
  have heval (n : ℕ) : Code.eval (O : ℕ →. ℕ) c.entryCode n = Part.some (f n) :=
    (Part.some_get (hp n)).symm
  have hf : ComputableIn {Z.oracle} f := RecursiveIn.iff_nat.2
    (hO ▸ (Code.recursiveIn_eval (O : ℕ →. ℕ) c.entryCode).of_eq heval)
  have hr := c.ran_eval_entryCode O
  have heq : p = (f : ℕ →. ℕ) := funext heval
  have hrange : Set.range f = A := by
    simpa only [← hdom, ← PFun.ran_coe, ← heq] using hr
  refine ⟨f, hf, hrange, fun m n hmn => ?_⟩
  have hx : f m ∈ (Code.eval (O : ℕ →. ℕ) c).Dom := hdom.symm ▸ hrange ▸ Set.mem_range_self m
  have huniq := (c.existsUnique_mem_eval_entryCode_iff O (f m)).2 hx
  exact huniq.unique (by rw [heval m]; exact Part.mem_some _) (by rwa [heval n, Part.mem_some_iff])

/-- Every nonempty set c.e. in the oracle has a total range presentation computable in it. -/
theorem IsSigma.exists_computableIn_range (hS : IsSigma Z 1 (· ∈ S)) (hne : S.Nonempty) :
    ∃ f : ℕ → α, ComputableIn {Z.oracle} f ∧ Set.range f = S := by
  have hencoded := Computable.encode.computableIn.isSigma_one_mem_image hS
  obtain ⟨a, ha⟩ := hne
  obtain ⟨f, hf, hr⟩ := exists_computableIn_range_nat hencoded ⟨encode a, ⟨a, ha, rfl⟩⟩
  obtain ⟨g, hg, hgr, _⟩ := hf.exists_decoded_range a hr
  exact ⟨g, hg, hgr⟩

/-- Every infinite set c.e. in the oracle has an injective total enumeration computable in it. -/
theorem IsSigma.exists_injective_computableIn_range (hS : IsSigma Z 1 (· ∈ S))
    (hinf : S.Infinite) :
    ∃ f : ℕ → α, ComputableIn {Z.oracle} f ∧ Function.Injective f ∧ Set.range f = S := by
  have hencoded := Computable.encode.computableIn.isSigma_one_mem_image hS
  obtain ⟨f, hf, hr, hi⟩ :=
    exists_injective_computableIn_range_nat hencoded (hinf.image encode_injective.injOn)
  obtain ⟨a, _⟩ := hinf.nonempty
  obtain ⟨g, hg, hgr, hgi⟩ := hf.exists_decoded_range a hr
  exact ⟨g, hg, hgi hi, hgr⟩

/-- A set has a total range presentation computable in the oracle exactly when it is
nonempty and c.e. in the oracle. -/
theorem exists_computableIn_range_iff :
    (∃ f : ℕ → α, ComputableIn {Z.oracle} f ∧ Set.range f = S) ↔
      S.Nonempty ∧ IsSigma Z 1 (· ∈ S) :=
  ⟨fun ⟨f, hf, h⟩ => h ▸ ⟨⟨f 0, Set.mem_range_self 0⟩, hf.isSigma_one_mem_range⟩,
    fun ⟨hne, hS⟩ => hS.exists_computableIn_range hne⟩

/-- A set has an injective total range presentation computable in the oracle exactly when
it is infinite and c.e. in the oracle. -/
theorem exists_injective_computableIn_range_iff :
    (∃ f : ℕ → α, ComputableIn {Z.oracle} f ∧ Function.Injective f ∧ Set.range f = S) ↔
      S.Infinite ∧ IsSigma Z 1 (· ∈ S) :=
  ⟨fun ⟨_, hf, hi, h⟩ => h ▸ ⟨Set.infinite_range_of_injective hi, hf.isSigma_one_mem_range⟩,
    fun ⟨hinf, hS⟩ => hS.exists_injective_computableIn_range hinf⟩

end TauCeti.ArithmeticalHierarchy
