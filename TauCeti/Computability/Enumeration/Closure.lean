/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Recursion
public import TauCeti.Computability.Hierarchy.Closure
public import TauCeti.Computability.Hierarchy.One
import TauCeti.Data.PFun.Basic

/-!
# Closure properties and uniform index compilers for c.e. sets

This file develops both uniform index-level and semantic closure properties for c.e. and
relativized c.e. (`Σ⁰₁`) sets.

At the level of oracle programs `TauCeti.Oracle.Single.Code`, intersections (`pair`, `interList`),
partial preimages (`comp`), and domain-restricted identities (`restrictId`) are direct syntactic
combinators that hold relative to every partial oracle. Finite unions (`unionList`, `union`),
range-to-domain conversion (`rangeDom`), partial images (`imageDom`), and existential projections
(`projDom`) are built from a single uniform dovetailing search over finite oracle prefixes via
`exists_code_dom_iff_exists_answers` and `curry`. Every index compiler is primitive recursive and
oracle-independent; the dovetailing compilers require a total oracle because prefix search queries
oracle addresses below the current fuel bound.

Specializing to the constant-zero oracle via `toSingleOracleCode` and `toPartrecCode` yields the
corresponding primitive recursive index compilers on ordinary Mathlib codes `Nat.Partrec.Code`
without duplicating the search constructions.

On arbitrary primitive-codable types, the index compilers yield semantic closure of relative `Σ⁰₁`
sets and ordinary `REPred` sets under finite unions and intersections, existential quantification,
ranges, partial images, and partial preimages, together with the partial-range characterization of
c.e. sets (which requires no nonemptiness hypothesis, unlike total range presentations).

## Main definitions

* `TauCeti.Oracle.Single.Code.interList`, `Nat.Partrec.Code.interList`: finite intersection
  compiler on program lists.
* `TauCeti.Oracle.Single.Code.restrictId`, `Nat.Partrec.Code.restrictId`: partial identity
  restricted to a program's domain.
* `TauCeti.Oracle.Single.Code.unionList`, `TauCeti.Oracle.Single.Code.union`,
  `Nat.Partrec.Code.unionList`, `Nat.Partrec.Code.union`: uniform finite-union compilers.
* `TauCeti.Oracle.Single.Code.rangeDom`, `Nat.Partrec.Code.rangeDom`: uniform range-to-domain
  compiler.
* `TauCeti.Oracle.Single.Code.imageDom`, `Nat.Partrec.Code.imageDom`: uniform partial-image
  compiler.
* `TauCeti.Oracle.Single.Code.projDom`, `Nat.Partrec.Code.projDom`: uniform projection compiler.

## Main results

* Semantic closure of `IsSigma Z 1` under domains, ranges, partial images, total images, and
  partial preimages, plus `TauCeti.ArithmeticalHierarchy.isSigma_one_iff_exists_recursiveIn_ran`.
* Semantic closure of `REPred` under conjunction, disjunction, existential quantification, partial
  ranges, partial images, total images, and partial preimages, plus
  `TauCeti.Enumeration.rePred_iff_exists_partrec_ran`.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapters II.1–2 and
  III.1.
-/

public section

open Encodable Denumerable

namespace TauCeti.Oracle.Single.Code

/-! ### Direct domain combinators for partial oracles -/

/-- The domain of a paired program is the intersection of the two domains, relative to every
partial oracle. -/
@[simp]
theorem dom_eval_pair (O : ℕ →. ℕ) (cf cg : Code) :
    (eval O (pair cf cg)).Dom = (eval O cf).Dom ∩ (eval O cg).Dom := by
  ext x
  simp [PFun.Dom, Seq.seq]

/-- The domain of a composed program is the partial preimage of the outer domain under the inner
program, relative to every partial oracle. -/
@[simp]
theorem dom_eval_comp (O : ℕ →. ℕ) (cf cg : Code) :
    (eval O (comp cf cg)).Dom = (eval O cg).preimage (eval O cf).Dom := by
  ext x
  simp only [PFun.mem_dom, eval_comp, PFun.mem_preimage]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨a, ha, hya⟩ := Part.mem_bind_iff.1 hy
    exact ⟨a, ⟨y, hya⟩, ha⟩
  · rintro ⟨a, ⟨y, hya⟩, ha⟩
    exact ⟨y, Part.mem_bind ha hya⟩

/-- When the inner program computes a total function `f`, the domain of `comp cf cg` is the usual
set-theoretic preimage of the domain of `cf` under `f`. -/
theorem dom_eval_comp_total {O : ℕ →. ℕ} {cf cg : Code} {f : ℕ → ℕ}
    (hf : ∀ x, eval O cg x = Part.some (f x)) :
    (eval O (comp cf cg)).Dom = f ⁻¹' (eval O cf).Dom := by
  ext x
  simp [PFun.Dom, hf]

/-- Uniform finite-intersection compiler for a list of oracle programs. -/
def interList (cs : List Code) : Code :=
  cs.foldr pair zero

/-- The empty intersection is the everywhere-defined program `zero`. -/
@[simp]
theorem interList_nil : interList [] = zero :=
  (rfl)

/-- Consing a program intersects its domain with the rest of the list. -/
@[simp]
theorem interList_cons (c : Code) (cs : List Code) :
    interList (c :: cs) = pair c (interList cs) :=
  (rfl)

/-- Finite intersection of program lists is primitive recursive. -/
theorem primrec_interList : Primrec interList :=
  (Primrec.list_foldr (h := fun (_ : List Code) (p : Code × Code) => pair p.1 p.2)
    Primrec.id (Primrec.const zero) <|
      Primrec₂.mk (primrec₂_pair.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))).of_eq
    fun _ => rfl

/-- The domain of `interList cs` is the intersection of the domains of its entries, relative to
every partial oracle. -/
@[simp]
theorem dom_eval_interList (O : ℕ →. ℕ) (cs : List Code) :
    (eval O (interList cs)).Dom = ⋂ c ∈ cs, (eval O c).Dom := by
  induction cs with
  | nil =>
    ext x
    simp [PFun.Dom]
  | cons c cs ih =>
    simp [ih]

/-- Restrict the identity function on `ℕ` to the domain of `c`. -/
def restrictId (c : Code) : Code :=
  comp left (pair (pair left right) c)

/-- Domain restriction of the identity is primitive recursive on programs. -/
theorem primrec_restrictId : Primrec restrictId :=
  primrec₂_comp.comp (Primrec.const left)
    (primrec₂_pair.comp (Primrec.const (pair left right)) Primrec.id)

/-- `restrictId c` outputs its input `x` whenever `c` halts on `x`, and diverges otherwise,
relative to every partial oracle. -/
theorem eval_restrictId (O : ℕ →. ℕ) (c : Code) (x : ℕ) :
    eval O (restrictId c) x = (eval O c x).map fun _ => x := by
  refine Part.ext fun y => ?_
  rw [restrictId, eval_comp, Part.mem_map_iff]
  constructor
  · intro h
    obtain ⟨p, hp, hy⟩ := Part.mem_bind_iff.1 h
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_eval_pair.1 hp
    obtain ⟨l, hl, r, hr, rfl⟩ := mem_eval_pair.1 ha
    rw [eval_left, Part.mem_some_iff] at hl hy
    rw [eval_right, Part.mem_some_iff] at hr
    exact ⟨b, hb, by simp [hl, hr, hy]⟩
  · rintro ⟨b, hb, rfl⟩
    exact Part.mem_bind (a := Nat.pair x b) (mem_eval_pair.2 ⟨x, mem_eval_pair.2
      ⟨x.unpair.1, by rw [eval_left]; exact Part.mem_some _,
       x.unpair.2, by rw [eval_right]; exact Part.mem_some _, Nat.pair_unpair x⟩,
      b, hb, rfl⟩) (by rw [eval_left, Nat.unpair_pair]; exact Part.mem_some _)

/-- `restrictId c` has the same domain as `c`, relative to every partial oracle. -/
@[simp]
theorem dom_eval_restrictId (O : ℕ →. ℕ) (c : Code) :
    (eval O (restrictId c)).Dom = (eval O c).Dom := by
  ext x
  simp [PFun.Dom, eval_restrictId]

/-- The range of `restrictId c` is the domain of `c`, relative to every partial oracle. -/
@[simp]
theorem ran_eval_restrictId (O : ℕ →. ℕ) (c : Code) :
    (eval O (restrictId c)).ran = (eval O c).Dom := by
  ext y
  simp only [PFun.ran, Set.mem_ofPred_eq, eval_restrictId, Part.mem_map_iff, PFun.mem_dom]
  constructor
  · rintro ⟨x, z, hz, rfl⟩
    exact ⟨z, hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨y, z, hz, rfl⟩

/-! ### Uniform dovetailing compilers for total oracles -/

/-- Bounded predicate for finite list union: at fuel `k` against oracle prefix `l`, some program in
the coded list halts on the given input. -/
private def unionSearchPred (q : ℕ × ℕ × List ℕ) : Bool :=
  (ofNat (List Code) q.1.unpair.1).foldr
    (fun c b => (evaln (fun z => q.2.2[z]?) q.2.1 c q.1.unpair.2).isSome || b) false

private theorem primrec_unionSearchPred : Primrec unionSearchPred := by
  open Primrec in
  refine list_foldr (h := fun (q : ℕ × ℕ × List ℕ) (p : Code × Bool) =>
      (evaln (fun z => q.2.2[z]?) q.2.1 p.1 q.1.unpair.2).isSome || p.2)
    ((Primrec.ofNat (List Code)).comp (fst.comp (Primrec.unpair.comp fst))) (const false) ?_
  have heval : Primrec fun p : (ℕ × ℕ × List ℕ) × Code × Bool =>
      (evaln (fun z => p.1.2.2[z]?) p.1.2.1 p.2.1 p.1.1.unpair.2).isSome :=
    option_isSome.comp <| primrec_evaln_list.comp <|
      (snd.comp (snd.comp fst)).pair <| (fst.comp (snd.comp fst)).pair <|
        (fst.comp snd).pair (snd.comp (Primrec.unpair.comp (fst.comp fst)))
  exact Primrec₂.mk (Primrec.or.comp heval (snd.comp snd))

private theorem foldr_or_eq_true {α : Type*} (P : α → Bool) (l : List α) :
    l.foldr (fun a b => P a || b) false = true ↔ ∃ a ∈ l, P a = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

private theorem exists_unionListBody :
    ∃ u : Code, ∀ (O : ℕ → ℕ) (cs : List Code) (x : ℕ),
      (eval (O : ℕ →. ℕ) u (Nat.pair (encode cs) x)).Dom ↔
        ∃ c ∈ cs, (eval (O : ℕ →. ℕ) c x).Dom := by
  obtain ⟨u, hu⟩ := exists_code_dom_iff_exists_answers primrec_unionSearchPred
  refine ⟨u, fun O cs x => ?_⟩
  rw [hu O (Nat.pair (encode cs) x)]
  simp only [unionSearchPred, Nat.unpair_pair, ofNat_encode, foldr_or_eq_true,
    Option.isSome_iff_exists, Part.dom_iff_mem, mem_eval_iff_exists_evaln_range_map]
  exact ⟨fun ⟨k, c, hc, d, hd⟩ => ⟨c, hc, d.output, k, d, hd, rfl⟩,
    fun ⟨c, hc, _, k, d, hd, _⟩ => ⟨k, c, hc, d, hd⟩⟩

/-- Uniform finite-union compiler on lists of oracle programs. Relative to every total oracle `O`,
its domain is the union of the domains of the programs in `cs`. -/
noncomputable def unionList (cs : List Code) : Code :=
  curry exists_unionListBody.choose (encode cs)

/-- Finite union of program lists is primitive recursive. -/
theorem primrec_unionList : Primrec unionList :=
  primrec₂_curry.comp (Primrec.const _) Primrec.encode

/-- Relative to every total oracle, the domain of `unionList cs` is the union of the domains of
the programs in `cs`. -/
@[simp]
theorem dom_eval_unionList (O : ℕ → ℕ) (cs : List Code) :
    (eval (O : ℕ →. ℕ) (unionList cs)).Dom = ⋃ c ∈ cs, (eval (O : ℕ →. ℕ) c).Dom := by
  ext x
  simp only [PFun.Dom, Set.mem_ofPred_eq, unionList, eval_curry,
    exists_unionListBody.choose_spec, Set.mem_iUnion, exists_prop]

/-- Uniform binary-union compiler for oracle programs. -/
noncomputable def union (cf cg : Code) : Code :=
  unionList [cf, cg]

/-- Binary union of oracle programs is primitive recursive. -/
theorem primrec₂_union : Primrec₂ union :=
  primrec_unionList.comp
    (Primrec.list_cons.comp Primrec.fst
      (Primrec.list_cons.comp Primrec.snd (Primrec.const [])))

/-- Relative to every total oracle, the domain of `union cf cg` is the union of the two domains. -/
@[simp]
theorem dom_eval_union (O : ℕ → ℕ) (cf cg : Code) :
    (eval (O : ℕ →. ℕ) (union cf cg)).Dom =
      (eval (O : ℕ →. ℕ) cf).Dom ∪ (eval (O : ℕ →. ℕ) cg).Dom := by
  ext x
  simp [union]

/-- Bounded predicate for range-to-domain conversion: at fuel `k` against oracle prefix `l`, the
coded program halts on input `k.unpair.1` with output `y`. -/
private def rangeSearchPred (q : ℕ × ℕ × List ℕ) : Bool :=
  (evaln (fun z => q.2.2[z]?) q.2.1 (ofNat Code q.1.unpair.1) q.2.1.unpair.1).casesOn
    false fun d => decide (d.output = q.1.unpair.2)

private theorem primrec_rangeSearchPred : Primrec rangeSearchPred := by
  open Primrec in
  have hrun : Primrec fun q : ℕ × ℕ × List ℕ =>
      evaln (fun z => q.2.2[z]?) q.2.1 (ofNat Code q.1.unpair.1) q.2.1.unpair.1 :=
    primrec_evaln_list.comp <| (snd.comp snd).pair <| (fst.comp snd).pair <|
      ((Primrec.ofNat Code).comp (fst.comp (Primrec.unpair.comp fst))).pair
        (fst.comp (Primrec.unpair.comp (fst.comp snd)))
  exact option_casesOn hrun (const false) <| Primrec₂.mk <|
    Primrec.eq.decide.comp (Halt.primrec_output.comp snd)
      (snd.comp (Primrec.unpair.comp (fst.comp fst)))

private theorem exists_rangeDomBody :
    ∃ r : Code, ∀ (O : ℕ → ℕ) (f : Code) (y : ℕ),
      (eval (O : ℕ →. ℕ) r (Nat.pair (encode f) y)).Dom ↔
        y ∈ (eval (O : ℕ →. ℕ) f).ran := by
  obtain ⟨r, hr⟩ := exists_code_dom_iff_exists_answers primrec_rangeSearchPred
  refine ⟨r, fun O f y => ?_⟩
  rw [hr O (Nat.pair (encode f) y)]
  simp only [rangeSearchPred, Nat.unpair_pair, ofNat_encode, PFun.ran, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨k, hk⟩
    cases h : evaln (fun z => ((List.range k).map O)[z]?) k f k.unpair.1 with
    | none => simp only [h, Bool.false_eq_true] at hk
    | some d =>
      simp only [h, decide_eq_true_eq] at hk
      exact ⟨k.unpair.1, mem_eval_iff_exists_evaln_range_map.2 ⟨k, d, h, hk⟩⟩
  · rintro ⟨x, hx⟩
    obtain ⟨s, d, hs, hout⟩ := mem_eval_iff_exists_evaln_range_map.1 hx
    refine ⟨Nat.pair x s, ?_⟩
    have hmon : evaln (fun z => ((List.range (Nat.pair x s)).map O)[z]?) (Nat.pair x s) f x =
        some d := by
      rw [evaln_range_map] at hs ⊢
      exact evaln_mono (Nat.right_le_pair x s) hs
    simp only [Nat.unpair_pair, hmon, hout, decide_true]

/-- Uniform range-to-domain compiler: relative to every total oracle `O`, the domain of
`rangeDom f` is the range of `eval O f`. -/
noncomputable def rangeDom (f : Code) : Code :=
  curry exists_rangeDomBody.choose (encode f)

/-- Range-to-domain compilation is primitive recursive on programs. -/
theorem primrec_rangeDom : Primrec rangeDom :=
  primrec₂_curry.comp (Primrec.const _) Primrec.encode

/-- Relative to every total oracle, the domain of `rangeDom f` is the range of `f`. -/
@[simp]
theorem dom_eval_rangeDom (O : ℕ → ℕ) (f : Code) :
    (eval (O : ℕ →. ℕ) (rangeDom f)).Dom = (eval (O : ℕ →. ℕ) f).ran := by
  ext y
  simp only [PFun.Dom, Set.mem_ofPred_eq, rangeDom, eval_curry, exists_rangeDomBody.choose_spec]

/-- Uniform partial-image compiler: relative to every total oracle `O`, the domain of
`imageDom f c` is the image of `(eval O c).Dom` under `eval O f`. -/
noncomputable def imageDom (f c : Code) : Code :=
  rangeDom (comp f (restrictId c))

/-- Partial-image compilation is primitive recursive in both programs. -/
theorem primrec₂_imageDom : Primrec₂ imageDom :=
  primrec_rangeDom.comp
    (primrec₂_comp.comp Primrec.fst (primrec_restrictId.comp Primrec.snd))

/-- Relative to every total oracle, the domain of `imageDom f c` is the partial image of the
domain of `c` under `f`. -/
@[simp]
theorem dom_eval_imageDom (O : ℕ → ℕ) (f c : Code) :
    (eval (O : ℕ →. ℕ) (imageDom f c)).Dom =
      (eval (O : ℕ →. ℕ) f).image (eval (O : ℕ →. ℕ) c).Dom := by
  ext y
  rw [imageDom, dom_eval_rangeDom]
  simp only [PFun.ran, Set.mem_ofPred_eq, PFun.mem_image, PFun.mem_dom, eval_comp]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨z, hz, hy⟩ := Part.mem_bind_iff.1 hx
    rw [eval_restrictId, Part.mem_map_iff] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact ⟨x, ⟨w, hw⟩, hy⟩
  · rintro ⟨x, ⟨w, hw⟩, hy⟩
    refine ⟨x, Part.mem_bind ?_ hy⟩
    rw [eval_restrictId, Part.mem_map_iff]
    exact ⟨w, hw, rfl⟩

/-- Uniform existential-projection compiler: relative to every total oracle `O`, `x` lies in the
domain of `projDom c` iff `Nat.pair x y` lies in the domain of `c` for some `y`. -/
noncomputable def projDom (c : Code) : Code :=
  imageDom left c

/-- Existential projection on program domains is primitive recursive. -/
theorem primrec_projDom : Primrec projDom :=
  primrec₂_imageDom.comp (Primrec.const left) Primrec.id

/-- Relative to every total oracle, the domain of `projDom c` is the first-coordinate projection of
the domain of `c` under Cantor pairing. -/
@[simp]
theorem dom_eval_projDom (O : ℕ → ℕ) (c : Code) :
    (eval (O : ℕ →. ℕ) (projDom c)).Dom =
      {x | ∃ y, Nat.pair x y ∈ (eval (O : ℕ →. ℕ) c).Dom} := by
  ext x
  simp only [projDom, dom_eval_imageDom, PFun.mem_image, eval_left, Part.mem_some_iff,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.unpair.2, by simpa using hp⟩
  · rintro ⟨y, hy⟩
    exact ⟨Nat.pair x y, hy, by simp⟩

end TauCeti.Oracle.Single.Code

/-! ### Empty-oracle specializations for ordinary Mathlib codes -/

namespace Nat.Partrec.Code

/-- The domain of a paired ordinary code is the intersection of the two domains. -/
@[simp]
theorem dom_eval_pair (cf cg : Code) :
    (pair cf cg).eval.Dom = cf.eval.Dom ∩ cg.eval.Dom := by
  ext x
  simp [PFun.Dom, eval, Seq.seq]

/-- The domain of a composed ordinary code is the partial preimage of the outer domain under the
inner code. -/
@[simp]
theorem dom_eval_comp (cf cg : Code) :
    (comp cf cg).eval.Dom = cg.eval.preimage cf.eval.Dom := by
  ext x
  simp only [PFun.Dom, Set.mem_ofPred_eq, eval, PFun.mem_preimage]
  constructor
  · rintro ⟨hdom, hcf⟩
    exact ⟨(cg.eval x).get hdom, hcf, Part.get_mem hdom⟩
  · rintro ⟨a, hcf, ha⟩
    have hdom : (cg.eval x).Dom := Part.dom_iff_mem.2 ⟨a, ha⟩
    refine ⟨hdom, ?_⟩
    dsimp only
    rwa [Part.get_eq_of_mem ha hdom]

/-- When `cg` computes a total function `f`, the domain of `comp cf cg` is `f ⁻¹' cf.eval.Dom`. -/
theorem dom_eval_comp_total {cf cg : Code} {f : ℕ → ℕ}
    (hf : ∀ x, cg.eval x = Part.some (f x)) :
    (comp cf cg).eval.Dom = f ⁻¹' cf.eval.Dom := by
  ext x
  simp [PFun.Dom, eval, hf]

/-- Finite-intersection compiler for a list of ordinary codes. -/
def interList (cs : List Code) : Code :=
  cs.foldr pair zero

/-- The empty intersection of ordinary codes is `zero`. -/
@[simp]
theorem interList_nil : interList [] = zero :=
  (rfl)

/-- Consing an ordinary code intersects its domain with the rest of the list. -/
@[simp]
theorem interList_cons (c : Code) (cs : List Code) :
    interList (c :: cs) = pair c (interList cs) :=
  (rfl)

/-- Finite intersection of ordinary code lists is primitive recursive. -/
theorem primrec_interList : _root_.Primrec interList :=
  (_root_.Primrec.list_foldr (h := fun (_ : List Code) (p : Code × Code) => pair p.1 p.2)
    _root_.Primrec.id (_root_.Primrec.const zero) <|
      Primrec₂.mk (primrec₂_pair.comp (_root_.Primrec.fst.comp _root_.Primrec.snd)
        (_root_.Primrec.snd.comp _root_.Primrec.snd))).of_eq
    fun _ => rfl

/-- The domain of `interList cs` is the intersection of the domains of its entries. -/
@[simp]
theorem dom_eval_interList (cs : List Code) :
    (interList cs).eval.Dom = ⋂ c ∈ cs, c.eval.Dom := by
  induction cs with
  | nil =>
    ext x
    simp only [PFun.Dom, Set.mem_ofPred_eq, interList_nil, Set.mem_iInter, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, iff_true]
    exact trivial
  | cons c cs ih =>
    simp [ih]

/-- Restrict the identity function on `ℕ` to the domain of an ordinary code `c`. -/
def restrictId (c : Code) : Code :=
  comp left (pair (pair left right) c)

/-- Domain restriction of the identity is primitive recursive on ordinary codes. -/
theorem primrec_restrictId : _root_.Primrec restrictId :=
  primrec₂_comp.comp (_root_.Primrec.const left)
    (primrec₂_pair.comp (_root_.Primrec.const (pair left right)) _root_.Primrec.id)

/-- `restrictId c` outputs its input `x` whenever `c` halts on `x`, and diverges otherwise. -/
theorem eval_restrictId (c : Code) (x : ℕ) :
    (restrictId c).eval x = (c.eval x).map fun _ => x := by
  have hpair : (pair (pair left right) c).eval x = (c.eval x).map (Nat.pair x) := by
    simp [eval, Seq.seq]
  refine Part.ext fun y => ?_
  rw [restrictId, eval]
  dsimp only
  rw [hpair, Part.mem_map_iff]
  constructor
  · intro h
    obtain ⟨p, hp, hy⟩ := Part.mem_bind_iff.1 h
    obtain ⟨b, hb, rfl⟩ := (Part.mem_map_iff _).1 hp
    have hyx : y = x := by simpa [eval] using hy
    exact ⟨b, hb, hyx.symm⟩
  · rintro ⟨b, hb, rfl⟩
    exact Part.mem_bind ((Part.mem_map_iff _).2 ⟨b, hb, rfl⟩) (by simp [eval])

/-- `restrictId c` has the same domain as `c`. -/
@[simp]
theorem dom_eval_restrictId (c : Code) :
    (restrictId c).eval.Dom = c.eval.Dom := by
  ext x
  simp [PFun.Dom, eval_restrictId]

/-- The range of `restrictId c` is the domain of `c`. -/
@[simp]
theorem ran_eval_restrictId (c : Code) :
    (restrictId c).eval.ran = c.eval.Dom := by
  ext y
  simp only [PFun.ran, Set.mem_ofPred_eq, eval_restrictId, Part.mem_map_iff, PFun.mem_dom]
  constructor
  · rintro ⟨x, z, hz, rfl⟩
    exact ⟨z, hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨y, z, hz, rfl⟩

/-- Finite-union compiler on lists of ordinary codes, specialized from the uniform oracle-program
compiler at the constant-zero oracle. -/
noncomputable def unionList (cs : List Code) : Code :=
  (TauCeti.Oracle.Single.Code.unionList (cs.map toSingleOracleCode)).toPartrecCode

/-- Finite union of ordinary code lists is primitive recursive. -/
theorem primrec_unionList : _root_.Primrec unionList :=
  TauCeti.Oracle.Single.Code.primrec_toPartrecCode.comp <|
    TauCeti.Oracle.Single.Code.primrec_unionList.comp <|
      _root_.Primrec.list_map _root_.Primrec.id
        (primrec_toSingleOracleCode.comp _root_.Primrec.snd)

/-- The domain of `unionList cs` is the union of the domains of its entries. -/
@[simp]
theorem dom_eval_unionList (cs : List Code) :
    (unionList cs).eval.Dom = ⋃ c ∈ cs, c.eval.Dom := by
  have h0 : ∀ n, PFun.lift (fun _ : ℕ => (0 : ℕ)) n = Part.some 0 := fun _ => rfl
  rw [unionList, ← TauCeti.Oracle.Single.Code.eval_toPartrecCode h0,
    TauCeti.Oracle.Single.Code.dom_eval_unionList (fun _ => 0)]
  ext x
  simp

/-- Binary-union compiler on ordinary codes. -/
noncomputable def union (cf cg : Code) : Code :=
  unionList [cf, cg]

/-- Binary union of ordinary codes is primitive recursive. -/
theorem primrec₂_union : Primrec₂ union :=
  primrec_unionList.comp
    (_root_.Primrec.list_cons.comp _root_.Primrec.fst
      (_root_.Primrec.list_cons.comp _root_.Primrec.snd (_root_.Primrec.const [])))

/-- The domain of `union cf cg` is the union of the domains of `cf` and `cg`. -/
@[simp]
theorem dom_eval_union (cf cg : Code) :
    (union cf cg).eval.Dom = cf.eval.Dom ∪ cg.eval.Dom := by
  ext x
  simp [union]

/-- Range-to-domain compiler on ordinary codes, specialized from the uniform oracle-program
compiler at the constant-zero oracle. -/
noncomputable def rangeDom (f : Code) : Code :=
  (TauCeti.Oracle.Single.Code.rangeDom f.toSingleOracleCode).toPartrecCode

/-- Range-to-domain compilation is primitive recursive on ordinary codes. -/
theorem primrec_rangeDom : _root_.Primrec rangeDom :=
  TauCeti.Oracle.Single.Code.primrec_toPartrecCode.comp <|
    TauCeti.Oracle.Single.Code.primrec_rangeDom.comp primrec_toSingleOracleCode

/-- The domain of `rangeDom f` is the range of `f`. -/
@[simp]
theorem dom_eval_rangeDom (f : Code) :
    (rangeDom f).eval.Dom = f.eval.ran := by
  have h0 : ∀ n, PFun.lift (fun _ : ℕ => (0 : ℕ)) n = Part.some 0 := fun _ => rfl
  rw [rangeDom, ← TauCeti.Oracle.Single.Code.eval_toPartrecCode h0,
    TauCeti.Oracle.Single.Code.dom_eval_rangeDom (fun _ => 0),
    TauCeti.Oracle.Single.Code.eval_toSingleOracleCode]

/-- Partial-image compiler on ordinary codes. -/
noncomputable def imageDom (f c : Code) : Code :=
  rangeDom (comp f (restrictId c))

/-- Partial-image compilation is primitive recursive on ordinary codes. -/
theorem primrec₂_imageDom : Primrec₂ imageDom :=
  primrec_rangeDom.comp
    (primrec₂_comp.comp _root_.Primrec.fst (primrec_restrictId.comp _root_.Primrec.snd))

/-- The domain of `imageDom f c` is the partial image of `c.eval.Dom` under `f`. -/
@[simp]
theorem dom_eval_imageDom (f c : Code) :
    (imageDom f c).eval.Dom = f.eval.image c.eval.Dom := by
  ext y
  rw [imageDom, dom_eval_rangeDom]
  simp only [PFun.ran, Set.mem_ofPred_eq, PFun.mem_image, PFun.mem_dom, eval]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨z, hz, hy⟩ := Part.mem_bind_iff.1 hx
    rw [eval_restrictId, Part.mem_map_iff] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact ⟨x, ⟨w, hw⟩, hy⟩
  · rintro ⟨x, ⟨w, hw⟩, hy⟩
    refine ⟨x, Part.mem_bind ?_ hy⟩
    rw [eval_restrictId, Part.mem_map_iff]
    exact ⟨w, hw, rfl⟩

/-- Existential-projection compiler on ordinary codes. -/
noncomputable def projDom (c : Code) : Code :=
  imageDom left c

/-- Existential projection on ordinary codes is primitive recursive. -/
theorem primrec_projDom : _root_.Primrec projDom :=
  primrec₂_imageDom.comp (_root_.Primrec.const left) _root_.Primrec.id

/-- The domain of `projDom c` is the first-coordinate projection of `c.eval.Dom` under Cantor
pairing. -/
@[simp]
theorem dom_eval_projDom (c : Code) :
    (projDom c).eval.Dom = {x | ∃ y, Nat.pair x y ∈ c.eval.Dom} := by
  ext x
  simp only [projDom, dom_eval_imageDom, PFun.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, hp, hxp⟩
    have hx : x = p.unpair.1 := by simpa [eval] using hxp
    exact ⟨p.unpair.2, by simpa [hx] using hp⟩
  · rintro ⟨y, hy⟩
    exact ⟨Nat.pair x y, hy, by simp [eval]⟩

end Nat.Partrec.Code

/-! ### Semantic closure for relative Σ⁰₁ sets -/

section RelativeSemantic

open TauCeti.ArithmeticalHierarchy TauCeti.Oracle.Single

variable {Z : Set ℕ} {α β : Type*} [Primcodable α] [Primcodable β]

namespace RecursiveIn

/-- The domain of a partial function recursive in `Z` is Σ⁰₁ relative to `Z`. -/
theorem isSigma_one_mem_dom {f : α →. β} (hf : RecursiveIn {Z.oracle} f) :
    IsSigma Z 1 (· ∈ f.Dom) := by
  unfold RecursiveIn at hf
  obtain ⟨c, hc⟩ := Code.exists_code.1 hf
  exact ((isSigma_one_dom_eval c).preimage Primrec.encode.computableIn).of_eq fun x => by
    simp [PFun.Dom, hc, encodek]

/-- The range of a partial function recursive in `Z` is Σ⁰₁ relative to `Z`. -/
theorem isSigma_one_mem_ran {f : α →. β} (hf : RecursiveIn {Z.oracle} f) :
    IsSigma Z 1 (· ∈ f.ran) := by
  unfold RecursiveIn at hf
  obtain ⟨c, hc⟩ := Code.exists_code.1 hf
  have hor : Z.oracle = ((Z.indicator 1 : ℕ → ℕ) : ℕ →. ℕ) := funext Z.oracle_apply
  refine ((isSigma_one_dom_eval (Z := Z) (Code.rangeDom c)).preimage
    Primrec.encode.computableIn).of_eq fun y => ?_
  change encode y ∈ (Code.eval Z.oracle (Code.rangeDom c)).Dom ↔ y ∈ f.ran
  rw [hor, Code.dom_eval_rangeDom, ← hor, hc]
  simp only [PFun.ran, Set.mem_ofPred_eq, Part.mem_bind_iff, Part.mem_map_iff]
  constructor
  · rintro ⟨n, x, _, y', hy', heq⟩
    exact ⟨x, encode_injective heq ▸ hy'⟩
  · rintro ⟨x, hx⟩
    exact ⟨encode x, x, by simp [encodek], y, hx, rfl⟩

/-- The image of a relative Σ⁰₁ set under a partial function recursive in `Z` is Σ⁰₁ relative to
`Z`. -/
theorem isSigma_one_mem_image {f : α →. β} {S : Set α} (hf : RecursiveIn {Z.oracle} f)
    (hS : IsSigma Z 1 (· ∈ S)) : IsSigma Z 1 (· ∈ f.image S) := by
  unfold RecursiveIn at hf
  obtain ⟨cf, hcf⟩ := Code.exists_code.1 hf
  obtain ⟨g, hg, hSdom⟩ := hS.exists_recursiveIn_domain
  unfold RecursiveIn at hg
  obtain ⟨cg, hcg⟩ := Code.exists_code.1 hg
  have hor : Z.oracle = ((Z.indicator 1 : ℕ → ℕ) : ℕ →. ℕ) := funext Z.oracle_apply
  refine ((isSigma_one_dom_eval (Z := Z) (Code.imageDom cf cg)).preimage
    Primrec.encode.computableIn).of_eq fun y => ?_
  change encode y ∈ (Code.eval Z.oracle (Code.imageDom cf cg)).Dom ↔ y ∈ f.image S
  rw [hor, Code.dom_eval_imageDom, ← hor, PFun.mem_image, PFun.mem_image, hcf, hcg]
  constructor
  · rintro ⟨n, hnS, hnf⟩
    obtain ⟨x, hx, hy⟩ := Part.mem_bind_iff.1 hnf
    obtain ⟨y', hy', heq⟩ := (Part.mem_map_iff encode).1 hy
    have hdx : decode (α := α) n = some x := Part.mem_ofOption.1 hx
    have hxg : (g x).Dom := by simpa [PFun.Dom, hdx] using hnS
    exact ⟨x, (hSdom x).2 hxg, encode_injective heq ▸ hy'⟩
  · rintro ⟨x, hxS, hxf⟩
    refine ⟨encode x, ?_, ?_⟩
    · simpa [PFun.Dom, encodek] using (hSdom x).1 hxS
    · exact Part.mem_bind (by simp [encodek]) ((Part.mem_map_iff encode).2 ⟨y, hxf, rfl⟩)

/-- The preimage of a relative Σ⁰₁ set under a partial function recursive in `Z` is Σ⁰₁ relative
to `Z`. -/
theorem isSigma_one_mem_preimage {f : α →. β} {S : Set β} (hf : RecursiveIn {Z.oracle} f)
    (hS : IsSigma Z 1 (· ∈ S)) : IsSigma Z 1 (· ∈ f.preimage S) := by
  unfold RecursiveIn at hf
  obtain ⟨cf, hcf⟩ := Code.exists_code.1 hf
  obtain ⟨cS, hcS⟩ := isSigma_one_iff_exists_code.1 hS
  refine ((isSigma_one_dom_eval (Z := Z) (Code.comp cS cf)).preimage
    Primrec.encode.computableIn).of_eq fun x => ?_
  change encode x ∈ (Code.eval Z.oracle (Code.comp cS cf)).Dom ↔ x ∈ f.preimage S
  rw [Code.dom_eval_comp, PFun.mem_preimage, PFun.mem_preimage, hcf]
  simp only [encodek, Part.coe_some, Part.bind_some, Part.mem_map_iff, PFun.Dom, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, hm, y, hy, rfl⟩
    exact ⟨y, (hcS y).2 hm, hy⟩
  · rintro ⟨y, hyS, hyf⟩
    exact ⟨encode y, (hcS y).1 hyS, y, hyf, rfl⟩

end RecursiveIn

namespace ComputableIn

/-- The range of a total function computable in `Z` is Σ⁰₁ relative to `Z`. -/
theorem isSigma_one_mem_range {f : α → β} (hf : ComputableIn {Z.oracle} f) :
    IsSigma Z 1 (· ∈ Set.range f) :=
  (RecursiveIn.isSigma_one_mem_ran hf).of_eq fun y => by
    simp [PFun.ran, eq_comm]

/-- The image of a relative Σ⁰₁ set under a total function computable in `Z` is Σ⁰₁ relative to
`Z`. -/
theorem isSigma_one_mem_image {f : α → β} {S : Set α} (hf : ComputableIn {Z.oracle} f)
    (hS : IsSigma Z 1 (· ∈ S)) : IsSigma Z 1 (· ∈ f '' S) :=
  (RecursiveIn.isSigma_one_mem_image hf hS).of_eq fun y => by
    change (y ∈ PFun.image (PFun.lift f) S) ↔ y ∈ f '' S
    simp [PFun.mem_image, Set.mem_image, eq_comm]

end ComputableIn

namespace TauCeti.ArithmeticalHierarchy

/-- A set in any primitive-codable type is Σ⁰₁ relative to `Z` if and only if it is the range of a
partial function `ℕ →. α` recursive in `Z`. Unlike total range presentations, this holds for the
empty set as well. -/
theorem isSigma_one_iff_exists_recursiveIn_ran {S : Set α} :
    IsSigma Z 1 (· ∈ S) ↔ ∃ f : ℕ →. α, RecursiveIn {Z.oracle} f ∧ f.ran = S := by
  refine ⟨fun hS => ?_, fun ⟨f, hf, hran⟩ => hran ▸ hf.isSigma_one_mem_ran⟩
  obtain ⟨c, hc⟩ := isSigma_one_iff_exists_code.1 hS
  let f : ℕ →. α := fun n =>
    (Part.ofOption (decode (α := α) n)).bind fun x =>
      (Code.eval Z.oracle c (encode x)).map fun _ => x
  have hdec : Nat.RecursiveIn {Z.oracle} fun n =>
      Part.ofOption ((decode (α := α) n).map encode) :=
    (Partrec.nat_iff.1 (Computable.ofOption
      (Computable.decode.option_map (Computable.encode.comp Computable.snd).to₂))).recursiveIn
  have hf : RecursiveIn {Z.oracle} f := by
    unfold RecursiveIn
    refine ((Code.recursiveIn_eval Z.oracle (Code.restrictId c)).comp hdec).of_eq fun n => ?_
    refine Part.ext fun m => ?_
    simp only [f, decode_nat, Part.coe_some, Part.bind_some]
    cases hd : decode (α := α) n with
    | none =>
      simp only [Option.map_none, Part.coe_none, Part.bind_none, Part.map_none]
      exact ⟨fun h => let ⟨_, ha, _⟩ := Part.mem_bind_iff.1 h; (Part.notMem_none _ ha).elim,
        fun h => (Part.notMem_none _ h).elim⟩
    | some x =>
      simp only [Option.map_some, Part.coe_some, Part.bind_some]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · obtain ⟨a, ha, hm⟩ := Part.mem_bind_iff.1 h
        rw [Part.mem_some_iff] at ha; subst ha
        obtain ⟨w, hw, rfl⟩ :=
          (Part.mem_map_iff _).1 (Code.eval_restrictId Z.oracle c (encode x) ▸ hm)
        exact (Part.mem_map_iff encode).2 ⟨x, (Part.mem_map_iff _).2 ⟨w, hw, rfl⟩, rfl⟩
      · obtain ⟨x', hx', rfl⟩ := (Part.mem_map_iff encode).1 h
        obtain ⟨w, hw, rfl⟩ := (Part.mem_map_iff _).1 hx'
        exact Part.mem_bind (Part.mem_some _)
          (Code.eval_restrictId Z.oracle c (encode x) ▸ (Part.mem_map_iff _).2 ⟨w, hw, rfl⟩)
  refine ⟨f, hf, Set.ext fun y => ?_⟩
  simp only [PFun.ran, Set.mem_ofPred_eq, f, Part.mem_bind_iff, Part.mem_ofOption,
    Part.mem_map_iff]
  constructor
  · rintro ⟨n, x, _, w, hw, rfl⟩
    exact (hc x).2 (Part.dom_iff_mem.2 ⟨w, hw⟩)
  · intro hy
    obtain ⟨w, hw⟩ := Part.dom_iff_mem.1 ((hc y).1 hy)
    exact ⟨encode y, y, encodek y, w, hw, rfl⟩

end TauCeti.ArithmeticalHierarchy

end RelativeSemantic

/-! ### Semantic closure for ordinary c.e. predicates -/

section OrdinarySemantic

open TauCeti.ArithmeticalHierarchy

variable {α β : Type*} [Primcodable α] [Primcodable β]

private theorem recursiveIn_empty_oracle_iff {f : α →. β} :
    RecursiveIn {(∅ : Set ℕ).oracle} f ↔ Partrec f := by
  refine ⟨fun hf => hf.partrec_of_oracle fun g hg => ?_, Partrec.recursiveIn⟩
  rw [Set.mem_singleton_iff.1 hg, Set.oracle_empty]
  exact Partrec.const' _

namespace REPred

/-- C.e. predicates are closed under conjunction. -/
protected theorem and {p q : α → Prop} (hp : REPred p) (hq : REPred q) :
    REPred fun x => p x ∧ q x :=
  isSigma_one_empty_iff_rePred.1
    ((isSigma_one_empty_iff_rePred.2 hp).and (isSigma_one_empty_iff_rePred.2 hq))

/-- C.e. predicates are closed under disjunction. -/
protected theorem or {p q : α → Prop} (hp : REPred p) (hq : REPred q) :
    REPred fun x => p x ∨ q x :=
  isSigma_one_empty_iff_rePred.1
    ((isSigma_one_empty_iff_rePred.2 hp).or (isSigma_one_empty_iff_rePred.2 hq))

/-- C.e. predicates are closed under existential quantification over any primitive-codable type. -/
protected theorem «exists» {r : α × β → Prop} (hr : REPred r) :
    REPred fun x => ∃ y : β, r (x, y) :=
  isSigma_one_empty_iff_rePred.1 (isSigma_one_empty_iff_rePred.2 hr).exists

end REPred

namespace Partrec

/-- The range of a partial computable function is c.e. -/
theorem rePred_mem_ran {f : α →. β} (hf : Partrec f) : REPred (· ∈ f.ran) :=
  isSigma_one_empty_iff_rePred.1 (RecursiveIn.isSigma_one_mem_ran hf.recursiveIn)

/-- The image of a c.e. set under a partial computable function is c.e. -/
theorem rePred_mem_image {f : α →. β} {S : Set α} (hf : Partrec f) (hS : REPred (· ∈ S)) :
    REPred (· ∈ f.image S) :=
  isSigma_one_empty_iff_rePred.1
    (RecursiveIn.isSigma_one_mem_image hf.recursiveIn (isSigma_one_empty_iff_rePred.2 hS))

/-- The preimage of a c.e. set under a partial computable function is c.e. -/
theorem rePred_mem_preimage {f : α →. β} {S : Set β} (hf : Partrec f) (hS : REPred (· ∈ S)) :
    REPred (· ∈ f.preimage S) :=
  isSigma_one_empty_iff_rePred.1
    (RecursiveIn.isSigma_one_mem_preimage hf.recursiveIn (isSigma_one_empty_iff_rePred.2 hS))

end Partrec

namespace Computable

/-- The image of a c.e. set under a total computable function is c.e. -/
theorem rePred_mem_image {f : α → β} {S : Set α} (hf : Computable f) (hS : REPred (· ∈ S)) :
    REPred (· ∈ f '' S) :=
  isSigma_one_empty_iff_rePred.1
    (ComputableIn.isSigma_one_mem_image hf.computableIn (isSigma_one_empty_iff_rePred.2 hS))

end Computable

namespace TauCeti.Enumeration

/-- A set in any primitive-codable type is c.e. if and only if it is the range of a partial
computable function `ℕ →. α`. Unlike `REPred.exists_computable_range`, this holds for the empty
set as well. -/
theorem rePred_iff_exists_partrec_ran {S : Set α} :
    REPred (· ∈ S) ↔ ∃ f : ℕ →. α, Partrec f ∧ f.ran = S := by
  rw [← isSigma_one_empty_iff_rePred, isSigma_one_iff_exists_recursiveIn_ran]
  exact exists_congr fun _ => and_congr_left fun _ => recursiveIn_empty_oracle_iff

end TauCeti.Enumeration

end OrdinarySemantic
