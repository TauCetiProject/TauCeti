/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Recursion
import TauCeti.Data.PFun.Basic

/-!
# Uniform index compilers for oracle and ordinary programs

This file provides primitive-recursive domain combinators on oracle programs
`TauCeti.Oracle.Single.Code` and transports them to ordinary Mathlib codes `Nat.Partrec.Code`
via `toSingleOracleCode` and `toPartrecCode`.

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
without duplicating the search or semantic proofs.

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

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapters II.1–2 and
  III.1.
-/

public section

open Encodable Denumerable

namespace TauCeti.Oracle.Single.Code

/-! ### Direct domain combinators for partial oracles -/

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
  have hrestrict : eval O (restrictId c) = fun x => (eval O c x).map fun _ => x :=
    funext (eval_restrictId O c)
  rw [hrestrict, PFun.ran_map_const]

/-! ### Uniform dovetailing compilers for total oracles -/

/-- Bounded predicate for finite list union: at fuel `k` against oracle prefix `l`, some program in
the coded list halts on the given input. -/
private def unionSearchPred (q : ℕ × ℕ × List ℕ) : Bool :=
  (ofNat (List Code) q.1.unpair.1).any fun c =>
    (evaln (fun z => q.2.2[z]?) q.2.1 c q.1.unpair.2).isSome

private theorem primrec_unionSearchPred : Primrec unionSearchPred := by
  open Primrec in
  refine list_any
    ((Primrec.ofNat (List Code)).comp (fst.comp (Primrec.unpair.comp fst))) <|
      Primrec₂.mk ?_
  exact option_isSome.comp <| primrec_evaln_list.comp <|
    (snd.comp (snd.comp fst)).pair <| (fst.comp (snd.comp fst)).pair <|
      snd.pair (snd.comp (Primrec.unpair.comp (fst.comp fst)))

private theorem exists_unionListBody :
    ∃ u : Code, ∀ (O : ℕ → ℕ) (cs : List Code) (x : ℕ),
      (eval (O : ℕ →. ℕ) u (Nat.pair (encode cs) x)).Dom ↔
        ∃ c ∈ cs, (eval (O : ℕ →. ℕ) c x).Dom := by
  obtain ⟨u, hu⟩ := exists_code_dom_iff_exists_answers primrec_unionSearchPred
  refine ⟨u, fun O cs x => ?_⟩
  rw [hu O (Nat.pair (encode cs) x)]
  simp only [unionSearchPred, Nat.unpair_pair, ofNat_encode, List.any_eq_true,
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
  have hrestrict : eval (O : ℕ →. ℕ) (restrictId c) =
      fun x => (eval (O : ℕ →. ℕ) c x).map fun _ => x :=
    funext (eval_restrictId (O : ℕ →. ℕ) c)
  rw [imageDom, dom_eval_rangeDom, eval_comp_eq, hrestrict, PFun.ran_comp_map_const]

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

@[local simp]
private theorem eval_toPartrecCode_zero (c : TauCeti.Oracle.Single.Code) :
    c.toPartrecCode.eval =
      TauCeti.Oracle.Single.Code.eval (((fun _ : ℕ => 0) : ℕ → ℕ) : ℕ →. ℕ) c :=
  (TauCeti.Oracle.Single.Code.eval_toPartrecCode (fun _ => rfl) c).symm

/-- Finite-intersection compiler for a list of ordinary codes, specialized from the uniform
oracle-program compiler at the constant-zero oracle. -/
def interList (cs : List Code) : Code :=
  (TauCeti.Oracle.Single.Code.interList (cs.map toSingleOracleCode)).toPartrecCode

/-- The empty intersection of ordinary codes is `zero`. -/
@[simp]
theorem interList_nil : interList [] = zero := by
  simp [interList]

/-- Consing an ordinary code intersects its domain with the rest of the list. -/
@[simp]
theorem interList_cons (c : Code) (cs : List Code) :
    interList (c :: cs) = pair c (interList cs) := by
  simp [interList]

/-- Finite intersection of ordinary code lists is primitive recursive. -/
theorem primrec_interList : _root_.Primrec interList :=
  TauCeti.Oracle.Single.Code.primrec_toPartrecCode.comp <|
    TauCeti.Oracle.Single.Code.primrec_interList.comp <|
      _root_.Primrec.list_map _root_.Primrec.id
        (_root_.Primrec₂.mk (primrec_toSingleOracleCode.comp _root_.Primrec.snd))

/-- The domain of `interList cs` is the intersection of the domains of its entries. -/
@[simp]
theorem dom_eval_interList (cs : List Code) :
    (interList cs).eval.Dom = ⋂ c ∈ cs, c.eval.Dom := by
  ext x
  simp [interList]

/-- Restrict the identity function on `ℕ` to the domain of an ordinary code `c`, specialized from
the uniform oracle-program compiler at the constant-zero oracle. -/
def restrictId (c : Code) : Code :=
  (TauCeti.Oracle.Single.Code.restrictId c.toSingleOracleCode).toPartrecCode

/-- Domain restriction of the identity is primitive recursive on ordinary codes. -/
theorem primrec_restrictId : _root_.Primrec restrictId :=
  TauCeti.Oracle.Single.Code.primrec_toPartrecCode.comp <|
    TauCeti.Oracle.Single.Code.primrec_restrictId.comp primrec_toSingleOracleCode

/-- `restrictId c` outputs its input `x` whenever `c` halts on `x`, and diverges otherwise. -/
theorem eval_restrictId (c : Code) (x : ℕ) :
    (restrictId c).eval x = (c.eval x).map fun _ => x := by
  simp [restrictId, TauCeti.Oracle.Single.Code.eval_restrictId]

/-- `restrictId c` has the same domain as `c`. -/
@[simp]
theorem dom_eval_restrictId (c : Code) :
    (restrictId c).eval.Dom = c.eval.Dom := by
  simp [restrictId]

/-- The range of `restrictId c` is the domain of `c`. -/
@[simp]
theorem ran_eval_restrictId (c : Code) :
    (restrictId c).eval.ran = c.eval.Dom := by
  simp [restrictId]

/-- Finite-union compiler on lists of ordinary codes, specialized from the uniform oracle-program
compiler at the constant-zero oracle. -/
noncomputable def unionList (cs : List Code) : Code :=
  (TauCeti.Oracle.Single.Code.unionList (cs.map toSingleOracleCode)).toPartrecCode

/-- Finite union of ordinary code lists is primitive recursive. -/
theorem primrec_unionList : _root_.Primrec unionList :=
  TauCeti.Oracle.Single.Code.primrec_toPartrecCode.comp <|
    TauCeti.Oracle.Single.Code.primrec_unionList.comp <|
      _root_.Primrec.list_map _root_.Primrec.id
        (_root_.Primrec₂.mk (primrec_toSingleOracleCode.comp _root_.Primrec.snd))

/-- The domain of `unionList cs` is the union of the domains of its entries. -/
@[simp]
theorem dom_eval_unionList (cs : List Code) :
    (unionList cs).eval.Dom = ⋃ c ∈ cs, c.eval.Dom := by
  ext x
  simp [unionList]

/-- Binary-union compiler on ordinary codes, specialized from the uniform oracle-program compiler
at the constant-zero oracle. -/
noncomputable def union (cf cg : Code) : Code :=
  (TauCeti.Oracle.Single.Code.union cf.toSingleOracleCode cg.toSingleOracleCode).toPartrecCode

/-- Binary union of ordinary codes is primitive recursive. -/
theorem primrec₂_union : Primrec₂ union :=
  TauCeti.Oracle.Single.Code.primrec_toPartrecCode.comp <|
    TauCeti.Oracle.Single.Code.primrec₂_union.comp
      (primrec_toSingleOracleCode.comp _root_.Primrec.fst)
      (primrec_toSingleOracleCode.comp _root_.Primrec.snd)

/-- The domain of `union cf cg` is the union of the domains of `cf` and `cg`. -/
@[simp]
theorem dom_eval_union (cf cg : Code) :
    (union cf cg).eval.Dom = cf.eval.Dom ∪ cg.eval.Dom := by
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
  simp [rangeDom]

/-- Partial-image compiler on ordinary codes, specialized from the uniform oracle-program
compiler at the constant-zero oracle. -/
noncomputable def imageDom (f c : Code) : Code :=
  (TauCeti.Oracle.Single.Code.imageDom f.toSingleOracleCode c.toSingleOracleCode).toPartrecCode

/-- Partial-image compilation is primitive recursive on ordinary codes. -/
theorem primrec₂_imageDom : Primrec₂ imageDom :=
  TauCeti.Oracle.Single.Code.primrec_toPartrecCode.comp <|
    TauCeti.Oracle.Single.Code.primrec₂_imageDom.comp
      (primrec_toSingleOracleCode.comp _root_.Primrec.fst)
      (primrec_toSingleOracleCode.comp _root_.Primrec.snd)

/-- The domain of `imageDom f c` is the partial image of `c.eval.Dom` under `f`. -/
@[simp]
theorem dom_eval_imageDom (f c : Code) :
    (imageDom f c).eval.Dom = f.eval.image c.eval.Dom := by
  simp [imageDom]

/-- Existential-projection compiler on ordinary codes, specialized from the uniform oracle-program
compiler at the constant-zero oracle. -/
noncomputable def projDom (c : Code) : Code :=
  (TauCeti.Oracle.Single.Code.projDom c.toSingleOracleCode).toPartrecCode

/-- Existential projection on ordinary codes is primitive recursive. -/
theorem primrec_projDom : _root_.Primrec projDom :=
  TauCeti.Oracle.Single.Code.primrec_toPartrecCode.comp <|
    TauCeti.Oracle.Single.Code.primrec_projDom.comp primrec_toSingleOracleCode

/-- The domain of `projDom c` is the first-coordinate projection of `c.eval.Dom` under Cantor
pairing. -/
@[simp]
theorem dom_eval_projDom (c : Code) :
    (projDom c).eval.Dom = {x | ∃ y, Nat.pair x y ∈ c.eval.Dom} := by
  simp [projDom]

end Nat.Partrec.Code
