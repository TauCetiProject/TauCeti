/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.BitString
public import TauCeti.Computability.Jump.Decide
import TauCeti.Computability.RecursiveIn

/-!
# The Kleene–Post theorem

Kleene and Post proved that there exist Turing incomparable sets strictly between the computable
degree `0` and its jump `0'`. Unlike the c.e. Friedberg–Muchnik construction, which must enumerate
into finite stages and repair injuries when oracle computations change, the Kleene–Post construction
uses `(∅ : Set ℕ).jump` directly as an oracle to settle one diagonal requirement per stage without
injury.

At stage `s`, the state is a pair `(α_s, β_s) : List Bool × List Bool` of finite binary initial
segments of two sets `A, B ⊆ ℕ`. Even stage `s = 2 * e` satisfies `A ≠ Φ_e^B` at the fresh witness
coordinate `x = α_s.length`:

1. Using the jump `(∅ : Set ℕ).jump`, decide the c.e. search `Code.findConvergentExt (ofNat Code e)
   x β_s` for a finite binary suffix `δ` on which bounded evaluation halts.
2. Under the extension-or-permanent-divergence alternative
   (`Code.exists_prefix_mem_eval_or_forall_eval_eq_none`), if a halting suffix `(δ, d)` is found,
   extend `α_s` by `[decide (d.output = 0)]` and `β_s` by `δ ++ [false]`; then every set `Y`
   extending `β_{s+1}` satisfies `d.output ∈ Φ_e^Y(x)` while every set `X` extending `α_{s+1}`
   disagrees with `d.output` at `x`. If no halting suffix exists, `Φ_e^Y(x)` diverges (`Part.none`)
   on every set `Y` extending `β_s`, and extending both strings by `[false]` preserves that
   permanent divergence while advancing both lengths.

Odd stage `s = 2 * e + 1` applies the symmetric step to satisfy `B ≠ Φ_e^A`. Because both stage
strings strictly lengthen at every step, every coordinate is covered, the partial stage-union
oracles `bitChainOracle stageA` and `bitChainOracle stageB` have total domain `Set.univ` and
coincide with `kleenePostSetA.oracle` and `kleenePostSetB.oracle`, and `(∅ : Set ℕ).jump` computes
both limit sets. Unlike the Friedberg–Muchnik theorem, this oracle-assisted construction only
establishes Turing reducibility to `(∅ : Set ℕ).jump` rather than c.e. membership.

The final section characterizes both satisfaction regimes (convergent disagreement and permanent
divergence) on `kleenePostSetA` and `kleenePostSetB`.

## Main definitions

* `TauCeti.KleenePost.diagStep`: one diagonal forcing step extending `(α, β)` against a program `c`
  at witness `α.length`.
* `TauCeti.KleenePost.stageStep`, `TauCeti.KleenePost.stage`, `TauCeti.KleenePost.stageA`,
  `TauCeti.KleenePost.stageB`: the `∅'`-computable sequence of finite binary initial segments.
* `TauCeti.kleenePostSetA`, `TauCeti.kleenePostSetB`: the two limit sets below `(∅ : Set ℕ).jump`.

## Main results

* `TauCeti.KleenePost.computableIn_jump_diagStep`, `TauCeti.KleenePost.computableIn_jump_stage`:
  every jump `Z.jump` computes the diagonal step and stage sequence.
* `TauCeti.KleenePost.exists_mem_eval_and_oracle_ne_of_hasConvergentExt`,
  `TauCeti.KleenePost.eval_eq_none_and_notMem_of_not_hasConvergentExt`,
  `TauCeti.KleenePost.eval_ne_oracle_of_extendsBits_diagStep`: diagonal forcing in the convergent
  and permanently divergent regimes, and the combined disagreement theorem.
* `TauCeti.dom_bitChainOracle_stageA_eq_univ`, `TauCeti.dom_bitChainOracle_stageB_eq_univ`,
  `TauCeti.bitChainOracle_stageA_eq_oracle`, `TauCeti.bitChainOracle_stageB_eq_oracle`: totality
  and coherence of the partial stage-union oracles.
* `TauCeti.turingReducible_kleenePostSetA_jump_empty`,
  `TauCeti.turingReducible_kleenePostSetB_jump_empty`,
  `TauCeti.not_turingReducible_kleenePostSetA_kleenePostSetB`,
  `TauCeti.not_turingReducible_kleenePostSetB_kleenePostSetA`: both sets reduce to
  `(∅ : Set ℕ).jump` and are Turing incomparable.
* `TauCeti.kleene_post`, `TauCeti.exists_incomparable_turingDegrees_mem_Ioo`: the Kleene–Post
  theorem in set and Turing-degree forms.

## References

* S. C. Kleene and E. L. Post, *The upper semi-lattice of degrees of recursive unsolvability*,
  Ann. of Math. (2) **59** (1954), 379–407.
* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Theorem VI.1.2,
  pp. 95–97.
-/

public section

open Denumerable Encodable Primrec TauCeti.Oracle.Single

namespace TauCeti

namespace KleenePost

/-! ### One diagonal forcing step -/

open Classical in
/-- **One diagonal forcing step** against program `c` at witness coordinate `α.length`:
* if `Code.findConvergentExt c α.length β` finds `(δ, d)` making `c` halt at `α.length` over
  `β ++ δ`, extend `α` by `[decide (d.output = 0)]` (forcing `X.oracle α.length ≠ d.output`) and
  extend `β` by `δ ++ [false]` (preserving the convergent run while lengthening `β`);
* if no convergent extension exists, extend both `α` and `β` by `[false]`. -/
noncomputable def diagStep (c : Code) (α β : List Bool) : List Bool × List Bool :=
  match (Code.findConvergentExt c α.length β).toOption with
  | some (δ, d) => (α ++ [decide (d.output = 0)], β ++ δ ++ [false])
  | none => (α ++ [false], β ++ [false])

/-- In the convergent regime, `diagStep` sets the bit at `α.length` to `decide (d.output = 0)`
(forcing `X.oracle α.length` to disagree with `d.output`) and commits `δ` followed by `false` on
the monitored side. -/
theorem diagStep_of_mem_findConvergentExt {c : Code} {α β δ : List Bool} {d : Code.Halt}
    (h : (δ, d) ∈ Code.findConvergentExt c α.length β) :
    diagStep c α β = (α ++ [decide (d.output = 0)], β ++ δ ++ [false]) := by
  classical
  have hopt : (Code.findConvergentExt c α.length β).toOption = some (δ, d) :=
    Part.toOption_eq_some_iff.2 h
  simp [diagStep, hopt]

/-- In the permanently divergent regime, `diagStep` extends both strings by `[false]`. -/
theorem diagStep_of_not_hasConvergentExt {c : Code} {α β : List Bool}
    (h : ¬Code.HasConvergentExt c α.length β) :
    diagStep c α β = (α ++ [false], β ++ [false]) := by
  classical
  have hopt : (Code.findConvergentExt c α.length β).toOption = none :=
    Part.toOption_eq_none_iff.2 (mt Code.dom_findConvergentExt_iff.1 h)
  simp [diagStep, hopt]

/-- The first output of `diagStep c α β` extends `α` as a prefix. -/
theorem prefix_fst_diagStep (c : Code) (α β : List Bool) : α <+: (diagStep c α β).1 := by
  classical
  unfold diagStep
  split <;> exact List.prefix_append _ _

/-- `diagStep c α β` extends `α` by exactly one bit. -/
@[simp]
theorem length_fst_diagStep (c : Code) (α β : List Bool) :
    (diagStep c α β).1.length = α.length + 1 := by
  classical
  unfold diagStep
  split <;> simp

/-- `diagStep c α β` strictly increases the length of its first string. -/
theorem length_lt_fst_diagStep (c : Code) (α β : List Bool) :
    α.length < (diagStep c α β).1.length := by
  simp

/-- The second output of `diagStep c α β` extends `β` as a prefix. -/
theorem prefix_snd_diagStep (c : Code) (α β : List Bool) : β <+: (diagStep c α β).2 := by
  classical
  unfold diagStep
  split
  · rw [List.append_assoc]
    exact List.prefix_append _ _
  · exact List.prefix_append _ _

/-- `diagStep c α β` strictly increases the length of its second string. -/
theorem length_lt_snd_diagStep (c : Code) (α β : List Bool) :
    β.length < (diagStep c α β).2.length := by
  classical
  unfold diagStep
  split <;> simp

/-- **Convergent disagreement.** When `Code.HasConvergentExt c α.length β` holds, `diagStep c α β`
forces a single convergent value `y` of `Code.eval Y.oracle c α.length` for every `Y` extending the
second string while forcing `X.oracle α.length ≠ Part.some y` for every `X` extending the first. -/
theorem exists_mem_eval_and_oracle_ne_of_hasConvergentExt {c : Code} {α β : List Bool}
    (h : Code.HasConvergentExt c α.length β) :
    ∃ y : ℕ, ∀ ⦃X Y : Set ℕ⦄,
      X.ExtendsBits (diagStep c α β).1 → Y.ExtendsBits (diagStep c α β).2 →
        y ∈ Code.eval Y.oracle c α.length ∧ X.oracle α.length ≠ Part.some y := by
  obtain ⟨⟨δ, d⟩, hmem⟩ := Part.dom_iff_mem.1 (Code.dom_findConvergentExt_iff.2 h)
  have hstep := diagStep_of_mem_findConvergentExt hmem
  refine ⟨d.output, fun X Y hX hY => ?_⟩
  rw [hstep] at hX hY
  have hYδ : Y.ExtendsBits (β ++ δ) := hY.of_prefix (List.prefix_append _ _)
  have heval : d.output ∈ Code.eval Y.oracle c α.length :=
    Code.mem_eval_oracle_of_mem_findConvergentExt hmem hYδ
  have hget : (α ++ [decide (d.output = 0)])[α.length]? = some (decide (d.output = 0)) := by simp
  have horacle : X.oracle α.length = Part.some (decide (d.output = 0)).toNat :=
    hX.oracle_eq_some_toNat hget
  refine ⟨heval, ?_⟩
  rw [horacle, ne_eq, Part.some_inj]
  by_cases h0 : d.output = 0 <;> simp [h0, Ne.symm]

/-- **Permanent divergence.** When `¬Code.HasConvergentExt c α.length β`, `Code.eval Y.oracle c
α.length = Part.none` for every set `Y` extending `β`, while every set `X` extending
`(diagStep c α β).1` satisfies `α.length ∉ X` and `X.oracle α.length = Part.some 0`. -/
theorem eval_eq_none_and_notMem_of_not_hasConvergentExt {c : Code} {α β : List Bool}
    (h : ¬Code.HasConvergentExt c α.length β) {X Y : Set ℕ}
    (hX : X.ExtendsBits (diagStep c α β).1) (hY : Y.ExtendsBits β) :
    Code.eval Y.oracle c α.length = Part.none ∧ α.length ∉ X ∧
      X.oracle α.length = Part.some 0 := by
  rw [diagStep_of_not_hasConvergentExt h] at hX
  have hxnot : α.length ∉ X := by simpa using (Set.extendsBits_concat.1 hX).2
  exact ⟨Code.not_hasConvergentExt_iff.1 h Y hY, hxnot, by simp [hxnot]⟩

/-- **Diagonal forcing theorem.** For every program `c`, pair `(α, β)`, and sets `X, Y` extending
the two outputs of `diagStep c α β`, `Code.eval Y.oracle c α.length ≠ X.oracle α.length`. -/
theorem eval_ne_oracle_of_extendsBits_diagStep {c : Code} {α β : List Bool} {X Y : Set ℕ}
    (hX : X.ExtendsBits (diagStep c α β).1) (hY : Y.ExtendsBits (diagStep c α β).2) :
    Code.eval Y.oracle c α.length ≠ X.oracle α.length := by
  by_cases h : Code.HasConvergentExt c α.length β
  · obtain ⟨y, hy⟩ := exists_mem_eval_and_oracle_ne_of_hasConvergentExt h
    obtain ⟨heval, hne⟩ := hy hX hY
    rw [Part.eq_some_iff.2 heval]
    exact hne.symm
  · rw [(eval_eq_none_and_notMem_of_not_hasConvergentExt h hX
      (hY.of_prefix (prefix_snd_diagStep c α β))).1]
    simp

/-- Every jump `Z.jump` computes `diagStep` uniformly in `(c, α, β)`. -/
theorem computableIn_jump_diagStep (Z : Set ℕ) :
    ComputableIn {Z.jump.oracle}
      fun p : Code × List Bool × List Bool => diagStep p.1 p.2.1 p.2.2 := by
  classical
  have hq : Primrec fun p : Code × List Bool × List Bool => (p.1, p.2.1.length, p.2.2) :=
    fst.pair ((list_length.comp (fst.comp snd)).pair (snd.comp snd))
  have hfind : ComputableIn {Z.jump.oracle}
      fun p : Code × List Bool × List Bool =>
        (Code.findConvergentExt p.1 p.2.1.length p.2.2).toOption :=
    (Code.partrec_findConvergentExt.computableIn_jump_toOption Z).comp hq.computableIn
  have hnone : Primrec fun r : (Code × List Bool × List Bool) × Option (List Bool × Code.Halt) =>
      (r.1.2.1 ++ [false], r.1.2.2 ++ [false]) :=
    (list_concat.comp (fst.comp (snd.comp fst)) (const false)).pair
      (list_concat.comp (snd.comp (snd.comp fst)) (const false))
  have hbit : Primrec
      fun u : ((Code × List Bool × List Bool) × Option (List Bool × Code.Halt)) ×
          (List Bool × Code.Halt) =>
        decide (u.2.2.output = 0) :=
    (Primrec.beq.comp (Code.Halt.primrec_output.comp (snd.comp snd)) (const 0)).of_eq
      fun _ => Bool.eq_iff_iff.2 (beq_iff_eq.trans decide_eq_true_iff.symm)
  have hsome : Primrec₂
      fun (r : (Code × List Bool × List Bool) × Option (List Bool × Code.Halt))
          (w : List Bool × Code.Halt) =>
        (r.1.2.1 ++ [decide (w.2.output = 0)], r.1.2.2 ++ w.1 ++ [false]) :=
    ((list_concat.comp (fst.comp (snd.comp (fst.comp fst))) hbit).pair
      (list_concat.comp
        (list_append.comp (snd.comp (snd.comp (fst.comp fst))) (fst.comp snd))
        (const false))).to₂
  have hpost := option_casesOn snd hnone hsome
  refine RecursiveIn.of_eq (hpost.computableIn.comp (ComputableIn.id.pair hfind)) fun p => ?_
  congr 1
  dsimp only [id_eq]
  unfold diagStep
  rcases (Code.findConvergentExt p.1 p.2.1.length p.2.2).toOption with _ | ⟨δ, d⟩ <;> rfl

/-! ### Stage recursion, coherence, and coordinate coverage -/

/-- One stage transition of the Kleene–Post construction: even `s` runs `diagStep` on `(st.1, st.2)`
and odd `s` runs `diagStep` on `(st.2, st.1)` and swaps the output pair. -/
noncomputable def stageStep (s : ℕ) (st : List Bool × List Bool) : List Bool × List Bool :=
  bif s.bodd then
    (diagStep (ofNat Code s.div2) st.2 st.1).swap
  else
    diagStep (ofNat Code s.div2) st.1 st.2

/-- Unfolding `stageStep`. -/
theorem stageStep_def (s : ℕ) (st : List Bool × List Bool) :
    stageStep s st =
      bif s.bodd then
        (diagStep (ofNat Code s.div2) st.2 st.1).swap
      else
        diagStep (ofNat Code s.div2) st.1 st.2 :=
  (rfl)

/-- At stage `0`, `stageStep` runs `diagStep` for `ofNat Code 0` on `(st.1, st.2)`. -/
@[simp]
theorem stageStep_zero (st : List Bool × List Bool) :
    stageStep 0 st = diagStep (ofNat Code 0) st.1 st.2 :=
  (rfl)

/-- At an even stage `2 * e`, `stageStep` runs `diagStep` for `ofNat Code e` on `(st.1, st.2)`. -/
@[simp]
theorem stageStep_two_mul (e : ℕ) (st : List Bool × List Bool) :
    stageStep (2 * e) st = diagStep (ofNat Code e) st.1 st.2 := by
  simp [stageStep, Nat.bodd_mul, Nat.div2_val]

/-- At an odd stage `2 * e + 1`, `stageStep` runs `diagStep` for `ofNat Code e` on `(st.2, st.1)`
and swaps the output pair. -/
@[simp]
theorem stageStep_two_mul_add_one (e : ℕ) (st : List Bool × List Bool) :
    stageStep (2 * e + 1) st = (diagStep (ofNat Code e) st.2 st.1).swap := by
  simp [stageStep, Nat.bodd_mul, Nat.div2_val]

/-- **Stage recursion of the Kleene–Post construction.** Stage `0` begins at `([], [])`; even stage
`2 * e` diagonalizes `A` against `ofNat Code e` relative to `B`, and odd stage `2 * e + 1` swaps
the sides to diagonalize `B` against `ofNat Code e` relative to `A`. -/
noncomputable def stage : ℕ → List Bool × List Bool
  | 0 => ([], [])
  | s + 1 => stageStep s (stage s)

/-- Stage `0` consists of two empty binary strings. -/
@[simp]
theorem stage_zero : stage 0 = ([], []) :=
  (rfl)

/-- Stage `s + 1` applies `stageStep s` to `stage s`. -/
theorem stage_succ (s : ℕ) : stage (s + 1) = stageStep s (stage s) :=
  (rfl)

/-- The binary initial segment of `kleenePostSetA` at stage `s`. -/
noncomputable def stageA (s : ℕ) : List Bool :=
  (stage s).1

/-- The binary initial segment of `kleenePostSetB` at stage `s`. -/
noncomputable def stageB (s : ℕ) : List Bool :=
  (stage s).2

/-- Unfolding `stageA`. -/
theorem stageA_def (s : ℕ) : stageA s = (stage s).1 :=
  (rfl)

/-- Unfolding `stageB`. -/
theorem stageB_def (s : ℕ) : stageB s = (stage s).2 :=
  (rfl)

/-- The first component of `stage s` is `stageA s`. -/
@[simp]
theorem fst_stage (s : ℕ) : (stage s).1 = stageA s :=
  (rfl)

/-- The second component of `stage s` is `stageB s`. -/
@[simp]
theorem snd_stage (s : ℕ) : (stage s).2 = stageB s :=
  (rfl)

/-- `stage s` pairs `stageA s` and `stageB s`. -/
theorem stage_eq_pair (s : ℕ) : stage s = (stageA s, stageB s) :=
  (rfl)

/-- `stageA` starts at the empty binary string. -/
@[simp]
theorem stageA_zero : stageA 0 = [] :=
  (rfl)

/-- `stageB` starts at the empty binary string. -/
@[simp]
theorem stageB_zero : stageB 0 = [] :=
  (rfl)

/-- Even stage transition `2 * e → 2 * e + 1`: `diagStep` acts directly on `stageA (2 * e)`
against `stageB (2 * e)`. -/
theorem stage_two_mul_succ (e : ℕ) :
    stage (2 * e + 1) = diagStep (ofNat Code e) (stageA (2 * e)) (stageB (2 * e)) := by
  rw [stage_succ, stageStep_two_mul, fst_stage, snd_stage]

/-- Odd stage transition `2 * e + 1 → 2 * e + 2`: `diagStep` acts on `stageB (2 * e + 1)`
against `stageA (2 * e + 1)` and swaps the resulting pair. -/
theorem stage_two_mul_add_one_succ (e : ℕ) :
    stage (2 * e + 1 + 1) =
      (diagStep (ofNat Code e) (stageB (2 * e + 1)) (stageA (2 * e + 1))).swap := by
  rw [stage_succ, stageStep_two_mul_add_one, fst_stage, snd_stage]

/-- Even stage transition for `stageA`. -/
theorem stageA_two_mul_succ (e : ℕ) :
    stageA (2 * e + 1) = (diagStep (ofNat Code e) (stageA (2 * e)) (stageB (2 * e))).1 :=
  congrArg Prod.fst (stage_two_mul_succ e)

/-- Even stage transition for `stageB`. -/
theorem stageB_two_mul_succ (e : ℕ) :
    stageB (2 * e + 1) = (diagStep (ofNat Code e) (stageA (2 * e)) (stageB (2 * e))).2 :=
  congrArg Prod.snd (stage_two_mul_succ e)

/-- Odd stage transition for `stageA`. -/
theorem stageA_two_mul_add_one_succ (e : ℕ) :
    stageA (2 * e + 1 + 1) =
      (diagStep (ofNat Code e) (stageB (2 * e + 1)) (stageA (2 * e + 1))).2 :=
  congrArg Prod.fst (stage_two_mul_add_one_succ e)

/-- Odd stage transition for `stageB`. -/
theorem stageB_two_mul_add_one_succ (e : ℕ) :
    stageB (2 * e + 1 + 1) =
      (diagStep (ofNat Code e) (stageB (2 * e + 1)) (stageA (2 * e + 1))).1 :=
  congrArg Prod.snd (stage_two_mul_add_one_succ e)

/-- Every jump `Z.jump` computes `stageStep` uniformly in `(s, st)`. -/
theorem computableIn_jump_stageStep (Z : Set ℕ) :
    ComputableIn {Z.jump.oracle} fun q : ℕ × (List Bool × List Bool) => stageStep q.1 q.2 := by
  let inp : ℕ × (List Bool × List Bool) → Code × List Bool × List Bool :=
    fun q => bif q.1.bodd then (ofNat Code q.1.div2, q.2.2, q.2.1)
      else (ofNat Code q.1.div2, q.2.1, q.2.2)
  have hcode : Primrec fun q : ℕ × (List Bool × List Bool) => ofNat Code q.1.div2 :=
    (Primrec.ofNat Code).comp (nat_div2.comp fst)
  have hin : Primrec inp :=
    Primrec.cond (nat_bodd.comp fst)
      (hcode.pair ((snd.comp snd).pair (fst.comp snd)))
      (hcode.pair snd)
  have hrun : ComputableIn {Z.jump.oracle} fun q : ℕ × (List Bool × List Bool) =>
      diagStep (inp q).1 (inp q).2.1 (inp q).2.2 :=
    (computableIn_jump_diagStep Z).comp hin.computableIn
  have hout : Primrec fun r : Bool × (List Bool × List Bool) =>
      bif r.1 then r.2.swap else r.2 :=
    Primrec.cond fst ((snd.comp snd).pair (fst.comp snd)) snd
  refine RecursiveIn.of_eq
    (hout.computableIn.comp (((nat_bodd.comp fst).computableIn).pair hrun)) fun q => ?_
  congr 1
  dsimp only [inp, stageStep]
  cases q.1.bodd <;> rfl

/-- Every jump `Z.jump` computes the full Kleene–Post stage sequence. -/
theorem computableIn_jump_stage (Z : Set ℕ) : ComputableIn {Z.jump.oracle} stage := by
  have hrec : ComputableIn {Z.jump.oracle} fun s : ℕ =>
      Nat.rec (motive := fun _ => List Bool × List Bool) ([], [])
        (fun n b => stageStep n b) s :=
    ComputableIn.nat_rec ComputableIn.id (ComputableIn.const ([], []))
      (h := fun (_ : ℕ) (q : ℕ × (List Bool × List Bool)) => stageStep q.1 q.2)
      ((computableIn_jump_stageStep Z).comp ComputableIn.snd)
  refine RecursiveIn.of_eq hrec fun s => congrArg Part.some ?_
  induction s with
  | zero => rfl
  | succ s ih => rw [stage, ← ih]

/-- Every jump `Z.jump` computes `stageA`. -/
theorem computableIn_jump_stageA (Z : Set ℕ) : ComputableIn {Z.jump.oracle} stageA :=
  fst.computableIn.comp (computableIn_jump_stage Z)

/-- Every jump `Z.jump` computes `stageB`. -/
theorem computableIn_jump_stageB (Z : Set ℕ) : ComputableIn {Z.jump.oracle} stageB :=
  snd.computableIn.comp (computableIn_jump_stage Z)

/-- `stageA` is prefix-monotone from each stage to the next. -/
theorem stageA_prefix_succ (s : ℕ) : stageA s <+: stageA (s + 1) := by
  simp only [stageA, stage, stageStep]
  cases s.bodd
  · exact prefix_fst_diagStep _ _ _
  · exact prefix_snd_diagStep _ _ _

/-- `stageB` is prefix-monotone from each stage to the next. -/
theorem stageB_prefix_succ (s : ℕ) : stageB s <+: stageB (s + 1) := by
  simp only [stageB, stage, stageStep]
  cases s.bodd
  · exact prefix_snd_diagStep _ _ _
  · exact prefix_fst_diagStep _ _ _

/-- `stageA` strictly increases in length at every stage. -/
theorem length_stageA_lt_succ (s : ℕ) : (stageA s).length < (stageA (s + 1)).length := by
  simp only [stageA, stage, stageStep]
  cases s.bodd
  · exact length_lt_fst_diagStep _ _ _
  · exact length_lt_snd_diagStep _ _ _

/-- `stageB` strictly increases in length at every stage. -/
theorem length_stageB_lt_succ (s : ℕ) : (stageB s).length < (stageB (s + 1)).length := by
  simp only [stageB, stage, stageStep]
  cases s.bodd
  · exact length_lt_snd_diagStep _ _ _
  · exact length_lt_fst_diagStep _ _ _

/-- **Coordinate coverage for `stageA`.** By stage `x + 1`, `stageA` covers coordinate `x`. -/
theorem lt_length_stageA_succ (x : ℕ) : x < (stageA (x + 1)).length :=
  (Nat.lt_succ_self x).trans_le ((strictMono_nat_of_lt_succ length_stageA_lt_succ).id_le (x + 1))

/-- **Coordinate coverage for `stageB`.** By stage `x + 1`, `stageB` covers coordinate `x`. -/
theorem lt_length_stageB_succ (x : ℕ) : x < (stageB (x + 1)).length :=
  (Nat.lt_succ_self x).trans_le ((strictMono_nat_of_lt_succ length_stageB_lt_succ).id_le (x + 1))

end KleenePost

/-! ### The Kleene–Post limit sets, totality, and Turing incomparability -/

/-- The first set constructed in the Kleene–Post finite-extension procedure below `∅'`. -/
noncomputable def kleenePostSetA : Set ℕ :=
  bitLimit KleenePost.stageA

/-- The second set constructed in the Kleene–Post finite-extension procedure below `∅'`. -/
noncomputable def kleenePostSetB : Set ℕ :=
  bitLimit KleenePost.stageB

/-- Unfolding `kleenePostSetA`. -/
theorem kleenePostSetA_def : kleenePostSetA = bitLimit KleenePost.stageA :=
  (rfl)

/-- Unfolding `kleenePostSetB`. -/
theorem kleenePostSetB_def : kleenePostSetB = bitLimit KleenePost.stageB :=
  (rfl)

/-- `x ∈ kleenePostSetA` iff `(stageA s)[x]? = some true` at some stage `s`. -/
theorem mem_kleenePostSetA {x : ℕ} :
    x ∈ kleenePostSetA ↔ ∃ s, (KleenePost.stageA s)[x]? = some true :=
  mem_bitLimit

/-- `x ∈ kleenePostSetB` iff `(stageB s)[x]? = some true` at some stage `s`. -/
theorem mem_kleenePostSetB {x : ℕ} :
    x ∈ kleenePostSetB ↔ ∃ s, (KleenePost.stageB s)[x]? = some true :=
  mem_bitLimit

/-- At any stage `s` covering `x`, `x ∈ kleenePostSetA` iff `(stageA s)[x]? = some true`. -/
theorem mem_kleenePostSetA_iff_getElem?_of_lt {s x : ℕ} (hx : x < (KleenePost.stageA s).length) :
    x ∈ kleenePostSetA ↔ (KleenePost.stageA s)[x]? = some true :=
  mem_bitLimit_iff_getElem?_of_lt KleenePost.stageA_prefix_succ hx

/-- At any stage `s` covering `x`, `x ∈ kleenePostSetB` iff `(stageB s)[x]? = some true`. -/
theorem mem_kleenePostSetB_iff_getElem?_of_lt {s x : ℕ} (hx : x < (KleenePost.stageB s).length) :
    x ∈ kleenePostSetB ↔ (KleenePost.stageB s)[x]? = some true :=
  mem_bitLimit_iff_getElem?_of_lt KleenePost.stageB_prefix_succ hx

/-- `kleenePostSetA` extends `stageA s` at every stage `s`. -/
theorem extendsBits_kleenePostSetA (s : ℕ) : kleenePostSetA.ExtendsBits (KleenePost.stageA s) :=
  extendsBits_bitLimit KleenePost.stageA_prefix_succ s

/-- `kleenePostSetB` extends `stageB s` at every stage `s`. -/
theorem extendsBits_kleenePostSetB (s : ℕ) : kleenePostSetB.ExtendsBits (KleenePost.stageB s) :=
  extendsBits_bitLimit KleenePost.stageB_prefix_succ s

/-- **Totality of the `stageA` partial stage-union oracle.** -/
theorem dom_bitChainOracle_stageA_eq_univ :
    PFun.Dom (bitChainOracle KleenePost.stageA) = Set.univ :=
  dom_bitChainOracle_eq_univ_iff.2 fun x => ⟨x + 1, KleenePost.lt_length_stageA_succ x⟩

/-- **Totality of the `stageB` partial stage-union oracle.** -/
theorem dom_bitChainOracle_stageB_eq_univ :
    PFun.Dom (bitChainOracle KleenePost.stageB) = Set.univ :=
  dom_bitChainOracle_eq_univ_iff.2 fun x => ⟨x + 1, KleenePost.lt_length_stageB_succ x⟩

/-- **Coherence and totality identify `bitChainOracle stageA` with `kleenePostSetA.oracle`.** -/
theorem bitChainOracle_stageA_eq_oracle :
    bitChainOracle KleenePost.stageA = kleenePostSetA.oracle :=
  bitChainOracle_eq_oracle_bitLimit KleenePost.stageA_prefix_succ
    fun x => ⟨x + 1, KleenePost.lt_length_stageA_succ x⟩

/-- **Coherence and totality identify `bitChainOracle stageB` with `kleenePostSetB.oracle`.** -/
theorem bitChainOracle_stageB_eq_oracle :
    bitChainOracle KleenePost.stageB = kleenePostSetB.oracle :=
  bitChainOracle_eq_oracle_bitLimit KleenePost.stageB_prefix_succ
    fun x => ⟨x + 1, KleenePost.lt_length_stageB_succ x⟩

/-- `kleenePostSetA` is the unique set extending every `stageA s`. -/
theorem forall_extendsBits_stageA_iff {A : Set ℕ} :
    (∀ s, A.ExtendsBits (KleenePost.stageA s)) ↔ A = kleenePostSetA :=
  forall_extendsBits_iff_eq_bitLimit KleenePost.stageA_prefix_succ
    fun x => ⟨x + 1, KleenePost.lt_length_stageA_succ x⟩

/-- `kleenePostSetB` is the unique set extending every `stageB s`. -/
theorem forall_extendsBits_stageB_iff {B : Set ℕ} :
    (∀ s, B.ExtendsBits (KleenePost.stageB s)) ↔ B = kleenePostSetB :=
  forall_extendsBits_iff_eq_bitLimit KleenePost.stageB_prefix_succ
    fun x => ⟨x + 1, KleenePost.lt_length_stageB_succ x⟩

/-- `kleenePostSetA` is Turing reducible to `(∅ : Set ℕ).jump`. -/
theorem turingReducible_kleenePostSetA_jump_empty :
    TuringReducible kleenePostSetA.oracle (∅ : Set ℕ).jump.oracle :=
  turingReducible_bitLimit_of_computableIn KleenePost.stageA_prefix_succ
    (fun x => ⟨x + 1, KleenePost.lt_length_stageA_succ x⟩)
    (KleenePost.computableIn_jump_stageA ∅)

/-- `kleenePostSetB` is Turing reducible to `(∅ : Set ℕ).jump`. -/
theorem turingReducible_kleenePostSetB_jump_empty :
    TuringReducible kleenePostSetB.oracle (∅ : Set ℕ).jump.oracle :=
  turingReducible_bitLimit_of_computableIn KleenePost.stageB_prefix_succ
    (fun x => ⟨x + 1, KleenePost.lt_length_stageB_succ x⟩)
    (KleenePost.computableIn_jump_stageB ∅)

/-- **Even diagonal requirements.** For every oracle program `c`, `c` relative to `kleenePostSetB`
disagrees with `kleenePostSetA.oracle` at the witness `(stageA (2 * encode c)).length`. -/
theorem eval_ne_oracle_kleenePostSetA (c : Code) :
    Code.eval kleenePostSetB.oracle c (KleenePost.stageA (2 * encode c)).length ≠
      kleenePostSetA.oracle (KleenePost.stageA (2 * encode c)).length := by
  have hA := extendsBits_kleenePostSetA (2 * encode c + 1)
  have hB := extendsBits_kleenePostSetB (2 * encode c + 1)
  rw [KleenePost.stageA_two_mul_succ, ofNat_encode] at hA
  rw [KleenePost.stageB_two_mul_succ, ofNat_encode] at hB
  exact KleenePost.eval_ne_oracle_of_extendsBits_diagStep hA hB

/-- **Odd diagonal requirements.** For every oracle program `c`, `c` relative to `kleenePostSetA`
disagrees with `kleenePostSetB.oracle` at the witness `(stageB (2 * encode c + 1)).length`. -/
theorem eval_ne_oracle_kleenePostSetB (c : Code) :
    Code.eval kleenePostSetA.oracle c (KleenePost.stageB (2 * encode c + 1)).length ≠
      kleenePostSetB.oracle (KleenePost.stageB (2 * encode c + 1)).length := by
  have hA := extendsBits_kleenePostSetA (2 * encode c + 1 + 1)
  have hB := extendsBits_kleenePostSetB (2 * encode c + 1 + 1)
  rw [KleenePost.stageA_two_mul_add_one_succ, ofNat_encode] at hA
  rw [KleenePost.stageB_two_mul_add_one_succ, ofNat_encode] at hB
  exact KleenePost.eval_ne_oracle_of_extendsBits_diagStep hB hA

/-- `kleenePostSetA` is not Turing reducible to `kleenePostSetB`. -/
theorem not_turingReducible_kleenePostSetA_kleenePostSetB :
    ¬TuringReducible kleenePostSetA.oracle kleenePostSetB.oracle := fun h => by
  obtain ⟨c, hc⟩ := Code.turingReducible_iff_exists_code.1 h
  exact eval_ne_oracle_kleenePostSetA c (congrFun hc _)

/-- `kleenePostSetB` is not Turing reducible to `kleenePostSetA`. -/
theorem not_turingReducible_kleenePostSetB_kleenePostSetA :
    ¬TuringReducible kleenePostSetB.oracle kleenePostSetA.oracle := fun h => by
  obtain ⟨c, hc⟩ := Code.turingReducible_iff_exists_code.1 h
  exact eval_ne_oracle_kleenePostSetB c (congrFun hc _)

/-- `kleenePostSetA` is not computable. -/
theorem not_computablePred_mem_kleenePostSetA :
    ¬ComputablePred (· ∈ kleenePostSetA) := fun h =>
  not_turingReducible_kleenePostSetA_kleenePostSetB <|
    ((Set.turingReducible_empty_iff _).2 h).trans (Set.empty_turingReducible _)

/-- `kleenePostSetB` is not computable. -/
theorem not_computablePred_mem_kleenePostSetB :
    ¬ComputablePred (· ∈ kleenePostSetB) := fun h =>
  not_turingReducible_kleenePostSetB_kleenePostSetA <|
    ((Set.turingReducible_empty_iff _).2 h).trans (Set.empty_turingReducible _)

/-- **The Kleene–Post theorem [Soare, Theorem VI.1.2].** There exist two Turing incomparable sets
both Turing reducible to `(∅ : Set ℕ).jump`. -/
theorem kleene_post :
    ∃ A B : Set ℕ,
      TuringReducible A.oracle (∅ : Set ℕ).jump.oracle ∧
        TuringReducible B.oracle (∅ : Set ℕ).jump.oracle ∧
          ¬TuringReducible A.oracle B.oracle ∧ ¬TuringReducible B.oracle A.oracle :=
  ⟨kleenePostSetA, kleenePostSetB,
    turingReducible_kleenePostSetA_jump_empty, turingReducible_kleenePostSetB_jump_empty,
    not_turingReducible_kleenePostSetA_kleenePostSetB,
    not_turingReducible_kleenePostSetB_kleenePostSetA⟩

/-- The Turing degree of `kleenePostSetA` lies strictly between `0` and `0'`. -/
theorem degree_kleenePostSetA_mem_Ioo :
    toAntisymmetrization TuringReducible kleenePostSetA.oracle ∈
      Set.Ioo (toAntisymmetrization TuringReducible (∅ : Set ℕ).oracle)
        (toAntisymmetrization TuringReducible (∅ : Set ℕ).jump.oracle) :=
  Set.degree_mem_Ioo_of_incomparable
    turingReducible_kleenePostSetA_jump_empty turingReducible_kleenePostSetB_jump_empty
    not_turingReducible_kleenePostSetA_kleenePostSetB
    not_turingReducible_kleenePostSetB_kleenePostSetA

/-- The Turing degree of `kleenePostSetB` lies strictly between `0` and `0'`. -/
theorem degree_kleenePostSetB_mem_Ioo :
    toAntisymmetrization TuringReducible kleenePostSetB.oracle ∈
      Set.Ioo (toAntisymmetrization TuringReducible (∅ : Set ℕ).oracle)
        (toAntisymmetrization TuringReducible (∅ : Set ℕ).jump.oracle) :=
  Set.degree_mem_Ioo_of_incomparable
    turingReducible_kleenePostSetB_jump_empty turingReducible_kleenePostSetA_jump_empty
    not_turingReducible_kleenePostSetB_kleenePostSetA
    not_turingReducible_kleenePostSetA_kleenePostSetB

/-- The Turing degrees of `kleenePostSetA` and `kleenePostSetB` are incomparable. -/
theorem incomparable_degree_kleenePostSetA_kleenePostSetB :
    ¬(toAntisymmetrization TuringReducible kleenePostSetA.oracle ≤
        toAntisymmetrization TuringReducible kleenePostSetB.oracle) ∧
      ¬(toAntisymmetrization TuringReducible kleenePostSetB.oracle ≤
        toAntisymmetrization TuringReducible kleenePostSetA.oracle) := by
  rw [turingDegree_le_iff, turingDegree_le_iff]
  exact ⟨not_turingReducible_kleenePostSetA_kleenePostSetB,
    not_turingReducible_kleenePostSetB_kleenePostSetA⟩

/-- **Degree form of the Kleene–Post theorem.** There exist two incomparable Turing degrees
strictly between `0` and `0'`. -/
theorem exists_incomparable_turingDegrees_mem_Ioo :
    ∃ A B : Set ℕ,
      toAntisymmetrization TuringReducible A.oracle ∈
        Set.Ioo (toAntisymmetrization TuringReducible (∅ : Set ℕ).oracle)
          (toAntisymmetrization TuringReducible (∅ : Set ℕ).jump.oracle) ∧
      toAntisymmetrization TuringReducible B.oracle ∈
        Set.Ioo (toAntisymmetrization TuringReducible (∅ : Set ℕ).oracle)
          (toAntisymmetrization TuringReducible (∅ : Set ℕ).jump.oracle) ∧
      ¬(toAntisymmetrization TuringReducible A.oracle ≤
          toAntisymmetrization TuringReducible B.oracle) ∧
      ¬(toAntisymmetrization TuringReducible B.oracle ≤
          toAntisymmetrization TuringReducible A.oracle) :=
  ⟨kleenePostSetA, kleenePostSetB,
    degree_kleenePostSetA_mem_Ioo, degree_kleenePostSetB_mem_Ioo,
    incomparable_degree_kleenePostSetA_kleenePostSetB.1,
    incomparable_degree_kleenePostSetA_kleenePostSetB.2⟩

/-! ### Satisfaction regimes -/

namespace KleenePost

/-- **General convergent-disagreement regime on `kleenePostSetA`.** When `c` has a convergent
extension over `stageB (2 * encode c)` at witness `x = (stageA (2 * encode c)).length`,
`Code.eval kleenePostSetB.oracle c x` halts at some `y` and `kleenePostSetA.oracle x` disagrees
with `Part.some y`. -/
theorem exists_mem_eval_and_oracle_kleenePostSetA_ne_of_hasConvergentExt {c : Code}
    (h : Code.HasConvergentExt c (stageA (2 * encode c)).length (stageB (2 * encode c))) :
    ∃ y : ℕ, y ∈ Code.eval kleenePostSetB.oracle c (stageA (2 * encode c)).length ∧
      kleenePostSetA.oracle (stageA (2 * encode c)).length ≠ Part.some y := by
  have hA := extendsBits_kleenePostSetA (2 * encode c + 1)
  have hB := extendsBits_kleenePostSetB (2 * encode c + 1)
  rw [stageA_two_mul_succ, ofNat_encode] at hA
  rw [stageB_two_mul_succ, ofNat_encode] at hB
  obtain ⟨y, hy⟩ := exists_mem_eval_and_oracle_ne_of_hasConvergentExt h
  exact ⟨y, hy hA hB⟩

/-- **General permanent-divergence regime on `kleenePostSetA`.** When `c` has no convergent
extension over `stageB (2 * encode c)` at witness `x = (stageA (2 * encode c)).length`,
`Code.eval kleenePostSetB.oracle c x = Part.none` and the default extension places
`x ∉ kleenePostSetA` (`kleenePostSetA.oracle x = Part.some 0`). -/
theorem eval_eq_none_and_notMem_kleenePostSetA_of_not_hasConvergentExt {c : Code}
    (h : ¬Code.HasConvergentExt c (stageA (2 * encode c)).length (stageB (2 * encode c))) :
    Code.eval kleenePostSetB.oracle c (stageA (2 * encode c)).length = Part.none ∧
      (stageA (2 * encode c)).length ∉ kleenePostSetA ∧
      kleenePostSetA.oracle (stageA (2 * encode c)).length = Part.some 0 := by
  have hA := extendsBits_kleenePostSetA (2 * encode c + 1)
  rw [stageA_two_mul_succ, ofNat_encode] at hA
  exact eval_eq_none_and_notMem_of_not_hasConvergentExt h hA
    (extendsBits_kleenePostSetB (2 * encode c))

/-- **General convergent-disagreement regime on `kleenePostSetB`.** When `c` has a convergent
extension over `stageA (2 * encode c + 1)` at witness `x = (stageB (2 * encode c + 1)).length`,
`Code.eval kleenePostSetA.oracle c x` halts at some `y` and `kleenePostSetB.oracle x` disagrees
with `Part.some y`. -/
theorem exists_mem_eval_and_oracle_kleenePostSetB_ne_of_hasConvergentExt {c : Code}
    (h : Code.HasConvergentExt c (stageB (2 * encode c + 1)).length (stageA (2 * encode c + 1))) :
    ∃ y : ℕ, y ∈ Code.eval kleenePostSetA.oracle c (stageB (2 * encode c + 1)).length ∧
      kleenePostSetB.oracle (stageB (2 * encode c + 1)).length ≠ Part.some y := by
  have hA := extendsBits_kleenePostSetA (2 * encode c + 1 + 1)
  have hB := extendsBits_kleenePostSetB (2 * encode c + 1 + 1)
  rw [stageA_two_mul_add_one_succ, ofNat_encode] at hA
  rw [stageB_two_mul_add_one_succ, ofNat_encode] at hB
  obtain ⟨y, hy⟩ := exists_mem_eval_and_oracle_ne_of_hasConvergentExt h
  exact ⟨y, hy hB hA⟩

/-- **General permanent-divergence regime on `kleenePostSetB`.** When `c` has no convergent
extension over `stageA (2 * encode c + 1)` at witness `x = (stageB (2 * encode c + 1)).length`,
`Code.eval kleenePostSetA.oracle c x = Part.none` and the default extension places
`x ∉ kleenePostSetB` (`kleenePostSetB.oracle x = Part.some 0`). -/
theorem eval_eq_none_and_notMem_kleenePostSetB_of_not_hasConvergentExt {c : Code}
    (h : ¬Code.HasConvergentExt c (stageB (2 * encode c + 1)).length (stageA (2 * encode c + 1))) :
    Code.eval kleenePostSetA.oracle c (stageB (2 * encode c + 1)).length = Part.none ∧
      (stageB (2 * encode c + 1)).length ∉ kleenePostSetB ∧
      kleenePostSetB.oracle (stageB (2 * encode c + 1)).length = Part.some 0 := by
  have hB := extendsBits_kleenePostSetB (2 * encode c + 1 + 1)
  rw [stageB_two_mul_add_one_succ, ofNat_encode] at hB
  exact eval_eq_none_and_notMem_of_not_hasConvergentExt h hB
    (extendsBits_kleenePostSetA (2 * encode c + 1))

end KleenePost

end TauCeti
