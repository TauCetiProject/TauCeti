/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Primrec
public import TauCeti.Computability.TuringDegree
import TauCeti.Computability.RecursiveIn

/-!
# Finite binary oracle strings, forcing alternatives, and growing bit chains

In finite-extension constructions of sets `A ⊆ ℕ`, a stage specifies a finite binary initial
segment `σ : List Bool` of a characteristic function rather than a finite set: coordinates below
`σ.length` have committed membership bits, while coordinates at or above `σ.length` are still
uncommitted and supply `none` (no answer) to bounded oracle evaluations. Returning `none` beyond
`σ.length`, rather than `some 0`, ensures that a computation succeeding against `σ` genuinely reads
only committed coordinates and therefore persists on *every* total set extending `σ`.

This file develops the three components of that finite-extension machinery:

1. **Set extensions and bounded evaluation against binary strings.** `Set.ExtendsBits A σ` asserts
   that `A` agrees with `σ` below `σ.length`, and `TauCeti.Oracle.Single.Code.bitAnswers σ` turns
   `σ` into partial oracle answers `(σ[z]?).map Bool.toNat`. A successful run against `bitAnswers σ`
   has use at most `σ.length`, persists under prefix extension of `σ`, and computes a value of
   `eval A.oracle` for every set `A` extending `σ`; conversely, every value of `eval A.oracle` is
   already witnessed by some finite binary extension of `σ` consistent with `A`.
2. **The extension-or-permanent-divergence alternative and effective search.** For a program `c`,
   input `x`, and string `β`, `HasConvergentExt c x β` asserts that some finite binary extension
   `β ++ δ` makes `evaln` halt on `x`. Either such an extension exists—forcing a single output on
   every set extending `β ++ δ`—or `eval Y.oracle c x = Part.none` for *every* set `Y` extending
   `β` (`exists_prefix_mem_eval_or_forall_eval_eq_none`). Unbounded search `findConvergentExt` via
   `Nat.rfindOpt` makes witness extraction partial recursive (`partrec_findConvergentExt`) and
   shows that `HasConvergentExt` is c.e. (`rePred_hasConvergentExt`).
3. **Coherent growing chains of binary strings.** Given a prefix-monotone sequence
   `σs : ℕ → List Bool` covering every coordinate, the partial union `bitChainOracle σs` is total
   (`Dom = Set.univ`) and equals `(bitLimit σs).oracle`, `bitLimit σs` is the unique set in
   `Set ℕ` extending every stage `σs s`, and `O`-computability of `σs` gives `O`-computability of
   `bitLimit σs`.

## Main definitions

* `Set.ExtendsBits`: a set `A ⊆ ℕ` agrees with a finite binary string `σ : List Bool` below
  `σ.length`.
* `TauCeti.Oracle.Single.Code.bitAnswers`: partial `0`/`1` oracle answers of a `List Bool`,
  answering `none` beyond `σ.length`.
* `TauCeti.Oracle.Single.Code.HasConvergentExt`: existence of a finite binary extension of `β` on
  which `c` halts at `x`.
* `TauCeti.Oracle.Single.Code.findConvergentExt`: partial recursive search returning a convergent
  extension `δ` together with its `Halt` record.
* `TauCeti.bitLimit`: the limit set `{x | ∃ s, (σs s)[x]? = some true}` of a chain of bit strings.
* `TauCeti.bitChainOracle`: the partial oracle `fun x => Nat.rfindOpt fun s => bitAnswers (σs s) x`
  formed by taking the first stage defining coordinate `x`.

## Main results

* `TauCeti.Oracle.Single.Code.evaln_bitAnswers_use_le_length`,
  `TauCeti.Oracle.Single.Code.evaln_bitAnswers_of_prefix`,
  `TauCeti.Oracle.Single.Code.mem_eval_oracle_of_evaln_bitAnswers`,
  `TauCeti.Oracle.Single.Code.exists_append_evaln_bitAnswers_of_mem_eval_oracle`: use bound,
  persistence, soundness, and completeness of bounded evaluation on binary oracle strings.
* `TauCeti.Oracle.Single.Code.exists_prefix_mem_eval_or_forall_eval_eq_none`: the
  **extension-or-permanent-divergence alternative**.
* `TauCeti.Oracle.Single.Code.partrec_findConvergentExt`,
  `TauCeti.Oracle.Single.Code.rePred_hasConvergentExt`: effectivity of convergent-extension search.
* `TauCeti.dom_bitChainOracle_eq_univ`, `TauCeti.bitChainOracle_eq_oracle_bitLimit`,
  `TauCeti.forall_extendsBits_iff_eq_bitLimit`, `TauCeti.turingReducible_bitLimit_of_computableIn`:
  totality, uniqueness, and Turing reducibility of the limit of a coherent covering bit chain.

## References

* S. C. Kleene and E. L. Post, *The upper semi-lattice of degrees of recursive unsolvability*,
  Ann. of Math. (2) **59** (1954), 379–407.
* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter VI.1.
-/

public section

open Encodable Primrec

/-! ### Sets extending finite binary strings -/

namespace Set

/-- A set `A : Set ℕ` **extends** a finite binary string `σ : List Bool` when membership in `A`
below `σ.length` agrees with the bits of `σ`: whenever `σ[z]? = some b`, `z ∈ A ↔ b = true`. -/
def ExtendsBits (A : Set ℕ) (σ : List Bool) : Prop :=
  ∀ ⦃z : ℕ⦄ ⦃b : Bool⦄, σ[z]? = some b → (z ∈ A ↔ b = true)

/-- Unfolding `Set.ExtendsBits`. -/
theorem extendsBits_def (A : Set ℕ) (σ : List Bool) :
    A.ExtendsBits σ ↔ ∀ ⦃z : ℕ⦄ ⦃b : Bool⦄, σ[z]? = some b → (z ∈ A ↔ b = true) :=
  Iff.rfl

/-- `A` extends `σ` exactly when membership in `A` at every index `z < σ.length` matches `σ[z]`. -/
theorem extendsBits_iff_getElem {A : Set ℕ} {σ : List Bool} :
    A.ExtendsBits σ ↔ ∀ (z : ℕ) (hz : z < σ.length), z ∈ A ↔ σ[z] = true := by
  constructor
  · intro h z hz
    exact h (List.getElem?_eq_getElem hz)
  · intro h z b hz
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.1 hz
    exact h z hlt

/-- Every set extends the empty binary string. -/
@[simp]
theorem extendsBits_nil (A : Set ℕ) : A.ExtendsBits [] := by
  intro _ _ hz
  simp at hz

/-- If `A` extends `τ` and `σ` is a prefix of `τ`, then `A` extends `σ`. -/
theorem ExtendsBits.of_prefix {A : Set ℕ} {σ τ : List Bool} (hA : A.ExtendsBits τ)
    (hστ : σ <+: τ) : A.ExtendsBits σ := by
  intro z b hz
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.1 hz
  exact hA (List.prefix_iff_getElem?.1 hστ z hlt)

/-- Extending `σ ++ τ` means extending `σ` and agreeing with `τ` shifted by `σ.length`. -/
theorem extendsBits_append {A : Set ℕ} {σ τ : List Bool} :
    A.ExtendsBits (σ ++ τ) ↔
      A.ExtendsBits σ ∧ ∀ ⦃z : ℕ⦄ ⦃b : Bool⦄, τ[z]? = some b → (σ.length + z ∈ A ↔ b = true) := by
  constructor
  · intro h
    refine ⟨h.of_prefix (List.prefix_append σ τ), fun z b hz => h ?_⟩
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact hz
  · rintro ⟨hσ, hτ⟩ z b hz
    by_cases hlt : z < σ.length
    · rw [List.getElem?_append_left hlt] at hz
      exact hσ hz
    · have hle : σ.length ≤ z := Nat.le_of_not_lt hlt
      rw [List.getElem?_append_right hle] at hz
      have heq : σ.length + (z - σ.length) = z := Nat.add_sub_cancel' hle
      exact heq ▸ hτ hz

/-- Extending `σ ++ [b]` means extending `σ` and matching `b` at coordinate `σ.length`. -/
@[simp]
theorem extendsBits_concat {A : Set ℕ} {σ : List Bool} {b : Bool} :
    A.ExtendsBits (σ ++ [b]) ↔ A.ExtendsBits σ ∧ (σ.length ∈ A ↔ b = true) := by
  rw [extendsBits_append]
  refine and_congr_right fun _ => ⟨fun h => by simpa using h (z := 0) rfl, fun h z b' hz => ?_⟩
  cases z with
  | zero =>
    obtain rfl : b' = b := by simpa using hz.symm
    simpa using h
  | succ z => simp at hz

/-- At an address where `σ[z]? = some b`, the characteristic function `A.indicator 1` of any set
`A` extending `σ` equals `b.toNat`. -/
theorem ExtendsBits.indicator_eq_toNat {A : Set ℕ} {σ : List Bool} (hA : A.ExtendsBits σ)
    {z : ℕ} {b : Bool} (hz : σ[z]? = some b) : A.indicator (1 : ℕ → ℕ) z = b.toNat := by
  have hmem := hA hz
  by_cases h : z ∈ A <;> cases b <;> simp_all

/-- At an address where `σ[z]? = some b`, the set oracle `A.oracle` of any set `A` extending `σ`
answers `Part.some b.toNat`. -/
theorem ExtendsBits.oracle_eq_some_toNat {A : Set ℕ} {σ : List Bool} (hA : A.ExtendsBits σ)
    {z : ℕ} {b : Bool} (hz : σ[z]? = some b) : A.oracle z = Part.some b.toNat := by
  simp [hA.indicator_eq_toNat hz]

/-- The finite set `{z | σ[z]? = some true}` extends `σ`. -/
@[simp]
theorem extendsBits_setOf_getElem?_eq_some_true {σ : List Bool} :
    {z : ℕ | σ[z]? = some true}.ExtendsBits σ := by
  intro z b hz
  simp [hz]

/-- Every set `A` extends its length-`m` membership prefix `(List.range m).map (decide (· ∈ A))`. -/
theorem extendsBits_map_range (A : Set ℕ) [DecidablePred (· ∈ A)] (m : ℕ) :
    A.ExtendsBits ((List.range m).map fun z => decide (z ∈ A)) := by
  rw [extendsBits_iff_getElem]
  simp

/-- If `A` extends `σ` and `σ.length ≤ m`, then `σ` is a prefix of the length-`m` membership
prefix of `A`. -/
theorem ExtendsBits.prefix_map_range {A : Set ℕ} [DecidablePred (· ∈ A)] {σ : List Bool}
    (hA : A.ExtendsBits σ) {m : ℕ} (hm : σ.length ≤ m) :
    σ <+: (List.range m).map fun z => decide (z ∈ A) := by
  rw [List.prefix_iff_getElem?]
  intro z hz
  rw [List.getElem?_map, List.getElem?_range (hz.trans_le hm), Option.map_some, Option.some.injEq]
  exact Bool.eq_iff_iff.2 (decide_eq_true_iff.trans (hA (List.getElem?_eq_getElem hz)))

end Set

/-! ### Bounded evaluation against binary strings and the forcing alternative -/

namespace TauCeti.Oracle.Single.Code

/-- If the partial oracle answers `τ` supply `none` at every address `z ≥ m`, then every successful
bounded run against `τ` has use at most `m`. -/
theorem evaln_use_le_of_forall_eq_none {τ : ℕ → Option ℕ} {m : ℕ}
    (hτ : ∀ z, m ≤ z → τ z = none) :
    ∀ {k : ℕ} {c : Code} {n : ℕ} {d : Halt}, evaln τ k c n = some d → d.use ≤ m
  | 0, _, _, _, h => by simp at h
  | k + 1, c, n, d, h => by
    induction c generalizing n d with
    | zero | succ | left | right =>
      simp only [evaln_succ_zero_eq_some, evaln_succ_succ_eq_some, evaln_succ_left_eq_some,
        evaln_succ_right_eq_some] at h
      obtain ⟨-, rfl⟩ := h
      exact Nat.zero_le m
    | oracle =>
      obtain ⟨-, y, hy, rfl⟩ := evaln_succ_oracle_eq_some.1 h
      dsimp only
      by_contra hlt
      have hnone := hτ n (by omega)
      simp [hnone] at hy
    | pair cf cg hf hg =>
      obtain ⟨-, df, dg, hdf, hdg, rfl⟩ := evaln_succ_pair_eq_some.1 h
      exact max_le (hf _ _ hdf) (hg _ _ hdg)
    | comp cf cg hf hg =>
      obtain ⟨-, dg, df, hdg, hdf, rfl⟩ := evaln_succ_comp_eq_some.1 h
      exact max_le (hg _ _ hdg) (hf _ _ hdf)
    | prec cf cg hf hg =>
      obtain ⟨a, y, rfl⟩ : ∃ a y, n = Nat.pair a y := ⟨_, _, (Nat.pair_unpair n).symm⟩
      cases y with
      | zero => exact hf _ _ (evaln_succ_prec_zero_eq_some.1 h).2
      | succ y =>
        obtain ⟨-, di, d', hdi, hd', rfl⟩ := evaln_succ_prec_succ_eq_some.1 h
        exact max_le (evaln_use_le_of_forall_eq_none hτ hdi) (hg _ _ hd')
    | rfind' cf hf =>
      obtain ⟨a, y, rfl⟩ : ∃ a y, n = Nat.pair a y := ⟨_, _, (Nat.pair_unpair n).symm⟩
      obtain ⟨-, dx, hdx, ⟨-, rfl⟩ | ⟨-, d', hd', rfl⟩⟩ := evaln_succ_rfind'_eq_some.1 h
      · exact hf _ dx hdx
      · exact max_le (hf _ _ hdx) (evaln_use_le_of_forall_eq_none hτ hd')

/-- The partial oracle answers supplied by a finite binary string `σ : List Bool`: `some b.toNat`
when `σ[z]? = some b`, and `none` for addresses `z ≥ σ.length`. -/
def bitAnswers (σ : List Bool) (z : ℕ) : Option ℕ :=
  (σ[z]?).map Bool.toNat

/-- Unfolding `bitAnswers`. -/
theorem bitAnswers_def (σ : List Bool) (z : ℕ) : bitAnswers σ z = (σ[z]?).map Bool.toNat :=
  (rfl)

/-- The empty binary string supplies no oracle answers. -/
@[simp]
theorem bitAnswers_nil (z : ℕ) : bitAnswers [] z = none :=
  (rfl)

/-- Beyond `σ.length`, `bitAnswers σ` answers `none`. -/
theorem bitAnswers_eq_none_of_le {σ : List Bool} {z : ℕ} (hz : σ.length ≤ z) :
    bitAnswers σ z = none := by
  simp [bitAnswers, List.getElem?_eq_none hz]

/-- Below `σ.length`, `bitAnswers σ` answers `some σ[z].toNat`. -/
theorem bitAnswers_of_lt {σ : List Bool} {z : ℕ} (hz : z < σ.length) :
    bitAnswers σ z = some σ[z].toNat := by
  simp [bitAnswers, hz]

/-- Prefix extension preserves all answers below the shorter string's length. -/
theorem bitAnswers_of_prefix {σ τ : List Bool} (hστ : σ <+: τ) {z : ℕ} (hz : z < σ.length) :
    bitAnswers τ z = bitAnswers σ z := by
  have hget : τ[z]? = some σ[z] := List.prefix_iff_getElem?.1 hστ z hz
  simp [bitAnswers, hz, hget]

/-- If `A` extends `σ`, then `setAnswers A` agrees with `bitAnswers σ` below `σ.length`. -/
theorem setAnswers_eq_bitAnswers_of_extendsBits {A : Set ℕ} {σ : List Bool}
    (hA : A.ExtendsBits σ) {z : ℕ} (hz : z < σ.length) :
    setAnswers A z = bitAnswers σ z := by
  rw [setAnswers_apply, bitAnswers_of_lt hz, hA.indicator_eq_toNat (List.getElem?_eq_getElem hz)]

/-- `bitAnswers` is primitive recursive in the binary string and the address. -/
theorem primrec₂_bitAnswers : Primrec₂ bitAnswers :=
  option_map list_getElem? ((Primrec.cond snd (const 1) (const 0)).to₂.of_eq
    fun _ b => by cases b <;> rfl)

/-- Bounded evaluation against `bitAnswers σ` is primitive recursive in `σ`, the fuel, the program,
and the input. -/
theorem primrec_evaln_bitAnswers :
    Primrec fun p : List Bool × ℕ × Code × ℕ => evaln (bitAnswers p.1) p.2.1 p.2.2.1 p.2.2.2 :=
  primrec_evaln primrec₂_bitAnswers

/-- A successful bounded run against `bitAnswers σ` has use at most `σ.length`. -/
theorem evaln_bitAnswers_use_le_length {σ : List Bool} {k : ℕ} {c : Code} {n : ℕ} {d : Halt}
    (h : evaln (bitAnswers σ) k c n = some d) : d.use ≤ σ.length :=
  evaln_use_le_of_forall_eq_none (fun _ hz => bitAnswers_eq_none_of_le hz) h

/-- **Persistence along binary extensions.** A successful run against `bitAnswers σ` succeeds with
the same output and use against `bitAnswers τ` whenever `σ <+: τ`. -/
theorem evaln_bitAnswers_of_prefix {σ τ : List Bool} (hστ : σ <+: τ) {k : ℕ} {c : Code} {n : ℕ}
    {d : Halt} (h : evaln (bitAnswers σ) k c n = some d) :
    evaln (bitAnswers τ) k c n = some d :=
  evaln_eq_some_of_eqOn h fun _ hz =>
    (bitAnswers_of_prefix hστ ((Set.mem_Iio.1 hz).trans_le (evaln_bitAnswers_use_le_length h))).symm

/-- A successful run against `bitAnswers σ` succeeds with the same output and use against
`setAnswers A` for every set `A` extending `σ`. -/
theorem evaln_setAnswers_of_evaln_bitAnswers {A : Set ℕ} {σ : List Bool} (hA : A.ExtendsBits σ)
    {k : ℕ} {c : Code} {n : ℕ} {d : Halt} (h : evaln (bitAnswers σ) k c n = some d) :
    evaln (setAnswers A) k c n = some d :=
  evaln_eq_some_of_eqOn h fun _ hz =>
    (setAnswers_eq_bitAnswers_of_extendsBits hA
      ((Set.mem_Iio.1 hz).trans_le (evaln_bitAnswers_use_le_length h))).symm

/-- **Soundness on all set extensions.** If `evaln (bitAnswers σ) k c n = some d`, then `d.output`
belongs to `eval A.oracle c n` for every set `A` extending `σ`. -/
theorem mem_eval_oracle_of_evaln_bitAnswers {A : Set ℕ} {σ : List Bool} (hA : A.ExtendsBits σ)
    {k : ℕ} {c : Code} {n : ℕ} {d : Halt} (h : evaln (bitAnswers σ) k c n = some d) :
    d.output ∈ eval A.oracle c n :=
  evaln_sound (evaln_setAnswers_of_evaln_bitAnswers hA h) (by simp)

/-- **Completeness by finite extension.** If `A` extends `σ` and `y ∈ eval A.oracle c n`, then `σ`
has a finite suffix `δ` such that `A` extends `σ ++ δ` and `evaln (bitAnswers (σ ++ δ))` halts on
`n` with output `y`. -/
theorem exists_append_evaln_bitAnswers_of_mem_eval_oracle {A : Set ℕ} {σ : List Bool}
    (hA : A.ExtendsBits σ) {c : Code} {n y : ℕ} (hy : y ∈ eval A.oracle c n) :
    ∃ (δ : List Bool) (k : ℕ) (d : Halt),
      A.ExtendsBits (σ ++ δ) ∧ evaln (bitAnswers (σ ++ δ)) k c n = some d ∧ d.output = y := by
  classical
  obtain ⟨k, d, hd, rfl⟩ := exists_evaln_eq_some_of_mem_eval (σ := setAnswers A) (by simp) hy
  let m := max σ.length k
  let τ := (List.range m).map fun z => decide (z ∈ A)
  have hστ : σ <+: τ := hA.prefix_map_range (le_max_left _ _)
  obtain ⟨δ, hδ⟩ := hστ
  have hAτ : A.ExtendsBits (σ ++ δ) := hδ.symm ▸ Set.extendsBits_map_range A m
  refine ⟨δ, k, d, hAτ, evaln_eq_some_of_eqOn hd fun z hz => ?_, rfl⟩
  have hzlen : z < (σ ++ δ).length := by
    have huse := evaln_use_le hd
    have hlen : (σ ++ δ).length = m := by simp [hδ, τ]
    exact (Set.mem_Iio.1 hz).trans_le (huse.trans ((le_max_right _ _).trans_eq hlen.symm))
  exact setAnswers_eq_bitAnswers_of_extendsBits hAτ hzlen

/-- `HasConvergentExt c x β` holds when some finite binary extension `β ++ δ` makes bounded
evaluation of `c` at `x` succeed at some fuel `k`. -/
def HasConvergentExt (c : Code) (x : ℕ) (β : List Bool) : Prop :=
  ∃ (δ : List Bool) (k : ℕ), (evaln (bitAnswers (β ++ δ)) k c x).isSome

/-- Unfolding `HasConvergentExt`. -/
theorem hasConvergentExt_def (c : Code) (x : ℕ) (β : List Bool) :
    HasConvergentExt c x β ↔
      ∃ (δ : List Bool) (k : ℕ), (evaln (bitAnswers (β ++ δ)) k c x).isSome :=
  Iff.rfl

/-- `HasConvergentExt c x β` holds exactly when some prefix extension `β'` of `β` forces `eval` at
`x` to converge to a single value `y` on every set extending `β'`. -/
theorem hasConvergentExt_iff_exists_prefix {c : Code} {x : ℕ} {β : List Bool} :
    HasConvergentExt c x β ↔
      ∃ β' : List Bool, β <+: β' ∧
        ∃ y : ℕ, ∀ Y : Set ℕ, Y.ExtendsBits β' → y ∈ eval Y.oracle c x := by
  constructor
  · rintro ⟨δ, k, hk⟩
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 hk
    exact ⟨β ++ δ, List.prefix_append β δ, d.output,
      fun _ hY => mem_eval_oracle_of_evaln_bitAnswers hY hd⟩
  · rintro ⟨β', ⟨δ, rfl⟩, y, hy⟩
    have hmem := hy {z | (β ++ δ)[z]? = some true} Set.extendsBits_setOf_getElem?_eq_some_true
    obtain ⟨δ', k, d, -, hd, -⟩ :=
      exists_append_evaln_bitAnswers_of_mem_eval_oracle
        Set.extendsBits_setOf_getElem?_eq_some_true hmem
    rw [List.append_assoc] at hd
    exact ⟨δ ++ δ', k, by simp [hd]⟩

/-- `HasConvergentExt c x β` holds exactly when `eval Y.oracle c x` halts for at least one set `Y`
extending `β`. -/
theorem hasConvergentExt_iff_exists_extendsBits_dom {c : Code} {x : ℕ} {β : List Bool} :
    HasConvergentExt c x β ↔ ∃ Y : Set ℕ, Y.ExtendsBits β ∧ (eval Y.oracle c x).Dom := by
  constructor
  · rintro ⟨δ, k, hk⟩
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 hk
    have hY : {z | (β ++ δ)[z]? = some true}.ExtendsBits (β ++ δ) :=
      Set.extendsBits_setOf_getElem?_eq_some_true
    exact ⟨_, hY.of_prefix (List.prefix_append β δ),
      Part.dom_iff_mem.2 ⟨d.output, mem_eval_oracle_of_evaln_bitAnswers hY hd⟩⟩
  · rintro ⟨Y, hY, hdom⟩
    obtain ⟨y, hy⟩ := Part.dom_iff_mem.1 hdom
    obtain ⟨δ, k, d, -, hd, -⟩ := exists_append_evaln_bitAnswers_of_mem_eval_oracle hY hy
    exact ⟨δ, k, by simp [hd]⟩

/-- Negating `HasConvergentExt`: when no finite binary extension makes `evaln` succeed, `c`
diverges (`Part.none`) at `x` relative to *every* set `Y` extending `β`. -/
theorem not_hasConvergentExt_iff {c : Code} {x : ℕ} {β : List Bool} :
    ¬HasConvergentExt c x β ↔ ∀ Y : Set ℕ, Y.ExtendsBits β → eval Y.oracle c x = Part.none := by
  rw [hasConvergentExt_iff_exists_extendsBits_dom]
  push Not
  exact forall₂_congr fun _ _ => Part.eq_none_iff'.symm

/-- **The extension-or-permanent-divergence alternative.** Given a program `c`, input `x`, and
finite binary string `β`, either some finite binary extension `β'` of `β` forces `eval Y.oracle c x`
to converge to a common output `y` for all `Y` extending `β'`, or `eval Y.oracle c x` diverges for
every `Y` extending `β`. -/
theorem exists_prefix_mem_eval_or_forall_eval_eq_none (c : Code) (x : ℕ) (β : List Bool) :
    (∃ β' : List Bool, β <+: β' ∧
        ∃ y : ℕ, ∀ Y : Set ℕ, Y.ExtendsBits β' → y ∈ eval Y.oracle c x) ∨
      (∀ Y : Set ℕ, Y.ExtendsBits β → eval Y.oracle c x = Part.none) := by
  by_cases h : HasConvergentExt c x β
  · exact Or.inl (hasConvergentExt_iff_exists_prefix.1 h)
  · exact Or.inr (not_hasConvergentExt_iff.1 h)

/-- Partial recursive search for a finite binary suffix `δ` and halting record `d` witnessing a
convergent run of `c` at `x` over `β ++ δ`. -/
def findConvergentExt (c : Code) (x : ℕ) (β : List Bool) : Part (List Bool × Halt) :=
  Nat.rfindOpt fun n =>
    (decode (α := List Bool × ℕ) n).bind fun p =>
      (evaln (bitAnswers (β ++ p.1)) p.2 c x).map fun d => (p.1, d)

/-- `findConvergentExt` is partial recursive uniformly in `(c, x, β)`. -/
theorem partrec_findConvergentExt :
    Partrec fun q : Code × ℕ × List Bool => findConvergentExt q.1 q.2.1 q.2.2 := by
  have heval : Primrec fun r : ((Code × ℕ × List Bool) × ℕ) × (List Bool × ℕ) =>
      evaln (bitAnswers (r.1.1.2.2 ++ r.2.1)) r.2.2 r.1.1.1 r.1.1.2.1 :=
    primrec_evaln_bitAnswers.comp <|
      (list_append.comp (snd.comp (snd.comp (fst.comp fst))) (fst.comp snd)).pair <|
        (snd.comp snd).pair <|
          (fst.comp (fst.comp fst)).pair (fst.comp (snd.comp (fst.comp fst)))
  have hmk : Primrec₂ fun (r : ((Code × ℕ × List Bool) × ℕ) × (List Bool × ℕ)) (d : Halt) =>
      (r.2.1, d) := ((fst.comp snd).comp fst).pair snd
  have hbody : Primrec₂ fun (u : (Code × ℕ × List Bool) × ℕ) (p : List Bool × ℕ) =>
      (evaln (bitAnswers (u.1.2.2 ++ p.1)) p.2 u.1.1 u.1.2.1).map fun d => (p.1, d) :=
    (option_map heval hmk).to₂
  have hdec : Primrec fun u : (Code × ℕ × List Bool) × ℕ => decode (α := List Bool × ℕ) u.2 :=
    (Primrec.decode (α := List Bool × ℕ)).comp snd
  exact Partrec.rfindOpt (option_bind hdec hbody).to₂.to_comp

/-- `findConvergentExt c x β` halts if and only if `HasConvergentExt c x β` holds. -/
@[simp]
theorem dom_findConvergentExt_iff {c : Code} {x : ℕ} {β : List Bool} :
    (findConvergentExt c x β).Dom ↔ HasConvergentExt c x β := by
  rw [findConvergentExt, Nat.rfindOpt_dom, HasConvergentExt]
  constructor
  · rintro ⟨n, ⟨δ, d⟩, hmem⟩
    simp only [Option.mem_def, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hmem
    obtain ⟨⟨δ', k⟩, -, d', hd, -⟩ := hmem
    exact ⟨δ', k, by simp [hd]⟩
  · rintro ⟨δ, k, hk⟩
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 hk
    exact ⟨encode (δ, k), (δ, d), by simp [hd]⟩

/-- Existence of a convergent binary extension is a c.e. predicate uniformly in `(c, x, β)`. -/
theorem rePred_hasConvergentExt :
    REPred fun q : Code × ℕ × List Bool => HasConvergentExt q.1 q.2.1 q.2.2 :=
  partrec_findConvergentExt.dom_re.of_eq fun _ => dom_findConvergentExt_iff

/-- Every output `(δ, d)` of `findConvergentExt c x β` comes from a successful run of `evaln`
against `bitAnswers (β ++ δ)` at some fuel `k`. -/
theorem exists_evaln_of_mem_findConvergentExt {c : Code} {x : ℕ} {β : List Bool}
    {w : List Bool × Halt} (hw : w ∈ findConvergentExt c x β) :
    ∃ k : ℕ, evaln (bitAnswers (β ++ w.1)) k c x = some w.2 := by
  obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hw
  simp only [Option.mem_def, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hn
  obtain ⟨⟨δ, k⟩, -, d, hd, hpair⟩ := hn
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair.symm
  exact ⟨k, hd⟩

/-- If `w ∈ findConvergentExt c x β`, then `w.2.output ∈ eval Y.oracle c x` for every set `Y`
extending `β ++ w.1`. -/
theorem mem_eval_oracle_of_mem_findConvergentExt {c : Code} {x : ℕ} {β : List Bool}
    {w : List Bool × Halt} (hw : w ∈ findConvergentExt c x β) {Y : Set ℕ}
    (hY : Y.ExtendsBits (β ++ w.1)) : w.2.output ∈ eval Y.oracle c x := by
  obtain ⟨k, hk⟩ := exists_evaln_of_mem_findConvergentExt hw
  exact mem_eval_oracle_of_evaln_bitAnswers hY hk

end TauCeti.Oracle.Single.Code

/-! ### Coherent growing chains of binary strings -/

namespace TauCeti

open Oracle.Single

/-- The limit set of a sequence of binary strings `σs : ℕ → List Bool`: the coordinates assigned
`true` at some stage. -/
def bitLimit (σs : ℕ → List Bool) : Set ℕ :=
  {x | ∃ s, (σs s)[x]? = some true}

/-- `x ∈ bitLimit σs` exactly when `(σs s)[x]? = some true` at some stage `s`. -/
@[simp]
theorem mem_bitLimit {σs : ℕ → List Bool} {x : ℕ} :
    x ∈ bitLimit σs ↔ ∃ s, (σs s)[x]? = some true :=
  Iff.rfl

/-- The partial oracle formed from a stage sequence of binary strings by taking the answer at the
first stage whose length covers the queried coordinate. -/
def bitChainOracle (σs : ℕ → List Bool) : ℕ →. ℕ :=
  fun x => Nat.rfindOpt fun s => Code.bitAnswers (σs s) x

/-- Evaluating `bitChainOracle` at `x`. -/
@[simp]
theorem bitChainOracle_apply (σs : ℕ → List Bool) (x : ℕ) :
    bitChainOracle σs x = Nat.rfindOpt fun s => Code.bitAnswers (σs s) x :=
  (rfl)

/-- Coherence of a prefix-monotone sequence of lists: any two stages defining coordinate `x`
assign the same value there. -/
theorem getElem?_eq_of_forall_prefix_succ {α : Type*} {σs : ℕ → List α}
    (hpref : ∀ s, σs s <+: σs (s + 1)) {s₁ s₂ x : ℕ} {b₁ b₂ : α}
    (h₁ : (σs s₁)[x]? = some b₁) (h₂ : (σs s₂)[x]? = some b₂) : b₁ = b₂ := by
  obtain ⟨hlt₁, rfl⟩ := List.getElem?_eq_some_iff.1 h₁
  obtain ⟨hlt₂, rfl⟩ := List.getElem?_eq_some_iff.1 h₂
  have hm₁ := List.prefix_iff_getElem?.1
    (Nat.rel_of_forall_rel_succ_of_le (· <+: ·) hpref (le_max_left s₁ s₂)) x hlt₁
  have hm₂ := List.prefix_iff_getElem?.1
    (Nat.rel_of_forall_rel_succ_of_le (· <+: ·) hpref (le_max_right s₁ s₂)) x hlt₂
  exact Option.some.inj (hm₁.symm.trans hm₂)

/-- Along a prefix-monotone sequence of binary strings, `bitLimit σs` extends every stage `σs s`. -/
theorem extendsBits_bitLimit {σs : ℕ → List Bool} (hpref : ∀ s, σs s <+: σs (s + 1)) (s : ℕ) :
    (bitLimit σs).ExtendsBits (σs s) := by
  intro x b hxs
  rw [mem_bitLimit]
  exact ⟨fun ⟨t, hxt⟩ => getElem?_eq_of_forall_prefix_succ hpref hxs hxt,
    fun hb => ⟨s, hb ▸ hxs⟩⟩

/-- Along a prefix-monotone sequence, at any stage `s` covering `x`, `x ∈ bitLimit σs` iff
`(σs s)[x]? = some true`. -/
theorem mem_bitLimit_iff_getElem?_of_lt {σs : ℕ → List Bool}
    (hpref : ∀ s, σs s <+: σs (s + 1)) {s x : ℕ} (hx : x < (σs s).length) :
    x ∈ bitLimit σs ↔ (σs s)[x]? = some true :=
  extendsBits_bitLimit hpref s (List.getElem?_eq_getElem hx) |>.trans
    ⟨fun h => by simp [hx, h], fun h => by simpa [hx] using h⟩

/-- Along a prefix-monotone sequence, at any stage `s` covering `x`, `x ∉ bitLimit σs` iff
`(σs s)[x]? = some false`. -/
theorem notMem_bitLimit_iff_getElem?_of_lt {σs : ℕ → List Bool}
    (hpref : ∀ s, σs s <+: σs (s + 1)) {s x : ℕ} (hx : x < (σs s).length) :
    x ∉ bitLimit σs ↔ (σs s)[x]? = some false := by
  rw [mem_bitLimit_iff_getElem?_of_lt hpref hx, List.getElem?_eq_getElem hx]
  cases (σs s)[x] <;> simp

/-- **Coordinate coverage implies totality of `bitChainOracle` at `x`.** -/
theorem dom_bitChainOracle {σs : ℕ → List Bool} (hcovers : ∀ x, ∃ s, x < (σs s).length) (x : ℕ) :
    (bitChainOracle σs x).Dom := by
  obtain ⟨s, hs⟩ := hcovers x
  exact Nat.rfindOpt_dom.2 ⟨s, (σs s)[x].toNat, Code.bitAnswers_of_lt hs⟩

/-- **Totality of the partial stage-union oracle.** If every coordinate is covered at some stage,
then `bitChainOracle σs` has total domain `Set.univ`. -/
theorem dom_bitChainOracle_eq_univ {σs : ℕ → List Bool} (hcovers : ∀ x, ∃ s, x < (σs s).length) :
    PFun.Dom (bitChainOracle σs) = Set.univ :=
  Set.eq_univ_of_forall (dom_bitChainOracle hcovers)

/-- **Coherence and totality identify `bitChainOracle σs` with `(bitLimit σs).oracle`.** -/
theorem bitChainOracle_eq_oracle_bitLimit {σs : ℕ → List Bool}
    (hpref : ∀ s, σs s <+: σs (s + 1)) (hcovers : ∀ x, ∃ s, x < (σs s).length) :
    bitChainOracle σs = (bitLimit σs).oracle := by
  ext x y
  constructor
  · intro hy
    obtain ⟨s, hs⟩ := Nat.rfindOpt_spec hy
    simp only [Option.mem_def, Code.bitAnswers_def, Option.map_eq_some_iff] at hs
    obtain ⟨b, hb, rfl⟩ := hs
    rw [(extendsBits_bitLimit hpref s).oracle_eq_some_toNat hb]
    exact Part.mem_some _
  · intro hy
    obtain ⟨z, hz⟩ := Part.dom_iff_mem.1 (dom_bitChainOracle hcovers x)
    obtain ⟨s, hs⟩ := Nat.rfindOpt_spec hz
    simp only [Option.mem_def, Code.bitAnswers_def, Option.map_eq_some_iff] at hs
    obtain ⟨b, hb, rfl⟩ := hs
    have hy' : y = b.toNat := by
      rw [(extendsBits_bitLimit hpref s).oracle_eq_some_toNat hb, Part.mem_some_iff] at hy
      exact hy
    exact hy' ▸ hz

/-- **Uniqueness of the limit set.** Along a prefix-monotone chain covering every coordinate, a set
`A` extends `σs s` for every `s` if and only if `A = bitLimit σs`. -/
theorem forall_extendsBits_iff_eq_bitLimit {σs : ℕ → List Bool}
    (hpref : ∀ s, σs s <+: σs (s + 1)) (hcovers : ∀ x, ∃ s, x < (σs s).length) {A : Set ℕ} :
    (∀ s, A.ExtendsBits (σs s)) ↔ A = bitLimit σs := by
  refine ⟨fun hA => Set.ext fun x => ?_, fun h => h ▸ extendsBits_bitLimit hpref⟩
  obtain ⟨s, hs⟩ := hcovers x
  have hget := List.getElem?_eq_getElem hs
  exact (hA s hget).trans (extendsBits_bitLimit hpref s hget).symm

/-- Along a prefix-monotone chain covering every coordinate, `bitLimit σs` is the unique set in
`Set ℕ` extending every stage. -/
theorem existsUnique_extendsBits {σs : ℕ → List Bool}
    (hpref : ∀ s, σs s <+: σs (s + 1)) (hcovers : ∀ x, ∃ s, x < (σs s).length) :
    ∃! A : Set ℕ, ∀ s, A.ExtendsBits (σs s) :=
  ⟨bitLimit σs, extendsBits_bitLimit hpref,
    fun _ hA => (forall_extendsBits_iff_eq_bitLimit hpref hcovers).1 hA⟩

/-- **Computing the limit characteristic function from the stages.** If a prefix-monotone covering
sequence `σs : ℕ → List Bool` is computable in `O`, then the characteristic function of
`bitLimit σs` is computable in `O`: search for the first stage `s` covering `x` and read its bit. -/
theorem computableIn_indicator_bitLimit {O : Set (ℕ →. ℕ)} {σs : ℕ → List Bool}
    (hpref : ∀ s, σs s <+: σs (s + 1)) (hcovers : ∀ x, ∃ s, x < (σs s).length)
    (hσs : ComputableIn O σs) :
    ComputableIn O ((bitLimit σs).indicator 1 : ℕ → ℕ) := by
  have hans : ComputableIn O fun n : ℕ => Code.bitAnswers (σs n.unpair.2) n.unpair.1 :=
    Code.primrec₂_bitAnswers.computableIn.comp
      ((hσs.comp (ComputableIn.snd.comp ComputableIn.unpair)).pair
        (ComputableIn.fst.comp ComputableIn.unpair))
  have htest : Nat.RecursiveIn O
      fun n => Part.some (cond (Code.bitAnswers (σs n.unpair.2) n.unpair.1).isSome 0 1) :=
    RecursiveIn.iff_nat.1 <|
      (Primrec.cond option_isSome (const 0) (const 1)).computableIn.comp hans
  have hval : Nat.RecursiveIn O
      fun n => Part.some ((Code.bitAnswers (σs n.unpair.2) n.unpair.1).getD 0) :=
    RecursiveIn.iff_nat.1 <| (option_getD.comp Primrec.id (const 0)).computableIn.comp hans
  refine RecursiveIn.iff_nat.2 <|
    (hval.comp (Nat.RecursiveIn.pair Nat.Primrec.id.recursiveIn htest.rfind)).of_eq_tot fun x => ?_
  have hdom : (Nat.rfind fun s =>
      (fun m => decide (m = 0)) <$>
        Part.some (cond (Code.bitAnswers (σs (Nat.pair x s).unpair.2)
          (Nat.pair x s).unpair.1).isSome 0 1)).Dom := by
    obtain ⟨s, hs⟩ := hcovers x
    exact Nat.rfind_dom.2 ⟨s, by simp [Code.bitAnswers_of_lt hs], fun _ => by simp⟩
  obtain ⟨s₀, hs₀⟩ := Part.dom_iff_mem.1 hdom
  have hsome : (Code.bitAnswers (σs s₀) x).isSome = true := by
    have := (Nat.mem_rfind.1 hs₀).1
    cases h : (Code.bitAnswers (σs s₀) x).isSome <;> simp [h] at this ⊢
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hsome
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hy
  have hind := (extendsBits_bitLimit hpref s₀).indicator_eq_toNat hb
  rw [Part.eq_some_iff.2 hs₀]
  simp [Seq.seq, Code.bitAnswers, hb, hind]

/-- **Turing reducibility of `bitLimit σs`.** If a prefix-monotone covering sequence `σs` is
computable in `{g}`, then `(bitLimit σs).oracle` is Turing reducible to `g`. -/
theorem turingReducible_bitLimit_of_computableIn {g : ℕ →. ℕ} {σs : ℕ → List Bool}
    (hpref : ∀ s, σs s <+: σs (s + 1)) (hcovers : ∀ x, ∃ s, x < (σs s).length)
    (hσs : ComputableIn {g} σs) :
    TuringReducible (bitLimit σs).oracle g :=
  ((bitLimit σs).turingReducible_iff_computableIn_indicator g).2
    (computableIn_indicator_bitLimit hpref hcovers hσs)

end TauCeti
