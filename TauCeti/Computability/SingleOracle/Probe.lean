/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Agreement
public import TauCeti.Computability.SingleOracle.Limit
import TauCeti.Data.PFun.Basic

/-!
# Diagonal probes for agreement-length tests

`diagonalProbe b e` waits for program `e` to halt on input `e`, returns the supplied value `b`
at input zero, and diverges at every positive input. The compiler is primitive recursive in
both numerical parameters, independently of the oracle. Its semantic equation holds even for
partial oracles.

These programs turn diagonal halting into a test on the length of agreement. Against a target
whose value at zero is `b`, the probe's agreement length is at most one, and is positive exactly
when its stage computation succeeds at zero. A genuine diagonal convergence is eventually
visible along any converging approximation of a total oracle, giving agreement length one.
For a fixed oracle, diagonal divergence gives agreement length zero at every stage. For moving
oracles, the latter conclusion requires additional preservation hypotheses; transient successes
need not represent convergence on the limit oracle.

In the low Sacks splitting argument the supplied value is the target's bit at zero. This bit is
an input to the compiler, rather than something extracted from an index for a c.e. target.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, VII.3, pp. 125–126.
-/

public section

open Encodable Denumerable Filter TauCeti.Approximation

namespace TauCeti.Oracle.Single.Code

/-- Wait for the diagonal computation numbered `e` and return `b` at input zero; diverge at
all other inputs. The output value is supplied explicitly and may be any natural number. -/
def diagonalProbe (b e : ℕ) : Code :=
  comp (prec
    (comp (Nat.Partrec.Code.const b).toSingleOracleCode
      (comp (ofNat Code e) (Nat.Partrec.Code.const e).toSingleOracleCode))
    (rfind' (comp succ zero))) (pair zero (pair left right))

private theorem eval_probe_loop (O : ℕ →. ℕ) (n : ℕ) :
    eval O (rfind' (comp succ zero)) n = Part.none := by
  rw [← Nat.pair_unpair n, eval_rfind']
  apply Part.eq_none_iff.2
  intro y hy
  obtain ⟨k, hk, -⟩ := (Part.mem_map_iff _).1 hy
  have := Nat.rfind_spec hk
  simp at this

/-- The probe's exact partial semantics, including divergence, uniformly for every oracle. -/
@[simp]
theorem eval_diagonalProbe (O : ℕ →. ℕ) (b e x : ℕ) :
    eval O (diagonalProbe b e) x =
      if x = 0 then (eval O (ofNat Code e) e).map (fun _ => b) else Part.none := by
  have hinput (n : ℕ) :
      eval O (pair zero (pair left right)) n = Part.some (Nat.pair 0 n) := by
    simp [Seq.seq]
  rw [diagonalProbe, eval_comp, hinput, PFun.some_bind]
  cases x with
  | zero =>
    rw [eval_prec_zero]
    have hb : (Nat.Partrec.Code.const b).eval = fun _ => Part.some b :=
      funext (Nat.Partrec.Code.eval_const b)
    simp [hb, Part.bind_some_eq_map]
  | succ x =>
    rw [eval_prec_succ]
    apply Part.eq_none_iff.2
    intro y
    simp only [Part.bind_eq_bind, Part.mem_bind_iff, eval_probe_loop, Part.notMem_none,
      and_false, exists_false, not_false_eq_true]

/-- The probe halts only at zero, exactly when the diagonal computation halts, and returns the
supplied value. -/
theorem mem_eval_diagonalProbe {O : ℕ →. ℕ} {b e x y : ℕ} :
    y ∈ eval O (diagonalProbe b e) x ↔
      x = 0 ∧ (eval O (ofNat Code e) e).Dom ∧ y = b := by
  by_cases hx : x = 0 <;> simp [hx, Part.mem_map_iff, ← Part.dom_iff_mem, eq_comm]

/-- The probe compiler is primitive recursive in the output value and the diagonal index. -/
theorem primrec₂_diagonalProbe : Primrec₂ diagonalProbe := by
  exact primrec₂_comp.comp
    (primrec₂_prec.comp
      (primrec₂_comp.comp
        (Nat.Partrec.Code.primrec_toSingleOracleCode.comp
          (Nat.Partrec.Code.primrec_const.comp Primrec.fst))
        (primrec₂_comp.comp ((Primrec.ofNat Code).comp Primrec.snd)
          (Nat.Partrec.Code.primrec_toSingleOracleCode.comp
            (Nat.Partrec.Code.primrec_const.comp Primrec.snd))))
      (Primrec.const _)) (Primrec.const _)

/-- On numerical program indices the probe compiler is primitive recursive as well. -/
theorem primrec₂_encode_diagonalProbe : Primrec₂ fun b e => encode (diagonalProbe b e) :=
  Primrec.encode.comp primrec₂_diagonalProbe

/-! ### Bounded observations -/

variable {σ : ℕ → Option ℕ} {k b e x : ℕ} {d : Halt} {g : ℕ → ℕ}

/-- Even a transient successful run of a probe has input zero and the prescribed output. -/
theorem eq_zero_and_output_eq_of_evaln_diagonalProbe
    (h : evaln σ k (diagonalProbe b e) x = some d) : x = 0 ∧ d.output = b := by
  have hs := evaln_sound (O := fun z => (σ z : Part ℕ)) h
    (fun z _ y hy => by simp [hy])
  exact ⟨(mem_eval_diagonalProbe.1 hs).1, (mem_eval_diagonalProbe.1 hs).2.2⟩

/-- A probe's agreement length never exceeds one, even with partial finite oracle answers. -/
theorem agreementLength_diagonalProbe_le_one : agreementLength σ k (diagonalProbe b e) g ≤ 1 := by
  by_contra hn
  obtain ⟨d, hd, -⟩ := agreesAt_iff.1 (agreesAt_of_lt_agreementLength (by omega :
    1 < agreementLength σ k (diagonalProbe b e) g))
  have := (eq_zero_and_output_eq_of_evaln_diagonalProbe hd).1
  omega

/-- When the supplied value matches the target at zero, agreement length one is precisely
successful bounded evaluation at zero. -/
theorem agreementLength_diagonalProbe_eq_one_iff (hg : g 0 = b) :
    agreementLength σ k (diagonalProbe b e) g = 1 ↔
      ∃ d, evaln σ k (diagonalProbe b e) 0 = some d := by
  have hle : agreementLength σ k (diagonalProbe b e) g ≤ 1 :=
    agreementLength_diagonalProbe_le_one
  constructor
  · intro h
    obtain ⟨d, hd, -⟩ := agreesAt_iff.1 (agreesAt_of_lt_agreementLength (by omega :
      0 < agreementLength σ k (diagonalProbe b e) g))
    exact ⟨d, hd⟩
  · rintro ⟨d, hd⟩
    have ha : AgreesAt σ k (diagonalProbe b e) g 0 :=
      (agreesAt_iff_of_evaln_eq_some hd).2
        ((eq_zero_and_output_eq_of_evaln_diagonalProbe hd).2.trans hg.symm)
    have : 1 ≤ agreementLength σ k (diagonalProbe b e) g :=
      le_agreementLength_iff.2 fun x hx => by
        have hx0 : x = 0 := by omega
        simpa [hx0] using ha
    omega

/-! ### Visibility along approximations -/

/-- Diagonal convergence on a total limit oracle eventually makes the probe's agreement length
one. Only the target value at zero needs to settle. No effectiveness of a stabilization stage is
asserted. -/
theorem eventually_agreementLength_diagonalProbe_eq_one {O : ℕ → ℕ}
    {σs : ℕ → ℕ → Option ℕ} {gs : ℕ → ℕ → ℕ}
    (hσ : Converges σs (fun z => some (O z)))
    (hg : ∀ᶠ s in atTop, gs s 0 = b) (he : (eval (O : ℕ →. ℕ) (ofNat Code e) e).Dom) :
    ∀ᶠ s in atTop, agreementLength (σs s) s (diagonalProbe b e) (gs s) = 1 := by
  have hp : b ∈ eval (O : ℕ →. ℕ) (diagonalProbe b e) 0 :=
    mem_eval_diagonalProbe.2 ⟨rfl, he, rfl⟩
  obtain ⟨d, -, hd⟩ := exists_eventually_evaln_eq_some_of_mem_eval
    (by simp) hσ tendsto_id hp
  filter_upwards [hg, hd] with s hgs hds
  exact (agreementLength_diagonalProbe_eq_one_iff hgs).2 ⟨d, hds⟩

/-- Against fixed partial oracle answers, diagonal divergence makes the probe's agreement length
zero at every stage, for any target. This conclusion is not asserted for moving oracles. -/
theorem agreementLength_diagonalProbe_eq_zero_of_not_dom
    (he : ¬(eval (fun z => (σ z : Part ℕ)) (ofNat Code e) e).Dom) (k : ℕ) (g : ℕ → ℕ) :
    agreementLength σ k (diagonalProbe b e) g = 0 := by
  apply (agreementLength_eq_iff).2
  refine ⟨?_, by simp⟩
  rintro ha
  obtain ⟨d, hd, -⟩ := agreesAt_iff.1 ha
  have hs := evaln_sound (O := fun z => (σ z : Part ℕ)) hd
    (fun z _ y hy => by simp [hy])
  exact he (mem_eval_diagonalProbe.1 hs).2.1

end TauCeti.Oracle.Single.Code
