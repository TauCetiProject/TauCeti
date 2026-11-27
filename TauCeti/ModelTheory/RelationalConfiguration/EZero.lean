/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Logic.Equiv.Finset
public import TauCeti.ModelTheory.RelationalConfiguration.BorelComplete
public import TauCeti.ModelTheory.RelationalConfiguration.Relabel
public import TauCeti.SetTheory.Descriptive.EZero

/-!
# `E₀` reduces to isomorphism on every Borel complete class

Eventual equality `E₀` of binary sequences (`TauCeti.eZero`) is Borel reducible to isomorphism of
countable structures, and so to isomorphism on every Borel complete class. Consequently the
isomorphism relation of such a class is not smooth: no Borel map into Cantor space gives complete
invariants. In a language with countably many relation symbols of each arity, such a class has
exactly continuum many isomorphism types.

The reduction lives in the relational language `copiesLanguage` with one binary symbol `S` and
two unary symbols `Z` and `P`. The code of `x : ℕ → Bool` (`copiesCode x`) has carrier
`Finset ℕ × ℕ`: on each copy `{F} × ℕ`, `S` is the successor relation, `Z` holds at `(F, 0)` only,
and `P` holds at `(F, n)` exactly when `x n ≠ (n ∈ F)`, so the copy of `F` reads `x` with the bits
in `F` flipped. If `x` and `y` differ exactly on the finite set `D`, then `F ↦ F ∆ D` carries the
copies of `x` onto the copies of `y`. Conversely, a map preserving `S`, `Z` and `P` sends the
copy of `∅` onto a single copy `{G} × ℕ`, following `Z` and then `S`, and then `x` and `y` differ
exactly on `G`. Relabelled along a bijection `Finset ℕ × ℕ ≃ ℕ`, this is a continuous reduction
of `E₀` to isomorphism of codes on `ℕ`.

## Main definitions

* `TauCeti.RelationalConfiguration.copiesLanguage`: the language with symbols `S`, `Z` and `P`.
* `TauCeti.RelationalConfiguration.copiesCode x`: the code on `Finset ℕ × ℕ` of the copies of `x`.

## Main results

* `TauCeti.RelationalConfiguration.isoSetoid_copiesCode_iff`: the codes of `x` and `y` are
  isomorphic exactly when `x` and `y` are eventually equal.
* `TauCeti.RelationalConfiguration.exists_continuous_reduction_eZero`: a continuous map to codes
  on `ℕ` reduces `E₀` to isomorphism.
* `TauCeti.RelationalConfiguration.borelReducible_eZero_of_borelComplete`: `E₀` is Borel reducible
  to isomorphism on every Borel complete class, and hence so is equality on Cantor space
  (`TauCeti.RelationalConfiguration.borelReducible_bot_of_borelComplete`).
* `TauCeti.RelationalConfiguration.not_isSmooth_classIso_of_borelComplete`: isomorphism on a Borel
  complete class is not smooth.
* `TauCeti.RelationalConfiguration.mk_quotient_classIso_of_borelComplete`: a Borel complete class
  in a countable relational language has exactly continuum many isomorphism types.

## References

* R. Camerlo and S. Gao, *The completeness of the isomorphism relation for countable Boolean
  algebras*, Trans. Amer. Math. Soc. 353 (2001), §1.
* S. Gao, *Invariant Descriptive Set Theory*, CRC Press, 2009, §13.1.
-/

public section

universe u v

open FirstOrder FirstOrder.Language Set Cardinal
open scoped symmDiff

namespace TauCeti.RelationalConfiguration

/-! ### The language of copies -/

/-- The relation symbols of `copiesLanguage`: a binary successor symbol `succ` and two unary
symbols, `zero` for the first point of a copy and `flip` for the flipped bits. -/
inductive CopiesRel : ℕ → Type
  | succ : CopiesRel 2
  | zero : CopiesRel 1
  | flip : CopiesRel 1

/-- The relational language with one binary symbol `S` and two unary symbols `Z` and `P`, in which
`copiesCode` codes the copies of a binary sequence. -/
@[expose] def copiesLanguage : Language.{0, 0} :=
  ⟨fun _ => Empty, CopiesRel⟩

instance : copiesLanguage.IsRelational := fun _ => inferInstanceAs (IsEmpty Empty)

/-- The position of a symbol among the three symbols of `copiesLanguage`. -/
private def CopiesRel.index : ∀ {n : ℕ}, CopiesRel n → Fin 3
  | _, .succ => 0
  | _, .zero => 1
  | _, .flip => 2

instance (n : ℕ) : Finite (copiesLanguage.Relations n) :=
  Finite.of_injective (β := Fin 3) CopiesRel.index fun R R' h => by
    cases R <;> cases R' <;> first | rfl | exact absurd h (by decide)

/-- The successor symbol `S` of `copiesLanguage`. -/
abbrev succSymb : copiesLanguage.Relations 2 := CopiesRel.succ

/-- The symbol `Z` of `copiesLanguage`, marking the first point of each copy. -/
abbrev zeroSymb : copiesLanguage.Relations 1 := CopiesRel.zero

/-- The symbol `P` of `copiesLanguage`, marking the flipped bits. -/
abbrev flipSymb : copiesLanguage.Relations 1 := CopiesRel.flip

/-! ### The code of the copies of a sequence -/

/-- The structure on `Finset ℕ × ℕ` of the copies of `x`, read by `copiesCode`. -/
@[instance_reducible]
private def copiesStructure (x : ℕ → Bool) : copiesLanguage.Structure (Finset ℕ × ℕ) where
  RelMap
    | CopiesRel.succ, v => (v 1).1 = (v 0).1 ∧ (v 1).2 = (v 0).2 + 1
    | CopiesRel.zero, v => (v 0).2 = 0
    | CopiesRel.flip, v => x (v 0).2 ≠ decide ((v 0).2 ∈ (v 0).1)

/-- The code on `Finset ℕ × ℕ` of the copies of `x : ℕ → Bool`: on each copy `{F} × ℕ`, `S` is the
successor relation, `Z` holds at `(F, 0)` only, and `P` holds at `(F, n)` exactly when
`x n ≠ (n ∈ F)`, so the copy of `F` reads `x` with the bits in `F` flipped. -/
noncomputable def copiesCode (x : ℕ → Bool) :
    RelationalConfiguration copiesLanguage (Finset ℕ × ℕ) :=
  @ofStructure _ _ (copiesStructure x)

/-- In `copiesCode x`, `S` relates `(F, n)` to `(F, n + 1)` and nothing else. -/
@[simp]
theorem eval_copiesCode_succSymb (x : ℕ → Bool) (v : Fin 2 → Finset ℕ × ℕ) :
    (copiesCode x).eval (atom succSymb v) =
      decide ((v 1).1 = (v 0).1 ∧ (v 1).2 = (v 0).2 + 1) := by
  rw [copiesCode, @eval_ofStructure _ _ (copiesStructure x)]
  exact decide_eq_decide.2 Iff.rfl

/-- In `copiesCode x`, `Z` holds at the points `(F, 0)`. -/
@[simp]
theorem eval_copiesCode_zeroSymb (x : ℕ → Bool) (v : Fin 1 → Finset ℕ × ℕ) :
    (copiesCode x).eval (atom zeroSymb v) = decide ((v 0).2 = 0) := by
  rw [copiesCode, @eval_ofStructure _ _ (copiesStructure x)]
  exact decide_eq_decide.2 Iff.rfl

/-- In `copiesCode x`, `P` holds at `(F, n)` exactly when `x n ≠ (n ∈ F)`. -/
@[simp]
theorem eval_copiesCode_flipSymb (x : ℕ → Bool) (v : Fin 1 → Finset ℕ × ℕ) :
    (copiesCode x).eval (atom flipSymb v) = decide (x (v 0).2 ≠ decide ((v 0).2 ∈ (v 0).1)) := by
  rw [copiesCode, @eval_ofStructure _ _ (copiesStructure x)]
  exact decide_eq_decide.2 Iff.rfl

/-- **`copiesCode` is continuous.** -/
theorem continuous_copiesCode : Continuous copiesCode := by
  -- Each coordinate is constant or reads one bit of `x`.
  refine continuous_iff.2 fun a => ?_
  induction a using Atom.induction_atom with | @h n R v => ?_
  cases R
  · simp only [eval_copiesCode_succSymb]
    exact continuous_const
  · simp only [eval_copiesCode_zeroSymb]
    exact continuous_const
  · rw [funext fun x => eval_copiesCode_flipSymb x v]
    exact (continuous_of_discreteTopology
      (f := fun b : Bool => decide (b ≠ decide ((v 0).2 ∈ (v 0).1)))).comp (continuous_apply _)

/-! ### Isomorphism of the codes is eventual equality -/

variable {x y : ℕ → Bool}

/-- If `x` and `y` are eventually equal, their codes are isomorphic. -/
theorem isoSetoid_copiesCode (h : eZero x y) :
    isoSetoid copiesLanguage (Finset ℕ × ℕ) (copiesCode x) (copiesCode y) := by
  -- With `D` the finite set where `x` and `y` differ, `F ↦ F ∆ D` carries the copy of `F` for `x`
  -- onto the copy of `F ∆ D` for `y`.
  set D := (eZero_iff_finite.1 h).toFinset
  have hD (n : ℕ) : n ∈ D ↔ x n ≠ y n := by simp [D]
  let τ : Equiv.Perm (Finset ℕ) := (symmDiff_left_involutive D).toPerm
  let ρ := τ.prodCongr (Equiv.refl ℕ)
  have hρ (p : Finset ℕ × ℕ) : ρ.symm p = (p.1 ∆ D, p.2) := by
    simp [ρ, τ, Equiv.prodCongr_symm, Prod.map_apply']
  refine isoSetoid_iff_exists_perm_smul_eq.2 ⟨ρ, ext fun a => ?_⟩
  induction a using Atom.induction_atom with | @h n R v => ?_
  rw [eval_perm_smul, Atom.map_atom]
  cases R
  · simp [Function.comp_def, hρ, symmDiff_left_inj]
  · simp [Function.comp_def, hρ]
  · simp only [eval_copiesCode_flipSymb, Function.comp_apply, hρ, Finset.mem_symmDiff, hD]
    by_cases hF : (v 0).2 ∈ (v 0).1 <;> cases hx : x (v 0).2 <;> cases hy : y (v 0).2 <;>
      simp_all

/-- If the codes of `x` and `y` are isomorphic, then `x` and `y` are eventually equal. -/
theorem eZero_of_isoSetoid_copiesCode
    (h : isoSetoid copiesLanguage (Finset ℕ × ℕ) (copiesCode x) (copiesCode y)) : eZero x y := by
  -- An isomorphism `σ` maps the copy of `∅` for `x` onto a copy `{G} × ℕ` for `y`, following `Z`
  -- and then `S`, and comparing `P` along the two copies shows that `x` and `y` differ exactly
  -- on `G`.
  obtain ⟨σ, hσ⟩ := isoSetoid_iff_exists_perm_smul_eq.1 h
  -- `σ` carries every atom of `copiesCode x` to an atom of `copiesCode y` with the same value.
  have hmap {k : ℕ} (R : copiesLanguage.Relations k) (v : Fin k → Finset ℕ × ℕ) :
      (copiesCode y).eval (atom R (σ ∘ v)) = (copiesCode x).eval (atom R v) :=
    hσ ▸ eval_perm_smul_atom_comp σ _ R v
  set G := (σ (∅, 0)).1
  have hcopy (n : ℕ) : σ (∅, n) = (G, n) := by
    induction n with
    | zero =>
      have h0 := hmap zeroSymb ![(∅, 0)]
      simp only [eval_copiesCode_zeroSymb, Function.comp_apply, Matrix.cons_val_fin_one,
        decide_true, decide_eq_true_eq] at h0
      exact Prod.ext rfl h0
    | succ n ih =>
      have hs := hmap succSymb ![(∅, n), (∅, n + 1)]
      simp only [eval_copiesCode_succSymb, Function.comp_apply, Matrix.cons_val_one,
        Matrix.cons_val_zero, ih, and_self, decide_true, decide_eq_true_eq] at hs
      exact Prod.ext hs.1 hs.2
  refine eZero_iff_finite.2 (G.finite_toSet.subset fun n hn => ?_)
  have hp := hmap flipSymb ![(∅, n)]
  simp only [eval_copiesCode_flipSymb, Function.comp_apply, Matrix.cons_val_fin_one, hcopy,
    Finset.notMem_empty, decide_false] at hp
  by_contra hG
  rw [Finset.mem_coe] at hG
  cases hx : x n <;> cases hy : y n <;> simp_all

/-- **The codes of `x` and `y` are isomorphic exactly when `x` and `y` are eventually equal.** -/
theorem isoSetoid_copiesCode_iff :
    isoSetoid copiesLanguage (Finset ℕ × ℕ) (copiesCode x) (copiesCode y) ↔ eZero x y :=
  ⟨eZero_of_isoSetoid_copiesCode, isoSetoid_copiesCode⟩

/-- **A continuous reduction of `E₀` to isomorphism**: relabelled along a bijection
`Finset ℕ × ℕ ≃ ℕ`, `copiesCode` is a continuous map to codes on `ℕ` whose values at `x` and `y`
are isomorphic exactly when `x` and `y` are eventually equal. -/
theorem exists_continuous_reduction_eZero :
    ∃ f : (ℕ → Bool) → RelationalConfiguration copiesLanguage ℕ, Continuous f ∧
      ∀ x y, eZero x y ↔ isoSetoid copiesLanguage ℕ (f x) (f y) :=
  ⟨fun x => relabel (Denumerable.eqv (Finset ℕ × ℕ)) (copiesCode x),
    (relabel _).continuous.comp continuous_copiesCode,
    fun _ _ => by rw [isoSetoid_relabel_iff, isoSetoid_copiesCode_iff]⟩

/-- `E₀` is Borel reducible to isomorphism of codes of `copiesLanguage` on `ℕ`. -/
theorem borelReducible_eZero_isoSetoid : eZero.BorelReducible (isoSetoid copiesLanguage ℕ) :=
  let ⟨f, hf, hiso⟩ := exists_continuous_reduction_eZero
  Setoid.borelReducible_iff.2 ⟨f, hf.measurable, hiso⟩

/-! ### Consequences for Borel complete classes -/

variable {L : Language.{u, v}} [L.IsRelational] {K : Set (RelationalConfiguration L ℕ)}

/-- **`E₀` is Borel reducible to isomorphism on every Borel complete class.** -/
theorem borelReducible_eZero_of_borelComplete (hK : BorelComplete K) :
    eZero.BorelReducible (classIso K) :=
  borelReducible_eZero_isoSetoid.trans (borelComplete_iff_forall_isoSetoid.1 hK copiesLanguage)

/-- Equality on Cantor space is Borel reducible to isomorphism on every Borel complete class. -/
theorem borelReducible_bot_of_borelComplete (hK : BorelComplete K) :
    (⊥ : Setoid (ℕ → Bool)).BorelReducible (classIso K) :=
  borelReducible_bot_eZero.trans (borelReducible_eZero_of_borelComplete hK)

/-- **Isomorphism on a Borel complete class is not smooth**: no Borel map into Cantor space has
the isomorphism classes as its fibres. -/
theorem not_isSmooth_classIso_of_borelComplete (hK : BorelComplete K) :
    ¬ (classIso K).IsSmooth :=
  not_isSmooth_of_borelReducible_eZero (borelReducible_eZero_of_borelComplete hK)

/-- **A Borel complete class has exactly continuum many isomorphism types**, in a language with
countably many relation symbols of each arity. -/
theorem mk_quotient_classIso_of_borelComplete [∀ n, Countable (L.Relations n)]
    (hK : BorelComplete K) : #(Quotient (classIso K)) = 𝔠 := by
  refine le_antisymm (mk_quotient_le.trans ((mk_set_le K).trans (mk_le_continuum L ℕ))) ?_
  have h := (borelReducible_eZero_of_borelComplete hK).lift_mk_quotient_le
  rwa [mk_quotient_eZero, lift_continuum, lift_uzero] at h

end TauCeti.RelationalConfiguration
