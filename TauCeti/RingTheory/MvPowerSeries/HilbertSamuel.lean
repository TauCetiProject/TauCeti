/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.PiLex
public import Mathlib.Order.WellFoundedSet
public import TauCeti.RingTheory.LocalRing.HilbertSamuel.Basic
public import TauCeti.RingTheory.MvPowerSeries.InitialDiagram
import TauCeti.Algebra.Order.Antidiag.FinsuppEquiv
import TauCeti.Data.Finsupp.UpperSet
import TauCeti.RingTheory.MvPowerSeries.FormalDivision
import TauCeti.RingTheory.MvPowerSeries.Length

/-!
# Hilbert–Samuel functions of ideals in multivariate formal power series

Over a field `K` in finitely many variables `σ`, given a degree-compatible monomial order
`ord : MonomialOrder σ` — one satisfying `Monotone (Finsupp.degree ∘ ord.toSyn.symm)`, such as
`MonomialOrder.degLex` — the truncated quotient equivalence
`ord.quotientSupMaximalIdealPowEquiv` identifies `MvPowerSeries σ K ⧸ (I ⊔ 𝔪 ^ n)` with
`({α | α.degree < n} \ ord.initialDiagram I) → K`.

Taking lengths (via `MvPowerSeries.length_restrictScalars`) yields the diagram formula for the
Hilbert–Samuel function (`MonomialOrder.hilbertSamuel_eq_ncard_degree_le_sdiff_initialDiagram`):
`I.hilbertSamuel ℓ = ({α : σ →₀ ℕ | α.degree ≤ ℓ} \ ord.initialDiagram I).ncard`.
In particular, `(⊥ : Ideal (MvPowerSeries σ K)).hilbertSamuel ℓ = (card σ + ℓ).choose (card σ)`
(`Ideal.hilbertSamuel_mvPowerSeries_bot`). Combining the diagram formula with the lexicographic
well-foundedness of complement-counting functions of upper sets in `σ →₀ ℕ`
(`Finsupp.isWF_range_toLex_ncard_degree_le_sdiff`) yields Bierstone–Milman's stabilization theorem:
the set of Hilbert–Samuel functions realized by ideals of `MvPowerSeries σ K` is well-founded in
`Lex (ℕ → ℕ∞)` (`MvPowerSeries.isWF_range_toLex_hilbertSamuel`), so every lexicographically — and in
particular every pointwise — antitone sequence of Hilbert–Samuel functions of ideals in
`MvPowerSeries σ K` stabilizes (`MvPowerSeries.exists_hilbertSamuel_eq_of_antitone_lex`,
`MvPowerSeries.exists_hilbertSamuel_eq_of_antitone`).

## Main results

* `MonomialOrder.hilbertSamuel_eq_ncard_degree_le_sdiff_initialDiagram`: `I.hilbertSamuel ℓ`
  counts exponents of degree at most `ℓ` outside `ord.initialDiagram I`.
* `Ideal.hilbertSamuel_mvPowerSeries_bot`: `(⊥ : Ideal (MvPowerSeries σ K)).hilbertSamuel ℓ` equals
  `(Fintype.card σ + ℓ).choose (Fintype.card σ)`.
* `MvPowerSeries.isWF_range_toLex_hilbertSamuel`: the set of Hilbert–Samuel functions realized by
  ideals of `MvPowerSeries σ K` is well-founded in `Lex (ℕ → ℕ∞)`.
* `MvPowerSeries.exists_hilbertSamuel_eq_of_antitone_lex`,
  `MvPowerSeries.exists_hilbertSamuel_eq_of_antitone`: lexicographic and pointwise Hilbert–Samuel
  stabilization for sequences of ideals in `MvPowerSeries σ K`.

## References

* Edward Bierstone and Pierre D. Milman, *Uniformization of analytic spaces*, J. Amer. Math. Soc. 2
  (1989), 801–836, Theorem 5.2.1 (pp. 820–821).
* Edward Bierstone and Pierre D. Milman, *Canonical desingularization in characteristic zero by
  blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), 207–302,
  Corollary 3.20 (p. 239).
-/

public section

open scoped MonomialOrder

namespace MonomialOrder

section HilbertSamuel

variable {σ K : Type*} [Finite σ] [Field K] (ord : MonomialOrder σ)

/-- **Diagram formula for the Hilbert–Samuel function** (Bierstone–Milman, Corollary 3.20): for any
degree-compatible monomial order `ord` on finitely many variables over a field `K`, the
Hilbert–Samuel function of `I : Ideal (MvPowerSeries σ K)` at degree `ℓ` counts the exponents of
total degree at most `ℓ` outside `ord.initialDiagram I`. -/
theorem hilbertSamuel_eq_ncard_degree_le_sdiff_initialDiagram
    (hdeg : Monotone (Finsupp.degree ∘ ord.toSyn.symm))
    (I : Ideal (MvPowerSeries σ K)) (ℓ : ℕ) :
    I.hilbertSamuel ℓ =
      (({α : σ →₀ ℕ | α.degree ≤ ℓ} \ ord.initialDiagram I).ncard : ℕ∞) := by
  rw [Ideal.hilbertSamuel_def, ← MvPowerSeries.length_restrictScalars,
    (ord.quotientSupMaximalIdealPowEquiv hdeg I (ℓ + 1)).length_eq,
    Module.length_pi, Module.length_eq_one K K, mul_one, ENat.card_coe_set_eq]
  simp_rw [Nat.lt_succ_iff]
  exact (Finsupp.finite_of_degree_le ℓ).sdiff.cast_ncard_eq.symm

end HilbertSamuel

end MonomialOrder

namespace Ideal

/-- In finitely many variables over a field `K`, the Hilbert–Samuel function of the zero ideal of
`MvPowerSeries σ K` is the binomial coefficient `(Fintype.card σ + ℓ).choose (Fintype.card σ)`. -/
theorem hilbertSamuel_mvPowerSeries_bot {σ K : Type*} [Fintype σ] [Field K] (ℓ : ℕ) :
    (⊥ : Ideal (MvPowerSeries σ K)).hilbertSamuel ℓ =
      ((Fintype.card σ + ℓ).choose (Fintype.card σ) : ℕ∞) := by
  let _ : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  have _ : WellFoundedGT σ := Finite.wellFounded_of_trans_of_irrefl _
  rw [MonomialOrder.degLex.hilbertSamuel_eq_ncard_degree_le_sdiff_initialDiagram
      Finsupp.DegLex.monotone_degree ⊥ ℓ,
    MonomialOrder.initialDiagram_bot, Set.sdiff_empty, Finsupp.ncard_degree_le]

end Ideal

namespace MvPowerSeries

section Stabilization

variable {σ K : Type*} [Finite σ] [Field K]

/-- **Bierstone–Milman lexicographic well-foundedness for formal power series**: in finitely many
variables over a field `K`, the set of Hilbert–Samuel functions realized by ideals of
`MvPowerSeries σ K` is well-founded in the lexicographic order on `ℕ → ℕ∞`. -/
theorem isWF_range_toLex_hilbertSamuel (σ K : Type*) [Finite σ] [Field K] :
    (Set.range fun I : Ideal (MvPowerSeries σ K) ↦ toLex I.hilbertSamuel).IsWF := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  let _ : LinearOrder σ := LinearOrder.lift' e e.injective
  have _ : WellFoundedGT σ := Finite.wellFounded_of_trans_of_irrefl _
  let castLex : Lex (ℕ → ℕ) → Lex (ℕ → ℕ∞) := fun x ↦ toLex fun ℓ ↦ (ofLex x ℓ : ℕ∞)
  have hcast : StrictMono castLex := by
    rintro x y ⟨m, hm_eq, hm_lt⟩
    exact ⟨m, fun k hk ↦ congrArg Nat.cast (hm_eq k hk), Nat.cast_lt.mpr hm_lt⟩
  refine ((Finsupp.isWF_range_toLex_ncard_degree_le_sdiff σ).isPWO.image_of_monotone
    hcast.monotone).isWF.mono ?_
  rintro _ ⟨I, rfl⟩
  refine ⟨toLex fun ℓ ↦ ({α : σ →₀ ℕ | α.degree ≤ ℓ} \
      MonomialOrder.degLex.initialDiagram I).ncard,
    ⟨⟨MonomialOrder.degLex.initialDiagram I,
      MonomialOrder.degLex.isUpperSet_initialDiagram I⟩, rfl⟩, ?_⟩
  apply ofLex.injective
  funext ℓ
  simpa [castLex] using
    (MonomialOrder.degLex.hilbertSamuel_eq_ncard_degree_le_sdiff_initialDiagram
      Finsupp.DegLex.monotone_degree I ℓ).symm

/-- **Lexicographic Hilbert–Samuel stabilization** (Bierstone–Milman, Theorem 5.2.1): for any
sequence of ideals `I : ℕ → Ideal (MvPowerSeries σ K)` in finitely many variables over a field,
if `j ↦ toLex (I j).hilbertSamuel` is antitone, then `j ↦ (I j).hilbertSamuel` is eventually
constant. -/
theorem exists_hilbertSamuel_eq_of_antitone_lex (I : ℕ → Ideal (MvPowerSeries σ K))
    (h : Antitone fun j ↦ toLex (I j).hilbertSamuel) :
    ∃ j₀, ∀ j, j₀ ≤ j → (I j).hilbertSamuel = (I j₀).hilbertSamuel := by
  have hwf : (Set.range fun j ↦ toLex (I j).hilbertSamuel).IsWF :=
    (isWF_range_toLex_hilbertSamuel σ K).mono (Set.range_subset_iff.mpr fun j ↦ ⟨I j, rfl⟩)
  obtain ⟨j₀, hj₀⟩ := hwf.min_mem (Set.range_nonempty _)
  dsimp only at hj₀
  refine ⟨j₀, fun j hj ↦ ?_⟩
  have heq : toLex (I j).hilbertSamuel = toLex (I j₀).hilbertSamuel :=
    eq_of_le_of_not_lt (h hj) (hj₀ ▸ hwf.not_lt_min (Set.range_nonempty _) ⟨j, rfl⟩)
  exact congrArg ofLex heq

/-- **Pointwise Hilbert–Samuel stabilization**: for any sequence of ideals
`I : ℕ → Ideal (MvPowerSeries σ K)` in finitely many variables over a field, if
`j ↦ (I j).hilbertSamuel` is antitone, then `j ↦ (I j).hilbertSamuel` is eventually constant. -/
theorem exists_hilbertSamuel_eq_of_antitone (I : ℕ → Ideal (MvPowerSeries σ K))
    (h : Antitone fun j ↦ (I j).hilbertSamuel) :
    ∃ j₀, ∀ j, j₀ ≤ j → (I j).hilbertSamuel = (I j₀).hilbertSamuel :=
  exists_hilbertSamuel_eq_of_antitone_lex I (Pi.toLex_monotone.comp_antitone h)

end Stabilization

end MvPowerSeries

section Examples

-- The singular quotient `K⟦x⟧ / (x²)` has `H(0) = 1` and `H(ℓ + 1) = 2` for every `ℓ`.
example {K : Type*} [Field K] (ℓ : ℕ) :
    (Ideal.span {(MvPowerSeries.X (0 : Fin 1) : MvPowerSeries (Fin 1) K) ^ 2}).hilbertSamuel
      (ℓ + 1) = 2 := by
  have hspan :
      (Ideal.span {(MvPowerSeries.X (0 : Fin 1) : MvPowerSeries (Fin 1) K) ^ 2}) =
        Ideal.span ((fun α ↦ MvPowerSeries.monomial α (1 : K)) ''
          {Finsupp.single (0 : Fin 1) 2}) := by
    rw [Set.image_singleton, MvPowerSeries.X_pow_eq]
  rw [MonomialOrder.degLex.hilbertSamuel_eq_ncard_degree_le_sdiff_initialDiagram
      Finsupp.DegLex.monotone_degree, hspan, MonomialOrder.initialDiagram_span_monomial,
    Set.biUnion_singleton]
  have hset : {α : Fin 1 →₀ ℕ | α.degree ≤ ℓ + 1} \ Set.Ici (Finsupp.single (0 : Fin 1) 2) =
      {(0 : Fin 1 →₀ ℕ), Finsupp.single (0 : Fin 1) 1} := by
    ext α
    simp [Finsupp.degree_eq_sum, Finsupp.le_def, Finsupp.ext_iff]
    omega
  rw [hset, Set.ncard_pair (by
    intro h
    have := congrArg (fun f : Fin 1 →₀ ℕ ↦ f 0) h
    simp at this)]
  norm_cast

-- Without realizability by ideals, `ℕ → ℕ∞` admits infinite strictly lex-decreasing sequences, so
-- `MvPowerSeries.isWF_range_toLex_hilbertSamuel` is genuinely non-trivial.
example : ∃ f : ℕ → ℕ → ℕ∞, StrictAnti fun j ↦ toLex (f j) := by
  refine ⟨fun j ℓ ↦ if j ≤ ℓ then 1 else 0, fun a b hab ↦ ⟨a, fun k hk ↦ ?_, ?_⟩⟩
  · have hka : ¬ a ≤ k := not_le.mpr hk
    have hkb : ¬ b ≤ k := not_le.mpr (hk.trans hab)
    simp [hka, hkb]
  · have hab' : ¬ b ≤ a := not_le.mpr hab
    simp [hab']

end Examples
