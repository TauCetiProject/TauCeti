/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Triadic.EnergyGap
public import TauCeti.Combinatorics.Hypergraph.Triadic.TopRegularization

/-!
# Strong top regularization

Top regularization (`Colored3Graph.exists_topRegularOverMostPolyads`) refines the pair palette
of a lower skeleton until a coloring `H` of the triples is top-regular over most polyads, at a
tolerance, exceptional proportion and rank fixed in advance. The complexity it produces depends
on these parameters, so they cannot be chosen as functions of that complexity.

This file proves the strong form, in which the parameters are schedules `η μ : ℕ → ℝ` and
`r : ℕ → ℕ` evaluated at the complexity of a coarse complex. Iterating top regularization
produces complexes `C₀, C₁, …` with the vertex cells of the initial skeleton, each refining the
pair palette of the previous one, where `C_{i+1}` is the top regularization of `C_i` at the
schedules evaluated at `C_i.complexity`. The polyad energy of `H` lies in `[0, 1]`, so for every
`g > 0` some consecutive pair `(C, D) = (C_i, C_{i+1})` with `i ≤ ⌊1 / g⌋₊` has energy gap at
most `g`
(`Colored3Graph.exists_strong_topRegularOverMostPolyads`). The fine complex `D` is then
`(η C.complexity, r C.complexity)`-top-regular off a `μ C.complexity`-proportion of the
triples, and the number of pair colors of `C` is bounded independently of `V` by
`strongTopRegularityBound`. The gap `g` itself is fixed in advance: a gap depending on the
coarse complexity would not bound the number of rounds.

Combined with the transfer of top regularity across a small energy gap
(`Colored3Graph.TopRegularOverMostPolyads.of_polyadEnergy_sub_le`), the coarse complex is
itself top-regular at a fixed tolerance and at the rank `r C.complexity` scheduled at its own
complexity (`Colored3Graph.exists_topRegularOverMostPolyads_scheduledRank`). This is the shape
of the Rödl–Schacht regularity lemma for three-uniform hypergraphs, in which the rank is a
function of the complexity of the partition while the top tolerance is a constant.

## Main definitions

* `TauCeti.strongTopRegularityStep`: the palette bound for one round at any reachable
  complexity.
* `TauCeti.strongTopRegularityBound`: the palette bound for the coarse complex.

## Main results

* `TauCeti.Colored3Graph.exists_strong_topRegularOverMostPolyads`: a coarse complex and a
  palette refinement with energy gap at most `g`, top-regular at the schedules evaluated at the
  coarse complexity.
* `TauCeti.Colored3Graph.exists_topRegularOverMostPolyads_scheduledRank`: top regularity at a
  fixed tolerance and at a rank scheduled at the complexity of the returned complex.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), Theorem 2.3.
* N. Alon, E. Fischer, M. Krivelevich and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000), the strong regularity lemma.
* T. Tao, *Szemerédi's regularity lemma revisited*, Contrib. Discrete Math. 1 (2006), the
  energy-gap stopping argument.
-/

public section

open Finset

namespace TauCeti

variable {κ κ₂ V : Type*} [Fintype V] [DecidableEq V]

/-- The bound on the number of pair colors after one round of strong top regularization. A
complex with `t` vertex cells and `m` pair colors has complexity at most `t + m + t³ m³`, and
top regularization at the schedules evaluated at any such complexity leads to at most this many
pair colors. -/
noncomputable def strongTopRegularityStep (t : ℕ) (η μ : ℕ → ℝ) (r : ℕ → ℕ) (m : ℕ) : ℕ :=
  (range (t + m + t ^ 3 * m ^ 3 + 1)).sup fun n ↦ topRegularRefinementBound t (r n) (η n) (μ n) m

/-- Unfolding lemma for `strongTopRegularityStep`. -/
theorem strongTopRegularityStep_def (t : ℕ) (η μ : ℕ → ℝ) (r : ℕ → ℕ) (m : ℕ) :
    strongTopRegularityStep t η μ r m =
      (range (t + m + t ^ 3 * m ^ 3 + 1)).sup fun n ↦
        topRegularRefinementBound t (r n) (η n) (μ n) m :=
  (rfl)

/-- One round of top regularization, at the schedules evaluated at a complexity reachable from
at most `M` pair colors, is dominated by `strongTopRegularityStep`. -/
theorem topRegularRefinementBound_le_strongTopRegularityStep {t m M n : ℕ} (η μ : ℕ → ℝ)
    (r : ℕ → ℕ) (hm : m ≤ M) (hn : n ≤ t + M + t ^ 3 * M ^ 3) :
    topRegularRefinementBound t (r n) (η n) (μ n) m ≤ strongTopRegularityStep t η μ r M :=
  (topRegularRefinementBound_mono _ _ _ _ hm).trans
    (le_sup (f := fun n ↦ topRegularRefinementBound t (r n) (η n) (μ n) M)
      (mem_range.2 (Nat.lt_succ_of_le hn)))

/-- `strongTopRegularityStep` never lowers the number of pair colors. -/
theorem le_strongTopRegularityStep (t : ℕ) (η μ : ℕ → ℝ) (r : ℕ → ℕ) (m : ℕ) :
    m ≤ strongTopRegularityStep t η μ r m :=
  (le_topRegularRefinementBound _ _ _ _ m).trans
    (topRegularRefinementBound_le_strongTopRegularityStep η μ r (n := 0) le_rfl (Nat.zero_le _))

/-- The bound on the number of pair colors of the coarse complex in strong top regularization,
starting from `m` pair colors over `t` vertex cells: at most `⌊1 / g⌋₊` rounds precede an energy
gap of at most `g`. -/
noncomputable def strongTopRegularityBound (t : ℕ) (g : ℝ) (η μ : ℕ → ℝ) (r : ℕ → ℕ) (m : ℕ) :
    ℕ :=
  (strongTopRegularityStep t η μ r)^[⌊1 / g⌋₊] m

/-- Unfolding lemma for `strongTopRegularityBound`. -/
theorem strongTopRegularityBound_def (t : ℕ) (g : ℝ) (η μ : ℕ → ℝ) (r : ℕ → ℕ) (m : ℕ) :
    strongTopRegularityBound t g η μ r m = (strongTopRegularityStep t η μ r)^[⌊1 / g⌋₊] m :=
  (rfl)

namespace Colored3Graph

variable [DecidableEq κ] (H : Colored3Graph κ V)

/-- **Strong top regularization.** Let `g > 0`, and let `η`, `μ` be positive schedules and `r` a
rank schedule. Every lower skeleton `S` has a refinement of its pair palette, selected as a
triadic complex `C` with all its polyads, together with a further palette refinement `D` along
`f`, both with the vertex cells of `S`, such that the polyad energy gap of `H` from `C` to `D` is
at most `g` and `H` is `(η C.complexity, r C.complexity)`-top-regular over all polyads of `D`
outside a `μ C.complexity`-proportion of the injective triples. The number of pair colors of `C`
is at most `strongTopRegularityBound #S.vertexPart.parts g η μ r (Fintype.card κ₂)`, and that of
`D` is bounded by top regularization at the schedules evaluated at `C.complexity`. -/
theorem exists_strong_topRegularOverMostPolyads [Fintype κ] [Fintype κ₂] (S : PairSkeleton3 κ₂ V)
    {g : ℝ} (hg : 0 < g) {η μ : ℕ → ℝ} (hη : ∀ n, 0 < η n) (hμ : ∀ n, 0 < μ n) (r : ℕ → ℕ) :
    ∃ (C D : TriadicComplex3 V) (π : Fin C.pairColorCount → κ₂)
      (f : Fin D.pairColorCount → Fin C.pairColorCount),
      C.pairColorCount ≤
        strongTopRegularityBound #S.vertexPart.parts g η μ r (Fintype.card κ₂) ∧
      D.pairColorCount ≤ topRegularRefinementBound #S.vertexPart.parts (r C.complexity)
        (η C.complexity) (μ C.complexity) C.pairColorCount ∧
      C.skeleton.vertexPart = S.vertexPart ∧ D.skeleton.vertexPart = S.vertexPart ∧
      (∀ p, π (C.skeleton.pairColors.color p) = S.pairColors.color p) ∧
      (∀ c, π (C.skeleton.pairColors.rev c) = S.pairColors.rev (π c)) ∧
      (∀ p, f (D.skeleton.pairColors.color p) = C.skeleton.pairColors.color p) ∧
      (∀ c, f (D.skeleton.pairColors.rev c) = C.skeleton.pairColors.rev (f c)) ∧
      C.polyads = univ ∧ D.polyads = univ ∧
      H.TopRegularOverMostPolyads D (η C.complexity) (μ C.complexity) (r C.complexity) ∧
      H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g := by
  -- Run rounds of top regularization from `S`, each at the schedules evaluated at the current
  -- coarse complexity. A round whose energy gap exceeds `g` replaces the coarse complex by its
  -- refinement; as the energy lies in `[0, 1]`, a round within the first `⌊1 / g⌋₊ + 1` stops.
  set t := #S.vertexPart.parts
  set step := strongTopRegularityStep t η μ r
  -- The admissible coarse complexes: palette refinements of `S` selecting all their polyads.
  let Coarse (C : TriadicComplex3 V) : Prop :=
    C.skeleton.vertexPart = S.vertexPart ∧ C.polyads = univ ∧
      ∃ π : Fin C.pairColorCount → κ₂,
        (∀ p, π (C.skeleton.pairColors.color p) = S.pairColors.color p) ∧
        ∀ c, π (C.skeleton.pairColors.rev c) = S.pairColors.rev (π c)
  -- The fine complexes required of a successful round.
  let Fine (C D : TriadicComplex3 V) (f : Fin D.pairColorCount → Fin C.pairColorCount) : Prop :=
    D.pairColorCount ≤ topRegularRefinementBound t (r C.complexity)
        (η C.complexity) (μ C.complexity) C.pairColorCount ∧
      D.skeleton.vertexPart = S.vertexPart ∧
      (∀ p, f (D.skeleton.pairColors.color p) = C.skeleton.pairColors.color p) ∧
      (∀ c, f (D.skeleton.pairColors.rev c) = C.skeleton.pairColors.rev (f c)) ∧
      D.polyads = univ ∧
      H.TopRegularOverMostPolyads D (η C.complexity) (μ C.complexity) (r C.complexity)
  let Good (C : TriadicComplex3 V) : Prop := ∃ (D : TriadicComplex3 V) (f : _), Fine C D f ∧
    H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g
  -- One round from a coarse complex with at most `M` pair colors either stops, or produces a
  -- coarse complex with at most `step M` pair colors and energy larger by more than `g`.
  have advance (M : ℕ) (C : TriadicComplex3 V) (hCM : C.pairColorCount ≤ M) (hC : Coarse C) :
      Good C ∨ ∃ C' : TriadicComplex3 V, C'.pairColorCount ≤ step M ∧ Coarse C' ∧
        H.polyadEnergy C.skeleton + g < H.polyadEnergy C'.skeleton := by
    obtain ⟨hCV, -, π, hπ, hrev⟩ := hC
    obtain ⟨D, f, hDcard, hDV, hf, hfrev, hDpol, hDreg⟩ :=
      H.exists_topRegularOverMostPolyads C.skeleton (hη C.complexity) (hμ C.complexity)
        (r C.complexity)
    rw [Fintype.card_fin, hCV] at hDcard
    have hfine : Fine C D f := ⟨hDcard, hDV.trans hCV, hf, hfrev, hDpol, hDreg⟩
    by_cases hgap : H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g
    · exact Or.inl ⟨D, f, hfine, hgap⟩
    refine Or.inr ⟨D, hDcard.trans (topRegularRefinementBound_le_strongTopRegularityStep η μ r
      hCM ((C.complexity_le).trans ?_)), ⟨hDV.trans hCV, hDpol, π ∘ f, fun p ↦ by simp [hf, hπ],
      fun c ↦ by simp [hfrev, hrev]⟩, by linarith⟩
    rw [hCV]
    gcongr
  -- After `j` rounds without stopping, the energy is at least `j * g`.
  have key (j : ℕ) : (∃ C, C.pairColorCount ≤ step^[j] (Fintype.card κ₂) ∧ Coarse C ∧ Good C) ∨
      ∃ C, C.pairColorCount ≤ step^[j] (Fintype.card κ₂) ∧ Coarse C ∧
        j * g ≤ H.polyadEnergy C.skeleton := by
    induction j with
    | zero =>
      let e := Fintype.equivFin κ₂
      refine Or.inr ⟨⟨_, S.relabel e, univ⟩, le_rfl, ⟨S.relabel_vertexPart e, rfl, e.symm,
        fun p ↦ by simp, fun c ↦ by simp⟩, ?_⟩
      simpa using H.polyadEnergy_nonneg _
    | succ j ih =>
      have hle : step^[j] (Fintype.card κ₂) ≤ step^[j + 1] (Fintype.card κ₂) := by
        rw [Function.iterate_succ_apply']
        exact le_strongTopRegularityStep _ _ _ _ _
      obtain ⟨C, hCcard, hC, hgood⟩ | ⟨C, hCcard, hC, hE⟩ := ih
      · exact Or.inl ⟨C, hCcard.trans hle, hC, hgood⟩
      obtain hgood | ⟨C', hC'card, hC', hE'⟩ := advance _ C hCcard hC
      · exact Or.inl ⟨C, hCcard.trans hle, hC, hgood⟩
      refine Or.inr ⟨C', by rwa [Function.iterate_succ_apply'], hC', ?_⟩
      push_cast
      linarith
  -- After `⌊1 / g⌋₊` rounds, one more round must stop, since the energy is at most one.
  have hK : 1 < (⌊1 / g⌋₊ + 1 : ℕ) * g := by
    rw [← div_lt_iff₀ hg, Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one _
  obtain ⟨C, hCcard, hC, hgood⟩ :
      ∃ C, C.pairColorCount ≤ step^[⌊1 / g⌋₊] (Fintype.card κ₂) ∧ Coarse C ∧ Good C := by
    obtain hgood | ⟨C, hCcard, hC, hE⟩ := key ⌊1 / g⌋₊
    · exact hgood
    obtain hgood | ⟨C', -, -, hE'⟩ := advance _ C hCcard hC
    · exact ⟨C, hCcard, hC, hgood⟩
    push_cast at hK
    linarith [H.polyadEnergy_le_one C'.skeleton]
  obtain ⟨hCV, hCpol, π, hπ, hrev⟩ := hC
  obtain ⟨D, f, ⟨hDcard, hDV, hf, hfrev, hDpol, hDreg⟩, hgap⟩ := hgood
  exact ⟨C, D, π, f, hCcard, hDcard, hCV, hDV, hπ, hrev, hf, hfrev, hCpol, hDpol, hDreg, hgap⟩

/-- **Top regularity at a scheduled rank.** Let `δ > 0`, `ε > 0` and let `r` be a rank schedule.
Every lower skeleton `S` has a refinement of its pair palette, selected as a triadic complex `C`
with all its polyads and the vertex cells of `S`, such that `H` is
`(δ, r C.complexity)`-top-regular over all polyads of `C` outside an `ε`-proportion of the
injective triples. The number of pair colors of `C` is bounded independently of `V`, in terms
of the number of vertex cells and pair colors of `S`, the number of top colors, `δ`, `ε` and
`r`. -/
theorem exists_topRegularOverMostPolyads_scheduledRank [Finite κ] [Fintype κ₂]
    (S : PairSkeleton3 κ₂ V) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (r : ℕ → ℕ) :
    ∃ (C : TriadicComplex3 V) (π : Fin C.pairColorCount → κ₂),
      C.pairColorCount ≤ strongTopRegularityBound #S.vertexPart.parts
        ((ε * δ ^ 2 / (4 * (Nat.card κ + 1))) ^ 2) (fun _ ↦ δ ^ 2 / 2) (fun _ ↦ ε * δ ^ 2 / 4) r
        (Fintype.card κ₂) ∧
      C.skeleton.vertexPart = S.vertexPart ∧
      (∀ p, π (C.skeleton.pairColors.color p) = S.pairColors.color p) ∧
      (∀ c, π (C.skeleton.pairColors.rev c) = S.pairColors.rev (π c)) ∧
      C.polyads = univ ∧ H.TopRegularOverMostPolyads C δ ε (r C.complexity) := by
  have := Fintype.ofFinite κ
  set q : ℝ := (Nat.card κ : ℝ)
  set γ := ε * δ ^ 2 / (4 * (q + 1))
  have hγ : 0 < γ := by positivity
  obtain ⟨C, D, π, f, hCcard, -, hCV, hDV, hπ, hrev, hf, -, hCpol, hDpol, hDreg, hgap⟩ :=
    H.exists_strong_topRegularOverMostPolyads S (pow_pos hγ 2) (η := fun _ ↦ δ ^ 2 / 2)
      (μ := fun _ ↦ ε * δ ^ 2 / 4) (fun _ ↦ by positivity) (fun _ ↦ by positivity) r
  refine ⟨C, π, hCcard, hCV, hπ, hrev, hCpol, ?_⟩
  have hdec {C : TriadicComplex3 V} (h : C.polyads = univ) : C.IsPolyadDecomposition :=
    C.isPolyadDecomposition_iff_ofTriple_mem.2 fun _ ↦ h ▸ mem_univ _
  have hreg := hDreg.of_polyadEnergy_sub_le (hdec hCpol) (hdec hDpol) (hDV.trans hCV.symm).le f
    (fun p ↦ (hf p).symm) hgap (by positivity) hδ (by linarith [pow_pos hδ 2])
  refine hreg.mono le_rfl ?_ le_rfl
  -- The exceptional proportion is at most `(ε δ² / 4 + q γ) / (δ² / 2) ≤ ε`.
  rw [Real.sqrt_sq hγ.le, ← Nat.card_eq_fintype_card, div_le_iff₀ (by nlinarith [pow_pos hδ 2])]
  have hqγ : q * γ ≤ ε * δ ^ 2 / 4 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hε (pow_pos hδ 2)]
  linarith

end Colored3Graph

end TauCeti
