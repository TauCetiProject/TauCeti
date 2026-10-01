/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Coinvariants
public import TauCeti.RepresentationTheory.Homological.TateCohomology.HerbrandQuotient

/-!
# Tate cohomology of a complete filtered representation

Let `M` be a representation of a finite group `G`, and let `F 0 = ⊤, F 1, F 2, …` be
`G`-stable submodules of `M` that are separated, meaning `⋂ n, F n = 0`, and complete, meaning
that every series `∑ n, x n` with `x n ∈ F n` has a limit `s`, in the sense that
`s - ∑ i < n, x i ∈ F n` for every `n`. Suppose that each `F n` surjects onto a representation
`Q n` with kernel contained in `F (n + 1)`, and that every `Q n` has vanishing Tate cohomology in
degree `0`, respectively `-1`. Then so does `M`. In the main case `F` is a decreasing filtration,
the kernel is exactly `F (n + 1)`, and `Q n` is the graded piece `F n / F (n + 1)`; neither
assumption is needed.

The proof is by successive approximation, using the low-degree descriptions
`H-hat^0(G, M) = Mᴳ / N_G M` and `H-hat^(-1)(G, M) = ker N_G / I_G M`. In degree `0`, an invariant
`m ∈ F n` is a norm modulo `F (n + 1)` because its image in `Q n` is a norm there; the
correction terms `y n ∈ F n` sum to some `s` with `N_G s = m`. In degree `-1`, an element `m` of
norm zero lies in `I_G M` modulo `F (n + 1)` once it lies in `F n`, and `I_G M` is the set of sums
`∑ g, (g • y g - y g)`, so one approximates each of the finitely many coordinates `y g`
separately.

The family `F` is not required to be decreasing, and the quotients `Q n` are not formed as
quotient representations. Instead, each is the target of a surjective morphism `π n` from the
subrepresentation `F n`, whose kernel is contained in `F (n + 1)`. When `F` is decreasing, `Q n`
is thus a quotient of `F n` refining the graded piece `F n / F (n + 1)`; this is how the graded
pieces arise in practice, with kernel exactly `F (n + 1)`, but only the containment is needed.
For finite cyclic `G`, Tate cohomology is two-periodic, so vanishing in degrees `0` and `-1` on
every `Q n` makes `M` cohomologically trivial, with Herbrand quotient `1`.

The motivating application is to the units of a finite Galois extension `L/K` of nonarchimedean
local fields. For a uniformizer `ϖ` of `K` and a Galois-stable lattice `A ⊆ 𝒪[L]`, free over
`𝒪[K][G]`, with `A * A ≤ ϖ • A` (`TauCeti.exists_span_orbit_mul_le_smul`), the subgroups
`1 + ϖ ^ (n + 1) • A` filter an open subgroup of the units of `𝒪[L]`, and each graded piece is
`A / ϖ • A`, free over `(𝒪[K] ⧸ ϖ)[G]`.

## Main results

* `TauCeti.TateCohomology.isZero_tateCohomology_zero_of_filtration`: degree-zero Tate cohomology
  vanishes if it vanishes on every `Q n`.
* `TauCeti.TateCohomology.isZero_tateCohomology_negOne_of_filtration`: degree `-1` Tate cohomology
  vanishes if it vanishes on every `Q n`.
* `TauCeti.TateCohomology.isZero_tateCohomology_of_filtration`: for finite cyclic `G`, all Tate
  cohomology vanishes if it vanishes on every `Q n` in degrees `0` and `-1`.
* `TauCeti.TateCohomology.herbrandQuotient_eq_one_of_filtration`: the Herbrand quotient is then
  `1`.

## References

* J.-P. Serre, *Local Fields*, Chapter IX, §3, Lemma 2 (the cohomology of a complete filtered
  module) and Proposition 3 (the units of a finite Galois extension of local fields).
* J. Neukirch, *Algebraic Number Theory*, Chapter V, Proposition 1.2.
-/

public section

universe u

open CategoryTheory Limits Rep

namespace TauCeti.TateCohomology

variable {R G : Type u} [CommRing R] [Group G] [Fintype G] {M : Rep R G}
  {F : ℕ → Submodule R M} {Q : ℕ → Rep R G} (hF : ∀ n g, F n ≤ (F n).comap (M.ρ g))
  (π : ∀ n, M.subrepresentation (F n) (hF n) ⟶ Q n)

include π in
/-- One step of the degree-zero approximation: an invariant of `F n` is the norm of an element of
`F n` modulo `F (n + 1)`, as soon as `Q n` has vanishing degree-zero Tate cohomology. -/
private theorem exists_sub_norm_mem_succ (hπ : ∀ n, Function.Surjective (π n).hom)
    (hker : ∀ n (x : F n), (π n).hom x = 0 → (x : M) ∈ F (n + 1))
    (hQ : ∀ n, IsZero (tateCohomology (Q n) 0)) (n : ℕ) {m : M} (hm : m ∈ F n)
    (hinv : ∀ g, M.ρ g m = m) : ∃ y ∈ F n, m - M.ρ.norm y ∈ F (n + 1) := by
  set x : F n := ⟨m, hm⟩
  have hq : (π n).hom x ∈ (Q n).ρ.invariants := fun g ↦ by
    rw [← Rep.hom_comm_apply]
    congr 1
    exact Subtype.ext (hinv g)
  have := ModuleCat.subsingleton_of_isZero (hQ n)
  have hzero := (H0π_eq_zero_iff ⟨_, hq⟩).1 (Subsingleton.elim _ _)
  obtain ⟨q, hq'⟩ := (Submodule.mem_comap.1 hzero : (π n).hom x ∈ LinearMap.range _)
  obtain ⟨y, rfl⟩ := hπ n q
  refine ⟨y, y.2, ?_⟩
  -- `Rep.norm_comm` evaluated at `y`; both sides unfold `Rep.norm_apply` and `Rep.hom_comp`.
  have hN : (π n).hom ((M.subrepresentation (F n) (hF n)).ρ.norm y) = (Q n).ρ.norm ((π n).hom y) :=
    congr(($(Rep.norm_comm (π n))).hom y).symm
  have h := hker n (x - (M.subrepresentation (F n) (hF n)).ρ.norm y) <| by
    rw [map_sub, hN, hq']
    exact sub_self _
  simpa [x, Representation.norm] using h

include π in
/-- One step of the degree `-1` approximation: an element of `F n` of norm zero lies in the
coinvariant kernel modulo `F (n + 1)`, with coordinates in `F n`, as soon as `Q n` has vanishing
degree `-1` Tate cohomology. -/
private theorem exists_sub_sum_mem_succ (hπ : ∀ n, Function.Surjective (π n).hom)
    (hker : ∀ n (x : F n), (π n).hom x = 0 → (x : M) ∈ F (n + 1))
    (hQ : ∀ n, IsZero (tateCohomology (Q n) (-1))) (n : ℕ) {m : M} (hm : m ∈ F n)
    (hnorm : M.ρ.norm m = 0) :
    ∃ y : G → M, (∀ g, y g ∈ F n) ∧ m - ∑ g, (M.ρ g (y g) - y g) ∈ F (n + 1) := by
  set x : F n := ⟨m, hm⟩
  have hq : (π n).hom x ∈ LinearMap.ker (Q n).ρ.norm := by
    -- `Rep.norm_comm` evaluated at `x`; both sides unfold `Rep.norm_apply` and `Rep.hom_comp`.
    have hN : (Q n).ρ.norm ((π n).hom x) =
        (π n).hom ((M.subrepresentation (F n) (hF n)).ρ.norm x) :=
      congr(($(Rep.norm_comm (π n))).hom x)
    rw [LinearMap.mem_ker, hN]
    convert map_zero (π n).hom
    exact Subtype.ext (by simpa [Representation.norm] using hnorm)
  have := ModuleCat.subsingleton_of_isZero (hQ n)
  have hzero := (HNegOneπ_eq_zero_iff ⟨_, hq⟩).1 (Subsingleton.elim _ _)
  obtain ⟨z, hz⟩ :=
    Representation.mem_coinvariantsKer_iff_exists_sum.1 (Submodule.mem_comap.1 hzero)
  choose y hy using fun g ↦ hπ n (z g)
  refine ⟨fun g ↦ y g, fun g ↦ (y g).2, ?_⟩
  have h := hker n (x - ∑ g, ((M.subrepresentation (F n) (hF n)).ρ g (y g) - y g)) <| by
    have hρ g : (π n).hom ((M.subrepresentation (F n) (hF n)).ρ g (y g)) = (Q n).ρ g (z g) := by
      rw [Rep.hom_comm_apply, hy]
    simp only [map_sub, map_sum, hρ, hy]
    exact sub_eq_zero.2 hz.symm
  simpa [x] using h

/-- **Degree-zero Tate cohomology of a complete filtered representation.** Let `F` be a separated
and complete family of `G`-stable submodules of `M` with `F 0 = ⊤`, and let `π n` be a
surjection from `F n` onto `Q n` whose kernel lies in `F (n + 1)`. If every `Q n` has vanishing
degree-zero Tate cohomology, so does `M`: every invariant of `M` is a norm. -/
theorem isZero_tateCohomology_zero_of_filtration (hF0 : F 0 = ⊤)
    (hsep : ∀ x : M, (∀ n, x ∈ F n) → x = 0)
    (hcomplete : ∀ x : ℕ → M, (∀ n, x n ∈ F n) →
      ∃ s : M, ∀ n, s - ∑ i ∈ Finset.range n, x i ∈ F n)
    (hπ : ∀ n, Function.Surjective (π n).hom)
    (hker : ∀ n (x : F n), (π n).hom x = 0 → (x : M) ∈ F (n + 1))
    (hQ : ∀ n, IsZero (tateCohomology (Q n) 0)) :
    IsZero (tateCohomology M 0) := by
  refine ModuleCat.isZero_iff_subsingleton.2 ⟨fun a b ↦ ?_⟩
  suffices h : ∀ c : tateCohomology M 0, c = 0 by rw [h a, h b]
  intro c
  induction c using H0_induction_on with | h m => ?_
  rw [H0π_eq_zero_iff]
  have step (n : ℕ) (m : M) : ∃ y : M, m ∈ F n → (∀ g, M.ρ g m = m) →
      y ∈ F n ∧ m - M.ρ.norm y ∈ F (n + 1) := by
    by_cases hm : m ∈ F n ∧ ∀ g, M.ρ g m = m
    · obtain ⟨y, hy, hy'⟩ := exists_sub_norm_mem_succ hF π hπ hker hQ n hm.1 hm.2
      exact ⟨y, fun _ _ ↦ ⟨hy, hy'⟩⟩
    · exact ⟨0, fun h₁ h₂ ↦ (hm ⟨h₁, h₂⟩).elim⟩
  choose Y hY using step
  -- The remainders `r n = m - N (∑ i < n, Y i (r i))` are invariant and lie in `F n`.
  let r : ℕ → M := fun n ↦ Nat.rec (m : M) (fun k r ↦ r - M.ρ.norm (Y k r)) n
  have hr : ∀ n, r n ∈ F n ∧ ∀ g, M.ρ g (r n) = r n := by
    intro n
    induction n with
    | zero => exact ⟨hF0 ▸ Submodule.mem_top, m.2⟩
    | succ n ih =>
      refine ⟨(hY n (r n) ih.1 ih.2).2, fun g ↦ ?_⟩
      -- `r (n + 1)` is `r n - N (Y n (r n))` by the defining recursion.
      change M.ρ g (r n - M.ρ.norm (Y n (r n))) = r n - M.ρ.norm (Y n (r n))
      rw [map_sub, ih.2 g, Representation.self_norm_apply]
  have hrsum : ∀ n, r n = m - M.ρ.norm (∑ i ∈ Finset.range n, Y i (r i)) := by
    intro n
    induction n with
    | zero => simp [r]
    | succ n ih =>
      rw [Finset.sum_range_succ, map_add, ← sub_sub, ← ih]
  obtain ⟨s, hs⟩ := hcomplete (fun n ↦ Y n (r n)) fun n ↦ (hY n (r n) (hr n).1 (hr n).2).1
  refine Submodule.mem_comap.2 ⟨s, (sub_eq_zero.1 (hsep _ fun n ↦ ?_)).symm⟩
  have hN : M.ρ.norm (s - ∑ i ∈ Finset.range n, Y i (r i)) ∈ F n := by
    simpa [Representation.norm] using (F n).sum_mem fun g _ ↦ hF n g (hs n)
  convert sub_mem (hr n).1 hN using 1
  rw [hrsum, map_sub, Submodule.subtype_apply]
  abel

/-- **Degree `-1` Tate cohomology of a complete filtered representation.** Let `F` be a separated
and complete family of `G`-stable submodules of `M` with `F 0 = ⊤`, and let `π n` be a
surjection from `F n` onto `Q n` whose kernel lies in `F (n + 1)`. If every `Q n` has vanishing
degree `-1` Tate cohomology, so does `M`: every element of `M` of norm zero lies in the
coinvariant kernel `I_G M`. -/
theorem isZero_tateCohomology_negOne_of_filtration (hF0 : F 0 = ⊤)
    (hsep : ∀ x : M, (∀ n, x ∈ F n) → x = 0)
    (hcomplete : ∀ x : ℕ → M, (∀ n, x n ∈ F n) →
      ∃ s : M, ∀ n, s - ∑ i ∈ Finset.range n, x i ∈ F n)
    (hπ : ∀ n, Function.Surjective (π n).hom)
    (hker : ∀ n (x : F n), (π n).hom x = 0 → (x : M) ∈ F (n + 1))
    (hQ : ∀ n, IsZero (tateCohomology (Q n) (-1))) :
    IsZero (tateCohomology M (-1)) := by
  refine ModuleCat.isZero_iff_subsingleton.2 ⟨fun a b ↦ ?_⟩
  suffices h : ∀ c : tateCohomology M (-1), c = 0 by rw [h a, h b]
  intro c
  induction c using HNegOne_induction_on with | h m => ?_
  rw [HNegOneπ_eq_zero_iff]
  have step (n : ℕ) (m : M) : ∃ y : G → M, m ∈ F n → M.ρ.norm m = 0 →
      (∀ g, y g ∈ F n) ∧ m - ∑ g, (M.ρ g (y g) - y g) ∈ F (n + 1) := by
    by_cases hm : m ∈ F n ∧ M.ρ.norm m = 0
    · obtain ⟨y, hy, hy'⟩ := exists_sub_sum_mem_succ hF π hπ hker hQ n hm.1 hm.2
      exact ⟨y, fun _ _ ↦ ⟨hy, hy'⟩⟩
    · exact ⟨0, fun h₁ h₂ ↦ (hm ⟨h₁, h₂⟩).elim⟩
  choose Y hY using step
  let D : (G → M) → M := fun y ↦ ∑ g, (M.ρ g (y g) - y g)
  have hD (y : G → M) : M.ρ.norm (D y) = 0 := by
    simp [D, map_sum, Representation.norm_self_apply]
  -- The remainders `r n = m - ∑ i < n, D (Y i (r i))` have norm zero and lie in `F n`.
  let r : ℕ → M := fun n ↦ Nat.rec (m : M) (fun k r ↦ r - D (Y k r)) n
  have hr : ∀ n, r n ∈ F n ∧ M.ρ.norm (r n) = 0 := by
    intro n
    induction n with
    | zero => exact ⟨hF0 ▸ Submodule.mem_top, m.2⟩
    | succ n ih =>
      refine ⟨(hY n (r n) ih.1 ih.2).2, ?_⟩
      -- `r (n + 1)` is `r n - D (Y n (r n))` by the defining recursion.
      change M.ρ.norm (r n - D (Y n (r n))) = 0
      rw [map_sub, ih.2, hD, sub_zero]
  have hrsum : ∀ n, r n = m - ∑ i ∈ Finset.range n, D (Y i (r i)) := by
    intro n
    induction n with
    | zero => simp [r]
    | succ n ih =>
      rw [Finset.sum_range_succ, ← sub_sub, ← ih]
  choose s hs using fun g ↦
    hcomplete (fun n ↦ Y n (r n) g) fun n ↦ (hY n (r n) (hr n).1 (hr n).2).1 g
  -- By separatedness, `m` equals `D s`, which lies in the coinvariant kernel.
  have hmDs : (m : M) = D s := by
    refine sub_eq_zero.1 (hsep _ fun n ↦ ?_)
    have hdiff : D s - ∑ i ∈ Finset.range n, D (Y i (r i)) =
        D fun g ↦ s g - ∑ i ∈ Finset.range n, Y i (r i) g := by
      simp only [D, map_sub, map_sum, Finset.sum_sub_distrib,
        Finset.sum_comm (s := Finset.range n) (t := (Finset.univ : Finset G))]
      abel
    have hmem : D (fun g ↦ s g - ∑ i ∈ Finset.range n, Y i (r i) g) ∈ F n :=
      Submodule.sum_mem _ fun g _ ↦ sub_mem (hF n g (hs g n)) (hs g n)
    convert sub_mem (hr n).1 hmem using 1
    rw [← hdiff, hrsum]
    abel
  refine Submodule.mem_comap.2 ?_
  rw [Submodule.subtype_apply, hmDs]
  exact Representation.mem_coinvariantsKer_iff_exists_sum.2 ⟨s, rfl⟩

/-- **A complete filtered representation of a finite cyclic group is cohomologically trivial if
the quotients `Q n` of the steps `F n` are.** Let `F` be a separated and complete family
of `G`-stable submodules of `M` with `F 0 = ⊤`, and let `π n` be a surjection from `F n` onto
`Q n` whose kernel lies in `F (n + 1)`. If every `Q n` has vanishing Tate cohomology in degrees
`0` and `-1`, then by two-periodicity `M` has vanishing Tate cohomology in every degree. -/
theorem isZero_tateCohomology_of_filtration [IsCyclic G] (hF0 : F 0 = ⊤)
    (hsep : ∀ x : M, (∀ n, x ∈ F n) → x = 0)
    (hcomplete : ∀ x : ℕ → M, (∀ n, x n ∈ F n) →
      ∃ s : M, ∀ n, s - ∑ i ∈ Finset.range n, x i ∈ F n)
    (hπ : ∀ n, Function.Surjective (π n).hom)
    (hker : ∀ n (x : F n), (π n).hom x = 0 → (x : M) ∈ F (n + 1))
    (hQ₀ : ∀ n, IsZero (tateCohomology (Q n) 0))
    (hQ₁ : ∀ n, IsZero (tateCohomology (Q n) (-1))) (k : ℤ) :
    IsZero (tateCohomology M k) := by
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · exact (isZero_tateCohomology_zero_of_filtration hF π hF0 hsep hcomplete hπ hker hQ₀).of_iso
      (Rep.FiniteCyclicGroup.periodicIso M k 0 (by rw [Int.ModEq, hk]; rfl))
  · exact (isZero_tateCohomology_negOne_of_filtration hF π hF0 hsep hcomplete hπ hker hQ₁).of_iso
      (Rep.FiniteCyclicGroup.periodicIso M k (-1) (by rw [Int.ModEq, hk]; rfl))

/-- **The Herbrand quotient of a complete filtered representation.** Under the hypotheses of
`isZero_tateCohomology_of_filtration`, the Herbrand quotient of `M` is `1`. -/
theorem herbrandQuotient_eq_one_of_filtration [IsCyclic G] (hF0 : F 0 = ⊤)
    (hsep : ∀ x : M, (∀ n, x ∈ F n) → x = 0)
    (hcomplete : ∀ x : ℕ → M, (∀ n, x n ∈ F n) →
      ∃ s : M, ∀ n, s - ∑ i ∈ Finset.range n, x i ∈ F n)
    (hπ : ∀ n, Function.Surjective (π n).hom)
    (hker : ∀ n (x : F n), (π n).hom x = 0 → (x : M) ∈ F (n + 1))
    (hQ₀ : ∀ n, IsZero (tateCohomology (Q n) 0))
    (hQ₁ : ∀ n, IsZero (tateCohomology (Q n) (-1))) :
    herbrandQuotient M = 1 := by
  have h k := ModuleCat.subsingleton_of_isZero <|
    isZero_tateCohomology_of_filtration hF π hF0 hsep hcomplete hπ hker hQ₀ hQ₁ k
  rw [herbrandQuotient_def, Nat.card_of_subsingleton (0 : tateCohomology M 0),
    Nat.card_of_subsingleton (0 : tateCohomology M (-1)), Nat.cast_one, div_one]

end TauCeti.TateCohomology
