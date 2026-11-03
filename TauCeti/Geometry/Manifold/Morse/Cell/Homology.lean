/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.MorseInequalities
public import TauCeti.Geometry.Manifold.Morse.RelCWComplex

/-!
# Relative homology across a critical level of a Morse function

Let `f` be a Morse function and `c` a value with a compact band `f⁻¹[c - δ, c + δ]`. Milnor's
cell attachment theorem in CW form (`TauCeti.IsMorse.exists_relCWComplex_sublevel_deformation`)
gives a small `ε > 0` and a finite relative CW complex `C` over the lower sublevel
`M_{c-ε} = {f ≤ c - ε}`, with one `m`-cell for each critical point of index `m` on the level `c`,
onto which the upper sublevel `M_{c+ε}` strong deformation retracts. Since the deformation fixes
`C ⊇ M_{c-ε}`, the relative singular homology of the sublevel pair
`TauCeti.sublevelPair f : (M_{c+ε}, M_{c-ε})` is the relative homology of the CW pair
`(C, M_{c-ε})`, by the map induced by the inclusion of pairs
(`TauCeti.IsMorse.exists_relCWComplex_isIso_singularHomologyMap_sublevelPair`).

This gives the local form of the Morse inequalities across one critical level
(`TauCeti.IsMorse.exists_isZero_and_finrank_le_singularHomology_sublevelPair`):
`Hₙ(M_{c+ε}, M_{c-ε})` vanishes when no critical point of the level has index `n`, for
coefficients in any abelian category with coproducts, and over a division ring it is
finite-dimensional, of dimension at most the number of critical points of index `n` on the level
times the dimension of the coefficients. In particular, if every critical point on the level has
index at most `d`, the relative homology of the sublevel pair is concentrated in degrees at most
`d` (`TauCeti.IsMorse.exists_isZero_singularHomology_sublevelPair_of_manifoldMorseIndex_le`).

## Main results

* `TauCeti.IsMorse.exists_relCWComplex_isIso_singularHomologyMap_sublevelPair`: across a
  critical level, the inclusion of a finite CW pair with one cell for each critical point, of
  dimension its index, induces isomorphisms on relative homology with the sublevel pair.
* `TauCeti.IsMorse.exists_isZero_and_finrank_le_singularHomology_sublevelPair`: vanishing in
  degrees carrying no critical point, and the weak Morse inequality.
* `TauCeti.IsMorse.exists_isZero_singularHomology_sublevelPair_of_manifoldMorseIndex_le`:
  vanishing above a bound on the indices of the critical points on the level.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.2 and Section 5.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Theorem 2.35.
-/

public section

noncomputable section

open CategoryTheory Limits Module Set Topology Topology.RelCWComplex
open scoped ContDiff Manifold

universe u v w

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] {f : M → ℝ} {c δ : ℝ}

/-- **The relative homology across a critical level is cellular.** Let `f` be a Morse function and
`c` a value with a compact band `f⁻¹[c - δ, c + δ]`. For some `0 < ε ≤ δ` there is a finite
relative CW complex `C` over `{f ≤ c - ε}`, whose `m`-cells correspond to the critical points of
index `m` on the level `c`, such that for every coefficient object the inclusion of pairs
`(C, {f ≤ c - ε}) ⟶ ({f ≤ c + ε}, {f ≤ c - ε})` induces isomorphisms on relative singular
homology. -/
theorem IsMorse.exists_relCWComplex_isIso_singularHomologyMap_sublevelPair
    (hf : IsMorse I f) (hδ : 0 < δ) (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ))) :
    ∃ ε, ∃ hε : 0 < ε, ε ≤ δ ∧ ∃ (C : Set M) (_ : RelCWComplex C {x | f x ≤ c - ε})
      (_ : RelCWComplex.Finite C) (hC : C ⊆ {x | f x ≤ c + ε}),
      (∀ m, Nonempty (cell C m ≃
        {p : ↥(criticalPoints I f ∩ f ⁻¹' {c}) // manifoldMorseIndex I f p = m})) ∧
      ∀ {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Preadditive A]
        [CategoryWithHomology A] (R : A) (n : ℕ),
        IsIso ((TopPair.ofInclusion (X := TopCat.of M) (base_subset_complex (C := C))
          ).singularHomologyMap (TopPair.ofInclusionMap (Y := TopCat.of M) _
            (sublevel_mono f (a := c - ε) (b := c + ε) (by linarith))
            (ContinuousMap.inclusion hC) fun _ hx ↦ hx) R n) := by
  obtain ⟨ε, hε, hεδ, C, _, _, hC, hcell, r, -, ⟨G⟩⟩ :=
    hf.exists_relCWComplex_sublevel_deformation hδ hcompact
  exact ⟨ε, hε, hεδ, C, inferInstance, inferInstance, hC, hcell, fun R n ↦
    TopPair.isIso_singularHomologyMap_ofInclusionMap_inclusion_of_homotopyRel
      (X := TopCat.of M) base_subset_complex hC r G R n⟩

/-- **The weak Morse inequalities across a critical level.** Let `f` be a Morse function and `c` a
value with a compact band `f⁻¹[c - δ, c + δ]`. For some `0 < ε ≤ δ`, the relative singular
homology `Hₙ({f ≤ c + ε}, {f ≤ c - ε}; R)`, with coefficients in an object `R` of an abelian
category with coproducts, vanishes when no critical point on the level `c` has index `n`; and with
coefficients in a finite-dimensional module `V` over a division ring it is finite-dimensional, of
dimension at most `dim V` times the number of critical points of index `n` on the level `c`. -/
theorem IsMorse.exists_isZero_and_finrank_le_singularHomology_sublevelPair
    (hf : IsMorse I f) (hδ : 0 < δ) (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ))) :
    ∃ ε, ∃ hε : 0 < ε, ε ≤ δ ∧
      (∀ {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A) (n : ℕ),
        (∀ p ∈ criticalPoints I f ∩ f ⁻¹' {c}, manifoldMorseIndex I f p ≠ n) →
        IsZero ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology R n)) ∧
      ∀ (k : Type u) [DivisionRing k] (V : ModuleCat.{u} k) [Module.Finite k V] (n : ℕ),
        Module.Finite k
            ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology V n :
              ModuleCat k) ∧
          finrank k
              ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology V n :
                ModuleCat k) ≤
            Nat.card {p : ↥(criticalPoints I f ∩ f ⁻¹' {c}) // manifoldMorseIndex I f p = n} *
              finrank k V := by
  -- The deformation is used at two coefficient universes, so we do not go through the
  -- existential isomorphism statement above, whose `ε` depends on the universe.
  obtain ⟨ε, hε, hεδ, C, _, _, hC, hcell, r, -, ⟨G⟩⟩ :=
    hf.exists_relCWComplex_sublevel_deformation hδ hcompact
  refine ⟨ε, hε, hεδ, fun {A} _ _ _ R n hn ↦ ?_, fun k _ V _ n ↦ ?_⟩
  · -- No critical point of index `n` means no `n`-cell.
    have : IsEmpty (cell C n) :=
      (hcell n).some.isEmpty_congr.2 ⟨fun p ↦ hn p.1 p.1.2 p.2⟩
    have : ∀ m, HasExactColimitsOfShape (Discrete (cell C m)) A := fun m ↦
      have : _root_.Finite (cell C m) := FiniteType.finite_cell m
      @hasExactColimitsOfShape_discrete_finite A _ _ Abelian.hasFiniteBiproducts _ _
    have h := isZero_singularHomology_complexBasePair_of_isEmpty_cell C R n
    rw [complexBasePair_eq_ofInclusion] at h
    have hiso := TopPair.isIso_singularHomologyMap_ofInclusionMap_inclusion_of_homotopyRel
      (X := TopCat.of M) base_subset_complex hC r G R n
    exact h.of_iso (@asIso _ _ _ _ _ hiso).symm
  · have : _root_.Finite (cell C n) := FiniteType.finite_cell n
    have hfin := finite_singularHomology_complexBasePair C V n
    have h := finrank_singularHomology_complexBasePair_le C V n
    rw [complexBasePair_eq_ofInclusion] at hfin h
    have hiso := TopPair.isIso_singularHomologyMap_ofInclusionMap_inclusion_of_homotopyRel
      (X := TopCat.of M) base_subset_complex hC r G V n
    refine ⟨Module.Finite.equiv (@asIso _ _ _ _ _ hiso).toLinearEquiv, ?_⟩
    rw [← (@asIso _ _ _ _ _ hiso).toLinearEquiv.finrank_eq, ← Nat.card_congr (hcell n).some]
    exact h

/-- **Vanishing above the indices across a critical level.** Let `f` be a Morse function whose
critical points on the level `c` all have index at most `d`, and let the band `f⁻¹[c - δ, c + δ]`
be compact. For some `0 < ε ≤ δ`, the relative singular homology `Hₙ({f ≤ c + ε}, {f ≤ c - ε}; R)`
vanishes for every `n > d` and every coefficient object `R` of an abelian category with
coproducts. -/
theorem IsMorse.exists_isZero_singularHomology_sublevelPair_of_manifoldMorseIndex_le
    (hf : IsMorse I f) {d : ℕ}
    (hd : ∀ p ∈ criticalPoints I f ∩ f ⁻¹' {c}, manifoldMorseIndex I f p ≤ d) (hδ : 0 < δ)
    (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ))) :
    ∃ ε, ∃ hε : 0 < ε, ε ≤ δ ∧
      ∀ {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A) (n : ℕ), d < n →
        IsZero ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology R n) := by
  obtain ⟨ε, hε, hεδ, hzero, -⟩ :=
    hf.exists_isZero_and_finrank_le_singularHomology_sublevelPair hδ hcompact
  exact ⟨ε, hε, hεδ, fun R n hn ↦ hzero R n fun p hp ↦ by have := hd p hp; omega⟩

end TauCeti
