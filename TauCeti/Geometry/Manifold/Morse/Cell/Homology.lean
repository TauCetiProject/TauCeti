/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.AttachedToBase
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.MorseInequalities
public import TauCeti.Geometry.Manifold.Morse.Deformation.Homology
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

Every cell of `C` is attached directly along `M_{c-ε}`, so all cellular differentials of `C`
vanish, and the relative homology is free on the critical points
(`TauCeti.IsMorse.exists_singularHomology_sublevelPair_iso_sigma`): `Hₙ(M_{c+ε}, M_{c-ε}; R)` is
the coproduct of one copy of `R` for each critical point of index `n` on the level `c`, for
coefficients in any abelian category with coproducts. Over a division ring, it has dimension the
number of these critical points times the dimension of the coefficients
(`TauCeti.IsMorse.exists_finrank_singularHomology_sublevelPair_eq`). This is the ordinary Morse
case of the identification of the relative homology across a critical level with the homology of
the critical set shifted by the index. In particular, if every critical point on the level has
index at most `d`, the relative homology of the sublevel pair is concentrated in degrees at most
`d` (`TauCeti.IsMorse.exists_isZero_singularHomology_sublevelPair_of_manifoldMorseIndex_le`).

The width `ε` can be removed: if `a < c < b`, the band `f⁻¹[a, b]` is compact and `c` is its only
critical value, then the collars `f⁻¹[a, c - ε]` and `f⁻¹[c + ε, b]` carry no relative homology,
and the long exact sequences of triples identify `Hₙ(M_b, M_a)` with `Hₙ(M_{c+ε}, M_{c-ε})`
(`TauCeti.IsMorse.nonempty_singularHomology_sublevelPair_iso_sigma` and
`TauCeti.IsMorse.finrank_singularHomology_sublevelPair_eq`). These are the groups
`Hₙ(M_{aⱼ₊₁}, M_{aⱼ})` of a filtration of `M` by sublevels at values `aⱼ` separating the critical
values.

## Main results

* `TauCeti.IsMorse.exists_relCWComplex_isIso_singularHomologyMap_sublevelPair`: across a
  critical level, the inclusion of a finite CW pair with one cell for each critical point, of
  dimension its index, induces isomorphisms on relative homology with the sublevel pair.
* `TauCeti.IsMorse.exists_singularHomology_sublevelPair_iso_sigma` and
  `TauCeti.IsMorse.exists_finrank_singularHomology_sublevelPair_eq`: the relative homology across
  a critical level is free on the critical points of the level, graded by their index.
* `TauCeti.IsMorse.exists_isZero_singularHomology_sublevelPair_of_manifoldMorseIndex_le`:
  vanishing above a bound on the indices of the critical points on the level.
* `TauCeti.IsMorse.nonempty_singularHomology_sublevelPair_iso_sigma` and
  `TauCeti.IsMorse.finrank_singularHomology_sublevelPair_eq`: the same for a compact band with a
  single critical value.

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
  obtain ⟨ε, hε, hεδ, C, _, _, hC, hcell, -, r, -, ⟨G⟩⟩ :=
    hf.exists_relCWComplex_sublevel_deformation hδ hcompact
  exact ⟨ε, hε, hεδ, C, inferInstance, inferInstance, hC, hcell, fun R n ↦
    TopPair.isIso_singularHomologyMap_ofInclusionMap_inclusion_of_homotopyRel
      (X := TopCat.of M) base_subset_complex hC r G R n⟩

/-- **The relative homology across a critical level is free on the critical points.** Let `f` be
a Morse function and `c` a value with a compact band `f⁻¹[c - δ, c + δ]`. For some `0 < ε ≤ δ`,
the relative singular homology `Hₙ({f ≤ c + ε}, {f ≤ c - ε}; R)`, with coefficients in an object
`R` of an abelian category with coproducts, is the coproduct of one copy of `R` for each critical
point of index `n` on the level `c`. In particular it vanishes when no critical point of the level
has index `n`. -/
theorem IsMorse.exists_singularHomology_sublevelPair_iso_sigma
    (hf : IsMorse I f) (hδ : 0 < δ) (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ))) :
    ∃ ε, ∃ hε : 0 < ε, ε ≤ δ ∧
      ∀ {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A) (n : ℕ),
        Nonempty ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology R n ≅
          ∐ fun _ : {p : ↥(criticalPoints I f ∩ f ⁻¹' {c}) // manifoldMorseIndex I f p = n} ↦
            R) := by
  obtain ⟨ε, hε, hεδ, C, _, _, hC, hcell, hfront, r, -, ⟨G⟩⟩ :=
    hf.exists_relCWComplex_sublevel_deformation hδ hcompact
  refine ⟨ε, hε, hεδ, fun {A} _ _ _ R n ↦ ?_⟩
  have : ∀ m, HasExactColimitsOfShape (Discrete (cell C m)) A := fun m ↦
    have : _root_.Finite (cell C m) := FiniteType.finite_cell m
    @hasExactColimitsOfShape_discrete_finite A _ _ Abelian.hasFiniteBiproducts _ _
  -- The CW pair `(C, {f ≤ c - ε})` has the relative homology of the sublevel pair, and its cells
  -- are attached along the base, so its relative homology is free on its cells.
  have h := nonempty_singularHomology_complexBasePair_iso_sigma C R hfront n
  rw [complexBasePair_eq_ofInclusion] at h
  obtain ⟨e⟩ := h
  have hiso := TopPair.isIso_singularHomologyMap_ofInclusionMap_inclusion_of_homotopyRel
    (X := TopCat.of M) base_subset_complex hC r G R n
  exact ⟨(@asIso _ _ _ _ _ hiso).symm ≪≫ e ≪≫
    Sigma.whiskerEquiv (hcell n).some fun _ ↦ Iso.refl R⟩

/-- **The Morse numbers of a critical level.** Let `f` be a Morse function and `c` a value with a
compact band `f⁻¹[c - δ, c + δ]`. For some `0 < ε ≤ δ`, the relative singular homology
`Hₙ({f ≤ c + ε}, {f ≤ c - ε}; V)`, with coefficients in a finite-dimensional module `V` over a
division ring, is finite-dimensional, of dimension `dim V` times the number of critical points of
index `n` on the level `c`. -/
theorem IsMorse.exists_finrank_singularHomology_sublevelPair_eq
    (hf : IsMorse I f) (hδ : 0 < δ) (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ))) :
    ∃ ε, ∃ hε : 0 < ε, ε ≤ δ ∧
      ∀ (k : Type u) [DivisionRing k] (V : ModuleCat.{u} k) [Module.Finite k V] (n : ℕ),
        Module.Finite k
            ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology V n :
              ModuleCat k) ∧
          finrank k
              ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology V n :
                ModuleCat k) =
            Nat.card {p : ↥(criticalPoints I f ∩ f ⁻¹' {c}) // manifoldMorseIndex I f p = n} *
              finrank k V := by
  obtain ⟨ε, hε, hεδ, C, _, _, hC, hcell, hfront, r, -, ⟨G⟩⟩ :=
    hf.exists_relCWComplex_sublevel_deformation hδ hcompact
  refine ⟨ε, hε, hεδ, fun k _ V _ n ↦ ?_⟩
  have : _root_.Finite (cell C n) := FiniteType.finite_cell n
  have hfin := finite_singularHomology_complexBasePair C V n
  have h := finrank_singularHomology_complexBasePair_of_cellFrontier_subset C V hfront n
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
  obtain ⟨ε, hε, hεδ, hiso⟩ := hf.exists_singularHomology_sublevelPair_iso_sigma hδ hcompact
  refine ⟨ε, hε, hεδ, fun R n hn ↦ ?_⟩
  -- No critical point of the level has index `n`, so the coproduct is empty.
  have : IsEmpty {p : ↥(criticalPoints I f ∩ f ⁻¹' {c}) // manifoldMorseIndex I f p = n} :=
    ⟨fun p ↦ by have := hd p.1 p.1.2; omega⟩
  exact ((IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ isEmptyElim)).of_iso (hiso R n).some

/-! ### Bands with a single critical value -/

/-- Around the only critical value `c` of a compact band `f⁻¹[a, b]`, with `a < c < b`, a width
`ε ≤ min (c - a) (b - c)` leaves the collars `f⁻¹[a, c - ε]` and `f⁻¹[c + ε, b]` compact and
without critical points, so that `({f ≤ b}, {f ≤ a})` has the relative homology of
`({f ≤ c + ε}, {f ≤ c - ε})`. -/
private def singularHomologySublevelPairIsoOfCriticalValue (hf : IsMorse I f) {a b ε : ℝ}
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c) (hε : 0 < ε)
    (hεa : ε ≤ c - a) (hεb : ε ≤ b - c) {A : Type*} [Category A] [Abelian A]
    [HasCoproducts.{u} A] (R : A) (n : ℕ) :
    (sublevelPair f (a := a) (b := b) (by linarith)).singularHomology R n ≅
      (sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology R n :=
  have hsub {s t : ℝ} (has : a ≤ s) (htb : t ≤ b) : IsCompact (f ⁻¹' Icc s t) :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.contMDiff.continuous)
      (preimage_mono (Icc_subset_Icc has htb))
  have hreg {s t : ℝ} (has : a ≤ s) (htb : t ≤ b) (hc : c ∉ Icc s t) :
      ∀ x, s ≤ f x → f x ≤ t → mfderiv I 𝓘(ℝ) f x ≠ 0 := fun x hs ht h0 ↦
    hc (hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 h0)
      ⟨has.trans hs, ht.trans htb⟩ ▸ ⟨hs, ht⟩)
  singularHomologySublevelPairIsoOfCollars hf.contMDiff (a := a) (b := b) (by linarith)
    (by linarith) (by linarith) (hsub le_rfl (by linarith)) (hsub (by linarith) le_rfl)
    (hreg le_rfl (by linarith) fun h ↦ by linarith [h.2])
    (hreg (by linarith) le_rfl fun h ↦ by linarith [h.1]) R n

/-- **The relative homology of a band with one critical value is free on its critical points.**
Let `f` be a Morse function and `a < c < b`, such that the band `f⁻¹[a, b]` is compact and `c` is
the only critical value of `f` in `[a, b]`. Then `Hₙ({f ≤ b}, {f ≤ a}; R)`, with coefficients in
an object `R` of an abelian category with coproducts, is the coproduct of one copy of `R` for each
critical point of index `n` on the level `c`. -/
theorem IsMorse.nonempty_singularHomology_sublevelPair_iso_sigma (hf : IsMorse I f) {a b : ℝ}
    (hac : a < c) (hcb : c < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c) {A : Type v} [Category.{w} A]
    [Abelian A] [HasCoproducts.{u} A] (R : A) (n : ℕ) :
    Nonempty ((sublevelPair f (hac.trans hcb).le).singularHomology R n ≅
      ∐ fun _ : {p : ↥(criticalPoints I f ∩ f ⁻¹' {c}) // manifoldMorseIndex I f p = n} ↦ R) := by
  have hδ : 0 < min (c - a) (b - c) := lt_min (by linarith) (by linarith)
  obtain ⟨ε, hε, hεδ, hiso⟩ := hf.exists_singularHomology_sublevelPair_iso_sigma (c := c) hδ
    (hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.contMDiff.continuous)
      (preimage_mono (Icc_subset_Icc (by linarith [min_le_left (c - a) (b - c)])
        (by linarith [min_le_right (c - a) (b - c)]))))
  exact ⟨singularHomologySublevelPairIsoOfCriticalValue hf hcompact hcrit hε
    (hεδ.trans (min_le_left _ _)) (hεδ.trans (min_le_right _ _)) R n ≪≫ (hiso R n).some⟩

/-- **The Morse numbers of a band with one critical value.** Let `f` be a Morse function and
`a < c < b`, such that the band `f⁻¹[a, b]` is compact and `c` is the only critical value of `f` in
`[a, b]`. Then, for a finite-dimensional module `V` over a division ring, `Hₙ({f ≤ b}, {f ≤ a}; V)`
has dimension `dim V` times the number of critical points of index `n` on the level `c`. -/
theorem IsMorse.finrank_singularHomology_sublevelPair_eq (hf : IsMorse I f) {a b : ℝ}
    (hac : a < c) (hcb : c < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c) {k : Type u} [DivisionRing k]
    (V : ModuleCat.{u} k) [Module.Finite k V] (n : ℕ) :
    finrank k ((sublevelPair f (hac.trans hcb).le).singularHomology V n : ModuleCat k) =
      Nat.card {p : ↥(criticalPoints I f ∩ f ⁻¹' {c}) // manifoldMorseIndex I f p = n} *
        finrank k V := by
  have hδ : 0 < min (c - a) (b - c) := lt_min (by linarith) (by linarith)
  obtain ⟨ε, hε, hεδ, hrank⟩ := hf.exists_finrank_singularHomology_sublevelPair_eq (c := c) hδ
    (hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.contMDiff.continuous)
      (preimage_mono (Icc_subset_Icc (by linarith [min_le_left (c - a) (b - c)])
        (by linarith [min_le_right (c - a) (b - c)]))))
  rw [(singularHomologySublevelPairIsoOfCriticalValue hf hcompact hcrit hε
    (hεδ.trans (min_le_left _ _)) (hεδ.trans (min_le_right _ _)) V n).toLinearEquiv.finrank_eq]
  exact (hrank k V n).2

end TauCeti
