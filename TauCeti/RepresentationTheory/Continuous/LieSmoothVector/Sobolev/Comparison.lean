/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Ordered
public import TauCeti.RepresentationTheory.Continuous.LieSmoothVector.Enveloping
public import TauCeti.RepresentationTheory.Continuous.LieSmoothVector.Seminorm

/-!
# Word seminorms are bounded by Sobolev seminorms

Let `π` be a continuous representation of a real Lie group `G` and `X₁, …, X_m` a spanning
family of its Lie algebra of left-invariant derivations. The word seminorm
`P_k(v) = ∑_{|w| ≤ k} ‖dπ(X_w) v‖` sums over all words of length at most `k`, the Sobolev seminorm
`Q_k(v) = (∑_{|α| ≤ k} ‖dπ(X^α) v‖²)^{1/2}` only over the ordered monomials
`X^α = X₁^{α₁} ⋯ X_m^{α_m}`, and `Q_k ≤ P_k` is
`ContRepresentation.sobolevSeminorm_le_wordSeminorm`. This file proves the converse bound
`P_k ≤ C_k Q_k` (`ContRepresentation.exists_wordSeminorm_le_mul_sobolevSeminorm`).

The operator `dπ(X_w)` of a word is the action of the monomial `X_w` of the universal enveloping
algebra (`ContRepresentation.wordAction_eq_lieSmoothVectorsEnvelopingAction`). By the spanning
half of the Poincaré–Birkhoff–Witt theorem
(`TauCeti.UniversalEnvelopingAlgebra.span_orderedPBWMonomials_eq_pbwFiltration`), `X_w` is a real
linear combination of ordered monomials of degree at most `k`, and these are exactly the monomials
`X^α` with `α` in `SobolevIndex m k`
(`TauCeti.UniversalEnvelopingAlgebra.range_pbwMonomial_monomialWord_eq_orderedPBWMonomials`). So
in any algebra receiving `U(L)`, the image of a word of length at most `k` is a combination of the
images of the ordered monomials of degree at most `k`
(`TauCeti.UniversalEnvelopingAlgebra.prod_map_mem_span_monomialWord`). For the operators
`dπ(X_i)` the comparison of the word and Sobolev seminorms along a family of operators
(`Seminorm.exists_endWordSeminorm_le_mul_endSobolevSeminorm`) then gives the bound.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.range_pbwMonomial_monomialWord_eq_orderedPBWMonomials`: the
  ordered PBW monomials of degree at most `k` are the monomials `X^α` with `|α| ≤ k`.
* `TauCeti.UniversalEnvelopingAlgebra.prod_map_mem_span_monomialWord`: under an algebra map out
  of `U(L)`, words of length at most `k` are combinations of ordered monomials of degree at most
  `k`.
* `ContRepresentation.wordAction_eq_lieSmoothVectorsEnvelopingAction`: `dπ(X_w)` is the action of
  the PBW monomial `X_w`.
* `ContRepresentation.exists_wordSeminorm_le_mul_sobolevSeminorm`: `P_k ≤ C_k Q_k`.

## References

* J. Bernstein, B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*,
  Israel J. Math. 199 (2014), §2.4.2–§2.4.3.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti.UniversalEnvelopingAlgebra

/-- The ordered PBW monomials of degree at most `k` in a family `X₁, …, X_m` are exactly the
monomials `X^α = X₁^{α₁} ⋯ X_m^{α_m}` of the exponent vectors `α` in `SobolevIndex m k`. -/
theorem range_pbwMonomial_monomialWord_eq_orderedPBWMonomials (R : Type*) (L : Type*)
    [CommRing R] [LieRing L] [LieAlgebra R L] {m : ℕ} (X : Fin m → L) (k : ℕ) :
    Set.range (fun α : SobolevIndex m k ↦ pbwMonomial R L X (monomialWord α.exponent)) =
      orderedPBWMonomials R L X k := by
  ext a
  refine ⟨?_, ?_⟩
  · rintro ⟨α, rfl⟩
    refine pbwMonomial_mem_orderedPBWMonomials R L X (pairwise_monomialWord _) ?_
    rw [length_monomialWord]
    simpa only [SobolevIndex.exponent_apply] using α.property
  · intro ha
    obtain ⟨word, hsorted, hlength, rfl⟩ := (mem_orderedPBWMonomials_iff R L X).1 ha
    obtain ⟨α, hα⟩ := exists_sobolevIndex_monomialWord_eq hsorted hlength
    exact ⟨α, congrArg (pbwMonomial R L X) hα⟩

/-- **Words are combinations of ordered monomials in any representation of `U(L)`.** For an
algebra map `φ` out of `U(L)` and a spanning family `X₁, …, X_m` of `L`, write `D i = φ(X_i)`.
The product `D_w = D_{i₁} ⋯ D_{iₙ}` along a word `w` of length at most `k` is an `R`-combination
of the ordered monomials `D^α = D₁^{α₁} ⋯ D_m^{α_m}` with `|α| ≤ k`. -/
theorem prod_map_mem_span_monomialWord (R : Type*) {L A : Type*} [CommRing R] [LieRing L]
    [LieAlgebra R L] [Ring A] [Algebra R A] (φ : _root_.UniversalEnvelopingAlgebra R L →ₐ[R] A)
    {m : ℕ} (X : Fin m → L) (hX : Submodule.span R (Set.range X) = ⊤) {k : ℕ}
    {w : List (Fin m)} (hw : w.length ≤ k) :
    (w.map fun i ↦ φ (_root_.UniversalEnvelopingAlgebra.ι R (X i))).prod ∈ Submodule.span R
      (Set.range fun α : SobolevIndex m k ↦
        ((monomialWord α.exponent).map fun i ↦
          φ (_root_.UniversalEnvelopingAlgebra.ι R (X i))).prod) := by
  have hφ : ∀ w : List (Fin m), φ (pbwMonomial R L X w) =
      (w.map fun i ↦ φ (_root_.UniversalEnvelopingAlgebra.ι R (X i))).prod := fun w ↦ by
    simp [pbwMonomial_def, map_list_prod, List.map_map, Function.comp_def]
  have hmem : pbwMonomial R L X w ∈ Submodule.span R
      (Set.range fun α : SobolevIndex m k ↦ pbwMonomial R L X (monomialWord α.exponent)) := by
    rw [range_pbwMonomial_monomialWord_eq_orderedPBWMonomials,
      span_orderedPBWMonomials_eq_pbwFiltration R L X hX]
    exact pbwFiltration_mono R L hw (pbwMonomial_mem_pbwFiltration R L X w)
  have h := Submodule.apply_mem_span_image_of_mem_span φ.toLinearMap hmem
  rw [← Set.range_comp] at h
  simpa only [AlgHom.toLinearMap_apply, Function.comp_def, hφ] using h

end TauCeti.UniversalEnvelopingAlgebra

namespace ContRepresentation

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **The operator of a word is the action of its PBW monomial**: `dπ(X_w)` is the action of
`X_w = ι(X_{i₁}) ⋯ ι(X_{iₙ})` on the smooth vectors. -/
theorem wordAction_eq_lieSmoothVectorsEnvelopingAction {R : Type*} [Ring R] [Module R V]
    [Algebra ℝ R] [IsScalarTower ℝ R V] [ContinuousConstSMul R V]
    {π : ContRepresentation R G V} {ι : Type*} (X : ι → LeftInvariantDerivation I G)
    (w : List ι) :
    wordAction I π X w =
      lieSmoothVectorsEnvelopingAction I π
        (UniversalEnvelopingAlgebra.pbwMonomial ℝ (LeftInvariantDerivation I G) X w) := by
  induction w with
  | nil => rw [wordAction_nil, UniversalEnvelopingAlgebra.pbwMonomial_nil, map_one]
  | cons i w ih =>
    rw [wordAction_cons, ih, UniversalEnvelopingAlgebra.pbwMonomial_cons, map_mul,
      lieSmoothVectorsEnvelopingAction_ι]

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] [SMulCommClass ℝ 𝕜 V]
  [NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 V] {π : ContRepresentation 𝕜 G V} {m : ℕ}

/-- **The word seminorm is bounded by a multiple of the Sobolev seminorm.** For a spanning family
`X₁, …, X_m` of the Lie algebra and every order `k` there is `C_k` with `P_k ≤ C_k Q_k`. -/
theorem exists_wordSeminorm_le_mul_sobolevSeminorm (X : Fin m → LeftInvariantDerivation I G)
    (hX : Submodule.span ℝ (Set.range X) = ⊤) (k : ℕ) :
    ∃ C : ℝ, ∀ v : lieSmoothVectors I π,
      wordSeminorm I π X k v ≤ C * sobolevSeminorm I π X k v := by
  simp only [wordSeminorm_eq_endWordSeminorm, sobolevSeminorm_eq_endSobolevSeminorm]
  refine Seminorm.exists_endWordSeminorm_le_mul_endSobolevSeminorm _ _ fun _ hw ↦
    Submodule.span_le_restrictScalars ℝ 𝕜 _ ?_
  simpa only [lieSmoothVectorsEnvelopingAction_ι] using
    UniversalEnvelopingAlgebra.prod_map_mem_span_monomialWord ℝ
      (lieSmoothVectorsEnvelopingAction I π) X hX hw

end ContRepresentation
