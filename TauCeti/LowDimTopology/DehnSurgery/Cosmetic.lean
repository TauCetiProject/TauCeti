/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Sphere
public import TauCeti.Geometry.Manifold.SmoothEmbedding.SmoothAmbientIsotopy.Basic
public import TauCeti.KnotTheory.TorusKnot
public import TauCeti.LowDimTopology.DehnSurgery.Orientation
public import TauCeti.LowDimTopology.DehnSurgery.SeifertFraming

/-!
# Cosmetic surgeries

Let `Φ` be a solid torus neighbourhood of a knot in an oriented `3`-manifold `X`. Two Dehn
fillings of the knot exterior, along slopes `s₁` and `s₂`, are oriented compatibly with `X` on the
open exterior (`TauCeti.DehnFilling.IsOrientationCompatible`). Following Bleiler (Kirby's problem
1.81), the pair of slopes is

* **purely cosmetic** (`TauCeti.IsSolidTorusNeighborhood.IsPurelyCosmetic`) when the two filled
  manifolds are homeomorphic by an orientation-preserving homeomorphism, and
* **chirally cosmetic** (`TauCeti.IsSolidTorusNeighborhood.IsChirallyCosmetic`) when they are
  homeomorphic by an orientation-reversing homeomorphism.

Both are properties of the slope pair on one knot exterior, not of two abstract manifolds. Reversing
the orientation of `X` changes neither (`TauCeti.IsSolidTorusNeighborhood.isPurelyCosmetic_neg_iff`,
`TauCeti.IsSolidTorusNeighborhood.isChirallyCosmetic_neg_iff`), and both are symmetric in the two
slopes. Every slope with a filling is purely cosmetic with itself; the meridian always is, through
the trivial filling (`TauCeti.IsSolidTorusNeighborhood.isPurelyCosmetic_meridian`).

For knots in the unit sphere `S³` of `ℝ⁴`, slopes are read as surgery coefficients in `ℚ ∪ {∞}`
through the preferred framing (`TauCeti.IsSolidTorusNeighborhood.preferredFramedBoundaryTorus`).
The coefficient depends on whether `Φ` preserves orientation, up to the sign `r ↦ -r`, and every
statement below is invariant under that sign. They are recorded as propositions, not proved.

* **The cosmetic surgery conjecture** (`TauCeti.CosmeticSurgeryConjecture`), part (A) of Kirby's
  problem 1.81 in Gordon's form for knots in `S³`: a nontrivial knot has no purely cosmetic pair of
  distinct slopes. For the unknot the `1 / n`-surgeries are all `S³`, so the nontriviality
  hypothesis cannot be dropped.
* **Ni and Wu's theorem** (`TauCeti.NiWuCosmeticSurgeryTheorem`): two distinct purely cosmetic
  slopes on a nontrivial knot have opposite coefficients `r` and `-r`, and if `r = p / q` in
  lowest terms then `q² ≡ -1` modulo `p`. Their theorem also asserts the vanishing of the
  Ozsváth–Szabó invariant `τ`, which is not stated here.
* **Hanselman's theorem** (`TauCeti.HanselmanCosmeticSurgeryTheorem`): two distinct purely cosmetic
  slopes on a nontrivial knot have coefficients `{2, -2}` or `{1 / q, -1 / q}` for a positive
  integer `q`. It implies the two parts of Ni and Wu's theorem stated here
  (`TauCeti.HanselmanCosmeticSurgeryTheorem.niWuCosmeticSurgeryTheorem`).
* **Mathieu's chirally cosmetic surgeries** (`TauCeti.MathieuChirallyCosmeticTheorem`): on the
  right-handed trefoil either the slopes with coefficients `9` and `9 / 2` or those with
  coefficients `-9` and `-9 / 2` are chirally cosmetic, depending on the sign the framing of `Φ`
  introduces. The two coefficients of each pair are distinct and not opposite, so the cosmetic
  surgery conjecture does not extend to chirally cosmetic pairs.

## Main definitions

* `TauCeti.IsSolidTorusNeighborhood.IsPurelyCosmetic`: two slopes have Dehn fillings that are
  homeomorphic by an orientation-preserving homeomorphism.
* `TauCeti.IsSolidTorusNeighborhood.IsChirallyCosmetic`: two slopes have Dehn fillings that are
  homeomorphic by an orientation-reversing homeomorphism.
* `TauCeti.CosmeticSurgeryConjecture`, `TauCeti.NiWuCosmeticSurgeryTheorem`,
  `TauCeti.HanselmanCosmeticSurgeryTheorem`, `TauCeti.MathieuChirallyCosmeticTheorem`: the
  statements above, as propositions.

## Main results

* `TauCeti.IsSolidTorusNeighborhood.IsPurelyCosmetic.symm`,
  `TauCeti.IsSolidTorusNeighborhood.IsChirallyCosmetic.symm`: both relations are symmetric.
* `TauCeti.IsSolidTorusNeighborhood.isPurelyCosmetic_neg_iff`,
  `TauCeti.IsSolidTorusNeighborhood.isChirallyCosmetic_neg_iff`: they do not depend on the
  orientation of the ambient manifold.
* `TauCeti.CosmeticSurgeryConjecture.eq_of_isPurelyCosmetic`,
  `TauCeti.NiWuCosmeticSurgeryTheorem.exists_value_eq_neg`,
  `TauCeti.HanselmanCosmeticSurgeryTheorem.exists_value_eq_neg`,
  `TauCeti.MathieuChirallyCosmeticTheorem.isChirallyCosmetic`: applying the statements.
* `TauCeti.CosmeticSurgeryConjecture.hanselmanCosmeticSurgeryTheorem` and
  `TauCeti.HanselmanCosmeticSurgeryTheorem.niWuCosmeticSurgeryTheorem`: the conjecture implies
  Hanselman's theorem, which implies Ni and Wu's.

## References

* R. Kirby (ed.), *Problems in Low-Dimensional Topology*, Problem 1.81, in *Geometric Topology*,
  AMS/IP Stud. Adv. Math. 2.2 (1997).
* C. McA. Gordon, *Dehn surgery on knots*, in *Proceedings of the International Congress of
  Mathematicians, Kyoto 1990*, Math. Soc. Japan (1991).
* Y. Ni, Z. Wu, *Cosmetic surgeries on knots in `S³`*, J. Reine Angew. Math. 706 (2015), 1–17,
  Theorem 1.2.
* J. Hanselman, *Heegaard Floer homology and cosmetic surgeries in `S³`*, J. Eur. Math. Soc. 25
  (2023), Theorem 2.
* Y. Mathieu, *Closed 3-manifolds unchanged by Dehn surgery*, J. Knot Theory Ramifications 1
  (1992).
* K. Ichihara, T. Ito, T. Saito, *Chirally cosmetic surgeries and Casson invariants*, Tokyo J.
  Math. 44 (2021), for the chirally cosmetic surgeries on the `(2, 2k + 1)` torus knots.
-/

public section

open CategoryTheory Limits Metric Topology
open scoped Manifold

namespace TauCeti

namespace IsSolidTorusNeighborhood

variable {X : Type} [TopologicalSpace X] [T2Space X] {f : Circle → X} {Φ : SolidTorus → X}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ChartedSpace E X] {d : ℕ}

/-- Two slopes `s₁`, `s₂` on the boundary torus of the exterior of a knot in a space `X` oriented
by `o` are **purely cosmetic** when there are Dehn fillings `Y₁`, `Y₂` of the exterior along them,
oriented by orientations compatible with `o`, and a homeomorphism `Y₁ ≃ₜ Y₂` preserving these
orientations (Kirby's problem 1.81). -/
def IsPurelyCosmetic (h : IsSolidTorusNeighborhood f Φ) (o : HomologicalOrientation X E d)
    (s₁ s₂ : Slope h.framedBoundaryTorus.H) : Prop :=
  ∃ (Y₁ Y₂ : Type) (_ : TopologicalSpace Y₁) (_ : T2Space Y₁) (_ : ChartedSpace E Y₁)
    (_ : TopologicalSpace Y₂) (_ : T2Space Y₂) (_ : ChartedSpace E Y₂)
    (F₁ : DehnFilling h s₁ Y₁) (F₂ : DehnFilling h s₂ Y₂)
    (o₁ : HomologicalOrientation Y₁ E d) (o₂ : HomologicalOrientation Y₂ E d) (e : Y₁ ≃ₜ Y₂),
    F₁.IsOrientationCompatible o o₁ ∧ F₂.IsOrientationCompatible o o₂ ∧
      o₂.comap e.isOpenEmbedding = o₁

/-- Two slopes `s₁`, `s₂` on the boundary torus of the exterior of a knot in a space `X` oriented
by `o` are **chirally cosmetic** when there are Dehn fillings `Y₁`, `Y₂` of the exterior along them,
oriented by orientations compatible with `o`, and a homeomorphism `Y₁ ≃ₜ Y₂` reversing these
orientations (Kirby's problem 1.81). -/
def IsChirallyCosmetic (h : IsSolidTorusNeighborhood f Φ) (o : HomologicalOrientation X E d)
    (s₁ s₂ : Slope h.framedBoundaryTorus.H) : Prop :=
  ∃ (Y₁ Y₂ : Type) (_ : TopologicalSpace Y₁) (_ : T2Space Y₁) (_ : ChartedSpace E Y₁)
    (_ : TopologicalSpace Y₂) (_ : T2Space Y₂) (_ : ChartedSpace E Y₂)
    (F₁ : DehnFilling h s₁ Y₁) (F₂ : DehnFilling h s₂ Y₂)
    (o₁ : HomologicalOrientation Y₁ E d) (o₂ : HomologicalOrientation Y₂ E d) (e : Y₁ ≃ₜ Y₂),
    F₁.IsOrientationCompatible o o₁ ∧ F₂.IsOrientationCompatible o o₂ ∧
      o₂.comap e.isOpenEmbedding = -o₁

/-- Unfolding `TauCeti.IsSolidTorusNeighborhood.IsPurelyCosmetic`. -/
theorem isPurelyCosmetic_iff (h : IsSolidTorusNeighborhood f Φ) (o : HomologicalOrientation X E d)
    (s₁ s₂ : Slope h.framedBoundaryTorus.H) :
    h.IsPurelyCosmetic o s₁ s₂ ↔
      ∃ (Y₁ Y₂ : Type) (_ : TopologicalSpace Y₁) (_ : T2Space Y₁) (_ : ChartedSpace E Y₁)
        (_ : TopologicalSpace Y₂) (_ : T2Space Y₂) (_ : ChartedSpace E Y₂)
        (F₁ : DehnFilling h s₁ Y₁) (F₂ : DehnFilling h s₂ Y₂)
        (o₁ : HomologicalOrientation Y₁ E d) (o₂ : HomologicalOrientation Y₂ E d) (e : Y₁ ≃ₜ Y₂),
        F₁.IsOrientationCompatible o o₁ ∧ F₂.IsOrientationCompatible o o₂ ∧
          o₂.comap e.isOpenEmbedding = o₁ :=
  Iff.rfl

/-- Unfolding `TauCeti.IsSolidTorusNeighborhood.IsChirallyCosmetic`. -/
theorem isChirallyCosmetic_iff (h : IsSolidTorusNeighborhood f Φ)
    (o : HomologicalOrientation X E d) (s₁ s₂ : Slope h.framedBoundaryTorus.H) :
    h.IsChirallyCosmetic o s₁ s₂ ↔
      ∃ (Y₁ Y₂ : Type) (_ : TopologicalSpace Y₁) (_ : T2Space Y₁) (_ : ChartedSpace E Y₁)
        (_ : TopologicalSpace Y₂) (_ : T2Space Y₂) (_ : ChartedSpace E Y₂)
        (F₁ : DehnFilling h s₁ Y₁) (F₂ : DehnFilling h s₂ Y₂)
        (o₁ : HomologicalOrientation Y₁ E d) (o₂ : HomologicalOrientation Y₂ E d) (e : Y₁ ≃ₜ Y₂),
        F₁.IsOrientationCompatible o o₁ ∧ F₂.IsOrientationCompatible o o₂ ∧
          o₂.comap e.isOpenEmbedding = -o₁ :=
  Iff.rfl

variable {h : IsSolidTorusNeighborhood f Φ} {o : HomologicalOrientation X E d}
  {s₁ s₂ : Slope h.framedBoundaryTorus.H}
  {Y₁ Y₂ : Type} [TopologicalSpace Y₁] [T2Space Y₁] [ChartedSpace E Y₁]
  [TopologicalSpace Y₂] [T2Space Y₂] [ChartedSpace E Y₂]

/-- Two Dehn fillings with compatible orientations and an orientation-preserving homeomorphism
between them make their slopes purely cosmetic. -/
theorem IsPurelyCosmetic.intro (F₁ : DehnFilling h s₁ Y₁) (F₂ : DehnFilling h s₂ Y₂)
    {o₁ : HomologicalOrientation Y₁ E d} {o₂ : HomologicalOrientation Y₂ E d}
    (hF₁ : F₁.IsOrientationCompatible o o₁) (hF₂ : F₂.IsOrientationCompatible o o₂)
    (e : Y₁ ≃ₜ Y₂) (he : o₂.comap e.isOpenEmbedding = o₁) : h.IsPurelyCosmetic o s₁ s₂ :=
  ⟨Y₁, Y₂, _, _, _, _, _, _, F₁, F₂, o₁, o₂, e, hF₁, hF₂, he⟩

/-- Two Dehn fillings with compatible orientations and an orientation-reversing homeomorphism
between them make their slopes chirally cosmetic. -/
theorem IsChirallyCosmetic.intro (F₁ : DehnFilling h s₁ Y₁) (F₂ : DehnFilling h s₂ Y₂)
    {o₁ : HomologicalOrientation Y₁ E d} {o₂ : HomologicalOrientation Y₂ E d}
    (hF₁ : F₁.IsOrientationCompatible o o₁) (hF₂ : F₂.IsOrientationCompatible o o₂)
    (e : Y₁ ≃ₜ Y₂) (he : o₂.comap e.isOpenEmbedding = -o₁) : h.IsChirallyCosmetic o s₁ s₂ :=
  ⟨Y₁, Y₂, _, _, _, _, _, _, F₁, F₂, o₁, o₂, e, hF₁, hF₂, he⟩

/-- Being purely cosmetic is symmetric in the two slopes. -/
theorem IsPurelyCosmetic.symm (hc : h.IsPurelyCosmetic o s₁ s₂) : h.IsPurelyCosmetic o s₂ s₁ := by
  obtain ⟨Y₁, Y₂, _, _, _, _, _, _, F₁, F₂, o₁, o₂, e, hF₁, hF₂, he⟩ := hc
  exact IsPurelyCosmetic.intro F₂ F₁ hF₂ hF₁ e.symm (by rw [← he, o₂.comap_symm_comap])

/-- A pair of slopes is purely cosmetic in either order or in neither. -/
theorem isPurelyCosmetic_comm : h.IsPurelyCosmetic o s₁ s₂ ↔ h.IsPurelyCosmetic o s₂ s₁ :=
  ⟨IsPurelyCosmetic.symm, IsPurelyCosmetic.symm⟩

/-- Being chirally cosmetic is symmetric in the two slopes. -/
theorem IsChirallyCosmetic.symm (hc : h.IsChirallyCosmetic o s₁ s₂) :
    h.IsChirallyCosmetic o s₂ s₁ := by
  obtain ⟨Y₁, Y₂, _, _, _, _, _, _, F₁, F₂, o₁, o₂, e, hF₁, hF₂, he⟩ := hc
  refine IsChirallyCosmetic.intro F₂ F₁ hF₂ hF₁ e.symm ?_
  rw [neg_eq_iff_eq_neg.mp he.symm, HomologicalOrientation.comap_neg, o₂.comap_symm_comap]

/-- A pair of slopes is chirally cosmetic in either order or in neither. -/
theorem isChirallyCosmetic_comm : h.IsChirallyCosmetic o s₁ s₂ ↔ h.IsChirallyCosmetic o s₂ s₁ :=
  ⟨IsChirallyCosmetic.symm, IsChirallyCosmetic.symm⟩

/-- Being purely cosmetic does not depend on the orientation of the ambient space. -/
@[simp]
theorem isPurelyCosmetic_neg_iff : h.IsPurelyCosmetic (-o) s₁ s₂ ↔ h.IsPurelyCosmetic o s₁ s₂ := by
  suffices key : ∀ o : HomologicalOrientation X E d,
      h.IsPurelyCosmetic o s₁ s₂ → h.IsPurelyCosmetic (-o) s₁ s₂ from
    ⟨fun hc ↦ neg_neg o ▸ key _ hc, key o⟩
  rintro o ⟨Y₁, Y₂, _, _, _, _, _, _, F₁, F₂, o₁, o₂, e, hF₁, hF₂, he⟩
  exact IsPurelyCosmetic.intro F₁ F₂ ((F₁.isOrientationCompatible_neg_iff o o₁).mpr hF₁)
    ((F₂.isOrientationCompatible_neg_iff o o₂).mpr hF₂) e
    (by rw [HomologicalOrientation.comap_neg, he])

/-- Being chirally cosmetic does not depend on the orientation of the ambient space. -/
@[simp]
theorem isChirallyCosmetic_neg_iff :
    h.IsChirallyCosmetic (-o) s₁ s₂ ↔ h.IsChirallyCosmetic o s₁ s₂ := by
  suffices key : ∀ o : HomologicalOrientation X E d,
      h.IsChirallyCosmetic o s₁ s₂ → h.IsChirallyCosmetic (-o) s₁ s₂ from
    ⟨fun hc ↦ neg_neg o ▸ key _ hc, key o⟩
  rintro o ⟨Y₁, Y₂, _, _, _, _, _, _, F₁, F₂, o₁, o₂, e, hF₁, hF₂, he⟩
  exact IsChirallyCosmetic.intro F₁ F₂ ((F₁.isOrientationCompatible_neg_iff o o₁).mpr hF₁)
    ((F₂.isOrientationCompatible_neg_iff o o₂).mpr hF₂) e
    (by rw [HomologicalOrientation.comap_neg, he])

/-- A slope having a Dehn filling with a compatible orientation is purely cosmetic with itself,
through the identity. -/
theorem IsPurelyCosmetic.refl (F : DehnFilling h s₁ Y₁) {o₁ : HomologicalOrientation Y₁ E d}
    (hF : F.IsOrientationCompatible o o₁) : h.IsPurelyCosmetic o s₁ s₁ :=
  IsPurelyCosmetic.intro F F hF hF (Homeomorph.refl Y₁)
    ((o₁.comap_congr _ IsOpenEmbedding.id (Homeomorph.refl_apply Y₁)).trans o₁.comap_id)

/-- The meridian is purely cosmetic with itself, through the trivial filling, the ambient space
itself. -/
theorem isPurelyCosmetic_meridian (h : IsSolidTorusNeighborhood f Φ)
    (o : HomologicalOrientation X E d) :
    h.IsPurelyCosmetic o h.framedBoundaryTorus.meridian h.framedBoundaryTorus.meridian :=
  IsPurelyCosmetic.refl h.meridianDehnFilling (h.isOrientationCompatible_meridianDehnFilling o)

end IsSolidTorusNeighborhood

/-! ### Cosmetic surgeries on knots in `S³` -/

/-- **The cosmetic surgery conjecture** for knots in `S³` (Gordon; part (A) of Kirby's problem
1.81): a knot `K : S¹ → S³` that is not smoothly ambient isotopic to the unknot has no purely
cosmetic pair of distinct slopes, whatever its solid torus neighbourhood `Φ` and the orientation
`o` of `S³`.

Hanselman's theorem (`TauCeti.HanselmanCosmeticSurgeryTheorem`) restricts the possible pairs to
those of coefficients `{2, -2}` and `{1 / q, -1 / q}`; the conjecture itself is recorded, not
proved. -/
def CosmeticSurgeryConjecture : Prop :=
  ∀ (o : HomologicalOrientation (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
      (EuclideanSpace ℝ (Fin 3)) 3)
    (K : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
    (Φ : SolidTorus → sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) (h : IsSolidTorusNeighborhood K Φ)
    (s₁ s₂ : Slope h.framedBoundaryTorus.H),
    ¬ SmoothEmbedding.SmoothAmbientIsotopic K unknot → h.IsPurelyCosmetic o s₁ s₂ → s₁ = s₂

/-- **Ni and Wu's theorem on cosmetic surgeries**: if two distinct slopes on the exterior of a knot
`K : S¹ → S³` that is not smoothly ambient isotopic to the unknot are purely cosmetic, then their
coefficients in the preferred framing are `r` and `-r` for some rational number `r`, and writing
`r = p / q` in lowest terms, `q² ≡ -1` modulo `p`.

The preferred framing is defined because the reduced integral homology of `S³` vanishes in degrees
`1` and `2` (`TauCeti.isZero_reducedSingularHomologyFunctor_one_sphere_euclideanSpace_fin_four` and
`TauCeti.isZero_reducedSingularHomologyFunctor_two_sphere_euclideanSpace_fin_four`). Hanselman's
theorem implies it (`TauCeti.HanselmanCosmeticSurgeryTheorem.niWuCosmeticSurgeryTheorem`). -/
def NiWuCosmeticSurgeryTheorem : Prop :=
  ∀ (o : HomologicalOrientation (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
      (EuclideanSpace ℝ (Fin 3)) 3)
    (K : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
    (Φ : SolidTorus → sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) (h : IsSolidTorusNeighborhood K Φ)
    (s₁ s₂ : Slope h.framedBoundaryTorus.H),
    ¬ SmoothEmbedding.SmoothAmbientIsotopic K unknot → h.IsPurelyCosmetic o s₁ s₂ → s₁ ≠ s₂ →
      ∃ r : ℚ,
        (h.preferredFramedBoundaryTorus
          (isZero_reducedSingularHomologyFunctor_one_sphere_euclideanSpace_fin_four _)
          (isZero_reducedSingularHomologyFunctor_two_sphere_euclideanSpace_fin_four _)).value s₁ =
            r ∧
        (h.preferredFramedBoundaryTorus
          (isZero_reducedSingularHomologyFunctor_one_sphere_euclideanSpace_fin_four _)
          (isZero_reducedSingularHomologyFunctor_two_sphere_euclideanSpace_fin_four _)).value s₂ =
            ((-r : ℚ) : OnePoint ℚ) ∧
        (r.den : ℤ) ^ 2 ≡ -1 [ZMOD r.num]

/-- **Hanselman's theorem on cosmetic surgeries**: if two distinct slopes on the exterior of a knot
`K : S¹ → S³` that is not smoothly ambient isotopic to the unknot are purely cosmetic, then their
coefficients in the preferred framing are `r` and `-r`, where `r = ±2` or `r = ±1 / q` for a
positive integer `q`. Hanselman also shows that `K` has genus `2` in the first case, and bounds `q`
in the second; genus is not available here, so these parts are not stated. -/
def HanselmanCosmeticSurgeryTheorem : Prop :=
  ∀ (o : HomologicalOrientation (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
      (EuclideanSpace ℝ (Fin 3)) 3)
    (K : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
    (Φ : SolidTorus → sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) (h : IsSolidTorusNeighborhood K Φ)
    (s₁ s₂ : Slope h.framedBoundaryTorus.H),
    ¬ SmoothEmbedding.SmoothAmbientIsotopic K unknot → h.IsPurelyCosmetic o s₁ s₂ → s₁ ≠ s₂ →
      ∃ r : ℚ,
        (h.preferredFramedBoundaryTorus
          (isZero_reducedSingularHomologyFunctor_one_sphere_euclideanSpace_fin_four _)
          (isZero_reducedSingularHomologyFunctor_two_sphere_euclideanSpace_fin_four _)).value s₁ =
            r ∧
        (h.preferredFramedBoundaryTorus
          (isZero_reducedSingularHomologyFunctor_one_sphere_euclideanSpace_fin_four _)
          (isZero_reducedSingularHomologyFunctor_two_sphere_euclideanSpace_fin_four _)).value s₂ =
            ((-r : ℚ) : OnePoint ℚ) ∧
        (|r| = 2 ∨ ∃ q : ℕ, 0 < q ∧ |r| = (q : ℚ)⁻¹)

/-- **Mathieu's chirally cosmetic surgeries on the trefoil**: on the exterior of the right-handed
trefoil, for every solid torus neighbourhood `Φ` and orientation `o` of `S³`, either the slopes
with coefficients `9` and `9 / 2` or those with coefficients `-9` and `-9 / 2` in the preferred
framing are chirally cosmetic. Which pair holds depends on whether `Φ` preserves orientation: the
pair `-9`, `-9 / 2` gives the coefficients of the same two surgeries for the mirrored framing.

The two coefficients are distinct and not opposite, so these slopes are not identified by any
symmetry of the knot exterior. -/
def MathieuChirallyCosmeticTheorem : Prop :=
  ∀ (o : HomologicalOrientation (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
      (EuclideanSpace ℝ (Fin 3)) 3)
    (Φ : SolidTorus → sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    (h : IsSolidTorusNeighborhood rightHandedTrefoil Φ),
    h.IsChirallyCosmetic o
        ((FramedBoundaryTorus.slopeEquiv (h.preferredFramedBoundaryTorus
          (isZero_reducedSingularHomologyFunctor_one_sphere_euclideanSpace_fin_four _)
          (isZero_reducedSingularHomologyFunctor_two_sphere_euclideanSpace_fin_four _))).symm
            ((9 : ℚ) : OnePoint ℚ))
        ((FramedBoundaryTorus.slopeEquiv (h.preferredFramedBoundaryTorus
          (isZero_reducedSingularHomologyFunctor_one_sphere_euclideanSpace_fin_four _)
          (isZero_reducedSingularHomologyFunctor_two_sphere_euclideanSpace_fin_four _))).symm
            ((9 / 2 : ℚ) : OnePoint ℚ)) ∨
      h.IsChirallyCosmetic o
        ((FramedBoundaryTorus.slopeEquiv (h.preferredFramedBoundaryTorus
          (isZero_reducedSingularHomologyFunctor_one_sphere_euclideanSpace_fin_four _)
          (isZero_reducedSingularHomologyFunctor_two_sphere_euclideanSpace_fin_four _))).symm
            ((-9 : ℚ) : OnePoint ℚ))
        ((FramedBoundaryTorus.slopeEquiv (h.preferredFramedBoundaryTorus
          (isZero_reducedSingularHomologyFunctor_one_sphere_euclideanSpace_fin_four _)
          (isZero_reducedSingularHomologyFunctor_two_sphere_euclideanSpace_fin_four _))).symm
            ((-9 / 2 : ℚ) : OnePoint ℚ))

/-- Applying the cosmetic surgery conjecture: purely cosmetic slopes on the exterior of a knot in
`S³` that is not smoothly ambient isotopic to the unknot are equal. -/
theorem CosmeticSurgeryConjecture.eq_of_isPurelyCosmetic (hC : CosmeticSurgeryConjecture)
    {o : HomologicalOrientation (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
      (EuclideanSpace ℝ (Fin 3)) 3}
    {K : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)}
    {Φ : SolidTorus → sphere (0 : EuclideanSpace ℝ (Fin 4)) 1} {h : IsSolidTorusNeighborhood K Φ}
    {s₁ s₂ : Slope h.framedBoundaryTorus.H}
    (hK : ¬ SmoothEmbedding.SmoothAmbientIsotopic K unknot) (hc : h.IsPurelyCosmetic o s₁ s₂) :
    s₁ = s₂ :=
  hC o K Φ h s₁ s₂ hK hc

section Applications

variable {o : HomologicalOrientation (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    (EuclideanSpace ℝ (Fin 3)) 3}
  {K : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)}
  {Φ : SolidTorus → sphere (0 : EuclideanSpace ℝ (Fin 4)) 1} {h : IsSolidTorusNeighborhood K Φ}
  {s₁ s₂ : Slope h.framedBoundaryTorus.H}
  (h₁ : IsZero ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) 1).obj
    (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))))
  (h₂ : IsZero ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) 2).obj
    (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))))
include h₁ h₂

/-- Applying Ni and Wu's theorem: distinct purely cosmetic slopes on the exterior of a knot in
`S³` that is not smoothly ambient isotopic to the unknot have opposite coefficients `r`, `-r` in
the preferred framing, defined from any proofs that the reduced integral homology of `S³`
vanishes in degrees `1` and `2`, and `q² ≡ -1` modulo `p` for `r = p / q` in lowest terms. -/
theorem NiWuCosmeticSurgeryTheorem.exists_value_eq_neg (hNW : NiWuCosmeticSurgeryTheorem)
    (hK : ¬ SmoothEmbedding.SmoothAmbientIsotopic K unknot) (hc : h.IsPurelyCosmetic o s₁ s₂)
    (hne : s₁ ≠ s₂) :
    ∃ r : ℚ, (h.preferredFramedBoundaryTorus h₁ h₂).value s₁ = r ∧
      (h.preferredFramedBoundaryTorus h₁ h₂).value s₂ = ((-r : ℚ) : OnePoint ℚ) ∧
      (r.den : ℤ) ^ 2 ≡ -1 [ZMOD r.num] :=
  hNW o K Φ h s₁ s₂ hK hc hne

/-- Applying Hanselman's theorem: distinct purely cosmetic slopes on the exterior of a knot in
`S³` that is not smoothly ambient isotopic to the unknot have opposite coefficients `r`, `-r` in
the preferred framing, with `r = ±2` or `r = ±1 / q` for a positive integer `q`. -/
theorem HanselmanCosmeticSurgeryTheorem.exists_value_eq_neg
    (hH : HanselmanCosmeticSurgeryTheorem)
    (hK : ¬ SmoothEmbedding.SmoothAmbientIsotopic K unknot) (hc : h.IsPurelyCosmetic o s₁ s₂)
    (hne : s₁ ≠ s₂) :
    ∃ r : ℚ, (h.preferredFramedBoundaryTorus h₁ h₂).value s₁ = r ∧
      (h.preferredFramedBoundaryTorus h₁ h₂).value s₂ = ((-r : ℚ) : OnePoint ℚ) ∧
      (|r| = 2 ∨ ∃ q : ℕ, 0 < q ∧ |r| = (q : ℚ)⁻¹) :=
  hH o K Φ h s₁ s₂ hK hc hne

end Applications

/-- Applying Mathieu's theorem: on the exterior of the right-handed trefoil, the slopes with
coefficients `9` and `9 / 2`, or those with coefficients `-9` and `-9 / 2`, in the preferred
framing are chirally cosmetic. -/
theorem MathieuChirallyCosmeticTheorem.isChirallyCosmetic (hM : MathieuChirallyCosmeticTheorem)
    (o : HomologicalOrientation (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
      (EuclideanSpace ℝ (Fin 3)) 3)
    {Φ : SolidTorus → sphere (0 : EuclideanSpace ℝ (Fin 4)) 1}
    (h : IsSolidTorusNeighborhood rightHandedTrefoil Φ)
    (h₁ : IsZero ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) 1).obj
      (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))))
    (h₂ : IsZero ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) 2).obj
      (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)))) :
    h.IsChirallyCosmetic o ((h.preferredFramedBoundaryTorus h₁ h₂).slopeEquiv.symm (9 : ℚ))
        ((h.preferredFramedBoundaryTorus h₁ h₂).slopeEquiv.symm (9 / 2 : ℚ)) ∨
      h.IsChirallyCosmetic o ((h.preferredFramedBoundaryTorus h₁ h₂).slopeEquiv.symm (-9 : ℚ))
        ((h.preferredFramedBoundaryTorus h₁ h₂).slopeEquiv.symm (-9 / 2 : ℚ)) :=
  hM o Φ h

/-- The cosmetic surgery conjecture implies Hanselman's theorem, whose hypotheses it shows can
never be met. -/
theorem CosmeticSurgeryConjecture.hanselmanCosmeticSurgeryTheorem
    (hC : CosmeticSurgeryConjecture) : HanselmanCosmeticSurgeryTheorem :=
  fun o K Φ h s₁ s₂ hK hc hne ↦ absurd (hC o K Φ h s₁ s₂ hK hc) hne

/-- Hanselman's theorem implies the two parts of Ni and Wu's theorem stated here: the coefficients
`±2` and `±1 / q` of a purely cosmetic pair satisfy `q² ≡ -1` modulo `p`. -/
theorem HanselmanCosmeticSurgeryTheorem.niWuCosmeticSurgeryTheorem
    (hH : HanselmanCosmeticSurgeryTheorem) : NiWuCosmeticSurgeryTheorem := by
  intro o K Φ h s₁ s₂ hK hc hne
  obtain ⟨r, hr₁, hr₂, hr⟩ := hH.exists_value_eq_neg
    (isZero_reducedSingularHomologyFunctor_one_sphere_euclideanSpace_fin_four _)
    (isZero_reducedSingularHomologyFunctor_two_sphere_euclideanSpace_fin_four _) hK hc hne
  refine ⟨r, hr₁, hr₂, ?_⟩
  rw [Int.modEq_iff_dvd, ← abs_dvd]
  rcases hr with hr | ⟨q, hq, hr⟩
  · have hnum : |r.num| = 2 := by rw [← Rat.num_abs_eq_abs_num, hr]; rfl
    have hden : r.den = 1 := by rw [← Rat.den_abs_eq_den, hr]; rfl
    rw [hnum, hden]
    norm_num
  · have hnum : |r.num| = 1 := by rw [← Rat.num_abs_eq_abs_num, hr, Rat.inv_natCast_num_of_pos hq]
    rw [hnum]
    exact one_dvd _

end TauCeti
