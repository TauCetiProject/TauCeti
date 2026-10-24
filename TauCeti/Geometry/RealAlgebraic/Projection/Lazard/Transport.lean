/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Degree.TrailingDegree
public import TauCeti.RingTheory.MvPolynomial.Lazard.Valuation
public import TauCeti.RingTheory.Polynomial.Content
public import TauCeti.Geometry.RealAlgebraic.Projection.Lazard.Basic

/-!
# Coefficient equivalences and Lazard projection

A coefficient ring equivalence transports the Lazard projection of a polynomial family to the
projection of its transported family and basis, up to associates. Leading and trailing
coefficients, discriminants, and resultants commute exactly with the equivalence. Contents
commute only up to associates, since a ring equivalence need not respect the chosen normalized
gcd representatives. The equality is therefore stated in the finite sets of associate classes.

Together with transport of irreducible bases, this permits a change of base-variable order
before applying Lazard lifting. Arbitrary specialization is not covered: it can change degrees,
trailing degrees, irreducibility, and contents.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 5.
-/

public section

open Polynomial

namespace TauCeti

variable {R S : Type*} [CommRing R] [CommRing S]
  [NormalizedGCDMonoid R] [NormalizedGCDMonoid S]

/-- A coefficient ring equivalence transports the Lazard projection exactly at the level of
associate classes. This holds for arbitrary finite families and bases, including zero inputs,
without compatibility between the two normalized gcd structures. -/
theorem image_associatesMk_lazardProjection_image_map_equiv [DecidableEq (Polynomial S)]
    [DecidableEq (Associates S)] (e : R ≃+* S) (F B : Finset (Polynomial R)) :
    ((F.image (Polynomial.map e.toRingHom)).lazardProjection
      (B.image (Polynomial.map e.toRingHom))).image Associates.mk =
        (F.lazardProjection B).image (fun a ↦ Associates.mk (e a)) := by
  classical
  have hc (p : Polynomial R) :
      Associates.mk (p.map e.toRingHom).content = Associates.mk (e p.content) :=
    Associates.mk_eq_mk_iff_associated.mpr associated_content_map_equiv
  have hl (p : Polynomial R) : (p.map e.toRingHom).leadingCoeff = e p.leadingCoeff :=
    leadingCoeff_map_of_injective (f := e.toRingHom) e.injective p
  have ht (p : Polynomial R) : (p.map e.toRingHom).trailingCoeff = e p.trailingCoeff :=
    trailingCoeff_map_of_injective e.injective
  have hd (p : Polynomial R) : (p.map e.toRingHom).discr = e p.discr :=
    discr_map_of_natDegree_eq _ (natDegree_map_eq_of_injective e.injective p)
  have hr (p q : Polynomial R) :
      resultant (p.map e.toRingHom) (q.map e.toRingHom) = e (resultant p q) := by
    rw [natDegree_map_eq_of_injective e.injective, natDegree_map_eq_of_injective e.injective,
      resultant_map_map]
    rfl
  have hinj := Polynomial.map_injective e.toRingHom e.injective
  -- Compare generators in both directions. Content needs associate classes; all other
  -- generators commute exactly, and injectivity preserves the off-diagonal pairs.
  ext a
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases Finset.mem_lazardProjection.mp hq with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩ |
      ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, p', hp', hne, rfl⟩
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨f.content, Finset.content_mem_lazardProjection hf, (hc f).symm⟩
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨f.leadingCoeff, Finset.leadingCoeff_mem_lazardProjection hf,
        congrArg Associates.mk (hl f).symm⟩
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨f.trailingCoeff, Finset.trailingCoeff_mem_lazardProjection hf,
        congrArg Associates.mk (ht f).symm⟩
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨f.discr, Finset.discr_mem_lazardProjection hf, congrArg Associates.mk (hd f).symm⟩
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hp'
      exact ⟨resultant f g, Finset.resultant_mem_lazardProjection hf hg
        (fun h ↦ hne (congrArg _ h)), congrArg Associates.mk (hr f g).symm⟩
  · rintro ⟨q, hq, rfl⟩
    rcases Finset.mem_lazardProjection.mp hq with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩ |
      ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, p', hp', hne, rfl⟩
    · exact ⟨(p.map e.toRingHom).content,
        Finset.content_mem_lazardProjection (Finset.mem_image_of_mem _ hp), hc p⟩
    · exact ⟨(p.map e.toRingHom).leadingCoeff,
        Finset.leadingCoeff_mem_lazardProjection (Finset.mem_image_of_mem _ hp),
        congrArg Associates.mk (hl p)⟩
    · exact ⟨(p.map e.toRingHom).trailingCoeff,
        Finset.trailingCoeff_mem_lazardProjection (Finset.mem_image_of_mem _ hp),
        congrArg Associates.mk (ht p)⟩
    · exact ⟨(p.map e.toRingHom).discr,
        Finset.discr_mem_lazardProjection (Finset.mem_image_of_mem _ hp),
        congrArg Associates.mk (hd p)⟩
    · exact ⟨resultant (p.map e.toRingHom) (p'.map e.toRingHom),
        Finset.resultant_mem_lazardProjection (Finset.mem_image_of_mem _ hp)
          (Finset.mem_image_of_mem _ hp') (fun h ↦ hne (hinj h)),
        congrArg Associates.mk (hr p p')⟩

/-- The valuation-equality hypothesis for a transported Lazard projection is equivalent to
valuation equality for the images of the original projection polynomials. This is the
hypothesis needed to apply Lazard lifting after a change of coefficient coordinates. -/
theorem lazardValuation_eq_lazardProjection_image_map_equiv_iff
    {A σ : Type*} [CommRing A]
    [LinearOrder σ] [WellFoundedGT σ] [NormalizedGCDMonoid (MvPolynomial σ A)]
    [DecidableEq (Polynomial (MvPolynomial σ A))]
    (e : R ≃+* MvPolynomial σ A) (F B : Finset (Polynomial R)) (x y : σ → A) :
    (∀ q ∈ (F.image (Polynomial.map e.toRingHom)).lazardProjection
        (B.image (Polynomial.map e.toRingHom)), q.lazardValuation x = q.lazardValuation y) ↔
      ∀ q ∈ F.lazardProjection B, (e q).lazardValuation x = (e q).lazardValuation y := by
  classical
  have hset := image_associatesMk_lazardProjection_image_map_equiv e F B
  constructor
  · intro h q hq
    have hmem : Associates.mk (e q) ∈
        ((F.image (Polynomial.map e.toRingHom)).lazardProjection
          (B.image (Polynomial.map e.toRingHom))).image Associates.mk := by
      rw [hset]
      exact Finset.mem_image_of_mem _ hq
    obtain ⟨r, hr, heq⟩ := Finset.mem_image.mp hmem
    have hassoc := Associates.mk_eq_mk_iff_associated.mp heq
    rw [← lazardValuation_eq_of_associated hassoc x, ← lazardValuation_eq_of_associated hassoc y]
    exact h r hr
  · intro h q hq
    have hmem : Associates.mk q ∈
        (F.lazardProjection B).image (fun r ↦ Associates.mk (e r)) := by
      rw [← hset]
      exact Finset.mem_image_of_mem _ hq
    obtain ⟨r, hr, heq⟩ := Finset.mem_image.mp hmem
    have hassoc := Associates.mk_eq_mk_iff_associated.mp heq
    rw [← lazardValuation_eq_of_associated hassoc x, ← lazardValuation_eq_of_associated hassoc y]
    exact h r hr

end TauCeti
