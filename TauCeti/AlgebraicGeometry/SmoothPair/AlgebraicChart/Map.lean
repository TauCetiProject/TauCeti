/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.SmoothPair.AlgebraicChart.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.RingTheory.RingHom.Etale

/-!
# Étale pullback of algebraic normal crossings charts

A relative algebraic normal crossings chart pulls back along an étale ring map by
extending its boundary ideal, without taking a radical. In particular, charts restrict
to principal open subsets. This is needed to refine affine normal crossings charts
when constructing smooth pairs on schemes.

`AlgebraicChart.map` allows the target ideal to be specified with an equality to the
extended ideal. This avoids transporting charts between equal ideal types when composing
pullbacks. `AlgebraicChart.localize` is the principal-open restriction. Its coordinates
and boundary equation are the images of the original ones. Inverting the boundary
equation gives the unit ideal, as required on the boundary complement.

## References

* H. Diao, K.-W. Lan, R. Liu, X. Zhu, *Logarithmic adic spaces: some foundational results*,
  §2.3, Example 2.3.17, for the coordinate-boundary description.
-/

public section

namespace TauCeti.SmoothPair.AlgebraicChart

variable {K R S T : Type*} [Field K] [CommRing R] [CommRing S] [CommRing T]
  {σ : K →+* R} {I : Ideal R} {J : Ideal S} {L : Ideal T}

/-- Pull back a normal crossings chart along an étale map, extending the actual boundary
ideal. The scalar map on the target is the composite with the given ground-field map. -/
-- Expose the dimension-indexed coordinate map so polynomial arguments elaborate after import.
@[expose] noncomputable def map (c : AlgebraicChart K σ I) (f : R →+* S) (hf : f.Etale)
    (hJ : I.map f = J) : AlgebraicChart K (f.comp σ) J where
  n := c.n
  r := c.r
  le := c.le
  coord := f.comp c.coord
  coord_comp_C := by rw [RingHom.comp_assoc, c.coord_comp_C]
  etale := hf.comp c.etale
  ideal_eq := by
    simpa only [Ideal.map_span, Set.image_singleton, RingHom.comp_apply] using
      hJ.symm.trans (congrArg (Ideal.map f) c.ideal_eq)

/-- Étale pullback leaves the ambient coordinate dimension unchanged. -/
@[simp] theorem map_n (c : AlgebraicChart K σ I) (f : R →+* S) (hf : f.Etale)
    (hJ : I.map f = J) : (c.map f hf hJ).n = c.n := (rfl)

/-- Étale pullback retains the number of boundary coordinates. -/
@[simp] theorem map_r (c : AlgebraicChart K σ I) (f : R →+* S) (hf : f.Etale)
    (hJ : I.map f = J) : (c.map f hf hJ).r = c.r := (rfl)

/-- Each pulled-back coordinate polynomial is its image under the ring map. -/
@[simp] theorem map_coord_apply (c : AlgebraicChart K σ I) (f : R →+* S) (hf : f.Etale)
    (hJ : I.map f = J) (p : MvPolynomial (Fin c.n) K) :
    (c.map f hf hJ).coord p = f (c.coord p) := (rfl)

/-- The boundary equation pulls back without changing its multiplicities. -/
@[simp] theorem map_generator (c : AlgebraicChart K σ I) (f : R →+* S) (hf : f.Etale)
    (hJ : I.map f = J) : (c.map f hf hJ).generator = f c.generator := by
  rw [generator_eq_prod, generator_eq_prod, map_prod]
  rfl

/-- Pullback along the identity recovers the chart, not just its boundary support. -/
@[simp] theorem map_id (c : AlgebraicChart K σ I) :
    c.map (RingHom.id R) (RingHom.Etale.of_bijective Function.bijective_id)
      (Ideal.map_id I) = c := by
  cases c
  rfl

/-- Iterated étale pullback agrees with pullback along the composite. The target ideals
are specified explicitly so no transport between equal ideal types is needed. -/
@[simp] theorem map_map (c : AlgebraicChart K σ I) (f : R →+* S) (hf : f.Etale)
    (hJ : I.map f = J) (g : S →+* T) (hg : g.Etale) (hL : J.map g = L) :
    (c.map f hf hJ).map g hg hL =
      c.map (g.comp f) (hg.comp hf)
        (by rw [← Ideal.map_map, hJ, hL]) := by
  cases c
  rfl

section Localization

variable (c : AlgebraicChart K σ I) (s : R)

/-- Restrict a relative normal crossings chart to the principal open `D(s)`.
The boundary ideal is its extension to `R[1/s]`, including on the empty open. -/
-- As for `map`, expose the coordinate dimension for polynomial arguments after import.
@[expose] noncomputable def localize :
    AlgebraicChart K ((algebraMap R (Localization.Away s)).comp σ)
      (I.map (algebraMap R (Localization.Away s))) :=
  c.map (algebraMap R (Localization.Away s))
    (RingHom.etale_algebraMap.mpr inferInstance) rfl

/-- Restriction to a principal open preserves the ambient coordinate dimension. -/
@[simp] theorem localize_n : (c.localize s).n = c.n := (rfl)

/-- Restriction to a principal open preserves the number of boundary coordinates. -/
@[simp] theorem localize_r : (c.localize s).r = c.r := (rfl)

/-- Coordinate polynomials restrict by the localization homomorphism. -/
@[simp] theorem localize_coord_apply (p : MvPolynomial (Fin c.n) K) :
    (c.localize s).coord p = algebraMap R (Localization.Away s) (c.coord p) := (rfl)

/-- The boundary equation restricts by the localization homomorphism. -/
@[simp] theorem localize_generator :
    (c.localize s).generator = algebraMap R (Localization.Away s) c.generator := by
  exact c.map_generator _ _ _

/-- On the principal open complementary to the boundary, the extended boundary ideal
is the unit ideal. -/
@[simp] theorem map_ideal_generator_eq_top :
    I.map (algebraMap R (Localization.Away c.generator)) = ⊤ := by
  calc
    I.map (algebraMap R (Localization.Away c.generator)) =
        (Ideal.span {c.generator}).map (algebraMap R (Localization.Away c.generator)) :=
      congrArg (Ideal.map _) c.ideal_eq_span_generator
    _ = ⊤ := by
      rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top]
      exact IsLocalization.Away.algebraMap_isUnit c.generator

end Localization

end TauCeti.SmoothPair.AlgebraicChart
