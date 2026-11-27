/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Rings of closed intervals in the prime spectrum

The ring of the interval from `p` to `q` is the localization of `R ⧸ p.asIdeal` obtained
by inverting the images of elements outside `q`. This is the interval ring used in
Bhatt–Mathew, *The arc-topology*, Definition 4.6, for the spectrum of a valuation domain.

* `PrimeSpectrum.intervalRingLift` and `PrimeSpectrum.intervalRing_hom_ext` give the
  universal property by composing `Ideal.Quotient.lift` and `IsLocalization.lift`.
* `PrimeSpectrum.intervalRingOrderIso` identifies the prime spectrum of the interval ring
  with `Set.Icc p q`, using the quotient and localization order isomorphisms.
* `PrimeSpectrum.intervalRing_algebraMap_eq_zero_iff` and
  `PrimeSpectrum.isUnit_intervalRing_algebraMap_iff` use contraction at the endpoints to detect
  zero and unit images for `p ≤ q`.
* `PrimeSpectrum.intervalRingMap` restricts from a larger interval to a smaller one.
* `PrimeSpectrum.isDomain_intervalRing` gives a domain for ordered endpoints. For a valuation
  domain, this lets the existing quotient and localization instances infer a valuation ring.
-/

public section

namespace PrimeSpectrum

variable {R : Type*} [CommRing R]

/-- The images of the complement of `q` in the quotient by `p`. -/
abbrev intervalDenominators (p q : PrimeSpectrum R) : Submonoid (R ⧸ p.asIdeal) :=
  q.asIdeal.primeCompl.map (Ideal.Quotient.mk p.asIdeal)

/-- The ring of `[p,q]` in the prime spectrum, formed by killing `p` and inverting
the complement of `q`. This construction also permits empty intervals. -/
abbrev IntervalRing (p q : PrimeSpectrum R) :=
  Localization (intervalDenominators p q)

/-- The ring of a nonempty closed interval in the prime spectrum is a domain. -/
theorem isDomain_intervalRing (p q : PrimeSpectrum R) (h : p ≤ q) :
    IsDomain (IntervalRing p q) := by
  apply IsLocalization.isDomain_of_le_nonZeroDivisors (M := intervalDenominators p q)
  apply le_nonZeroDivisors_of_noZeroDivisors
  intro hz
  obtain ⟨x, hx, hzero⟩ := Submonoid.mem_map.mp hz
  exact hx (h (Ideal.Quotient.eq_zero_iff_mem.mp hzero))

/-- The canonical map to the interval ring kills the lower endpoint. -/
@[simp]
theorem intervalRing_algebraMap_eq_zero (p q : PrimeSpectrum R) {x : R} (hx : x ∈ p.asIdeal) :
    algebraMap R (IntervalRing p q) x = 0 := by
  rw [IsScalarTower.algebraMap_apply R (R ⧸ p.asIdeal), Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

/-- The canonical map to the interval ring inverts elements outside the upper endpoint. -/
theorem isUnit_intervalRing_algebraMap (p q : PrimeSpectrum R) {x : R} (hx : x ∉ q.asIdeal) :
    IsUnit (algebraMap R (IntervalRing p q) x) := by
  rw [IsScalarTower.algebraMap_apply R (R ⧸ p.asIdeal), Ideal.Quotient.algebraMap_eq]
  exact IsLocalization.map_units (M := intervalDenominators p q)
    _ ⟨_, Submonoid.mem_map.mpr ⟨x, hx, rfl⟩⟩

/-- A map killing the lower endpoint and inverting the complement of the upper endpoint
factors through the interval ring. -/
noncomputable def intervalRingLift {S : Type*} [CommSemiring S] (p q : PrimeSpectrum R)
    (f : R →+* S)
    (hzero : ∀ x ∈ p.asIdeal, f x = 0) (hunit : ∀ x ∉ q.asIdeal, IsUnit (f x)) :
    IntervalRing p q →+* S :=
  IsLocalization.lift (M := intervalDenominators p q)
    (g := Ideal.Quotient.lift p.asIdeal f hzero) fun ⟨y, hy⟩ ↦ by
      obtain ⟨x, hx, rfl⟩ := Submonoid.mem_map.mp hy
      simpa only [Ideal.Quotient.lift_mk] using hunit x hx

/-- The factorization through an interval ring agrees with the initial homomorphism on the
ambient ring. -/
@[simp]
theorem intervalRingLift_algebraMap {S : Type*} [CommSemiring S]
    (p q : PrimeSpectrum R) (f : R →+* S)
    (hzero : ∀ x ∈ p.asIdeal, f x = 0) (hunit : ∀ x ∉ q.asIdeal, IsUnit (f x)) (x : R) :
    p.intervalRingLift q f hzero hunit (algebraMap R (IntervalRing p q) x) = f x := by
  rw [IsScalarTower.algebraMap_apply R (R ⧸ p.asIdeal), Ideal.Quotient.algebraMap_eq,
    intervalRingLift, IsLocalization.lift_eq, Ideal.Quotient.lift_mk]

/-- Maps out of an interval ring are determined by their composite with the canonical map. -/
theorem intervalRing_hom_ext {S : Type*} [Semiring S] (p q : PrimeSpectrum R)
    {f g : IntervalRing p q →+* S}
    (h : f.comp (algebraMap R (IntervalRing p q)) = g.comp (algebraMap R (IntervalRing p q))) :
    f = g := by
  apply IsLocalization.ringHom_ext (intervalDenominators p q)
  apply Ideal.Quotient.ringHom_ext
  exact RingHom.ext fun x ↦ by
    simpa only [RingHom.comp_apply, IsScalarTower.algebraMap_apply R (R ⧸ p.asIdeal),
      Ideal.Quotient.algebraMap_eq] using RingHom.congr_fun h x

/-- Contraction to the ambient ring identifies the prime spectrum of the interval ring
with the closed interval between the two endpoints. -/
noncomputable def intervalRingOrderIso (p q : PrimeSpectrum R) :
    PrimeSpectrum (IntervalRing p q) ≃o Set.Icc p q :=
  let M := intervalDenominators p q
  let e := p.asIdeal.primeSpectrumQuotientOrderIsoZeroLocus
  have hdisj (r : PrimeSpectrum (R ⧸ p.asIdeal)) :
      Disjoint (M : Set (R ⧸ p.asIdeal)) r.asIdeal ↔
        (e r : PrimeSpectrum R) ≤ q := by
    have he : (e r : PrimeSpectrum R) = r.comap (Ideal.Quotient.mk p.asIdeal) := rfl
    rw [he, ← asIdeal_le_asIdeal, comap_asIdeal, disjoint_comm]
    exact Ideal.disjoint_map_primeCompl_iff_comap_le
  (IsLocalization.primeSpectrumOrderIso M (IntervalRing p q)).trans
    { toFun := fun r ↦ ⟨e r, (e r).property, (hdisj r).mp r.property⟩
      invFun := fun r ↦ ⟨e.symm ⟨r, r.property.1⟩, (hdisj _).mpr (by
        rw [e.apply_symm_apply]
        exact r.property.2)⟩
      left_inv := fun r ↦ Subtype.ext (e.symm_apply_apply r)
      right_inv := fun r ↦ by
        have hr := e.apply_symm_apply ⟨r, r.property.1⟩
        exact Subtype.ext (congrArg (fun t : zeroLocus (p.asIdeal : Set R) ↦ t.val) hr)
      map_rel_iff' := e.le_iff_le }

/-- The spectrum identification acts by contraction to the ambient ring.
This computation rule permits simplification without unfolding the order isomorphism. -/
@[simp]
theorem intervalRingOrderIso_apply (p q : PrimeSpectrum R)
    (r : PrimeSpectrum (IntervalRing p q)) :
    (p.intervalRingOrderIso q r : PrimeSpectrum R) = r.comap (algebraMap R (IntervalRing p q)) :=
  (rfl)

/-- For ordered endpoints, the canonical map to the interval ring vanishes exactly on the
lower endpoint. -/
@[simp]
theorem intervalRing_algebraMap_eq_zero_iff {p q : PrimeSpectrum R} (h : p ≤ q) {x : R} :
    algebraMap R (IntervalRing p q) x = 0 ↔ x ∈ p.asIdeal := by
  refine ⟨fun hx ↦ ?_, p.intervalRing_algebraMap_eq_zero q⟩
  let r := (p.intervalRingOrderIso q).symm ⟨p, le_rfl, h⟩
  have hr : r.comap (algebraMap R (IntervalRing p q)) = p := by
    simp only [r, ← intervalRingOrderIso_apply, OrderIso.apply_symm_apply]
  rw [← hr, comap_asIdeal, Ideal.mem_comap, hx]
  exact r.asIdeal.zero_mem

/-- For ordered endpoints, the canonical map to the interval ring sends exactly the elements
outside the upper endpoint to units. -/
@[simp]
theorem isUnit_intervalRing_algebraMap_iff {p q : PrimeSpectrum R} (h : p ≤ q) {x : R} :
    IsUnit (algebraMap R (IntervalRing p q) x) ↔ x ∉ q.asIdeal := by
  refine ⟨fun hx ↦ ?_, p.isUnit_intervalRing_algebraMap q⟩
  let r := (p.intervalRingOrderIso q).symm ⟨q, h, le_rfl⟩
  have hr : r.comap (algebraMap R (IntervalRing p q)) = q := by
    simp only [r, ← intervalRingOrderIso_apply, OrderIso.apply_symm_apply]
  rw [← hr, comap_asIdeal, Ideal.mem_comap]
  exact r.asIdeal.notMem_of_isUnit hx

/-- Restrict from `[p,q]` to an interval `[p',q']` whose endpoints lie inside it. -/
noncomputable def intervalRingMap (p q : PrimeSpectrum R) {p' q' : PrimeSpectrum R}
    (hp : p ≤ p') (hq : q' ≤ q) : IntervalRing p q →+* IntervalRing p' q' :=
  p.intervalRingLift q (algebraMap R (IntervalRing p' q'))
    (fun _ hx ↦ p'.intervalRing_algebraMap_eq_zero q' (hp hx))
    (fun _ hx ↦ p'.isUnit_intervalRing_algebraMap q' (fun h ↦ hx (hq h)))

/-- Restriction preserves the image of each element of the ambient ring. -/
@[simp]
theorem intervalRingMap_algebraMap (p q : PrimeSpectrum R) {p' q' : PrimeSpectrum R}
    (hp : p ≤ p') (hq : q' ≤ q) (x : R) :
    p.intervalRingMap q hp hq (algebraMap R (IntervalRing p q) x) =
      algebraMap R (IntervalRing p' q') x := by
  rw [intervalRingMap, intervalRingLift_algebraMap]

/-- Restriction to the same interval is the identity. -/
@[simp]
theorem intervalRingMap_refl (p q : PrimeSpectrum R) :
    p.intervalRingMap q le_rfl le_rfl = RingHom.id (IntervalRing p q) := by
  apply p.intervalRing_hom_ext q
  apply RingHom.ext
  intro x
  simp only [RingHom.comp_apply, intervalRingMap_algebraMap, RingHom.id_apply]

/-- Restricting in two steps agrees with direct restriction. -/
@[simp]
theorem intervalRingMap_comp (p q : PrimeSpectrum R) {p' q' p'' q'' : PrimeSpectrum R}
    (hp : p ≤ p') (hq : q' ≤ q) (hp' : p' ≤ p'') (hq' : q'' ≤ q') :
    (p'.intervalRingMap q' hp' hq').comp (p.intervalRingMap q hp hq) =
      p.intervalRingMap q (hp.trans hp') (hq'.trans hq) := by
  apply p.intervalRing_hom_ext q
  apply RingHom.ext
  intro x
  simp only [RingHom.comp_apply, intervalRingMap_algebraMap]

/-- Applying two successive restrictions agrees with applying the direct restriction. -/
@[simp]
theorem intervalRingMap_intervalRingMap (p q : PrimeSpectrum R) {p' q' p'' q'' : PrimeSpectrum R}
    (hp : p ≤ p') (hq : q' ≤ q) (hp' : p' ≤ p'') (hq' : q'' ≤ q') (x : IntervalRing p q) :
    p'.intervalRingMap q' hp' hq' (p.intervalRingMap q hp hq x) =
      p.intervalRingMap q (hp.trans hp') (hq'.trans hq) x := by
  exact RingHom.congr_fun (p.intervalRingMap_comp q hp hq hp' hq') x

end PrimeSpectrum
