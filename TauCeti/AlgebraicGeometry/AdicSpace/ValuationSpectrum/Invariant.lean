/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Invariant.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Cont.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.Action
import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.Amalgamation
import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.LyingOver
import TauCeti.RingTheory.Invariant.Basic
import TauCeti.RingTheory.Valuation.Continuous.Invariant

/-!
# The valuation spectrum over the invariants of a finite group

Let a finite group `G` act on a ring `A` by ring automorphisms, and let `R → A` be a ring map
whose image contains every invariant (`Algebra.IsInvariant R A G`), for instance the inclusion of
the fixed subring `Aᴳ`. The group acts on `Spv A` by `(g • y)(a) = y(g⁻¹ • a)`, that is
`g • y = comap (g⁻¹ • ·) y` (`TauCeti.ValuationSpectrum.smul_def`). This file describes the
restriction map `Spv A → Spv R` on the level of points, with no hypothesis on the order of `G`:

* when `G` acts by `R`-algebra automorphisms (`SMulCommClass G R A`), its fibres are exactly the
  `G`-orbits; that points in one orbit have the same restriction needs neither finiteness nor
  invariance (`TauCeti.ValuationSpectrum.comap_algebraMap_smul`);
* when `R → A` is injective, it is surjective, since `A` is integral over `R`
  (`TauCeti.ValuationSpectrum.comap_algebraMap_surjective_of_isIntegral`).

So when both hold, `Spv R` is the set of `G`-orbits of `Spv A`. If `G` acts by continuous
automorphisms of a topological ring `A` and `R → A` is inducing, continuity of a point of `Spv A`
can be tested on its restriction to `R`. Hence, under the same two qualifications, the restriction
map sends `Cont A` onto `Cont R` (for `R → A` injective) with the `G`-orbits as fibres (for `G`
acting by `R`-algebra automorphisms).

Two points `y` and `y'` with the same restriction amalgamate to a point of `Spv (A ⊗[R] A)`
(`TauCeti.ValuationSpectrum.exists_amalgamation`), which is pulled back from the residue field
`κ` of its support. The two maps `A → A ⊗[R] A → κ` agree on `R`, so they differ by an element
of `G` (`TauCeti.Algebra.IsInvariant.exists_comp_eq_of_comp_algebraMap_eq`), and that element
carries `y` to `y'`.

## Main results

* `TauCeti.ValuationSpectrum.comap_algebraMap_eq_comap_algebraMap_iff_of_isInvariant`: the fibres
  of `Spv A → Spv R` are the `G`-orbits when `G` acts by `R`-algebra automorphisms.
* `TauCeti.ValuationSpectrum.isContinuous_comap_algebraMap_iff_of_isInvariant`: for `R → A`
  inducing, a point of `Spv A` is continuous exactly when its restriction to `R` is.
* `TauCeti.ValuationSpectrum.surjOn_comap_algebraMap_cont_of_isInvariant`: for `R → A` injective
  and inducing, every continuous point of `Spv R` is the restriction of a continuous point of
  `Spv A`.

## References

* D. Hansen, *Quotients of adic spaces by finite groups*, Math. Res. Lett. 28 (2021), proof of
  Theorem 3.1, Step 1.
-/

public section

open scoped TensorProduct

open Algebra.TensorProduct

namespace TauCeti.ValuationSpectrum

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (G : Type*) [Group G] [Finite G]
  [MulSemiringAction G A] [Algebra.IsInvariant R A G]

/-- **The fibres of `Spv A → Spv R` are the `G`-orbits.** If a finite group `G` acts on `A` by
`R`-algebra automorphisms and every invariant of `A` comes from `R`, two points `y` and `y'` of
`Spv A` have the same restriction to `R` exactly when `y' = g • y` for some `g ∈ G`, where
`(g • y)(a) = y(g⁻¹ • a)`. -/
theorem comap_algebraMap_eq_comap_algebraMap_iff_of_isInvariant [SMulCommClass G R A]
    {y y' : Spv A} :
    comap (algebraMap R A) y = comap (algebraMap R A) y' ↔
      ∃ g : G, y' = g • y := by
  refine ⟨fun h ↦ ?_, fun ⟨g, hg⟩ ↦ by rw [hg, comap_algebraMap_smul]⟩
  -- amalgamate `y` and `y'` to a point `v` of `Spv (A ⊗[R] A)`, pulled back from `κ(supp v)`
  obtain ⟨v, hvy, hvy'⟩ := exists_amalgamation y y' h
  set ψ := algebraMap (A ⊗[R] A) v.supp.ResidueField
  have hv : comap ψ (ofValuation (residueFieldValuation v)) = v :=
    comap_algebraMap_residueField_ofValuation v
  -- the two maps `A → κ(supp v)` agree on `R`, so they differ by an element `g` of `G`
  obtain ⟨g, hg⟩ := TauCeti.Algebra.IsInvariant.exists_comp_eq_of_comp_algebraMap_eq R G
    (ψ.comp includeLeftRingHom) (ψ.comp (includeRight (R := R) (A := A)).toRingHom)
    (RingHom.ext fun r ↦ congrArg ψ (((includeLeft (S := R)).commutes r).trans
      (includeRight.commutes r).symm))
  refine ⟨g⁻¹, ?_⟩
  rw [smul_def, inv_inv, ← hvy, ← hvy', ← hv, comap_comap, comap_comap, comap_comap, ← hg,
    RingHom.comp_assoc]

variable [TopologicalSpace R] [TopologicalSpace A] [IsTopologicalRing A] [ContinuousConstSMul G A]

include G in
/-- **Continuity is detected on the invariants.** If a finite group `G` acts on a topological ring
`A` by continuous ring automorphisms and `R → A` is an inducing ring map whose image contains
every invariant, then a point of `Spv A` is continuous exactly when its restriction to `R` is. -/
theorem isContinuous_comap_algebraMap_iff_of_isInvariant
    (hι : Topology.IsInducing (algebraMap R A)) {y : Spv A} :
    (comap (algebraMap R A) y).IsContinuous ↔ y.IsContinuous := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comap hι.continuous⟩
  rw [← ofValuation_valuation y, comap_ofValuation, isContinuous_ofValuation_iff] at h
  exact (isContinuous_def y).mpr
    (Valuation.isContinuous_of_isContinuous_comap_of_isInvariant G hι h)

include G in
/-- **`Cont A → Cont R` is surjective.** If a finite group `G` acts on a topological ring `A` by
continuous ring automorphisms and `R → A` is an injective inducing ring map whose image contains
every invariant, every continuous point of `Spv R` is the restriction of a continuous point of
`Spv A`. -/
theorem surjOn_comap_algebraMap_cont_of_isInvariant [FaithfulSMul R A]
    (hι : Topology.IsInducing (algebraMap R A)) :
    Set.SurjOn (comap (algebraMap R A)) (cont A) (cont R) := fun x hx ↦ by
  have := Algebra.IsInvariant.isIntegral R A G
  obtain ⟨y, rfl⟩ := comap_algebraMap_surjective_of_isIntegral (A := R) (B := A) x
  rw [mem_cont_iff, isContinuous_comap_algebraMap_iff_of_isInvariant G hι] at hx
  exact ⟨y, (mem_cont_iff y).mpr hx, rfl⟩

end TauCeti.ValuationSpectrum
