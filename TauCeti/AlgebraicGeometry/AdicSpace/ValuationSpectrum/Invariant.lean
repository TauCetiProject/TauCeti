/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Invariant.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Cont.Basic
import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.Amalgamation
import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.LyingOver
import TauCeti.RingTheory.Invariant.Basic
import TauCeti.RingTheory.Valuation.Continuous.Invariant

/-!
# The valuation spectrum over the invariants of a finite group

Let a finite group `G` act on a ring `A` by ring automorphisms, and let `R → A` be a ring map
whose image contains every invariant (`Algebra.IsInvariant R A G`), for instance the inclusion of
the fixed subring `Aᴳ`. The group acts on `Spv A` by `(g • y)(a) = y(g⁻¹ • a)`, that is
`g • y = comap (g⁻¹ • ·) y`, by homeomorphisms (an instance, for any group acting by ring
automorphisms). This file shows that the restriction map `Spv A → Spv R` is a
quotient by this action on the level of points, with no hypothesis on the order of `G`:

* its fibres are exactly the `G`-orbits, when `G` fixes `R`; that points in one orbit have the
  same restriction needs neither finiteness nor invariance
  (`TauCeti.ValuationSpectrum.comap_algebraMap_smul`);
* it is surjective when `R → A` is injective, since `A` is integral over `R`
  (`TauCeti.ValuationSpectrum.comap_algebraMap_surjective_of_isIntegral`).

If `G` acts by continuous automorphisms of a topological ring `A` and `R` carries the induced
topology, continuity of a point of `Spv A` can be tested on its restriction to `R`. Hence the
restriction map also sends `Cont A` onto `Cont R`, with the `G`-orbits as fibres.

Two points `y` and `y'` with the same restriction amalgamate to a point of `Spv (A ⊗[R] A)`
(`TauCeti.ValuationSpectrum.exists_amalgamation`), which is pulled back from the residue field
`κ` of its support. The two maps `A → A ⊗[R] A → κ` agree on `R`, so they differ by an element
of `G` (`TauCeti.Algebra.IsInvariant.exists_comp_eq_of_comp_algebraMap_eq`), and that element
carries `y` to `y'`.

## Main results

* `TauCeti.ValuationSpectrum.comap_algebraMap_eq_comap_algebraMap_iff_of_isInvariant`: the fibres
  of `Spv A → Spv R` are the `G`-orbits.
* `TauCeti.ValuationSpectrum.isContinuous_comap_algebraMap_iff_of_isInvariant`: a point of
  `Spv A` is continuous exactly when its restriction to `R` is.
* `TauCeti.ValuationSpectrum.surjOn_comap_algebraMap_cont_of_isInvariant`: every continuous point
  of `Spv R` is the restriction of a continuous point of `Spv A`.

## References

* D. Hansen, *Quotients of adic spaces by finite groups*, Math. Res. Lett. 28 (2021), proof of
  Theorem 3.1, Step 1.
-/

public section

open scoped TensorProduct

open Algebra.TensorProduct

namespace TauCeti.ValuationSpectrum

section Action

section SMul

variable {G A : Type*} [Group G] [CommRing A] [MulSemiringAction G A]

/-- A group acting on `A` by ring automorphisms acts on `Spv A` by transport of structure,
`(g • v)(a) = v(g⁻¹ • a)`, that is `g • v = comap (g⁻¹ • ·) v`. This matches Mathlib's action on
`PrimeSpectrum A`. -/
instance : SMul G (Spv A) :=
  ⟨fun g v ↦ comap (MulSemiringAction.toRingHom G A g⁻¹) v⟩

/-- `g • v` is the pullback of `v` along the ring automorphism `g⁻¹ • ·`. -/
theorem smul_def (g : G) (v : Spv A) : g • v = comap (MulSemiringAction.toRingHom G A g⁻¹) v :=
  (rfl)

/-- The action of `G` on `Spv A` by transport of structure is a group action. -/
instance : MulAction G (Spv A) where
  one_smul v := by
    have h : MulSemiringAction.toRingHom G A 1 = RingHom.id A := RingHom.ext (one_smul G)
    rw [smul_def, inv_one, h, comap_id, id]
  mul_smul g h v := by
    rw [smul_def, smul_def, smul_def, comap_comap]
    congr 1
    exact RingHom.ext fun a ↦ by simp [mul_smul]

/-- `G` acts on `Spv A` by homeomorphisms. -/
instance : ContinuousConstSMul G (Spv A) :=
  ⟨fun _ ↦ continuous_comap _⟩

end SMul

variable {G R A : Type*} [Group G] [CommRing R] [CommRing A] [Algebra R A]
  [MulSemiringAction G A] [SMulCommClass G R A]

/-- Acting by `g ∈ G` does not change the image in `Spv R`, since `G` acts by `R`-algebra
automorphisms. No finiteness or invariance hypothesis is needed. -/
@[simp]
theorem comap_algebraMap_smul (g : G) (y : Spv A) :
    comap (algebraMap R A) (g • y) = comap (algebraMap R A) y := by
  rw [smul_def, comap_comap]
  congr 1
  exact RingHom.ext fun r ↦ smul_algebraMap g⁻¹ r

end Action

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (G : Type*) [Group G] [Finite G]
  [MulSemiringAction G A] [Algebra.IsInvariant R A G]

/-- **The fibres of `Spv A → Spv R` are the `G`-orbits.** If a finite group `G` acts on `A` by
`R`-algebra automorphisms and every invariant of `A` comes from `R`, two points `y` and `y'` of
`Spv A` have the same restriction to `R` exactly when `y' = g • y` for some `g ∈ G`, where
`(g • y)(a) = y(g⁻¹ • a)`. -/
theorem comap_algebraMap_eq_comap_algebraMap_iff_of_isInvariant [SMulCommClass G R A]
    {y y' : Spv A} :
    comap (algebraMap R A) y = comap (algebraMap R A) y' ↔
      ∃ g : G, y' = comap (MulSemiringAction.toRingHom G A g⁻¹) y := by
  refine ⟨fun h ↦ ?_, fun ⟨g, hg⟩ ↦ by rw [hg, ← smul_def, comap_algebraMap_smul]⟩
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
  rw [inv_inv, ← hvy, ← hvy', ← hv, comap_comap, comap_comap, comap_comap, ← hg,
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
