/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Invariant.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.Basic
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.Spectrum.Prime.Topology
import TauCeti.AlgebraicGeometry.AdicSpace.ResidueField.Basic
import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.LyingOver
import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.Normal
import TauCeti.RingTheory.Invariant.Basic

/-!
# Valuation spectra of invariant extensions of commutative rings

Let `A → B` be an invariant extension for a finite group `G` acting on `B` by ring automorphisms
(`Algebra.IsInvariant A B G`). This file identifies the fibres of `Spv B → Spv A` as the
`G`-orbits (`TauCeti.ValuationSpectrum.comap_algebraMap_eq_comap_algebraMap_iff_of_isInvariant`),
with no freeness, étaleness, or topology assumptions.

Given `v, w ∈ Spv B` with the same restriction to `A`, their supports `supp v` and `supp w` lie
over the same prime of `A`, hence lie in the same `G`-orbit (`Ideal.exists_smul_eq_of_under_eq`).
Translating `v` puts both points over the same prime `Q` of `B` lying over `P = Q ∩ A`, where they
come from points of `Spv κ(Q)` with the same restriction to `κ(P)`. The residue field extension
`κ(Q) / κ(P)` is normal (`Ideal.IsFractionRing.normal`) and receives a surjection from the
stabilizer of `Q` (`IsFractionRing.stabilizerHom_surjective`), so `Aut(κ(Q) / κ(P))` is finite.
By conjugacy of valuations in normal extensions
(`TauCeti.ValuationSpectrum.comap_algebraMap_eq_comap_algebraMap_iff_of_normal`), an automorphism
of `κ(Q) / κ(P)` sends one to the other, and lifting it to the stabilizer of `Q` exhibits `w` in
the `G`-orbit of `v`.

Because `B` is integral over `A`, `Spv B → Spv A` is also surjective whenever `A → B` is injective
(`TauCeti.ValuationSpectrum.comap_surjective_of_isInvariant`). Specialising to the fixed subring
`Aᴳ = FixedPoints.subring A G` yields surjectivity and orbit fibres for `Spv A → Spv Aᴳ`.

## Main results

* `TauCeti.ValuationSpectrum.exists_smul_comap_eq_of_comap_algebraMap_eq`: two points of `Spv B`
  with the same restriction to an invariant subring `A` lie in the same `G`-orbit.
* `TauCeti.ValuationSpectrum.comap_algebraMap_eq_comap_algebraMap_iff_of_isInvariant`: for an
  invariant extension commuting with `G`, the fibres of `Spv B → Spv A` are exactly the `G`-orbits.
* `TauCeti.ValuationSpectrum.comap_surjective_of_isInvariant`: `Spv B → Spv A` is surjective when
  `algebraMap A B` is injective.
* `TauCeti.ValuationSpectrum.comap_subtype_fixedPoints_surjective`,
  `TauCeti.ValuationSpectrum.comap_subtype_fixedPoints_eq_iff`: surjectivity and orbit fibres for
  `Spv A → Spv Aᴳ`.

## References

* D. Hansen, *Quotients of adic spaces by finite groups*, Math. Res. Lett. 28 (2021), Step 1 of
  the proof of Theorem 3.1.
-/

public section

namespace TauCeti.ValuationSpectrum

section Invariant

variable {G A B : Type*} [Group G] [Finite G] [CommRing A] [CommRing B] [Algebra A B]
  [MulSemiringAction G B]

/-- Two points of `Spv B` with the same support `Q` and the same restriction to an invariant ring
`A` differ by an element of the stabilizer of `Q`. -/
private theorem exists_smul_comap_eq_of_supp_eq [Algebra.IsInvariant A B G] [SMulCommClass G A B]
    {v w : Spv B} (h : comap (algebraMap A B) v = comap (algebraMap A B) w)
    (hsupp : v.supp = w.supp) :
    ∃ g : G, w = comap (MulSemiringAction.toRingHom G B g) v := by
  set Q : Ideal B := w.supp
  set P : Ideal A := Q.under A
  have : Q.LiesOver P := ⟨rfl⟩
  let : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) :=
    Localization.AtPrime.algebraOfLiesOver P Q
  let : Algebra P.ResidueField Q.ResidueField :=
    (Ideal.ResidueField.map P Q (algebraMap A B) rfl).toAlgebra
  let : Algebra (A ⧸ P) Q.ResidueField :=
    ((algebraMap (B ⧸ Q) Q.ResidueField).comp (algebraMap (A ⧸ P) (B ⧸ Q))).toAlgebra
  have hcomp_AQ : (algebraMap P.ResidueField Q.ResidueField).comp (algebraMap A P.ResidueField) =
      (algebraMap B Q.ResidueField).comp (algebraMap A B) :=
    RingHom.ext fun a ↦ Ideal.ResidueField.map_algebraMap P Q (algebraMap A B) rfl a
  have : IsScalarTower (A ⧸ P) (B ⧸ Q) Q.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower (A ⧸ P) P.ResidueField Q.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      change algebraMap (B ⧸ Q) Q.ResidueField (algebraMap B (B ⧸ Q) (algebraMap A B a)) =
        algebraMap P.ResidueField Q.ResidueField (algebraMap A P.ResidueField a)
      rw [← IsScalarTower.algebraMap_apply B (B ⧸ Q) Q.ResidueField]
      exact (Ideal.ResidueField.map_algebraMap P Q (algebraMap A B) rfl a).symm
  -- Pull `v` and `w` back to `Spv κ(Q)`, where they agree on `κ(P)`.
  obtain ⟨v', hv'⟩ := (mem_range_comap_algebraMap_residueField_iff Q v).mpr hsupp
  obtain ⟨w', hw'⟩ := (mem_range_comap_algebraMap_residueField_iff Q w).mpr rfl
  have hK : comap (algebraMap P.ResidueField Q.ResidueField) v' =
      comap (algebraMap P.ResidueField Q.ResidueField) w' := by
    refine comap_algebraMap_residueField_injective P ?_
    rw [comap_comap, comap_comap, hcomp_AQ, ← comap_comap, ← comap_comap, hv', hw', h]
  -- `κ(Q)/κ(P)` is normal and receives a surjection from `stabilizer G Q`, so its `Aut` is finite.
  have : Normal P.ResidueField Q.ResidueField :=
    Ideal.IsFractionRing.normal G P Q P.ResidueField Q.ResidueField
  have hsurj := IsFractionRing.stabilizerHom_surjective G P Q P.ResidueField Q.ResidueField
  have : Finite (Q.ResidueField ≃ₐ[P.ResidueField] Q.ResidueField) :=
    Finite.of_surjective _ hsurj
  obtain ⟨σ, hσ⟩ := comap_algebraMap_eq_comap_algebraMap_iff_of_normal.mp hK
  obtain ⟨g, rfl⟩ := hsurj σ
  refine ⟨g.val, ?_⟩
  have hcomm : ((IsFractionRing.stabilizerHom G P Q P.ResidueField Q.ResidueField g :
      Q.ResidueField ≃ₐ[P.ResidueField] Q.ResidueField) : Q.ResidueField →+* Q.ResidueField).comp
      (algebraMap B Q.ResidueField) =
      (algebraMap B Q.ResidueField).comp (MulSemiringAction.toRingHom G B g.val) := by
    refine RingHom.ext fun b ↦ ?_
    change IsFractionRing.stabilizerHom G P Q P.ResidueField Q.ResidueField g
      (algebraMap (B ⧸ Q) Q.ResidueField (Ideal.Quotient.mk Q b)) =
      algebraMap (B ⧸ Q) Q.ResidueField (Ideal.Quotient.mk Q (g.val • b))
    exact IsFractionRing.stabilizerHom_apply_apply_mk G P Q P.ResidueField Q.ResidueField g b
  rw [← hw', hσ, comap_comap, hcomm, ← comap_comap, hv']

variable (G A) in
/-- **Points of `Spv B` with the same restriction to an invariant ring are conjugate.** If `A → B`
is an invariant extension for a finite group `G`, two points of `Spv B` with the same pullback to
`A` lie in the same `G`-orbit. The action of `G` need not commute with `A`: the proof passes to
`FixedPoints.subring B G`, which lies in the image of `A`. -/
theorem exists_smul_comap_eq_of_comap_algebraMap_eq [Algebra.IsInvariant A B G] {v w : Spv B}
    (h : comap (algebraMap A B) v = comap (algebraMap A B) w) :
    ∃ g : G, w = comap (MulSemiringAction.toRingHom G B g) v := by
  -- Pass to `Bᴳ`, on which `G` acts trivially.
  set R := FixedPoints.subring B G
  have hR : comap (algebraMap R B) v = comap (algebraMap R B) w := by
    refine ext' fun x y ↦ ?_
    obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := G) x.1 x.2
    obtain ⟨b, hb⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := G) y.1 y.2
    have hxy := congrArg (fun u : Spv A ↦ u.toValuativeRel.vle a b) h
    simpa only [comap_vle, ha, hb, Algebra.algebraMap_ofSubsemiring_apply] using hxy.to_iff
  -- Align the supports using the prime-orbit theorem.
  have hunder : w.supp.under R = v.supp.under R := by
    rw [Ideal.under_def, Ideal.under_def, ← supp_comap, ← supp_comap, hR]
  obtain ⟨g₁, hg₁⟩ := Algebra.IsInvariant.exists_smul_of_under_eq R B G w.supp v.supp hunder
  set v₁ := comap (MulSemiringAction.toRingHom G B g₁) v
  have hv₁_supp : v₁.supp = w.supp := by
    ext b
    simp only [v₁, supp_comap, Ideal.mem_comap, MulSemiringAction.toRingHom_apply, hg₁,
      Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul]
  have hv₁_R : comap (algebraMap R B) v₁ = comap (algebraMap R B) w := by
    rw [← hR, comap_comap]
    exact congrFun (congrArg comap (RingHom.ext fun x ↦ x.2 g₁)) v
  obtain ⟨g₂, hg₂⟩ := exists_smul_comap_eq_of_supp_eq (G := G) (A := R) hv₁_R hv₁_supp
  refine ⟨g₁ * g₂, ?_⟩
  rw [hg₂, comap_comap]
  exact congrFun (congrArg comap (RingHom.ext fun b ↦ (mul_smul g₁ g₂ b).symm)) v

/-- **Fibres of `Spv B → Spv A` for an invariant extension are the `G`-orbits.** If `A → B` is an
invariant extension for a finite group `G` commuting with `A`, two points of `Spv B` have the same
restriction to `A` if and only if they lie in the same `G`-orbit. -/
theorem comap_algebraMap_eq_comap_algebraMap_iff_of_isInvariant [Algebra.IsInvariant A B G]
    [SMulCommClass G A B] {v w : Spv B} :
    comap (algebraMap A B) v = comap (algebraMap A B) w ↔
      ∃ g : G, w = comap (MulSemiringAction.toRingHom G B g) v := by
  refine ⟨exists_smul_comap_eq_of_comap_algebraMap_eq G A, ?_⟩
  rintro ⟨g, rfl⟩
  rw [comap_comap]
  exact (congrFun (congrArg comap (RingHom.ext fun a ↦ smul_algebraMap g a)) v).symm

/-- **Surjectivity of `Spv B → Spv A` for an injective invariant extension.** Since `B` is integral
over `A`, `Spec B → Spec A` is surjective when `algebraMap A B` is injective, and therefore so is
`Spv B → Spv A`. -/
theorem comap_surjective_of_isInvariant [Algebra.IsInvariant A B G]
    (hinj : Function.Injective (algebraMap A B)) :
    Function.Surjective (comap (algebraMap A B)) :=
  have := Algebra.IsInvariant.isIntegral A B G
  have := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  (comap_surjective_iff (algebraMap A B)).mpr (Algebra.IsIntegral.comap_surjective A B)

end Invariant

section FixedPoints

variable (G : Type*) {A : Type*} [Group G] [Finite G] [CommRing A] [MulSemiringAction G A]

/-- Restriction `Spv A → Spv Aᴳ` along the inclusion of the fixed subring is surjective. -/
theorem comap_subtype_fixedPoints_surjective :
    Function.Surjective (comap (FixedPoints.subring A G).subtype) :=
  comap_surjective_of_isInvariant (G := G) (A := FixedPoints.subring A G) Subtype.val_injective

/-- Two points of `Spv A` have the same restriction to `Aᴳ` if and only if they lie in the same
`G`-orbit. -/
theorem comap_subtype_fixedPoints_eq_iff {v w : Spv A} :
    comap (FixedPoints.subring A G).subtype v = comap (FixedPoints.subring A G).subtype w ↔
      ∃ g : G, w = comap (MulSemiringAction.toRingHom G A g) v :=
  comap_algebraMap_eq_comap_algebraMap_iff_of_isInvariant (A := FixedPoints.subring A G)

end FixedPoints

end TauCeti.ValuationSpectrum
