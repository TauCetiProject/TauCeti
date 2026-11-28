/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Face.Orbit.Saturation
public import TauCeti.Algebra.MonoidAlgebra.IntegrallyClosed

/-!
# Normalization fibers over field-valued points of semigroup algebras

For a submonoid `S` of a torsion-free abelian group `G` (`[Module.IsTorsionFree ℤ G]`), an
integrally closed domain `R` (`IsDomain R`, `IsIntegrallyClosed R`), a fraction ring `L` of `R[S]`,
and an integral closure `B` of `R[S]` in `L`, this file transports the orbit-saturation fiber
analysis across `AddSubmonoid.fiberIntegralClosureEquivMapDomainAlgHom` to describe the fiber of
lifts `z : B →+* K` of a fixed `K`-point `x : R[S] →ₐ[R] K` under precomposition with
`algebraMap R[S] B`:

* Under `[RootableBy Kˣ ℕ]`, every `K`-point `x` lifts along `R[S] →+* B`
  (`AddSubmonoid.exists_ringHom_comp_algebraMap_eq_of_isIntegralClosure`).
* Over an algebraically closed field `K`, writing `Q_F =`
  `F.faceSubgroup.nsmulSaturation ⧸ F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation`,
  when `Q_F` is finite and `Nat.card Q_F` is invertible in `K`, the fiber of lifts of `x` with
  `S.pointSupport x = F` has cardinality `Nat.card Q_F`
  (`SaturatedAddSubmonoid.card_fiber_ringHom_of_isIntegralClosure`); in characteristic `0` it is a
  singleton iff `F.faceSubgroup = F.faceSubgroup.nsmulSaturation`
  (`SaturatedAddSubmonoid.subsingleton_fiber_ringHom_iff_of_charZero`).
* In characteristic `p`, if `Q_F` is `p`-primary and `[RootableBy Kˣ ℕ]`, every `K`-point `x` with
  `S.pointSupport x = F` lifts uniquely along `R[S] →+* B`
  (`SaturatedAddSubmonoid.existsUnique_ringHom_of_isIntegralClosure_of_charP_of_pPrimary`).

## References

* W. Bruns and J. Gubeladze, *Polytopes, Rings, and K-Theory*, Chapter 4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §1.3 and §3.2.
-/

public section

open AddMonoidAlgebra

namespace SaturatedAddSubmonoid

variable {G : Type*} [AddCommGroup G] [Module.IsTorsionFree ℤ G] {S : AddSubmonoid G}

/-- For an integrally closed domain `R`, torsion-free `G`, a fraction ring `L` of `R[S]`, an
integral closure `B` of `R[S]` in `L`, and a field `K` with `[RootableBy Kˣ ℕ]`, every `K`-point
`x : R[S] →ₐ[R] K` lifts along `algebraMap R[S] B` under precomposition. -/
theorem _root_.AddSubmonoid.exists_ringHom_comp_algebraMap_eq_of_isIntegralClosure
    (S : AddSubmonoid G) (R L B K : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing L] [Algebra (AddMonoidAlgebra R S) L] [IsFractionRing (AddMonoidAlgebra R S) L]
    [CommRing B] [Algebra (AddMonoidAlgebra R S) B] [Algebra B L]
    [IsScalarTower (AddMonoidAlgebra R S) B L] [IsIntegralClosure B (AddMonoidAlgebra R S) L]
    [Field K] [RootableBy Kˣ ℕ] [Algebra R K] (x : AddMonoidAlgebra R S →ₐ[R] K) :
    ∃ z : B →+* K, z.comp (algebraMap (AddMonoidAlgebra R S) B) = x.toRingHom :=
  have ⟨y, hy⟩ := S.exists_comp_mapDomainAlgHom_inclusion_nsmulSaturation R K x
  ⟨_, ((S.fiberIntegralClosureEquivMapDomainAlgHom R L B K x).symm ⟨y, hy⟩).property⟩

/-- For an integrally closed domain `R`, torsion-free `G`, a fraction ring `L` of `R[S]`, and an
integral closure `B` of `R[S]` in `L`, when `Q_F` is finite and `Nat.card Q_F` is invertible in an
algebraically closed field `K`, the fiber of lifts `z : B →+* K` of `x` (with
`S.pointSupport x = F`) under precomposition with `algebraMap R[S] B` has cardinality
`Nat.card Q_F`. -/
theorem card_fiber_ringHom_of_isIntegralClosure (F : SaturatedAddSubmonoid S)
    (R L B K : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing L]
    [Algebra (AddMonoidAlgebra R S) L] [IsFractionRing (AddMonoidAlgebra R S) L] [CommRing B]
    [Algebra (AddMonoidAlgebra R S) B] [Algebra B L] [IsScalarTower (AddMonoidAlgebra R S) B L]
    [IsIntegralClosure B (AddMonoidAlgebra R S) L] [Field K] [IsAlgClosed K] [Algebra R K]
    [Finite (F.faceSubgroup.nsmulSaturation ⧸
      F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation)]
    [NeZero ((Nat.card (F.faceSubgroup.nsmulSaturation ⧸
      F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation) : ℕ) : K)]
    {x : AddMonoidAlgebra R S →ₐ[R] K} (hx : S.pointSupport x = F) :
    Nat.card {z : B →+* K // z.comp (algebraMap (AddMonoidAlgebra R S) B) = x.toRingHom} =
      Nat.card (F.faceSubgroup.nsmulSaturation ⧸
        F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation) := by
  rw [Nat.card_congr (S.fiberIntegralClosureEquivMapDomainAlgHom R L B K x),
    F.card_fiber_mapDomainAlgHom_inclusion_nsmulSaturation R K hx]

/-- For an integrally closed domain `R`, torsion-free `G`, a fraction ring `L` of `R[S]`, and an
integral closure `B` of `R[S]` in `L`, over a char-`0` algebraically closed field `K` with
`[Finite Q_F]`, the fiber of lifts `z : B →+* K` of `x` (with `S.pointSupport x = F`) under
precomposition with `algebraMap R[S] B` is a singleton iff
`F.faceSubgroup = F.faceSubgroup.nsmulSaturation`. -/
theorem subsingleton_fiber_ringHom_iff_of_charZero (F : SaturatedAddSubmonoid S)
    (R L B K : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing L]
    [Algebra (AddMonoidAlgebra R S) L] [IsFractionRing (AddMonoidAlgebra R S) L] [CommRing B]
    [Algebra (AddMonoidAlgebra R S) B] [Algebra B L] [IsScalarTower (AddMonoidAlgebra R S) B L]
    [IsIntegralClosure B (AddMonoidAlgebra R S) L] [Field K] [IsAlgClosed K] [CharZero K]
    [Algebra R K]
    [Finite (F.faceSubgroup.nsmulSaturation ⧸
      F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation)]
    {x : AddMonoidAlgebra R S →ₐ[R] K} (hx : S.pointSupport x = F) :
    Subsingleton {z : B →+* K // z.comp (algebraMap (AddMonoidAlgebra R S) B) = x.toRingHom} ↔
      F.faceSubgroup = F.faceSubgroup.nsmulSaturation := by
  let Q := F.faceSubgroup.nsmulSaturation ⧸
    F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation
  have : NeZero ((Nat.card Q : ℕ) : K) := ⟨Nat.cast_ne_zero.2 Nat.card_pos.ne'⟩
  have hcard := F.card_fiber_ringHom_of_isIntegralClosure R L B K hx
  have : Finite {z : B →+* K // z.comp (algebraMap (AddMonoidAlgebra R S) B) = x.toRingHom} :=
    Nat.finite_of_card_ne_zero (hcard ▸ Nat.card_pos.ne')
  rw [← Finite.card_le_one_iff_subsingleton, hcard, Finite.card_le_one_iff_subsingleton,
    F.faceSubgroup.subsingleton_quotient_nsmulSaturation_iff]

/-- For an integrally closed domain `R`, torsion-free `G`, a fraction ring `L` of `R[S]`, and an
integral closure `B` of `R[S]` in `L`, in char `p` if `Q_F` is `p`-primary and `[RootableBy Kˣ ℕ]`,
every `K`-point `x` with `S.pointSupport x = F` lifts uniquely along `algebraMap R[S] B` under
precomposition. -/
theorem existsUnique_ringHom_of_isIntegralClosure_of_charP_of_pPrimary
    (F : SaturatedAddSubmonoid S) (R L B K : Type*) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CommRing L] [Algebra (AddMonoidAlgebra R S) L]
    [IsFractionRing (AddMonoidAlgebra R S) L] [CommRing B] [Algebra (AddMonoidAlgebra R S) B]
    [Algebra B L] [IsScalarTower (AddMonoidAlgebra R S) B L]
    [IsIntegralClosure B (AddMonoidAlgebra R S) L] [Field K] [RootableBy Kˣ ℕ] [Algebra R K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp : ∀ q : F.faceSubgroup.nsmulSaturation ⧸
      F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation, ∃ e : ℕ, (p ^ e) • q = 0)
    {x : AddMonoidAlgebra R S →ₐ[R] K} (hx : S.pointSupport x = F) :
    ∃! z : B →+* K, z.comp (algebraMap (AddMonoidAlgebra R S) B) = x.toRingHom := by
  let e := (S.fiberIntegralClosureEquivMapDomainAlgHom R L B K x).trans
    (F.fiberMapDomainAlgHomEquivOrbitSaturationCharHom R K hx)
  have hbij := F.orbitSaturationCharHom_bijective_of_charP_of_pPrimary K p hp
  obtain ⟨ψ, hψ⟩ := hbij.2 (F.pointSupportSubtypeEquivChar R K ⟨x, hx⟩)
  refine ⟨(e.symm ⟨ψ, hψ⟩).val, (e.symm ⟨ψ, hψ⟩).property, fun z hz ↦ ?_⟩
  have : Subsingleton
      ((F.orbitSaturationCharHom Kˣ) ⁻¹' {F.pointSupportSubtypeEquivChar R K ⟨x, hx⟩}) :=
    ⟨fun a b ↦ Subtype.ext (hbij.1 (a.property.trans b.property.symm))⟩
  exact congrArg Subtype.val (e.eq_symm_apply.2 (Subsingleton.elim (e ⟨z, hz⟩) ⟨ψ, hψ⟩))

end SaturatedAddSubmonoid
