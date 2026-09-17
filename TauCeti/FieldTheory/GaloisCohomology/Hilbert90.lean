/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import TauCeti.FieldTheory.GaloisCohomology.Coefficients
public import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.Colimit

/-!
# Hilbert 90 for infinite Galois extensions

For a Galois extension `L/K`, finite or infinite, the first continuous cohomology of `Gal(L/K)`
with coefficients in the discrete module `Lˣ` vanishes:

```text
H¹(Gal(L/K), Lˣ) = 0.
```

Specialised to a separable closure this is Hilbert 90 for the absolute Galois group,
`H¹(G_K, (Kˢ)ˣ) = 0`, which is what makes the Kummer map `Kˣ → H¹(G_K, μₙ)` surjective.

The proof passes to finite layers. An open normal subgroup `U` of `Gal(L/K)` has a fixed field `F`
that is finite Galois over `K`; the infinite Galois correspondence identifies `Gal(L/K) ⧸ U` with
`Gal(F/K)` (`InfiniteGalois.normalAutEquivQuotient`), and the units of `L` fixed by `U` are the
units of `F`. Through these two identifications a `1`-cocycle of the finite layer becomes a
multiplicative `1`-cocycle `Gal(F/K) → Fˣ`, which is a coboundary by Noether's form of Hilbert 90,
`groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`. The vanishing then passes to
`Gal(L/K)` because every continuous class is inflated from a finite layer,
`TauCeti.ContCohomology.subsingleton_H1_of_forall_openNormalSubgroup`.

## Main results

* `TauCeti.isCoboundary₁_of_isCocycle₁_of_quotient_to_fixedPoints`: Hilbert 90 at a finite layer
  `Gal(L/K) ⧸ U` with coefficients `(Lˣ)^U`.
* `TauCeti.subsingleton_H1_additive_units`: `H¹(Gal(L/K), Lˣ) = 0` for any Galois `L/K`.
* `TauCeti.subsingleton_H1_unitsCoeff`: `H¹(G_K, (Kˢ)ˣ) = 0`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (6.2.1).
-/

public section

namespace TauCeti

open ContCohomology groupCohomology

section FiniteLevel

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]

/-- **Hilbert 90 at a finite layer of a Galois extension.** For an open normal subgroup `U` of
`Gal(L/K)`, every `1`-cocycle of the finite group `Gal(L/K) ⧸ U` with values in the invariant
units `(Lˣ)^U`, written additively, is a coboundary. No continuity is assumed: the quotient is
finite, and this is the finite-level vanishing of `H¹(Gal(L/K) ⧸ U, (Lˣ)^U)`. -/
theorem isCoboundary₁_of_isCocycle₁_of_quotient_to_fixedPoints (U : OpenNormalSubgroup Gal(L/K))
    {f : Gal(L/K) ⧸ U.toSubgroup → FixedPoints.addSubgroup U.toSubgroup (Additive Lˣ)}
    (hf : IsCocycle₁ f) : IsCoboundary₁ f := by
  -- The fixed field `F` of `U` is finite Galois over `K`, with group `Gal(L/K) ⧸ U`.
  let H : ClosedSubgroup Gal(L/K) := ⟨U.toSubgroup, U.toOpenSubgroup.isClosed⟩
  let F := IntermediateField.fixedField U.toSubgroup
  have : FiniteDimensional K F := by
    refine (InfiniteGalois.isOpen_iff_finite F).1 ?_
    rw [InfiniteGalois.fixingSubgroup_fixedField H]
    exact U.isOpen
  let e : Gal(L/K) ⧸ U.toSubgroup ≃* Gal(F/K) := InfiniteGalois.normalAutEquivQuotient H
  have he (σ : Gal(L/K)) (x : F) : ((e σ x : F) : L) = σ x := by
    rw [InfiniteGalois.normalAutEquivQuotient_apply]
    exact AlgEquiv.restrictNormal_commutes σ F x
  -- A unit of `L` fixed by `U` is a unit of `F`.
  have hmem (m : FixedPoints.addSubgroup U.toSubgroup (Additive Lˣ)) :
      ((m : Additive Lˣ).toMul : L) ∈ F :=
    (IntermediateField.mem_fixedField_iff _ _).2 fun σ hσ => by
      simpa [AlgEquiv.smul_units_def] using
        congrArg (fun v : Additive Lˣ => ((v.toMul : Lˣ) : L)) (m.2 ⟨σ, hσ⟩)
  -- The cocycle `f`, transported to `Gal(F/K) → Fˣ`.
  let g : Gal(F/K) → Fˣ := fun τ =>
    Units.mk0 ⟨_, hmem (f (e.symm τ))⟩ fun h => (f (e.symm τ) : Additive Lˣ).toMul.ne_zero
      (congrArg Subtype.val h)
  have hg_apply (q : Gal(L/K) ⧸ U.toSubgroup) :
      ((g (e q) : F) : L) = ((f q : Additive Lˣ).toMul : L) := by
    simp [g]
  have hg : IsMulCocycle₁ g := by
    intro τ₁ τ₂
    obtain ⟨q₁, rfl⟩ := e.surjective τ₁
    obtain ⟨q₂, rfl⟩ := e.surjective τ₂
    obtain ⟨σ₁, rfl⟩ := QuotientGroup.mk_surjective q₁
    refine Units.ext (Subtype.ext ?_)
    rw [← map_mul, hg_apply, hf]
    simp [AlgEquiv.smul_units_def, hg_apply, he]
  -- Noether's Hilbert 90 for `F/K` gives `β`, which read in `L` is the required `U`-invariant.
  obtain ⟨β, hβ⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units g hg
  refine ⟨⟨Additive.ofMul (Units.map (F.val : F →* L) β), fun σ => ?_⟩, fun q => ?_⟩
  · refine Additive.toMul.injective (Units.ext ?_)
    simpa [Subgroup.smul_def, AlgEquiv.smul_units_def] using
      (IntermediateField.mem_fixedField_iff _ _).1 (β : F).2 σ σ.2
  · obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective q
    refine Subtype.ext (Additive.toMul.injective (Units.ext ?_))
    rw [← hg_apply, ← hβ]
    simp [AlgEquiv.smul_units_def, he]

end FiniteLevel

/-- **Hilbert 90 for a Galois extension** `L/K`, finite or not: the continuous `H¹(Gal(L/K), Lˣ)`
vanishes, the units of `L` being written additively and carrying the discrete topology
(NSW (6.2.1)). Every class is inflated from a finite layer, where it vanishes by
`TauCeti.isCoboundary₁_of_isCocycle₁_of_quotient_to_fixedPoints`.

The continuity of the action is automatic for the discrete topology
(`TauCeti.stabilizer_isOpen_units`) and is an instance argument only because `H¹` is formed under
it. -/
theorem subsingleton_H1_additive_units {K L : Type*} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] [TopologicalSpace (Additive Lˣ)] [DiscreteTopology (Additive Lˣ)]
    [ContinuousSMul Gal(L/K) (Additive Lˣ)] :
    Subsingleton (H1 Gal(L/K) (Additive Lˣ)) :=
  subsingleton_H1_of_forall_openNormalSubgroup fun U => subsingleton_of_forall_eq 0 fun x => by
    induction x using QuotientAddGroup.induction_on with
    | H z =>
      exact H1pi_eq_zero_iff.2 (mem_B1_iff.2
        (isCoboundary₁_of_isCocycle₁_of_quotient_to_fixedPoints U (mem_Z1_iff.1 z.2).2))

variable (K : Type*) [Field K]

/-- **Hilbert 90 for the absolute Galois group**: `H¹(G_K, (Kˢ)ˣ) = 0`. -/
instance subsingleton_H1_unitsCoeff :
    Subsingleton (H1 (AbsoluteGaloisGroup K) (UnitsCoeff K)) :=
  subsingleton_H1_additive_units

end TauCeti
