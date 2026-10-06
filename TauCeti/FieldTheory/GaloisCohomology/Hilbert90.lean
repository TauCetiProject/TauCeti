/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Extension
public import TauCeti.FieldTheory.GaloisCohomology.Coefficients
public import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.Colimit
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Transgression
import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison

/-!
# Hilbert 90 for infinite Galois extensions

For a Galois extension `L/K`, finite or infinite, the first continuous cohomology of `Gal(L/K)`
with coefficients in the discrete module `Lˣ` vanishes:

```text
H¹(Gal(L/K), Lˣ) = 0.
```

Specialised to a separable closure this is Hilbert 90 for the absolute Galois group,
`H¹(G_K, (Kˢ)ˣ) = 0`, which is what makes the Kummer map `Kˣ → H¹(G_K, μₙ)` surjective for
`n` positive and invertible in `K`.

The proof passes to finite layers. An open normal subgroup `U` of `Gal(L/K)` has a fixed field `F`
that is finite Galois over `K`; the infinite Galois correspondence identifies `Gal(L/K) ⧸ U` with
`Gal(F/K)` (`InfiniteGalois.normalAutEquivQuotient`), and the units of `L` fixed by `U` are the
units of `F`. Through these two identifications a `1`-cocycle of the finite layer becomes a
multiplicative `1`-cocycle `Gal(F/K) → Fˣ`, which is a coboundary by Noether's form of Hilbert 90,
`groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`. The vanishing then passes to
`Gal(L/K)` because every continuous class is inflated from a finite layer,
`TauCeti.ContCohomology.subsingleton_H1_of_forall_openNormalSubgroup`.

For a finite group `H` of automorphisms of `L`, embedded in `Gal(L/K)` by `f`, Artin's theorem
identifies `H` with the Galois group of `L` over the fixed field of the image of `f`, so Noether's
Hilbert 90 gives `H¹(H, Lˣ) = 0` without any finiteness assumption on `L/K`.

## Main results

* `TauCeti.galEquivOfInjective`: a finite group `H` embedded in `Gal(L/K)` is the Galois group of
  `L` over the fixed field of its image.
* `TauCeti.groupCohomologyResUnitsIso`: the induced isomorphism of the cohomology of `Lˣ`.
* `TauCeti.isZero_groupCohomology_one_res_units`: `H¹(H, Lˣ) = 0` for such `H`.
* `TauCeti.isCoboundary₁_of_isCocycle₁_of_quotient_to_fixedPoints`: Hilbert 90 at a finite layer
  `Gal(L/K) ⧸ U` with coefficients `(Lˣ)^U`.
* `TauCeti.subsingleton_H1_additive_units`: `H¹(Gal(L/K), Lˣ) = 0` for any Galois `L/K`.
* `TauCeti.subsingleton_H1_unitsCoeff`: `H¹(G_K, (Kˢ)ˣ) = 0`.
* `TauCeti.subsingleton_H1_unitsCoeff_fixingSubgroup`,
  `TauCeti.subsingleton_H1_unitsCoeff_of_isClosed`: `H¹(N, (Kˢ)ˣ) = 0` for the subgroup `N` fixing
  a subextension, equivalently for every closed subgroup `N` of `G_K`.
* `TauCeti.explicitInfl2_unitsCoeff_injective`: consequently inflation from `G_K ⧸ N` into
  `H²(G_K, (Kˢ)ˣ)` is injective for every closed normal subgroup `N`.
* `TauCeti.hilbert90`: the preceding vanishing for Mathlib's canonical continuous cohomology.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (6.2.1).
-/

public section

namespace TauCeti

open ContCohomology groupCohomology
open CategoryTheory

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

section FiniteGroup

open Limits IntermediateField

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  {H : Type} [Group H] [Finite H] {f : H →* Gal(L/K)} (hf : Function.Injective f)

/-- **Artin's theorem for a finite group of automorphisms.** An injective homomorphism
`f : H →* Gal(L/K)` from a finite group identifies `H` with the Galois group of `L` over the fixed
field of the image of `f` (`FixedPoints.toAlgAutMulEquiv`). No finiteness of `L/K` is needed. -/
noncomputable def galEquivOfInjective : H ≃* Gal(L/fixedField f.range) :=
  have : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  (MonoidHom.ofInjective hf).trans (FixedPoints.toAlgAutMulEquiv f.range L)

@[simp]
theorem galEquivOfInjective_apply (h : H) (x : L) :
    galEquivOfInjective hf h x = f h x :=
  (rfl)

/-- The cohomology of a finite group `H` acting on `Lˣ` through an injective
`f : H →* Gal(L/K)` is the cohomology of `Gal(L/E)` acting on `Lˣ`, for `E` the fixed field of the
image of `f`. -/
noncomputable def groupCohomologyResUnitsIso (n : ℕ) :
    groupCohomology (Rep.res f (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) n ≅
      groupCohomology (Rep.ofMulDistribMulAction Gal(L/fixedField f.range) Lˣ) n :=
  groupCohomology.mapIso (galEquivOfInjective hf) (LinearEquiv.refl ℤ _) (fun h => by
    ext x
    exact Additive.toMul.injective (Units.ext (galEquivOfInjective_apply hf h _).symm)) n

include hf in
/-- **Hilbert 90 for a finite group of automorphisms.** If `H` is finite and
`f : H →* Gal(L/K)` is injective, then `H¹(H, Lˣ) = 0` for the action of `H` on `Lˣ` through
`f`: the group `H` is the Galois group of `L` over the fixed field of its image, and Noether's
Hilbert 90 applies to that finite extension. -/
theorem isZero_groupCohomology_one_res_units :
    IsZero (groupCohomology (Rep.res f (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) 1) := by
  refine IsZero.of_iso ?_ (groupCohomologyResUnitsIso hf 1)
  have : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  have : FiniteDimensional (fixedField f.range) L :=
    inferInstanceAs (FiniteDimensional (FixedPoints.subfield f.range L) L)
  -- `Rep.ofAlgebraAutOnUnits` unfolds to `Rep.ofMulDistribMulAction`, and `H1` to degree one.
  have : Subsingleton (groupCohomology
      (Rep.ofMulDistribMulAction Gal(L/fixedField f.range) Lˣ) 1) :=
    inferInstanceAs <| Subsingleton <|
      groupCohomology.H1 (Rep.ofAlgebraAutOnUnits (fixedField f.range) L)
  exact ModuleCat.isZero_of_subsingleton _

end FiniteGroup

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

/-- **Hilbert 90 for the subgroup of `G_K` fixing a subextension**: for a `K`-embedding
`σ : L →ₐ[K] Kˢ`, the continuous `H¹(Gal(Kˢ/σ(L)), (Kˢ)ˣ)` vanishes. The isomorphism
`G_L ≃ₜ* Gal(Kˢ/σ(L))` of `TauCeti.absoluteGaloisGroupEquivFixingSubgroup`, together with the
matching identification `(Kˢ)ˣ ≃ (Lˢ)ˣ` of coefficients, carries it to Hilbert 90 for `G_L`. -/
theorem subsingleton_H1_unitsCoeff_fixingSubgroup {L : Type*} [Field L] [Algebra K L]
    (σ : L →ₐ[K] SeparableClosure K) :
    Subsingleton (H1 ↥σ.fieldRange.fixingSubgroup (UnitsCoeff K)) :=
  (explicitMap1Equiv (↥σ.fieldRange.fixingSubgroup) (UnitsCoeff K) (AbsoluteGaloisGroup L)
    (UnitsCoeff L) (absoluteGaloisGroupEquivFixingSubgroup K L σ)
    (Units.mapEquiv (separableClosureRingEquiv K L σ).symm.toMulEquiv).toAdditive
    continuous_of_discreteTopology continuous_of_discreteTopology fun g m ↦ by
      refine Additive.toMul.injective (Units.ext ?_)
      rw [Subgroup.smul_def (α := UnitsCoeff K), Additive.toMul_smul]
      simp only [MulEquiv.toAdditive_apply_apply, toMul_ofMul, Additive.toMul_smul]
      simp [AlgEquiv.smul_units_def]).toEquiv.subsingleton_congr.2 inferInstance

/-- **Hilbert 90 for a closed subgroup of `G_K`**: `H¹(N, (Kˢ)ˣ) = 0` for every closed subgroup
`N`, which is the subgroup fixing its fixed field (`InfiniteGalois.fixingSubgroup_fixedField`). -/
theorem subsingleton_H1_unitsCoeff_of_isClosed (N : Subgroup (AbsoluteGaloisGroup K))
    (hN : IsClosed (N : Set (AbsoluteGaloisGroup K))) :
    Subsingleton (H1 N (UnitsCoeff K)) := by
  have h : (IntermediateField.fixedField N).val.fieldRange.fixingSubgroup = N := by
    rw [IntermediateField.fieldRange_val]
    exact InfiniteGalois.fixingSubgroup_fixedField ⟨N, hN⟩
  rw [← h]
  exact subsingleton_H1_unitsCoeff_fixingSubgroup K (IntermediateField.fixedField N).val

/-- **Inflation into `H²(G_K, (Kˢ)ˣ)` is injective**: for a closed normal subgroup `N` of `G_K`,
inflation `H²(G_K ⧸ N, ((Kˢ)ˣ)^N) → H²(G_K, (Kˢ)ˣ)` is injective, since by Hilbert 90 for `N`
the transgression out of `H¹(N, (Kˢ)ˣ)` vanishes. For the subgroup fixing a Galois subextension
`L/K` this is the injectivity of `H²(Gal(L/K), Lˣ)` into the cohomological Brauer group. -/
theorem explicitInfl2_unitsCoeff_injective (N : Subgroup (AbsoluteGaloisGroup K)) [N.Normal]
    (hN : IsClosed (N : Set (AbsoluteGaloisGroup K)))
    [ContinuousSMul (AbsoluteGaloisGroup K ⧸ N) (FixedPoints.addSubgroup N (UnitsCoeff K))] :
    Function.Injective (explicitInfl2 (AbsoluteGaloisGroup K) (UnitsCoeff K) N) :=
  have := subsingleton_H1_unitsCoeff_of_isClosed K N hN
  explicitInfl2_injective_of_subsingleton _ _ N hN

/-- **Hilbert 90 for the absolute Galois group**, stated for Mathlib's canonical continuous
cohomology: `H¹(G_K, (Kˢ)ˣ) = 0` (NSW (6.2.1)). This is the form in which the vanishing feeds
the canonical all-degree theory, where it makes the Kummer map `Kˣ → H¹(G_K, μₙ)` surjective for
`n` positive and invertible in `K`. -/
theorem hilbert90 :
    Limits.IsZero (continuousCohomology 1
      (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (UnitsCoeff K))) := by
  let h : Subsingleton (DiscreteH1 (AbsoluteGaloisGroup K) (UnitsCoeff K)) :=
    (discreteH1Equiv (AbsoluteGaloisGroup K) (UnitsCoeff K)).toEquiv.subsingleton_congr.mpr
      inferInstance
  rw [← (explicitH1IsoContinuousCohomology
    (AbsoluteGaloisGroup K) (UnitsCoeff K)).isZero_iff]
  rw [Limits.IsZero.iff_id_eq_zero]
  ext x
  exact h.elim _ _

end TauCeti
