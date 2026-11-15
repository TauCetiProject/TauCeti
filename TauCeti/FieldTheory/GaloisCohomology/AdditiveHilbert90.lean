/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic
public import TauCeti.FieldTheory.KrullTopology
public import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.Colimit
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete.Basic
import TauCeti.Algebra.GroupAction.Equiv
import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison

/-!
# The additive Hilbert 90

For a Galois extension `L/K`, finite or infinite, the first continuous cohomology of `Gal(L/K)`
with coefficients in the additive group of `L`, carrying the discrete topology, vanishes:

```text
H¹(Gal(L/K), L) = 0.
```

For a separable closure this is `H¹(G_K, Kˢ) = 0`. It is the additive companion of Hilbert 90,
`H¹(G_K, (Kˢ)ˣ) = 0` (`TauCeti/FieldTheory/GaloisCohomology/Hilbert90.lean`). The two vanishing
theorems, in their form for explicit locally constant cocycles, are the inputs to the vanishing of
the first Galois cohomology of the admissible changes of variables `(u, r, s, t)` of Weierstrass
equations: the scaling `u` is a unit, and the changes with `u = 1` are built from three copies of
the additive group, one for each of `r`, `s` and `t`. That vanishing, which lets a Galois cocycle of
changes of variables descend a Weierstrass equation, is
`WeierstrassCurve.VariableChange.exists_eq_mul_map_inv`.

The finite case is Noether's argument with the sum over all `K`-automorphisms in place of a norm.
For a finite extension `L/K` the automorphisms of `L/K` are linearly independent over `L`
(Dedekind), so their sum is not identically zero: some `z ∈ L` has `c = ∑_τ τ z ≠ 0`, and `c` is
fixed by every automorphism. For a `1`-cocycle `f`, the cocycle identity
`f (σ τ) = σ (f τ) + f σ` gives `σ (∑_τ f τ · τ z) = ∑_τ f τ · τ z - f σ · c`, so
`x = -(∑_τ f τ · τ z) / c` satisfies `σ x - x = f σ`. The infinite case passes to finite layers,
exactly as for Hilbert 90: every continuous class is inflated from a finite quotient
`Gal(L/K) ⧸ U`, which is the Galois group of the finite Galois subextension fixed by `U`.

## Main results

* `TauCeti.isCoboundary₁_of_isCocycle₁_of_aut`: for a finite extension `L/K`, every `1`-cocycle
  `Gal(L/K) → L` is a coboundary.
* `TauCeti.H1ofAutUnique`: for a finite extension `L/K`, `H¹(Gal(L/K), L) = 0` in Mathlib's group
  cohomology.
* `TauCeti.isCoboundary₁_of_isCocycle₁_of_quotient_to_fixedPoints_forcedDiscrete`: the additive
  Hilbert 90 at a finite layer `Gal(L/K) ⧸ U`, with coefficients in `L^U`.
* `TauCeti.subsingleton_H1_forcedDiscrete`: `H¹(Gal(L/K), L) = 0` for any Galois `L/K`.
* `TauCeti.isCoboundary₁_of_isCocycle₁_of_isLocallyConstant`: the same for an explicit locally
  constant cocycle `Gal(L/K) → L`.
* `TauCeti.subsingleton_H1_forcedDiscrete_separableClosure` and `TauCeti.additiveHilbert90`:
  `H¹(G_K, Kˢ) = 0`, for the explicit and for Mathlib's canonical continuous cohomology.

## References

* J.-P. Serre, *Local Fields*, X, §1, Proposition 1.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter VI, §1.
-/

public section

namespace TauCeti

open ContCohomology groupCohomology
open CategoryTheory

section FiniteExtension

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **The additive Hilbert 90 for a finite extension.** For a finite extension `L/K`, every
function `f : Gal(L/K) → L` satisfying the `1`-cocycle condition `f (σ τ) = σ (f τ) + f σ` is a
coboundary: there is `x : L` with `σ x - x = f σ` for every `σ`. No separability is assumed: the
group is the group of all automorphisms of `L/K`. -/
theorem isCoboundary₁_of_isCocycle₁_of_aut (f : Gal(L/K) → L) (hf : IsCocycle₁ f) :
    IsCoboundary₁ f := by
  -- By Dedekind's independence of characters, the sum of the automorphisms is not zero; this is
  -- Mathlib's `Hilbert90.aux_ne_zero` for the constant family `1`.
  obtain ⟨z, hz⟩ : ∃ z, Hilbert90.aux (K := K) (fun _ => (1 : Lˣ)) z ≠ 0 :=
    not_forall.1 fun H => Hilbert90.aux_ne_zero (K := K) (fun _ => (1 : Lˣ)) (funext H)
  have hc : Hilbert90.aux (K := K) (fun _ => (1 : Lˣ)) z = ∑ τ : Gal(L/K), τ z := by
    simp [Hilbert90.aux, Finsupp.linearCombination, Finsupp.sum_fintype]
  rw [hc] at hz
  set c := ∑ τ : Gal(L/K), τ z
  -- The sum `c` is fixed by every automorphism.
  have hσc (σ : Gal(L/K)) : σ c = c := by
    rw [map_sum]
    exact Fintype.sum_bijective (σ * ·) (Group.mulLeft_bijective σ) _ _ fun τ => rfl
  refine ⟨-(∑ τ : Gal(L/K), f τ * τ z) / c, fun σ => ?_⟩
  -- Apply the cocycle identity to `σ (∑ f τ · τ z)` and reindex by `τ ↦ σ τ`.
  have hS : σ (∑ τ : Gal(L/K), f τ * τ z) = ∑ τ : Gal(L/K), f τ * τ z - f σ * c := by
    simp only [map_sum, map_mul]
    have h (τ : Gal(L/K)) : σ (f τ) * σ (τ z) = f (σ * τ) * (σ * τ) z - f σ * (σ * τ) z := by
      rw [hf σ τ, AlgEquiv.smul_def, AlgEquiv.mul_apply]
      ring
    simp_rw [h, Finset.sum_sub_distrib, ← Finset.mul_sum]
    congr 1
    · exact Fintype.sum_bijective (σ * ·) (Group.mulLeft_bijective σ) _ _ fun τ => rfl
    · simp_rw [AlgEquiv.mul_apply, ← map_sum]
      exact congrArg (f σ * ·) (hσc σ)
  rw [AlgEquiv.smul_def, map_div₀, map_neg, hσc, hS]
  field_simp
  ring

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **The additive Hilbert 90 for a finite extension**, in Mathlib's group cohomology: the first
group cohomology `H¹(Gal(L/K), L)` of the automorphism group of a finite extension `L/K`, acting on
the additive group of `L`, is trivial. -/
noncomputable instance H1ofAutUnique : Unique (H1 (Rep.ofAlgebraAut K L)) where
  default := 0
  uniq := fun a => H1_induction_on a fun x => (H1π_eq_zero_iff _).2 <| by
    refine (coboundariesOfIsCoboundary₁ ?_).2
    exact isCoboundary₁_of_isCocycle₁_of_aut x.1 (isCocycle₁_of_mem_cocycles₁ _ x.2)

end FiniteExtension

section Galois

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

variable [IsGalois K L]

/-- **The additive Hilbert 90 at a finite layer of a Galois extension.** For an open normal
subgroup `U` of `Gal(L/K)`, every `1`-cocycle of the finite group `Gal(L/K) ⧸ U` with values in the
invariants `L^U` is a coboundary. No continuity is assumed: the quotient is finite, and this is the
finite-level vanishing of `H¹(Gal(L/K) ⧸ U, L^U)`. -/
theorem isCoboundary₁_of_isCocycle₁_of_quotient_to_fixedPoints_forcedDiscrete
    (U : OpenNormalSubgroup Gal(L/K))
    {f : Gal(L/K) ⧸ U.toSubgroup → FixedPoints.addSubgroup U.toSubgroup (ForcedDiscrete L)}
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
  -- An element of `L` fixed by `U` lies in `F`.
  have hmem (m : FixedPoints.addSubgroup U.toSubgroup (ForcedDiscrete L)) :
      (ForcedDiscrete.addEquiv L).symm m ∈ F :=
    (IntermediateField.mem_fixedField_iff _ _).2 fun σ hσ => m.2 ⟨σ, hσ⟩
  -- The cocycle `f`, transported to `Gal(F/K) → F`.
  let g : Gal(F/K) → F := fun τ => ⟨_, hmem (f (e.symm τ))⟩
  have hg_apply (q : Gal(L/K) ⧸ U.toSubgroup) :
      ((g (e q) : F) : L) = (ForcedDiscrete.addEquiv L).symm (f q) := by
    simp [g]
  have hg : IsCocycle₁ g := by
    intro τ₁ τ₂
    obtain ⟨q₁, rfl⟩ := e.surjective τ₁
    obtain ⟨q₂, rfl⟩ := e.surjective τ₂
    obtain ⟨σ₁, rfl⟩ := QuotientGroup.mk_surjective q₁
    refine Subtype.ext ?_
    rw [← map_mul, hg_apply, hf]
    simp [AlgEquiv.smul_def, hg_apply, he, AddEquiv.symm_map_smul_of_map_smul
      (ForcedDiscrete.addEquiv L) (fun g x => (ForcedDiscrete.smul_addEquiv g x).symm)]
  -- The finite additive Hilbert 90 for `F/K` gives `β`, which read in `L` is the `U`-invariant.
  obtain ⟨β, hβ⟩ := isCoboundary₁_of_isCocycle₁_of_aut g hg
  refine ⟨⟨ForcedDiscrete.addEquiv L (β : L), fun σ => ?_⟩, fun q => ?_⟩
  · simpa [Subgroup.smul_def] using
      (IntermediateField.mem_fixedField_iff _ _).1 β.2 σ σ.2
  · obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective q
    refine Subtype.ext ?_
    rw [← (ForcedDiscrete.addEquiv L).apply_symm_apply (f _), ← hg_apply, ← hβ]
    simp [AlgEquiv.smul_def, he]

/-- **The additive Hilbert 90 for a Galois extension** `L/K`, finite or not: the continuous
`H¹(Gal(L/K), L)` vanishes, the additive group of `L` carrying the discrete topology. Every class
is inflated from a finite layer, where it vanishes by
`TauCeti.isCoboundary₁_of_isCocycle₁_of_quotient_to_fixedPoints_forcedDiscrete`. -/
theorem subsingleton_H1_forcedDiscrete : Subsingleton (H1 Gal(L/K) (ForcedDiscrete L)) :=
  subsingleton_H1_of_forall_openNormalSubgroup fun U => subsingleton_of_forall_eq 0 fun x => by
    induction x using QuotientAddGroup.induction_on with
    | H z =>
      exact H1pi_eq_zero_iff.2 (mem_B1_iff.2
        (isCoboundary₁_of_isCocycle₁_of_quotient_to_fixedPoints_forcedDiscrete U
          (mem_Z1_iff.1 z.2).2))

/-- **The additive Hilbert 90 for explicit cocycles.** For a Galois extension `L/K`, finite or
not, every locally constant `1`-cocycle `f : Gal(L/K) → L`, that is
`f (σ * τ) = σ (f τ) + f σ`, is a coboundary: `f σ = σ x - x` for some `x : L`. -/
theorem isCoboundary₁_of_isCocycle₁_of_isLocallyConstant {f : Gal(L/K) → L}
    (hf : IsCocycle₁ f) (hc : IsLocallyConstant f) : IsCoboundary₁ f := by
  have := subsingleton_H1_forcedDiscrete (K := K) (L := L)
  have hz : ForcedDiscrete.addEquiv L ∘ f ∈ Z1 Gal(L/K) (ForcedDiscrete L) := by
    refine mem_Z1_iff.2 ⟨(hc.comp _).continuous, fun σ τ ↦ ?_⟩
    simp only [Function.comp_apply, hf σ τ, map_add, ForcedDiscrete.smul_addEquiv]
  obtain ⟨x, hx⟩ := mem_B1_iff.1 (H1pi_eq_zero_iff.1 (Subsingleton.elim (H1pi _ _ ⟨_, hz⟩) 0))
  obtain ⟨y, rfl⟩ := (ForcedDiscrete.addEquiv L).surjective x
  refine ⟨y, fun σ ↦ (ForcedDiscrete.addEquiv L).injective ?_⟩
  rw [map_sub, ← ForcedDiscrete.smul_addEquiv]
  exact hx σ

end Galois

variable (K : Type*) [Field K]

/-- **The additive Hilbert 90 for the absolute Galois group**: `H¹(G_K, Kˢ) = 0`. -/
instance subsingleton_H1_forcedDiscrete_separableClosure :
    Subsingleton (H1 (AbsoluteGaloisGroup K) (ForcedDiscrete (SeparableClosure K))) :=
  subsingleton_H1_forcedDiscrete

/-- **The additive Hilbert 90 for the absolute Galois group**, stated for Mathlib's canonical
continuous cohomology: `H¹(G_K, Kˢ) = 0`. -/
theorem additiveHilbert90 :
    Limits.IsZero (continuousCohomology 1
      (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (ForcedDiscrete (SeparableClosure K)))) :=
  isZero_continuousCohomology_one_of_subsingleton _ _

end TauCeti
