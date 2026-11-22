/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Kernel
public import TauCeti.Topology.Algebra.Nonarchimedean.Basic

/-!
# Unit-weight restricted power series over a subring

For any subring `R` of a commutative nonarchimedean topological ring `A` equipped with the subspace
topology, the trivial-weight restricted power series ring `R⟨X₁, …, Xₖ⟩` identifies canonically as
a ring with the coefficientwise subring `TauCeti.Huber.weightedSubring` of `R`-bounded series in
`A⟨X₁, …, Xₖ⟩`.

The map in the forward direction codomain-restricts `TauCeti.Huber.weightedMap` along the
continuous subring inclusion `R ↪ A`, so injectivity follows from
`TauCeti.Huber.weightedMap_injective`. Conversely, a series in `A⟨X⟩` all of whose coefficients
lie in `R` has coefficients tending to zero in the subspace topology on `R`, giving a restricted
series over `R`.

## Main definitions

* `TauCeti.Huber.weightedRestrictedSubringEquivWeightedSubring`: the canonical ring isomorphism
  `(↥R)⟨X₁, …, Xₖ⟩ ≃+* R⟨X₁, …, Xₖ⟩`.

## Main results

* `TauCeti.Huber.coe_weightedRestrictedSubringEquivWeightedSubring`,
  `TauCeti.Huber.coeff_weightedRestrictedSubringEquivWeightedSubring`, and
  `TauCeti.Huber.coeff_weightedRestrictedSubringEquivWeightedSubring_symm`: underlying series and
  coefficient computation rules.
* `TauCeti.Huber.weightedRestrictedSubringEquivWeightedSubring_weightedC`,
  `TauCeti.Huber.weightedRestrictedSubringEquivWeightedSubring_weightedX`, and
  `TauCeti.Huber.weightedRestrictedSubringEquivWeightedSubring_weightedPolynomialHom` (with their
  `.symm` counterparts): behavior on constants, coordinate variables, and polynomials.
-/

public section

namespace TauCeti.Huber

open Filter Topology

variable {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- Every coordinate variable `Xᵢ` belongs to `R⟨X₁, …, Xₖ⟩` at unit weights. -/
theorem weightedX_mem_weightedSubring_one_weight (R : Subring A) (i : Fin k) :
    weightedX (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight i ∈
      weightedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight R := by
  rw [mem_weightedSubring, mem_weightedNhd]
  intro ν
  rw [weightMul_one_weight, coe_weightedX, MvPowerSeries.coeff_X, Subring.mem_toAddSubgroup]
  split_ifs
  exacts [R.one_mem, R.zero_mem]

/-- Every polynomial with coefficients in `R` maps into `R⟨X₁, …, Xₖ⟩` at unit weights. -/
theorem weightedPolynomialHom_map_mem_weightedSubring_one_weight (R : Subring A)
    (p : MvPolynomial (Fin k) R) :
    weightedPolynomialHom (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight
        (MvPolynomial.map R.subtype p) ∈
      weightedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight R := by
  rw [mem_weightedSubring, mem_weightedNhd]
  intro ν
  rw [weightMul_one_weight, coe_weightedPolynomialHom, MvPolynomial.coeff_coe,
    MvPolynomial.coeff_map, Subring.coe_subtype, Subring.mem_toAddSubgroup]
  exact (p.coeff ν).property

omit [NonarchimedeanRing A] in
private theorem continuous_subringSubtype (R : Subring A) : Continuous R.subtype :=
  continuous_subtypeVal

private noncomputable def weightedMapToWeightedSubring (R : Subring A) :
    weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight →+*
      weightedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight R :=
  (weightedMap (φ := R.subtype) (continuous_subringSubtype R) isWeightFamily_one_weight
      isWeightFamily_one_weight (fun _ ↦ by simp)).codRestrict _ fun f ↦ by
    rw [mem_weightedSubring, mem_weightedNhd]
    intro ν
    rw [weightMul_one_weight, coe_weightedMap, MvPowerSeries.coeff_map, Subring.coe_subtype,
      Subring.mem_toAddSubgroup]
    exact (MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) R)).property

/-- **Unit-weight restricted series over a subring.** For a subring `R` of `A` with the subspace
topology, the trivial-weight restricted power series ring over `R` is canonically isomorphic to the
subring `R⟨X₁, …, Xₖ⟩` of series in `A⟨X₁, …, Xₖ⟩` with coefficients in `R`. -/
noncomputable def weightedRestrictedSubringEquivWeightedSubring (R : Subring A) :
    weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight ≃+*
      weightedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight R := by
  refine RingEquiv.ofBijective (weightedMapToWeightedSubring R) ⟨fun f g h ↦
      weightedMap_injective (φ := R.subtype) (continuous_subringSubtype R) Subtype.val_injective
        (congrArg Subtype.val h), fun g ↦ ?_⟩
  let f : MvPowerSeries (Fin k) R := fun ν ↦
    ⟨MvPowerSeries.coeff ν ((g.val : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
        isWeightFamily_one_weight) : MvPowerSeries (Fin k) A),
      by simpa only [weightMul_one_weight, Subring.mem_toAddSubgroup] using
        mem_weightedNhd.mp (mem_weightedSubring.mp g.property) ν⟩
  have hf : IsWeightedRestricted (fun _ : Fin k ↦ ({1} : Set R)) f :=
    isWeightedRestricted_one_weight_iff.mpr <| tendsto_subtype_rng.mpr <|
      isWeightedRestricted_one_weight_iff.mp (mem_weightedRestrictedSubring.mp g.val.property)
  refine ⟨⟨f, mem_weightedRestrictedSubring.mpr hf⟩,
    Subtype.ext <| Subtype.ext <| MvPowerSeries.ext fun ν ↦ ?_⟩
  simp only [weightedMapToWeightedSubring, RingHom.codRestrict_apply, coe_weightedMap,
    MvPowerSeries.coeff_map, Subring.coe_subtype]
  rfl

/-- `weightedRestrictedSubringEquivWeightedSubring R` acts on underlying formal power series by
`MvPowerSeries.map R.subtype`. -/
@[simp]
theorem coe_weightedRestrictedSubringEquivWeightedSubring (R : Subring A)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    ((weightedRestrictedSubringEquivWeightedSubring R f :
        weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
        MvPowerSeries (Fin k) A) =
      MvPowerSeries.map R.subtype (f : MvPowerSeries (Fin k) R) :=
  coe_weightedMap (continuous_subringSubtype R) (fun _ ↦ by simp) f

/-- Each coefficient of `weightedRestrictedSubringEquivWeightedSubring R f` is the coercion of the
corresponding coefficient of `f`. -/
theorem coeff_weightedRestrictedSubringEquivWeightedSubring (R : Subring A)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight)
    (ν : Fin k →₀ ℕ) :
    MvPowerSeries.coeff ν ((weightedRestrictedSubringEquivWeightedSubring R f :
        weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
        MvPowerSeries (Fin k) A) =
      ((MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) R) : R) : A) := by
  simp only [coe_weightedRestrictedSubringEquivWeightedSubring, MvPowerSeries.coeff_map,
    Subring.coe_subtype]

/-- Each coefficient of `(weightedRestrictedSubringEquivWeightedSubring R).symm g` coerces in `A`
to the corresponding coefficient of `g`. -/
@[simp]
theorem coeff_weightedRestrictedSubringEquivWeightedSubring_symm (R : Subring A)
    (g : weightedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight R)
    (ν : Fin k →₀ ℕ) :
    ((MvPowerSeries.coeff ν ((weightedRestrictedSubringEquivWeightedSubring R).symm g :
        MvPowerSeries (Fin k) R) : R) : A) =
      MvPowerSeries.coeff ν ((g.val : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
        isWeightFamily_one_weight) : MvPowerSeries (Fin k) A) := by
  have h := congrArg (fun x : weightedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight R ↦
    MvPowerSeries.coeff ν ((x.val : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight) : MvPowerSeries (Fin k) A))
    ((weightedRestrictedSubringEquivWeightedSubring R).apply_symm_apply g)
  simpa only [coeff_weightedRestrictedSubringEquivWeightedSubring] using h

/-- `weightedRestrictedSubringEquivWeightedSubring R` sends constant series to constant series. -/
@[simp]
theorem weightedRestrictedSubringEquivWeightedSubring_weightedC (R : Subring A) (a : R) :
    weightedRestrictedSubringEquivWeightedSubring R
        (weightedC (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight a) =
      ⟨weightedC _ isWeightFamily_one_weight (a : A),
        (weightedC_mem_weightedSubring isWeightFamily_one_weight).mpr a.property⟩ :=
  Subtype.ext <| Subtype.ext (by simp [MvPowerSeries.map_C])

/-- `(weightedRestrictedSubringEquivWeightedSubring R).symm` sends constant series in `R` to
constant series over `R`. -/
@[simp]
theorem weightedRestrictedSubringEquivWeightedSubring_symm_weightedC (R : Subring A) (a : R) :
    (weightedRestrictedSubringEquivWeightedSubring R).symm
        ⟨weightedC (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight (a : A),
          (weightedC_mem_weightedSubring isWeightFamily_one_weight).mpr a.property⟩ =
      weightedC _ isWeightFamily_one_weight a :=
  (weightedRestrictedSubringEquivWeightedSubring R).symm_apply_eq.mpr
    (weightedRestrictedSubringEquivWeightedSubring_weightedC R a).symm

/-- `weightedRestrictedSubringEquivWeightedSubring R` preserves coordinate variables. -/
@[simp]
theorem weightedRestrictedSubringEquivWeightedSubring_weightedX (R : Subring A) (i : Fin k) :
    weightedRestrictedSubringEquivWeightedSubring R
        (weightedX (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight i) =
      ⟨weightedX _ isWeightFamily_one_weight i, weightedX_mem_weightedSubring_one_weight R i⟩ :=
  Subtype.ext <| Subtype.ext (by simp [MvPowerSeries.map_X])

/-- `(weightedRestrictedSubringEquivWeightedSubring R).symm` preserves coordinate variables. -/
@[simp]
theorem weightedRestrictedSubringEquivWeightedSubring_symm_weightedX (R : Subring A) (i : Fin k) :
    (weightedRestrictedSubringEquivWeightedSubring R).symm
        ⟨weightedX (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight i,
          weightedX_mem_weightedSubring_one_weight R i⟩ =
      weightedX _ isWeightFamily_one_weight i :=
  (weightedRestrictedSubringEquivWeightedSubring R).symm_apply_eq.mpr
    (weightedRestrictedSubringEquivWeightedSubring_weightedX R i).symm

/-- `weightedRestrictedSubringEquivWeightedSubring R` sends embedded polynomials over `R` to their
coefficient-mapped counterparts in `R⟨X₁, …, Xₖ⟩`. -/
@[simp]
theorem weightedRestrictedSubringEquivWeightedSubring_weightedPolynomialHom (R : Subring A)
    (p : MvPolynomial (Fin k) R) :
    weightedRestrictedSubringEquivWeightedSubring R
        (weightedPolynomialHom (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight p) =
      ⟨weightedPolynomialHom _ isWeightFamily_one_weight (MvPolynomial.map R.subtype p),
        weightedPolynomialHom_map_mem_weightedSubring_one_weight R p⟩ :=
  Subtype.ext <| Subtype.ext <| MvPowerSeries.ext fun ν ↦ by
    simp [MvPolynomial.coeff_coe, MvPolynomial.coeff_map]

/-- `(weightedRestrictedSubringEquivWeightedSubring R).symm` lifts embedded polynomials with
coefficients in `R`. -/
@[simp]
theorem weightedRestrictedSubringEquivWeightedSubring_symm_weightedPolynomialHom (R : Subring A)
    (p : MvPolynomial (Fin k) R) :
    (weightedRestrictedSubringEquivWeightedSubring R).symm
        ⟨weightedPolynomialHom (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight
            (MvPolynomial.map R.subtype p),
          weightedPolynomialHom_map_mem_weightedSubring_one_weight R p⟩ =
      weightedPolynomialHom _ isWeightFamily_one_weight p :=
  (weightedRestrictedSubringEquivWeightedSubring R).symm_apply_eq.mpr
    (weightedRestrictedSubringEquivWeightedSubring_weightedPolynomialHom R p).symm

end TauCeti.Huber
