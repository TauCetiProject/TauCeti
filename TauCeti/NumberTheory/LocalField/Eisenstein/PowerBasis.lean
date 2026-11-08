/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Norm.Basic
public import TauCeti.RingTheory.Valuation.Orthogonality
public import TauCeti.RingTheory.Polynomial.Eisenstein.DiscreteValuationRing
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import TauCeti.RingTheory.Polynomial.Eisenstein.Minpoly
import TauCeti.NumberTheory.LocalField.MultiplicativeGroup

/-!
# Valuations in an Eisenstein power basis of a local field

Let `ξ ∈ 𝒪[L]` be a root of an Eisenstein polynomial `f` over `𝒪[K]` with `L = K(ξ)`. Comparing
the normalized valuations of `ξ` and of its norm, which is the constant coefficient of `f` up to
a unit, shows that `ξ` is a uniformizer of `L` and that `L/K` has inertia degree one, so that
`e(L/K) = [L : K] = deg f`. By `TauCeti.addVal_sum_algebraMap_mul_pow_of_irreducible`, the
valuation of a linear combination in the power basis `1, ξ, …, ξ^{deg f - 1}` is therefore the
minimum of its term valuations.

## Main result

* `TauCeti.irreducible_of_eisenstein_adjoin_eq_top` shows that a generator of `L/K` satisfying
  an Eisenstein polynomial is a uniformizer.
* `TauCeti.inertiaDegree_eq_one_of_eisenstein_adjoin_eq_top` and
  `TauCeti.ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top` record its characteristic
  total-ramification consequences.
* `TauCeti.addVal_sum_eisenstein_powerBasis` computes the additive valuation of a linear
  combination of powers of an Eisenstein generator.

## References

* J.-P. Serre, *Local Fields*, Chapter I, §6, Proposition 17.
* J.-P. Serre, *Local Fields*, Chapter III, §6, Proposition 12.
-/

public section

open ValuativeRel IsLocalRing IsNonarchimedeanLocalField
open scoped IntermediateField

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]

namespace TauCeti

/-- A generator of `L/K` that is a root of an Eisenstein polynomial `f` over `𝒪[K]` has degree
`deg f`, and its norm is an irreducible element of `𝒪[K]`. -/
private theorem finrank_and_norm_of_eisenstein_adjoin_eq_top [Algebra K L]
    [ValuativeExtension K L] (f : Polynomial 𝒪[K]) (hf : f.IsEisensteinAt 𝓂[K])
    (ξ : 𝒪[L]) (hroot : (f.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ξ)
    (hgen : K⟮(ξ : L)⟯ = ⊤) :
    Module.finrank K L = f.natDegree ∧
      ∃ c : 𝒪[K], Irreducible c ∧ Algebra.norm K (ξ : L) = (c : K) := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  have hint : IsIntegral 𝒪[K] ξ := IsIntegral.of_finite 𝒪[K] ξ
  have hassoc : Associated (minpoly 𝒪[K] ξ) f := hf.associated_minpoly hf.isUnit_leadingCoeff hroot
  have hnatDegree : (minpoly 𝒪[K] ξ).natDegree = f.natDegree :=
    Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hassoc)
  have hdeg : 0 < f.natDegree := hnatDegree ▸ minpoly.natDegree_pos hint
  have hminpoly : minpoly K (ξ : L) = (minpoly 𝒪[K] ξ).map (algebraMap 𝒪[K] K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions K L hint
  -- `ξ` generates a power basis of `L/K` of length `deg f`.
  let pb : PowerBasis K L := .ofAdjoinSimpleEqTop (.of_finite K (ξ : L)) hgen
  have hpbgen : pb.gen = ξ := PowerBasis.ofAdjoinSimpleEqTop_gen _ hgen
  have hpbdim : pb.dim = f.natDegree := by
    rw [PowerBasis.ofAdjoinSimpleEqTop_dim, hminpoly, (minpoly.monic hint).natDegree_map,
      hnatDegree]
  -- Its norm is, up to sign, the constant coefficient of the minimal polynomial over `𝒪[K]`.
  have hfc0 : Irreducible (f.coeff 0) := hf.irreducible_coeff_zero hdeg
  have hminc0 : Irreducible ((minpoly 𝒪[K] ξ).coeff 0) :=
    Associated.irreducible (hassoc.map Polynomial.constantCoeff).symm hfc0
  set c : 𝒪[K] := (-1) ^ f.natDegree * (minpoly 𝒪[K] ξ).coeff 0 with hc
  have hnormirr : Irreducible c := by
    simpa [c] using (irreducible_units_mul ((-1 : 𝒪[K]ˣ) ^ f.natDegree)).mpr hminc0
  refine ⟨(PowerBasis.finrank pb).trans hpbdim, c, hnormirr, ?_⟩
  rw [← hpbgen, Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, hpbgen, hminpoly,
    hpbdim, Polynomial.coeff_map, hc]
  simp [Algebra.algebraMap_ofSubsemiring_apply]

private theorem eisenstein_adjoin_eq_top_data [Algebra K L] [ValuativeExtension K L]
    (f : Polynomial 𝒪[K]) (hf : f.IsEisensteinAt 𝓂[K])
    (ξ : 𝒪[L]) (hroot : (f.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ξ)
    (hgen : K⟮(ξ : L)⟯ = ⊤) :
    Irreducible ξ ∧ inertiaDegree K L = 1 ∧ ramificationIndex K L = f.natDegree := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  obtain ⟨hrank, c, hc, hnorm⟩ := finrank_and_norm_of_eisenstein_adjoin_eq_top f hf ξ hroot hgen
  obtain ⟨hξirr, hf_one⟩ := irreducible_and_inertiaDegree_eq_one_of_norm ξ c hc hnorm
  refine ⟨hξirr, hf_one, ?_⟩
  have hef := ramificationIndex_mul_inertiaDegree (K := K) (L := L)
  rw [hf_one, mul_one, hrank] at hef
  exact hef

/-- A generator of `L/K` that is a root of an Eisenstein polynomial over `𝒪[K]` is a uniformizer
of `𝒪[L]`. -/
theorem irreducible_of_eisenstein_adjoin_eq_top [Algebra K L] [ValuativeExtension K L]
    (f : Polynomial 𝒪[K]) (hf : f.IsEisensteinAt 𝓂[K])
    (ξ : 𝒪[L]) (hroot : (f.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ξ)
    (hgen : K⟮(ξ : L)⟯ = ⊤) : Irreducible ξ :=
  (eisenstein_adjoin_eq_top_data f hf ξ hroot hgen).1

/-- An extension `L/K` generated by a root of an Eisenstein polynomial over `𝒪[K]` has inertia
degree one. -/
theorem inertiaDegree_eq_one_of_eisenstein_adjoin_eq_top [Algebra K L] [ValuativeExtension K L]
    (f : Polynomial 𝒪[K]) (hf : f.IsEisensteinAt 𝓂[K])
    (ξ : 𝒪[L]) (hroot : (f.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ξ)
    (hgen : K⟮(ξ : L)⟯ = ⊤) : inertiaDegree K L = 1 :=
  (eisenstein_adjoin_eq_top_data f hf ξ hroot hgen).2.1

/-- For a generator of `L/K` that is a root of an Eisenstein polynomial over `𝒪[K]`, the
ramification index is the degree of that polynomial. -/
theorem ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top [Algebra K L]
    [ValuativeExtension K L] (f : Polynomial 𝒪[K]) (hf : f.IsEisensteinAt 𝓂[K])
    (ξ : 𝒪[L]) (hroot : (f.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ξ)
    (hgen : K⟮(ξ : L)⟯ = ⊤) : ramificationIndex K L = f.natDegree :=
  (eisenstein_adjoin_eq_top_data f hf ξ hroot hgen).2.2

/-- For a generator `ξ` of `L/K` that is a root of an Eisenstein polynomial `f` over `𝒪[K]`, the
additive valuation of a linear combination of `1, ξ, …, ξ^{deg f - 1}` with coefficients in
`𝒪[K]` is the least of its term valuations. -/
theorem addVal_sum_eisenstein_powerBasis [Algebra K L] [ValuativeExtension K L]
    (f : Polynomial 𝒪[K]) (hf : f.IsEisensteinAt 𝓂[K])
    (ξ : 𝒪[L]) (hroot : (f.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ξ)
    (hgen : K⟮(ξ : L)⟯ = ⊤) (c : Fin f.natDegree → 𝒪[K]) :
    IsDiscreteValuationRing.addVal 𝒪[L]
        (∑ i, algebraMap 𝒪[K] 𝒪[L] (c i) * ξ ^ (i : ℕ)) =
      ⨅ i, ramificationIndex K L • IsDiscreteValuationRing.addVal 𝒪[K] (c i) + (i : ℕ) :=
  addVal_sum_algebraMap_mul_pow_of_irreducible
    (irreducible_of_eisenstein_adjoin_eq_top f hf ξ hroot hgen)
    (ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top f hf ξ hroot hgen).ge c

end TauCeti
