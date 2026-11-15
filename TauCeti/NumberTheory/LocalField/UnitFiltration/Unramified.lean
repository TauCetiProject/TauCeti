/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Unramified.Basic
public import TauCeti.NumberTheory.LocalField.UnitFiltration.HerbrandQuotient
import TauCeti.FieldTheory.GaloisCohomology.Inflation
import TauCeti.NumberTheory.LocalField.Norm.Unramified.Basic
import TauCeti.NumberTheory.LocalField.ResidueCorrespondence

/-!
# The units of an unramified extension have no Tate cohomology

Let `L/K` be a finite unramified Galois extension of nonarchimedean local fields, with Galois
group `G`. This file proves that the unit group `𝒪[L]ˣ = U(L, 0)`, with its Galois action and
read as an integral representation of `G`, has vanishing Tate cohomology in every degree.

In degree zero, `H-hat^0(G, 𝒪[L]ˣ) = 𝒪[K]ˣ / N_{L/K}(𝒪[L]ˣ)` vanishes because the norm of
an unramified extension maps `𝒪[L]ˣ` onto `𝒪[K]ˣ` (`TauCeti.map_normUnits_unitFiltration`). The
group `G` is cyclic (`TauCeti.isCyclic_algEquiv`) and the Herbrand quotient of `𝒪[L]ˣ` is `1`
(`TauCeti.TateCohomology.herbrandQuotient_unitFiltration_zero`), so `H-hat^(-1)(G, 𝒪[L]ˣ)`
vanishes as well, and two-periodicity gives every other degree.

The statement concerns the whole group `G`. Since `L/E` is again unramified for every intermediate
field `E`, the same theorem over `E` applies to the subgroup `Gal(L/E)` of `G`.

This is the local factor at the places outside `S` in the computation of the Herbrand quotient
of the `S`-ideles of a cyclic extension of number fields: the unit groups at places unramified
in `L` contribute nothing to the Tate cohomology of the ideles.

⚠ For ramified extensions only the Herbrand quotient survives: for `L = ℚ_2(√2)` the norms of the
units of `𝒪[L]` have index `2` in `ℤ_2ˣ`, so `H-hat^0(G, 𝒪[L]ˣ)` has order `2`.

## Main results

* `TauCeti.TateCohomology.isZero_tateCohomology_unitFiltration_zero_of_isUnramified`:
  `H-hat^n(G, 𝒪[L]ˣ) = 0` for every `n : ℤ`, for an unramified Galois extension `L/K`.

## References

* J.-P. Serre, *Local Fields*, Chapter V, §2, Proposition 3 and Chapter VIII, §1.
* J. S. Milne, *Class Field Theory*, Chapter III, Proposition 1.2 and Chapter VII, Lemma 2.4.
-/

public section

open CategoryTheory Limits ValuativeRel

namespace TauCeti.TateCohomology

variable {K L : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]
  [IsGalois K L] [IsUnramified K L]

/-- Degree zero: for a finite unramified Galois extension `L/K`, every Galois-invariant unit of
`𝒪[L]` is the norm of a unit of `𝒪[L]`, since it lies in `𝒪[K]ˣ`, which the norm of an
unramified extension maps `𝒪[L]ˣ` onto. -/
private theorem isZero_tateCohomology_zero_unitFiltration_zero_of_isUnramified :
    IsZero (tateCohomology (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (unitFiltration L 0)) 0) := by
  refine ModuleCat.isZero_iff_subsingleton.2 (subsingleton_of_forall_eq 0 fun x ↦ ?_)
  induction x using H0_induction_on with | h y => ?_
  rw [H0π_eq_zero_iff, Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
  -- the invariant unit `u` comes from a unit `a` of `K`, which is again a unit of `𝒪[K]`
  set u : unitFiltration L 0 :=
    (Rep.toAdditive (y : Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (unitFiltration L 0))).toMul
  -- `ρ σ` acts on `Additive (unitFiltration L 0)` through `σ`, by `rfl`
  -- (`Rep.ofMulDistribMulAction_ρ_apply_apply`, `TauCeti.val_coe_smul_unitFiltration`)
  obtain ⟨a, ha⟩ := exists_unitsMap_eq_of_forall_apply_eq (F := K) (x := (u : Lˣ)) fun σ ↦
    congr(((((Rep.toAdditive $(y.2 σ)).toMul : unitFiltration L 0) : Lˣ) : L))
  have haK : a ∈ unitFiltration K 0 := by
    rw [← ker_normalizedValuation, MonoidHom.mem_ker,
      ← normalizedValuation_algebraMap_eq_one_iff (L := L), ← MonoidHom.mem_ker,
      ker_normalizedValuation, ha]
    exact u.2
  -- and `a` is the norm of a unit `w` of `𝒪[L]`, whose representation norm is then `u`
  obtain ⟨w, hw, hwa⟩ := (map_normUnits_unitFiltration K L 0).ge haK
  refine ⟨Rep.toAdditive.symm (Additive.ofMul ⟨w, hw⟩), ?_⟩
  apply Rep.toAdditive.injective
  apply Additive.toMul.injective
  refine Subtype.ext (Units.ext ?_)
  rw [← ha]
  refine (coe_norm_unitFiltrationZero K L _).trans (congrArg (algebraMap K L) ?_)
  rw [AddEquiv.apply_symm_apply, toMul_ofMul, ← hwa, Algebra.coe_normUnits]

/-- **The units of an unramified extension have no Tate cohomology.** For a finite unramified
Galois extension `L/K` of nonarchimedean local fields, the unit group `𝒪[L]ˣ` has vanishing Tate
cohomology `H-hat^n(Gal(L/K), 𝒪[L]ˣ)` in every degree `n : ℤ`. -/
theorem isZero_tateCohomology_unitFiltration_zero_of_isUnramified (n : ℤ) :
    IsZero (tateCohomology (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (unitFiltration L 0)) n) := by
  set M := Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (unitFiltration L 0)
  have h₀ := isZero_tateCohomology_zero_unitFiltration_zero_of_isUnramified (K := K) (L := L)
  have h₁ : IsZero (tateCohomology M (-1)) := by
    have := ModuleCat.isZero_iff_subsingleton.1 h₀
    have hq := herbrandQuotient_unitFiltration_zero (K := K) (L := L)
    rw [herbrandQuotient_def, Nat.card_unique, Nat.cast_one, one_div, inv_eq_one,
      Nat.cast_eq_one, Nat.card_eq_one_iff_unique] at hq
    exact ModuleCat.isZero_iff_subsingleton.2 hq.1
  rcases Int.emod_two_eq_zero_or_one n with hn | hn
  · exact h₀.of_iso (Rep.FiniteCyclicGroup.periodicIso M n 0 (by rw [Int.ModEq, hn]; rfl))
  · exact h₁.of_iso (Rep.FiniteCyclicGroup.periodicIso M n (-1) (by rw [Int.ModEq, hn]; rfl))

end TauCeti.TateCohomology
