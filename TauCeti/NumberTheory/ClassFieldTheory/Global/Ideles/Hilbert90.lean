/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.GaloisAction
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Relative
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.RepNorm
import TauCeti.NumberTheory.ClassFieldTheory.Global.Ideles.GaloisModule
import TauCeti.NumberTheory.ClassFieldTheory.Global.PlacewiseCohomology

/-!
# Hilbert 90 on norm-one ideles

For a cyclic extension of number fields with generator `σ`, a relative norm-one idele is
`y / σ(y)` for some idele `y`. This is the elementwise form of the vanishing of `H¹` for ideles.
We use the same cyclic cohomology comparison as Mathlib's field-level
`groupCohomology.Hilbert90.exists_div_of_norm_eq_one`.
-/

public section

open IsDedekindDomain NumberField
open scoped AdeleGaloisAction

namespace TauCeti.GlobalNumberFields

open ClassFieldTheory

/-- Hilbert 90 for a cyclic extension of number fields: an idele has relative norm one if and
only if it is the quotient of an idele by its translate under a generator. -/
theorem ideleNormMap_eq_one_iff_exists_div_smul {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [IsGalois K L] {σ : Gal(L/K)}
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) (x : IdeleGroup (𝓞 L) L) :
    ideleNormMap K L x = 1 ↔ ∃ y : IdeleGroup (𝓞 L) L, y / (σ • y) = x := by
  classical
  constructor
  · intro hx
    let a : idelesRep K L := Rep.toAdditive.symm (Additive.ofMul x)
    have ha : (idelesRep K L).norm.asHom.hom a = 0 := by
      apply Rep.toAdditive.injective
      rw [idelesRep_norm_apply, map_zero]
      simp only [a, AddEquiv.apply_symm_apply, toMul_ofMul, hx, map_one]
      rfl
    let : IsCyclic Gal(L/K) := ⟨⟨σ, hσ⟩⟩
    let := IsCyclic.commGroup (α := Gal(L/K))
    let a' : LinearMap.ker (idelesRep K L).norm.asHom.hom.toLinearMap :=
      ⟨a, LinearMap.mem_ker.mpr ha⟩
    obtain ⟨b, hb⟩ :=
      (Rep.FiniteCyclicGroup.groupCohomologyπOdd_eq_zero_iff (idelesRep K L) σ hσ 1 odd_one a').mp
        (Subsingleton.elim _ _)
    -- Read the additive coboundary `σ b - b` in the multiplicative idele group.
    have hb' : (idelesRep K L).ρ σ b - b = a := by
      simpa only [Rep.sub_hom, Rep.hom_id, Representation.IntertwiningMap.sub_toLinearMap,
        Representation.IntertwiningMap.toLinearMap_id, LinearMap.sub_apply,
        Representation.IntertwiningMap.coe_toLinearMap, Rep.applyAsHom_apply,
        LinearMap.id_coe, id_eq] using hb
    have hact : (Rep.toAdditive ((idelesRep K L).ρ σ b)).toMul = σ • (Rep.toAdditive b).toMul := by
      rw [idelesRep_ρ_apply, idele_smul_def]
      -- `Rep.toAdditive` identifies the representation carrier with the additive ideles.
      exact Units.ext (adeleGaloisAction_apply K L σ _).symm
    have h : (σ • (Rep.toAdditive b).toMul) / (Rep.toAdditive b).toMul = x := by
      simpa only [map_sub, toMul_sub, hact, a, AddEquiv.apply_symm_apply, toMul_ofMul] using
        congrArg (fun c : idelesRep K L ↦ (Rep.toAdditive c).toMul) hb'
    refine ⟨(Rep.toAdditive b).toMul⁻¹, ?_⟩
    simpa only [smul_inv', inv_div_inv] using h
  · rintro ⟨y, rfl⟩
    have heq : ideleNormMap K L (σ • y) = ideleNormMap K L y := by
      apply ideleExtension_injective K L
      simp only [ideleExtension_ideleNormMap, ← idele_smul_def, smul_smul]
      exact Fintype.prod_equiv (Equiv.mulRight σ) _ _ fun _ ↦ rfl
    rw [map_div, heq, div_self']

end TauCeti.GlobalNumberFields
