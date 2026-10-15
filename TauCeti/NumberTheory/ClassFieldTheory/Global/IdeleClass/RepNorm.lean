/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.SIdeles
public import TauCeti.NumberTheory.NumberField.Global.Ideles.GaloisDescent
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Galois

/-!
# The representation norm on the ideles

Let `L/K` be a Galois extension of number fields. The norm `∑_σ σ x` of the representation
`idelesRep K L` of `Gal(L/K)` on `I_L` is the idele norm `N_{L/K}(x)`, extended back to `L`
(`idelesRep_norm_apply`). This is `TauCeti.GlobalNumberFields.ideleExtension_ideleNormMap` read on
the representation. By Galois descent of ideles, an idele of `K`, extended to `L`, is then a
representation norm exactly when it is an idele norm from `L`
(`ideleExtension_mem_range_idelesRep_norm_iff`).

## Main results

* `TauCeti.ClassFieldTheory.idelesRep_norm_apply`: the norm of the representation of `Gal(L/K)` on
  `I_L` is the idele norm, extended back to `L`.
* `TauCeti.ClassFieldTheory.ideleExtension_mem_range_idelesRep_norm_iff`: an idele of `K`,
  extended to `L`, is a representation norm exactly when it is an idele norm from `L`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §2.
-/

public section

noncomputable section

open NumberField
open scoped AdeleGaloisAction

namespace TauCeti.ClassFieldTheory

open GlobalNumberFields

variable {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- **The representation norm on ideles is the idele norm.** For `L/K` Galois, the norm
`∑_σ σ x` of the representation of `Gal(L/K)` on `I_L` is the idele norm `N_{L/K}(x)`, extended
back to `L`. -/
theorem idelesRep_norm_apply (x : idelesRep K L) :
    Rep.toAdditive ((idelesRep K L).norm.hom x) =
      Additive.ofMul (ideleExtension K L (ideleNormMap K L (Rep.toAdditive x).toMul)) := by
  apply Additive.toMul.injective
  rw [ideleExtension_ideleNormMap, Rep.norm_apply]
  exact (Representation.norm_ofMulDistribMulAction_eq (Rep.toAdditive x)).trans
    (Finset.prod_congr rfl fun σ _ ↦ idele_smul_def σ _)

/-- An idele of `K`, extended to `L`, lies in the image of the representation norm on `I_L`
exactly when it is an idele norm from `L`. -/
theorem ideleExtension_mem_range_idelesRep_norm_iff (x : IdeleGroup (𝓞 K) K) :
    Rep.toAdditive.symm (Additive.ofMul (ideleExtension K L x)) ∈
        LinearMap.range (idelesRep K L).norm.hom.toLinearMap ↔
      x ∈ (ideleNormMap K L).toMonoidHom.range := by
  refine ⟨fun ⟨y, hy⟩ ↦ ⟨(Rep.toAdditive y).toMul, ideleExtension_injective K L ?_⟩,
    fun ⟨y, hy⟩ ↦ ⟨Rep.toAdditive.symm (Additive.ofMul y), ?_⟩⟩
  · exact congrArg Additive.toMul ((idelesRep_norm_apply y).symm.trans
      (congrArg Rep.toAdditive hy))
  · apply Rep.toAdditive.injective
    exact (idelesRep_norm_apply _).trans (by rw [← hy]; rfl)

end TauCeti.ClassFieldTheory
