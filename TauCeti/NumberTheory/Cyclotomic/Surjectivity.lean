/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.Gal

/-!
# Surjectivity of finite cyclotomic characters

In a normal extension containing all `n`-th roots of unity, irreducibility of the `n`-th
cyclotomic polynomial makes the finite cyclotomic character surjective. Restriction to the
cyclotomic subextension realizes each unit modulo `n`; normality extends its automorphisms to
the ambient field. This supplies the finite-level input to surjectivity of cyclotomic
characters on absolute Galois groups.

The central formal inputs are Mathlib's `IsCyclotomicExtension.autEquivPow` and
`AlgEquiv.restrictNormalHom_surjective`.

## References

* T. Szamuely, *Galois Groups and Fundamental Groups*, Example 4.7.4.
-/

public section

namespace TauCeti

open Polynomial

/-- If `Φ_n` is irreducible over `K`, the action of a normal extension's Galois group on
its `n`-th roots of unity realizes every unit modulo `n`. -/
theorem surjective_modularCyclotomicCharacter_of_irreducible
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Normal K L]
    {n : ℕ} [NeZero n] (hn : Nat.card (rootsOfUnity n L) = n)
    (hirr : Irreducible (cyclotomic n K)) :
    Function.Surjective (fun σ : Gal(L/K) ↦
      modularCyclotomicCharacter L hn σ.toRingEquiv) := by
  obtain ⟨ζ, hζ⟩ := card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot.mp hn
  let E := IntermediateField.adjoin K ({ζ} : Set L)
  let _ : IsCyclotomicExtension {n} K E :=
    hζ.intermediateField_adjoin_isCyclotomicExtension K
  let _ : IsGalois K E := IsCyclotomicExtension.isGalois (S := {n}) K E
  have hζE : ζ ∈ E := IntermediateField.subset_adjoin K _ (Set.mem_singleton ζ)
  intro u
  let τ := (IsCyclotomicExtension.autEquivPow E hirr).symm u
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective L τ
  refine ⟨σ, ?_⟩
  have hpow : σ ζ = ζ ^ (u : ZMod n).val := by
    have hcomm := AlgEquiv.restrictNormal_commutes σ E ⟨ζ, hζE⟩
    have hrestrict : σ.restrictNormal E = τ := hσ
    rw [hrestrict] at hcomm
    have hτ := IsCyclotomicExtension.autEquivPow_apply_of_pow_eq_one E hirr τ
      (x := ⟨ζ, hζE⟩) (Subtype.ext hζ.pow_eq_one)
    simp only [τ, MulEquiv.apply_symm_apply] at hτ
    exact hcomm.symm.trans (congrArg Subtype.val hτ)
  have hAut : hζ.autToPow K σ = u := by
    apply Units.ext
    apply ZMod.val_injective
    exact hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
      ((IsPrimitiveRoot.autToPow_spec K hζ σ).trans hpow)
  exact (IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter n K hζ σ).symm.trans hAut

end TauCeti
