/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.BaseChange
import TauCeti.Algebra.Module.LocalizedModule.Lift
import TauCeti.RingTheory.Artinian.Socle.Basic
import TauCeti.RingTheory.TensorProduct.CentralBaseChange

/-!
# Occurrence of integral characters after base change

Let `Λ` be a finite commutative `O`-algebra acting faithfully on a finitely generated flat
`O`-module `M`, and let `V` be a domain over `O` whose fraction field `L` is flat over `O`. Every
`O`-algebra map `ψ : Λ → V` occurs on `V ⊗[O] M`. The algebra `L ⊗[O] Λ` is Artinian and acts
faithfully on `L ⊗[O] M`, so the character of `L ⊗[O] Λ` induced by `ψ` occurs on a nonzero
vector of `L ⊗[O] M` by `AlgHom.exists_ne_zero_forall_smul_eq_smul`. Clearing denominators along
the localization `V ⊗[O] M → L ⊗[O] M` gives a nonzero integral vector. This is the occurrence
step of the Deligne–Serre eigenvalue lifting lemma.

## Main results

* `AlgHom.exists_ne_zero_forall_baseChange_lsmul_apply_eq_smul`: a character `Λ → V` of a finite
  commutative algebra acting faithfully on a finitely generated flat module `M` occurs on a
  nonzero vector of `V ⊗[O] M`, for any domain `V` whose fraction field is flat over the base.

## References

* P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7
  (1974), 507–530, proof of Lemme 6.11.
-/

public section

open TensorProduct

namespace AlgHom

variable {O : Type*} [CommRing O] {V : Type*} [CommRing V] [Algebra O V]
  (L : Type*) [Field L] [Algebra V L] [IsFractionRing V L] [Algebra O L] [IsScalarTower O V L]
  [Module.Flat O L]
  {Λ : Type*} [CommRing Λ] [Algebra O Λ] [Module.Finite O Λ]
  {M : Type*} [AddCommGroup M] [Module O M] [Module.Finite O M] [Module.Flat O M]
  [Module Λ M] [IsScalarTower O Λ M] [FaithfulSMul Λ M]

attribute [local instance low] TauCeti.CentralBaseChange.module

include L in
/-- **Occurrence of an integral character.** Let `Λ` be a finite commutative `O`-algebra acting
faithfully on a finitely generated flat `O`-module `M`, and let `V` be a domain over `O` whose
fraction field `L` is flat over `O`. Every `O`-algebra map `ψ : Λ → V` occurs on `V ⊗[O] M`: some
nonzero `n` satisfies `(l • ·).baseChange V n = ψ l • n` for every `l : Λ`. -/
theorem exists_ne_zero_forall_baseChange_lsmul_apply_eq_smul (ψ : Λ →ₐ[O] V) :
    ∃ n : V ⊗[O] M, n ≠ 0 ∧ ∀ l : Λ, (Algebra.lsmul O O M l).baseChange V n = ψ l • n := by
  -- The character of `L ⊗[O] Λ` induced by `ψ` occurs on the faithful module `L ⊗[O] M`.
  obtain ⟨v, hv0, hv⟩ :
      ∃ v : L ⊗[O] M, v ≠ 0 ∧ ∀ l : Λ, (Algebra.lsmul O O M l).baseChange L v =
        algebraMap V L (ψ l) • v := by
    let ψL : L ⊗[O] Λ →ₐ[L] L := Algebra.TensorProduct.lift (Algebra.ofId L L)
      ((IsScalarTower.toAlgHom O V L).comp ψ) fun _ _ ↦ Commute.all _ _
    have : IsArtinianRing (L ⊗[O] Λ) := IsArtinianRing.of_finite L _
    obtain ⟨v, hv0, hv⟩ := ψL.exists_ne_zero_forall_smul_eq_smul (V := L ⊗[O] M)
    refine ⟨v, hv0, fun l ↦ ?_⟩
    simpa [TauCeti.CentralBaseChange.smul_def, TauCeti.CentralBaseChange.lsmul_tmul, ψL]
      using hv (1 ⊗ₜ l)
  -- Clear the denominators of `v` along the localization `V ⊗[O] M → L ⊗[O] M`.
  let g : V ⊗[O] M →ₗ[V] L ⊗[O] M := AlgebraTensorModule.rTensor O M (Algebra.linearMap V L)
  have hg : Function.Injective g :=
    Module.Flat.rTensor_preserves_injective_linearMap ((Algebra.linearMap V L).restrictScalars O)
      (IsFractionRing.injective V L)
  obtain ⟨n, hn0, hn, -⟩ :=
    IsLocalizedModule.exists_ne_zero_forall_apply_eq_smul_of_injective (nonZeroDivisors V) hg
      (T := fun l : Λ ↦ (Algebra.lsmul O O M l).baseChange V)
      (T' := fun l : Λ ↦ ((Algebra.lsmul O O M l).baseChange L).restrictScalars V)
      (fun l ↦ by ext; simp [g]) hv0 (b := fun l ↦ ψ l) fun l ↦ by
        simpa [algebraMap_smul] using hv l
  exact ⟨n, hn0, hn⟩

end AlgHom
