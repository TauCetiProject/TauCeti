/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Colimit.FinitePresentation
import TauCeti.RingTheory.TensorProduct.Maps

/-!
# Detecting algebra isomorphisms at a finite stage

If a map between algebras becomes an isomorphism after extension of scalars to a directed
colimit, it already becomes an isomorphism over some stage. The target must be finitely
presented, to descend the inverse, whereas finite type suffices for the source, to descend
one of the inverse identities. This is an affine shrinking step for spreading isomorphisms
from local schemes.

The argument uses the factorization and eventual-equality theorems of
`TauCeti.Algebra.Colimit.FinitePresentation`.

## Main result

* `AlgHom.exists_bijective_lTensor_of_finitePresentation`: detect
  invertibility of a given algebra map after scalar extension at a finite stage.

## References

* The Stacks Project, Lemma 10.127.8 (05N9).
* The Stacks Project, Lemma 32.20.3 (0BQ5), the isomorphism shrinking step.
-/

public section

open scoped TensorProduct

namespace AlgHom

open _root_.DirectLimit.Algebra _root_.Algebra.TensorProduct TauCeti.DirectLimit.Algebra

variable {A ι : Type*} [CommRing A] [Preorder ι] {B : ι → Type*}
  [∀ i, CommSemiring (B i)] [∀ i, Algebra A (B i)]
  {f : ∀ i j, i ≤ j → B i →ₐ[A] B j} [DirectedSystem B (f · · ·)]
  [IsDirectedOrder ι] [Nonempty ι]
  {S T : Type*} [CommSemiring S] [Algebra A S] [CommRing T] [Algebra A T]

-- Descend the inverse map. Its two inverse identities hold after passage to the colimit;
-- they will be equalized at a later stage using finite type of the two algebras.
private theorem exists_inverse_candidate [Algebra.FinitePresentation A T] (φ : S →ₐ[A] T)
    (hφ : Function.Bijective (lTensor (S := DirectLimit B f) (DirectLimit B f) φ)) :
    ∃ i, ∃ ψ : T →ₐ[A] B i ⊗[A] S,
      (rTensor T (of B f i)).comp
          (((lTensor (S := B i) (B i) φ).restrictScalars A).comp ψ) =
        (rTensor T (of B f i)).comp includeRight ∧
      (rTensor S (of B f i)).comp
          (((AlgHom.liftEquiv A (B i) T (B i ⊗[A] S) ψ).restrictScalars A).comp
            (includeRight.comp φ)) =
        (rTensor S (of B f i)).comp includeRight := by
  let e := AlgEquiv.ofBijective
    (lTensor (S := DirectLimit B f) (DirectLimit B f) φ) hφ
  obtain ⟨i, ψ, hψ⟩ := exists_eq_rTensor_comp_of_finitePresentation (f := f) S
    ((e.symm.toAlgHom.restrictScalars A).comp includeRight)
  let Ψ := AlgHom.liftEquiv A (B i) T (B i ⊗[A] S) ψ
  have hΨ : (e.symm.toAlgHom.restrictScalars A).comp (rTensor T (of B f i)) =
      (rTensor S (of B f i)).comp (Ψ.restrictScalars A) := by
    apply Algebra.TensorProduct.ext
    · ext b
      simpa [Ψ, Algebra.smul_def, -DirectLimit.Algebra.of_apply] using
        e.symm.commutes (of B f i b)
    · ext t
      simpa [Ψ, -DirectLimit.Algebra.of_apply] using congr($hψ t)
  have hT : (rTensor T (of B f i)).comp
        (((lTensor (S := B i) (B i) φ).restrictScalars A).comp ψ) =
      (rTensor T (of B f i)).comp includeRight := by
    ext t
    have ht := congrArg (lTensor (S := DirectLimit B f) (DirectLimit B f) φ)
      (congr($hψ t))
    have ht' : (lTensor (S := DirectLimit B f) (DirectLimit B f) φ)
        ((rTensor S (of B f i)) (ψ t)) = 1 ⊗ₜ[A] t := by
      exact ht.symm.trans (e.apply_symm_apply _)
    simpa only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', includeRight_apply,
      map_tmul, map_one, AlgHom.id_apply, φ.lTensor_rTensor_comm] using ht'
  have hS : (rTensor S (of B f i)).comp
        ((Ψ.restrictScalars A).comp (includeRight.comp φ)) =
      (rTensor S (of B f i)).comp includeRight := by
    ext s
    have hs := congr($hΨ (1 ⊗ₜ[A] φ s))
    have hs' : e.symm (1 ⊗ₜ[A] φ s) = 1 ⊗ₜ[A] s :=
      e.symm_apply_apply (1 ⊗ₜ[A] s)
    have hs'' : (rTensor S (of B f i)) (Ψ (1 ⊗ₜ[A] φ s)) =
        e.symm (1 ⊗ₜ[A] φ s) := by
      simpa [-DirectLimit.Algebra.of_apply] using hs.symm
    simpa only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', includeRight_apply,
      map_tmul, map_one, AlgHom.id_apply] using hs''.trans hs'
  exact ⟨i, ψ, hT, hS⟩

/-- A map whose scalar extension to a directed colimit is bijective is bijective after scalar
extension to some stage. Finite presentation is needed only for the target; the source need
only be of finite type. No flatness of the transition maps is required. -/
theorem exists_bijective_lTensor_of_finitePresentation
    [Algebra.FiniteType A S] [Algebra.FinitePresentation A T] (φ : S →ₐ[A] T)
    (hφ : Function.Bijective (lTensor (S := DirectLimit B f) (DirectLimit B f) φ)) :
    ∃ i, Function.Bijective (lTensor (S := B i) (B i) φ) := by
  obtain ⟨i, ψ, hT, hS⟩ := exists_inverse_candidate (f := f) φ hφ
  -- Equalize the two inverse identities, then pass to a common upper stage.
  obtain ⟨j, hij, hj⟩ := exists_rTensor_comp_eq_rTensor_comp_of_finiteType T hT
  obtain ⟨k, hik, hk⟩ := exists_rTensor_comp_eq_rTensor_comp_of_finiteType S hS
  obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j k
  let hil := hij.trans hjl
  let ψl := (rTensor S (f i l hil)).comp ψ
  let Ψl := AlgHom.liftEquiv A (B l) T (B l ⊗[A] S) ψl
  have hlT : ((lTensor (S := B l) (B l) φ).restrictScalars A).comp ψl = includeRight := by
    ext t
    have ht := congrArg (rTensor T (f j l hjl)) (congr($hj t))
    simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', includeRight_apply] at ht
    rw [DirectedSystem.map_map' (F := fun i ↦ B i ⊗[A] T)
      (fun i j h ↦ rTensor (R := A) T (f i j h)) hij hjl] at ht
    simpa only [ψl, AlgHom.comp_apply, AlgHom.coe_restrictScalars', φ.lTensor_rTensor_comm,
      includeRight_apply, map_tmul, AlgHom.id_apply, map_one] using ht
  have hlS : (Ψl.restrictScalars A).comp (includeRight.comp φ) = includeRight := by
    ext s
    have hs := congrArg (rTensor S (f k l hkl)) (congr($hk s))
    simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', includeRight_apply,
      AlgHom.liftEquiv_tmul, one_smul] at hs
    rw [DirectedSystem.map_map' (F := fun i ↦ B i ⊗[A] S)
      (fun i j h ↦ rTensor (R := A) S (f i j h)) hik hkl] at hs
    simpa [Ψl, ψl] using hs
  -- The identities on the original algebra generators determine the scalar-extended maps.
  have hright : (lTensor (S := B l) (B l) φ).comp Ψl = AlgHom.id (B l) (B l ⊗[A] T) := by
    ext t
    simpa [Ψl] using congr($hlT t)
  have hleft : Ψl.comp (lTensor (S := B l) (B l) φ) = AlgHom.id (B l) (B l ⊗[A] S) := by
    ext s
    simpa using congr($hlS s)
  exact ⟨l, ⟨Function.LeftInverse.injective (congr($hleft ·)),
    Function.RightInverse.surjective (congr($hright ·))⟩⟩

end AlgHom
