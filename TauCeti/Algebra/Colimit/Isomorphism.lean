/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Colimit.FinitePresentation
public import TauCeti.RingTheory.TensorProduct.Maps

/-!
# Descent of algebra isomorphisms along directed colimits

An isomorphism between the base changes of two finitely presented algebras to a directed
colimit descends to an isomorphism over some stage. The descended isomorphism recovers the
specified one, not just its isomorphism class. In particular, splitting isomorphisms of finite
étale algebras can be descended once their source and target have been defined at a stage.

The proof uses the morphism descent and eventual equality results in
`TauCeti.Algebra.Colimit.FinitePresentation`: descend both directions, move them to a common
stage, and impose their two inverse identities at a later stage. Neither injectivity of the
transition maps nor flatness is required.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  Remark 1.2.9.
-/

public section

open scoped TensorProduct

namespace TauCeti.DirectLimit.Algebra

open _root_.Algebra.TensorProduct _root_.DirectLimit.Algebra

variable {A ι : Type*} [CommRing A] [Preorder ι] {B : ι → Type*} [∀ i, CommSemiring (B i)]
  [∀ i, Algebra A (B i)] {f : ∀ i j, i ≤ j → B i →ₐ[A] B j} [DirectedSystem B (f · · ·)]
  [IsDirectedOrder ι] [Nonempty ι]
  {S M : Type*} [CommSemiring S] [Algebra A S] [CommSemiring M] [Algebra A M]

/-- An isomorphism between the base changes of two finitely presented algebras to a directed
colimit descends to a stage, compatibly with the specified isomorphism. -/
theorem exists_algEquiv_of_finitePresentation
    [Algebra.FinitePresentation A S] [Algebra.FinitePresentation A M]
    (e : DirectLimit B f ⊗[A] S ≃ₐ[DirectLimit B f] DirectLimit B f ⊗[A] M) :
    ∃ i, ∃ eᵢ : B i ⊗[A] S ≃ₐ[B i] B i ⊗[A] M,
      (e.toAlgHom.restrictScalars A).comp (rTensor S (of B f i)) =
        (rTensor M (of B f i)).comp (eᵢ.toAlgHom.restrictScalars A) := by
  -- Descend both directions, initially to possibly different stages.
  obtain ⟨i, p, hp⟩ := exists_restrictScalars_comp_rTensor_eq_of_finitePresentation M e.toAlgHom
  obtain ⟨j, q, hq⟩ := exists_restrictScalars_comp_rTensor_eq_of_finitePresentation S
    e.symm.toAlgHom
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  let pₖ : B k ⊗[A] S →ₐ[B k] B k ⊗[A] M :=
    AlgHom.liftEquiv A (B k) S _
      ((rTensor M (f i k hik)).comp ((p.restrictScalars A).comp includeRight))
  let qₖ : B k ⊗[A] M →ₐ[B k] B k ⊗[A] S :=
    AlgHom.liftEquiv A (B k) M _
      ((rTensor S (f j k hjk)).comp ((q.restrictScalars A).comp includeRight))
  have hpₖ : (e.toAlgHom.restrictScalars A).comp (rTensor S (of B f k)) =
      (rTensor M (of B f k)).comp (pₖ.restrictScalars A) := by
    apply TauCeti.Algebra.tensorProduct_comp_rTensor_ext
    ext s
    have hs := congr($hp (1 ⊗ₜ s))
    simp only [AlgHom.comp_apply, map_tmul, map_one, AlgHom.id_apply,
      AlgHom.coe_restrictScalars'] at hs
    simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', includeRight_apply,
      pₖ, AlgHom.liftEquiv_tmul, one_smul]
    rw [← AlgHom.comp_apply, ← map_comp, of_comp_f, AlgHom.comp_id, ← hs]
  have hqₖ : (e.symm.toAlgHom.restrictScalars A).comp (rTensor M (of B f k)) =
      (rTensor S (of B f k)).comp (qₖ.restrictScalars A) := by
    apply TauCeti.Algebra.tensorProduct_comp_rTensor_ext
    ext t
    have ht := congr($hq (1 ⊗ₜ t))
    simp only [AlgHom.comp_apply, map_tmul, map_one, AlgHom.id_apply,
      AlgHom.coe_restrictScalars'] at ht
    simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', includeRight_apply,
      qₖ, AlgHom.liftEquiv_tmul, one_smul]
    rw [← AlgHom.comp_apply, ← map_comp, of_comp_f, AlgHom.comp_id, ← ht]
  -- Mathlib's finite-presentation-to-finite-type instance is stated for rings.
  have : Algebra.FiniteType A S := by
    obtain ⟨n, π, hπ, -⟩ := Algebra.FinitePresentation.out (R := A) (A := S)
    exact Algebra.FiniteType.of_surjective π hπ
  have : Algebra.FiniteType A M := by
    obtain ⟨n, π, hπ, -⟩ := Algebra.FinitePresentation.out (R := A) (A := M)
    exact Algebra.FiniteType.of_surjective π hπ
  -- The inverse identities hold in the colimit; finite type makes them hold eventually.
  have hqp : (rTensor S (of B f k)).comp
      (((qₖ.comp pₖ).restrictScalars A).comp includeRight) =
      (rTensor S (of B f k)).comp includeRight := by
    ext s
    have h₁ := congr($hpₖ (1 ⊗ₜ s))
    have h₂ := congr($hqₖ (pₖ (1 ⊗ₜ s)))
    simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', includeRight_apply] at h₁ h₂ ⊢
    rw [← h₂, ← h₁]
    simp
  have hpq : (rTensor M (of B f k)).comp
      (((pₖ.comp qₖ).restrictScalars A).comp includeRight) =
      (rTensor M (of B f k)).comp includeRight := by
    ext m
    have h₁ := congr($hqₖ (1 ⊗ₜ m))
    have h₂ := congr($hpₖ (qₖ (1 ⊗ₜ m)))
    simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', includeRight_apply] at h₁ h₂ ⊢
    rw [← h₂, ← h₁]
    simp
  obtain ⟨l, hkl, hl⟩ := exists_rTensor_comp_eq_rTensor_comp_of_finiteType S hqp
  obtain ⟨m, hkm, hm⟩ := exists_rTensor_comp_eq_rTensor_comp_of_finiteType M hpq
  obtain ⟨n, hln, hmn⟩ := exists_ge_ge l m
  let hkn := hkl.trans hln
  let pₙ : B n ⊗[A] S →ₐ[B n] B n ⊗[A] M :=
    AlgHom.liftEquiv A (B n) S _
      ((rTensor M (f k n hkn)).comp ((pₖ.restrictScalars A).comp includeRight))
  let qₙ : B n ⊗[A] M →ₐ[B n] B n ⊗[A] S :=
    AlgHom.liftEquiv A (B n) M _
      ((rTensor S (f k n hkn)).comp ((qₖ.restrictScalars A).comp includeRight))
  have hpn : (pₙ.restrictScalars A).comp (rTensor S (f k n hkn)) =
      (rTensor M (f k n hkn)).comp (pₖ.restrictScalars A) := by
    apply TauCeti.Algebra.tensorProduct_comp_rTensor_ext
    ext s
    simp [pₙ]
  have hqn : (qₙ.restrictScalars A).comp (rTensor M (f k n hkn)) =
      (rTensor S (f k n hkn)).comp (qₖ.restrictScalars A) := by
    apply TauCeti.Algebra.tensorProduct_comp_rTensor_ext
    ext t
    simp [qₙ]
  have hleft : qₙ.comp pₙ = AlgHom.id (B n) _ := by
    apply Algebra.TensorProduct.ext_ring
    ext s
    have htrans : (f l n hln).comp (f k l hkl) = f k n hkn :=
      AlgHom.ext fun x ↦ DirectedSystem.map_map' f hkl hln x
    have hs := congr((rTensor S (f l n hln)).comp $hl)
    simp only [← AlgHom.comp_assoc, ← map_comp, htrans, AlgHom.comp_id] at hs
    have hn := congr($hs s)
    have hp := congr($hpn (1 ⊗ₜ s))
    have hq := congr($hqn (pₖ (1 ⊗ₜ s)))
    simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', includeRight_apply] at hn hp hq ⊢
    rw [← hq, ← hp] at hn
    simpa only [map_tmul, map_one, AlgHom.id_apply, AlgHom.comp_apply] using hn
  have hright : pₙ.comp qₙ = AlgHom.id (B n) _ := by
    apply Algebra.TensorProduct.ext_ring
    ext t
    have htrans : (f m n hmn).comp (f k m hkm) = f k n hkn :=
      AlgHom.ext fun x ↦ DirectedSystem.map_map' f hkm hmn x
    have hs := congr((rTensor M (f m n hmn)).comp $hm)
    simp only [← AlgHom.comp_assoc, ← map_comp, htrans, AlgHom.comp_id] at hs
    have hn := congr($hs t)
    have hp := congr($hpn (qₖ (1 ⊗ₜ t)))
    have hq := congr($hqn (1 ⊗ₜ t))
    simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', includeRight_apply] at hn hp hq ⊢
    rw [← hp, ← hq] at hn
    simpa only [map_tmul, map_one, AlgHom.id_apply, AlgHom.comp_apply] using hn
  refine ⟨n, AlgEquiv.ofAlgHom pₙ qₙ hright hleft, ?_⟩
  rw [AlgEquiv.toAlgHom_ofAlgHom]
  apply TauCeti.Algebra.tensorProduct_comp_rTensor_ext
  ext s
  have hs := congr($hpₖ (1 ⊗ₜ s))
  simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', map_tmul, map_one,
    AlgHom.id_apply] at hs
  simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', includeRight_apply,
    pₙ, AlgHom.liftEquiv_tmul, one_smul]
  rw [← AlgHom.comp_apply, ← map_comp, of_comp_f, AlgHom.comp_id, ← hs]

end TauCeti.DirectLimit.Algebra
