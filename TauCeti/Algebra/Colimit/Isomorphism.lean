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

The morphism descent and eventual equality API is in
`TauCeti.Algebra.Colimit.FinitePresentation`. Neither injectivity of the transition maps nor
flatness is required.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  Remark 1.2.9.
-/

public section

open scoped TensorProduct

section

open Algebra.TensorProduct DirectLimit.Algebra TauCeti.DirectLimit.Algebra

variable {A ι : Type*} [CommRing A] [Preorder ι] {B : ι → Type*} [∀ i, CommSemiring (B i)]
  [∀ i, Algebra A (B i)] {f : ∀ i j, i ≤ j → B i →ₐ[A] B j} [DirectedSystem B (f · · ·)]
  [IsDirectedOrder ι] [Nonempty ι]
  {S M : Type*} [CommSemiring S] [Algebra A S] [CommSemiring M] [Algebra A M]

namespace AlgHom

-- Advancing a descended map preserves its compatibility with the specified colimit map.
private theorem comp_rTensor_liftEquiv_eq {i j : ι} (hij : i ≤ j)
    (p : B i ⊗[A] S →ₐ[B i] B i ⊗[A] M)
    (q : DirectLimit B f ⊗[A] S →ₐ[DirectLimit B f] DirectLimit B f ⊗[A] M)
    (h : (q.restrictScalars A).comp (rTensor S (of B f i)) =
      (rTensor M (of B f i)).comp (p.restrictScalars A)) :
    (q.restrictScalars A).comp (rTensor S (of B f j)) =
      (rTensor M (of B f j)).comp
        ((AlgHom.liftEquiv A (B j) S _
          ((rTensor M (f i j hij)).comp
            ((p.restrictScalars A).comp includeRight))).restrictScalars A) := by
  apply tensorProduct_comp_rTensor_ext
  ext s
  have hs := congr($h (1 ⊗ₜ s))
  simp only [AlgHom.comp_apply, map_tmul, map_one, AlgHom.id_apply,
    AlgHom.coe_restrictScalars'] at hs
  simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', includeRight_apply,
    AlgHom.liftEquiv_tmul, one_smul]
  rw [← AlgHom.comp_apply, ← map_comp, of_comp_f, AlgHom.comp_id, ← hs]

-- An inverse identity on the right factor remains an inverse identity at every later stage.
omit [IsDirectedOrder ι] [Nonempty ι] in
private theorem comp_eq_id_of_rTensor_comp_eq {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k)
    (p : B i ⊗[A] S →ₐ[B i] B i ⊗[A] M)
    (q : B i ⊗[A] M →ₐ[B i] B i ⊗[A] S)
    (p' : B k ⊗[A] S →ₐ[B k] B k ⊗[A] M)
    (q' : B k ⊗[A] M →ₐ[B k] B k ⊗[A] S)
    (hp : (p'.restrictScalars A).comp (rTensor S (f i k (hij.trans hjk))) =
      (rTensor M (f i k (hij.trans hjk))).comp (p.restrictScalars A))
    (hq : (q'.restrictScalars A).comp (rTensor M (f i k (hij.trans hjk))) =
      (rTensor S (f i k (hij.trans hjk))).comp (q.restrictScalars A))
    (h : (rTensor S (f i j hij)).comp
        (((q.comp p).restrictScalars A).comp includeRight) =
      (rTensor S (f i j hij)).comp includeRight) :
    q'.comp p' = AlgHom.id (B k) _ := by
  apply Algebra.TensorProduct.ext_ring
  ext s
  have htrans : (f j k hjk).comp (f i j hij) = f i k (hij.trans hjk) :=
    AlgHom.ext fun x ↦ DirectedSystem.map_map' f hij hjk x
  have hs := congr((rTensor S (f j k hjk)).comp $h)
  simp only [← AlgHom.comp_assoc, ← map_comp, htrans, AlgHom.comp_id] at hs
  have hn := congr($hs s)
  have hp₁ := congr($hp (1 ⊗ₜ s))
  have hq₁ := congr($hq (p (1 ⊗ₜ s)))
  simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', includeRight_apply] at hn hp₁ hq₁ ⊢
  rw [← hq₁, ← hp₁] at hn
  simpa only [map_tmul, map_one, AlgHom.id_apply, AlgHom.comp_apply] using hn

end AlgHom

namespace AlgEquiv

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
      (rTensor M (of B f k)).comp (pₖ.restrictScalars A) :=
    AlgHom.comp_rTensor_liftEquiv_eq hik p e.toAlgHom hp
  have hqₖ : (e.symm.toAlgHom.restrictScalars A).comp (rTensor M (of B f k)) =
      (rTensor S (of B f k)).comp (qₖ.restrictScalars A) :=
    AlgHom.comp_rTensor_liftEquiv_eq hjk q e.symm.toAlgHom hq
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
    apply AlgHom.tensorProduct_comp_rTensor_ext
    ext s
    simp [pₙ]
  have hqn : (qₙ.restrictScalars A).comp (rTensor M (f k n hkn)) =
      (rTensor S (f k n hkn)).comp (qₖ.restrictScalars A) := by
    apply AlgHom.tensorProduct_comp_rTensor_ext
    ext t
    simp [qₙ]
  have hleft : qₙ.comp pₙ = AlgHom.id (B n) _ :=
    AlgHom.comp_eq_id_of_rTensor_comp_eq hkl hln pₖ qₖ pₙ qₙ hpn hqn hl
  have hright : pₙ.comp qₙ = AlgHom.id (B n) _ :=
    AlgHom.comp_eq_id_of_rTensor_comp_eq hkm hmn qₖ pₖ qₙ pₙ hqn hpn hm
  refine ⟨n, AlgEquiv.ofAlgHom pₙ qₙ hright hleft, ?_⟩
  rw [AlgEquiv.toAlgHom_ofAlgHom]
  exact AlgHom.comp_rTensor_liftEquiv_eq hkn pₖ e.toAlgHom hpₖ

end AlgEquiv

end
