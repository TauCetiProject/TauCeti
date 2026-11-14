/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.Idempotents.Connected.Spectrum
public import TauCeti.RingTheory.FiniteType.Tensor.PointSeparation
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.RingTheory.Flat.Basic
import TauCeti.Algebra.Group.Idempotent
import TauCeti.RingTheory.Ideal.Quotient.Nilpotent
import TauCeti.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Connectedness over an algebraically closed field

The tensor product of two connected algebras over an algebraically closed field is connected. In
particular, a connected algebra over an algebraically closed field remains connected after any
extension of that field. No finite-type or reducedness assumption is needed.

Thus ordinary connectedness of an affine scheme over an algebraically closed field implies
geometric connectedness. In particular, this applies to identity components of affine groups.

## References

* The Stacks Project, Section 10.48, *Geometrically connected algebras*,
  https://stacks.math.columbia.edu/tag/05DV.
-/

public section

open scoped TensorProduct

namespace TauCeti

-- The reduced finite-type case of `exists_eq_tmul_one_of_isIdempotentElem_of_finiteType`.
private theorem exists_eq_tmul_one_of_isIdempotentElem_of_isReduced
    {k A B : Type*} [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A] [ConnectedSpace (PrimeSpectrum A)]
    [CommRing B] [Algebra k B] [Algebra.FiniteType k B] [IsReduced B]
    {e : B ⊗[k] A} (he : IsIdempotentElem e) :
    ∃ c : B, e = c ⊗ₜ[k] (1 : A) := by
  let : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one k (one_ne_zero : (1 : A) ≠ 0)
  let c := LinearMap.tensorComponent f e
  refine ⟨c, tensor_eq_of_forall_map_algHom_eq (K := k) fun p ↦ ?_⟩
  let F := Algebra.TensorProduct.map p (AlgHom.id k A)
  have hconn : ConnectedSpace (PrimeSpectrum (k ⊗[k] A)) :=
    (PrimeSpectrum.homeomorphOfRingEquiv
      (Algebra.TensorProduct.lid k A).toRingEquiv).connectedSpace_iff.mpr inferInstance
  have hcomponent : p c = LinearMap.tensorComponent f (F e) :=
    (LinearMap.tensorComponent_map f p.toLinearMap LinearMap.id e).symm
  rcases (he.map F).eq_zero_or_eq_one_of_preconnectedSpace with h | h
  · have hc : p c = 0 := by rw [hcomponent, h, map_zero]
    exact h.trans (by simp [hc])
  · have hc : p c = 1 := by
      rw [hcomponent, h, Algebra.TensorProduct.one_def, LinearMap.tensorComponent_tmul, hf,
        one_smul]
    exact h.trans (by simp [hc, Algebra.TensorProduct.one_def])

/-- The finite-type case of `IsIdempotentElem.exists_isIdempotentElem_eq_tmul_one`. -/
private theorem exists_eq_tmul_one_of_isIdempotentElem_of_finiteType
    {k A B : Type*} [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A] [ConnectedSpace (PrimeSpectrum A)]
    [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    {e : B ⊗[k] A} (he : IsIdempotentElem e) :
    ∃ c : B, IsIdempotentElem c ∧ e = c ⊗ₜ[k] (1 : A) := by
  let : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  let q : B →ₐ[k] B ⧸ nilradical B := Ideal.Quotient.mkₐ k (nilradical B)
  have hq : Function.Surjective q := Ideal.Quotient.mkₐ_surjective k _
  have hqker : RingHom.ker q = nilradical B := Ideal.Quotient.mkₐ_ker k _
  let G := Algebra.TensorProduct.map q (AlgHom.id k A)
  -- the kernel of `G` is the extension of the nilradical, which consists of nilpotents
  have hker : ∀ x ∈ RingHom.ker G, IsNilpotent x := fun x hx ↦ by
    rw [Algebra.TensorProduct.rTensor_ker q hq, hqker] at hx
    simpa only [← mem_nilradical, nilradical, Ideal.zero_eq_bot, Ideal.map_bot] using
      (⊥ : Ideal B).map_radical_le (Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] A) hx
  obtain ⟨cb, hcb⟩ := exists_eq_tmul_one_of_isIdempotentElem_of_isReduced (he.map G)
  have hcbid : IsIdempotentElem cb :=
    (IsIdempotentElem.map_iff (Algebra.TensorProduct.includeLeft_injective (S := k) (B := A)
      (algebraMap k A).injective)).mp
      (by rw [Algebra.TensorProduct.includeLeft_apply, ← hcb]; exact he.map G)
  obtain ⟨c, hc, hcq⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent (q : B →+* _)
    (fun x hx ↦ by simpa [mem_nilradical] using (hqker ▸ hx : x ∈ nilradical B)) cb
    (RingHom.mem_range.mpr (hq cb)) hcbid
  refine ⟨c, hc, eq_of_isNilpotent_sub_of_isIdempotentElem he ?_ (hker _ ?_)⟩
  · simpa using hc.map (Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] A)
  · rw [RingHom.mem_ker, map_sub, hcb, sub_eq_zero]
    simp [G, ← hcq]

/-- In the tensor product `B ⊗[k] A` of commutative algebras over an algebraically closed field `k`
with `PrimeSpectrum A` preconnected, every idempotent has the form `c ⊗ₜ 1` for an idempotent
`c : B`. -/
theorem _root_.IsIdempotentElem.exists_isIdempotentElem_eq_tmul_one
    {k A B : Type*} [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A] [PreconnectedSpace (PrimeSpectrum A)]
    [CommRing B] [Algebra k B]
    {e : B ⊗[k] A} (he : IsIdempotentElem e) :
    ∃ c : B, IsIdempotentElem c ∧ e = c ⊗ₜ[k] (1 : A) := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨0, .zero, Subsingleton.elim _ _⟩
  have : ConnectedSpace (PrimeSpectrum A) :=
    ⟨PrimeSpectrum.nonempty_iff_nontrivial.mpr hA⟩
  -- the idempotent comes from a finitely generated subalgebra `B'` of `B`, into which tensoring
  -- over the field embeds injectively, so the finite-type case applies
  obtain ⟨B', hB', x, hx⟩ := TensorProduct.Algebra.exists_of_fg e
  let : Algebra.FiniteType k B' := B'.fg_iff_finiteType.mp hB'
  let F := Algebra.TensorProduct.map B'.val (AlgHom.id k A)
  have hFlin (y : B' ⊗[k] A) : F y = B'.val.toLinearMap.rTensor A y :=
    (AlgHom.rTensor_toLinearMap_apply A B'.val y).symm
  have hlin : Function.Injective (B'.val.toLinearMap.rTensor A) :=
    Module.Flat.rTensor_preserves_injective_linearMap B'.val.toLinearMap Subtype.val_injective
  have hF : Function.Injective F := fun a b h ↦
    hlin ((hFlin a).symm.trans (h.trans (hFlin b)))
  have hxe : F x = e := (hFlin x).trans hx
  obtain ⟨c, hc, hcx⟩ := exists_eq_tmul_one_of_isIdempotentElem_of_finiteType (A := A) (e := x)
    ((IsIdempotentElem.map_iff hF).mp (by rwa [hxe]))
  have hec : e = (c : B) ⊗ₜ[k] (1 : A) := by rw [← hxe, hcx]; simp [F]
  exact ⟨c, hc.map B'.val, hec⟩

/-- The tensor product of two connected algebras over an algebraically closed field has connected
spectrum. -/
theorem connectedSpace_primeSpectrum_tensorProduct_of_isAlgClosed
    (k A B : Type*) [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A] [ConnectedSpace (PrimeSpectrum A)]
    [CommRing B] [Algebra k B] [ConnectedSpace (PrimeSpectrum B)] :
    ConnectedSpace (PrimeSpectrum (A ⊗[k] B)) := by
  suffices h : ConnectedSpace (PrimeSpectrum (B ⊗[k] A)) from
    (PrimeSpectrum.homeomorphOfRingEquiv
      (Algebra.TensorProduct.comm k A B).toRingEquiv).connectedSpace_iff.mpr h
  let : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  let : Nontrivial B := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  let : Nontrivial (B ⊗[k] A) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left k B A
      (FaithfulSMul.algebraMap_injective k A)
  apply connectedSpace_primeSpectrum_iff_idempotent_eq_zero_or_one.mpr
  intro e he
  obtain ⟨c, hcid, hec⟩ := he.exists_isIdempotentElem_eq_tmul_one
  rcases hcid.eq_zero_or_eq_one_of_preconnectedSpace with h | h <;>
    simp [hec, h, Algebra.TensorProduct.one_def]

end TauCeti
