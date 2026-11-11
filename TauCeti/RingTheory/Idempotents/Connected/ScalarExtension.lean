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
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Connectedness over an algebraically closed field

A connected algebra over an algebraically closed field remains connected after any extension
of that field. No finite-type or reducedness assumption on the connected algebra is needed.

Thus ordinary connectedness of an affine scheme over an algebraically closed field implies
geometric connectedness. In particular, this applies to identity components of affine groups.

## References

* The Stacks Project, Section 10.48, *Geometrically connected algebras*,
  https://stacks.math.columbia.edu/tag/05DV.
-/

public section

open scoped TensorProduct

namespace TauCeti

/-- The reduced case of `exists_eq_tmul_one_of_isIdempotentElem`: points separate. -/
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

/-- An idempotent in a family over a finite-type parameter algebra is scalar when the other
factor has connected spectrum and the ground field is algebraically closed. The nilradical of
the parameter algebra is nilpotent, so the reduced case lifts. -/
theorem exists_eq_tmul_one_of_isIdempotentElem
    {k A B : Type*} [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A] [ConnectedSpace (PrimeSpectrum A)]
    [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    {e : B ⊗[k] A} (he : IsIdempotentElem e) :
    ∃ c : B, e = c ⊗ₜ[k] (1 : A) := by
  let : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  let q : B →ₐ[k] B ⧸ nilradical B := Ideal.Quotient.mkₐ k (nilradical B)
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  have : IsReduced (B ⧸ nilradical B) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
  have : Algebra.FiniteType k (B ⧸ nilradical B) := Algebra.FiniteType.of_surjective q hq
  have hqker : RingHom.ker q = nilradical B := Ideal.mk_ker
  let G := Algebra.TensorProduct.map q (AlgHom.id k A)
  have := Algebra.FiniteType.isNoetherianRing k B
  obtain ⟨n, hn⟩ := IsNoetherianRing.isNilpotent_nilradical B
  have hker : ∀ x ∈ RingHom.ker G, IsNilpotent x := fun x hx => by
    rw [Algebra.TensorProduct.rTensor_ker q hq] at hx
    refine ⟨n, ?_⟩
    have hmem := Ideal.pow_mem_pow hx n
    rwa [← Ideal.map_pow, hqker, hn,
      Ideal.zero_eq_bot, Ideal.map_bot, Ideal.mem_bot] at hmem
  obtain ⟨cb, hcb⟩ := exists_eq_tmul_one_of_isIdempotentElem_of_isReduced (he.map G)
  have hcbid : IsIdempotentElem cb := by
    apply Algebra.TensorProduct.includeLeft_injective (S := k) (B := A)
      (algebraMap k A).injective
    simpa only [map_mul, Algebra.TensorProduct.includeLeft_apply, ← hcb] using (he.map G).eq
  obtain ⟨c, hc, hcq⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent (q : B →+* _)
    (fun x hx => by simpa [mem_nilradical] using (hqker ▸ hx : x ∈ nilradical B)) cb
    (RingHom.mem_range.mpr (hq cb)) hcbid
  refine ⟨c, eq_of_isNilpotent_sub_of_isIdempotentElem he ?_ (hker _ ?_)⟩
  · simpa using hc.map (Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] A)
  · rw [RingHom.mem_ker, map_sub, hcb, sub_eq_zero]
    simp [G, ← hcq]

/-- A connected algebra over an algebraically closed field remains connected after every field
extension, without finite-type or reducedness assumptions. -/
theorem connectedSpace_primeSpectrum_tensorProduct_of_isAlgClosed
    (k A K : Type*) [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A] [ConnectedSpace (PrimeSpectrum A)]
    [Field K] [Algebra k K] : ConnectedSpace (PrimeSpectrum (A ⊗[k] K)) := by
  suffices h : ConnectedSpace (PrimeSpectrum (K ⊗[k] A)) from
    (PrimeSpectrum.homeomorphOfRingEquiv
      (Algebra.TensorProduct.comm k A K).toRingEquiv).connectedSpace_iff.mpr h
  let : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  let : Nontrivial (K ⊗[k] A) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left k K A
      (FaithfulSMul.algebraMap_injective k A)
  apply connectedSpace_primeSpectrum_iff_idempotent_eq_zero_or_one.mpr
  intro e he
  obtain ⟨B, hB, x, hx⟩ := TensorProduct.Algebra.exists_of_fg e
  let : Algebra.FiniteType k B := B.fg_iff_finiteType.mp hB
  let F := Algebra.TensorProduct.map B.val (AlgHom.id k A)
  have hF : Function.Injective F :=
    Module.Flat.rTensor_preserves_injective_linearMap B.val.toLinearMap Subtype.val_injective
  have hxe : F x = e := hx
  have hxid : IsIdempotentElem x := by
    apply hF
    simpa only [map_mul, hxe] using he.eq
  obtain ⟨c, hc⟩ := exists_eq_tmul_one_of_isIdempotentElem hxid
  have hec : e = (c : K) ⊗ₜ[k] (1 : A) := by
    rw [← hxe, hc]
    simp [F]
  have hinj : Function.Injective (Algebra.TensorProduct.includeLeft : K →ₐ[k] K ⊗[k] A) :=
    (Algebra.TensorProduct.includeLeft : K →ₐ[k] K ⊗[k] A).injective
  have hcid : IsIdempotentElem (c : K) := by
    apply hinj
    simpa only [map_mul, Algebra.TensorProduct.includeLeft_apply, ← hec] using he.eq
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hcid with h | h <;>
    simp [hec, h, Algebra.TensorProduct.one_def]

end TauCeti
