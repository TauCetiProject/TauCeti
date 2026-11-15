/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.ModuleTopology.Pair
public import TauCeti.RingTheory.Huber.QuotientMapping
public import TauCeti.Topology.Algebra.Module.ModuleTopology
import Mathlib.RingTheory.Etale.Basic
import TauCeti.RingTheory.Etale.Idempotent
import TauCeti.RingTheory.RingHom.Etale

/-!
# Composition and infinitesimal lifting for finite étale morphisms of Huber pairs

Finite étale morphisms of Huber pairs compose (`TauCeti.Huber.Pair.Hom.IsFiniteEtale.comp`), and any
morphism into a subsingleton Huber pair is finite étale
(`TauCeti.Huber.Pair.Hom.IsFiniteEtale.of_subsingleton`). Besides finiteness and étaleness of the
ring maps, composition requires restriction of scalars for the natural module topology and
transitivity of integrality on plus rings.

Because the underlying ring map of a finite étale morphism `ψ : (A, A⁺) → (B, B⁺)` is formally
étale and `ψ.exists_hom` upgrades every `A`-algebra lift out of `B` to a morphism of Huber pairs,
finite étale morphisms of Huber pairs satisfy unique infinitesimal lifting along square-zero ideal
quotients (`TauCeti.Huber.Pair.Hom.IsFiniteEtale.existsUnique_of_sqZero_quotient`) and more
generally along quotient mappings with square-zero kernel
(`eq_of_isQuotientMapping_sqZero_ker`, `exists_of_isQuotientMapping_sqZero_ker`). None of these
result statements require completeness, separatedness, a Tate hypothesis, or sheafiness.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §8.2, Definition 8.2.16 and Lemma 8.2.17(c).
* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of Mathematics
  E30 (1996), §1.6.
-/

public section

namespace TauCeti.Huber.Pair

variable {A B C : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
  {S : Pair A} {T : Pair B} {U : Pair C}

/-- The identity of any Huber pair is finite étale. -/
@[simp]
theorem Hom.isFiniteEtale_id (S : Pair A) : (Hom.id S).IsFiniteEtale where
  finite := by
    rw [Hom.toRingHom_id]
    exact RingHom.Finite.id A
  etale := by
    rw [Hom.toRingHom_id]
    exact RingHom.Etale.of_bijective Function.bijective_id
  isModuleTopology := by
    rw [Hom.toRingHom_id, ← Algebra.algebraMap_self (R := A), _root_.toAlgebra_algebraMap]
    infer_instance
  plus_eq := by
    rw [Hom.toRingHom_id, Subring.map_id]
    ext a
    exact ⟨fun ha ↦ algebraMap_mem (integralClosure S.plus A) ⟨a, ha⟩,
      fun ha ↦ Subring.isIntegrallyClosedIn_iff.mp
        S.isRingOfIntegralElements.isIntegrallyClosedIn ha⟩

/-- Any morphism of Huber pairs into a subsingleton coefficient ring is finite étale. -/
theorem Hom.IsFiniteEtale.of_subsingleton {φ : Hom S T} [Subsingleton B] : φ.IsFiniteEtale where
  finite := by
    let _ := φ.toRingHom.toAlgebra
    exact RingHom.finite_algebraMap.mpr inferInstance
  etale := by
    let _ := φ.toRingHom.toAlgebra
    exact RingHom.etale_algebraMap.mpr inferInstance
  isModuleTopology := by
    let _ := φ.toRingHom.toAlgebra
    exact inferInstance
  plus_eq := by
    ext b
    rw [Subsingleton.elim b 0]
    exact ⟨fun _ ↦ Subring.zero_mem _, fun _ ↦ T.plus.zero_mem⟩

/-- The composite of finite étale morphisms of Huber pairs is finite étale. Both its natural
topology and its integral-closure plus ring are taken over the original source pair. -/
theorem Hom.IsFiniteEtale.comp {f : Hom S T} {g : Hom T U} (hg : g.IsFiniteEtale)
    (hf : f.IsFiniteEtale) : (g.comp f).IsFiniteEtale where
  finite := by
    rw [Hom.toRingHom_comp]
    exact hg.finite.comp hf.finite
  etale := by
    rw [Hom.toRingHom_comp]
    exact hg.etale.comp hf.etale
  isModuleTopology := by
    rw [Hom.toRingHom_comp]
    algebraize [f.toRingHom, g.toRingHom, g.toRingHom.comp f.toRingHom]
    have : Module.Finite A B := hf.finite
    have : IsModuleTopology A B := hf.isModuleTopology
    have : IsModuleTopology B C := hg.isModuleTopology
    exact IsModuleTopology.restrictScalars A B C
  plus_eq := by
    ext c
    rw [Subalgebra.mem_toSubring, mem_integralClosure_iff]
    refine ⟨fun hc ↦ ?_, (g.comp f).mem_plus_of_isIntegral⟩
    have hplus (b : B) (hb : b ∈ T.plus) : IsIntegral (S.plus.map f.toRingHom) b := by
      rw [hf.plus_eq] at hb
      exact (mem_integralClosure_iff _ _).mp hb
    rw [hg.plus_eq] at hc
    exact Hom.isIntegral_plus_map_comp hplus ((mem_integralClosure_iff _ _).mp hc)

section SqZeroLifting

/-- **Formal unramifiedness of finite étale morphisms of Huber pairs.** Two morphisms `(B, B⁺) →
(C, C⁺)` under `(A, A⁺)` that agree after composing with `quotientHom U I` for a square-zero ideal
`I` (`I ^ 2 = ⊥`) are equal. -/
theorem Hom.IsFiniteEtale.eq_of_sqZero_quotient {ψ : Hom S T} (hψ : ψ.IsFiniteEtale)
    {I : Ideal C} (hI : I ^ 2 = ⊥) {σ₁ σ₂ : Hom T U}
    (hψ_eq : σ₁.comp ψ = σ₂.comp ψ)
    (hq_eq : (quotientHom U I).comp σ₁ = (quotientHom U I).comp σ₂) :
    σ₁ = σ₂ := by
  let _ : Algebra A B := ψ.toRingHom.toAlgebra
  let _ : Algebra A C := (σ₁.toRingHom.comp ψ.toRingHom).toAlgebra
  have _ : Algebra.Etale A B := hψ.etale
  have hring : σ₂.toRingHom.comp ψ.toRingHom = σ₁.toRingHom.comp ψ.toRingHom := by
    simpa only [Hom.toRingHom_comp] using congrArg Hom.toRingHom hψ_eq.symm
  let f₁ : B →ₐ[A] C := { σ₁.toRingHom with commutes' := fun _ ↦ rfl }
  let f₂ : B →ₐ[A] C := { σ₂.toRingHom with commutes' := fun a ↦ RingHom.congr_fun hring a }
  have hmk : (Ideal.Quotient.mkₐ A I).comp f₁ = (Ideal.Quotient.mkₐ A I).comp f₂ := by
    ext b
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, f₁, f₂, AlgHom.coe_mk]
    simpa only [Hom.toRingHom_comp, Hom.toRingHom_quotientHom, RingHom.comp_apply] using
      RingHom.congr_fun (congrArg Hom.toRingHom hq_eq) b
  have hf : f₁ = f₂ := (Algebra.FormallyEtale.comp_bijective A B I hI).injective hmk
  exact Hom.ext (RingHom.ext fun b ↦ AlgHom.congr_fun hf b)

/-- **Infinitesimal lifting (existence) for finite étale morphisms of Huber pairs** along a
square-zero ideal quotient `(C, C⁺) → (C ⧸ I, (U.quotient I)⁺)`. -/
theorem Hom.IsFiniteEtale.exists_of_sqZero_quotient {ψ : Hom S T} (hψ : ψ.IsFiniteEtale)
    {I : Ideal C} (hI : I ^ 2 = ⊥) (α : Hom S U) (β₀ : Hom T (U.quotient I))
    (hcomm : β₀.comp ψ = (quotientHom U I).comp α) :
    ∃ β : Hom T U, β.comp ψ = α ∧ (quotientHom U I).comp β = β₀ := by
  let _ : Algebra A B := ψ.toRingHom.toAlgebra
  let _ : Algebra A C := α.toRingHom.toAlgebra
  have _ : Algebra.Etale A B := hψ.etale
  have hring : β₀.toRingHom.comp ψ.toRingHom = (Ideal.Quotient.mk I).comp α.toRingHom := by
    simpa only [Hom.toRingHom_comp, Hom.toRingHom_quotientHom] using
      congrArg Hom.toRingHom hcomm
  let β₀_alg : B →ₐ[A] C ⧸ I :=
    { β₀.toRingHom with commutes' := fun a ↦ RingHom.congr_fun hring a }
  obtain ⟨β_alg, hβ_alg⟩ := (Algebra.FormallyEtale.comp_bijective A B I hI).surjective β₀_alg
  obtain ⟨β, hβ⟩ := hψ.exists_hom α β_alg.toRingHom β_alg.comp_algebraMap
  refine ⟨β, Hom.ext (by rw [Hom.toRingHom_comp, hβ]; exact β_alg.comp_algebraMap), ?_⟩
  refine Hom.ext (RingHom.ext fun b ↦ ?_)
  have hb := AlgHom.congr_fun hβ_alg b
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, β₀_alg, AlgHom.coe_mk] at hb
  simpa only [Hom.toRingHom_comp, Hom.toRingHom_quotientHom, hβ, RingHom.comp_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hb

/-- **Unique infinitesimal lifting for finite étale morphisms of Huber pairs** along a square-zero
ideal quotient `(C, C⁺) → (C ⧸ I, (U.quotient I)⁺)`. -/
theorem Hom.IsFiniteEtale.existsUnique_of_sqZero_quotient {ψ : Hom S T} (hψ : ψ.IsFiniteEtale)
    {I : Ideal C} (hI : I ^ 2 = ⊥) (α : Hom S U) (β₀ : Hom T (U.quotient I))
    (hcomm : β₀.comp ψ = (quotientHom U I).comp α) :
    ∃! β : Hom T U, β.comp ψ = α ∧ (quotientHom U I).comp β = β₀ := by
  obtain ⟨β, hβ₁, hβ₂⟩ := hψ.exists_of_sqZero_quotient hI α β₀ hcomm
  exact ⟨β, ⟨hβ₁, hβ₂⟩, fun β' ⟨hβ'₁, hβ'₂⟩ ↦
    hψ.eq_of_sqZero_quotient hI (hβ'₁.trans hβ₁.symm) (hβ'₂.trans hβ₂.symm)⟩

/-- Uniqueness of Huber-pair lifts along any quotient mapping `q` whose kernel is square-zero. -/
theorem Hom.IsFiniteEtale.eq_of_isQuotientMapping_sqZero_ker {ψ : Hom S T}
    (hψ : ψ.IsFiniteEtale)
    {D : Type*} [CommRing D] [TopologicalSpace D] [IsTopologicalRing D] [IsHuberRing D]
    {V : Pair D} {q : Hom U V} (hq : q.IsQuotientMapping)
    (hker : RingHom.ker q.toRingHom ^ 2 = ⊥) {σ₁ σ₂ : Hom T U}
    (hψ_eq : σ₁.comp ψ = σ₂.comp ψ) (hq_eq : q.comp σ₁ = q.comp σ₂) :
    σ₁ = σ₂ := by
  refine hψ.eq_of_sqZero_quotient hker hψ_eq ?_
  have hcomp : hq.quotientKerInverse.comp q = quotientHom U (RingHom.ker q.toRingHom) :=
    calc
      hq.quotientKerInverse.comp q =
          hq.quotientKerInverse.comp ((q.quotientLift _ le_rfl).comp (quotientHom U _)) :=
        congrArg hq.quotientKerInverse.comp (Hom.quotientLift_comp_quotientHom _ q le_rfl).symm
      _ = quotientHom U (RingHom.ker q.toRingHom) := by
        rw [← Hom.comp_assoc, hq.quotientKerInverse_comp_quotientLift, Hom.id_comp]
  simpa only [← Hom.comp_assoc, hcomp] using congrArg hq.quotientKerInverse.comp hq_eq

/-- Existence of Huber-pair lifts along any quotient mapping `q` whose kernel is square-zero. -/
theorem Hom.IsFiniteEtale.exists_of_isQuotientMapping_sqZero_ker {ψ : Hom S T}
    (hψ : ψ.IsFiniteEtale)
    {D : Type*} [CommRing D] [TopologicalSpace D] [IsTopologicalRing D] [IsHuberRing D]
    {V : Pair D} {q : Hom U V} (hq : q.IsQuotientMapping)
    (hker : RingHom.ker q.toRingHom ^ 2 = ⊥) (α : Hom S U) (β₀ : Hom T V)
    (hcomm : β₀.comp ψ = q.comp α) :
    ∃ β : Hom T U, β.comp ψ = α ∧ q.comp β = β₀ := by
  have hcomp : hq.quotientKerInverse.comp q = quotientHom U (RingHom.ker q.toRingHom) :=
    calc
      hq.quotientKerInverse.comp q =
          hq.quotientKerInverse.comp ((q.quotientLift _ le_rfl).comp (quotientHom U _)) :=
        congrArg hq.quotientKerInverse.comp (Hom.quotientLift_comp_quotientHom _ q le_rfl).symm
      _ = quotientHom U (RingHom.ker q.toRingHom) := by
        rw [← Hom.comp_assoc, hq.quotientKerInverse_comp_quotientLift, Hom.id_comp]
  have hcomm' : (hq.quotientKerInverse.comp β₀).comp ψ =
      (quotientHom U (RingHom.ker q.toRingHom)).comp α := by
    rw [Hom.comp_assoc, hcomm, ← Hom.comp_assoc, hcomp]
  obtain ⟨β, hβ₁, hβ₂⟩ :=
    hψ.exists_of_sqZero_quotient hker α (hq.quotientKerInverse.comp β₀) hcomm'
  refine ⟨β, hβ₁, ?_⟩
  calc
    q.comp β = (q.quotientLift _ le_rfl).comp ((quotientHom U _).comp β) := by
      rw [← Hom.comp_assoc, Hom.quotientLift_comp_quotientHom]
    _ = ((q.quotientLift _ le_rfl).comp hq.quotientKerInverse).comp β₀ := by
      rw [hβ₂, Hom.comp_assoc]
    _ = β₀ := by rw [hq.quotientLift_comp_quotientKerInverse, Hom.id_comp]

end SqZeroLifting

end TauCeti.Huber.Pair
