/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.RingTheory.Etale.Kaehler
public import TauCeti.RingTheory.Trace.LeftMulMatrix
public import TauCeti.RingTheory.Idempotents.Product
public import TauCeti.Algebra.Module.Submodule.LocalGlobal
public import Mathlib.RingTheory.Localization.Away.Lemmas
public import TauCeti.RingTheory.Kaehler.Trace.Basic

/-!
# The trace of differentials and idempotents

Let `B` be a finite free `R`-algebra and `e ∈ B` an idempotent, so that
`B ≅ B ⧸ (1 - e) × B ⧸ (e)`. If both factors are free over `R`, the trace derivation of `B`
restricted to `e B` is the trace derivation of `B ⧸ (1 - e)`
(`Derivation.traceDeriv_mul_idempotent`). Duality for the trace of differentials can be
checked on the factors of `B`: if every maximal ideal of `B` avoids an idempotent `e` for which
the trace derivation of `B ⧸ (1 - e)` induces an isomorphism `Ω ≅ Hom_R(-, M)`, then so does the
trace derivation of `B`; see
`Derivation.bijective_liftKaehlerDifferential_traceDerivation_of_isIdempotentElem`.

-/

public section

open Matrix Algebra TauCeti.Algebra

namespace Derivation

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] {e : B}

variable {k M : Type*} [CommRing k] [Algebra k R] [AddCommGroup M] [Module R M] [Module k M]
  (D : Derivation k R M)

/-- The trace derivation of `B` on `e B` is the trace derivation of `B ⧸ (1 - e)`. -/
lemma traceDeriv_mul_idempotent [Module.Free R B] [Module.Finite R B]
    [Module.Free R (B ⧸ Ideal.span {1 - e})]
    [Module.Free R (B ⧸ Ideal.span {e})]
    (he : IsIdempotentElem e) (a c : B) :
    traceDeriv D a (e * c) = traceDeriv D (Ideal.Quotient.mk (Ideal.span {1 - e}) a)
      (Ideal.Quotient.mk (Ideal.span {1 - e}) c) := by
  classical
  set b₁ := Module.Free.chooseBasis R (B ⧸ Ideal.span {1 - e})
  set b₂ := Module.Free.chooseBasis R (B ⧸ Ideal.span {e})
  rw [traceDeriv_eq D (idempotentBasis he b₁ b₂), traceDeriv_eq D b₁, traceDerivOfBasis_def,
    traceDerivOfBasis_def, leftMulMatrix_idempotentBasis, leftMulMatrix_idempotentBasis,
    traceDerivForm_fromBlocks]
  have h1 : Ideal.Quotient.mk (Ideal.span {1 - e}) (e * c) = Ideal.Quotient.mk _ c := by
    rw [Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton'.mpr ⟨-c, by ring⟩
  have h2 : Ideal.Quotient.mk (Ideal.span {e}) (e * c) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton'.mpr ⟨c, by ring⟩
  rw [h1, h2, map_zero, traceDerivForm_zero_left, add_zero]

end Derivation

namespace Derivation

open Algebra TauCeti.Algebra

variable {k R B : Type*} [CommRing k] [CommRing R] [CommRing B] [Algebra k R] [Algebra R B]
  [Algebra k B] [IsScalarTower k R B] [Module.Free R B] [Module.Finite R B]
  {M : Type*} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  (D : Derivation k R M) {e : B}

/-- The map `Ω_{B/k} → Hom_R(B, M)` induced by the trace derivation is compatible with the
quotient `B → B ⧸ (1 - e)` for an idempotent `e`. -/
lemma liftKaehlerDifferential_traceDerivation_mul_idempotent (he : IsIdempotentElem e)
    [Module.Free R (B ⧸ Ideal.span {1 - e})]
    [Module.Free R (B ⧸ Ideal.span {e})]
    (ω : Ω[B⁄k]) (c : B) :
    (traceDerivation (B := B) D).liftKaehlerDifferential ω (e * c) =
      (traceDerivation (B := B ⧸ Ideal.span {1 - e}) D).liftKaehlerDifferential
        (KaehlerDifferential.map k k B (B ⧸ Ideal.span {1 - e}) ω) (Ideal.Quotient.mk _ c) := by
  have hω : ω ∈ (⊤ : Submodule B Ω[B⁄k]) := Submodule.mem_top
  rw [← KaehlerDifferential.span_range_derivation] at hω
  induction hω using Submodule.span_induction generalizing c with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    rw [Derivation.liftKaehlerDifferential_comp_D, KaehlerDifferential.map_D,
      Derivation.liftKaehlerDifferential_comp_D, traceDerivation_apply, traceDerivation_apply,
      traceDeriv_mul_idempotent D he]
    rw [Ideal.Quotient.algebraMap_eq]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, PrecompLinearMap.add_apply, hx, hy]
  | smul b x _ hx =>
    rw [LinearMap.map_smul, LinearMap.map_smul, PrecompLinearMap.smul_apply, smul_eq_mul,
      mul_left_comm, hx,
      ← algebraMap_smul (B ⧸ Ideal.span {1 - e}) b, LinearMap.map_smul,
      PrecompLinearMap.smul_apply, smul_eq_mul, Ideal.Quotient.algebraMap_eq, map_mul]

/-- **Duality for the trace of differentials can be checked on factors.** If every maximal ideal
of `B` avoids an idempotent `e` such that `B ⧸ (1 - e)` and `B ⧸ (e)` are free over `R` and the
trace derivation of `B ⧸ (1 - e)` induces an isomorphism `Ω ≅ Hom_R(-, M)`, then so does the
trace derivation of `B`. -/
theorem bijective_liftKaehlerDifferential_traceDerivation_of_isIdempotentElem
    (h : ∀ q : Ideal B, q.IsMaximal → ∃ e : B, IsIdempotentElem e ∧ e ∉ q ∧
      ∃ (_ : Module.Free R (B ⧸ Ideal.span {1 - e})) (_ : Module.Free R (B ⧸ Ideal.span {e})),
      Function.Bijective
        (traceDerivation (B := B ⧸ Ideal.span {1 - e}) D).liftKaehlerDifferential) :
    Function.Bijective (traceDerivation (B := B) D).liftKaehlerDifferential := by
  let Ψ := (traceDerivation (B := B) D).liftKaehlerDifferential
  refine ⟨(injective_iff_map_eq_zero Ψ).2 fun ω hω ↦ ?_, fun φ ↦ ?_⟩
  · suffices ω ∈ (⊥ : Submodule B Ω[B⁄k]) by simpa using this
    apply Submodule.mem_of_forall_maximal_exists_smul_mem
    intro q hq
    obtain ⟨e, he, heq, _, _, hΨ⟩ := h q hq
    refine ⟨e, heq, ?_⟩
    have : IsLocalization.Away e (B ⧸ Ideal.span {1 - e}) :=
      IsLocalization.Away.quotient_of_isIdempotentElem he
    have h0 : KaehlerDifferential.map k k B (B ⧸ Ideal.span {1 - e}) ω = 0 := by
      apply hΨ.1
      rw [map_zero]
      refine PrecompLinearMap.ext fun c ↦ ?_
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
      rw [← liftKaehlerDifferential_traceDerivation_mul_idempotent D he]
      simpa only [PrecompLinearMap.zero_apply] using
        congrArg (fun φ : PrecompLinearMap R B M ↦ φ (e * c)) hω
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers e)
      (KaehlerDifferential.map k k B (B ⧸ Ideal.span {1 - e}))).1 h0
    rw [Submodule.mem_bot, ← he.pow_succ_eq n, pow_succ', mul_smul]
    -- The scalar in `hn` belongs to the powers submonoid; its action is the ambient action.
    have hn' : e ^ n • ω = 0 := by simpa only [Submonoid.smul_def] using hn
    rw [hn', smul_zero]
  · suffices φ ∈ LinearMap.range Ψ by exact this
    apply Submodule.mem_of_forall_maximal_exists_smul_mem
    intro q hq
    obtain ⟨e, he, heq, _, _, hΨ⟩ := h q hq
    refine ⟨e, heq, ?_⟩
    let σ : (B ⧸ Ideal.span {1 - e}) →ₗ[R] B :=
      (AlgEquiv.prodQuotientOfIsIdempotentElem R he.one_sub he
        (sub_add_cancel 1 e) he.one_sub_mul_self).toLinearEquiv.symm.toLinearMap ∘ₗ
        LinearMap.inl R _ _
    have hσ (c : B) : σ (Ideal.Quotient.mk (Ideal.span {1 - e}) c) = e * c := by
      simpa only [σ, LinearMap.comp_apply, LinearMap.inl_apply,
        LinearEquiv.coe_coe, AlgEquiv.coe_symm_toLinearEquiv] using
        AlgEquiv.prodQuotientOfIsIdempotentElem_symm_mk_zero (R := R) he c
    obtain ⟨ω₁, hω₁⟩ := hΨ.2
      (PrecompLinearMap.ofLinearMap (PrecompLinearMap.toLinearMap φ ∘ₗ σ))
    obtain ⟨ω, rfl⟩ := KaehlerDifferential.map_surjective_of_surjective k k B
      (B ⧸ Ideal.span {1 - e}) Ideal.Quotient.mk_surjective ω₁
    refine ⟨e • ω, PrecompLinearMap.ext fun c ↦ ?_⟩
    calc
      Ψ (e • ω) c = (e • Ψ ω : PrecompLinearMap R B M) c :=
        congrArg (fun φ : PrecompLinearMap R B M ↦ φ c) (Ψ.map_smul e ω)
      _ = Ψ ω (e * c) := by rw [PrecompLinearMap.smul_apply, smul_eq_mul]
      _ = (traceDerivation (B := B ⧸ Ideal.span {1 - e}) D).liftKaehlerDifferential
          (KaehlerDifferential.map k k B (B ⧸ Ideal.span {1 - e}) ω)
          (Ideal.Quotient.mk _ c) :=
        liftKaehlerDifferential_traceDerivation_mul_idempotent D he ω c
      _ = φ (e * c) := by
        rw [hω₁, PrecompLinearMap.ofLinearMap_apply, LinearMap.comp_apply,
          PrecompLinearMap.toLinearMap_apply, hσ]
      _ = (e • φ : PrecompLinearMap R B M) c := by
        rw [PrecompLinearMap.smul_apply, smul_eq_mul]

end Derivation
