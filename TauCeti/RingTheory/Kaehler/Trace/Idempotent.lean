/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Localization.Away.Lemmas
public import TauCeti.RingTheory.Kaehler.Trace.Basic

/-!
# The trace of differentials and idempotents

Let `B` be a finite free `R`-algebra and `e ∈ B` an idempotent, so that
`B ≅ B ⧸ (1 - e) × B ⧸ (e)`. If both factors are free over `R`, the trace derivation of `B`
restricted to `e B` is the trace derivation of `B ⧸ (1 - e)`
(`Algebra.traceDeriv_mul_idempotent`). Consequently, duality for the trace of differentials can be
checked on the factors of `B`: if every maximal ideal of `B` avoids an idempotent `e` for which
the trace derivation of `B ⧸ (1 - e)` induces an isomorphism `Ω ≅ Hom_R(-, R)`, then so does the
trace derivation of `B`
(`KaehlerDifferential.bijective_liftKaehlerDifferential_traceDerivation_of_isIdempotentElem`).

## Source

Adapted from `Jacobian/RingTheory/Kaehler/TraceIdempotent.lean` in the Jacobian library,
accepted release `baef7723da528551b7d2f93bd9a9a53303b04dbc`.
-/

@[expose] public section

open Matrix

namespace Matrix

variable {k R M : Type*} [CommRing k] [CommRing R] [Algebra k R] [AddCommGroup M] [Module R M]
  [Module k M] (D : Derivation k R M)

/-- `Tr(X D(Y))` for block diagonal matrices is the sum over the blocks. -/
lemma traceDerivForm_fromBlocks {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n]
    [Fintype p] (X₁ : Matrix l m R) (X₂ : Matrix n p R) (Y₁ : Matrix m l R)
    (Y₂ : Matrix p n R) :
    traceDerivForm D (fromBlocks X₁ 0 0 X₂) (fromBlocks Y₁ 0 0 Y₂) =
      traceDerivForm D X₁ Y₁ + traceDerivForm D X₂ Y₂ := by
  simp [traceDerivForm, Fintype.sum_sum_type]

end Matrix

namespace Algebra

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] {e : B}

/-- The basis of `B` adapted to the decomposition `B ≅ B ⧸ (1 - e) × B ⧸ (e)`. -/
noncomputable def idempotentBasis (he : IsIdempotentElem e) {ι₁ ι₂ : Type*}
    (b₁ : Module.Basis ι₁ R (B ⧸ Ideal.span {1 - e}))
    (b₂ : Module.Basis ι₂ R (B ⧸ Ideal.span {e})) : Module.Basis (ι₁ ⊕ ι₂) R B :=
  (b₁.prod b₂).map (AlgEquiv.prodQuotientOfIsIdempotentElem R he.one_sub he
    (sub_add_cancel 1 e) he.one_sub_mul_self).toLinearEquiv.symm

/-- The matrix of multiplication in the basis adapted to `B ≅ B ⧸ (1 - e) × B ⧸ (e)` is block
diagonal. -/
lemma leftMulMatrix_idempotentBasis (he : IsIdempotentElem e) {ι₁ ι₂ : Type*} [Fintype ι₁]
    [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    (b₁ : Module.Basis ι₁ R (B ⧸ Ideal.span {1 - e}))
    (b₂ : Module.Basis ι₂ R (B ⧸ Ideal.span {e})) (x : B) :
    leftMulMatrix (idempotentBasis he b₁ b₂) x =
      fromBlocks (leftMulMatrix b₁ (Ideal.Quotient.mk _ x)) 0 0
        (leftMulMatrix b₂ (Ideal.Quotient.mk _ x)) := by
  have hrepr (y : B) : (idempotentBasis he b₁ b₂).repr y =
      (b₁.prod b₂).repr ((AlgEquiv.prodQuotientOfIsIdempotentElem R he.one_sub he
        (sub_add_cancel 1 e) he.one_sub_mul_self) y) := by
    simp [idempotentBasis]
  have hb (j : ι₁ ⊕ ι₂) : (AlgEquiv.prodQuotientOfIsIdempotentElem R he.one_sub he
      (sub_add_cancel 1 e) he.one_sub_mul_self) (idempotentBasis he b₁ b₂ j) =
      b₁.prod b₂ j := by
    simp [idempotentBasis]
  ext i j
  rw [leftMulMatrix_eq_repr_mul, hrepr, map_mul, hb]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr, leftMulMatrix_eq_repr_mul,
      AlgEquiv.prodQuotientOfIsIdempotentElem_apply]

variable {k M : Type*} [CommRing k] [Algebra k R] [AddCommGroup M] [Module R M] [Module k M]
  (D : Derivation k R M)

/-- The trace derivation of `B` on `e B` is the trace derivation of `B ⧸ (1 - e)`. -/
lemma traceDeriv_mul_idempotent [Module.Free R B] [Module.Finite R B]
    [Module.Free R (B ⧸ Ideal.span {1 - e})] [Module.Finite R (B ⧸ Ideal.span {1 - e})]
    [Module.Free R (B ⧸ Ideal.span {e})] [Module.Finite R (B ⧸ Ideal.span {e})]
    (he : IsIdempotentElem e) (a c : B) :
    traceDeriv D a (e * c) = traceDeriv D (Ideal.Quotient.mk (Ideal.span {1 - e}) a)
      (Ideal.Quotient.mk (Ideal.span {1 - e}) c) := by
  classical
  set b₁ := Module.Free.chooseBasis R (B ⧸ Ideal.span {1 - e})
  set b₂ := Module.Free.chooseBasis R (B ⧸ Ideal.span {e})
  rw [traceDeriv_eq D (idempotentBasis he b₁ b₂), traceDeriv_eq D b₁, traceDerivAux,
    traceDerivAux, leftMulMatrix_idempotentBasis, leftMulMatrix_idempotentBasis,
    traceDerivForm_fromBlocks]
  have h1 : Ideal.Quotient.mk (Ideal.span {1 - e}) (e * c) = Ideal.Quotient.mk _ c := by
    rw [Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton'.mpr ⟨-c, by ring⟩
  have h2 : Ideal.Quotient.mk (Ideal.span {e}) (e * c) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton'.mpr ⟨c, by ring⟩
  rw [h1, h2, map_zero, traceDerivForm_zero_left, add_zero]

end Algebra

namespace KaehlerDifferential

open Algebra

attribute [local instance] precompModule precompModule_isScalarTower

variable {k R B : Type*} [CommRing k] [CommRing R] [CommRing B] [Algebra k R] [Algebra R B]
  [Algebra k B] [IsScalarTower k R B] [Module.Free R B] [Module.Finite R B]
  (D : Derivation k R R) {e : B}

/-- The map `Ω_{B/k} → Hom_R(B, R)` induced by the trace derivation is compatible with the
quotient `B → B ⧸ (1 - e)` for an idempotent `e`. -/
lemma liftKaehlerDifferential_traceDerivation_mul_idempotent (he : IsIdempotentElem e)
    [Module.Free R (B ⧸ Ideal.span {1 - e})] [Module.Finite R (B ⧸ Ideal.span {1 - e})]
    [Module.Free R (B ⧸ Ideal.span {e})] [Module.Finite R (B ⧸ Ideal.span {e})]
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
    rfl
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | smul b x _ hx =>
    rw [LinearMap.map_smul, LinearMap.map_smul, precompModule_smul_apply, mul_left_comm, hx,
      ← algebraMap_smul (B ⧸ Ideal.span {1 - e}) b, LinearMap.map_smul, precompModule_smul_apply,
      Ideal.Quotient.algebraMap_eq, map_mul]

/-- **Duality for the trace of differentials can be checked on factors.** If every maximal ideal
of `B` avoids an idempotent `e` such that `B ⧸ (1 - e)` and `B ⧸ (e)` are free over `R` and the
trace derivation of `B ⧸ (1 - e)` induces an isomorphism `Ω ≅ Hom_R(-, R)`, then so does the
trace derivation of `B`. -/
theorem bijective_liftKaehlerDifferential_traceDerivation_of_isIdempotentElem
    (h : ∀ q : Ideal B, q.IsMaximal → ∃ e : B, IsIdempotentElem e ∧ e ∉ q ∧
      ∃ (_ : Module.Free R (B ⧸ Ideal.span {1 - e})) (_ : Module.Free R (B ⧸ Ideal.span {e})),
      Function.Bijective
        (traceDerivation (B := B ⧸ Ideal.span {1 - e}) D).liftKaehlerDifferential) :
    Function.Bijective (traceDerivation (B := B) D).liftKaehlerDifferential := by
  set Ψ := (traceDerivation (B := B) D).liftKaehlerDifferential
  refine ⟨(injective_iff_map_eq_zero Ψ).2 fun ω hω ↦ ?_, fun φ ↦ ?_⟩
  · let I : Ideal B := Submodule.comap (LinearMap.toSpanSingleton B _ ω) ⊥
    suffices I = ⊤ by
      have h1 : (1 : B) ∈ I := this ▸ Submodule.mem_top
      simpa [I] using h1
    by_contra hI
    obtain ⟨q, hq, hIq⟩ := Ideal.exists_le_maximal I hI
    obtain ⟨e, he, heq, _, _, hΨ⟩ := h q hq
    refine heq (hIq ?_)
    have : IsLocalization.Away e (B ⧸ Ideal.span {1 - e}) :=
      IsLocalization.Away.quotient_of_isIdempotentElem he
    have h0 : KaehlerDifferential.map k k B (B ⧸ Ideal.span {1 - e}) ω = 0 := by
      apply hΨ.1
      rw [map_zero]
      refine LinearMap.ext fun c ↦ ?_
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
      rw [← liftKaehlerDifferential_traceDerivation_mul_idempotent D he]
      change Ψ ω (e * c) = 0
      rw [hω, LinearMap.zero_apply]
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers e)
      (KaehlerDifferential.map k k B (B ⧸ Ideal.span {1 - e}))).1 h0
    change e • ω = 0
    rw [← he.pow_succ_eq n, pow_succ', mul_smul]
    rw [show e ^ n • ω = 0 from hn, smul_zero]
  · let I : Ideal B := Submodule.comap (LinearMap.toSpanSingleton B _ φ) (LinearMap.range Ψ)
    suffices I = ⊤ by
      have h1 : (1 : B) ∈ I := this ▸ Submodule.mem_top
      simpa [I] using h1
    by_contra hI
    obtain ⟨q, hq, hIq⟩ := Ideal.exists_le_maximal I hI
    obtain ⟨e, he, heq, _, _, hΨ⟩ := h q hq
    refine heq (hIq ?_)
    let σ : (B ⧸ Ideal.span {1 - e}) →ₗ[R] B :=
      (AlgEquiv.prodQuotientOfIsIdempotentElem R he.one_sub he
        (sub_add_cancel 1 e) he.one_sub_mul_self).toLinearEquiv.symm.toLinearMap ∘ₗ
        LinearMap.inl R _ _
    obtain ⟨ω₁, hω₁⟩ := hΨ.2 (φ ∘ₗ σ)
    obtain ⟨ω, rfl⟩ := KaehlerDifferential.map_surjective_of_surjective k k B
      (B ⧸ Ideal.span {1 - e}) Ideal.Quotient.mk_surjective ω₁
    refine ⟨e • ω, LinearMap.ext fun c ↦ ?_⟩
    rw [LinearMap.map_smul, precompModule_smul_apply,
      liftKaehlerDifferential_traceDerivation_mul_idempotent D he, hω₁]
    change φ (σ _) = φ (e * c)
    congr 1
    change (AlgEquiv.prodQuotientOfIsIdempotentElem R he.one_sub he
      (sub_add_cancel 1 e) he.one_sub_mul_self).symm
        (Ideal.Quotient.mk (Ideal.span {1 - e}) c, 0) = e * c
    rw [AlgEquiv.symm_apply_eq]
    change (Ideal.Quotient.mk (Ideal.span {1 - e}) c, (0 : B ⧸ Ideal.span {e})) =
      (Ideal.Quotient.mk (Ideal.span {1 - e}) (e * c),
        Ideal.Quotient.mk (Ideal.span {e}) (e * c))
    refine Prod.ext ?_ ?_
    · exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr ⟨c, by ring⟩)
    · exact ((Ideal.Quotient.eq_zero_iff_mem).mpr
        (Ideal.mem_span_singleton.mpr ⟨c, by ring⟩)).symm

end KaehlerDifferential
