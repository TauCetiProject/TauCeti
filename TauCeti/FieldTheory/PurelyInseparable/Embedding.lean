/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Exponent

/-!
# Embedding a purely inseparable extension into a reduced ring with enough roots

Let `M / K` be a purely inseparable extension of exponent at most `n`, so that
`x ↦ x ^ (p ^ n)` is a ring homomorphism `M →+* K` (`IsPurelyInseparable.iterateFrobenius`). If a
reduced commutative ring `K'` over `K` contains `p ^ n`-th roots of the images of a generating set
of `M`, then `M` embeds into `K'` over `K`: the embedding is `ψ⁻¹ ∘ φ` for `φ` the Frobenius of `M`
into `K` and `ψ` the (injective, as `K'` is reduced) Frobenius of `K'`. Mathlib provides this
embedding only into perfect fields
(`IsPurelyInseparable.instNonemptyAlgHomOfPerfectField`); the target that
normalization-finiteness needs, `k'(X_1, …, X_r)`, is not perfect.

The companion existence statement — for finitely many elements of a field, a finite extension
containing `n`-th roots of all of them — is
`TauCeti.exists_finiteDimensional_forall_exists_pow_eq`, in
`TauCeti/FieldTheory/IntermediateField/Adjoin/Roots.lean`; nothing about it is specific to purely
inseparable extensions.

## Main results

* `TauCeti.IsPurelyInseparable.nonempty_algHom_of_forall_exists_pow_eq`: the embedding of a
  purely inseparable extension of bounded exponent into any reduced commutative ring over `K`
  containing `p ^ n`-th roots of the Frobenius images of a generating set.

## Provenance

The mathematics is the field-theoretic half of the "some details omitted" sentence of Stacks
10.161.13 (tag 032O): there is a finite purely inseparable `L' / K` and `q = p ^ e` with
`L ⊂ L'(x^{1/q})`.
-/

public section

universe u

namespace TauCeti

/-- Source: Stacks, Lemma 10.161.13 (tag 032O), proof: "`L ⊂ L′(x^{1/q})`; some details omitted"
— the embedding. Let `M / K` be purely inseparable of exponent at most `n`, with Frobenius
`φ = IsPurelyInseparable.iterateFrobenius K M p hn : M →+* K`, and let `s` generate `M` over
`K`. If every `φ x` for `x ∈ s` has a `p ^ n`-th root in a reduced commutative ring `K'` over
`K`, then `M` embeds into `K'` over `K`. -/
theorem IsPurelyInseparable.nonempty_algHom_of_forall_exists_pow_eq (K M : Type*) [Field K]
    [Field M] [Algebra K M] [IsPurelyInseparable.HasExponent K M] (p : ℕ) [ExpChar K p] {n : ℕ}
    (hn : IsPurelyInseparable.exponent K M ≤ n) (K' : Type*) [CommRing K'] [IsReduced K']
    [Algebra K K'] {s : Set M} (hs : IntermediateField.adjoin K s = ⊤)
    (h : ∀ x ∈ s, ∃ y : K',
      y ^ p ^ n = algebraMap K K' (IsPurelyInseparable.iterateFrobenius K M p hn x)) :
    Nonempty (M →ₐ[K] K') := by
  nontriviality K'
  have : ExpChar K' p := expChar_of_injective_algebraMap (algebraMap K K').injective p
  let ψ := iterateFrobenius K' p n
  have hψ : Function.Injective ψ := iterateFrobenius_inj K' p n
  let θ : M →+* K' := (algebraMap K K').comp (IsPurelyInseparable.iterateFrobenius K M p hn)
  -- On the image of `K`, `θ` and `ψ` agree: this gives both that the subalgebra below contains
  -- `K` and that the embedding assembled at the end is `K`-linear.
  have hKθ (a : K) : θ (algebraMap K M a) = ψ (algebraMap K K' a) := by
    simp [θ, ψ, iterateFrobenius_def, IsPurelyInseparable.iterateFrobenius_algebraMap]
  -- Every `θ x` is a `p ^ n`-th power: the `x` for which it is form a `K`-subalgebra containing
  -- `s`, and `s` generates `M` as a `K`-algebra because `M / K` is algebraic.
  let G : Subalgebra K M :=
    { ψ.range.comap θ with algebraMap_mem' := fun a ↦ ⟨_, (hKθ a).symm⟩ }
  have hgood (x : M) : θ x ∈ ψ.range := by
    have hs' : Algebra.adjoin K s = ⊤ := by
      rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
        fun x _ ↦ Algebra.IsAlgebraic.isAlgebraic x, hs, IntermediateField.top_toSubalgebra]
    have hG : ⊤ ≤ G := by
      rw [← hs']
      refine Algebra.adjoin_le fun z hz ↦ ?_
      obtain ⟨y, hy⟩ := h z hz
      exact ⟨y, by simpa [θ, ψ, iterateFrobenius_def] using hy⟩
    -- membership in `G` is, by construction, membership of `θ x` in the range of `ψ`
    exact hG Algebra.mem_top
  -- Invert `ψ` on its range. This is only a ring map: `ψ` is `K`-semilinear along Frobenius,
  -- not `K`-linear.
  let σ : M →+* K' :=
    (RingEquiv.ofLeftInverse (Function.leftInverse_invFun hψ)).symm.toRingHom.comp
      (θ.codRestrict ψ.range hgood)
  have hσ (x : M) : ψ (σ x) = θ x := by
    simpa [σ] using Function.invFun_eq (hgood x)
  -- `K`-linearity is forced by injectivity of `ψ`.
  exact ⟨{ toRingHom := σ
           commutes' := fun a ↦ hψ ((hσ _).trans (hKθ a)) }⟩

end TauCeti
