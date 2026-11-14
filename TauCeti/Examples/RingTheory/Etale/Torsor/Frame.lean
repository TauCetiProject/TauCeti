/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Ring.Prod
import Mathlib.Data.Rat.Lemmas
import TauCeti.RingTheory.Etale.Torsor.Splitting

/-!
# Tests for frame torsors, universal frames, and splitting finite étale covers

For the split cover `Fin 2 → A`, the frame algebra is the trivial `Perm (Fin 2)`-torsor, its two
slot projections are exchanged by `Equiv.swap 0 1`, and the universal frame twists coordinates by
the sheet permutation.

For the nonsplit quadratic étale cover `ℚ[X] ⧸ (X ^ 2 - 2)` over `ℚ`, the algebra has no section
over `ℚ`, hence is not totally split over `ℚ`; over its `Perm (Fin 2)`-frame torsor `P`, the
universal frame splits `P ⊗[ℚ] S ≃ₐ[P] (Fin 2 → P)` and exhibits two distinct square roots of `2`
in `P` exchanged by `Equiv.swap 0 1`.

Over the disconnected ring `ℚ × ℚ`, the clopen projection `(ℚ × ℚ) ⧸ (1 - (1, 0))` is finite étale
of non-constant stalk rank (`1` on one point of `Spec (ℚ × ℚ)` and `0` on the other), so constant-
rank Galois closure theorems do not apply directly, whereas
`TauCeti.Algebra.exists_isFiniteEtaleTorsor_isTotallySplit` produces a finite étale torsor
splitting it.
-/

open Polynomial
open scoped TensorProduct

universe u

namespace TauCeti.Algebra

section SplitCover

/-- *test_split_rank_two*: on the split cover `Fin 2 → A` over a nontrivial ring `A`, the two slot
maps into `FrameAlgebra A (Fin 2 → A) (Fin 2)` are distinct and swapped by `Equiv.swap 0 1`. -/
example (A : Type*) [CommRing A] [Nontrivial A] :
    FrameAlgebra.slotAlgHom A (Fin 2 → A) (0 : Fin 2) ≠
      FrameAlgebra.slotAlgHom A (Fin 2 → A) (1 : Fin 2) ∧
    ∀ f : Fin 2 → A,
      Equiv.swap (0 : Fin 2) 1 • FrameAlgebra.slotAlgHom A (Fin 2 → A) (0 : Fin 2) f =
        FrameAlgebra.slotAlgHom A (Fin 2 → A) (1 : Fin 2) f := by
  have hrank : Module.rankAtStalk (R := A) (Fin 2 → A) = Fintype.card (Fin 2) := by
    ext p
    simp [Module.rankAtStalk_fin_fun]
  refine ⟨fun h ↦ ?_, fun f ↦ by simp⟩
  exact absurd (FrameAlgebra.slotAlgHom_injective_of_etale hrank h) (by decide)

/-- *test_universalFrame_split_twist*: under `permEquiv`, the `0`-th coordinate of
`universalFrameEquivPi A (Fin 2) (1 ⊗ f)` evaluates to `f 0` on the identity sheet and to `f 1` on
the transposed sheet `Equiv.swap 0 1`. -/
example (A : Type*) [CommRing A] (f : Fin 2 → A) :
    FrameAlgebra.permEquiv A (Fin 2)
        (FrameAlgebra.universalFrameEquivPi A (Fin 2) (1 ⊗ₜ f) 0) 1 = f 0 ∧
    FrameAlgebra.permEquiv A (Fin 2)
        (FrameAlgebra.universalFrameEquivPi A (Fin 2) (1 ⊗ₜ f) 0) (Equiv.swap 0 1) = f 1 := by
  simp

end SplitCover

section QuadraticCover

/-- *test_quadratic_nonsplit_over_base*: `ℚ[X] ⧸ (X ^ 2 - 2)` is finite étale of constant rank `2`
over `ℚ`, is not totally split over `ℚ`, and is split into two sheets over its `Perm (Fin 2)`-frame
torsor `P`, where the two slot images of `X` are distinct square roots of `2` swapped by
`Equiv.swap 0 1`. -/
example :
    let q : ℚ[X] := X ^ 2 - C 2
    have hmon : q.Monic := monic_X_pow_sub_C (2 : ℚ) (by norm_num)
    have hsep : q.Separable := separable_X_pow_sub_C (2 : ℚ) (by norm_num) (by norm_num)
    letI : Algebra.Etale ℚ (AdjoinRoot q) := hmon.etale_adjoinRoot_iff.mpr hsep
    letI : Module.Finite ℚ (AdjoinRoot q) := (AdjoinRoot.powerBasis hmon.ne_zero).finite
    ¬ IsTotallySplit ℚ (AdjoinRoot q) ∧
    ∃ hrank : Module.rankAtStalk (R := ℚ) (AdjoinRoot q) = Fintype.card (Fin 2),
      let P := FrameAlgebra ℚ (AdjoinRoot q) (Fin 2)
      IsFiniteEtaleTorsor (Equiv.Perm (Fin 2)) ℚ P ∧
      Nonempty (P ⊗[ℚ] AdjoinRoot q ≃ₐ[P] (Fin 2 → P)) ∧
      let r₀ : P := FrameAlgebra.slotAlgHom ℚ (AdjoinRoot q) (0 : Fin 2) (AdjoinRoot.root q)
      let r₁ : P := FrameAlgebra.slotAlgHom ℚ (AdjoinRoot q) (1 : Fin 2) (AdjoinRoot.root q)
      r₀ ^ 2 = 2 ∧ r₁ ^ 2 = 2 ∧ r₀ ≠ r₁ ∧ Equiv.swap (0 : Fin 2) 1 • r₀ = r₁ := by
  let q : ℚ[X] := X ^ 2 - C 2
  have hmon : q.Monic := monic_X_pow_sub_C (2 : ℚ) (by norm_num)
  have hsep : q.Separable := separable_X_pow_sub_C (2 : ℚ) (by norm_num) (by norm_num)
  have : Algebra.Etale ℚ (AdjoinRoot q) := hmon.etale_adjoinRoot_iff.mpr hsep
  let pb := AdjoinRoot.powerBasis hmon.ne_zero
  have : Module.Finite ℚ (AdjoinRoot q) := pb.finite
  have hdeg : q.natDegree = 2 := by
    dsimp [q]
    rw [natDegree_X_pow_sub_C]
  have hfinrank : Module.finrank ℚ (AdjoinRoot q) = 2 := by
    rw [pb.finrank, AdjoinRoot.powerBasis_dim, hdeg]
  have hrank : Module.rankAtStalk (R := ℚ) (AdjoinRoot q) = Fintype.card (Fin 2) := by
    ext p
    rw [Module.rankAtStalk_eq_finrank_of_free, hfinrank]
    simp
  have hroot_sq {T : Type} [CommRing T] [Algebra ℚ T] (φ : AdjoinRoot q →ₐ[ℚ] T) :
      φ (AdjoinRoot.root q) ^ 2 = 2 := by
    have h0 : aeval (φ (AdjoinRoot.root q)) q = 0 := by
      rw [aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
    simpa [q, sub_eq_zero, map_ofNat] using h0
  refine ⟨fun hsplit ↦ ?_, hrank, FrameAlgebra.isFiniteEtaleTorsor hrank,
    ⟨FrameAlgebra.universalFrameEquiv hrank⟩, ?_⟩
  · -- A total splitting over `ℚ` would give a `ℚ`-algebra section, hence a rational root of
    -- `X ^ 2 - 2`.
    have : Nontrivial (AdjoinRoot q) :=
      Module.nontrivial_of_finrank_pos (R := ℚ) (by omega)
    obtain ⟨σ⟩ := hsplit.nonempty_algHom_of_faithfulSMul
    have h2 : IsSquare ((2 : ℕ) : ℚ) :=
      ⟨σ (AdjoinRoot.root q), by rw [Nat.cast_ofNat, ← sq, hroot_sq σ]⟩
    exact Nat.prime_two.not_isSquare (Rat.isSquare_natCast_iff.mp h2)
  · dsimp only
    refine ⟨hroot_sq _, hroot_sq _, fun heq ↦ ?_, by simp⟩
    have hhom : FrameAlgebra.slotAlgHom ℚ (AdjoinRoot q) (0 : Fin 2) =
        FrameAlgebra.slotAlgHom ℚ (AdjoinRoot q) (1 : Fin 2) :=
      AdjoinRoot.algHom_ext heq
    exact absurd (FrameAlgebra.slotAlgHom_injective_of_etale hrank hhom) (by decide)

end QuadraticCover

section NonConstantRank

/-- *test_nonconstant_rank_splitting*: over `ℚ × ℚ`, the clopen factor `(ℚ × ℚ) ⧸ (1 - (1, 0))` is
finite étale with non-constant stalk rank, yet `exists_isFiniteEtaleTorsor_isTotallySplit` produces
a finite étale torsor over `ℚ × ℚ` splitting it. -/
example :
    let A := ℚ × ℚ
    let e : A := (1, 0)
    have he : IsIdempotentElem e := Prod.ext (mul_one 1) (mul_zero 0)
    let S := A ⧸ Ideal.span {1 - e}
    letI : Algebra.Etale A S := Etale.quotient_span_singleton he.one_sub
    (¬ ∃ d : ℕ, Module.rankAtStalk (R := A) S = d) ∧
    ∃ (G : Type) (_ : Group G) (_ : Finite G) (P : Type) (_ : CommRing P)
      (_ : Algebra A P) (_ : MulSemiringAction G P) (_ : SMulCommClass G A P),
      IsFiniteEtaleTorsor G A P ∧ IsTotallySplit P (P ⊗[A] S) := by
  let A := ℚ × ℚ
  let e : A := (1, 0)
  have he : IsIdempotentElem e := Prod.ext (mul_one 1) (mul_zero 0)
  let S := A ⧸ Ideal.span {1 - e}
  have : Algebra.Etale A S := Etale.quotient_span_singleton he.one_sub
  refine ⟨?_, exists_isFiniteEtaleTorsor_isTotallySplit A S⟩
  rintro ⟨d, hd⟩
  -- Compare stalk ranks at the kernels of `Prod.fst` and `Prod.snd`.
  let p₁ : PrimeSpectrum A := ⟨RingHom.ker (RingHom.fst ℚ ℚ), RingHom.ker_isPrime _⟩
  let p₂ : PrimeSpectrum A := ⟨RingHom.ker (RingHom.snd ℚ ℚ), RingHom.ker_isPrime _⟩
  have h₁ := (congrFun hd p₁).symm.trans (Module.rankAtStalk_quotient_span_one_sub he p₁)
  have h₂ := (congrFun hd p₂).symm.trans (Module.rankAtStalk_quotient_span_one_sub he p₂)
  have he₁ : e ∉ p₁.asIdeal := by
    dsimp [p₁, e]
    rw [RingHom.mem_ker, RingHom.coe_fst]
    exact one_ne_zero
  have he₂ : e ∈ p₂.asIdeal := by
    dsimp [p₂, e]
    rw [RingHom.mem_ker, RingHom.coe_snd]
  simp only [he₁, ↓reduceIte, Pi.natCast_apply, Nat.cast_id] at h₁
  simp only [he₂, ↓reduceIte, Pi.natCast_apply, Nat.cast_id] at h₂
  omega

end NonConstantRank

section Degenerate

/-- *test_subsingleton_base*: over the zero ring, `exists_isFiniteEtaleTorsor_isTotallySplit`
applies without nontriviality assumptions. -/
example (A : Type u) [CommRing A] [Subsingleton A] (S : Type*) [CommRing S] [Algebra A S]
    [Algebra.Etale A S] [Module.Finite A S] :
    ∃ (G : Type u) (_ : Group G) (_ : Finite G) (P : Type u) (_ : CommRing P)
      (_ : Algebra A P) (_ : MulSemiringAction G P) (_ : SMulCommClass G A P),
      IsFiniteEtaleTorsor G A P ∧ IsTotallySplit P (P ⊗[A] S) :=
  exists_isFiniteEtaleTorsor_isTotallySplit A S

/-- *test_preconnected_finite_split*: over a ring with preconnected prime spectrum (such as any
integral domain or local ring), `exists_isFiniteEtaleTorsor_isFiniteSplit` upgrades the conclusion
to constant-rank splitting `Algebra.IsFiniteSplit`. -/
example (A : Type u) [CommRing A] [IsDomain A] (S : Type*) [CommRing S] [Algebra A S]
    [Algebra.Etale A S] [Module.Finite A S] :
    ∃ (G : Type u) (_ : Group G) (_ : Finite G) (P : Type u) (_ : CommRing P)
      (_ : Algebra A P) (_ : MulSemiringAction G P) (_ : SMulCommClass G A P),
      IsFiniteEtaleTorsor G A P ∧ Algebra.IsFiniteSplit P (P ⊗[A] S) :=
  exists_isFiniteEtaleTorsor_isFiniteSplit A S

end Degenerate

end TauCeti.Algebra
