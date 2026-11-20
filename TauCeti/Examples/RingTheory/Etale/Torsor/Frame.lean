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
# Tests for frame torsors, canonical sections, and symmetric-group splitting

For the split cover `Fin 2 → A`, the two canonical sections `singleAlgHom` into
`FrameAlgebra A (Fin 2 → A) (Fin 2)` are distinct and exchanged by `Equiv.swap 0 1`, and
`FrameAlgebra.liftPi` extracts the universal map from two point-separating `A`-algebra homs.

For the nonsplit quadratic étale cover `ℚ[X] ⧸ (X ^ 2 - 2)` over `ℚ`, the algebra has no section
over `ℚ`, hence is not totally split over `ℚ`; over its `Perm (Fin 2)`-frame torsor `P`, the
universal frame splits `P ⊗[ℚ] S ≃ₐ[P] (Fin 2 → P)` and exhibits two distinct square roots of `2`
in `P` exchanged by `Equiv.swap 0 1`.

Over the disconnected ring `ℚ × ℚ`, the clopen projection `(ℚ × ℚ) ⧸ (1 - (1, 0))` is finite étale
of non-constant stalk rank (`1` on one point of `Spec (ℚ × ℚ)` and `0` on the other), and
`TauCeti.Algebra.exists_perm_isFiniteEtaleTorsor_isTotallySplit` produces a symmetric-group torsor
splitting it; over an integral domain,
`TauCeti.Algebra.exists_perm_isFiniteEtaleTorsor_isFiniteSplit_of_preconnectedSpace` produces a
symmetric-group torsor making it finite split.
-/

open Polynomial TauCeti.Algebra
open scoped TensorProduct

universe u

namespace TauCeti.Examples.TorsorFrame

section SplitCover

/-- *test_split_rank_two*: on the split cover `Fin 2 → A` over a nontrivial ring `A`, the two
canonical sections into `FrameAlgebra A (Fin 2 → A) (Fin 2)` are distinct and swapped by
`Equiv.swap 0 1`. -/
example (A : Type*) [CommRing A] [Nontrivial A] :
    FrameAlgebra.singleAlgHom A (Fin 2 → A) (0 : Fin 2) ≠
      FrameAlgebra.singleAlgHom A (Fin 2 → A) (1 : Fin 2) ∧
    ∀ f : Fin 2 → A,
      Equiv.swap (0 : Fin 2) 1 • FrameAlgebra.singleAlgHom A (Fin 2 → A) (0 : Fin 2) f =
        FrameAlgebra.singleAlgHom A (Fin 2 → A) (1 : Fin 2) f := by
  have hrank : Module.rankAtStalk (R := A) (Fin 2 → A) = Fintype.card (Fin 2) := by
    ext p
    simp [Module.rankAtStalk_fin_fun]
  refine ⟨fun h ↦ ?_, fun f ↦ by simp⟩
  exact absurd (FrameAlgebra.singleAlgHom_injective_of_etale hrank h) (by decide)

/-- *test_liftPi_split*: `FrameAlgebra.liftPi` packages a pair of point-separating projections
`Fin 2 → A →ₐ[A] A` into an `A`-algebra map out of `FrameAlgebra A (Fin 2 → A) (Fin 2)`. -/
example (A : Type*) [CommRing A] :
    ∃ ψ : FrameAlgebra A (Fin 2 → A) (Fin 2) →ₐ[A] A,
      (∀ f : Fin 2 → A, ψ (FrameAlgebra.singleAlgHom A (Fin 2 → A) 0 f) = f 0) ∧
      (∀ f : Fin 2 → A, ψ (FrameAlgebra.singleAlgHom A (Fin 2 → A) 1 f) = f 1) := by
  let eval : Fin 2 → ((Fin 2 → A) →ₐ[A] A) := fun i ↦ Pi.evalAlgHom A (fun _ ↦ A) i
  have heval : ∀ i j : Fin 2, i ≠ j →
      Algebra.TensorProduct.productMap (eval i) (eval j)
        (Algebra.FormallyUnramified.elem A (Fin 2 → A)) = 0 := by
    intro i j hij
    let g : FrameAlgebra A (Fin 2 → A) (Fin 2) →ₐ[A] A :=
      (Pi.evalAlgHom A (fun _ ↦ A) (Equiv.refl (Fin 2))).comp
        (FrameAlgebra.permEquiv A (Fin 2)).toAlgHom
    have hcomp (k : Fin 2) : g.comp (FrameAlgebra.singleAlgHom A (Fin 2 → A) k) = eval k := by
      ext f
      simp [g, eval]
    have h0 := congrArg g (FrameAlgebra.productMap_singleAlgHom_elem (R := A) (S := Fin 2 → A) hij)
    rw [map_zero, ← AlgHom.comp_apply] at h0
    have hprod : g.comp (Algebra.TensorProduct.productMap
        (FrameAlgebra.singleAlgHom A (Fin 2 → A) i)
        (FrameAlgebra.singleAlgHom A (Fin 2 → A) j)) =
        Algebra.TensorProduct.productMap (eval i) (eval j) :=
      Algebra.TensorProduct.ext' fun a b ↦ by
        simp [hcomp]
    rwa [← hprod]
  refine ⟨FrameAlgebra.liftPi eval heval, fun f ↦ ?_, fun f ↦ ?_⟩
  · simp [eval]
  · simp [eval]

end SplitCover

section QuadraticCover

/-- *test_quadratic_nonsplit_over_base*: `ℚ[X] ⧸ (X ^ 2 - 2)` is finite étale of constant rank `2`
over `ℚ`, is not totally split over `ℚ`, and becomes totally split over its `Perm (Fin 2)`-frame
torsor `P`, where the two slot images of `X` are distinct square roots of `2` swapped by
`Equiv.swap 0 1`. -/
example :
    let q : ℚ[X] := X ^ 2 - C 2
    have hmon : q.Monic := monic_X_pow_sub_C (2 : ℚ) (by norm_num)
    have hsep : q.Separable := separable_X_pow_sub_C (2 : ℚ) (by norm_num) (by norm_num)
    letI : Algebra.Etale ℚ (AdjoinRoot q) := hmon.etale_adjoinRoot_iff.mpr hsep
    letI : Module.Finite ℚ (AdjoinRoot q) := (AdjoinRoot.powerBasis hmon.ne_zero).finite
    ¬ TauCeti.Algebra.IsTotallySplit ℚ (AdjoinRoot q) ∧
    ∃ hrank : Module.rankAtStalk (R := ℚ) (AdjoinRoot q) = Fintype.card (Fin 2),
      let P := TauCeti.Algebra.FrameAlgebra ℚ (AdjoinRoot q) (Fin 2)
      TauCeti.Algebra.IsFiniteEtaleTorsor (Equiv.Perm (Fin 2)) ℚ P ∧
      TauCeti.Algebra.IsTotallySplit P (P ⊗[ℚ] AdjoinRoot q) ∧
      let r₀ : P :=
        TauCeti.Algebra.FrameAlgebra.singleAlgHom ℚ (AdjoinRoot q) (0 : Fin 2) (AdjoinRoot.root q)
      let r₁ : P :=
        TauCeti.Algebra.FrameAlgebra.singleAlgHom ℚ (AdjoinRoot q) (1 : Fin 2) (AdjoinRoot.root q)
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
  refine ⟨fun hsplit ↦ ?_, hrank, TauCeti.Algebra.FrameAlgebra.isFiniteEtaleTorsor hrank,
    TauCeti.Algebra.FrameAlgebra.isTotallySplit_tensorProduct hrank, ?_⟩
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
    have hhom : TauCeti.Algebra.FrameAlgebra.singleAlgHom ℚ (AdjoinRoot q) (0 : Fin 2) =
        TauCeti.Algebra.FrameAlgebra.singleAlgHom ℚ (AdjoinRoot q) (1 : Fin 2) :=
      AdjoinRoot.algHom_ext heq
    exact absurd (TauCeti.Algebra.FrameAlgebra.singleAlgHom_injective_of_etale hrank hhom)
      (by decide)

end QuadraticCover

section PermSplitting

/-- *test_nonconstant_rank_perm_splitting*: over `ℚ × ℚ`, the clopen factor `(ℚ × ℚ) ⧸ (1 - (1, 0))`
has non-constant stalk rank, yet `exists_perm_isFiniteEtaleTorsor_isTotallySplit` produces a
symmetric-group torsor over `ℚ × ℚ` splitting it. -/
example :
    let A := ℚ × ℚ
    let e : A := (1, 0)
    have he : IsIdempotentElem e := Prod.ext (mul_one 1) (mul_zero 0)
    let S := A ⧸ Ideal.span {1 - e}
    letI : Algebra.Etale A S := Etale.quotient_span_singleton he.one_sub
    (¬ ∃ d : ℕ, Module.rankAtStalk (R := A) S = d) ∧
    ∃ (n : ℕ) (P : Type) (_ : CommRing P) (_ : Algebra A P)
      (_ : MulSemiringAction (Equiv.Perm (Fin n)) P)
      (_ : SMulCommClass (Equiv.Perm (Fin n)) A P),
      TauCeti.Algebra.IsFiniteEtaleTorsor (Equiv.Perm (Fin n)) A P ∧
        TauCeti.Algebra.IsTotallySplit P (P ⊗[A] S) := by
  let A := ℚ × ℚ
  let e : A := (1, 0)
  have he : IsIdempotentElem e := Prod.ext (mul_one 1) (mul_zero 0)
  let S := A ⧸ Ideal.span {1 - e}
  have : Algebra.Etale A S := Etale.quotient_span_singleton he.one_sub
  refine ⟨?_, TauCeti.Algebra.exists_perm_isFiniteEtaleTorsor_isTotallySplit A S⟩
  rintro ⟨d, hd⟩
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

/-- *test_preconnected_perm_finite_split*: over an integral domain `A`,
`exists_perm_isFiniteEtaleTorsor_isFiniteSplit_of_preconnectedSpace` upgrades the conclusion to
constant-rank splitting `Algebra.IsFiniteSplit` under `Equiv.Perm (Fin n)`. -/
example (A : Type u) [CommRing A] [IsDomain A] (S : Type*) [CommRing S] [Algebra A S]
    [Algebra.Etale A S] [Module.Finite A S] :
    ∃ (n : ℕ) (P : Type u) (_ : CommRing P) (_ : Algebra A P)
      (_ : MulSemiringAction (Equiv.Perm (Fin n)) P)
      (_ : SMulCommClass (Equiv.Perm (Fin n)) A P),
      TauCeti.Algebra.IsFiniteEtaleTorsor (Equiv.Perm (Fin n)) A P ∧
        Algebra.IsFiniteSplit P (P ⊗[A] S) :=
  TauCeti.Algebra.exists_perm_isFiniteEtaleTorsor_isFiniteSplit_of_preconnectedSpace A S

end PermSplitting

end TauCeti.Examples.TorsorFrame
