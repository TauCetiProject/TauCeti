/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.Tactic.ComputeDegree
import TauCeti.RingTheory.Etale.Torsor.Frame
import TauCeti.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Tests for splitting finite étale algebras by frame torsors

This file exercises the frame-torsor splitting API across representative examples and edge cases:

* the trivial `n`-sheeted cover `Fin n → A`, whose frame algebra is a `Perm (Fin n)`-torsor of
  constant stalk rank `n!` splitting the cover via `FrameAlgebra.universalFrameEquivPi`;
* the empty cover `Fin 0 → A` over a nontrivial base `A`, which has no section yet has frame
  algebra isomorphic to `A` (rank `0! = 1`), splitting `Fin 0 → A`;
* the non-Galois cubic extension `ℚ[X] ⧸ (X ^ 3 - 2)` over `ℚ`, whose `Fin 3`-frame algebra is an
  `S_3`-torsor of rank `6` over which the cubic splits into three copies of the torsor;
* the Artin–Schreier quadratic extension `𝔽₂[X] ⧸ (X ^ 2 + X + 1)` in characteristic `2`, where
  averaging over the group is unavailable;
* a clopen cover `(K₁ × K₂) ⧸ (1 - (1, 0))` of nonconstant rank (`1` over `K₁`, `0` over `K₂`),
  which becomes `IsTotallySplit` over a finite étale torsor by
  `exists_isFiniteEtaleTorsor_isTotallySplit` while never becoming `Algebra.IsFiniteSplit` over any
  faithfully flat extension;
* universe polymorphism in `S`, placing both `G` and `P` in the universe of the base ring `A`.
-/

open Polynomial
open scoped _root_.TensorProduct

universe u

namespace TauCeti.Algebra

/-- *test_split_cover*: for the split cover `Fin n → A`, the frame algebra is a
`Perm (Fin n)`-torsor of stalk rank `n!` at every prime, and the universal frame splits it into `n`
copies of the frame algebra. -/
example (A : Type*) [CommRing A] (n : ℕ) (p : PrimeSpectrum A) :
    let P := FrameAlgebra A (Fin n → A) (Fin n)
    IsFiniteEtaleTorsor (Equiv.Perm (Fin n)) A P ∧
      Module.rankAtStalk (R := A) P p = n.factorial ∧
      Nonempty (P ⊗[A] (Fin n → A) ≃ₐ[P] (Fin n → P)) := by
  intro P
  have htor : IsFiniteEtaleTorsor (Equiv.Perm (Fin n)) A P :=
    FrameAlgebra.isFiniteEtaleTorsor_of_algEquiv_pi A
      (Algebra.TensorProduct.piScalarRight A A A (Fin n))
  refine ⟨htor, ?_, ⟨FrameAlgebra.universalFrameEquivPi A (Fin n)⟩⟩
  rw [IsFiniteEtaleTorsor.rankAtStalk_eq_card (G := Equiv.Perm (Fin n)), Nat.card_eq_fintype_card,
    Fintype.card_perm, Fintype.card_fin]

/-- *test_zero_cover_over_nontrivial*: over a nonzero ring `A`, the zero cover `Fin 0 → A` is not
faithfully flat (it has no `A`-algebra section), yet its `Fin 0`-frame algebra is a faithfully flat
`Perm (Fin 0)`-torsor of rank `1 = 0!` over `A` that splits `Fin 0 → A`. -/
example (A : Type) [CommRing A] [Nontrivial A] (p : PrimeSpectrum A) :
    let P := FrameAlgebra A (Fin 0 → A) (Fin 0)
    IsEmpty ((Fin 0 → A) →ₐ[A] A) ∧
      IsFiniteEtaleTorsor (Equiv.Perm (Fin 0)) A P ∧
      Module.rankAtStalk (R := A) P p = 1 ∧
      IsTotallySplit P (P ⊗[A] (Fin 0 → A)) := by
  intro P
  have hrank : Module.rankAtStalk (R := A) (Fin 0 → A) = Fintype.card (Fin 0) := by
    ext q
    simp [Module.rankAtStalk_fin_fun]
  have htor := FrameAlgebra.isFiniteEtaleTorsor hrank
  refine ⟨⟨fun σ ↦ one_ne_zero <|
    (map_one σ).symm.trans ((congrArg σ (Subsingleton.elim 1 0)).trans (map_zero σ))⟩,
    htor, ?_, FrameAlgebra.isTotallySplit_tensorProduct hrank⟩
  rw [IsFiniteEtaleTorsor.rankAtStalk_eq_card (G := Equiv.Perm (Fin 0)), Nat.card_eq_fintype_card,
    Fintype.card_perm, Fintype.card_fin, Nat.factorial_zero]

/-- *test_cubic_galois_closure*: for `S = ℚ[X] ⧸ (X ^ 3 - 2)`, `FrameAlgebra ℚ S (Fin 3)` is a
finite étale `S_3`-torsor of rank `6` over `ℚ` over which `S` splits into `3` copies of the
torsor. -/
example (p : PrimeSpectrum ℚ) :
    let f : ℚ[X] := X ^ 3 - C 2
    ∃ (_ : Algebra.Etale ℚ (AdjoinRoot f)) (_ : Module.Finite ℚ (AdjoinRoot f)),
      let P := FrameAlgebra ℚ (AdjoinRoot f) (Fin 3)
      IsFiniteEtaleTorsor (Equiv.Perm (Fin 3)) ℚ P ∧
        Module.rankAtStalk (R := ℚ) P p = 6 ∧
        Nonempty (P ⊗[ℚ] AdjoinRoot f ≃ₐ[P] (Fin 3 → P)) := by
  intro f
  have hf : f.Monic := monic_X_pow_sub_C 2 (by norm_num)
  have hs : f.Separable := separable_X_pow_sub_C 2 (by norm_num) (by norm_num)
  have : Algebra.Etale ℚ (AdjoinRoot f) := hf.etale_adjoinRoot_iff.mpr hs
  let pb := AdjoinRoot.powerBasis' hf
  have : Module.Finite ℚ (AdjoinRoot f) := pb.finite
  have : Module.Free ℚ (AdjoinRoot f) := .of_basis pb.basis
  have hrank : Module.rankAtStalk (R := ℚ) (AdjoinRoot f) = Fintype.card (Fin 3) := by
    ext q
    rw [Module.rankAtStalk_eq_finrank_of_free, pb.finrank, AdjoinRoot.powerBasis'_dim,
      natDegree_X_pow_sub_C]
    rfl
  have htor := FrameAlgebra.isFiniteEtaleTorsor hrank
  refine ⟨inferInstance, inferInstance, htor, ?_, ⟨FrameAlgebra.universalFrameEquiv hrank⟩⟩
  rw [IsFiniteEtaleTorsor.rankAtStalk_eq_card (G := Equiv.Perm (Fin 3)), Nat.card_eq_fintype_card,
    Fintype.card_perm, Fintype.card_fin]
  rfl

/-- *test_artin_schreier_char_two*: in characteristic `2`, `𝔽₂[X] ⧸ (X ^ 2 + X + 1)` is finite
étale of rank `2` (its derivative is `1`), and its `Fin 2`-frame algebra is an `S_2`-torsor over
`𝔽₂` splitting it. -/
example :
    let f : (ZMod 2)[X] := X ^ 2 + X + 1
    ∃ (_ : Algebra.Etale (ZMod 2) (AdjoinRoot f)) (_ : Module.Finite (ZMod 2) (AdjoinRoot f)),
      let P := FrameAlgebra (ZMod 2) (AdjoinRoot f) (Fin 2)
      IsFiniteEtaleTorsor (Equiv.Perm (Fin 2)) (ZMod 2) P ∧
        Algebra.IsFiniteSplit P (P ⊗[ZMod 2] AdjoinRoot f) := by
  intro f
  have hdeg : f.natDegree = 2 := by unfold f; compute_degree!
  have hf : f.Monic := by rw [Monic.def, leadingCoeff, hdeg]; unfold f; compute_degree!
  have hderiv : derivative f = 1 := by
    simp only [f, derivative_add, derivative_X_pow, derivative_X, derivative_one,
      Nat.cast_ofNat, add_zero]
    rw [show (2 : ZMod 2) = 0 from rfl, map_zero, zero_mul, zero_add]
  have hs : f.Separable :=
    separable_iff_isUnit_mk_derivative.mpr (by rw [hderiv, map_one]; exact isUnit_one)
  have : Algebra.Etale (ZMod 2) (AdjoinRoot f) := hf.etale_adjoinRoot_iff.mpr hs
  let pb := AdjoinRoot.powerBasis' hf
  have : Module.Finite (ZMod 2) (AdjoinRoot f) := pb.finite
  have : Module.Free (ZMod 2) (AdjoinRoot f) := .of_basis pb.basis
  have hrank : Module.rankAtStalk (R := ZMod 2) (AdjoinRoot f) = Fintype.card (Fin 2) := by
    ext q
    simp [Module.rankAtStalk_eq_finrank_of_free, pb.finrank, pb, AdjoinRoot.powerBasis'_dim, hdeg]
  exact ⟨inferInstance, inferInstance, FrameAlgebra.isFiniteEtaleTorsor hrank,
    FrameAlgebra.isFiniteSplit_tensorProduct hrank⟩

/-- *test_varying_rank_not_isFiniteSplit*: over a product of two fields `K₁ × K₂`, the clopen cover
cut out by the idempotent `(1, 0)` has stalk rank `1` over `Spec K₁` and `0` over `Spec K₂`. It is
split into an `IsTotallySplit` algebra by a finite étale torsor
(`exists_isFiniteEtaleTorsor_isTotallySplit`), whereas over *any* faithfully flat `K₁ × K₂`-algebra
`T` its base change cannot satisfy `Algebra.IsFiniteSplit` because its stalk rank is nonconstant on
`Spec T`. -/
example (K₁ K₂ : Type) [Field K₁] [Field K₂] :
    let A := K₁ × K₂
    let e : A := (1, 0)
    let S := A ⧸ Ideal.span {1 - e}
    (∃ (G : Type) (_ : Group G) (_ : Finite G) (P : Type) (_ : CommRing P) (_ : Algebra A P)
      (_ : MulSemiringAction G P) (_ : SMulCommClass G A P),
      IsFiniteEtaleTorsor G A P ∧ IsTotallySplit P (P ⊗[A] S)) ∧
    ∀ (T : Type) [CommRing T] [Algebra A T] [Module.FaithfullyFlat A T],
      ¬ Algebra.IsFiniteSplit T (T ⊗[A] S) := by
  intro A e S
  have he : IsIdempotentElem e := by
    change ((1 : K₁), (0 : K₂)) * (1, 0) = (1, 0)
    rw [Prod.mk_mul_mk, mul_one, mul_zero]
  have : Algebra.Etale A S := Etale.quotient_span_singleton he.one_sub
  refine ⟨exists_isFiniteEtaleTorsor_isTotallySplit A S, ?_⟩
  rintro T _ _ _ ⟨m, ⟨φ⟩⟩
  have : Module.FinitePresentation A S := .of_finite_of_finitePresentation A S
  -- Pull back the two primes of `K₁ × K₂` along the surjective map `Spec T → Spec A`.
  let p₁ : PrimeSpectrum A := PrimeSpectrum.comap (RingHom.fst K₁ K₂) ⊥
  let p₂ : PrimeSpectrum A := PrimeSpectrum.comap (RingHom.snd K₁ K₂) ⊥
  obtain ⟨q₁, hq₁⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := T) p₁
  obtain ⟨q₂, hq₂⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := T) p₂
  let φlin : T ⊗[A] S ≃ₗ[T] (Fin m → T) := φ.toLinearEquiv
  have hm (q : PrimeSpectrum T) :
      Module.rankAtStalk (R := A) S (q.comap (algebraMap A T)) = m := by
    have h1 := Module.rankAtStalk_baseChange (R := A) (S := T) (M := S) q
    have h2 := congrFun (Module.rankAtStalk_eq_of_equiv φlin) q
    rw [Module.rankAtStalk_fin_fun] at h2
    exact h1.symm.trans h2
  have hp₁ : e ∉ p₁.asIdeal := fun h ↦ one_ne_zero (Ideal.mem_bot.mp h)
  have hp₂ : e ∈ p₂.asIdeal := Ideal.mem_bot.mpr rfl
  have hr₁ : Module.rankAtStalk (R := A) S p₁ = 1 := by
    simp [S, Module.rankAtStalk_quotient_span_one_sub he, hp₁]
  have hr₂ : Module.rankAtStalk (R := A) S p₂ = 0 := by
    simp [S, Module.rankAtStalk_quotient_span_one_sub he, hp₂]
  have : (1 : ℕ) = 0 := by
    calc 1 = Module.rankAtStalk (R := A) S p₁ := hr₁.symm
      _ = m := by rw [← hq₁, hm q₁]
      _ = Module.rankAtStalk (R := A) S p₂ := by rw [← hq₂, hm q₂]
      _ = 0 := hr₂
  omega

/-- *test_universe_polymorphism*: for `A : Type u` and `S` in a higher universe `Type (u + 1)`,
`exists_isFiniteEtaleTorsor_isTotallySplit` still produces both `G` and `P` in `Type u`. -/
example (A : Type u) (S : Type (u + 1)) [CommRing A] [CommRing S] [Algebra A S]
    [Algebra.Etale A S] [Module.Finite A S] :
    ∃ (G : Type u) (_ : Group G) (_ : Finite G) (P : Type u) (_ : CommRing P)
      (_ : Algebra A P) (_ : MulSemiringAction G P) (_ : SMulCommClass G A P),
      IsFiniteEtaleTorsor G A P ∧ IsTotallySplit P (P ⊗[A] S) :=
  exists_isFiniteEtaleTorsor_isTotallySplit A S

end TauCeti.Algebra
