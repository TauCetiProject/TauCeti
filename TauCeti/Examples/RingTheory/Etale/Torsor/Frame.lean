/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import TauCeti.RingTheory.Etale.Idempotent
import TauCeti.RingTheory.Etale.Torsor.Frame
import TauCeti.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Tests for frame algebras as splitting torsors

For a finite separable field extension `L / K` of degree `n`, the frame algebra
`FrameAlgebra K L (Fin n)` is a `Perm (Fin n)`-torsor over `K` of dimension `n!` on which
`Perm (Fin n)` acts as a Galois group, and `L` splits into `n` copies of it after base change.
Asking for more distinct points than the rank produces the zero ring, and asking for a positive
number of slots fewer than the rank produces an algebra whose dimension exceeds `|Perm ι|`; neither
is a `Perm ι`-torsor over a field.
Over a disconnected base `K × K`, a finite étale algebra of non-constant rank `(1, 0)` is split in
the sense of `IsTotallySplit` by a finite étale torsor, while `Algebra.IsFiniteSplit` fails after
every faithfully flat base change. Over the zero ring every finite étale algebra is split by a
torsor as well.
-/

open scoped TensorProduct

universe u

namespace TauCeti.Algebra

attribute [local instance] Algebra.FormallyUnramified.of_isSeparable in
/-- *test_separable_field_extension*: for a finite separable field extension `L / K` of degree
`n = Module.finrank K L`, its frame algebra `P = FrameAlgebra K L (Fin n)` is a finite étale
`Perm (Fin n)`-torsor over `K` on which `Perm (Fin n)` acts as a Galois group, of `K`-dimension
`n!`, and `P ⊗[K] L` splits into `n` copies of `P`. -/
example (K : Type u) (L : Type*) [Field K] [Field L] [Algebra K L] [Module.Finite K L]
    [Algebra.IsSeparable K L] :
    let n := Module.finrank K L
    let P := FrameAlgebra K L (Fin n)
    IsFiniteEtaleTorsor (Equiv.Perm (Fin n)) K P ∧
      IsGaloisGroup (Equiv.Perm (Fin n)) K P ∧
      Module.finrank K P = n.factorial ∧
      Nonempty (P ⊗[K] L ≃ₐ[P] (Fin n → P)) := by
  intro n P
  have : Algebra.FormallyEtale K L := .of_isSeparable K L
  have : Algebra.Etale K L :=
    ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  have hrank : Module.rankAtStalk (R := K) L = Fintype.card (Fin n) := by
    rw [Module.rankAtStalk_eq_finrank_of_free (R := K), Fintype.card_fin]
  have : IsFiniteEtaleTorsor (Equiv.Perm (Fin n)) K P :=
    FrameAlgebra.isFiniteEtaleTorsor hrank
  have hcard : Module.rankAtStalk (R := K) P = n.factorial := funext fun p ↦ by
    rw [IsFiniteEtaleTorsor.rankAtStalk_eq_card (G := Equiv.Perm (Fin n))]
    simp [Fintype.card_perm]
  exact ⟨inferInstance, inferInstance, TauCeti.Module.finrank_eq_of_rankAtStalk_eq hcard,
    ⟨FrameAlgebra.tensorProductEquivPi hrank⟩⟩

/-- *test_overcounting_frame_is_zero*: over a field `K`, asking for `2` distinct points of the
rank-`1` algebra `Fin 1 → K` yields the zero ring, which is not a `Perm (Fin 2)`-torsor. -/
example (K : Type*) [Field K] :
    Subsingleton (FrameAlgebra K (Fin 1 → K) (Fin 2)) ∧
      ¬ IsFiniteEtaleTorsor (Equiv.Perm (Fin 2)) K (FrameAlgebra K (Fin 1 → K) (Fin 2)) := by
  have : IsEmpty (Fin 2 ↪ Fin 1) :=
    ⟨fun f ↦ by have := Fintype.card_le_of_injective f f.injective; simp at this⟩
  have : Subsingleton (FrameAlgebra K (Fin 1 → K) (Fin 2)) :=
    (FrameAlgebra.piEquiv K (Fin 2) (Fin 1)).toEquiv.subsingleton
  refine ⟨inferInstance, fun h ↦ ?_⟩
  obtain ⟨hnt, -⟩ := (IsFiniteEtaleTorsor.iff_field K).mp h
  exact not_nontrivial _ hnt

/-- *test_undercounting_frame_not_torsor*: over a field `K`, the frame of `1`-tuples in the
rank-`2` split algebra `Fin 2 → K` has dimension `2`, so it is not a `Perm (Fin 1)`-torsor. -/
example (K : Type*) [Field K] :
    ¬ IsFiniteEtaleTorsor (Equiv.Perm (Fin 1)) K (FrameAlgebra K (Fin 2 → K) (Fin 1)) := by
  classical
  intro h
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum K) := inferInstance
  have hcard := IsFiniteEtaleTorsor.rankAtStalk_eq_card (G := Equiv.Perm (Fin 1))
    (A := K) (B := FrameAlgebra K (Fin 2 → K) (Fin 1)) p
  have heq := congrFun (Module.rankAtStalk_eq_of_equiv
    (FrameAlgebra.piEquiv K (Fin 1) (Fin 2)).toLinearEquiv) p
  rw [heq, Module.rankAtStalk_eq_finrank_of_free (R := K)] at hcard
  simp at hcard
  let e₀ : Fin 1 ↪ Fin 2 := ⟨fun _ ↦ 0, Function.injective_of_subsingleton _⟩
  let e₁ : Fin 1 ↪ Fin 2 := ⟨fun _ ↦ 1, Function.injective_of_subsingleton _⟩
  have : Nontrivial (Fin 1 ↪ Fin 2) :=
    ⟨e₀, e₁, fun h01 ↦ Fin.zero_ne_one (DFunLike.congr_fun h01 0)⟩
  have : 1 < Fintype.card (Fin 1 ↪ Fin 2) := Fintype.one_lt_card
  omega

/-- *test_nonconstant_rank_split_by_torsor*: over `K × K`, the quotient `S` by `1 - (1, 0)` is
finite étale of rank `1` on one factor and `0` on the other; it becomes `IsTotallySplit` over a
finite étale torsor `P`, whereas `Algebra.IsFiniteSplit P (P ⊗[K × K] S)` fails. -/
example (K : Type u) [Field K] :
    let e : K × K := (1, 0)
    let S := (K × K) ⧸ Ideal.span {1 - e}
    ∃ (G : Type u) (_ : Group G) (_ : Finite G) (P : Type u) (_ : CommRing P)
      (_ : Algebra (K × K) P) (_ : MulSemiringAction G P) (_ : SMulCommClass G (K × K) P),
      IsFiniteEtaleTorsor G (K × K) P ∧
        IsTotallySplit P (P ⊗[K × K] S) ∧
        ¬ Algebra.IsFiniteSplit P (P ⊗[K × K] S) := by
  intro e S
  have he : IsIdempotentElem e := by ext <;> simp [e]
  have : Algebra.Etale (K × K) S := Etale.quotient_span_singleton he.one_sub
  obtain ⟨G, _, _, P, _, _, _, _, hP, hsplit⟩ :=
    exists_isFiniteEtaleTorsor_isTotallySplit (K × K) S
  refine ⟨G, _, _, P, _, _, _, _, hP, hsplit, fun hfs ↦ ?_⟩
  have := hP.faithfullyFlat
  let p₁ : PrimeSpectrum (K × K) := (⊥ : PrimeSpectrum K).comap (RingHom.fst K K)
  let p₂ : PrimeSpectrum (K × K) := (⊥ : PrimeSpectrum K).comap (RingHom.snd K K)
  obtain ⟨q₁, hq₁⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := K × K) (B := P) p₁
  obtain ⟨q₂, hq₂⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := K × K) (B := P) p₂
  have : Nontrivial P := PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨q₁⟩
  obtain ⟨m, ⟨φ⟩⟩ := hfs.nonempty_algEquiv_fun
  let ψ : P ⊗[K × K] S ≃ₗ[P] (Fin m → P) := φ.toLinearEquiv
  have hm (q : PrimeSpectrum P) : Module.rankAtStalk (R := P) (P ⊗[K × K] S) q = m := by
    rw [congrFun (Module.rankAtStalk_eq_of_equiv ψ) q,
      Module.rankAtStalk_eq_finrank_of_free (R := P)]
    simp
  have h1 : Module.rankAtStalk (R := P) (P ⊗[K × K] S) q₁ = 1 := by
    rw [Module.rankAtStalk_baseChange, hq₁, Module.rankAtStalk_quotient_span_one_sub he]
    simp [p₁, e]
  have h2 : Module.rankAtStalk (R := P) (P ⊗[K × K] S) q₂ = 0 := by
    rw [Module.rankAtStalk_baseChange, hq₂, Module.rankAtStalk_quotient_span_one_sub he]
    simp [p₂, e]
  have hm1 := hm q₁
  have hm2 := hm q₂
  omega

/-- *test_zero_ring*: over a subsingleton base ring, every finite étale algebra is split by a
finite étale torsor. -/
example (A : Type u) (S : Type*) [CommRing A] [Subsingleton A] [CommRing S] [Algebra A S]
    [Algebra.Etale A S] [Module.Finite A S] :
    ∃ (G : Type u) (_ : Group G) (_ : Finite G) (P : Type u) (_ : CommRing P)
      (_ : Algebra A P) (_ : MulSemiringAction G P) (_ : SMulCommClass G A P),
      IsFiniteEtaleTorsor G A P ∧ IsTotallySplit P (P ⊗[A] S) :=
  exists_isFiniteEtaleTorsor_isTotallySplit A S

end TauCeti.Algebra
