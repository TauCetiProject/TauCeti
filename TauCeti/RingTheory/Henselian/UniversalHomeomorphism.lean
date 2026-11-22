/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian
public import TauCeti.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import TauCeti.AlgebraicGeometry.Morphisms.Thickening
import TauCeti.RingTheory.Henselian.Integral
import TauCeti.RingTheory.Ideal.Quotient.Defs
import TauCeti.RingTheory.Spectrum.Prime.Idempotent

/-!
# Henselian pairs and universal homeomorphisms

Let `B → R` be a ring map such that `Spec R → Spec B` is a universal homeomorphism, and let `I` be
an ideal of `B`. Then `(B, I)` is a henselian pair if and only if `(R, IR)` is
(`Ideal.henselianRing_map_iff_of_isUniversalHomeomorphism`). No finiteness hypothesis on `B → R`
is needed. For instance, `(B, I)` is henselian if and only if `(B ⧸ N, I (B ⧸ N))` is, for every
nil ideal `N` (`Ideal.henselianRing_map_quotient_iff_of_le_nilradical`).

One direction holds for every integral ring map (`Ideal.henselianRing_map_of_isIntegral`). For the
other, henselian pairs are characterised by lifting idempotents in finite algebras
(`TauCeti.henselianRing_of_forall_exists_isIdempotentElem_adjoinRoot`). Idempotents correspond to
clopen subsets of the prime spectrum, and for every `B`-algebra `C` the map
`Spec (R ⊗[B] C) → Spec C` is a homeomorphism. Hence `C → R ⊗[B] C` is a bijection on
idempotents, both for `C` and for `C ⧸ IC`, and an idempotent lifting over `R` descends to `C`.

## References

* [Stacks Project, Lemma 15.11.8](https://stacks.math.columbia.edu/tag/09XK), henselian pairs and
  integral maps inducing homeomorphisms on spectra.
* [Stacks Project, Lemma 15.11.6](https://stacks.math.columbia.edu/tag/09XI), characterisation of
  henselian pairs by idempotents of finite algebras.
* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, proof of Lemma 7.2.3(3).
* O. Gabber, L. Ramero, *Almost ring theory*, Remark 5.1.9(i).
-/

public section

universe u

open AlgebraicGeometry TauCeti.AlgebraicGeometry
open scoped TensorProduct

namespace Ideal

variable {B R : Type u} [CommRing B] [CommRing R] [Algebra B R]

/-- **Henselian pairs are invariant under universal homeomorphisms.** If `Spec R → Spec B` is a
universal homeomorphism, then `(R, IR)` is a henselian pair if and only if `(B, I)` is. -/
@[stacks 09XK]
theorem henselianRing_map_iff_of_isUniversalHomeomorphism
    [IsUniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap B R)))] (I : Ideal B) :
    HenselianRing R (I.map (algebraMap B R)) ↔ HenselianRing B I := by
  obtain ⟨hint, -, hsurj⟩ := (IsUniversalHomeomorphism.SpecMap_iff _).mp ‹_›
  have : Algebra.IsIntegral B R := algebraMap_isIntegral_iff.mp hint
  refine ⟨fun hR ↦ ?_, fun _ ↦ inferInstance⟩
  refine TauCeti.henselianRing_of_forall_exists_isIdempotentElem_adjoinRoot ?_ fun f hf s hs ↦ ?_
  · -- Every maximal ideal of `B` is the contraction of a maximal ideal of `R`.
    rw [← jacobson_bot]
    refine le_sInf fun m ⟨_, hm⟩ ↦ ?_
    obtain ⟨q, hq⟩ := hsurj ⟨m, hm.isPrime⟩
    have hqm : q.asIdeal.comap (algebraMap B R) = m := congrArg PrimeSpectrum.asIdeal hq
    have : q.asIdeal.IsMaximal :=
      isMaximal_of_isIntegral_of_isMaximal_comap _ hint _ (hqm ▸ hm)
    rw [← hqm, ← map_le_iff_le_comap]
    exact hR.jac.trans (Ring.jacobson_le_of_isMaximal _)
  · -- Lift `s` to an idempotent of the finite `R`-algebra `R ⊗[B] C`, and descend it to `C`.
    let C := AdjoinRoot f
    have : Module.Finite B C := hf.finite_adjoinRoot
    let K := I.map (algebraMap B C)
    let ψ : C →+* R ⊗[B] C := (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C).toRingHom
    have hK : (I.map (algebraMap B R)).map (algebraMap R (R ⊗[B] C)) = K.map ψ := by
      rw [map_map, map_map, ← IsScalarTower.algebraMap_eq]
      exact congrArg (I.map ·) (Algebra.TensorProduct.includeRight.comp_algebraMap).symm
    have hψs : ψ s * ψ s - ψ s ∈ (I.map (algebraMap B R)).map (algebraMap R (R ⊗[B] C)) := by
      rw [hK, ← map_mul, ← map_sub]
      exact mem_map_of_mem _ hs
    obtain ⟨t, ht, hts⟩ := exists_isIdempotentElem_sub_mem_map_of_isIntegral _ hψs
    obtain ⟨e, he, rfl⟩ := ψ.surjOn_isIdempotentElem_of_isHomeomorph_comap
      (IsUniversalHomeomorphism.isHomeomorph_comap_includeRight C) ht
    refine ⟨e, he, Quotient.eq.mp ?_⟩
    -- Compare `e` and `s` modulo `K` after base change to `R ⊗[B] (C ⧸ K)`.
    let ψ' : C ⧸ K →+* R ⊗[B] (C ⧸ K) :=
      (Algebra.TensorProduct.includeRight : C ⧸ K →ₐ[B] R ⊗[B] (C ⧸ K)).toRingHom
    let π := Algebra.TensorProduct.map (AlgHom.id B R) (Quotient.mkₐ B K)
    have hπ (c : C) : π (ψ c) = ψ' (Quotient.mk K c) := by
      simp [π, ψ, ψ']
    have hπK : K.map ψ ≤ RingHom.ker π := map_le_iff_le_comap.mpr fun k hk ↦ by
      simp [hπ, Quotient.eq_zero_iff_mem.mpr hk]
    refine ψ'.injOn_isIdempotentElem_of_surjective_comap
      (IsUniversalHomeomorphism.isHomeomorph_comap_includeRight (C ⧸ K)).surjective
      (he.map (Quotient.mk K)) (Quotient.isIdempotentElem_mk_iff.mpr hs) ?_
    have := hπK (hK ▸ hts)
    rwa [RingHom.mem_ker, map_sub, hπ, hπ, sub_eq_zero] at this

/-- **Henselian pairs and nil ideals.** For a nil ideal `N` of `B`, the pair `(B, I)` is
henselian if and only if `(B ⧸ N, I (B ⧸ N))` is. -/
theorem henselianRing_map_quotient_iff_of_le_nilradical {N : Ideal B} (hN : N ≤ nilradical B)
    (I : Ideal B) : HenselianRing (B ⧸ N) (I.map (Quotient.mk N)) ↔ HenselianRing B I := by
  have : IsThickening (Spec.map (CommRingCat.ofHom (algebraMap B (B ⧸ N)))) :=
    (IsThickening.SpecMap_iff _ Quotient.mk_surjective).mpr (by simpa using hN)
  exact henselianRing_map_iff_of_isUniversalHomeomorphism I

end Ideal
