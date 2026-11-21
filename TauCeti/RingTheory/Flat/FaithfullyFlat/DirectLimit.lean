/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import TauCeti.Algebra.Colimit.Ring.Ideal
public import TauCeti.RingTheory.RingHom.FaithfullyFlat

/-!
# Faithful flatness at a finite stage

Let `S` be a flat finitely presented algebra over `A`, and let `B` be a directed system of
`A`-algebras. If the base change of `S` to the colimit is faithfully flat, then its base change
to some stage above any prescribed stage is faithfully flat.

The proof follows the paragraph establishing eventual faithful flatness in the proof of
Stacks, Lemma 35.14.1 (02KK). The spectral image of `S` is open. Its closed complement is cut
out by an ideal whose extension to the colimit is the unit ideal. Membership of `1` in that
ideal descends to a finite stage.

## References

* [The Stacks Project, Lemma 35.14.1](https://stacks.math.columbia.edu/tag/02KK),
  the paragraph proving that the spread-out flat algebras are eventually faithfully flat.
-/

public section

open scoped TensorProduct

namespace TauCeti.DirectLimit.Algebra

/-- Faithful flatness of the base change of a flat finitely presented algebra to a directed
colimit already holds after base change to some stage above any prescribed stage. -/
@[stacks 02KK "eventual faithful flatness in the proof"]
theorem exists_faithfullyFlat_baseChange
    {A ι : Type*} [CommRing A] [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {B : ι → Type*} [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
    {f : ∀ i j, i ≤ j → B i →ₐ[A] B j} [DirectedSystem B (f · · ·)]
    (S : Type*) [CommRing S] [Algebra A S] [Module.Flat A S]
    [Algebra.FinitePresentation A S]
    [Module.FaithfullyFlat (DirectLimit B f) ((DirectLimit B f) ⊗[A] S)] (i : ι) :
    ∃ j, i ≤ j ∧ Module.FaithfullyFlat (B j) (B j ⊗[A] S) := by
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal
    (Set.range (PrimeSpectrum.comap (algebraMap A S)))ᶜ).mp
    (PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
      (R := A) (S := S)).isOpen_range.isClosed_compl
  have htop : I.map (algebraMap A (DirectLimit B f)) = ⊤ :=
    (Ideal.faithfullyFlat_baseChange_iff_map_eq_top I hI).mp inferInstance
  let J (j : ι) := I.map (algebraMap A (B j))
  have hJ (j k : ι) (hjk : j ≤ k) : J j ≤ (J k).comap (f j k hjk) := by
    rw [← Ideal.map_le_iff_le_comap, ← Ideal.map_coe, Ideal.map_map]
    exact le_of_eq (congrArg (I.map ·) (f j k hjk).comp_algebraMap)
  have hJA (j : ι) :
      (J j).map (DirectLimit.Ring.of B f j) = I.map (algebraMap A (DirectLimit B f)) := by
    rw [Ideal.map_map]
    congr 1
    ext a
    simp [DirectLimit.algebraMap_def j]
  obtain ⟨j, hij, hj⟩ := (TauCeti.DirectLimit.Ring.of_mem_iSup_map_of_iff hJ
    (i := i) (x := 1)).1 (by simp [hJA, htop])
  exact ⟨j, hij, (Ideal.faithfullyFlat_baseChange_iff_map_eq_top I hI).mpr
    (Ideal.eq_top_of_isUnit_mem _ (by simpa using hj) isUnit_one)⟩

end TauCeti.DirectLimit.Algebra
