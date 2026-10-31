/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Unramified.Basic

/-!
# Descending formal unramifiedness in a tower

Let `R → S → T` be ring maps with `T` formally smooth and faithfully flat over `S`. If `T` is
formally unramified over `R`, then so is `S`
(`Algebra.FormallyUnramified.of_formallySmooth_of_faithfullyFlat`). Formal smoothness makes the
first fundamental sequence `T ⊗[S] Ω[S⁄R] → Ω[T⁄R]` injective, since its kernel is the image of
`H₁(L_{T/S}) = 0` (Mathlib's `Algebra.H1Cotangent.exact_δ_mapBaseChange`, Stacks 00S2), and
faithful flatness detects the vanishing of `Ω[S⁄R]` after base change to `T`.

This is the ring-theoretic input for formal unramifiedness being local on the source for the
smooth topology. It is the analogue for formal unramifiedness of
`Module.Flat.of_faithfullyFlat_of_flat`.
-/

public section

open TensorProduct

namespace Algebra.FormallyUnramified

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  [Algebra S T] [IsScalarTower R S T]

/-- If `T` is a formally smooth, faithfully flat `S`-algebra and `T` is formally unramified over
`R`, then `S` is formally unramified over `R`. -/
theorem of_formallySmooth_of_faithfullyFlat [FormallySmooth S T] [Module.FaithfullyFlat S T]
    [FormallyUnramified R T] : FormallyUnramified R S := by
  -- `T ⊗[S] Ω[S⁄R] → Ω[T⁄R]` is injective because `H₁(L_{T/S})` vanishes.
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange R S T) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := (H1Cotangent.exact_δ_mapBaseChange R S T x).mp hx
    rw [Subsingleton.elim x 0, map_zero]
  have : Subsingleton (T ⊗[S] Ω[S⁄R]) := hinj.subsingleton
  exact ⟨(Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right S T).mp this⟩

end Algebra.FormallyUnramified
