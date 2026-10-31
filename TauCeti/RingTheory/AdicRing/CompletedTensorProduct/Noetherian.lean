/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicRing.CompletedTensorProduct
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Basic

import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Adic

/-!
# Noetherianity of the completed tensor product over a strictly topologically finite type ring

Let `A` carry the `I`-adic topology for a finitely generated ideal `I`, and let `B` and `C` be
adic rings of finite ideal type which are `A`-algebras. If `B` is strictly topologically of finite
type over `A`, that is, an open quotient of some `A⟨X₁, …, Xₖ⟩`, and `C` is noetherian, then the
completed tensor product `B ⊗̂_A C` is noetherian. This reduces to
`TauCeti.AdicRing.CompletedTensorProduct.isNoetherianRing_of_finiteType`, since `B ⧸ I_B` is then
a finitely generated `A`-algebra.

## Main results

* `TauCeti.AdicRing.CompletedTensorProduct.isNoetherianRing`: `B ⊗̂_A C` is noetherian when `C`
  is noetherian and `B` is strictly topologically of finite type over `A` with an `I`-adic
  topology, `I` finitely generated.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. I, 10.13.5.
-/

public section

namespace TauCeti.AdicRing.CompletedTensorProduct

variable {A : Type*} (B C : Type*) [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B] [Algebra A B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsAdicRing C] [Algebra A C]

/-- **Noetherianity of the completed tensor product** (EGA I, Ch. I, 10.13.5). Let `A` carry the
`I`-adic topology for a finitely generated ideal `I`. If `B` is strictly topologically of finite
type over `A`, that is, an open quotient of some `A⟨X₁, …, Xₖ⟩`, and `C` is noetherian, then
`B ⊗̂_A C` is noetherian. Neither `A` nor `B` needs to be noetherian here. -/
theorem isNoetherianRing [IsNoetherianRing C] {I : Ideal A} (hI : IsAdic I) (hfg : I.FG)
    (hB : Huber.IsStrictlyTopologicallyFiniteType (algebraMap A B)) :
    IsNoetherianRing (CompletedTensorProduct A B C) := by
  -- `B` is `I·B`-adic, so the open ideal `I_B` contains `(I·B) ^ (n + 1) = I ^ (n + 1)·B`
  obtain ⟨n, -, hn⟩ := (hB.isAdic hI hfg).hasBasis_nhds_zero.mem_iff.mp
    ((IsAdicRing.ideal_spec B).2.1.hasBasis_nhds_zero.mem_of_mem (i := 1) trivial)
  have hle : (I ^ (n + 1)).map (algebraMap A B) ≤ IsAdicRing.ideal B := by
    rw [Ideal.map_pow]
    exact (Ideal.pow_le_pow_right n.le_succ).trans (by simpa using hn)
  -- the reduction of `B` modulo `I ^ (n + 1)` is of finite type, and `B ⧸ I_B` is a quotient of it
  have := hB.finiteType_quotient (is_ideal_adic_pow hI n.succ_pos) hfg.pow
  have : Algebra.FiniteType A (B ⧸ (I ^ (n + 1)).map (algebraMap A B)) :=
    .trans (S := A ⧸ I ^ (n + 1)) inferInstance inferInstance
  have : Algebra.FiniteType A (B ⧸ IsAdicRing.ideal B) :=
    .of_surjective (Ideal.Quotient.factorₐ A hle) (Ideal.Quotient.factor_surjective hle)
  exact isNoetherianRing_of_finiteType A B C

end TauCeti.AdicRing.CompletedTensorProduct
