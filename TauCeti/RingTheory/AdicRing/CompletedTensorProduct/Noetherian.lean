/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicRing.CompletedTensorProduct
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Basic

-- `B ⊗̂_A C` is by definition an adic completion; the proof of noetherianity unfolds this.
import all TauCeti.RingTheory.AdicRing.CompletedTensorProduct
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.TensorProduct.Quotient
import TauCeti.RingTheory.AdicCompletion.Noetherian
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Adic

/-!
# Noetherianity of the completed tensor product

Let `B` and `C` be adic rings of finite ideal type which are algebras over a commutative ring
`A`, with ideals of definition `I_B` and `I_C`, and let `J = I_B ⊗ 1 + 1 ⊗ I_C`. If `C` is
noetherian and `B ⧸ I_B` is a finitely generated `A`-algebra, then `(B ⊗[A] C) ⧸ J` is a quotient
of the finitely generated `C`-algebra `C ⊗[A] (B ⧸ I_B)`, hence noetherian, and so its `J`-adic
completion `B ⊗̂_A C` is noetherian.

Now let `A` carry the `I`-adic topology for a finitely generated ideal `I`, and let `B` and `C` be
adic rings of finite ideal type which are `A`-algebras. If `B` is strictly topologically of finite
type over `A`, that is, an open quotient of some `A⟨X₁, …, Xₖ⟩`, and `C` is noetherian, then the
completed tensor product `B ⊗̂_A C` is noetherian. This reduces to the previous statement, since
`B ⧸ I_B` is then a finitely generated `A`-algebra.

## Main results

* `TauCeti.AdicRing.CompletedTensorProduct.isNoetherianRing_quotient_tensorIdeal`: the quotient
  `(B ⊗[A] C) ⧸ J` is noetherian when `C` is noetherian and `B ⧸ I_B` is a finitely generated
  `A`-algebra.
* `TauCeti.AdicRing.CompletedTensorProduct.isNoetherianRing_of_finiteType`: `B ⊗̂_A C` is
  noetherian when `C` is noetherian and `B ⧸ I_B` is a finitely generated `A`-algebra.
* `TauCeti.AdicRing.CompletedTensorProduct.isNoetherianRing`: `B ⊗̂_A C` is noetherian when `C`
  is noetherian and `B` is strictly topologically of finite type over `A` with an `I`-adic
  topology, `I` finitely generated.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. I, 10.13.5.
-/

public section

namespace TauCeti.AdicRing.CompletedTensorProduct

open TensorProduct

variable (A B C : Type*) [CommRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B] [Algebra A B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsAdicRing C] [Algebra A C]

/-- The quotient of `B ⊗[A] C` by `I_B ⊗ 1 + 1 ⊗ I_C` is noetherian when `C` is noetherian and
`B ⧸ I_B` is a finitely generated `A`-algebra. -/
theorem isNoetherianRing_quotient_tensorIdeal [IsNoetherianRing C]
    [Algebra.FiniteType A (B ⧸ IsAdicRing.ideal B)] :
    IsNoetherianRing (B ⊗[A] C ⧸ tensorIdeal A B C) := by
  set I := IsAdicRing.ideal B
  -- `C ⊗[A] (B ⧸ I_B)` is a finitely generated `C`-algebra, hence noetherian
  have : IsNoetherianRing (C ⊗[A] (B ⧸ I)) := Algebra.FiniteType.isNoetherianRing C _
  -- and it is isomorphic to `(B ⊗[A] C) ⧸ I_B ⊗ 1`, which surjects onto the quotient by `J`
  let e : C ⊗[A] (B ⧸ I) ≃+* B ⊗[A] C ⧸ I.map (algebraMap B (B ⊗[A] C)) :=
    (Algebra.TensorProduct.comm A C (B ⧸ I)).toRingEquiv.trans
      (Algebra.TensorProduct.quotientTensorEquiv A C B I).toRingEquiv
  have hle : I.map (algebraMap B (B ⊗[A] C)) ≤ tensorIdeal A B C :=
    Ideal.map_le_iff_le_comap.mpr fun b hb ↦ by
      rw [Ideal.mem_comap, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply]
      exact tmul_one_mem_tensorIdeal hb
  exact isNoetherianRing_of_surjective _ _ ((Ideal.Quotient.factor hle).comp e.toRingHom)
    ((Ideal.Quotient.factor_surjective hle).comp e.surjective)

/-- **Noetherianity of the completed tensor product.** If `C` is noetherian and `B ⧸ I_B` is a
finitely generated `A`-algebra, then `B ⊗̂_A C` is noetherian. -/
theorem isNoetherianRing_of_finiteType [IsNoetherianRing C]
    [Algebra.FiniteType A (B ⧸ IsAdicRing.ideal B)] :
    IsNoetherianRing (CompletedTensorProduct A B C) :=
  have := isNoetherianRing_quotient_tensorIdeal A B C
  Ideal.isNoetherianRing_adicCompletion_of_fg _ (tensorIdeal_fg A B C)

variable {A} [TopologicalSpace A] [NonarchimedeanRing A]

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
