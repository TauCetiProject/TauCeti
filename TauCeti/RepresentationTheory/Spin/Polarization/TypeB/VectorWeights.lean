/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.VectorWeights
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeB.CartanWeights

/-!
# The type-B spin module is not built from the standard module

The weights of the type-`B` spin module are the half-integral sign vectors `½(±ε₁ ± ⋯ ± εₗ)`.
In characteristic zero and positive rank none of them lies in the lattice of vector weights
`TauCeti.typeBVectorWeightLattice`, the integer combinations of the `εᵢ`. A Lie module map sends
each weight vector to a weight vector of the same weight, and the spin module has a basis of weight
vectors, so **the spin module has no nonzero map to any module whose weights are vector weights**.

The modules whose weights are vector weights include the standard module and are closed under
tensor products and under passing to Lie submodules
(`LieModule.Weight.exists_mem_typeBVectorWeightLattice_standard`,
`TauCeti.exists_mem_weight_tensorProduct` and `LieModuleHom.exists_mem_weight_of_injective`). So
the spin module embeds in no tensor power of the standard module and in no module embedding in one,
such as its exterior powers in characteristic zero. This is the classical reason the spin
representations are not found among the tensor constructions on the vector representation of
`so(2l + 1)`.

## Main results

* `TauCeti.typeBWeightEquiv_spinWeight_notMem_typeBVectorWeightLattice`: in characteristic zero
  and positive rank, no spin weight is a vector weight.
* `TauCeti.SpinPolarizationData.typeBSpinLieRep_lieModuleHom_eq_zero`: the spin module has no
  nonzero Lie module map to a module whose weights are vector weights.
* `TauCeti.SpinPolarizationData.isEmpty_lieModuleEquiv_typeBSpinLieRep`: in particular it is
  equivalent to no such module.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §20.1: the spin
  representations do not occur in the tensor powers of the standard representation.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate II.
-/

public section

open LieModule Module

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v w t

/-- **No spin weight is a vector weight**, in characteristic zero and positive rank: each
coordinate `±½` of a half-integral sign vector fails to be an integer. -/
@[simp]
theorem typeBWeightEquiv_spinWeight_notMem_typeBVectorWeightLattice {K : Type u} [Field K]
    [CharZero K] [Invertible (2 : K)] {ι : Type v} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (s : Finset ι) :
    typeBWeightEquiv (K := K) (ι := ι) (spinWeight K s) ∉ typeBVectorWeightLattice K ι := by
  rw [mem_typeBVectorWeightLattice_iff]
  rintro ⟨m, hm⟩
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hi : ((m i + m i : ℤ) : K) = spinWeight K s i + spinWeight K s i := by
    rw [Int.cast_add, ← congrFun (typeBWeightEquiv.injective hm) i]
  by_cases his : i ∈ s
  · rw [spinWeight_add_self_of_mem his] at hi
    have : m i + m i = 1 := by exact_mod_cast hi
    omega
  · rw [spinWeight_add_self_of_notMem his] at hi
    have : m i + m i = -1 := by exact_mod_cast hi
    omega

namespace SpinPolarizationData

variable {K : Type u} [Field K] [CharZero K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  {ι : Type w} [Fintype ι] [LinearOrder ι] [Nonempty ι] (b : Module.Basis ι K P.W)
  (z : P.line) (hz : Q (z : V) = 1) [Invertible (2 : K)]
  {M : Type t} [AddCommGroup M] [Module K M]
  [LieRingModule (LieAlgebra.Orthogonal.typeB ι K) M]
  [LieModule K (LieAlgebra.Orthogonal.typeB ι K) M]

/-- **The type-`B` spin module has no nonzero map to a module whose weights are vector weights**,
in characteristic zero and positive rank. Such modules include the tensor powers of the standard
module and the modules embedding in them. -/
theorem typeBSpinLieRep_lieModuleHom_eq_zero
    (hM : ∀ χ : Weight K (typeBDiagonalCartan K ι) M,
      ∃ φ ∈ typeBVectorWeightLattice K ι, ⇑φ = ⇑χ) :
    letI : LieRingModule (LieAlgebra.Orthogonal.typeB ι K) (ExteriorAlgebra K P.W) :=
      LieRingModule.compLieHom _ (P.typeBSpinLieRep b z hz)
    letI : LieModule K (LieAlgebra.Orthogonal.typeB ι K) (ExteriorAlgebra K P.W) :=
      LieModule.compLieHom _ (P.typeBSpinLieRep b z hz)
    ∀ f : ExteriorAlgebra K P.W →ₗ⁅K,LieAlgebra.Orthogonal.typeB ι K⁆ M, f = 0 := by
  let _ : LieRingModule (LieAlgebra.Orthogonal.typeB ι K) (ExteriorAlgebra K P.W) :=
    LieRingModule.compLieHom _ (P.typeBSpinLieRep b z hz)
  let _ : LieModule K (LieAlgebra.Orthogonal.typeB ι K) (ExteriorAlgebra K P.W) :=
    LieModule.compLieHom _ (P.typeBSpinLieRep b z hz)
  intro f
  have hbasis (s : Finset ι) : f (b.ExteriorAlgebra s) = 0 := by
    let χ : typeBDiagonalCartan K ι → K := typeBWeightEquiv (spinWeight K s)
    have hmem : b.ExteriorAlgebra s ∈ genWeightSpace (ExteriorAlgebra K P.W) χ := by
      rw [← LieSubmodule.mem_toSubmodule, P.genWeightSpace_typeBSpinLieRep_spinWeight b z hz]
      exact Submodule.mem_span_singleton_self _
    have hf : f (b.ExteriorAlgebra s) ∈ genWeightSpace M χ :=
      map_genWeightSpace_le (f.restrictLie (typeBDiagonalCartan K ι))
        (LieSubmodule.mem_map_of_mem hmem)
    by_contra hne
    obtain ⟨φ, hφ, hφχ⟩ := hM ⟨χ, fun h ↦ hne (by rwa [h, LieSubmodule.mem_bot] at hf)⟩
    rw [DFunLike.coe_injective hφχ] at hφ
    exact typeBWeightEquiv_spinWeight_notMem_typeBVectorWeightLattice s hφ
  ext x
  exact LinearMap.congr_fun (b.ExteriorAlgebra.ext (f₁ := (f : ExteriorAlgebra K P.W →ₗ[K] M))
    (f₂ := 0) hbasis) x

/-- **The type-`B` spin module is equivalent to no module whose weights are vector weights**, in
characteristic zero and positive rank; in particular to no tensor power of the standard module. -/
theorem isEmpty_lieModuleEquiv_typeBSpinLieRep
    (hM : ∀ χ : Weight K (typeBDiagonalCartan K ι) M,
      ∃ φ ∈ typeBVectorWeightLattice K ι, ⇑φ = ⇑χ) :
    letI : LieRingModule (LieAlgebra.Orthogonal.typeB ι K) (ExteriorAlgebra K P.W) :=
      LieRingModule.compLieHom _ (P.typeBSpinLieRep b z hz)
    letI : LieModule K (LieAlgebra.Orthogonal.typeB ι K) (ExteriorAlgebra K P.W) :=
      LieModule.compLieHom _ (P.typeBSpinLieRep b z hz)
    IsEmpty (ExteriorAlgebra K P.W ≃ₗ⁅K,LieAlgebra.Orthogonal.typeB ι K⁆ M) := by
  let _ : LieRingModule (LieAlgebra.Orthogonal.typeB ι K) (ExteriorAlgebra K P.W) :=
    LieRingModule.compLieHom _ (P.typeBSpinLieRep b z hz)
  let _ : LieModule K (LieAlgebra.Orthogonal.typeB ι K) (ExteriorAlgebra K P.W) :=
    LieModule.compLieHom _ (P.typeBSpinLieRep b z hz)
  refine ⟨fun e ↦ one_ne_zero (α := ExteriorAlgebra K P.W) (e.injective ?_)⟩
  rw [map_zero]
  exact LieModuleHom.congr_fun (P.typeBSpinLieRep_lieModuleHom_eq_zero b z hz hM e.toLieModuleHom) 1

end SpinPolarizationData

end TauCeti
