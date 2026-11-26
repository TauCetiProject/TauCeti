/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.NuclearlyEmbeddable

/-!
# Checks for nuclearly embeddable C⋆-algebras

The complex numbers and the full matrix algebras `M_m(ℂ)` are nuclear, hence nuclearly
embeddable, and nuclear embeddability passes along the injective star homomorphism `ℂ → M_2(ℂ)`
onto the scalar matrices.
-/

public section

open scoped CStarAlgebra ComplexOrder

namespace TauCeti.CStarAlgebra

/-- `ℂ` is nuclearly embeddable. -/
example : IsNuclearlyEmbeddable ℂ := inferInstance

/-- The full matrix algebras `M_m(ℂ)` are nuclearly embeddable. -/
example (m : Type) [Fintype m] [DecidableEq m] :
    IsNuclearlyEmbeddable (CStarMatrix m m ℂ) :=
  inferInstance

/-- Nuclear embeddability passes to `ℂ` along the scalar embedding `ℂ → M_2(ℂ)`. -/
example : IsNuclearlyEmbeddable ℂ :=
  .of_injective (B := CStarMatrix (Fin 2) (Fin 2) ℂ)
    (StarAlgHom.ofId ℂ (CStarMatrix (Fin 2) (Fin 2) ℂ)).toNonUnitalStarAlgHom
    (algebraMap ℂ (CStarMatrix (Fin 2) (Fin 2) ℂ)).injective

end TauCeti.CStarAlgebra
