/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Symmetric.Standard
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Projection
import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Permutation.PrimePower

/-!
# Inducing the two-dimensional simple A₃-module over 𝔽₂

The restriction of the standard S₃-module `S` to A₃ is simple over 𝔽₂. Its induced
class is `2[S]` in the exact Grothendieck group. Thus both `2[k]` and `2[S]` are
induced from A₃, providing the two generators needed to compute the prime-to-two
induction subgroup once the simple S₃ classes have been classified.

The calculation uses the projection formula and the fact that the two-point quotient
permutation module has class `2[k]`. It concerns composition factors, without asserting
a direct-sum decomposition of the induced representation.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part III, §14.
-/

public section

open scoped MonoidAlgebra

namespace TauCeti

/-- In characteristic two, inducing the restriction of the standard S₃-module to A₃
gives twice its class. Over 𝔽₂ the source is simple, by
`isIrreducible_standardRepresentation_comp_alternatingGroup_zmod_two`. -/
-- Simplify this concrete class before `indK0_of` expands induction to coextension of scalars.
@[simp high]
theorem indK0_standardRepresentation_comp_alternatingGroup (k : Type) [Field k] [CharP k 2] :
    let ρ := standardRepresentation k (Fin 3)
    let σ : Representation k (alternatingGroup (Fin 3)) _ :=
      ρ.comp (alternatingGroup (Fin 3)).subtype
    letI : Module.Finite k[Equiv.Perm (Fin 3)] ρ.asModule :=
      Module.Finite.of_restrictScalars_finite k _ _
    letI : Module.Finite k[alternatingGroup (Fin 3)] σ.asModule :=
      Module.Finite.of_restrictScalars_finite k _ _
    indK0 k (alternatingGroup (Fin 3))
      (ExactK0.of (FGModuleCat.of _ σ.asModule)) =
        2 • (ExactK0.of (FGModuleCat.of _ ρ.asModule) :
          ExactK0 (finiteModulesExactStructure k[Equiv.Perm (Fin 3)])) := by
  dsimp only
  let ρ := standardRepresentation k (Fin 3)
  let : Module.Finite k[Equiv.Perm (Fin 3)] ρ.asModule :=
    Module.Finite.of_restrictScalars_finite k _ _
  let : Module.Finite k[alternatingGroup (Fin 3)]
      (Representation.asModule (ρ.comp (alternatingGroup (Fin 3)).subtype)) :=
    Module.Finite.of_restrictScalars_finite k _ _
  have hperm : permK0 k (Equiv.Perm (Fin 3))
      (Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) =
        2 • (1 : ExactK0 (finiteModulesExactStructure k[Equiv.Perm (Fin 3)])) := by
    rw [permK0_def, exactK0_ofMulAction_quotient_eq_index_nsmul (k := k) 2
      (alternatingGroup (Fin 3)) (fun g ↦ ⟨1, by
        simp [Equiv.Perm.mem_alternatingGroup, Int.units_sq]⟩),
      alternatingGroup.index_eq_two, ← exactK0_one_eq_of_trivial]
  rw [← resK0_of_asModule k (alternatingGroup (Fin 3)).subtype ρ,
    indK0_resK0, hperm, smul_mul_assoc, one_mul]

end TauCeti
