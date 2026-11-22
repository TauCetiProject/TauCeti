/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.RingHom

import TauCeti.Algebra.Ring.Prod

/-!
# Projectivity of a ring as a module through a ring homomorphism

For a ring homomorphism `f : R →+* S`, `S` becomes an `R`-module via `f.toModule`. When `f` admits
an `R`-linear right inverse `j : S →+ R` (satisfying `f (j s) = s` and `r * j s = j (f r * s)`),
`S` is a projective `R`-module (`RingHom.projective_toModule_of_split`). In particular, the factor
projections of a binary product ring `R × S` (and their opposites) make the factors projective.
-/

public section

namespace RingHom

variable {R S : Type*} [Ring R] [Ring S]

/-- If `f : R →+* S` admits an additive right inverse `j : S →+ R` with `r * j s = j (f r * s)`,
then `S` is projective as an `R`-module through `f`. -/
theorem projective_toModule_of_split (f : R →+* S) (j : S →+ R)
    (hfj : ∀ s, f (j s) = s) (hmul_left : ∀ r s, r * j s = j (f r * s)) :
    letI := f.toModule; Module.Projective R S :=
  letI := f.toModule
  Module.Projective.of_split ({ j with map_smul' r s := (hmul_left r s).symm } : S →ₗ[R] R)
    ({ f with map_smul' := f.map_mul } : R →ₗ[R] S) (LinearMap.ext hfj)

/-- `R` is projective as an `(R × S)`-module via `RingHom.fst R S`. -/
theorem projective_fst (R S : Type*) [Ring R] [Ring S] :
    letI := (fst R S).toModule; Module.Projective (R × S) R :=
  projective_toModule_of_split _ (AddMonoidHom.inl R S) (fun _ ↦ rfl) AddMonoidHom.mul_inl

/-- `S` is projective as an `(R × S)`-module via `RingHom.snd R S`. -/
theorem projective_snd (R S : Type*) [Ring R] [Ring S] :
    letI := (snd R S).toModule; Module.Projective (R × S) S :=
  projective_toModule_of_split _ (AddMonoidHom.inr R S) (fun _ ↦ rfl) AddMonoidHom.mul_inr

/-- `Rᵐᵒᵖ` is projective as an `(R × S)ᵐᵒᵖ`-module via `RingHom.op (RingHom.fst R S)`. -/
theorem projective_op_fst (R S : Type*) [Ring R] [Ring S] :
    letI := (op (fst R S)).toModule; Module.Projective (R × S)ᵐᵒᵖ Rᵐᵒᵖ :=
  projective_toModule_of_split _
    ((MulOpposite.opAddEquiv.toAddMonoidHom.comp (AddMonoidHom.inl R S)).comp
      MulOpposite.opAddEquiv.symm.toAddMonoidHom)
    (fun _ ↦ rfl) fun _ _ ↦ MulOpposite.unop_injective (by ext <;> simp)

/-- `Sᵐᵒᵖ` is projective as an `(R × S)ᵐᵒᵖ`-module via `RingHom.op (RingHom.snd R S)`. -/
theorem projective_op_snd (R S : Type*) [Ring R] [Ring S] :
    letI := (op (snd R S)).toModule; Module.Projective (R × S)ᵐᵒᵖ Sᵐᵒᵖ :=
  projective_toModule_of_split _
    ((MulOpposite.opAddEquiv.toAddMonoidHom.comp (AddMonoidHom.inr R S)).comp
      MulOpposite.opAddEquiv.symm.toAddMonoidHom)
    (fun _ ↦ rfl) fun _ _ ↦ MulOpposite.unop_injective (by ext <;> simp)

end RingHom
