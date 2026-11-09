/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.Extension.Cotangent.Smooth

/-!
# Projective cotangent modules at augmented points

For an augmentation `f : A →ₐ[R] R` of a formally smooth `R`-algebra `A`, the module
`ker(f) / ker(f)²` is projective over `R`. This is the specialization of
`Algebra.Extension.projective_cotangent_of_formallySmooth` to the extension `A → R` given by `f`.
It does not require a noetherian base or a finite-type algebra. It supplies the projectivity
input for forming the adjoint comodule of a smooth affine group over a ring.

## References

* The Stacks Project, Tags 00TH and 031I (cotangent sequence and formal smoothness).
* B. Conrad, *Reductive Group Schemes*, §3.1 (the Lie algebra over a base).
-/

public section

namespace AlgHom

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The cotangent module at an augmented point of a formally smooth algebra is projective
over the base. No finiteness or noetherian hypothesis is needed. -/
theorem projective_cotangent_ker_of_formallySmooth (f : A →ₐ[R] R)
    [Algebra.FormallySmooth R A] :
    Module.Projective R (RingHom.ker f.toRingHom).Cotangent := by
  let P : Algebra.Extension R R :=
    Algebra.Extension.ofSurjective f (fun r ↦ ⟨algebraMap R A r, f.commutes r⟩)
  have hker : P.ker = RingHom.ker f.toRingHom :=
    congrArg RingHom.ker (RingHom.algebraMap_toAlgebra f.toRingHom)
  have : Algebra.FormallySmooth R P.Ring := ‹_›
  have := P.projective_cotangent_of_formallySmooth
  have : Module.Projective R P.ker.Cotangent :=
    .of_equiv (P.cotangentEquivCotangentKer.restrictScalars R)
  exact .of_equiv
    ((Ideal.Cotangent.equivOfEq P.ker (RingHom.ker f.toRingHom) hker).restrictScalars R)

end AlgHom
