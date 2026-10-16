/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Smooth.Basic

/-!
# Projective cotangent modules at augmented points

For an augmentation `f : A →ₐ[R] R`, the module `ker(f) / ker(f)²` is projective over `R`
when `A` is formally smooth. This does not require a noetherian base or a finite-type
algebra. It supplies the projectivity input for forming the adjoint comodule of a
smooth affine group over a ring.

The comparison uses Mathlib's `Algebra.Extension.cotangentComplex` and its splitting
criterion for formal smoothness. This map is split injective, exhibiting the cotangent
module as a direct summand of the
fiber of the projective module of differentials of `A`.

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
  have hmap : algebraMap P.Ring R = f.toRingHom :=
    RingHom.algebraMap_toAlgebra f.toRingHom
  have hker : P.ker = RingHom.ker f.toRingHom := congrArg RingHom.ker hmap
  let _ : Algebra.FormallySmooth R P.Ring := inferInstanceAs (Algebra.FormallySmooth R A)
  obtain ⟨l, hl⟩ := P.formallySmooth_iff_split_injection.mp
    (inferInstance : Algebra.FormallySmooth R R)
  let _ : Module.Projective R P.Cotangent :=
    Module.Projective.of_split P.cotangentComplex l hl
  let _ : Module.Projective R P.ker.Cotangent :=
    Module.Projective.of_equiv (P.cotangentEquivCotangentKer.restrictScalars R)
  exact Module.Projective.of_equiv
    ((Ideal.Cotangent.equivOfEq P.ker (RingHom.ker f.toRingHom) hker).restrictScalars R)

end AlgHom
