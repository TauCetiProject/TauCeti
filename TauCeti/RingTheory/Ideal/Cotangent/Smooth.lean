/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Smooth.Basic

/-!
# Projective cotangent modules at augmented points

For an extension `P → S` of `R`-algebras with `P` and `S` formally smooth over `R`, the
cotangent module `I / I²` of its kernel is projective over `S`: Mathlib's splitting criterion
for formal smoothness exhibits it as a direct summand of the projective module
`S ⊗[P] Ω[P⁄R]`.

Specialized to an augmentation `f : A →ₐ[R] R`, the module `ker(f) / ker(f)²` is projective
over `R` when `A` is formally smooth. This does not require a noetherian base or a finite-type
algebra. It supplies the projectivity input for forming the adjoint comodule of a
smooth affine group over a ring.

## References

* The Stacks Project, Tags 00TH and 031I (cotangent sequence and formal smoothness).
* B. Conrad, *Reductive Group Schemes*, §3.1 (the Lie algebra over a base).
-/

public section

namespace Algebra.Extension

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The cotangent module of an extension of formally smooth algebras is projective: it is a
direct summand of `S ⊗[P] Ω[P⁄R]` via the cotangent complex. -/
theorem projective_cotangent_of_formallySmooth (P : Extension R S)
    [FormallySmooth R P.Ring] [FormallySmooth R S] : Module.Projective S P.Cotangent :=
  have ⟨l, hl⟩ := P.formallySmooth_iff_split_injection.mp ‹_›
  .of_split P.cotangentComplex l hl

end Algebra.Extension

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
