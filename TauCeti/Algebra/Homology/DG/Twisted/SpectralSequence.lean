/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.Filtration
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.SpectralObject

/-!
# The spectral sequence of the twisted complex

The canonical index filtration `TwistingCocycle.twistedIndexSubobject` gives a spectral sequence
of the twisted cochain complex. Strong convergence follows from the generic
`CochainComplex.filtrationSpectralSequencePageXIsoGradedOfFinite` in
`TauCeti.Algebra.Homology.SpectralSequence.Filtered.Convergence`, using
`TwistingCocycle.twistedIndexSubobject_eq_bot` and
`TwistingCocycle.twistedIndexSubobject_eq_top` to supply the finite filtration bounds.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 3.38.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Section 4.2.
-/

public section

open CategoryTheory Limits MulOpposite

universe uR uA uM uP

namespace TauCeti.TwistingCocycle

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M]
  {P : Type uP} {ind : P → ℤ}
  [Fintype P] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ] (dM : M →ₗ[R] M)
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  (m : TwistingCocycle 𝒜 d P ind) (hM : IsDGRightModule h ℳ dM)

/-- The **index spectral sequence** of the twisted complex of a twisting cocycle: the spectral
sequence of its index filtration.  On its first page, numbered `2`, the object at `(p, q)` is the
cohomology `H^{p+q}(F_{q+1} / F_q)` of a graded piece of the index filtration
(`CochainComplex.spectralSequenceFirstPageXIsoCokernel`). -/
noncomputable abbrev indexSpectralSequence :=
  CochainComplex.spectralSequence
    (CochainComplex.filtrationFunctor
      (m.twistedIndexSubobject hM) (m.twistedIndexSubobject_mono hM))

end TauCeti.TwistingCocycle
