/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.Filtration
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Convergence

/-!
# The spectral sequence of the twisted complex

The canonical index filtration `TwistingCocycle.twistedIndexSubobject` gives a spectral sequence
of the twisted cochain complex. Finite bounds on the generator indices identify its stable pages
with the graded pieces of the filtered cohomology, proving strong convergence.

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

/-- **Strong convergence of the index spectral sequence.** If every index lies in the interval
`(a, b]`, then on every page `r ≥ 2` with `q - r + 2 ≤ a` and `b ≤ q + r - 1`, the object at
`pq = (p, q)` is the graded piece `F_{q+1} H^{p+q} / F_q H^{p+q}` of the filtration of the
cohomology `H^{p+q}` of the twisted complex (identified with the abutment by
`CochainComplex.filtrationAbutmentIso`). -/
noncomputable def indexSpectralSequencePageXIsoGraded {a b : ℤ} (ha : ∀ x, a < ind x)
    (hb : ∀ x, ind x ≤ b) (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (hra : pq.2 - r + 2 ≤ a)
    (hrb : b ≤ pq.2 + r - 1) :
    ((m.indexSpectralSequence dM hM).page r).X pq ≅
      cokernel ((CochainComplex.spectralObject (CochainComplex.filtrationFunctor
        (m.twistedIndexSubobject hM) (m.twistedIndexSubobject_mono hM))).abutmentFiltrationMap pq.2
          (pq.1 + pq.2)) :=
  CochainComplex.filtrationSpectralSequencePageXIsoGradedOfFinite _ _
    (m.twistedIndexSubobject_eq_bot hM ha) (m.twistedIndexSubobject_eq_top hM hb) r hr pq hra hrb

end TauCeti.TwistingCocycle
