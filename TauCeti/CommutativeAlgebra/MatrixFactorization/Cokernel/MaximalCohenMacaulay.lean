/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.GorensteinProjective.Hypersurface
public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Resolution
public import TauCeti.RingTheory.CohenMacaulay.Hypersurface

/-!
# Maximal Cohen–Macaulay modules as cokernels of matrix factorizations

Let `S` be a Noetherian local ring, `w` a non-zero-divisor of `S` with `S/(w)` local, and
`R = S/(w)`. A finitely generated `R`-module `M` is maximal Cohen–Macaulay when
`dim R ≤ depth M`; this formulation includes the zero module.

When `S` is Cohen–Macaulay, the cokernel of the reduction modulo `w` of a finite-projective matrix
factorization of `w` is maximal Cohen–Macaulay
(`TauCeti.MatrixFactorization.ringKrullDim_quotient_le_depth_quotientCokernel`): such a cokernel
has projective dimension at most one over `S`, and the Auslander–Buchsbaum formula turns this
into the depth bound (`ModuleCat.ringKrullDim_quotient_le_depth_of_hasProjectiveDimensionLE`).

When `S` is regular local, this is **Eisenbud's description** of the maximal Cohen–Macaulay
modules over the hypersurface: a finitely generated `R`-module is maximal Cohen–Macaulay exactly
when it is the cokernel of the reduction of a matrix factorization
(`TauCeti.MatrixFactorization.exists_quotientCokernel_iso_iff_ringKrullDim_le_depth`). Since the
finitely generated projective `S`-modules are free, these are the finite free factorizations.

In the same regular local setting the finitely generated Gorenstein-projective `R`-modules are
exactly the maximal Cohen–Macaulay ones
(`TauCeti.isGorensteinProjective_quotient_iff_ringKrullDim_le_depth`). A Gorenstein-projective
`R`-module has projective dimension at most one over `S`
(`hasProjectiveDimensionLE_restrictScalars_quotient_of_isRegularLocalRing` in the namespace
`TauCeti.IsGorensteinProjective`), and an `R`-module of projective dimension at most one over `S`
is the cokernel of a matrix factorization, hence Gorenstein-projective
(`TauCeti.MatrixFactorization.isGorensteinProjective_of_hasProjectiveDimensionLE`). Thus the
stable category of Gorenstein-projective `R`-modules, the target of the triangle equivalence
`HMF(S,w) ≌ stable(Gproj-R)` (`quotientGorensteinProjectiveStableCokernelEquivalence` in the
namespace `TauCeti.MatrixFactorization.HomotopyCategory`), is the stable category of maximal
Cohen–Macaulay `R`-modules.

## Main results

* `TauCeti.MatrixFactorization.ringKrullDim_quotient_le_depth_quotientCokernel`: over a
  Cohen–Macaulay local ring, cokernels of reduced matrix factorizations are maximal
  Cohen–Macaulay.
* `TauCeti.MatrixFactorization.exists_quotientCokernel_iso_iff_ringKrullDim_le_depth`: over a
  regular local ring, the cokernels of reduced matrix factorizations are exactly the finitely
  generated maximal Cohen–Macaulay modules.
* `TauCeti.isGorensteinProjective_quotient_iff_ringKrullDim_le_depth`: over a hypersurface in a
  regular local ring, a module is Gorenstein-projective exactly when it is finitely generated and
  maximal Cohen–Macaulay.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Sections 5–6.
* R.-O. Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Mathematical Surveys
  and Monographs **262**, American Mathematical Society (2021), Section 4.
-/

public section

open CategoryTheory IsLocalRing

universe u

namespace TauCeti

variable {S : Type u} [CommRing S] {w : S} [IsLocalRing (S ⧸ Ideal.span {w})]

namespace MatrixFactorization

/-- **Cokernels of matrix factorizations are maximal Cohen–Macaulay.** Let `S` be a
Cohen–Macaulay Noetherian local ring and `w` a non-zero-divisor with `S/(w)` local. The cokernel
of the reduction modulo `w` of a finite-projective matrix factorization of `w` has depth at least
`dim S/(w)`. -/
theorem ringKrullDim_quotient_le_depth_quotientCokernel [IsLocalRing S] [IsNoetherianRing S]
    (hS : Module.IsCohenMacaulay S S) (hw : w ∈ nonZeroDivisors S) (X : MatrixFactorization S w) :
    ringKrullDim (S ⧸ Ideal.span {w}) ≤
      depth (cokernelFunctor.obj
        ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X)).obj :=
  ModuleCat.ringKrullDim_quotient_le_depth_of_hasProjectiveDimensionLE hS hw _
    ((exists_quotientCokernel_iso_iff_hasProjectiveDimensionLE_of_isNoetherianRing hw _).1
      ⟨X, ⟨Iso.refl _⟩⟩)

/-- **Eisenbud's description of maximal Cohen–Macaulay modules over a hypersurface.** Let `S` be a
regular local ring and `w` a non-zero-divisor with `S/(w)` local. A finitely generated
`S/(w)`-module is isomorphic to the cokernel of the reduction modulo `w` of a finite-projective
matrix factorization of `w` exactly when its depth is at least `dim S/(w)`. -/
theorem exists_quotientCokernel_iso_iff_ringKrullDim_le_depth [IsRegularLocalRing S]
    (hw : w ∈ nonZeroDivisors S) (M : ModuleCat.{u} (S ⧸ Ideal.span {w}))
    [Module.Finite (S ⧸ Ideal.span {w}) M] :
    (∃ X : MatrixFactorization S w, Nonempty
      ((cokernelFunctor.obj ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj
        X)).obj ≅ M)) ↔
      ringKrullDim (S ⧸ Ideal.span {w}) ≤ depth M := by
  rw [exists_quotientCokernel_iso_iff_hasProjectiveDimensionLE_of_isNoetherianRing hw,
    ModuleCat.hasProjectiveDimensionLE_iff_ringKrullDim_quotient_le_depth hw]

end MatrixFactorization

/-- **Gorenstein-projective modules over a hypersurface are the maximal Cohen–Macaulay modules.**
Let `S` be a regular local ring and `w` a non-zero-divisor with `S/(w)` local. An `S/(w)`-module
is Gorenstein-projective exactly when it is finitely generated and its depth is at least
`dim S/(w)`. -/
theorem isGorensteinProjective_quotient_iff_ringKrullDim_le_depth [IsRegularLocalRing S]
    (hw : w ∈ nonZeroDivisors S) (M : ModuleCat.{u} (S ⧸ Ideal.span {w})) :
    IsGorensteinProjective (S ⧸ Ideal.span {w}) M ↔
      Module.Finite (S ⧸ Ideal.span {w}) M ∧
        ringKrullDim (S ⧸ Ideal.span {w}) ≤ depth M := by
  refine ⟨fun hM ↦ ?_, fun ⟨_, hM⟩ ↦ ?_⟩
  · have := hM.finite
    exact ⟨this, (ModuleCat.hasProjectiveDimensionLE_iff_ringKrullDim_quotient_le_depth hw M).1
      (hM.hasProjectiveDimensionLE_restrictScalars_quotient_of_isRegularLocalRing hw)⟩
  · obtain ⟨X, ⟨e⟩⟩ :=
      (MatrixFactorization.exists_quotientCokernel_iso_iff_ringKrullDim_le_depth hw M).2 hM
    exact (IsGorensteinProjective _).prop_of_iso e
      (MatrixFactorization.isGorensteinProjective_cokernelFunctor_obj_baseChangeFunctor_obj hw X)

end TauCeti
