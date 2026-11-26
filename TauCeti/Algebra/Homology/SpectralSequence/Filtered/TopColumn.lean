/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Convergence
public import TauCeti.Algebra.Homology.SpectralObject.Edge
public import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import TauCeti.Algebra.Category.ModuleCat.Range

/-!
# The top column of the spectral sequence of a filtered complex

Let `F : ℤ → Subobject K` be an increasing filtration of a cochain complex `K` with
`F_{q+1} = K`. Then `H^n(K)` is the piece `F_{q+1}` of the filtration of the abutment, and it
projects onto the graded piece `F_{q+1} H^n / F_q H^n`, which is the limit object `E∞` at `q` in
degree `n` (`CategoryTheory.Abelian.SpectralObject.EInftyIsoCokernel`). This projection is
`CochainComplex.filtrationToTopColumnEInfty`, the projection
`CategoryTheory.Abelian.SpectralObject.abutmentToEInfty` of the spectral object of the filtration
transported to `H^n(K)`; when `q + 1` is the largest filtration index, its
target is the top column of the limit page.

For complexes of modules, the filtration of the abutment is the image filtration
(`CochainComplex.range_abutmentFiltrationι_comp_filtrationAbutmentIso_hom`), so the projection
onto the top column vanishes on a class exactly when the class comes from the cohomology of the
subcomplex `F_q` (`CochainComplex.filtrationToTopColumnEInfty_eq_zero_iff`). This is the
algebraic content of reading a class off the top column of a spectral sequence, as for the
classes living over the fundamental class of the base of a fibration.

## Main definitions

* `CochainComplex.filtrationToTopColumnEInfty`: the projection `H^n(K) ⟶ E∞` at `q`.

## Main results

* `CochainComplex.filtrationToTopColumnEInfty_eq_zero_iff`: its kernel is the image of
  `H^n(F_q) ⟶ H^n(K)`.

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 2.2.
-/

public section

open CategoryTheory Limits

namespace CochainComplex

section TopColumn

variable {C : Type*} [Category* C] [Abelian C] {K : CochainComplex C ℤ} (F : ℤ → Subobject K)
  (hF : Monotone F) {q : ℤ} (hq : F (q + 1) = ⊤)

include hq in
/-- **The projection onto the top column of the spectral sequence of a filtered complex.** If
`F_{q+1}` is all of `K`, then `H^n(K)` is the piece `F_{q+1}` of the filtration of the abutment,
and this is its projection onto the graded piece `F_{q+1} H^n / F_q H^n`, the limit object `E∞` at
`q` in degree `n`. -/
noncomputable def filtrationToTopColumnEInfty (n : ℤ) :
    K.homology n ⟶ (spectralObject (filtrationFunctor F hF)).EInfty q n :=
  haveI := isIso_filtrationAbutmentFiltrationι F hF hq n
  (filtrationAbutmentIso F hF n).inv ≫
    (spectralObject (filtrationFunctor F hF)).abutmentToEInfty q n

/-- **The defining property of the projection onto the top column.** On the piece `F_{q+1}` of the
filtration of the abutment, identified with `H^n(K)`, the projection is the quotient map onto the
cokernel of `F_q ⟶ F_{q+1}`, identified with `E∞`. -/
@[reassoc]
lemma abutmentFiltrationι_comp_filtrationAbutmentIso_hom_comp_filtrationToTopColumnEInfty
    (n : ℤ) :
    (spectralObject (filtrationFunctor F hF)).abutmentFiltrationι (q + 1) n ≫
        (filtrationAbutmentIso F hF n).hom ≫ filtrationToTopColumnEInfty F hF hq n =
      cokernel.π ((spectralObject (filtrationFunctor F hF)).abutmentFiltrationMap q n) ≫
        ((spectralObject (filtrationFunctor F hF)).EInftyIsoCokernel q n).inv := by
  have := isIso_filtrationAbutmentFiltrationι F hF hq n
  simp [filtrationToTopColumnEInfty]

instance (n : ℤ) : Epi (filtrationToTopColumnEInfty F hF hq n) := by
  have := isIso_filtrationAbutmentFiltrationι F hF hq n
  rw [filtrationToTopColumnEInfty]
  infer_instance

end TopColumn

section ModuleCat

variable {k : Type*} [Ring k] {K : CochainComplex (ModuleCat k) ℤ} (F : ℤ → Subobject K)
  (hF : Monotone F)

/-- **The filtration of the abutment is the image filtration.** Through `filtrationAbutmentIso`,
the `q`th piece of the filtration of the abutment `H^n(K)` is the image of the map
`H^n(F_q) ⟶ H^n(K)` induced by the inclusion of the subcomplex `F_q`. -/
theorem range_abutmentFiltrationι_comp_filtrationAbutmentIso_hom (q n : ℤ) :
    LinearMap.range ((spectralObject (filtrationFunctor F hF)).abutmentFiltrationι q n ≫
        (filtrationAbutmentIso F hF n).hom).hom =
      LinearMap.range (HomologicalComplex.homologyMap (F q).arrow n).hom := by
  have h := congrArg (fun f ↦ LinearMap.range (ModuleCat.Hom.hom f))
    (toFiltrationAbutmentFiltration_comp_filtrationAbutmentIso_hom F hF q n)
  simp only [ModuleCat.hom_comp] at h ⊢
  rwa [LinearMap.range_comp_of_range_eq_top _
    ((ModuleCat.epi_iff_range_eq_top _).1 inferInstance)] at h

/-- **The kernel of the projection onto the top column.** If `F_{q+1}` is all of `K`, the
projection of `H^n(K)` onto the limit object `E∞` at `q` vanishes on a class exactly when the class
comes from the cohomology of the subcomplex `F_q`. -/
theorem filtrationToTopColumnEInfty_eq_zero_iff {q : ℤ} (hq : F (q + 1) = ⊤) {n : ℤ}
    (α : K.homology n) :
    (filtrationToTopColumnEInfty F hF hq n).hom α = 0 ↔
      α ∈ LinearMap.range (HomologicalComplex.homologyMap (F q).arrow n).hom := by
  have := isIso_filtrationAbutmentFiltrationι F hF hq n
  -- Through `filtrationAbutmentIso`, the kernel is the piece `F_q` of the filtration of the
  -- abutment, which is the image filtration.
  rw [← SetLike.ext_iff.1 (range_abutmentFiltrationι_comp_filtrationAbutmentIso_hom F hF q n) α,
    ModuleCat.mem_range_comp_iso_hom,
    ((spectralObject (filtrationFunctor F hF)).abutmentToEInfty_exact q n).moduleCat_range_eq_ker,
    LinearMap.mem_ker, filtrationToTopColumnEInfty, ModuleCat.hom_comp, LinearMap.comp_apply]

end ModuleCat

end CochainComplex
