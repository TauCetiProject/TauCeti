/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Convergence
public import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The top column of the spectral sequence of a filtered complex

Let `F : ℤ → Subobject K` be an increasing filtration of a cochain complex `K` with
`F_{q+1} = K`. Then `H^n(K)` is the piece `F_{q+1}` of the filtration of the abutment, and it
projects onto the graded piece `F_{q+1} H^n / F_q H^n`, which is the limit object `E∞` at `q` in
degree `n` (`CategoryTheory.Abelian.SpectralObject.EInftyIsoCokernel`). This projection is
`CochainComplex.filtrationToTopColumnEInfty`; when `q + 1` is the largest filtration index, its
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
    inv ((spectralObject (filtrationFunctor F hF)).abutmentFiltrationι (q + 1) n) ≫
      cokernel.π ((spectralObject (filtrationFunctor F hF)).abutmentFiltrationMap q n) ≫
        ((spectralObject (filtrationFunctor F hF)).EInftyIsoCokernel q n).inv

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
  set X := spectralObject (filtrationFunctor F hF)
  set e := asIso (X.abutmentFiltrationι (q + 1) n) ≪≫ filtrationAbutmentIso F hF n
  set m := X.abutmentFiltrationMap q n
  -- Up to the isomorphism `e` of the source with the piece `F_{q+1}` and the isomorphism of the
  -- target with the cokernel of `m`, the projection is the quotient map onto that cokernel.
  have hproj : (filtrationToTopColumnEInfty F hF hq n).hom α = 0 ↔
      (cokernel.π m).hom (e.inv.hom α) = 0 := by
    have h : filtrationToTopColumnEInfty F hF hq n =
        e.inv ≫ cokernel.π m ≫ (X.EInftyIsoCokernel q n).inv := by
      simp [e, m, X, filtrationToTopColumnEInfty]
    rw [h, ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]
    exact (X.EInftyIsoCokernel q n).symm.toLinearEquiv.map_eq_zero_iff
  have hmem : e.inv.hom α ∈ LinearMap.range m.hom ↔ α ∈ LinearMap.range (m ≫ e.hom).hom := by
    rw [ModuleCat.hom_comp, LinearMap.range_comp]
    exact (Submodule.mem_map_equiv (p := LinearMap.range m.hom) (e := e.toLinearEquiv)).symm
  -- Applying `e`, the range of `m` becomes the embedding of the piece `F_q`, which is the image
  -- filtration.
  have hm : m ≫ e.hom = X.abutmentFiltrationι q n ≫ (filtrationAbutmentIso F hF n).hom :=
    Abelian.SpectralObject.abutmentFiltrationMap_ι_assoc _ _ _ _
  rw [hproj, ← LinearMap.mem_ker, ← (ShortComplex.exact_cokernel m).moduleCat_range_eq_ker, hmem,
    hm]
  exact SetLike.ext_iff.1 (range_abutmentFiltrationι_comp_filtrationAbutmentIso_hom F hF q n) α

end ModuleCat

end CochainComplex
