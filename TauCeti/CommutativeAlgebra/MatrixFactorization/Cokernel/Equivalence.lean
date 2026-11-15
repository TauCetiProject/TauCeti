/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.FullyFaithful
public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Resolution
public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Triangulated
public import TauCeti.Algebra.Homology.GorensteinProjective.Hypersurface

/-!
# Matrix factorizations and stable Gorenstein-projective modules over a hypersurface

Let `w` be a non-zero-divisor of a commutative ring `S` and put `R = S/(w)`. Reducing a
finite-projective matrix factorization `X = (X₀ --d₀--> X₁ --d₁--> X₀)` of `w` modulo `w` and
taking the cokernel of `d₀'` gives a fully faithful triangle functor
`HMF(S,w) ⥤ stable(Gproj-R)`
(`TauCeti.MatrixFactorization.HomotopyCategory.quotientGorensteinProjectiveStableCokernel`).
This file shows that, when `S` moreover has finite global dimension, this functor is a triangle
equivalence. This covers Eisenbud's case of a regular local ring `S`; there the finitely generated
projective modules are free, so the factorizations are the finite free ones.

The essential image of the cokernel functor consists of the `R`-modules with a resolution of
length one by finitely generated projective `S`-modules
(`TauCeti.MatrixFactorization.quotientGorensteinProjectiveCokernel_essImage_iff`). A
Gorenstein-projective `R`-module is finitely presented over `R`, hence over `S`, so it has such a
resolution exactly when its projective dimension over `S` is at most one
(`quotientGorensteinProjectiveCokernel_essImage_iff_hasProjectiveDimensionLE`). When `S` has
finite global dimension, every finitely generated Gorenstein-projective `R`-module has projective
dimension at most one over `S`
(`TauCeti.IsGorensteinProjective.hasProjectiveDimensionLE_restrictScalars_quotient`), so the
cokernel functor is essentially surjective, already before passing to stable categories.
Together with full faithfulness this makes the stable cokernel functor an equivalence, and an
equivalence whose functor is a triangle functor is a triangulated equivalence.

The non-zero-divisor hypothesis is the only one on `w`: if `w` is a unit both categories are
trivial. Identifying the finitely generated Gorenstein-projective `R`-modules with the maximal
Cohen–Macaulay ones is a separate statement, not made here.

## Main results

In the namespace `TauCeti.MatrixFactorization`:

* `quotientGorensteinProjectiveCokernel_essImage_iff_hasProjectiveDimensionLE`: a
  Gorenstein-projective `S/(w)`-module is the cokernel of the reduction of a matrix factorization
  exactly when its projective dimension over `S` is at most one.
* `quotientGorensteinProjectiveCokernel_essSurj`: in finite global dimension, every finitely
  generated Gorenstein-projective `S/(w)`-module is such a cokernel.

In the namespace `TauCeti.MatrixFactorization.HomotopyCategory`:

* `quotientGorensteinProjectiveStableCokernel_isEquivalence`: in finite global dimension, the
  cokernel functor `HMF(S,w) ⥤ stable(Gproj-S/(w))` is an equivalence;
  `quotientGorensteinProjectiveStableCokernel_isEquivalence_of_isRegularLocalRing` is the case of
  a regular local ring.
* `quotientGorensteinProjectiveStableCokernelEquivalence`: the equivalence
  `HMF(S,w) ≌ stable(Gproj-S/(w))`, and
  `quotientGorensteinProjectiveStableCokernelEquivalence_isTriangulated`: it is a triangulated
  equivalence.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Sections 5–6: the equivalence between
  matrix factorizations and stable maximal Cohen–Macaulay modules over a hypersurface in a regular
  local ring.
* R.-O. Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Mathematical Surveys
  and Monographs **262**, American Mathematical Society (2021), Section 4.
-/

public section

noncomputable section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory

variable {S : Type u} [CommRing S] {w : S}

/-! ### Essential surjectivity of the cokernel functor -/

/-- **The essential image of the cokernel functor by projective dimension.** For a
non-zero-divisor `w`, a Gorenstein-projective `S/(w)`-module is isomorphic to the cokernel of the
reduction of a finite-projective matrix factorization of `w` exactly when its projective dimension
over `S` is at most one. -/
theorem quotientGorensteinProjectiveCokernel_essImage_iff_hasProjectiveDimensionLE
    (hw : w ∈ nonZeroDivisors S) (M : GorensteinProjectiveModuleCat.{u} (S ⧸ Ideal.span {w})) :
    (quotientGorensteinProjectiveCokernel hw).essImage M ↔
      HasProjectiveDimensionLE
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M.obj) 1 := by
  -- `M` is finitely presented over `S/(w)`, which is a finitely presented `S`-module.
  have : Module.FinitePresentation (S ⧸ Ideal.span {w})
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M.obj) :=
    M.property.finitePresentation
  have : Module.FinitePresentation S (S ⧸ Ideal.span {w}) :=
    Module.finitePresentation_of_surjective (Ideal.span {w}).mkQ (Submodule.mkQ_surjective _)
      (by rw [Submodule.ker_mkQ]; exact Submodule.fg_span_singleton w)
  have : IsScalarTower S (S ⧸ Ideal.span {w})
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M.obj) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  have := Module.FinitePresentation.trans S
    ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M.obj)
    (S ⧸ Ideal.span {w})
  rw [quotientGorensteinProjectiveCokernel_essImage_iff hw, ← exists_quotientCokernel_iso_iff hw,
    exists_quotientCokernel_iso_iff_hasProjectiveDimensionLE hw]

/-- **Essential surjectivity of the cokernel functor.** For a non-zero-divisor `w` of a
ring `S` of finite global dimension, every finitely generated Gorenstein-projective
`S/(w)`-module is isomorphic to the cokernel of the reduction modulo `w` of a finite-projective
matrix factorization of `w`. The global-dimension hypothesis ranges over all `S`-modules in the
universe of `S`. -/
theorem quotientGorensteinProjectiveCokernel_essSurj
    (hw : w ∈ nonZeroDivisors S) (d : ℕ)
    (hd : ∀ N : ModuleCat.{u} S, HasProjectiveDimensionLE N d) :
    (quotientGorensteinProjectiveCokernel hw).EssSurj where
  mem_essImage M :=
    (quotientGorensteinProjectiveCokernel_essImage_iff_hasProjectiveDimensionLE hw M).2
      (M.property.hasProjectiveDimensionLE_restrictScalars_quotient hw d hd)

namespace HomotopyCategory

/-- **Essential surjectivity of the stable cokernel functor.** For a non-zero-divisor `w` of a
ring `S` of finite global dimension, every object of the stable category of finitely
generated Gorenstein-projective `S/(w)`-modules is isomorphic to the cokernel of the reduction of
a finite-projective matrix factorization of `w`. -/
theorem quotientGorensteinProjectiveStableCokernel_essSurj
    (hw : w ∈ nonZeroDivisors S) (d : ℕ)
    (hd : ∀ N : ModuleCat.{u} S, HasProjectiveDimensionLE N d) :
    (quotientGorensteinProjectiveStableCokernel hw).EssSurj := by
  have := quotientGorensteinProjectiveCokernel_essSurj hw d hd
  have : ((nullHomotopic (S := S) (w := w)).quotientFunctor ⋙
      quotientGorensteinProjectiveStableCokernel hw).EssSurj := by
    rw [quotientFunctor_comp_quotientGorensteinProjectiveStableCokernel]
    infer_instance
  exact ⟨fun Y ↦ ⟨_, ⟨((nullHomotopic (S := S) (w := w)).quotientFunctor ⋙
    quotientGorensteinProjectiveStableCokernel hw).objObjPreimageIso Y⟩⟩⟩

/-- **The stable cokernel functor is an equivalence in finite global dimension.** For a
non-zero-divisor `w` of a ring `S` of finite global dimension, the functor
`HMF(S,w) ⥤ stable(Gproj-S/(w))` sending a finite-projective matrix factorization to the cokernel
of its reduction modulo `w` is an equivalence of categories. -/
theorem quotientGorensteinProjectiveStableCokernel_isEquivalence
    (hw : w ∈ nonZeroDivisors S) (d : ℕ)
    (hd : ∀ N : ModuleCat.{u} S, HasProjectiveDimensionLE N d) :
    (quotientGorensteinProjectiveStableCokernel hw).IsEquivalence where
  faithful := quotientGorensteinProjectiveStableCokernel_faithful hw
  full := quotientGorensteinProjectiveStableCokernel_full hw
  essSurj := quotientGorensteinProjectiveStableCokernel_essSurj hw d hd

/-- **Eisenbud's equivalence.** For a non-zero-divisor `w` of a regular local ring `S`, the
functor `HMF(S,w) ⥤ stable(Gproj-S/(w))` sending a finite free matrix factorization to the
cokernel of its reduction modulo `w` is an equivalence of categories. -/
theorem quotientGorensteinProjectiveStableCokernel_isEquivalence_of_isRegularLocalRing
    [IsRegularLocalRing S] (hw : w ∈ nonZeroDivisors S) :
    (quotientGorensteinProjectiveStableCokernel hw).IsEquivalence :=
  quotientGorensteinProjectiveStableCokernel_isEquivalence hw
    (IsLocalRing.maximalIdeal S).spanFinrank
    (IsRegularLocalRing.hasProjectiveDimensionLE
      (IsRegularLocalRing.spanFinrank_maximalIdeal (R := S)).ge)

/-- The equivalence `HMF(S,w) ≌ stable(Gproj-S/(w))` given by the cokernel of the reduction
modulo `w`, for a non-zero-divisor `w` of a ring `S` of finite global dimension.
Its functor is the cokernel functor
(`quotientGorensteinProjectiveStableCokernelEquivalence_functor`). -/
def quotientGorensteinProjectiveStableCokernelEquivalence
    (hw : w ∈ nonZeroDivisors S) (d : ℕ)
    (hd : ∀ N : ModuleCat.{u} S, HasProjectiveDimensionLE N d) :
    HomotopyCategory (S := S) (w := w) ≌
      (GorensteinProjectiveModuleCat.exactStructure.{u}
        (S ⧸ Ideal.span {w})).ProjectiveStableCategory :=
  haveI := quotientGorensteinProjectiveStableCokernel_isEquivalence hw d hd
  (quotientGorensteinProjectiveStableCokernel hw).asEquivalence

/-- The functor of the cokernel equivalence is the stable cokernel functor. -/
@[simp]
theorem quotientGorensteinProjectiveStableCokernelEquivalence_functor
    (hw : w ∈ nonZeroDivisors S) (d : ℕ)
    (hd : ∀ N : ModuleCat.{u} S, HasProjectiveDimensionLE N d) :
    (quotientGorensteinProjectiveStableCokernelEquivalence hw d hd).functor =
      quotientGorensteinProjectiveStableCokernel hw :=
  (rfl)

/-- **The cokernel equivalence is triangulated.** For a non-zero-divisor `w` of a ring `S` of
finite global dimension, the equivalence `HMF(S,w) ≌ stable(Gproj-S/(w))` is a
triangulated equivalence, for the triangulation of `HMF(S,w)` by the parity shift and Happel's
triangulation of the stable category of Gorenstein-projective `S/(w)`-modules: both it and its
inverse are triangle functors. -/
theorem quotientGorensteinProjectiveStableCokernelEquivalence_isTriangulated
    (hw : w ∈ nonZeroDivisors S) (d : ℕ)
    (hd : ∀ N : ModuleCat.{u} S, HasProjectiveDimensionLE N d) :
    letI := (GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
      (A := S ⧸ Ideal.span {w})).stableHasShift
    letI := (GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
      (A := S ⧸ Ideal.span {w})).stableShiftFunctor_additive
    letI := (GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
      (A := S ⧸ Ideal.span {w})).stablePretriangulated
    letI := quotientGorensteinProjectiveStableCokernelCommShift hw
    letI : (quotientGorensteinProjectiveStableCokernelEquivalence hw d hd).functor.CommShift ℤ :=
      Functor.CommShift.ofIso
        (eqToIso (quotientGorensteinProjectiveStableCokernelEquivalence_functor hw d hd).symm) ℤ
    letI := (quotientGorensteinProjectiveStableCokernelEquivalence hw d hd).commShiftInverse ℤ
    letI := (quotientGorensteinProjectiveStableCokernelEquivalence hw d hd).commShift_of_functor ℤ
    (quotientGorensteinProjectiveStableCokernelEquivalence hw d hd).IsTriangulated := by
  have hE' := GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
    (A := S ⧸ Ideal.span {w})
  let := hE'.stableHasShift
  let := hE'.stableShiftFunctor_additive
  let := hE'.stablePretriangulated
  let := quotientGorensteinProjectiveStableCokernelCommShift hw
  let e := eqToIso (quotientGorensteinProjectiveStableCokernelEquivalence_functor hw d hd).symm
  let : (quotientGorensteinProjectiveStableCokernelEquivalence hw d hd).functor.CommShift ℤ :=
    Functor.CommShift.ofIso e ℤ
  let := (quotientGorensteinProjectiveStableCokernelEquivalence hw d hd).commShiftInverse ℤ
  let := (quotientGorensteinProjectiveStableCokernelEquivalence hw d hd).commShift_of_functor ℤ
  have := Functor.CommShift.ofIso_compatibility e ℤ
  have := quotientGorensteinProjectiveStableCokernel_isTriangulated hw
  exact Equivalence.IsTriangulated.mk' _ (Functor.isTriangulated_of_iso e)

end HomotopyCategory

end TauCeti.MatrixFactorization
