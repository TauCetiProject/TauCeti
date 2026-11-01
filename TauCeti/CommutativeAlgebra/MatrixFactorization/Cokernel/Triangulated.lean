/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.GorensteinProjective
public import TauCeti.CommutativeAlgebra.MatrixFactorization.Triangulated
public import TauCeti.CategoryTheory.Exact.Stable.Functor.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# The Gorenstein-projective stable cokernel functor is a triangle functor

Let `w` be a non-zero-divisor of a commutative ring `S`. Reducing a finite-projective matrix
factorization `X = (X₀ --d₀--> X₁ --d₁--> X₀)` modulo `w` and taking the cokernel of `d₀'`
gives a finitely generated Gorenstein-projective `S/(w)`-module, and this descends to a functor
`HMF(S,w) ⥤ stable(Gproj-S/(w))`
(`TauCeti.MatrixFactorization.HomotopyCategory.quotientGorensteinProjectiveStableCokernel`).
Both categories are triangulated: `HMF(S,w)` through the componentwise split Frobenius structure
on factorizations, and the stable category of Gorenstein-projectives by Happel's theorem.
This file shows that the cokernel functor is a triangle functor.

The cokernel functor on factorizations is exact for the two Frobenius structures.

* It preserves conflations. Let `X₁ ⟶ X₂ ⟶ X₃` be a short complex of factorizations which
  splits in both components. After reduction, the cokernels form a right exact sequence because
  the cokernel is right exact. The map `coker d₀'(X₁) ⟶ coker d₀'(X₂)` is injective because the
  reduction of `X₃` is exact at its even component, `ker d₀' = im d₁'`; this is the vanishing of
  the connecting map of the snake lemma
  (`TauCeti.MatrixFactorization.shortExact_map_cokernelFunctor_comp_forget₂`).
* It preserves projective-injectives. These are the contractible factorizations, and the
  cokernel of a null-homotopic map factors through a projective module, so the cokernel of a
  contractible factorization is projective.

Hence it induces a triangle functor between the stable categories
(`TauCeti.StableConflationExact.stableFunctorIsTriangulated`), which agrees with the descended
cokernel functor along the identification of the stable category of factorizations with
`HMF(S,w)`. The shift compatibility is transported along that identification, and with it the
cokernel functor `HMF(S,w) ⥤ stable(Gproj-S/(w))` is a triangle functor.

Only the non-zero-divisor hypothesis on `w` is used. Under Eisenbud's further hypotheses (`S`
regular local) this functor is an equivalence onto the stable category of maximal
Cohen–Macaulay modules; that is not proved here.

## Main definitions

In the namespace `TauCeti.MatrixFactorization.HomotopyCategory`:

* `quotientGorensteinProjectiveStableCokernelCommShift`: the compatibility of the cokernel
  functor `HMF(S,w) ⥤ stable(Gproj-S/(w))` with the shifts by `ℤ`.
* `stableToHomotopyInverseCompStableFunctorIso`: the cokernel functor on `HMF(S,w)` is the
  functor induced on stable categories, precomposed with the inverse of `stableToHomotopy`.

## Main results

* `TauCeti.MatrixFactorization.stableConflationExact_quotientGorensteinProjectiveCokernel`: the
  Gorenstein-projective cokernel functor preserves conflations and projective-injectives.
* `HomotopyCategory.stableToHomotopy_comp_quotientGorensteinProjectiveStableCokernel`, in the
  same namespace: the descended cokernel functor agrees with the induced functor on stable
  categories.
* `HomotopyCategory.quotientGorensteinProjectiveStableCokernel_isTriangulated`, in the same
  namespace: the cokernel functor `HMF(S,w) ⥤ stable(Gproj-S/(w))` is a triangle functor.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Sections 5–6.
* R.-O. Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Mathematical Surveys
  and Monographs **262** (2021), Section 4.
* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2: exact functors between Frobenius categories induce triangle
  functors.
-/

public section

noncomputable section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory Limits

variable {S : Type u} [CommRing S] {w : S}

/-! ### Exactness of the Gorenstein-projective cokernel functor -/

/-- For a non-zero-divisor `w`, the Gorenstein-projective cokernel functor is exact for the
componentwise split structure on matrix factorizations and the inherited structure on
Gorenstein-projective `S/(w)`-modules, and it sends contractible factorizations to projective
modules. -/
theorem stableConflationExact_quotientGorensteinProjectiveCokernel (hw : w ∈ nonZeroDivisors S) :
    StableConflationExact (splitExact S w)
      (GorensteinProjectiveModuleCat.exactStructure.{u} (S ⧸ Ideal.span {w}))
      (quotientGorensteinProjectiveCokernel hw) where
  isConflationExact := ⟨fun {T} hT ↦ by
    have hw₀ : Ideal.Quotient.mk (Ideal.span {w}) w = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self w)
    -- Extension of scalars carries the componentwise splittings of `T` to splittings of the
    -- components of its reduction.
    obtain ⟨⟨s₀⟩, ⟨s₁⟩⟩ := (splitExact_conflation_iff T).1 hT
    have e₀ := (s₀.map (forget₂ (FGModuleCat.{u} S) (ModuleCat.{u} S) ⋙
      ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {w})))).shortExact
    have e₁ := (s₁.map (forget₂ (FGModuleCat.{u} S) (ModuleCat.{u} S) ⋙
      ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {w})))).shortExact
    rw [GorensteinProjectiveModuleCat.exactStructure_conflation_iff, ← ShortComplex.map_comp]
    refine ShortComplex.shortExact_of_iso
      (T.mapNatIso (eqToIso (quotientGorensteinProjectiveCokernel_comp_ι hw).symm)) ?_
    exact shortExact_map_cokernelFunctor_comp_forget₂ hw₀
      (T := T.map (baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))))
      ((ModuleCat.mono_iff_injective _).1 e₁.mono_f)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 e₀.exact)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 e₁.exact)
      ((ModuleCat.epi_iff_surjective _).1 e₀.epi_g)
      ((ModuleCat.epi_iff_surjective _).1 e₁.epi_g)
      (exact_quotient_d₁_d₀ hw T.X₃)⟩
  map_projectiveInjective {X} hX := by
    -- A projective-injective factorization is contractible, and the cokernel of a null-homotopic
    -- map factors through a projective module.
    have h := quotientGorensteinProjectiveCokernel_map_mem_projectiveStableIdeal hw
      ((splitExact_isProjective_iff X).1 (((splitExact S w).projectiveInjective_iff X).1 hX).1)
    rw [CategoryTheory.Functor.map_id, ExactStructure.mem_projectiveStableIdeal_iff,
      ObjectProperty.factorsThrough_id_iff] at h
    exact (ExactStructure.projectiveInjective_iff _ _).2 ⟨h,
      (GorensteinProjectiveModuleCat.exactStructure_isFrobenius.projective_iff_injective _).1 h⟩

/-! ### The triangle functor on homotopy categories -/

namespace HomotopyCategory

/-- Along the identification of the componentwise split stable category of matrix factorizations
with `HMF(S,w)`, the Gorenstein-projective stable cokernel functor is the functor induced on
stable categories by the exact cokernel functor. -/
theorem stableToHomotopy_comp_quotientGorensteinProjectiveStableCokernel
    (hw : w ∈ nonZeroDivisors S) :
    stableToHomotopy S w ⋙ quotientGorensteinProjectiveStableCokernel hw =
      (stableConflationExact_quotientGorensteinProjectiveCokernel hw).stableFunctor
        (splitExact_isFrobenius S w) := by
  apply Quotient.lift_unique' (splitExact S w).projectiveStableIdeal.rel
  rw [StableConflationExact.stableFunctor_eq_map, MorphismIdeal.quotientFunctor_comp_map,
    ← Functor.assoc, projectiveStableFunctor_comp_stableToHomotopy,
    quotientFunctor_comp_quotientGorensteinProjectiveStableCokernel]

/-- The Gorenstein-projective stable cokernel functor is the inverse of the identification of the
componentwise split stable category with `HMF(S,w)`, followed by the functor induced on stable
categories by the exact cokernel functor. -/
def stableToHomotopyInverseCompStableFunctorIso (hw : w ∈ nonZeroDivisors S) :
    (stableToHomotopy S w).asEquivalence.inverse ⋙
        (stableConflationExact_quotientGorensteinProjectiveCokernel hw).stableFunctor
          (splitExact_isFrobenius S w) ≅
      quotientGorensteinProjectiveStableCokernel hw :=
  Iso.inverseCompIso
    (eqToIso (stableToHomotopy_comp_quotientGorensteinProjectiveStableCokernel hw).symm)

/-- The Gorenstein-projective stable cokernel functor commutes with the shifts by `ℤ`: the parity
shift on `HMF(S,w)` and the shift generated by stable suspension on Gorenstein-projectives. It is
transported along `stableToHomotopyInverseCompStableFunctorIso` from the shift compatibility of
the functor induced on stable categories. -/
@[instance_reducible]
def quotientGorensteinProjectiveStableCokernelCommShift (hw : w ∈ nonZeroDivisors S) :
    letI := (GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
      (A := S ⧸ Ideal.span {w})).stableHasShift
    (quotientGorensteinProjectiveStableCokernel hw).CommShift ℤ :=
  have hE := splitExact_isFrobenius S w
  have hE' := GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
    (A := S ⧸ Ideal.span {w})
  letI := hE.stableHasShift
  letI := hE'.stableHasShift
  letI : (stableToHomotopy S w).asEquivalence.functor.CommShift ℤ := stableToHomotopyCommShift S w
  letI := (stableToHomotopy S w).asEquivalence.commShiftInverse ℤ
  letI := (stableConflationExact_quotientGorensteinProjectiveCokernel hw).stableFunctorCommShift
    hE hE'
  Functor.CommShift.ofIso (stableToHomotopyInverseCompStableFunctorIso hw) ℤ

/-- The shift compatibility of the Gorenstein-projective stable cokernel functor is the one for
which `stableToHomotopyInverseCompStableFunctorIso` commutes with the shifts, the inverse of
`stableToHomotopy` carrying the shift compatibility inverse to `stableToHomotopyCommShift`. -/
theorem stableToHomotopyInverseCompStableFunctorIso_commShift (hw : w ∈ nonZeroDivisors S) :
    letI := (splitExact_isFrobenius S w).stableHasShift
    letI := (GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
      (A := S ⧸ Ideal.span {w})).stableHasShift
    letI : (stableToHomotopy S w).asEquivalence.functor.CommShift ℤ := stableToHomotopyCommShift S w
    letI := (stableToHomotopy S w).asEquivalence.commShiftInverse ℤ
    letI := (stableConflationExact_quotientGorensteinProjectiveCokernel hw).stableFunctorCommShift
      (splitExact_isFrobenius S w) GorensteinProjectiveModuleCat.exactStructure_isFrobenius
    letI := quotientGorensteinProjectiveStableCokernelCommShift hw
    NatTrans.CommShift (stableToHomotopyInverseCompStableFunctorIso hw).hom ℤ := by
  let := (splitExact_isFrobenius S w).stableHasShift
  let := (GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
    (A := S ⧸ Ideal.span {w})).stableHasShift
  let : (stableToHomotopy S w).asEquivalence.functor.CommShift ℤ := stableToHomotopyCommShift S w
  let := (stableToHomotopy S w).asEquivalence.commShiftInverse ℤ
  let := (stableConflationExact_quotientGorensteinProjectiveCokernel hw).stableFunctorCommShift
    (splitExact_isFrobenius S w) GorensteinProjectiveModuleCat.exactStructure_isFrobenius
  exact Functor.CommShift.ofIso_compatibility _ ℤ

/-- **The cokernel functor of matrix factorizations is a triangle functor.** For a
non-zero-divisor `w` of a commutative ring `S`, the functor `HMF(S,w) ⥤ stable(Gproj-S/(w))`
sending a matrix factorization to the cokernel of its reduction modulo `w` is a triangle functor
for the triangulation of `HMF(S,w)` by the parity shift and Happel's triangulation of the stable
category of Gorenstein-projective `S/(w)`-modules. -/
theorem quotientGorensteinProjectiveStableCokernel_isTriangulated (hw : w ∈ nonZeroDivisors S) :
    letI := (GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
      (A := S ⧸ Ideal.span {w})).stableHasShift
    letI := (GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
      (A := S ⧸ Ideal.span {w})).stableShiftFunctor_additive
    letI := (GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
      (A := S ⧸ Ideal.span {w})).stablePretriangulated
    letI := quotientGorensteinProjectiveStableCokernelCommShift hw
    (quotientGorensteinProjectiveStableCokernel hw).IsTriangulated := by
  have hE := splitExact_isFrobenius S w
  have hE' := GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
    (A := S ⧸ Ideal.span {w})
  let := hE.stableHasShift
  let := hE.stableShiftFunctor_additive
  let := hE.stablePretriangulated
  let := hE'.stableHasShift
  let := hE'.stableShiftFunctor_additive
  let := hE'.stablePretriangulated
  let : (stableToHomotopy S w).asEquivalence.functor.CommShift ℤ := stableToHomotopyCommShift S w
  let := (stableToHomotopy S w).asEquivalence.commShiftInverse ℤ
  let := (stableToHomotopy S w).asEquivalence.commShift_of_functor ℤ
  let := (stableConflationExact_quotientGorensteinProjectiveCokernel hw).stableFunctorCommShift
    hE hE'
  let := quotientGorensteinProjectiveStableCokernelCommShift hw
  -- The inverse of the triangulated equivalence `stableToHomotopy` is a triangle functor, and so
  -- is the functor induced on stable categories by the exact cokernel functor.
  have : (stableToHomotopy S w).asEquivalence.IsTriangulated :=
    Equivalence.IsTriangulated.mk' _ (stableToHomotopy_isTriangulated S w)
  have :=
    (stableConflationExact_quotientGorensteinProjectiveCokernel hw).stableFunctorIsTriangulated
      hE hE'
  have := stableToHomotopyInverseCompStableFunctorIso_commShift hw
  exact Functor.isTriangulated_of_iso (stableToHomotopyInverseCompStableFunctorIso hw)

end HomotopyCategory

end TauCeti.MatrixFactorization
