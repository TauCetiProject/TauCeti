/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.GorensteinProjective.FGModuleCat
public import TauCeti.CategoryTheory.Triangulated.Equivalence
public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Equivalence
public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Singularity
public import TauCeti.RingTheory.RegularLocalRing.IwanagaGorenstein
public import TauCeti.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Polynomial.Coeff

/-!
# Matrix factorizations and the singularity category of a hypersurface (Eisenbud, Orlov)

For `w ∈ nonZeroDivisors S` with Noetherian quotient `R = S ⧸ (w)`,
`quotientSingularityCokernel : HMF(S, w) ⥤ D_sg(mod-R)` factors through
`quotientGorensteinProjectiveStableCokernel` and Chen's functor
`TauCeti.GorensteinProjectiveModuleCat.toSingularityCategory R`
(`quotientGorensteinProjectiveStableCokernelCompToSingularityCategoryIso`), making it a triangle
functor (`quotientSingularityCokernel_isTriangulated`).

Over a Noetherian ring `S` of finite global dimension, Eisenbud–Buchweitz and Buchweitz's theorem
(`TauCeti.IsIwanagaGorenstein.quotient_span_singleton`) make `quotientSingularityCokernel` a
triangle equivalence (`quotientSingularityCokernelEquivalence`), specializing to regular rings of
finite Krull dimension
(`quotientSingularityCokernel_isEquivalence_of_isRegularRing_of_ringKrullDim_lt_top`), **Eisenbud's
singularity equivalence** (`quotientSingularityCokernel_isEquivalence_of_isRegularLocalRing`, with
triangulated `.asEquivalence` via `quotientSingularityCokernel_asEquivalence_isTriangulated`), and
**Orlov's affine theorem** (`quotientSingularityCokernelEquivalenceOfFlatPolynomial`) for a flat
morphism `φ : k[X] →+* S` sending `X` to `w` (`RingHom.Flat.map_mem_nonZeroDivisors`).

## References

* D. Orlov, *Triangulated categories of singularities and D-branes in Landau–Ginzburg models*,
  Proc. Steklov Inst. Math. **246** (2004), Theorem 3.9.
* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Theorem 6.1.
* R.-O. Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, AMS (2021), Theorem 4.4.1.
* Xiao-Wu Chen, *Relative singularity categories and Gorenstein-projective modules*, Math. Nachr.
  **284** (2011), 199–212.
-/

public section

noncomputable section

universe v u w

namespace TauCeti.MatrixFactorization.HomotopyCategory

open CategoryTheory

section Comparison

variable {S : Type u} [CommRing S] {w : S} [IsNoetherianRing (S ⧸ Ideal.span {w})]

/-- Viewing `quotientGorensteinProjectiveCokernel` inside `FGModuleCat (S ⧸ (w))` recovers base
change modulo `w` followed by `cokernelFunctor`. -/
theorem quotientGorensteinProjectiveCokernel_comp_toFGModuleCat_comp_ι
    (hw : w ∈ nonZeroDivisors S) :
    (quotientGorensteinProjectiveCokernel hw ⋙
        GorensteinProjectiveModuleCat.toFGModuleCat (S ⧸ Ideal.span {w})) ⋙
        (isGorensteinProjective (FGModuleCat.{u} (S ⧸ Ideal.span {w}))).ι =
      baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w})) ⋙ cokernelFunctor := by
  let R := S ⧸ Ideal.span {w}
  have h : ((quotientGorensteinProjectiveCokernel hw ⋙
        GorensteinProjectiveModuleCat.toFGModuleCat R) ⋙
        (isGorensteinProjective (FGModuleCat.{u} R)).ι) ⋙
        forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R) =
      (baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w})) ⋙ cokernelFunctor) ⋙
        forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R) := by
    rw [Functor.assoc, Functor.assoc,
      GorensteinProjectiveModuleCat.toFGModuleCat_comp_ι_comp_forget₂,
      quotientGorensteinProjectiveCokernel_comp_ι hw]; rfl
  refine CategoryTheory.Functor.ext
    (fun X ↦ ObjectProperty.FullSubcategory.ext (Functor.congr_obj h X))
    fun X Y g ↦ (ModuleCat.isFG R).fullyFaithfulι.map_injective ?_
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  exact Functor.congr_hom h g

variable [HasDerivedCategory.{v} (FGModuleCat.{u} (S ⧸ Ideal.span {w}))]

/-- **Factorization of `quotientSingularityCokernel`** through `stable(Gproj-S/(w))`. -/
theorem quotientGorensteinProjectiveStableCokernel_comp_toSingularityCategory
    (hw : w ∈ nonZeroDivisors S) :
    quotientGorensteinProjectiveStableCokernel hw ⋙
        GorensteinProjectiveModuleCat.toSingularityCategory.{v, u} (S ⧸ Ideal.span {w}) =
      quotientSingularityCokernel.{v, u} (S := S) (w := w) := by
  apply Quotient.lift_unique'
  rw [← Functor.assoc, quotientFunctor_comp_quotientGorensteinProjectiveStableCokernel,
    Functor.assoc, GorensteinProjectiveModuleCat.projectiveStableFunctor_comp_toSingularityCategory,
    GorensteinProjective.toSingularityCategoryFunctor, ← Functor.assoc, ← Functor.assoc,
    quotientGorensteinProjectiveCokernel_comp_toFGModuleCat_comp_ι hw,
    quotientFunctor_comp_quotientSingularityCokernel]
  simp only [Functor.assoc]

/-- Natural isomorphism factoring `quotientSingularityCokernel` via `stable(Gproj-S/(w))`. -/
def quotientGorensteinProjectiveStableCokernelCompToSingularityCategoryIso
    (hw : w ∈ nonZeroDivisors S) :
    quotientGorensteinProjectiveStableCokernel hw ⋙
        GorensteinProjectiveModuleCat.toSingularityCategory.{v, u} (S ⧸ Ideal.span {w}) ≅
      quotientSingularityCokernel.{v, u} (S := S) (w := w) :=
  eqToIso (quotientGorensteinProjectiveStableCokernel_comp_toSingularityCategory.{v, u} hw)

@[simp] theorem quotientGorensteinProjectiveStableCokernelCompToSingularityCategoryIso_hom
    (hw : w ∈ nonZeroDivisors S) :
    (quotientGorensteinProjectiveStableCokernelCompToSingularityCategoryIso.{v, u} hw).hom =
      eqToHom (quotientGorensteinProjectiveStableCokernel_comp_toSingularityCategory.{v, u} hw) :=
  (rfl)
@[simp] theorem quotientGorensteinProjectiveStableCokernelCompToSingularityCategoryIso_inv
    (hw : w ∈ nonZeroDivisors S) :
    (quotientGorensteinProjectiveStableCokernelCompToSingularityCategoryIso.{v, u} hw).inv =
      eqToHom
        (quotientGorensteinProjectiveStableCokernel_comp_toSingularityCategory.{v, u} hw).symm :=
  (rfl)

/-- Shift compatibility for `quotientSingularityCokernel`, transported via `stable(Gproj-S/(w))`. -/
@[instance_reducible] def quotientSingularityCokernelCommShift (hw : w ∈ nonZeroDivisors S) :
    (quotientSingularityCokernel.{v, u} (S := S) (w := w)).CommShift ℤ := by
  let := (GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
    (A := S ⧸ Ideal.span {w})).stableHasShift
  let := quotientGorensteinProjectiveStableCokernelCommShift hw
  let := GorensteinProjectiveModuleCat.toSingularityCategoryCommShift.{v, u} (S ⧸ Ideal.span {w})
  exact Functor.CommShift.ofIso
    (quotientGorensteinProjectiveStableCokernelCompToSingularityCategoryIso.{v, u} hw) ℤ

/-- Shift comparison of `quotientSingularityCokernel` via `stable(Gproj-S/(w))`. -/
theorem quotientSingularityCokernel_commShiftIso (hw : w ∈ nonZeroDivisors S) (n : ℤ) :
    letI := (GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
      (A := S ⧸ Ideal.span {w})).stableHasShift
    letI := quotientGorensteinProjectiveStableCokernelCommShift hw
    letI := GorensteinProjectiveModuleCat.toSingularityCategoryCommShift.{v, u} (S ⧸ Ideal.span {w})
    letI := quotientSingularityCokernelCommShift.{v, u} hw
    (quotientSingularityCokernel.{v, u} (S := S) (w := w)).commShiftIso n =
      Functor.isoWhiskerLeft (shiftFunctor (HomotopyCategory (S := S) (w := w)) n)
        (quotientGorensteinProjectiveStableCokernelCompToSingularityCategoryIso.{v, u} hw).symm ≪≫
      (quotientGorensteinProjectiveStableCokernel hw ⋙
        GorensteinProjectiveModuleCat.toSingularityCategory.{v, u}
          (S ⧸ Ideal.span {w})).commShiftIso n ≪≫
      Functor.isoWhiskerRight
        (quotientGorensteinProjectiveStableCokernelCompToSingularityCategoryIso.{v, u} hw)
        (shiftFunctor (SingularityCategory (FGModuleCat.{u} (S ⧸ Ideal.span {w}))) n) := (rfl)

/-- **The singularity-category cokernel functor is a triangle functor.** -/
theorem quotientSingularityCokernel_isTriangulated (hw : w ∈ nonZeroDivisors S) :
    letI := quotientSingularityCokernelCommShift.{v, u} hw
    (quotientSingularityCokernel.{v, u} (S := S) (w := w)).IsTriangulated := by
  have hE' := GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
    (A := S ⧸ Ideal.span {w})
  let := hE'.stableHasShift; let := hE'.stableShiftFunctor_additive
  let := hE'.stablePretriangulated; let := quotientGorensteinProjectiveStableCokernelCommShift hw
  have := quotientGorensteinProjectiveStableCokernel_isTriangulated hw
  let := GorensteinProjectiveModuleCat.toSingularityCategoryCommShift.{v, u} (S ⧸ Ideal.span {w})
  have := GorensteinProjectiveModuleCat.toSingularityCategory_isTriangulated.{v, u}
    (S ⧸ Ideal.span {w})
  let := quotientSingularityCokernelCommShift.{v, u} hw
  have := Functor.CommShift.ofIso_compatibility
    (quotientGorensteinProjectiveStableCokernelCompToSingularityCategoryIso.{v, u} hw) ℤ
  exact Functor.isTriangulated_of_iso
    (quotientGorensteinProjectiveStableCokernelCompToSingularityCategoryIso.{v, u} hw)

/-- Any equivalence `E : HMF(S, w) ≌ D_sg(mod-S/(w))` with `E.functor = quotientSingularityCokernel`
is a triangulated equivalence. -/
theorem isTriangulated_of_functor_eq_quotientSingularityCokernel (hw : w ∈ nonZeroDivisors S)
    (E : HomotopyCategory (S := S) (w := w) ≌
      SingularityCategory (FGModuleCat.{u} (S ⧸ Ideal.span {w})))
    (hE : E.functor = quotientSingularityCokernel.{v, u} (S := S) (w := w)) :
    letI := quotientSingularityCokernelCommShift.{v, u} hw
    letI : E.functor.CommShift ℤ := Functor.CommShift.ofIso (eqToIso hE.symm) ℤ
    letI := E.commShiftInverse ℤ; letI := E.commShift_of_functor ℤ
    E.IsTriangulated := by
  let := quotientSingularityCokernelCommShift.{v, u} hw
  have := quotientSingularityCokernel_isTriangulated.{v, u} hw
  exact E.isTriangulated_of_functor_eq hE

/-- When `quotientSingularityCokernel` is an equivalence, its `.asEquivalence` is triangulated. -/
theorem quotientSingularityCokernel_asEquivalence_isTriangulated (hw : w ∈ nonZeroDivisors S)
    [(quotientSingularityCokernel.{v, u} (S := S) (w := w)).IsEquivalence] :
    letI := quotientSingularityCokernelCommShift.{v, u} hw
    letI : (quotientSingularityCokernel.{v, u} (S := S) (w := w)).asEquivalence.functor.CommShift
        ℤ := Functor.CommShift.ofIso (eqToIso (Functor.asEquivalence_functor _).symm) ℤ
    letI := (quotientSingularityCokernel.{v, u} (S := S) (w := w)).asEquivalence.commShiftInverse ℤ
    letI := (quotientSingularityCokernel.{v, u}
      (S := S) (w := w)).asEquivalence.commShift_of_functor ℤ
    (quotientSingularityCokernel.{v, u} (S := S) (w := w)).asEquivalence.IsTriangulated :=
  isTriangulated_of_functor_eq_quotientSingularityCokernel.{v, u} hw _
    (Functor.asEquivalence_functor _)

end Comparison

section Equivalence

variable {S : Type u} [CommRing S] {w : S}

section Noetherian
variable [IsNoetherianRing S] [HasDerivedCategory.{v} (FGModuleCat.{u} (S ⧸ Ideal.span {w}))]

/-- **Singularity equivalence in finite global dimension.** -/
theorem quotientSingularityCokernel_isEquivalence (hw : w ∈ nonZeroDivisors S)
    (d : ℕ) (hd : ∀ N : ModuleCat.{u} S, HasProjectiveDimensionLE N d) :
    (quotientSingularityCokernel.{v, u} (S := S) (w := w)).IsEquivalence := by
  have : IsIwanagaGorenstein S := .of_hasProjectiveDimensionLE S d hd
  have : IsIwanagaGorenstein (S ⧸ Ideal.span {w}) := .quotient_span_singleton hw
  have := quotientGorensteinProjectiveStableCokernel_isEquivalence hw d hd
  exact Functor.isEquivalence_of_iso
    (quotientGorensteinProjectiveStableCokernelCompToSingularityCategoryIso.{v, u} hw)

/-- Equivalence `HMF(S, w) ≌ D_sg(mod-S/(w))` over a Noetherian ring of finite global dimension. -/
def quotientSingularityCokernelEquivalence (hw : w ∈ nonZeroDivisors S) (d : ℕ)
    (hd : ∀ N : ModuleCat.{u} S, HasProjectiveDimensionLE N d) :
    HomotopyCategory (S := S) (w := w) ≌
      SingularityCategory (FGModuleCat.{u} (S ⧸ Ideal.span {w})) :=
  haveI := quotientSingularityCokernel_isEquivalence.{v, u} hw d hd
  (quotientSingularityCokernel.{v, u} (S := S) (w := w)).asEquivalence

@[simp] theorem quotientSingularityCokernelEquivalence_functor (hw : w ∈ nonZeroDivisors S) (d : ℕ)
    (hd : ∀ N : ModuleCat.{u} S, HasProjectiveDimensionLE N d) :
    (quotientSingularityCokernelEquivalence.{v, u} hw d hd).functor =
      quotientSingularityCokernel.{v, u} (S := S) (w := w) := (rfl)

/-- **The singularity-category cokernel equivalence is triangulated.** -/
theorem quotientSingularityCokernelEquivalence_isTriangulated (hw : w ∈ nonZeroDivisors S) (d : ℕ)
    (hd : ∀ N : ModuleCat.{u} S, HasProjectiveDimensionLE N d) :
    letI := quotientSingularityCokernelCommShift.{v, u} hw
    letI : (quotientSingularityCokernelEquivalence.{v, u} hw d hd).functor.CommShift ℤ :=
      Functor.CommShift.ofIso
        (eqToIso (quotientSingularityCokernelEquivalence_functor.{v, u} hw d hd).symm) ℤ
    letI := (quotientSingularityCokernelEquivalence.{v, u} hw d hd).commShiftInverse ℤ
    letI := (quotientSingularityCokernelEquivalence.{v, u} hw d hd).commShift_of_functor ℤ
    (quotientSingularityCokernelEquivalence.{v, u} hw d hd).IsTriangulated :=
  isTriangulated_of_functor_eq_quotientSingularityCokernel.{v, u} hw _
    (quotientSingularityCokernelEquivalence_functor.{v, u} hw d hd)

end Noetherian

/-- **Singularity equivalence over a regular ring of finite Krull dimension.** -/
theorem quotientSingularityCokernel_isEquivalence_of_isRegularRing_of_ringKrullDim_lt_top
    [IsRegularRing S] [HasDerivedCategory.{v} (FGModuleCat.{u} (S ⧸ Ideal.span {w}))]
    (hdim : ringKrullDim S < ⊤) (hw : w ∈ nonZeroDivisors S) :
    (quotientSingularityCokernel.{v, u} (S := S) (w := w)).IsEquivalence := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim S ≤ d := by
    cases h : ringKrullDim S with
    | bot => exact ⟨0, bot_le⟩
    | coe e => lift e to ℕ using fun he ↦ hdim.ne (by simp [h, he]); exact ⟨e, le_rfl⟩
  exact quotientSingularityCokernel_isEquivalence.{v, u} hw d
    (IsRegularRing.hasProjectiveDimensionLE hd)

/-- **Eisenbud's singularity equivalence** over a regular local ring `S`. -/
theorem quotientSingularityCokernel_isEquivalence_of_isRegularLocalRing [IsRegularLocalRing S]
    [HasDerivedCategory.{v} (FGModuleCat.{u} (S ⧸ Ideal.span {w}))] (hw : w ∈ nonZeroDivisors S) :
    (quotientSingularityCokernel.{v, u} (S := S) (w := w)).IsEquivalence :=
  quotientSingularityCokernel_isEquivalence_of_isRegularRing_of_ringKrullDim_lt_top.{v, u}
    ((_root_.IsRegularLocalRing.spanFinrank_maximalIdeal (R := S)).symm.trans_lt
      (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _))) hw

section FlatPolynomial
variable [IsRegularRing S] [HasDerivedCategory.{v} (FGModuleCat.{u} (S ⧸ Ideal.span {w}))]

/-- **Orlov's affine theorem** (Orlov, Theorem 3.9): for `[IsRegularRing S]` with
`ringKrullDim S < ⊤` and a flat morphism `φ : k[X] →+* S` sending `X` to `w`,
`quotientSingularityCokernel : HMF(S, w) ⥤ D_sg(mod-S/(w))` is an equivalence of categories. -/
theorem quotientSingularityCokernel_isEquivalence_of_flat_polynomial
    (hdim : ringKrullDim S < ⊤) {k : Type w} [CommRing k] {φ : Polynomial k →+* S}
    (hφ : φ.Flat) (hw : φ Polynomial.X = w) :
    (quotientSingularityCokernel.{v, u} (S := S) (w := w)).IsEquivalence :=
  quotientSingularityCokernel_isEquivalence_of_isRegularRing_of_ringKrullDim_lt_top.{v, u} hdim
    (hw ▸ hφ.map_mem_nonZeroDivisors Polynomial.X_mem_nonZeroDivisors)

/-- Equivalence `HMF(S, w) ≌ D_sg(mod-S/(w))` of Orlov's affine theorem. -/
def quotientSingularityCokernelEquivalenceOfFlatPolynomial
    (hdim : ringKrullDim S < ⊤) {k : Type w} [CommRing k] {φ : Polynomial k →+* S}
    (hφ : φ.Flat) (hw : φ Polynomial.X = w) :
    HomotopyCategory (S := S) (w := w) ≌
      SingularityCategory (FGModuleCat.{u} (S ⧸ Ideal.span {w})) :=
  haveI := quotientSingularityCokernel_isEquivalence_of_flat_polynomial.{v, u, w} hdim hφ hw
  (quotientSingularityCokernel.{v, u} (S := S) (w := w)).asEquivalence

@[simp] theorem quotientSingularityCokernelEquivalenceOfFlatPolynomial_functor
    (hdim : ringKrullDim S < ⊤) {k : Type w} [CommRing k] {φ : Polynomial k →+* S}
    (hφ : φ.Flat) (hw : φ Polynomial.X = w) :
    (quotientSingularityCokernelEquivalenceOfFlatPolynomial.{v, u, w} hdim hφ hw).functor =
      quotientSingularityCokernel.{v, u} (S := S) (w := w) := (rfl)

/-- **Orlov's affine equivalence is triangulated.** -/
theorem quotientSingularityCokernelEquivalenceOfFlatPolynomial_isTriangulated
    (hdim : ringKrullDim S < ⊤) {k : Type w} [CommRing k] {φ : Polynomial k →+* S}
    (hφ : φ.Flat) (hw : φ Polynomial.X = w) :
    letI := quotientSingularityCokernelCommShift.{v, u}
      (hw ▸ hφ.map_mem_nonZeroDivisors Polynomial.X_mem_nonZeroDivisors)
    letI : (quotientSingularityCokernelEquivalenceOfFlatPolynomial.{v, u, w}
        hdim hφ hw).functor.CommShift ℤ := Functor.CommShift.ofIso
      (eqToIso (quotientSingularityCokernelEquivalenceOfFlatPolynomial_functor.{v, u, w}
        hdim hφ hw).symm) ℤ
    letI := (quotientSingularityCokernelEquivalenceOfFlatPolynomial.{v, u, w}
      hdim hφ hw).commShiftInverse ℤ
    letI := (quotientSingularityCokernelEquivalenceOfFlatPolynomial.{v, u, w}
      hdim hφ hw).commShift_of_functor ℤ
    (quotientSingularityCokernelEquivalenceOfFlatPolynomial.{v, u, w} hdim hφ hw).IsTriangulated :=
  isTriangulated_of_functor_eq_quotientSingularityCokernel.{v, u}
    (hw ▸ hφ.map_mem_nonZeroDivisors Polynomial.X_mem_nonZeroDivisors) _
    (quotientSingularityCokernelEquivalenceOfFlatPolynomial_functor.{v, u, w} hdim hφ hw)

end FlatPolynomial

end Equivalence

end TauCeti.MatrixFactorization.HomotopyCategory
