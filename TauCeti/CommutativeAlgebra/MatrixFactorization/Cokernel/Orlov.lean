/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.GorensteinProjective.FGModuleCat
public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Equivalence
public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Singularity
public import TauCeti.RingTheory.IwanagaGorenstein
public import TauCeti.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Polynomial.Coeff

/-!
# Matrix factorizations and the singularity category of a hypersurface (Eisenbud, Orlov)

Let `w` be a non-zero-divisor of a commutative ring `S` and put `R = S ⧸ (w)`. When `R` is
noetherian, three triangulated categories sit in a comparison diagram:

```text
  HMF(S, w) ───quotientGorensteinProjectiveStableCokernel───▶ stable(Gproj-R)
      │                                                              │
      └──────────────quotientSingularityCokernel──────────────▶ D_sg(mod-R)
```

where the vertical arrow is Chen's functor
`TauCeti.GorensteinProjectiveModuleCat.toSingularityCategory R` placing a Gorenstein-projective
`R`-module in degree zero. Both functors out of `HMF(S, w)` send a matrix factorization `X` to the
reduced cokernel `coker d₀'` placed in degree zero, so the diagram commutes up to a canonical
natural isomorphism (`quotientGorensteinProjectiveStableCokernelCompToSingularityCategoryIso`).

Since `quotientGorensteinProjectiveStableCokernel` and `toSingularityCategory` are both triangle
functors, transporting their composite `CommShift ℤ` along this isomorphism equips
`quotientSingularityCokernel` with shift compatibility and proves that it is a triangle functor
(`quotientSingularityCokernel_isTriangulated`), requiring only `w ∈ nonZeroDivisors S` and
`IsNoetherianRing R`.

When `S` is noetherian of finite global dimension:

1. `quotientGorensteinProjectiveStableCokernel` is a triangle equivalence
   (`quotientGorensteinProjectiveStableCokernel_isEquivalence`, Eisenbud–Buchweitz);
2. `S` is Iwanaga–Gorenstein (`TauCeti.IsIwanagaGorenstein.of_hasProjectiveDimensionLE`), hence the
   hypersurface `R = S ⧸ (w)` is Iwanaga–Gorenstein
   (`TauCeti.IsIwanagaGorenstein.quotient_span_singleton`), so Chen's functor is a triangle
   equivalence (`TauCeti.GorensteinProjectiveModuleCat.isEquivalence_toSingularityCategory`,
   Buchweitz's theorem).

Combining (1) and (2) makes `quotientSingularityCokernel : HMF(S, w) ⥤ D_sg(mod-R)` a triangle
equivalence (`quotientSingularityCokernel_isEquivalence`). Specializing to regular ambient rings of
finite Krull dimension yields:

* **Eisenbud's singularity equivalence**
  (`quotientSingularityCokernel_isEquivalence_of_isRegularLocalRing`) over a regular local ring `S`;
* **Orlov's affine theorem** (`quotientSingularityCokernel_isEquivalence_of_flat_polynomial`): for a
  regular ring `S` of finite Krull dimension and a flat ring homomorphism `φ : k[X] →+* S` sending
  `X` to `w` (an affine Landau–Ginzburg model `Spec S → A¹_k` with flat potential `w`), `X` is a
  nonzerodivisor in `k[X]` over *any* commutative ring `k` (`Polynomial.X_mem_nonZeroDivisors`),
  flatness transports it to `w ∈ nonZeroDivisors S` (`RingHom.Flat.map_mem_nonZeroDivisors`), and
  `HMF(S, w) ≌ D_sg(mod-S/(w))` as triangulated categories. Notice that neither `IsDomain k` nor
  `w ≠ 0` needs to be assumed separately: if `w = 0`, flatness of `φ` forces `S` to be the zero
  ring, where both categories are zero.

## Main definitions and results

In `TauCeti.MatrixFactorization.HomotopyCategory`:

* `quotientGorensteinProjectiveStableCokernel_comp_toSingularityCategory` and
  `quotientGorensteinProjectiveStableCokernelCompToSingularityCategoryIso`: the factorization of
  `quotientSingularityCokernel` through `stable(Gproj-S/(w))`.
* `quotientSingularityCokernelCommShift` and `quotientSingularityCokernel_isTriangulated`: shift
  compatibility and triangle-functor structure on `quotientSingularityCokernel`.
* `quotientSingularityCokernel_isEquivalence`, `quotientSingularityCokernelEquivalence`, and
  `quotientSingularityCokernelEquivalence_isTriangulated`: the singularity equivalence in finite
  global dimension.
* `quotientSingularityCokernel_isEquivalence_of_isRegularRing` and
  `quotientSingularityCokernel_isEquivalence_of_isRegularLocalRing`: regular-ring and regular-local
  specializations.
* `quotientSingularityCokernel_isEquivalence_of_flat_polynomial`,
  `quotientSingularityCokernelEquivalenceOfFlatPolynomial`, and
  `quotientSingularityCokernelEquivalenceOfFlatPolynomial_isTriangulated`: **Orlov's affine
  theorem**.

## References

* D. Orlov, *Triangulated categories of singularities and D-branes in Landau–Ginzburg models*,
  Proc. Steklov Inst. Math. **246** (2004), Theorem 3.9.
* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Theorem 6.1.
* R.-O. Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Mathematical Surveys and
  Monographs **262**, American Mathematical Society (2021), Theorem 4.4.1.
* Xiao-Wu Chen, *Relative singularity categories and Gorenstein-projective modules*, Math. Nachr.
  **284** (2011), 199–212.
-/

public section

noncomputable section

universe v u w

namespace TauCeti.MatrixFactorization.HomotopyCategory

open CategoryTheory

section Comparison

variable {S : Type u} [CommRing S] {w : S}
  [IsNoetherianRing (S ⧸ Ideal.span {w})]

private theorem quotientGorensteinProjectiveCokernel_comp_toFGModuleCat_comp_ι
    (hw : w ∈ nonZeroDivisors S) :
    (quotientGorensteinProjectiveCokernel hw ⋙
        GorensteinProjectiveModuleCat.toFGModuleCat (S ⧸ Ideal.span {w})) ⋙
        (CategoryTheory.isGorensteinProjective
          (FGModuleCat.{u} (S ⧸ Ideal.span {w}))).ι =
      baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w})) ⋙ cokernelFunctor := by
  have h : ((quotientGorensteinProjectiveCokernel hw ⋙
        GorensteinProjectiveModuleCat.toFGModuleCat (S ⧸ Ideal.span {w})) ⋙
        (CategoryTheory.isGorensteinProjective
          (FGModuleCat.{u} (S ⧸ Ideal.span {w}))).ι) ⋙
        forget₂ (FGModuleCat.{u} (S ⧸ Ideal.span {w}))
          (ModuleCat.{u} (S ⧸ Ideal.span {w})) =
      (baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w})) ⋙ cokernelFunctor) ⋙
        forget₂ (FGModuleCat.{u} (S ⧸ Ideal.span {w}))
          (ModuleCat.{u} (S ⧸ Ideal.span {w})) := by
    rw [Functor.assoc, Functor.assoc,
      GorensteinProjectiveModuleCat.toFGModuleCat_comp_ι_comp_forget₂,
      quotientGorensteinProjectiveCokernel_comp_ι hw]
    rfl
  refine CategoryTheory.Functor.ext
    (fun X ↦ ObjectProperty.FullSubcategory.ext (Functor.congr_obj h X)) fun X Y g ↦ ?_
  apply (ModuleCat.isFG (S ⧸ Ideal.span {w})).fullyFaithfulι.map_injective
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  exact Functor.congr_hom h g

variable [HasDerivedCategory.{v} (FGModuleCat.{u} (S ⧸ Ideal.span {w}))]

/-- **Factorization of the singularity-category cokernel functor.** For a nonzerodivisor `w`,
`quotientSingularityCokernel : HMF(S, w) ⥤ D_sg(mod-S/(w))` equals
`quotientGorensteinProjectiveStableCokernel` followed by Chen's functor `toSingularityCategory`. -/
theorem quotientGorensteinProjectiveStableCokernel_comp_toSingularityCategory
    (hw : w ∈ nonZeroDivisors S) :
    quotientGorensteinProjectiveStableCokernel hw ⋙
        GorensteinProjectiveModuleCat.toSingularityCategory.{v, u} (S ⧸ Ideal.span {w}) =
      quotientSingularityCokernel.{v, u} (S := S) (w := w) := by
  apply CategoryTheory.Quotient.lift_unique'
  rw [← Functor.assoc, quotientFunctor_comp_quotientGorensteinProjectiveStableCokernel,
    Functor.assoc, GorensteinProjectiveModuleCat.projectiveStableFunctor_comp_toSingularityCategory,
    CategoryTheory.GorensteinProjective.toSingularityCategoryFunctor, ← Functor.assoc,
    ← Functor.assoc, quotientGorensteinProjectiveCokernel_comp_toFGModuleCat_comp_ι hw,
    quotientFunctor_comp_quotientSingularityCokernel]
  simp only [Functor.assoc]

/-- The natural isomorphism witnessing the factorization
`quotientGorensteinProjectiveStableCokernel ⋙ toSingularityCategory ≅ quotientSingularityCokernel`.
-/
def quotientGorensteinProjectiveStableCokernelCompToSingularityCategoryIso
    (hw : w ∈ nonZeroDivisors S) :
    quotientGorensteinProjectiveStableCokernel hw ⋙
        GorensteinProjectiveModuleCat.toSingularityCategory.{v, u} (S ⧸ Ideal.span {w}) ≅
      quotientSingularityCokernel.{v, u} (S := S) (w := w) :=
  eqToIso (quotientGorensteinProjectiveStableCokernel_comp_toSingularityCategory.{v, u} hw)

/-- Shift compatibility for `quotientSingularityCokernel : HMF(S, w) ⥤ D_sg(mod-S/(w))`,
transported from the composite through `stable(Gproj-S/(w))`. -/
@[instance_reducible]
def quotientSingularityCokernelCommShift (hw : w ∈ nonZeroDivisors S) :
    (quotientSingularityCokernel.{v, u} (S := S) (w := w)).CommShift ℤ := by
  let hE' := GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
    (A := S ⧸ Ideal.span {w})
  let := hE'.stableHasShift
  let := quotientGorensteinProjectiveStableCokernelCommShift hw
  let := GorensteinProjectiveModuleCat.toSingularityCategoryCommShift.{v, u} (S ⧸ Ideal.span {w})
  exact Functor.CommShift.ofIso
    (quotientGorensteinProjectiveStableCokernelCompToSingularityCategoryIso.{v, u} hw) ℤ

/-- The comparison isomorphism factoring `quotientSingularityCokernel` through
`stable(Gproj-S/(w))` respects shifts. -/
theorem quotientGorensteinProjectiveStableCokernelCompToSingularityCategoryIso_commShift
    (hw : w ∈ nonZeroDivisors S) :
    letI := (GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
      (A := S ⧸ Ideal.span {w})).stableHasShift
    letI := quotientGorensteinProjectiveStableCokernelCommShift hw
    letI := GorensteinProjectiveModuleCat.toSingularityCategoryCommShift.{v, u}
      (S ⧸ Ideal.span {w})
    letI := quotientSingularityCokernelCommShift.{v, u} hw
    (quotientGorensteinProjectiveStableCokernelCompToSingularityCategoryIso.{v, u}
      hw).hom.CommShift ℤ := by
  let hE' := GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
    (A := S ⧸ Ideal.span {w})
  let := hE'.stableHasShift
  let := quotientGorensteinProjectiveStableCokernelCommShift hw
  let := GorensteinProjectiveModuleCat.toSingularityCategoryCommShift.{v, u} (S ⧸ Ideal.span {w})
  let := quotientSingularityCokernelCommShift.{v, u} hw
  have := Functor.CommShift.ofIso_compatibility
    (quotientGorensteinProjectiveStableCokernelCompToSingularityCategoryIso.{v, u} hw) ℤ
  infer_instance

/-- **The singularity-category cokernel functor is a triangle functor.** Only
`w ∈ nonZeroDivisors S` and `IsNoetherianRing (S ⧸ (w))` are needed. -/
theorem quotientSingularityCokernel_isTriangulated (hw : w ∈ nonZeroDivisors S) :
    letI := quotientSingularityCokernelCommShift.{v, u} hw
    (quotientSingularityCokernel.{v, u} (S := S) (w := w)).IsTriangulated := by
  let hE' := GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
    (A := S ⧸ Ideal.span {w})
  let := hE'.stableHasShift
  let := hE'.stableShiftFunctor_additive
  let := hE'.stablePretriangulated
  let := quotientGorensteinProjectiveStableCokernelCommShift hw
  have := quotientGorensteinProjectiveStableCokernel_isTriangulated hw
  let := GorensteinProjectiveModuleCat.toSingularityCategoryCommShift.{v, u} (S ⧸ Ideal.span {w})
  have := GorensteinProjectiveModuleCat.toSingularityCategory_isTriangulated.{v, u}
    (S ⧸ Ideal.span {w})
  let := quotientSingularityCokernelCommShift.{v, u} hw
  have := quotientGorensteinProjectiveStableCokernelCompToSingularityCategoryIso_commShift.{v, u}
    hw
  exact Functor.isTriangulated_of_iso
    (quotientGorensteinProjectiveStableCokernelCompToSingularityCategoryIso.{v, u} hw)

end Comparison

/-! ### Singularity equivalences in finite global dimension, for regular rings, and for Orlov's
affine Landau–Ginzburg models -/

section Equivalence

variable {S : Type u} [CommRing S] {w : S}

/-- **Singularity equivalence in finite global dimension.** Let `S` be a noetherian commutative
ring of finite global dimension and let `w` be a nonzerodivisor of `S`. Then
`quotientSingularityCokernel : HMF(S, w) ⥤ D_sg(mod-S/(w))` is an equivalence of categories. -/
theorem quotientSingularityCokernel_isEquivalence [IsNoetherianRing S]
    [HasDerivedCategory.{v} (FGModuleCat.{u} (S ⧸ Ideal.span {w}))]
    (hw : w ∈ nonZeroDivisors S) (d : ℕ)
    (hd : ∀ N : ModuleCat.{u} S, HasProjectiveDimensionLE N d) :
    (quotientSingularityCokernel.{v, u} (S := S) (w := w)).IsEquivalence := by
  have : IsIwanagaGorenstein S := .of_hasProjectiveDimensionLE S d hd
  have : IsIwanagaGorenstein (S ⧸ Ideal.span {w}) := .quotient_span_singleton hw
  have := quotientGorensteinProjectiveStableCokernel_isEquivalence hw d hd
  exact Functor.isEquivalence_of_iso
    (quotientGorensteinProjectiveStableCokernelCompToSingularityCategoryIso.{v, u} hw)

/-- The equivalence `HMF(S, w) ≌ D_sg(mod-S/(w))` for a nonzerodivisor `w` of a noetherian ring `S`
of finite global dimension. -/
def quotientSingularityCokernelEquivalence [IsNoetherianRing S]
    [HasDerivedCategory.{v} (FGModuleCat.{u} (S ⧸ Ideal.span {w}))]
    (hw : w ∈ nonZeroDivisors S) (d : ℕ)
    (hd : ∀ N : ModuleCat.{u} S, HasProjectiveDimensionLE N d) :
    HomotopyCategory (S := S) (w := w) ≌
      SingularityCategory (FGModuleCat.{u} (S ⧸ Ideal.span {w})) :=
  haveI := quotientSingularityCokernel_isEquivalence.{v, u} hw d hd
  (quotientSingularityCokernel.{v, u} (S := S) (w := w)).asEquivalence

/-- The forward functor of `quotientSingularityCokernelEquivalence` is
`quotientSingularityCokernel`. -/
@[simp]
theorem quotientSingularityCokernelEquivalence_functor [IsNoetherianRing S]
    [HasDerivedCategory.{v} (FGModuleCat.{u} (S ⧸ Ideal.span {w}))]
    (hw : w ∈ nonZeroDivisors S) (d : ℕ)
    (hd : ∀ N : ModuleCat.{u} S, HasProjectiveDimensionLE N d) :
    (quotientSingularityCokernelEquivalence.{v, u} hw d hd).functor =
      quotientSingularityCokernel.{v, u} (S := S) (w := w) :=
  (rfl)

/-- **The singularity-category cokernel equivalence is triangulated.** -/
theorem quotientSingularityCokernelEquivalence_isTriangulated [IsNoetherianRing S]
    [HasDerivedCategory.{v} (FGModuleCat.{u} (S ⧸ Ideal.span {w}))]
    (hw : w ∈ nonZeroDivisors S) (d : ℕ)
    (hd : ∀ N : ModuleCat.{u} S, HasProjectiveDimensionLE N d) :
    letI := quotientSingularityCokernelCommShift.{v, u} hw
    letI : (quotientSingularityCokernelEquivalence.{v, u} hw d hd).functor.CommShift ℤ :=
      Functor.CommShift.ofIso
        (eqToIso (quotientSingularityCokernelEquivalence_functor.{v, u} hw d hd).symm) ℤ
    letI := (quotientSingularityCokernelEquivalence.{v, u} hw d hd).commShiftInverse ℤ
    letI := (quotientSingularityCokernelEquivalence.{v, u} hw d hd).commShift_of_functor ℤ
    (quotientSingularityCokernelEquivalence.{v, u} hw d hd).IsTriangulated := by
  let := quotientSingularityCokernelCommShift.{v, u} hw
  let e := eqToIso (quotientSingularityCokernelEquivalence_functor.{v, u} hw d hd).symm
  let : (quotientSingularityCokernelEquivalence.{v, u} hw d hd).functor.CommShift ℤ :=
    Functor.CommShift.ofIso e ℤ
  let := (quotientSingularityCokernelEquivalence.{v, u} hw d hd).commShiftInverse ℤ
  let := (quotientSingularityCokernelEquivalence.{v, u} hw d hd).commShift_of_functor ℤ
  have := Functor.CommShift.ofIso_compatibility e ℤ
  have := quotientSingularityCokernel_isTriangulated.{v, u} hw
  exact Equivalence.IsTriangulated.mk' _ (Functor.isTriangulated_of_iso e)

/-- **Singularity equivalence over a regular ring of finite Krull dimension.** Let `S` be a regular
commutative ring of finite Krull dimension and `w` a nonzerodivisor of `S`. Then
`quotientSingularityCokernel : HMF(S, w) ⥤ D_sg(mod-S/(w))` is an equivalence of categories. -/
theorem quotientSingularityCokernel_isEquivalence_of_isRegularRing [IsRegularRing S]
    [HasDerivedCategory.{v} (FGModuleCat.{u} (S ⧸ Ideal.span {w}))]
    (hdim : ringKrullDim S < ⊤) (hw : w ∈ nonZeroDivisors S) :
    (quotientSingularityCokernel.{v, u} (S := S) (w := w)).IsEquivalence := by
  have ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim S ≤ d := by
    induction h : ringKrullDim S using WithBot.recBotCoe with
    | bot => exact ⟨0, bot_le⟩
    | coe e =>
      induction e with
      | top => exact absurd h hdim.ne
      | coe d => exact ⟨d, le_rfl⟩
  exact quotientSingularityCokernel_isEquivalence.{v, u} hw d
    (IsRegularRing.hasProjectiveDimensionLE hd)

/-- **Eisenbud's singularity equivalence.** Over a regular local ring `S`, for every nonzerodivisor
`w` of `S`, `quotientSingularityCokernel : HMF(S, w) ⥤ D_sg(mod-S/(w))` is an equivalence of
categories. -/
theorem quotientSingularityCokernel_isEquivalence_of_isRegularLocalRing [IsRegularLocalRing S]
    [HasDerivedCategory.{v} (FGModuleCat.{u} (S ⧸ Ideal.span {w}))]
    (hw : w ∈ nonZeroDivisors S) :
    (quotientSingularityCokernel.{v, u} (S := S) (w := w)).IsEquivalence :=
  quotientSingularityCokernel_isEquivalence.{v, u} hw
    (IsLocalRing.maximalIdeal S).spanFinrank
    (IsRegularLocalRing.hasProjectiveDimensionLE
      (IsRegularLocalRing.spanFinrank_maximalIdeal (R := S)).ge)

/-- **Orlov's affine theorem** (Orlov, Theorem 3.9). Let `S` be a regular commutative ring of
finite Krull dimension, `k` a commutative ring, and `φ : k[X] →+* S` a flat ring homomorphism with
`φ X = w` (the flat potential morphism `Spec S → A¹_k`). Then
`quotientSingularityCokernel : HMF(S, w) ⥤ D_sg(mod-S/(w))` is an equivalence of categories. -/
theorem quotientSingularityCokernel_isEquivalence_of_flat_polynomial [IsRegularRing S]
    [HasDerivedCategory.{v} (FGModuleCat.{u} (S ⧸ Ideal.span {w}))]
    (hdim : ringKrullDim S < ⊤) {k : Type w} [CommRing k] {φ : Polynomial k →+* S}
    (hφ : φ.Flat) (hw : φ Polynomial.X = w) :
    (quotientSingularityCokernel.{v, u} (S := S) (w := w)).IsEquivalence :=
  quotientSingularityCokernel_isEquivalence_of_isRegularRing.{v, u} hdim
    (hw ▸ hφ.map_mem_nonZeroDivisors Polynomial.X_mem_nonZeroDivisors)

/-- The equivalence `HMF(S, w) ≌ D_sg(mod-S/(w))` of Orlov's affine theorem, for a regular ring `S`
of finite Krull dimension and a flat morphism `φ : k[X] →+* S` sending `X` to `w`. -/
def quotientSingularityCokernelEquivalenceOfFlatPolynomial [IsRegularRing S]
    [HasDerivedCategory.{v} (FGModuleCat.{u} (S ⧸ Ideal.span {w}))]
    (hdim : ringKrullDim S < ⊤) {k : Type w} [CommRing k] {φ : Polynomial k →+* S}
    (hφ : φ.Flat) (hw : φ Polynomial.X = w) :
    HomotopyCategory (S := S) (w := w) ≌
      SingularityCategory (FGModuleCat.{u} (S ⧸ Ideal.span {w})) :=
  haveI := quotientSingularityCokernel_isEquivalence_of_flat_polynomial.{v, u, w} hdim hφ hw
  (quotientSingularityCokernel.{v, u} (S := S) (w := w)).asEquivalence

/-- The forward functor of `quotientSingularityCokernelEquivalenceOfFlatPolynomial` is
`quotientSingularityCokernel`. -/
@[simp]
theorem quotientSingularityCokernelEquivalenceOfFlatPolynomial_functor [IsRegularRing S]
    [HasDerivedCategory.{v} (FGModuleCat.{u} (S ⧸ Ideal.span {w}))]
    (hdim : ringKrullDim S < ⊤) {k : Type w} [CommRing k] {φ : Polynomial k →+* S}
    (hφ : φ.Flat) (hw : φ Polynomial.X = w) :
    (quotientSingularityCokernelEquivalenceOfFlatPolynomial.{v, u, w} hdim hφ hw).functor =
      quotientSingularityCokernel.{v, u} (S := S) (w := w) :=
  (rfl)

/-- **Orlov's affine equivalence is triangulated.** -/
theorem quotientSingularityCokernelEquivalenceOfFlatPolynomial_isTriangulated [IsRegularRing S]
    [HasDerivedCategory.{v} (FGModuleCat.{u} (S ⧸ Ideal.span {w}))]
    (hdim : ringKrullDim S < ⊤) {k : Type w} [CommRing k] {φ : Polynomial k →+* S}
    (hφ : φ.Flat) (hw : φ Polynomial.X = w) :
    letI := quotientSingularityCokernelCommShift.{v, u}
      (hw ▸ hφ.map_mem_nonZeroDivisors Polynomial.X_mem_nonZeroDivisors)
    letI : (quotientSingularityCokernelEquivalenceOfFlatPolynomial.{v, u, w}
        hdim hφ hw).functor.CommShift ℤ :=
      Functor.CommShift.ofIso (eqToIso
        (quotientSingularityCokernelEquivalenceOfFlatPolynomial_functor.{v, u, w}
          hdim hφ hw).symm) ℤ
    letI := (quotientSingularityCokernelEquivalenceOfFlatPolynomial.{v, u, w}
      hdim hφ hw).commShiftInverse ℤ
    letI := (quotientSingularityCokernelEquivalenceOfFlatPolynomial.{v, u, w}
      hdim hφ hw).commShift_of_functor ℤ
    (quotientSingularityCokernelEquivalenceOfFlatPolynomial.{v, u, w}
      hdim hφ hw).IsTriangulated := by
  let := quotientSingularityCokernelCommShift.{v, u}
    (hw ▸ hφ.map_mem_nonZeroDivisors Polynomial.X_mem_nonZeroDivisors)
  let e := eqToIso
    (quotientSingularityCokernelEquivalenceOfFlatPolynomial_functor.{v, u, w} hdim hφ hw).symm
  let : (quotientSingularityCokernelEquivalenceOfFlatPolynomial.{v, u, w}
      hdim hφ hw).functor.CommShift ℤ :=
    Functor.CommShift.ofIso e ℤ
  let := (quotientSingularityCokernelEquivalenceOfFlatPolynomial.{v, u, w}
    hdim hφ hw).commShiftInverse ℤ
  let := (quotientSingularityCokernelEquivalenceOfFlatPolynomial.{v, u, w}
    hdim hφ hw).commShift_of_functor ℤ
  have := Functor.CommShift.ofIso_compatibility e ℤ
  have := quotientSingularityCokernel_isTriangulated.{v, u}
    (hw ▸ hφ.map_mem_nonZeroDivisors Polynomial.X_mem_nonZeroDivisors)
  exact Equivalence.IsTriangulated.mk' _ (Functor.isTriangulated_of_iso e)

end Equivalence

end TauCeti.MatrixFactorization.HomotopyCategory
