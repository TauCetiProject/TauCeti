/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import TauCeti.Algebra.Homology.DerivedCategory.Singularity.Syzygy
public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Equivalence
public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Singularity
public import TauCeti.RingTheory.Flat.NonZeroDivisors
public import TauCeti.RingTheory.KrullDimension.FiniteType

/-!
# Hypersurface singularity equivalences and Orlov's theorem for matrix factorizations

Let `w` be a non-zero-divisor of a commutative Noetherian ring `S` and put `R = S/(w)`. Reducing a
finite-projective matrix factorization of `w` modulo `w` and placing the cokernel of its
even-to-odd differential in degree zero defines a fully faithful triangle functor
`quotientSingularityCokernel : HMF(S,w) ⥤ D_sg(mod-R)` factoring as
`quotientGorensteinProjectiveStableCokernel ⋙ GorensteinProjectiveModuleCat.toSingularityCategory R`
(`HomotopyCategory.quotientGorensteinProjectiveStableCokernel_comp_toSingularityCategory`).

When `S` has finite global dimension `≤ d`, every `d`-th projective syzygy in `FGModuleCat R`
restricts to an `S`-module of projective dimension at most `1`
(`ModuleCat.hasProjectiveDimensionLE_one_restrictScalars_of_isSyzygy`), hence is
Gorenstein-projective over `R` (`FGModuleCat.isGorensteinProjective_quotient_of_isSyzygy`). Since
every object of `D_sg(mod-R)` is isomorphic to a shifted `d`-th syzygy
(`TauCeti.SingularityCategory.exists_iso_Q_obj_singleFunctor_obj_isSyzygy`), Chen's functor
`stable(Gproj-R) ⥤ D_sg(mod-R)` is a triangulated equivalence
(`TauCeti.GorensteinProjectiveModuleCat.singularityEquivalenceQuotient_isTriangulated`), and so is
the composite `quotientSingularityCokernel : HMF(S,w) ⥤ D_sg(mod-R)`
(`HomotopyCategory.quotientSingularityCokernelEquivalence_isTriangulated`).

We specialize this general finite-global-dimension theorem to three distinct geometric and
ring-theoretic regimes without conflating their hypotheses:

1. **Regular local rings (Eisenbud–Buchweitz):** `[IsRegularLocalRing S]` and
   `w ∈ nonZeroDivisors S`
   (`quotientSingularityCokernel_isEquivalence_of_isRegularLocalRing` and
   `quotientSingularityCokernelEquivalenceOfIsRegularLocalRing`).
2. **Regular rings of finite Krull dimension:** `[IsRegularRing S]`, `ringKrullDim S < ⊤` (or
   `[FiniteRingKrullDim S]`), and `w ∈ nonZeroDivisors S`
   (`quotientSingularityCokernel_isEquivalence_of_isRegularRing` and
   `quotientSingularityCokernelEquivalenceOfIsRegularRing`).
3. **Orlov's affine Landau–Ginzburg theorem over a field** (Proposition 3.3 and Theorem 3.9 of
   Orlov (2004), without Karoubi completion): `[Field k] [IsRegularRing S] [Algebra k S]
   [Algebra.FiniteType k S]` and `(Polynomial.aeval (R := k) w).toRingHom.Flat` (so `Spec S → A¹_k`
   is flat, hence `w ∈ nonZeroDivisors S`), together with the companion form for a regular flat
   finite-type `k[X]`-algebra with `algebraMap k[X] S X = w`
   (`quotientSingularityCokernel_isEquivalence_of_flat_aeval`,
   `quotientSingularityCokernelEquivalenceOfFlatAeval`, and
   `quotientSingularityCokernel_isEquivalence_of_flat_polynomial`).

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Sections 5–6.
* R.-O. Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Mathematical Surveys
  and Monographs **262**, American Mathematical Society (2021), Theorem 4.4.1.
* D. Orlov, *Triangulated categories of singularities and D-branes in Landau–Ginzburg models*,
  Proc. Steklov Inst. Math. **246** (2004), 227–248, Proposition 3.3 and Theorem 3.9.
* Xiao-Wu Chen, *Relative singularity categories and Gorenstein-projective modules*,
  Math. Nachr. **284** (2011), 199–212.
-/

public section

noncomputable section

open CategoryTheory

universe u₀ v u

/-! ### High syzygies and Buchweitz–Chen equivalence over a hypersurface -/

namespace FGModuleCat

/-- Over a hypersurface `S/(w)` in a Noetherian commutative ring `S` of global dimension at most
`d`, every `k`-th projective syzygy in `FGModuleCat (S/(w))` with `d ≤ k + 1` (in particular every
`d`-th syzygy) is Gorenstein-projective. -/
theorem isGorensteinProjective_quotient_of_isSyzygy {S : Type u} [CommRing S] [IsNoetherianRing S]
    {w : S} (hw : w ∈ nonZeroDivisors S) {d k : ℕ} (hdk : d ≤ k + 1)
    (hd : ∀ N : ModuleCat.{u} S, HasProjectiveDimensionLE N d)
    {M : FGModuleCat.{u} (S ⧸ Ideal.span {w})}
    (hM : (isProjective (FGModuleCat.{u} (S ⧸ Ideal.span {w}))).IsSyzygy k M) :
    isGorensteinProjective (FGModuleCat.{u} (S ⧸ Ideal.span {w})) M := by
  let U := forget₂ (FGModuleCat.{u} (S ⧸ Ideal.span {w})) (ModuleCat.{u} (S ⧸ Ideal.span {w}))
  have hM_mod : (isProjective (ModuleCat.{u} (S ⧸ Ideal.span {w}))).IsSyzygy k M.obj :=
    hM.map U (fun T hT ↦ hT.map_of_exact U) fun Q hQ ↦ by
      have : Projective Q := hQ
      have := FGModuleCat.moduleProjective_of_projective Q
      exact ModuleCat.projective_of_categoryTheory_projective Q.obj
  have hpd : HasProjectiveDimensionLE
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M.obj) 1 :=
    ModuleCat.hasProjectiveDimensionLE_one_restrictScalars_of_isSyzygy hw hdk hM_mod hd
  have : Module.Finite S
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M.obj) :=
    ((Ideal.Quotient.mk (Ideal.span {w})).finite_restrictScalars_iff
      Ideal.Quotient.mk_surjective M.obj).2 M.property
  have := Module.finitePresentation_of_finite S
    ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M.obj)
  exact (FGModuleCat.isGorensteinProjective_iff M).2
    (TauCeti.MatrixFactorization.isGorensteinProjective_of_hasProjectiveDimensionLE hw M.obj hpd)

end FGModuleCat

namespace TauCeti.GorensteinProjectiveModuleCat

section Hypersurface

variable {S : Type u} [CommRing S] [IsNoetherianRing S] {w : S}
  [HasDerivedCategory.{v} (FGModuleCat.{u} (S ⧸ Ideal.span {w}))]

/-- Over a hypersurface `S/(w)` in a Noetherian ring `S` of finite global dimension, Chen's functor
`CategoryTheory.GorensteinProjective.toSingularityCategory (FGModuleCat (S/(w)))` is essentially
surjective: every object of `D_sg(mod-S/(w))` is isomorphic to a shifted `d`-th syzygy, which is
Gorenstein-projective. -/
theorem essSurj_fgModuleCat_toSingularityCategory_quotient (hw : w ∈ nonZeroDivisors S) (d : ℕ)
    (hd : ∀ N : ModuleCat.{u} S, HasProjectiveDimensionLE N d) :
    (CategoryTheory.GorensteinProjective.toSingularityCategory
      (FGModuleCat.{u} (S ⧸ Ideal.span {w}))).EssSurj where
  mem_essImage Y := by
    let C := FGModuleCat.{u} (S ⧸ Ideal.span {w})
    have := Localization.essSurj (SingularityCategory.Q C) (DerivedCategory.Bounded.perfect C).trW
    obtain ⟨M, n, hM, ⟨e⟩⟩ :=
      SingularityCategory.exists_iso_Q_obj_singleFunctor_obj_isSyzygy
        ((SingularityCategory.Q C).objPreimage Y) d
    have hGP : isGorensteinProjective C M :=
      FGModuleCat.isGorensteinProjective_quotient_of_isSyzygy hw (Nat.le_succ d) hd hM
    exact (CategoryTheory.GorensteinProjective.mem_essImage_toSingularityCategory hGP n).ofIso
      (e.symm ≪≫ (SingularityCategory.Q C).objObjPreimageIso Y)

/-- **Buchweitz–Chen essential surjectivity** over a hypersurface in a Noetherian ring of finite
global dimension: Chen's functor `stable(Gproj-S/(w)) ⥤ D_sg(mod-S/(w))` is essentially
surjective. -/
theorem essSurj_toSingularityCategory_quotient (hw : w ∈ nonZeroDivisors S) (d : ℕ)
    (hd : ∀ N : ModuleCat.{u} S, HasProjectiveDimensionLE N d) :
    (toSingularityCategory.{v, u} (S ⧸ Ideal.span {w})).EssSurj := by
  have := essSurj_fgModuleCat_toSingularityCategory_quotient.{v, u} hw d hd
  rw [toSingularityCategory_def]
  infer_instance

/-- **Buchweitz's theorem** over a hypersurface in a Noetherian ring of finite global dimension:
Chen's functor `stable(Gproj-S/(w)) ⥤ D_sg(mod-S/(w))` is an equivalence of categories. -/
theorem isEquivalence_toSingularityCategory_quotient (hw : w ∈ nonZeroDivisors S) (d : ℕ)
    (hd : ∀ N : ModuleCat.{u} S, HasProjectiveDimensionLE N d) :
    (toSingularityCategory.{v, u} (S ⧸ Ideal.span {w})).IsEquivalence :=
  have := essSurj_toSingularityCategory_quotient.{v, u} hw d hd
  { faithful := inferInstance
    full := inferInstance
    essSurj := inferInstance }

/-- **Buchweitz's equivalence** `stable(Gproj-S/(w)) ≌ D_sg(mod-S/(w))` over a hypersurface in a
Noetherian ring `S` of finite global dimension. -/
def singularityEquivalenceQuotient (hw : w ∈ nonZeroDivisors S) (d : ℕ)
    (hd : ∀ N : ModuleCat.{u} S, HasProjectiveDimensionLE N d) :
    (exactStructure.{u} (S ⧸ Ideal.span {w})).ProjectiveStableCategory ≌
      SingularityCategory (FGModuleCat.{u} (S ⧸ Ideal.span {w})) :=
  haveI := isEquivalence_toSingularityCategory_quotient.{v, u} hw d hd
  (toSingularityCategory.{v, u} (S ⧸ Ideal.span {w})).asEquivalence

/-- The forward functor of `singularityEquivalenceQuotient` is `toSingularityCategory`. -/
@[simp]
theorem singularityEquivalenceQuotient_functor (hw : w ∈ nonZeroDivisors S) (d : ℕ)
    (hd : ∀ N : ModuleCat.{u} S, HasProjectiveDimensionLE N d) :
    (singularityEquivalenceQuotient.{v, u} hw d hd).functor =
      toSingularityCategory.{v, u} (S ⧸ Ideal.span {w}) :=
  (rfl)

/-- **Buchweitz's equivalence is triangulated**, for Happel's triangulation of
`stable(Gproj-S/(w))` and the Verdier-quotient triangulation of `D_sg(mod-S/(w))`. -/
theorem singularityEquivalenceQuotient_isTriangulated (hw : w ∈ nonZeroDivisors S) (d : ℕ)
    (hd : ∀ N : ModuleCat.{u} S, HasProjectiveDimensionLE N d) :
    letI := (exactStructure_isFrobenius.{u, u} (A := S ⧸ Ideal.span {w})).stableHasShift
    letI :=
      (exactStructure_isFrobenius.{u, u} (A := S ⧸ Ideal.span {w})).stableShiftFunctor_additive
    letI := (exactStructure_isFrobenius.{u, u} (A := S ⧸ Ideal.span {w})).stablePretriangulated
    letI := toSingularityCategoryCommShift.{v, u} (S ⧸ Ideal.span {w})
    letI : (singularityEquivalenceQuotient.{v, u} hw d hd).functor.CommShift ℤ :=
      Functor.CommShift.ofIso
        (eqToIso (singularityEquivalenceQuotient_functor.{v, u} hw d hd).symm) ℤ
    letI := (singularityEquivalenceQuotient.{v, u} hw d hd).commShiftInverse ℤ
    letI := (singularityEquivalenceQuotient.{v, u} hw d hd).commShift_of_functor ℤ
    (singularityEquivalenceQuotient.{v, u} hw d hd).IsTriangulated := by
  have hE := exactStructure_isFrobenius.{u, u} (A := S ⧸ Ideal.span {w})
  let := hE.stableHasShift
  let := hE.stableShiftFunctor_additive
  let := hE.stablePretriangulated
  let := toSingularityCategoryCommShift.{v, u} (S ⧸ Ideal.span {w})
  let e := eqToIso (singularityEquivalenceQuotient_functor.{v, u} hw d hd).symm
  let : (singularityEquivalenceQuotient.{v, u} hw d hd).functor.CommShift ℤ :=
    Functor.CommShift.ofIso e ℤ
  let := (singularityEquivalenceQuotient.{v, u} hw d hd).commShiftInverse ℤ
  let := (singularityEquivalenceQuotient.{v, u} hw d hd).commShift_of_functor ℤ
  have := Functor.CommShift.ofIso_compatibility e ℤ
  have := toSingularityCategory_isTriangulated.{v, u} (S ⧸ Ideal.span {w})
  exact Equivalence.IsTriangulated.mk' _ (Functor.isTriangulated_of_iso e)

end Hypersurface

end TauCeti.GorensteinProjectiveModuleCat

/-! ### Singularity-category equivalences for matrix factorizations -/

namespace TauCeti.MatrixFactorization

namespace HomotopyCategory

section FiniteGlobalDimension

variable {S : Type u} [CommRing S] [IsNoetherianRing S] {w : S}
  [HasDerivedCategory.{v} (FGModuleCat.{u} (S ⧸ Ideal.span {w}))]

/-- **Essential surjectivity of the singularity-category cokernel functor.** For a non-zero-divisor
`w` of a Noetherian ring `S` of finite global dimension, `quotientSingularityCokernel` is
essentially surjective onto `D_sg(mod-S/(w))`. -/
theorem quotientSingularityCokernel_essSurj (hw : w ∈ nonZeroDivisors S) (d : ℕ)
    (hd : ∀ N : ModuleCat.{u} S, HasProjectiveDimensionLE N d) :
    (quotientSingularityCokernel (S := S) (w := w)).EssSurj := by
  have := quotientGorensteinProjectiveStableCokernel_essSurj hw d hd
  have := GorensteinProjectiveModuleCat.essSurj_toSingularityCategory_quotient.{v, u} hw d hd
  rw [← quotientGorensteinProjectiveStableCokernel_comp_toSingularityCategory hw]
  infer_instance

/-- **The singularity-category cokernel functor is an equivalence in finite global dimension.**
For a non-zero-divisor `w` of a Noetherian commutative ring `S` of finite global dimension,
`quotientSingularityCokernel : HMF(S,w) ⥤ D_sg(mod-S/(w))` is an equivalence of categories. -/
theorem quotientSingularityCokernel_isEquivalence (hw : w ∈ nonZeroDivisors S) (d : ℕ)
    (hd : ∀ N : ModuleCat.{u} S, HasProjectiveDimensionLE N d) :
    (quotientSingularityCokernel (S := S) (w := w)).IsEquivalence where
  faithful := quotientSingularityCokernel_faithful hw
  full := quotientSingularityCokernel_full hw
  essSurj := quotientSingularityCokernel_essSurj hw d hd

/-- The equivalence `HMF(S,w) ≌ D_sg(mod-S/(w))` given by the reduced cokernel placed in degree
zero, for a non-zero-divisor `w` of a Noetherian ring `S` of finite global dimension. -/
def quotientSingularityCokernelEquivalence (hw : w ∈ nonZeroDivisors S) (d : ℕ)
    (hd : ∀ N : ModuleCat.{u} S, HasProjectiveDimensionLE N d) :
    HomotopyCategory (S := S) (w := w) ≌
      SingularityCategory (FGModuleCat.{u} (S ⧸ Ideal.span {w})) :=
  haveI := quotientSingularityCokernel_isEquivalence.{v, u} hw d hd
  (quotientSingularityCokernel (S := S) (w := w)).asEquivalence

/-- The forward functor of `quotientSingularityCokernelEquivalence` is
`quotientSingularityCokernel`. -/
@[simp]
theorem quotientSingularityCokernelEquivalence_functor (hw : w ∈ nonZeroDivisors S) (d : ℕ)
    (hd : ∀ N : ModuleCat.{u} S, HasProjectiveDimensionLE N d) :
    (quotientSingularityCokernelEquivalence.{v, u} hw d hd).functor =
      quotientSingularityCokernel (S := S) (w := w) :=
  (rfl)

/-- **The singularity-category cokernel equivalence is triangulated** in finite global dimension,
for the parity-shift triangulation of `HMF(S,w)` and the Verdier-quotient triangulation of
`D_sg(mod-S/(w))`. -/
theorem quotientSingularityCokernelEquivalence_isTriangulated (hw : w ∈ nonZeroDivisors S) (d : ℕ)
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

end FiniteGlobalDimension

section RegularLocalRing

variable {S : Type u} [CommRing S] [IsRegularLocalRing S] {w : S}
  [HasDerivedCategory.{v} (FGModuleCat.{u} (S ⧸ Ideal.span {w}))]

/-- **Eisenbud–Buchweitz singularity equivalence.** For a non-zero-divisor `w` of a regular local
ring `S`, the reduced-cokernel functor `HMF(S,w) ⥤ D_sg(mod-S/(w))` is an equivalence of
categories. -/
theorem quotientSingularityCokernel_isEquivalence_of_isRegularLocalRing
    (hw : w ∈ nonZeroDivisors S) :
    (quotientSingularityCokernel (S := S) (w := w)).IsEquivalence :=
  quotientSingularityCokernel_isEquivalence hw (IsLocalRing.maximalIdeal S).spanFinrank
    (IsRegularLocalRing.hasProjectiveDimensionLE
      (IsRegularLocalRing.spanFinrank_maximalIdeal (R := S)).ge)

/-- **Eisenbud–Buchweitz equivalence** `HMF(S,w) ≌ D_sg(mod-S/(w))` for a non-zero-divisor `w` of
a regular local ring `S`. -/
def quotientSingularityCokernelEquivalenceOfIsRegularLocalRing (hw : w ∈ nonZeroDivisors S) :
    HomotopyCategory (S := S) (w := w) ≌
      SingularityCategory (FGModuleCat.{u} (S ⧸ Ideal.span {w})) :=
  quotientSingularityCokernelEquivalence hw (IsLocalRing.maximalIdeal S).spanFinrank
    (IsRegularLocalRing.hasProjectiveDimensionLE
      (IsRegularLocalRing.spanFinrank_maximalIdeal (R := S)).ge)

/-- The forward functor of `quotientSingularityCokernelEquivalenceOfIsRegularLocalRing` is
`quotientSingularityCokernel`. -/
@[simp]
theorem quotientSingularityCokernelEquivalenceOfIsRegularLocalRing_functor
    (hw : w ∈ nonZeroDivisors S) :
    (quotientSingularityCokernelEquivalenceOfIsRegularLocalRing.{v, u} hw).functor =
      quotientSingularityCokernel (S := S) (w := w) :=
  (rfl)

/-- **The Eisenbud–Buchweitz singularity equivalence is triangulated.** -/
theorem quotientSingularityCokernelEquivalenceOfIsRegularLocalRing_isTriangulated
    (hw : w ∈ nonZeroDivisors S) :
    letI := quotientSingularityCokernelCommShift.{v, u} hw
    letI :
      (quotientSingularityCokernelEquivalenceOfIsRegularLocalRing.{v, u} hw).functor.CommShift ℤ :=
        Functor.CommShift.ofIso (eqToIso
          (quotientSingularityCokernelEquivalenceOfIsRegularLocalRing_functor.{v, u} hw).symm) ℤ
    letI :=
      (quotientSingularityCokernelEquivalenceOfIsRegularLocalRing.{v, u} hw).commShiftInverse ℤ
    letI :=
      (quotientSingularityCokernelEquivalenceOfIsRegularLocalRing.{v, u} hw).commShift_of_functor ℤ
    (quotientSingularityCokernelEquivalenceOfIsRegularLocalRing.{v, u} hw).IsTriangulated :=
  quotientSingularityCokernelEquivalence_isTriangulated hw
    (IsLocalRing.maximalIdeal S).spanFinrank
    (IsRegularLocalRing.hasProjectiveDimensionLE
      (IsRegularLocalRing.spanFinrank_maximalIdeal (R := S)).ge)

end RegularLocalRing

section RegularRing

variable {S : Type u} [CommRing S] [IsRegularRing S] {w : S}
  [HasDerivedCategory.{v} (FGModuleCat.{u} (S ⧸ Ideal.span {w}))]

/-- For a non-zero-divisor `w` of a regular ring `S` of finite Krull dimension
(`ringKrullDim S < ⊤`), the reduced-cokernel functor `HMF(S,w) ⥤ D_sg(mod-S/(w))` is an
equivalence of categories. -/
theorem quotientSingularityCokernel_isEquivalence_of_isRegularRing
    (hdim : ringKrullDim S < ⊤) (hw : w ∈ nonZeroDivisors S) :
    (quotientSingularityCokernel (S := S) (w := w)).IsEquivalence :=
  let ⟨d, hd⟩ := IsRegularRing.exists_hasProjectiveDimensionLE.{u} hdim
  quotientSingularityCokernel_isEquivalence hw d hd

/-- For a non-zero-divisor `w` of a regular ring `S` satisfying `[FiniteRingKrullDim S]`,
the reduced-cokernel functor `HMF(S,w) ⥤ D_sg(mod-S/(w))` is an equivalence of categories. -/
theorem quotientSingularityCokernel_isEquivalence_of_finiteRingKrullDim
    [FiniteRingKrullDim S] (hw : w ∈ nonZeroDivisors S) :
    (quotientSingularityCokernel (S := S) (w := w)).IsEquivalence :=
  quotientSingularityCokernel_isEquivalence_of_isRegularRing ringKrullDim_lt_top hw

/-- Equivalence `HMF(S,w) ≌ D_sg(mod-S/(w))` for a non-zero-divisor `w` of a regular ring `S` of
finite Krull dimension (`ringKrullDim S < ⊤`). -/
def quotientSingularityCokernelEquivalenceOfIsRegularRing
    (hdim : ringKrullDim S < ⊤) (hw : w ∈ nonZeroDivisors S) :
    HomotopyCategory (S := S) (w := w) ≌
      SingularityCategory (FGModuleCat.{u} (S ⧸ Ideal.span {w})) :=
  haveI := quotientSingularityCokernel_isEquivalence_of_isRegularRing.{v, u} hdim hw
  (quotientSingularityCokernel (S := S) (w := w)).asEquivalence

/-- The forward functor of `quotientSingularityCokernelEquivalenceOfIsRegularRing` is
`quotientSingularityCokernel`. -/
@[simp]
theorem quotientSingularityCokernelEquivalenceOfIsRegularRing_functor
    (hdim : ringKrullDim S < ⊤) (hw : w ∈ nonZeroDivisors S) :
    (quotientSingularityCokernelEquivalenceOfIsRegularRing.{v, u} hdim hw).functor =
      quotientSingularityCokernel (S := S) (w := w) :=
  (rfl)

/-- **The singularity-category cokernel equivalence over a regular ring of finite Krull dimension
is triangulated.** -/
theorem quotientSingularityCokernelEquivalenceOfIsRegularRing_isTriangulated
    (hdim : ringKrullDim S < ⊤) (hw : w ∈ nonZeroDivisors S) :
    letI := quotientSingularityCokernelCommShift.{v, u} hw
    letI :
      (quotientSingularityCokernelEquivalenceOfIsRegularRing.{v, u}
        hdim hw).functor.CommShift ℤ :=
        Functor.CommShift.ofIso (eqToIso
          (quotientSingularityCokernelEquivalenceOfIsRegularRing_functor.{v, u}
            hdim hw).symm) ℤ
    letI :=
      (quotientSingularityCokernelEquivalenceOfIsRegularRing.{v, u} hdim hw).commShiftInverse ℤ
    letI :=
      (quotientSingularityCokernelEquivalenceOfIsRegularRing.{v, u}
        hdim hw).commShift_of_functor ℤ
    (quotientSingularityCokernelEquivalenceOfIsRegularRing.{v, u} hdim hw).IsTriangulated := by
  obtain ⟨d, hd⟩ := IsRegularRing.exists_hasProjectiveDimensionLE.{u} hdim
  exact quotientSingularityCokernelEquivalence_isTriangulated hw d hd

end RegularRing

section Orlov

/-- **Orlov's affine Landau–Ginzburg theorem** (Orlov 2004, Proposition 3.3 and Theorem 3.9,
without Karoubi completion): for a regular finite-type algebra `S` over a field `k` and an element
`w : S` whose evaluation map `k[X] →+* S` is flat, the reduced-cokernel functor
`HMF(S,w) ⥤ D_sg(mod-S/(w))` is an equivalence of categories. -/
theorem quotientSingularityCokernel_isEquivalence_of_flat_aeval
    {k : Type u₀} [Field k] {S : Type u} [CommRing S] [IsRegularRing S]
    [Algebra k S] [Algebra.FiniteType k S] {w : S}
    (hw : (Polynomial.aeval (R := k) w).toRingHom.Flat)
    [HasDerivedCategory.{v} (FGModuleCat.{u} (S ⧸ Ideal.span {w}))] :
    (quotientSingularityCokernel (S := S) (w := w)).IsEquivalence :=
  quotientSingularityCokernel_isEquivalence_of_isRegularRing
    (TauCeti.ringKrullDim_lt_top_of_finiteType k S)
    (Polynomial.aeval_X (R := k) w ▸ hw.map_mem_nonZeroDivisors Polynomial.X_mem_nonZeroDivisors)

/-- **Orlov's equivalence** `HMF(S,w) ≌ D_sg(mod-S/(w))` for a regular finite-type `k`-algebra `S`
and a flat potential `w : S` (`(Polynomial.aeval (R := k) w).toRingHom.Flat`). -/
def quotientSingularityCokernelEquivalenceOfFlatAeval
    {k : Type u₀} [Field k] {S : Type u} [CommRing S] [IsRegularRing S]
    [Algebra k S] [Algebra.FiniteType k S] {w : S}
    (hw : (Polynomial.aeval (R := k) w).toRingHom.Flat)
    [HasDerivedCategory.{v} (FGModuleCat.{u} (S ⧸ Ideal.span {w}))] :
    HomotopyCategory (S := S) (w := w) ≌
      SingularityCategory (FGModuleCat.{u} (S ⧸ Ideal.span {w})) :=
  quotientSingularityCokernelEquivalenceOfIsRegularRing
    (TauCeti.ringKrullDim_lt_top_of_finiteType k S)
    (Polynomial.aeval_X (R := k) w ▸ hw.map_mem_nonZeroDivisors Polynomial.X_mem_nonZeroDivisors)

/-- The forward functor of `quotientSingularityCokernelEquivalenceOfFlatAeval` is
`quotientSingularityCokernel`. -/
@[simp]
theorem quotientSingularityCokernelEquivalenceOfFlatAeval_functor
    {k : Type u₀} [Field k] {S : Type u} [CommRing S] [IsRegularRing S]
    [Algebra k S] [Algebra.FiniteType k S] {w : S}
    (hw : (Polynomial.aeval (R := k) w).toRingHom.Flat)
    [HasDerivedCategory.{v} (FGModuleCat.{u} (S ⧸ Ideal.span {w}))] :
    (quotientSingularityCokernelEquivalenceOfFlatAeval.{u₀, v, u} hw).functor =
      quotientSingularityCokernel (S := S) (w := w) :=
  (rfl)

/-- **Orlov's affine Landau–Ginzburg equivalence is triangulated**, for the parity-shift
triangulation of `HMF(S,w)` and the Verdier-quotient triangulation of `D_sg(mod-S/(w))`. -/
theorem quotientSingularityCokernelEquivalenceOfFlatAeval_isTriangulated
    {k : Type u₀} [Field k] {S : Type u} [CommRing S] [IsRegularRing S]
    [Algebra k S] [Algebra.FiniteType k S] {w : S}
    (hw : (Polynomial.aeval (R := k) w).toRingHom.Flat)
    [HasDerivedCategory.{v} (FGModuleCat.{u} (S ⧸ Ideal.span {w}))] :
    letI := quotientSingularityCokernelCommShift.{v, u} (S := S) (w := w)
      (Polynomial.aeval_X (R := k) w ▸ hw.map_mem_nonZeroDivisors Polynomial.X_mem_nonZeroDivisors)
    letI :
      (quotientSingularityCokernelEquivalenceOfFlatAeval.{u₀, v, u} hw).functor.CommShift ℤ :=
        Functor.CommShift.ofIso (eqToIso
          (quotientSingularityCokernelEquivalenceOfFlatAeval_functor.{u₀, v, u} hw).symm) ℤ
    letI :=
      (quotientSingularityCokernelEquivalenceOfFlatAeval.{u₀, v, u} hw).commShiftInverse ℤ
    letI :=
      (quotientSingularityCokernelEquivalenceOfFlatAeval.{u₀, v, u} hw).commShift_of_functor ℤ
    (quotientSingularityCokernelEquivalenceOfFlatAeval.{u₀, v, u} hw).IsTriangulated :=
  quotientSingularityCokernelEquivalenceOfIsRegularRing_isTriangulated
    (TauCeti.ringKrullDim_lt_top_of_finiteType k S)
    (Polynomial.aeval_X (R := k) w ▸ hw.map_mem_nonZeroDivisors Polynomial.X_mem_nonZeroDivisors)

/-- Companion form of **Orlov's affine Landau–Ginzburg theorem** phrased directly over a flat
finite-type `k[X]`-algebra `S` with `IsRegularRing S` and `algebraMap (Polynomial k) S X = w`. -/
theorem quotientSingularityCokernel_isEquivalence_of_flat_polynomial
    {k : Type u₀} [Field k] {S : Type u} [CommRing S] [IsRegularRing S]
    [Algebra (Polynomial k) S] [Algebra.FiniteType (Polynomial k) S] [Module.Flat (Polynomial k) S]
    {w : S} (hw : algebraMap (Polynomial k) S Polynomial.X = w)
    [HasDerivedCategory.{v} (FGModuleCat.{u} (S ⧸ Ideal.span {w}))] :
    (quotientSingularityCokernel (S := S) (w := w)).IsEquivalence := by
  let : Algebra k S := ((algebraMap (Polynomial k) S).comp Polynomial.C).toAlgebra
  have : IsScalarTower k (Polynomial k) S := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.FiniteType k S :=
    Algebra.FiniteType.trans (S := Polynomial k) inferInstance inferInstance
  have haeval : (Polynomial.aeval (R := k) w).toRingHom = algebraMap (Polynomial k) S := by
    refine Polynomial.ringHom_ext' ?_ ?_
    · ext c
      simp [RingHom.algebraMap_toAlgebra]
    · simpa using hw.symm
  have hflat : (Polynomial.aeval (R := k) w).toRingHom.Flat := by
    rw [haeval, RingHom.flat_algebraMap_iff]
    infer_instance
  exact quotientSingularityCokernel_isEquivalence_of_flat_aeval hflat

end Orlov

end HomotopyCategory

end TauCeti.MatrixFactorization
