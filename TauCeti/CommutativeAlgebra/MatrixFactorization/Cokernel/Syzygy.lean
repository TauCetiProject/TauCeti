/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Stable
public import TauCeti.CommutativeAlgebra.MatrixFactorization.Shift
public import TauCeti.CategoryTheory.Exact.Stable.Loop
public import TauCeti.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Parity shift and syzygy of matrix-factorization cokernels

Let `X = (X₀ --d₀--> X₁ --d₁--> X₀)` be a finite-projective matrix factorization of a
non-zero-divisor `w` of a Noetherian commutative ring `S`, and let `X̄` be its reduction modulo
`w`, a factorization of the zero potential over the hypersurface ring `S/(w)`. The reduced
complex is exact in both parities (`exact_quotient_d₁_d₀`, `exact_quotient_d₀_d₁`): if
`d₀ x = w y`, then `w x = d₁ d₀ x = w d₁ y`, so `x = d₁ y`. Exactness at `X̄₀` makes

`0 ⟶ coker d̄₁ ⟶ X̄₁ ⟶ coker d̄₀ ⟶ 0`

short exact, with first map induced by `-d̄₀` (`shortExact_cokernelDesc_parityShift`). Its
middle term is projective, so it is a projective presentation of `coker d̄₀` whose kernel term is
the cokernel of the parity shift `X̄[1]` (`cokernelPresentation`). Hence the syzygy `Ω` of the
stable module category of `S/(w)` sends the cokernel of `X` to the cokernel of `X[1]`.

These identifications are natural, and they descend to the homotopy category `HMF(S,w)`: the
stable cokernel functor intertwines the parity shift, which is the shift by `1` of the
triangulated category `HMF(S,w)`, with `Ω`
(`HomotopyCategory.quotientStableCokernelCompStableLoopIso`,
`HomotopyCategory.shiftFunctorOneCompQuotientStableCokernelIso`). Since the parity shift squares
to the identity, every cokernel is periodic of period at most two for `Ω`
(`HomotopyCategory.quotientStableCokernelCompStableLoopCompStableLoopIso`).

Only the non-zero-divisor hypothesis on `w` is used. Under Eisenbud's further hypotheses
(`S` regular local) the cokernels are maximal Cohen–Macaulay modules and the cokernel functor is
an equivalence onto their stable category; neither statement is made here.

## Main definitions

* `TauCeti.MatrixFactorization.cokernelPresentation`: for a factorization of the zero potential
  exact at its even component, the projective presentation `coker d₁ ⟶ X₁ ⟶ coker d₀`.
* `TauCeti.MatrixFactorization.quotientCokernelStableLoopIso`: `Ω` of the cokernel of the
  reduction of `X` is the cokernel of the reduction of `X[1]`, naturally in `X`.
* `TauCeti.MatrixFactorization.HomotopyCategory.quotientStableCokernelCompStableLoopIso`: its
  descent to `HMF(S,w)`.
* `HomotopyCategory.quotientStableCokernelCompStableLoopCompStableLoopIso`, in the same
  namespace: `Ω² ∘ coker ≅ coker` on `HMF(S,w)`.

## Main results

* `TauCeti.MatrixFactorization.exact_quotient_d₁_d₀`: the reduction modulo a non-zero-divisor
  potential is exact at the even component.
* `TauCeti.MatrixFactorization.shortExact_cokernelDesc_parityShift`: the short exact sequence
  `0 ⟶ coker d₁ ⟶ X₁ ⟶ coker d₀ ⟶ 0` of a factorization of the zero potential exact at `X₀`.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Sections 5–6: exactness of the
  reduced periodic complex and the two-periodic resolution of the cokernel.
* R.-O. Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Mathematical Surveys
  and Monographs **262** (2021), Section 4: the syzygy as the inverse suspension of the stable
  category.
-/

public section

noncomputable section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory Limits

/-! ### Factorizations of the zero potential

The potential is only assumed to be propositionally zero, so that these results apply to the
reduction of a factorization modulo its potential. -/

section ZeroPotential

variable {T : Type u} [CommRing T] {v : T}

/-- For a zero potential, the descent through `coker d₁` of the odd differential `-d₀` of the
parity shift restricts to `-d₀` along the cokernel projection. -/
@[reassoc]
theorem cokernelπ_cokernelDesc_parityShift (hv : v = 0) (X : MatrixFactorization T v) :
    cokernelπ (parityShift.obj X) ≫ (cokernelDesc hv (parityShift.obj X)).hom =
      -X.obj.d₀.hom :=
  cokernelπ_cokernelDesc_hom hv (parityShift.obj X)

variable [IsNoetherianRing T]

/-- For a factorization of the zero potential that is exact at its even component, the sequence
`0 ⟶ coker d₁ ⟶ X₁ ⟶ coker d₀ ⟶ 0`, whose first map is induced by `-d₀` and whose second map is
the projection, is short exact. Here `coker d₁` is the cokernel of the parity shift. -/
theorem shortExact_cokernelDesc_parityShift (hv : v = 0) (X : MatrixFactorization T v)
    (hX : Function.Exact X.obj.d₁.hom.hom X.obj.d₀.hom.hom) :
    (ShortComplex.mk (cokernelDesc hv (parityShift.obj X)) (ObjectProperty.homMk (cokernelπ X))
      (by
        apply ObjectProperty.hom_ext
        apply (cancel_epi (cokernelπ (parityShift.obj X))).1
        simp [cokernelπ_cokernelDesc_parityShift_assoc hv X])).ShortExact := by
  -- The descent `i` of `-d₀` satisfies `i (π' y) = -d₀ y` for the projection `π'` from `X₀`.
  have hi (y : X.obj.X₀) : (cokernelDesc hv (parityShift.obj X)).hom
      (cokernelπ (parityShift.obj X) y) = -X.obj.d₀.hom y :=
    ConcreteCategory.congr_hom (cokernelπ_cokernelDesc_parityShift hv X) y
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [← ShortComplex.exact_map_iff_of_faithful _
        (forget₂ (FGModuleCat.{u} T) (ModuleCat.{u} T)),
      ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    -- Both maps into `X₁` have the image of `d₀` as their range.
    intro z
    refine (exact_d₀_cokernelπ X z).trans ⟨?_, ?_⟩
    · rintro ⟨y, rfl⟩
      exact ⟨cokernelπ (parityShift.obj X) (-y), (hi (-y)).trans (by simp)⟩
    · rintro ⟨k, rfl⟩
      obtain ⟨y, rfl⟩ := cokernelπ_surjective _ k
      exact ⟨-y, (map_neg _ y).trans (hi y).symm⟩
  · -- If `d₀ y = 0` then `y = d₁ x` by exactness, so `y` vanishes in `coker d₁`.
    refine ConcreteCategory.mono_of_injective _ ((injective_iff_map_eq_zero _).2 fun k hk ↦ ?_)
    obtain ⟨y, rfl⟩ := cokernelπ_surjective _ k
    obtain ⟨x, rfl⟩ := (hX y).1 (neg_eq_zero.1 ((hi y).symm.trans hk))
    exact (exact_d₀_cokernelπ (parityShift.obj X) _).2 ⟨-x, by simp⟩
  · exact ConcreteCategory.epi_of_surjective _ (cokernelπ_surjective X)

/-- For a factorization of the zero potential that is exact at its even component, the projective
presentation `coker d₁ ⟶ X₁ ⟶ coker d₀` of `coker d₀` in finitely generated modules. Its kernel
term is the cokernel of the parity shift, and its middle term is the projective odd component. -/
-- Reducible, so that its kernel term is syntactically the cokernel of the parity shift when
-- stable loop objects are compared with that cokernel.
abbrev cokernelPresentation (hv : v = 0) (X : MatrixFactorization T v)
    (hX : Function.Exact X.obj.d₁.hom.hom X.obj.d₀.hom.hom) :
    (ExactStructure.abelian (FGModuleCat.{u} T)).ProjectivePresentation
      (cokernelFunctor.obj X) where
  K := cokernelFunctor.obj (parityShift.obj X)
  P := X.obj.X₁
  i := cokernelDesc hv (parityShift.obj X)
  p := ObjectProperty.homMk (cokernelπ X)
  zero := _
  conflation :=
    (ExactStructure.abelian_conflation _).2 (shortExact_cokernelDesc_parityShift hv X hX)
  isProjective := (ExactStructure.abelian_isProjective_iff _).2
    (FGModuleCat.projective_of_moduleProjective T X.obj.X₁)

/-- In the stable category, the map induced by a closed even map `g` between the kernel terms of
`cokernelPresentation` is the cokernel of the parity shift of `g`. -/
theorem projectiveStableFunctor_map_cokernelPresentation_kernelMap (hv : v = 0)
    {X Y : MatrixFactorization T v} (hX : Function.Exact X.obj.d₁.hom.hom X.obj.d₀.hom.hom)
    (hY : Function.Exact Y.obj.d₁.hom.hom Y.obj.d₀.hom.hom) (g : X ⟶ Y) :
    (ExactStructure.abelian (FGModuleCat.{u} T)).projectiveStableFunctor.map
        ((cokernelPresentation hv X hX).kernelMap (cokernelPresentation hv Y hY)
          (cokernelFunctor.map g)) =
      (ExactStructure.abelian (FGModuleCat.{u} T)).projectiveStableFunctor.map
        (cokernelFunctor.map (parityShift.map g)) := by
  refine ExactStructure.projectiveStableFunctor_map_kernelMap_eq _ _ _ g.hom.f₁ _ ?_ ?_
  · apply ObjectProperty.hom_ext
    exact (cokernelπ_naturality g).symm
  · apply ObjectProperty.hom_ext
    apply (cancel_epi (cokernelπ (parityShift.obj X))).1
    dsimp only [ObjectProperty.FullSubcategory.comp_hom]
    rw [cokernelπ_naturality_assoc, cokernelπ_cokernelDesc_parityShift_assoc hv X,
      cokernelπ_cokernelDesc_parityShift hv Y, Preadditive.comp_neg, Preadditive.neg_comp,
      neg_inj]
    exact congrArg (fun k ↦ k.hom) g.hom.comm₀

end ZeroPotential

/-! ### Reduction modulo a non-zero-divisor potential -/

section Hypersurface

variable {S : Type u} [CommRing S] {w : S}

/-- An equation `f ≫ g = w • 𝟙` of finitely generated modules, as an equation of linear maps. -/
private theorem linearMap_comp_eq_smul {M N : FGModuleCat.{u} S} {f : M ⟶ N} {g : N ⟶ M}
    (h : f ≫ g = w • 𝟙 M) : g.hom.hom ∘ₗ f.hom.hom = w • LinearMap.id := by
  simpa only [ObjectProperty.FullSubcategory.comp_hom, ModuleCat.hom_comp,
    ObjectProperty.smul_hom, ObjectProperty.FullSubcategory.id_hom, ModuleCat.hom_smul,
    ModuleCat.hom_id] using congrArg (fun k ↦ k.hom.hom) h

/-- The reduction modulo a non-zero-divisor potential `w` of a finite-projective matrix
factorization is exact at its even component: the kernel of `d̄₀` is the image of `d̄₁`. -/
theorem exact_quotient_d₁_d₀ (hw : w ∈ nonZeroDivisors S) (X : MatrixFactorization S w) :
    Function.Exact
      ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X).obj.d₁.hom.hom
      ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X).obj.d₀.hom.hom :=
  LinearMap.exact_lTensor_quotient_span_singleton X.obj.d₀.hom.hom X.obj.d₁.hom.hom
    (linearMap_comp_eq_smul X.obj.d₁_comp_d₀)
    (linearMap_comp_eq_smul X.obj.d₀_comp_d₁)
    (Module.Flat.isSMulRegular_of_nonZeroDivisors hw)

/-- The reduction modulo a non-zero-divisor potential `w` of a finite-projective matrix
factorization is exact at its odd component: the kernel of `d̄₁` is the image of `d̄₀`. -/
theorem exact_quotient_d₀_d₁ (hw : w ∈ nonZeroDivisors S) (X : MatrixFactorization S w) :
    Function.Exact
      ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X).obj.d₀.hom.hom
      ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X).obj.d₁.hom.hom :=
  LinearMap.exact_lTensor_quotient_span_singleton X.obj.d₁.hom.hom X.obj.d₀.hom.hom
    (linearMap_comp_eq_smul X.obj.d₀_comp_d₁)
    (linearMap_comp_eq_smul X.obj.d₁_comp_d₀)
    (Module.Flat.isSMulRegular_of_nonZeroDivisors hw)

variable [IsNoetherianRing S]

/-- **Syzygy of a matrix-factorization cokernel.** For a non-zero-divisor potential `w`, the
syzygy `Ω`, in the stable category of finitely generated `S/(w)`-modules, of the cokernel of the
reduction of `X` modulo `w` is the cokernel of the reduction of its parity shift `X[1]`,
naturally in `X`. -/
def quotientCokernelStableLoopIso (hw : w ∈ nonZeroDivisors S) :
    baseChangeFunctor (w := w) (Ideal.Quotient.mk (Ideal.span {w})) ⋙ cokernelFunctor ⋙
        (ExactStructure.abelian (FGModuleCat.{u} (S ⧸ Ideal.span {w}))).projectiveStableFunctor ⋙
          (ExactStructure.abelian_enoughProjectives
            (A := FGModuleCat.{u} (S ⧸ Ideal.span {w}))).stableLoop ≅
      parityShift ⋙ baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w})) ⋙ cokernelFunctor ⋙
        (ExactStructure.abelian (FGModuleCat.{u} (S ⧸ Ideal.span {w}))).projectiveStableFunctor :=
  NatIso.ofComponents
    (fun X ↦ ExactStructure.abelian_enoughProjectives.stableLoopObjIso
        (cokernelPresentation (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self w))
          _ (exact_quotient_d₁_d₀ hw X)) ≪≫
      (ExactStructure.abelian _).projectiveStableFunctor.mapIso
        (cokernelFunctor.mapIso ((parityShiftCompBaseChangeFunctorIso _).app X).symm))
    (fun {X Y} g ↦ by
      have h := (parityShiftCompBaseChangeFunctorIso (w := w)
        (Ideal.Quotient.mk (Ideal.span {w}))).inv.naturality g
      rw [Functor.comp_map, Functor.comp_map] at h
      simp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv]
      rw [ExactStructure.EnoughProjectives.stableLoop_map_comp_stableLoopObjIso_hom_assoc,
        projectiveStableFunctor_map_cokernelPresentation_kernelMap, Category.assoc,
        ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, h])

/-- A component of `quotientCokernelStableLoopIso` is the comparison of the stable loop object
with the kernel term of `cokernelPresentation`, followed by the cokernel of the comparison
between base change and parity shift. -/
@[simp]
theorem quotientCokernelStableLoopIso_hom_app (hw : w ∈ nonZeroDivisors S)
    (X : MatrixFactorization S w) :
    (quotientCokernelStableLoopIso hw).hom.app X =
      (ExactStructure.abelian_enoughProjectives.stableLoopObjIso
          (cokernelPresentation
            (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self w))
            _ (exact_quotient_d₁_d₀ hw X))).hom ≫
        (ExactStructure.abelian _).projectiveStableFunctor.map
          (cokernelFunctor.map ((parityShiftCompBaseChangeFunctorIso _).inv.app X)) :=
  (rfl)

/-- **Cokernels of matrix factorizations are `Ω`-periodic.** For a non-zero-divisor potential,
applying the syzygy `Ω` twice to the cokernel of the reduction of `X` modulo `w` returns that
cokernel, naturally in `X`: `Ω` corresponds to the parity shift, which squares to the identity. -/
def quotientCokernelStableLoopStableLoopIso (hw : w ∈ nonZeroDivisors S) :
    baseChangeFunctor (w := w) (Ideal.Quotient.mk (Ideal.span {w})) ⋙ cokernelFunctor ⋙
        (ExactStructure.abelian (FGModuleCat.{u} (S ⧸ Ideal.span {w}))).projectiveStableFunctor ⋙
          (ExactStructure.abelian_enoughProjectives
            (A := FGModuleCat.{u} (S ⧸ Ideal.span {w}))).stableLoop ⋙
          (ExactStructure.abelian_enoughProjectives
            (A := FGModuleCat.{u} (S ⧸ Ideal.span {w}))).stableLoop ≅
      baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w})) ⋙ cokernelFunctor ⋙
        (ExactStructure.abelian (FGModuleCat.{u} (S ⧸ Ideal.span {w}))).projectiveStableFunctor :=
  Functor.isoWhiskerRight (quotientCokernelStableLoopIso hw)
      (ExactStructure.abelian_enoughProjectives
        (A := FGModuleCat.{u} (S ⧸ Ideal.span {w}))).stableLoop ≪≫
    Functor.isoWhiskerLeft parityShift (quotientCokernelStableLoopIso hw) ≪≫
    Functor.isoWhiskerRight parityShiftCompParityShiftIso
      (baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w})) ⋙ cokernelFunctor ⋙
        (ExactStructure.abelian (FGModuleCat.{u} (S ⧸ Ideal.span {w}))).projectiveStableFunctor) ≪≫
    Functor.leftUnitor _

/-! ### Descent to the homotopy category -/

namespace HomotopyCategory

/-- **The stable cokernel functor intertwines parity shift and syzygy.** For a non-zero-divisor
potential `w`, the syzygy `Ω` of the cokernel of the reduction modulo `w` of a matrix
factorization is the cokernel of its parity shift, naturally on `HMF(S,w)`. -/
def quotientStableCokernelCompStableLoopIso (hw : w ∈ nonZeroDivisors S) :
    quotientStableCokernel (S := S) (w := w) ⋙
        (ExactStructure.abelian_enoughProjectives
          (A := FGModuleCat.{u} (S ⧸ Ideal.span {w}))).stableLoop ≅
      (parityShiftEquivalence (S := S) (w := w)).functor ⋙ quotientStableCokernel :=
  CategoryTheory.Quotient.natIsoLift _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (eqToIso quotientFunctor_comp_quotientStableCokernel) _ ≪≫
      quotientCokernelStableLoopIso hw ≪≫
      Functor.isoWhiskerLeft parityShift
        (eqToIso quotientFunctor_comp_quotientStableCokernel.symm) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (eqToIso quotientFunctor_comp_parityShiftEquivalence_functor.symm) _ ≪≫
      Functor.associator _ _ _)

/-- Precomposed with the quotient functor, the stable cokernel functor followed by `Ω` is base
change, cokernel, the stable quotient and `Ω`. -/
theorem quotientFunctor_comp_quotientStableCokernel_comp_stableLoop :
    (nullHomotopic (S := S) (w := w)).quotientFunctor ⋙ quotientStableCokernel ⋙
        (ExactStructure.abelian_enoughProjectives
          (A := FGModuleCat.{u} (S ⧸ Ideal.span {w}))).stableLoop =
      baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w})) ⋙ cokernelFunctor ⋙
        (ExactStructure.abelian (FGModuleCat.{u} (S ⧸ Ideal.span {w}))).projectiveStableFunctor ⋙
          (ExactStructure.abelian_enoughProjectives
            (A := FGModuleCat.{u} (S ⧸ Ideal.span {w}))).stableLoop := by
  rw [← Functor.assoc, quotientFunctor_comp_quotientStableCokernel]
  simp only [Functor.assoc]

/-- Precomposed with the quotient functor, the parity shift followed by the stable cokernel
functor is the parity shift followed by base change, cokernel and the stable quotient. -/
theorem quotientFunctor_comp_parityShift_comp_quotientStableCokernel :
    (nullHomotopic (S := S) (w := w)).quotientFunctor ⋙
        (parityShiftEquivalence (S := S) (w := w)).functor ⋙ quotientStableCokernel =
      parityShift ⋙ baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w})) ⋙ cokernelFunctor ⋙
        (ExactStructure.abelian (FGModuleCat.{u} (S ⧸ Ideal.span {w}))).projectiveStableFunctor :=
  by rw [← Functor.assoc, quotientFunctor_comp_parityShiftEquivalence_functor, Functor.assoc,
    quotientFunctor_comp_quotientStableCokernel]

/-- On a representative, `quotientStableCokernelCompStableLoopIso` is
`quotientCokernelStableLoopIso`, up to the identifications of the functors on representatives. -/
theorem quotientStableCokernelCompStableLoopIso_hom_app (hw : w ∈ nonZeroDivisors S)
    (X : MatrixFactorization S w) :
    (quotientStableCokernelCompStableLoopIso hw).hom.app
        ((nullHomotopic (S := S) (w := w)).quotientFunctor.obj X) =
      eqToHom (Functor.congr_obj quotientFunctor_comp_quotientStableCokernel_comp_stableLoop X) ≫
        (quotientCokernelStableLoopIso hw).hom.app X ≫
        eqToHom (Functor.congr_obj
          quotientFunctor_comp_parityShift_comp_quotientStableCokernel X).symm := by
  simp [quotientStableCokernelCompStableLoopIso, eqToHom_map]

/-- For a non-zero-divisor potential, the stable cokernel functor carries the shift by `1` of the
triangulated category `HMF(S,w)` to the syzygy `Ω`. -/
def shiftFunctorOneCompQuotientStableCokernelIso (hw : w ∈ nonZeroDivisors S) :
    shiftFunctor (HomotopyCategory (S := S) (w := w)) (1 : ℤ) ⋙ quotientStableCokernel ≅
      quotientStableCokernel ⋙
        (ExactStructure.abelian_enoughProjectives
          (A := FGModuleCat.{u} (S ⧸ Ideal.span {w}))).stableLoop :=
  Functor.isoWhiskerRight (shiftFunctorOneIso S w) _ ≪≫
    (quotientStableCokernelCompStableLoopIso hw).symm

/-- **Cokernels of matrix factorizations are `Ω`-periodic on `HMF(S,w)`.** For a non-zero-divisor
potential, `Ω² ∘ coker ≅ coker` as functors on the homotopy category. -/
def quotientStableCokernelCompStableLoopCompStableLoopIso (hw : w ∈ nonZeroDivisors S) :
    quotientStableCokernel (S := S) (w := w) ⋙
        (ExactStructure.abelian_enoughProjectives
          (A := FGModuleCat.{u} (S ⧸ Ideal.span {w}))).stableLoop ⋙
        (ExactStructure.abelian_enoughProjectives
          (A := FGModuleCat.{u} (S ⧸ Ideal.span {w}))).stableLoop ≅
      quotientStableCokernel :=
  CategoryTheory.Quotient.natIsoLift _
    ((Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerRight (eqToIso quotientFunctor_comp_quotientStableCokernel) _) _ ≪≫
      quotientCokernelStableLoopStableLoopIso hw ≪≫
      eqToIso quotientFunctor_comp_quotientStableCokernel.symm)

end HomotopyCategory

end Hypersurface

end TauCeti.MatrixFactorization
