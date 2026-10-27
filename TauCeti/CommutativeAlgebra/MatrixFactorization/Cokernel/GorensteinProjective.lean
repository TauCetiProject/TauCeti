/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Stable
public import TauCeti.Algebra.Homology.GorensteinProjective.Frobenius
public import TauCeti.Algebra.Homology.Periodic.Unfold

/-!
# Cokernels of matrix factorizations are Gorenstein-projective

Let `X = (X₀ --d₀--> X₁ --d₁--> X₀)` be a finite-projective matrix factorization of a
non-zero-divisor `w` of a commutative ring `S`, and let `X'` be its reduction modulo `w`, with
differentials `d₀'` and `d₁'` over the hypersurface ring `R = S/(w)`. Unfolding the reduced
two-periodic complex along the integers gives the complex

`⋯ → X₀' --d₀'--> X₁' --d₁'--> X₀' --d₀'--> X₁' → ⋯`

with `X₀'` in even degrees. Its terms are finitely generated projective `R`-modules and it is
acyclic (`quotientPeriodicComplex_acyclic`). It is also acyclic after applying `Hom_R(-, R)`: a
functional `φ` on `X₁'` killing the image of `d₀'` lifts to `ϕ : X₁ → S`, and `ϕ ∘ d₀ = w χ`
with `χ ∘ d₁ = ϕ` (`LinearMap.exact_comp_baseChange_quotient_span_singleton`). So the unfolded
complex is totally acyclic, a complete resolution of its degree-zero cycles
`ker d₀' ≅ coker d₀'`. Hence the cokernel of the reduction of `X` is a finitely generated
Gorenstein-projective `R`-module.

This lifts the cokernel of the reduction to a functor from matrix factorizations to
Gorenstein-projective `R`-modules. It sends null-homotopic maps to maps factoring through the
projective module `X₀'`, so it descends to a functor from the homotopy category `HMF(S,w)` to
the stable category of Gorenstein-projective `R`-modules. That stable category is the stable
category of a Frobenius exact category (`GorensteinProjectiveModuleCat.exactStructure_isFrobenius`),
so it carries Happel's triangulation. In contrast, finitely generated `R`-modules, whose stable
category is the target of `MatrixFactorization.HomotopyCategory.quotientStableCokernel`, need not
form a Frobenius exact category.

Only the non-zero-divisor hypothesis on `w` is used. No noetherian or regularity hypothesis is
needed. When `S` is a regular local ring, `R` is Gorenstein, so its finitely generated
Gorenstein-projective modules are its maximal Cohen–Macaulay modules (Buchweitz), and the
cokernel functor is an equivalence onto their stable category (Eisenbud, Buchweitz). Neither
statement is made here.

## Main definitions

* `TauCeti.MatrixFactorization.quotientGorensteinProjectiveCokernel`: the cokernel of the
  reduction modulo `w`, as a functor to finitely generated Gorenstein-projective
  `S/(w)`-modules.
* `TauCeti.MatrixFactorization.HomotopyCategory.quotientGorensteinProjectiveStableCokernel`: its
  descent to a functor from `HMF(S,w)` to the stable category of Gorenstein-projective
  `S/(w)`-modules.

## Main results

* `TauCeti.MatrixFactorization.isTotallyAcyclic_unfoldFunctor_obj_quotientPeriodicComplex_obj`:
  the unfolded reduction of a matrix factorization is a totally acyclic complex.
* `TauCeti.MatrixFactorization.isGorensteinProjective_cokernelFunctor_obj_baseChangeFunctor_obj`:
  the cokernel of the reduction is Gorenstein-projective.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Sections 5–6.
* R.-O. Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Mathematical Surveys
  and Monographs **262** (2021), Section 4: complete resolutions and the stable category of
  Gorenstein-projective modules.
-/

public section

noncomputable section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory Limits

variable {S : Type u} [CommRing S] {w : S}

/-! ### The complete resolution of the cokernel -/

/-- The two-periodic complex over `S/(w)` obtained by reducing a finite-projective matrix
factorization modulo a non-zero-divisor `w` remains exact after applying `Hom(-, S/(w))`: for
consecutive parities `a, b, c`, precomposition with the differentials `b ⟶ c` and `a ⟶ b` gives
an exact pair. -/
theorem exact_lcomp_quotientPeriodicComplex_d (hw : w ∈ nonZeroDivisors S)
    (X : MatrixFactorization S w) (a b c : ZMod 2) (hab : a + 1 = b) (hbc : b + 1 = c) :
    Function.Exact
      (LinearMap.lcomp (S ⧸ Ideal.span {w})ᵐᵒᵖ (S ⧸ Ideal.span {w})
        ((quotientPeriodicComplex.obj X).d b c).hom)
      (LinearMap.lcomp (S ⧸ Ideal.span {w})ᵐᵒᵖ (S ⧸ Ideal.span {w})
        ((quotientPeriodicComplex.obj X).d a b).hom) := by
  have hr : IsSMulRegular S w := Module.Flat.isSMulRegular_of_nonZeroDivisors hw
  -- The differentials of the reduced complex are, by definition of extension of scalars, the
  -- base changes of `d₀` and `d₁`, and precomposition `LinearMap.lcomp` is composition, so both
  -- cases are instances of the dual exactness of a reduced factorization.
  rcases (by decide : ∀ j : ZMod 2, j = 0 ∨ j = 1) a with rfl | rfl
  · obtain rfl : b = 1 := hab.symm
    obtain rfl : c = 0 := hbc.symm.trans (by decide)
    have : Module.Projective S ((forget₂ (FGModuleCat.{u} S) (ModuleCat.{u} S)).obj X.obj.X₁) :=
      X.property.2
    exact LinearMap.exact_comp_baseChange_quotient_span_singleton _ _
      (LinearMap.ext (d₁_comp_d₀_apply X)) (LinearMap.ext (d₀_comp_d₁_apply X)) hr
  · obtain rfl : b = 0 := hab.symm.trans (by decide)
    obtain rfl : c = 1 := hbc.symm
    have : Module.Projective S ((forget₂ (FGModuleCat.{u} S) (ModuleCat.{u} S)).obj X.obj.X₀) :=
      X.property.1
    exact LinearMap.exact_comp_baseChange_quotient_span_singleton _ _
      (LinearMap.ext (d₀_comp_d₁_apply X)) (LinearMap.ext (d₁_comp_d₀_apply X)) hr

/-- **The reduction of a matrix factorization is a complete resolution.** For a non-zero-divisor
`w`, unfolding along the integers the reduction modulo `w` of a finite-projective matrix
factorization gives a totally acyclic complex of finitely generated projective
`S/(w)`-modules. -/
theorem isTotallyAcyclic_unfoldFunctor_obj_quotientPeriodicComplex_obj
    (hw : w ∈ nonZeroDivisors S) (X : MatrixFactorization S w) :
    ((PeriodicComplex.unfoldFunctor (ModuleCat.{u} (S ⧸ Ideal.span {w})) 2).obj
      (quotientPeriodicComplex.obj X)).IsTotallyAcyclic where
  -- The components of the reduced complex are those of the reduced factorization, which are
  -- finitely generated projective modules.
  finite n := by
    rw [PeriodicComplex.unfoldFunctor_obj_X]
    generalize (n : ZMod 2) = a
    rcases (by decide : ∀ j : ZMod 2, j = 0 ∨ j = 1) a with rfl | rfl
    · exact (inferInstance : Module.Finite (S ⧸ Ideal.span {w})
        ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X).obj.X₀)
    · exact (inferInstance : Module.Finite (S ⧸ Ideal.span {w})
        ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X).obj.X₁)
  projective n := by
    rw [PeriodicComplex.unfoldFunctor_obj_X]
    generalize (n : ZMod 2) = a
    rcases (by decide : ∀ j : ZMod 2, j = 0 ∨ j = 1) a with rfl | rfl
    · exact ModuleCat.projective_of_categoryTheory_projective
        ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X).obj.X₀.obj
    · exact ModuleCat.projective_of_categoryTheory_projective
        ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X).obj.X₁.obj
  acyclic := (PeriodicComplex.unfoldFunctor_acyclic_iff _ _ _).2
    (quotientPeriodicComplex_acyclic hw X)
  exact_dual i j k hij hjk := by
    subst hij hjk
    rw [PeriodicComplex.unfoldFunctor_obj_d, PeriodicComplex.unfoldFunctor_obj_d]
    exact exact_lcomp_quotientPeriodicComplex_d hw X _ _ _ (by push_cast; ring)
      (by push_cast; ring)

/-- **Cokernels of matrix factorizations are Gorenstein-projective.** For a non-zero-divisor `w`,
the cokernel of the reduction modulo `w` of the even-to-odd differential of a finite-projective
matrix factorization is a Gorenstein-projective `S/(w)`-module. Its complete resolution is the
unfolded reduction, whose degree-zero cycles `ker d₀'` are identified with `coker d₀'` by
`d₁'`. -/
theorem isGorensteinProjective_cokernelFunctor_obj_baseChangeFunctor_obj
    (hw : w ∈ nonZeroDivisors S) (X : MatrixFactorization S w) :
    IsGorensteinProjective (S ⧸ Ideal.span {w})
      (cokernelFunctor.obj
        ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X)).obj := by
  let X' := (baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X
  let P := (PeriodicComplex.unfoldFunctor (ModuleCat.{u} (S ⧸ Ideal.span {w})) 2).obj
    (quotientPeriodicComplex.obj X)
  have hex₁₀ := exact_quotient_d₁_d₀ hw X
  have hex₀₁ := exact_quotient_d₀_d₁ hw X
  -- `d₁'` maps onto the kernel of `d₀'`, and its kernel is the image of `d₀'`.
  let g : X'.obj.X₁ →ₗ[S ⧸ Ideal.span {w}] LinearMap.ker X'.obj.d₀.hom.hom :=
    X'.obj.d₁.hom.hom.codRestrict _ fun y ↦ (hex₁₀ _).2 ⟨y, rfl⟩
  have hg : Function.Exact X'.obj.d₀.hom.hom g := fun y ↦
    Submodule.coe_eq_zero.symm.trans (hex₀₁ y)
  have hgs : Function.Surjective g := fun ⟨x, hx⟩ ↦ by
    obtain ⟨y, rfl⟩ := (hex₁₀ x).1 hx
    exact ⟨y, rfl⟩
  have hker : LinearMap.ker (P.sc' (-1) 0 1).g.hom = LinearMap.ker X'.obj.d₀.hom.hom := by
    -- The second map of `sc' (-1) 0 1` is `P.d 0 1`, the reduction of `d₀`; the reduction in the
    -- periodic complex and in the reduced factorization are both the base change of `d₀`.
    change LinearMap.ker (P.d 0 1).hom = _
    rw [show P.d 0 1 = (quotientPeriodicComplex.obj X).d 0 1 from
      PeriodicComplex.unfoldFunctor_obj_d _ _ _ 0]
    rfl
  exact (isGorensteinProjective_iff _).2
    ⟨P, isTotallyAcyclic_unfoldFunctor_obj_quotientPeriodicComplex_obj hw X,
      ⟨P.cyclesIsoSc' (-1) 0 1 (by simp) (by simp) ≪≫ (P.sc' (-1) 0 1).moduleCatCyclesIso ≪≫
        (LinearEquiv.ofEq _ _ hker).toModuleIso ≪≫
        (hg.linearEquivOfSurjective hgs).symm.toModuleIso ≪≫
        (ModuleCat.cokernelIsoRangeQuotient _).symm ≪≫ (cokernelFunctorObjIso X').symm⟩⟩

/-! ### The Gorenstein-projective cokernel functor -/

/-- The cokernel of the reduction modulo a non-zero-divisor `w`, as a functor from
finite-projective matrix factorizations of `w` to finitely generated Gorenstein-projective
`S/(w)`-modules. -/
def quotientGorensteinProjectiveCokernel (hw : w ∈ nonZeroDivisors S) :
    MatrixFactorization S w ⥤ GorensteinProjectiveModuleCat.{u} (S ⧸ Ideal.span {w}) :=
  ObjectProperty.lift _ (baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w})) ⋙
      cokernelFunctor ⋙ forget₂ (FGModuleCat.{u} (S ⧸ Ideal.span {w})) (ModuleCat.{u} _))
    (isGorensteinProjective_cokernelFunctor_obj_baseChangeFunctor_obj hw)

/-- The underlying module of `quotientGorensteinProjectiveCokernel` is the cokernel of the
reduction. -/
@[simp]
theorem quotientGorensteinProjectiveCokernel_obj_obj (hw : w ∈ nonZeroDivisors S)
    (X : MatrixFactorization S w) :
    ((quotientGorensteinProjectiveCokernel hw).obj X).obj =
      (cokernelFunctor.obj ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X)).obj :=
  (rfl)

/-- Followed by the inclusion into all modules, the Gorenstein-projective cokernel functor is the
cokernel of the reduction modulo `w`. -/
theorem quotientGorensteinProjectiveCokernel_comp_ι (hw : w ∈ nonZeroDivisors S) :
    quotientGorensteinProjectiveCokernel hw ⋙ (IsGorensteinProjective (S ⧸ Ideal.span {w})).ι =
      baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w})) ⋙ cokernelFunctor ⋙
        forget₂ (FGModuleCat.{u} (S ⧸ Ideal.span {w})) (ModuleCat.{u} _) :=
  (rfl)

instance (hw : w ∈ nonZeroDivisors S) : (quotientGorensteinProjectiveCokernel hw).Additive := by
  unfold quotientGorensteinProjectiveCokernel
  infer_instance

/-- The Gorenstein-projective cokernel functor sends a null-homotopic map to a map factoring
through a projective module, namely the reduction of the even component of its source. -/
theorem quotientGorensteinProjectiveCokernel_map_mem_projectiveStableIdeal
    (hw : w ∈ nonZeroDivisors S) {X Y : MatrixFactorization S w} {g : X ⟶ Y}
    (hg : g ∈ (nullHomotopic (S := S) (w := w)).hom X Y) :
    (quotientGorensteinProjectiveCokernel hw).map g ∈
      (GorensteinProjectiveModuleCat.exactStructure
        (S ⧸ Ideal.span {w})).projectiveStableIdeal.hom _ _ := by
  have hw₀ : Ideal.Quotient.mk (Ideal.span {w}) w = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self w)
  obtain ⟨h₀, h₁, hh⟩ := (mem_nullHomotopic_iff _).1
    (baseChangeFunctor_map_mem_nullHomotopic (Ideal.Quotient.mk (Ideal.span {w})) hg)
  let X' := (baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X
  let Y' := (baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj Y
  -- The reduced cokernel map factors through the finitely generated projective module `X₀'`.
  let Q : GorensteinProjectiveModuleCat.{u} (S ⧸ Ideal.span {w}) :=
    ⟨X'.obj.X₀.obj, have : Projective X'.obj.X₀.obj :=
      ModuleCat.projective_of_categoryTheory_projective _
      isGorensteinProjective_of_projective _⟩
  have hQ : (GorensteinProjectiveModuleCat.exactStructure _).isProjective Q := by
    rw [GorensteinProjectiveModuleCat.exactStructure_isProjective_iff]
    exact ModuleCat.projective_of_categoryTheory_projective _
  have hfac : (quotientGorensteinProjectiveCokernel hw).map g =
      (ObjectProperty.homMk (cokernelDesc hw₀ X').hom : _ ⟶ Q) ≫
        ObjectProperty.homMk (h₀.hom ≫ cokernelπ Y') := by
    apply ObjectProperty.hom_ext
    exact cokernelFunctor_map_hom_eq hw₀ _ h₀ h₁ hh
  rw [hfac, ExactStructure.mem_projectiveStableIdeal_iff]
  exact ObjectProperty.factorsThrough_comp _ hQ _ _

namespace HomotopyCategory

/-- The **Gorenstein-projective stable cokernel functor** of the hypersurface `S/(w)`, for a
non-zero-divisor `w`: a finite-projective matrix factorization of `w` goes to the cokernel of its
even-to-odd differential reduced modulo `w`, in the stable category of finitely generated
Gorenstein-projective `S/(w)`-modules. Null-homotopic maps are killed, so this is a functor on
the homotopy category `HMF(S,w)`. -/
def quotientGorensteinProjectiveStableCokernel (hw : w ∈ nonZeroDivisors S) :
    HomotopyCategory (S := S) (w := w) ⥤
      (GorensteinProjectiveModuleCat.exactStructure.{u}
        (S ⧸ Ideal.span {w})).ProjectiveStableCategory :=
  (nullHomotopic (S := S) (w := w)).lift
    (quotientGorensteinProjectiveCokernel hw ⋙
      (GorensteinProjectiveModuleCat.exactStructure (S ⧸ Ideal.span {w})).projectiveStableFunctor)
    (by
      intro X Y g hg
      rw [Functor.mem_kerIdeal_hom, Functor.comp_map,
        MorphismIdeal.quotientFunctor_map_eq_zero_iff]
      exact quotientGorensteinProjectiveCokernel_map_mem_projectiveStableIdeal hw hg)

instance (hw : w ∈ nonZeroDivisors S) :
    (quotientGorensteinProjectiveStableCokernel hw).Additive := by
  unfold quotientGorensteinProjectiveStableCokernel
  infer_instance

/-- The Gorenstein-projective stable cokernel functor is induced by the Gorenstein-projective
cokernel functor. -/
theorem quotientFunctor_comp_quotientGorensteinProjectiveStableCokernel
    (hw : w ∈ nonZeroDivisors S) :
    (nullHomotopic (S := S) (w := w)).quotientFunctor ⋙
        quotientGorensteinProjectiveStableCokernel hw =
      quotientGorensteinProjectiveCokernel hw ⋙
        (GorensteinProjectiveModuleCat.exactStructure
          (S ⧸ Ideal.span {w})).projectiveStableFunctor := by
  unfold quotientGorensteinProjectiveStableCokernel
  exact CategoryTheory.Quotient.lift_spec _ _ _

end HomotopyCategory

end TauCeti.MatrixFactorization
