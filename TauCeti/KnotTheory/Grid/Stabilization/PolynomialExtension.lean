/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import TauCeti.Algebra.Homology.PolynomialExtension
public import TauCeti.Algebra.MvPolynomial.Equiv
public import TauCeti.KnotTheory.Grid.Stabilization.Cone

/-!
# The center complex of a stabilized grid is a polynomial extension

Let `G` be a grid diagram of size `n`, let `s` be a column, and let
`G' = G.stabilizeX s.castSucc (G.X s).castSucc s` be the stabilization splitting the `X`-marking
of column `s`. Write `A = R[V₀, …, V_{n-1}]` and `S = R[V₀, …, V_n]` for the coefficient rings of
`GC⁻(G)` and `GC⁻(G')`. The columns of `G` become the columns `s.castSucc.succAbove c` of `G'`;
the remaining column `s.castSucc` carries the new `O`-marking, and the old `O`-marking of column
`s` now sits in column `s.succ`. Renaming the variables accordingly makes `S` an `A`-algebra, and
singling out the new variable identifies `S` with the polynomial ring `A[X]`, with
`X = V_{s.castSucc}` (`MvPolynomial.finSuccEquiv'`).

By `TauCeti.KnotTheory.Grid.Stabilization.Cone`, `GC⁻(G')` is the mapping cone of the connecting
map from the *center complex* `I`, spanned by the grid states of `G`, whose differential is that
of `GC⁻(G)` with the variables renamed into `S`. This file shows that, after restricting scalars
from `S` to `A`, `I` is the polynomial extension `A[X] ⊗[A] GC⁻(G)`
(`polynomialExtensionIsoStabilizeXCenter`), with multiplication by a polynomial `q` on
the extension corresponding to multiplication by its image in `S`.

Under this identification multiplication by `V_{s.succ} + V_{s.castSucc}` on `I` is
multiplication by `X - V_s` on `A[X] ⊗[A] GC⁻(G)`, because the ring has characteristic two. The
mapping cone of the latter is homotopy equivalent to `GC⁻(G)`
(`HomologicalComplex.polynomialExtensionMulXSubCHomotopyEquiv`), so the mapping cone of
multiplication by `V_{s.succ} + V_{s.castSucc}` on `I` is homotopy equivalent to `GC⁻(G)` as a
complex of `A`-modules (`stabilizeXCenterConeHomotopyEquiv`). On the summand `I` of that cone the
equivalence is evaluation at `X = V_s`, which merges the variables `V_{s.castSucc}` and `V_{s.succ}`
of `G'` into the variable `V_s` of `G`.

This is the cone to which the pair `(𝟙, H_I^N)` of `TauCeti.KnotTheory.Grid.Stabilization.XHomotopy`
maps `GC⁻(G') = Cone(∂_I^N)`, so the equivalence here is the step comparing that cone with `GC⁻(G)`
in the proof of stabilization invariance of `GH⁻`.

## Main definitions

* `TauCeti.GridDiagram.polynomialExtensionIsoStabilizeXCenter`: the isomorphism of
  complexes of `A`-modules between `A[X] ⊗[A] GC⁻(G)` and the center complex.
* `TauCeti.GridDiagram.stabilizeXCenterConeHomotopyEquiv`: the homotopy equivalence between the
  mapping cone of multiplication by `V_{s.succ} + V_{s.castSucc}` on the center complex and
  `GC⁻(G)`.

## Main results

* `TauCeti.GridDiagram.polynomialExtensionIsoStabilizeXCenter_hom_f_tmul`: the isomorphism sends
  `p ⊗ f` to the image of `p` in `S` times `f` with its coefficients renamed into `S`.
* `TauCeti.GridDiagram.polynomialExtensionMul_comp_polynomialExtensionIsoStabilizeXCenter_hom`:
  the isomorphism intertwines multiplication by `q : A[X]` with multiplication by its image in `S`.
* `TauCeti.GridDiagram.map_inr_comp_stabilizeXCenterConeHomotopyEquiv_hom` and
  `TauCeti.GridDiagram.stabilizeXCenterConeHomotopyEquiv_inv`: the equivalence is evaluation at
  `V_s` on the summand `I` of the cone, and its inverse includes `GC⁻(G)` into that summand as the
  constant polynomials.

## References

The identification of the center complex with the polynomial extension `GC⁻(G)[V₁]`, and of the
cone of `V₁ - V₂` on it with `GC⁻(G)`, are steps of the stabilization argument in
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.2, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.2. The
comparison of the whole stabilized complex with that cone is not carried out here.
-/

public section

open CategoryTheory MonoidalCategory HomologicalComplex MvPolynomial TensorProduct

namespace TauCeti

namespace GridDiagram

universe u

variable {n : ℕ} (G : GridDiagram n) (s : Fin n) (R : Type u) [CommRing R]

local notation "A" => MvPolynomial (Fin n) R
local notation "S" => MvPolynomial (Fin (n + 1)) R

/-! ### The underlying modules -/

/-- Coefficientwise, the identification `A[X] ≃ S` singling out the new variable, as an
`A`-linear map to the restriction of scalars of `GridState n →₀ S`. -/
private noncomputable def centerCoefficientEquiv :
    (GridState n →₀ Polynomial A) ≃ₗ[A]
      (ModuleCat.restrictScalars
        (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).obj
        (ModuleCat.of S (GridState n →₀ S)) where
  toFun f := Finsupp.mapRange (finSuccEquiv' R s.castSucc).symm (map_zero _) f
  -- The restriction of scalars of `GridState n →₀ S` has, by definition, the same elements.
  -- The explicit identifications below in both `invFun` and `right_inv` tell Lean to use that
  -- underlying `Finsupp`; they are needed because the expected type is a restricted module.
  invFun g := Finsupp.mapRange (finSuccEquiv' R s.castSucc) (map_zero _)
    (show GridState n →₀ S from g)
  map_add' f g := Finsupp.mapRange_add (map_add _) f g
  map_smul' a f := by
    refine Eq.trans ?_
      (ModuleCat.restrictScalars.smul_def (M := ModuleCat.of S (GridState n →₀ S)) _ a _).symm
    refine Finsupp.ext fun x => ?_
    simp [Polynomial.smul_eq_C_mul]
  left_inv f := Finsupp.ext fun x => by simp
  right_inv g := Finsupp.ext fun x =>
    (finSuccEquiv' R s.castSucc).symm_apply_apply ((show GridState n →₀ S from g) x)

/-- The `A`-linear identification of `A[X] ⊗[A] GC⁻(G)` with the restriction of scalars of the
chain module of the center complex. -/
private noncomputable def centerExtensionEquiv :
    Polynomial A ⊗[A] GridChainMinus R n ≃ₗ[A]
      (ModuleCat.restrictScalars
        (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).obj
        (ModuleCat.of S (GridState n →₀ S)) :=
  finsuppScalarRight A A (Polynomial A) (GridState n) ≪≫ₗ centerCoefficientEquiv s R

/-- The identification sends `p ⊗ f` to the image of `p` in `S` times `f` with its coefficients
renamed into `S`. -/
private theorem centerExtensionEquiv_tmul (p : Polynomial A) (f : GridChainMinus R n) :
    centerExtensionEquiv s R (p ⊗ₜ f) =
      ((finSuccEquiv' R s.castSucc).symm p •
        Finsupp.mapRange (rename s.castSucc.succAbove) (map_zero _) f : GridState n →₀ S) := by
  refine Finsupp.ext fun x => ?_
  -- By definition, the coefficient at `x` is `ε⁻¹` applied to the coefficient of
  -- `finsuppScalarRight (p ⊗ f)` at `x`.
  refine (congrArg (finSuccEquiv' R s.castSucc).symm
    (finsuppScalarRight_apply_tmul_apply p f x)).trans ?_
  simp [Polynomial.smul_eq_C_mul, mul_comm]

private theorem centerExtensionEquiv_tmul_unblockedDifferential (p : Polynomial A)
    (f : GridChainMinus R n) :
    centerExtensionEquiv s R (p ⊗ₜ G.unblockedDifferential R f) =
      G.stabilizeXCenterDifferential s R (centerExtensionEquiv s R (p ⊗ₜ f)) := by
  rw [centerExtensionEquiv_tmul, centerExtensionEquiv_tmul, map_smul,
    stabilizeXCenterDifferential_mapRange_rename]

private theorem centerExtensionEquiv_mul_tmul (q p : Polynomial A) (f : GridChainMinus R n) :
    centerExtensionEquiv s R ((q * p) ⊗ₜ f) =
      (finSuccEquiv' R s.castSucc).symm q • centerExtensionEquiv s R (p ⊗ₜ f) := by
  rw [centerExtensionEquiv_tmul, centerExtensionEquiv_tmul, map_mul, mul_smul]
  -- The `S`-action on the restriction of scalars is, by definition, the original one.
  rfl

/-- `centerExtensionEquiv` as an isomorphism in `ModuleCat A`. -/
private noncomputable def centerExtensionIso :
    ModuleCat.of A (Polynomial A ⊗[A] GridChainMinus R n) ≅
      (ModuleCat.restrictScalars
        (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).obj
        (ModuleCat.of S (GridState n →₀ S)) :=
  (centerExtensionEquiv s R).toModuleIso

private theorem centerExtensionIso_hom_comp :
    (centerExtensionIso s R).hom ≫
        (ModuleCat.restrictScalars
          (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).map
          (ModuleCat.ofHom (G.stabilizeXCenterDifferential s R)) =
      ModuleCat.of A (Polynomial A) ◁ ModuleCat.ofHom (G.unblockedDifferential R) ≫
        (centerExtensionIso s R).hom :=
  -- On `p ⊗ f`, both sides are by definition the two sides of
  -- `centerExtensionEquiv_tmul_unblockedDifferential`.
  ModuleCat.hom_ext (TensorProduct.ext' fun p f =>
    (G.centerExtensionEquiv_tmul_unblockedDifferential s R p f).symm)

private theorem whiskerRight_mulLeft_comp_centerExtensionIso_hom (q : Polynomial A) :
    ModuleCat.ofHom (LinearMap.mulLeft A q) ▷ ModuleCat.of A (GridChainMinus R n) ≫
        (centerExtensionIso s R).hom =
      (centerExtensionIso s R).hom ≫
        (ModuleCat.restrictScalars
          (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).map
        ((finSuccEquiv' R s.castSucc).symm q • 𝟙 (ModuleCat.of S (GridState n →₀ S))) :=
  -- On `p ⊗ f`, both sides are by definition the two sides of `centerExtensionEquiv_mul_tmul`.
  ModuleCat.hom_ext (TensorProduct.ext' fun p f => centerExtensionEquiv_mul_tmul s R q p f)

private theorem finSuccEquiv'_symm_X_sub_C [CharP R 2] :
    (finSuccEquiv' R s.castSucc).symm (Polynomial.X - Polynomial.C (MvPolynomial.X s)) =
      (MvPolynomial.X s.succ + MvPolynomial.X s.castSucc : S) := by
  rw [map_sub, finSuccEquiv'_symm_X, finSuccEquiv'_symm_C, rename_X, Fin.succAbove_castSucc_self,
    CharTwo.sub_eq_add]
  exact add_comm _ _

/-! ### The center complex -/

variable [CharP R 2]

/-- The unique component of `polynomialExtensionIsoStabilizeXCenter`. -/
private noncomputable def polynomialExtensionXIso :
    (G.unblockedComplex R).polynomialExtension.X () ≅
      (ModuleCat.restrictScalars
        (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).obj
        ((G.stabilizeXCenterComplex s R).X ()) :=
  MonoidalCategory.whiskerLeftIso (ModuleCat.of A (Polynomial A))
      (eqToIso (G.unblockedComplex_X R ())) ≪≫ centerExtensionIso s R ≪≫
    (ModuleCat.restrictScalars
      (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).mapIso
      (eqToIso (G.stabilizeXCenterComplex_X s R ()).symm)

private theorem polynomialExtensionXIso_hom :
    (G.polynomialExtensionXIso s R).hom =
      ModuleCat.of A (Polynomial A) ◁ eqToHom (G.unblockedComplex_X R ()) ≫
        (centerExtensionIso s R).hom ≫
          (ModuleCat.restrictScalars
            (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).map
            (eqToHom (G.stabilizeXCenterComplex_X s R ()).symm) :=
  rfl

/-- **The center complex is the polynomial extension of `GC⁻(G)`.** After restricting scalars
from `S = R[V₀, …, V_n]` to `A = R[V₀, …, V_{n-1}]` along the renaming of the columns of `G` into
those of the stabilization, the complex of center states is isomorphic to `A[X] ⊗[A] GC⁻(G)`.
The isomorphism sends `p ⊗ x`, for `x` a grid state of `G`, to the image of `p` in `S` under
`X ↦ V_{s.castSucc}` times the center state `x`. -/
noncomputable def polynomialExtensionIsoStabilizeXCenter :
    (G.unblockedComplex R).polynomialExtension ≅
      ((ModuleCat.restrictScalars
        (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).mapHomologicalComplex
          _).obj
        (G.stabilizeXCenterComplex s R) :=
  Hom.isoOfComponents (fun _ => G.polynomialExtensionXIso s R) (by
    rintro ⟨⟩ ⟨⟩ -
    simp [polynomialExtensionXIso_hom, reassoc_of% (G.centerExtensionIso_hom_comp s R)])

/-- Up to the identifications of the chain modules with their underlying free modules, the
component of `polynomialExtensionIsoStabilizeXCenter` is `centerExtensionIso`. -/
private theorem polynomialExtensionIsoStabilizeXCenter_hom_f_eq :
    ModuleCat.of A (Polynomial A) ◁ eqToHom (G.unblockedComplex_X R ()).symm ≫
        (G.polynomialExtensionIsoStabilizeXCenter s R).hom.f () ≫
          (ModuleCat.restrictScalars
            (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).map
            (eqToHom (G.stabilizeXCenterComplex_X s R ())) =
      (centerExtensionIso s R).hom := by
  simp [polynomialExtensionIsoStabilizeXCenter, polynomialExtensionXIso_hom]

/-- On a pure tensor `p ⊗ f`, the identification of `A[X] ⊗[A] GC⁻(G)` with the center complex
is the image of `p` in `S` times `f` with its coefficients renamed into `S`. The `eqToHom`s
identify the chain modules of `GC⁻(G)` and of the center complex with their underlying free
modules. -/
theorem polynomialExtensionIsoStabilizeXCenter_hom_f_tmul (p : Polynomial A)
    (f : GridChainMinus R n) :
    (ModuleCat.of A (Polynomial A) ◁ eqToHom (G.unblockedComplex_X R ()).symm ≫
        (G.polynomialExtensionIsoStabilizeXCenter s R).hom.f () ≫
          (ModuleCat.restrictScalars
            (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).map
            (eqToHom (G.stabilizeXCenterComplex_X s R ()))) (p ⊗ₜ[A] f) =
      (finSuccEquiv' R s.castSucc).symm p •
        Finsupp.mapRange (rename s.castSucc.succAbove) (map_zero _) f := by
  rw [polynomialExtensionIsoStabilizeXCenter_hom_f_eq]
  exact centerExtensionEquiv_tmul s R p f

/-- The identification of the center complex with the polynomial extension of `GC⁻(G)`
intertwines multiplication by a polynomial `q : A[X]` with multiplication by its image in `S`
under `X ↦ V_{s.castSucc}`. -/
@[reassoc]
theorem polynomialExtensionMul_comp_polynomialExtensionIsoStabilizeXCenter_hom
    (q : Polynomial A) :
    (G.unblockedComplex R).polynomialExtensionMul q ≫
        (G.polynomialExtensionIsoStabilizeXCenter s R).hom =
      (G.polynomialExtensionIsoStabilizeXCenter s R).hom ≫
        ((ModuleCat.restrictScalars
          (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).mapHomologicalComplex
            _).map
          ((finSuccEquiv' R s.castSucc).symm q • 𝟙 (G.stabilizeXCenterComplex s R)) := by
  ext ⟨⟩ : 1
  simp [polynomialExtensionIsoStabilizeXCenter, polynomialExtensionXIso_hom,
    reassoc_of% whiskerRight_mulLeft_comp_centerExtensionIso_hom, ← Functor.map_comp]

/-! ### The mapping cone of `V_{s.succ} + V_{s.castSucc}` -/

/-- **The cone of `V_{s.succ} + V_{s.castSucc}` on the center complex is `GC⁻(G)`.** After
restricting scalars to `A = R[V₀, …, V_{n-1}]`, the mapping cone of multiplication by
`V_{s.succ} + V_{s.castSucc}` on the complex of center states of the stabilization is homotopy
equivalent to `GC⁻(G)`. In characteristic two this multiplication is multiplication by
`X - V_s` on the polynomial extension `A[X] ⊗[A] GC⁻(G)`, whose cone is homotopy equivalent to
`GC⁻(G)` by evaluation at `V_s`. -/
noncomputable def stabilizeXCenterConeHomotopyEquiv :
    HomotopyEquiv
      (((ModuleCat.restrictScalars
        (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).mapHomologicalComplex
          _).obj
        (homotopyCofiber ((MvPolynomial.X s.succ + MvPolynomial.X s.castSucc : S) •
          𝟙 (G.stabilizeXCenterComplex s R))))
      (G.unblockedComplex R) :=
  (HomotopyEquiv.ofIso
    (homotopyCofiber.mapHomologicalComplexObjIso _ _ ≪≫
      homotopyCofiber.mapArrowIso _ _ (fun j => ⟨j, ComplexShape.refl_rel j⟩)
        (Arrow.isoMk (G.polynomialExtensionIsoStabilizeXCenter s R).symm
          (G.polynomialExtensionIsoStabilizeXCenter s R).symm (by
            dsimp only [Arrow.mk_hom, Iso.symm_hom]
            rw [Iso.inv_comp_eq, ← finSuccEquiv'_symm_X_sub_C, ← Category.assoc,
              ← polynomialExtensionMul_comp_polynomialExtensionIsoStabilizeXCenter_hom,
              Category.assoc, Iso.hom_inv_id, Category.comp_id])))).trans
    ((G.unblockedComplex R).polynomialExtensionMulXSubCHomotopyEquiv
      (fun j => ⟨j, ComplexShape.refl_rel j⟩) (MvPolynomial.X s))

/-- On the summand of the cone given by the center complex, the homotopy equivalence
`stabilizeXCenterConeHomotopyEquiv` is evaluation at `X = V_s` on the polynomial extension of
`GC⁻(G)`. -/
@[reassoc (attr := simp)]
theorem map_inr_comp_stabilizeXCenterConeHomotopyEquiv_hom :
    ((ModuleCat.restrictScalars
      (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).mapHomologicalComplex _).map
        (homotopyCofiber.inr _) ≫
        (G.stabilizeXCenterConeHomotopyEquiv s R).hom =
      (G.polynomialExtensionIsoStabilizeXCenter s R).inv ≫
        (G.unblockedComplex R).polynomialExtensionEval (MvPolynomial.X s) := by
  simp only [stabilizeXCenterConeHomotopyEquiv, HomotopyEquiv.ofIso, HomotopyEquiv.trans_hom,
    Iso.trans_hom, Category.assoc]
  rw [homotopyCofiber.inr_mapHomologicalComplexObjIso_hom_assoc, homotopyCofiber.mapArrowIso_hom,
    homotopyCofiber.mapArrowHom, homotopyCofiber.inr_desc_assoc]
  simp

/-- Evaluation from the center cone kills its shifted summand. -/
theorem map_inlX_comp_stabilizeXCenterConeHomotopyEquiv_hom :
    (ModuleCat.restrictScalars
      (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).map
        (homotopyCofiber.inlX
          ((MvPolynomial.X s.succ + MvPolynomial.X s.castSucc : S) •
            𝟙 (G.stabilizeXCenterComplex s R)) () () (ComplexShape.refl_rel ())) ≫
      (G.stabilizeXCenterConeHomotopyEquiv s R).hom.f () = 0 := by
  simp only [stabilizeXCenterConeHomotopyEquiv, HomotopyEquiv.ofIso,
    HomotopyEquiv.trans_hom, HomologicalComplex.comp_f, Iso.trans_hom]
  have h : (homotopyCofiber.mapHomologicalComplexObjIso
      ((MvPolynomial.X s.succ + MvPolynomial.X s.castSucc : S) •
        𝟙 (G.stabilizeXCenterComplex s R))
      (ModuleCat.restrictScalars
        (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S))).hom.f () =
      (homotopyCofiber.mapHomologicalComplexObjXIso
        ((MvPolynomial.X s.succ + MvPolynomial.X s.castSucc : S) •
          𝟙 (G.stabilizeXCenterComplex s R))
        (ModuleCat.restrictScalars
          (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)) ()).hom := by
    rfl
  rw [h]
  have hc :
      (ModuleCat.restrictScalars
        (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).map
          (homotopyCofiber.inlX
            ((MvPolynomial.X s.succ + MvPolynomial.X s.castSucc : S) •
              𝟙 (G.stabilizeXCenterComplex s R)) () () (ComplexShape.refl_rel ())) ≫
        (homotopyCofiber.mapHomologicalComplexObjXIso _
          (ModuleCat.restrictScalars
            (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)) ()).hom =
      homotopyCofiber.inlX
        (((ModuleCat.restrictScalars
          (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).mapHomologicalComplex
            _).map
          ((MvPolynomial.X s.succ + MvPolynomial.X s.castSucc : S) •
            𝟙 (G.stabilizeXCenterComplex s R))) () () (ComplexShape.refl_rel ()) := by
    rw [← homotopyCofiber.inlX_mapHomologicalComplexObjXIso_inv,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [← Category.assoc]
  rw [hc]
  simp

/-- The homotopy inverse of `stabilizeXCenterConeHomotopyEquiv` includes `GC⁻(G)` into the
summand of the cone given by the center complex, as the constant polynomials of its polynomial
extension. -/
@[simp]
theorem stabilizeXCenterConeHomotopyEquiv_inv :
    (G.stabilizeXCenterConeHomotopyEquiv s R).inv =
      (G.unblockedComplex R).polynomialExtensionConst ≫
        (G.polynomialExtensionIsoStabilizeXCenter s R).hom ≫
          ((ModuleCat.restrictScalars
            (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).mapHomologicalComplex
              _).map
            (homotopyCofiber.inr _) := by
  have h := homotopyCofiber.inr_mapHomologicalComplexObjIso_hom
    ((MvPolynomial.X s.succ + MvPolynomial.X s.castSucc : S) • 𝟙 (G.stabilizeXCenterComplex s R))
    (ModuleCat.restrictScalars
      (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S))
  rw [← Iso.eq_comp_inv] at h
  simp only [stabilizeXCenterConeHomotopyEquiv, HomotopyEquiv.ofIso, HomotopyEquiv.trans_inv,
    polynomialExtensionMulXSubCHomotopyEquiv_inv, Iso.trans_inv, Category.assoc]
  rw [homotopyCofiber.mapArrowIso_inv, homotopyCofiber.mapArrowHom,
    homotopyCofiber.inr_desc_assoc, Category.assoc, ← h]
  simp

end GridDiagram

end TauCeti
