/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Module.Projective
public import TauCeti.Algebra.Homology.Ext.Basic
public import TauCeti.Algebra.Homology.UniversalCoefficient.Basic

/-!
# The universal coefficient sequence for the dual of a cochain complex

Let `K` be a cochain complex indexed by `ℤ` in a `k`-linear abelian category `C`, and let `Y : C`.
The dual of `K` with coefficients in `Y` is Mathlib's Hom complex
`linearHomComplex k K Y[0]` into the complex `Y[0]` concentrated in degree `0`. Its term in degree
`i` is identified with `K⁻ⁱ ⟶ Y` by `CochainComplex.HomComplex.Cochain.toSingleEquiv`, with
differential `f ↦ (-1)^(i+1) d_K ≫ f`. This file proves the universal coefficient theorem for it:

`0 ⟶ Ext¹(H¹⁻ⁱ(K), Y) ⟶ Hⁱ(Hom(K, Y[0])) ⟶ (H⁻ⁱ(K) ⟶ Y) ⟶ 0`

is exact when the cycles of `K` split off its terms and are projective, and the Kronecker map
`Hⁱ(Hom(K, Y[0])) ⟶ (H⁻ⁱ(K) ⟶ Y)` is bijective when `Y` is injective, for instance for a vector
space over a field. Both cohomological degrees are reversed, and the `Ext` term sits one degree
higher: torsion in `H¹⁻ⁱ(K)` contributes to `Hⁱ` of the dual.

The theorem is deduced from the universal coefficient theorem for chain complexes,
`TauCeti.ChainComplex.exact_extToHomology_kronecker`. The chain complex `K.negChainComplex` has
`K⁻ᵐ` in degree `m` and differential `(-1)^m d_K`; the sign makes the dual of `K` *equal* to
Mathlib's `ChainComplex.linearYonedaObj` of `K.negChainComplex` term by term, with no sign in the
identification `CochainComplex.linearHomComplexSingleIso`. The sign does not change homology:
`CochainComplex.negChainComplexHomologyIso` identifies `Hₘ` of `K.negChainComplex` with `H⁻ᵐ(K)`.

## Main definitions

* `CochainComplex.negChainComplex`: the chain complex `K⁻ᵐ` with differential `(-1)^m d_K`.
* `CochainComplex.linearHomComplexSingleIso`: `Hom(K, Y[0]) ≅ Hom(K.negChainComplex, Y)`.
* `CochainComplex.negChainComplexHomologyIso`: `Hₘ(K.negChainComplex) ≅ H⁻ᵐ(K)`.
* `CochainComplex.kronecker`: the Kronecker map `Hⁱ(Hom(K, Y[0])) →ₗ[k] (H⁻ⁱ(K) ⟶ Y)`, evaluating
  cocycles on cycles (`CochainComplex.homologyπ_kronecker_homologyπ`).
* `CochainComplex.extToHomology`: the map `Ext¹(H¹⁻ⁱ(K), Y) →ₗ[k] Hⁱ(Hom(K, Y[0]))`.

## Main results

* `CochainComplex.kronecker_bijective` and `CochainComplex.kroneckerEquiv`: for an injective `Y`,
  `Hⁱ(Hom(K, Y[0])) ≃ₗ[k] (H⁻ⁱ(K) ⟶ Y)`.
* `CochainComplex.kronecker_surjective_of_isSplitMono`, `CochainComplex.extToHomology_injective` and
  `CochainComplex.exact_extToHomology_kronecker`: the universal coefficient sequence is exact.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1, Theorem 3.2.
* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Theorem 3.6.5.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex Abelian

universe w

namespace CochainComplex

section Preadditive

variable {C : Type*} [Category* C] [Preadditive C] (K : CochainComplex C ℤ)

/-- The chain complex with the term `K⁻ᵐ` in degree `m` and the differential `(-1)^m d_K`. Its
`Hom` complex into an object is the dual of `K` with no further sign
(`CochainComplex.linearHomComplexSingleIso`), and its homology in degree `m` is that of `K` in
degree `-m` (`CochainComplex.negChainComplexHomologyIso`). -/
@[expose, simps]
def negChainComplex : ChainComplex C ℤ where
  X m := K.X (-m)
  d m m' := m.negOnePow • K.d (-m) (-m')
  shape m m' h := by
    rw [K.shape, smul_zero]
    simp only [ComplexShape.down_Rel, ComplexShape.up_Rel] at h ⊢
    omega
  d_comp_d' m m' m'' _ _ := by
    rw [Linear.units_smul_comp, Linear.comp_units_smul, K.d_comp_d, smul_zero, smul_zero]

/-- The isomorphism between the short complexes computing `Hₘ` of `K.negChainComplex` and `Hᵖ` of
`K`, for `m + p = 0`. Its components are the identifications of the terms `K⁻ᵐ⁻¹ = Kᵖ⁻¹`,
`K⁻ᵐ = Kᵖ` and `K⁻ᵐ⁺¹ = Kᵖ⁺¹`, the outer ones with the signs of the differentials. -/
def negChainComplexScIso (m p : ℤ) (hmp : m + p = 0) : K.negChainComplex.sc m ≅ K.sc p :=
  ShortComplex.isoMk ((m + 1).negOnePow • K.XIsoOfEq (by simp; omega)) (K.XIsoOfEq (by omega))
    (m.negOnePow • K.XIsoOfEq (by simp; omega))
    -- The terms of `K.negChainComplex` are those of `K` only up to unfolding, so both squares are
    -- restated by `change` with the differentials of `K`.
    (by
      change ((m + 1).negOnePow • (K.XIsoOfEq (by simp; omega)).hom) ≫
          K.d ((ComplexShape.up ℤ).prev p) p =
        (((ComplexShape.down ℤ).prev m).negOnePow •
          K.d (-(ComplexShape.down ℤ).prev m) (-m)) ≫ (K.XIsoOfEq (by omega)).hom
      rw [Linear.units_smul_comp, XIsoOfEq_hom_comp_d, Linear.units_smul_comp, d_comp_XIsoOfEq_hom,
        ChainComplex.prev])
    (by
      change (K.XIsoOfEq (by omega)).hom ≫ K.d p ((ComplexShape.up ℤ).next p) =
        (m.negOnePow • K.d (-m) (-(ComplexShape.down ℤ).next m)) ≫
          (m.negOnePow • (K.XIsoOfEq (by simp; omega)).hom)
      rw [XIsoOfEq_hom_comp_d, Linear.comp_units_smul, Linear.units_smul_comp, d_comp_XIsoOfEq_hom,
        smul_smul, Int.units_mul_self, one_smul])

end Preadditive

section Homology

variable {C : Type*} [Category* C] [Preadditive C] [CategoryWithHomology C]
  (K : CochainComplex C ℤ)

/-- **The homology of `K.negChainComplex`** in degree `m` is the homology of `K` in degree
`p = -m`: the two differentials agree up to sign. -/
def negChainComplexHomologyIso (m p : ℤ) (hmp : m + p = 0) :
    K.negChainComplex.homology m ≅ K.homology p :=
  ShortComplex.homologyMapIso (K.negChainComplexScIso m p hmp)

/-- The isomorphism `CochainComplex.negChainComplexHomologyIso` sends the class of a cycle to the
class of the same cycle. -/
@[reassoc]
lemma homologyπ_negChainComplexHomologyIso_inv (m p : ℤ) (hmp : m + p = 0) :
    K.homologyπ p ≫ (K.negChainComplexHomologyIso m p hmp).inv =
      ShortComplex.cyclesMap (K.negChainComplexScIso m p hmp).inv ≫
        K.negChainComplex.homologyπ m :=
  ShortComplex.homologyπ_naturality (K.negChainComplexScIso m p hmp).inv

/-- The identification of cycles underlying `CochainComplex.negChainComplexHomologyIso` commutes
with the inclusions of the cycles into `Kᵖ = K⁻ᵐ`. -/
@[reassoc (attr := simp)]
lemma cyclesMap_negChainComplexScIso_inv_iCycles (m p : ℤ) (hmp : m + p = 0) :
    ShortComplex.cyclesMap (K.negChainComplexScIso m p hmp).inv ≫
        K.negChainComplex.iCycles m =
      K.iCycles p ≫ (K.XIsoOfEq (by omega : p = -m)).hom :=
  ShortComplex.cyclesMap_i _

end Homology

section Abelian

variable {C : Type*} [Category* C] [Abelian C] (K : CochainComplex C ℤ)

section Linear

variable (k : Type*) [Ring k] [Linear k C] (Y : C)

/-- The identification of the degree `i` terms of `Hom(K, Y[0])` and `Hom(K.negChainComplex, Y)`,
with the types of the two complexes. -/
private def linearHomComplexSingleXIso (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).X i ≅
      (K.negChainComplex.linearYonedaObj k Y).X i :=
  (HomComplex.Cochain.toSingleLinearEquiv (neg_add_cancel i)).toModuleIso

/-- **The dual of `K` is the `Hom` complex of `K.negChainComplex`**: the cochain complex
`Hom(K, Y[0])` is isomorphic to `Hom(K.negChainComplex, Y)`, through the identification of cochains
of degree `i` with morphisms `K⁻ⁱ ⟶ Y` (`CochainComplex.HomComplex.Cochain.toSingleEquiv`). -/
def linearHomComplexSingleIso :
    linearHomComplex k K ((singleFunctor C 0).obj Y) ≅ K.negChainComplex.linearYonedaObj k Y :=
  HomologicalComplex.Hom.isoOfComponents (linearHomComplexSingleXIso K k Y) (by
      rintro i _ rfl
      refine ModuleCat.hom_ext (LinearMap.ext fun f ↦ ?_)
      obtain ⟨g, rfl⟩ := HomComplex.Cochain.toSingleMk_surjective f (-i) (neg_add_cancel i)
      -- The terms of both complexes are their modules of cochains and of morphisms only up to
      -- unfolding, so the equation of morphisms is stated by `change`.
      change ((i + 1).negOnePow • K.d (-(i + 1)) (-i)) ≫ HomComplex.Cochain.toSingleEquiv
          (neg_add_cancel i) (HomComplex.Cochain.toSingleMk g (neg_add_cancel i)) =
        HomComplex.Cochain.toSingleEquiv (neg_add_cancel (i + 1))
          (HomComplex.δ i (i + 1) (HomComplex.Cochain.toSingleMk g (neg_add_cancel i)))
      rw [HomComplex.Cochain.δ_toSingleMk g (neg_add_cancel i) (i + 1) (-(i + 1))
        (neg_add_cancel _), Units.smul_def, Units.smul_def, map_zsmul, Preadditive.zsmul_comp,
        HomComplex.Cochain.toSingleEquiv_toSingleMk, HomComplex.Cochain.toSingleEquiv_toSingleMk])

/-- `CochainComplex.linearHomComplexSingleIso` sends a cochain of degree `i` to the morphism
`K⁻ⁱ ⟶ Y` it consists of. -/
lemma linearHomComplexSingleIso_hom_f_apply (i : ℤ)
    (f : HomComplex.Cochain K ((singleFunctor C 0).obj Y) i) :
    (K.linearHomComplexSingleIso k Y).hom.f i f =
      HomComplex.Cochain.toSingleEquiv (neg_add_cancel i) f :=
  (rfl)

/-- `CochainComplex.linearHomComplexSingleIso` sends a morphism `K⁻ⁱ ⟶ Y` back to the cochain of
degree `i` it defines. -/
lemma linearHomComplexSingleIso_inv_f_apply (i : ℤ) (g : K.negChainComplex.X i ⟶ Y) :
    (K.linearHomComplexSingleIso k Y).inv.f i g =
      HomComplex.Cochain.toSingleMk (K := K) g (neg_add_cancel i) :=
  (rfl)

/-- **The Kronecker map of the dual** `Hⁱ(Hom(K, Y[0])) →ₗ[k] (H⁻ⁱ(K) ⟶ Y)`: a cocycle, a morphism
`K⁻ⁱ ⟶ Y` vanishing on boundaries, restricts on the cycles to a morphism out of `H⁻ⁱ(K)`
(`CochainComplex.homologyπ_kronecker_homologyπ`). It is the Kronecker map
`TauCeti.ChainComplex.kronecker` of `K.negChainComplex`. -/
def kronecker (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i →ₗ[k] (K.homology (-i) ⟶ Y) :=
  (Linear.homCongr k (K.negChainComplexHomologyIso i (-i) (add_neg_cancel i))
      (Iso.refl Y)).toLinearMap ∘ₗ
    TauCeti.ChainComplex.kronecker k K.negChainComplex Y i ∘ₗ
      (homologyMap (K.linearHomComplexSingleIso k Y).hom i).hom

/-- **The Kronecker map of the dual on classes**: evaluating the class of a cocycle `φ` on the class
of a cycle of `K⁻ⁱ` is evaluating the morphism `K⁻ⁱ ⟶ Y` of `φ` on the cycle. -/
@[reassoc (attr := simp)]
lemma homologyπ_kronecker_homologyπ (i : ℤ)
    (φ : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i) :
    K.homologyπ (-i) ≫
        K.kronecker k Y i ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i φ) =
      K.iCycles (-i) ≫ HomComplex.Cochain.toSingleEquiv (neg_add_cancel i)
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ) := by
  have h := congrArg (fun f ↦ f.hom φ)
    (homologyπ_naturality (K.linearHomComplexSingleIso k Y).hom i)
  have h' := ConcreteCategory.congr_hom (cyclesMap_i (K.linearHomComplexSingleIso k Y).hom i) φ
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  simp only [ConcreteCategory.comp_apply] at h'
  -- The cycles of the two `Hom` complexes are morphisms out of `K⁻ⁱ` only up to unfolding, so the
  -- composites are compared through `calc` rather than rewritten in place.
  calc K.homologyπ (-i) ≫
        K.kronecker k Y i ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i φ)
      = K.homologyπ (-i) ≫ (K.negChainComplexHomologyIso i (-i) (add_neg_cancel i)).inv ≫
          TauCeti.ChainComplex.kronecker k K.negChainComplex Y i
            ((K.negChainComplex.linearYonedaObj k Y).homologyπ i
              (cyclesMap (K.linearHomComplexSingleIso k Y).hom i φ)) := by
        rw [kronecker, LinearMap.comp_apply, LinearMap.comp_apply, h, LinearEquiv.coe_coe,
          Linear.homCongr_apply, Iso.refl_hom, Category.comp_id]
    _ = ShortComplex.cyclesMap (K.negChainComplexScIso i (-i) (add_neg_cancel i)).inv ≫
          K.negChainComplex.iCycles i ≫ (K.negChainComplex.linearYonedaObj k Y).iCycles i
            (cyclesMap (K.linearHomComplexSingleIso k Y).hom i φ) := by
        rw [homologyπ_negChainComplexHomologyIso_inv_assoc,
          TauCeti.ChainComplex.kronecker_homologyπ]
    _ = K.iCycles (-i) ≫ (K.negChainComplex.linearYonedaObj k Y).iCycles i
            (cyclesMap (K.linearHomComplexSingleIso k Y).hom i φ) :=
        (K.cyclesMap_negChainComplexScIso_inv_iCycles_assoc i (-i) (add_neg_cancel i) _).trans
          (by
            rw [XIsoOfEq_rfl, Iso.refl_hom]
            exact congrArg (· ≫ _) (Category.comp_id _))
    _ = _ := congrArg (K.iCycles (-i) ≫ ·) h'

/-- **The universal coefficient theorem for the dual with injective coefficients**: for an
injective object `Y`, the Kronecker map `Hⁱ(Hom(K, Y[0])) →ₗ[k] (H⁻ⁱ(K) ⟶ Y)` is bijective. -/
theorem kronecker_bijective [Injective Y] (i : ℤ) : Function.Bijective (K.kronecker k Y i) :=
  (Linear.homCongr k _ _).bijective.comp
    ((TauCeti.ChainComplex.kronecker_bijective i).comp (ConcreteCategory.bijective_of_isIso _))

/-- The Kronecker map of the dual as a `k`-linear equivalence
`Hⁱ(Hom(K, Y[0])) ≃ₗ[k] (H⁻ⁱ(K) ⟶ Y)`, for an injective object `Y`. -/
def kroneckerEquiv [Injective Y] (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i ≃ₗ[k] (K.homology (-i) ⟶ Y) :=
  LinearEquiv.ofBijective (K.kronecker k Y i) (K.kronecker_bijective k Y i)

/-- The equivalence `CochainComplex.kroneckerEquiv` is the Kronecker map. -/
@[simp]
lemma kroneckerEquiv_apply [Injective Y] (i : ℤ)
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    K.kroneckerEquiv k Y i x = K.kronecker k Y i x :=
  (rfl)

/-- **Surjectivity in the universal coefficient sequence of the dual**: the Kronecker map
`Hⁱ(Hom(K, Y[0])) →ₗ[k] (H⁻ⁱ(K) ⟶ Y)` is surjective when the cycles split off `K⁻ⁱ`, written as
the degree `i` term of `K.negChainComplex`. -/
theorem kronecker_surjective_of_isSplitMono (i : ℤ) [IsSplitMono (K.negChainComplex.iCycles i)] :
    Function.Surjective (K.kronecker k Y i) :=
  (Linear.homCongr k _ _).surjective.comp
    ((TauCeti.ChainComplex.kronecker_surjective_of_isSplitMono i).comp
      ((ModuleCat.epi_iff_surjective _).1 inferInstance))

end Linear

section Ext

variable (k : Type*) [CommRing k] [Linear k C] [HasExt.{w} C] (Y : C)

/-- **The `Ext` term of the universal coefficient sequence of the dual**: the `k`-linear map
`Ext¹(Hᵖ(K), Y) →ₗ[k] Hⁱ(Hom(K, Y[0]))`, through which torsion in `H¹⁻ⁱ(K)` contributes to `Hⁱ` of
the dual. It is `TauCeti.ChainComplex.extToHomology` for `K.negChainComplex`, and is defined when
the cycles of `K⁻⁽⁻ᵖ⁾ = Kᵖ`, the degree `-p` term of `K.negChainComplex`, are projective and split
off it. It is injective when `i + p = 1` (`CochainComplex.extToHomology_injective`). -/
def extToHomology (i p : ℤ) [Projective (K.negChainComplex.cycles (-p))]
    [IsSplitMono (K.negChainComplex.iCycles (-p))] :
    Ext.{w} (K.homology p) Y 1 →ₗ[k]
      (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i :=
  (homologyMap (K.linearHomComplexSingleIso k Y).inv i).hom ∘ₗ
    TauCeti.ChainComplex.extToHomology k K.negChainComplex Y i (-p) ∘ₗ
      (TauCeti.extLinearEquivOfIso k (K.negChainComplexHomologyIso (-p) p (neg_add_cancel p)).symm
        (Iso.refl Y) 1).toLinearMap

/-- **Injectivity in the universal coefficient sequence of the dual**: for `i + p = 1`, the map
`Ext¹(Hᵖ(K), Y) →ₗ[k] Hⁱ(Hom(K, Y[0]))` is injective. -/
theorem extToHomology_injective {i p : ℤ} (hip : i + p = 1)
    [Projective (K.negChainComplex.cycles (-p))] [IsSplitMono (K.negChainComplex.iCycles (-p))] :
    Function.Injective (K.extToHomology.{w} k Y i p) :=
  ((ModuleCat.mono_iff_injective _).1 inferInstance).comp
    ((TauCeti.ChainComplex.extToHomology_injective (by omega)).comp (LinearEquiv.injective _))

/-- **Exactness in the middle of the universal coefficient sequence of the dual**: for
`i + p = 1`, a cohomology class of `Hom(K, Y[0])` evaluates to zero on `H⁻ⁱ(K)` exactly when it
comes from `Ext¹(Hᵖ(K), Y)`. -/
theorem exact_extToHomology_kronecker {i p : ℤ} (hip : i + p = 1)
    [Projective (K.negChainComplex.cycles (-p))] [IsSplitMono (K.negChainComplex.iCycles (-p))] :
    Function.Exact (K.extToHomology.{w} k Y i p) (K.kronecker k Y i) := by
  rw [extToHomology, kronecker, ← LinearMap.comp_assoc, LinearEquiv.precomp_exact_iff_exact,
    LinearEquiv.postcomp_exact_iff_exact]
  -- `Hⁱ` of the isomorphism `Hom(K, Y[0]) ≅ Hom(K.negChainComplex, Y)` carries the sequence of
  -- `K.negChainComplex` to that of the dual.
  exact (LinearEquiv.conj_symm_exact_iff_exact _ _
    (homologyMapIso (K.linearHomComplexSingleIso k Y) i).toLinearEquiv).2
    (TauCeti.ChainComplex.exact_extToHomology_kronecker (by omega))

/-- `CochainComplex.extToHomology` is `TauCeti.ChainComplex.extToHomology` for
`K.negChainComplex`, transported along `CochainComplex.negChainComplexHomologyIso` and
`CochainComplex.linearHomComplexSingleIso`. -/
lemma homologyMap_linearHomComplexSingleIso_hom_extToHomology (i p : ℤ)
    [Projective (K.negChainComplex.cycles (-p))] [IsSplitMono (K.negChainComplex.iCycles (-p))]
    (e : Ext.{w} (K.homology p) Y 1) :
    homologyMap (K.linearHomComplexSingleIso k Y).hom i (K.extToHomology k Y i p e) =
      TauCeti.ChainComplex.extToHomology k K.negChainComplex Y i (-p)
        ((Ext.mk₀ (K.negChainComplexHomologyIso (-p) p (neg_add_cancel p)).hom).comp e
          (zero_add 1)) := by
  simp [extToHomology, ← ConcreteCategory.comp_apply, ← homologyMap_comp]

end Ext

end Abelian

section ModuleCat

variable {k : Type*} [CommRing k] (K : CochainComplex (ModuleCat.{w} k) ℤ)

/-- The terms of `K.negChainComplex` are projective when the terms of `K` are: its degree `m` term
is `K⁻ᵐ`. -/
instance projective_negChainComplex_X (m : ℤ) [h : Module.Projective k (K.X (-m))] :
    Module.Projective k (K.negChainComplex.X m) :=
  h

variable (Y : ModuleCat.{w} k)

/-- **The Kronecker map of the dual on classes, elementwise**: for a complex of `k`-modules,
evaluating the class of a cocycle `φ` on the class of a cycle `x` of `K⁻ⁱ` is the morphism
`K⁻ⁱ ⟶ Y` of `φ` evaluated on the underlying chain of `x`. -/
@[simp]
lemma kronecker_homologyπ_homologyπ (i : ℤ)
    (φ : (linearHomComplex k K ((singleFunctor (ModuleCat.{w} k) 0).obj Y)).cycles i)
    (x : K.cycles (-i)) :
    K.kronecker k Y i ((linearHomComplex k K ((singleFunctor _ 0).obj Y)).homologyπ i φ)
        (K.homologyπ (-i) x) =
      (HomComplex.Cochain.toSingleEquiv (neg_add_cancel i)
        ((linearHomComplex k K ((singleFunctor _ 0).obj Y)).iCycles i φ)).hom
        (K.iCycles (-i) x) :=
  ConcreteCategory.congr_hom (K.homologyπ_kronecker_homologyπ k Y i φ) x

end ModuleCat

end CochainComplex
