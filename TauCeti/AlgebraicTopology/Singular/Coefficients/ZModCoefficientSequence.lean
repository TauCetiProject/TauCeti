/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
public import TauCeti.Algebra.Category.ModuleCat.ZModCoefficientSequence
public import TauCeti.AlgebraicTopology.Singular.Coefficients.Bockstein
public import TauCeti.AlgebraicTopology.Singular.Coefficients.MapCoefficients

import Mathlib.Data.Nat.Prime.Basic
import TauCeti.Algebra.Category.ModuleCat.AB
import TauCeti.Algebra.Homology.Linear
import TauCeti.AlgebraicTopology.Singular.Reduced

/-!
# Singular homology and the mod-`m` coefficient sequence

The singular homology of a space with coefficients in `ℤ/m` can be formed in two ways: with the
integer module `ℤ/m` as coefficients in `ModuleCat ℤ`, which is how it appears in the coefficient
long exact sequence of `0 ⟶ ℤ ⟶ ℤ ⟶ ℤ/m ⟶ 0` (`TauCeti.zmodCoefficientSequence`), or with the ring
`ZMod m` as coefficients in `ModuleCat (ZMod m)`. Restriction of scalars along `ℤ → ZMod m`
preserves coproducts and homology, so the two agree (`TopCat.singularHomologyZModIso`), and one
vanishes exactly when the other does (`TopCat.isZero_singularHomology_zmod_iff`, with universe-`0`
variants `TopCat.isZero_singularHomology_uliftZMod_iff` and
`TopCat.isZero_singularHomology_zmod_iff'`).

The first map of the coefficient sequence `0 ⟶ ℤ ⟶ ℤ ⟶ ℤ/m ⟶ 0` is multiplication by `m`, so it
induces multiplication by `m` on integral singular homology `Hₙ(X; ℤ)`
(`TopCat.singularHomologyFunctor_map_zmodCoefficientSequence_f_app`), and its second map induces
the reduction `ρ : Hₙ(X; ℤ) ⟶ Hₙ(X; ℤ/m)` (`TopCat.singularHomologyReductionZMod`). From the
coefficient long exact sequence for `m ≠ 0` (together with `ρ = id` at `m = 0`):

* a class reduces to zero modulo `m` exactly when it is an `m`-multiple, for every `m : ℕ`
  (`TopCat.ker_singularHomologyReductionZMod`);
* for `m ≠ 0`, the reduction is onto in degree `n + 1` exactly when multiplication by `m` is
  injective on `Hₙ(X; ℤ)` (`TopCat.surjective_singularHomologyReductionZMod_succ_iff`), and in
  degree one it is always onto (`TopCat.surjective_singularHomologyReductionZMod_one`);
* for `m ≠ 0`, `Hₙ₊₁(X; ℤ/m)` vanishes exactly when multiplication by `m` is surjective on
  `Hₙ₊₁(X; ℤ)` and injective on `Hₙ(X; ℤ)` (`TopCat.isZero_singularHomology_zmod_succ_iff`);
* for every `m : ℕ`, vanishing of `Hₙ(X; ℤ/m)` and `Hₙ₊₁(X; ℤ/m)` makes multiplication by `m`
  bijective on `Hₙ(X; ℤ)` (`TopCat.bijective_zsmul_singularHomology_of_isZero_zmod`).

For nonzero moduli, because surjectivity and injectivity of multiplication by `m` decompose across
factors of `m`, vanishing of `Hₙ(X; ℤ/m)` transfers to every divisor `d ∣ m`
(`TopCat.isZero_singularHomology_zmod_of_dvd`), splits across products
(`TopCat.isZero_singularHomology_zmod_mul_iff`), and holds exactly when `Hₙ(X; ℤ/p)` vanishes for
every prime `p ∣ m` (`TopCat.isZero_singularHomology_zmod_iff_forall_prime`), in every degree
including degree zero.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.A (change of coefficients) and Section 3.E (Bockstein homomorphisms).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

universe u

namespace TopCat

/-! ### Comparison with homology over `ZMod m` -/

/-- **Integral homology with `ℤ/m` coefficients is `ZMod m`-homology**: the singular homology with
coefficients in the integer module `ℤ/m` is the singular homology with coefficients in the ring
`ZMod m`, with its scalars restricted to `ℤ`. -/
def singularHomologyZModIso (X : TopCat.{u}) (m n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} (ZMod m)))).obj X ≅
      (ModuleCat.restrictScalars (algebraMap ℤ (ZMod m))).obj
        (((singularHomologyFunctor (ModuleCat.{u} (ZMod m)) n).obj
          (ModuleCat.of (ZMod m) (ULift.{u} (ZMod m)))).obj X) :=
  ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).mapIso
      (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := ZMod m)
        (ULift.{u} (ZMod m))).symm).app X ≪≫
    ((Functor.singularHomologyFunctorObjCompIso
      (ModuleCat.restrictScalars.{u} (algebraMap ℤ (ZMod m)))
        (ModuleCat.of (ZMod m) (ULift.{u} (ZMod m))) n).app X).symm

/-- The identification of integral `ℤ/m` homology with `ZMod m`-homology is the inverse of the
identification of `ℤ/m` with the restriction of `ZMod m`, followed by the inverse of the comparison
of restricted `ZMod m`-homology with integral homology. -/
theorem singularHomologyZModIso_hom (X : TopCat.{u}) (m n : ℕ) :
    (X.singularHomologyZModIso m n).hom =
      ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).map
          (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := ZMod m)
            (ULift.{u} (ZMod m))).inv).app X ≫
        (Functor.singularHomologyFunctorObjCompIso
          (ModuleCat.restrictScalars.{u} (algebraMap ℤ (ZMod m)))
            (ModuleCat.of (ZMod m) (ULift.{u} (ZMod m))) n).inv.app X :=
  (rfl)

/-- The identification of integral `ℤ/m` homology with `ZMod m`-homology is natural in the space. -/
@[reassoc]
theorem singularHomologyZModIso_hom_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) (m n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} (ZMod m)))).map f ≫ (Y.singularHomologyZModIso m n).hom =
      (X.singularHomologyZModIso m n).hom ≫
        (ModuleCat.restrictScalars (algebraMap ℤ (ZMod m))).map
          (((singularHomologyFunctor (ModuleCat.{u} (ZMod m)) n).obj
            (ModuleCat.of (ZMod m) (ULift.{u} (ZMod m)))).map f) := by
  rw [singularHomologyZModIso_hom, singularHomologyZModIso_hom, NatTrans.naturality_assoc]
  exact congrArg _ ((Functor.singularHomologyFunctorObjCompIso _ _ n).inv.naturality f)

/-- Singular homology with coefficients in the integer module `ℤ/m` vanishes exactly when singular
homology with coefficients in the ring `ZMod m` does. -/
theorem isZero_singularHomology_zmod_iff (X : TopCat.{u}) (m n : ℕ) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} (ZMod m)))).obj X) ↔
      IsZero (((singularHomologyFunctor (ModuleCat.{u} (ZMod m)) n).obj
        (ModuleCat.of (ZMod m) (ULift.{u} (ZMod m)))).obj X) := by
  rw [Iso.isZero_iff (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).mapIso
    (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := ZMod m)
      (ULift.{u} (ZMod m))).symm).app X)]
  exact (ModuleCat.restrictScalars.{u} (algebraMap ℤ (ZMod m))).isZero_singularHomologyFunctor_iff
    (ModuleCat.of (ZMod m) (ULift.{u} (ZMod m))) n X

/-- In universe `0`, vanishing of singular homology with coefficients in the integer module
`ULift (ZMod m)` agrees with vanishing of singular homology with coefficients in `ZMod m`. -/
theorem isZero_singularHomology_uliftZMod_iff (X : TopCat.{0}) (m n : ℕ) :
    IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{0} (ZMod m)))).obj X) ↔
      IsZero (((singularHomologyFunctor (ModuleCat.{0} (ZMod m)) n).obj
        (ModuleCat.of (ZMod m) (ZMod m))).obj X) := by
  rw [X.isZero_singularHomology_zmod_iff m n]
  let e := ((singularHomologyFunctor (ModuleCat.{0} (ZMod m)) n).mapIso
    (ULift.moduleEquiv : ULift.{0} (ZMod m) ≃ₗ[ZMod m] ZMod m).toModuleIso).app X
  exact ⟨fun h ↦ h.of_iso e.symm, fun h ↦ h.of_iso e⟩

/-- In universe `0`, singular homology with coefficients in the integer module `ℤ/m` vanishes
exactly when singular homology with coefficients in the ring `ZMod m` does, with the coefficients
`ℤ/m` and `ZMod m` themselves rather than their universe lifts. -/
theorem isZero_singularHomology_zmod_iff' (X : TopCat.{0}) (m n : ℕ) :
    IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ (ZMod m))).obj X) ↔
      IsZero (((singularHomologyFunctor (ModuleCat.{0} (ZMod m)) n).obj
        (ModuleCat.of (ZMod m) (ZMod m))).obj X) := by
  rw [Iso.isZero_iff (((singularHomologyFunctor (ModuleCat.{0} ℤ) n).mapIso
    (ULift.moduleEquiv : ULift.{0} (ZMod m) ≃ₗ[ℤ] ZMod m).toModuleIso.symm).app X)]
  exact X.isZero_singularHomology_uliftZMod_iff m n

/-! ### Multiplication by `m` and reduction modulo `m` -/

/-- The coefficient map `ℤ ⟶ ℤ` of the mod-`m` coefficient sequence induces multiplication by `m`
on integral singular homology. -/
theorem singularHomologyFunctor_map_zmodCoefficientSequence_f_app (X : TopCat.{u}) (m n : ℕ) :
    (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).map
        (TauCeti.zmodCoefficientSequence.{u} m).f).app X).hom =
      LinearMap.lsmul ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) m := by
  -- Mathlib's `singularHomologyFunctor` is by definition singular chains followed by homology, and
  -- the first coefficient map is multiplication by `m` (`TauCeti.zmodCoefficientSequence_f`)
  change (HomologicalComplex.homologyMap (((singularChainComplexFunctor (ModuleCat.{u} ℤ)).map
    ((m : ℤ) • 𝟙 (ModuleCat.of ℤ (ULift.{u} ℤ)))).app X) n).hom =
      LinearMap.lsmul ℤ ((((singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X).homology n) m
  ext x
  simp [HomologicalComplex.homologyMap_smul, Nat.cast_smul_eq_nsmul]

/-- The **reduction modulo `m`** `Hₙ(X; ℤ) ⟶ Hₙ(X; ℤ/m)`, induced by the coefficient map
`ℤ ⟶ ℤ/m`. -/
abbrev singularHomologyReductionZMod (X : TopCat.{u}) (m n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X ⟶
      ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} (ZMod m)))).obj X :=
  ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).map
    (TauCeti.zmodCoefficientSequence.{u} m).g).app X

/-- Reduction modulo `m` is natural in the space. -/
@[reassoc]
theorem singularHomologyReductionZMod_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) (m n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj (ModuleCat.of ℤ (ULift.{u} ℤ))).map f ≫
        Y.singularHomologyReductionZMod m n =
      X.singularHomologyReductionZMod m n ≫
        ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
          (ModuleCat.of ℤ (ULift.{u} (ZMod m)))).map f :=
  ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).map
    (TauCeti.zmodCoefficientSequence.{u} m).g).naturality f

/-- For `m = 0`, reduction modulo `0` acts as the identity on integral singular homology. -/
@[simp]
theorem singularHomologyReductionZMod_zero_apply (X : TopCat.{u}) (n : ℕ)
    (x : ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) :
    X.singularHomologyReductionZMod 0 n x = x := by
  have hEq : X.singularHomologyReductionZMod 0 n =
      (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).mapIso
        TauCeti.zmodZeroModuleIso.symm).app X).hom :=
    congrArg (fun f ↦ ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).map f).app X)
      TauCeti.zmodCoefficientSequence_zero_g
  have h : ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).map
      TauCeti.zmodZeroModuleIso.inv).app X x = x := by
    erw [CategoryTheory.Functor.map_id, NatTrans.id_app]
    rfl
  exact (ConcreteCategory.congr_hom hEq x).trans h

/-- **The kernel of the reduction modulo `m`**: an integral homology class reduces to zero modulo
`m` exactly when it is an `m`-multiple of a class (for all `m : ℕ`, including `m = 0`). -/
theorem ker_singularHomologyReductionZMod (X : TopCat.{u}) (m n : ℕ) :
    LinearMap.ker (X.singularHomologyReductionZMod m n).hom =
      LinearMap.range (LinearMap.lsmul ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) m) := by
  rcases eq_or_ne m 0 with rfl | hm
  · have hEq : X.singularHomologyReductionZMod 0 n =
        (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).mapIso
          TauCeti.zmodZeroModuleIso.symm).app X).hom :=
      congrArg (fun f ↦ ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).map f).app X)
        TauCeti.zmodCoefficientSequence_zero_g
    have : Mono (X.singularHomologyReductionZMod 0 n) := by rw [hEq]; infer_instance
    rw [LinearMap.ker_eq_bot.2 ((ModuleCat.mono_iff_injective _).1 this)]
    simp
  · have : NeZero m := ⟨hm⟩
    rw [← X.singularHomologyFunctor_map_zmodCoefficientSequence_f_app m n]
    exact ((X.singularHomology_exact_coefficient₂
      (TauCeti.zmodCoefficientSequence_shortExact.{u} m) n).moduleCat_range_eq_ker).symm

/-- For `m ≠ 0`, the reduction modulo `m` is onto in degree `n + 1` exactly when multiplication by
`m` is injective on `Hₙ(X; ℤ)`. -/
theorem surjective_singularHomologyReductionZMod_succ_iff (X : TopCat.{u}) (m : ℕ) [NeZero m]
    (n : ℕ) :
    Function.Surjective (X.singularHomologyReductionZMod m (n + 1)) ↔
      Function.Injective (LinearMap.lsmul ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) m) := by
  have hS := TauCeti.zmodCoefficientSequence_shortExact.{u} m
  -- both conditions say that the Bockstein homomorphism vanishes
  rw [← ModuleCat.epi_iff_surjective,
    (X.singularHomology_exact_coefficient₃ hS (n + 1) n).epi_f_iff,
    ← (X.singularHomology_exact_coefficient₁ hS (n + 1) n).mono_g_iff, ModuleCat.mono_iff_injective,
    ← X.singularHomologyFunctor_map_zmodCoefficientSequence_f_app m n]

/-- The reduction modulo `m` is onto in degree one (for all `m : ℕ`): the zeroth integral homology
is a free abelian group, so multiplication by `m ≠ 0` is injective on it, and for `m = 0` reduction
is the identity. -/
theorem surjective_singularHomologyReductionZMod_one (X : TopCat.{u}) (m : ℕ) :
    Function.Surjective (X.singularHomologyReductionZMod m 1) := by
  rcases eq_or_ne m 0 with rfl | hm
  · exact fun x ↦ ⟨x, X.singularHomologyReductionZMod_zero_apply 1 x⟩
  · have : NeZero m := ⟨hm⟩
    exact (X.surjective_singularHomologyReductionZMod_succ_iff m 0).2
      (smul_right_injective _ (Nat.cast_ne_zero.2 hm))

/-- **The first mod-`m` homology is the first integral homology modulo `m`**: reduction modulo `m`
induces `H₁(X; ℤ) ⧸ m H₁(X; ℤ) ≃ H₁(X; ℤ/m)` (for all `m : ℕ`). -/
def singularHomologyOneZModAddEquiv (X : TopCat.{u}) (m : ℕ) :
    (((singularHomologyFunctor (ModuleCat.{u} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X ⧸
        LinearMap.range (LinearMap.lsmul ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) 1).obj
          (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) m)) ≃+
      ((singularHomologyFunctor (ModuleCat.{u} ℤ) 1).obj
        (ModuleCat.of ℤ (ULift.{u} (ZMod m)))).obj X :=
  ((Submodule.quotEquivOfEq _ _ (X.ker_singularHomologyReductionZMod m 1).symm).trans
    ((X.singularHomologyReductionZMod m 1).hom.quotKerEquivOfSurjective
      (X.surjective_singularHomologyReductionZMod_one m)) : _ ≃+ _)

/-- The identification `H₁(X; ℤ) ⧸ m H₁(X; ℤ) ≃ H₁(X; ℤ/m)` sends the class of an integral class to
its reduction modulo `m`. -/
@[simp]
theorem singularHomologyOneZModAddEquiv_mk (X : TopCat.{u}) (m : ℕ)
    (x : ((singularHomologyFunctor (ModuleCat.{u} ℤ) 1).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) :
    X.singularHomologyOneZModAddEquiv m (Submodule.Quotient.mk x) =
      X.singularHomologyReductionZMod m 1 x := by
  simp [singularHomologyOneZModAddEquiv]

/-! ### Vanishing criteria and divisibility transfer -/

/-- **Zeroth mod-`m` homology vanishes** exactly when the space is empty or `m = 1`. -/
theorem isZero_singularHomology_zmod_zero_iff (X : TopCat.{u}) (m : ℕ) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) 0).obj
        (ModuleCat.of ℤ (ULift.{u} (ZMod m)))).obj X) ↔ IsEmpty X ∨ m = 1 := by
  constructor
  · intro h
    by_cases hne : Nonempty X
    · right
      obtain ⟨x⟩ := hne
      have hz : IsZero (ModuleCat.of ℤ (ULift.{u} (ZMod m))) :=
        (IsZero.iff_id_eq_zero _).2 <| by
          rw [← TauCeti.singularHomology₀Section_singularHomology₀ε _ x,
            h.eq_of_src (X.singularHomology₀ε _) 0, Limits.comp_zero]
      have : Subsingleton (ULift.{u} (ZMod m)) := ModuleCat.isZero_iff_subsingleton.1 hz
      exact ZMod.subsingleton_iff.1 Equiv.ulift.symm.subsingleton
    · exact Or.inl (not_nonempty_iff.1 hne)
  · rintro (h | rfl)
    · exact TauCeti.isZero_singularHomology_of_isEmpty _ X 0
    · rw [isZero_singularHomology_zmod_iff, ModuleCat.isZero_iff_subsingleton]
      exact Module.subsingleton (ZMod 1) _

/-- Vanishing of mod-`m` singular homology in degree `n` makes multiplication by `m` surjective on
degree-`n` integral singular homology. -/
private lemma surjective_lsmul_singularHomology_of_isZero_zmod (X : TopCat.{u}) (m n : ℕ)
    (h : IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{u} (ZMod m)))).obj X)) :
    Function.Surjective (LinearMap.lsmul ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) m) :=
  LinearMap.range_eq_top.1 ((X.ker_singularHomologyReductionZMod m n).symm.trans
    (LinearMap.ker_eq_top.2
      (LinearMap.ext fun _ ↦ (ModuleCat.isZero_iff_subsingleton.1 h).elim _ _)))

/-- **Vanishing of mod-`m` singular homology in positive degrees**: for `m ≠ 0`, `Hₙ₊₁(X; ℤ/m) = 0`
exactly when multiplication by `m` is surjective on `Hₙ₊₁(X; ℤ)` and injective on `Hₙ(X; ℤ)`. -/
theorem isZero_singularHomology_zmod_succ_iff (X : TopCat.{u}) (m : ℕ) [NeZero m] (n : ℕ) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) (n + 1)).obj
        (ModuleCat.of ℤ (ULift.{u} (ZMod m)))).obj X) ↔
      Function.Surjective (LinearMap.lsmul ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ)
          (n + 1)).obj (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) m) ∧
        Function.Injective (LinearMap.lsmul ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
          (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) m) := by
  constructor
  · intro h
    have hsurj := X.surjective_lsmul_singularHomology_of_isZero_zmod m (n + 1) h
    have hinj := (X.surjective_singularHomologyReductionZMod_succ_iff m n).1 fun y ↦
      ⟨0, (ModuleCat.isZero_iff_subsingleton.1 h).elim _ _⟩
    exact ⟨hsurj, hinj⟩
  · rintro ⟨hsurj, hinj⟩
    have hρ : Function.Surjective (X.singularHomologyReductionZMod m (n + 1)) :=
      (X.surjective_singularHomologyReductionZMod_succ_iff m n).2 hinj
    have hker : LinearMap.ker (X.singularHomologyReductionZMod m (n + 1)).hom = ⊤ :=
      (X.ker_singularHomologyReductionZMod m (n + 1)).trans (LinearMap.range_eq_top.2 hsurj)
    refine ModuleCat.isZero_iff_subsingleton.2 ⟨fun y z ↦ ?_⟩
    obtain ⟨a, rfl⟩ := hρ y
    obtain ⟨b, rfl⟩ := hρ z
    have ha : (X.singularHomologyReductionZMod m (n + 1)).hom a = 0 :=
      LinearMap.mem_ker.1 (hker.symm ▸ Submodule.mem_top)
    have hb : (X.singularHomologyReductionZMod m (n + 1)).hom b = 0 :=
      LinearMap.mem_ker.1 (hker.symm ▸ Submodule.mem_top)
    exact ha.trans hb.symm

/-- Vanishing of mod-`m` singular homology in two adjacent degrees makes multiplication by `m`
bijective on integral singular homology in the lower degree (for all `m : ℕ`, including `m = 0`).
-/
theorem bijective_zsmul_singularHomology_of_isZero_zmod (X : TopCat.{u}) (m n : ℕ)
    (hn : IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{u} (ZMod m)))).obj X))
    (hn' : IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) (n + 1)).obj
      (ModuleCat.of ℤ (ULift.{u} (ZMod m)))).obj X)) :
    Function.Bijective fun x : ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X ↦ (m : ℤ) • x := by
  rcases eq_or_ne m 0 with rfl | hm
  · have hnℤ : IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) :=
      hn.of_iso (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).mapIso
        TauCeti.zmodZeroModuleIso).app X).symm
    have : Subsingleton (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) := ModuleCat.isZero_iff_subsingleton.1 hnℤ
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  · have : NeZero m := ⟨hm⟩
    have hinj := ((X.isZero_singularHomology_zmod_succ_iff m n).1 hn').2
    have hsurj := X.surjective_lsmul_singularHomology_of_isZero_zmod m n hn
    have hbij : Function.Bijective (LinearMap.lsmul ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ)
        n).obj (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) (m : ℤ)) := ⟨hinj, hsurj⟩
    convert hbij using 1
    funext x
    simp only [LinearMap.lsmul_apply, Nat.cast_smul_eq_nsmul, natCast_zsmul]

/-- **Divisibility transfer for mod-`m` vanishing**: for `m ≠ 0` and `d ∣ m`, vanishing of
`Hₙ(X; ℤ/m)` implies vanishing of `Hₙ(X; ℤ/d)` in the same single degree `n`, with no hypothesis in
adjacent degrees. -/
theorem isZero_singularHomology_zmod_of_dvd (X : TopCat.{u}) {d m : ℕ} [NeZero m] (hdm : d ∣ m)
    (n : ℕ)
    (hm : IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{u} (ZMod m)))).obj X)) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{u} (ZMod d)))).obj X) := by
  obtain ⟨k, rfl⟩ := hdm
  have : NeZero d := ⟨left_ne_zero_of_mul (NeZero.ne (d * k))⟩
  cases n with
  | zero =>
    rw [isZero_singularHomology_zmod_zero_iff] at hm ⊢
    exact hm.imp_right fun h ↦ (mul_eq_one.1 h).1
  | succ n =>
    rw [isZero_singularHomology_zmod_succ_iff] at hm ⊢
    rcases hm with ⟨hsurj, hinj⟩
    refine ⟨fun x ↦ ?_, fun y₁ y₂ h ↦ ?_⟩
    · obtain ⟨y, hy⟩ := hsurj x
      simp only [LinearMap.lsmul_apply, Nat.cast_smul_eq_nsmul, mul_nsmul'] at hy
      exact ⟨k • y, by simpa only [LinearMap.lsmul_apply, Nat.cast_smul_eq_nsmul] using hy⟩
    · apply hinj
      simp only [LinearMap.lsmul_apply, Nat.cast_smul_eq_nsmul, mul_comm d k, mul_nsmul']
      simpa only [LinearMap.lsmul_apply, Nat.cast_smul_eq_nsmul] using congrArg (k • ·) h

/-- **Product criterion for mod-`m` vanishing**: for `a, b ≠ 0` and every degree `n`,
`Hₙ(X; ℤ/(ab)) = 0` holds exactly when both `Hₙ(X; ℤ/a) = 0` and `Hₙ(X; ℤ/b) = 0`. -/
theorem isZero_singularHomology_zmod_mul_iff (X : TopCat.{u}) (a b : ℕ) [NeZero a] [NeZero b]
    (n : ℕ) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} (ZMod (a * b))))).obj X) ↔
      IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
          (ModuleCat.of ℤ (ULift.{u} (ZMod a)))).obj X) ∧
        IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
          (ModuleCat.of ℤ (ULift.{u} (ZMod b)))).obj X) := by
  refine ⟨fun h ↦ ⟨X.isZero_singularHomology_zmod_of_dvd (dvd_mul_right a b) n h,
    X.isZero_singularHomology_zmod_of_dvd (dvd_mul_left b a) n h⟩, ?_⟩
  rintro ⟨ha, hb⟩
  cases n with
  | zero =>
    rw [isZero_singularHomology_zmod_zero_iff] at ha hb ⊢
    rcases ha with h | rfl
    · exact Or.inl h
    · rcases hb with h | rfl
      · exact Or.inl h
      · exact Or.inr rfl
  | succ n =>
    rw [isZero_singularHomology_zmod_succ_iff] at ha hb ⊢
    refine ⟨fun x ↦ ?_, fun y₁ y₂ h ↦ ?_⟩
    · obtain ⟨y, hy⟩ := ha.1 x
      obtain ⟨z, hz⟩ := hb.1 y
      refine ⟨z, ?_⟩
      simp only [LinearMap.lsmul_apply, Nat.cast_smul_eq_nsmul, mul_nsmul'] at hy hz ⊢
      rw [hz, hy]
    · apply hb.2
      apply ha.2
      simp only [LinearMap.lsmul_apply, Nat.cast_smul_eq_nsmul, mul_nsmul'] at h ⊢
      exact h

/-- **Prime-factor criterion for mod-`m` vanishing**: for `m ≠ 0` and every degree `n`,
`Hₙ(X; ℤ/m) = 0` holds exactly when `Hₙ(X; ℤ/p) = 0` for every prime `p ∣ m`. -/
theorem isZero_singularHomology_zmod_iff_forall_prime (X : TopCat.{u}) (m : ℕ) [NeZero m] (n : ℕ) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} (ZMod m)))).obj X) ↔
      ∀ p : ℕ, p.Prime → p ∣ m →
        IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
          (ModuleCat.of ℤ (ULift.{u} (ZMod p)))).obj X) := by
  refine ⟨fun h p _ hpm ↦ X.isZero_singularHomology_zmod_of_dvd hpm n h, ?_⟩
  revert ‹NeZero m›
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro _ h
    by_cases hm1 : m = 1
    · subst hm1
      rw [isZero_singularHomology_zmod_iff, ModuleCat.isZero_iff_subsingleton]
      exact Module.subsingleton (ZMod 1) _
    · have hp : m.minFac.Prime := Nat.minFac_prime hm1
      have hpm : m.minFac ∣ m := Nat.minFac_dvd m
      have hdiv_pos : 0 < m / m.minFac :=
        Nat.div_pos (Nat.le_of_dvd (NeZero.pos m) hpm) hp.pos
      have : NeZero m.minFac := ⟨hp.ne_zero⟩
      have : NeZero (m / m.minFac) := ⟨hdiv_pos.ne'⟩
      have hlt : m / m.minFac < m := Nat.div_lt_self (NeZero.pos m) hp.one_lt
      rw [← Nat.mul_div_cancel' hpm, isZero_singularHomology_zmod_mul_iff]
      exact ⟨h m.minFac hp hpm,
        ih (m / m.minFac) hlt fun q hq hqd ↦ h q hq (hqd.trans (Nat.div_dvd_of_dvd hpm))⟩

end TopCat
