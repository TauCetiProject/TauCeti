/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import TauCeti.Algebra.Homology.PrincipalIdealRing
public import TauCeti.Algebra.Homology.UniversalCoefficient.CochainComplex
public import TauCeti.KnotTheory.Khovanov.Homology
public import TauCeti.KnotTheory.Khovanov.Mirror.Basic

/-!
# Khovanov homology of the mirror diagram

For a planar oriented PD-code `D`, the normalized Khovanov complex of the mirror `D.mirror` in
quantum degree `j` is the dual `Hom(C(D)_{-j}, R)` of the complex of `D` in quantum degree `-j`
(`TauCeti.OrientedPDCode.khovanovComplexMirrorIso`). The universal coefficient theorem for the
dual of a cochain complex (`CochainComplex.exact_extToHomology_kronecker`) turns this into
statements about Khovanov homology, with both bidegrees reversed:

* the Kronecker map `Khⁱʲ(D.mirror; R) →ₗ[R] Kh⁻ⁱ⁻ʲ(D; R)ᵛ` evaluates a cocycle of the mirror on
  a cycle of `D` by the pairing of `khovanovComplexMirrorIso`
  (`TauCeti.OrientedPDCode.khovanovHomologyMirrorKronecker_homologyπ_homologyπ`);
* over a self-injective coefficient ring, such as a field, it is an isomorphism
  `Khⁱʲ(D.mirror; R) ≃ₗ[R] Kh⁻ⁱ⁻ʲ(D; R)ᵛ`
  (`TauCeti.OrientedPDCode.khovanovHomologyMirrorEquiv`); for a field `K`,
  `Module.injective_of_isSemisimpleRing K K` supplies the hypothesis `Module.Injective K K`;
* over a principal ideal ring without zero divisors, such as `ℤ`, the sequence

  `0 ⟶ Ext¹(Khᵖ⁻ʲ(D; R), R) ⟶ Khⁱʲ(D.mirror; R) ⟶ Kh⁻ⁱ⁻ʲ(D; R)ᵛ ⟶ 0`, for `i + p = 1`,

  is exact (`TauCeti.OrientedPDCode.extToKhovanovHomologyMirror_injective`,
  `TauCeti.OrientedPDCode.exact_extToKhovanovHomologyMirror_khovanovHomologyMirrorKronecker` and
  `TauCeti.OrientedPDCode.khovanovHomologyMirrorKronecker_surjective`). The dual of
  `Kh⁻ⁱ⁻ʲ(D; ℤ)` and the `Ext¹` of `Kh¹⁻ⁱ⁻ʲ(D; ℤ)`, through which its torsion enters, together
  make up `Khⁱʲ(D.mirror; ℤ)`.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §7.3.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1, Theorem 3.2.
-/

public section

noncomputable section

open CategoryTheory CochainComplex HomologicalComplex

namespace TauCeti.OrientedPDCode

universe u

variable {n : ℕ} (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar)
  (hD' : D.mirror.toPDCode.IsPlanar) (R : Type u) [CommRing R]

/-- **The Kronecker map of the mirror**: the `R`-linear map `Khⁱʲ(D.mirror; R) →ₗ[R] Kh⁻ⁱ⁻ʲ(D; R)ᵛ`
evaluating a cocycle of the mirror on the cycles of `D` through the identification of the complex
of the mirror with the dual complex of `D` (`TauCeti.OrientedPDCode.khovanovComplexMirrorIso`). -/
def khovanovHomologyMirrorKronecker (i j : ℤ) :
    D.mirror.khovanovHomology hD' R i j →ₗ[R] Module.Dual R (D.khovanovHomology hD R (-i) (-j)) :=
  ModuleCat.homLinearEquiv.toLinearMap ∘ₗ
    (D.khovanovComplex hD R (-j)).kronecker R (ModuleCat.of R R) i ∘ₗ
      (homologyMap (D.khovanovComplexMirrorIso hD R j hD').hom i).hom

/-- **The Kronecker map of the mirror on classes**: the class of a cocycle `φ` of the mirror pairs
with the class of a cycle `x` of `D` to the value on `x` of the cochain that
`TauCeti.OrientedPDCode.khovanovComplexMirrorIso` assigns to `φ`. -/
@[simp]
theorem khovanovHomologyMirrorKronecker_homologyπ_homologyπ (i j : ℤ)
    (φ : (D.mirror.khovanovComplex hD' R j).cycles i)
    (x : (D.khovanovComplex hD R (-j)).cycles (-i)) :
    D.khovanovHomologyMirrorKronecker hD hD' R i j
        ((D.mirror.khovanovComplex hD' R j).homologyπ i φ)
        ((D.khovanovComplex hD R (-j)).homologyπ (-i) x) =
      (HomComplex.Cochain.toSingleEquiv (neg_add_cancel i)
        ((D.khovanovComplexMirrorIso hD R j hD').hom.f i
          ((D.mirror.khovanovComplex hD' R j).iCycles i φ))).hom
        ((D.khovanovComplex hD R (-j)).iCycles (-i) x) := by
  have h := congrArg (fun f ↦ f.hom φ)
    (homologyπ_naturality (D.khovanovComplexMirrorIso hD R j hD').hom i)
  have h' := congrArg (fun f ↦ f.hom φ)
    (cyclesMap_i (D.khovanovComplexMirrorIso hD R j hD').hom i)
  have hk := congrArg (fun f ↦ f.hom x)
    ((D.khovanovComplex hD R (-j)).homologyπ_kronecker_homologyπ R (ModuleCat.of R R) i
      (cyclesMap (D.khovanovComplexMirrorIso hD R j hD').hom i φ))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h h' hk
  rw [khovanovHomologyMirrorKronecker, LinearMap.comp_apply, LinearMap.comp_apply, h]
  -- The cocycles of the dual complex are cochains only up to unfolding, so the last step is a
  -- congruence rather than a rewrite.
  exact hk.trans (congrArg (fun g : HomComplex.Cochain (D.khovanovComplex hD R (-j))
      ((singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)) i ↦
    (HomComplex.Cochain.toSingleEquiv (neg_add_cancel i) g).hom
      ((D.khovanovComplex hD R (-j)).iCycles (-i) x)) h')

/-- **Mirror duality of Khovanov homology over a self-injective ring**: when `R` is injective as a
module over itself, for instance a field, the Kronecker map of the mirror is bijective. -/
theorem khovanovHomologyMirrorKronecker_bijective [Module.Injective R R] (i j : ℤ) :
    Function.Bijective (D.khovanovHomologyMirrorKronecker hD hD' R i j) := by
  have := Module.injective_object_of_injective_module R R
  exact (ModuleCat.homLinearEquiv (S := R)).bijective.comp
    (((D.khovanovComplex hD R (-j)).kronecker_bijective R (ModuleCat.of R R) i).comp
      (ConcreteCategory.bijective_of_isIso _))

/-- **Mirror duality of Khovanov homology**: over a coefficient ring `R` injective as a module over
itself, such as a field, `Khⁱʲ(D.mirror; R)` is the `R`-linear dual of `Kh⁻ⁱ⁻ʲ(D; R)`. The
equivalence is the Kronecker map `TauCeti.OrientedPDCode.khovanovHomologyMirrorKronecker`. -/
def khovanovHomologyMirrorEquiv [Module.Injective R R] (i j : ℤ) :
    D.mirror.khovanovHomology hD' R i j ≃ₗ[R] Module.Dual R (D.khovanovHomology hD R (-i) (-j)) :=
  LinearEquiv.ofBijective (D.khovanovHomologyMirrorKronecker hD hD' R i j)
    (D.khovanovHomologyMirrorKronecker_bijective hD hD' R i j)

/-- The equivalence `TauCeti.OrientedPDCode.khovanovHomologyMirrorEquiv` is the Kronecker map. -/
@[simp]
theorem khovanovHomologyMirrorEquiv_apply [Module.Injective R R] (i j : ℤ)
    (x : D.mirror.khovanovHomology hD' R i j) :
    D.khovanovHomologyMirrorEquiv hD hD' R i j x =
      D.khovanovHomologyMirrorKronecker hD hD' R i j x :=
  (rfl)

section PrincipalIdealRing

variable [NoZeroDivisors R] [IsPrincipalIdealRing R]

/-- **Surjectivity in the mirror universal coefficient sequence**: over a principal ideal ring
without zero divisors, such as `ℤ`, every linear form on `Kh⁻ⁱ⁻ʲ(D; R)` is the evaluation of a
class of the mirror. -/
theorem khovanovHomologyMirrorKronecker_surjective (i j : ℤ) :
    Function.Surjective (D.khovanovHomologyMirrorKronecker hD hD' R i j) :=
  (ModuleCat.homLinearEquiv (S := R)).surjective.comp
    (((D.khovanovComplex hD R (-j)).kronecker_surjective_of_isSplitMono R (ModuleCat.of R R) i).comp
      ((ModuleCat.epi_iff_surjective _).1 inferInstance))

/-- **The `Ext` term of the mirror universal coefficient sequence**: over a principal ideal ring
without zero divisors, the `R`-linear map `Ext¹(Khᵖ⁻ʲ(D; R), R) →ₗ[R] Khⁱʲ(D.mirror; R)`, the map
`CochainComplex.extToHomology` of the complex of `D` followed by the inverse mirror isomorphism. For
`i + p = 1` it is injective (`TauCeti.OrientedPDCode.extToKhovanovHomologyMirror_injective`) and its
image is the kernel of the Kronecker map
(`TauCeti.OrientedPDCode.exact_extToKhovanovHomologyMirror_khovanovHomologyMirrorKronecker`). -/
def extToKhovanovHomologyMirror (i p j : ℤ) :
    Abelian.Ext.{u} (D.khovanovHomology hD R p (-j)) (ModuleCat.of R R) 1 →ₗ[R]
      D.mirror.khovanovHomology hD' R i j :=
  (homologyMap (D.khovanovComplexMirrorIso hD R j hD').inv i).hom ∘ₗ
    (D.khovanovComplex hD R (-j)).extToHomology R (ModuleCat.of R R) i p

/-- `TauCeti.OrientedPDCode.extToKhovanovHomologyMirror` is `CochainComplex.extToHomology` of the
complex of `D`, transported along `TauCeti.OrientedPDCode.khovanovComplexMirrorIso`. -/
lemma homologyMap_khovanovComplexMirrorIso_hom_extToKhovanovHomologyMirror (i p j : ℤ)
    (e : Abelian.Ext.{u} (D.khovanovHomology hD R p (-j)) (ModuleCat.of R R) 1) :
    homologyMap (D.khovanovComplexMirrorIso hD R j hD').hom i
        (D.extToKhovanovHomologyMirror hD hD' R i p j e) =
      (D.khovanovComplex hD R (-j)).extToHomology R (ModuleCat.of R R) i p e := by
  simp [extToKhovanovHomologyMirror, ← ConcreteCategory.comp_apply, ← homologyMap_comp]

/-- **Injectivity in the mirror universal coefficient sequence**: over a principal ideal ring
without zero divisors, for `i + p = 1`, the map `Ext¹(Khᵖ⁻ʲ(D; R), R) →ₗ[R] Khⁱʲ(D.mirror; R)` is
injective. -/
theorem extToKhovanovHomologyMirror_injective {i p : ℤ} (hip : i + p = 1) (j : ℤ) :
    Function.Injective (D.extToKhovanovHomologyMirror hD hD' R i p j) :=
  ((ModuleCat.mono_iff_injective _).1 inferInstance).comp
    ((D.khovanovComplex hD R (-j)).extToHomology_injective R (ModuleCat.of R R) hip)

/-- **Exactness of the mirror universal coefficient sequence**: over a principal ideal ring without
zero divisors, for `i + p = 1`, a class of `Khⁱʲ(D.mirror; R)` evaluates to zero on
`Kh⁻ⁱ⁻ʲ(D; R)` exactly when it comes from `Ext¹(Khᵖ⁻ʲ(D; R), R)`. With
`TauCeti.OrientedPDCode.extToKhovanovHomologyMirror_injective` and
`TauCeti.OrientedPDCode.khovanovHomologyMirrorKronecker_surjective` this is the short exact
sequence `0 ⟶ Ext¹(Khᵖ⁻ʲ(D; R), R) ⟶ Khⁱʲ(D.mirror; R) ⟶ Kh⁻ⁱ⁻ʲ(D; R)ᵛ ⟶ 0`. -/
theorem exact_extToKhovanovHomologyMirror_khovanovHomologyMirrorKronecker {i p : ℤ}
    (hip : i + p = 1) (j : ℤ) :
    Function.Exact (D.extToKhovanovHomologyMirror hD hD' R i p j)
      (D.khovanovHomologyMirrorKronecker hD hD' R i j) := by
  rw [extToKhovanovHomologyMirror, khovanovHomologyMirrorKronecker,
    LinearEquiv.postcomp_exact_iff_exact]
  -- `Hⁱ` of the mirror isomorphism carries the sequence of the dual complex of `D` to that of the
  -- complex of the mirror.
  exact (LinearEquiv.conj_symm_exact_iff_exact _ _
    (homologyMapIso (D.khovanovComplexMirrorIso hD R j hD') i).toLinearEquiv).2
    ((D.khovanovComplex hD R (-j)).exact_extToHomology_kronecker R (ModuleCat.of R R) hip)

end PrincipalIdealRing

end TauCeti.OrientedPDCode
