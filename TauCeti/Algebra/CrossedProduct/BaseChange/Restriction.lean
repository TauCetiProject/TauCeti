/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.BaseChange.Inflation
public import TauCeti.Algebra.CrossedProduct.Comparison
public import TauCeti.Algebra.CrossedProduct.Restriction
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteSubextension

/-!
# The cohomology class of a restricted crossed product

Let `E/K` be finite Galois inside `Kˢ`, and let `L` be an intermediate scalar field,
embedded by `σ : L →ₐ[K] Kˢ` compatibly with the scalar action on `E`. Restricting a
cocycle of `Aut_K(E)` to `Aut_L(E)` gives a crossed product over `L`. Its image under
`brauerCohomologyEquiv L` is the restriction of the original inflated cohomology class.

The statement does not require `L/K` to be normal. To evaluate the comparison over `L`,
the finite Galois extension `E/L` is transported into `Lˢ`; both its crossed-product
class and its inflated class are preserved by this transport. Combined with the
centralizer description of `CrossedProduct.restrictHom`, this supplies the cohomological
side of scalar-extension naturality of the Brauer comparison.

## References

* J.-P. Serre, *Local Fields*, GTM 67 (1979), Chapter X, §5.
* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology*, §4.4.
-/

public section

noncomputable section

namespace TauCeti

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  (σ : L →ₐ[K] SeparableClosure K)
  (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] [IsGalois K E]
  [Algebra L E] [IsScalarTower K L E]
  (hσ : ∀ x : L, E.val (algebraMap L E x) = σ x)

local instance : FiniteDimensional L E := FiniteDimensional.right K L E
local instance : IsGalois L E := IsGalois.tower_top_of_isGalois K L E

include hσ

/-- A restricted cocycle can be presented over a finite Galois subextension of `Lˢ`,
preserving both the crossed-product Brauer class and the restricted inflated class. -/
private theorem exists_restricted_galoisCocycle (c : TwoCocycle K E) :
    ∃ g : GaloisCocycle L,
      BrauerGroup.crossedProductClass (c.restrict L) = g.brauerClass ∧
        galoisResUnits K L σ 2 (c.inflateClass E) = g.inflateClass := by
  obtain ⟨F, hfin, hgal, e, he⟩ :=
    σ.exists_finiteGalois_subextension_equiv E.val hσ
  let := hfin
  let := hgal
  let π : (F ≃ₐ[L] F) →* (E ≃ₐ[K] E) :=
    (AlgEquiv.restrictScalarsHom K).comp e.autCongr.symm.toMonoidHom
  have he' (x : E) : (separableClosureRingEquiv K L σ).symm (E.val x) = F.val (e x) :=
    (RingEquiv.symm_apply_eq _).2 (he x).symm
  have hconj (g : F ≃ₐ[L] F) (x : E) :
      e.toAlgHom (e.autCongr.symm.toMonoidHom g x) = g (e.toAlgHom x) := by
    simp [AlgEquiv.autCongr_symm, AlgEquiv.autCongr_apply]
  have hπ (g : F ≃ₐ[L] F) (x : E) : e (π g x) = g (e x) := hconj g x
  let d := (c.restrict L).comap e.autCongr.symm.toMonoidHom e.toAlgHom hconj
  have hd (g h : F ≃ₐ[L] F) :
      d.toFun g h = Units.map e.toRingHom.toMonoidHom (c.toFun (π g) (π h)) := by
    apply Units.ext
    simp [d, π]
  refine ⟨⟨F, d⟩, ?_, ?_⟩
  · rw [GaloisCocycle.brauerClass_def]
    exact BrauerGroup.crossedProductClass_eq_of_algEquiv (c.restrict L) d e
      (fun g h => by
        dsimp only [d]
        rw [TwoCocycle.comap_toFun]
        simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
        apply Units.ext
        rfl)
  · rw [GaloisCocycle.inflateClass_def]
    exact TwoCocycle.inflateClass_galoisResUnits σ E F e.toRingHom π he' hπ c d hd

/-- The Brauer comparison commutes with restricting a finite Galois cocycle to the
automorphisms fixing an intermediate scalar field, even when `L/K` is not normal. -/
theorem brauerCohomologyEquiv_restrict_crossedProductClass (c : TwoCocycle K E) :
    brauerCohomologyEquiv L
        (Additive.ofMul (BrauerGroup.crossedProductClass (c.restrict L))) =
      galoisResUnits K L σ 2
        (brauerCohomologyEquiv K (Additive.ofMul (BrauerGroup.crossedProductClass c))) := by
  obtain ⟨g, hb, hi⟩ := exists_restricted_galoisCocycle σ E hσ c
  rw [hb, brauerCohomologyEquiv_galoisCocycle_brauerClass,
    brauerCohomologyEquiv_crossedProductClass, hi]

end TauCeti
