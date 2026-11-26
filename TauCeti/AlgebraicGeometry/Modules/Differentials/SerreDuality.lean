/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.Trace
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.LinearEquivalence
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Picard

/-!
# Serre duality through the residue trace

Let `X` be an integral Noetherian separated curve over an exact constant field `k`, with discrete
valuation rings at its codimension-one points, invertible relative differentials, and all the
places of its function field, and let `tr : H¹(X, Ω_{X/k}) → k` be the residue trace
`relativeDifferentialsResidueTrace`. A morphism `φ : F ⟶ Ω_{X/k}` of sheaves of modules gives the
linear form `tr ∘ H¹(φ)` on `H¹(X, F)`. This is the additive map
`residueTraceDualityHom F : Hom(F, Ω_{X/k}) → H¹(X, F)^∨`, natural in `F`
(`residueTraceDualityHom_comp`).

For a line bundle `L` the map is bijective (`InvertibleSheaf.bijective_residueTraceDualityHom`):
for every linear form `ℓ` on `H¹(X, L)` there is exactly one `φ : L ⟶ Ω_{X/k}` with
`tr ∘ H¹(φ) = ℓ`. This is Serre duality for line bundles in its normalized form, with the duality
map named: `InvertibleSheaf.residueTraceDualityEquiv`. Informally, through
`Hom(L, Ω_{X/k}) = H⁰(X, Ω_{X/k} ⊗ L⁻¹)` this is the classical statement that the cup product
followed by the trace is a perfect pairing; that identification and the cup-product form are not
formalised here.

Every line bundle on such a curve is the sheaf `𝒪_X(D)` of a Weil divisor, so it suffices to treat
`𝒪_X(D)` (`bijective_residueTraceDualityHom_sheaf`). For a separating function `t`, the sheaf
`Ω_{X/k}` is `𝒪_X(K)` for `K` the divisor of `dt`, a morphism `𝒪_X(D) ⟶ 𝒪_X(K)` is multiplication
by a rational function `f` with `div f ≥ D - K`, and `tr ∘ H¹(φ)` sends the class of a repartition
`a` to `ω(f a)`, where `ω` is the Weil differential of `dt`. Since `ω ≠ 0` this determines `f`,
and every linear form on `H¹(X, 𝒪_X(D))` is of this shape by the duality `Ω(D) ≃ L(K - D)` of
Weil differentials (`SchemeWeilDivisor.cohomologyOneDualEquivCohomologyZero`).

## Main declarations

* `residueTraceDualityHom`: the map `φ ↦ tr ∘ H¹(φ)`, with its naturality
  `residueTraceDualityHom_comp`;
* `bijective_residueTraceDualityHom_sheaf`: it is bijective for every divisor sheaf, and
  `bijective_residueTraceDualityHom_iff_of_iso` transports bijectivity along isomorphisms;
* `InvertibleSheaf.bijective_residueTraceDualityHom` and
  `InvertibleSheaf.residueTraceDualityEquiv`: Serre duality for line bundles through the trace.

## References

* J. Tate, *Residues of differentials on curves*, Ann. Sci. École Norm. Sup. (4) 1 (1968),
  Section 4, Theorem 5 and its Corollary.
* J.-P. Serre, *Algebraic Groups and Class Fields*, Chapter II, Section 5.
* R. Hartshorne, *Algebraic Geometry*, Chapter III, Section 7.
* The Stacks Project, Tag 0BS2.
-/

public section

open CategoryTheory AlgebraicGeometry Order
open scoped IntermediateField

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsIntegral X] [IsNoetherian X] [X.IsSeparated]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
  [SheafOfModules.isInvertible X (X.relativeDifferentials k)]
  (hF : IsFunctionField k X.functionField) (hk : IsIntegrallyClosedIn k X.functionField)
  (hex : ValuativeCriterion.Existence (X ↘ Spec (.of k)))
  (hdim : ∀ y : X, coheight y ≤ 1)

/-- The top open of an integral scheme is nonempty. -/
local instance nonemptyTopOpensResidueTraceDuality : Nonempty (⊤ : X.Opens) :=
  ⟨⟨Classical.choice inferInstance, trivial⟩⟩

/-- **The trace duality map** `Hom(F, Ω_{X/k}) → H¹(X, F)^∨`, sending `φ : F ⟶ Ω_{X/k}` to the
linear form `tr ∘ H¹(φ)` on `H¹(X, F)`, where `tr` is the residue trace. -/
def residueTraceDualityHom (F : X.Modules) :
    (F ⟶ X.relativeDifferentials k) →+ Module.Dual k (Scheme.Modules.Cohomology F 1) where
  toFun φ := (relativeDifferentialsResidueTrace hF hk hex hdim).comp
    (Scheme.Modules.cohomologyMapBaseLinear k X φ 1)
  map_zero' := by rw [Scheme.Modules.cohomologyMapBaseLinear_zero, LinearMap.comp_zero]
  map_add' φ ψ := by rw [Scheme.Modules.cohomologyMapBaseLinear_add, LinearMap.comp_add]

@[simp]
lemma residueTraceDualityHom_apply (F : X.Modules) (φ : F ⟶ X.relativeDifferentials k) :
    residueTraceDualityHom hF hk hex hdim F φ =
      (relativeDifferentialsResidueTrace hF hk hex hdim).comp
        (Scheme.Modules.cohomologyMapBaseLinear k X φ 1) :=
  (rfl)

/-- The trace duality map is natural in the sheaf: precomposing with `α : F ⟶ G` corresponds to
precomposing linear forms with `H¹(α)`. -/
lemma residueTraceDualityHom_comp {F G : X.Modules} (α : F ⟶ G)
    (φ : G ⟶ X.relativeDifferentials k) :
    residueTraceDualityHom hF hk hex hdim F (α ≫ φ) =
      (residueTraceDualityHom hF hk hex hdim G φ).comp
        (Scheme.Modules.cohomologyMapBaseLinear k X α 1) := by
  rw [residueTraceDualityHom_apply, residueTraceDualityHom_apply,
    Scheme.Modules.cohomologyMapBaseLinear_comp, LinearMap.comp_assoc]

section Separating

variable {t : X.functionField} (ht : Transcendental k t)
  [Algebra.IsSeparable k⟮t⟯ X.functionField] (K : SchemeWeilDivisor X)
  (hK : ∀ y : CodimensionOnePoint X, WeilDivisor.coeff K y =
    weilDifferentialOrder hF hk (weilDifferentialOfSeparating hF ht).property
      (coe_weilDifferentialOfSeparating_ne_zero hF ht) (X.toPlace (k := k) (y : X)))

/-- A morphism `φ : 𝒪_X(D) ⟶ Ω_{X/k}` which, read through `Ω_{X/k} ≅ 𝒪_X(K)`, is multiplication by
`g` sends the class of a repartition `a` to `ω(g a)` under `tr ∘ H¹(φ)`, where `ω` is the Weil
differential of `dt`. -/
private lemma residueTraceDualityHom_sheaf_apply {D : SchemeWeilDivisor X}
    (φ : SchemeWeilDivisor.sheaf D ⟶ X.relativeDifferentials k) (g : X.functionField)
    (hφ : φ ≫ (relativeDifferentialsIsoDivisorSheaf ht hF hk hdim K hK).hom ≫
        SchemeWeilDivisor.sheafι K =
      SchemeWeilDivisor.sheafι D ≫ Scheme.rationalFunctionsMul X g)
    (a : repartitionSpace k X.functionField) :
    residueTraceDualityHom hF hk hex hdim _ φ
        (SchemeWeilDivisor.repartitionToCohomologyOne hex hdim D a) =
      (weilDifferentialOfSeparating hF ht : Module.Dual k (repartitionSpace k X.functionField))
        (repartitionMul hF g a) := by
  set e := relativeDifferentialsIsoDivisorSheaf ht hF hk hdim K hK
  have hH := SchemeWeilDivisor.cohomologyMapBaseLinear_repartitionToCohomologyOne_of_comp_sheafι_eq
    hex hdim hF (φ ≫ e.hom) g (by rw [Category.assoc, hφ]) a
  rw [residueTraceDualityHom_apply, LinearMap.comp_apply,
    ← relativeDifferentialsResidueTrace_repartitionToRelativeDifferentialsCohomologyOne
      ht hF hk hex hdim K hK]
  congr 1
  -- compare the two classes after the isomorphism `H¹(Ω_{X/k}) ≅ H¹(𝒪_X(K))`
  apply (Scheme.Modules.cohomologyBaseLinearEquivOfIso k e 1).injective
  simp only [Scheme.Modules.cohomologyMapBaseLinear_comp, LinearMap.comp_apply,
    Scheme.Modules.coe_cohomologyMapBaseLinear] at hH
  simp only [Scheme.Modules.cohomologyBaseLinearEquivOfIso_apply,
    Scheme.Modules.coe_cohomologyMapBaseLinear, hH]
  exact
    (cohomologyMap_repartitionToRelativeDifferentialsCohomologyOne ht hF hk hex hdim K hK _).symm

include ht hK in
/-- Serre duality through the trace for `𝒪_X(D)`, computed with a separating function `t`. -/
private lemma bijective_residueTraceDualityHom_sheaf_of_separating
    (D : SchemeWeilDivisor X) :
    Function.Bijective (residueTraceDualityHom hF hk hex hdim (SchemeWeilDivisor.sheaf D)) := by
  set e := relativeDifferentialsIsoDivisorSheaf ht hF hk hdim K hK
  have hD := SchemeWeilDivisor.isLocallyPrincipal_of_forall_coheight_le_one hdim D
  refine ⟨(injective_iff_map_eq_zero _).mpr fun φ hφ ↦ ?_, fun ℓ ↦ ?_⟩
  · -- `φ`, read inside `𝒦_X`, is multiplication by some `g`, and `ω(g a) = 0` for all `a`
    obtain ⟨g, hg⟩ := hD.exists_rationalFunctionsMul_eq (φ ≫ e.hom ≫ SchemeWeilDivisor.sheafι K)
    have hg0 : g = 0 := by
      by_contra hg0
      apply coe_weilDifferentialOfSeparating_ne_zero hF ht
      ext b
      have h := residueTraceDualityHom_sheaf_apply hF hk hex hdim ht K hK φ g hg
        (repartitionMul hF g⁻¹ b)
      have hb : repartitionMul hF g (repartitionMul hF g⁻¹ b) = b :=
        Subtype.ext (by rw [coe_repartitionMul_apply, coe_repartitionMul_apply, smul_smul,
          mul_inv_cancel₀ hg0, one_smul])
      rwa [hφ, LinearMap.zero_apply, hb, eq_comm] at h
    rw [hg0, Scheme.rationalFunctionsMul_zero, Limits.comp_zero] at hg
    rw [← cancel_mono (e.hom ≫ SchemeWeilDivisor.sheafι K), hg, Limits.zero_comp]
  · -- the duality of Weil differentials writes `ℓ` as `[a] ↦ ω(f a)` for a section `f` of
    -- `𝒪_X(K - D)`, and multiplication by `f` is a morphism `𝒪_X(D) ⟶ 𝒪_X(K)`
    have hKg := isGreatest_weilDifferentialFiltration_equivFunctionFieldDivisor
      ht hF hk hex hdim K hK
    set s := SchemeWeilDivisor.cohomologyOneDualEquivCohomologyZero hex hdim hF hk hKg D ℓ
    set f := Scheme.rationalFunctionsEquiv ⊤ ((SchemeWeilDivisor.sheafι (K - D)).app ⊤
      (Scheme.Modules.cohomologyZeroEquiv _ s))
    have hf : ∀ y : CodimensionOnePoint X, f = 0 ∨ -WeilDivisor.coeff (K - D) y ≤ X.ord f y :=
      fun y ↦ SchemeWeilDivisor.mem_sections.mp (SchemeWeilDivisor.sheafι_app_mem _ _ _) y
        (TopologicalSpace.Opens.mem_top _)
    refine ⟨SchemeWeilDivisor.sheafHomOfMul f hf ≫ e.inv, LinearMap.ext fun x ↦ ?_⟩
    obtain ⟨a, rfl⟩ := SchemeWeilDivisor.repartitionToCohomologyOne_surjective hex hdim D x
    rw [residueTraceDualityHom_sheaf_apply hF hk hex hdim ht K hK _ f
        (by rw [Category.assoc, Iso.inv_hom_id_assoc, SchemeWeilDivisor.sheafHomOfMul_ι]) a,
      ← LinearEquiv.symm_apply_apply
        (SchemeWeilDivisor.cohomologyOneDualEquivCohomologyZero hex hdim hF hk hKg D) ℓ,
      SchemeWeilDivisor.cohomologyOneDualEquivCohomologyZero_symm_apply_repartitionToCohomologyOne]

end Separating

/-- **Serre duality through the trace for divisor sheaves.** For every Weil divisor `D`, the map
`φ ↦ tr ∘ H¹(φ)` from morphisms `𝒪_X(D) ⟶ Ω_{X/k}` to linear forms on `H¹(X, 𝒪_X(D))` is
bijective. -/
theorem bijective_residueTraceDualityHom_sheaf (D : SchemeWeilDivisor X) :
    Function.Bijective (residueTraceDualityHom hF hk hex hdim (SchemeWeilDivisor.sheaf D)) := by
  obtain ⟨t, ht, _⟩ := exists_transcendental_and_isSeparable_adjoin_of_isInvertible (k := k) hF
  exact bijective_residueTraceDualityHom_sheaf_of_separating hF hk hex hdim ht
    ((SchemeWeilDivisor.equivFunctionFieldDivisor hex hdim).symm
      (weilDifferentialDivisor hF hk (weilDifferentialOfSeparating hF ht).property
        (coe_weilDifferentialOfSeparating_ne_zero hF ht)))
    (fun y ↦ by simp only [SchemeWeilDivisor.coeff_equivFunctionFieldDivisor_symm,
      coeff_weilDifferentialDivisor]) D

/-- The trace duality map is bijective for `F` exactly when it is bijective for a sheaf `G`
isomorphic to `F`: along `e : F ≅ G` the two maps differ by the bijections `(e.inv ≫ ·)` and the
dual of `H¹(e)`. -/
theorem bijective_residueTraceDualityHom_iff_of_iso {F G : X.Modules} (e : F ≅ G) :
    Function.Bijective (residueTraceDualityHom hF hk hex hdim F) ↔
      Function.Bijective (residueTraceDualityHom hF hk hex hdim G) := by
  have h : ⇑(residueTraceDualityHom hF hk hex hdim F) =
      (Scheme.Modules.cohomologyBaseLinearEquivOfIso k e 1).dualMap ∘
        residueTraceDualityHom hF hk hex hdim G ∘ e.homFromEquiv := by
    funext φ
    refine LinearMap.ext fun x ↦ ?_
    simp only [Function.comp_apply, LinearEquiv.dualMap_apply, Iso.homFromEquiv_apply,
      Scheme.Modules.cohomologyBaseLinearEquivOfIso_apply, ← LinearMap.comp_apply,
      ← residueTraceDualityHom_comp, Iso.hom_inv_id_assoc]
  rw [h, Function.Bijective.of_comp_iff' (LinearEquiv.dualMap _).bijective,
    Function.Bijective.of_comp_iff _ e.homFromEquiv.bijective]

/-- **Serre duality for line bundles, through the trace.** For every line bundle `L`, the map
`φ ↦ tr ∘ H¹(φ)` from `Hom(L, Ω_{X/k})` to `H¹(X, L)^∨` is bijective: every linear form on
`H¹(X, L)` is `tr ∘ H¹(φ)` for exactly one `φ : L ⟶ Ω_{X/k}`. -/
theorem InvertibleSheaf.bijective_residueTraceDualityHom (L : InvertibleSheaf X) :
    Function.Bijective (residueTraceDualityHom hF hk hex hdim L.obj) := by
  obtain ⟨D, ⟨e⟩⟩ := SchemeWeilDivisor.exists_nonempty_iso_sheaf hdim L
  exact (bijective_residueTraceDualityHom_iff_of_iso hF hk hex hdim e).mpr
    (bijective_residueTraceDualityHom_sheaf hF hk hex hdim D)

/-- **Serre duality for line bundles, through the trace**, as an additive equivalence
`Hom(L, Ω_{X/k}) ≃ H¹(X, L)^∨`, `φ ↦ tr ∘ H¹(φ)`. -/
def InvertibleSheaf.residueTraceDualityEquiv (L : InvertibleSheaf X) :
    (L.obj ⟶ X.relativeDifferentials k) ≃+ Module.Dual k (Scheme.Modules.Cohomology L.obj 1) :=
  AddEquiv.ofBijective (residueTraceDualityHom hF hk hex hdim L.obj)
    (InvertibleSheaf.bijective_residueTraceDualityHom hF hk hex hdim L)

@[simp]
lemma InvertibleSheaf.residueTraceDualityEquiv_apply (L : InvertibleSheaf X)
    (φ : L.obj ⟶ X.relativeDifferentials k) :
    InvertibleSheaf.residueTraceDualityEquiv hF hk hex hdim L φ =
      (relativeDifferentialsResidueTrace hF hk hex hdim).comp
        (Scheme.Modules.cohomologyMapBaseLinear k X φ 1) :=
  (rfl)

end

end TauCeti.AlgebraicGeometry
