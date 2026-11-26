/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Localization.AtPrime.Extension
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
public import TauCeti.AlgebraicGeometry.IdealSheaf.Rank
public import TauCeti.AlgebraicGeometry.Morphisms.Finite.Flat.Degree
public import TauCeti.RingTheory.Intersection.ProjectionFormula

/-!
# The projection formula for finite dominant morphisms

Let `g : X ⟶ Y` be a finite dominant morphism of integral schemes, and `x` a point of `Y` whose
local ring `𝒪_{Y,x}` is noetherian of dimension at most one, such as a closed point of a curve over
a field. For a nonzero function `a` defined near `x`, the orders of vanishing of its pullback
`g^* a` at the finitely many points `y` above `x`, weighted by their residue degrees, add up to
the degree `[K(X) : g^* K(Y)]` times the order of `a` at `x`:

`Σ_{g(y) = x} [κ(y) : κ(x)] · ord_y(g^* a) = [K(X) : g^* K(Y)] · ord_x(a)`

(`AlgebraicGeometry.Scheme.Hom.finsum_residueDegree_mul_toNat_ord_eq_finrank_mul_toNat_ord`).
Neither scheme needs to be normal, and `g` need not be flat: this covers finite birational maps
onto singular curves, where the fibre length of `g` jumps at the singular points.

Over an affine open `U` of `Y` around `x`, the stalks above `x` are the localizations of the
semilocal ring `B = Γ(X, g⁻¹ U)_x` at its maximal ideals, which correspond to the points of the
fibre. The ring `B` is finite over `𝒪_{Y,x}` of rank `[K(X) : g^* K(Y)]`, so the formula is the
local projection formula for finite extensions of local rings of dimension one,
`TauCeti.finsum_toNat_ord_algebraMap_mul_length_quotient_eq_finrank_mul_ord`.

Summed over the points of an effective Cartier divisor `D` on `Y` finite over a field `K`, this
gives the degree of its inverse image,

`dim_K Γ(g⁻¹ D, 𝒪) = [K(X) : g^* K(Y)] · dim_K Γ(D, 𝒪)`

(`AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier.finrank_comap_subschemeι_comp`),
the identity `g_* g^* D = [K(X) : g^* K(Y)] · D` of divisors measured by degrees. For flat `g`
of constant rank this is `AlgebraicGeometry.Scheme.IdealSheafData.finrank_comap_subschemeι_comp`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.finsum_residueDegree_mul_toNat_ord_eq_finrank_mul_toNat_ord`:
  the local projection formula at a point of the target.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier.finrank_comap_subschemeι_comp`:
  inverse images of effective Cartier divisors finite over a field multiply degrees by
  `[K(X) : g^* K(Y)]`.

## References

* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 7.3 (the degree of the pullback of a
  divisor along a finite morphism of curves) and Section 9.2 (the projection formula).
* W. Fulton, *Intersection Theory*, Example 1.7.4 and Appendix A.3.
-/

public section

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

namespace Scheme.Hom

variable (g : X ⟶ Y) [IsFinite g] [IsIntegral X] [IsIntegral Y] [IsDominant g]

omit [IsIntegral X] [IsIntegral Y] [IsDominant g] in
/-- The points of the fibre of `g` over `x ∈ U`, for `U` affine, are the maximal ideals of the
semilocal ring `Γ(X, g⁻¹ U)_x`, localized at the complement of the prime of `x`: the point `y`
corresponds to the extension of its prime ideal in `Γ(X, g⁻¹ U)`. -/
private lemma exists_equiv_maximalSpectrum {x : Y} {U : Y.Opens} (hU : IsAffineOpen U)
    (hxU : x ∈ U) :
    letI := (g.appLE U (g ⁻¹ᵁ U) le_rfl).hom.toAlgebra
    ∃ e : {y : X // g y = x} ≃ MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
        Γ(X, g ⁻¹ᵁ U) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl)),
      ∀ y, (e y).asIdeal = ((hU.preimage g).primeIdealOf
        ⟨y, g.mem_preimage.mpr (y.property.symm ▸ hxU)⟩).asIdeal.map (algebraMap _ _) := by
  have hV : IsAffineOpen (g ⁻¹ᵁ U) := hU.preimage g
  set φ := g.appLE U (g ⁻¹ᵁ U) le_rfl with hφ
  have hfin : φ.hom.Finite := by
    rw [hφ, ← g.app_eq_appLE]
    exact g.finite_app U hU
  algebraize [φ.hom]
  set p := hU.primeIdealOf ⟨x, hxU⟩ with hp
  let := Y.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  set M := p.asIdeal.primeCompl
  set B := Localization (Algebra.algebraMapSubmonoid Γ(X, g ⁻¹ᵁ U) M)
  let : Algebra (Y.presheaf.stalk x) B := localizationAlgebra M Γ(X, g ⁻¹ᵁ U)
  have : IsScalarTower Γ(Y, U) (Y.presheaf.stalk x) B := isScalarTower_localizationAlgebra _ _
  have : Module.Finite (Y.presheaf.stalk x) B := by
    have : IsLocalization (M.map (algebraMap Γ(Y, U) Γ(X, g ⁻¹ᵁ U))) B :=
      inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid _ M) B)
    exact RingHom.finite_algebraMap.mp (RingHom.finite_localizationPreserves
      (algebraMap Γ(Y, U) Γ(X, g ⁻¹ᵁ U)) M (Y.presheaf.stalk x) B hfin)
  have hyV (y : {y : X // g y = x}) : (y : X) ∈ g ⁻¹ᵁ U :=
    g.mem_preimage.mpr (y.property.symm ▸ hxU)
  let q (y : {y : X // g y = x}) := (hV.primeIdealOf ⟨y, hyV y⟩).asIdeal
  -- The prime of a point of the fibre lies over the prime `p` of `x`.
  have hq (y : {y : X // g y = x}) : (q y).LiesOver p.asIdeal := by
    have h := IsAffineOpen.comap_primeIdealOf_appLE U hU (g ⁻¹ᵁ U) hV le_rfl (hyV y)
    rw [show (⟨g y, hyV y⟩ : U) = ⟨x, hxU⟩ from Subtype.ext y.property] at h
    exact ⟨congrArg PrimeSpectrum.asIdeal h.symm⟩
  -- Its extension to `B` lies over the maximal ideal of `𝒪_{Y,x}`, so is maximal.
  have hmax (y : {y : X // g y = x}) : ((q y).map (algebraMap _ B)).IsMaximal := by
    have := IsLocalization.AtPrime.isPrime_map_of_liesOver _ p.asIdeal B (q y)
    have := IsLocalization.AtPrime.liesOver_map_of_liesOver p.asIdeal (Y.presheaf.stalk x) B (q y)
    exact Ideal.IsMaximal.of_liesOver_isMaximal _ (maximalIdeal (Y.presheaf.stalk x))
  let e : {y : X // g y = x} → MaximalSpectrum B := fun y ↦ ⟨_, hmax y⟩
  refine ⟨.ofBijective e ⟨fun y₁ y₂ h ↦ ?_, fun m ↦ ?_⟩, fun _ ↦ rfl⟩
  · -- Primes disjoint from the localized submonoid are recovered from their extensions.
    have h' := congrArg (fun m : MaximalSpectrum B ↦ m.asIdeal.under Γ(X, g ⁻¹ᵁ U)) h
    simp only [e] at h'
    rw [IsLocalization.under_map_of_isPrime_disjoint _ B inferInstance
        (Ideal.disjoint_primeCompl_of_liesOver _ p.asIdeal),
      IsLocalization.under_map_of_isPrime_disjoint _ B inferInstance
        (Ideal.disjoint_primeCompl_of_liesOver _ p.asIdeal)] at h'
    simpa only [IsAffineOpen.fromSpec_primeIdealOf, Subtype.ext_iff] using
      congrArg hV.fromSpec (PrimeSpectrum.ext h')
  · -- A maximal ideal of `B` lies over the maximal ideal of `𝒪_{Y,x}`, so its contraction to
    -- `Γ(X, g⁻¹ U)` is the prime of a point over `x`.
    have : m.asIdeal.LiesOver (maximalIdeal (Y.presheaf.stalk x)) :=
      ⟨(eq_maximalIdeal (Ideal.IsMaximal.under (Y.presheaf.stalk x) m.asIdeal)).symm⟩
    have := IsLocalization.AtPrime.liesOver_comap_of_liesOver p.asIdeal
      (Y.presheaf.stalk x) (S := Γ(X, g ⁻¹ᵁ U)) m.asIdeal
    let z : g ⁻¹ᵁ U := hV.isoSpec.inv ⟨m.asIdeal.under _, inferInstance⟩
    have hz : hV.primeIdealOf z = ⟨m.asIdeal.under _, inferInstance⟩ :=
      Scheme.inv_hom_apply hV.isoSpec _
    have hzx : g z = x := by
      have h := IsAffineOpen.comap_primeIdealOf_appLE U hU (g ⁻¹ᵁ U) hV le_rfl z.property
      simp only [Subtype.coe_eta] at h
      have h' : hU.primeIdealOf ⟨g z, z.property⟩ = p := by
        rw [← h, hz]
        exact PrimeSpectrum.ext (Ideal.over_def _ p.asIdeal).symm
      simpa only [hp, IsAffineOpen.fromSpec_primeIdealOf] using congrArg hU.fromSpec h'
    refine ⟨⟨z, hzx⟩, MaximalSpectrum.ext ?_⟩
    change ((hV.primeIdealOf z).asIdeal).map _ = _
    rw [hz]
    exact IsLocalization.map_under (Algebra.algebraMapSubmonoid Γ(X, g ⁻¹ᵁ U) M) B m.asIdeal

omit [IsIntegral X] [IsIntegral Y] [IsDominant g] [IsFinite g] in
/-- The residue degree of `g` at `y` is computed by any local ring `T` over `𝒪_{Y, g y}` isomorphic
to `𝒪_{X,y}` compatibly with the stalk map. -/
private lemma residueDegree_eq_finrank_residueField (y : X) {T : Type u} [CommRing T]
    [IsLocalRing T] [Algebra (Y.presheaf.stalk (g y)) T]
    [IsLocalHom (algebraMap (Y.presheaf.stalk (g y)) T)] (e : T ≃+* X.presheaf.stalk y)
    (he : ∀ a, e (algebraMap _ T a) = g.stalkMap y a) :
    g.residueDegree y =
      Module.finrank (ResidueField (Y.presheaf.stalk (g y))) (ResidueField T) := by
  dsimp only [Scheme.Hom.residueDegree]
  let := (g.residueFieldMap y).hom.toAlgebra
  refine Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl _) (ResidueField.mapEquiv e).symm
    (RingHom.ext fun a ↦ ?_)
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a
  change IsLocalRing.residue _ (algebraMap _ _ a) = ResidueField.map (e.symm : _ →+* T)
    (ResidueField.map (g.stalkMap y).hom (IsLocalRing.residue _ a))
  rw [ResidueField.map_residue, ResidueField.map_residue, ← he]
  simp

/-- The local projection formula over an affine open of the target. -/
private lemma finsum_residueDegree_mul_toNat_ord_eq_of_isAffineOpen (x : Y)
    [IsNoetherianRing (Y.presheaf.stalk x)] [Ring.KrullDimLE 1 (Y.presheaf.stalk x)]
    {U : Y.Opens} (hU : IsAffineOpen U) (hxU : x ∈ U) {f : Γ(Y, U)} (hf : f ≠ 0) :
    ∑ᶠ y : {y : X // g y = x}, g.residueDegree y *
      (Ring.ord (X.presheaf.stalk y) (X.presheaf.germ (g ⁻¹ᵁ U) y
        (g.mem_preimage.mpr (y.property.symm ▸ hxU)) (g.app U f))).toNat =
      Module.finrank g.functionFieldMap.hom.fieldRange X.functionField *
        (Ring.ord (Y.presheaf.stalk x) (Y.presheaf.germ U x hxU f)).toNat := by
  -- Set up `A = 𝒪_{Y,x}`, the localization of `R = Γ(Y, U)` at the prime `p` of `x`, and the
  -- semilocal ring `B`, the localization of `S = Γ(X, g⁻¹ U)` at the complement `M` of `p`.
  have hV : IsAffineOpen (g ⁻¹ᵁ U) := hU.preimage g
  set φ := g.appLE U (g ⁻¹ᵁ U) le_rfl with hφ
  have hfin : φ.hom.Finite := by
    rw [hφ, ← g.app_eq_appLE]
    exact g.finite_app U hU
  have : Nonempty (g ⁻¹ᵁ U) := by
    obtain ⟨y, hy⟩ := g.denseRange.exists_mem_open U.isOpen ⟨x, hxU⟩
    exact ⟨⟨y, hy⟩⟩
  have hinj : Function.Injective φ.hom := g.appLE_injective_of_isDominant U (g ⁻¹ᵁ U) le_rfl
  algebraize [φ.hom]
  let := Y.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  set M := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  set B := Localization (Algebra.algebraMapSubmonoid Γ(X, g ⁻¹ᵁ U) M)
  let : Algebra (Y.presheaf.stalk x) B := localizationAlgebra M Γ(X, g ⁻¹ᵁ U)
  have : IsScalarTower Γ(Y, U) (Y.presheaf.stalk x) B := isScalarTower_localizationAlgebra _ _
  have hM : Algebra.algebraMapSubmonoid Γ(X, g ⁻¹ᵁ U) M ≤ nonZeroDivisors Γ(X, g ⁻¹ᵁ U) := by
    rintro _ ⟨r, hr, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h ↦ hr ?_
    rw [show r = 0 from hinj (h.trans (map_zero _).symm)]
    exact Ideal.zero_mem _
  have : IsDomain B := IsLocalization.isDomain_localization hM
  have : Module.Finite (Y.presheaf.stalk x) B := by
    have : IsLocalization (M.map (algebraMap Γ(Y, U) Γ(X, g ⁻¹ᵁ U))) B :=
      inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid _ M) B)
    exact RingHom.finite_algebraMap.mp (RingHom.finite_localizationPreserves
      (algebraMap Γ(Y, U) Γ(X, g ⁻¹ᵁ U)) M (Y.presheaf.stalk x) B hfin)
  have : FaithfulSMul (Y.presheaf.stalk x) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (localizationAlgebra_injective _ _ hinj)
  have hgerm (r : Γ(Y, U)) :
      algebraMap Γ(Y, U) (Y.presheaf.stalk x) r = Y.presheaf.germ U x hxU r :=
    congr($(Y.presheaf.stalk_open_algebraMap ⟨x, hxU⟩) r)
  -- `B` has rank `[K(X) : g^* K(Y)]` over `A`: localization does not change the rank of `S`.
  have hrank : Module.finrank (Y.presheaf.stalk x) B =
      Module.finrank g.functionFieldMap.hom.fieldRange X.functionField := by
    have : Nonempty U := ⟨⟨x, hxU⟩⟩
    have hM₀ : M ≤ nonZeroDivisors Γ(Y, U) := Ideal.primeCompl_le_nonZeroDivisors _
    rw [IsLocalization.finrank_eq (Y.presheaf.stalk x) M hM₀,
      IsLocalizedModule.finrank_eq M (IsScalarTower.toAlgHom Γ(Y, U) Γ(X, g ⁻¹ᵁ U) B).toLinearMap
        hM₀]
    exact g.finrank_appLE_eq_finrank_fieldRange_functionFieldMap hU
  -- Apply the local projection formula to `A ⟶ B`, and match its terms with the points of the
  -- fibre through `e`.
  obtain ⟨e, he⟩ := g.exists_equiv_maximalSpectrum hU hxU
  rw [← hrank, ← TauCeti.finsum_toNat_ord_algebraMap_mul_length_quotient_eq_finrank_mul_ord
    (fun m ↦ Localization.AtPrime m.asIdeal) (fun h ↦
      hf (germ_injective_of_isIntegral Y x hxU (h.trans (map_zero _).symm))),
    ← finsum_comp_equiv e]
  refine finsum_congr fun y ↦ ?_
  have hyV : (y : X) ∈ g ⁻¹ᵁ U := g.mem_preimage.mpr (y.property.symm ▸ hxU)
  set q := (hV.primeIdealOf ⟨y, hyV⟩).asIdeal
  set m := e y
  have hm : m.asIdeal.under Γ(X, g ⁻¹ᵁ U) = q := by
    have : q.LiesOver (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
      have h := IsAffineOpen.comap_primeIdealOf_appLE U hU (g ⁻¹ᵁ U) hV le_rfl hyV
      rw [show (⟨g y, hyV⟩ : U) = ⟨x, hxU⟩ from Subtype.ext y.property] at h
      exact ⟨congrArg PrimeSpectrum.asIdeal h.symm⟩
    rw [show m.asIdeal = _ from he y]
    exact IsLocalization.under_map_of_isPrime_disjoint _ B inferInstance
      (Ideal.disjoint_primeCompl_of_liesOver _ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal)
  -- The stalk of `X` at `y` and the localization of `B` at `m` both localize `S` at `q`.
  have : IsLocalization.AtPrime (Localization.AtPrime m.asIdeal) q := by
    have := IsLocalization.isLocalization_atPrime_localization_atPrime
      (Algebra.algebraMapSubmonoid Γ(X, g ⁻¹ᵁ U) M) m.asIdeal
    rwa [IsLocalization.AtPrime, show q.primeCompl = (m.asIdeal.under _).primeCompl from
      Submonoid.ext fun _ ↦ by simp only [Ideal.mem_primeCompl_iff, hm]]
  let := X.presheaf.algebra_section_stalk ⟨y, hyV⟩
  have := hV.isLocalization_stalk ⟨y, hyV⟩
  have hgermy (s : Γ(X, g ⁻¹ᵁ U)) : algebraMap Γ(X, g ⁻¹ᵁ U) (X.presheaf.stalk y) s =
      X.presheaf.germ (g ⁻¹ᵁ U) y hyV s :=
    congr($(X.presheaf.stalk_open_algebraMap ⟨y, hyV⟩) s)
  -- The orders of vanishing agree.
  have hord : Ring.ord (X.presheaf.stalk y) (X.presheaf.germ (g ⁻¹ᵁ U) y hyV (g.app U f)) =
      Ring.ord (Localization.AtPrime m.asIdeal) (algebraMap B (Localization.AtPrime m.asIdeal)
        (algebraMap (Y.presheaf.stalk x) B (Y.presheaf.germ U x hxU f))) := by
    rw [← hgerm, ← IsScalarTower.algebraMap_apply Γ(Y, U) (Y.presheaf.stalk x) B,
      IsScalarTower.algebraMap_apply Γ(Y, U) Γ(X, g ⁻¹ᵁ U) B,
      ← IsScalarTower.algebraMap_apply Γ(X, g ⁻¹ᵁ U) B, g.app_eq_appLE, ← hgermy]
    exact (TauCeti.Ring.ord_algebraMap_isLocalization q.primeCompl _ _ _).symm
  rw [hord, mul_comm]
  congr 1
  -- The residue degrees agree: identify `x` with `g y`, and compare residue fields through the
  -- isomorphism `e'` of the two localizations of `S` at `q`, which is compatible with `A`.
  rcases y with ⟨y, rfl⟩
  let e' := IsLocalization.algEquiv q.primeCompl (Localization.AtPrime m.asIdeal)
    (X.presheaf.stalk y)
  have hcomp : (e' : Localization.AtPrime m.asIdeal →+* X.presheaf.stalk y).comp
      (algebraMap (Y.presheaf.stalk (g y)) (Localization.AtPrime m.asIdeal)) =
      (g.stalkMap y).hom := by
    refine IsLocalization.ringHom_ext M (RingHom.ext fun r ↦ ?_)
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    rw [← IsScalarTower.algebraMap_apply Γ(Y, U) (Y.presheaf.stalk (g y)),
      IsScalarTower.algebraMap_apply Γ(Y, U) Γ(X, g ⁻¹ᵁ U) (Localization.AtPrime m.asIdeal),
      AlgEquiv.commutes, hgerm, hgermy, Scheme.Hom.germ_stalkMap_apply, g.app_eq_appLE]
    rfl
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (g y)) (Localization.AtPrime m.asIdeal)) :=
    ⟨fun a ha ↦ isUnit_of_map_unit (g.stalkMap y).hom a
      (congr($hcomp a) ▸ ha.map (e' : Localization.AtPrime m.asIdeal →+* X.presheaf.stalk y))⟩
  rw [MaximalSpectrum.toNat_length_quotient_eq_finrank_residueField
    (S := Localization.AtPrime m.asIdeal)]
  exact g.residueDegree_eq_finrank_residueField y e'.toRingEquiv fun a ↦ congr($hcomp a)

/-- **The local projection formula.** Let `g : X ⟶ Y` be a finite dominant morphism of integral
schemes and `x` a point of `Y` whose local ring is noetherian of dimension at most one. For a
nonzero section `a` of `𝒪_Y` near `x`, the orders of vanishing of `g^* a` at the points `y` above
`x`, weighted by the residue degrees `[κ(y) : κ(x)]`, add up to `[K(X) : g^* K(Y)] · ord_x(a)`.
The morphism `g` need not be flat and the schemes need not be normal. -/
theorem finsum_residueDegree_mul_toNat_ord_eq_finrank_mul_toNat_ord (x : Y)
    [IsNoetherianRing (Y.presheaf.stalk x)] [Ring.KrullDimLE 1 (Y.presheaf.stalk x)]
    {U : Y.Opens} (hxU : x ∈ U) {a : Γ(Y, U)} (ha : a ≠ 0) :
    ∑ᶠ y : {y : X // g y = x}, g.residueDegree y *
      (Ring.ord (X.presheaf.stalk y) (X.presheaf.germ (g ⁻¹ᵁ U) y
        (g.mem_preimage.mpr (y.property.symm ▸ hxU)) (g.app U a))).toNat =
      Module.finrank g.functionFieldMap.hom.fieldRange X.functionField *
        (Ring.ord (Y.presheaf.stalk x) (Y.presheaf.germ U x hxU a)).toNat := by
  -- Restrict `a` to an affine neighbourhood `W ⊆ U` of `x`; this does not change its germs.
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hxU U.isOpen
  replace hWU : W ≤ U := hWU
  have hgerm : Y.presheaf.germ W x hxW (Y.presheaf.map (homOfLE hWU).op a) =
      Y.presheaf.germ U x hxU a :=
    Y.presheaf.germ_res_apply (homOfLE hWU) x hxW a
  have ha' : Y.presheaf.map (homOfLE hWU).op a ≠ 0 := fun h ↦
    ha (germ_injective_of_isIntegral Y x hxU (by rw [← hgerm, h, map_zero, map_zero]))
  rw [← hgerm, ← finsum_residueDegree_mul_toNat_ord_eq_of_isAffineOpen g x hW hxW ha']
  refine finsum_congr fun y ↦ ?_
  rw [← ConcreteCategory.comp_apply (Y.presheaf.map _) (g.app W), g.naturality,
    ConcreteCategory.comp_apply, X.presheaf.germ_res_apply']

/-- The local projection formula for an effective Cartier divisor `D = V(I)` on `Y`: at a point
`x`, the local multiplicities of `g⁻¹ D` above `x`, weighted by residue degrees, add up to
`[K(X) : g^* K(Y)]` times the local multiplicity of `D` at `x`. -/
private lemma finsum_residueDegree_mul_length_stalkIdeal_comap {I : Y.IdealSheafData}
    (hI : I.IsEffectiveCartier) (x : Y) [IsNoetherianRing (Y.presheaf.stalk x)]
    [Ring.KrullDimLE 1 (Y.presheaf.stalk x)] :
    ∑ᶠ y : {y : X // g y = x}, g.residueDegree y * (Module.length (X.presheaf.stalk y)
      (X.presheaf.stalk y ⧸ (I.comap g).stalkIdeal y)).toNat =
      Module.finrank g.functionFieldMap.hom.fieldRange X.functionField *
        (Module.length (Y.presheaf.stalk x) (Y.presheaf.stalk x ⧸ I.stalkIdeal x)).toNat := by
  obtain ⟨U, hxU, a, ha, hUa⟩ := (Scheme.IdealSheafData.isEffectiveCartier_iff I).mp hI x
  have : Nonempty U.val := ⟨⟨x, hxU⟩⟩
  have ha₀ : a ≠ 0 := fun h ↦ one_ne_zero (ha (show a • (1 : Γ(Y, U)) = a • 0 by simp [h]))
  rw [I.stalkIdeal_eq_map U x hxU, hUa, Ideal.map_span, Set.image_singleton]
  refine (finsum_congr fun y ↦ ?_).trans
    (finsum_residueDegree_mul_toNat_ord_eq_finrank_mul_toNat_ord g x hxU ha₀)
  rw [Scheme.IdealSheafData.stalkIdeal_comap, I.stalkIdeal_eq_map U _ (y.property.symm ▸ hxU),
    hUa, Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton,
    Scheme.Hom.germ_stalkMap_apply]
  rfl

end Scheme.Hom

namespace Scheme.IdealSheafData.IsEffectiveCartier

/-- **Inverse images of divisors along a finite dominant morphism.** Let `g : X ⟶ Y` be a finite
dominant morphism of integral schemes, `Y` locally noetherian of dimension at most one at every
point, and `D = V(I)` an effective Cartier divisor on `Y` finite over a field `K`. Then
`dim_K Γ(g⁻¹ D, 𝒪) = [K(X) : g^* K(Y)] · dim_K Γ(D, 𝒪)`, the dimensions being the ranks of the
finite morphisms to `Spec K`. Unlike `Scheme.IdealSheafData.finrank_comap_subschemeι_comp`, no
flatness is needed: `Y` may be a singular curve. -/
theorem finrank_comap_subschemeι_comp {K : Type u} [Field K] {I : Y.IdealSheafData}
    (hI : I.IsEffectiveCartier) (g : X ⟶ Y) [IsFinite g] [IsIntegral X] [IsIntegral Y]
    [IsDominant g] [IsLocallyNoetherian Y] (hY : ∀ y : Y, Order.coheight y ≤ 1)
    (f : Y ⟶ Spec (.of K)) [IsFinite (I.subschemeι ≫ f)] (s : Spec (.of K)) :
    ((I.comap g).subschemeι ≫ g ≫ f).finrank s =
      Module.finrank g.functionFieldMap.hom.fieldRange X.functionField *
        (I.subschemeι ≫ f).finrank s := by
  have := I.isFinite_comap_subschemeι_comp f g
  rw [Scheme.Hom.finrank_comp_eq_finsum_of_isClosedImmersion _ (g ≫ f) s,
    Scheme.Hom.finrank_comp_eq_finsum_of_isClosedImmersion _ f s, ker_subschemeι, ker_subschemeι,
    ← TauCeti.finsum_fiberwise g _ (((I.comap g).finite_support_length_stalkIdeal (g ≫ f)).subset
      (Function.support_mul_subset_right _ _)),
    mul_finsum]
  -- Regroup by the fibres of `g`, and apply the local projection formula at each point of `Y`.
  refine finsum_congr fun x ↦ ?_
  have := krullDimLE_of_coheight_le (hY x)
  rw [mul_left_comm, ← g.finsum_residueDegree_mul_length_stalkIdeal_comap hI x, mul_finsum]
  refine finsum_congr fun y ↦ ?_
  rw [Scheme.Hom.residueDegree_comp, y.property, mul_assoc]

end Scheme.IdealSheafData.IsEffectiveCartier

end AlgebraicGeometry
