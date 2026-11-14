/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGlueing.Ext
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.IsTensorProduct
import TauCeti.RingTheory.FormalGlueing.CyclicExt
import TauCeti.RingTheory.FormalGlueing.Koszul
import TauCeti.RingTheory.FormalGlueing.Torsion
import TauCeti.Algebra.Homology.Ext.Map.Surjective
import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Descent of extensions with ideal-power torsion quotient

Let `R → S` be flat and induce an isomorphism `R/I ≅ S/IS`, with `I` finitely generated.
Scalar extension induces a bijection on `Ext¹_R(M, N)` whenever `M` is `I`-power torsion.
The coefficient module `N` is arbitrary, and no Noetherianity or faithful flatness is needed.
Thus extensions with quotient supported on the formal neighbourhood descend uniquely at the
level of extension classes. This is the extension comparison used to reconstruct modules by
formal gluing.

For a cyclic quotient, use the Koszul complex on a finite set of ideal generators. Its first
cohomology is unchanged by the coefficient map `N → S ⊗ N`; the Ext-to-Koszul comparison gives
the same assertion for `Ext¹`. The extension--restriction adjunction converts this coefficient
comparison into scalar extension of extensions. A presentation by cyclic quotients then handles
arbitrary ideal-power torsion sources.

Consequently, an `S`-module `N` containing `S ⊗[R] K` with `I`-power torsion cokernel is the base
change of an `R`-module containing `K` with `I`-power torsion quotient
(`LinearMap.exists_isBaseChange_comp_eq_of_primaryComponent_eq_top`): the extension
`0 → S ⊗[R] K → N → N ⧸ (S ⊗[R] K) → 0` descends along scalar extension.

## References

* The Stacks Project, Lemma 15.91.8 (05EG), the degree-one extension comparison.
* The Stacks Project, Proposition 15.91.16 (05ER), reconstruction by formal gluing.
-/

public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

universe u

namespace RingHom

variable {R S : Type u} [CommRing R] [CommRing S]

/-- A flat ring map preserving the quotient by a finitely generated ideal preserves first Ext
with that cyclic quotient as source, with no restriction on the coefficient module. -/
theorem mapExt_one_bijective_of_quotient (f : R →+* S) (hf : f.Flat)
    (I : Ideal R) (hIfg : I.FG)
    (hI : Function.Bijective (Ideal.quotientMap (I.map f) f Ideal.le_comap_map))
    (N : ModuleCat.{u} R) :
    let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
    Function.Bijective ((ModuleCat.extendScalars f).mapExtAddHom
      (ModuleCat.of R (R ⧸ I)) N 1) := by
  algebraize [f]
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  obtain ⟨n, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hIfg
  let φ := Fintype.linearCombination R x
  have hφ : LinearMap.range φ = I := by
    simpa only [φ, Fintype.range_linearCombination] using hx
  have hcoeff := TauCeti.koszulComplex.postcomp_ext_mk_one_bijective_of_cohomologyMap_bijective
    (S := S) φ (hφ.symm ▸ hI) N
    (TauCeti.koszulComplex.homologyMap_coefficient_mk_one_bijective φ N (hφ.symm ▸ hI) 1)
  rw [hφ] at hcoeff
  apply (Adjunction.mapExt_bijective_iff_postcomp_unit_app
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)) (ModuleCat.of R (R ⧸ I)) N 1).mpr
  have hunit : (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).unit.app N =
      ModuleCat.ofHom (TensorProduct.mk R S N 1) := by
    ext m
    exact ModuleCat.extendRestrictScalarsAdj_unit_app_apply (algebraMap R S) N m
  rw [hunit]
  simp only [TauCeti.coe_postcompOfLinear] at hcoeff
  exact hcoeff

/-- **Descent of degree-one extension classes with ideal-power torsion source.** For a flat
ring map inducing `R/I ≅ S/IS` and finitely generated `I`, scalar extension preserves first Ext
bijectively when the source is `I`-power torsion. The coefficient module is unrestricted. -/
@[stacks 05EG "the degree-one extension comparison for ideal-power torsion sources"]
theorem mapExt_one_bijective_of_primaryComponent_eq_top (f : R →+* S) (hf : f.Flat)
    (I : Ideal R) (hIfg : I.FG)
    (hI : Function.Bijective (Ideal.quotientMap (I.map f) f Ideal.le_comap_map))
    (M N : ModuleCat.{u} R) (hM : I.primaryComponent M = ⊤) :
    let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
    Function.Bijective ((ModuleCat.extendScalars f).mapExtAddHom M N 1) := by
  algebraize [f]
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  refine ⟨f.mapExt_one_injective_of_primaryComponent_eq_top hf I hIfg hI M N hM,
    f.mapExt_one_surjective_of_quotient_pow hf I hIfg hI N (fun n ↦ ?_) M hM⟩
  exact (f.mapExt_one_bijective_of_quotient hf (I ^ n) hIfg.pow
    (Ideal.quotientMap_bijective_of_primaryComponent_eq_top I (I ^ n) hI
      (I.primaryComponent_quotient_pow_eq_top n)) N).surjective

end RingHom

namespace LinearMap

open Function

-- Mathlib's `ModuleCat.extendRestrictScalarsAdj`, which underlies the Ext comparison, relates
-- modules in one universe.
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

/-- **Descent of an extension with torsion cokernel.** Let `R → S` be flat and induce
`R/I ≅ S/IS`, where `I` is generated by a finite set `G`. Let `j : K → N` be an `R`-linear map
into an `S`-module whose scalar extension `S ⊗[R] K → N` is injective with `I`-power torsion
cokernel. Then `N` is the base change of an `R`-module `E` containing `K` with `I`-power torsion
quotient, by a map `ε : E → N` restricting to `j` on `K`. -/
theorem exists_isBaseChange_comp_eq_of_primaryComponent_eq_top {K N : Type u}
    [AddCommGroup K] [Module R K] [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] (j : K →ₗ[R] N) (G : Finset R)
    (hG : Bijective (Ideal.quotientMap ((Ideal.span (G : Set R)).map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map))
    (hj : Injective (j.liftBaseChange S))
    (hQ : (Ideal.span (G : Set R)).primaryComponent (N ⧸ range (j.liftBaseChange S)) = ⊤) :
    ∃ (E : ModuleCat.{u} R) (i : K →ₗ[R] E) (ε : E →ₗ[R] N), Injective i ∧
      (Ideal.span (G : Set R)).primaryComponent (E ⧸ range i) = ⊤ ∧ ε ∘ₗ i = j ∧
        IsBaseChange S ε := by
  classical
  set I := Ideal.span (G : Set R)
  set c := j.liftBaseChange S
  set Q := N ⧸ range c
  have hQS : (I.map (algebraMap R S)).primaryComponent Q = ⊤ := by
    refine eq_top_iff.mpr fun q _ ↦ ?_
    have hq := (Ideal.mem_primaryComponent_span_iff G).mp (hQ ▸ Submodule.mem_top (x := q))
    rw [Ideal.map_span, ← Finset.coe_image, Ideal.mem_primaryComponent_span_iff]
    intro s hs
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨n, hn⟩ := hq a ha
    exact ⟨n, by rw [← map_pow, algebraMap_smul, hn]⟩
  -- Descend the extension `0 → S ⊗ K → N → Q → 0` along extension of scalars `F`.
  have hflat : (algebraMap R S).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  let F := ModuleCat.extendScalars.{u, u, u} (algebraMap R S)
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  have hsurj : Surjective (F.mapExtAddHom (ModuleCat.of R Q) (ModuleCat.of R K) 1) :=
    (RingHom.mapExt_one_bijective_of_primaryComponent_eq_top (algebraMap R S) hflat I
      ⟨G, rfl⟩ hG (ModuleCat.of R Q) (ModuleCat.of R K) hQ).2
  let eK := ModuleCat.extendScalarsAlgebraMapIso (S := S) (ModuleCat.of R K)
  let eQ := ModuleCat.extendScalarsAlgebraMapIso (S := S) (ModuleCat.of R Q)
  let bQ := (TauCeti.isBaseChange_of_primaryComponent_eq_top hG hQS).equiv
  let i : F.obj (ModuleCat.of R K) ⟶ ModuleCat.of S N := eK.hom ≫ ModuleCat.ofHom c
  let p : ModuleCat.of S N ⟶ F.obj (ModuleCat.of R Q) :=
    ModuleCat.ofHom (bQ.symm.toLinearMap ∘ₗ (range c).mkQ) ≫ eQ.inv
  have hi (x) : i x = c (eK.hom x) := rfl
  have hp (y : N) : p y = eQ.symm.toLinearEquiv (bQ.symm ((range c).mkQ y)) := rfl
  have hp0 (y : N) : p y = 0 ↔ y ∈ range c := by
    rw [hp, LinearEquiv.map_eq_zero_iff, LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
  have hip : i ≫ p = 0 := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using (hp0 (i x)).mpr ⟨_, (hi x).symm⟩
  have hT : (ShortComplex.mk i p hip).ShortExact := by
    refine ModuleCat.shortComplex_shortExact _ (fun y ↦ (hp0 y).trans ?_) ?_ ?_
    · refine ⟨fun ⟨x, hx⟩ ↦ ⟨eK.inv x, ?_⟩, fun ⟨x, hx⟩ ↦ ⟨eK.hom x, hx⟩⟩
      simpa only [hi, Iso.inv_hom_id_apply] using hx
    · exact hj.comp eK.toLinearEquiv.injective
    · exact eQ.symm.toLinearEquiv.surjective.comp
        (bQ.symm.surjective.comp (range c).mkQ_surjective)
  obtain ⟨E, i₀, p₀, hi₀p₀, hS, e, he₁, -⟩ :=
    F.exists_shortExact_map_of_mapExt_one_surjective _ _ hsurj i p hip hT
  -- Read off the descended extension as linear maps.
  have hex : Function.Exact i₀ p₀ :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS.exact
  have hE : I.primaryComponent (E ⧸ range i₀.hom) = ⊤ := by
    refine eq_top_iff.mpr fun q _ ↦ ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    refine (Ideal.mem_primaryComponent_span_iff G).mpr fun a ha ↦ ?_
    obtain ⟨n, hn⟩ := (Ideal.mem_primaryComponent_span_iff G).mp
      (hQ ▸ Submodule.mem_top (x := p₀ x)) a ha
    obtain ⟨k, hk⟩ := (hex _).mp (by rw [map_smul, hn])
    refine ⟨n, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← hk]
    exact LinearMap.mem_range_self _ k
  let eL : S ⊗[R] E ≃ₗ[S] N :=
    ((ModuleCat.extendScalarsAlgebraMapIso E).symm ≪≫ e).toLinearEquiv
  let ε : E →ₗ[R] N := eL.toLinearMap.restrictScalars R ∘ₗ TensorProduct.mk R S E 1
  have hε (x : E) : ε x = eL (1 ⊗ₜ x) := rfl
  have he (y) : e.hom (F.map i₀ y) = i y := by rw [← he₁, ConcreteCategory.comp_apply]
  refine ⟨E, i₀.hom, ε, hS.moduleCat_injective_f, hE, LinearMap.ext fun k ↦ ?_,
    IsBaseChange.of_equiv eL fun x ↦ (hε x).symm⟩
  have h : F.map i₀ (eK.inv ((1 : S) ⊗ₜ[R] k)) =
      (ModuleCat.extendScalarsAlgebraMapIso E).inv ((1 : S) ⊗ₜ[R] i₀ k) := by
    rw [ModuleCat.extendScalarsAlgebraMapIso_inv_tmul,
      ModuleCat.extendScalarsAlgebraMapIso_inv_tmul]
    exact ModuleCat.ExtendScalars.map_tmul _ _ _ _
  rw [LinearMap.comp_apply, hε, Iso.toLinearEquiv_apply, Iso.trans_hom, Iso.symm_hom,
    ConcreteCategory.comp_apply, ← h, he, hi, Iso.inv_hom_id_apply, liftBaseChange_tmul, one_smul]

end LinearMap
