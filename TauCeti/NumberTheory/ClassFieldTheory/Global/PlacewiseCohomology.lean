/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.SIdeles
public import TauCeti.NumberTheory.ClassFieldTheory.Global.SemilocalUnits
public import TauCeti.NumberTheory.NumberField.Discriminant.RamifiedSupport.Basic
public import TauCeti.RepresentationTheory.Homological.TateCohomology.DirectedUnion
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Pi
import TauCeti.Data.DFinsupp.Basic

/-!
# The cohomology of the ideles, place by place

Let `L/K` be a finite Galois extension of number fields with Galois group `G`. The ideles `I_L` of
`L`, as a representation of `G`, map to the semi-local unit groups `(K_v ⊗[K] L)ˣ ≃ ∏_{w ∣ v} L_wˣ`
at every place `v` of `K`, finite (`idelesToSemilocalUnits`) or infinite
(`idelesToInfiniteSemilocalUnits`). This file shows that in every positive degree `n` these maps
identify the cohomology of the ideles with the direct sum of the semi-local cohomology groups,

```text
H^n(G, I_L) ≃ ⨁_v H^n(G, (K_v ⊗[K] L)ˣ)
```

(`idelesCohomologyLocalizationEquiv`), the sum running over the finite and the infinite places:

* a class of `H^n(G, I_L)` whose images in all the groups `H^n(G, (K_v ⊗[K] L)ˣ)` vanish is zero
  (`eq_zero_of_forall_map_semilocal_eq_zero`);
* only finitely many of its images at the finite places are nonzero
  (`finite_setOf_map_idelesToSemilocalUnits_ne_zero`);
* every finitely supported family of semi-local classes is the family of images of a class
  (`idelesCohomologyLocalization_surjective`);
* its first cohomology vanishes (`isZero_tateCohomology_one_idelesRep`), by field Hilbert 90
  and Shapiro at every finite and infinite place, without a cyclicity hypothesis.

By positive-degree Shapiro (`HeightOneSpectrum.semilocalUnitsTateCohomologyIsoPos` at the finite
places, `InfinitePlace.infiniteSemilocalUnitsTateCohomologyIsoPos` at the infinite places) the group
`H^n(G, (K_v ⊗[K] L)ˣ)` is the cohomology `H^n(G_w, L_wˣ)` of the completion at a place `w ∣ v`,
so the images of a degree-`2` cohomology class with coefficients in the ideles are its local Brauer
classes in `Br(L_w/K_v)`, and `H²(G, I_L)` is the direct sum of the local Brauer groups
`Br(L_w/K_v)`. The first statement is the idelic half of the injectivity of
`Br(L/K) → ⨁_v Br(L_w/K_v)`; the other half is the vanishing of `H¹(G, C_L)`.

The proof is Milne's (*Class Field Theory*, VII, Lemma 2.4 and Proposition 2.5). The ideles are the
union of the `S`-ideles over the finite sets `S` of finite places, so every class comes from the
`S`-ideles for a finite `S` that may be taken to contain the places ramified in `L`
(`TauCeti.TateCohomology.exists_tateCohomologyFunctor_map_eq`). The `S`-ideles split as
`I_{L,S} = L_∞ˣ × I_{L,S}^f` (`sIdeles_hom_decomp`), the infinite ideles are the product
of the archimedean semi-local unit groups (`TauCeti.GlobalNumberFields.infiniteIdelesPiIso`), and
the finite `S`-ideles are the product of the semi-local unit groups at `S` and of the integral
semi-local unit groups away from `S` (`TauCeti.finiteSIdelesPiIso`). Tate cohomology commutes with
products (`TauCeti.TateCohomology.linearEquivPi`), and the integral factors, at places unramified
in `L`, have no cohomology in positive degrees
(`isZero_tateCohomology_semilocalIntegralUnitsRep_of_neZero`). Read backwards, the same
decomposition prescribes the semi-local components: a family supported on such an `S` is the image
of a class of the `S`-ideles, built factor by factor.

## Main definitions

* `TauCeti.ClassFieldTheory.idelesToSemilocalUnits L v`,
  `TauCeti.ClassFieldTheory.idelesToInfiniteSemilocalUnits L w`: the semi-local components of an
  idele at a finite place `v` and at an infinite place `w` of `K`.
* `TauCeti.ClassFieldTheory.idelesCohomologyLocalization K L n`: the map
  `H^n(G, I_L) → ⨁_v H^n(G, (K_v ⊗[K] L)ˣ)` taking a class to its semi-local components.
* `TauCeti.ClassFieldTheory.idelesCohomologyLocalizationEquiv K L n`: the same map, as an
  isomorphism for `n > 0`.

## Main results

* `TauCeti.ClassFieldTheory.eq_zero_of_forall_map_semilocal_eq_zero`: a class of
  `H^n(G, I_L)`, `n > 0`, with vanishing semi-local components is zero.
* `TauCeti.ClassFieldTheory.finite_setOf_map_idelesToSemilocalUnits_ne_zero`: a class of
  `H^n(G, I_L)`, `n > 0`, has nonzero semi-local components at only finitely many finite places.
* `TauCeti.ClassFieldTheory.idelesCohomologyLocalization_surjective`: for `n > 0`, every finitely
  supported family of semi-local classes is the family of semi-local components of a class.
* `TauCeti.ClassFieldTheory.isZero_tateCohomology_one_idelesRep`: Hilbert 90 for ideles,
  on the Tate carrier.
* `TauCeti.ClassFieldTheory.subsingleton_groupCohomology_one_idelesRep`: Hilbert 90 on ordinary
  cohomology, as an instance.

In the long exact cohomology sequence of `Lˣ → I_L → C_L`, idelic Hilbert 90 makes
`H¹(Gal(L/K), C_L) → H²(Gal(L/K), Lˣ)` injective. Thus vanishing of idele-class `H¹` is
equivalent to injectivity of the map from relative Brauer classes to idelic cohomology.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, Lemma 2.4, Proposition 2.5
  and Corollary 2.6.
* J. Tate, *Global class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VII, §§6–7.
-/

public section
noncomputable section

open CategoryTheory Limits IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped AdeleGaloisAction TensorProduct

namespace TauCeti.ClassFieldTheory

open GlobalNumberFields

variable {K : Type} [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]

/-! ### The semi-local components of an idele -/

section Components

/-- **The semi-local component of an idele at a finite place** `v` of `K`, its components at the
places `w ∣ v` of `L` as a unit of `K_v ⊗[K] L ≃ ∏_{w ∣ v} L_w`, as a morphism of representations
of `Aut(L/K)`. -/
def idelesToSemilocalUnits (v : HeightOneSpectrum (𝓞 K)) :
    idelesRep K L ⟶ semilocalUnitsRep L v :=
  Rep.ofHom <| LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    ((finiteIdeleSemilocalHom L v).comp (IdeleGroup.toFiniteIdele (𝓞 L) L)
      ).toAdditive.toIntLinearMap
    fun σ x ↦ congrArg Additive.ofMul <| (congrArg (finiteIdeleSemilocalHom L v)
      (toFiniteIdele_smul σ x.toMul)).trans
        (finiteIdeleSemilocalHom_map_finiteAdeleGaloisAction v σ _)

/-- `idelesToSemilocalUnits L v` is the semi-local component at `v` of the finite part. -/
-- Normalize the implicit restriction parameters so the simp rule matches after `Rep.res_obj_ρ`.
@[simp]
theorem idelesToSemilocalUnits_hom_apply (v : HeightOneSpectrum (𝓞 K))
    (x : Additive (IdeleGroup (𝓞 L) L)) :
    dsimp% only [Rep.ofAlgebraAutOnUnits, Rep.res_obj_ρ]
      ((idelesToSemilocalUnits L v).hom x =
        Additive.ofMul (finiteIdeleSemilocalHom L v (IdeleGroup.toFiniteIdele (𝓞 L) L x.toMul))) :=
  (rfl)

/-- **The semi-local component of an idele at an infinite place** `w` of `K`, its components at
the places of `L` above `w` as a unit of `K_w ⊗[K] L`, as a morphism of representations of
`Aut(L/K)`. -/
def idelesToInfiniteSemilocalUnits (w : InfinitePlace K) :
    idelesRep K L ⟶ infiniteSemilocalUnitsRep L w :=
  idelesToInfiniteIdeles K L ≫ (infiniteIdelesPiIso K L).hom ≫ Rep.piProj _ w

/-- `idelesToInfiniteSemilocalUnits L w` is the semi-local component at `w` of the infinite
part. -/
-- Normalize the implicit restriction parameters so the simp rule matches after `Rep.res_obj_ρ`.
@[simp]
theorem coe_idelesToInfiniteSemilocalUnits_hom_apply (w : InfinitePlace K)
    (x : Additive (IdeleGroup (𝓞 L) L)) :
    dsimp% only [Rep.ofAlgebraAutOnUnits, Rep.res_obj_ρ]
      ((Additive.toMul (α := (w.Completion ⊗[K] L)ˣ) ((idelesToInfiniteSemilocalUnits L w).hom x) :
        w.Completion ⊗[K] L) =
        infiniteAdeleSemilocalHom L w (x.toMul : AdeleRing (𝓞 L) L).1) :=
  -- `idelesToInfiniteSemilocalUnits L w` is by definition the component at `w` of the image of
  -- the infinite part under `infiniteIdelesPiIso`, and the infinite part of `x` has underlying
  -- infinite adele the first component of `x`
  (congrArg (fun z ↦ ((Additive.toMul (α := (w.Completion ⊗[K] L)ˣ) z : _) : w.Completion ⊗[K] L))
    (Rep.piProj_hom_apply _ _)).trans <|
      (coe_infiniteIdelesPiIso_hom_apply ((idelesToInfiniteIdeles K L).hom x) w).trans <|
        congrArg (infiniteAdeleSemilocalHom L w) <|
          congrArg (fun z ↦ ((Additive.toMul z : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L))
            (idelesToInfiniteIdeles_hom_apply L x)

end Components

/-! ### The `S`-ideles inside the ideles -/

section SIdeles

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- At a place `v ∈ S`, the semi-local component of an `S`-idele is read off its finite part
through `finiteSIdelesPiIso`. -/
private theorem sIdelesToFiniteSIdeles_comp_piProj_inl (v : S) :
    sIdelesToFiniteSIdeles L S ≫ (finiteSIdelesPiIso L S).hom ≫ Rep.piProj _ (Sum.inl v) =
      sIdelesToIdeles (K := K) L S ≫ idelesToSemilocalUnits L v.1 := by
  ext x
  -- both composites take the semi-local component at `v` of the finite part
  have h : (sIdelesToIdeles (K := K) L S ≫ idelesToSemilocalUnits L v.1).hom x =
      Additive.ofMul (finiteIdeleSemilocalHom L v.1
        (IdeleGroup.toFiniteIdele (𝓞 L) L
          (Additive.toMul (α := sIdeles L (S : Set (HeightOneSpectrum (𝓞 K)))) x).1)) :=
    (congrArg (idelesToSemilocalUnits L v.1).hom
      (sIdelesToIdeles_hom_apply (K := K) L S x)).trans
        (idelesToSemilocalUnits_hom_apply L v.1 _)
  exact ((Rep.piProj_hom_apply _ _).trans <|
    (congrArg (fun z ↦ (finiteSIdelesPiIso L S).hom.hom z (Sum.inl v))
      (sIdelesToFiniteSIdeles_hom_apply L S x)).trans
        (finiteSIdelesPiIso_hom_apply_inl L S _ v)).trans h.symm

/-- At a place `v ∉ S`, the semi-local component of an `S`-idele is integral; as a morphism of
representations. -/
private def sIdelesToSemilocalIntegralUnits (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    sIdelesRep (K := K) L S ⟶ semilocalIntegralUnitsRep L v :=
  Rep.ofHom <| LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (((finiteIdeleSemilocalHom L v).comp ((IdeleGroup.toFiniteIdele (𝓞 L) L).comp
      (sIdeles L (S : Set (HeightOneSpectrum (𝓞 K)))).subtype)).codRestrict
        (semilocalIntegralUnits L v) fun x ↦
          mem_finiteSIdeles_iff.1 (toFiniteIdele_mem_finiteSIdeles_iff.2 x.2) v hv
      ).toAdditive.toIntLinearMap
    fun σ x ↦ congrArg Additive.ofMul <| Subtype.ext <| (congrArg (finiteIdeleSemilocalHom L v)
      (toFiniteIdele_smul σ x.toMul.1)).trans
        (finiteIdeleSemilocalHom_map_finiteAdeleGaloisAction v σ _)

/-- At a place `v ∉ S`, the semi-local component of an `S`-idele factors through the integral
semi-local units. -/
private theorem sIdelesToSemilocalIntegralUnits_comp_incl (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ S) :
    sIdelesToSemilocalIntegralUnits L S v hv ≫ semilocalIntegralUnitsIncl L v =
      sIdelesToIdeles (K := K) L S ≫ idelesToSemilocalUnits L v := by
  ext x
  -- both send an `S`-idele to the semi-local component at `v` of its finite part
  exact (semilocalIntegralUnitsIncl_apply v _).trans ((congrArg (idelesToSemilocalUnits L v).hom
    (sIdelesToIdeles_hom_apply (K := K) L S x)).trans
      (idelesToSemilocalUnits_hom_apply L v _)).symm

end SIdeles

/-! ### The cohomology of the ideles -/

section Cohomology

variable [IsGalois K L]

/-- At a finite place of `K` outside a set containing the ramified places, the integral
semi-local units have no cohomology in positive degrees. -/
private theorem isZero_tateCohomology_semilocalIntegralUnitsRep_of_notMem
    {S : Finset (HeightOneSpectrum (𝓞 K))} (hS : NumberField.ramifiedSupport K L ⊆ S)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) (n : ℕ) [NeZero n] :
    IsZero (tateCohomology (semilocalIntegralUnitsRep L v) n) := by
  obtain ⟨w, rfl⟩ := under_surjective (𝓞 K) (𝓞 L) v
  have := NumberField.isUnramifiedAway_ramifiedSupport (w.under (𝓞 K)) (fun h ↦ hv (hS h))
    w.asIdeal
  exact isZero_tateCohomology_semilocalIntegralUnitsRep_of_neZero (w.under (𝓞 K)) w n

omit [IsGalois K L] in
/-- Every class of `H^n(G, I_L)` comes from the `S`-ideles for a finite set `S` of finite places
containing the ramified ones. -/
private theorem exists_map_sIdelesToIdeles_eq (n : ℤ) (x : tateCohomology (idelesRep K L) n) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), NumberField.ramifiedSupport K L ⊆ S ∧
      ∃ y, ((tateCohomologyFunctor n).map (sIdelesToIdeles (K := K) L S)).hom y = x := by
  classical
  -- a finite set of ideles lies in the `S`-ideles for the union of the sets that work for each
  have hcover (s : Finset (idelesRep K L)) : ∃ S : {S : Finset (HeightOneSpectrum (𝓞 K)) //
      NumberField.ramifiedSupport K L ⊆ S},
        ∀ x ∈ s, x ∈ Set.range (sIdelesToIdeles (K := K) L S.1).hom := by
    choose S hRS hS using fun x : idelesRep K L ↦ exists_finset_mem_sIdeles
      (NumberField.ramifiedSupport K L) (Additive.toMul x : IdeleGroup (𝓞 L) L)
    let T := NumberField.ramifiedSupport K L ∪ s.sup S
    refine ⟨⟨T, Finset.subset_union_left⟩, fun x hx ↦
      ⟨Additive.ofMul ⟨Additive.toMul x, sIdeles_mono ?_ (hS x)⟩,
        sIdelesToIdeles_hom_apply (K := K) L T _⟩⟩
    exact Finset.coe_subset.2 ((Finset.le_sup hx).trans Finset.subset_union_right)
  obtain ⟨⟨S, hS⟩, y, hy⟩ := TateCohomology.exists_tateCohomologyFunctor_map_eq
    (fun S : {S : Finset (HeightOneSpectrum (𝓞 K)) // NumberField.ramifiedSupport K L ⊆ S} ↦
      sIdelesToIdeles (K := K) L S.1) (fun S ↦ sIdelesToIdeles_hom_injective (K := K) L S.1)
    hcover n x
  exact ⟨S, hS, y, hy⟩

variable (n : ℕ) [NeZero n]

/-- **The cohomology of the ideles is detected place by place.** For a finite Galois extension
`L/K` of number fields and `n > 0`, a class of `H^n(Gal(L/K), I_L)` whose images in
`H^n(Gal(L/K), (K_v ⊗[K] L)ˣ)` vanish at every finite and every infinite place `v` of `K` is
zero. -/
theorem eq_zero_of_forall_map_semilocal_eq_zero
    {x : tateCohomology (idelesRep K L) n}
    (hfin : ∀ v, ((tateCohomologyFunctor n).map (idelesToSemilocalUnits L v)).hom x = 0)
    (hinf : ∀ w, ((tateCohomologyFunctor n).map (idelesToInfiniteSemilocalUnits L w)).hom x = 0) :
    x = 0 := by
  classical
  obtain ⟨S, hS, y, rfl⟩ := exists_map_sIdelesToIdeles_eq L n x
  -- a component of `y` that factors through the ideles vanishes when that of `x` does
  have hy {Y Z : Rep ℤ (L ≃ₐ[K] L)} (f : sIdelesRep (K := K) L S ⟶ Y) (g : Y ⟶ Z)
      (g' : idelesRep K L ⟶ Z) (hfg : f ≫ g = sIdelesToIdeles (K := K) L S ≫ g')
      (hg : ((tateCohomologyFunctor n).map g').hom
        (((tateCohomologyFunctor n).map (sIdelesToIdeles (K := K) L S)).hom y) = 0) :
      ((tateCohomologyFunctor n).map g).hom (((tateCohomologyFunctor n).map f).hom y) = 0 := by
    simpa only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, hg] using
      congrArg (fun φ ↦ ((tateCohomologyFunctor n).map φ).hom y) hfg
  -- a component of `y` vanishes when its image under an isomorphism does
  have hiso {Y Z : Rep ℤ (L ≃ₐ[K] L)} (f : sIdelesRep (K := K) L S ⟶ Y) (e : Y ≅ Z)
      (he : ((tateCohomologyFunctor n).map (f ≫ e.hom)).hom y = 0) :
      ((tateCohomologyFunctor n).map f).hom y = 0 := by
    rw [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at he
    exact (map_eq_zero_iff _ ((ModuleCat.mono_iff_injective _).1 inferInstance)).1 he
  -- the finite part of `y` vanishes: its components at `S` are those of `x`, and the factors
  -- away from `S` have no cohomology
  have hfin' : ((tateCohomologyFunctor n).map (sIdelesToFiniteSIdeles L S)).hom y = 0 := by
    refine hiso _ (finiteSIdelesPiIso L S) <|
      (TateCohomology.linearEquivPi _ n).injective (funext fun i ↦ ?_)
    rw [TateCohomology.linearEquivPi_apply, map_zero, Pi.zero_apply]
    rcases i with v | v
    · exact hy _ _ _ ((Category.assoc _ _ _).trans (sIdelesToFiniteSIdeles_comp_piProj_inl L S v))
        (hfin v)
    · exact (ModuleCat.subsingleton_of_isZero
        (isZero_tateCohomology_semilocalIntegralUnitsRep_of_notMem L hS v.2 n)).elim _ _
  -- the infinite part of `y` vanishes: its components are those of `x`
  have hinf' : ((tateCohomologyFunctor n).map
      (sIdelesToIdeles (K := K) L S ≫ idelesToInfiniteIdeles K L)).hom y = 0 := by
    refine hiso _ (infiniteIdelesPiIso K L) <|
      (TateCohomology.linearEquivPi _ n).injective (funext fun w ↦ ?_)
    rw [TateCohomology.linearEquivPi_apply, map_zero, Pi.zero_apply]
    exact hy _ _ _ (by simp only [idelesToInfiniteSemilocalUnits, Category.assoc]) (hinf w)
  -- an `S`-idele is the product of its infinite part and its finite part
  have hy0 : y = 0 := by
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at hinf'
    simpa only [CategoryTheory.Functor.map_id, ModuleCat.hom_id, LinearMap.id_apply,
      Functor.map_add, ModuleCat.hom_add, LinearMap.add_apply, Functor.map_comp,
      ModuleCat.hom_comp, LinearMap.comp_apply, hinf', hfin', map_zero, add_zero] using
      congrArg (fun φ ↦ ((tateCohomologyFunctor n).map φ).hom y) (sIdeles_hom_decomp L S)
  rw [hy0, map_zero]

/-- **The semi-local components of a cohomology class with coefficients in the ideles are finitely
supported.** For a finite Galois extension `L/K` of number fields and `n > 0`, a class of
`H^n(Gal(L/K), I_L)` has nonzero image in `H^n(Gal(L/K), (K_v ⊗[K] L)ˣ)` at only finitely many
finite places `v` of `K`. -/
theorem finite_setOf_map_idelesToSemilocalUnits_ne_zero (x : tateCohomology (idelesRep K L) n) :
    {v | ((tateCohomologyFunctor n).map (idelesToSemilocalUnits L v)).hom x ≠ 0}.Finite := by
  obtain ⟨S, hS, y, rfl⟩ := exists_map_sIdelesToIdeles_eq L n x
  refine S.finite_toSet.subset fun v hv ↦ ?_
  by_contra hvS
  refine hv ?_
  -- the image factors through the integral semi-local units, which have no cohomology
  have := ModuleCat.subsingleton_of_isZero
    (isZero_tateCohomology_semilocalIntegralUnitsRep_of_notMem L hS hvS n)
  simpa only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
    Subsingleton.elim (((tateCohomologyFunctor n).map
      (sIdelesToSemilocalIntegralUnits L S v hvS)).hom y) 0, map_zero] using
    (congrArg (fun φ ↦ ((tateCohomologyFunctor n).map φ).hom y)
      (sIdelesToSemilocalIntegralUnits_comp_incl L S v hvS)).symm

end Cohomology

/-! ### Prescribing the semi-local components -/

section Prescribe

variable [IsGalois K L] (n : ℕ) [NeZero n]

/-- Every family of semi-local classes at the finite places, vanishing outside a finite set `S`,
together with a family at the infinite places, is the family of semi-local components of a class
with coefficients in the ideles. -/
private theorem exists_map_semilocal_eq (S : Finset (HeightOneSpectrum (𝓞 K)))
    (y : ∀ v, tateCohomology (semilocalUnitsRep L v) n) (hy : ∀ v ∉ S, y v = 0)
    (z : ∀ w, tateCohomology (infiniteSemilocalUnitsRep L w) n) :
    ∃ x : tateCohomology (idelesRep K L) n,
      (∀ v, ((tateCohomologyFunctor n).map (idelesToSemilocalUnits L v)).hom x = y v) ∧
        ∀ w, ((tateCohomologyFunctor n).map (idelesToInfiniteSemilocalUnits L w)).hom x = z w := by
  classical
  let F := tateCohomologyFunctor (R := ℤ) (G := L ≃ₐ[K] L) n
  have hF {X Y Z : Rep ℤ (L ≃ₐ[K] L)} (f : X ⟶ Y) (g : Y ⟶ Z) (c : tateCohomology X n) :
      (F.map g).hom ((F.map f).hom c) = (F.map (f ≫ g)).hom c := by
    rw [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  set T := NumberField.ramifiedSupport K L ∪ S
  -- a class of the finite `T`-ideles with components `y` at the places of `T`
  obtain ⟨a, ha⟩ : ∃ a : tateCohomology (finiteSIdelesRep L T) n, ∀ v : T,
      (F.map ((finiteSIdelesPiIso L T).hom ≫ Rep.piProj _ (Sum.inl v))).hom a = y v.1 :=
    ⟨(F.map (finiteSIdelesPiIso L T).inv).hom
      ((TateCohomology.linearEquivPi _ n).symm (Sum.rec (fun v ↦ y v.1) fun _ ↦ 0)), fun v ↦ by
        rw [hF, Iso.inv_hom_id_assoc, ← TateCohomology.linearEquivPi_apply,
          LinearEquiv.apply_symm_apply]⟩
  -- a class of the infinite ideles with components `z`
  obtain ⟨b, hb⟩ : ∃ b : tateCohomology (infiniteIdelesRep K L) n, ∀ w,
      (F.map ((infiniteIdelesPiIso K L).hom ≫ Rep.piProj _ w)).hom b = z w :=
    ⟨(F.map (infiniteIdelesPiIso K L).inv).hom ((TateCohomology.linearEquivPi _ n).symm z),
      fun w ↦ by
        rw [hF, Iso.inv_hom_id_assoc, ← TateCohomology.linearEquivPi_apply,
          LinearEquiv.apply_symm_apply]⟩
  -- the class of the `T`-ideles with finite part `a` and infinite part `b`
  set c := (F.map (finiteSIdelesToSIdeles L T)).hom a + (F.map (infiniteIdelesToSIdeles L T)).hom b
  have hcf : (F.map (sIdelesToFiniteSIdeles L T)).hom c = a := by
    rw [map_add, hF, hF]
    simp
  have hci : (F.map (sIdelesToIdeles (K := K) L T ≫ idelesToInfiniteIdeles K L)).hom c = b := by
    rw [map_add, hF, hF]
    simp
  refine ⟨(F.map (sIdelesToIdeles (K := K) L T)).hom c, fun v ↦ ?_, fun w ↦ ?_⟩
  · rw [hF]
    by_cases hv : v ∈ T
    · -- at a place of `T`, the component is read off the finite part
      exact (congrArg (fun φ ↦ (F.map φ).hom c)
        (sIdelesToFiniteSIdeles_comp_piProj_inl L T ⟨v, hv⟩)).symm.trans
          ((hF _ _ c).symm.trans ((congrArg _ hcf).trans (ha ⟨v, hv⟩)))
    · -- away from `T`, the component factors through the integral semi-local units, which have no
      -- cohomology
      have := ModuleCat.subsingleton_of_isZero
        (isZero_tateCohomology_semilocalIntegralUnitsRep_of_notMem L Finset.subset_union_left hv n)
      rw [hy v fun h ↦ hv (Finset.mem_union_right _ h),
        ← sIdelesToSemilocalIntegralUnits_comp_incl L T v hv, ← hF,
        Subsingleton.elim ((F.map (sIdelesToSemilocalIntegralUnits L T v hv)).hom c) 0, map_zero]
  · rw [← hb, ← hci, hF, hF]
    simp only [idelesToInfiniteSemilocalUnits, Category.assoc]

variable (K) in
/-- **The semi-local components of the cohomology of the ideles.** For a finite Galois extension
`L/K` of number fields and `n > 0`, the map
`H^n(Gal(L/K), I_L) → ⨁_v H^n(Gal(L/K), (K_v ⊗[K] L)ˣ)` taking a class to its semi-local
components, as a finitely supported family at the finite places
(`finite_setOf_map_idelesToSemilocalUnits_ne_zero`) together with a family at the infinite places.
It is an isomorphism (`idelesCohomologyLocalizationEquiv`). -/
def idelesCohomologyLocalization : tateCohomology (idelesRep K L) n →+
    (Π₀ v : HeightOneSpectrum (𝓞 K), tateCohomology (semilocalUnitsRep L v) n) ×
      ((w : InfinitePlace K) → tateCohomology (infiniteSemilocalUnitsRep L w) n) where
  toFun x :=
    (dfinsuppOfFiniteSupport
      (fun v ↦ ((tateCohomologyFunctor n).map (idelesToSemilocalUnits L v)).hom x)
      (finite_setOf_map_idelesToSemilocalUnits_ne_zero L n x),
      fun w ↦ ((tateCohomologyFunctor n).map (idelesToInfiniteSemilocalUnits L w)).hom x)
  map_zero' := Prod.ext (DFinsupp.ext fun _ ↦ by simp) (funext fun _ ↦ map_zero _)
  map_add' x y := Prod.ext (DFinsupp.ext fun _ ↦ by simp) (funext fun _ ↦ map_add _ x y)

/-- The component of `idelesCohomologyLocalization` at a finite place `v` is induced by the
semi-local component at `v`. -/
@[simp]
theorem idelesCohomologyLocalization_fst_apply (x : tateCohomology (idelesRep K L) n)
    (v : HeightOneSpectrum (𝓞 K)) :
    (idelesCohomologyLocalization K L n x).1 v =
      ((tateCohomologyFunctor n).map (idelesToSemilocalUnits L v)).hom x :=
  dfinsuppOfFiniteSupport_apply _ _ v

/-- The component of `idelesCohomologyLocalization` at an infinite place `w` is induced by the
semi-local component at `w`. -/
@[simp]
theorem idelesCohomologyLocalization_snd_apply (x : tateCohomology (idelesRep K L) n)
    (w : InfinitePlace K) :
    (idelesCohomologyLocalization K L n x).2 w =
      ((tateCohomologyFunctor n).map (idelesToInfiniteSemilocalUnits L w)).hom x :=
  (rfl)

variable (K) in
/-- A class with coefficients in the ideles is determined by its semi-local components. -/
theorem idelesCohomologyLocalization_injective :
    Function.Injective (idelesCohomologyLocalization K L n) :=
  (injective_iff_map_eq_zero _).2 fun x hx ↦ eq_zero_of_forall_map_semilocal_eq_zero L n
    (fun v ↦ by simpa using congrArg (fun y ↦ y.1 v) hx)
    (fun w ↦ by simpa using congrArg (fun y ↦ y.2 w) hx)

variable (K) in
/-- Every finitely supported family of semi-local classes is the family of semi-local components
of a class with coefficients in the ideles. -/
theorem idelesCohomologyLocalization_surjective :
    Function.Surjective (idelesCohomologyLocalization K L n) := by
  classical
  rintro ⟨y, z⟩
  obtain ⟨x, hy, hz⟩ := exists_map_semilocal_eq L n y.support y
    (fun v hv ↦ DFinsupp.notMem_support_iff.1 hv) z
  exact ⟨x, Prod.ext (DFinsupp.ext fun v ↦ by simp [hy]) (funext fun w ↦ by simp [hz])⟩

variable (K) in
/-- **The cohomology of the ideles is the direct sum of the semi-local cohomology groups.** For a
finite Galois extension `L/K` of number fields and `n > 0`,
`H^n(Gal(L/K), I_L) ≃ ⨁_v H^n(Gal(L/K), (K_v ⊗[K] L)ˣ)`, the sum running over the finite and the
infinite places of `K`, by taking semi-local components. -/
def idelesCohomologyLocalizationEquiv : tateCohomology (idelesRep K L) n ≃+
    (Π₀ v : HeightOneSpectrum (𝓞 K), tateCohomology (semilocalUnitsRep L v) n) ×
      ((w : InfinitePlace K) → tateCohomology (infiniteSemilocalUnitsRep L w) n) :=
  AddEquiv.ofBijective (idelesCohomologyLocalization K L n)
    ⟨idelesCohomologyLocalization_injective K L n, idelesCohomologyLocalization_surjective K L n⟩

/-- `idelesCohomologyLocalizationEquiv` takes a class to its semi-local components. -/
@[simp]
theorem coe_idelesCohomologyLocalizationEquiv :
    ⇑(idelesCohomologyLocalizationEquiv K L n) = idelesCohomologyLocalization K L n :=
  (rfl)

end Prescribe

section Hilbert90

variable {L} [IsGalois K L]

/-- **Hilbert 90 for ideles.** The first Tate cohomology of the idele module of a finite Galois
extension of number fields vanishes. -/
theorem isZero_tateCohomology_one_idelesRep : IsZero (tateCohomology (idelesRep K L) 1) := by
  have h (x : tateCohomology (idelesRep K L) 1) : x = 0 := by
    apply eq_zero_of_forall_map_semilocal_eq_zero L 1
    · intro v
      exact (ModuleCat.subsingleton_of_isZero
        (v.isZero_tateCohomology_one_semilocalUnitsRep (L := L))).elim _ _
    · intro v
      exact (ModuleCat.subsingleton_of_isZero
        (v.isZero_tateCohomology_one_infiniteSemilocalUnitsRep (L := L))).elim _ _
  have : Subsingleton (tateCohomology (idelesRep K L) 1) :=
    ⟨fun x y => (h x).trans (h y).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- **Hilbert 90 for ideles**, on ordinary group cohomology: `H¹(Gal(L/K), I_L) = 0`. -/
instance subsingleton_groupCohomology_one_idelesRep :
    Subsingleton (groupCohomology (idelesRep K L) 1) :=
  ModuleCat.subsingleton_of_isZero <| isZero_tateCohomology_one_idelesRep.of_iso
    ((_root_.TateCohomology.isoGroupCohomology 1).app (idelesRep K L)).symm

end Hilbert90

end TauCeti.ClassFieldTheory
