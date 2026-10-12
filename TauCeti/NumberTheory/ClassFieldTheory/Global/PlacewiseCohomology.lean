/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.SIdeles
public import TauCeti.NumberTheory.ClassFieldTheory.Global.SemilocalUnits
public import TauCeti.RepresentationTheory.Homological.TateCohomology.DirectedUnion
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Pi

/-!
# The cohomology of the ideles, place by place

Let `L/K` be a finite Galois extension of number fields with Galois group `G`. The ideles `I_L` of
`L`, as a representation of `G`, map to the semi-local unit groups `(K_v ⊗[K] L)ˣ ≃ ∏_{w ∣ v} L_wˣ`
at every place `v` of `K`, finite (`idelesToSemilocalUnits`) or infinite
(`idelesToInfiniteSemilocalUnits`). This file shows that in every positive degree `n` these maps
detect the cohomology of the ideles:

* a class of `H^n(G, I_L)` whose images in all the groups `H^n(G, (K_v ⊗[K] L)ˣ)` vanish is zero
  (`eq_zero_of_forall_map_semilocal_eq_zero`);
* only finitely many of its images at the finite places are nonzero
  (`finite_setOf_map_idelesToSemilocalUnits_ne_zero`).

By Shapiro's lemma (`semilocalUnitsTateCohomologyIso` for cyclic `G`) the group
`H^n(G, (K_v ⊗[K] L)ˣ)` is the cohomology `H^n(G_w, L_wˣ)` of the completion at a place `w ∣ v`,
so in degree `2` the images of an idele class are its local Brauer classes in `Br(L_w/K_v)`. The
first statement is the idelic half of the injectivity of `Br(L/K) → ⨁_v Br(L_w/K_v)`; the other
half is the vanishing of `H¹(G, C_L)`.

The proof is Milne's (*Class Field Theory*, VII, Lemma 2.4 and Proposition 2.5). The ideles are the
union of the `S`-ideles over the finite sets `S` of finite places, so every class comes from the
`S`-ideles for a finite `S` that may be taken to contain the places ramified in `L`
(`TauCeti.TateCohomology.exists_tateCohomologyFunctor_map_eq`). The `S`-ideles split as
`I_{L,S} = L_∞ˣ × I_{L,S}^f` (`sIdelesInfiniteShortComplex`), the infinite ideles are the product
of the archimedean semi-local unit groups (`TauCeti.GlobalNumberFields.infiniteIdelesPiIso`), and
the finite `S`-ideles are the product of the semi-local unit groups at `S` and of the integral
semi-local unit groups away from `S` (`TauCeti.finiteSIdelesPiIso`). Tate cohomology commutes with
products (`TauCeti.TateCohomology.linearEquivPi`), and the integral factors, at places unramified
in `L`, have no cohomology in positive degrees
(`isZero_tateCohomology_semilocalIntegralUnitsRep_of_neZero`).

## Main definitions

* `TauCeti.ClassFieldTheory.idelesRep K L`: the ideles of `L` as an integral representation of
  `Aut(L/K)`.
* `TauCeti.ClassFieldTheory.idelesToSemilocalUnits L v`,
  `TauCeti.ClassFieldTheory.idelesToInfiniteSemilocalUnits L w`: the semi-local components of an
  idele at a finite place `v` and at an infinite place `w` of `K`.
* `TauCeti.ClassFieldTheory.sIdelesToIdeles L S`: the inclusion of the `S`-ideles into the
  ideles.

## Main results

* `TauCeti.ClassFieldTheory.eq_zero_of_forall_map_semilocal_eq_zero`: a class of
  `H^n(G, I_L)`, `n > 0`, with vanishing semi-local components is zero.
* `TauCeti.ClassFieldTheory.finite_setOf_map_idelesToSemilocalUnits_ne_zero`: a class of
  `H^n(G, I_L)`, `n > 0`, has nonzero semi-local components at only finitely many finite places.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, Lemma 2.4 and Proposition 2.5.
* J. Tate, *Global class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VII, §§6–7.
-/

public section
noncomputable section

open CategoryTheory Limits IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped AdeleGaloisAction TensorProduct

namespace TauCeti.ClassFieldTheory

open GlobalNumberFields

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]

/-- The ideles of `L`, as an integral representation of `Aut(L/K)`. -/
abbrev idelesRep : Rep ℤ (L ≃ₐ[K] L) :=
  Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (IdeleGroup (𝓞 L) L)

variable {K}

/-! ### The semi-local components of an idele -/

section Components

omit [NumberField K] in
/-- The infinite part of `σ • x` is `σ` applied to the infinite part of `x`. -/
private theorem fst_smul (σ : L ≃ₐ[K] L) (x : IdeleGroup (𝓞 L) L) :
    Units.map (MonoidHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) (σ • x) =
      σ • Units.map (MonoidHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) x :=
  -- both sides have underlying infinite adele the infinite component of `adeleGaloisAction σ x`
  Units.ext <| (congrArg Prod.fst (coe_idele_smul σ x)).trans (adeleGaloisAction_fst K L σ _)

variable (K) in
/-- The infinite part `I_L → L_∞ˣ` of an idele, as a morphism of representations of
`Aut(L/K)`. -/
def idelesToInfiniteIdeles : idelesRep K L ⟶ infiniteIdelesRep K L :=
  Rep.ofHom <| LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (Units.map (MonoidHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))
      ).toAdditive.toIntLinearMap
    fun σ x ↦ congrArg Additive.ofMul (fst_smul L σ x.toMul)

omit [NumberField K] in
/-- `idelesToInfiniteIdeles` takes the infinite part of an idele. -/
@[simp]
theorem idelesToInfiniteIdeles_hom_apply (x : Additive (IdeleGroup (𝓞 L) L)) :
    (idelesToInfiniteIdeles K L).hom x = Additive.ofMul
      (Units.map (MonoidHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) x.toMul) :=
  (rfl)

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
theorem coe_idelesToInfiniteSemilocalUnits_hom_apply (w : InfinitePlace K)
    (x : Additive (IdeleGroup (𝓞 L) L)) :
    (Additive.toMul (α := (w.Completion ⊗[K] L)ˣ) ((idelesToInfiniteSemilocalUnits L w).hom x) :
      w.Completion ⊗[K] L) =
      infiniteAdeleSemilocalHom L w (x.toMul : AdeleRing (𝓞 L) L).1 :=
  -- `idelesToInfiniteSemilocalUnits L w` is by definition the component at `w` of the image of
  -- the infinite part under `infiniteIdelesPiIso`, and the infinite part of `x` has underlying
  -- infinite adele the first component of `x`
  (congrArg (fun z ↦ ((Additive.toMul (α := (w.Completion ⊗[K] L)ˣ) z : _) : w.Completion ⊗[K] L))
    (Rep.piProj_hom_apply _ _)).trans
      (coe_infiniteIdelesPiIso_hom_apply ((idelesToInfiniteIdeles K L).hom x) w)

end Components

/-! ### The `S`-ideles inside the ideles -/

section SIdeles

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- The inclusion `I_{L,S} → I_L` of the `S`-ideles, as a morphism of representations of
`Aut(L/K)`. -/
def sIdelesToIdeles : sIdelesRep (K := K) L S ⟶ idelesRep K L :=
  Rep.ofHom <| LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (sIdeles L (S : Set (HeightOneSpectrum (𝓞 K)))).subtype.toAdditive.toIntLinearMap
    fun _ _ ↦ rfl

/-- `sIdelesToIdeles` sends an `S`-idele to itself. -/
@[simp]
theorem sIdelesToIdeles_hom_apply (x : Additive (sIdeles L (S : Set (HeightOneSpectrum (𝓞 K))))) :
    (sIdelesToIdeles L S).hom x = Additive.ofMul (x.toMul : IdeleGroup (𝓞 L) L) :=
  (rfl)

/-- The inclusion of the `S`-ideles into the ideles is injective. -/
theorem sIdelesToIdeles_hom_injective : Function.Injective (sIdelesToIdeles L S).hom :=
  fun x y h ↦ Additive.toMul.injective <| Subtype.ext <| Additive.ofMul.injective <|
    (sIdelesToIdeles_hom_apply L S x).symm.trans (h.trans (sIdelesToIdeles_hom_apply L S y))

/-- The idele `(1, a)` of a finite `S`-idele `a`, as a morphism of representations, a section of
`sIdelesToFiniteSIdeles`. -/
private def finiteSIdelesToSIdeles : finiteSIdelesRep L S ⟶ sIdelesRep (K := K) L S :=
  Rep.ofHom <| LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (((IdeleGroup.ofFiniteIdele (𝓞 L) L).comp (finiteSIdeles L S).subtype).codRestrict _
      fun a ↦ toFiniteIdele_mem_finiteSIdeles_iff.1 (by simp)).toAdditive.toIntLinearMap
    fun σ a ↦ congrArg Additive.ofMul <| Subtype.ext <|
      ofFiniteIdele_map_finiteAdeleGaloisAction σ a.toMul.1

private theorem finiteSIdelesToSIdeles_hom_apply (a : Additive (finiteSIdeles L S)) :
    (finiteSIdelesToSIdeles L S).hom a = Additive.ofMul
      ⟨IdeleGroup.ofFiniteIdele (𝓞 L) L a.toMul, toFiniteIdele_mem_finiteSIdeles_iff.1 (by simp)⟩ :=
  (rfl)

/-- An `S`-idele is the product of its infinite part and its finite part. -/
private theorem sIdeles_hom_decomp :
    𝟙 (sIdelesRep (K := K) L S) =
      (sIdelesToIdeles L S ≫ idelesToInfiniteIdeles K L) ≫ infiniteIdelesToSIdeles L S +
        sIdelesToFiniteSIdeles L S ≫ finiteSIdelesToSIdeles L S := by
  ext x
  -- the two summands, computed on the `S`-idele `a`
  let a : sIdeles L (S : Set (HeightOneSpectrum (𝓞 K))) := Additive.toMul x
  have h₁ : (infiniteIdelesToSIdeles L S).hom
      ((idelesToInfiniteIdeles K L).hom ((sIdelesToIdeles L S).hom x)) =
      Additive.ofMul ⟨IdeleGroup.ofInfiniteIdele (𝓞 L) L
        (Units.map (MonoidHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) a.1),
        ofInfiniteIdele_mem_sIdeles _ _⟩ :=
    infiniteIdelesToSIdeles_hom_apply L S _
  have hb : IdeleGroup.toFiniteIdele (𝓞 L) L
      (IdeleGroup.ofFiniteIdele (𝓞 L) L (IdeleGroup.toFiniteIdele (𝓞 L) L a.1)) ∈
        finiteSIdeles L S := by
    rw [IdeleGroup.toFiniteIdele_ofFiniteIdele]
    exact toFiniteIdele_mem_finiteSIdeles_iff.2 a.2
  have h₂ : (finiteSIdelesToSIdeles L S).hom ((sIdelesToFiniteSIdeles L S).hom x) =
      Additive.ofMul ⟨IdeleGroup.ofFiniteIdele (𝓞 L) L (IdeleGroup.toFiniteIdele (𝓞 L) L a.1),
        toFiniteIdele_mem_finiteSIdeles_iff.1 hb⟩ :=
    (congrArg _ (sIdelesToFiniteSIdeles_hom_apply L S x)).trans
      (finiteSIdelesToSIdeles_hom_apply L S _)
  -- multiplicatively, `a = (a_∞, 1) * (1, a_f)`
  have ha : a = ⟨IdeleGroup.ofInfiniteIdele (𝓞 L) L
        (Units.map (MonoidHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) a.1),
        ofInfiniteIdele_mem_sIdeles _ _⟩ *
      ⟨IdeleGroup.ofFiniteIdele (𝓞 L) L (IdeleGroup.toFiniteIdele (𝓞 L) L a.1),
        toFiniteIdele_mem_finiteSIdeles_iff.1 hb⟩ := by
    refine Subtype.ext (Units.ext (Prod.ext ?_ ?_))
    -- the product of adeles is computed componentwise, and the infinite part of `a` has
    -- underlying infinite adele the first component of `a`
    · simp only [Subgroup.coe_mul, Units.val_mul, IdeleGroup.coe_ofInfiniteIdele,
        IdeleGroup.coe_ofFiniteIdele, IdeleGroup.coe_toFiniteIdele]
      exact (mul_one _).symm
    · simp only [Subgroup.coe_mul, Units.val_mul, IdeleGroup.coe_ofInfiniteIdele,
        IdeleGroup.coe_ofFiniteIdele, IdeleGroup.coe_toFiniteIdele]
      exact (one_mul _).symm
  exact (congrArg Additive.ofMul ha).trans (congrArg₂ (· + ·) h₁ h₂).symm

/-- At a place `v ∈ S`, the semi-local component of an `S`-idele is read off its finite part
through `finiteSIdelesPiIso`. -/
private theorem sIdelesToFiniteSIdeles_comp_piProj_inl (v : S) :
    sIdelesToFiniteSIdeles L S ≫ (finiteSIdelesPiIso L S).hom ≫ Rep.piProj _ (Sum.inl v) =
      sIdelesToIdeles L S ≫ idelesToSemilocalUnits L v.1 := by
  ext x
  -- the composite on the left takes the semi-local component at `v` of the finite part
  exact (Rep.piProj_hom_apply _ _).trans <|
    (congrArg (fun z ↦ (finiteSIdelesPiIso L S).hom.hom z (Sum.inl v))
      (sIdelesToFiniteSIdeles_hom_apply L S x)).trans
        (finiteSIdelesPiIso_hom_apply_inl L S _ v)

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
      sIdelesToIdeles L S ≫ idelesToSemilocalUnits L v := by
  ext x
  -- both send an `S`-idele to the semi-local component at `v` of its finite part
  exact semilocalIntegralUnitsIncl_apply v _

end SIdeles

/-! ### The cohomology of the ideles -/

section Cohomology

variable [IsGalois K L]

variable (K) in
/-- The finite places of `K` below a place of `L` ramified over `K`. -/
private def ramifiedPlaces : Finset (HeightOneSpectrum (𝓞 K)) :=
  ((Ideal.finite_factors (differentIdeal_ne_bot (A := 𝓞 K) (B := 𝓞 L))).image
    (HeightOneSpectrum.under (𝓞 K))).toFinset

/-- At a finite place of `K` outside a set containing the ramified places, the integral
semi-local units have no cohomology in positive degrees. -/
private theorem isZero_tateCohomology_semilocalIntegralUnitsRep_of_notMem
    {S : Finset (HeightOneSpectrum (𝓞 K))} (hS : ramifiedPlaces K L ⊆ S)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) (n : ℕ) [NeZero n] :
    IsZero (tateCohomology (semilocalIntegralUnitsRep L v) n) := by
  obtain ⟨w, rfl⟩ := under_surjective (𝓞 K) (𝓞 L) v
  have : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := not_dvd_differentIdeal_iff.1 fun h ↦
    hv (hS ((Set.Finite.mem_toFinset _).2 ⟨w, h, rfl⟩))
  exact isZero_tateCohomology_semilocalIntegralUnitsRep_of_neZero (w.under (𝓞 K)) w n

omit [IsGalois K L] in
/-- Every class of `H^n(G, I_L)` comes from the `S`-ideles for a finite set `S` of finite places
containing the ramified ones. -/
private theorem exists_map_sIdelesToIdeles_eq (n : ℤ) (x : tateCohomology (idelesRep K L) n) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ramifiedPlaces K L ⊆ S ∧
      ∃ y, ((tateCohomologyFunctor n).map (sIdelesToIdeles L S)).hom y = x := by
  classical
  -- a finite set of ideles lies in the `S`-ideles for the union of the sets that work for each
  have hcover (s : Finset (idelesRep K L)) : ∃ S : {S : Finset (HeightOneSpectrum (𝓞 K)) //
      ramifiedPlaces K L ⊆ S}, ∀ x ∈ s, x ∈ Set.range (sIdelesToIdeles L S.1).hom := by
    choose S hRS hS using fun x : idelesRep K L ↦
      exists_finset_mem_sIdeles (ramifiedPlaces K L) (Additive.toMul x : IdeleGroup (𝓞 L) L)
    refine ⟨⟨ramifiedPlaces K L ∪ s.sup S, Finset.subset_union_left⟩, fun x hx ↦
      ⟨Additive.ofMul ⟨Additive.toMul x, sIdeles_mono ?_ (hS x)⟩, rfl⟩⟩
    exact Finset.coe_subset.2 ((Finset.le_sup hx).trans Finset.subset_union_right)
  obtain ⟨⟨S, hS⟩, y, hy⟩ := TateCohomology.exists_tateCohomologyFunctor_map_eq
    (fun S : {S : Finset (HeightOneSpectrum (𝓞 K)) // ramifiedPlaces K L ⊆ S} ↦
      sIdelesToIdeles L S.1) (fun S ↦ sIdelesToIdeles_hom_injective L S.1) hcover n x
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
  -- read off the vanishing components of `y`
  have hy {Y : Rep ℤ (L ≃ₐ[K] L)} (f : sIdelesRep (K := K) L S ⟶ Y) (g : idelesRep K L ⟶ Y)
      (hfg : f = sIdelesToIdeles L S ≫ g)
      (hg : ((tateCohomologyFunctor n).map g).hom
        (((tateCohomologyFunctor n).map (sIdelesToIdeles L S)).hom y) = 0) :
      ((tateCohomologyFunctor n).map f).hom y = 0 := by
    rwa [hfg, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  -- the finite part of `y` vanishes: its components at `S` are those of `x`, and the factors
  -- away from `S` have no cohomology
  have hfin' : ((tateCohomologyFunctor n).map (sIdelesToFiniteSIdeles L S)).hom y = 0 := by
    suffices ((tateCohomologyFunctor n).map
        (sIdelesToFiniteSIdeles L S ≫ (finiteSIdelesPiIso L S).hom)).hom y = 0 by
      rw [← Category.comp_id (sIdelesToFiniteSIdeles L S), ← (finiteSIdelesPiIso L S).hom_inv_id,
        ← Category.assoc, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, this,
        map_zero]
    refine (TateCohomology.linearEquivPi _ n).injective (funext fun i ↦ ?_)
    rw [TateCohomology.linearEquivPi_apply, map_zero, Pi.zero_apply, ← LinearMap.comp_apply,
      ← ModuleCat.hom_comp, ← Functor.map_comp, Category.assoc]
    rcases i with v | v
    · exact hy _ _ (sIdelesToFiniteSIdeles_comp_piProj_inl L S v) (hfin v)
    · exact (ModuleCat.subsingleton_of_isZero
        (isZero_tateCohomology_semilocalIntegralUnitsRep_of_notMem L hS v.2 n)).elim _ _
  -- the infinite part of `y` vanishes: its components are those of `x`
  have hinf' : ((tateCohomologyFunctor n).map
      (sIdelesToIdeles L S ≫ idelesToInfiniteIdeles K L)).hom y = 0 := by
    suffices ((tateCohomologyFunctor n).map
        ((sIdelesToIdeles L S ≫ idelesToInfiniteIdeles K L) ≫ (infiniteIdelesPiIso K L).hom)).hom
          y = 0 by
      rw [← Category.comp_id (sIdelesToIdeles L S ≫ idelesToInfiniteIdeles K L),
        ← (infiniteIdelesPiIso K L).hom_inv_id, ← Category.assoc, Functor.map_comp,
        ModuleCat.hom_comp, LinearMap.comp_apply, this, map_zero]
    refine (TateCohomology.linearEquivPi _ n).injective (funext fun w ↦ ?_)
    rw [TateCohomology.linearEquivPi_apply, map_zero, Pi.zero_apply, ← LinearMap.comp_apply,
      ← ModuleCat.hom_comp, ← Functor.map_comp]
    exact hy _ _ (by simp only [idelesToInfiniteSemilocalUnits, Category.assoc]) (hinf w)
  -- an `S`-idele is the product of its infinite part and its finite part
  have hy0 : y = 0 := by
    calc y = ((tateCohomologyFunctor n).map (𝟙 _)).hom y := by
          rw [CategoryTheory.Functor.map_id, ModuleCat.hom_id, LinearMap.id_apply]
      _ = 0 := by
          rw [sIdeles_hom_decomp, Functor.map_add, ModuleCat.hom_add, LinearMap.add_apply,
            Functor.map_comp (tateCohomologyFunctor n) (sIdelesToIdeles L S ≫ _),
            Functor.map_comp (tateCohomologyFunctor n) (sIdelesToFiniteSIdeles L S),
            ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
            hinf', hfin', map_zero, map_zero, add_zero]
  rw [hy0, map_zero]

/-- **The semi-local components of an idele class are finitely supported.** For a finite Galois
extension `L/K` of number fields and `n > 0`, a class of `H^n(Gal(L/K), I_L)` has nonzero image in
`H^n(Gal(L/K), (K_v ⊗[K] L)ˣ)` at only finitely many finite places `v` of `K`. -/
theorem finite_setOf_map_idelesToSemilocalUnits_ne_zero (x : tateCohomology (idelesRep K L) n) :
    {v | ((tateCohomologyFunctor n).map (idelesToSemilocalUnits L v)).hom x ≠ 0}.Finite := by
  obtain ⟨S, hS, y, rfl⟩ := exists_map_sIdelesToIdeles_eq L n x
  refine S.finite_toSet.subset fun v hv ↦ ?_
  by_contra hvS
  refine hv ?_
  -- the image factors through the integral semi-local units, which have no cohomology
  have := ModuleCat.subsingleton_of_isZero
    (isZero_tateCohomology_semilocalIntegralUnitsRep_of_notMem L hS hvS n)
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← Functor.map_comp,
    ← sIdelesToSemilocalIntegralUnits_comp_incl L S v hvS, Functor.map_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply, Subsingleton.elim (((tateCohomologyFunctor n).map
      (sIdelesToSemilocalIntegralUnits L S v hvS)).hom y) 0, map_zero]

end Cohomology

end TauCeti.ClassFieldTheory
