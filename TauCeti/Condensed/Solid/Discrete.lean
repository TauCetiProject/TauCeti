/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Condensed.Discrete.Characterization
public import TauCeti.Condensed.Free
public import TauCeti.Condensed.Solid
public import TauCeti.Condensed.Solid.Free
import TauCeti.Topology.LocallyConstant.Compact

/-!
# Discrete condensed modules are solid

Let `R` be a ring and `M` an `R`-module. This file proves that the discrete condensed `R`-module
on `M` is solid (`ModuleCat.isSolid_discrete`), and deduces that the free solid module
`R[S]^solid` on a profinite set `S` is solid (`Condensed.isSolid_profiniteSolid`): it is a product
of copies of the discrete module `R`, and solid modules are closed under limits. In particular
`ℤ[S]^solid` is a solid condensed abelian group.

The key input is a condensed form of Specker's theorem
(`TauCeti.locallyConstantIntDual_exists_finset_hom_app_eq_zero`). Write `R[S]^solid` as the module
`T ↦ Hom_ℤ(C(S, ℤ), C(T, R))` of measures (`TauCeti.locallyConstantIntDual`). Every morphism from
it to a discrete module vanishes on the measures that vanish on some finite set of locally constant
functions. To see this, choose a `ℤ`-basis `(b i)` of `C(S, ℤ)`, so that measures are families of
coordinates indexed by `I`. Evaluating the morphism on a family of coordinates switched on and off
by the points of the Cantor cube `I → Bool` gives a locally constant function on that compact
product; it depends on finitely many coordinates only (`IsLocallyConstant.exists_finset_dependsOn`).

Solidity then follows. A morphism `R[S]^solid ⟶ M` that vanishes on `R[S]` vanishes: the
condensed Specker theorem factors it through the pushforward of measures to a finite quotient `F`
of `S`, where the solidification map `R[F] ⟶ R[F]^solid` is an isomorphism and `R[S] ⟶ R[F]` is
split surjective. Conversely, a morphism `R[S] ⟶ M` is a locally constant function `S → M`
(`Profinite.freeModuleHomEquiv`), which factors through a finite quotient, and so extends to
`R[S]^solid`.

## Main results

* `TauCeti.locallyConstantIntDual_exists_finset_hom_app_eq_zero`: a morphism from the measures on
  `S` to a discrete module vanishes on the measures that vanish on a finite set of locally constant
  functions.
* `ModuleCat.isSolid_locallyConstant`, `ModuleCat.isSolid_discrete`,
  `CondensedMod.isSolid_of_isDiscrete`: discrete condensed modules are solid.
* `Condensed.isSolid_profiniteSolid`: the free solid module `R[S]^solid` is solid.

## References

* D. Clausen and P. Scholze, *Lectures on condensed mathematics*, Lecture V: Corollary 5.5 and
  Proposition 5.7, and the proof of Theorem 5.8.
-/

public section

universe u

open CategoryTheory Limits Opposite Condensed

namespace TauCeti

variable {R : Type (u + 1)} [Ring R] {S : Profinite.{u}} {M : ModuleCat.{u + 1} R}

section Specker

/-- The component over `T` of a morphism from the measures on `S` to the discrete module `M`, as a
linear map `Hom(C(S, ℤ), C(T, R)) → C(T, M)`. -/
private noncomputable def homApp
    (g : locallyConstantIntDual R S ⟶ (CondensedMod.LocallyConstant.functor R).obj M)
    (T : CompHaus.{u}) :
    (LocallyConstant S ℤ →+ LocallyConstant T R) →ₗ[R] LocallyConstant T M :=
  (g.hom.app (op T)).hom

/-- The value at `t : T` of the component over `T` is the component over the point applied to the
measure restricted to `t`. -/
private theorem homApp_apply_apply
    (g : locallyConstantIntDual R S ⟶ (CondensedMod.LocallyConstant.functor R).obj M)
    {T : CompHaus.{u}} (μ : LocallyConstant S ℤ →+ LocallyConstant T R) (t : T) :
    homApp g T μ t = homApp g (CompHaus.of PUnit.{u + 1})
        ((LocallyConstant.comapAddMonoidHom (ContinuousMap.const _ t)).comp μ) PUnit.unit :=
  (congrArg (fun f : LocallyConstant _ M ↦ f PUnit.unit) (CondensedMod.hom_naturality_apply R g
    (CompHausLike.const (CompHaus.of PUnit.{u + 1}) t).op μ)).symm

variable {I : Type u} (b : Module.Basis I ℤ (LocallyConstant S ℤ))

/-- The coordinates of a measure in the `ℤ`-basis `b` of `C(S, ℤ)`. -/
private noncomputable def coord (T : CompHaus.{u}) :
    (LocallyConstant S ℤ →+ LocallyConstant T R) ≃ₗ[R] (I → LocallyConstant T R) :=
  addMonoidHomLequivInt R ≪≫ₗ (b.constr R).symm

private theorem coord_apply (T : CompHaus.{u}) (μ : LocallyConstant S ℤ →+ LocallyConstant T R)
    (i : I) : coord b T μ i = μ (b i) := by
  simp [coord]

/-- A morphism from the measures on `S` to the discrete module `M`, over the point and in the
coordinates given by the basis `b`. -/
private noncomputable def pointMap
    (g : locallyConstantIntDual R S ⟶ (CondensedMod.LocallyConstant.functor R).obj M) :
    (I → LocallyConstant (CompHaus.of PUnit.{u + 1}) R) →ₗ[R] M :=
  LocallyConstant.evalₗ R PUnit.unit ∘ₗ homApp g (CompHaus.of PUnit.{u + 1}) ∘ₗ
    (coord (R := R) b (CompHaus.of PUnit.{u + 1})).symm.toLinearMap

private theorem pointMap_apply
    (g : locallyConstantIntDual R S ⟶ (CondensedMod.LocallyConstant.functor R).obj M)
    (x : I → LocallyConstant (CompHaus.of PUnit.{u + 1}) R) :
    pointMap b g x = homApp g _ ((coord b _).symm x) PUnit.unit :=
  rfl

/-- For coordinates `c`, the value of `pointMap b g` on the coordinates of `c` switched on by
`t : I → Bool` depends on only finitely many values of `t`. -/
private theorem exists_finset_pointMap_eq
    (g : locallyConstantIntDual R S ⟶ (CondensedMod.LocallyConstant.functor R).obj M)
    (c : I → R) :
    ∃ s : Finset I, ∀ t t' : I → Bool, (∀ i ∈ s, t i = t' i) →
      pointMap b g (fun i ↦ .const _ (if t i then c i else 0)) =
        pointMap b g (fun i ↦ .const _ (if t' i then c i else 0)) := by
  -- The measure over the Cantor cube `I → Bool` whose restriction to `t` has the coordinates of
  -- `c` switched on by `t`.
  let T := CompHaus.of (I → Bool)
  let μ : LocallyConstant S ℤ →+ LocallyConstant T R := (coord b T).symm fun i ↦
    LocallyConstant.comap (ContinuousMap.eval i)
      ⟨fun x : Bool ↦ if x then c i else 0, IsLocallyConstant.of_discrete _⟩
  obtain ⟨s, hs⟩ :=
    (homApp g T μ).isLocallyConstant.exists_finset_dependsOn (π := fun _ : I ↦ Bool)
  have key (t : I → Bool) :
      pointMap b g (fun i ↦ .const _ (if t i then c i else 0)) = homApp g T μ t := by
    rw [homApp_apply_apply, pointMap_apply]
    congr 2
    rw [LinearEquiv.symm_apply_eq]
    funext i
    rw [coord_apply, AddMonoidHom.comp_apply, ← coord_apply b, LinearEquiv.apply_symm_apply]
    ext ⟨⟩
    rfl
  exact ⟨s, fun t t' htt' ↦ (key t).trans ((hs htt').trans (key t').symm)⟩

/-- If `pointMap b g` on the all-one coordinates switched on by `t` depends only on the values of
`t` on `s`, then `pointMap b g` vanishes on every single coordinate outside `s`. -/
private theorem pointMap_single_eq_zero [DecidableEq I]
    {g : locallyConstantIntDual R S ⟶ (CondensedMod.LocallyConstant.functor R).obj M}
    {s : Finset I} (hs : ∀ t t' : I → Bool, (∀ i ∈ s, t i = t' i) →
      pointMap b g (fun i ↦ .const _ (if t i then (1 : I → R) i else 0)) =
        pointMap b g (fun i ↦ .const _ (if t' i then (1 : I → R) i else 0)))
    {i : I} (hi : i ∉ s) (r : LocallyConstant (CompHaus.of PUnit.{u + 1}) R) :
    pointMap b g (Pi.single i r) = 0 := by
  -- First on the basis vector, comparing the indicator of `i` with zero, then by linearity.
  have h1 : pointMap b g (Pi.single i 1) = 0 := by
    have h := hs (fun k ↦ decide (k = i)) (fun _ ↦ false)
      (fun k hk ↦ by simp [ne_of_mem_of_not_mem hk hi])
    have e1 : (fun k ↦ LocallyConstant.const (CompHaus.of PUnit.{u + 1})
        (if decide (k = i) then (1 : I → R) k else 0)) = Pi.single i 1 := by
      funext k
      ext ⟨⟩
      by_cases hk : k = i <;> simp [hk]
    have e2 : (fun k ↦ LocallyConstant.const (CompHaus.of PUnit.{u + 1})
        (if (fun _ ↦ false) k then (1 : I → R) k else 0)) = 0 := by
      funext k
      ext ⟨⟩
      simp
    rwa [e1, e2, map_zero] at h
  have hr : Pi.single i r =
      r PUnit.unit • (Pi.single i 1 : I → LocallyConstant (CompHaus.of PUnit.{u + 1}) R) := by
    funext k
    ext ⟨⟩
    by_cases hk : k = i <;> simp [hk]
  rw [hr, map_smul, h1, smul_zero]

/-- `pointMap b g` vanishes on the coordinates that vanish on some finite set. -/
private theorem exists_finset_pointMap_eq_zero
    (g : locallyConstantIntDual R S ⟶ (CondensedMod.LocallyConstant.functor R).obj M) :
    ∃ s : Finset I, ∀ x : I → LocallyConstant (CompHaus.of PUnit.{u + 1}) R,
      (∀ i ∈ s, x i = 0) → pointMap b g x = 0 := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_pointMap_eq b g 1
  refine ⟨s, fun x hx ↦ ?_⟩
  -- Switching off the coordinates of `x` outside a large enough finite set does not change the
  -- value, and what remains is a finite sum of single coordinates.
  obtain ⟨s', hs'⟩ := exists_finset_pointMap_eq b g fun i ↦ x i PUnit.unit
  have hx' : x = fun i ↦ LocallyConstant.const (CompHaus.of PUnit.{u + 1})
      (if (fun _ ↦ true) i then x i PUnit.unit else 0) := by
    funext i
    ext ⟨⟩
    rfl
  have hsum : (fun i ↦ LocallyConstant.const (CompHaus.of PUnit.{u + 1})
      (if decide (i ∈ s' ∪ s) then x i PUnit.unit else 0)) = ∑ k ∈ s' ∪ s, Pi.single k (x k) := by
    funext i
    ext ⟨⟩
    by_cases hi : i ∈ s' ∪ s <;> simp [hi, Finset.sum_apply, Pi.single_apply]
  rw [hx', ← hs' (fun k ↦ decide (k ∈ s' ∪ s)) _ (fun k hk ↦ by simp [hk]), hsum, map_sum]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  by_cases hk : k ∈ s
  · simp [hx k hk]
  · exact pointMap_single_eq_zero b hs hk _

/-- A morphism from the measures on `S` to a discrete module vanishes on the measures that vanish
on finitely many vectors of the basis `b`. -/
private theorem exists_finset_homApp_eq_zero
    (g : locallyConstantIntDual R S ⟶ (CondensedMod.LocallyConstant.functor R).obj M) :
    ∃ s : Finset I, ∀ (T : CompHaus.{u}) (μ : LocallyConstant S ℤ →+ LocallyConstant T R),
      (∀ i ∈ s, μ (b i) = 0) → homApp g T μ = 0 := by
  obtain ⟨s, hs⟩ := exists_finset_pointMap_eq_zero b g
  refine ⟨s, fun T μ hμ ↦ ?_⟩
  ext t
  have h := hs (coord b _ ((LocallyConstant.comapAddMonoidHom (ContinuousMap.const _ t)).comp μ))
    fun i hi ↦ by rw [coord_apply, AddMonoidHom.comp_apply, hμ i hi, map_zero]
  rwa [pointMap_apply, LinearEquiv.symm_apply_apply, ← homApp_apply_apply] at h

end Specker

/-- A condensed form of Specker's theorem: a morphism from the condensed module of `R`-valued
measures on a profinite set `S` to a discrete condensed module vanishes on the measures that vanish
on a finite set of locally constant functions `S → ℤ`. Equivalently, every morphism from
`R[S]^solid = ∏ R` to a discrete module `M` factors through finitely many coordinates. -/
theorem locallyConstantIntDual_exists_finset_hom_app_eq_zero
    (g : locallyConstantIntDual R S ⟶ (CondensedMod.LocallyConstant.functor R).obj M) :
    ∃ s : Finset (LocallyConstant S ℤ), ∀ (T : CompHaus.{u})
      (μ : LocallyConstant S ℤ →+ LocallyConstant T R), (∀ f ∈ s, μ f = 0) →
        g.hom.app (op T) μ = 0 := by
  classical
  have := LocallyConstant.freeOfProfinite S
  obtain ⟨s, hs⟩ := exists_finset_homApp_eq_zero (Module.Free.chooseBasis ℤ (LocallyConstant S ℤ)) g
  exact ⟨s.image (Module.Free.chooseBasis ℤ _), fun T μ hμ ↦
    hs T μ fun i hi ↦ hμ _ (Finset.mem_image_of_mem _ hi)⟩

attribute [local instance] discreteTopology_toProfinite_obj

/-- A morphism from the measures on `S` to a discrete condensed module factors through the
pushforward of measures `locallyConstantIntDualMap R j.hom` along a surjection `j` from `S` onto a
finite set: it is that pushforward followed by the pushforward along a section `sec` of `j` and the
morphism itself. -/
private theorem exists_eq_locallyConstantIntDualMap_comp
    (g : locallyConstantIntDual R S ⟶ (CondensedMod.LocallyConstant.functor R).obj M) :
    ∃ (j : StructuredArrow S FintypeCat.toProfinite) (sec : FintypeCat.toProfinite.obj j.right ⟶ S),
      sec ≫ j.hom = 𝟙 _ ∧
        g = locallyConstantIntDualMap R j.hom ≫ locallyConstantIntDualMap R sec ≫ g := by
  obtain ⟨s, hs⟩ := locallyConstantIntDual_exists_finset_hom_app_eq_zero g
  obtain ⟨j, hj, hjs⟩ := S.exists_structuredArrow_surjective_forall_comap_eq s
  let F := FintypeCat.toProfinite.obj j.right
  let sec : F ⟶ S :=
    ConcreteCategory.ofHom (⟨Function.surjInv hj, continuous_of_discreteTopology⟩ : C(F, S))
  have hsec (φ : LocallyConstant F ℤ) :
      LocallyConstant.comap sec.hom.hom (LocallyConstant.comap j.hom.hom.hom φ) = φ := by
    ext x
    exact congrArg φ (Function.surjInv_eq hj x)
  have hs' : ∀ (T : CompHaus.{u}) (μ : LocallyConstant S ℤ →+ LocallyConstant T R),
      (∀ f ∈ s, μ f = 0) → homApp g T μ = 0 := hs
  -- Pushing a measure forward to `F` and back along `sec` does not change its values on `s`.
  have key (T : CompHaus.{u}) (μ : LocallyConstant S ℤ →+ LocallyConstant T R) :
      homApp g T μ = homApp g T ((locallyConstantIntDualMap R sec).hom.app (op T)
        ((locallyConstantIntDualMap R j.hom).hom.app (op T) μ)) := by
    rw [locallyConstantIntDualMap_hom_app_apply, locallyConstantIntDualMap_hom_app_apply,
      ← sub_eq_zero, ← map_sub]
    refine hs' T _ fun f hf ↦ ?_
    obtain ⟨φ, rfl⟩ := hjs f hf
    simp [hsec]
  refine ⟨j, sec, ?_, ?_⟩
  · ext x
    exact Function.surjInv_eq hj x
  · ext T μ : 4
    exact key T.unop μ

/-- A morphism from `R[S]^solid` to a discrete condensed module vanishes if it vanishes after
precomposition with the solidification map `R[S] ⟶ R[S]^solid`. -/
private theorem eq_zero_of_profiniteSolidification_comp_eq_zero
    (h : (profiniteSolid R).obj S ⟶ (CondensedMod.LocallyConstant.functor R).obj M)
    (hh : (profiniteSolidification R).app S ≫ h = 0) : h = 0 := by
  let e := profiniteSolidIsoLocallyConstantIntDual R S
  obtain ⟨j, sec, hsj, hg⟩ := exists_eq_locallyConstantIntDualMap_comp (e.inv ≫ h)
  let F := FintypeCat.toProfinite.obj j.right
  -- On the finite set `F` solidification is an isomorphism, and `R[S] ⟶ R[F]` is split
  -- surjective, so the factor through the measures on `F` vanishes.
  have : IsSplitEpi ((profiniteFree R).map j.hom) :=
    ⟨⟨(profiniteFree R).map sec, by rw [← Functor.map_comp, hsj, CategoryTheory.Functor.map_id]⟩⟩
  have h0 : locallyConstantIntDualMap R sec ≫ e.inv ≫ h = 0 := by
    have h1 : (profiniteFree R).map j.hom ≫ (profiniteSolidification R).app F ≫
        (profiniteSolidIsoLocallyConstantIntDual R F).hom ≫ locallyConstantIntDualMap R sec ≫
          e.inv ≫ h = 0 := by
      rw [NatTrans.naturality_assoc, profiniteSolidIsoLocallyConstantIntDual_hom_naturality_assoc,
        ← hg]
      simpa [e] using hh
    rwa [← comp_zero (f := (profiniteFree R).map j.hom), cancel_epi, ← comp_zero
      (f := (profiniteSolidification R).app F), cancel_epi, ← comp_zero
      (f := (profiniteSolidIsoLocallyConstantIntDual R F).hom), cancel_epi] at h1
  have h2 : e.inv ≫ h = 0 := by rw [hg, h0, comp_zero]
  simpa [e] using congrArg (e.hom ≫ ·) h2

/-- Every morphism from `R[S]` to a discrete condensed module extends along the solidification
map `R[S] ⟶ R[S]^solid`. -/
private theorem exists_profiniteSolidification_comp_eq
    (g : (profiniteFree R).obj S ⟶ (CondensedMod.LocallyConstant.functor R).obj M) :
    ∃ h, (profiniteSolidification R).app S ≫ h = g := by
  -- The section of `M` over `S` corresponding to `g` is pulled back from a finite set `F`, so `g`
  -- factors through `R[S] ⟶ R[F]`, and on `F` solidification is an isomorphism.
  obtain ⟨j, φ, hφ⟩ := S.exists_structuredArrow_comap_eq
    (S.freeModuleHomEquiv g : LocallyConstant S M)
  let F := FintypeCat.toProfinite.obj j.right
  refine ⟨(profiniteSolid R).map j.hom ≫ inv ((profiniteSolidification R).app F) ≫
    F.freeModuleHomEquiv.symm φ, ?_⟩
  rw [← NatTrans.naturality_assoc, IsIso.hom_inv_id_assoc]
  apply S.freeModuleHomEquiv.injective
  rw [Functor.comp_map, Profinite.freeModuleHomEquiv_comp]
  exact (congrArg (ConcreteCategory.hom (((CondensedMod.LocallyConstant.functor R).obj M).obj.map
    (profiniteToCompHaus.map j.hom).op)) (Equiv.apply_symm_apply _ φ)).trans hφ

end TauCeti

namespace ModuleCat

open TauCeti

variable {R : Type (u + 1)} [Ring R]

/-- The condensed module of locally constant functions to an `R`-module `M` is solid. -/
instance isSolid_locallyConstant (M : ModuleCat.{u + 1} R) :
    CondensedMod.IsSolid R ((CondensedMod.LocallyConstant.functor R).obj M) :=
  (CondensedMod.isSolid_iff_bijective _).2 fun _ ↦
    ⟨fun _ _ h ↦ sub_eq_zero.1 (eq_zero_of_profiniteSolidification_comp_eq_zero _
      (by rw [Preadditive.comp_sub]; exact sub_eq_zero.2 h)),
     fun g ↦ exists_profiniteSolidification_comp_eq g⟩

/-- The discrete condensed module on an `R`-module `M` is solid. -/
instance isSolid_discrete (M : ModuleCat.{u + 1} R) :
    CondensedMod.IsSolid R ((discrete (ModuleCat R)).obj M) :=
  ObjectProperty.prop_of_iso _ ((CondensedMod.LocallyConstant.functorIsoDiscrete R).app M)
    (isSolid_locallyConstant M)

end ModuleCat

namespace CondensedMod

variable {R : Type (u + 1)} [Ring R]

/-- A discrete condensed module is solid. -/
theorem isSolid_of_isDiscrete (A : CondensedMod.{u} R) [Condensed.IsDiscrete A] : A.IsSolid := by
  obtain ⟨M, ⟨e⟩⟩ := Sheaf.IsConstant.mem_essImage (J := coherentTopology CompHaus) (F := A)
  exact ObjectProperty.prop_of_iso _ e (ModuleCat.isSolid_discrete M)

end CondensedMod

namespace Condensed

variable (R : Type (u + 1)) [Ring R]

/-- The free solid module `R[S]^solid` on a profinite set `S` is solid: it is a product of copies
of the discrete module `R`, which is solid. -/
instance isSolid_profiniteSolid (S : Profinite.{u}) : ((profiniteSolid R).obj S).IsSolid := by
  have := LocallyConstant.freeOfProfinite S
  let b := Module.Free.chooseBasis ℤ (LocallyConstant S ℤ)
  have : (TauCeti.locallyConstantIntDualFan (R := R) b).pt.IsSolid :=
    ObjectProperty.prop_of_isLimit _ (TauCeti.isLimitLocallyConstantIntDualFan b) fun _ ↦
      ModuleCat.isSolid_locallyConstant _
  rw [TauCeti.locallyConstantIntDualFan_pt] at this
  exact ObjectProperty.prop_of_iso _ (TauCeti.profiniteSolidIsoLocallyConstantIntDual R S).symm this

end Condensed
