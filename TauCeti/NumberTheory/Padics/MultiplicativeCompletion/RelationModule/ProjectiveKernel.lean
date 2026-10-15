/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.Cohomology
public import TauCeti.NumberTheory.Padics.GroupAlgebra.RelationModule
import TauCeti.LinearAlgebra.FreeModule.PID
import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.Rational
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.RepresentationTheory.Homological.GroupCohomology.Corestriction
import TauCeti.RepresentationTheory.Homological.TateCohomology.Projective.Kernel
import TauCeti.RepresentationTheory.Homological.TateCohomology.RelationModule

/-!
# Relation-module surjections onto `A(L)` that are onto on `H²`

Let `L/K` be a finite Galois extension of `p`-adic fields with group `G = Gal(L/K)`, let
`A(L) = lim_m Lˣ/(Lˣ)^(p^m)` be the `p`-adic completion of `Lˣ`, and let `R` be the relation module
over `ℤ_p` of a family `g` generating `G`. If a surjection `β : R → A(L)` of `ℤ_p[G]`-modules is
onto on `H²(G, -)`, then its kernel is a projective `ℤ_p[G]`-module; if moreover `g` has
`[K : ℚ_p] + 2` members, the kernel is free of rank one.

On every `p`-subgroup `S` of `G` both modules have the low-degree cohomology of a class module:
`H¹(S, A(L)) = 0` and `H²(S, A(L))` has order `#S` (NSW (3.6.4), read through local reciprocity),
while `H-hat^3(S, R) = 0` and `H-hat^2(S, R) ≅ ℤ_p ⧸ #S` by the dimension shift along Lyndon's
sequence. Some class of `A(L)` restricts to a generator of `H²(S, A(L))` on every subgroup, so a
map onto `H²(G, A(L))` is onto `H²(S, A(L))`, and then bijective by counting. On `ℓ`-subgroups
for `ℓ ≠ p` all positive-degree cohomology of `ℤ_p`-modules vanishes. Tate's isomorphism criterion
and the theorem of Nakayama and Rim then make the kernel of `β` projective
(`TauCeti.TateCohomology.projective_X₁_of_forall_isPGroup`). For `[K : ℚ_p] + 2` generators the
rational dimension count and Swan's theorem identify it with `ℤ_p[G]`
(`TauCeti.nonempty_ker_linearEquiv_of_relationModule_surjective`).

This is a converse of `TauCeti.groupCohomology.isIso_map_of_surjective_of_projective_ker`. It
identifies the kernel from degree-two information alone, the form in which a relation-module
surjection `R^ab(p) ↠ A(L)` induced by a free presentation of the absolute Galois group of `K` is
controlled, through its effect on extension classes.

## Main statements

* `TauCeti.projective_ker_of_relationModule_surjective_of_h2_surjective`: a surjection from the
  relation module onto `A(L)` which is onto on `H²` has projective kernel.
* `TauCeti.nonempty_ker_linearEquiv_of_relationModule_surjective_of_h2_surjective`: for a
  generating family with `[K : ℚ_p] + 2` members, that kernel is isomorphic to `ℤ_p[G]`.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.1.4),
  (3.6.4), (5.6.6) and the proof of (7.4.2).
* J.-P. Serre, *Local Fields*, Chapter IX, §§5–6.
-/

public section

open CategoryTheory Limits

namespace TauCeti

open _root_.Rep

variable (p : ℕ) [Fact p.Prime]

section LocalField

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [CharZero L]
  [Algebra ℚ_[p] K] [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] K L] [Module.Finite ℚ_[p] L]
  [ValuativeExtension ℚ_[p] L]

/-- A map from the relation module to `A(L)` which is onto on `H²(G, -)` is bijective on
`H-hat^2(S, -)` for every `p`-subgroup `S`: a class of `A(L)` restricting to a generator on every
subgroup lies in its image, and both groups have `#S` elements. -/
private theorem bijective_tateCohomology_two_res_of_surjective {ι : Type} [Fintype ι]
    {g : ι → L ≃ₐ[K] L} (hg : Subgroup.closure (Set.range g) = ⊤)
    (f : ofModuleMonoidAlgebra.obj (ModuleCat.of (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L))
      (MonoidAlgebra.relationModule ℤ_[p] (L ≃ₐ[K] L) g)) ⟶
        Rep.of (padicCompletionUnitsRepresentation p L K))
    (hf : Function.Surjective ((_root_.groupCohomology.functor ℤ_[p] (L ≃ₐ[K] L) 2).map f))
    (S : Subgroup (L ≃ₐ[K] L)) [Fintype S] (hS : IsPGroup p S) :
    Function.Bijective ((tateCohomologyFunctor (2 : ℤ)).map ((resFunctor S.subtype).map f)) := by
  obtain ⟨u, hu⟩ :=
    exists_zmultiples_eq_top_restriction_groupCohomology_two_padicCompletionUnits p K L
  obtain ⟨x, hx⟩ := hf u
  -- Restriction is natural, so every multiple of the restriction of `u` is in the image.
  have hsurj : Function.Surjective
      ((_root_.groupCohomology.functor ℤ_[p] S 2).map ((resFunctor S.subtype).map f)) :=
    fun y ↦ by
      obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 ((hu S).symm ▸ AddSubgroup.mem_top y)
      exact ⟨m • groupCohomology.map S.subtype (𝟙 _) 2 x, (map_zsmul _ m _).trans
        (congrArg (m • ·) ((ConcreteCategory.congr_hom
          ((_root_.groupCohomology.resNatTrans ℤ_[p] S.subtype 2).naturality f) x).symm.trans
            (congrArg _ hx)))⟩
  -- The same on Tate cohomology, which is group cohomology in degree two.
  set e := TateCohomology.isoGroupCohomology (R := ℤ_[p]) (G := S) 2
  have hnat (w) : e.hom.app _ ((tateCohomologyFunctor (2 : ℤ)).map
      ((resFunctor S.subtype).map f) w) = (_root_.groupCohomology.functor ℤ_[p] S 2).map
        ((resFunctor S.subtype).map f) (e.hom.app _ w) :=
    ConcreteCategory.congr_hom (e.hom.naturality _) w
  have hsurjT : Function.Surjective
      ((tateCohomologyFunctor (2 : ℤ)).map ((resFunctor S.subtype).map f)) := fun y ↦ by
    obtain ⟨z, hz⟩ := hsurj (e.hom.app _ y)
    refine ⟨e.inv.app _ z, (ConcreteCategory.bijective_of_isIso (e.hom.app _)).injective ?_⟩
    rw [hnat, Iso.inv_hom_id_app_apply, hz]
  -- Both sides have `#S` elements.
  obtain ⟨n, hn⟩ := hS.exists_card_eq
  have hcardR : Nat.card (tateCohomology (res S.subtype (ofModuleMonoidAlgebra.obj (ModuleCat.of
      (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) (MonoidAlgebra.relationModule ℤ_[p] (L ≃ₐ[K] L) g)))) 2) =
        Nat.card S := by
    rw [TateCohomology.natCard_tateCohomology_two_res_relationModule ℤ_[p] hg S,
      PadicInt.natCard_quotient_span (Nat.cast_ne_zero.mpr Nat.card_pos.ne'),
      PadicInt.valuation_natCast, hn, padicValNat.prime_pow]
  have hcardA : Nat.card (tateCohomology
      (res S.subtype (Rep.of (padicCompletionUnitsRepresentation p L K))) 2) = Nat.card S :=
    (Nat.card_congr (e.app _).toLinearEquiv.toEquiv).trans
      (natCard_groupCohomology_two_res_padicCompletionUnits p K L S hS)
  have : Finite (tateCohomology (res S.subtype (ofModuleMonoidAlgebra.obj (ModuleCat.of
      (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) (MonoidAlgebra.relationModule ℤ_[p] (L ≃ₐ[K] L) g)))) 2) :=
    Nat.finite_of_card_ne_zero (hcardR ▸ Nat.card_pos.ne')
  exact (Nat.bijective_iff_surjective_and_card _).2 ⟨hsurjT, hcardR.trans hcardA.symm⟩

end LocalField

/-- **A relation-module surjection onto `A(L)` which is onto on `H²` has projective kernel.** Let
`L/K` be a finite Galois extension of finite extensions of `ℚ_p`, `g` a family generating
`G = Gal(L/K)`, and `β` a surjection of `ℤ_p[G]`-modules from the relation module of `g` onto the
`p`-adic completion `A(L)` of `Lˣ`. If `β` induces a surjection `H²(G, R) → H²(G, A(L))`, then the
kernel of `β` is a projective `ℤ_p[G]`-module. -/
theorem projective_ker_of_relationModule_surjective_of_h2_surjective {L K : Type} [Field L]
    [Field K] [Algebra K L] [Algebra ℚ_[p] L] [Module.Finite ℚ_[p] L] [Algebra ℚ_[p] K]
    [IsScalarTower ℚ_[p] K L] [IsGalois K L] {ι : Type} [Fintype ι] {g : ι → L ≃ₐ[K] L}
    (hg : Subgroup.closure (Set.range g) = ⊤)
    {β : MonoidAlgebra.relationModule ℤ_[p] (L ≃ₐ[K] L) g →ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)]
      Additive ↑(padicCompletionUnits p L)} (hβ : Function.Surjective β)
    (h2 : Function.Surjective ((_root_.groupCohomology.functor ℤ_[p] (L ≃ₐ[K] L) 2).map
      (ofModuleMonoidAlgebra.map (ModuleCat.ofHom β)))) :
    Module.Projective (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) (LinearMap.ker β) := by
  have : Module.Finite ℚ_[p] K := .left ℚ_[p] K L
  have : FiniteDimensional K L := .right ℚ_[p] K L
  -- The local-field structures of `K` and `L`; the statement does not see them.
  let _ := finiteExtensionValuativeRel ℚ_[p] K
  let _ := finiteExtensionNormedFieldTopology ℚ_[p] K
  have := finiteExtension_isNonarchimedeanLocalField ℚ_[p] K
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  let _ := finiteExtensionValuativeRel ℚ_[p] L
  let _ := finiteExtensionNormedFieldTopology ℚ_[p] L
  have := finiteExtension_isNonarchimedeanLocalField ℚ_[p] L
  have := finiteExtension_valuativeExtension ℚ_[p] L
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ_[p] L).injective
  let Λ := MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)
  let A := Rep.of (padicCompletionUnitsRepresentation p L K)
  -- The module structure of `A(L)` is that of `A.ρ.asModule`, so the unit of the equivalence
  -- between representations and `ℤ_p[G]`-modules compares the two representations of `A(L)`.
  let eA : ofModuleMonoidAlgebra.obj (ModuleCat.of Λ (Additive ↑(padicCompletionUnits p L))) ≅
      A :=
    (Rep.unitIso A).symm
  -- The sequence `0 → ker β → R → A(L) → 0`, carried to representations and ending in `A`.
  let T₀ := β.shortComplexKer.map ofModuleMonoidAlgebra
  have hT₀ : T₀.ShortExact := (LinearMap.shortExact_shortComplexKer hβ).map_of_exact _
  let T : ShortComplex (Rep ℤ_[p] (L ≃ₐ[K] L)) :=
    ShortComplex.mk T₀.f (T₀.g ≫ eA.hom) (by rw [← Category.assoc, T₀.zero, zero_comp])
  have hT : T.ShortExact := ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (S₁ := T₀) (S₂ := T) (Iso.refl _) (Iso.refl _) eA (by simp [T])
      (by simp [T])) hT₀
  -- `ker β` is a `ℤ_p`-lattice, as a submodule of `ℤ_p[G]^ι`.
  have : Module.Free ℤ_[p] (LinearMap.ker β) :=
    Module.Free.of_injective_of_projective_of_isPrincipalIdealRing (R := ℤ_[p])
      (M := ι → Λ) (N := LinearMap.ker β)
      (((MonoidAlgebra.relationModule ℤ_[p] (L ≃ₐ[K] L) g).subtype ∘ₗ
        (LinearMap.ker β).subtype).restrictScalars ℤ_[p])
      (Subtype.val_injective.comp Subtype.val_injective)
  let e₁ : T.X₁.ρ.asModule ≃ₗ[Λ] LinearMap.ker β :=
    (counitIso (ModuleCat.of Λ (LinearMap.ker β))).toLinearEquiv
  have : Module.Projective ℤ_[p] T.X₁.V :=
    .of_equiv (e₁.restrictScalars ℤ_[p] |>.symm.trans T.X₁.ρ.asModuleEquiv)
  -- On an `ℓ`-subgroup with `ℓ ≠ p`, all positive-degree cohomology vanishes: `#S` is a unit.
  have hsub (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ p) (S : Subgroup (L ≃ₐ[K] L)) [Fintype S]
      (hS : IsPGroup ℓ S) (B : Rep ℤ_[p] (L ≃ₐ[K] L)) (n : ℕ) :
      Subsingleton (tateCohomology (res S.subtype B) (n + 1 : ℕ)) := by
    obtain ⟨e, he⟩ := hS.exists_card_eq
    have hunit : IsUnit (Nat.card S : ℤ_[p]) := by
      rw [he, Nat.cast_pow]
      exact (PadicInt.isUnit_natCast_of_coprime
        ((Nat.coprime_primes Fact.out Fact.out).mpr (Ne.symm hℓ))).pow e
    exact @Equiv.subsingleton _ _
      ((TateCohomology.isoGroupCohomology (n + 1)).app _).toLinearEquiv.toEquiv
      (groupCohomology.subsingleton_of_isUnit_natCard (res S.subtype B) hunit n)
  -- Tate's criterion in degrees `1, 2, 3`: `H-hat^1(S, A(L))` and `H-hat^3(S, R)` vanish, and the
  -- map is bijective on `H-hat^2(S, -)`, on `p`-subgroups by
  -- `bijective_tateCohomology_two_res_of_surjective`.
  have : Module.Projective Λ T.X₁.ρ.asModule := by
    refine TateCohomology.projective_X₁_of_forall_isPGroup
      (fun _ ↦ PadicInt.isUnit_natCast_or_isMaximal_span) hT (q := 2) (fun ℓ _ S _ hS ↦ ?_)
      (fun ℓ _ S _ hS ↦ ?_) (fun ℓ _ S _ hS ↦ @Function.injective_of_subsingleton _ _
        (ModuleCat.subsingleton_of_isZero
          (TateCohomology.isZero_tateCohomology_three_res_relationModule ℤ_[p] hg S)) _)
    · by_cases hℓ : ℓ = p
      · subst hℓ
        exact @Function.surjective_to_subsingleton _ _ _ (ModuleCat.subsingleton_of_isZero
          ((isZero_groupCohomology_one_res_padicCompletionUnits ℓ K L S).of_iso
            ((TateCohomology.isoGroupCohomology 1).app _))) _
      · exact @Function.surjective_to_subsingleton _ _ _ (hsub ℓ hℓ S hS A 0) _
    · by_cases hℓ : ℓ = p
      · subst hℓ
        refine bijective_tateCohomology_two_res_of_surjective ℓ hg T.g ?_ S hS
        rw [Functor.map_comp, ConcreteCategory.coe_comp]
        exact (ConcreteCategory.bijective_of_isIso _).surjective.comp h2
      · exact ⟨@Function.injective_of_subsingleton _ _ (hsub ℓ hℓ S hS _ 1) _,
          @Function.surjective_to_subsingleton _ _ _ (hsub ℓ hℓ S hS _ 1) _⟩
  exact .of_equiv e₁

/-- **A relation-module surjection onto `A(L)` which is onto on `H²` has kernel `ℤ_p[G]`.** Let
`L/K` be a finite Galois extension of finite extensions of `ℚ_p`, `g` a family of
`[K : ℚ_p] + 2` elements generating `G = Gal(L/K)`, and `β` a surjection of `ℤ_p[G]`-modules from
the relation module of `g` onto the `p`-adic completion `A(L)` of `Lˣ`. If `β` induces a
surjection `H²(G, R) → H²(G, A(L))`, then the kernel of `β` is isomorphic to `ℤ_p[G]`. -/
theorem nonempty_ker_linearEquiv_of_relationModule_surjective_of_h2_surjective {L K : Type}
    [Field L] [Field K] [Algebra K L] [Algebra ℚ_[p] L] [Module.Finite ℚ_[p] L] [Algebra ℚ_[p] K]
    [IsScalarTower ℚ_[p] K L] [IsGalois K L] {ι : Type} [Fintype ι] {g : ι → L ≃ₐ[K] L}
    (hg : Subgroup.closure (Set.range g) = ⊤) (hι : Fintype.card ι = Module.finrank ℚ_[p] K + 2)
    {β : MonoidAlgebra.relationModule ℤ_[p] (L ≃ₐ[K] L) g →ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)]
      Additive ↑(padicCompletionUnits p L)} (hβ : Function.Surjective β)
    (h2 : Function.Surjective ((_root_.groupCohomology.functor ℤ_[p] (L ≃ₐ[K] L) 2).map
      (ofModuleMonoidAlgebra.map (ModuleCat.ofHom β)))) :
    Nonempty (LinearMap.ker β ≃ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)]
      MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) :=
  have : FiniteDimensional K L := .right ℚ_[p] K L
  have := projective_ker_of_relationModule_surjective_of_h2_surjective p hg hβ h2
  nonempty_ker_linearEquiv_of_relationModule_surjective hg hι hβ
    (nonempty_padicCompletionUnits_tensorRat_linearEquiv p)

end TauCeti
