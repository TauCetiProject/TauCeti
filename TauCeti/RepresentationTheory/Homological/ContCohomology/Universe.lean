/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.DegreeZero

/-!
# Universe independence of the extra carrier parameter in continuous cohomology

For a topological ring `R : Type u` and a topological group `G : Type v`, Mathlib's continuous
cohomology `continuousCohomology.{u, v, w} n X` takes a continuous representation
`X : TopRep.{max v w} R G`. The extra universe parameter `w` enters the carrier universe of `X`
only through `max v w` — so that the coinduced function spaces `C(G, -)` stay in the same category
— yet `w` itself is threaded separately through the recursion of `TopRep.resolutionX`, `TopRep.d`,
`TopRep.homogeneousCochains`, `ContinuousCohomology.cocycles` and `continuousCohomology`.

Consequently, for any `X : TopRep.{max v w} R G`, instantiating that third universe parameter at
`max v w` and at `w` produces objects in the *same* categories (`TopRep.{max v w} R G`,
`CochainComplex (TopModuleCat.{max v w} R) ℕ` and `TopModuleCat.{max v w} R`, since
`max v (max v w)` and `max v w` are definitionally equal) that are not definitionally equal. At
`w = 0`, where `max v 0` is definitionally `v`, this is the discrepancy between the two parameters
`w' = v` and `w' = 0` for a representation `X : TopRep.{v} R G` in the universe of `G`: elaborating
`continuousCohomology n X` from `X : TopRep.{v} R G` chooses `w' = v`, whereas definitions whose
extra universe parameter is unbound default to `w' = 0`.

This file proves that the coinduced resolutions, homogeneous cochain complexes, cocycle objects and
continuous cohomology objects at the parameters `max v w` and `w` are propositionally equal, and
packages the resulting comparison isomorphisms with their full computational interface:

* On `TopRep.resolutionX`, `X.resolutionXUniverseIso n` is the identity in degree `0` and acts in
  degree `n + 1` on `C(G, -)` by postcomposing with the degree-`n` isomorphism (with inverse given
  by postcomposing with the inverse); it commutes with the coinduction unit and with the recursive
  differentials `TopRep.d`.
* On `TopRep.homogeneousCochains`, `X.homogeneousCochainsUniverseIso` restricts the shifted
  resolution isomorphism to `G`-invariants in every degree.
* On cocycles and continuous cohomology, `X.cocyclesUniverseIso n` and
  `X.continuousCohomologyUniverseIso n` (with underlying additive equivalences
  `X.cocyclesUniverseEquiv n` and `X.continuousCohomologyUniverseEquiv n`) agree with the maps
  induced on cycles and homology by the cochain isomorphism, preserve cocycle values on `Gⁿ⁺¹` and
  send the cohomology class of a cocycle (`ContinuousCohomology.π` and `TopRep.cochainClass`) to
  the class of its image.
* The comparison is natural with respect to compatible-pair maps (`ContinuousCohomology.map`), and
  in particular with respect to equivariant coefficient maps (`coeffMap`), subgroup restriction
  (`res`) and quotient inflation (`infl`), giving a natural isomorphism of functors
  `continuousCohomologyFunctorUniverseIso`.
* When `w = v` (in particular for `G : Type 0` at `w = 0`), the two universe parameters coincide
  and every comparison isomorphism is the identity.

Since `w` does not appear outside `max v w` in the arguments, it is declared as the first universe
parameter throughout this file: specializing to `w = 0` for `X : TopRep.{v} R G` is written `.{0}`.

## Main definitions

* `TopRep.resolutionXUniverseIso`: the isomorphism
  `resolutionX.{u, v, max v w} X n ≅ resolutionX.{u, v, w} X n`.
* `TopRep.homogeneousCochainsUniverseIso`: the chain isomorphism
  `homogeneousCochains.{u, v, max v w} X ≅ homogeneousCochains.{u, v, w} X`.
* `TopRep.cocyclesUniverseIso`, `TopRep.cocyclesUniverseEquiv`: the comparison on `n`-cocycles, in
  `TopModuleCat R` and as an additive equivalence.
* `TopRep.continuousCohomologyUniverseIso`, `TopRep.continuousCohomologyUniverseEquiv`: the
  comparison on degree-`n` continuous cohomology, in `TopModuleCat R` and as an additive
  equivalence.
* `TauCeti.ContinuousCohomology.continuousCohomologyFunctorUniverseIso`: the natural isomorphism
  `continuousCohomologyFunctor.{u, v, max v w} R G n ≅ continuousCohomologyFunctor.{u, v, w} R G n`.

## Main results

* `TopRep.resolutionX_universe_eq`, `TopRep.homogeneousCochains_universe_eq`,
  `TopRep.cocycles_universe_eq`, `TopRep.continuousCohomology_universe_eq`: propositional equality
  of the objects at parameters `max v w` and `w`.
* `TopRep.π_comp_continuousCohomologyUniverseIso_hom`,
  `TopRep.continuousCohomologyUniverseEquiv_π`,
  `TopRep.continuousCohomologyUniverseEquiv_cochainClass`: the cohomology comparison sends the
  class of a cocycle to the class of its image.
* `TauCeti.ContinuousCohomology.map_comp_continuousCohomologyUniverseIso_hom`,
  `TauCeti.ContinuousCohomology.coeffMap_comp_continuousCohomologyUniverseIso_hom`,
  `TauCeti.ContinuousCohomology.res_comp_continuousCohomologyUniverseIso_hom`,
  `TauCeti.ContinuousCohomology.infl_comp_continuousCohomologyUniverseIso_hom`: naturality with
  respect to compatible pairs, coefficient maps, restriction and inflation.
* `TauCeti.ContinuousCohomology.continuousCohomologyUniverseIso_zero_hom_comp_zeroIso_hom`,
  `TauCeti.ContinuousCohomology.continuousCohomologyUniverseEquiv_degreeZeroClass`: compatibility
  in degree zero with `ContinuousCohomology.zeroIso` and `degreeZeroClass`.
-/

public section

open CategoryTheory

universe w u v

namespace TopRep

open ContRepresentation _root_.ContinuousCohomology

section ResolutionAndCochains

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : TopRep.{max v w} R G)

/-- The `n`-th term of the coinduced resolution of `X` at extra universe `max v w` equals that at
`w`. -/
theorem resolutionX_universe_eq :
    ∀ n : ℕ, resolutionX.{u, v, max v w} X n = resolutionX.{u, v, w} X n
  | 0 => rfl
  | n + 1 => congrArg coind₁ (resolutionX_universe_eq n)

private theorem d_succ_step {A A' : TopRep.{max v w} R G} (hA : A = A')
    (f : A ⟶ A.coind₁) (f' : A' ⟶ A'.coind₁) (hf : f ≍ f') :
    (ofHom A.coind₁.ρ.coind₁ι - (coind₁Functor R G).map f) ≍
      (ofHom A'.coind₁.ρ.coind₁ι - (coind₁Functor R G).map f') := by
  subst hA
  cases hf
  rfl

/-- The `n`-th differential of the coinduced resolution of `X` at extra universe `max v w` agrees
with that at `w`. -/
theorem d_universe_heq : ∀ n : ℕ, d.{u, v, max v w} X n ≍ d.{u, v, w} X n
  | 0 => HEq.rfl
  | n + 1 => by
    rw [d_succ, d_succ]
    exact d_succ_step (X.resolutionX_universe_eq n) _ _ (d_universe_heq n)

private theorem cochainComplex_of_eq {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    {F F' : ℕ → C} {f₁ : ∀ n, F n ⟶ F (n + 1)} {f₂ : ∀ n, F' n ⟶ F' (n + 1)}
    (hd₁ : ∀ n, f₁ n ≫ f₁ (n + 1) = 0) (hd₂ : ∀ n, f₂ n ≫ f₂ (n + 1) = 0)
    (hF : F = F') (hf : f₁ ≍ f₂) :
    CochainComplex.of F f₁ hd₁ = CochainComplex.of F' f₂ hd₂ := by
  subst hF
  cases hf
  rfl

/-- The unshifted coinduced resolution complex of `X` at extra universe `max v w` equals that at
`w`. -/
theorem resolution_universe_eq : resolution.{u, v, max v w} X = resolution.{u, v, w} X := by
  refine cochainComplex_of_eq _ _ (funext X.resolutionX_universe_eq) ?_
  refine Function.hfunext rfl fun n m hnm ↦ ?_
  cases hnm
  exact X.d_universe_heq n

/-- The shifted coinduced resolution complex of `X` at extra universe `max v w` equals that at
`w`. -/
theorem resolution'_universe_eq : resolution'.{u, v, max v w} X = resolution'.{u, v, w} X := by
  refine cochainComplex_of_eq _ _ (funext fun n ↦ X.resolutionX_universe_eq (n + 1)) ?_
  refine Function.hfunext rfl fun n m hnm ↦ ?_
  cases hnm
  exact X.d_universe_heq (n + 1)

/-- The homogeneous cochain complex of `X` at extra universe `max v w` equals that at `w`. -/
theorem homogeneousCochains_universe_eq :
    homogeneousCochains.{u, v, max v w} X = homogeneousCochains.{u, v, w} X :=
  congrArg ((invariantsFunctor.{u, v, max v w} R G).mapHomologicalComplex _).obj
    X.resolution'_universe_eq

/-- The canonical isomorphism `resolutionX.{u, v, max v w} X n ≅ resolutionX.{u, v, w} X n`
identifying the degree-`n` terms of the coinduced resolution across the extra universe parameter. -/
noncomputable def resolutionXUniverseIso (n : ℕ) :
    resolutionX.{u, v, max v w} X n ≅ resolutionX.{u, v, w} X n :=
  eqToIso (X.resolutionX_universe_eq n)

/-- `resolutionXUniverseIso` is the transport `eqToIso` along `resolutionX_universe_eq`. -/
theorem resolutionXUniverseIso_eq_eqToIso (n : ℕ) :
    X.resolutionXUniverseIso.{w} n = eqToIso (X.resolutionX_universe_eq.{w} n) :=
  (rfl)

/-- In degree zero, `resolutionXUniverseIso` is the identity of `X`. -/
@[simp]
theorem resolutionXUniverseIso_zero : X.resolutionXUniverseIso.{w} 0 = Iso.refl X :=
  (rfl)

/-- In degree zero, the forward map of `resolutionXUniverseIso` is the identity on elements. -/
theorem resolutionXUniverseIso_zero_hom_apply (x : X.V) :
    (X.resolutionXUniverseIso.{w} 0).hom.hom x = x :=
  (rfl)

/-- In degree zero, the inverse map of `resolutionXUniverseIso` is the identity on elements. -/
theorem resolutionXUniverseIso_zero_inv_apply (x : X.V) :
    (X.resolutionXUniverseIso.{w} 0).inv.hom x = x :=
  (rfl)

/-- In degree `n + 1`, `resolutionXUniverseIso` is the coinduction of the degree-`n`
isomorphism. -/
theorem resolutionXUniverseIso_succ (n : ℕ) :
    X.resolutionXUniverseIso.{w} (n + 1) =
      (coind₁Functor R G).mapIso (X.resolutionXUniverseIso.{w} n) :=
  (eqToIso_map (coind₁Functor R G) (X.resolutionX_universe_eq.{w} n)).symm

/-- In degree `n + 1`, the forward map of `resolutionXUniverseIso` acts on `C(G, -)` by
postcomposing with the degree-`n` isomorphism. -/
@[simp]
theorem resolutionXUniverseIso_succ_hom_apply (n : ℕ)
    (f : (resolutionX.{u, v, max v w} X (n + 1)).V) (g : G) :
    (X.resolutionXUniverseIso.{w} (n + 1)).hom.hom f g =
      (X.resolutionXUniverseIso.{w} n).hom.hom (f g) := by
  have aux : ∀ {A B : TopRep.{max v w} R G} (h : A = B) (f : A.coind₁.V),
      (eqToIso (congrArg coind₁ h)).hom.hom f g = (eqToIso h).hom.hom (f g) := by
    rintro A _ rfl f
    rfl
  exact aux (X.resolutionX_universe_eq.{w} n) f

/-- In degree `n + 1`, the inverse map of `resolutionXUniverseIso` acts on `C(G, -)` by
postcomposing with the inverse of the degree-`n` isomorphism. -/
@[simp]
theorem resolutionXUniverseIso_succ_inv_apply (n : ℕ)
    (f : (resolutionX.{u, v, w} X (n + 1)).V) (g : G) :
    (X.resolutionXUniverseIso.{w} (n + 1)).inv.hom f g =
      (X.resolutionXUniverseIso.{w} n).inv.hom (f g) := by
  have aux : ∀ {A B : TopRep.{max v w} R G} (h : A = B) (f : B.coind₁.V),
      (eqToIso (congrArg coind₁ h)).inv.hom f g = (eqToIso h).inv.hom (f g) := by
    rintro A _ rfl f
    rfl
  exact aux (X.resolutionX_universe_eq.{w} n) f

/-- When `w = v`, the two universe parameters coincide and `resolutionXUniverseIso` is the
identity. -/
theorem resolutionXUniverseIso_self (Y : TopRep.{v} R G) (n : ℕ) :
    Y.resolutionXUniverseIso.{v} n = Iso.refl _ :=
  eqToIso_refl _

/-- `resolutionXUniverseIso` commutes with the coinduction unit `coind₁ι` in degree zero. -/
@[reassoc]
theorem coind₁ι_comp_resolutionXUniverseIso_one_hom :
    ofHom X.ρ.coind₁ι ≫ (X.resolutionXUniverseIso.{w} 1).hom =
      (X.resolutionXUniverseIso.{w} 0).hom ≫ ofHom X.ρ.coind₁ι := by
  rw [resolutionXUniverseIso_eq_eqToIso, resolutionXUniverseIso_zero, Iso.refl_hom,
    eqToIso.hom, eqToHom_refl, Category.comp_id, Category.id_comp]

/-- `resolutionXUniverseIso` commutes with the differentials of the coinduced resolution. -/
@[reassoc]
theorem d_comp_resolutionXUniverseIso_hom (n : ℕ) :
    d.{u, v, max v w} X n ≫ (X.resolutionXUniverseIso.{w} (n + 1)).hom =
      (X.resolutionXUniverseIso.{w} n).hom ≫ d.{u, v, w} X n := by
  have aux : ∀ {A A' B B' : TopRep.{max v w} R G} (hA : A = A') (hB : B = B')
      {f : A ⟶ B} {f' : A' ⟶ B'}, f ≍ f' → f ≫ eqToHom hB = eqToHom hA ≫ f' := by
    rintro A _ B _ rfl rfl f _ ⟨⟩
    simp
  exact aux (X.resolutionX_universe_eq n) (X.resolutionX_universe_eq (n + 1)) (X.d_universe_heq n)

/-- The inverse of `resolutionXUniverseIso` commutes with the differentials of the coinduced
resolution. -/
@[reassoc]
theorem d_comp_resolutionXUniverseIso_inv (n : ℕ) :
    d.{u, v, w} X n ≫ (X.resolutionXUniverseIso.{w} (n + 1)).inv =
      (X.resolutionXUniverseIso.{w} n).inv ≫ d.{u, v, max v w} X n := by
  have aux : ∀ {A A' B B' : TopRep.{max v w} R G} (hA : A = A') (hB : B = B')
      {f : A ⟶ B} {f' : A' ⟶ B'}, f ≍ f' → f ≫ eqToHom hB = eqToHom hA ≫ f' := by
    rintro A _ B _ rfl rfl f _ ⟨⟩
    simp
  exact aux (X.resolutionX_universe_eq n).symm (X.resolutionX_universe_eq (n + 1)).symm
    (X.d_universe_heq n).symm

/-- **The homogeneous cochain complex does not depend on the extra carrier universe**: the canonical
chain isomorphism `homogeneousCochains.{u, v, max v w} X ≅ homogeneousCochains.{u, v, w} X`. -/
noncomputable def homogeneousCochainsUniverseIso :
    homogeneousCochains.{u, v, max v w} X ≅ homogeneousCochains.{u, v, w} X :=
  eqToIso X.homogeneousCochains_universe_eq

/-- `homogeneousCochainsUniverseIso` is the transport `eqToIso` along
`homogeneousCochains_universe_eq`. -/
theorem homogeneousCochainsUniverseIso_eq_eqToIso :
    X.homogeneousCochainsUniverseIso.{w} = eqToIso X.homogeneousCochains_universe_eq.{w} :=
  (rfl)

/-- When `w = v`, `homogeneousCochainsUniverseIso` is the identity isomorphism. -/
theorem homogeneousCochainsUniverseIso_self (Y : TopRep.{v} R G) :
    Y.homogeneousCochainsUniverseIso.{v} = Iso.refl _ :=
  eqToIso_refl _

/-- In degree `n`, the forward map of `homogeneousCochainsUniverseIso` is the restriction to
`G`-invariants of `resolutionXUniverseIso` in degree `n + 1`. -/
theorem homogeneousCochainsUniverseIso_hom_f (n : ℕ) :
    X.homogeneousCochainsUniverseIso.{w}.hom.f n =
      (invariantsFunctor R G).map (X.resolutionXUniverseIso.{w} (n + 1)).hom := by
  rw [homogeneousCochainsUniverseIso_eq_eqToIso, resolutionXUniverseIso_eq_eqToIso,
    eqToIso.hom, eqToIso.hom, HomologicalComplex.eqToHom_f, eqToHom_map]

/-- In degree `n`, the inverse map of `homogeneousCochainsUniverseIso` is the restriction to
`G`-invariants of the inverse of `resolutionXUniverseIso` in degree `n + 1`. -/
theorem homogeneousCochainsUniverseIso_inv_f (n : ℕ) :
    X.homogeneousCochainsUniverseIso.{w}.inv.f n =
      (invariantsFunctor R G).map (X.resolutionXUniverseIso.{w} (n + 1)).inv := by
  rw [homogeneousCochainsUniverseIso_eq_eqToIso, resolutionXUniverseIso_eq_eqToIso,
    eqToIso.inv, eqToIso.inv, HomologicalComplex.eqToHom_f, eqToHom_map]

/-- On elements, the degree-`n` forward map of `homogeneousCochainsUniverseIso` applies
`resolutionXUniverseIso` in degree `n + 1` to the underlying invariant function. -/
theorem coe_homogeneousCochainsUniverseIso_hom_f (n : ℕ)
    (a : (homogeneousCochains.{u, v, max v w} X).X n) :
    (X.homogeneousCochainsUniverseIso.{w}.hom.f n a).val =
      (X.resolutionXUniverseIso.{w} (n + 1)).hom.hom a.val := by
  rw [homogeneousCochainsUniverseIso_hom_f]
  rfl

/-- On elements, the degree-`n` inverse map of `homogeneousCochainsUniverseIso` applies the inverse
of `resolutionXUniverseIso` in degree `n + 1` to the underlying invariant function. -/
theorem coe_homogeneousCochainsUniverseIso_inv_f (n : ℕ)
    (a : (homogeneousCochains.{u, v, w} X).X n) :
    (X.homogeneousCochainsUniverseIso.{w}.inv.f n a).val =
      (X.resolutionXUniverseIso.{w} (n + 1)).inv.hom a.val := by
  rw [homogeneousCochainsUniverseIso_inv_f]
  rfl

end ResolutionAndCochains

/-! ### Cocycles, continuous cohomology, and classes -/

section Cohomology

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : TopRep.{max v w} R G) (n : ℕ)

/-- The `n`-cocycles of `X` at extra universe `max v w` equal those at `w`. -/
theorem cocycles_universe_eq :
    cocycles.{u, v, max v w} X n = cocycles.{u, v, w} X n :=
  congrArg (fun C ↦ HomologicalComplex.cycles C n) X.homogeneousCochains_universe_eq

/-- The degree-`n` continuous cohomology of `X` at extra universe `max v w` equals that at `w`. -/
theorem continuousCohomology_universe_eq :
    continuousCohomology.{u, v, max v w} n X = continuousCohomology.{u, v, w} n X :=
  congrArg (fun C ↦ HomologicalComplex.homology C n) X.homogeneousCochains_universe_eq

/-- The canonical isomorphism `cocycles.{u, v, max v w} X n ≅ cocycles.{u, v, w} X n` in
`TopModuleCat R` induced by `homogeneousCochainsUniverseIso`. -/
noncomputable def cocyclesUniverseIso :
    cocycles.{u, v, max v w} X n ≅ cocycles.{u, v, w} X n :=
  HomologicalComplex.cyclesMapIso X.homogeneousCochainsUniverseIso.{w} n

/-- `cocyclesUniverseIso` is `cyclesMapIso` of `homogeneousCochainsUniverseIso`. -/
theorem cocyclesUniverseIso_eq_cyclesMapIso :
    X.cocyclesUniverseIso.{w} n =
      HomologicalComplex.cyclesMapIso X.homogeneousCochainsUniverseIso.{w} n :=
  (rfl)

/-- `cocyclesUniverseIso` agrees with `eqToIso` along `cocycles_universe_eq`. -/
theorem cocyclesUniverseIso_eq_eqToIso :
    X.cocyclesUniverseIso.{w} n = eqToIso (X.cocycles_universe_eq.{w} n) := by
  have aux : ∀ {K L : CochainComplex (TopModuleCat.{max v w, u} R) ℕ} (h : K = L),
      HomologicalComplex.cyclesMapIso (eqToIso h) n =
        eqToIso (congrArg (fun C ↦ HomologicalComplex.cycles C n) h) := by
    rintro K _ rfl
    ext : 1
    exact HomologicalComplex.cyclesMap_id K n
  exact aux X.homogeneousCochains_universe_eq

/-- When `w = v`, `cocyclesUniverseIso` is the identity isomorphism. -/
theorem cocyclesUniverseIso_self (Y : TopRep.{v} R G) :
    Y.cocyclesUniverseIso.{v} n = Iso.refl _ := by
  rw [cocyclesUniverseIso_eq_eqToIso]
  exact eqToIso_refl _

/-- The canonical additive equivalence `cocycles.{u, v, max v w} X n ≃+ cocycles.{u, v, w} X n`
between the cocycle groups at extra universes `max v w` and `w`. -/
noncomputable def cocyclesUniverseEquiv :
    cocycles.{u, v, max v w} X n ≃+ cocycles.{u, v, w} X n :=
  (X.cocyclesUniverseIso.{w} n).toContinuousLinearEquiv.toAddEquiv

/-- `cocyclesUniverseEquiv` acts as the forward morphism of `cocyclesUniverseIso`. -/
theorem cocyclesUniverseEquiv_apply (z : cocycles.{u, v, max v w} X n) :
    X.cocyclesUniverseEquiv.{w} n z = (X.cocyclesUniverseIso.{w} n).hom z :=
  (rfl)

/-- The inverse of `cocyclesUniverseEquiv` acts as the inverse morphism of
`cocyclesUniverseIso`. -/
theorem cocyclesUniverseEquiv_symm_apply (z : cocycles.{u, v, w} X n) :
    (X.cocyclesUniverseEquiv.{w} n).symm z = (X.cocyclesUniverseIso.{w} n).inv z :=
  (rfl)

/-- When `w = v`, `cocyclesUniverseEquiv` is the identity additive equivalence. -/
theorem cocyclesUniverseEquiv_self (Y : TopRep.{v} R G) :
    Y.cocyclesUniverseEquiv.{v} n = AddEquiv.refl _ := by
  ext z
  rw [cocyclesUniverseEquiv_apply, cocyclesUniverseIso_self]
  rfl

/-- **Continuous cohomology does not depend on the extra carrier universe**: the canonical
isomorphism `continuousCohomology.{u, v, max v w} n X ≅ continuousCohomology.{u, v, w} n X` in
`TopModuleCat R` induced on homology by `homogeneousCochainsUniverseIso`. -/
noncomputable def continuousCohomologyUniverseIso :
    continuousCohomology.{u, v, max v w} n X ≅ continuousCohomology.{u, v, w} n X :=
  HomologicalComplex.homologyMapIso X.homogeneousCochainsUniverseIso.{w} n

/-- `continuousCohomologyUniverseIso` is `homologyMapIso` of `homogeneousCochainsUniverseIso`. -/
theorem continuousCohomologyUniverseIso_eq_homologyMapIso :
    X.continuousCohomologyUniverseIso.{w} n =
      HomologicalComplex.homologyMapIso X.homogeneousCochainsUniverseIso.{w} n :=
  (rfl)

/-- `continuousCohomologyUniverseIso` agrees with `eqToIso` along
`continuousCohomology_universe_eq`. -/
theorem continuousCohomologyUniverseIso_eq_eqToIso :
    X.continuousCohomologyUniverseIso.{w} n =
      eqToIso (X.continuousCohomology_universe_eq.{w} n) := by
  have aux : ∀ {K L : CochainComplex (TopModuleCat.{max v w, u} R) ℕ} (h : K = L),
      HomologicalComplex.homologyMapIso (eqToIso h) n =
        eqToIso (congrArg (fun C ↦ HomologicalComplex.homology C n) h) := by
    rintro K _ rfl
    ext : 1
    exact HomologicalComplex.homologyMap_id K n
  exact aux X.homogeneousCochains_universe_eq

/-- When `w = v`, `continuousCohomologyUniverseIso` is the identity isomorphism. -/
theorem continuousCohomologyUniverseIso_self (Y : TopRep.{v} R G) :
    Y.continuousCohomologyUniverseIso.{v} n = Iso.refl _ := by
  rw [continuousCohomologyUniverseIso_eq_eqToIso]
  exact eqToIso_refl _

/-- **Continuous cohomology does not depend on the extra carrier universe**, read as an additive
equivalence `continuousCohomology.{u, v, max v w} n X ≃+ continuousCohomology.{u, v, w} n X`. -/
noncomputable def continuousCohomologyUniverseEquiv :
    continuousCohomology.{u, v, max v w} n X ≃+ continuousCohomology.{u, v, w} n X :=
  (X.continuousCohomologyUniverseIso.{w} n).toContinuousLinearEquiv.toAddEquiv

/-- `continuousCohomologyUniverseEquiv` acts as the forward morphism of
`continuousCohomologyUniverseIso`. -/
theorem continuousCohomologyUniverseEquiv_apply
    (x : continuousCohomology.{u, v, max v w} n X) :
    X.continuousCohomologyUniverseEquiv.{w} n x =
      (X.continuousCohomologyUniverseIso.{w} n).hom x :=
  (rfl)

/-- The inverse of `continuousCohomologyUniverseEquiv` acts as the inverse morphism of
`continuousCohomologyUniverseIso`. -/
theorem continuousCohomologyUniverseEquiv_symm_apply
    (x : continuousCohomology.{u, v, w} n X) :
    (X.continuousCohomologyUniverseEquiv.{w} n).symm x =
      (X.continuousCohomologyUniverseIso.{w} n).inv x :=
  (rfl)

/-- When `w = v`, `continuousCohomologyUniverseEquiv` is the identity additive equivalence. -/
theorem continuousCohomologyUniverseEquiv_self (Y : TopRep.{v} R G) :
    Y.continuousCohomologyUniverseEquiv.{v} n = AddEquiv.refl _ := by
  ext x
  rw [continuousCohomologyUniverseEquiv_apply, continuousCohomologyUniverseIso_self]
  rfl

/-- `cocyclesUniverseIso` commutes with the inclusion `iCycles` into the homogeneous cochains. -/
@[reassoc (attr := simp)]
theorem cocyclesUniverseIso_hom_comp_iCycles :
    (X.cocyclesUniverseIso.{w} n).hom ≫ (homogeneousCochains.{u, v, w} X).iCycles n =
      (homogeneousCochains.{u, v, max v w} X).iCycles n ≫
        X.homogeneousCochainsUniverseIso.{w}.hom.f n :=
  HomologicalComplex.cyclesMap_i X.homogeneousCochainsUniverseIso.{w}.hom n

/-- The inverse of `cocyclesUniverseIso` commutes with the inclusion `iCycles` into the homogeneous
cochains. -/
@[reassoc (attr := simp)]
theorem cocyclesUniverseIso_inv_comp_iCycles :
    (X.cocyclesUniverseIso.{w} n).inv ≫ (homogeneousCochains.{u, v, max v w} X).iCycles n =
      (homogeneousCochains.{u, v, w} X).iCycles n ≫
        X.homogeneousCochainsUniverseIso.{w}.inv.f n :=
  HomologicalComplex.cyclesMap_i X.homogeneousCochainsUniverseIso.{w}.inv n

/-- **`continuousCohomologyUniverseIso` sends the class of a cocycle to the class of its image.** -/
@[reassoc (attr := simp)]
theorem π_comp_continuousCohomologyUniverseIso_hom :
    π.{u, v, max v w} X n ≫ (X.continuousCohomologyUniverseIso.{w} n).hom =
      (X.cocyclesUniverseIso.{w} n).hom ≫ π.{u, v, w} X n :=
  HomologicalComplex.homologyπ_naturality X.homogeneousCochainsUniverseIso.{w}.hom n

/-- The inverse of `continuousCohomologyUniverseIso` sends the class of a cocycle to the class of
its preimage. -/
@[reassoc (attr := simp)]
theorem π_comp_continuousCohomologyUniverseIso_inv :
    π.{u, v, w} X n ≫ (X.continuousCohomologyUniverseIso.{w} n).inv =
      (X.cocyclesUniverseIso.{w} n).inv ≫ π.{u, v, max v w} X n :=
  HomologicalComplex.homologyπ_naturality X.homogeneousCochainsUniverseIso.{w}.inv n

/-- **`continuousCohomologyUniverseEquiv` sends the class of a cocycle to the class of its
image.** -/
@[simp]
theorem continuousCohomologyUniverseEquiv_π (z : cocycles.{u, v, max v w} X n) :
    X.continuousCohomologyUniverseEquiv.{w} n (π.{u, v, max v w} X n z) =
      π.{u, v, w} X n (X.cocyclesUniverseEquiv.{w} n z) :=
  congr($(X.π_comp_continuousCohomologyUniverseIso_hom.{w} n) z)

/-- The inverse of `continuousCohomologyUniverseEquiv` sends the class of a cocycle to the class of
its preimage. -/
@[simp]
theorem continuousCohomologyUniverseEquiv_symm_π (z : cocycles.{u, v, w} X n) :
    (X.continuousCohomologyUniverseEquiv.{w} n).symm (π.{u, v, w} X n z) =
      π.{u, v, max v w} X n ((X.cocyclesUniverseEquiv.{w} n).symm z) :=
  congr($(X.π_comp_continuousCohomologyUniverseIso_inv.{w} n) z)

/-- `homogeneousCochainsUniverseIso` carries homogeneous cocycles to homogeneous cocycles. -/
theorem homogeneousCochainsUniverseIso_d_eq_zero
    (a : (homogeneousCochains.{u, v, max v w} X).X n)
    (ha : ((homogeneousCochains.{u, v, max v w} X).d n (n + 1)).hom a = 0) :
    ((homogeneousCochains.{u, v, w} X).d n (n + 1)).hom
        (X.homogeneousCochainsUniverseIso.{w}.hom.f n a) = 0 := by
  have comm := congrArg (fun h ↦ h.hom a)
    (X.homogeneousCochainsUniverseIso.{w}.hom.comm n (n + 1))
  simp only [TopModuleCat.hom_comp, ContinuousLinearMap.comp_apply] at comm
  exact comm.trans ((congrArg _ ha).trans (map_zero _))

/-- **`continuousCohomologyUniverseEquiv` preserves classes of homogeneous cocycles**
(`TopRep.cochainClass`). -/
theorem continuousCohomologyUniverseEquiv_cochainClass
    (a : (homogeneousCochains.{u, v, max v w} X).X n)
    (ha : ((homogeneousCochains.{u, v, max v w} X).d n (n + 1)).hom a = 0)
    (hb : ((homogeneousCochains.{u, v, w} X).d n (n + 1)).hom
      (X.homogeneousCochainsUniverseIso.{w}.hom.f n a) = 0 :=
        X.homogeneousCochainsUniverseIso_d_eq_zero.{w} n a ha) :
    X.continuousCohomologyUniverseEquiv.{w} n (cochainClass.{u, v, max v w} X n a ha) =
      cochainClass.{u, v, w} X n (X.homogeneousCochainsUniverseIso.{w}.hom.f n a) hb := by
  rw [cochainClass_def, cochainClass_def, continuousCohomologyUniverseEquiv_π]
  congr 1
  apply (homogeneousCochains.{u, v, w} X).iCycles_injective n
  have hi := congr($(X.cocyclesUniverseIso_hom_comp_iCycles.{w} n)
    ((homogeneousCochains.{u, v, max v w} X).cyclesMkOfEq a (n + 1) (CochainComplex.next ℕ n) ha))
  simpa only [cocyclesUniverseEquiv_apply, CategoryTheory.comp_apply,
    HomologicalComplex.iCycles_cyclesMkOfEq] using hi

/-- Under `cocyclesUniverseEquiv`, the underlying homogeneous cochain of a cocycle is carried by
`resolutionXUniverseIso` in degree `n + 1`. -/
theorem coe_iCycles_cocyclesUniverseEquiv (z : cocycles.{u, v, max v w} X n) :
    ((homogeneousCochains.{u, v, w} X).iCycles n (X.cocyclesUniverseEquiv.{w} n z)).val =
      (X.resolutionXUniverseIso.{w} (n + 1)).hom.hom
        ((homogeneousCochains.{u, v, max v w} X).iCycles n z).val := by
  have h : (homogeneousCochains.{u, v, w} X).iCycles n (X.cocyclesUniverseEquiv.{w} n z) =
      X.homogeneousCochainsUniverseIso.{w}.hom.f n
        ((homogeneousCochains.{u, v, max v w} X).iCycles n z) :=
    congr($(X.cocyclesUniverseIso_hom_comp_iCycles.{w} n) z)
  rw [h, coe_homogeneousCochainsUniverseIso_hom_f]

/-- In degree zero, `cocyclesUniverseEquiv` preserves the values of a homogeneous cocycle on `G`. -/
theorem iCycles_cocyclesUniverseEquiv_zero_apply
    (z : cocycles.{u, v, max v w} X 0) (g₀ : G) :
    ((homogeneousCochains.{u, v, w} X).iCycles 0 (X.cocyclesUniverseEquiv.{w} 0 z)).val g₀ =
      ((homogeneousCochains.{u, v, max v w} X).iCycles 0 z).val g₀ :=
  (congrArg (fun f : C(G, X.V) ↦ f g₀) (X.coe_iCycles_cocyclesUniverseEquiv.{w} 0 z)).trans
    ((X.resolutionXUniverseIso_succ_hom_apply.{w} 0 _ g₀).trans
      (X.resolutionXUniverseIso_zero_hom_apply.{w} _))

/-- In degree one, `cocyclesUniverseEquiv` preserves the values of a homogeneous cocycle on
`G × G`. -/
-- Not a `simp` lemma: `simp` unfolds `(homogeneousCochains _).X 1` inside the implicit type of
-- `Subtype.val` before matching.
theorem iCycles_cocyclesUniverseEquiv_one_apply
    (z : cocycles.{u, v, max v w} X 1) (g₀ g₁ : G) :
    ((homogeneousCochains.{u, v, w} X).iCycles 1 (X.cocyclesUniverseEquiv.{w} 1 z)).val g₀ g₁ =
      ((homogeneousCochains.{u, v, max v w} X).iCycles 1 z).val g₀ g₁ :=
  (congrArg (fun f : C(G, C(G, X.V)) ↦ f g₀ g₁)
    (X.coe_iCycles_cocyclesUniverseEquiv.{w} 1 z)).trans
    ((congrArg (fun f : C(G, X.V) ↦ f g₁)
      (X.resolutionXUniverseIso_succ_hom_apply.{w} 1 _ g₀)).trans
      ((X.resolutionXUniverseIso_succ_hom_apply.{w} 0 _ g₁).trans
        (X.resolutionXUniverseIso_zero_hom_apply.{w} _)))

/-- In degree two, `cocyclesUniverseEquiv` preserves the values of a homogeneous cocycle on
`G × G × G`. -/
theorem iCycles_cocyclesUniverseEquiv_two_apply
    (z : cocycles.{u, v, max v w} X 2) (g₀ g₁ g₂ : G) :
    ((homogeneousCochains.{u, v, w} X).iCycles 2 (X.cocyclesUniverseEquiv.{w} 2 z)).val g₀ g₁ g₂ =
      ((homogeneousCochains.{u, v, max v w} X).iCycles 2 z).val g₀ g₁ g₂ :=
  (congrArg (fun f : C(G, C(G, C(G, X.V))) ↦ f g₀ g₁ g₂)
    (X.coe_iCycles_cocyclesUniverseEquiv.{w} 2 z)).trans
    ((congrArg (fun f : C(G, C(G, X.V)) ↦ f g₁ g₂)
      (X.resolutionXUniverseIso_succ_hom_apply.{w} (1 + 1) _ g₀)).trans
      ((congrArg (fun f : C(G, X.V) ↦ f g₂)
        (X.resolutionXUniverseIso_succ_hom_apply.{w} 1 _ g₁)).trans
        ((X.resolutionXUniverseIso_succ_hom_apply.{w} 0 _ g₂).trans
          (X.resolutionXUniverseIso_zero_hom_apply.{w} _))))

/-- Triviality of `Hⁿ(G, X)` does not depend on the extra carrier universe. -/
theorem subsingleton_continuousCohomology_universe_iff :
    Subsingleton (continuousCohomology.{u, v, max v w} n X) ↔
      Subsingleton (continuousCohomology.{u, v, w} n X) :=
  (X.continuousCohomologyUniverseEquiv.{w} n).toEquiv.subsingleton_congr

/-- Nontriviality of `Hⁿ(G, X)` does not depend on the extra carrier universe. -/
theorem nontrivial_continuousCohomology_universe_iff :
    Nontrivial (continuousCohomology.{u, v, max v w} n X) ↔
      Nontrivial (continuousCohomology.{u, v, w} n X) :=
  (X.continuousCohomologyUniverseEquiv.{w} n).toEquiv.nontrivial_congr

/-- The cardinality of `Hⁿ(G, X)` does not depend on the extra carrier universe. -/
theorem natCard_continuousCohomology_universe_eq :
    Nat.card (continuousCohomology.{u, v, max v w} n X) =
      Nat.card (continuousCohomology.{u, v, w} n X) :=
  Nat.card_congr (X.continuousCohomologyUniverseEquiv.{w} n).toEquiv

end Cohomology

end TopRep

/-! ### Naturality -/

namespace TauCeti.ContinuousCohomology

open TopRep _root_.ContinuousCohomology

section CompatiblePairs

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G H : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {X : TopRep.{max v w} R G} {Y : TopRep.{max v w} R H}
  (φ : H →ₜ* G) (f : TopRep.res (φ : H →* G) X ⟶ Y)

private theorem coind₁ResMap_step {A A' : TopRep.{max v w} R G} {B B' : TopRep.{max v w} R H}
    (hA : A = A') (hB : B = B')
    (g₁ : TopRep.res (φ : H →* G) A ⟶ B) (g₂ : TopRep.res (φ : H →* G) A' ⟶ B')
    (hg : g₁ ≍ g₂) :
    ofHom (ContRepresentation.coind₁ResMap φ g₁.hom) ≍
      ofHom (ContRepresentation.coind₁ResMap φ g₂.hom) := by
  subst hA hB
  cases hg
  rfl

/-- The compatible-pair map on coinduced resolutions at extra universe `max v w` agrees with that
at `w`. -/
theorem resolutionMap_universe_heq :
    ∀ i : ℕ, _root_.ContinuousCohomology.resolutionMap.{u, v, max v w} φ f i ≍
      _root_.ContinuousCohomology.resolutionMap.{u, v, w} φ f i
  | 0 => HEq.rfl
  | i + 1 => by
    rw [resolutionMap_succ, resolutionMap_succ]
    exact coind₁ResMap_step φ (X.resolutionX_universe_eq i) (Y.resolutionX_universe_eq i) _ _
      (resolutionMap_universe_heq i)

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
private theorem invariantsResMap_step {A A' : TopRep.{max v w} R G} {B B' : TopRep.{max v w} R H}
    (hA : A = A') (hB : B = B')
    (g₁ : TopRep.res (φ : H →* G) A ⟶ B) (g₂ : TopRep.res (φ : H →* G) A' ⟶ B')
    (hg : g₁ ≍ g₂) :
    invariantsResMap (φ : H →* G) g₁ ≍ invariantsResMap (φ : H →* G) g₂ := by
  subst hA hB
  cases hg
  rfl

private theorem hom_heq_of_f_heq {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    {K K' L L' : CochainComplex C ℕ} (hK : K = K') (hL : L = L')
    {α : K ⟶ L} {β : K' ⟶ L'} (h : ∀ i, α.f i ≍ β.f i) : α ≍ β := by
  subst hK hL
  exact heq_of_eq (HomologicalComplex.hom_ext α β fun i ↦ eq_of_heq (h i))

/-- The compatible-pair map on homogeneous cochains at extra universe `max v w` agrees with that at
`w`. -/
theorem cochainsMap_universe_heq :
    cochainsMap.{u, v, max v w} φ f ≍ cochainsMap.{u, v, w} φ f :=
  hom_heq_of_f_heq X.homogeneousCochains_universe_eq Y.homogeneousCochains_universe_eq fun i ↦
    invariantsResMap_step φ (X.resolutionX_universe_eq (i + 1)) (Y.resolutionX_universe_eq (i + 1))
      _ _ (resolutionMap_universe_heq φ f (i + 1))

/-- The compatible-pair map on cocycles at extra universe `max v w` agrees with that at `w`. -/
theorem cocyclesMap_universe_heq (n : ℕ) :
    cocyclesMap.{u, v, max v w} φ f n ≍ cocyclesMap.{u, v, w} φ f n := by
  have aux : ∀ {K K' L L' : CochainComplex (TopModuleCat.{max v w, u} R) ℕ},
      K = K' → L = L' → ∀ {α : K ⟶ L} {β : K' ⟶ L'}, α ≍ β →
      HomologicalComplex.cyclesMap α n ≍ HomologicalComplex.cyclesMap β n := by
    rintro K _ L _ rfl rfl α _ ⟨⟩
    rfl
  exact aux X.homogeneousCochains_universe_eq Y.homogeneousCochains_universe_eq
    (cochainsMap_universe_heq φ f)

/-- The compatible-pair map on continuous cohomology at extra universe `max v w` agrees with that
at `w`. -/
theorem map_universe_heq (n : ℕ) :
    _root_.ContinuousCohomology.map.{u, v, max v w} φ f n ≍
      _root_.ContinuousCohomology.map.{u, v, w} φ f n := by
  have aux : ∀ {K K' L L' : CochainComplex (TopModuleCat.{max v w, u} R) ℕ},
      K = K' → L = L' → ∀ {α : K ⟶ L} {β : K' ⟶ L'}, α ≍ β →
      HomologicalComplex.homologyMap α n ≍ HomologicalComplex.homologyMap β n := by
    rintro K _ L _ rfl rfl α _ ⟨⟩
    rfl
  exact aux X.homogeneousCochains_universe_eq Y.homogeneousCochains_universe_eq
    (cochainsMap_universe_heq φ f)

/-- `homogeneousCochainsUniverseIso` is natural with respect to compatible-pair cochain maps. -/
@[reassoc (attr := simp)]
theorem cochainsMap_comp_homogeneousCochainsUniverseIso_hom :
    cochainsMap.{u, v, max v w} φ f ≫ Y.homogeneousCochainsUniverseIso.{w}.hom =
      X.homogeneousCochainsUniverseIso.{w}.hom ≫ cochainsMap.{u, v, w} φ f := by
  have aux : ∀ {K K' L L' : CochainComplex (TopModuleCat.{max v w, u} R) ℕ}
      (hK : K = K') (hL : L = L') {α : K ⟶ L} {β : K' ⟶ L'}, α ≍ β →
      α ≫ eqToHom hL = eqToHom hK ≫ β := by
    rintro K _ L _ rfl rfl α _ ⟨⟩
    simp
  rw [homogeneousCochainsUniverseIso_eq_eqToIso, homogeneousCochainsUniverseIso_eq_eqToIso,
    eqToIso.hom, eqToIso.hom]
  exact aux X.homogeneousCochains_universe_eq Y.homogeneousCochains_universe_eq
    (cochainsMap_universe_heq φ f)

/-- `cocyclesUniverseIso` is natural with respect to compatible-pair maps on cocycles. -/
@[reassoc (attr := simp)]
theorem cocyclesMap_comp_cocyclesUniverseIso_hom (n : ℕ) :
    cocyclesMap.{u, v, max v w} φ f n ≫ (Y.cocyclesUniverseIso.{w} n).hom =
      (X.cocyclesUniverseIso.{w} n).hom ≫ cocyclesMap.{u, v, w} φ f n := by
  simp only [cocyclesUniverseIso_eq_cyclesMapIso, HomologicalComplex.cyclesMapIso_hom, cocyclesMap,
    ← HomologicalComplex.cyclesMap_comp, cochainsMap_comp_homogeneousCochainsUniverseIso_hom]

/-- **`continuousCohomologyUniverseIso` is natural with respect to compatible-pair maps.** -/
@[reassoc (attr := simp)]
theorem map_comp_continuousCohomologyUniverseIso_hom (n : ℕ) :
    _root_.ContinuousCohomology.map.{u, v, max v w} φ f n ≫
        (Y.continuousCohomologyUniverseIso.{w} n).hom =
      (X.continuousCohomologyUniverseIso.{w} n).hom ≫
        _root_.ContinuousCohomology.map.{u, v, w} φ f n := by
  simp only [continuousCohomologyUniverseIso_eq_homologyMapIso,
    HomologicalComplex.homologyMapIso_hom, _root_.ContinuousCohomology.map,
    ← HomologicalComplex.homologyMap_comp, cochainsMap_comp_homogeneousCochainsUniverseIso_hom]

/-- On elements, `continuousCohomologyUniverseEquiv` commutes with compatible-pair maps. -/
theorem continuousCohomologyUniverseEquiv_map_apply (n : ℕ)
    (x : continuousCohomology.{u, v, max v w} n X) :
    Y.continuousCohomologyUniverseEquiv.{w} n
        (_root_.ContinuousCohomology.map.{u, v, max v w} φ f n x) =
      _root_.ContinuousCohomology.map.{u, v, w} φ f n
        (X.continuousCohomologyUniverseEquiv.{w} n x) :=
  congr($(map_comp_continuousCohomologyUniverseIso_hom.{w} φ f n) x)

end CompatiblePairs

section NamedMaps

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **`continuousCohomologyUniverseIso` is natural in equivariant coefficient maps.** -/
@[reassoc (attr := simp)]
theorem coeffMap_comp_continuousCohomologyUniverseIso_hom
    {X Y : TopRep.{max v w} R G} (f : X ⟶ Y) (n : ℕ) :
    coeffMap.{u, v, max v w} f n ≫ (Y.continuousCohomologyUniverseIso.{w} n).hom =
      (X.continuousCohomologyUniverseIso.{w} n).hom ≫ coeffMap.{u, v, w} f n := by
  rw [coeffMap_def, coeffMap_def]
  exact map_comp_continuousCohomologyUniverseIso_hom.{w} (ContinuousMonoidHom.id G) f n

/-- On elements, `continuousCohomologyUniverseEquiv` commutes with equivariant coefficient maps. -/
theorem continuousCohomologyUniverseEquiv_coeffMap_apply
    {X Y : TopRep.{max v w} R G} (f : X ⟶ Y) (n : ℕ)
    (x : continuousCohomology.{u, v, max v w} n X) :
    Y.continuousCohomologyUniverseEquiv.{w} n (coeffMap.{u, v, max v w} f n x) =
      coeffMap.{u, v, w} f n (X.continuousCohomologyUniverseEquiv.{w} n x) :=
  congr($(coeffMap_comp_continuousCohomologyUniverseIso_hom.{w} f n) x)

/-- `continuousCohomologyUniverseIso` commutes with subgroup restriction. -/
@[reassoc (attr := simp)]
theorem res_comp_continuousCohomologyUniverseIso_hom (S : Subgroup G)
    (X : TopRep.{max v w} R G) (n : ℕ) :
    res.{u, v, max v w} S X n ≫
        ((TopRep.res (S.subtype : S →* G) X).continuousCohomologyUniverseIso.{w} n).hom =
      (X.continuousCohomologyUniverseIso.{w} n).hom ≫ res.{u, v, w} S X n := by
  rw [res_def, res_def]
  exact map_comp_continuousCohomologyUniverseIso_hom.{w}
    (ContinuousMonoidHom.subgroupSubtype S) (𝟙 _) n

/-- `continuousCohomologyUniverseIso` commutes with quotient inflation. -/
@[reassoc (attr := simp)]
theorem infl_comp_continuousCohomologyUniverseIso_hom (N : Subgroup G) [N.Normal]
    (X : TopRep.{max v w} R G) (n : ℕ) :
    infl.{u, v, max v w} N X n ≫ (X.continuousCohomologyUniverseIso.{w} n).hom =
      ((TopRep.quotientToInvariants X N).continuousCohomologyUniverseIso.{w} n).hom ≫
        infl.{u, v, w} N X n := by
  rw [infl_def, infl_def]
  exact map_comp_continuousCohomologyUniverseIso_hom.{w}
    (Subgroup.quotientMkContinuousMonoidHom N) _ n

variable (R G) in
/-- **The continuous cohomology functor does not depend on the extra carrier universe**: the
natural isomorphism
`continuousCohomologyFunctor.{u, v, max v w} R G n ≅ continuousCohomologyFunctor.{u, v, w} R G n`.
-/
noncomputable def continuousCohomologyFunctorUniverseIso (n : ℕ) :
    continuousCohomologyFunctor.{u, v, max v w} R G n ≅
      continuousCohomologyFunctor.{u, v, w} R G n :=
  NatIso.ofComponents (fun X ↦ X.continuousCohomologyUniverseIso.{w} n)
    fun f ↦ coeffMap_comp_continuousCohomologyUniverseIso_hom.{w} f n

/-- Componentwise forward map of `continuousCohomologyFunctorUniverseIso`. -/
@[simp]
theorem continuousCohomologyFunctorUniverseIso_hom_app
    (X : TopRep.{max v w} R G) (n : ℕ) :
    (continuousCohomologyFunctorUniverseIso.{w} R G n).hom.app X =
      (X.continuousCohomologyUniverseIso.{w} n).hom :=
  (rfl)

/-- Componentwise inverse map of `continuousCohomologyFunctorUniverseIso`. -/
@[simp]
theorem continuousCohomologyFunctorUniverseIso_inv_app
    (X : TopRep.{max v w} R G) (n : ℕ) :
    (continuousCohomologyFunctorUniverseIso.{w} R G n).inv.app X =
      (X.continuousCohomologyUniverseIso.{w} n).inv :=
  (rfl)

variable (R G) in
/-- When `w = v`, `continuousCohomologyFunctorUniverseIso` is the identity natural isomorphism. -/
theorem continuousCohomologyFunctorUniverseIso_self (n : ℕ) :
    continuousCohomologyFunctorUniverseIso.{v} R G n = Iso.refl _ :=
  Iso.ext <| NatTrans.ext <| funext fun X ↦
    (continuousCohomologyFunctorUniverseIso_hom_app X n).trans <|
      by rw [continuousCohomologyUniverseIso_self]; rfl

end NamedMaps

section DegreeZero

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : TopRep.{max v w} R G)

/-- In degree zero, `continuousCohomologyUniverseIso` commutes with `ContinuousCohomology.zeroIso`
identifying `H⁰_cont(G, X)` with the invariants `X^G`. -/
@[reassoc (attr := simp)]
theorem continuousCohomologyUniverseIso_zero_hom_comp_zeroIso_hom :
    (X.continuousCohomologyUniverseIso.{w} 0).hom ≫ (zeroIso.{u, v, w} X).hom =
      (zeroIso.{u, v, max v w} X).hom := by
  rw [← cancel_epi (π.{u, v, max v w} X 0), π_comp_continuousCohomologyUniverseIso_hom_assoc]
  ext σ
  simp only [ConcreteCategory.comp_apply, ← TopRep.cocyclesUniverseEquiv_apply]
  exact (coe_zeroIso_hom_π X (X.cocyclesUniverseEquiv.{w} 0 σ)).trans
    ((X.iCycles_cocyclesUniverseEquiv_zero_apply.{w} σ 1).trans (coe_zeroIso_hom_π X σ).symm)

/-- In degree zero, `ContinuousCohomology.zeroIso.inv` commutes with
`continuousCohomologyUniverseIso`. -/
@[reassoc (attr := simp)]
theorem zeroIso_inv_comp_continuousCohomologyUniverseIso_zero_hom :
    (zeroIso.{u, v, max v w} X).inv ≫ (X.continuousCohomologyUniverseIso.{w} 0).hom =
      (zeroIso.{u, v, w} X).inv := by
  rw [Iso.inv_comp_eq, Iso.eq_comp_inv, continuousCohomologyUniverseIso_zero_hom_comp_zeroIso_hom]

/-- **`continuousCohomologyUniverseEquiv` preserves degree-zero classes of invariant vectors.** -/
@[simp]
theorem continuousCohomologyUniverseEquiv_degreeZeroClass
    (x : X.V) (hx : ∀ g : G, X.ρ g x = x) :
    X.continuousCohomologyUniverseEquiv.{w} 0
        (degreeZeroClass.{u, v, max v w} X x hx) =
      degreeZeroClass.{u, v, w} X x hx := by
  apply (zeroIso.{u, v, w} X).toContinuousLinearEquiv.injective
  refine Subtype.ext ?_
  have h := congr($(continuousCohomologyUniverseIso_zero_hom_comp_zeroIso_hom.{w} X)
    (degreeZeroClass.{u, v, max v w} X x hx))
  have hval : (((zeroIso.{u, v, w} X).hom
      (X.continuousCohomologyUniverseEquiv.{w} 0 (degreeZeroClass.{u, v, max v w} X x hx))) : X.V) =
      (((zeroIso.{u, v, max v w} X).hom (degreeZeroClass.{u, v, max v w} X x hx)) : X.V) :=
    congrArg Subtype.val h
  exact hval.trans ((coe_zeroIso_hom_degreeZeroClass x hx).trans
    (coe_zeroIso_hom_degreeZeroClass x hx).symm)

end DegreeZero

end TauCeti.ContinuousCohomology
