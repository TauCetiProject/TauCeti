/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.RingTheory.Flat.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Abelian
public import TauCeti.Algebra.Coalgebra.Comodule.Cohomology.Basic
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# The long exact sequence in Hochschild cohomology of comodules

Let `H` be a bialgebra over a commutative ring `R`, flat as an `R`-module. A short exact sequence
`0 → M₁ → M₂ → M₃ → 0` of right `H`-comodules gives a short exact sequence of Hochschild complexes
`0 → M₁ ⊗ H^⊗• → M₂ ⊗ H^⊗• → M₃ ⊗ H^⊗• → 0`, and hence a long exact sequence
`⋯ → Hⁱ(H, M₂) → Hⁱ(H, M₃) → Hⁱ⁺¹(H, M₁) → Hⁱ⁺¹(H, M₂) → ⋯`.

Right exactness of the tensor product makes `M ↦ M ⊗ H^⊗n` preserve surjections and exactness in
the middle for any `H`; flatness of `H` is used only to keep the first map injective. This file
proves these degreewise statements for unbundled comodule morphisms, assembles the Hochschild
complexes into a functor on the category of comodules, and specializes Mathlib's long exact
homology sequence to it. The connecting map is described on cocycles (`δ_apply`) and, in degree
zero, on invariants (`δ_zero_apply`): an invariant `z ∈ M₃ᴴ` with a preimage `y ∈ M₂` is sent to
the class of the unique `x ∈ M₁ ⊗ H` whose image is `ρ(y) - y ⊗ 1`; it vanishes exactly when `z`
lifts to an invariant of `M₂` (`δ_zero_eq_zero_iff`). When `H = O(G)` is the coordinate algebra
of a flat affine group scheme, this is the long exact sequence of rational cohomology
(Jantzen, I.4.2 and I.4.14–4.16).

The comodules live in the universe of `H`, as in `cochainComplex`. The layout of the long exact
sequence API follows Mathlib's group-cohomology version,
`Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence`.

## Main definitions

* `TauCeti.Comodule.Cohomology.cochainComplexFunctor`: the Hochschild complex as a functor on
  `ComoduleCat R H`.
* `TauCeti.Comodule.Cohomology.cohomologyFunctor`: the functor `M ↦ Hⁿ(H, M)`.
* `TauCeti.Comodule.Cohomology.δ`: the connecting map `Hⁱ(H, M₃) ⟶ Hʲ(H, M₁)`, for `i + 1 = j`.

## Main results

* `TauCeti.Comodule.Cohomology.cochainsMap_exact`,
  `TauCeti.Comodule.Cohomology.cochainsMap_surjective`,
  `TauCeti.Comodule.Cohomology.cochainsMap_injective`: degreewise exactness of the cochain maps.
* `TauCeti.Comodule.Cohomology.map_cochainComplexFunctor_shortExact`: a short exact sequence of
  comodules gives a short exact sequence of Hochschild complexes.
* `TauCeti.Comodule.Cohomology.mapShortComplex₁_exact`,
  `TauCeti.Comodule.Cohomology.mapShortComplex₂_exact`,
  `TauCeti.Comodule.Cohomology.mapShortComplex₃_exact`: exactness of the long exact sequence at
  each of its three kinds of terms.
* `TauCeti.Comodule.Cohomology.δ_naturality`: naturality of the connecting map.
* `TauCeti.Comodule.Cohomology.δ_apply`, `TauCeti.Comodule.Cohomology.δ_zero_apply`: the
  connecting map on cocycles, and in degree zero on invariants.
* `TauCeti.Comodule.Cohomology.δ_zero_eq_zero_iff`: an invariant of `M₃` lifts to an invariant of
  `M₂` exactly when its connecting image in `H¹(H, M₁)` vanishes.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., Part I, §§4.2, 4.14–4.16.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.Comodule.Cohomology

universe u v

variable {R : Type u} [CommRing R] {H : Type v} [Ring H] [Bialgebra R H]

/-! ### Degreewise exactness of the cochain maps -/

section Degreewise

variable {M₁ M₂ M₃ : Type v} [AddCommGroup M₁] [Module R M₁] [Comodule R H M₁]
  [AddCommGroup M₂] [Module R M₂] [Comodule R H M₂]
  [AddCommGroup M₃] [Module R M₃] [Comodule R H M₃]

/-- A surjective comodule morphism induces surjections on Hochschild cochains. -/
theorem cochainsMap_surjective {g : Hom R H M₂ M₃} (hg : Function.Surjective g) (n : ℕ) :
    Function.Surjective (cochainsMap g n) := by
  induction n with
  | zero => rw [cochainsMap_zero]; exact hg
  | succ n ih => rw [cochainsMap_succ]; exact LinearMap.rTensor_surjective H ih

/-- An injective comodule morphism induces injections on Hochschild cochains, when `H` is flat. -/
theorem cochainsMap_injective [Module.Flat R H] {f : Hom R H M₁ M₂}
    (hf : Function.Injective f) (n : ℕ) : Function.Injective (cochainsMap f n) := by
  induction n with
  | zero => rw [cochainsMap_zero]; exact hf
  | succ n ih => rw [cochainsMap_succ]; exact Module.Flat.rTensor_preserves_injective_linearMap _ ih

/-- A sequence `M₁ → M₂ → M₃ → 0` of comodules that is exact at `M₂` stays exact at
`M₂ ⊗ H^⊗n` after passing to Hochschild cochains. -/
theorem cochainsMap_exact {f : Hom R H M₁ M₂} {g : Hom R H M₂ M₃} (hfg : Function.Exact f g)
    (hg : Function.Surjective g) (n : ℕ) :
    Function.Exact (cochainsMap f n) (cochainsMap g n) := by
  induction n with
  | zero => rw [cochainsMap_zero, cochainsMap_zero]; exact hfg
  | succ n ih =>
    rw [cochainsMap_succ, cochainsMap_succ]
    exact rTensor_exact H ih (cochainsMap_surjective hg n)

/-- For an injective comodule morphism `f : M₁ → M₂` over a flat `H`, an `(i + 1)`-cochain `x` of
`M₁` whose image in `M₂` is the differential of an `i`-cochain is a cocycle. -/
theorem d_eq_zero_of_cochainsMap_eq_d [Module.Flat R H] {f : Hom R H M₁ M₂}
    (hf : Function.Injective f) {i : ℕ} {y : cochains R H M₂ i} {x : cochains R H M₁ (i + 1)}
    (hx : cochainsMap f (i + 1) x = d R H M₂ i y) :
    d R H M₁ (i + 1) x = 0 := by
  apply cochainsMap_injective hf (i + 2)
  have h := LinearMap.congr_fun (d_comp_cochainsMap f (i + 1)) x
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hx, d_d] at h
  rw [map_zero]
  exact h.symm

/-- In degree zero, the image of `x ∈ M₁ ⊗ H` is the differential of `y ∈ M₂` exactly when
`(f ⊗ id) x = ρ(y) - y ⊗ 1`. -/
theorem cochainsMap_one_eq_d_zero_iff {f : Hom R H M₁ M₂} {x : M₁ ⊗[R] H} {y : M₂} :
    cochainsMap f 1 x = d R H M₂ 0 y ↔
      f.toLinearMap.rTensor H x = Comodule.coact (R := R) (C := H) y - y ⊗ₜ[R] 1 := by
  rw [d_zero_apply, cochainsMap_succ, cochainsMap_zero]

end Degreewise

/-! ### The Hochschild complex as a functor on comodules -/

variable (R H) in
/-- The Hochschild complex `M ↦ M ⊗ H^⊗•`, as a functor on the category of right `H`-comodules.
A comodule morphism acts on the first tensor factor. -/
-- Exposed so that the cohomology of the image of a comodule `M` is, by definition, the Hochschild
-- cohomology `cohomology R H M`, in the types of the connecting maps.
@[expose, simps]
noncomputable def cochainComplexFunctor :
    ComoduleCat.{u, v, v} R H ⥤ CochainComplex (ModuleCat.{v} R) ℕ where
  obj M := cochainComplex R H M
  map f := cochainComplexMap f
  map_id _ := cochainComplexMap_id
  map_comp f g := cochainComplexMap_comp g f

/-- The Hochschild complex functor is additive: a sum of comodule morphisms acts on cochains as the
sum of the induced maps. -/
instance : (cochainComplexFunctor R H).Additive where
  map_add {_ _ f g} := by
    rw [cochainComplexFunctor_map, cochainComplexFunctor_map, cochainComplexFunctor_map]
    exact cochainComplexMap_add f g

/-- In degree `n`, the Hochschild complex functor sends a comodule morphism to its induced map on
cochains. -/
theorem hom_cochainComplexFunctor_map_f {M N : ComoduleCat.{u, v, v} R H} (f : M ⟶ N) (n : ℕ) :
    (((cochainComplexFunctor R H).map f).f n).hom = cochainsMap f n :=
  congrArg ModuleCat.Hom.hom (cochainComplexMap_f f n)

/-- The differential of the image of a comodule under the Hochschild complex functor is the
Hochschild differential. -/
@[simp]
theorem hom_cochainComplexFunctor_obj_d (M : ComoduleCat.{u, v, v} R H) (n : ℕ) :
    (((cochainComplexFunctor R H).obj M).d n (n + 1)).hom = d R H M n :=
  congrArg ModuleCat.Hom.hom (cochainComplex_d_succ R H M n)

variable (R H) in
/-- The Hochschild cohomology `M ↦ Hⁿ(H, M)`, as a functor on the category of right
`H`-comodules. -/
noncomputable abbrev cohomologyFunctor (n : ℕ) : ComoduleCat.{u, v, v} R H ⥤ ModuleCat.{v} R :=
  cochainComplexFunctor R H ⋙ HomologicalComplex.homologyFunctor _ _ n

/-- The value of the Hochschild cohomology functor is the Hochschild cohomology. -/
theorem cohomologyFunctor_obj (n : ℕ) (M : ComoduleCat.{u, v, v} R H) :
    (cohomologyFunctor R H n).obj M = cohomology R H M n :=
  (rfl)

/-! ### The long exact sequence -/

section LongExactSequence

variable [Module.Flat R H] {X : ShortComplex (ComoduleCat.{u, v, v} R H)} (hX : X.ShortExact)

include hX

/-- A short exact sequence of comodules over a flat bialgebra gives a short exact sequence of
Hochschild complexes. -/
theorem map_cochainComplexFunctor_shortExact :
    (X.map (cochainComplexFunctor R H)).ShortExact := by
  have hfg : Function.Exact X.f X.g := X.comoduleCat_exact_iff_function_exact.1 hX.exact
  have hg : Function.Surjective X.g := hX.comoduleCat_surjective_g
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
    ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_ <;>
  dsimp only [ShortComplex.map_f, ShortComplex.map_g, HomologicalComplex.eval_map] <;>
  simp only [hom_cochainComplexFunctor_map_f]
  · exact cochainsMap_exact hfg hg n
  · exact cochainsMap_injective hX.comoduleCat_injective_f n
  · exact cochainsMap_surjective hg n

open HomologicalComplex.HomologySequence

/-- The short complex `Hⁱ(H, M₃) ⟶ Hʲ(H, M₁) ⟶ Hʲ(H, M₂)` attached to a short exact sequence
`0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of comodules, for `i + 1 = j`. -/
noncomputable abbrev mapShortComplex₁ {i j : ℕ} (hij : i + 1 = j) :=
  (snakeInput (map_cochainComplexFunctor_shortExact hX) _ _ hij).L₂'

omit [Module.Flat R H] hX in
variable (X) in
/-- The short complex `Hⁱ(H, M₁) ⟶ Hⁱ(H, M₂) ⟶ Hⁱ(H, M₃)` attached to a short complex
`M₁ ⟶ M₂ ⟶ M₃` of comodules. -/
noncomputable abbrev mapShortComplex₂ (i : ℕ) :=
  X.map (cohomologyFunctor R H i)

/-- The short complex `Hⁱ(H, M₂) ⟶ Hⁱ(H, M₃) ⟶ Hʲ(H, M₁)` attached to a short exact sequence
`0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of comodules, for `i + 1 = j`. -/
noncomputable abbrev mapShortComplex₃ {i j : ℕ} (hij : i + 1 = j) :=
  (snakeInput (map_cochainComplexFunctor_shortExact hX) _ _ hij).L₁'

/-- Exactness of `Hⁱ(H, M₃) ⟶ Hʲ(H, M₁) ⟶ Hʲ(H, M₂)`. -/
theorem mapShortComplex₁_exact {i j : ℕ} (hij : i + 1 = j) :
    (mapShortComplex₁ hX hij).Exact :=
  (map_cochainComplexFunctor_shortExact hX).homology_exact₁ i j hij

/-- Exactness of `Hⁱ(H, M₁) ⟶ Hⁱ(H, M₂) ⟶ Hⁱ(H, M₃)`. -/
theorem mapShortComplex₂_exact (i : ℕ) : (mapShortComplex₂ X i).Exact :=
  (map_cochainComplexFunctor_shortExact hX).homology_exact₂ i

/-- Exactness of `Hⁱ(H, M₂) ⟶ Hⁱ(H, M₃) ⟶ Hʲ(H, M₁)`. -/
theorem mapShortComplex₃_exact {i j : ℕ} (hij : i + 1 = j) :
    (mapShortComplex₃ hX hij).Exact :=
  (map_cochainComplexFunctor_shortExact hX).homology_exact₃ i j hij

/-- The connecting map `Hⁱ(H, M₃) ⟶ Hʲ(H, M₁)` attached to a short exact sequence
`0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of comodules, for `i + 1 = j`. -/
noncomputable abbrev δ (i j : ℕ) (hij : i + 1 = j) :
    cohomology R H X.X₃ i ⟶ cohomology R H X.X₁ j :=
  (map_cochainComplexFunctor_shortExact hX).δ i j hij

open Limits in
/-- The connecting map `Hⁿ(H, M₃) ⟶ Hⁿ⁺¹(H, M₁)` is surjective when `Hⁿ⁺¹(H, M₂)` vanishes. -/
theorem epi_δ_of_isZero (n : ℕ) (h : IsZero (cohomology R H X.X₂ (n + 1))) :
    Epi (δ hX n (n + 1) rfl) :=
  ShortComplex.SnakeInput.epi_δ _ h

open Limits in
/-- The connecting map `Hⁿ(H, M₃) ⟶ Hⁿ⁺¹(H, M₁)` is injective when `Hⁿ(H, M₂)` vanishes. -/
theorem mono_δ_of_isZero (n : ℕ) (h : IsZero (cohomology R H X.X₂ n)) :
    Mono (δ hX n (n + 1) rfl) :=
  ShortComplex.SnakeInput.mono_δ _ h

open Limits in
/-- The connecting map `Hⁿ(H, M₃) ⟶ Hⁿ⁺¹(H, M₁)` is an isomorphism when `Hⁿ(H, M₂)` and
`Hⁿ⁺¹(H, M₂)` vanish. -/
theorem isIso_δ_of_isZero (n : ℕ) (h : IsZero (cohomology R H X.X₂ n))
    (hs : IsZero (cohomology R H X.X₂ (n + 1))) :
    IsIso (δ hX n (n + 1) rfl) :=
  ShortComplex.SnakeInput.isIso_δ _ h hs

omit hX in
/-- The connecting map is natural in morphisms of short exact sequences of comodules. -/
theorem δ_naturality {X₁ X₂ : ShortComplex (ComoduleCat.{u, v, v} R H)} (hX₁ : X₁.ShortExact)
    (hX₂ : X₂.ShortExact) (F : X₁ ⟶ X₂) (i j : ℕ) (hij : i + 1 = j) :
    δ hX₁ i j hij ≫ (cohomologyFunctor R H j).map F.τ₁ =
      (cohomologyFunctor R H i).map F.τ₃ ≫ δ hX₂ i j hij :=
  HomologicalComplex.HomologySequence.δ_naturality
    ((cochainComplexFunctor R H).mapShortComplex.map F)
    (map_cochainComplexFunctor_shortExact hX₁) (map_cochainComplexFunctor_shortExact hX₂) i j hij

end LongExactSequence

/-! ### The connecting map on cocycles -/

section Cocycles

variable [Module.Flat R H] {X : ShortComplex (ComoduleCat.{u, v, v} R H)} (hX : X.ShortExact)

include hX

/-- The connecting map on cocycles. Let `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` be a short exact sequence of
comodules, `z` an `i`-cocycle of `M₃`, `y` an `i`-cochain of `M₂` lifting `z`, and `x` an
`(i + 1)`-cochain of `M₁` whose image is the differential of `y`. Then `x` is a cocycle, and the
connecting map sends the class of `z` to the class of `x`. -/
theorem δ_apply {i : ℕ} (z : cochains R H X.X₃ i) (hz : d R H X.X₃ i z = 0)
    (y : cochains R H X.X₂ i) (hy : cochainsMap X.g i y = z)
    (x : cochains R H X.X₁ (i + 1)) (hx : cochainsMap X.f (i + 1) x = d R H X.X₂ i y) :
    (δ hX i (i + 1) rfl).hom (((cochainComplex R H X.X₃).homologyπ i).hom (cocyclesMk z hz)) =
      ((cochainComplex R H X.X₁).homologyπ (i + 1)).hom
        (cocyclesMk x (d_eq_zero_of_cochainsMap_eq_d hX.comoduleCat_injective_f hx)) := by
  rw [cocyclesMk_eq_cyclesMk, cocyclesMk_eq_cyclesMk]
  -- Mathlib's `ShortExact.δ_apply` is stated through `forget₂ (ModuleCat R) Ab`. On `ModuleCat`,
  -- `(forget₂ _ Ab).map f` is `AddCommGrpCat.ofHom f.hom` by definition (`ModuleCat.forget₂_map`),
  -- so its conclusion and side conditions agree with the `.hom` forms here up to that unfolding.
  -- Rewriting with `ModuleCat.forget₂_map` instead fails, since the cycles in the statement depend
  -- on the rewritten maps.
  exact (map_cochainComplexFunctor_shortExact hX).δ_apply i (i + 1) rfl z _ y
    (by
      simp only [ShortComplex.map_X₃, ModuleCat.forget₂_obj, ShortComplex.map_X₂,
        ShortComplex.map_g, cochainComplexFunctor_map, cochainComplexMap_f]
      exact hy) x
    (by
      simp only [ShortComplex.map_X₂, ModuleCat.forget₂_obj, ShortComplex.map_X₁,
        ShortComplex.map_f, cochainComplexFunctor_map, cochainComplexMap_f, ModuleCat.forget₂_map,
        hom_cochainComplexFunctor_obj_d, ConcreteCategory.hom_ofHom]
      exact hx) (i + 2) (by simp)

/-- The connecting map in degree zero. Let `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` be a short exact sequence of
comodules, `z ∈ M₃ᴴ` an invariant vector, `y ∈ M₂` a preimage of `z`, and `x ∈ M₁ ⊗ H` the
element whose image in `M₂ ⊗ H` is `ρ(y) - y ⊗ 1`. Then `x` is a `1`-cocycle, and the connecting
map `H⁰(H, M₃) ⟶ H¹(H, M₁)` sends `z` to its class. -/
theorem δ_zero_apply (z : fixedSubcomodule R H X.X₃) (y : X.X₂) (hy : X.g y = z)
    (x : X.X₁ ⊗[R] H)
    (hx : X.f.toLinearMap.rTensor H x = Comodule.coact (R := R) (C := H) y - y ⊗ₜ[R] 1) :
    (δ hX 0 1 rfl).hom ((cohomologyZeroIso R H X.X₃).inv.hom z) =
      ((cochainComplex R H X.X₁).homologyπ 1).hom
        (cocyclesMk (n := 1) x (d_eq_zero_of_cochainsMap_eq_d (i := 0)
          hX.comoduleCat_injective_f (cochainsMap_one_eq_d_zero_iff.2 hx))) := by
  rw [← homologyπ_cocyclesMk_zero]
  exact δ_apply hX (i := 0) _ _ y (by rw [cochainsMap_zero]; exact hy) x
    (cochainsMap_one_eq_d_zero_iff.2 hx)

/-- An invariant vector of `M₃` lifts to an invariant vector of `M₂` exactly when its image under
the connecting map `H⁰(H, M₃) ⟶ H¹(H, M₁)` vanishes. -/
theorem δ_zero_eq_zero_iff (z : fixedSubcomodule R H X.X₃) :
    (δ hX 0 1 rfl).hom ((cohomologyZeroIso R H X.X₃).inv.hom z) = 0 ↔
      ∃ y : fixedSubcomodule R H X.X₂, X.g.fixedMap y = z := by
  have hexact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (mapShortComplex₃_exact hX (i := 0) (j := 1) rfl)
  -- The first map of `mapShortComplex₃` is the map `H⁰(H, M₂) ⟶ H⁰(H, M₃)` induced by `g`, which
  -- `cohomologyZeroIso` identifies with `g.fixedMap` on invariants.
  have hnat (b : cohomology R H X.X₂ 0) :
      (cohomologyZeroIso R H X.X₃).hom.hom
          ((HomologicalComplex.homologyMap (cochainComplexMap X.g) 0).hom b) =
        X.g.fixedMap ((cohomologyZeroIso R H X.X₂).hom.hom b) :=
    congr(ModuleCat.Hom.hom $(homologyMap_comp_cohomologyZeroIso_hom (R := R) (H := H) X.g) b)
  refine (hexact ((cohomologyZeroIso R H X.X₃).inv.hom z)).trans ⟨?_, ?_⟩
  · rintro ⟨b, hb⟩
    refine ⟨(cohomologyZeroIso R H X.X₂).hom.hom b, ?_⟩
    refine (hnat b).symm.trans ?_
    exact (congrArg (cohomologyZeroIso R H X.X₃).hom.hom hb).trans
      ((cohomologyZeroIso R H X.X₃).inv_hom_id_apply z)
  · rintro ⟨y, rfl⟩
    refine ⟨(cohomologyZeroIso R H X.X₂).inv.hom y, ?_⟩
    apply (cohomologyZeroIso R H X.X₃).toLinearEquiv.injective
    refine (hnat _).trans ?_
    rw [Iso.inv_hom_id_apply]
    exact ((cohomologyZeroIso R H X.X₃).inv_hom_id_apply _).symm

end Cocycles

end TauCeti.Comodule.Cohomology
