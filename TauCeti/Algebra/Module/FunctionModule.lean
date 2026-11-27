/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Length
public import TauCeti.LinearAlgebra.Pi.Detection
import TauCeti.LinearAlgebra.Quotient.Pi.Generators
import TauCeti.RingTheory.DiscreteValuationRing.MatlisDual
import TauCeti.RingTheory.Length

/-!
# Modules of functions with values in `O ⧸ (p)`

Let `O` be a commutative ring and `N ⊆ F` a submodule over a ring `R` acting on `F` compatibly
with `O`. Fix an `O`-linear map `Φ : V → F`, a map `z : G → V` from a set `G`, and `p ∈ O`. The
*module of functions* of `N` is the `O`-module of the functions `g ↦ Ψ (z g)` on `G`, for the
`O`-linear `Ψ : V → O ⧸ (p)` vanishing on `Φ⁻¹(N)`: the image of `Hom_O(V ⧸ Φ⁻¹(N), O ⧸ (p))`
under evaluation at the classes of the `z g` (`Submodule.toFunctionModule`). When `G` is a group
and `N` contains cocycle relations, these functions are cocycles with values in `O ⧸ (p)`; the
definition uses no structure on `G`, so it stands in for a module of cocycles over any group.

Over a principal ideal domain, when `p ≠ 0` kills `V ⧸ Φ⁻¹(N)`, duality with values in `O ⧸ (p)`
(`IsDiscreteValuationRing.length_linearMap_quotient_span_singleton_right`) turns the module of
functions into a measure of the relations. If `N ⊆ O^ι` and the `Φ (z (gen i))` are congruent to
the standard basis vectors modulo `N`, the classes of the `z (gen i)` span `V ⧸ Φ⁻¹(N)`
(`Submodule.span_range_mkQ_comap_eq_top`), so the module of functions has the length of
`O^ι ⧸ N` and is detected by the `gen i`; over a discrete valuation ring, the colength of `N` is
then bounded by a length modulo `C`-torsion. For any `A ⊆ G`, the image in `F ⧸ N` of the
relations `Φ (z a)`, `a ∈ A`, is no longer than the quotient of the module of functions by its
members vanishing on `A`, because linear maps to `O ⧸ (p)` extend
(`IsDiscreteValuationRing.exists_linearMap_quotient_span_singleton_comp_eq`).

## Main definitions

* `Submodule.functionModule N Φ z p`: the module of functions of `N`.
* `Submodule.toFunctionModule N Φ z p`: evaluation at the classes of the `z g`, from
  `Hom_O(V ⧸ Φ⁻¹(N), O ⧸ (p))` onto the module of functions.

## Main results

* `Submodule.mem_functionModule`, `Submodule.functionModule_le_functionModule`: membership, and
  more relations give fewer functions.
* `Submodule.toFunctionModule_surjective`, `Submodule.apply_mkQ_mem_functionModule`: evaluation
  is onto the module of functions.
* `Submodule.smul_quotient_comap_eq_zero`: if `Φ (p • v) ∈ N` for all `v`, then `p` kills
  `V ⧸ Φ⁻¹(N)`.
* `Submodule.functionModule_isDetectedBy_range`, `Submodule.length_functionModule`: for a module
  of relations in `O^ι` in which `Φ (z (gen i)) ≡ e_i`, the module of functions is detected by the
  `gen i` and, over a principal ideal domain, has the length of `O^ι ⧸ N`.
* `Submodule.length_quotient_le_length_functionModule_quotient_add`: over a discrete valuation
  ring, the colength of such an `N` is at most the length of its module of functions modulo
  `C`-torsion plus `#ι v(C)`.
* `Submodule.length_map_mkQ_span_image_le`: over a principal ideal domain, the image of the
  relations `Φ (z a)`, `a ∈ A`, is no longer than the module of functions modulo its members
  vanishing on `A`.

## Provenance

These modules of functions carry the duality step of the method of
`New.Selmer.exists_mul_prod_X_mem_fittingIdeal` in grh-lean (https://github.com/lsernau/grh-lean,
file `src/New/Congruences/FirstOrder/FittingBlock.lean`, Apache 2.0, Copyright 2026 Anthropic,
PBC), used in `TauCeti.RingTheory.FittingIdeal.TriangleCost`; no grh-lean code was read or copied.
-/

public section

noncomputable section

open IsDiscreteValuationRing Module

namespace Submodule

section FunctionModule

variable {O R F V G : Type*} [CommRing O] [Semiring R] [AddCommMonoid F] [Module O F]
  [Module R F] [SMul O R] [IsScalarTower O R F] [AddCommGroup V] [Module O V]

/-- The *module of functions* of a submodule `N ⊆ F` along `Φ : V → F` and `z : G → V`, with
values in `O ⧸ (p)`: the `O`-module of the functions `g ↦ Ψ (z g)` on `G`, for the `O`-linear maps
`Ψ : V → O ⧸ (p)` vanishing on `Φ⁻¹(N)` (`Submodule.mem_functionModule`). -/
def functionModule (N : Submodule R F) (Φ : V →ₗ[O] F) (z : G → V) (p : O) :
    Submodule O (G → O ⧸ Ideal.span {p}) :=
  LinearMap.range <| LinearMap.pi fun g ↦
    LinearMap.applyₗ (((N.restrictScalars O).comap Φ).mkQ (z g))

/-- Evaluation at the classes of the `z g`: the map onto the module of functions of `N` sending an
`O`-linear `Ψ : V ⧸ Φ⁻¹(N) → O ⧸ (p)` to the function `g ↦ Ψ (z g)`. -/
def toFunctionModule (N : Submodule R F) (Φ : V →ₗ[O] F) (z : G → V) (p : O) :
    (V ⧸ (N.restrictScalars O).comap Φ →ₗ[O] O ⧸ Ideal.span {p}) →ₗ[O]
      N.functionModule Φ z p :=
  LinearMap.rangeRestrict _

variable {N : Submodule R F} {Φ : V →ₗ[O] F} {z : G → V} {p : O}

@[simp]
theorem coe_toFunctionModule_apply (Ψ : V ⧸ (N.restrictScalars O).comap Φ →ₗ[O] O ⧸ Ideal.span {p})
    (g : G) :
    (N.toFunctionModule Φ z p Ψ : G → O ⧸ Ideal.span {p}) g =
      Ψ (((N.restrictScalars O).comap Φ).mkQ (z g)) := by
  rfl

/-- Evaluation at the classes of the `z g` is onto the module of functions. -/
theorem toFunctionModule_surjective : Function.Surjective (N.toFunctionModule Φ z p) :=
  LinearMap.surjective_rangeRestrict _

/-- Each `O`-linear `Ψ : V ⧸ Φ⁻¹(N) → O ⧸ (p)` gives the member `g ↦ Ψ (z g)` of the module of
functions of `N`. -/
theorem apply_mkQ_mem_functionModule
    (Ψ : V ⧸ (N.restrictScalars O).comap Φ →ₗ[O] O ⧸ Ideal.span {p}) :
    (fun g ↦ Ψ (((N.restrictScalars O).comap Φ).mkQ (z g))) ∈ N.functionModule Φ z p := by
  have h := (N.toFunctionModule Φ z p Ψ).property
  rwa [show (N.toFunctionModule Φ z p Ψ : G → O ⧸ Ideal.span {p}) = _ from
    funext (coe_toFunctionModule_apply Ψ)] at h

/-- A linear map vanishing at the `v` with `Φ v ∈ N` vanishes on `Φ⁻¹(N)`. -/
private theorem comap_le_ker {M : Type*} [AddCommGroup M] [Module O M] {Ψ : V →ₗ[O] M}
    (hΨ : ∀ v, Φ v ∈ N → Ψ v = 0) : (N.restrictScalars O).comap Φ ≤ LinearMap.ker Ψ :=
  fun v hv ↦ LinearMap.mem_ker.2 (hΨ v (by simpa using hv))

/-- The members of the module of functions of `N` are the functions `g ↦ Ψ (z g)` for the
`O`-linear `Ψ : V → O ⧸ (p)` vanishing on `Φ⁻¹(N)`. -/
@[simp]
theorem mem_functionModule {c : G → O ⧸ Ideal.span {p}} :
    c ∈ N.functionModule Φ z p ↔
      ∃ Ψ : V →ₗ[O] O ⧸ Ideal.span {p}, (∀ v, Φ v ∈ N → Ψ v = 0) ∧ ∀ g, Ψ (z g) = c g := by
  constructor
  · intro hc
    obtain ⟨Ψ, hΨ⟩ := toFunctionModule_surjective (N := N) (z := z) ⟨c, hc⟩
    refine ⟨Ψ ∘ₗ ((N.restrictScalars O).comap Φ).mkQ, fun v hv ↦ ?_, fun g ↦ ?_⟩
    · rw [LinearMap.comp_apply, mkQ_apply, (Quotient.mk_eq_zero _).2 (by simpa using hv),
        map_zero]
    · rw [LinearMap.comp_apply, ← coe_toFunctionModule_apply, hΨ]
  · rintro ⟨Ψ, hΨ, hc⟩
    refine ⟨((N.restrictScalars O).comap Φ).liftQ Ψ (comap_le_ker hΨ), funext fun g ↦ ?_⟩
    simp [hc]

/-- More relations give fewer functions: if `Φ v ∈ N` implies `Φ' v ∈ N'`, every function of `N'`
along `Φ'` is a function of `N` along `Φ`. -/
theorem functionModule_le_functionModule {R' F' : Type*} [Semiring R'] [AddCommMonoid F']
    [Module O F'] [Module R' F'] [SMul O R'] [IsScalarTower O R' F'] {N' : Submodule R' F'}
    {Φ' : V →ₗ[O] F'} (h : ∀ v, Φ v ∈ N → Φ' v ∈ N') :
    N'.functionModule Φ' z p ≤ N.functionModule Φ z p := fun c hc ↦ by
  obtain ⟨Ψ, hΨ, hc⟩ := mem_functionModule.1 hc
  exact mem_functionModule.2 ⟨Ψ, fun v hv ↦ hΨ v (h v hv), hc⟩

/-- If `Φ (p • v) ∈ N` for all `v`, then `p` kills `V ⧸ Φ⁻¹(N)`. -/
theorem smul_quotient_comap_eq_zero (hpN : ∀ v, Φ (p • v) ∈ N)
    (q : V ⧸ (N.restrictScalars O).comap Φ) : p • q = 0 := by
  obtain ⟨v, rfl⟩ := ((N.restrictScalars O).comap Φ).mkQ_surjective q
  rw [← map_smul, mkQ_apply, Quotient.mk_eq_zero]
  simpa using hpN v

end FunctionModule

section Coordinates

variable {O V G ι : Type*} [CommRing O] [AddCommGroup V] [Module O V] [DecidableEq ι]
  {N : Submodule O (ι → O)} {Φ : V →ₗ[O] ι → O} {z : G → V} {gen : ι → G}

/-- If `Φ (z (gen i)) ≡ e_i` modulo a submodule `N ⊆ O^ι`, the module of functions of `N` is
detected by the `gen i`. -/
theorem functionModule_isDetectedBy_range [Finite ι]
    (h : ∀ i, Φ (z (gen i)) - Pi.single i 1 ∈ N) (p : O) :
    (N.functionModule Φ z p).IsDetectedBy (Set.range gen) := by
  refine isDetectedBy_iff.2 fun c hc hcs ↦ ?_
  obtain ⟨Ψ, hΨ⟩ := toFunctionModule_surjective (N := N) (z := z) ⟨c, hc⟩
  have hΨ0 : Ψ = 0 :=
    eq_zero_of_forall_apply_mkQ_comap_eq_zero (N := N.restrictScalars O) h fun i ↦ by
      rw [← coe_toFunctionModule_apply, hΨ]
      exact hcs _ ⟨i, rfl⟩
  simpa [hΨ0] using congrArg Subtype.val hΨ.symm

/-- If `Φ (z (gen i)) ≡ e_i` and `Φ (p • v) ≡ 0` modulo a submodule `N ⊆ O^ι` over a principal
ideal domain, with `p ≠ 0`, the module of functions of `N` has the length of `O^ι ⧸ N`. -/
theorem length_functionModule [Finite ι] [IsDomain O] [IsPrincipalIdealRing O] {p : O}
    (hp : p ≠ 0) (hpN : ∀ v, Φ (p • v) ∈ N) (h : ∀ i, Φ (z (gen i)) - Pi.single i 1 ∈ N) :
    length O (N.functionModule Φ z p) = length O ((ι → O) ⧸ N) := by
  have := Fintype.ofFinite ι
  set W := (N.restrictScalars O).comap Φ
  -- Evaluation at the `z g` identifies `Hom_O(V ⧸ Φ⁻¹(N), O ⧸ (p))` with the module of functions.
  have hinj : Function.Injective (N.toFunctionModule Φ z p) :=
    (injective_iff_map_eq_zero _).2 fun Ψ hΨ ↦
      eq_zero_of_forall_apply_mkQ_comap_eq_zero (N := N.restrictScalars O) h fun i ↦ by
        rw [← coe_toFunctionModule_apply, hΨ]
        rfl
  -- `Φ` induces an isomorphism `V ⧸ Φ⁻¹(N) ≃ O^ι ⧸ N`.
  have hW : W ≤ N.comap Φ := le_rfl
  have hinj' : Function.Injective (W.mapQ N Φ hW) := by
    rw [← LinearMap.ker_eq_bot, ker_mapQ]
    exact mkQ_map_self W
  have hsurj : Function.Surjective (W.mapQ N Φ hW) := fun y ↦ by
    obtain ⟨y, rfl⟩ := N.mkQ_surjective y
    refine ⟨W.mkQ (∑ i, y i • z (gen i)), (Quotient.eq _).2 ?_⟩
    simpa using neg_mem (sub_sum_smul_mem h y)
  calc length O (N.functionModule Φ z p) = length O (V ⧸ W →ₗ[O] O ⧸ Ideal.span {p}) :=
        (LinearEquiv.ofBijective _ ⟨hinj, toFunctionModule_surjective⟩).length_eq.symm
    _ = length O (V ⧸ W) :=
        length_linearMap_quotient_span_singleton_right hp (smul_quotient_comap_eq_zero hpN)
    _ = length O ((ι → O) ⧸ N) := (LinearEquiv.ofBijective _ ⟨hinj', hsurj⟩).length_eq

/-- If `Φ (z (gen i)) ≡ e_i` and `Φ (p • v) ≡ 0` modulo a submodule `N ⊆ O^ι` over a discrete
valuation ring, with `p ≠ 0`, the colength of `N` is at most the length of its module of functions
modulo `C`-torsion plus `#ι v(C)`: the module of functions is detected by the `#ι` points `gen i`,
and `O ⧸ (p)` has `C`-torsion of length at most `v(C)`. -/
theorem length_quotient_le_length_functionModule_quotient_add [Fintype ι] [IsDomain O]
    [IsDiscreteValuationRing O] {p : O} (hp : p ≠ 0) (hpN : ∀ v, Φ (p • v) ∈ N)
    (h : ∀ i, Φ (z (gen i)) - Pi.single i 1 ∈ N) (C : O) :
    length O ((ι → O) ⧸ N) ≤ length O (N.functionModule Φ z p ⧸
      torsionBy O (N.functionModule Φ z p) C) + Fintype.card ι • addVal O C := by
  classical
  have hdet : (N.functionModule Φ z p).IsDetectedBy ↑(Finset.univ.image gen) := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact functionModule_isDetectedBy_range h p
  rw [← length_functionModule hp hpN h]
  refine (hdet.length_le C).trans ?_
  gcongr
  · exact length_torsionBy_quotient_span_singleton_le p C
  · exact Finset.card_image_le.trans (by simp)

end Coordinates

section Relations

variable {O R F V G : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Semiring R]
  [AddCommGroup F] [Module O F] [Module R F] [SMul O R] [IsScalarTower O R F] [AddCommGroup V]
  [Module O V]

/-- **The cost of the relations `Φ (z a)`.** Over a principal ideal domain, if `Φ (p • v) ∈ N`
for all `v` with `p ≠ 0`, the image in `F ⧸ N` of the relations `Φ (z a)`, `a ∈ A`, is no longer
than the quotient of the module of functions of `N` by its members vanishing on `A`. -/
theorem length_map_mkQ_span_image_le {N : Submodule R F} {Φ : V →ₗ[O] F} {z : G → V} {p : O}
    (hp : p ≠ 0) (hpN : ∀ v, Φ (p • v) ∈ N) (A : Set G) :
    length O ((span O (Φ '' (z '' A))).map (N.restrictScalars O).mkQ) ≤
      length O (N.functionModule Φ z p ⧸
        (pi A fun _ ↦ ⊥).comap (N.functionModule Φ z p).subtype) := by
  -- Both are dual to the span `QA` of the classes of the `z a` in `V ⧸ Φ⁻¹(N)`.
  set W := (N.restrictScalars O).comap Φ
  set Z := N.functionModule Φ z p
  set QA := span O (W.mkQ '' (z '' A))
  -- The image of the relations is the image of `QA` under `V ⧸ Φ⁻¹(N) → F ⧸ N`.
  have hmap : (span O (Φ '' (z '' A))).map (N.restrictScalars O).mkQ =
      QA.map (W.mapQ (N.restrictScalars O) Φ le_rfl) := by
    simp only [QA, map_span, Set.image_image, mkQ_apply, mapQ_apply]
  -- Restriction to `QA` is onto the dual of `QA`, and kills what vanishes on `A`.
  let ρ := LinearMap.lcomp O (O ⧸ Ideal.span {p}) QA.subtype
  have hρ : Function.Surjective ρ := fun θ ↦ exists_linearMap_quotient_span_singleton_comp_eq hp
    (smul_quotient_comap_eq_zero hpN) QA.injective_subtype θ
  let ψ := ((pi A fun _ ↦ ⊥).comap Z.subtype).mkQ ∘ₗ N.toFunctionModule Φ z p
  have hψ : Function.Surjective ψ := (mkQ_surjective _).comp toFunctionModule_surjective
  have hker : LinearMap.ker ψ ≤ LinearMap.ker ρ := fun Ψ hΨ ↦ by
    rw [LinearMap.mem_ker, LinearMap.comp_apply, mkQ_apply, Quotient.mk_eq_zero, mem_comap,
      mem_pi] at hΨ
    have hQA : QA ≤ LinearMap.ker Ψ := span_le.2 <| by
      rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact (mem_bot O).1 (hΨ a ha)
    exact LinearMap.ext fun x ↦ hQA x.property
  calc length O ((span O (Φ '' (z '' A))).map (N.restrictScalars O).mkQ)
      ≤ length O QA := hmap ▸ length_le_of_surjective _ (LinearMap.submoduleMap_surjective _ _)
    _ = length O (QA →ₗ[O] O ⧸ Ideal.span {p}) :=
        (length_linearMap_quotient_span_singleton_right hp
          fun x ↦ Subtype.ext (smul_quotient_comap_eq_zero hpN x)).symm
    _ = length O (LinearMap.range ρ) := by rw [LinearMap.range_eq_top.2 hρ, length_top]
    _ ≤ length O ((V ⧸ W →ₗ[O] O ⧸ Ideal.span {p}) ⧸ LinearMap.ker ψ) :=
        TauCeti.length_range_le_length_quotient ρ hker
    _ = length O (Z ⧸ (pi A fun _ ↦ ⊥).comap Z.subtype) := (ψ.quotKerEquivOfSurjective hψ).length_eq

end Relations

end Submodule
