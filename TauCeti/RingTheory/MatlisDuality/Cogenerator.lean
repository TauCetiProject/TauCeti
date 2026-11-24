/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Artinian.Module
public import TauCeti.RingTheory.MatlisDuality.Basic

import TauCeti.RingTheory.Artinian.Module

/-!
# Embedding Artinian modules into finite powers of the dual regular module

Let `R` be a commutative ring, `E` an `R`-module and `A` an `R`-algebra. If evaluation
`N → D_R (D_R N)` is injective for an Artinian left `A`-module `N`, as it is when `E` is an
injective cogenerator of `R`-modules, then `N` embeds into a finite power of `D_R A`, the dual of
the right regular module (`TauCeti.exists_injective_linearMap_pi_matlisDual`). A functional on `N`
that does not kill an element gives, through the Hom-tensor adjunction
`TauCeti.MatlisDual.equivLinearMapDualRegular`, a map `N → D_R A` that does not kill it, and
finitely many such maps suffice as `N` is Artinian (`IsArtinian.exists_injective_linearMap_pi`).

If `N` is moreover injective, the embedding splits (`TauCeti.exists_retract_pi_matlisDual`).

Suppose now that `E` is injective and that each `Hom_R(R ⧸ 𝔪, E)` has length one, the conditions
under which `D_R` is Matlis duality on modules of finite length over `R`. Then an injective
`A`-module `N` of finite length over `R` is a cogenerator over its endomorphism ring
`B = Module.End A N`: every nonzero element of every `B`-module is detected by a `B`-linear map to
`N` (`TauCeti.exists_linearMap_end_apply_ne_zero_of_injective`).

## Implementation notes

Write `D = D_R = Hom_R(-, E)`, with `E` injective and each `Hom_R(R ⧸ 𝔪, E)` of length one; then
`E` separates points, so evaluation `N → D (D N)` is injective, and Matlis biduality holds for
modules of finite length over `R`. As `N` is Artinian, it is a retract of a finite power `(D A)ⁿ`,
with split embedding `s` and retraction `r`; write `sᵢ` and `rᵢ` for their coordinates. By
naturality of the Hom-tensor adjunction `adj` (`TauCeti.MatlisDual.equivLinearMapDualRegular`) each
map `D N → B`, `χ ↦ rᵢ ∘ adj χ`, is right `B`-linear; dualizing it and applying biduality gives a
`B`-linear map `D B → N`. Together these maps embed `D B` into `Nⁿ`
(`TauCeti.exists_injective_matlisDual_end`), because `b = ∑ᵢ rᵢ ∘ sᵢ ∘ b` for every `b ∈ B`. As
`D B` detects the nonzero elements of every `B`-module, by the adjunction for `B`, so does `N`.

## Main results

* `TauCeti.exists_injective_linearMap_pi_matlisDual`: an Artinian module with injective evaluation
  into its double dual embeds into a finite power of `D_R A`.
* `TauCeti.exists_retract_pi_matlisDual`: if it is moreover injective, it is a retract of a finite
  power of `D_R A`.
* `TauCeti.exists_injective_matlisDual_end`: if `E` is injective and each `Hom_R(R ⧸ 𝔪, E)` has
  length one, the dual of the endomorphism ring of an injective module `N` of finite length over
  `R` embeds into a finite power of `N`.
* `TauCeti.exists_linearMap_end_apply_ne_zero_of_injective`: under the same hypotheses, `N` is a
  cogenerator over its endomorphism ring.
-/

public section

namespace TauCeti

open MatlisDual

universe u v w t

section Cogenerator

variable {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E] {A : Type t} [Ring A]
  [Algebra R A] {N : Type w} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]

/-- **Embedding into a finite power of `D_R A`.** An Artinian left `A`-module `N` for which
evaluation `N → D_R (D_R N)` is injective, as it is when `E` is an injective cogenerator of
`R`-modules, embeds into a finite power of `D_R A`. -/
theorem exists_injective_linearMap_pi_matlisDual [IsArtinian A N]
    (hEval : Function.Injective (MatlisDual.evalₗ R E N)) :
    ∃ (n : ℕ) (g : N →ₗ[A] (Fin n → MatlisDual R E A)), Function.Injective g := by
  refine IsArtinian.exists_injective_linearMap_pi fun x hx ↦ ?_
  -- Some functional `φ` on `N` does not kill `x`; its adjoint `N → D_R A` does not kill `x`
  -- either, evaluating at `1`.
  obtain ⟨φ, hφ⟩ : ∃ φ : MatlisDual R E N, equivLinearMap R E N φ x ≠ 0 := by
    by_contra! h
    exact hx (hEval (MatlisDual.ext fun φ ↦ by simpa using h φ))
  refine ⟨equivLinearMapDualRegular φ, fun h ↦ hφ ?_⟩
  simpa using congr(equivLinearMap R E A $h 1)

end Cogenerator

section Injective

variable {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E] {A : Type t} [Ring A]
  [Algebra R A] [Small.{w} A] {N : Type w} [AddCommGroup N] [Module R N] [Module A N]
  [IsScalarTower R A N] [Module.Injective A N]

/-- **A retract of a finite power of `D_R A`.** An injective Artinian left `A`-module `N` for which
evaluation `N → D_R (D_R N)` is injective, as it is when `E` is an injective cogenerator of
`R`-modules, is a retract of a finite power of `D_R A`: the embedding of
`TauCeti.exists_injective_linearMap_pi_matlisDual` splits. The module `N` may live in any universe
in which `A` is small. -/
theorem exists_retract_pi_matlisDual [IsArtinian A N]
    (hEval : Function.Injective (MatlisDual.evalₗ R E N)) :
    ∃ (n : ℕ) (s : N →ₗ[A] Fin n → MatlisDual R E A) (r : (Fin n → MatlisDual R E A) →ₗ[A] N),
      r ∘ₗ s = LinearMap.id := by
  obtain ⟨n, s, hs⟩ := exists_injective_linearMap_pi_matlisDual (A := A) hEval
  obtain ⟨r, hr⟩ := Module.Injective.extension_property A N _ _ s hs LinearMap.id
  exact ⟨n, s, r, hr⟩

variable [Module.Injective R E] [Small.{v} R]
  (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
include hE

/-- **The dual of the endomorphism ring embeds into a finite power.** Let `E` be an injective
`R`-module such that each `Hom_R(R ⧸ 𝔪, E)` has length one, and let `N` be an injective left
`A`-module of finite length over `R`, with endomorphism ring `B = Module.End A N`. Then `D_R B`
embeds into a finite power `Nⁿ` as a left `B`-module. The hypotheses on `E` give the split
embedding of `N` into a finite power of `D_R A` and Matlis biduality for `N`. -/
theorem exists_injective_matlisDual_end (hN : IsFiniteLength R N) :
    ∃ (n : ℕ) (σ : MatlisDual R E (Module.End A N) →ₗ[Module.End A N] Fin n → N),
      Function.Injective σ := by
  have : IsArtinian R N := (isFiniteLength_iff_isNoetherian_isArtinian.1 hN).2
  have : IsArtinian A N := isArtinian_of_tower R inferInstance
  obtain ⟨n, s, r, hrs⟩ := exists_retract_pi_matlisDual (A := A)
    (MatlisDual.injective_evalₗ (N := N) (nontrivial_linearMap_of_isMaximal hE))
  -- `τᵢ χ = rᵢ ∘ adj χ` is right `B`-linear, by naturality of the adjunction.
  let τ (i : Fin n) : MatlisDual R E N →ₗ[(Module.End A N)ᵐᵒᵖ] Module.End A N :=
    { toFun χ := r ∘ₗ LinearMap.single A _ i ∘ₗ equivLinearMapDualRegular χ
      map_add' _ _ := by simp [LinearMap.comp_add]
      map_smul' b χ := by
        rw [end_op_smul_eq_map, equivLinearMapDualRegular_map, RingHom.id_apply,
          MulOpposite.smul_eq_mul_unop, Module.End.mul_eq_comp]
        simp only [LinearMap.comp_assoc] }
  have hτ (i : Fin n) (χ : MatlisDual R E N) :
      τ i χ = r ∘ₗ LinearMap.single A _ i ∘ₗ equivLinearMapDualRegular χ := rfl
  refine ⟨n, LinearMap.pi fun i ↦
    (evalEquiv (A := Module.End A N) hE hN).symm.toLinearMap ∘ₗ mapOp (τ i),
    (injective_iff_map_eq_zero _).2 fun θ hθ ↦ ?_⟩
  have h0 (i : Fin n) (χ : MatlisDual R E N) : equivLinearMap R E _ θ (τ i χ) = 0 := by
    have := congr_fun hθ i
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, Pi.zero_apply,
      LinearEquiv.map_eq_zero_iff] at this
    simpa using congr(equivLinearMap R E _ $this χ)
  -- Every `b ∈ B` is `∑ᵢ rᵢ ∘ sᵢ ∘ b`, a sum of values of the maps `τᵢ`.
  have hb (b : Module.End A N) :
      b = ∑ i, τ i (map b (equivLinearMapDualRegular.symm (LinearMap.proj i ∘ₗ s))) := by
    ext x
    simp only [hτ, LinearMap.sum_apply, LinearMap.comp_apply, equivLinearMapDualRegular_map,
      LinearEquiv.apply_symm_apply, LinearMap.coe_single, LinearMap.proj_apply]
    rw [← map_sum, Finset.univ_sum_single]
    exact (LinearMap.congr_fun hrs (b x)).symm
  ext b
  rw [hb b, map_sum]
  simp [h0]

/-- **An injective module is a cogenerator over its endomorphism ring.** Let `E` be an injective
`R`-module such that each `Hom_R(R ⧸ 𝔪, E)` has length one, and let `N` be an injective left
`A`-module of finite length over `R`. Then every nonzero element `y` of every module `Y` over
`B = Module.End A N` is detected by a `B`-linear map `Y → N`. -/
theorem exists_linearMap_end_apply_ne_zero_of_injective (hN : IsFiniteLength R N) {Y : Type*}
    [AddCommGroup Y] [Module (Module.End A N) Y] {y : Y} (hy : y ≠ 0) :
    ∃ h : Y →ₗ[Module.End A N] N, h y ≠ 0 := by
  let : Module R Y := Module.compHom Y (algebraMap R (Module.End A N))
  have : IsScalarTower R (Module.End A N) Y := .of_algebraMap_smul fun _ _ ↦ rfl
  -- `D_R B` detects `y` by the adjunction for `B`, and `D_R B` embeds into `Nⁿ`.
  obtain ⟨n, σ, hσ⟩ := exists_injective_matlisDual_end (A := A) hE hN
  obtain ⟨χ, hχ⟩ :=
    exists_apply_ne_zero_of_forall_isMaximal (nontrivial_linearMap_of_isMaximal hE) hy
  let g := equivLinearMapDualRegular (A := Module.End A N) ((equivLinearMap R E Y).symm χ)
  have hg : g y ≠ 0 := fun h ↦ hχ (by simpa [g] using congr(equivLinearMap R E _ $h 1))
  obtain ⟨i, hi⟩ := Function.ne_iff.1 ((map_ne_zero_iff σ hσ).2 hg)
  exact ⟨LinearMap.proj i ∘ₗ σ ∘ₗ g, hi⟩

end Injective

end TauCeti
