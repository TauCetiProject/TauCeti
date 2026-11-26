/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.Algebra.Category.ModuleCat.Tower.Basic
public import TauCeti.LinearAlgebra.TensorProduct.Quotient

import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import TauCeti.RingTheory.AdicCompletion.Pi

/-!
# Adic systems of modules and their limits

Let `I` be an ideal of a commutative ring `A`. A tower of `A`-modules `M₀ ← M₁ ← M₂ ← ⋯` is an
`I`-adic system if every transition `Mₙ₊₁ → Mₙ` is surjective with kernel `I^{n+1} Mₙ₊₁`, so
that `Mₙ ≃ Mₙ₊₁ ⧸ I^{n+1} Mₙ₊₁` and `I^{n+1}` kills `Mₙ`. The reductions `M ⧸ I^{n+1} M` of an
`A`-module `M` form the basic example.

If `A` is `I`-adically precomplete and `M₀` is a finite `A`-module, then the limit `L = lim Mₙ` is
a finite `A`-module, each projection `L → Mₙ` is surjective with kernel `I^{n+1} L`, and so
`L ⧸ I^{n+1} L ≃ Mₙ` (EGA I, Ch. 0, 7.2.9). Moreover, the morphisms from such a system to any
`I`-adic system `(Nₙ)` are the linear maps `lim Mₙ → lim Nₙ` (EGA I, Ch. 0, 7.2.10). This
reassembles a compatible system of finite modules over the truncations `A ⧸ I^{n+1}` of an adic
ring into a single finite `A`-module; it is the algebraic input for coherent modules on formal
schemes. Neither noetherianity of `A` nor finite generation of `I` is needed.

## Main definitions

* `TauCeti.ModuleTower.IsAdicSystem`: the tower is an `I`-adic system.
* `TauCeti.ModuleTower.IsAdicSystem.levelModule`: each term over `A ⧸ I ^ (n + 1)`, with
  quotient-linear transition `levelTransition` and bijective base-change map `levelReduction`.
* `TauCeti.ModuleTower.IsAdicSystem.limQuotientEquiv`: `L ⧸ I^{n+1} L ≃ Mₙ`.
* `TauCeti.ModuleTower.IsAdicSystem.limBaseChangeEquiv`: quotient-linear scalar change of the limit.
* `TauCeti.ModuleTower.IsAdicSystem.ofLimHom`: the morphism of adic systems induced by a linear map
  of their limits.
* `TauCeti.ModuleTower.IsAdicSystem.limMapEquiv`: morphisms of adic systems are the linear maps of
  their limits.

## Main results

* `TauCeti.ModuleTower.IsAdicSystem.pow_smul_top_eq_bot`: `I^{n+1} Mₙ = 0`.
* `TauCeti.ModuleTower.IsAdicSystem.surjective_limπ_comp`: bottom surjectivity implies
  surjectivity onto each term.
* `TauCeti.ModuleTower.IsAdicSystem.surjective_of_surjective_limπ_zero_comp`: bottom surjectivity
  from an `I`-adically precomplete module implies surjectivity onto the limit.
* `TauCeti.ModuleTower.IsAdicSystem.finite_obj`: if `M₀` is finite, then so is every `Mₙ`.
* `TauCeti.ModuleTower.IsAdicSystem.finite_lim`: the limit is a finite module.
* `TauCeti.ModuleTower.IsAdicSystem.ker_limπ`: the kernel of `L → Mₙ` is `I^{n+1} L`.
* `TauCeti.ModuleTower.IsAdicSystem.isBaseChange_limπ`: `L → Mₙ` exhibits scalar change to
  `A ⧸ I ^ (n + 1)`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, 7.2.9–7.2.10.
-/

public section

namespace TauCeti.ModuleTower

open CategoryTheory Opposite

universe v u

variable {A : Type u} [CommRing A] (I : Ideal A) (F : ModuleTower.{v} A)

/-- A tower `M₀ ← M₁ ← ⋯` of `A`-modules is an *`I`-adic system* if each transition
`Mₙ₊₁ → Mₙ` is surjective with kernel `I^{n+1} Mₙ₊₁`, that is, `Mₙ ≃ Mₙ₊₁ ⧸ I^{n+1} Mₙ₊₁`. -/
structure IsAdicSystem : Prop where
  /-- Each transition `Mₙ₊₁ → Mₙ` is surjective. -/
  transition_surjective (n : ℕ) : Function.Surjective (F.transition n)
  /-- The kernel of the transition `Mₙ₊₁ → Mₙ` is `I^{n+1} Mₙ₊₁`. -/
  ker_transition (n : ℕ) : LinearMap.ker (F.transition n) = I ^ (n + 1) • ⊤

namespace IsAdicSystem

variable {I F} (hF : F.IsAdicSystem I)
include hF

/-- `I^{n+1}` kills the `n`-th term of an `I`-adic system. -/
theorem pow_smul_top_eq_bot (n : ℕ) : I ^ (n + 1) • (⊤ : Submodule A (F.obj (op n))) = ⊥ := by
  -- `Mₙ` is the image of `Mₙ₊₁`, so `I^{n+1} Mₙ` is the image of `I^{n+1} Mₙ₊₁`, the kernel.
  have himage : I ^ (n + 1) • (⊤ : Submodule A (F.obj (op n))) =
      (LinearMap.ker (F.transition n)).map (F.transition n) := by
    simp [hF.ker_transition n, Submodule.map_smul'',
      LinearMap.range_eq_top.2 (hF.transition_surjective n)]
  rw [himage, ← LinearMap.le_ker_iff_map]

/-- Every linear map into the `n`-th term of an `I`-adic system kills `I^{n+1}`. -/
theorem pow_smul_top_le_ker {P : Type*} [AddCommGroup P] [Module A P] {n : ℕ}
    (f : P →ₗ[A] F.obj (op n)) : I ^ (n + 1) • (⊤ : Submodule A P) ≤ LinearMap.ker f := by
  rw [← Submodule.comap_bot, ← Submodule.map_le_iff_le_comap, Submodule.map_smul'',
    ← hF.pow_smul_top_eq_bot n]
  exact smul_mono_right _ le_top

variable {P : Type*} [AddCommGroup P] [Module A P] {φ : P →ₗ[A] F.lim}

/-- Nakayama's lemma along the tower: if `P → L → M₀` is surjective, then so is every
`P → L → Mₙ`. -/
theorem surjective_limπ_comp (hφ : Function.Surjective (F.limπ 0 ∘ₗ φ)) (n : ℕ) :
    Function.Surjective (F.limπ n ∘ₗ φ) := by
  rw [← LinearMap.range_eq_top] at hφ ⊢
  induction n with
  | zero => exact hφ
  | succ n ih =>
    -- The image `N` of `P` in `Mₙ₊₁` maps onto `Mₙ`, so `N + I^{n+1} Mₙ₊₁ = Mₙ₊₁`.
    have hN : ⊤ ≤ LinearMap.range (F.limπ (n + 1) ∘ₗ φ) ⊔ I ^ (n + 1) • ⊤ := by
      have hmap : (LinearMap.range (F.limπ (n + 1) ∘ₗ φ)).map (F.transition n) = ⊤ := by
        rw [← LinearMap.range_comp, ← LinearMap.comp_assoc, transition_comp_limπ, ih]
      rw [← hF.ker_transition n, ← Submodule.comap_map_eq, hmap, Submodule.comap_top]
    -- Substituting this into itself gives `N + I^{2n+2} Mₙ₊₁`, and `I^{n+2}` kills `Mₙ₊₁`.
    have hsq : I ^ (n + 1) • I ^ (n + 1) • (⊤ : Submodule A (F.obj (op (n + 1)))) = ⊥ := by
      rw [← Submodule.mul_smul, ← pow_add, eq_bot_iff, ← hF.pow_smul_top_eq_bot (n + 1)]
      exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
    refine top_le_iff.1 (hN.trans (sup_le le_rfl ?_))
    calc I ^ (n + 1) • ⊤
        ≤ I ^ (n + 1) • (LinearMap.range (F.limπ (n + 1) ∘ₗ φ) ⊔ I ^ (n + 1) • ⊤) :=
          smul_mono_right _ hN
      _ = I ^ (n + 1) • LinearMap.range (F.limπ (n + 1) ∘ₗ φ) := by
          rw [Submodule.smul_sup, hsq, sup_bot_eq]
      _ ≤ LinearMap.range (F.limπ (n + 1) ∘ₗ φ) := Submodule.smul_le_right

/-- One approximation step: an element of `L` vanishing in `Mₙ` agrees in `Mₙ₊₁` with the image
of an element of `I^{n+1} P`. -/
private theorem exists_mem_pow_smul_top_limπ_sub_eq_zero
    (hφ : ∀ n, Function.Surjective (F.limπ n ∘ₗ φ)) {n : ℕ} {z : F.lim}
    (hz : F.limπ n z = 0) :
    ∃ c ∈ I ^ (n + 1) • (⊤ : Submodule A P), F.limπ (n + 1) (z - φ c) = 0 := by
  have hmem : F.limπ (n + 1) z ∈ I ^ (n + 1) • (⊤ : Submodule A (F.obj (op (n + 1)))) := by
    rw [← hF.ker_transition n, LinearMap.mem_ker, ← LinearMap.comp_apply, transition_comp_limπ,
      hz]
  rw [← LinearMap.range_eq_top.2 (hφ (n + 1)), LinearMap.range_eq_map,
    ← Submodule.map_smul''] at hmem
  obtain ⟨c, hc, hcz⟩ := hmem
  exact ⟨c, hc, by rw [map_sub, sub_eq_zero]; exact hcz.symm⟩

/-- Successive approximation: if `P` is `I`-adically precomplete, an element of `L` vanishing in
`Mₙ` is the image of an element of `I^{n+1} P`. -/
private theorem exists_mem_pow_smul_top_eq [IsPrecomplete I P]
    (hφ : ∀ n, Function.Surjective (F.limπ n ∘ₗ φ)) {n : ℕ} {z : F.lim}
    (hz : F.limπ n z = 0) : ∃ a ∈ I ^ (n + 1) • (⊤ : Submodule A P), φ a = z := by
  choose c hc hcz using fun m (w : {w : F.lim // F.limπ m w = 0}) ↦
    hF.exists_mem_pow_smul_top_limπ_sub_eq_zero hφ w.property
  -- The remainders `wⱼ = z - φ(sⱼ)`, vanishing in `Mₙ₊ⱼ`, and the partial sums `sⱼ`.
  let w : ∀ j, {w : F.lim // F.limπ (n + j) w = 0} := fun j ↦
    Nat.rec ⟨z, hz⟩ (fun j wj ↦ ⟨wj.val - φ (c (n + j) wj), hcz (n + j) wj⟩) j
  let s : ℕ → P := fun j ↦ ∑ i ∈ Finset.range j, c (n + i) (w i)
  have hs_succ (j : ℕ) : s (j + 1) = s j + c (n + j) (w j) := Finset.sum_range_succ _ _
  have hs (j : ℕ) : z - φ (s j) = (w j).val := by
    induction j with
    | zero => simp [s, w]
    | succ j ih => rw [hs_succ, map_add, ← sub_sub, ih]
  have hsub {j j' : ℕ} (hjj' : j ≤ j') : s j' - s j ∈ I ^ (n + 1 + j) • (⊤ : Submodule A P) := by
    rw [← Finset.sum_Ico_eq_sub _ hjj']
    refine Submodule.sum_mem _ fun i hi ↦ Submodule.smul_mono_left ?_ (hc (n + i) (w i))
    exact Ideal.pow_le_pow_right (by have := (Finset.mem_Ico.1 hi).1; omega)
  obtain ⟨a, ha⟩ := ‹IsPrecomplete I P›.prec fun {j j'} hjj' ↦ SModEq.sub_mem.2 <| by
    rw [← neg_sub]
    exact Submodule.neg_mem _ (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
      (hsub hjj'))
  -- `a - sⱼ ∈ I^j P`, and `sⱼ ∈ I^{n+1} P` because `s₀ = 0`.
  have has (j : ℕ) : a - s j ∈ I ^ j • (⊤ : Submodule A P) := by
    rw [← neg_sub]
    exact Submodule.neg_mem _ (SModEq.sub_mem.1 (ha j))
  refine ⟨a, ?_, Subtype.ext <| funext fun m ↦ ?_⟩
  · rw [← sub_add_cancel a (s (n + 1))]
    refine Submodule.add_mem _ (has (n + 1)) ?_
    simpa [s] using hsub (j := 0) (j' := n + 1) (Nat.zero_le _)
  -- In `Mₘ`, `φ(a)` agrees with `φ(sₘ₊₁)`, and `z - φ(sₘ₊₁)` vanishes in `Mₙ₊ₘ₊₁`.
  have h₁ : F.limπ m (φ (a - s (m + 1))) = 0 :=
    hF.pow_smul_top_le_ker (F.limπ m ∘ₗ φ) (has (m + 1))
  have h₂ : F.limπ m (z - φ (s (m + 1))) = 0 := by
    rw [hs, ← LinearMap.congr_fun (F.transitionOfLE_comp_limπ (by omega : m ≤ n + (m + 1))),
      LinearMap.comp_apply, (w (m + 1)).property, map_zero]
  have hdiff : φ a - z = φ (a - s (m + 1)) - (z - φ (s (m + 1))) := by
    rw [map_sub]; abel
  have h : F.limπ m (φ a) = F.limπ m z := by
    rw [← sub_eq_zero, ← map_sub, hdiff, map_sub, h₁, h₂, sub_zero]
  simpa using h

/-- A linear map to the limit of an `I`-adic system is surjective if its source is
`I`-adically precomplete and its composite with the bottom projection is surjective. -/
theorem surjective_of_surjective_limπ_zero_comp [IsPrecomplete I P]
    (hφ : Function.Surjective (F.limπ 0 ∘ₗ φ)) : Function.Surjective φ := by
  have hφn := hF.surjective_limπ_comp hφ
  intro z
  obtain ⟨c, hc⟩ := hφ (F.limπ 0 z)
  obtain ⟨a, -, ha⟩ := hF.exists_mem_pow_smul_top_eq hφn (n := 0) (z := z - φ c) <| by
    rw [map_sub, sub_eq_zero]
    exact hc.symm
  exact ⟨a + c, by rw [map_add, ha, sub_add_cancel]⟩

/-- A finite free module mapping onto the bottom term of an adic system with finite `M₀`. -/
private theorem exists_fin_surjective_limπ_zero_comp [Module.Finite A (F.obj (op 0))] :
    ∃ (k : ℕ) (φ : (Fin k → A) →ₗ[A] F.lim), Function.Surjective (F.limπ 0 ∘ₗ φ) := by
  obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin' A (F.obj (op 0))
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property (F.limπ 0) g
    (F.limπ_surjective hF.transition_surjective 0)
  exact ⟨k, φ, hφ ▸ hg⟩

/-- **Every term of an `I`-adic system with `M₀` finite is a finite module**, over any commutative
ring: `Mₙ` is generated by lifts of generators of `M₀ = Mₙ ⧸ I Mₙ`, as `I` is nilpotent on `Mₙ`. -/
theorem finite_obj [Module.Finite A (F.obj (op 0))] (n : ℕ) :
    Module.Finite A (F.obj (op n)) := by
  obtain ⟨k, φ, hφ⟩ := hF.exists_fin_surjective_limπ_zero_comp
  exact Module.Finite.of_surjective _ (hF.surjective_limπ_comp hφ n)

noncomputable section QuotientLevels

open scoped ChangeOfRings

/-- The ideal `I ^ (n + 1)` annihilates the `n`-th term of an adic system. -/
lemma isTorsionBySet_obj (n : ℕ) :
    Module.IsTorsionBySet A (F.obj (op n)) (I ^ (n + 1) : Ideal A) :=
  (Module.isTorsionBySet_iff_subset_annihilator _ _).2 <| by
    rw [← Submodule.annihilator_top]
    exact Submodule.le_annihilator_iff.2 (hF.pow_smul_top_eq_bot n)

/-- The `n`-th term of an `I`-adic system, as a module over `A ⧸ I ^ (n + 1)`. -/
-- This is a type abbreviation: quotient scalar-action lemmas must see the original carrier.
abbrev levelModule (n : ℕ) : ModuleCat.{v} (A ⧸ I ^ (n + 1)) :=
  letI := (isTorsionBySet_obj hF n).module
  ModuleCat.of _ (F.obj (op n))

/-- The transition `Mₙ₊₁ → Mₙ` of an `I`-adic system, as a map of `A ⧸ I ^ (n + 2)`-modules. -/
def levelTransition (n : ℕ) :
    levelModule hF (n + 1) ⟶ (ModuleCat.restrictScalars (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1))))).obj (levelModule hF n) :=
  ModuleCat.semilinearMapAddEquiv (Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1))))
      (levelModule hF (n + 1)) (levelModule hF n)
    { toFun := F.transition n
      map_add' := map_add _
      map_smul' s x := by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
        rw [Ideal.Quotient.factor_mk]
        exact (congrArg (F.transition n) ((isTorsionBySet_obj hF (n + 1)).mk_smul r x)).trans
          (((F.transition n).map_smul r x).trans
            ((isTorsionBySet_obj hF n).mk_smul r (F.transition n x)).symm) }

/-- The quotient-linear transition is the original transition on elements. -/
@[simp]
lemma levelTransition_apply (n : ℕ) (x : levelModule hF (n + 1)) :
    (levelTransition hF n).hom x = F.transition n x :=
  (rfl)

omit hF

variable {F : ModuleTower.{max u v} A} (hF : F.IsAdicSystem I)

/-- The map `(A ⧸ I ^ (n + 1)) ⊗ Mₙ₊₁ ⟶ Mₙ` induced by the transition of an `I`-adic system. -/
def levelReduction (n : ℕ) :
    (ModuleCat.extendScalars (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1))))).obj (levelModule hF (n + 1)) ⟶
      levelModule hF n :=
  ((ModuleCat.extendRestrictScalarsAdj _).homEquiv _ _).symm (levelTransition hF n)

/-- The base-change map sends `1 ⊗ x` to the transition of `x`. -/
@[simp]
lemma levelReduction_one_tmul (n : ℕ) (x : levelModule hF (n + 1)) :
    (levelReduction hF n).hom ((1 : A ⧸ I ^ (n + 1)) ⊗ₜ[A ⧸ I ^ (n + 1 + 1),
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1)))]
        x) =
      F.transition n x :=
  ModuleCat.extendRestrictScalarsAdj_homEquiv_apply (levelReduction hF n) _ |>.symm.trans <| by
    rw [levelReduction, Equiv.apply_symm_apply]
    exact levelTransition_apply hF n x

/-- `(A ⧸ I ^ (n + 1)) ⊗ Mₙ₊₁ ⟶ Mₙ` is bijective: the transition `Mₙ₊₁ → Mₙ` is surjective with
kernel `I ^ (n + 1) Mₙ₊₁`, which is the kernel of `Mₙ₊₁ → (A ⧸ I ^ (n + 1)) ⊗ Mₙ₊₁`. -/
lemma levelReduction_bijective (n : ℕ) : Function.Bijective (levelReduction hF n).hom := by
  let φ := Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1)))
  have hφ : Function.Surjective φ := Ideal.Quotient.factor_surjective _
  let := φ.toAlgebra
  let := (isTorsionBySet_obj hF (n + 1)).module
  have := (isTorsionBySet_obj hF (n + 1)).isScalarTower (S := A)
  let e := ModuleCat.extendScalarsAlgebraMapIso (S := A ⧸ I ^ (n + 1))
    (levelModule hF (n + 1))
  refine ⟨(injective_iff_map_eq_zero _).2 fun z hz ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := e.toLinearEquiv.symm.surjective z
    obtain ⟨x, rfl⟩ := TensorProduct.mk_surjective (A ⧸ I ^ (n + 1 + 1)) (levelModule hF (n + 1))
      (A ⧸ I ^ (n + 1)) hφ z
    -- Select the original `A`-module carrier for the adic-system kernel formula.
    have hx : (show F.obj (op (n + 1)) from x) ∈
        I ^ (n + 1) • (⊤ : Submodule A (F.obj (op (n + 1)))) := by
      rw [← hF.ker_transition n, LinearMap.mem_ker, ← levelReduction_one_tmul hF n x]
      exact (congrArg (levelReduction hF n).hom
        (ModuleCat.extendScalarsAlgebraMapIso_inv_tmul (S := A ⧸ I ^ (n + 1))
          (levelModule hF (n + 1)) 1 x).symm).trans hz
    have ht : (1 : A ⧸ I ^ (n + 1)) ⊗ₜ[A ⧸ I ^ (n + 1 + 1)] x = 0 := by
      apply (LinearMap.mem_ker (f := TensorProduct.mk _ _ _ 1)).mp
      rw [TensorProduct.ker_mk_one_of_surjective hφ]
      -- Restricting `ker φ • Mₙ₊₁` to `A` gives `I ^ (n + 1) • Mₙ₊₁`.
      dsimp only [RingHom.algebraMap_toAlgebra, φ]
      rw [Ideal.Quotient.factor_ker]
      exact (Submodule.restrictScalars_mem A _ _).mp <|
        (SetLike.ext_iff.mp (Ideal.smul_restrictScalars (M := F.obj (op (n + 1)))
          (I ^ (n + 1)) (⊤ : Submodule (A ⧸ I ^ (n + 1 + 1)) _)) x).mpr hx
    exact (congrArg e.inv ht).trans (map_zero _)
  · obtain ⟨x, rfl⟩ := hF.transition_surjective n y
    exact ⟨_, levelReduction_one_tmul hF n x⟩

variable {F : ModuleTower.{v} A} (hF : F.IsAdicSystem I)
  [IsNoetherianRing A] [Module.Finite A (F.obj (op 0))]

/-- Over a noetherian ring, every quotient-ring level of a finite adic system is finitely
presented. -/
lemma finitePresentation_levelModule (n : ℕ) :
    Module.FinitePresentation (A ⧸ I ^ (n + 1)) (levelModule hF n) := by
  let := (isTorsionBySet_obj hF n).module
  have := (isTorsionBySet_obj hF n).isScalarTower (S := A)
  have := hF.finite_obj n
  have : Module.Finite (A ⧸ I ^ (n + 1)) (levelModule hF n) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ I ^ (n + 1)) (F.obj (op n))
  exact Module.finitePresentation_of_finite _ _

end QuotientLevels

variable [IsPrecomplete I A] [Module.Finite A (F.obj (op 0))]

/-- **The kernel of `lim Mₙ → Mₙ` is `I^{n+1} lim Mₙ`** for an `I`-adic system over an
`I`-adically precomplete ring with `M₀` finite (EGA I, Ch. 0, 7.2.9). -/
theorem ker_limπ (n : ℕ) : LinearMap.ker (F.limπ n) = I ^ (n + 1) • ⊤ := by
  obtain ⟨k, φ, hφ⟩ := hF.exists_fin_surjective_limπ_zero_comp
  refine le_antisymm (fun z hz ↦ ?_) (hF.pow_smul_top_le_ker _)
  obtain ⟨a, ha, rfl⟩ := hF.exists_mem_pow_smul_top_eq (hF.surjective_limπ_comp hφ) hz
  exact Submodule.smul_top_le_comap_smul_top _ φ ha

/-- **The limit of an `I`-adic system with `M₀` finite is a finite module** over an `I`-adically
precomplete ring (EGA I, Ch. 0, 7.2.9). -/
theorem finite_lim : Module.Finite A F.lim := by
  obtain ⟨k, φ, hφ⟩ := hF.exists_fin_surjective_limπ_zero_comp
  exact Module.Finite.of_surjective φ (hF.surjective_of_surjective_limπ_zero_comp hφ)

/-- **`lim Mₙ ⧸ I^{n+1} lim Mₙ ≃ Mₙ`** for an `I`-adic system over an `I`-adically precomplete ring
with `M₀` finite (EGA I, Ch. 0, 7.2.9), induced by the projection `lim Mₙ → Mₙ`. -/
noncomputable def limQuotientEquiv (n : ℕ) :
    (F.lim ⧸ I ^ (n + 1) • (⊤ : Submodule A F.lim)) ≃ₗ[A] F.obj (op n) :=
  (Submodule.quotEquivOfEq _ _ (hF.ker_limπ n).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (F.limπ_surjective hF.transition_surjective n))

@[simp]
theorem limQuotientEquiv_mk (n : ℕ) (x : F.lim) :
    hF.limQuotientEquiv n (Submodule.Quotient.mk x) = F.limπ n x := by
  simp [limQuotientEquiv]

open scoped TensorProduct

/-- The limit projection exhibits the `n`-th term as scalar change to `A ⧸ I ^ (n + 1)`. -/
theorem isBaseChange_limπ (n : ℕ) :
    letI := (hF.isTorsionBySet_obj n).isScalarTower (S := A)
    IsBaseChange (N := hF.levelModule n) (A ⧸ I ^ (n + 1)) (F.limπ n) := by
  have := (hF.isTorsionBySet_obj n).isScalarTower (S := A)
  exact (IsBaseChange.quotient_iff (N := hF.levelModule n) _ _).2
    ⟨F.limπ_surjective hF.transition_surjective n, hF.ker_limπ n⟩

/-- The quotient-linear scalar-change equivalence induced by a limit projection. -/
noncomputable def limBaseChangeEquiv (n : ℕ) :
    (A ⧸ I ^ (n + 1)) ⊗[A] F.lim ≃ₗ[A ⧸ I ^ (n + 1)] hF.levelModule n :=
  (hF.isBaseChange_limπ n).equiv

/-- The scalar-change equivalence evaluates `1 ⊗ x` by the limit projection. -/
@[simp↓]
theorem limBaseChangeEquiv_one_tmul (n : ℕ) (x : F.lim) :
    hF.limBaseChangeEquiv n (1 ⊗ₜ[A] x) = F.limπ n x := by
  unfold limBaseChangeEquiv
  simp only [IsBaseChange.equiv_tmul, one_smul]

/-- The inverse scalar-change equivalence sends a projected element to `1 ⊗ x`. -/
@[simp↓]
theorem limBaseChangeEquiv_symm_limπ (n : ℕ) (x : F.lim) :
    (hF.limBaseChangeEquiv n).symm (F.limπ n x) = 1 ⊗ₜ[A] x := by
  apply (hF.limBaseChangeEquiv n).injective
  rw [LinearEquiv.apply_symm_apply, hF.limBaseChangeEquiv_one_tmul]

/-! ### Morphisms of adic systems and linear maps of their limits -/

variable {G : ModuleTower.{v} A} (hG : G.IsAdicSystem I) (φ : F.lim →ₗ[A] G.lim)

/-- The `n`-th component of the morphism of `I`-adic systems induced by a linear map
`φ : lim Mₙ → lim Nₙ`: the map `Mₙ ≃ lim Mₙ ⧸ I^{n+1} → lim Nₙ → Nₙ`. -/
private noncomputable def ofLimHomApp (n : ℕ) : F.obj (op n) →ₗ[A] G.obj (op n) :=
  (I ^ (n + 1) • ⊤ : Submodule A F.lim).liftQ (G.limπ n ∘ₗ φ) (hG.pow_smul_top_le_ker _) ∘ₗ
    (hF.limQuotientEquiv n).symm.toLinearMap

private theorem ofLimHomApp_coe (n : ℕ) (x : F.lim) :
    hF.ofLimHomApp hG φ n ((x : F.Product) n) = (φ x : G.Product) n := by
  have hx : (hF.limQuotientEquiv n).symm (F.limπ n x) = Submodule.Quotient.mk x := by
    rw [LinearEquiv.symm_apply_eq, limQuotientEquiv_mk]
  rw [← limπ_apply, ← limπ_apply]
  simp only [ofLimHomApp, LinearMap.comp_apply, LinearEquiv.coe_coe, hx, Submodule.liftQ_apply]

/-- The morphism of `I`-adic systems induced by a linear map `φ : lim Mₙ → lim Nₙ` of their limits,
over an `I`-adically precomplete ring with `M₀` finite (EGA I, Ch. 0, 7.2.10). It is the inverse of
`ModuleTower.limMap`, see `ModuleTower.IsAdicSystem.limMapEquiv`. -/
noncomputable def ofLimHom : F ⟶ G :=
  NatTrans.ofOpSequence (fun n ↦ ModuleCat.ofHom (hF.ofLimHomApp hG φ n)) fun n ↦ by
    ext x
    obtain ⟨y, rfl⟩ := F.limπ_surjective hF.transition_surjective (n + 1) x
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply, ← transition_def,
      limπ_apply, transition_coe_lim_succ, ofLimHomApp_coe]

/-- The morphism induced by `φ` sends the `n`-th term of `x ∈ lim Mₙ` to that of `φ x`. -/
@[simp]
theorem ofLimHom_app_coe_apply (n : ℕ) (x : F.lim) :
    ((hF.ofLimHom hG φ).app (op n)).hom ((x : F.Product) n) = (φ x : G.Product) n := by
  rw [ofLimHom, NatTrans.ofOpSequence_app, ModuleCat.hom_ofHom, ofLimHomApp_coe]

@[simp]
theorem limMap_ofLimHom : limMap (hF.ofLimHom hG φ) = φ := by
  ext n : 1
  rw [limπ_comp_limMap]
  ext x
  simp

@[simp]
theorem ofLimHom_limMap (f : F ⟶ G) : hF.ofLimHom hG (limMap f) = f :=
  (limMap_inj hF.transition_surjective).1 (hF.limMap_ofLimHom hG _)

/-- **Morphisms of `I`-adic systems are the linear maps of their limits** (EGA I, Ch. 0, 7.2.10):
over an `I`-adically precomplete ring, if `M₀` is finite, then `f ↦ lim f` is a bijection from
morphisms of towers `(Mₙ) ⟶ (Nₙ)` to linear maps `lim Mₙ → lim Nₙ`, for every `I`-adic system
`(Nₙ)`. It is additive. -/
noncomputable def limMapEquiv : (F ⟶ G) ≃+ (F.lim →ₗ[A] G.lim) where
  toFun := limMap
  invFun := hF.ofLimHom hG
  left_inv := hF.ofLimHom_limMap hG
  right_inv := hF.limMap_ofLimHom hG
  map_add' := limMap_add

@[simp]
theorem limMapEquiv_apply (f : F ⟶ G) : hF.limMapEquiv hG f = limMap f :=
  (rfl)

@[simp]
theorem limMapEquiv_symm_apply : (hF.limMapEquiv hG).symm φ = hF.ofLimHom hG φ :=
  (rfl)

end IsAdicSystem

end TauCeti.ModuleTower
