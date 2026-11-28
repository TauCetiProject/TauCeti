/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Component.Cycle.Basic
import TauCeti.Dynamics.PeriodicPts.Basic
import TauCeti.GroupTheory.Perm.Cycle.Enumeration

/-!
# Diagonal transport, folded indices, and cycle-wise product decomposition

This file constructs the diagonal isomorphism `RootPairing.componentCycleDiag` from the return
fixed space of a component `C` to `RootPairing.componentCycleFixedSubmodule σ C`, with inverse
`RootPairing.componentCycleFixedProj`, and develops:

* `RootPairing.componentCycleFoldedIndicesEquiv`: bijection between folded root vectors of the
  return map and folded root vectors on the cycle.
* `RootPairing.Equiv.componentReturnFixedCongr` and `RootPairing.componentReturnFixedShift`:
  equivalence transport and starting-component shift on return fixed spaces.
* `RootPairing.componentCycleFixedPiEquiv`: product decomposition of the full `σ`-fixed weight
  space across all component cycles.
* `RootPairing.mem_rootSpan_componentCycleDiag_iff`: preservation of the root lattice under
  `componentCycleDiag`.
-/

public section

open Finset Function TauCeti
open _root_.Equiv (Perm)
open _root_.Equiv.Perm (SameCycle)
open scoped DirectSum

namespace RootPairing

section Field

variable {ι K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

section Finite

variable (P : RootPairing ι K M N) [Finite ι] [P.IsRootSystem] (σ : P.Aut) (C : P.Component)

/-- **Restriction of `P.componentProj C` to `σ`-fixed weights** into the return fixed space. -/
noncomputable def componentCycleFixedProj :
    LinearMap.fixedSubmodule σ.weightMap →ₗ[K]
      LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap where
  toFun y := ⟨P.componentProj C (y : M),
    Equiv.componentProj_mem_fixedSubmodule_componentReturn σ C y.property⟩
  map_add' x y := Subtype.ext (map_add (P.componentProj C) (x : M) (y : M))
  map_smul' r x := Subtype.ext (map_smul (P.componentProj C) r (x : M))

@[simp] theorem val_componentCycleFixedProj_apply (y : LinearMap.fixedSubmodule σ.weightMap) :
    (P.componentCycleFixedProj σ C y : P.componentSpace C) = P.componentProj C (y : M) := (rfl)

theorem coe_componentCycleFixedProj_apply (y : LinearMap.fixedSubmodule σ.weightMap) :
    ((P.componentCycleFixedProj σ C y : P.componentSpace C) : M) =
      P.componentProj C (y : M) := (rfl)

/-- **Diagonal transport `u ↦ ∑ r ∈ range c, (σ.weightMap ^ r) u`** from the return fixed space
onto `P.componentCycleFixedSubmodule σ C`, with inverse `P.componentCycleFixedProj σ C`. -/
noncomputable def componentCycleDiag :
    LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap ≃ₗ[K]
      P.componentCycleFixedSubmodule σ C where
  toFun u := ⟨σ.componentCycleMap C u, by
    rw [P.mem_componentCycleFixedSubmodule, Equiv.coe_componentCycleMap_apply,
      Equiv.componentCycleSum_apply]
    refine Submodule.sum_mem _ fun r _ ↦ ?_
    rw [σ.weightMap_pow]
    exact P.pow_weightMap_mem_componentCycleSpace
      (P.self_componentSpace_le_componentCycleSpace σ C u.val.property) r⟩
  map_add' _ _ := Subtype.ext <| map_add (σ.componentCycleMap C) _ _
  map_smul' _ _ := Subtype.ext <| map_smul (σ.componentCycleMap C) _ _
  invFun y := P.componentCycleFixedProj σ C y.val
  left_inv u := Subtype.ext (Equiv.componentProj_componentCycleMap σ C u)
  right_inv y := Subtype.ext <| Subtype.ext <| by
    rw [Equiv.coe_componentCycleMap_apply, Equiv.componentCycleSum_apply]
    simp_rw [σ.weightMap_pow]
    exact P.sum_range_pow_weightMap_componentProj (P.mem_componentCycleFixedSubmodule.mp y.property)
      (LinearMap.mem_fixedSubmodule_iff.mp y.val.property)

@[simp] theorem componentCycleDiag_symm_apply (y : P.componentCycleFixedSubmodule σ C) :
    (P.componentCycleDiag σ C).symm y = P.componentCycleFixedProj σ C y.val := (rfl)

section DiagApply

variable (u : LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap)

theorem componentCycleDiag_apply :
    (P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) =
      σ.componentCycleMap C u := (rfl)

theorem coe_componentCycleDiag_apply :
    ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M) =
      ∑ r ∈ range (minimalPeriod σ.componentEquiv C), (σ.weightMap ^ r) (u : M) := by
  rw [P.componentCycleDiag_apply, Equiv.coe_componentCycleMap_apply, Equiv.componentCycleSum_apply]
  simp_rw [σ.weightMap_pow]

@[simp] theorem componentProj_componentCycleDiag :
    P.componentProj C ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M) =
      (u : P.componentSpace C) :=
  Equiv.componentProj_componentCycleMap σ C u

@[simp] theorem componentCycleFixedProj_componentCycleDiag :
    P.componentCycleFixedProj σ C (P.componentCycleDiag σ C u) = u :=
  (P.componentCycleDiag σ C).symm_apply_apply u

end DiagApply

section ImplicitDiag

variable {P σ C}

theorem componentCycleDiag_componentCycleFixedProj_of_mem
    {y : LinearMap.fixedSubmodule σ.weightMap} (hy : y ∈ P.componentCycleFixedSubmodule σ C) :
    P.componentCycleDiag σ C (P.componentCycleFixedProj σ C y) = ⟨y, hy⟩ :=
  (P.componentCycleDiag σ C).apply_symm_apply ⟨y, hy⟩

theorem componentCycleFixedProj_eq_zero_of_not_sameCycle {D : P.Component}
    (hCD : ¬SameCycle σ.componentEquiv D C) {y : LinearMap.fixedSubmodule σ.weightMap}
    (hy : y ∈ P.componentCycleFixedSubmodule σ D) :
    P.componentCycleFixedProj σ C y = 0 :=
  Subtype.ext (P.componentProj_eq_zero_of_not_sameCycle
    (P.mem_componentCycleFixedSubmodule.mp hy) hCD)

/-- When `σ` fixes `C` (`c = 1`), `componentCycleDiag` acts as the identity on ambient vectors. -/
theorem coe_componentCycleDiag_of_componentEquiv_eq (hC : σ.componentEquiv C = C)
    (u : LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap) :
    ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M) = (u : M) := by
  rw [P.coe_componentCycleDiag_apply, minimalPeriod_eq_one_iff_isFixedPt.mpr hC,
    Finset.sum_range_one, pow_zero, Module.End.one_eq_id, LinearMap.id_apply]

end ImplicitDiag

/-! ### Orbit sizes and distinct orbit-sum transport -/

theorem minimalPeriod_componentReturn_indexEquiv (i : C.supp) :
    minimalPeriod (σ.componentReturn C).indexEquiv i =
      minimalPeriod (σ.indexEquiv ^ minimalPeriod σ.componentEquiv C) (i : ι) :=
  Semiconj.minimalPeriod_eq (fb := ⇑(σ.indexEquiv ^ minimalPeriod σ.componentEquiv C))
    (fun j ↦ Equiv.coe_componentReturn_indexEquiv_apply σ C j) Subtype.val_injective i

/-- **Minimal period factorization via the return map.** -/
theorem minimalPeriod_indexEquiv_eq_mul_componentReturn (i : C.supp) :
    minimalPeriod σ.indexEquiv (i : ι) =
      minimalPeriod σ.componentEquiv C * minimalPeriod (σ.componentReturn C).indexEquiv i := by
  have hi : P.componentOf (i : ι) = C := (C.mem_supp_iff (i : ι)).mp i.property
  rw [P.minimalPeriod_indexEquiv_eq_mul σ (i : ι), hi,
    P.minimalPeriod_componentReturn_indexEquiv σ C i]

/-- The return orbit sum of `i : C.supp` packaged in the return fixed submodule. -/
noncomputable def componentReturnOrbitSumFixed (i : C.supp) :
    LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap :=
  ⟨(P.componentPairing C).orbitSum (σ.componentReturn C) i,
    (P.componentPairing C).orbitSum_mem_fixedSubmodule (σ.componentReturn C) i⟩

@[simp] theorem coe_componentReturnOrbitSumFixed (i : C.supp) :
    (P.componentReturnOrbitSumFixed σ C i : P.componentSpace C) =
      (P.componentPairing C).orbitSum (σ.componentReturn C) i := (rfl)

/-- **Diagonal transport carries return orbit sums to ambient orbit sums.** -/
@[simp] theorem coe_componentCycleDiag_orbitSum (i : C.supp) :
    ((P.componentCycleDiag σ C (P.componentReturnOrbitSumFixed σ C i) :
        LinearMap.fixedSubmodule σ.weightMap) : M) = P.orbitSum σ (i : ι) := by
  rw [P.componentCycleDiag_apply, Equiv.coe_componentCycleMap_apply]
  exact Equiv.componentCycleSum_orbitSum σ C i

/-- Two roots in `C.supp` have equal ambient orbit sums iff they have equal return orbit sums. -/
theorem orbitSum_eq_iff_componentReturn (i j : C.supp) :
    P.orbitSum σ (i : ι) = P.orbitSum σ (j : ι) ↔
      (P.componentPairing C).orbitSum (σ.componentReturn C) i =
        (P.componentPairing C).orbitSum (σ.componentReturn C) j := by
  rw [← P.coe_componentCycleDiag_orbitSum σ C i, ← P.coe_componentCycleDiag_orbitSum σ C j]
  exact ⟨fun h ↦ congrArg Subtype.val ((P.componentCycleDiag σ C).injective
      (Subtype.ext (Subtype.ext h))),
    fun h ↦ congrArg (fun u ↦ ((P.componentCycleDiag σ C u : _) : M)) (Subtype.ext h)⟩

/-- **Bijection of distinct folded root vectors on a component cycle.** -/
noncomputable def componentCycleFoldedIndicesEquiv :
    (P.componentPairing C).foldedIndices (σ.componentReturn C) ≃
      P.componentCycleFoldedIndices σ C where
  toFun v := ⟨((P.componentCycleDiag σ C
      ⟨v.val, (P.componentPairing C).foldedIndices_subset_fixedSubmodule
        (σ.componentReturn C) v.property⟩ :
        LinearMap.fixedSubmodule σ.weightMap) : M), by
    obtain ⟨i, hi⟩ := (P.componentPairing C).mem_foldedIndices.mp v.property
    have hEq : (⟨v.val, (P.componentPairing C).foldedIndices_subset_fixedSubmodule
          (σ.componentReturn C) v.property⟩ :
        LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap) =
        P.componentReturnOrbitSumFixed σ C i := Subtype.ext hi.symm
    rw [hEq, P.coe_componentCycleDiag_orbitSum]
    exact P.orbitSum_mem_componentCycleFoldedIndices_of_mem_supp i⟩
  invFun w := ⟨P.componentProj C w.val, by
    obtain ⟨i, hi⟩ : w.val ∈ Set.range fun i : C.supp ↦ P.orbitSum σ (i : ι) :=
      P.componentCycleFoldedIndices_eq_range_supp σ C ▸ w.property
    have hi' : P.orbitSum σ (i : ι) = w.val := hi
    refine (P.componentPairing C).mem_foldedIndices.mpr ⟨i, ?_⟩
    rw [← hi', ← P.coe_componentCycleDiag_orbitSum σ C i, P.componentProj_componentCycleDiag,
      P.coe_componentReturnOrbitSumFixed]⟩
  left_inv v := Subtype.ext <| Equiv.componentProj_componentCycleMap σ C
    ⟨v.val, (P.componentPairing C).foldedIndices_subset_fixedSubmodule
      (σ.componentReturn C) v.property⟩
  right_inv w := Subtype.ext <| by
    rw [P.coe_componentCycleDiag_apply]
    exact P.sum_range_pow_weightMap_componentProj
      (P.componentCycleFoldedIndices_subset_componentCycleSpace σ C w.property)
      (LinearMap.mem_fixedSubmodule_iff.mp
        (P.foldedIndices_subset_fixedSubmodule σ
          (P.componentCycleFoldedIndices_subset_foldedIndices σ C w.property)))

@[simp] theorem coe_componentCycleFoldedIndicesEquiv_apply
    (v : (P.componentPairing C).foldedIndices (σ.componentReturn C)) :
    (P.componentCycleFoldedIndicesEquiv σ C v : M) =
      ((P.componentCycleDiag σ C ⟨v.val,
        (P.componentPairing C).foldedIndices_subset_fixedSubmodule
          (σ.componentReturn C) v.property⟩ :
          LinearMap.fixedSubmodule σ.weightMap) : M) := (rfl)

theorem coe_componentCycleFoldedIndicesEquiv_apply_eq_sum
    (v : (P.componentPairing C).foldedIndices (σ.componentReturn C)) :
    (P.componentCycleFoldedIndicesEquiv σ C v : M) =
      ∑ r ∈ range (minimalPeriod σ.componentEquiv C), (σ.weightMap ^ r) (v.val : M) := by
  rw [coe_componentCycleFoldedIndicesEquiv_apply, coe_componentCycleDiag_apply]

@[simp] theorem coe_componentCycleFoldedIndicesEquiv_symm_apply
    (w : P.componentCycleFoldedIndices σ C) :
    ((P.componentCycleFoldedIndicesEquiv σ C).symm w : P.componentSpace C) =
      P.componentProj C w.val := (rfl)

/-! ### Equivalence transport, starting-component shift, and product assembly across cycles -/

end Finite

section EquivTransport

variable {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module K M₂] [AddCommGroup N₂] [Module K N₂]
  {P : RootPairing ι K M N} {Q : RootPairing ι₂ K M₂ N₂}
  [Finite ι] [Finite ι₂] [P.IsRootSystem] [Q.IsRootSystem]

/-- **An equivalence conjugating `σ` to `τ` conjugates the return map of `C` to the return map
of `e.componentEquiv C`.** -/
theorem Equiv.autCongr_componentReturn (e : P.Equiv Q) {σ : P.Aut} {τ : Q.Aut}
    (hστ : e.autCongr σ = τ) (C : P.Component) :
    (e.componentPairingEquiv C rfl).autCongr (σ.componentReturn C) =
      τ.componentReturn (e.componentEquiv C) := by
  rw [Equiv.componentReturn_def,
    e.autCongr_componentPairingEquiv (Equiv.componentEquiv_pow_minimalPeriod σ C) rfl,
    Equiv.componentReturn_def]
  refine Equiv.componentPairingEquiv_congr ?_ _ _
  rw [map_pow, hστ, e.minimalPeriod_componentEquiv_of_autCongr hστ C]

/-- Linear equivalence between return fixed spaces induced by an equivalence conjugating `σ` to
`τ`. -/
noncomputable def Equiv.componentReturnFixedCongr (e : P.Equiv Q) {σ : P.Aut} {τ : Q.Aut}
    (hστ : e.autCongr σ = τ) (C : P.Component) :
    LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap ≃ₗ[K]
      LinearMap.fixedSubmodule (τ.componentReturn (e.componentEquiv C)).toHom.weightMap :=
  (e.componentPairingEquiv C rfl).weightEquiv.fixedSubmoduleCongr <| by
    ext u
    have hu := congrArg (fun g : (Q.componentPairing (e.componentEquiv C)).Aut ↦
      (g.weightMap ((e.componentPairingEquiv C rfl).weightEquiv u) : M₂))
      (e.autCongr_componentReturn hστ C)
    simpa [← Equiv.weightEquiv_apply, Equiv.weightEquiv_autCongr_apply] using hu

@[simp] theorem Equiv.coe_componentReturnFixedCongr_apply (e : P.Equiv Q) {σ : P.Aut} {τ : Q.Aut}
    (hστ : e.autCongr σ = τ) (C : P.Component)
    (u : LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap) :
    ((e.componentReturnFixedCongr hστ C u : Q.componentSpace (e.componentEquiv C)) : M₂) =
      e.weightMap (u : M) := by
  simp [componentReturnFixedCongr]

/-- An equivalence conjugating `σ` to `τ` intertwines `componentCycleFixedProj`. -/
theorem Equiv.componentCycleFixedProj_of_autCongr (e : P.Equiv Q) {σ : P.Aut} {τ : Q.Aut}
    (hστ : e.autCongr σ = τ) (C : P.Component)
    {y : LinearMap.fixedSubmodule σ.weightMap} {y' : LinearMap.fixedSubmodule τ.weightMap}
    (hy : (y' : M₂) = e.weightMap (y : M)) :
    Q.componentCycleFixedProj τ (e.componentEquiv C) y' =
      e.componentReturnFixedCongr hστ C (P.componentCycleFixedProj σ C y) :=
  Subtype.ext <| Subtype.ext <| by
    rw [coe_componentCycleFixedProj_apply, coe_componentReturnFixedCongr_apply,
      coe_componentCycleFixedProj_apply, hy, e.coe_componentProj_weightMap]

/-- **Equivalence transport of `componentCycleDiag`**: conjugating `σ` to `τ` carries the
diagonal cycle sum on `C` to the diagonal cycle sum on `e.componentEquiv C` along
`e.weightMap`. -/
theorem Equiv.coe_componentCycleDiag_componentReturnFixedCongr (e : P.Equiv Q) {σ : P.Aut}
    {τ : Q.Aut} (hστ : e.autCongr σ = τ) (C : P.Component)
    (u : LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap) :
    ((Q.componentCycleDiag τ (e.componentEquiv C)
        (e.componentReturnFixedCongr hστ C u) : LinearMap.fixedSubmodule τ.weightMap) : M₂) =
      e.weightMap ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M) := by
  have hcomm : Semiconj e.weightMap σ.weightMap τ.weightMap := fun x ↦ by
    have h := congrArg (fun g : Q.Aut ↦ g.weightMap (e.weightEquiv x)) hστ
    simpa [Equiv.weightEquiv_autCongr_apply, ← Equiv.weightEquiv_apply] using h
  rw [coe_componentCycleDiag_apply, coe_componentCycleDiag_apply, map_sum,
    coe_componentReturnFixedCongr_apply, e.minimalPeriod_componentEquiv_of_autCongr hστ C]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [pow_apply_eq_iterate, pow_apply_eq_iterate]
  exact (hcomm.iterate_right r (u : M)).symm

end EquivTransport

section Finite

variable (P : RootPairing ι K M N) [Finite ι] [P.IsRootSystem] (σ : P.Aut) (C : P.Component)

/-- **Changing the starting component conjugates the return map.** -/
theorem autCongr_componentReturn_pow (k : ℕ) :
    ((σ ^ k).componentPairingEquiv C rfl).autCongr (σ.componentReturn C) =
      σ.componentReturn ((σ ^ k).componentEquiv C) :=
  (σ ^ k).autCongr_componentReturn (Equiv.autCongr_pow_self σ k) C

/-- Shift of return fixed vectors from `C` to `(σ ^ k).componentEquiv C` via `σ.weightMap ^ k`. -/
noncomputable def componentReturnFixedShift (k : ℕ) :
    LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap ≃ₗ[K]
      LinearMap.fixedSubmodule (σ.componentReturn ((σ ^ k).componentEquiv C)).toHom.weightMap :=
  (σ ^ k).componentReturnFixedCongr (Equiv.autCongr_pow_self σ k) C

@[simp] theorem coe_componentReturnFixedShift_apply (k : ℕ)
    (u : LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap) :
    ((P.componentReturnFixedShift σ C k u : P.componentSpace ((σ ^ k).componentEquiv C)) : M) =
      (σ.weightMap ^ k) (u : M) := by
  rw [componentReturnFixedShift, Equiv.coe_componentReturnFixedCongr_apply, σ.weightMap_pow]

/-- Projecting a `σ`-fixed weight to `(σ ^ k).componentEquiv C` shifts its `C`-projection. -/
theorem componentCycleFixedProj_pow (k : ℕ) (y : LinearMap.fixedSubmodule σ.weightMap) :
    P.componentCycleFixedProj σ ((σ ^ k).componentEquiv C) y =
      P.componentReturnFixedShift σ C k (P.componentCycleFixedProj σ C y) :=
  (σ ^ k).componentCycleFixedProj_of_autCongr (Equiv.autCongr_pow_self σ k) C <| by
    rw [σ.weightMap_pow, LinearMap.pow_apply_of_mem_fixedSubmodule σ.weightMap y.property k]

/-- **Independence of the starting component** for `componentCycleDiag`. -/
theorem coe_componentCycleDiag_componentReturnFixedShift (k : ℕ)
    (u : LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap) :
    ((P.componentCycleDiag σ ((σ ^ k).componentEquiv C)
        (P.componentReturnFixedShift σ C k u) : LinearMap.fixedSubmodule σ.weightMap) : M) =
      ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M) := by
  rw [componentReturnFixedShift,
    (σ ^ k).coe_componentCycleDiag_componentReturnFixedCongr (Equiv.autCongr_pow_self σ k) C u,
    σ.weightMap_pow,
    LinearMap.pow_apply_of_mem_fixedSubmodule σ.weightMap
      (P.componentCycleDiag σ C u).val.property k]

/-- **Product decomposition of the full `σ`-fixed weight space across all component cycles.** -/
noncomputable def componentCycleFixedPiEquiv :
    LinearMap.fixedSubmodule σ.weightMap ≃ₗ[K]
      ∀ O : Quotient (SameCycle.setoid σ.componentEquiv),
        LinearMap.fixedSubmodule (σ.componentReturn O.out).toHom.weightMap := by
  classical
  letI := Fintype.ofFinite (Quotient (SameCycle.setoid σ.componentEquiv))
  exact
    ((LinearEquiv.ofBijective
        (DirectSum.coeLinearMap fun O : Quotient (SameCycle.setoid σ.componentEquiv) ↦
          P.componentCycleFixedSubmodule σ O.out)
        (P.isInternal_componentCycleFixedSubmodule σ)).symm.trans
      (DirectSum.linearEquivFunOnFintype K _ _)).trans
      (LinearEquiv.piCongrRight fun O ↦ (P.componentCycleDiag σ O.out).symm)

@[simp] theorem componentCycleFixedPiEquiv_apply (y : LinearMap.fixedSubmodule σ.weightMap)
    (O : Quotient (SameCycle.setoid σ.componentEquiv)) :
    P.componentCycleFixedPiEquiv σ y O = P.componentCycleFixedProj σ O.out y := by
  classical
  let := Fintype.ofFinite (Quotient (SameCycle.setoid σ.componentEquiv))
  let Q := fun O' : Quotient (SameCycle.setoid σ.componentEquiv) ↦
    P.componentCycleFixedSubmodule σ O'.out
  let e₁ := LinearEquiv.ofBijective (DirectSum.coeLinearMap Q)
    (P.isInternal_componentCycleFixedSubmodule σ)
  have hy : y = ∑ O', (e₁.symm y O').val := by
    simpa using (e₁.apply_symm_apply y).symm.trans
      (congrArg (DirectSum.coeLinearMap Q) (DirectSum.sum_univ_of (e₁.symm y)).symm)
  dsimp [componentCycleFixedPiEquiv]
  rw [DirectSum.linearEquivFunOnFintype_apply, componentCycleDiag_symm_apply]
  conv_rhs => rw [hy, map_sum]
  rw [Finset.sum_eq_single O (fun O' _ hO' ↦
    P.componentCycleFixedProj_eq_zero_of_not_sameCycle
      (Perm.not_sameCycle_out_of_ne σ.componentEquiv hO') (e₁.symm y O').property) (by simp)]

theorem coe_componentCycleFixedPiEquiv_symm_apply
    [Fintype (Quotient (SameCycle.setoid σ.componentEquiv))]
    (f : ∀ O : Quotient (SameCycle.setoid σ.componentEquiv),
      LinearMap.fixedSubmodule (σ.componentReturn O.out).toHom.weightMap) :
    ((P.componentCycleFixedPiEquiv σ).symm f : M) =
      ∑ O, ((P.componentCycleDiag σ O.out (f O) : LinearMap.fixedSubmodule σ.weightMap) : M) := by
  suffices h : (P.componentCycleFixedPiEquiv σ).symm f =
      ∑ O, (P.componentCycleDiag σ O.out (f O)).val by
    rw [h, Submodule.coe_sum]
  rw [LinearEquiv.symm_apply_eq]
  ext O
  rw [componentCycleFixedPiEquiv_apply, map_sum, Finset.sum_eq_single O (fun O' _ hO' ↦
    P.componentCycleFixedProj_eq_zero_of_not_sameCycle
      (Perm.not_sameCycle_out_of_ne σ.componentEquiv hO')
      (P.componentCycleDiag σ O'.out (f O')).property) (by simp),
    componentCycleFixedProj_componentCycleDiag]

end Finite

section

variable (P : RootPairing ι K M N) [Finite ι] [P.IsRootSystem]

/-- An additive submonoid invariant under `σ.weightMap` and `P.componentProj C` is preserved by
`componentCycleDiag`. -/
theorem mem_addSubmonoid_componentCycleDiag_iff (A : AddSubmonoid M) {σ : P.Aut}
    (hstep : ∀ {x}, x ∈ A → σ.weightMap x ∈ A) (C : P.Component)
    (hproj : ∀ {x}, x ∈ A → (P.componentProj C x : M) ∈ A)
    (u : LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap) :
    ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M) ∈ A ↔
      (u : M) ∈ A := by
  refine ⟨fun hD ↦ ?_, fun hu ↦ ?_⟩
  · have h := hproj hD; rwa [P.componentProj_componentCycleDiag] at h
  · rw [P.coe_componentCycleDiag_apply]
    exact AddSubmonoid.sum_mem _ fun r _ ↦ by
      rw [pow_apply_eq_iterate]
      exact Set.MapsTo.iterate (fun _ h ↦ hstep h) r hu

/-- **Root-lattice preservation under `componentCycleDiag`** for any compatible scalar ring `S`. -/
theorem mem_rootSpan_componentCycleDiag_iff (S : Type*) [CommRing S] [Module S M]
    [LinearMap.CompatibleSMul M M S K] (σ : P.Aut) (C : P.Component)
    (u : LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap) :
    ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M) ∈ P.rootSpan S ↔
      (u : M) ∈ P.rootSpan S :=
  P.mem_addSubmonoid_componentCycleDiag_iff (P.rootSpan S).toAddSubmonoid
    (fun {x} hx ↦ (Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j ↦ by
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply,
        Hom.root_weightMap_apply P P j σ.toHom]
      exact (P.rootSpanMem S _).property) :
        P.rootSpan S ≤ (P.rootSpan S).comap (σ.weightMap.restrictScalars S)) hx)
    C (fun hx ↦ P.componentProj_mem_rootSpan S C hx) u

end

end Field

end RootPairing
