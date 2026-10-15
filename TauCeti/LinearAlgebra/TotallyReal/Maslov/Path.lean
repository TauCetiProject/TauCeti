/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TotallyReal.Maslov.Index
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Relative Maslov index of paths of totally real subspaces

For two paths `Λ`, `Γ` of maximal totally real subspaces with the same endpoints, the Maslov
phases `t ↦ ρ(Γ t, Λ t)` form a loop in the circle based at `1`. Its degree is the **relative
Maslov index** `μ(Λ, Γ)`, an integer measuring the relative homotopy class detected by the Maslov
phases; the crossing-form index for a single path is a further construction.

The relative index has the formal properties of the Robbin--Salamon Maslov index for paths:

* it vanishes on the diagonal, `μ(Λ, Λ) = 0`, and is antisymmetric, `μ(Γ, Λ) = -μ(Λ, Γ)`
  (`TauCeti.TotallyRealPath.relativeMaslovIndex_swap`);
* it is a cocycle, `μ(Λ, Γ) + μ(Γ, Δ) = μ(Λ, Δ)`
  (`TauCeti.TotallyRealPath.relativeMaslovIndex_add`);
* it is additive under catenation of paths,
  `μ(Λ₁ ⬝ Λ₂, Γ₁ ⬝ Γ₂) = μ(Λ₁, Γ₁) + μ(Λ₂, Γ₂)`
  (`TauCeti.TotallyRealPath.relativeMaslovIndex_trans`), and reversing both paths negates it
  (`TauCeti.TotallyRealPath.relativeMaslovIndex_symm`);
* it is natural: moving both paths by the same continuous path of complex-linear automorphisms
  does not change it (`TauCeti.TotallyRealPath.relativeMaslovIndex_map`);
* it is invariant under homotopies of the pair, given by continuous two-parameter frames, during
  which the two paths keep common endpoints
  (`TauCeti.TotallyRealPath.relativeMaslovIndex_eq_of_homotopy`);
* it is additive under direct sums, `μ(Λ ⊕ Λ', Γ ⊕ Γ') = μ(Λ, Γ) + μ(Λ', Γ')`
  (`TauCeti.TotallyRealPath.relativeMaslovIndex_prod`, in
  `TauCeti/LinearAlgebra/TotallyReal/Maslov/Prod.lean`);
* for two loops with the same base subspace it is the difference of their Maslov indices,
  `μ(Λ, Γ) = μ(Λ) - μ(Γ)` (`TauCeti.TotallyRealLoop.relativeMaslovIndex_toTotallyRealPath`).

The paths are given, like loops, by continuous frames of complex-linear automorphisms acting on
one maximal totally real subspace; reversal (`TauCeti.TotallyRealPath.symm`), catenation
(`TauCeti.TotallyRealPath.trans`) and the pointwise image under a path of automorphisms
(`TauCeti.TotallyRealPath.map`) are constructed on such frames.

The Maslov phase and its loop degree follow McDuff--Salamon, *J-holomorphic Curves and Symplectic
Topology*, 2nd ed., Appendix C.3. The relative path viewpoint and the naturality, catenation,
homotopy and direct-sum properties are those of the Robbin--Salamon Maslov index for paths.

## Main declarations

* `TauCeti.TotallyRealPath`: paths of maximal totally real subspaces.
* `TauCeti.TotallyRealPath.symm`, `TauCeti.TotallyRealPath.trans`: reversal and catenation.
* `TauCeti.TotallyRealPath.map`: the pointwise image under a path of automorphisms.
* `TauCeti.TotallyRealLoop.toTotallyRealPath`: a loop, read as a path.
* `TauCeti.TotallyRealPath.relativeMaslovPhasePath`: the loop `t ↦ ρ(Γ t, Λ t)`.
* `TauCeti.TotallyRealPath.relativeMaslovIndex`: its degree.
* `TauCeti.TotallyRealPath.relativeMaslovIndex_eq_degree`: the relative index is the degree of
  every loop of the circle with the values `ρ(Γ t, Λ t)`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C.3.
* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827--844,
  Theorem 2.3 (the axioms of the Maslov index for paths, including naturality, catenation,
  homotopy invariance and the direct sum).
-/

public section

open Module Real
open scoped ComplexConjugate unitInterval

namespace TauCeti

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A path of maximal totally real subspaces, given by a continuous family of complex-linear
changes of frame applied to one maximal totally real subspace. -/
structure TotallyRealPath where
  /-- The subspace at time `t`. -/
  toFun : I → Submodule ℝ E
  /-- The path is given by a continuous family of complex-linear automorphisms. -/
  exists_frame : ∃ L₀ : Submodule ℝ E,
    IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₀ ∧
    ∃ A : I → E ≃L[ℂ] E, Continuous (fun t => (A t : E →L[ℂ] E)) ∧
      ∀ t, toFun t = L₀.map (((A t).toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ)

namespace TotallyRealPath

variable {E}

attribute [coe] toFun

instance : CoeFun (TotallyRealPath E) fun _ => I → Submodule ℝ E := ⟨toFun⟩

@[ext]
theorem ext {Λ Λ' : TotallyRealPath E} (h : ∀ t, Λ t = Λ' t) : Λ = Λ' := by
  cases Λ
  cases Λ'
  congr
  exact funext h

/-- Every subspace along a path of maximal totally real subspaces is maximal totally real. -/
theorem isMaximalTotallyReal (Λ : TotallyRealPath E) (t : I) :
    IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) (Λ t) := by
  obtain ⟨L₀, hL₀, A, -, hA⟩ := Λ.exists_frame
  rw [hA t]
  exact hL₀.map_linearEquiv (A t).toLinearEquiv

/-- The reverse `t ↦ Λ (1 - t)` of a path of maximal totally real subspaces. -/
def symm (Λ : TotallyRealPath E) : TotallyRealPath E where
  toFun t := Λ (σ t)
  exists_frame := by
    obtain ⟨L₀, hL₀, A, hAc, hA⟩ := Λ.exists_frame
    exact ⟨L₀, hL₀, fun t => A (σ t), hAc.comp unitInterval.continuous_symm, fun t => hA (σ t)⟩

@[simp]
theorem symm_apply (Λ : TotallyRealPath E) (t : I) : Λ.symm t = Λ (σ t) :=
  (rfl)

/-- The catenation of a path `Λ` ending at the start of a path `Γ`: it runs through `Λ` and then
through `Γ`, each at double speed, as `Path.trans` does. -/
noncomputable def trans (Λ Γ : TotallyRealPath E) (h : Λ 1 = Γ 0) : TotallyRealPath E where
  toFun t :=
    if ht : (t : ℝ) ≤ 1 / 2 then Λ ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩
    else Γ ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩
  exists_frame := by
    obtain ⟨L₀, hL₀, A, hAc, hA⟩ := Λ.exists_frame
    obtain ⟨L₁, hL₁, B, hBc, hB⟩ := Γ.exists_frame
    -- After `Λ`, follow the frame `C s = B s ∘ (B 0)⁻¹ ∘ A 1`, which starts at `A 1` and carries
    -- `L₀` along `Γ`.
    let C (s : I) : E ≃L[ℂ] E := (A 1).trans ((B 0).symm.trans (B s))
    have hC (s : I) : L₀.map (((C s).toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ) = Γ s := by
      -- Apply `(B 0)⁻¹ ∘ B s` to `A 1 L₀ = Λ 1 = Γ 0 = B 0 L₁`.
      have hs := congrArg (Submodule.map
        ((((B 0).symm.trans (B s)).toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ))
        ((hA 1).symm.trans (h.trans (hB 0)))
      rw [← Submodule.map_comp, ← Submodule.map_comp] at hs
      rw [hB s]
      convert hs using 2 <;> ext x <;> simp [C]
    let a : Path (A 0 : E →L[ℂ] E) (A 1) := ⟨⟨fun t => A t, hAc⟩, rfl, rfl⟩
    have hCc : (fun s => (C s : E →L[ℂ] E)) =
        fun s => (B s : E →L[ℂ] E).comp ((A 1).trans (B 0).symm : E →L[ℂ] E) := by
      ext1 s
      ext x
      simp [C]
    let c : Path (A 1 : E →L[ℂ] E) (C 1) :=
      ⟨⟨fun s => C s, hCc ▸ hBc.clm_comp_const _⟩, by ext x; simp [C], rfl⟩
    refine ⟨L₀, hL₀, fun t => if ht : (t : ℝ) ≤ 1 / 2 then
      A ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩
      else C ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩,
      ?_, fun t => ?_⟩
    · convert (a.trans c).continuous using 1
      ext1 t
      rw [Path.trans_apply]
      dsimp only
      split_ifs <;> rfl
    · dsimp only
      split_ifs
      · exact hA _
      · exact (hC _).symm

/-- The catenation is `Λ` at double speed on `[0, 1 / 2]` and `Γ` at double speed after. -/
theorem trans_apply (Λ Γ : TotallyRealPath E) (h : Λ 1 = Γ 0) (t : I) :
    Λ.trans Γ h t =
      if ht : (t : ℝ) ≤ 1 / 2 then
        Λ ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩
      else Γ ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩ :=
  (rfl)

/-- The catenation starts where its first path starts. -/
@[simp]
theorem trans_zero (Λ Γ : TotallyRealPath E) (h : Λ 1 = Γ 0) : Λ.trans Γ h 0 = Λ 0 := by
  rw [trans_apply]
  split_ifs with ht
  · congr 1
    ext
    simp
  · norm_num at ht

/-- The catenation ends where its second path ends. -/
@[simp]
theorem trans_one (Λ Γ : TotallyRealPath E) (h : Λ 1 = Γ 0) : Λ.trans Γ h 1 = Γ 1 := by
  rw [trans_apply]
  split_ifs with ht
  · norm_num at ht
  · congr 1
    ext
    norm_num

/-- The pointwise image `t ↦ B t (Λ t)` of a path of maximal totally real subspaces under a
continuous path `B` of complex-linear automorphisms. -/
noncomputable def map (Λ : TotallyRealPath E) (B : I → E ≃L[ℂ] E)
    (hB : Continuous fun t => (B t : E →L[ℂ] E)) : TotallyRealPath E where
  toFun t := (Λ t).map (((B t).toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ)
  exists_frame := exists_frame_map Λ.exists_frame B hB

@[simp]
theorem map_apply (Λ : TotallyRealPath E) (B : I → E ≃L[ℂ] E)
    (hB : Continuous fun t => (B t : E →L[ℂ] E)) (t : I) :
    Λ.map B hB t = (Λ t).map (((B t).toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ) :=
  (rfl)

variable [FiniteDimensional ℂ E]

/-- The Maslov phase along a path, relative to a fixed maximal totally real subspace, is
continuous. -/
theorem continuous_maslovPhase (Λ : TotallyRealPath E) {L₀ : Submodule ℝ E}
    (hL₀ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₀) :
    Continuous fun t => hL₀.maslovPhase (Λ.isMaximalTotallyReal t) := by
  obtain ⟨L₁, hL₁, A, hAc, hA⟩ := Λ.exists_frame
  have hphase (t : I) : hL₀.maslovPhase (Λ.isMaximalTotallyReal t) =
      hL₀.maslovPhase hL₁ * (LinearMap.det ((A t).toLinearEquiv : E →ₗ[ℂ] E) /
        conj (LinearMap.det ((A t).toLinearEquiv : E →ₗ[ℂ] E))) := by
    rw [← hL₀.maslovPhase_mul_maslovPhase hL₁ (Λ.isMaximalTotallyReal t),
      hL₁.maslovPhase_congr (Λ.isMaximalTotallyReal t)
        (hL₁.map_linearEquiv (A t).toLinearEquiv) (hA t),
      IsMaximalTotallyReal.maslovPhase_map]
  simp_rw [hphase]
  exact continuous_const.mul (continuous_det_div_conj A hAc)

/-- The Maslov phase between two paths, taken pointwise, is continuous. -/
theorem continuous_maslovPhase_maslovPhase (Λ Γ : TotallyRealPath E) :
    Continuous fun t => (Γ.isMaximalTotallyReal t).maslovPhase (Λ.isMaximalTotallyReal t) := by
  -- Pass through the fixed reference `Λ 0`: `ρ(Γ t, Λ t) = ρ(Λ 0, Λ t) / ρ(Λ 0, Γ t)`.
  have hL := Λ.isMaximalTotallyReal 0
  have h (t : I) : (Γ.isMaximalTotallyReal t).maslovPhase (Λ.isMaximalTotallyReal t) =
      hL.maslovPhase (Λ.isMaximalTotallyReal t) / hL.maslovPhase (Γ.isMaximalTotallyReal t) :=
    (hL.maslovPhase_div_maslovPhase _ _).symm
  simp_rw [h]
  exact (Λ.continuous_maslovPhase hL).div₀ (Γ.continuous_maslovPhase hL) fun t =>
    hL.maslovPhase_ne_zero _

/-- The path of Maslov phases of `Λ` relative to a maximal totally real reference, as a continuous
map to the circle. -/
noncomputable def maslovPhasePath (Λ : TotallyRealPath E) {L₀ : Submodule ℝ E}
    (hL₀ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₀) :
    C(I, Circle) where
  toFun t := ⟨hL₀.maslovPhase (Λ.isMaximalTotallyReal t),
    mem_sphere_zero_iff_norm.2 (IsMaximalTotallyReal.norm_maslovPhase _ _)⟩
  continuous_toFun := (Λ.continuous_maslovPhase hL₀).subtype_mk _

@[simp]
theorem maslovPhasePath_apply (Λ : TotallyRealPath E) {L₀ : Submodule ℝ E}
    (hL₀ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₀)
    (t : I) :
    ((Λ.maslovPhasePath hL₀ t : Circle) : ℂ) = hL₀.maslovPhase (Λ.isMaximalTotallyReal t) :=
  (rfl)

/-- The loop of relative Maslov phases `t ↦ ρ(Γ t, Λ t)` of two paths with the same endpoints,
based at `1`. -/
noncomputable def relativeMaslovPhasePath (Λ Γ : TotallyRealPath E)
    (h₀ : Λ 0 = Γ 0) (h₁ : Λ 1 = Γ 1) : Path (1 : Circle) 1 where
  toFun t := ⟨(Γ.isMaximalTotallyReal t).maslovPhase (Λ.isMaximalTotallyReal t),
    mem_sphere_zero_iff_norm.2 (IsMaximalTotallyReal.norm_maslovPhase _ _)⟩
  continuous_toFun := (Λ.continuous_maslovPhase_maslovPhase Γ).subtype_mk _
  source' := Circle.ext <| by
    rw [Circle.coe_one, ← (Λ.isMaximalTotallyReal 0).maslovPhase_self]
    exact (Γ.isMaximalTotallyReal 0).maslovPhase_congr_left _ _ h₀.symm
  target' := Circle.ext <| by
    rw [Circle.coe_one, ← (Λ.isMaximalTotallyReal 1).maslovPhase_self]
    exact (Γ.isMaximalTotallyReal 1).maslovPhase_congr_left _ _ h₁.symm

@[simp]
theorem relativeMaslovPhasePath_apply (Λ Γ : TotallyRealPath E)
    (h₀ : Λ 0 = Γ 0) (h₁ : Λ 1 = Γ 1) (t : I) :
    (Λ.relativeMaslovPhasePath Γ h₀ h₁ t : ℂ) =
      (Γ.isMaximalTotallyReal t).maslovPhase (Λ.isMaximalTotallyReal t) :=
  (rfl)

/-- The relative Maslov index of two paths with the same endpoints is the degree of the loop
`t ↦ ρ(Γ t, Λ t)` of their relative Maslov phases. -/
noncomputable def relativeMaslovIndex (Λ Γ : TotallyRealPath E)
    (h₀ : Λ 0 = Γ 0) (h₁ : Λ 1 = Γ 1) : ℤ :=
  Circle.degree (Λ.relativeMaslovPhasePath Γ h₀ h₁)

/-- The relative Maslov index is the degree of the relative phase loop. -/
theorem relativeMaslovIndex_def (Λ Γ : TotallyRealPath E)
    (h₀ : Λ 0 = Γ 0) (h₁ : Λ 1 = Γ 1) :
    relativeMaslovIndex Λ Γ h₀ h₁ = Circle.degree (Λ.relativeMaslovPhasePath Γ h₀ h₁) := by
  rw [relativeMaslovIndex]

/-- The relative Maslov index is the degree of every loop of the circle whose value at `t` is the
Maslov phase `ρ(Γ t, Λ t)`. -/
theorem relativeMaslovIndex_eq_degree (Λ Γ : TotallyRealPath E)
    (h₀ : Λ 0 = Γ 0) (h₁ : Λ 1 = Γ 1) {x : Circle} (γ : Path x x)
    (hγ : ∀ t, (γ t : ℂ) = (Γ.isMaximalTotallyReal t).maslovPhase (Λ.isMaximalTotallyReal t)) :
    relativeMaslovIndex Λ Γ h₀ h₁ = Circle.degree γ :=
  Circle.degree_congr _ _ fun t => Circle.ext (hγ t).symm

/-- Comparing a path with itself gives relative Maslov index zero. -/
@[simp]
theorem relativeMaslovIndex_self (Λ : TotallyRealPath E) :
    relativeMaslovIndex Λ Λ rfl rfl = 0 := by
  rw [relativeMaslovIndex_eq_degree Λ Λ rfl rfl (Path.refl 1) fun t => by simp]
  exact Circle.degree_refl _

/-- **Antisymmetry of the relative Maslov index:** `μ(Γ, Λ) = -μ(Λ, Γ)`. -/
theorem relativeMaslovIndex_swap (Λ Γ : TotallyRealPath E)
    (h₀ : Λ 0 = Γ 0) (h₁ : Λ 1 = Γ 1) :
    relativeMaslovIndex Γ Λ h₀.symm h₁.symm = -relativeMaslovIndex Λ Γ h₀ h₁ := by
  rw [relativeMaslovIndex_eq_degree Γ Λ h₀.symm h₁.symm (Λ.relativeMaslovPhasePath Γ h₀ h₁).inv
    fun t => by simp [(Λ.isMaximalTotallyReal t).maslovPhase_symm], Circle.degree_inv,
    relativeMaslovIndex]

/-- **The relative Maslov index is a cocycle:** `μ(Λ, Γ) + μ(Γ, Δ) = μ(Λ, Δ)`. -/
theorem relativeMaslovIndex_add (Λ Γ Δ : TotallyRealPath E)
    (h₀ : Λ 0 = Γ 0) (h₁ : Λ 1 = Γ 1) (h₀' : Γ 0 = Δ 0) (h₁' : Γ 1 = Δ 1) :
    relativeMaslovIndex Λ Γ h₀ h₁ + relativeMaslovIndex Γ Δ h₀' h₁' =
      relativeMaslovIndex Λ Δ (h₀.trans h₀') (h₁.trans h₁') := by
  rw [relativeMaslovIndex_eq_degree Λ Δ (h₀.trans h₀') (h₁.trans h₁')
    ((Λ.relativeMaslovPhasePath Γ h₀ h₁).mul (Γ.relativeMaslovPhasePath Δ h₀' h₁')) fun t => by
      simpa [mul_comm] using (Δ.isMaximalTotallyReal t).maslovPhase_mul_maslovPhase
        (Γ.isMaximalTotallyReal t) (Λ.isMaximalTotallyReal t),
    Circle.degree_mul, relativeMaslovIndex, relativeMaslovIndex]

/-- **Catenation property of the relative Maslov index:**
`μ(Λ₁ ⬝ Λ₂, Γ₁ ⬝ Γ₂) = μ(Λ₁, Γ₁) + μ(Λ₂, Γ₂)`. -/
theorem relativeMaslovIndex_trans (Λ₁ Λ₂ Γ₁ Γ₂ : TotallyRealPath E)
    (hΛ : Λ₁ 1 = Λ₂ 0) (hΓ : Γ₁ 1 = Γ₂ 0) (h₀ : Λ₁ 0 = Γ₁ 0) (h : Λ₁ 1 = Γ₁ 1)
    (h₁ : Λ₂ 1 = Γ₂ 1) :
    relativeMaslovIndex (Λ₁.trans Λ₂ hΛ) (Γ₁.trans Γ₂ hΓ) (by simpa using h₀)
        (by simpa using h₁) =
      relativeMaslovIndex Λ₁ Γ₁ h₀ h +
        relativeMaslovIndex Λ₂ Γ₂ (hΛ.symm.trans (h.trans hΓ)) h₁ := by
  rw [relativeMaslovIndex_eq_degree _ _ _ _ ((Λ₁.relativeMaslovPhasePath Γ₁ h₀ h).trans
    (Λ₂.relativeMaslovPhasePath Γ₂ (hΛ.symm.trans (h.trans hΓ)) h₁)) fun t => ?_,
    Circle.degree_trans, relativeMaslovIndex, relativeMaslovIndex]
  -- On each half, the catenated paths are the reparametrized pieces.
  rw [Path.trans_apply]
  split_ifs with ht <;>
  exact (IsMaximalTotallyReal.maslovPhase_congr_left _
    ((Γ₁.trans Γ₂ hΓ).isMaximalTotallyReal t) _ (by simp only [trans_apply, ht, ↓reduceDIte])).trans
    (IsMaximalTotallyReal.maslovPhase_congr _ _ _ (by simp only [trans_apply, ht, ↓reduceDIte]))

/-- **Reversal of the relative Maslov index:** reversing both paths negates the relative index. -/
theorem relativeMaslovIndex_symm (Λ Γ : TotallyRealPath E)
    (h₀ : Λ 0 = Γ 0) (h₁ : Λ 1 = Γ 1) :
    relativeMaslovIndex Λ.symm Γ.symm (by simpa using h₁) (by simpa using h₀) =
      -relativeMaslovIndex Λ Γ h₀ h₁ := by
  rw [relativeMaslovIndex_eq_degree _ _ _ _ (Λ.relativeMaslovPhasePath Γ h₀ h₁).symm
    fun t => ?_, Circle.degree_symm, relativeMaslovIndex]
  rw [Path.symm_apply, Function.comp_apply, relativeMaslovPhasePath_apply]
  exact (IsMaximalTotallyReal.maslovPhase_congr_left _ (Γ.symm.isMaximalTotallyReal t) _
    (symm_apply Γ t).symm).trans
    (IsMaximalTotallyReal.maslovPhase_congr _ _ _ (symm_apply Λ t).symm)

/-- **Naturality of the relative Maslov index:** moving both paths by the same continuous path
`B` of complex-linear automorphisms does not change their relative index,
`μ(B Λ, B Γ) = μ(Λ, Γ)`. -/
@[simp]
theorem relativeMaslovIndex_map (Λ Γ : TotallyRealPath E) (B : I → E ≃L[ℂ] E)
    (hB : Continuous fun t => (B t : E →L[ℂ] E)) (h₀ : Λ 0 = Γ 0) (h₁ : Λ 1 = Γ 1) :
    relativeMaslovIndex (Λ.map B hB) (Γ.map B hB) (by simp [h₀]) (by simp [h₁]) =
      relativeMaslovIndex Λ Γ h₀ h₁ := by
  refine (relativeMaslovIndex_eq_degree _ _ _ _ (Λ.relativeMaslovPhasePath Γ h₀ h₁)
    fun t => ?_).trans (relativeMaslovIndex_def Λ Γ h₀ h₁).symm
  rw [relativeMaslovPhasePath_apply, ← (Γ.isMaximalTotallyReal t).maslovPhase_map_map
    (Λ.isMaximalTotallyReal t) (B t).toLinearEquiv]
  exact (IsMaximalTotallyReal.maslovPhase_congr_left _ ((Γ.map B hB).isMaximalTotallyReal t) _
    (map_apply Γ B hB t).symm).trans
    (IsMaximalTotallyReal.maslovPhase_congr _ _ _ (map_apply Λ B hB t).symm)

/-- **Homotopy invariance of the relative Maslov index.** Let `A (s, t)` and `B (s, t)` be
continuous two-parameter families of complex-linear automorphisms and `L₀` a maximal totally real
subspace such that, for every `s`, the paths `t ↦ A (s, t) L₀` and `t ↦ B (s, t) L₀` have the same
endpoints; the common endpoints may move with `s`. Then the relative index of the two paths at
`s = 0` equals that at `s = 1`. -/
theorem relativeMaslovIndex_eq_of_homotopy (Λ₀ Γ₀ Λ₁ Γ₁ : TotallyRealPath E)
    {L₀ : Submodule ℝ E}
    (hL₀ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₀)
    (A B : I × I → E ≃L[ℂ] E) (hA : Continuous fun p => (A p : E →L[ℂ] E))
    (hB : Continuous fun p => (B p : E →L[ℂ] E))
    (hΛ₀ : ∀ t, Λ₀ t = L₀.map (((A (0, t)).toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ))
    (hΓ₀ : ∀ t, Γ₀ t = L₀.map (((B (0, t)).toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ))
    (hΛ₁ : ∀ t, Λ₁ t = L₀.map (((A (1, t)).toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ))
    (hΓ₁ : ∀ t, Γ₁ t = L₀.map (((B (1, t)).toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ))
    (hAB₀ : ∀ s, L₀.map (((A (s, 0)).toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ) =
      L₀.map (((B (s, 0)).toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ))
    (hAB₁ : ∀ s, L₀.map (((A (s, 1)).toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ) =
      L₀.map (((B (s, 1)).toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ)) :
    relativeMaslovIndex Λ₀ Γ₀ (by rw [hΛ₀, hΓ₀, hAB₀]) (by rw [hΛ₀, hΓ₀, hAB₁]) =
      relativeMaslovIndex Λ₁ Γ₁ (by rw [hΛ₁, hΓ₁, hAB₀]) (by rw [hΛ₁, hΓ₁, hAB₁]) := by
  -- The two-parameter family of relative phases
  -- `ρ(B (s, t) L₀, A (s, t) L₀) = ρ(L₀, A (s, t) L₀) / ρ(L₀, B (s, t) L₀)`.
  have hphase (p : I × I) : (hL₀.map_linearEquiv (B p).toLinearEquiv).maslovPhase
      (hL₀.map_linearEquiv (A p).toLinearEquiv) =
      hL₀.maslovPhase (hL₀.map_linearEquiv (A p).toLinearEquiv) /
        hL₀.maslovPhase (hL₀.map_linearEquiv (B p).toLinearEquiv) :=
    (hL₀.maslovPhase_div_maslovPhase _ _).symm
  let F : C(I × I, Circle) :=
    ⟨fun p => ⟨(hL₀.map_linearEquiv (B p).toLinearEquiv).maslovPhase
        (hL₀.map_linearEquiv (A p).toLinearEquiv),
      mem_sphere_zero_iff_norm.2 (IsMaximalTotallyReal.norm_maslovPhase _ _)⟩, by
      refine Continuous.subtype_mk ?_ _
      simp_rw [hphase, IsMaximalTotallyReal.maslovPhase_map]
      refine (continuous_det_div_conj A hA).div (continuous_det_div_conj B hB) fun p => ?_
      rw [← IsMaximalTotallyReal.maslovPhase_map hL₀]
      exact hL₀.maslovPhase_ne_zero _⟩
  -- At both ends of the `t`-interval the two subspaces agree, so the phase is `1` there.
  have hF (s : I) (t : I) (h : L₀.map (((A (s, t)).toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ) =
      L₀.map (((B (s, t)).toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ)) : F (s, t) = 1 :=
    Circle.ext <| ((hL₀.map_linearEquiv (B (s, t)).toLinearEquiv).maslovPhase_congr _
      (hL₀.map_linearEquiv (B (s, t)).toLinearEquiv) h).trans
      (IsMaximalTotallyReal.maslovPhase_self _)
  let γ (s : I) : Path (F (s, 0)) (F (s, 0)) :=
    { toFun := fun t => F (s, t)
      continuous_toFun := by fun_prop
      source' := rfl
      target' := (hF s 1 (hAB₁ s)).trans (hF s 0 (hAB₀ s)).symm }
  have hμ₀ := relativeMaslovIndex_eq_degree Λ₀ Γ₀ (by rw [hΛ₀, hΓ₀, hAB₀])
    (by rw [hΛ₀, hΓ₀, hAB₁]) (γ 0) fun t =>
      ((IsMaximalTotallyReal.maslovPhase_congr_left _ _ _ (hΓ₀ t).symm).trans
        (IsMaximalTotallyReal.maslovPhase_congr _ _ _ (hΛ₀ t).symm))
  have hμ₁ := relativeMaslovIndex_eq_degree Λ₁ Γ₁ (by rw [hΛ₁, hΓ₁, hAB₀])
    (by rw [hΛ₁, hΓ₁, hAB₁]) (γ 1) fun t =>
      ((IsMaximalTotallyReal.maslovPhase_congr_left _ _ _ (hΓ₁ t).symm).trans
        (IsMaximalTotallyReal.maslovPhase_congr _ _ _ (hΛ₁ t).symm))
  rw [hμ₀, hμ₁]
  exact Circle.degree_eq_of_homotopy (γ 0) (γ 1) F (fun _ => rfl) (fun _ => rfl)
    fun s => (hF s 0 (hAB₀ s)).trans (hF s 1 (hAB₁ s)).symm

/-- Compute the relative Maslov index from continuous angle lifts of the two Maslov phase paths.
If the change in the difference of the angles is `2π n`, the relative index is `n`. -/
theorem relativeMaslovIndex_eq_of_angle_lifts (Λ Γ : TotallyRealPath E)
    (h₀ : Λ 0 = Γ 0) (h₁ : Λ 1 = Γ 1) {θΛ θΓ : I → ℝ}
    (hθΛ : Continuous θΛ) (hθΓ : Continuous θΓ)
    (hΛ : ∀ t, Circle.exp (θΛ t) =
      Λ.maslovPhasePath (Λ.isMaximalTotallyReal 0) t)
    (hΓ : ∀ t, Circle.exp (θΓ t) =
      Γ.maslovPhasePath (Λ.isMaximalTotallyReal 0) t)
    {n : ℤ}
    (hangle : (θΛ 1 - θΓ 1) - (θΛ 0 - θΓ 0) = n * (2 * π)) :
    relativeMaslovIndex Λ Γ h₀ h₁ = n := by
  have hL := Λ.isMaximalTotallyReal 0
  have hθγ (t : I) : Circle.exp (θΛ t - θΓ t) = Λ.relativeMaslovPhasePath Γ h₀ h₁ t := by
    refine Circle.ext ?_
    simp [hΛ, hΓ, hL.maslovPhase_div_maslovPhase]
  exact Circle.degree_eq_of_sub_eq _ (hθΛ.sub hθΓ) hθγ hangle

end TotallyRealPath

namespace TotallyRealLoop

variable {E}

/-- A loop of maximal totally real subspaces, read as a path. -/
def toTotallyRealPath (Λ : TotallyRealLoop E) : TotallyRealPath E :=
  ⟨Λ.toFun, Λ.exists_frame⟩

@[simp]
theorem toTotallyRealPath_apply (Λ : TotallyRealLoop E) (t : I) : Λ.toTotallyRealPath t = Λ t :=
  (rfl)

variable [FiniteDimensional ℂ E]

/-- For two loops of maximal totally real subspaces with the same base subspace, the relative
Maslov index is the difference of their Maslov indices: `μ(Λ, Γ) = μ(Λ) - μ(Γ)`. -/
theorem relativeMaslovIndex_toTotallyRealPath (Λ Γ : TotallyRealLoop E) (h : Λ 0 = Γ 0) :
    Λ.toTotallyRealPath.relativeMaslovIndex Γ.toTotallyRealPath (by simpa using h)
      (by simpa [← Λ.toFun_zero_eq_toFun_one, ← Γ.toFun_zero_eq_toFun_one] using h) =
      Λ.maslovIndex - Γ.maslovIndex := by
  have hL := Λ.isMaximalTotallyReal 0
  -- Both Maslov indices are read off with the common reference `Λ 0 = Γ 0`.
  obtain ⟨θΛ, hθΛ', -⟩ := Circle.isCoveringMap_exp.exists_path_lifts
    (Λ.toTotallyRealPath.maslovPhasePath hL)
    (Complex.arg (Λ.toTotallyRealPath.maslovPhasePath hL 0)) (Circle.exp_arg _).symm
  obtain ⟨θΓ, hθΓ', -⟩ := Circle.isCoveringMap_exp.exists_path_lifts
    (Γ.toTotallyRealPath.maslovPhasePath hL)
    (Complex.arg (Γ.toTotallyRealPath.maslovPhasePath hL 0)) (Circle.exp_arg _).symm
  have hθΛ (t : I) : Circle.exp (θΛ t) = Λ.toTotallyRealPath.maslovPhasePath hL t :=
    congr_fun hθΛ' t
  have hθΓ (t : I) : Circle.exp (θΓ t) = Γ.toTotallyRealPath.maslovPhasePath hL t :=
    congr_fun hθΓ' t
  have hμΛ := Λ.sub_eq_maslovIndex_mul hL θΛ.continuous fun t => by
    rw [← Circle.coe_exp, hθΛ, TotallyRealPath.maslovPhasePath_apply]
    exact hL.maslovPhase_congr _ _ (toTotallyRealPath_apply Λ t)
  have hμΓ := Γ.sub_eq_maslovIndex_mul hL θΓ.continuous fun t => by
    rw [← Circle.coe_exp, hθΓ, TotallyRealPath.maslovPhasePath_apply]
    exact hL.maslovPhase_congr _ _ (toTotallyRealPath_apply Γ t)
  refine TotallyRealPath.relativeMaslovIndex_eq_of_angle_lifts _ _ _ _ θΛ.continuous
    θΓ.continuous hθΛ hθΓ ?_
  push_cast
  linarith

end TotallyRealLoop

end TauCeti
