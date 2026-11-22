/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorPower.Flag.Basic
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Homogeneous
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace
import TauCeti.LinearAlgebra.ExteriorPower.Basic
import TauCeti.LinearAlgebra.ExteriorPower.Basis
import TauCeti.LinearAlgebra.ExteriorPower.Decomposable
import TauCeti.LinearAlgebra.SymmetricAlgebra.Evaluation
import TauCeti.LinearAlgebra.SymmetricAlgebra.QuadraticForm
import TauCeti.LinearAlgebra.SymmetricAlgebra.Semilinear
import TauCeti.LinearAlgebra.TensorProduct.Segre

/-!
# The affine cone of exterior flag vectors

Scalar multiples of `exteriorFlagVector R d v` in `FlagSpace R M d` form
`TauCeti.exteriorPower.exteriorFlagCone R M d`. Over a field `k` with `M` finite-dimensional (in
arbitrary characteristic), `exteriorFlagCone k M d` is cut out by the degree-`2` homogeneous
polynomials `TauCeti.exteriorPower.exteriorFlagForms k M d`, and when `d = Module.finrank k M`,
every nonzero element is a unit multiple of `exteriorFlagVector k d b` for a basis `b`.

## Main definitions

* `TauCeti.exteriorPower.exteriorFlagCone`: scalar multiples of `exteriorFlagVector`.
* `TauCeti.exteriorPower.exteriorFlagForms`: degree-`2` forms vanishing on `exteriorFlagCone`.

## Main results

* `TauCeti.exteriorPower.mem_exteriorFlagCone_iff`: over a field, membership in
  `exteriorFlagCone k M d` is equivalent to vanishing of all forms in `exteriorFlagForms k M d`.
* `TauCeti.exteriorPower.exists_basis_of_mem_exteriorFlagCone_of_finrank_eq`: in degree
  `Module.finrank k M`, nonzero cone vectors arise from bases of `M`.
-/

public section

open scoped TensorProduct

namespace TauCeti.exteriorPower

universe u v w

section ConeDefinitions

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

/-- The affine cone of exterior flag vectors in `FlagSpace R M d`: all scalar multiples of
`exteriorFlagVector R d v` as `v` ranges over `Fin d → M`. -/
def exteriorFlagCone (d : ℕ) : Set (FlagSpace R M d) :=
  {w | ∃ (c : R) (v : Fin d → M), w = c • exteriorFlagVector R d v}

/-- The set of degree-`2` homogeneous polynomials in
`SymmetricAlgebra R (Module.Dual R (FlagSpace R M d))` that vanish identically on
`exteriorFlagCone R M d`. -/
def exteriorFlagForms (d : ℕ) :
    Set (_root_.SymmetricAlgebra R (Module.Dual R (FlagSpace R M d))) :=
  {s | s ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R (FlagSpace R M d)) 2 ∧
    ∀ w ∈ exteriorFlagCone R M d,
      _root_.SymmetricAlgebra.lift (Module.Dual.eval R (FlagSpace R M d) w) s = 0}

variable {R M}

/-- Characterization of membership in `exteriorFlagCone R M d`. -/
theorem mem_exteriorFlagCone_iff_exists_smul {d : ℕ} {w : FlagSpace R M d} :
    w ∈ exteriorFlagCone R M d ↔
      ∃ (c : R) (v : Fin d → M), w = c • exteriorFlagVector R d v :=
  Iff.rfl

/-- Characterization of membership in `exteriorFlagForms R M d`. -/
theorem mem_exteriorFlagForms_iff {d : ℕ}
    {s : _root_.SymmetricAlgebra R (Module.Dual R (FlagSpace R M d))} :
    s ∈ exteriorFlagForms R M d ↔
      s ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R (FlagSpace R M d)) 2 ∧
        ∀ w ∈ exteriorFlagCone R M d,
          _root_.SymmetricAlgebra.lift (Module.Dual.eval R (FlagSpace R M d) w) s = 0 :=
  Iff.rfl

/-- Zero belongs to `exteriorFlagCone R M d`. -/
@[simp]
theorem zero_mem_exteriorFlagCone (d : ℕ) : (0 : FlagSpace R M d) ∈ exteriorFlagCone R M d :=
  ⟨0, 0, by simp⟩

/-- Every exterior flag vector belongs to `exteriorFlagCone R M d`. -/
@[simp]
theorem exteriorFlagVector_mem_exteriorFlagCone {d : ℕ} (v : Fin d → M) :
    exteriorFlagVector R d v ∈ exteriorFlagCone R M d :=
  ⟨1, v, by simp⟩

/-- The cone `exteriorFlagCone R M d` is closed under scalar multiplication. -/
theorem smul_mem_exteriorFlagCone {d : ℕ} (c : R) {w : FlagSpace R M d}
    (hw : w ∈ exteriorFlagCone R M d) : c • w ∈ exteriorFlagCone R M d := by
  obtain ⟨a, v, rfl⟩ := hw
  exact ⟨c * a, v, (mul_smul c a _).symm⟩

/-- Induced flag maps carry `exteriorFlagCone R M d` into `exteriorFlagCone R N d`. -/
theorem exteriorFlagMap_mem_exteriorFlagCone {N : Type w} [AddCommGroup N] [Module R N]
    {d : ℕ} (f : M →ₗ[R] N) {w : FlagSpace R M d} (hw : w ∈ exteriorFlagCone R M d) :
    exteriorFlagMap d f w ∈ exteriorFlagCone R N d := by
  obtain ⟨c, v, rfl⟩ := hw
  exact ⟨c, f ∘ v, by rw [map_smul, exteriorFlagMap_exteriorFlagVector]⟩

/-- Every form in `exteriorFlagForms R M d` is homogeneous of degree `2`. -/
theorem mem_homogeneousSubmodule_of_mem_exteriorFlagForms {d : ℕ}
    {s : _root_.SymmetricAlgebra R (Module.Dual R (FlagSpace R M d))}
    (hs : s ∈ exteriorFlagForms R M d) :
    s ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R (FlagSpace R M d)) 2 :=
  hs.1

/-- If a linear map `p` sends `exteriorFlagCone` into `exteriorFlagCone`, pulling back along
`p.dualMap` sends `exteriorFlagForms` into `exteriorFlagForms`. -/
theorem map_dualMap_mem_exteriorFlagForms {N : Type w} [AddCommGroup N] [Module R N]
    {d₁ d₂ : ℕ} {p : FlagSpace R M d₁ →ₗ[R] FlagSpace R N d₂}
    (hp : ∀ w ∈ exteriorFlagCone R M d₁, p w ∈ exteriorFlagCone R N d₂)
    {s : _root_.SymmetricAlgebra R (Module.Dual R (FlagSpace R N d₂))}
    (hs : s ∈ exteriorFlagForms R N d₂) :
    _root_.SymmetricAlgebra.map R p.dualMap s ∈ exteriorFlagForms R M d₁ :=
  ⟨TauCeti.SymmetricAlgebra.map_mem_homogeneousSubmodule p.dualMap hs.1, fun w hw ↦ by
    rw [_root_.SymmetricAlgebra.lift_eval_map_dualMap]
    exact hs.2 (p w) (hp w hw)⟩

end ConeDefinitions

section QuadraticCriterion

variable {k : Type u} {M : Type v} [Field k] [AddCommGroup M] [Module k M]

private theorem exists_tmul_of_forall_exteriorFlagForms {r : ℕ} {w : FlagSpace k M (r + 1)}
    (hw : ∀ s ∈ exteriorFlagForms k M (r + 1),
      _root_.SymmetricAlgebra.lift (Module.Dual.eval k (FlagSpace k M (r + 1)) w) s = 0) :
    ∃ (w_r : FlagSpace k M r) (θ : ⋀[k]^(r + 1) M),
      w = (flagSpaceSuccEquiv k M r).symm (w_r ⊗ₜ[k] θ) := by
  suffices ∃ (w_r : FlagSpace k M r) (θ : ⋀[k]^(r + 1) M),
      flagSpaceSuccEquiv k M r w = w_r ⊗ₜ[k] θ by
    obtain ⟨w_r, θ, h⟩ := this
    exact ⟨w_r, θ, (flagSpaceSuccEquiv k M r).eq_symm_apply.mpr h⟩
  refine (TensorProduct.exists_eq_tmul_iff _).mpr fun φ₁ φ₂ ψ₁ ψ₂ ↦ ?_
  let δ := (flagSpaceSuccEquiv k M r).toLinearMap.dualMap ∘ₗ
    TensorProduct.dualDistrib k (FlagSpace k M r) (⋀[k]^(r + 1) M)
  let ι := _root_.SymmetricAlgebra.ι k (Module.Dual k (FlagSpace k M (r + 1)))
  let s :=
    ι (δ (φ₁ ⊗ₜ ψ₁)) * ι (δ (φ₂ ⊗ₜ ψ₂)) -
      ι (δ (φ₁ ⊗ₜ ψ₂)) * ι (δ (φ₂ ⊗ₜ ψ₁))
  have hs : s ∈ exteriorFlagForms k M (r + 1) :=
    ⟨Submodule.sub_mem _
        (SetLike.mul_mem_graded (TauCeti.SymmetricAlgebra.ι_mem_homogeneousSubmodule _ _ _)
          (TauCeti.SymmetricAlgebra.ι_mem_homogeneousSubmodule _ _ _))
        (SetLike.mul_mem_graded (TauCeti.SymmetricAlgebra.ι_mem_homogeneousSubmodule _ _ _)
          (TauCeti.SymmetricAlgebra.ι_mem_homogeneousSubmodule _ _ _)), by
      rintro _ ⟨c, v, rfl⟩
      simp [s, ι, δ]
      ring⟩
  simpa [s, ι, δ, sub_eq_zero] using hw s hs

section FiniteDimensional

variable [FiniteDimensional k M]

private theorem decomposable_of_forall_exteriorFlagForms {r : ℕ}
    {w_r : FlagSpace k M r} {θ : ⋀[k]^(r + 1) M} (hw_r : w_r ≠ 0)
    (hw : ∀ s ∈ exteriorFlagForms k M (r + 1),
      _root_.SymmetricAlgebra.lift (Module.Dual.eval k (FlagSpace k M (r + 1))
        ((flagSpaceSuccEquiv k M r).symm (w_r ⊗ₜ[k] θ))) s = 0) :
    θ ∈ Set.range (_root_.exteriorPower.ιMulti k (r + 1)) := by
  let _ := Module.addCommMonoidToAddCommGroup k (M := FlagSpace k M r)
  let _ := Module.addCommMonoidToAddCommGroup k (M := ⋀[k]^(r + 1) M)
  obtain ⟨φ₀, hφ₀⟩ := Module.Projective.exists_dual_eq_one k hw_r
  let p₂ : FlagSpace k M (r + 1) →ₗ[k] ⋀[k]^(r + 1) M :=
    (TensorProduct.lid k (⋀[k]^(r + 1) M)).toLinearMap ∘ₗ
      TensorProduct.map φ₀ LinearMap.id ∘ₗ (flagSpaceSuccEquiv k M r).toLinearMap
  have hp₂ : p₂ ((flagSpaceSuccEquiv k M r).symm (w_r ⊗ₜ[k] θ)) = θ := by
    simp [p₂, hφ₀]
  refine (_root_.exteriorPower.mem_range_ιMulti_iff_forall_ι_contract_mul_eq_zero θ).mpr
    fun η ↦ (Module.forall_dual_apply_eq_zero_iff k _).mp fun ξ ↦ ?_
  let B : ⋀[k]^(r + 1) M →ₗ[k] ⋀[k]^(r + 1) M →ₗ[k] k :=
    LinearMap.mk₂ k
      (fun θ₁ θ₂ ↦ ξ (_root_.ExteriorAlgebra.ι k
        (_root_.exteriorPower.contract k M r η θ₁) * (θ₂ : ExteriorAlgebra k M)))
      (fun _ _ _ ↦ by simp [add_mul]) (fun _ _ _ ↦ by simp)
      (fun _ _ _ ↦ by simp [mul_add]) (fun _ _ _ ↦ by simp)
  let s := _root_.SymmetricAlgebra.map k p₂.dualMap
    (TauCeti.SymmetricAlgebra.bilinearToQuadForm B : _)
  have hs : s ∈ exteriorFlagForms k M (r + 1) :=
    ⟨TauCeti.SymmetricAlgebra.map_mem_homogeneousSubmodule _
        (TauCeti.SymmetricAlgebra.bilinearToQuadForm B).property, by
      rintro _ ⟨c, v, rfl⟩
      rw [_root_.SymmetricAlgebra.lift_eval_map_dualMap,
        TauCeti.SymmetricAlgebra.lift_eval_bilinearToQuadForm]
      have hpv : p₂ (c • exteriorFlagVector k (r + 1) v) =
          (c * φ₀ (exteriorFlagVector k r (v ∘ Fin.castSucc))) •
            _root_.exteriorPower.ιMulti k (r + 1) v := by
        simp [p₂, mul_smul]
      simp only [hpv, map_smul, LinearMap.smul_apply, B, LinearMap.mk₂_apply,
        _root_.exteriorPower.ιMulti_apply_coe,
        _root_.exteriorPower.ι_contract_mul_ιMulti_eq_zero, map_zero, smul_zero]⟩
  have hval := hw s hs
  rwa [_root_.SymmetricAlgebra.lift_eval_map_dualMap, hp₂,
    TauCeti.SymmetricAlgebra.lift_eval_bilinearToQuadForm] at hval

private noncomputable def incidenceDual {m : ℕ}
    (η : ⋀[k]^m (Module.Dual k M)) (φ : Module.Dual k (FlagSpace k M m))
    (ξ : Module.Dual k (ExteriorAlgebra k M)) :
    Module.Dual k (FlagSpace k M (m + 2)) :=
  let g₁ : FlagSpace k M (m + 1) →ₗ[k] M :=
    _root_.exteriorPower.contract k M m η ∘ₗ
      (TensorProduct.lid k (⋀[k]^(m + 1) M)).toLinearMap ∘ₗ
        TensorProduct.map φ LinearMap.id ∘ₗ (flagSpaceSuccEquiv k M m).toLinearMap
  TensorProduct.lift (LinearMap.mk₂ k
    (fun (a : FlagSpace k M (m + 1)) (β : ⋀[k]^(m + 2) M) ↦
      ξ (_root_.ExteriorAlgebra.ι k (g₁ a) * (β : ExteriorAlgebra k M)))
    (fun _ _ _ ↦ by simp [add_mul]) (fun _ _ _ ↦ by simp)
    (fun _ _ _ ↦ by simp [mul_add]) (fun _ _ _ ↦ by simp)) ∘ₗ
      (flagSpaceSuccEquiv k M (m + 1)).toLinearMap

private theorem incidenceDual_exteriorFlagVector_eq_zero {m : ℕ}
    (η : ⋀[k]^m (Module.Dual k M)) (φ : Module.Dual k (FlagSpace k M m))
    (ξ : Module.Dual k (ExteriorAlgebra k M)) (v : Fin (m + 2) → M) :
    incidenceDual η φ ξ (exteriorFlagVector k (m + 2) v) = 0 := by
  have hmem : _root_.exteriorPower.contract k M m η
      (_root_.exteriorPower.ιMulti k (m + 1) (v ∘ Fin.castSucc)) ∈
      Submodule.span k (Set.range v) :=
    Submodule.span_mono (Set.range_comp_subset_range _ _)
      (_root_.exteriorPower.contract_ιMulti_mem_span η (v ∘ Fin.castSucc))
  simp only [incidenceDual, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    flagSpaceSuccEquiv_exteriorFlagVector (r := m + 1), flagSpaceSuccEquiv_exteriorFlagVector,
    TensorProduct.lift.tmul, LinearMap.mk₂_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    TensorProduct.lid_tmul, map_smul, smul_mul_assoc]
  rw [_root_.exteriorPower.ι_mul_ιMulti_eq_zero_of_mem_span hmem, map_zero, smul_zero]

private theorem span_le_of_forall_exteriorFlagForms {r : ℕ} {c₀ : k} {u : Fin r → M}
    {v₀ : Fin (r + 1) → M} (hc₀ : c₀ ≠ 0) (hu : LinearIndependent k u)
    (hv₀ : LinearIndependent k v₀)
    (hw : ∀ s ∈ exteriorFlagForms k M (r + 1),
      _root_.SymmetricAlgebra.lift (Module.Dual.eval k (FlagSpace k M (r + 1))
        ((flagSpaceSuccEquiv k M r).symm ((c₀ • exteriorFlagVector k r u) ⊗ₜ[k]
          _root_.exteriorPower.ιMulti k (r + 1) v₀)))
        s = 0) :
    Submodule.span k (Set.range u) ≤ Submodule.span k (Set.range v₀) := by
  cases r with
  | zero => simp [Set.range_eq_empty]
  | succ m =>
    let _ := Module.addCommMonoidToAddCommGroup k (M := FlagSpace k M m)
    rw [← _root_.exteriorPower.range_contract_flip_ιMulti hu]
    rintro _ ⟨η, rfl⟩
    refine (mem_span_range_iff_ι_mul_ιMulti_eq_zero hv₀ _).mpr
      ((Module.forall_dual_apply_eq_zero_iff k _).mp fun ξ ↦ ?_)
    let y_m : FlagSpace k M m := exteriorFlagVector k m (u ∘ Fin.castSucc)
    have hy_m : y_m ≠ 0 :=
      exteriorFlagVector_ne_zero_iff.mpr (hu.comp _ (Fin.castSucc_injective m))
    obtain ⟨φ_m, hφ_m⟩ := Module.Projective.exists_dual_eq_one k hy_m
    let L := incidenceDual η φ_m ξ
    let s := _root_.SymmetricAlgebra.ι k _ L * _root_.SymmetricAlgebra.ι k _ L
    have hs : s ∈ exteriorFlagForms k M (m + 2) :=
      ⟨SetLike.mul_mem_graded (TauCeti.SymmetricAlgebra.ι_mem_homogeneousSubmodule _ _ L)
          (TauCeti.SymmetricAlgebra.ι_mem_homogeneousSubmodule _ _ L), by
        rintro _ ⟨c, v, rfl⟩
        simp only [s, map_mul, _root_.SymmetricAlgebra.lift_ι_apply, map_smul,
          LinearMap.smul_apply, Module.Dual.eval_apply]
        rw [show L (exteriorFlagVector k (m + 2) v) = 0 from
            incidenceDual_exteriorFlagVector_eq_zero η φ_m ξ v, smul_zero, mul_zero]⟩
    have hLw : L ((flagSpaceSuccEquiv k M (m + 1)).symm
        ((c₀ • exteriorFlagVector k (m + 1) u) ⊗ₜ[k]
          _root_.exteriorPower.ιMulti k (m + 2) v₀)) = 0 :=
      mul_self_eq_zero.mp (by simpa [s] using hw s hs)
    rw [LinearMap.flip_apply]
    simpa [L, incidenceDual, y_m, hφ_m, hc₀] using hLw

private theorem mem_exteriorFlagCone_succ_of_span_le {r : ℕ} {c₀ : k} {u : Fin r → M}
    {v₀ : Fin (r + 1) → M} (hu : LinearIndependent k u) (hv₀ : LinearIndependent k v₀)
    (hle : Submodule.span k (Set.range u) ≤ Submodule.span k (Set.range v₀)) :
    (flagSpaceSuccEquiv k M r).symm ((c₀ • exteriorFlagVector k r u) ⊗ₜ[k]
        _root_.exteriorPower.ιMulti k (r + 1) v₀) ∈
      exteriorFlagCone k M (r + 1) := by
  have hnot_le : ¬ Submodule.span k (Set.range v₀) ≤ Submodule.span k (Set.range u) := by
    intro hge
    have hdim := Submodule.finrank_mono hge
    rw [finrank_span_eq_card hv₀, finrank_span_eq_card hu, Fintype.card_fin,
      Fintype.card_fin] at hdim
    omega
  rw [Submodule.span_le, Set.subset_def] at hnot_le
  push Not at hnot_le
  obtain ⟨_, ⟨j, rfl⟩, hv₀j⟩ := hnot_le
  let v : Fin (r + 1) → M := Fin.snoc u (v₀ j)
  have hv : LinearIndependent k v := linearIndependent_finSnoc.mpr ⟨hu, hv₀j⟩
  have hv_le : Submodule.span k (Set.range v) ≤ Submodule.span k (Set.range v₀) := by
    rw [Fin.range_snoc, Submodule.span_insert]
    exact sup_le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
      (Submodule.subset_span (Set.mem_range_self j)))) hle
  have hv_span : Submodule.span k (Set.range v) = Submodule.span k (Set.range v₀) :=
    Submodule.eq_of_le_of_finrank_eq hv_le
      (by rw [finrank_span_eq_card hv, finrank_span_eq_card hv₀])
  obtain ⟨c₁, hc₁⟩ :=
    _root_.exteriorPower.exists_units_smul_ιMulti_of_span_eq hv₀ hv hv_span.symm
  refine ⟨c₀ * c₁, v, (flagSpaceSuccEquiv k M r).injective ?_⟩
  have hcast : v ∘ Fin.castSucc = u := funext fun x ↦ by simp [v]
  simp [hc₁, Units.smul_def, TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_smul,
    mul_comm, hcast]

/-- **Quadratic equations of the exterior flag cone.** Over a field `k` of arbitrary characteristic,
a vector in `FlagSpace k M d` for a finite-dimensional `k`-vector space `M` lies in
`exteriorFlagCone k M d` if and only if every quadratic form in `exteriorFlagForms k M d` vanishes
at it. -/
theorem mem_exteriorFlagCone_iff {d : ℕ} (w : FlagSpace k M d) :
    w ∈ exteriorFlagCone k M d ↔
      ∀ s ∈ exteriorFlagForms k M d,
        _root_.SymmetricAlgebra.lift (Module.Dual.eval k (FlagSpace k M d) w) s = 0 := by
  refine ⟨fun hw s hs ↦ hs.2 w hw, fun hw ↦ ?_⟩
  induction d with
  | zero =>
    refine ⟨_root_.exteriorPower.zeroEquiv k M (flagSpaceZeroEquiv k M w), Fin.elim0,
      ((flagSpaceZeroEquiv k M).trans (_root_.exteriorPower.zeroEquiv k M)).injective (by simp)⟩
  | succ r ih =>
    by_cases hw0 : w = 0
    · exact hw0 ▸ zero_mem_exteriorFlagCone (r + 1)
    obtain ⟨w_r, θ, rfl⟩ := exists_tmul_of_forall_exteriorFlagForms hw
    have hw_r0 : w_r ≠ 0 := fun h ↦ hw0 (by simp [h])
    have hθ0 : θ ≠ 0 := fun h ↦ hw0 (by simp [h])
    let _ := Module.addCommMonoidToAddCommGroup k (M := ⋀[k]^(r + 1) M)
    obtain ⟨ψ₀, hψ₀⟩ := Module.Projective.exists_dual_eq_one k hθ0
    let p₁ : FlagSpace k M (r + 1) →ₗ[k] FlagSpace k M r :=
      (TensorProduct.rid k (FlagSpace k M r)).toLinearMap ∘ₗ
        TensorProduct.map LinearMap.id ψ₀ ∘ₗ (flagSpaceSuccEquiv k M r).toLinearMap
    have hp₁_cone :
        ∀ z ∈ exteriorFlagCone k M (r + 1), p₁ z ∈ exteriorFlagCone k M r := by
      rintro _ ⟨c, v, rfl⟩
      exact ⟨c * ψ₀ (_root_.exteriorPower.ιMulti k (r + 1) v), v ∘ Fin.castSucc,
        by simp [p₁, mul_smul]⟩
    have hw_r_cone : w_r ∈ exteriorFlagCone k M r := ih w_r fun s₀ hs₀ ↦ by
      have hval := hw _ (map_dualMap_mem_exteriorFlagForms hp₁_cone hs₀)
      have hp₁w : p₁ ((flagSpaceSuccEquiv k M r).symm (w_r ⊗ₜ[k] θ)) = w_r := by
        simp [p₁, hψ₀]
      rwa [_root_.SymmetricAlgebra.lift_eval_map_dualMap, hp₁w] at hval
    obtain ⟨c₀, u, rfl⟩ := hw_r_cone
    have hc₀ : c₀ ≠ 0 := fun h ↦ hw_r0 (by simp [h])
    have hu : LinearIndependent k u :=
      exteriorFlagVector_ne_zero_iff.mp fun h ↦ hw_r0 (by simp [h])
    obtain ⟨v₀, hv₀_eq⟩ := decomposable_of_forall_exteriorFlagForms hw_r0 hw
    subst hv₀_eq
    have hv₀ : LinearIndependent k v₀ :=
      (_root_.exteriorPower.ιMulti_ne_zero_iff (K := k) v₀).mp hθ0
    exact mem_exteriorFlagCone_succ_of_span_le hu hv₀
      (span_le_of_forall_exteriorFlagForms hc₀ hu hv₀ hw)

end FiniteDimensional

end QuadraticCriterion

section BasisCone

variable {k : Type u} {M : Type v} [Field k] [AddCommGroup M] [Module k M]

/-- When `Module.finrank k M = d`, every nonzero vector in `exteriorFlagCone k M d` is a unit
multiple of the flag vector of a basis `b : Module.Basis (Fin d) k M`. -/
theorem exists_basis_of_mem_exteriorFlagCone_of_finrank_eq [FiniteDimensional k M] {d : ℕ}
    (hd : Module.finrank k M = d) {w : FlagSpace k M d} (hw : w ∈ exteriorFlagCone k M d)
    (hw0 : w ≠ 0) :
    ∃ (c : kˣ) (b : Module.Basis (Fin d) k M), w = c • exteriorFlagVector k d b := by
  obtain ⟨c, v, rfl⟩ := hw
  have hc : c ≠ 0 := fun h ↦ hw0 (by simp [h])
  have hv : LinearIndependent k v :=
    exteriorFlagVector_ne_zero_iff.mp fun h ↦ hw0 (by simp [h])
  let b : Module.Basis (Fin d) k M :=
    basisOfLinearIndependentOfCardEqFinrank' v hv ((Fintype.card_fin d).trans hd.symm)
  exact ⟨Units.mk0 c hc, b, by
    simp [b, Units.smul_def, coe_basisOfLinearIndependentOfCardEqFinrank']⟩

end BasisCone

end TauCeti.exteriorPower
