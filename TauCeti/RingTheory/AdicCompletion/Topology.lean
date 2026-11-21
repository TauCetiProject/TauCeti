/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import TauCeti.RingTheory.AdicCompletion.Pow
public import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology.Basic
public import TauCeti.Topology.Algebra.TopologicallyNilpotent.Basic
import TauCeti.LinearAlgebra.Quotient.Basic
import TauCeti.RingTheory.Ideal.Quotient.Operations

/-!
# Adic topology and adic completeness

Two ideals defining the same topology on a ring give the same notion of separated completeness,
for the ring itself and for every module (`IsAdic.isAdicComplete_iff_of_isAdic`), and in an
`I`-adically complete `I`-adic ring the topological nilradical lies in the Jacobson radical
(`IsAdic.topologicalNilradical_le_jacobson`). When `N` is `I`-adically complete with zero
neighbourhood basis `I ^ n • ⊤`, the lift `IsAdicComplete.StrictMono.lift` of a compatible tower
`M →ₗ[R] N ⧸ (I ^ a n • ⊤)` with open kernels is continuous
(`IsAdicComplete.StrictMono.liftContinuousLinearMap`); specializing to `R` yields
`IsAdic.liftIdealTower`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §7.1.9.
-/

public section

open Filter Topology

namespace IsAdicComplete.StrictMono

section Continuity

variable {R : Type*} [CommRing R] (I : Ideal R)
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
variable {N : Type*} [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N]
variable [IsAdicComplete I N]
variable (hbasis : (𝓝 (0 : N)).HasBasis (fun _ : ℕ ↦ True)
  fun n ↦ (↑(I ^ n • (⊤ : Submodule R N)) : Set N))
variable {a : ℕ → ℕ} (ha : StrictMono a)
variable (f : (n : ℕ) → M →ₗ[R] N ⧸ (I ^ a n • ⊤ : Submodule R N))
variable (hf : ∀ {m : ℕ}, Submodule.factorPow I N (ha.monotone m.le_succ) ∘ₗ f (m + 1) = f m)
variable (hopen : ∀ n : ℕ, IsOpen (LinearMap.ker (f n) : Set M))

include hbasis hopen in
/-- If `N` is `I`-adically complete with zero-neighbourhood basis `I ^ n • ⊤`, then the lift of a
compatible strictly increasing tower `f` with open kernels is continuous. -/
theorem continuous_lift_of_hasBasis : Continuous (lift I ha f hf) := by
  refine continuous_of_continuousAt_zero (lift I ha f hf).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, hbasis.tendsto_right_iff]
  intro n _
  refine Filter.mem_of_superset ((hopen n).mem_nhds (zero_mem _)) fun m hm ↦ ?_
  rw [Set.mem_ofPred_eq, LinearMap.toAddMonoidHom_coe, SetLike.mem_coe]
  exact Submodule.pow_smul_top_le I N (ha.id_le n) <| by
    rw [← Submodule.Quotient.mk_eq_zero, mk_lift]
    exact LinearMap.mem_ker.mp hm

include hbasis hopen in
/-- Bundle `IsAdicComplete.StrictMono.lift` as `M →L[R] N`. -/
noncomputable def liftContinuousLinearMap : M →L[R] N :=
  ⟨lift I ha f hf, continuous_lift_of_hasBasis I hbasis ha f hf hopen⟩

/-- The underlying linear map of `liftContinuousLinearMap` is `IsAdicComplete.StrictMono.lift`. -/
@[grind =]
theorem toLinearMap_liftContinuousLinearMap :
    (liftContinuousLinearMap I hbasis ha f hf hopen).toLinearMap = lift I ha f hf := by rfl

/-- Underlying evaluation of `liftContinuousLinearMap`. -/
@[grind =]
theorem liftContinuousLinearMap_apply (m : M) :
    liftContinuousLinearMap I hbasis ha f hf hopen m = lift I ha f hf m := by rfl

/-- Composing `liftContinuousLinearMap` with the quotient projection to `N ⧸ (I ^ a n • ⊤)` recovers
`f n`. -/
-- Not `@[grind =]` because `n` only occurs under `a n`.
@[simp]
theorem mk_liftContinuousLinearMap (n : ℕ) (m : M) :
    Submodule.Quotient.mk (p := (I ^ a n • ⊤ : Submodule R N))
      (liftContinuousLinearMap I hbasis ha f hf hopen m) = f n m := by
  rw [liftContinuousLinearMap_apply, mk_lift]

/-- Uniqueness of `liftContinuousLinearMap`. -/
theorem eq_liftContinuousLinearMap {F : M →L[R] N}
    (hF : ∀ n m, Submodule.Quotient.mk (p := (I ^ a n • ⊤ : Submodule R N)) (F m) = f n m) :
    F = liftContinuousLinearMap I hbasis ha f hf hopen := by
  ext m
  exact LinearMap.congr_fun
    (eq_lift I ha f hf (F := F.toLinearMap) fun n ↦ LinearMap.ext fun x ↦ hF n x) m

end Continuity

end IsAdicComplete.StrictMono

namespace IsAdic

variable {R : Type*} [CommRing R] [TopologicalSpace R] {I J : Ideal R}
  {M : Type*} [AddCommGroup M] [Module R M]

/-- Separated adic completeness of a module depends only on the topology defined by the ideal on
the ring. There is no finite generation hypothesis on either ideal. -/
theorem isAdicComplete_iff_of_isAdic (hI : IsAdic I) (hJ : IsAdic J) :
    IsAdicComplete I M ↔ IsAdicComplete J M := by
  obtain ⟨-, k, hJI⟩ := hI.isAdic_iff_isOpen_and_exists_pow_le.mp hJ
  obtain ⟨-, l, hIJ⟩ := hJ.isAdic_iff_isOpen_and_exists_pow_le.mp hI
  exact ⟨fun _ ↦ .of_pow_le_of_pow_le hJI hIJ, fun _ ↦ .of_pow_le_of_pow_le hIJ hJI⟩

/-- In an `I`-adically complete ring whose topology is `I`-adic, the topological nilradical lies in
the Jacobson radical. -/
theorem topologicalNilradical_le_jacobson [IsLinearTopology R R] (hI : IsAdic I)
    [IsAdicComplete I R] : topologicalNilradical R ≤ Ring.jacobson R := by
  rw [← Ideal.jacobson_bot]
  refine topologicalNilradical_le_jacobson_bot (by simpa using hI.isOpen_pow 1) ?_
  rw [Ideal.jacobson_bot]
  exact IsAdicComplete.le_jacobson I

/-- In an `I`-adic ring, the submodules `I ^ n • ⊤` form a neighbourhood basis of zero. -/
theorem hasBasis_nhds_zero_smul_top (hI : IsAdic I) :
    (𝓝 (0 : R)).HasBasis (fun _ : ℕ ↦ True)
      fun n ↦ (↑(I ^ n • (⊤ : Submodule R R)) : Set R) := by
  simpa only [smul_eq_mul, Ideal.mul_top] using hI.hasBasis_nhds_zero

section TowerLift

variable [TopologicalSpace M] [IsTopologicalAddGroup M]

/-- Specialization of `continuous_lift_of_hasBasis` to an `I`-adically complete `I`-adic ring. -/
theorem continuous_strictMono_lift (hI : IsAdic I) [IsAdicComplete I R]
    {a : ℕ → ℕ} (ha : StrictMono a)
    (f : (n : ℕ) → M →ₗ[R] R ⧸ (I ^ a n • ⊤ : Submodule R R))
    (hf : ∀ {m : ℕ}, Submodule.factorPow I R (ha.monotone m.le_succ) ∘ₗ f (m + 1) = f m)
    (hopen : ∀ n : ℕ, IsOpen (LinearMap.ker (f n) : Set M)) :
    Continuous (IsAdicComplete.StrictMono.lift I ha f hf) :=
  have := hI.nonarchimedeanRing
  IsAdicComplete.StrictMono.continuous_lift_of_hasBasis
    I hI.hasBasis_nhds_zero_smul_top ha f hf hopen

section LiftIdealTower

variable (hI : IsAdic I) [IsAdicComplete I R] {a : ℕ → ℕ} (ha : StrictMono a)
  {K : ℕ → Ideal R} (hK : ∀ n, K n = I ^ a n) {hle : ∀ n, K (n + 1) ≤ K n}
  (g : (n : ℕ) → M →ₗ[R] R ⧸ K n) (hopen : ∀ n, IsOpen (LinearMap.ker (g n) : Set M))
  (hcomp : ∀ n m, Ideal.Quotient.factor (hle n) (g (n + 1) m) = g n m)

/-- Assemble a compatible tower `g n : M →ₗ[R] R ⧸ K n` (`K n = I ^ a n`) with open kernels into
`M →L[R] R`. -/
noncomputable def liftIdealTower : M →L[R] R :=
  have := hI.nonarchimedeanRing
  have heq (n : ℕ) : K n = (I ^ a n • (⊤ : Submodule R R) : Ideal R) := by
    rw [hK n, smul_eq_mul, Ideal.mul_top]
  let f (n : ℕ) : M →ₗ[R] R ⧸ (I ^ a n • (⊤ : Submodule R R)) :=
    (Submodule.quotEquivOfEq _ _ (heq n)).toLinearMap.comp (g n)
  have hf : ∀ {n : ℕ},
      Submodule.factorPow I R (ha.monotone n.le_succ) ∘ₗ f (n + 1) = f n := fun {n} ↦ by
    ext m
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, f]
    rw [Submodule.factor_quotEquivOfEq (heq (n + 1)) (heq n) (hle n),
      Submodule.factor_eq_factor, hcomp n m]
  IsAdicComplete.StrictMono.liftContinuousLinearMap I hI.hasBasis_nhds_zero_smul_top ha f hf
    fun n ↦ by
      rw [LinearMap.ker_comp_of_ker_eq_bot (g n) (LinearEquiv.ker _)]
      exact hopen n

/-- Reducing `IsAdic.liftIdealTower` modulo `K n` recovers `g n`. -/
-- Not `@[grind =]` because `n` only occurs under `K n`.
@[simp]
theorem mk_liftIdealTower (n : ℕ) (m : M) :
    Ideal.Quotient.mk (K n) (hI.liftIdealTower ha hK g hopen hcomp m) = g n m := by
  have := hI.nonarchimedeanRing
  have heq : K n = (I ^ a n • (⊤ : Submodule R R) : Ideal R) := by
    rw [hK n, smul_eq_mul, Ideal.mul_top]
  apply (Submodule.quotEquivOfEq _ _ heq).injective
  rw [Submodule.quotEquivOfEq_ideal_mk, liftIdealTower, ← Ideal.Quotient.mk_eq_mk,
    IsAdicComplete.StrictMono.mk_liftContinuousLinearMap, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap]

/-- Uniqueness of `IsAdic.liftIdealTower`. -/
theorem eq_liftIdealTower {F : M →L[R] R}
    (hF : ∀ n m, Ideal.Quotient.mk (K n) (F m) = g n m) :
    F = hI.liftIdealTower ha hK g hopen hcomp := by
  ext m
  exact congr_fun (IsHausdorff.StrictMono.funext' I ha fun n x ↦ by
    rw [← Submodule.quotEquivOfEq_ideal_mk (hK n), ← Submodule.quotEquivOfEq_ideal_mk (hK n),
      hF n x, mk_liftIdealTower]) m

end LiftIdealTower

end TowerLift

end IsAdic
