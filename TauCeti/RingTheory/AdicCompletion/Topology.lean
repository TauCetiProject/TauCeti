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
import TauCeti.RingTheory.Ideal.Quotient.PowTransition

/-!
# Adic topology and adic completeness

Two ideals defining the same topology on a ring give the same notion of separated completeness,
for the ring itself and for every module over it (`IsAdic.isAdicComplete_iff_of_isAdic`). Each of
the two ideals has a power inside the other, so their adic filtrations are cofinal in each other
and adic completeness transfers by `IsAdicComplete.of_pow_le_of_pow_le`. Callers need only specify
the ring topology: no uniform structure on the ring and no topology on the module is involved.

In an `I`-adically complete ring carrying the `I`-adic topology, `I` is open and contained in the
Jacobson radical, so the topological nilradical also lies in the Jacobson radical
(`IsAdic.topologicalNilradical_le_jacobson`).

When a target module `N` is `I`-adically complete and its zero neighbourhoods admit the adic basis
`I ^ n • ⊤`, the algebraic inverse-limit lift `IsAdicComplete.StrictMono.lift` of a compatible
tower of linear maps `M →ₗ[R] N ⧸ (I ^ a n • ⊤)` with open kernels is automatically continuous
(`IsAdicComplete.StrictMono.continuous_lift_of_hasBasis`, bundled as
`IsAdicComplete.StrictMono.liftContinuousLinearMap`). Specializing to an `I`-adically complete
ring `R` with the `I`-adic topology yields `IsAdic.liftIdealTower`, which assembles any compatible
tower of maps `M →ₗ[R] R ⧸ K n` with `K n = I ^ a n` and open kernels into a unique continuous
linear map `M →L[R] R`.

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

/-- If `N` is `I`-adically complete with zero-neighbourhood basis `I ^ n • ⊤`, then the lift of a
compatible strictly increasing tower of `R`-linear maps `M →ₗ[R] N ⧸ (I ^ a n • ⊤)` with open
kernels is continuous. -/
theorem continuous_lift_of_hasBasis
    (hbasis : (𝓝 (0 : N)).HasBasis (fun _ : ℕ ↦ True)
      fun n ↦ (↑(I ^ n • (⊤ : Submodule R N)) : Set N))
    {a : ℕ → ℕ} (ha : StrictMono a)
    (f : (n : ℕ) → M →ₗ[R] N ⧸ (I ^ a n • ⊤ : Submodule R N))
    (hf : ∀ {m : ℕ}, Submodule.factorPow I N (ha.monotone m.le_succ) ∘ₗ f (m + 1) = f m)
    (hopen : ∀ n : ℕ, IsOpen (LinearMap.ker (f n) : Set M)) :
    Continuous (lift I ha f hf) := by
  refine continuous_of_continuousAt_zero (lift I ha f hf).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, hbasis.tendsto_right_iff]
  intro n _
  refine Filter.mem_of_superset ((hopen n).mem_nhds (zero_mem _)) fun m hm ↦ ?_
  rw [Set.mem_ofPred_eq, LinearMap.toAddMonoidHom_coe, SetLike.mem_coe]
  have hm' : lift I ha f hf m ∈ (I ^ a n • ⊤ : Submodule R N) := by
    rw [← Submodule.Quotient.mk_eq_zero, mk_lift]
    exact LinearMap.mem_ker.mp hm
  exact Submodule.pow_smul_top_le I N (ha.id_le n) hm'

/-- Bundle `IsAdicComplete.StrictMono.lift` as a continuous `R`-linear map `M →L[R] N` when `N` has
zero-neighbourhood basis `I ^ n • ⊤` and every map in the tower has open kernel. -/
noncomputable def liftContinuousLinearMap
    (hbasis : (𝓝 (0 : N)).HasBasis (fun _ : ℕ ↦ True)
      fun n ↦ (↑(I ^ n • (⊤ : Submodule R N)) : Set N))
    {a : ℕ → ℕ} (ha : StrictMono a)
    (f : (n : ℕ) → M →ₗ[R] N ⧸ (I ^ a n • ⊤ : Submodule R N))
    (hf : ∀ {m : ℕ}, Submodule.factorPow I N (ha.monotone m.le_succ) ∘ₗ f (m + 1) = f m)
    (hopen : ∀ n : ℕ, IsOpen (LinearMap.ker (f n) : Set M)) :
    M →L[R] N :=
  ⟨lift I ha f hf, continuous_lift_of_hasBasis I hbasis ha f hf hopen⟩

/-- The underlying linear map of `liftContinuousLinearMap` is `IsAdicComplete.StrictMono.lift`. -/
@[grind =]
theorem toLinearMap_liftContinuousLinearMap
    (hbasis : (𝓝 (0 : N)).HasBasis (fun _ : ℕ ↦ True)
      fun n ↦ (↑(I ^ n • (⊤ : Submodule R N)) : Set N))
    {a : ℕ → ℕ} (ha : StrictMono a)
    (f : (n : ℕ) → M →ₗ[R] N ⧸ (I ^ a n • ⊤ : Submodule R N))
    (hf : ∀ {m : ℕ}, Submodule.factorPow I N (ha.monotone m.le_succ) ∘ₗ f (m + 1) = f m)
    (hopen : ∀ n : ℕ, IsOpen (LinearMap.ker (f n) : Set M)) :
    (liftContinuousLinearMap I hbasis ha f hf hopen).toLinearMap = lift I ha f hf := by
  rfl

/-- Underlying evaluation of `liftContinuousLinearMap`. -/
@[grind =]
theorem liftContinuousLinearMap_apply
    (hbasis : (𝓝 (0 : N)).HasBasis (fun _ : ℕ ↦ True)
      fun n ↦ (↑(I ^ n • (⊤ : Submodule R N)) : Set N))
    {a : ℕ → ℕ} (ha : StrictMono a)
    (f : (n : ℕ) → M →ₗ[R] N ⧸ (I ^ a n • ⊤ : Submodule R N))
    (hf : ∀ {m : ℕ}, Submodule.factorPow I N (ha.monotone m.le_succ) ∘ₗ f (m + 1) = f m)
    (hopen : ∀ n : ℕ, IsOpen (LinearMap.ker (f n) : Set M)) (m : M) :
    liftContinuousLinearMap I hbasis ha f hf hopen m = lift I ha f hf m := by
  rfl

/-- Composing `liftContinuousLinearMap` with the quotient projection to `N ⧸ (I ^ a n • ⊤)` recovers
`f n`. -/
-- Not `@[grind =]` because `n` only occurs under the function variable `a n`, so `grind`'s
-- E-matching cannot instantiate `n`; `liftContinuousLinearMap_apply` carries `@[grind =]`.
@[simp]
theorem mk_liftContinuousLinearMap
    (hbasis : (𝓝 (0 : N)).HasBasis (fun _ : ℕ ↦ True)
      fun n ↦ (↑(I ^ n • (⊤ : Submodule R N)) : Set N))
    {a : ℕ → ℕ} (ha : StrictMono a)
    (f : (n : ℕ) → M →ₗ[R] N ⧸ (I ^ a n • ⊤ : Submodule R N))
    (hf : ∀ {m : ℕ}, Submodule.factorPow I N (ha.monotone m.le_succ) ∘ₗ f (m + 1) = f m)
    (hopen : ∀ n : ℕ, IsOpen (LinearMap.ker (f n) : Set M)) (n : ℕ) (m : M) :
    Submodule.Quotient.mk (p := (I ^ a n • ⊤ : Submodule R N))
      (liftContinuousLinearMap I hbasis ha f hf hopen m) = f n m := by
  rw [liftContinuousLinearMap_apply, mk_lift]

/-- Uniqueness of `liftContinuousLinearMap`: any continuous `R`-linear map reducing to `f n` modulo
`I ^ a n • ⊤` for all `n` equals `liftContinuousLinearMap`. -/
theorem eq_liftContinuousLinearMap
    (hbasis : (𝓝 (0 : N)).HasBasis (fun _ : ℕ ↦ True)
      fun n ↦ (↑(I ^ n • (⊤ : Submodule R N)) : Set N))
    {a : ℕ → ℕ} (ha : StrictMono a)
    (f : (n : ℕ) → M →ₗ[R] N ⧸ (I ^ a n • ⊤ : Submodule R N))
    (hf : ∀ {m : ℕ}, Submodule.factorPow I N (ha.monotone m.le_succ) ∘ₗ f (m + 1) = f m)
    (hopen : ∀ n : ℕ, IsOpen (LinearMap.ker (f n) : Set M))
    {F : M →L[R] N}
    (hF : ∀ n m, Submodule.Quotient.mk (p := (I ^ a n • ⊤ : Submodule R N)) (F m) = f n m) :
    F = liftContinuousLinearMap I hbasis ha f hf hopen := by
  ext m
  rw [liftContinuousLinearMap_apply]
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

/-- In a ring carrying the `I`-adic topology, the submodules `I ^ n • ⊤` form a neighbourhood basis
of zero. -/
theorem hasBasis_nhds_zero_smul_top (hI : IsAdic I) :
    (𝓝 (0 : R)).HasBasis (fun _ : ℕ ↦ True)
      fun n ↦ (↑(I ^ n • (⊤ : Submodule R R)) : Set R) := by
  simpa only [smul_eq_mul, Ideal.mul_top] using hI.hasBasis_nhds_zero

section TowerLift

variable [TopologicalSpace M] [IsTopologicalAddGroup M]

/-- Specialization of `IsAdicComplete.StrictMono.continuous_lift_of_hasBasis` to an `I`-adically
complete ring carrying the `I`-adic topology. -/
theorem continuous_strictMono_lift (hI : IsAdic I) [IsAdicComplete I R]
    {a : ℕ → ℕ} (ha : StrictMono a)
    (f : (n : ℕ) → M →ₗ[R] R ⧸ (I ^ a n • ⊤ : Submodule R R))
    (hf : ∀ {m : ℕ}, Submodule.factorPow I R (ha.monotone m.le_succ) ∘ₗ f (m + 1) = f m)
    (hopen : ∀ n : ℕ, IsOpen (LinearMap.ker (f n) : Set M)) :
    Continuous (IsAdicComplete.StrictMono.lift I ha f hf) :=
  have := hI.nonarchimedeanRing
  IsAdicComplete.StrictMono.continuous_lift_of_hasBasis I hI.hasBasis_nhds_zero_smul_top
    ha f hf hopen

/-- Assemble a compatible tower of `R`-linear maps `g n : M →ₗ[R] R ⧸ K n` with open kernels into
a single continuous `R`-linear map `M →L[R] R`, where `K n = I ^ a n` for a strictly increasing
sequence `a : ℕ → ℕ` and `R` is `I`-adically complete with the `I`-adic topology. -/
noncomputable def liftIdealTower (hI : IsAdic I) [IsAdicComplete I R]
    {a : ℕ → ℕ} (ha : StrictMono a)
    {K : ℕ → Ideal R} (hK : ∀ n, K n = I ^ a n)
    {hle : ∀ n, K (n + 1) ≤ K n}
    (g : (n : ℕ) → M →ₗ[R] R ⧸ K n)
    (hopen : ∀ n, IsOpen (LinearMap.ker (g n) : Set M))
    (hcomp : ∀ n m, Ideal.Quotient.factor (hle n) (g (n + 1) m) = g n m) :
    M →L[R] R :=
  have := hI.nonarchimedeanRing
  have heq (n : ℕ) : K n = (I ^ a n • (⊤ : Submodule R R) : Ideal R) := by
    rw [hK n, smul_eq_mul, Ideal.mul_top]
  let eqv (n : ℕ) : (R ⧸ K n) ≃ₗ[R] (R ⧸ (I ^ a n • (⊤ : Submodule R R))) :=
    Submodule.quotEquivOfEq _ _ (heq n)
  let f (n : ℕ) : M →ₗ[R] R ⧸ (I ^ a n • (⊤ : Submodule R R)) :=
    (eqv n).toLinearMap.comp (g n)
  have hf : ∀ {n : ℕ},
      Submodule.factorPow I R (ha.monotone n.le_succ) ∘ₗ f (n + 1) = f n := by
    intro n
    ext m
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearEquiv.coe_toLinearMap, LinearEquiv.coe_toLinearMap,
      Submodule.factor_quotEquivOfEq (heq (n + 1)) (heq n) (hle n),
      Submodule.factor_eq_factor, hcomp n m]
  have hopen_f : ∀ n : ℕ, IsOpen (LinearMap.ker (f n) : Set M) := fun n ↦ by
    have hker : LinearMap.ker (f n) = LinearMap.ker (g n) :=
      LinearMap.ker_comp_of_ker_eq_bot (g n) (LinearEquiv.ker (eqv n))
    rw [hker]
    exact hopen n
  IsAdicComplete.StrictMono.liftContinuousLinearMap I hI.hasBasis_nhds_zero_smul_top
    ha f hf hopen_f

/-- Reducing `IsAdic.liftIdealTower` modulo `K n` recovers `g n`. -/
-- Not `@[grind =]` because `n` only occurs under the function variable `K n`, so `grind`'s
-- E-matching cannot instantiate `n`.
@[simp]
theorem mk_liftIdealTower (hI : IsAdic I) [IsAdicComplete I R]
    {a : ℕ → ℕ} (ha : StrictMono a)
    {K : ℕ → Ideal R} (hK : ∀ n, K n = I ^ a n)
    {hle : ∀ n, K (n + 1) ≤ K n}
    (g : (n : ℕ) → M →ₗ[R] R ⧸ K n)
    (hopen : ∀ n, IsOpen (LinearMap.ker (g n) : Set M))
    (hcomp : ∀ n m, Ideal.Quotient.factor (hle n) (g (n + 1) m) = g n m)
    (n : ℕ) (m : M) :
    Ideal.Quotient.mk (K n) (hI.liftIdealTower ha hK g hopen hcomp m) = g n m := by
  have := hI.nonarchimedeanRing
  have heq : K n = (I ^ a n • (⊤ : Submodule R R) : Ideal R) := by
    rw [hK n, smul_eq_mul, Ideal.mul_top]
  apply (Submodule.quotEquivOfEq _ _ heq).injective
  rw [Submodule.quotEquivOfEq_ideal_mk, liftIdealTower, ← Ideal.Quotient.mk_eq_mk,
    IsAdicComplete.StrictMono.mk_liftContinuousLinearMap,
    LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]

/-- Uniqueness of `IsAdic.liftIdealTower`: any continuous `R`-linear map reducing to `g n` modulo
`K n` for all `n` equals `hI.liftIdealTower ha hK g hopen hcomp`. -/
theorem eq_liftIdealTower (hI : IsAdic I) [IsAdicComplete I R]
    {a : ℕ → ℕ} (ha : StrictMono a)
    {K : ℕ → Ideal R} (hK : ∀ n, K n = I ^ a n)
    {hle : ∀ n, K (n + 1) ≤ K n}
    (g : (n : ℕ) → M →ₗ[R] R ⧸ K n)
    (hopen : ∀ n, IsOpen (LinearMap.ker (g n) : Set M))
    (hcomp : ∀ n m, Ideal.Quotient.factor (hle n) (g (n + 1) m) = g n m)
    {F : M →L[R] R}
    (hF : ∀ n m, Ideal.Quotient.mk (K n) (F m) = g n m) :
    F = hI.liftIdealTower ha hK g hopen hcomp := by
  ext m
  exact congr_fun (IsHausdorff.StrictMono.funext' I ha fun n x ↦ by
    rw [← Submodule.quotEquivOfEq_ideal_mk (hK n), ← Submodule.quotEquivOfEq_ideal_mk (hK n),
      hF n x, mk_liftIdealTower]) m

end TowerLift

end IsAdic
