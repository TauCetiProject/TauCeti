/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import TauCeti.Analysis.Normed.Ring.PseudoUniformizer
public import TauCeti.Analysis.Normed.Ring.UnitBall

/-!
# The unit ball and the residue module of an ultrametric normed module

Let `R` be an ultrametric seminormed commutative ring with `‖1‖ = 1`, with closed unit ball
`R⁰ = Subring.unitClosedBall R` and open-ball ideal `R⁰⁰ = TauCeti.unitBallIdeal R`, and let `M`
be an ultrametric seminormed `R`-module with contractive scalar action. The vectors of norm at
most one form an `R⁰`-submodule `M⁰ = TauCeti.unitClosedBallSubmodule R M` of `M`, and the
*residue module* of `M` is

`M~ = TauCeti.ResidueModule R M = M⁰ ⧸ R⁰⁰ • M⁰`,

a module over the residue ring `R~ = R⁰ ⧸ R⁰⁰`. Reduction modulo `R⁰⁰ • M⁰` is the
`R⁰`-linear map `TauCeti.ResidueModule.mk`.

Every vector of `R⁰⁰ • M⁰` has norm less than one. The converse holds when the norm of `M` takes
its values in `‖ϖ‖ ^ ℤ ∪ {0}` for a multiplicative pseudo-uniformiser `ϖ` of `R` (this is the
condition `zpowCeil ‖ϖ‖ ‖m‖ = ‖m‖` of `TauCeti.zpowCeil`, which rounding the norm achieves): a
vector of norm less than one then has norm at most `‖ϖ‖`, so it is `ϖ` times a vector of `M⁰`.
Thus for such norms `R⁰⁰ • M⁰ = ϖ M⁰` is the open unit ball of `M`, and two vectors of `M⁰` have
the same residue exactly when they are at distance less than one
(`TauCeti.ResidueModule.mk_eq_mk_iff`). This is the reduction used by Serre to compare
orthonormal bases of `M` with bases of `M~`.

## Main definitions

* `TauCeti.unitClosedBallSubmodule R M`: the closed unit ball `M⁰` as an `R⁰`-submodule of `M`.
* `TauCeti.ResidueModule R M`: the residue module `M⁰ ⧸ R⁰⁰ • M⁰`, a module over
  `R⁰ ⧸ R⁰⁰`.
* `TauCeti.ResidueModule.mk`: the reduction map `M⁰ → M~`.

## Main results

* `TauCeti.norm_lt_one_of_mem_unitBallIdeal_smul_top`: the vectors of `R⁰⁰ • M⁰` have norm
  less than one.
* `TauCeti.mem_unitBallIdeal_smul_top_of_norm_le`: the vectors of `M⁰` of norm at most `‖ϖ‖`
  lie in `R⁰⁰ • M⁰`, for any multiplicative pseudo-uniformiser `ϖ`.
* `TauCeti.mem_unitBallIdeal_smul_top_iff`: for a norm with values in `‖ϖ‖ ^ ℤ ∪ {0}`, these are
  exactly the vectors of `M⁰` of norm less than one.
* `TauCeti.ResidueModule.mk_eq_zero_iff` and `TauCeti.ResidueModule.mk_eq_mk_iff`: the same
  statement for the reduction map.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS 12 (1962), 69–85, §1.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.1.
-/

public section

namespace TauCeti

variable (R M : Type*) [SeminormedCommRing R] [IsUltrametricDist R] [NormOneClass R]
  [SeminormedAddCommGroup M] [IsUltrametricDist M] [Module R M] [IsBoundedSMul R M]

/-- **The closed unit ball of a module.** In an ultrametric seminormed module with contractive
scalar action, the open additive subgroup `IsUltrametricDist.closedBall_openAddSubgroup` of
vectors of norm at most one is a submodule over the closed unit ball `Subring.unitClosedBall R`
of the scalars. -/
def unitClosedBallSubmodule : Submodule (Subring.unitClosedBall R) M :=
  { (IsUltrametricDist.closedBall_openAddSubgroup M one_pos : AddSubgroup M) with
    smul_mem' a m hm := mem_closedBall_zero_iff.mpr <| (norm_smul_le (a : R) m).trans <|
      (mul_le_of_le_one_left (norm_nonneg _) (Subring.mem_unitClosedBall.mp a.2)).trans
        (mem_closedBall_zero_iff.mp hm) }

variable {R M} in
/-- A vector lies in the closed unit ball exactly when its norm is at most one. -/
@[simp]
theorem mem_unitClosedBallSubmodule {m : M} : m ∈ unitClosedBallSubmodule R M ↔ ‖m‖ ≤ 1 :=
  mem_closedBall_zero_iff

/-- The carrier of `unitClosedBallSubmodule R M` is `Metric.closedBall 0 1`. -/
@[simp]
theorem coe_unitClosedBallSubmodule :
    (unitClosedBallSubmodule R M : Set M) = Metric.closedBall 0 1 := by
  ext
  simp

/-- **The residue module** `M⁰ ⧸ R⁰⁰ • M⁰` of an ultrametric seminormed module: the closed unit
ball modulo the multiples of the open-ball ideal `unitBallIdeal R` of the scalars. It is a module
over the residue ring `Subring.unitClosedBall R ⧸ unitBallIdeal R`. -/
abbrev ResidueModule : Type _ :=
  unitClosedBallSubmodule R M ⧸
    (unitBallIdeal R • ⊤ : Submodule (Subring.unitClosedBall R) (unitClosedBallSubmodule R M))

namespace ResidueModule

variable {R M}

/-- The reduction map from the closed unit ball to the residue module. -/
def mk : unitClosedBallSubmodule R M →ₗ[Subring.unitClosedBall R] ResidueModule R M :=
  Submodule.mkQ _

/-- The reduction map is the quotient map. -/
theorem mk_apply (m : unitClosedBallSubmodule R M) : mk m = Submodule.Quotient.mk m :=
  (rfl)

/-- Every element of the residue module is the residue of a vector of the closed unit ball. -/
theorem mk_surjective : Function.Surjective (mk : unitClosedBallSubmodule R M → _) :=
  Submodule.mkQ_surjective _

/-- The residue ring acts on residues through representatives:
the residue of `a` times the residue of `m` is the residue of `a • m`. -/
@[simp]
theorem smul_mk (a : Subring.unitClosedBall R) (m : unitClosedBallSubmodule R M) :
    Ideal.Quotient.mk (unitBallIdeal R) a • mk m = mk (a • m) := by
  rw [mk_apply, mk_apply, Module.Quotient.mk_smul_mk]

end ResidueModule

variable {R M}

/-- The multiples `R⁰⁰ • M⁰` of the open-ball ideal have norm less than one. -/
theorem norm_lt_one_of_mem_unitBallIdeal_smul_top {m : unitClosedBallSubmodule R M}
    (hm : m ∈ (unitBallIdeal R • ⊤ :
      Submodule (Subring.unitClosedBall R) (unitClosedBallSubmodule R M))) :
    ‖(m : M)‖ < 1 := by
  refine Submodule.smul_induction_on hm (fun a ha n _ ↦ ?_) fun m n hm hn ↦ ?_
  · exact (norm_smul_le (a : R) (n : M)).trans_lt <|
      (mul_le_of_le_one_right (norm_nonneg _) (mem_unitClosedBallSubmodule.mp n.2)).trans_lt
        (mem_unitBallIdeal.mp ha)
  · exact (IsUltrametricDist.norm_add_le_max (m : M) n).trans_lt (max_lt hm hn)

/-- A vector of the closed unit ball of norm at most `‖ϖ‖`, for a multiplicative
pseudo-uniformiser `ϖ`, is `ϖ` times a vector of the closed unit ball, so it lies in `R⁰⁰ • M⁰`. -/
theorem mem_unitBallIdeal_smul_top_of_norm_le (ϖ : NormedRing.PseudoUniformizer R)
    {m : unitClosedBallSubmodule R M} (hm : ‖(m : M)‖ ≤ ‖(ϖ.unit : R)‖) :
    m ∈ (unitBallIdeal R • ⊤ :
      Submodule (Subring.unitClosedBall R) (unitClosedBallSubmodule R M)) := by
  -- So `m = ϖ • (ϖ⁻¹ • m)` with `‖ϖ⁻¹ • m‖ ≤ 1`.
  let ϖ₀ : Subring.unitClosedBall R := ⟨ϖ.unit, Subring.mem_unitClosedBall.mpr ϖ.norm_lt_one.le⟩
  let n : unitClosedBallSubmodule R M :=
    ⟨((ϖ.unit⁻¹ : Rˣ) : R) • (m : M), by
      rw [mem_unitClosedBallSubmodule, ϖ.norm_inv_smul]
      exact inv_mul_le_one_of_le₀ hm ϖ.norm_pos.le⟩
  have hmn : m = ϖ₀ • n := by
    ext
    simp [ϖ₀, n, Subring.smul_def, smul_smul]
  rw [hmn]
  exact Submodule.smul_mem_smul (mem_unitBallIdeal.mpr ϖ.norm_lt_one) Submodule.mem_top

/-- **The residue module of a discretely normed module.** If the norm of `M` takes its values in
`‖ϖ‖ ^ ℤ ∪ {0}` for a multiplicative pseudo-uniformiser `ϖ`, then `R⁰⁰ • M⁰` consists exactly of
the vectors of `M⁰` of norm less than one. -/
theorem mem_unitBallIdeal_smul_top_iff (ϖ : NormedRing.PseudoUniformizer R)
    (hM : ∀ m : M, zpowCeil ‖(ϖ.unit : R)‖ ‖m‖ = ‖m‖) {m : unitClosedBallSubmodule R M} :
    m ∈ (unitBallIdeal R • ⊤ :
      Submodule (Subring.unitClosedBall R) (unitClosedBallSubmodule R M)) ↔ ‖(m : M)‖ < 1 :=
  ⟨norm_lt_one_of_mem_unitBallIdeal_smul_top, fun hm ↦ mem_unitBallIdeal_smul_top_of_norm_le ϖ
    (le_of_zpowCeil_eq_self_of_lt_one ϖ.norm_pos ϖ.norm_lt_one (hM _) hm)⟩

namespace ResidueModule

/-- The residue of a vector vanishes exactly when the vector has norm less than one, for a norm
with values in `‖ϖ‖ ^ ℤ ∪ {0}`. -/
theorem mk_eq_zero_iff (ϖ : NormedRing.PseudoUniformizer R)
    (hM : ∀ m : M, zpowCeil ‖(ϖ.unit : R)‖ ‖m‖ = ‖m‖) {m : unitClosedBallSubmodule R M} :
    mk m = 0 ↔ ‖(m : M)‖ < 1 := by
  rw [mk_apply, Submodule.Quotient.mk_eq_zero, mem_unitBallIdeal_smul_top_iff ϖ hM]

/-- Two vectors of the closed unit ball have the same residue exactly when they are at distance
less than one, for a norm with values in `‖ϖ‖ ^ ℤ ∪ {0}`. -/
theorem mk_eq_mk_iff (ϖ : NormedRing.PseudoUniformizer R)
    (hM : ∀ m : M, zpowCeil ‖(ϖ.unit : R)‖ ‖m‖ = ‖m‖) {m n : unitClosedBallSubmodule R M} :
    mk m = mk n ↔ ‖(m : M) - n‖ < 1 := by
  rw [← sub_eq_zero, ← map_sub, mk_eq_zero_iff ϖ hM, Submodule.coe_sub]

end ResidueModule

end TauCeti
