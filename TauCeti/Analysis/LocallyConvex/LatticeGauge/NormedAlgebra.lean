/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LocallyConvex.LatticeGauge.Basic

/-!
# Normed algebras and modules from scalar lattice gauges

`latticeGaugeNormedRing` and `latticeGaugeNormedCommRing` give a multiplicatively closed lattice
in a Hausdorff uniform algebra its scalar gauge as a ring norm with the original uniformity.
They use `latticeGaugeNormedAddCommGroup` and `latticeGauge_mul_le`.
`latticeGaugeNormedAlgebra` gives the normed algebra structure over the base field, using
`latticeGauge_smul`. If the algebra is nonzero and its lattice contains one,
`normOneClass_latticeGaugeNormedRing` supplies the normalization needed for Tate scalars.
For a module lattice stable under the algebra lattice, `isBoundedSMul_latticeGauge` packages
`latticeGauge_smul_le` as the contractive action needed by the ring-scalar operator norm.
-/

public section

open Filter Set Topology Bornology Pointwise

namespace TauCeti

variable {K A M : Type*} [NontriviallyNormedField K]
  [Ring A] [Algebra K A] [UniformSpace A] [IsUniformAddGroup A] [ContinuousSMul K A] [T2Space A]
  {A₀ : Set A}
  (hAb : Balanced K A₀) (hAa : A₀ + A₀ ⊆ A₀) (hAn : A₀ ∈ 𝓝 0) (hAu : IsVonNBounded K A₀)
  (hAm : A₀ * A₀ ⊆ A₀)

/-- A balanced bounded neighbourhood of zero closed under addition and multiplication gives a
normed ring via its scalar lattice gauge, with the original uniformity. -/
noncomputable abbrev latticeGaugeNormedRing : NormedRing A :=
  letI groupNorm := latticeGaugeNormedAddCommGroup K hAb hAa hAn hAu
  { ‹Ring A›, groupNorm.toNorm, groupNorm.toMetricSpace with
    dist_eq := dist_eq_norm_neg_add
    norm_mul_le := latticeGauge_mul_le (absorbent_nhds_zero hAn) hAm }

/-- The norm projection of `latticeGaugeNormedRing` is the scalar lattice gauge. This equation
lets callers compute the ring norm without unfolding its construction from the additive norm. -/
@[simp] theorem latticeGaugeNormedRing_norm (a : A) :
    @Norm.norm A (latticeGaugeNormedRing hAb hAa hAn hAu hAm).toNorm a =
      latticeGauge K A₀ a :=
  latticeGaugeNormedAddCommGroup_norm hAb hAa hAn hAu a

/-- The lattice gauge ring norm induces the original uniformity. -/
@[simp] theorem latticeGaugeNormedRing_toUniformSpace :
    (latticeGaugeNormedRing hAb hAa hAn hAu hAm).toMetricSpace.toUniformSpace =
      ‹UniformSpace A› :=
  (rfl)

/-- The coefficient ring with the lattice gauge is a normed algebra over the scalar field. -/
noncomputable abbrev latticeGaugeNormedAlgebra :
    @NormedAlgebra K A _ (latticeGaugeNormedRing hAb hAa hAn hAu hAm).toSeminormedRing :=
  letI := latticeGaugeNormedRing hAb hAa hAn hAu hAm
  { ‹Algebra K A› with
    norm_smul_le c a := by
      simpa only [latticeGaugeNormedRing_norm hAb hAa hAn hAu hAm]
        using (latticeGauge_smul A₀ c a).le }

/-- The scalar lattice gauge has norm one at one if the lattice contains one and the algebra
is nonzero. -/
theorem normOneClass_latticeGaugeNormedRing [Nontrivial A] (hA1 : 1 ∈ A₀) :
    @NormOneClass A (latticeGaugeNormedRing hAb hAa hAn hAu hAm).toNorm _ :=
  letI := latticeGaugeNormedRing hAb hAa hAn hAu hAm
  { norm_one := by
      rw [latticeGaugeNormedRing_norm]
      exact latticeGauge_one hAb hAm hA1 hAn hAu }

variable [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
  [UniformSpace M] [IsUniformAddGroup M] [ContinuousSMul K M] [T2Space M] {M₀ : Set M}
  (hMb : Balanced K M₀) (hMa : M₀ + M₀ ⊆ M₀) (hMn : M₀ ∈ 𝓝 0) (hMu : IsVonNBounded K M₀)

/-- If the algebra lattice preserves the module lattice, their scalar lattice gauges make the
module action contractive. -/
theorem isBoundedSMul_latticeGauge (h : A₀ • M₀ ⊆ M₀) :
    @IsBoundedSMul A M
      (latticeGaugeNormedAddCommGroup K hAb hAa hAn hAu).toPseudoMetricSpace
      (latticeGaugeNormedAddCommGroup K hMb hMa hMn hMu).toPseudoMetricSpace _ _ _ :=
  letI := latticeGaugeNormedAddCommGroup K hAb hAa hAn hAu
  letI := latticeGaugeNormedAddCommGroup K hMb hMa hMn hMu
  have hle (a : A) (m : M) : ‖a • m‖ ≤ ‖a‖ * ‖m‖ := by
    simpa only [latticeGaugeNormedAddCommGroup_norm hAb hAa hAn hAu,
      latticeGaugeNormedAddCommGroup_norm hMb hMa hMn hMu]
      using latticeGauge_smul_le (K := K) (absorbent_nhds_zero hAn) (absorbent_nhds_zero hMn) h a m
  { dist_smul_pair' := fun a m n ↦ by
      simpa only [dist_eq_norm, sub_zero, smul_sub] using hle a (m - n)
    dist_pair_smul' := fun a b m ↦ by
      simpa only [dist_eq_norm, sub_zero, sub_smul] using hle (a - b) m }

section CommRing

variable {B : Type*} [CommRing B] [Algebra K B] [UniformSpace B] [IsUniformAddGroup B]
  [ContinuousSMul K B] [T2Space B] {B₀ : Set B}

/-- The scalar lattice gauge as a norm on a commutative coefficient algebra. Its underlying
`NormedRing` is `latticeGaugeNormedRing`. -/
noncomputable abbrev latticeGaugeNormedCommRing (hb : Balanced K B₀) (ha : B₀ + B₀ ⊆ B₀)
    (hn : B₀ ∈ 𝓝 0) (hu : IsVonNBounded K B₀) (hm : B₀ * B₀ ⊆ B₀) : NormedCommRing B :=
  { latticeGaugeNormedRing hb ha hn hu hm, ‹CommRing B› with }

end CommRing

end TauCeti
