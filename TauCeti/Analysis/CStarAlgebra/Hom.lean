/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import TauCeti.Topology.Algebra.Ring.TwoSidedIdeal
public import TauCeti.Topology.Algebra.Star.Hom
public import TauCeti.Topology.UniformSpace.Equicontinuity

/-!
# Topological properties of C⋆-algebra homomorphisms and equivalences

A `⋆`-algebra homomorphism between complex C⋆-algebras is automatically contractive and hence
continuous, so its two-sided ideal kernel is closed (`NonUnitalStarAlgHom.isClosed_ker`, stated for
any morphism class, so it covers unital `⋆`-homomorphisms and `⋆`-equivalences as well), and any
indexed family of such homomorphisms is uniformly equicontinuous
(`NonUnitalStarAlgHom.uniformEquicontinuous`).

Consequently, if a sequence `φ : ℕ → A →⋆ₙₐ[ℂ] B` satisfies summable consecutive norm estimates
`‖φ (n + 1) a - φ n a‖ ≤ η n` along a monotone sequence of subsets `F n ⊆ A` with dense union, it
converges pointwise everywhere on `A` to a `⋆`-homomorphism `Φ : A →⋆ₙₐ[ℂ] B` satisfying the
tail-error bound `‖Φ a - φ n a‖ ≤ ∑' m, η (n + m)` on `F n`
(`NonUnitalStarAlgHom.exists_tendsto_of_norm_succ_sub_le`).

A `⋆`-algebra equivalence of complex C⋆-algebras is isometric (`StarAlgEquiv.isometry`), so it
bundles as a continuous linear equivalence `StarAlgEquiv.toContinuousLinearEquiv`.
-/

public section

open Filter Set Topology

namespace NonUnitalStarAlgHom

section MorphismClass

variable {ι F A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

open scoped CStarAlgebra in
/-- The two-sided ideal kernel of any `⋆`-homomorphism between C⋆-algebras (unital or not, and
in any morphism class) is closed. -/
instance isClosed_ker (φ : F) : IsClosed (TwoSidedIdeal.ker φ : Set A) :=
  TwoSidedIdeal.isClosed_ker (map_continuous φ)

/-- Any indexed family of `⋆`-homomorphisms between C⋆-algebras is uniformly equicontinuous, since
every member is contractive. -/
theorem uniformEquicontinuous (φ : ι → F) : UniformEquicontinuous fun i a ↦ φ i a := by
  apply Metric.uniformEquicontinuous_of_continuity_modulus id tendsto_id
  intro a b i
  simpa only [id_eq, dist_eq_norm, ← map_sub] using norm_apply_le (φ i) (a - b)

/-- Any indexed family of `⋆`-homomorphisms between C⋆-algebras is equicontinuous. -/
theorem equicontinuous (φ : ι → F) : Equicontinuous fun i a ↦ φ i a :=
  (uniformEquicontinuous φ).equicontinuous

end MorphismClass

section Limit

variable {M A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [FunLike M A B] [NonUnitalAlgHomClass M ℂ A B] [StarHomClass M A B]

/-- If a sequence of `⋆`-homomorphisms `φ : ℕ → M` between C⋆-algebras (in any morphism class)
satisfies `‖φ (n + 1) a - φ n a‖ ≤ η n` on a monotone family of subsets `F : ℕ → Set A` with dense
union and `η` is summable, then `φ n` converges pointwise on all of `A` to a `⋆`-homomorphism `Φ`
with tail estimate `‖Φ a - φ n a‖ ≤ ∑' m, η (n + m)` for `a ∈ F n`. -/
theorem exists_tendsto_of_norm_succ_sub_le (φ : ℕ → M) {F : ℕ → Set A}
    (hF_mono : Monotone F) (hF_dense : Dense (⋃ n, F n)) {η : ℕ → ℝ} (hη : Summable η)
    (hstep : ∀ n, ∀ a ∈ F n, ‖φ (n + 1) a - φ n a‖ ≤ η n) :
    ∃ Φ : A →⋆ₙₐ[ℂ] B,
      (∀ a, Tendsto (fun n ↦ φ n a) atTop (𝓝 (Φ a))) ∧
      (∀ n, ∀ a ∈ F n, ‖Φ a - φ n a‖ ≤ ∑' m, η (n + m)) := by
  have hcauchy : ∀ a ∈ ⋃ n, F n, Cauchy (atTop.map fun n ↦ φ n a) := by
    rintro a ha
    rcases mem_iUnion.mp ha with ⟨N, haN⟩
    have hd (k : ℕ) : dist (φ (N + k) a) (φ (N + (k + 1)) a) ≤ η (N + k) := by
      rw [dist_eq_norm, norm_sub_rev, ← Nat.add_assoc]
      exact hstep (N + k) a (hF_mono (Nat.le_add_right N k) haN)
    have hcs : CauchySeq fun k ↦ φ (N + k) a :=
      cauchySeq_of_dist_le_of_summable (fun k ↦ η (N + k)) hd
        (hη.comp_injective (add_right_injective N))
    obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hcs
    have hb' : Tendsto (fun k ↦ φ (k + N) a) atTop (𝓝 b) := by
      simpa only [Nat.add_comm] using hb
    exact cauchy_map_iff_exists_tendsto.mpr ⟨b, (tendsto_add_atTop_iff_nat N).mp hb'⟩
  obtain ⟨f, _, hf⟩ := (equicontinuous φ).exists_continuous_tendsto_of_dense hF_dense hcauchy
  let Φ : A →⋆ₙₐ[ℂ] B := nonUnitalStarAlgHomOfTendsto f φ (tendsto_pi_nhds.mpr hf)
  have hΦ (a : A) : Tendsto (fun n ↦ φ n a) atTop (𝓝 (Φ a)) := by
    simpa only [Φ, nonUnitalStarAlgHomOfTendsto_apply] using hf a
  refine ⟨Φ, hΦ, fun n a ha ↦ ?_⟩
  have hd (m : ℕ) : dist (φ (n + m) a) (φ (n + (m + 1)) a) ≤ η (n + m) := by
    rw [dist_eq_norm, norm_sub_rev, ← Nat.add_assoc]
    exact hstep (n + m) a (hF_mono (Nat.le_add_right n m) ha)
  have hlim : Tendsto (fun m ↦ φ (n + m) a) atTop (𝓝 (Φ a)) := by
    have hlim' : Tendsto (fun m ↦ φ (m + n) a) atTop (𝓝 (Φ a)) :=
      (tendsto_add_atTop_iff_nat n).mpr (hΦ a)
    simpa only [Nat.add_comm] using hlim'
  have hdist := dist_le_tsum_of_dist_le_of_tendsto₀ (fun m ↦ η (n + m)) hd
    (hη.comp_injective (add_right_injective n)) hlim
  simpa only [Nat.add_zero, dist_eq_norm, norm_sub_rev] using hdist

end Limit

end NonUnitalStarAlgHom

namespace StarAlgEquiv

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- A star-algebra equivalence of C⋆-algebras as a continuous linear equivalence. Both directions
are continuous because star-algebra equivalences of C⋆-algebras are isometric. -/
def toContinuousLinearEquiv (e : A ≃⋆ₐ[ℂ] B) : A ≃L[ℂ] B where
  toFun := e
  invFun := e.symm
  left_inv := e.symm_apply_apply
  right_inv := e.apply_symm_apply
  map_add' := map_add e
  map_smul' := map_smul e
  continuous_toFun := (StarAlgEquiv.isometry e).continuous
  continuous_invFun := (StarAlgEquiv.isometry e.symm).continuous

@[simp]
theorem coe_toContinuousLinearEquiv (e : A ≃⋆ₐ[ℂ] B) : ⇑e.toContinuousLinearEquiv = e :=
  (rfl)

@[simp]
theorem toContinuousLinearEquiv_symm (e : A ≃⋆ₐ[ℂ] B) :
    e.toContinuousLinearEquiv.symm = e.symm.toContinuousLinearEquiv :=
  (rfl)

end StarAlgEquiv
