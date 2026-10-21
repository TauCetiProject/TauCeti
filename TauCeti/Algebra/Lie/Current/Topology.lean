/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.FilterBasis
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import TauCeti.Algebra.Lie.Current.Basic

/-!
# The order topology on formal currents

Formal currents `R⸨X⸩ ⊗[R] L` carry the linear topology in which the order submodules
`orderSubmodule R L N`, the currents of order at least `N`, form a basis of neighbourhoods of
zero. The coefficient ring `R` and the coefficient module `L` carry no topology: this is the
`X`-adic topology for discrete coefficients. The order submodules are defined without a choice of
basis, so neither is the topology.

This topology makes the formal currents a nonarchimedean topological additive group whose
topology is `R`-linear, and multiplication by a fixed Laurent series is continuous. For a Lie
algebra `L` the bracket is jointly continuous, because brackets of currents of orders at least
`M` and `N` have order at least `M + N` and every current has a finite lower order. Truncations
of a current converge to it, so polynomial currents are dense.

When `L` is a free `R`-module, the topology is Hausdorff. When `L` is moreover finite, it is
complete: a Cauchy sequence has eventually constant coefficients below every order and a common
lower order, and every such coefficient family is the coefficient family of a formal current. The
finiteness assumption cannot be dropped: for infinitely many basis vectors `bᵢ`, the partial sums
of `∑ᵢ Xⁱ ⊗ bᵢ` form a Cauchy sequence without a limit in the tensor product.

## Main results

* `TauCeti.CurrentAlgebra.hasBasis_nhds_zero`: the order submodules form a basis of
  neighbourhoods of zero.
* `TauCeti.CurrentAlgebra.tendsto_nhds_iff`: convergence of currents in terms of orders.
* `TauCeti.CurrentAlgebra.continuous_lie`: the bracket of formal currents is continuous.
* `TauCeti.CurrentAlgebra.instT2Space`, `TauCeti.CurrentAlgebra.instCompleteSpace`: the topology is
  Hausdorff, and complete over a finite free coefficient module.
* `TauCeti.CurrentAlgebra.denseRange_ofLoop`: polynomial currents are dense.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.3, for the topology of the formal
  loop algebra `g((t))`.
-/

public section

noncomputable section

open Filter Topology Uniformity
open scoped TensorProduct LaurentSeries

namespace TauCeti.CurrentAlgebra

variable (R L : Type*) [CommRing R]

-- The coefficientwise algebra structure matches the module used by the tensor product.
attribute [local instance 1100] HahnSeries.instAlgebra

section Module

variable [AddCommGroup L] [Module R L]

/-- The order submodules, as a filter basis of the additive group of formal currents. -/
@[instance_reducible]
def orderFilterBasis : AddGroupFilterBasis (currentAlgebra R L) :=
  addGroupFilterBasisOfComm (Set.range fun N : ℤ ↦ (orderSubmodule R L N : Set _))
    (Set.range_nonempty _)
    (by
      rintro _ _ ⟨M, rfl⟩ ⟨N, rfl⟩
      exact ⟨_, ⟨max M N, rfl⟩, Set.subset_inter
        (orderSubmodule_antitone R L (le_max_left M N))
        (orderSubmodule_antitone R L (le_max_right M N))⟩)
    (by
      rintro _ ⟨N, rfl⟩
      exact zero_mem _)
    (by
      rintro _ ⟨N, rfl⟩
      exact ⟨_, ⟨N, rfl⟩, Set.add_subset_iff.mpr fun _ hu _ hv ↦ add_mem hu hv⟩)
    (by
      rintro _ ⟨N, rfl⟩
      exact ⟨_, ⟨N, rfl⟩, fun _ hu ↦ neg_mem hu⟩)

/-- Formal currents carry the linear topology in which the order submodules form a basis of
neighbourhoods of zero. -/
instance : TopologicalSpace (currentAlgebra R L) :=
  (orderFilterBasis R L).topology

instance : IsTopologicalAddGroup (currentAlgebra R L) :=
  (orderFilterBasis R L).isTopologicalAddGroup

/-- The order submodules form a basis of neighbourhoods of zero. -/
theorem hasBasis_nhds_zero :
    (𝓝 (0 : currentAlgebra R L)).HasBasis (fun _ : ℤ ↦ True)
      (fun N ↦ (orderSubmodule R L N : Set (currentAlgebra R L))) := by
  refine ((orderFilterBasis R L).nhds_zero_hasBasis).to_hasBasis ?_ ?_
  · rintro _ ⟨N, rfl⟩
    exact ⟨N, trivial, subset_rfl⟩
  · exact fun N _ ↦ ⟨_, ⟨N, rfl⟩, subset_rfl⟩

/-- The translates of the order submodules form a basis of neighbourhoods of a current. -/
theorem hasBasis_nhds (u : currentAlgebra R L) :
    (𝓝 u).HasBasis (fun _ : ℤ ↦ True) (fun N ↦ {v | v - u ∈ orderSubmodule R L N}) := by
  rw [← nhds_translation_sub u]
  exact (hasBasis_nhds_zero R L).comap _

variable {R L} in
/-- A family of currents converges to `u` exactly when, for every order `N`, its differences with
`u` eventually have order at least `N`. -/
theorem tendsto_nhds_iff {ι : Type*} {l : Filter ι} {f : ι → currentAlgebra R L}
    {u : currentAlgebra R L} :
    Tendsto f l (𝓝 u) ↔ ∀ N : ℤ, ∀ᶠ i in l, f i - u ∈ orderSubmodule R L N := by
  simp [(hasBasis_nhds R L u).tendsto_right_iff]

/-- Every order submodule is a neighbourhood of zero. -/
theorem orderSubmodule_mem_nhds_zero (N : ℤ) :
    (orderSubmodule R L N : Set (currentAlgebra R L)) ∈ 𝓝 0 :=
  (hasBasis_nhds_zero R L).mem_of_mem trivial

/-- Every order submodule is open. -/
theorem isOpen_orderSubmodule (N : ℤ) :
    IsOpen (orderSubmodule R L N : Set (currentAlgebra R L)) :=
  (orderSubmodule R L N).toAddSubgroup.isOpen_of_mem_nhds (orderSubmodule_mem_nhds_zero R L N)

/-- Every order submodule is closed. -/
theorem isClosed_orderSubmodule (N : ℤ) :
    IsClosed (orderSubmodule R L N : Set (currentAlgebra R L)) :=
  (orderSubmodule R L N).toAddSubgroup.isClosed_of_isOpen (isOpen_orderSubmodule R L N)

/-- The order topology on formal currents is linear over the coefficient ring. -/
instance : IsLinearTopology R (currentAlgebra R L) :=
  IsLinearTopology.mk_of_hasBasis R (hasBasis_nhds_zero R L)

/-- Formal currents form a nonarchimedean additive group: the order submodules are open
subgroups. -/
instance : NonarchimedeanAddGroup (currentAlgebra R L) where
  is_nonarchimedean U hU := by
    obtain ⟨N, -, hN⟩ := (hasBasis_nhds_zero R L).mem_iff.mp hU
    exact ⟨⟨(orderSubmodule R L N).toAddSubgroup, isOpen_orderSubmodule R L N⟩, hN⟩

/-- Multiplication by a fixed Laurent series is continuous on formal currents. -/
instance : ContinuousConstSMul R⸨X⸩ (currentAlgebra R L) where
  continuous_const_smul f := by
    refine continuous_of_continuousAt_zero (DistribSMul.toAddMonoidHom (currentAlgebra R L) f) ?_
    obtain ⟨M, hM⟩ : ∃ M : ℤ, (M : WithTop ℤ) ≤ f.orderTop := by
      rcases eq_or_ne f 0 with rfl | hf
      · exact ⟨0, by simp⟩
      · exact ⟨f.order, (HahnSeries.order_eq_orderTop_of_ne_zero hf).le⟩
    rw [ContinuousAt, map_zero, (hasBasis_nhds_zero R L).tendsto_iff (hasBasis_nhds_zero R L)]
    refine fun N _ ↦ ⟨N - M, trivial, fun u hu ↦ ?_⟩
    simpa using smul_mem_orderSubmodule R L hM hu

/-- Multiplication by a fixed coefficient is continuous on formal currents. -/
instance : ContinuousConstSMul R (currentAlgebra R L) :=
  IsScalarTower.continuousConstSMul R R⸨X⸩ _

/-- The order topology is Hausdorff over a free coefficient module. -/
instance instT2Space [Module.Free R L] : T2Space (currentAlgebra R L) := by
  refine IsTopologicalAddGroup.t2Space_of_zero_sep fun u hu ↦ ?_
  have hu' : u ∉ ⨅ N, orderSubmodule R L N := by simpa using hu
  obtain ⟨N, hN⟩ : ∃ N, u ∉ orderSubmodule R L N := by
    simpa only [Submodule.mem_iInf, not_forall] using hu'
  exact ⟨_, orderSubmodule_mem_nhds_zero R L N, hN⟩

/-- Formal currents carry the uniform structure of their topological additive group. -/
instance : UniformSpace (currentAlgebra R L) :=
  IsTopologicalAddGroup.rightUniformSpace _

instance : IsUniformAddGroup (currentAlgebra R L) :=
  isUniformAddGroup_of_addCommGroup

/-- In a Cauchy sequence of currents, all coefficients below `N` are eventually constant. -/
private theorem exists_coeff_eq_of_cauchySeq {u : ℕ → currentAlgebra R L} (hu : CauchySeq u)
    (N : ℤ) : ∃ k, ∀ m ≥ k, ∀ n < N, coeff R L n (u m) = coeff R L n (u k) := by
  have hbasis := (uniformity_eq_comap_nhds_zero (currentAlgebra R L)) ▸
    (hasBasis_nhds_zero R L).comap fun p : currentAlgebra R L × currentAlgebra R L ↦ p.2 - p.1
  obtain ⟨k, hk⟩ := hbasis.cauchySeq_iff.mp hu N trivial
  refine ⟨k, fun m hm n hn ↦ ?_⟩
  rw [← sub_eq_zero, ← map_sub]
  exact coeff_eq_zero_of_mem_orderSubmodule R L (hk k le_rfl m hm) hn

/-- The order topology is complete over a finite free coefficient module. -/
instance instCompleteSpace [Module.Free R L] [Module.Finite R L] :
    CompleteSpace (currentAlgebra R L) := by
  have : (𝓤 (currentAlgebra R L)).IsCountablyGenerated :=
    have : (𝓝 (0 : currentAlgebra R L)).IsCountablyGenerated :=
      (hasBasis_nhds_zero R L).isCountablyGenerated
    IsUniformAddGroup.uniformity_countably_generated
  refine UniformSpace.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  choose k hk using exists_coeff_eq_of_cauchySeq R L hu
  -- The limit has, at each `n`, the coefficient on which the sequence stabilises below `n + 1`.
  have hlim (N : ℤ) (m : ℕ) (hm : k N ≤ m) (n : ℤ) (hn : n < N) :
      coeff R L n (u m) = coeff R L n (u (k (n + 1))) := by
    rw [hk N m hm n hn, ← hk N (max (k N) (k (n + 1))) (le_max_left _ _) n hn,
      hk (n + 1) _ (le_max_right _ _) n (Int.lt_add_one_iff.mpr le_rfl)]
  obtain ⟨a, ha⟩ := exists_mem_orderSubmodule R L (u (k 0))
  obtain ⟨v, hv⟩ := exists_forall_coeff_eq R L (fun n ↦ coeff R L n (u (k (n + 1))))
    (a := min a 0) fun n hn ↦ by
      rw [← hlim 0 (max (k 0) (k (n + 1))) (le_max_left _ _) n (by omega),
        hk 0 _ (le_max_left _ _) n (by omega)]
      exact coeff_eq_zero_of_mem_orderSubmodule R L ha (by omega)
  refine ⟨v, tendsto_nhds_iff.mpr fun N ↦ eventually_atTop.mpr ⟨k N, fun m hm ↦ ?_⟩⟩
  rw [mem_orderSubmodule_iff]
  intro n hn
  rw [map_sub, hv, hlim N m hm n hn, sub_self]

end Module

section Lie

variable [LieRing L] [LieAlgebra R L]

/-- The bracket of formal currents is jointly continuous. -/
theorem continuous_lie :
    Continuous fun p : currentAlgebra R L × currentAlgebra R L ↦ ⁅p.1, p.2⁆ := by
  let B : currentAlgebra R L →+ currentAlgebra R L →+ currentAlgebra R L :=
    AddMonoidHom.mk' (fun u ↦ AddMonoidHom.mk' (fun v ↦ ⁅u, v⁆) (lie_add u)) fun u u' ↦ by
      ext v
      simp [add_lie]
  have h0 := hasBasis_nhds_zero R L
  refine continuous_of_continuousAt_zero₂ B ?_ (fun u ↦ ?_) (fun v ↦ ?_)
  · rw [ContinuousAt, nhds_prod_eq, map_zero, (h0.prod h0).tendsto_iff h0]
    refine fun N _ ↦ ⟨(max N 0, max N 0), ⟨trivial, trivial⟩, fun p hp ↦ ?_⟩
    simpa [B] using orderSubmodule_antitone R L (by omega : N ≤ max N 0 + max N 0)
      (lie_mem_orderSubmodule R L hp.1 hp.2)
  · obtain ⟨M, hM⟩ := exists_mem_orderSubmodule R L u
    rw [ContinuousAt, map_zero, h0.tendsto_iff h0]
    refine fun N _ ↦ ⟨N - M, trivial, fun v hv ↦ ?_⟩
    simpa [B] using lie_mem_orderSubmodule R L hM hv
  · obtain ⟨M, hM⟩ := exists_mem_orderSubmodule R L v
    rw [ContinuousAt, map_zero, AddMonoidHom.zero_apply, h0.tendsto_iff h0]
    refine fun N _ ↦ ⟨N - M, trivial, fun u hu ↦ ?_⟩
    simpa [B] using lie_mem_orderSubmodule R L hu hM

/-- The truncations of a formal current converge to it as the cutoff grows. -/
theorem tendsto_ofLoop_trunc (u : currentAlgebra R L) :
    Tendsto (fun N ↦ ofLoop R L (trunc R L N u)) atTop (𝓝 u) :=
  tendsto_nhds_iff.mpr fun N ↦ eventually_atTop.mpr
    ⟨N, fun M hM ↦ orderSubmodule_antitone R L hM (ofLoop_trunc_sub_mem_orderSubmodule R L M u)⟩

/-- Polynomial currents are dense in formal currents. -/
theorem denseRange_ofLoop : DenseRange (ofLoop R L) := fun u ↦
  mem_closure_of_tendsto (tendsto_ofLoop_trunc R L u) (Eventually.of_forall fun _ ↦ ⟨_, rfl⟩)

end Lie

end TauCeti.CurrentAlgebra
