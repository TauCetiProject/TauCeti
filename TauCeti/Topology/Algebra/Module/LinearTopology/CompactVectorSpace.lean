/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Logic.Small.Defs
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import TauCeti.Topology.Algebra.Module.Compact
import Mathlib.Algebra.Module.LinearMap.DivisionRing
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Logic.Small.Basic
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Homeomorph.Lemmas
import TauCeti.LinearAlgebra.Dual.Lemmas
import TauCeti.Topology.Algebra.Module.Quotient

/-!
# Lefschetz linear duality for compact linearly topologized vector spaces

This file establishes Lefschetz linear duality for compact Hausdorff linearly topologized vector
spaces: every such vector space `V` over a `T₂` topological field `K` is topologically isomorphic to
a product `I → K` via evaluation against a basis of its continuous dual `V →L[K] K`. In
nonarchimedean algebra, reducing a compact module `M` over a compact Hausdorff noetherian local ring
`R` modulo its maximal ideal `𝔪` produces a compact vector space `M ⧸ 𝔪M` over the finite discrete
residue field `R ⧸ 𝔪`; decomposing `M ⧸ 𝔪M ≃L[R ⧸ 𝔪] (I → R ⧸ 𝔪)` supplies the mod-`𝔪` coordinate
functionals that lift to pseudobases of profinite flat modules.

Let `V` be a topological vector space over a division ring or field `K` whose topology is `K`-linear
(`IsLinearTopology K V`):

1. Over any division ring `K` (for any topology on `K`), open subspaces have discrete quotients, so
   extending linear forms across `V ⧸ U` shows that continuous linear forms `V →L[K] K` separate
   points whenever `V` is `T₁` (`TauCeti.exists_continuousLinearMap_apply_eq_one`,
   `TauCeti.exists_continuousLinearMap_apply_ne_zero`). As a standalone consequence for discrete
   division rings `K`, compactness of a nontrivial `T₁` linearly topologized `K`-vector space forces
   `K` to be finite (`TauCeti.finite_of_compactSpace_of_isLinearTopology`).
2. Over any field `K` (with any topology on `K`), any `K`-linearly independent family
   `f : ι → (V →ₗ[K] K)` evaluates surjectively onto finite coordinate tuples and therefore has
   dense range in `ι → K` (`LinearIndependent.denseRange_pi`).
3. Over any `T₂` topological field `K` (`[IsTopologicalRing K] [T2Space K]`), when `V` is compact
   and Hausdorff, joint evaluation against any `K`-basis `b : Module.Basis ι K (V →L[K] K)` of the
   continuous dual is injective (by point separation) and has dense compact range (hence is
   surjective), yielding `b.continuousDualEquivPi : V ≃L[K] (ι → K)`. Shrinking a dual basis into
   `Type v` gives `TauCeti.exists_continuousLinearEquiv_pi_of_isLinearTopology`.
4. Over a compact Hausdorff topological field `K` (`[IsTopologicalRing K] [CompactSpace K]
   [T2Space K]`, such as any finite discrete field), `TauCeti.IsCompactModule K V` is equivalent to
   `∃ I : Type v, Nonempty (V ≃L[K] (I → K))`
   (`TauCeti.IsCompactModule.iff_exists_continuousLinearEquiv_pi_of_field`).

## Main definitions and results

* `LinearIndependent.denseRange_pi`: evaluation against a linearly independent family of linear
  forms has dense range in `ι → K` for any topology on `K`.
* `TauCeti.exists_continuousLinearMap_apply_eq_one`,
  `TauCeti.exists_continuousLinearMap_apply_ne_zero`: continuous linear forms separate points on a
  `T₁` linearly topologized vector space over a division ring (with any topology on `K`).
* `TauCeti.small_strongDual`: `Small.{v} (StrongDual K V)` for `V : Type v`.
* `TauCeti.finite_of_compactSpace_of_isLinearTopology`: for a discrete division ring `K`, if `V` is
  compact, `T₁`, linearly topologized, and nontrivial, then `Finite K`.
* `Module.Basis.continuousDualEquivPi`, `Module.Basis.apply_continuousDualEquivPi_symm`: over a `T₂`
  topological field `K`, a `K`-basis `b` of `V →L[K] K` induces `V ≃L[K] (ι → K)` sending `v` to
  `fun i ↦ b i v`.
* `TauCeti.exists_continuousLinearEquiv_pi_of_isLinearTopology`: over a `T₂` topological field `K`,
  every compact Hausdorff linearly topologized vector space `V : Type v` is topologically isomorphic
  to `I → K` for some `I : Type v`.
* `TauCeti.IsCompactModule.exists_continuousLinearEquiv_pi_of_field`,
  `TauCeti.IsCompactModule.iff_exists_continuousLinearEquiv_pi_of_field`: over a compact Hausdorff
  topological field `K` (`[IsTopologicalRing K] [CompactSpace K] [T2Space K]`), a topological
  `K`-vector space `V : Type v` is a compact module if and only if it is topologically isomorphic to
  `I → K` for some `I : Type v`.

## References

* [S. Lefschetz, *Algebraic Topology*], Ch. II, §6, (25.4)–(27.1), for linear compactness and the
  product decomposition of linearly compact vector spaces via their continuous dual.
* [N. Bourbaki, *Algebra I*], Ch. II, §7, Exercises, and [N. Bourbaki, *Commutative Algebra*],
  Ch. III, §2, Exercises, for linearly topologized vector spaces.
-/

public section

open Filter Topology

namespace LinearIndependent

section Field

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] {f : ι → (V →ₗ[K] K)}

/-- Evaluation against any `K`-linearly independent family of linear forms `V →ₗ[K] K` has dense
range in `ι → K` for any topology on `K`. -/
theorem denseRange_pi [TopologicalSpace K] (hf : LinearIndependent K f) :
    DenseRange (LinearMap.pi f) := by
  intro y
  rw [mem_closure_iff_nhds]
  intro W hW
  rw [nhds_pi, Filter.mem_pi'] at hW
  obtain ⟨s, t, ht, hst⟩ := hW
  have hfs : LinearIndependent K (fun i : s ↦ f i.val) := hf.comp Subtype.val Subtype.val_injective
  obtain ⟨v, hv⟩ := hfs.pi_surjective (fun i : s ↦ y i.val)
  refine ⟨LinearMap.pi f v, hst fun i hi ↦ ?_, v, rfl⟩
  have hvi : f i v = y i := by simpa [LinearMap.pi_apply] using congr_fun hv ⟨i, hi⟩
  rw [LinearMap.pi_apply, hvi]
  exact mem_of_mem_nhds (ht i)

end Field

end LinearIndependent

namespace TauCeti

section DivisionRing

universe u v

variable (K : Type u) {V : Type v} [DivisionRing K] [TopologicalSpace K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [IsLinearTopology K V] [T1Space V]

/-- **Normalized point separation on a `T₁` linearly topologized vector space over a division
ring** (with any topology on `K`): for any nonzero `v : V`, some continuous linear functional
evaluates to `1` at `v`. -/
theorem exists_continuousLinearMap_apply_eq_one {v : V} (hv : v ≠ 0) :
    ∃ φ : V →L[K] K, φ v = 1 := by
  -- Separate `v` from `0` by an open subspace `U`, so `v` has nonzero image in the discrete
  -- quotient vector space `V ⧸ U`.
  have h0 : ({v}ᶜ : Set V) ∈ 𝓝 (0 : V) := isClosed_singleton.compl_mem_nhds hv.symm
  obtain ⟨U, hU, hUv⟩ := (IsLinearTopology.hasBasis_open_submodule K).mem_iff.mp h0
  have hvU : v ∉ U := fun h ↦ hUv h (Set.mem_singleton v)
  have := Submodule.Quotient.discreteTopology_of_isOpen U hU
  have hqv : U.mkQ v ≠ 0 := fun h ↦ hvU ((Submodule.Quotient.mk_eq_zero U).mp h)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero K hqv
  let g : (V ⧸ U) →ₗ[K] K := (LinearMap.mulRight K (f (U.mkQ v))⁻¹).comp f
  have hcont : Continuous (g.comp U.mkQ) :=
    (continuous_of_discreteTopology (f := g)).comp continuous_quotient_mk'
  exact ⟨⟨g.comp U.mkQ, hcont⟩, by
    simp only [ContinuousLinearMap.coe_mk', LinearMap.comp_apply, g, LinearMap.mulRight_apply]
    exact mul_inv_cancel₀ hf⟩

/-- **Continuous linear forms separate points on a `T₁` linearly topologized vector space over a
division ring** (with any topology on `K`). -/
theorem exists_continuousLinearMap_apply_ne_zero {v : V} (hv : v ≠ 0) :
    ∃ φ : V →L[K] K, φ v ≠ 0 := by
  obtain ⟨φ, hφ⟩ := exists_continuousLinearMap_apply_eq_one K hv
  exact ⟨φ, hφ.symm ▸ one_ne_zero⟩

variable (V)

/-- The continuous dual `StrongDual K V` of a `T₁` linearly topologized vector space `V : Type v`
over a division ring `K` is `Small.{v}`, regardless of the universe or topology of `K`. -/
theorem small_strongDual : Small.{v} (StrongDual K V) := by
  rcases subsingleton_or_nontrivial V with hsub | hnt
  · infer_instance
  · obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨φ, hφ⟩ := exists_continuousLinearMap_apply_ne_zero K hv
    have hsurj : Function.Surjective φ :=
      φ.toLinearMap.surjective fun h ↦ hφ (DFunLike.congr_fun h v)
    have : Small.{v} K := small_of_surjective hsurj
    exact small_of_injective (DFunLike.coe_injective (F := StrongDual K V))

/-- If a nontrivial compact `T₁` vector space over a discrete division ring `K` carries a
`K`-linear topology, then `K` must be finite. -/
theorem finite_of_compactSpace_of_isLinearTopology [DiscreteTopology K] [CompactSpace V]
    [Nontrivial V] : Finite K := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨φ, hφ⟩ := exists_continuousLinearMap_apply_ne_zero K hv
  have hsurj : Function.Surjective φ :=
    φ.toLinearMap.surjective fun h ↦ hφ (DFunLike.congr_fun h v)
  have := hsurj.compactSpace φ.continuous
  exact finite_of_compact_of_discrete

end DivisionRing

end TauCeti

namespace Module.Basis

variable {K V ι : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [IsLinearTopology K V] [CompactSpace V] [T2Space V] [T2Space K]

omit [CompactSpace V] [T2Space K] in
private theorem pi_injective (b : Module.Basis ι K (V →L[K] K)) :
    Function.Injective (ContinuousLinearMap.pi b).toLinearMap := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro v hv
  by_contra hv0
  obtain ⟨φ, hφ⟩ := TauCeti.exists_continuousLinearMap_apply_ne_zero K hv0
  have hbv : ∀ i : ι, b i v = 0 := fun i ↦ by
    have hv' : (ContinuousLinearMap.pi b).toLinearMap v = 0 := LinearMap.mem_ker.mp hv
    rw [ContinuousLinearMap.coe_coe] at hv'
    simpa [ContinuousLinearMap.pi_apply] using congr_fun hv' i
  have hφ0 : φ v = 0 := by
    conv_lhs => rw [← b.linearCombination_repr φ]
    simp [Finsupp.linearCombination_apply, Finsupp.sum, hbv]
  exact hφ hφ0

omit [IsTopologicalAddGroup V] [IsLinearTopology K V] [T2Space V] in
private theorem pi_surjective (b : Module.Basis ι K (V →L[K] K)) :
    Function.Surjective (ContinuousLinearMap.pi b).toLinearMap := by
  rw [ContinuousLinearMap.coe_pi, ← Set.range_eq_univ]
  have hclosed : IsClosed (Set.range (LinearMap.pi fun i ↦ (b i).toLinearMap)) := by
    rw [← ContinuousLinearMap.coe_pi, ContinuousLinearMap.coe_coe]
    exact (isCompact_range (ContinuousLinearMap.pi b).continuous).isClosed
  rw [← hclosed.closure_eq]
  have hli : LinearIndependent K (fun i : ι ↦ (b i : V →ₗ[K] K)) :=
    b.linearIndependent.map' (ContinuousLinearMap.coeLM K)
      (LinearMap.ker_eq_bot_of_injective ContinuousLinearMap.coe_injective)
  exact hli.denseRange_pi.closure_eq

/-- **Lefschetz product decomposition from a continuous dual basis**: a `K`-basis
`b : Module.Basis ι K (V →L[K] K)` of the continuous dual of a compact Hausdorff linearly
topologized `K`-vector space `V` over a `T₂` topological field `K` induces a topological `K`-linear
isomorphism `V ≃L[K] (ι → K)` sending `v` to `fun i ↦ b i v`. -/
noncomputable def continuousDualEquivPi (b : Module.Basis ι K (V →L[K] K)) :
    V ≃L[K] (ι → K) :=
  let e := LinearEquiv.ofBijective (ContinuousLinearMap.pi b).toLinearMap
    ⟨pi_injective b, pi_surjective b⟩
  { toLinearEquiv := e
    continuous_toFun := (ContinuousLinearMap.pi b).continuous
    continuous_invFun :=
      (ContinuousLinearMap.pi b).continuous.continuous_symm_of_equiv_compact_to_t2
        (f := e.toEquiv) }

@[simp, grind =]
theorem continuousDualEquivPi_apply (b : Module.Basis ι K (V →L[K] K)) (v : V) (i : ι) :
    b.continuousDualEquivPi v i = b i v :=
  (rfl)

@[simp, grind =]
theorem apply_continuousDualEquivPi_symm (b : Module.Basis ι K (V →L[K] K)) (c : ι → K)
    (i : ι) : b i (b.continuousDualEquivPi.symm c) = c i := by
  rw [← continuousDualEquivPi_apply, ContinuousLinearEquiv.apply_symm_apply]

end Module.Basis

namespace TauCeti

section ExistsPi

universe u v

variable (K : Type u) (V : Type v) [Field K] [TopologicalSpace K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V]

/-- **Every compact Hausdorff linearly topologized vector space `V : Type v` over a `T₂`
topological field `K` is topologically isomorphic to a product `I → K` for some `I : Type v`.** -/
theorem exists_continuousLinearEquiv_pi_of_isLinearTopology
    [IsTopologicalRing K] [T2Space K] [IsTopologicalAddGroup V] [IsLinearTopology K V]
    [CompactSpace V] [T2Space V] :
    ∃ I : Type v, Nonempty (V ≃L[K] (I → K)) := by
  have : Small.{v} (V →L[K] K) := small_strongDual K V
  let b₀ := Module.Free.chooseBasis K (V →L[K] K)
  have : Small.{v} (Module.Free.ChooseBasisIndex K (V →L[K] K)) :=
    small_of_injective b₀.injective
  let b := b₀.reindex (equivShrink (Module.Free.ChooseBasisIndex K (V →L[K] K)))
  exact ⟨Shrink.{v} (Module.Free.ChooseBasisIndex K (V →L[K] K)), ⟨b.continuousDualEquivPi⟩⟩

namespace IsCompactModule

variable {K V}

/-- Every compact module `V : Type v` over a compact Hausdorff topological field `K` (in
particular, any finite discrete field) is topologically isomorphic to `I → K` for some
`I : Type v`. -/
theorem exists_continuousLinearEquiv_pi_of_field [IsTopologicalRing K] [CompactSpace K]
    [T2Space K] (hV : IsCompactModule K V) :
    ∃ I : Type v, Nonempty (V ≃L[K] (I → K)) := by
  have := hV.isTopologicalAddGroup
  have := hV.isLinearTopology
  have := hV.compactSpace
  have := hV.t2Space
  exact exists_continuousLinearEquiv_pi_of_isLinearTopology K V

/-- Over a compact Hausdorff topological field `K` (such as any finite discrete field), a
topological `K`-vector space `V : Type v` is a compact module if and only if it is topologically
isomorphic to a product `I → K` for some `I : Type v`. -/
theorem iff_exists_continuousLinearEquiv_pi_of_field [IsTopologicalRing K] [CompactSpace K]
    [T2Space K] :
    IsCompactModule K V ↔ ∃ I : Type v, Nonempty (V ≃L[K] (I → K)) := by
  refine ⟨fun hV ↦ hV.exists_continuousLinearEquiv_pi_of_field, fun ⟨I, ⟨e⟩⟩ ↦ ?_⟩
  have : DiscreteTopology K :=
    discreteTopology_iff_isOpen_singleton_zero.mpr GroupWithZero.isOpen_singleton_zero
  exact (IsCompactModule.pi fun _ : I ↦ IsCompactModule.self (R := K)).of_continuousLinearEquiv
    e.symm

end IsCompactModule

end ExistsPi

end TauCeti
