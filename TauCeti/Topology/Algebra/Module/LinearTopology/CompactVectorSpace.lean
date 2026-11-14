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
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Logic.Small.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import TauCeti.Topology.Algebra.Module.Quotient

/-!
# Compact linearly topologized vector spaces over discrete fields

Let `V` be a topological vector space over a field `K` whose topology is `K`-linear
(`IsLinearTopology K V`). Every open subspace `U` of `V` has discrete quotient `V ⧸ U`, so
extending linear functionals across `V ⧸ U` shows that continuous linear forms `V →L[K] K`
separate points whenever `V` is `T₁` (for any topology on `K`).

When `K` has the discrete topology and `V` is compact and Hausdorff (`CompactSpace V` and
`T2Space V`), Lefschetz linear duality identifies `V` with a product of copies of `K`:

1. If `V` is nontrivial, any nonzero continuous linear functional on `V` is surjective onto `K`, so
   compactness of `V` forces the discrete field `K` to be finite.
2. Any `K`-linearly independent family `f : ι → (V →ₗ[K] K)` evaluates surjectively onto finite
   coordinate tuples `s → K`, so `(fun v i ↦ f i v) : V → (ι → K)` has dense range.
3. For any `K`-basis `b : Module.Basis ι K (V →L[K] K)` of the continuous dual, the joint
   evaluation map `V →L[K] (ι → K)` is injective (by point separation), has dense compact range
   (hence is surjective), and is therefore a topological linear isomorphism
   `b.continuousDualEquivPi : V ≃L[K] (ι → K)`.
4. Because `V →L[K] K` embeds into `V → K` and `K` is `Small.{v}` whenever `V : Type v` is
   nontrivial (or else `V →L[K] K` is subsingleton), the continuous dual has a basis indexed in
   `Type v`, giving `∃ I : Type v, Nonempty (V ≃L[K] (I → K))` with no universe restriction on `K`.

## Main definitions and results

* `LinearIndependent.surjective_pi_eval`, `LinearIndependent.denseRange_pi_eval`: evaluation of a
  linearly independent family of linear forms is surjective on finite index types and has dense
  range in `ι → K`.
* `TauCeti.exists_continuousLinearMap_apply_ne_zero`,
  `TauCeti.exists_continuousLinearMap_apply_eq_one`: continuous linear forms separate points on a
  `T₁` linearly topologized vector space over a division ring or field.
* `TauCeti.small_continuousLinearMap_self`: `Small.{v} (V →L[K] K)` for `V : Type v`.
* `TauCeti.finite_of_compactSpace_of_isLinearTopology`: if `V` is compact, `T₁`, linearly
  topologized, and nontrivial over discrete `K`, then `Finite K`.
* `Module.Basis.continuousDualEquivPi`: a `K`-basis `b` of `V →L[K] K` induces a continuous linear
  equivalence `V ≃L[K] (ι → K)` sending `v` to `fun i ↦ b i v`.
* `TauCeti.exists_continuousLinearEquiv_pi_of_isLinearTopology`,
  `TauCeti.IsCompactModule.exists_continuousLinearEquiv_pi_of_field`,
  `TauCeti.IsCompactModule.iff_exists_continuousLinearEquiv_pi_of_field`: every compact Hausdorff
  linearly topologized vector space over a discrete field is topologically isomorphic to `I → K`.

## References

* [S. Lefschetz, *Algebraic Topology*], Ch. II, §6, (25.4)–(27.1), for linear compactness and the
  product decomposition of linearly compact vector spaces via their continuous dual.
* [N. Bourbaki, *Algebra II*], Ch. IV, §2, Exercises, for linearly topologized vector spaces.
-/

public section

open Filter Topology

namespace LinearIndependent

section Field

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] {f : ι → (V →ₗ[K] K)}

/-- Evaluation against a finite `K`-linearly independent family of linear forms `V →ₗ[K] K` is
surjective onto `ι → K`. -/
theorem surjective_pi_eval [Finite ι] (hf : LinearIndependent K f) :
    Function.Surjective (fun v : V ↦ fun i : ι ↦ f i v) := by
  classical
  have := Fintype.ofFinite ι
  let E : V →ₗ[K] (ι → K) := LinearMap.pi f
  intro y
  by_contra hy_ex
  have hy : y ∉ LinearMap.range E := fun ⟨v, hv⟩ ↦ hy_ex ⟨v, hv⟩
  let q := (LinearMap.range E).mkQ
  have hqy : q y ≠ 0 := fun h ↦ hy ((Submodule.Quotient.mk_eq_zero _).mp h)
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_ne_zero K hqy
  let ψ : (ι → K) →ₗ[K] K := ℓ.comp q
  let c : ι → K := fun i ↦ ψ (Pi.single i 1)
  have hpi : ∀ z : ι → K, ∑ i : ι, z i • Pi.single i (1 : K) = z := fun z ↦ by
    ext j
    simp [Pi.single_apply]
  have hrel : ∑ i : ι, c i • f i = 0 := by
    ext v
    have hEv : ψ (E v) = 0 := by
      have hv_mem : E v ∈ LinearMap.range E := ⟨v, rfl⟩
      simp [ψ, q, (Submodule.Quotient.mk_eq_zero _).mpr hv_mem]
    calc
      (∑ i : ι, c i • f i) v = ∑ i : ι, f i v * ψ (Pi.single i 1) := by
        simp [LinearMap.sum_apply, c, mul_comm]
      _ = ψ (∑ i : ι, E v i • Pi.single i 1) := by simp [E, map_sum, map_smul]
      _ = ψ (E v) := by rw [hpi (E v)]
      _ = 0 := hEv
  have hc : ∀ i : ι, c i = 0 := Fintype.linearIndependent_iff.mp hf c hrel
  have hψy : ψ y = 0 := by
    rw [← hpi y, map_sum]
    simp [map_smul, c, hc]
  exact hℓ hψy

/-- Evaluation against any `K`-linearly independent family of linear forms `V →ₗ[K] K` has dense
range in `ι → K` for any topology on `K`. -/
theorem denseRange_pi_eval [TopologicalSpace K] (hf : LinearIndependent K f) :
    DenseRange (fun v : V ↦ fun i : ι ↦ f i v) := by
  intro y
  rw [mem_closure_iff_nhds]
  intro W hW
  rw [nhds_pi, Filter.mem_pi'] at hW
  obtain ⟨s, t, ht, hst⟩ := hW
  have hfs : LinearIndependent K (fun i : s ↦ f i.1) := hf.comp Subtype.val Subtype.val_injective
  obtain ⟨v, hv⟩ := hfs.surjective_pi_eval (fun i : s ↦ y i.1)
  refine ⟨fun i ↦ f i v, hst fun i hi ↦ ?_, v, rfl⟩
  have hvi : f i v = y i := congr_fun hv ⟨i, hi⟩
  exact hvi ▸ mem_of_mem_nhds (ht i)

end Field

end LinearIndependent

namespace TauCeti

section DivisionRing

universe u v

variable {K : Type u} {V : Type v} [DivisionRing K] [TopologicalSpace K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [IsLinearTopology K V] [T1Space V]

/-- **Continuous linear forms separate points on a `T₁` linearly topologized vector space over a
division ring** (with any topology on `K`). -/
theorem exists_continuousLinearMap_apply_ne_zero {v : V} (hv : v ≠ 0) :
    ∃ φ : V →L[K] K, φ v ≠ 0 := by
  -- Separate `v` from `0` by an open subspace `U`, so `v` has nonzero image in the discrete
  -- quotient vector space `V ⧸ U`.
  have h0 : ({v}ᶜ : Set V) ∈ 𝓝 (0 : V) := isClosed_singleton.compl_mem_nhds hv.symm
  obtain ⟨U, hU, hUv⟩ := (IsLinearTopology.hasBasis_open_submodule K).mem_iff.mp h0
  have hvU : v ∉ U := fun h ↦ hUv h (Set.mem_singleton v)
  have := Submodule.Quotient.discreteTopology_of_isOpen U hU
  let b := Module.Free.chooseBasis K (V ⧸ U)
  have hqv : U.mkQ v ≠ 0 := fun h ↦ hvU ((Submodule.Quotient.mk_eq_zero U).mp h)
  obtain ⟨i, hi⟩ : ∃ i, b.coord i (U.mkQ v) ≠ 0 := by
    by_contra! hall
    exact hqv (b.repr.map_eq_zero_iff.mp (Finsupp.ext hall))
  have hcont : Continuous ((b.coord i).comp U.mkQ) :=
    (continuous_of_discreteTopology (f := b.coord i)).comp continuous_quotient_mk'
  exact ⟨⟨(b.coord i).comp U.mkQ, hcont⟩, hi⟩

/-- The continuous dual `V →L[K] K` of a `T₁` linearly topologized vector space `V : Type v` over a
division ring `K` is `Small.{v}`, regardless of the universe or topology of `K`. -/
theorem small_continuousLinearMap_self : Small.{v} (V →L[K] K) := by
  rcases subsingleton_or_nontrivial V with hsub | hnt
  · infer_instance
  · obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨φ, hφ⟩ := exists_continuousLinearMap_apply_ne_zero (K := K) hv
    have hsurj : Function.Surjective φ := fun k ↦
      ⟨(k * (φ v)⁻¹) • v, by simp [inv_mul_cancel_right₀ hφ]⟩
    have : Small.{v} K := small_of_surjective hsurj
    exact small_of_injective (DFunLike.coe_injective (F := V →L[K] K))

/-- If a nontrivial compact `T₁` vector space over a discrete division ring `K` carries a
`K`-linear topology, then `K` must be finite. -/
theorem finite_of_compactSpace_of_isLinearTopology [DiscreteTopology K] [CompactSpace V]
    [Nontrivial V] : Finite K := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨φ, hφ⟩ := exists_continuousLinearMap_apply_ne_zero (K := K) hv
  have hsurj : Function.Surjective φ := fun k ↦
    ⟨(k * (φ v)⁻¹) • v, by simp [inv_mul_cancel_right₀ hφ]⟩
  have := hsurj.compactSpace φ.continuous
  exact finite_of_compact_of_discrete

end DivisionRing

section Field

variable {K V : Type*} [Field K] [TopologicalSpace K] [ContinuousConstSMul K K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [IsLinearTopology K V] [T1Space V]

/-- Normalized point separation: for any nonzero `v` in a `T₁` linearly topologized vector space
over a field `K` with continuous scalar multiplication on itself, some continuous linear functional
evaluates to `1` at `v`. -/
theorem exists_continuousLinearMap_apply_eq_one {v : V} (hv : v ≠ 0) :
    ∃ φ : V →L[K] K, φ v = 1 := by
  obtain ⟨φ, hφ⟩ := exists_continuousLinearMap_apply_ne_zero (K := K) hv
  exact ⟨(φ v)⁻¹ • φ, inv_mul_cancel₀ hφ⟩

end Field

end TauCeti

namespace Module.Basis

variable {K V ι : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [IsLinearTopology K V] [CompactSpace V] [T2Space V] [T2Space K]

private noncomputable def dualPiCLM (b : Module.Basis ι K (V →L[K] K)) : V →L[K] (ι → K) :=
  ⟨LinearMap.pi fun i ↦ (b i).toLinearMap, continuous_pi fun i ↦ (b i).continuous⟩

omit [CompactSpace V] [T2Space K] in
private theorem injective_dualPiCLM (b : Module.Basis ι K (V →L[K] K)) :
    Function.Injective (dualPiCLM b).toLinearMap := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro v hv
  by_contra hv0
  obtain ⟨φ, hφ⟩ := TauCeti.exists_continuousLinearMap_apply_ne_zero (K := K) hv0
  have hbv : ∀ i : ι, b i v = 0 := fun i ↦ congr_fun hv i
  have hφ0 : φ v = 0 := by
    conv_lhs => rw [← b.linearCombination_repr φ]
    simp [Finsupp.linearCombination_apply, Finsupp.sum, hbv]
  exact hφ hφ0

omit [IsTopologicalAddGroup V] [IsLinearTopology K V] [T2Space V] in
private theorem surjective_dualPiCLM (b : Module.Basis ι K (V →L[K] K)) :
    Function.Surjective (dualPiCLM b).toLinearMap := by
  rw [ContinuousLinearMap.coe_coe, ← Set.range_eq_univ]
  have hclosed : IsClosed (Set.range (dualPiCLM b)) :=
    (isCompact_range (dualPiCLM b).continuous).isClosed
  rw [← hclosed.closure_eq]
  have hli : LinearIndependent K (fun i : ι ↦ (b i : V →ₗ[K] K)) :=
    b.linearIndependent.map' (ContinuousLinearMap.coeLM K)
      (LinearMap.ker_eq_bot_of_injective ContinuousLinearMap.coe_injective)
  exact hli.denseRange_pi_eval.closure_eq

/-- **Lefschetz product decomposition from a continuous dual basis**: a `K`-basis
`b : Module.Basis ι K (V →L[K] K)` of the continuous dual of a compact Hausdorff linearly
topologized `K`-vector space `V` over a `T₂` topological field `K` induces a topological `K`-linear
isomorphism `V ≃L[K] (ι → K)` sending `v` to `fun i ↦ b i v`. -/
noncomputable def continuousDualEquivPi (b : Module.Basis ι K (V →L[K] K)) :
    V ≃L[K] (ι → K) :=
  let e := LinearEquiv.ofBijective (dualPiCLM b).toLinearMap
    ⟨injective_dualPiCLM b, surjective_dualPiCLM b⟩
  { toLinearEquiv := e
    continuous_toFun := (dualPiCLM b).continuous
    continuous_invFun :=
      (dualPiCLM b).continuous.continuous_symm_of_equiv_compact_to_t2
        (f := e.toEquiv) }

@[simp]
theorem continuousDualEquivPi_apply (b : Module.Basis ι K (V →L[K] K)) (v : V) (i : ι) :
    b.continuousDualEquivPi v i = b i v :=
  (rfl)

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
  have : Small.{v} (V →L[K] K) := small_continuousLinearMap_self
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

/-- Over a compact totally disconnected topological field `K` (such as any finite discrete field),
a topological `K`-vector space `V : Type v` is a compact module if and only if it is topologically
isomorphic to a product `I → K` for some `I : Type v`. -/
theorem iff_exists_continuousLinearEquiv_pi_of_field [IsTopologicalRing K] [CompactSpace K]
    [TotallyDisconnectedSpace K] :
    IsCompactModule K V ↔ ∃ I : Type v, Nonempty (V ≃L[K] (I → K)) := by
  refine ⟨fun hV ↦ hV.exists_continuousLinearEquiv_pi_of_field, fun ⟨I, ⟨e⟩⟩ ↦ ?_⟩
  exact (IsCompactModule.pi fun _ : I ↦ IsCompactModule.self (R := K)).of_continuousLinearEquiv
    e.symm

end IsCompactModule

end ExistsPi

end TauCeti
