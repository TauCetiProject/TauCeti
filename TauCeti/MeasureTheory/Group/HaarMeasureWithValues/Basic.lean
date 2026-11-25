/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import TauCeti.Topology.Algebra.Group.CompactOpens
public import TauCeti.Topology.Algebra.Group.Profinite.UnitProOrder
import Mathlib.Algebra.Group.Pointwise.Set.Card
import TauCeti.GroupTheory.Coset.Card
import TauCeti.Topology.Algebra.Group.OpenSubgroup.Basic

/-!
# Haar measures with values in a ring

Let `G` be a topological group and `A` an additive commutative monoid. An `A`-valued (left) Haar
measure on `G` (`TauCeti.HaarMeasureWithValues A G`) assigns a volume `μ K : A` to each compact
open subset `K` of `G`, vanishing on `∅`, additive on disjoint unions and invariant under left
translation. On a locally profinite group these volumes are what integrates locally constant
compactly supported functions and so defines the Hecke algebra over an arbitrary coefficient ring,
including rings such as `ℤ[1/p]` and `𝔽_ℓ` that carry no topology.

When `G` has a compact open subgroup `U₀` whose pro-order is invertible in a semiring `A`
(`TauCeti.HasUnitProOrder A U₀`), a compact open set `K` is a finite disjoint union of left cosets
of a small enough open subgroup `W ≤ U₀`, and `U₀` is a disjoint union of `[U₀ : W]` of them. This
forces `μ K = (#(K / W) : A) * [U₀ : W]⁻¹ * μ U₀`, so a Haar measure is determined by its value on
`U₀`, and conversely the formula with `μ U₀ = 1` defines a Haar measure, the normalised measure
`TauCeti.HaarMeasureWithValues.normalized A U₀ hU₀ h`. Every Haar measure is the normalised one
multiplied by its volume of `U₀`.

## Main definitions

* `TauCeti.HaarMeasureWithValues A G`: finitely additive, left-invariant `A`-valued functions on
  the compact open subsets of `G`.
* `TauCeti.HaarMeasureWithValues.map`: pushing the values forward along an additive map.
* `TauCeti.HaarMeasureWithValues.normalized`: the Haar measure normalised by `μ U₀ = 1` on a
  compact open subgroup `U₀` of invertible pro-order.

## Main results

* `TauCeti.HaarMeasureWithValues.apply_eq_ncard_smul`: if `K` is a union of left cosets of a
  compact open subgroup `W`, then `μ K` is the number of those cosets times `μ W`.
* `TauCeti.HaarMeasureWithValues.apply_toCompactOpens_eq_relIndex_smul`: `μ U = [U : W] • μ W` for
  compact open subgroups `W ≤ U`.
* `TauCeti.HaarMeasureWithValues.apply_toCompactOpens_eq_inverse_mul`: `μ W = [U₀ : W]⁻¹ * μ U₀`
  for an open subgroup `W ≤ U₀` when `U₀` has invertible pro-order.
* `TauCeti.HaarMeasureWithValues.hasUnitProOrder_of_isUnit`: a compact open subgroup whose volume
  is a unit has invertible pro-order. In particular no `𝔽_p`-valued Haar measure gives volume `1`
  to a compact open subgroup having a finite continuous quotient of order divisible by `p`.
* `TauCeti.HaarMeasureWithValues.apply_eq_normalized_mul`,
  `TauCeti.HaarMeasureWithValues.ext_of_apply_toCompactOpens_eq`: uniqueness; a Haar measure is
  determined by its value on `U₀`.
* `TauCeti.HaarMeasureWithValues.normalized_apply_toCompactOpens`: the normalised volume of a
  compact open subgroup `U` is `[U : U ∩ U₀] * [U₀ : U ∩ U₀]⁻¹`, and
  `TauCeti.HaarMeasureWithValues.isUnit_normalized_apply_toCompactOpens_iff` says that it is a unit
  exactly when `U` has invertible pro-order.
* `TauCeti.HaarMeasureWithValues.map_normalized`: the normalised measure is compatible with change
  of coefficients along a ring homomorphism.

## Implementation notes

The volume is a function on `TopologicalSpace.CompactOpens G` rather than Mathlib's
`MeasureTheory.AddContent A C` for the set ring `C` of compact open sets. An `AddContent` is a
function on all of `Set G` whose values off `C` are unconstrained, so two `AddContent`s with the
same volumes on compact open sets can differ; on `CompactOpens G` a Haar measure is determined by
its volumes (`TauCeti.HaarMeasureWithValues.ext`). Additivity is asked of compact open sets that
are disjoint as sets.

## References

* X. He, *Cocenters of p-adic groups I*, Forum Math. Pi 6 (2018), §1.2, pp. 6–7, for Haar
  measures with values in `ℤ[1/p]`.
* C. J. Bushnell and G. Henniart, *The Local Langlands Conjecture for GL(2)*, §3.1, for Haar
  measures on locally profinite groups and the coset decomposition of compact open sets.
-/

public section

open Set TopologicalSpace
open scoped Pointwise

namespace TauCeti

variable (A : Type*) (G : Type*) [Group G] [TopologicalSpace G]

/-- An **`A`-valued (left) Haar measure** on a topological group `G`: a function `μ` from the
compact open subsets of `G` to `A` with `μ ∅ = 0`, `μ (K ∪ L) = μ K + μ L` for disjoint `K` and `L`,
and `μ (g • K) = μ K` for every `g : G`. No normalisation is imposed; for instance the zero function
is a Haar measure. -/
structure HaarMeasureWithValues [AddCommMonoid A] [ContinuousConstSMul G G] where
  /-- The volume of a compact open set. Use the coercion to a function instead. -/
  toFun : CompactOpens G → A
  map_bot' : toFun ⊥ = 0
  map_sup' (K L : CompactOpens G) : Disjoint (K : Set G) L → toFun (K ⊔ L) = toFun K + toFun L
  map_smul' (g : G) (K : CompactOpens G) : toFun (g • K) = toFun K

namespace HaarMeasureWithValues

variable {A G}

section AddCommMonoid

variable [ContinuousConstSMul G G] [AddCommMonoid A]

instance : FunLike (HaarMeasureWithValues A G) (CompactOpens G) A where
  coe := toFun
  coe_injective μ ν h := by cases μ; cases ν; congr

variable (μ : HaarMeasureWithValues A G)

@[simp]
theorem toFun_eq_coe : μ.toFun = μ :=
  (rfl)

@[simp]
theorem coe_mk (f : CompactOpens G → A) (h₁ h₂ h₃) :
    ⇑(⟨f, h₁, h₂, h₃⟩ : HaarMeasureWithValues A G) = f :=
  (rfl)

/-- Haar measures with values in `A` are equal when they give every compact open set the same
volume. -/
@[ext]
theorem ext {μ ν : HaarMeasureWithValues A G} (h : ∀ K, μ K = ν K) : μ = ν :=
  DFunLike.ext _ _ h

@[simp]
theorem apply_bot : μ ⊥ = 0 :=
  μ.map_bot'

theorem apply_sup {K L : CompactOpens G} (h : Disjoint (K : Set G) L) :
    μ (K ⊔ L) = μ K + μ L :=
  μ.map_sup' K L h

@[simp]
theorem apply_smul (g : G) (K : CompactOpens G) : μ (g • K) = μ K :=
  μ.map_smul' g K

/-- Finite additivity: the volume of a finite union of pairwise disjoint compact open sets is the
sum of their volumes. -/
theorem apply_finsetSup {ι : Type*} {s : Finset ι} {f : ι → CompactOpens G}
    (hf : (s : Set ι).PairwiseDisjoint fun i ↦ (f i : Set G)) :
    μ (s.sup f) = ∑ i ∈ s, μ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sup_insert, μ.apply_sup, ih (hf.subset (by simp)), Finset.sum_insert ha]
    rw [CompactOpens.coe_finsetSup]
    refine Set.disjoint_iUnion₂_right.2 fun i hi ↦ ?_
    exact hf (by simp) (by simp [hi]) (ne_of_mem_of_not_mem hi ha).symm

instance : Zero (HaarMeasureWithValues A G) :=
  ⟨{ toFun := 0
     map_bot' := rfl
     map_sup' := fun _ _ _ ↦ by simp
     map_smul' := fun _ _ ↦ rfl }⟩

@[simp]
theorem zero_apply (K : CompactOpens G) : (0 : HaarMeasureWithValues A G) K = 0 :=
  (rfl)

instance : Inhabited (HaarMeasureWithValues A G) :=
  ⟨0⟩

/-- The Haar measure `f ∘ μ` obtained by pushing the volumes of `μ` forward along an additive map
`f : A →+ B`, for instance a change of coefficients. -/
def map {B : Type*} [AddCommMonoid B] (f : A →+ B) : HaarMeasureWithValues B G where
  toFun K := f (μ K)
  map_bot' := by simp
  map_sup' K L h := by simp [μ.apply_sup h]
  map_smul' g K := by simp

@[simp]
theorem map_apply {B : Type*} [AddCommMonoid B] (f : A →+ B) (K : CompactOpens G) :
    μ.map f K = f (μ K) :=
  (rfl)

end AddCommMonoid

/-! ### Compact open sets as unions of cosets -/

section Cosets

variable [IsTopologicalGroup G]

variable [AddCommMonoid A] (μ : HaarMeasureWithValues A G)

/-- **Coset decomposition of volumes.** If a compact open set `K` is a union of left cosets of a
compact open subgroup `W`, then its volume is the number of these cosets times the volume of `W`. -/
theorem apply_eq_ncard_smul (K : CompactOpens G) (W : OpenSubgroup G) (hW : IsCompact (W : Set G))
    (hKW : ∀ k ∈ K, ∀ w ∈ W, k * w ∈ K) :
    μ K = (((↑) : G → G ⧸ (W : Subgroup G)) '' K).ncard • μ (W.toCompactOpens hW) := by
  classical
  have hT := K.isCompact.finite_image_mk W
  have hK : K = hT.toFinset.sup fun q ↦ q.out • W.toCompactOpens hW := by
    refine CompactOpens.ext (Set.ext fun g ↦ ?_)
    simp only [CompactOpens.coe_finsetSup, Set.Finite.mem_toFinset, Set.mem_iUnion, exists_prop,
      SetLike.mem_coe, W.mem_out_smul_toCompactOpens_iff hW, exists_eq_right']
    exact (Subgroup.mk_mem_image_iff_of_forall_mul_mem
      (W := (W : Subgroup G)) (K := (K : Set G)) hKW).symm
  conv_lhs => rw [hK]
  rw [μ.apply_finsetSup (W.pairwiseDisjoint_out_smul_toCompactOpens hW _),
    Finset.sum_congr rfl fun q _ ↦ μ.apply_smul _ _, Finset.sum_const,
    ← Set.ncard_eq_toFinset_card _ hT]

/-- **Index formula.** For compact open subgroups `W ≤ U`, the volume of `U` is `[U : W]` times
the volume of `W`. -/
theorem apply_toCompactOpens_eq_relIndex_smul {U W : OpenSubgroup G} (hU : IsCompact (U : Set G))
    (hW : IsCompact (W : Set G)) (h : W ≤ U) :
    μ (U.toCompactOpens hU) = (W : Subgroup G).relIndex U • μ (W.toCompactOpens hW) := by
  rw [μ.apply_eq_ncard_smul _ W hW (OpenSubgroup.forall_mul_mem_toCompactOpens hU h),
    OpenSubgroup.ncard_image_mk_toCompactOpens hU h]

end Cosets

/-! ### Uniqueness and the unit criterion -/

section Semiring

variable [IsTopologicalGroup G] [Semiring A] (μ : HaarMeasureWithValues A G)

/-- A compact open subgroup whose volume is a unit of `A` has invertible pro-order in `A`. In
particular no Haar measure with values in `𝔽_p` gives volume `1` to a compact open subgroup having a
finite continuous quotient of order divisible by `p`. -/
theorem hasUnitProOrder_of_isUnit (U : OpenSubgroup G) (hU : IsCompact (U : Set G))
    (h : IsUnit (μ (U.toCompactOpens hU))) : HasUnitProOrder A U := by
  have : CompactSpace U := isCompact_iff_compactSpace.mp hU
  have : SeparatelyContinuousMul U :=
    Topology.IsInducing.separatelyContinuousMul (U : Subgroup G).subtype .subtypeVal
  refine hasUnitProOrder_iff_forall_openSubgroup_isUnit_index.2 fun V ↦ ?_
  have hWo : IsOpen (((V : Subgroup U).map (U : Subgroup G).subtype : Subgroup G) : Set G) := by
    rw [Subgroup.coe_map]
    exact U.isOpen.isOpenMap_subtypeVal _ V.isOpen
  let W : OpenSubgroup G := ⟨(V : Subgroup U).map (U : Subgroup G).subtype, hWo⟩
  have hWU : W ≤ U := by
    rintro _ ⟨v, -, rfl⟩
    exact v.property
  have hWc : IsCompact (W : Set G) := hU.of_isClosed_subset W.isClosed hWU
  have hidx : (W : Subgroup G).relIndex U = (V : Subgroup U).index := by
    rw [← Subgroup.relIndex_top_right, ← Subgroup.relIndex_map_map_of_injective _ _
      (U : Subgroup G).subtype_injective, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [μ.apply_toCompactOpens_eq_relIndex_smul hU hWc hWU, nsmul_eq_mul, hidx] at h
  exact ((Nat.cast_commute _ _).isUnit_mul_iff.1 h).1

variable {U₀ : OpenSubgroup G} (hU₀ : IsCompact (U₀ : Set G))

/-- The volume of a compact open subgroup `W ≤ U₀` is `[U₀ : W]⁻¹` times the volume of `U₀`, when
`U₀` has invertible pro-order. -/
theorem apply_toCompactOpens_eq_inverse_mul (h : HasUnitProOrder A U₀)
    {W : OpenSubgroup G} (hW : W ≤ U₀) :
    μ (W.toCompactOpens (hU₀.of_isClosed_subset W.isClosed hW)) =
      Ring.inverse ((W : Subgroup G).relIndex U₀ : A) * μ (U₀.toCompactOpens hU₀) := by
  have hunit : IsUnit ((W : Subgroup G).relIndex U₀ : A) := by
    simpa [Subgroup.inf_relIndex_right, inf_eq_left.2 hW] using
      h.isUnit_relIndex_openSubgroup hU₀ W
  rw [μ.apply_toCompactOpens_eq_relIndex_smul hU₀ _ hW, nsmul_eq_mul,
    Ring.inverse_mul_cancel_left _ _ hunit]

end Semiring

/-! ### The normalised measure -/

section Normalized

variable [IsTopologicalGroup G] [Semiring A] {U₀ : OpenSubgroup G}

/-- The volume of `K` computed at the level of an open subgroup `W ≤ U₀`: the number of left cosets
of `W` that `K` meets, times `[U₀ : W]⁻¹`. -/
private noncomputable def levelVolume (A : Type*) [Semiring A] (U₀ : OpenSubgroup G)
    (K : Set G) (W : Subgroup G) : A :=
  ((((↑) : G → G ⧸ W) '' K).ncard : A) * Ring.inverse (W.relIndex U₀ : A)

/-- The level volume does not depend on the level, among open subgroups `W ≤ U₀` of which `K` is a
union of left cosets. -/
private theorem levelVolume_eq (hU₀ : IsCompact (U₀ : Set G)) (h : HasUnitProOrder A U₀)
    {K : Set G} {W W' : OpenSubgroup G} (hW : W ≤ U₀) (hW' : W' ≤ U₀)
    (hKW : ∀ k ∈ K, ∀ w ∈ W, k * w ∈ K) (hKW' : ∀ k ∈ K, ∀ w ∈ W', k * w ∈ K) :
    levelVolume A U₀ K W = levelVolume A U₀ K W' := by
  -- Both sides agree with the level volume at the common refinement `W ⊓ W'`.
  suffices key : ∀ V V' : OpenSubgroup G, V' ≤ V → V ≤ U₀ → (∀ k ∈ K, ∀ w ∈ V, k * w ∈ K) →
      levelVolume A U₀ K V' = levelVolume A U₀ K V by
    rw [← key W (W ⊓ W') inf_le_left hW hKW, key W' (W ⊓ W') inf_le_right hW' hKW']
  intro V V' hV'V hV hKV
  have hunit : IsUnit ((V' : Subgroup G).relIndex V : A) := by
    have hVc : IsCompact (V : Set G) := hU₀.of_isClosed_subset V.isClosed hV
    simpa [Subgroup.inf_relIndex_right, inf_eq_left.2 hV'V] using
      (h.mono_openSubgroup hU₀ hV).isUnit_relIndex_openSubgroup hVc V'
  simp only [levelVolume]
  -- `#(K / V') * [U₀ : V']⁻¹ = (#(K / V) * [V : V']) * ([U₀ : V] * [V : V'])⁻¹`, and the unit
  -- `[V : V']` cancels.
  rw [Subgroup.ncard_image_mk_of_le hKV (W' := V') hV'V,
    ← Subgroup.relIndex_mul_relIndex (V' : Subgroup G) V U₀ hV'V hV,
    Nat.mul_comm ((V' : Subgroup G).relIndex V), Nat.cast_mul, Nat.cast_mul,
    Ring.mul_inverse_rev' (Nat.cast_commute _ _), mul_assoc, Ring.mul_inverse_cancel_left _ _ hunit]

omit [IsTopologicalGroup G] in
/-- Level volumes are invariant under left translation. -/
private theorem levelVolume_smul (g : G) (K : Set G) (W : Subgroup G) :
    levelVolume A U₀ (g • K) W = levelVolume A U₀ K W := by
  have : ((↑) : G → G ⧸ W) '' (g • K) = g • (((↑) : G → G ⧸ W) '' K) :=
    Set.image_smul_comm _ g K fun x ↦ (MulAction.Quotient.smul_mk W g x).symm
  rw [levelVolume, levelVolume, this, Set.ncard_smul_set]

/-- Level volumes are additive on disjoint unions of left cosets of an open subgroup. -/
private theorem levelVolume_union {K L : Set G} (hK : IsCompact K) (hL : IsCompact L)
    (hKL : Disjoint K L) {W : OpenSubgroup G} (hLW : ∀ k ∈ L, ∀ w ∈ W, k * w ∈ L) :
    levelVolume A U₀ (K ∪ L) W = levelVolume A U₀ K W + levelVolume A U₀ L W := by
  have hdisj : Disjoint (((↑) : G → G ⧸ (W : Subgroup G)) '' K)
      (((↑) : G → G ⧸ (W : Subgroup G)) '' L) :=
    Set.disjoint_left.2 fun _ ⟨k, hk, hkq⟩ hqL ↦ Set.disjoint_left.1 hKL hk
      ((Subgroup.mk_mem_image_iff_of_forall_mul_mem hLW).1 (hkq ▸ hqL))
  rw [levelVolume, Set.image_union,
    ncard_union_eq hdisj (hK.finite_image_mk W) (hL.finite_image_mk W), Nat.cast_add, add_mul,
    ← levelVolume, ← levelVolume]

/-- The normalised volume of a compact open set: its level volume at a chosen open subgroup
`W ≤ U₀` of which it is a union of left cosets. -/
private noncomputable def volume (A : Type*) [Semiring A] (U₀ : OpenSubgroup G)
    (K : CompactOpens G) : A :=
  levelVolume A U₀ K (K.exists_openSubgroup_le_forall_mul_mem U₀).choose

private theorem volume_eq (hU₀ : IsCompact (U₀ : Set G)) (h : HasUnitProOrder A U₀)
    (K : CompactOpens G) {W : OpenSubgroup G} (hW : W ≤ U₀) (hKW : ∀ k ∈ K, ∀ w ∈ W, k * w ∈ K) :
    volume A U₀ K = levelVolume A U₀ K W :=
  have hK := (K.exists_openSubgroup_le_forall_mul_mem U₀).choose_spec
  levelVolume_eq hU₀ h hK.1 hW hK.2 hKW

/-- The **normalised `A`-valued Haar measure** with volume `1` on a compact open subgroup `U₀` of
invertible pro-order in `A`: the volume of a compact open set `K` is `#(K / W) * [U₀ : W]⁻¹` for any
open subgroup `W ≤ U₀` such that `K` is a union of left cosets of `W`
(`TauCeti.HaarMeasureWithValues.normalized_apply`). -/
noncomputable def normalized (A : Type*) [Semiring A] (U₀ : OpenSubgroup G)
    (hU₀ : IsCompact (U₀ : Set G)) (h : HasUnitProOrder A U₀) : HaarMeasureWithValues A G where
  toFun := volume A U₀
  map_bot' := by simp [volume, levelVolume]
  map_sup' K L hKL := by
    -- Compute all three volumes at a common level `W` for `K` and `L`.
    obtain ⟨WK, hWK, hKW⟩ := K.exists_openSubgroup_le_forall_mul_mem U₀
    obtain ⟨WL, -, hLW⟩ := L.exists_openSubgroup_le_forall_mul_mem U₀
    have hKW' : ∀ k ∈ K, ∀ w ∈ WK ⊓ WL, k * w ∈ K := fun k hk w hw ↦ hKW k hk w hw.1
    have hLW' : ∀ k ∈ L, ∀ w ∈ WK ⊓ WL, k * w ∈ L := fun k hk w hw ↦ hLW k hk w hw.2
    have hW : WK ⊓ WL ≤ U₀ := inf_le_left.trans hWK
    rw [volume_eq hU₀ h K hW hKW', volume_eq hU₀ h L hW hLW', volume_eq hU₀ h (K ⊔ L) hW
      fun k hk w hw ↦ hk.elim (fun hk ↦ Or.inl (hKW' k hk w hw)) fun hk ↦ Or.inr (hLW' k hk w hw)]
    exact levelVolume_union K.isCompact L.isCompact hKL hLW'
  map_smul' g K := by
    obtain ⟨W, hW, hKW⟩ := K.exists_openSubgroup_le_forall_mul_mem U₀
    rw [volume_eq hU₀ h K hW hKW, volume_eq hU₀ h (g • K) hW fun k hk w hw ↦ ?_]
    · exact levelVolume_smul g K W
    · rw [CompactOpens.mem_smul_iff_inv_smul_mem, smul_eq_mul] at hk ⊢
      simpa [mul_assoc] using hKW _ hk w hw

variable (hU₀ : IsCompact (U₀ : Set G)) (h : HasUnitProOrder A U₀)

/-- The normalised volume of a compact open set `K`, computed at any level `W ≤ U₀` of which `K` is
a union of left cosets: `#(K / W) * [U₀ : W]⁻¹`. -/
theorem normalized_apply (K : CompactOpens G) {W : OpenSubgroup G} (hW : W ≤ U₀)
    (hKW : ∀ k ∈ K, ∀ w ∈ W, k * w ∈ K) :
    normalized A U₀ hU₀ h K = ((((↑) : G → G ⧸ (W : Subgroup G)) '' K).ncard : A) *
      Ring.inverse ((W : Subgroup G).relIndex U₀ : A) :=
  volume_eq hU₀ h K hW hKW

/-- The normalised measure gives `U₀` volume `1`. -/
@[simp]
theorem normalized_apply_self : normalized A U₀ hU₀ h (U₀.toCompactOpens hU₀) = 1 := by
  rw [normalized_apply hU₀ h _ le_rfl (OpenSubgroup.forall_mul_mem_toCompactOpens hU₀ le_rfl),
    OpenSubgroup.ncard_image_mk_toCompactOpens hU₀ le_rfl, Subgroup.relIndex_self, Nat.cast_one,
    Ring.inverse_one, mul_one]

/-- **Uniqueness of `A`-valued Haar measures.** Every `A`-valued Haar measure is the normalised
measure multiplied on the right by its volume of `U₀`. -/
theorem apply_eq_normalized_mul (μ : HaarMeasureWithValues A G) (K : CompactOpens G) :
    μ K = normalized A U₀ hU₀ h K * μ (U₀.toCompactOpens hU₀) := by
  obtain ⟨W, hW, hKW⟩ := K.exists_openSubgroup_le_forall_mul_mem U₀
  rw [μ.apply_eq_ncard_smul K W (hU₀.of_isClosed_subset W.isClosed hW) hKW,
    μ.apply_toCompactOpens_eq_inverse_mul hU₀ h hW, normalized_apply hU₀ h K hW hKW, nsmul_eq_mul,
    mul_assoc]

include h in
/-- Two `A`-valued Haar measures that agree on a compact open subgroup `U₀` of invertible pro-order
in `A` are equal. -/
theorem ext_of_apply_toCompactOpens_eq {μ ν : HaarMeasureWithValues A G}
    (hμν : μ (U₀.toCompactOpens hU₀) = ν (U₀.toCompactOpens hU₀)) : μ = ν :=
  ext fun K ↦ by rw [μ.apply_eq_normalized_mul hU₀ h, ν.apply_eq_normalized_mul hU₀ h, hμν]

/-- An `A`-valued Haar measure is the normalised one exactly when it gives `U₀` volume `1`. -/
theorem eq_normalized_iff {μ : HaarMeasureWithValues A G} :
    μ = normalized A U₀ hU₀ h ↔ μ (U₀.toCompactOpens hU₀) = 1 :=
  ⟨fun hμ ↦ hμ ▸ normalized_apply_self hU₀ h,
    fun hμ ↦ ext_of_apply_toCompactOpens_eq hU₀ h (by rw [hμ, normalized_apply_self])⟩

/-- The normalised volume of the left coset `g • W` of an open subgroup `W ≤ U₀` is
`[U₀ : W]⁻¹`. -/
theorem normalized_apply_smul_toCompactOpens (g : G) {W : OpenSubgroup G} (hW : W ≤ U₀) :
    normalized A U₀ hU₀ h (g • W.toCompactOpens (hU₀.of_isClosed_subset W.isClosed hW)) =
      Ring.inverse ((W : Subgroup G).relIndex U₀ : A) := by
  rw [apply_smul, (normalized A U₀ hU₀ h).apply_toCompactOpens_eq_inverse_mul hU₀ h hW,
    normalized_apply_self, mul_one]

/-- **Volume of a compact open subgroup.** Under the measure normalised on `U₀`, a compact open
subgroup `U` has volume `[U : U ∩ U₀] * [U₀ : U ∩ U₀]⁻¹`. -/
theorem normalized_apply_toCompactOpens (U : OpenSubgroup G) (hU : IsCompact (U : Set G)) :
    normalized A U₀ hU₀ h (U.toCompactOpens hU) =
      ((U₀ : Subgroup G).relIndex U : A) * Ring.inverse ((U : Subgroup G).relIndex U₀ : A) := by
  rw [normalized_apply hU₀ h _ (W := U ⊓ U₀) inf_le_right
      (OpenSubgroup.forall_mul_mem_toCompactOpens hU inf_le_left),
    OpenSubgroup.ncard_image_mk_toCompactOpens hU inf_le_left]
  simp [Subgroup.inf_relIndex_left, Subgroup.inf_relIndex_right]

/-- **Unit criterion.** Under the measure normalised on `U₀`, a compact open subgroup `U` has unit
volume exactly when it has invertible pro-order in `A`. -/
theorem isUnit_normalized_apply_toCompactOpens_iff (U : OpenSubgroup G)
    (hU : IsCompact (U : Set G)) :
    IsUnit (normalized A U₀ hU₀ h (U.toCompactOpens hU)) ↔ HasUnitProOrder A U := by
  refine ⟨(normalized A U₀ hU₀ h).hasUnitProOrder_of_isUnit U hU, fun hUA ↦ ?_⟩
  have hunit₀ : IsUnit ((U : Subgroup G).relIndex U₀ : A) := h.isUnit_relIndex_openSubgroup hU₀ U
  rw [normalized_apply_toCompactOpens]
  exact (hUA.isUnit_relIndex_openSubgroup hU U₀).mul hunit₀.ringInverse

/-- **Change of coefficients.** The image of the normalised `A`-valued Haar measure under a ring
homomorphism `f : A →+* B` is the normalised `B`-valued Haar measure. -/
theorem map_normalized {B : Type*} [Semiring B] (f : A →+* B) :
    (normalized A U₀ hU₀ h).map (f : A →+ B) = normalized B U₀ hU₀ (h.map f) :=
  (eq_normalized_iff hU₀ (h.map f)).2 (by simp)

end Normalized

end HaarMeasureWithValues

end TauCeti
