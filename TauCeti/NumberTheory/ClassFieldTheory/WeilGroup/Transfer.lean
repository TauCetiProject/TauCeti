/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.WeilGroup.Topology
public import TauCeti.NumberTheory.LocalField.Unramified.Inertia.Extension
import TauCeti.Topology.Algebra.Group.Subgroup

/-!
# Functoriality of the local Weil group under finite extensions

Let `L/K` be a finite extension of nonarchimedean local fields, embedded in a separable closure of
`K` by `ι`, with residue degree `f = f(L/K)`. The embedding identifies `G_L` with the open subgroup
of `G_K` fixing `ι(L)` (`TauCeti.absoluteGaloisGroupExtend`). An element of `G_L` acting on
`L^{ur}` as the `n`-th power of the arithmetic Frobenius of `L` acts on `K^{ur}` as the `f n`-th
power of that of `K`, and conversely an element of `G_L` acting on `K^{ur}` as an integral power of
Frobenius has that power divisible by `f`. So the local Weil group of `L` is exactly the part of the
local Weil group of `K` lying in `G_L`, and the embedding restricts to the **Weil transfer**

`TauCeti.ClassFieldTheory.weilTransfer K L ι : W_L →* W_K`,

a continuous injection with open image of index `[L : K]`, along which the degree is multiplied by
the residue degree: `deg_K (weilTransfer w) = f · deg_L w`. The degrees agree only when `L/K` is
totally ramified.

When `L/K` is normal, restriction of automorphisms along `ι` gives the **Weil restriction**

`TauCeti.ClassFieldTheory.weilRestrict K L ι : W_K →* Gal(L/K)`,

which is surjective because `W_K` is dense in `G_K`, and whose kernel is the image of the Weil
transfer: `1 → W_L → W_K → Gal(L/K) → 1` is exact.

## Main definitions

* `TauCeti.ClassFieldTheory.weilTransfer K L ι`: the Weil transfer `W_L →* W_K`.
* `TauCeti.ClassFieldTheory.weilRestrict K L ι`: for `L/K` normal, the restriction
  `W_K →* Gal(L/K)`.

## Main results

* `TauCeti.ClassFieldTheory.absoluteGaloisGroupExtend_mem_localWeilGroup_iff`: `W_L` is the
  preimage of `W_K` in `G_L`.
* `TauCeti.ClassFieldTheory.weilDegree_weilTransfer`: `deg_K ∘ weilTransfer = f · deg_L`.
* `TauCeti.ClassFieldTheory.injective_weilTransfer`,
  `TauCeti.ClassFieldTheory.continuous_weilTransfer`: the Weil transfer is a continuous injection.
* `TauCeti.ClassFieldTheory.range_weilTransfer`,
  `TauCeti.ClassFieldTheory.isOpen_range_weilTransfer`,
  `TauCeti.ClassFieldTheory.index_range_weilTransfer`: its image is the part of `W_K` lying in
  `G_L`, an open subgroup of index `[L : K]`.
* `TauCeti.ClassFieldTheory.surjective_weilRestrict`,
  `TauCeti.ClassFieldTheory.range_weilTransfer_eq_ker_weilRestrict`: for `L/K` normal, the
  restriction `W_K → Gal(L/K)` is surjective with kernel the image of the Weil transfer.

## References

* J. Tate, *Number theoretic background*, in *Automorphic forms, representations and
  L-functions*, Proc. Sympos. Pure Math. 33, Part 2 (1979), §1.4.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

universe u v

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (L : Type v) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] (ι : L →ₐ[K] SeparableClosure K)

variable {K L} in
/-- **The Weil group of `L` inside that of `K`.** An element of `G_L` lies in the local Weil group
of `L` exactly when its image in `G_K` lies in the local Weil group of `K`. -/
@[simp]
theorem absoluteGaloisGroupExtend_mem_localWeilGroup_iff {τ : Field.absoluteGaloisGroup L} :
    absoluteGaloisGroupExtend K L ι τ ∈ localWeilGroup K ↔ τ ∈ localWeilGroup L := by
  rw [mem_localWeilGroup_iff, mem_localWeilGroup_iff]
  refine ⟨fun ⟨m, hm⟩ ↦ ?_, fun ⟨n, hn⟩ ↦ ⟨_,
    (restrictMaximalUnramifiedHom_absoluteGaloisGroupExtend_eq_zpow_iff ι τ n).2 hn⟩⟩
  obtain ⟨n, rfl⟩ :=
    inertiaDegree_dvd_of_restrictMaximalUnramifiedHom_absoluteGaloisGroupExtend_eq_zpow ι hm
  exact ⟨n, (restrictMaximalUnramifiedHom_absoluteGaloisGroupExtend_eq_zpow_iff ι τ n).1 hm⟩

/-! ### The Weil transfer -/

/-- **The Weil transfer** `W_L →* W_K` along a finite extension `L/K` embedded by `ι`: the
restriction of the embedding `G_L →* G_K` of absolute Galois groups to the Weil groups. -/
def weilTransfer : WeilGroup L →* WeilGroup K :=
  (weilGroupEquivLocalWeilGroup K).symm.toMonoidHom.comp
    (((absoluteGaloisGroupExtend K L ι).comp (weilToAbsolute L)).codRestrict (localWeilGroup K)
      fun w ↦ (absoluteGaloisGroupExtend_mem_localWeilGroup_iff ι).2
        (weilToAbsolute_mem_localWeilGroup w))

variable {K L}

/-- **The characterization of the Weil transfer**: in `G_K`, the Weil transfer of `w ∈ W_L` is the
image of `w ∈ G_L` under the embedding of absolute Galois groups. -/
@[simp]
theorem weilToAbsolute_weilTransfer (w : WeilGroup L) :
    weilToAbsolute K (weilTransfer K L ι w) =
      absoluteGaloisGroupExtend K L ι (weilToAbsolute L w) :=
  weilToAbsolute_weilGroupEquivLocalWeilGroup_symm K _

/-- **The degree along the Weil transfer** is multiplied by the residue degree:
`deg_K (weilTransfer w) = f(L/K) · deg_L w`. -/
@[simp]
theorem weilDegree_weilTransfer (w : WeilGroup L) :
    weilDegree K (weilTransfer K L ι w) = weilDegree L w ^ inertiaDegree K L := by
  rw [weilDegree_eq_iff, weilToAbsolute_weilTransfer, toAdd_pow, nsmul_eq_mul]
  exact (restrictMaximalUnramifiedHom_absoluteGaloisGroupExtend_eq_zpow_iff ι _ _).2
    (restrictMaximalUnramifiedHom_weilToAbsolute w)

/-- An element of inertia of `L` maps to inertia of `K` under the Weil transfer. -/
@[simp]
theorem weilTransfer_inertiaToWeil (σ : inertiaSubgroup L) :
    weilTransfer K L ι (inertiaToWeil L σ) =
      inertiaToWeil K ⟨absoluteGaloisGroupExtend K L ι σ,
        (absoluteGaloisGroupExtend_mem_inertiaSubgroup_iff ι).2 σ.2⟩ :=
  injective_weilToAbsolute K (by simp)

variable (K L)

/-- **The Weil transfer is injective.** -/
theorem injective_weilTransfer : Function.Injective (weilTransfer K L ι) := fun _ _ h ↦
  injective_weilToAbsolute L <| injective_absoluteGaloisGroupExtend K L ι <| by
    simpa using congrArg (weilToAbsolute K) h

/-- **The Weil transfer is continuous** for the Weil topologies. -/
@[fun_prop]
theorem continuous_weilTransfer : Continuous (weilTransfer K L ι) := by
  refine (isEmbedding_weilToAbsolute_prod_weilDegree K).continuous_iff.2 ?_
  have h : (weilToAbsolute K).prod (weilDegree K) ∘ weilTransfer K L ι =
      fun w ↦ (absoluteGaloisGroupExtend K L ι (weilToAbsolute L w),
        weilDegree L w ^ inertiaDegree K L) :=
    funext fun w ↦ Prod.ext (weilToAbsolute_weilTransfer ι w) (weilDegree_weilTransfer ι w)
  rw [h]
  exact ((continuous_absoluteGaloisGroupExtend K L ι).comp (continuous_weilToAbsolute L)).prodMk
    ((continuous_weilDegree L).pow _)

/-- **The image of the Weil transfer** consists of the elements of `W_K` lying in `G_L`. -/
theorem range_weilTransfer :
    (weilTransfer K L ι).range =
      (absoluteGaloisGroupExtend K L ι).range.comap (weilToAbsolute K) := by
  ext w
  refine ⟨?_, fun ⟨τ, hτ⟩ ↦ ?_⟩
  · rintro ⟨w', rfl⟩
    exact ⟨weilToAbsolute L w', (weilToAbsolute_weilTransfer ι w').symm⟩
  · -- `τ` lies in the Weil group of `L`, since its image `w` lies in that of `K`.
    have hτL : τ ∈ localWeilGroup L := (absoluteGaloisGroupExtend_mem_localWeilGroup_iff ι).1
      (hτ ▸ weilToAbsolute_mem_localWeilGroup w)
    refine ⟨(weilGroupEquivLocalWeilGroup L).symm ⟨τ, hτL⟩, injective_weilToAbsolute K ?_⟩
    rw [weilToAbsolute_weilTransfer, weilToAbsolute_weilGroupEquivLocalWeilGroup_symm, hτ]

/-- **The image of the Weil transfer is open** in `W_K`. -/
theorem isOpen_range_weilTransfer :
    IsOpen ((weilTransfer K L ι).range : Set (WeilGroup K)) := by
  rw [range_weilTransfer]
  exact (isOpen_range_absoluteGaloisGroupExtend K L ι).preimage (continuous_weilToAbsolute K)

/-- **The image of the Weil transfer has index `[L : K]`** in `W_K`, as the image of `G_L` has in
`G_K`, since `W_K` is dense in `G_K`. -/
theorem index_range_weilTransfer :
    (weilTransfer K L ι).range.index = Module.finrank K L := by
  rw [range_weilTransfer,
    Subgroup.index_comap_of_denseRange (denseRange_weilToAbsolute K)
      (isOpen_range_absoluteGaloisGroupExtend K L ι),
    index_range_absoluteGaloisGroupExtend]

/-! ### The Weil restriction -/

section Restrict

variable [Normal K L]

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
  [FiniteDimensional K L] in
/-- **The Weil restriction** `W_K →* Gal(L/K)` for a finite normal extension `L/K` embedded by
`ι`: an element of the Weil group of `K` acts on the image of `ι`, and so on `L`. -/
def weilRestrict : WeilGroup K →* Gal(L/K) :=
  ι.restrictNormalHom.comp
    ((absoluteGaloisGroupRestrictEquiv K).toMulEquiv.toMonoidHom.comp (weilToAbsolute K))

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
  [FiniteDimensional K L] in
variable {K L} in
/-- The Weil restriction of `w` is the restriction along `ι` of the automorphism `w` of `Kˢ`. -/
@[simp]
theorem weilRestrict_apply (w : WeilGroup K) :
    weilRestrict K L ι w =
      ι.restrictNormalHom (absoluteGaloisGroupRestrictEquiv K (weilToAbsolute K w)) :=
  (rfl)

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
  [FiniteDimensional K L] in
variable {K L} in
/-- **The characterization of the Weil restriction**: `weilRestrict K L ι w` is the automorphism of
`L` through which `w` acts on `ι(L)`. -/
theorem weilRestrict_commutes (w : WeilGroup K) (x : L) :
    ι (weilRestrict K L ι w x) = absoluteGaloisGroupRestrictEquiv K (weilToAbsolute K w) (ι x) := by
  rw [weilRestrict_apply, AlgHom.restrictNormalHom_commutes]

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] in
/-- **The Weil restriction is surjective**, since `W_K` is dense in `G_K` and the fibres of
restriction `G_K → Gal(L/K)` are cosets of the open subgroup `galoisSubgroup K L ι`. -/
theorem surjective_weilRestrict : Function.Surjective (weilRestrict K L ι) := fun g ↦ by
  obtain ⟨σ, rfl⟩ := ι.restrictNormalHom_surjective g
  -- The coset `σ • galoisSubgroup K L ι` is open, so it meets the dense image of `W_K` in `Kˢ`.
  have hdense : DenseRange fun w : WeilGroup K ↦ absoluteGaloisGroupRestrictEquiv K
      (weilToAbsolute K w) :=
    (absoluteGaloisGroupRestrictEquiv K).surjective.denseRange.comp (denseRange_weilToAbsolute K)
      (absoluteGaloisGroupRestrictEquiv K).continuous
  obtain ⟨w, hw⟩ := hdense.exists_mem_open ((galoisSubgroup K L ι).isOpen.leftCoset σ)
    ⟨σ, mem_own_leftCoset (galoisSubgroup K L ι).toSubgroup.toSubmonoid σ⟩
  have hmem : ι.restrictNormalHom (σ⁻¹ * absoluteGaloisGroupRestrictEquiv K (weilToAbsolute K w)) =
      1 := by
    rw [← MonoidHom.mem_ker, AlgHom.ker_restrictNormalHom, ← galoisSubgroup_toSubgroup,
      OpenSubgroup.mem_toSubgroup]
    exact (mem_leftCoset_iff σ).1 hw
  refine ⟨w, ?_⟩
  rw [weilRestrict_apply, ← mul_inv_cancel_left σ (absoluteGaloisGroupRestrictEquiv K _), map_mul,
    hmem, mul_one]

/-- **Exactness of `1 → W_L → W_K → Gal(L/K) → 1` in the middle**: the image of the Weil
transfer is the kernel of the Weil restriction. -/
theorem range_weilTransfer_eq_ker_weilRestrict :
    (weilTransfer K L ι).range = (weilRestrict K L ι).ker := by
  ext w
  rw [iff_comm, range_weilTransfer, Subgroup.mem_comap, mem_range_absoluteGaloisGroupExtend_iff,
    ← OpenSubgroup.mem_toSubgroup, galoisSubgroup_toSubgroup, ← AlgHom.ker_restrictNormalHom,
    MonoidHom.mem_ker, MonoidHom.mem_ker, weilRestrict_apply]

end Restrict

end TauCeti.ClassFieldTheory
