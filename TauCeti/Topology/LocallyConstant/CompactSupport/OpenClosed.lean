/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.LocallyConstant.CompactSupport
public import Mathlib.Algebra.Exact.Basic
import Mathlib.Topology.Separation.Regular

/-!
# The open-closed exact sequence of locally constant functions with compact support

Let `X` be a topological space, `U ⊆ X` an open subset with closed complement `Z = X ∖ U`, and `M`
an `R`-module. This file constructs the two maps of the open-closed sequence
`0 → C_c^∞(U, M) → C_c^∞(X, M) → C_c^∞(Z, M) → 0`:

* `LocallyConstant.compactlySupported.extendByZero R M hU`: for `X` Hausdorff, extension by zero
  from the open subset `U`. Off `U` the extension vanishes on the complement of the compact, hence
  closed, support, so it is again locally constant.
* `LocallyConstant.compactlySupported.restrict R M hZ`: restriction to a closed subset `Z`.

The sequence is exact at `C_c^∞(U, M)` and `C_c^∞(X, M)` for every Hausdorff `X`. Restriction is
surjective when `X` is an *l-space* (Hausdorff, locally compact and totally disconnected): a
compact open subset `K` of `Z` is cut out of `Z` by a compact open subset of `X`, found by covering
the compact set `K` with compact open neighbourhoods inside an open set meeting `Z` in `K`, so every
indicator `1_K • m` extends, and these indicators span `C_c^∞(Z, M)`.

## Main definitions

* `LocallyConstant.extendByZero hU f hf`: the extension by zero of a compactly supported locally
  constant function on an open subset.
* `LocallyConstant.compactlySupported.extendByZero`, `LocallyConstant.compactlySupported.restrict`:
  the two maps of the sequence, as `R`-linear maps.

## Main results

* `LocallyConstant.compactlySupported.extendByZero_injective`: exactness at `C_c^∞(U, M)`.
* `LocallyConstant.compactlySupported.exact_extendByZero_restrict`: exactness at `C_c^∞(X, M)`.
* `LocallyConstant.compactlySupported.restrict_surjective`: exactness at `C_c^∞(Z, M)` for an
  l-space `X`.
* `TopologicalSpace.CompactOpens.exists_between`: in an l-space, a compact set inside an open set
  lies in a compact open set between them.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §1.2, Proposition 2, p. 8.
-/

public section

open Function Set Topology TopologicalSpace

namespace TopologicalSpace.CompactOpens

variable {X : Type*} [TopologicalSpace X] [T2Space X] [WeaklyLocallyCompactSpace X]
  [TotallyDisconnectedSpace X]

/-- In an l-space (Hausdorff, locally compact and totally disconnected), a compact set `K` inside
an open set `V` lies in a compact open set between them. -/
theorem exists_between {K V : Set X} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ W : CompactOpens X, K ⊆ W ∧ (W : Set X) ⊆ V := by
  obtain ⟨L, hL, hKL, hLV⟩ := exists_compact_between hK hV hKV
  -- Each point of `K` has a clopen, hence compact, neighbourhood inside `interior L`.
  have hs (x : K) : ∃ s : Set X, IsClopen s ∧ (x : X) ∈ s ∧ s ⊆ interior L :=
    exists_isClopen_mem_of_isOpen isOpen_interior (hKL x.property)
  choose s hsc hxs hsL using hs
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover s (fun x => (hsc x).isOpen) fun x hx =>
    mem_iUnion.2 ⟨⟨x, hx⟩, hxs _⟩
  refine ⟨⟨⟨⋃ x ∈ t, s x, t.isCompact_biUnion fun x _ =>
    hL.of_isClosed_subset (hsc x).isClosed ((hsL x).trans interior_subset)⟩,
    isOpen_biUnion fun x _ => (hsc x).isOpen⟩, ht, iUnion₂_subset fun x _ => ?_⟩
  exact (hsL x).trans (interior_subset.trans hLV)

/-- In an l-space, every compact open subset `K` of a subspace `Z` is cut out of `Z` by a compact
open subset of the whole space. -/
theorem exists_preimage_subtypeVal_eq {Z : Set X} (K : CompactOpens Z) :
    ∃ W : CompactOpens X, Subtype.val ⁻¹' (W : Set X) = (K : Set Z) := by
  obtain ⟨V, hV, hVK⟩ := isOpen_induced_iff.1 K.isOpen
  have hKV : Subtype.val '' (K : Set Z) ⊆ V := by
    rintro _ ⟨z, hz, rfl⟩
    rw [← hVK] at hz
    exact hz
  obtain ⟨W, hKW, hWV⟩ := exists_between (K.isCompact.image continuous_subtypeVal) hV hKV
  refine ⟨W, Subset.antisymm ?_ fun z hz => hKW ⟨z, hz, rfl⟩⟩
  rw [← hVK]
  exact preimage_mono hWV

end TopologicalSpace.CompactOpens

namespace LocallyConstant

variable {R X M : Type*} [TopologicalSpace X]

section ExtendByZero

variable [Zero M] [T2Space X] {U : Set X}

/-- Extension by zero of a compactly supported locally constant function `f` on an open subset `U`
of a Hausdorff space: the function equal to `f` on `U` and to `0` off `U`. It is locally constant
off `U` because it vanishes off the compact, hence closed, image of the support of `f`. -/
noncomputable def extendByZero (hU : IsOpen U) (f : LocallyConstant U M)
    (hf : HasCompactSupport f) : LocallyConstant X M where
  toFun := extend Subtype.val f 0
  isLocallyConstant := by
    have hext (y : X) (hy : y ∉ U) : extend Subtype.val f 0 y = 0 :=
      extend_apply' _ _ _ fun ⟨a, ha⟩ => hy (by subst ha; exact a.property)
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    by_cases hx : x ∈ U
    · -- Near a point of `U`, the extension is `f`, which is locally constant.
      lift x to U using hx
      rw [← hU.isOpenEmbedding_subtypeVal.map_nhds_eq x, Filter.eventually_map]
      filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 f.isLocallyConstant x] with y hy
      simpa [Subtype.val_injective.extend_apply] using hy
    · -- Off `U`, the extension vanishes outside the closed image of the support of `f`.
      have hS : IsClosed (Subtype.val '' support f) :=
        ((hasCompactSupport_iff_isCompact_support.1 hf).image continuous_subtypeVal).isClosed
      have hxS : x ∉ Subtype.val '' support f := fun ⟨y, _, hy⟩ => hx (hy ▸ y.property)
      filter_upwards [hS.isOpen_compl.mem_nhds hxS] with y hy
      rw [hext x hx]
      by_cases hyU : y ∈ U
      · lift y to U using hyU
        rw [Subtype.val_injective.extend_apply]
        exact by_contra fun hne => hy ⟨y, hne, rfl⟩
      · exact hext y hyU

variable (hU : IsOpen U) (f : LocallyConstant U M) (hf : HasCompactSupport f)

@[simp]
theorem extendByZero_apply_coe (x : U) : extendByZero hU f hf x = f x :=
  Subtype.val_injective.extend_apply _ _ x

theorem extendByZero_apply_of_notMem {x : X} (hx : x ∉ U) : extendByZero hU f hf x = 0 :=
  extend_apply' _ _ _ fun ⟨a, ha⟩ => hx (by subst ha; exact a.property)

/-- The support of the extension by zero is the image of the support. -/
theorem support_extendByZero : support (extendByZero hU f hf) = Subtype.val '' support f := by
  ext x
  by_cases hx : x ∈ U
  · lift x to U using hx
    simp
  · simp only [mem_support, extendByZero_apply_of_notMem hU f hf hx, ne_eq, not_true_eq_false,
      false_iff]
    exact fun ⟨y, _, hy⟩ => hx (hy ▸ y.property)

theorem hasCompactSupport_extendByZero : HasCompactSupport (extendByZero hU f hf) := by
  rw [hasCompactSupport_iff_isCompact_support, support_extendByZero]
  exact (hasCompactSupport_iff_isCompact_support.1 hf).image continuous_subtypeVal

end ExtendByZero

namespace compactlySupported

variable [Semiring R] [AddCommMonoid M] [Module R M]

section ExtendByZero

variable [T2Space X] {U : Set X} (hU : IsOpen U)

variable (R M) in
/-- Extension by zero `C_c^∞(U, M) → C_c^∞(X, M)` from an open subset `U` of a Hausdorff space,
as an `R`-linear map. -/
noncomputable def extendByZero :
    compactlySupported R U M →ₗ[R] compactlySupported R X M where
  toFun f := ⟨LocallyConstant.extendByZero hU f (mem_compactlySupported.1 f.property),
    mem_compactlySupported.2 (hasCompactSupport_extendByZero hU _ _)⟩
  map_add' f g := compactlySupported.ext fun x => by
    by_cases hx : x ∈ U
    · lift x to U using hx
      simp
    · simp [extendByZero_apply_of_notMem _ _ _ hx]
  map_smul' c f := compactlySupported.ext fun x => by
    by_cases hx : x ∈ U
    · lift x to U using hx
      simp
    · simp [extendByZero_apply_of_notMem _ _ _ hx]

@[simp]
theorem extendByZero_apply_coe (f : compactlySupported R U M) (x : U) :
    (extendByZero R M hU f : LocallyConstant X M) x = (f : LocallyConstant U M) x :=
  LocallyConstant.extendByZero_apply_coe hU _ (mem_compactlySupported.1 f.property) x

theorem extendByZero_apply_of_notMem (f : compactlySupported R U M) {x : X} (hx : x ∉ U) :
    (extendByZero R M hU f : LocallyConstant X M) x = 0 :=
  LocallyConstant.extendByZero_apply_of_notMem hU _ (mem_compactlySupported.1 f.property) hx

/-- Extension by zero is injective: the sequence is exact at `C_c^∞(U, M)`. -/
theorem extendByZero_injective : Injective (extendByZero R M hU) := fun f g h =>
  compactlySupported.ext fun x => by
    simpa using congr_arg (fun F : compactlySupported R X M => (F : LocallyConstant X M) x) h

end ExtendByZero

section Restrict

variable {Z : Set X} (hZ : IsClosed Z)

variable (R M) in
/-- Restriction `C_c^∞(X, M) → C_c^∞(Z, M)` to a closed subset `Z`, as an `R`-linear map. -/
def restrict : compactlySupported R X M →ₗ[R] compactlySupported R Z M where
  toFun f := ⟨(f : LocallyConstant X M).comap ⟨Subtype.val, continuous_subtypeVal⟩,
    mem_compactlySupported.2 ((mem_compactlySupported.1 f.property).comp_isClosedEmbedding
      hZ.isClosedEmbedding_subtypeVal)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem restrict_apply (f : compactlySupported R X M) (z : Z) :
    (restrict R M hZ f : LocallyConstant Z M) z = (f : LocallyConstant X M) z :=
  (rfl)

/-- In an l-space, restriction to a closed subset is surjective: the sequence is exact at
`C_c^∞(Z, M)`. Every compact open subset of `Z` is cut out by a compact open subset of `X`, so the
spanning indicators `1_K • m` of `C_c^∞(Z, M)` are restrictions. -/
theorem restrict_surjective [T2Space X] [WeaklyLocallyCompactSpace X]
    [TotallyDisconnectedSpace X] : Surjective (restrict R M hZ) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  intro f _
  have hf : (f : LocallyConstant Z M) ∈
      Submodule.span R (range fun p : CompactOpens Z × M => compactOpenIndicator p.1 p.2) := by
    rw [← compactlySupported_eq_span]
    exact f.property
  -- The range contains the span of the indicators, as a submodule of `LocallyConstant Z M`.
  suffices h : Submodule.span R (range fun p : CompactOpens Z × M => compactOpenIndicator p.1 p.2)
      ≤ (LinearMap.range (restrict R M hZ)).map (compactlySupported R Z M).subtype by
    obtain ⟨g, hg, hgf⟩ := h hf
    exact Subtype.val_injective hgf ▸ hg
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨K, m⟩, rfl⟩
  obtain ⟨W, hW⟩ := CompactOpens.exists_preimage_subtypeVal_eq K
  refine ⟨restrict R M hZ
    ⟨compactOpenIndicator W m, compactOpenIndicator_mem_compactlySupported W m⟩,
    LinearMap.mem_range_self _ _, LocallyConstant.ext fun z => ?_⟩
  simp only [Submodule.coe_subtype, restrict_apply, coe_compactOpenIndicator]
  by_cases hz : (z : X) ∈ (W : Set X)
  · have hzK : z ∈ (K : Set Z) := hW ▸ hz
    simp [hz, hzK]
  · have hzK : z ∉ (K : Set Z) := hW ▸ hz
    simp [hz, hzK]

end Restrict

/-- **The open-closed exact sequence**, exactness at `C_c^∞(X, M)`: for an open subset `U` of a
Hausdorff space `X`, a compactly supported locally constant function on `X` vanishes on the closed
complement of `U` exactly when it is the extension by zero of one on `U`. -/
theorem exact_extendByZero_restrict [T2Space X] {U : Set X} (hU : IsOpen U) :
    Exact (extendByZero R M hU) (restrict R M hU.isClosed_compl) := by
  intro f
  constructor
  · intro hf
    -- `f` vanishes off `U`, so its restriction to `U` has the same compact support.
    have hfU : ∀ x, x ∉ U → (f : LocallyConstant X M) x = 0 := fun x hx => by
      simpa using congr_arg
        (fun g : compactlySupported R (Uᶜ : Set X) M => g.val ⟨x, hx⟩) hf
    have hsupp : support (f : LocallyConstant X M) ⊆ U := fun x hx =>
      by_contra fun h => hx (hfU x h)
    let g : LocallyConstant U M := (f : LocallyConstant X M).comap
      ⟨Subtype.val, continuous_subtypeVal⟩
    have hg : HasCompactSupport g := by
      rw [hasCompactSupport_iff_isCompact_support, Subtype.isCompact_iff]
      have : Subtype.val '' support g = support (f : LocallyConstant X M) := by
        rw [show support g = Subtype.val ⁻¹' support (f : LocallyConstant X M) from rfl,
          image_preimage_eq_inter_range, Subtype.range_coe, inter_eq_left.2 hsupp]
      rw [this, ← tsupport_eq_support]
      exact (mem_compactlySupported.1 f.property).isCompact
    refine ⟨⟨g, mem_compactlySupported.2 hg⟩, compactlySupported.ext fun x => ?_⟩
    by_cases hx : x ∈ U
    · lift x to U using hx
      simp [g]
    · simp [extendByZero_apply_of_notMem _ _ hx, hfU x hx]
  · rintro ⟨g, rfl⟩
    exact compactlySupported.ext fun x => by simp [extendByZero_apply_of_notMem _ _ x.property]

end compactlySupported

end LocallyConstant
