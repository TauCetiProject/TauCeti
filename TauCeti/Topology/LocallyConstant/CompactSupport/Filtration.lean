/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.LocallyConstant.CompactSupport.OpenClosed
public import TauCeti.Topology.Sets.CompactOpens
public import Mathlib.LinearAlgebra.Isomorphisms
import TauCeti.Topology.Spectral.Prespectral

/-!
# The filtration of compactly supported locally constant functions by open subsets

Let `X` be a topological space and `M` an `R`-module. For a subset `U ⊆ X`, the locally constant
functions `X → M` with compact support that vanish off `U` form a submodule
`LocallyConstant.compactlySupportedIn R M U` of `LocallyConstant X M`, contained in `C_c^∞(X, M)`
(`LocallyConstant.compactlySupportedIn_le_compactlySupported`); for `U` open in a Hausdorff space
it is the image of extension by zero `C_c^∞(U, M) → C_c^∞(X, M)`
(`LocallyConstant.compactlySupported.range_subtype_comp_extendByZero`).
A filtration of `X` by open subsets `∅ = U₀ ⊆ U₁ ⊆ ⋯ ⊆ Uₙ = X` therefore gives a filtration of
`C_c^∞(X, M)` running from `0` to the whole module.

For open subsets `V` and `W` of an l-space `X` (Hausdorff, locally compact and totally
disconnected), restriction to the locally closed stratum `W \ V` identifies the successive quotient
with compact sections on the stratum:

`C_c^∞(X, M)_W / C_c^∞(X, M)_V ≃ C_c^∞(W \ V, M)`.

The restriction of a function vanishing off `W` has compact support on `W \ V`, because its support
meets `W \ V` in its intersection with the closed set `Vᶜ`. The kernel is `C_c^∞(X, M)_V` (inside
`C_c^∞(X, M)_W`), and restriction is surjective because a compact open subset of the stratum is cut
out by a compact open subset of `X` contained in `W`
(`TopologicalSpace.CompactOpens.exists_subset_preimage_subtypeVal_eq`).

## Main definitions

* `LocallyConstant.compactlySupportedIn R M U`: compactly supported functions vanishing off `U`.
* `LocallyConstant.restrictStratum R M hV W`: restriction from `C_c^∞(X, M)_W` to
  `C_c^∞(W \ V, M)`, for `V` open.
* `LocallyConstant.stratumEquiv R M hV hW`: the successive quotient
  `C_c^∞(X, M)_W / C_c^∞(X, M)_V` is `C_c^∞(W \ V, M)`, for `V` and `W` open in an l-space.

## Main results

* `LocallyConstant.compactlySupported.range_subtype_comp_extendByZero`: `C_c^∞(X, M)_U` is the
  image of extension by zero from an open `U`.
* `LocallyConstant.compactlySupportedIn_empty`, `LocallyConstant.compactlySupportedIn_univ`,
  `LocallyConstant.compactlySupportedIn_monotone`: the filtration starts at `0`, ends at
  `C_c^∞(X, M)` and is monotone.
* `LocallyConstant.ker_restrictStratum`, `LocallyConstant.restrictStratum_surjective`: the exact
  sequence `0 → C_c^∞(X, M)_V → C_c^∞(X, M)_W → C_c^∞(W \ V, M) → 0` for `V ⊆ W`.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §1.2, Proposition 2, p. 8.
-/

public section

open Function Set Topology TopologicalSpace

namespace LocallyConstant

variable {R X M : Type*} [TopologicalSpace X]

section Semiring

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable (R M) in
/-- The submodule `C_c^∞(X, M)_U` of locally constant functions `X → M` with compact support that
vanish off `U`. For `U` open in a Hausdorff space it is the image of `C_c^∞(U, M)` under extension
by zero (`LocallyConstant.compactlySupported.range_subtype_comp_extendByZero`). -/
def compactlySupportedIn (U : Set X) : Submodule R (LocallyConstant X M) where
  carrier := {f | HasCompactSupport f ∧ ∀ x, x ∉ U → f x = 0}
  add_mem' hf hg := ⟨hf.1.add hg.1, fun x hx => by simp [hf.2 x hx, hg.2 x hx]⟩
  zero_mem' := ⟨HasCompactSupport.zero, fun _ _ => rfl⟩
  smul_mem' c f hf := ⟨hf.1.mono (support_const_smul_subset c f), fun x hx => by simp [hf.2 x hx]⟩

@[simp]
theorem mem_compactlySupportedIn {U : Set X} {f : LocallyConstant X M} :
    f ∈ compactlySupportedIn R M U ↔ HasCompactSupport f ∧ ∀ x, x ∉ U → f x = 0 :=
  Iff.rfl

/-- A function lies in `C_c^∞(X, M)_U` exactly when it has compact support contained in `U`. -/
theorem mem_compactlySupportedIn_iff_support_subset {U : Set X} {f : LocallyConstant X M} :
    f ∈ compactlySupportedIn R M U ↔ HasCompactSupport f ∧ support f ⊆ U := by
  rw [mem_compactlySupportedIn, support_subset_iff']

theorem compactlySupportedIn_le_compactlySupported (U : Set X) :
    compactlySupportedIn R M U ≤ compactlySupported R X M :=
  fun _ hf => mem_compactlySupported.2 hf.1

variable (R X M) in
/-- The filtration by supports is monotone. -/
theorem compactlySupportedIn_monotone : Monotone (compactlySupportedIn R M : Set X → _) :=
  fun _ _ h _ hf => ⟨hf.1, fun x hx => hf.2 x fun h' => hx (h h')⟩

theorem compactlySupportedIn_mono {U V : Set X} (h : U ⊆ V) :
    compactlySupportedIn R M U ≤ compactlySupportedIn R M V :=
  compactlySupportedIn_monotone R X M h

variable (R X M) in
@[simp]
theorem compactlySupportedIn_empty : compactlySupportedIn R M (∅ : Set X) = ⊥ :=
  eq_bot_iff.2 fun _ hf => (Submodule.mem_bot R).2 <| ext fun x => hf.2 x id

variable (R X M) in
@[simp]
theorem compactlySupportedIn_univ :
    compactlySupportedIn R M (univ : Set X) = compactlySupported R X M :=
  le_antisymm (compactlySupportedIn_le_compactlySupported _) fun _ hf =>
    ⟨mem_compactlySupported.1 hf, fun x hx => absurd (mem_univ x) hx⟩

theorem compactlySupportedIn_inter (U V : Set X) :
    compactlySupportedIn R M (U ∩ V) = compactlySupportedIn R M U ⊓ compactlySupportedIn R M V := by
  refine le_antisymm (le_inf (compactlySupportedIn_mono inter_subset_left)
    (compactlySupportedIn_mono inter_subset_right)) fun f ⟨hU, hV⟩ => ⟨hU.1, fun x hx => ?_⟩
  by_cases hxU : x ∈ U
  · exact hV.2 x fun hxV => hx ⟨hxU, hxV⟩
  · exact hU.2 x hxU

/-- The indicator `1_K • m` of a compact open set `K ⊆ U` lies in `C_c^∞(X, M)_U`. -/
theorem compactOpenIndicator_mem_compactlySupportedIn [T2Space X] {U : Set X} {K : CompactOpens X}
    (hKU : (K : Set X) ⊆ U) (m : M) : compactOpenIndicator K m ∈ compactlySupportedIn R M U :=
  ⟨mem_compactlySupported.1 (compactOpenIndicator_mem_compactlySupported (R := R) K m),
    fun _ hx => compactOpenIndicator_of_notMem (fun h => hx (hKU h)) m⟩

/-- For an open subset `U` of a Hausdorff space, `C_c^∞(X, M)_U` is the image of extension by zero
`C_c^∞(U, M) → C_c^∞(X, M)`. -/
theorem compactlySupported.range_subtype_comp_extendByZero [T2Space X] {U : Set X} (hU : IsOpen U) :
    LinearMap.range ((compactlySupported R X M).subtype ∘ₗ
      compactlySupported.extendByZero R M hU) = compactlySupportedIn R M U := by
  ext f
  simp only [LinearMap.mem_range, LinearMap.coe_comp, Submodule.coe_subtype, comp_apply]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨mem_compactlySupported.1 (compactlySupported.extendByZero R M hU g).property,
      fun x hx => compactlySupported.extendByZero_apply_of_notMem hU g hx⟩
  · intro hf
    obtain ⟨g, hg⟩ := ((compactlySupported.exact_extendByZero_restrict (R := R) (M := M) hU)
      ⟨f, mem_compactlySupported.2 hf.1⟩).1
        (compactlySupported.ext fun x => by simpa using hf.2 x x.property)
    exact ⟨g, congr_arg Subtype.val hg⟩

section Stratum

variable {V S : Set X}

/-- The restriction of a function in `C_c^∞(X, M)_W` to the stratum `W \ V` has compact support,
as the support meets `W \ V` in its intersection with the closed set `Vᶜ`. -/
theorem hasCompactSupport_comap_stratum (hV : IsOpen V) {W : Set X} (hS : S = W \ V)
    (f : compactlySupportedIn R M W) :
    HasCompactSupport ((f : LocallyConstant X M).comap
      ⟨Subtype.val, continuous_subtypeVal⟩ : LocallyConstant S M) := by
  subst hS
  rw [hasCompactSupport_iff_isCompact_support, Subtype.isCompact_iff]
  have hsupp : support (f : LocallyConstant X M) ⊆ W :=
    (mem_compactlySupportedIn_iff_support_subset.1 f.property).2
  have himage : Subtype.val '' support ((f : LocallyConstant X M).comap
      ⟨Subtype.val, continuous_subtypeVal⟩ : LocallyConstant (W \ V : Set X) M) =
      support (f : LocallyConstant X M) ∩ Vᶜ := by
    ext x
    simp
    grind
  rw [himage]
  exact (hasCompactSupport_iff_isCompact_support.1 f.property.1).inter_right hV.isClosed_compl

variable (R M) in
/-- Restriction from `C_c^∞(X, M)_W` to the stratum `W \ V`, for `V` open. -/
def restrictStratum (hV : IsOpen V) (W : Set X) (hS : S = W \ V) :
    compactlySupportedIn R M W →ₗ[R] compactlySupported R S M where
  toFun f := ⟨(f : LocallyConstant X M).comap ⟨Subtype.val, continuous_subtypeVal⟩,
    mem_compactlySupported.2 (hasCompactSupport_comap_stratum hV hS f)⟩
  map_add' _ _ := compactlySupported.ext fun _ => by simp
  map_smul' _ _ := compactlySupported.ext fun _ => by simp

@[simp]
theorem restrictStratum_apply (hV : IsOpen V) {W : Set X} (hS : S = W \ V)
    (f : compactlySupportedIn R M W) (x : S) :
    (restrictStratum R M hV W hS f : LocallyConstant S M) x =
      (f : LocallyConstant X M) x := by
  simp [restrictStratum]

/-- The kernel of restriction from `C_c^∞(X, M)_W` to the stratum `W \ V` is `C_c^∞(X, M)_V`. -/
theorem ker_restrictStratum (hV : IsOpen V) (W : Set X) (hS : S = W \ V) :
    LinearMap.ker (restrictStratum R M hV W hS) =
      (compactlySupportedIn R M V).comap (compactlySupportedIn R M W).subtype := by
  subst hS
  ext f
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype,
    mem_compactlySupportedIn]
  constructor
  · intro hf
    refine ⟨f.property.1, fun x hxV => ?_⟩
    by_cases hxW : x ∈ W
    · simpa using congr_arg
        (fun g : compactlySupported R (W \ V : Set X) M => g.val ⟨x, hxW, hxV⟩) hf
    · exact f.property.2 x hxW
  · intro hf
    exact compactlySupported.ext fun x => by simpa using hf.2 x x.property.2

/-- In an l-space, restriction from `C_c^∞(X, M)_W` to the stratum `W \ V` is surjective for `W`
open. A compact open subset of the stratum is cut out by a compact open subset of `X` contained in
`W`, so the spanning indicators `1_K • m` of `C_c^∞(W \ V, M)` are restrictions. -/
theorem restrictStratum_surjective [T2Space X] [WeaklyLocallyCompactSpace X]
    [TotallyDisconnectedSpace X] (hV : IsOpen V) {W : Set X} (hW : IsOpen W)
    (hS : S = W \ V) : Surjective (restrictStratum R M hV W hS) := by
  have : PrespectralSpace X := .of_locallyCompactSpace_of_zeroDimensionalSpace
  refine compactlySupported.surjective_of_forall_compactOpenIndicator _ fun K m => ?_
  obtain ⟨K', hK'W, hK'⟩ :=
    CompactOpens.exists_subset_preimage_subtypeVal_eq hW (hS.subset.trans sdiff_subset) K
  exact ⟨⟨_, compactOpenIndicator_mem_compactlySupportedIn hK'W m⟩,
    comap_subtypeVal_compactOpenIndicator hK' m⟩

end Stratum

end Semiring

section Ring

variable [Ring R] [AddCommGroup M] [Module R M] [T2Space X] [WeaklyLocallyCompactSpace X]
  [TotallyDisconnectedSpace X] {V W S : Set X}

variable (R M) in
/-- **The successive quotients of the support filtration**: for open subsets `V` and `W` of an
l-space, restriction identifies `C_c^∞(X, M)_W / C_c^∞(X, M)_V` with `C_c^∞(W \ V, M)`. -/
noncomputable def stratumEquiv (hV : IsOpen V) (hW : IsOpen W) (hS : S = W \ V) :
    (compactlySupportedIn R M W ⧸
        (compactlySupportedIn R M V).comap (compactlySupportedIn R M W).subtype) ≃ₗ[R]
      compactlySupported R S M :=
  (Submodule.quotEquivOfEq _ _ (ker_restrictStratum hV W hS).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (restrictStratum_surjective hV hW hS))

@[simp]
theorem stratumEquiv_mk (hV : IsOpen V) (hW : IsOpen W) (hS : S = W \ V)
    (f : compactlySupportedIn R M W) :
    stratumEquiv R M hV hW hS (Submodule.Quotient.mk f) = restrictStratum R M hV W hS f :=
  (rfl)

end Ring

end LocallyConstant
