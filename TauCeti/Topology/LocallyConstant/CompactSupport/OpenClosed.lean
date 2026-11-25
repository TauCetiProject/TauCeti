/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.LocallyConstant.CompactSupport
public import Mathlib.Algebra.Exact.Basic
import Mathlib.Topology.Separation.Regular
import TauCeti.Topology.Sets.CompactOpens
import TauCeti.Topology.Spectral.Prespectral

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
surjective when `X` is an *l-space* (Hausdorff, locally compact and totally disconnected): such a
space is prespectral, so a compact open subset `K` of `Z` is cut out of `Z` by a compact open subset
of `X` (`TopologicalSpace.CompactOpens.exists_subset_preimage_subtypeVal_eq`), every indicator
`1_K • m` extends, and these indicators span `C_c^∞(Z, M)`.

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
* `LocallyConstant.compactlySupported.restrict_extendByZero`: restricting an extension by zero to
  the complement gives `0`.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §1.2, Proposition 2, p. 8.
-/

public section

open Function Set Topology TopologicalSpace

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
    let : TopologicalSpace M := ⊥
    have : DiscreteTopology M := ⟨rfl⟩
    exact (IsLocallyConstant.iff_continuous _).2 (hf.continuous_extend_zero hU f.continuous)

variable (hU : IsOpen U) (f : LocallyConstant U M) (hf : HasCompactSupport f)

@[simp]
theorem extendByZero_apply_coe (x : U) : extendByZero hU f hf x = f x :=
  Subtype.val_injective.extend_apply _ _ x

@[simp]
theorem extendByZero_apply_of_notMem {x : X} (hx : x ∉ U) : extendByZero hU f hf x = 0 :=
  extend_apply' _ _ _ fun ⟨a, ha⟩ => hx (by subst ha; exact a.property)

end ExtendByZero

namespace compactlySupported

variable [Semiring R] [AddCommMonoid M] [Module R M]

/-- Two compactly supported locally constant functions on `X` agree if they agree on a set `U` and
off it. -/
private theorem ext_of_mem_of_notMem {U : Set X} {f g : compactlySupported R X M}
    (h₁ : ∀ x : U, (f : LocallyConstant X M) x = (g : LocallyConstant X M) x)
    (h₂ : ∀ x, x ∉ U → (f : LocallyConstant X M) x = (g : LocallyConstant X M) x) : f = g :=
  compactlySupported.ext fun x => by
    by_cases hx : x ∈ U
    · exact h₁ ⟨x, hx⟩
    · exact h₂ x hx

section ExtendByZero

variable [T2Space X] {U : Set X} (hU : IsOpen U)

variable (R M) in
/-- Extension by zero `C_c^∞(U, M) → C_c^∞(X, M)` from an open subset `U` of a Hausdorff space,
as an `R`-linear map. -/
noncomputable def extendByZero :
    compactlySupported R U M →ₗ[R] compactlySupported R X M where
  toFun f := ⟨LocallyConstant.extendByZero hU f (mem_compactlySupported.1 f.property),
    mem_compactlySupported.2 ((mem_compactlySupported.1 f.property).extend_zero
      continuous_subtypeVal)⟩
  map_add' f g := ext_of_mem_of_notMem (U := U) (fun x => by simp) fun x hx => by simp [hx]
  map_smul' c f := ext_of_mem_of_notMem (U := U) (fun x => by simp) fun x hx => by simp [hx]

@[simp]
theorem extendByZero_apply_coe (f : compactlySupported R U M) (x : U) :
    (extendByZero R M hU f : LocallyConstant X M) x = (f : LocallyConstant U M) x :=
  LocallyConstant.extendByZero_apply_coe hU _ (mem_compactlySupported.1 f.property) x

@[simp]
theorem extendByZero_apply_of_notMem (f : compactlySupported R U M) {x : X} (hx : x ∉ U) :
    (extendByZero R M hU f : LocallyConstant X M) x = 0 :=
  LocallyConstant.extendByZero_apply_of_notMem hU _ (mem_compactlySupported.1 f.property) hx

/-- Extension by zero is injective: the sequence is exact at `C_c^∞(U, M)`. -/
theorem extendByZero_injective : Injective (extendByZero R M hU) := fun _ _ h =>
  compactlySupported.coeFn_injective <| extend_injective Subtype.val_injective (0 : X → M) <|
    congr_arg (fun F : compactlySupported R X M => ⇑(F : LocallyConstant X M)) h

end ExtendByZero

section Restrict

variable {Z : Set X} (hZ : IsClosed Z)

variable (R M) in
/-- Restriction `C_c^∞(X, M) → C_c^∞(Z, M)` to a closed subset `Z`, as an `R`-linear map. -/
def restrict : compactlySupported R X M →ₗ[R] compactlySupported R Z M :=
  (LocallyConstant.comapₗ R ⟨Subtype.val, continuous_subtypeVal⟩).restrict fun _ hf =>
    mem_compactlySupported.2 ((mem_compactlySupported.1 hf).comp_isClosedEmbedding
      hZ.isClosedEmbedding_subtypeVal)

@[simp]
theorem restrict_apply (f : compactlySupported R X M) (z : Z) :
    (restrict R M hZ f : LocallyConstant Z M) z = (f : LocallyConstant X M) z := by
  simp only [restrict, LinearMap.restrict_apply, comapₗ_apply_apply, ContinuousMap.coe_mk]

/-- In an l-space, restriction to a closed subset is surjective: the sequence is exact at
`C_c^∞(Z, M)`. Every compact open subset of `Z` is cut out by a compact open subset of `X`, so the
spanning indicators `1_K • m` of `C_c^∞(Z, M)` are restrictions. -/
theorem restrict_surjective [T2Space X] [WeaklyLocallyCompactSpace X]
    [TotallyDisconnectedSpace X] : Surjective (restrict R M hZ) := by
  have : PrespectralSpace X := .of_locallyCompactSpace_of_zeroDimensionalSpace
  refine surjective_of_forall_compactOpenIndicator _ fun K m => ?_
  obtain ⟨W, -, hW⟩ :=
    CompactOpens.exists_subset_preimage_subtypeVal_eq isOpen_univ (subset_univ Z) K
  exact ⟨⟨compactOpenIndicator W m, compactOpenIndicator_mem_compactlySupported W m⟩,
    comap_subtypeVal_compactOpenIndicator hW m⟩

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
    have hsupp : support (f : LocallyConstant X M) ⊆ U := Function.support_subset_iff'.2 hfU
    let g : LocallyConstant U M := (f : LocallyConstant X M).comap
      ⟨Subtype.val, continuous_subtypeVal⟩
    have hg : HasCompactSupport g := hasCompactSupport_comap_subtypeVal_of_support_subset
      (mem_compactlySupported.1 f.property) hsupp
    exact ⟨⟨g, mem_compactlySupported.2 hg⟩,
      ext_of_mem_of_notMem (U := U) (fun x => by simp [g]) fun x hx => by simp [hx, hfU x hx]⟩
  · rintro ⟨g, rfl⟩
    exact compactlySupported.ext fun x => by simp [extendByZero_apply_of_notMem _ _ x.property]

/-- Restricting an extension by zero from an open set `U` to its complement gives `0`. -/
@[simp]
theorem restrict_extendByZero [T2Space X] {U : Set X} (hU : IsOpen U)
    (f : compactlySupported R U M) :
    restrict R M hU.isClosed_compl (extendByZero R M hU f) = 0 :=
  (exact_extendByZero_restrict hU).apply_apply_eq_zero f

end compactlySupported

end LocallyConstant
