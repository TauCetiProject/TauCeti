/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Support
public import TauCeti.Analysis.Distribution.TestFunction.ExtDeriv
import TauCeti.Analysis.Calculus.DifferentialForm.Const
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity

/-!
# Localization of distributions and the augmentation

Let `Ω` be an open subset of a finite-dimensional real normed space `E`. Mathlib's `dsupport T`
of a map `T` on test functions is the complement of the union of the open sets on which `T`
vanishes. For an additive map on test functions, such as a distribution or a current, the
*localization principle* says that `T` vanishes on that union, so on the complement of its
support. Consequently `T φ` depends only on the germ of `φ` along `dsupport T`, `T` vanishes
exactly when its support is empty, and the support of a sum lies in the union of the supports.

When `dsupport T` is a compact subset of `Ω`, a test `χ` equal to one near `dsupport T` exists, and
`T (χ • c)` is independent of that cutoff for every vector `c`. This value is the *augmentation*
`augmentation T c`: the pairing of a compactly supported distribution with the constant function
`c`. For degree-zero currents and `c` the unit `0`-form it is the augmentation of the current, the
total coefficient of a finite sum of point masses. No constant test function is inserted into the
domain of `T`: when the support of `T` is not a compact subset of `Ω`, no such cutoff exists and
`augmentation T c` is the junk value zero. The augmentation of an additive map is additive in `c`,
and that of a linear map is homogeneous in `c`. The augmentation is homogeneous in the map, and on
maps whose supports are compact subsets of `Ω` it is also additive in the map. It sends the point
evaluation `φ ↦ ℓ (φ x)` to `ℓ c`, and it vanishes on the boundary `T ∘ d` of a current, because
the exterior derivative of a cutoff equal to one vanishes near the support.

## Main declarations

* `Distribution.isVanishingOn_compl_dsupport`: an additive map on test functions vanishes on the
  complement of its support; `Distribution.isVanishingOn_iff_disjoint_dsupport` is the resulting
  characterization of the open sets on which it vanishes.
* `Distribution.map_eq_map_of_eventuallyEq`: tests that agree near the support have equal values.
* `Distribution.dsupport_eq_empty_iff`: an additive map on test functions vanishes exactly when its
  support is empty.
* `Distribution.augmentation`: the pairing `T (χ • c)` with a cutoff `χ` equal to one near the
  support; `Distribution.augmentation_eq` is its independence of the cutoff.
* `Distribution.augmentation_comp_extDerivCLM`: the augmentation of a boundary is zero.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §2.2 (localization and
  support) and §2.3 (distributions with compact support).
* H. Federer, *Geometric Measure Theory*, §4.1.7 (support of a current).
-/

public section

open Set Filter TopologicalSpace ContinuousLinearMap
open scoped Distributions Topology

namespace Distribution

variable {E F V 𝓕 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E} {n : ℕ∞}

section Localization

variable [FiniteDimensional ℝ E] [AddCommMonoid V] [FunLike 𝓕 𝓓^{n}(Ω, F) V]
  [AddMonoidHomClass 𝓕 𝓓^{n}(Ω, F) V] (T : 𝓕) {𝓖 : Type*} [FunLike 𝓖 𝓓^{n}(Ω, F) V]
  [AddMonoidHomClass 𝓖 𝓓^{n}(Ω, F) V]

/-- **Localization principle.** An additive map on test functions that vanishes on each member of
a family of open sets vanishes on their union. -/
theorem isVanishingOn_iUnion {ι : Type*} {U : ι → Set E} (hU : ∀ i, IsOpen (U i))
    (hT : ∀ i, IsVanishingOn T (U i)) : IsVanishingOn T (⋃ i, U i) := by
  intro φ hφ
  obtain ⟨s, ψ, hψ, hsum, -⟩ := φ.exists_sum_subordinate U hU hφ
  rw [← hsum, map_sum]
  exact Finset.sum_eq_zero fun i _ ↦ hT i (ψ i) (hψ i)

/-- An additive map on test functions that vanishes on each member of a set of open sets vanishes
on their union. -/
theorem isVanishingOn_sUnion {S : Set (Set E)} (hS : ∀ s ∈ S, IsOpen s ∧ IsVanishingOn T s) :
    IsVanishingOn T (⋃₀ S) := by
  rw [sUnion_eq_iUnion]
  exact isVanishingOn_iUnion T (fun s ↦ (hS s s.2).1) fun s ↦ (hS s s.2).2

/-- An additive map on test functions vanishes on the complement of its support. -/
theorem isVanishingOn_compl_dsupport : IsVanishingOn T (dsupport T)ᶜ := by
  rw [dsupport_compl_eq]
  exact isVanishingOn_sUnion T fun s hs ↦ ⟨hs.2, hs.1⟩

/-- An additive map on test functions vanishes on an open set exactly when that set is disjoint
from its support. -/
theorem isVanishingOn_iff_disjoint_dsupport {s : Set E} (hs : IsOpen s) :
    IsVanishingOn T s ↔ Disjoint s (dsupport T) :=
  ⟨fun h ↦ h.disjoint_dsupport hs,
    fun h ↦ (isVanishingOn_compl_dsupport T).mono h.subset_compl_right⟩

/-- An additive map on test functions vanishes on every test whose support is disjoint from its
support. -/
theorem map_eq_zero_of_disjoint_dsupport {φ : 𝓓^{n}(Ω, F)}
    (h : Disjoint (tsupport φ) (dsupport T)) : T φ = 0 :=
  isVanishingOn_compl_dsupport T φ h.subset_compl_right

/-- An additive map on test functions vanishes exactly when its support is empty. -/
theorem dsupport_eq_empty_iff : dsupport T = ∅ ↔ ⇑T = 0 :=
  ⟨fun h ↦ funext fun φ ↦ map_eq_zero_of_disjoint_dsupport T (by simp [h]),
    fun h ↦ univ_disjoint.1 <|
      (isVanishingOn_iff_disjoint_dsupport T isOpen_univ).1 fun φ _ ↦ congrFun h φ⟩

/-- The support of a sum of additive maps on test functions lies in the union of their supports. -/
theorem dsupport_add_subset (S : 𝓖) : dsupport (⇑T + ⇑S) ⊆ dsupport T ∪ dsupport S := by
  have h : IsVanishingOn (⇑T + ⇑S) (dsupport T ∪ dsupport S)ᶜ := fun φ hφ ↦ by
    rw [compl_union] at hφ
    simp [isVanishingOn_compl_dsupport T φ (hφ.trans inter_subset_left),
      isVanishingOn_compl_dsupport S φ (hφ.trans inter_subset_right)]
  have hsub :=
    (h.disjoint_dsupport (isClosed_dsupport.union isClosed_dsupport).isOpen_compl).subset_compl_left
  rwa [compl_compl] at hsub

end Localization

section Group

variable [FiniteDimensional ℝ E] [AddCommGroup V] [FunLike 𝓕 𝓓^{n}(Ω, F) V]
  [AddMonoidHomClass 𝓕 𝓓^{n}(Ω, F) V] (T : 𝓕)

/-- The value of an additive map on test functions depends only on the germ of the test along the
support of the map. -/
theorem map_eq_map_of_eventuallyEq {φ ψ : 𝓓^{n}(Ω, F)}
    (h : (φ : E → F) =ᶠ[𝓝ˢ (dsupport T)] ψ) : T φ = T ψ := by
  obtain ⟨U, hU, hTU, hφψ⟩ := mem_nhdsSet_iff_exists.1 h
  rw [← sub_eq_zero, ← map_sub]
  refine map_eq_zero_of_disjoint_dsupport T (Disjoint.mono_left ?_ hTU.disjoint_compl_left)
  refine closure_minimal (fun x hx hxU ↦ hx ?_) hU.isClosed_compl
  have hx' : φ x = ψ x := hφψ hxU
  simp [hx']

end Group

section Augmentation

variable [Zero V]

open Classical in
/-- The **augmentation** of a map `f` on test functions at a vector `c`: the value `f (χ • c)`,
where `χ` is a test function equal to one on a neighbourhood of the support of `f`. For an additive
map it does not depend on the choice of `χ` (`Distribution.augmentation_eq`), and such a `χ`
exists when the support is a compact subset of `Ω`. It is zero when no such `χ` exists. -/
noncomputable def augmentation (f : 𝓓^{n}(Ω, F) → V) (c : F) : V :=
  if h : ∃ χ : 𝓓^{n}(Ω, ℝ), ∀ᶠ x in 𝓝ˢ (dsupport f), χ x = 1 then
    f (TestFunction.postcompCLM (toSpanSingleton ℝ c) h.choose)
  else 0

/-- The augmentation is zero when no test function is equal to one on a neighbourhood of the
support. -/
@[simp]
theorem augmentation_of_not_exists {f : 𝓓^{n}(Ω, F) → V}
    (h : ¬∃ χ : 𝓓^{n}(Ω, ℝ), ∀ᶠ x in 𝓝ˢ (dsupport f), χ x = 1) (c : F) :
    augmentation f c = 0 := by
  rw [augmentation, dite_eq_right h]

/-- The support of a boundary `T ∘ d` lies in the support of `T`. -/
theorem dsupport_comp_extDerivCLM_subset {k : ℕ} (f : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) → V) :
    dsupport (f ∘ TestFunction.extDerivCLM (k := k)) ⊆ dsupport f := by
  refine compl_subset_compl.1 fun x hx ↦ ?_
  obtain ⟨s, hf, hs, hxs⟩ := (notMem_dsupport_iff x).1 hx
  exact (notMem_dsupport_iff x).2 ⟨s, fun φ hφ ↦
    hf (TestFunction.extDerivCLM φ) ((TestFunction.tsupport_extDerivCLM_subset φ).trans hφ),
    hs, hxs⟩

end Augmentation

section AugmentationConst

/-- The augmentation of a map vanishing at zero is zero at the zero vector. -/
@[simp]
theorem augmentation_zero_right [Zero V] [FunLike 𝓕 𝓓^{n}(Ω, F) V]
    [ZeroHomClass 𝓕 𝓓^{n}(Ω, F) V] (T : 𝓕) : augmentation T (0 : F) = 0 := by
  unfold augmentation
  split_ifs
  · rw [← map_zero T]
    congr 1
    ext x
    simp
  · rfl

/-- The augmentation of an additive map is additive in the vector. -/
theorem augmentation_add_right [AddZeroClass V] [FunLike 𝓕 𝓓^{n}(Ω, F) V]
    [AddMonoidHomClass 𝓕 𝓓^{n}(Ω, F) V] (T : 𝓕) (c d : F) :
    augmentation T (c + d) = augmentation T c + augmentation T d := by
  unfold augmentation
  split_ifs
  · rw [← map_add]
    congr 1
    ext x
    simp
  · simp

/-- The augmentation of a linear map is homogeneous in the vector. -/
theorem augmentation_smul_right [AddCommMonoid V] [Module ℝ V] [FunLike 𝓕 𝓓^{n}(Ω, F) V]
    [LinearMapClass 𝓕 ℝ 𝓓^{n}(Ω, F) V] (T : 𝓕) (a : ℝ) (c : F) :
    augmentation T (a • c) = a • augmentation T c := by
  unfold augmentation
  split_ifs
  · rw [← map_smul]
    congr 1
    ext x
    simp [smul_comm a]
  · simp

end AugmentationConst

section AugmentationGroup

variable [FiniteDimensional ℝ E] [AddCommGroup V] [FunLike 𝓕 𝓓^{n}(Ω, F) V]
  [AddMonoidHomClass 𝓕 𝓓^{n}(Ω, F) V] (T : 𝓕) {𝓖 : Type*} [FunLike 𝓖 𝓓^{n}(Ω, F) V]
  [AddMonoidHomClass 𝓖 𝓓^{n}(Ω, F) V]

/-- **Independence of the cutoff.** The augmentation of an additive map on test functions is its
value on `χ • c` for any test function `χ` equal to one on a neighbourhood of its support. -/
theorem augmentation_eq {χ : 𝓓^{n}(Ω, ℝ)} (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) (c : F) :
    augmentation T c = T (TestFunction.postcompCLM (toSpanSingleton ℝ c) χ) := by
  have h : ∃ χ : 𝓓^{n}(Ω, ℝ), ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1 := ⟨χ, hχ⟩
  rw [augmentation, dite_eq_left h]
  refine map_eq_map_of_eventuallyEq T ?_
  filter_upwards [h.choose_spec, hχ] with x h₁ h₂
  simp [h₁, h₂]

/-- The augmentation is additive on additive maps whose supports are compact subsets of `Ω`. -/
theorem augmentation_add (S : 𝓖) (hT : IsCompact (dsupport T)) (hTΩ : dsupport T ⊆ Ω)
    (hS : IsCompact (dsupport S)) (hSΩ : dsupport S ⊆ Ω) (c : F) :
    augmentation (⇑T + ⇑S) c = augmentation T c + augmentation S c := by
  obtain ⟨χ, hχ, -⟩ :=
    TestFunction.exists_eventually_eq_one (n := n) (hT.union hS) (union_subset hTΩ hSΩ)
  let A : 𝓓^{n}(Ω, F) →+ V := (T : 𝓓^{n}(Ω, F) →+ V) + S
  have hA : ⇑A = ⇑T + ⇑S := by
    ext φ
    simp [A]
  have hχA : ∀ᶠ x in 𝓝ˢ (dsupport A), χ x = 1 :=
    hχ.filter_mono (nhdsSet_mono (hA ▸ dsupport_add_subset T S))
  rw [← hA, augmentation_eq A hχA, augmentation_eq T (hχ.filter_mono (nhdsSet_mono
    subset_union_left)), augmentation_eq S (hχ.filter_mono (nhdsSet_mono subset_union_right))]
  simp [A]

/-- The augmentation of a difference is the difference of the augmentations. -/
theorem augmentation_sub (S : 𝓖) (hT : IsCompact (dsupport T)) (hTΩ : dsupport T ⊆ Ω)
    (hS : IsCompact (dsupport S)) (hSΩ : dsupport S ⊆ Ω) (c : F) :
    augmentation (⇑T - ⇑S) c = augmentation T c - augmentation S c := by
  let N : 𝓓^{n}(Ω, F) →+ V := -(S : 𝓓^{n}(Ω, F) →+ V)
  have hN : dsupport N = dsupport S :=
    (dsupport_subset_dsupport fun _ _ h φ hφ ↦ by simp [N, h φ hφ]).antisymm
      (dsupport_subset_dsupport fun _ _ h φ hφ ↦ by simpa [N] using h φ hφ)
  have hNS : augmentation N c = -augmentation S c := by
    obtain ⟨χ, hχ, -⟩ := TestFunction.exists_eventually_eq_one (n := n) hS hSΩ
    rw [augmentation_eq N (hN ▸ hχ), augmentation_eq S hχ]
    simp [N]
  have h := augmentation_add T N hT hTΩ (hN ▸ hS) (hN ▸ hSΩ) c
  have hTN : ⇑T + ⇑N = ⇑T - ⇑S := by
    ext φ
    simp [N, sub_eq_add_neg]
  rw [hTN, hNS] at h
  rw [h, sub_eq_add_neg]

/-- **The augmentation of a point evaluation.** For `x ∈ Ω` and an additive map `ℓ`, the
evaluation `φ ↦ ℓ (φ x)` has augmentation `ℓ c` at `c`. For the degree-zero point current and the
unit `0`-form it is one. -/
theorem augmentation_apply_apply {x : E} (hx : x ∈ Ω) (ℓ : F →+ V) (c : F) :
    augmentation (fun φ : 𝓓^{n}(Ω, F) ↦ ℓ (φ x)) c = ℓ c := by
  let A : 𝓓^{n}(Ω, F) →+ V :=
    { toFun φ := ℓ (φ x), map_zero' := by simp, map_add' φ ψ := by simp }
  have hA : dsupport A ⊆ {x} := by
    refine compl_subset_compl.1 fun y hy ↦ ?_
    rw [mem_compl_iff, notMem_dsupport_iff]
    refine ⟨{x}ᶜ, fun φ hφ ↦ ?_, isOpen_compl_singleton, hy⟩
    simp [A, image_eq_zero_of_notMem_tsupport fun h ↦ hφ h rfl]
  obtain ⟨χ, hχ, -⟩ := TestFunction.exists_eventually_eq_one (n := n) isCompact_singleton
    (singleton_subset_iff.2 hx)
  have hχx : χ x = 1 := hχ.self_of_nhdsSet x rfl
  exact (augmentation_eq A (hχ.filter_mono (nhdsSet_mono hA)) c).trans (by simp [A, hχx])

/-- The Dirac distribution at a point of `Ω` has augmentation `c` at `c`. -/
@[simp]
theorem augmentation_delta {x : E} (hx : x ∈ Ω) (c : ℝ) :
    augmentation (delta x : 𝓓'^{n}(Ω, ℝ)) c = c := by
  have h : ⇑(delta x : 𝓓'^{n}(Ω, ℝ)) = fun φ ↦ AddMonoidHom.id ℝ (φ x) :=
    funext fun φ ↦ delta_apply x φ
  rw [h, augmentation_apply_apply hx, AddMonoidHom.id_apply]

end AugmentationGroup

section Module

variable [FiniteDimensional ℝ E] [AddCommGroup V] [Module ℝ V] [FunLike 𝓕 𝓓^{n}(Ω, F) V]
  [AddMonoidHomClass 𝓕 𝓓^{n}(Ω, F) V] (T : 𝓕)

/-- The augmentation is homogeneous. -/
theorem augmentation_smul (a : ℝ) (c : F) :
    augmentation (a • ⇑T) c = a • augmentation T c := by
  let A : 𝓓^{n}(Ω, F) →+ V := a • (T : 𝓓^{n}(Ω, F) →+ V)
  have hA : ⇑A = a • ⇑T := by
    ext φ
    simp [A]
  have hsub : dsupport A ⊆ dsupport T :=
    dsupport_subset_dsupport fun _ _ h φ hφ ↦ by simp [A, h φ hφ]
  by_cases h : ∃ χ : 𝓓^{n}(Ω, ℝ), ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1
  · obtain ⟨χ, hχ⟩ := h
    rw [← hA, augmentation_eq A (hχ.filter_mono (nhdsSet_mono hsub)), augmentation_eq T hχ]
    simp [A]
  rw [augmentation_of_not_exists h, smul_zero]
  rcases eq_or_ne a 0 with rfl | ha
  · unfold augmentation
    split_ifs <;> simp
  -- For `a ≠ 0` the supports agree, so no cutoff exists for `a • T` either.
  have hsup : dsupport T ⊆ dsupport A :=
    dsupport_subset_dsupport fun _ _ h' φ hφ ↦ by simpa [A, ha] using h' φ hφ
  rw [← hA, augmentation_of_not_exists (hsub.antisymm hsup ▸ h)]

end Module

section Boundary

variable [FiniteDimensional ℝ E] [AddCommGroup V] {k : ℕ}
  [FunLike 𝓕 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) V]
  [AddMonoidHomClass 𝓕 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) V] (T : 𝓕)

/-- **The augmentation of a boundary vanishes.** If the support of `T` is a compact subset of `Ω`,
then the boundary `T ∘ d` has augmentation zero at every constant `k`-form: the exterior derivative
of a cutoff equal to one near the support vanishes there. -/
theorem augmentation_comp_extDerivCLM (hT : IsCompact (dsupport T)) (hTΩ : dsupport T ⊆ Ω)
    (c : E [⋀^Fin k]→L[ℝ] F) : augmentation (T ∘ TestFunction.extDerivCLM) c = 0 := by
  obtain ⟨χ, hχ, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) hT hTΩ
  let A : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →+ V :=
    (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →+ V).comp
      (TestFunction.extDerivCLM : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] _).toLinearMap.toAddMonoidHom
  have hA : ⇑A = T ∘ TestFunction.extDerivCLM := by
    ext ω
    simp [A]
  have hχA : ∀ᶠ x in 𝓝ˢ (dsupport A), χ x = 1 :=
    hχ.filter_mono (nhdsSet_mono (dsupport_comp_extDerivCLM_subset _))
  rw [← hA, augmentation_eq A hχA, hA, Function.comp_apply, ← map_zero T]
  refine map_eq_map_of_eventuallyEq T ?_
  -- Near the support `χ • c` is the constant form `c`, whose exterior derivative vanishes.
  filter_upwards [hχ.eventually_nhdsSet] with y hy
  have hc : (TestFunction.postcompCLM (toSpanSingleton ℝ c) χ : E → E [⋀^Fin k]→L[ℝ] F) =ᶠ[𝓝 y]
      fun _ ↦ c := hy.mono fun z hz ↦ by simp [hz]
  rw [TestFunction.extDerivCLM_apply, hc.extDeriv_eq]
  simp

end Boundary

end Distribution
