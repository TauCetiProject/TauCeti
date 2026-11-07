/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HolomorphicFunctions.Bergman.Restriction
public import TauCeti.Analysis.Normed.Operator.Compact.Pi

/-!
# Square-integrable holomorphic Čech cocycles

For a finite family of planar open sets and complete values, the products of Bergman spaces on
its pairwise and triple intersections are Banach spaces with the finite-product norm.
The Čech maps in degrees zero and one are continuous: each restriction is a contraction.
The space of square-integrable holomorphic one-cocycles is closed and complete.
Repetitions of indices are allowed, as in the full Čech complex; the differential has the convention
`(δc)ᵢⱼₖ = cⱼₖ - cᵢₖ + cᵢⱼ` after restriction to the triple intersection.

Shrinking each open set relatively compactly gives a compact map on one-cochains and on the
closed cocycle spaces. These provide analytic Banach stages for Čech arguments; they do not
assert that coboundaries are closed or that sheaf cohomology is finite-dimensional. No covering
hypothesis is needed for these constructions.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §§12 and 14.
-/

public noncomputable section

open TopologicalSpace Set

namespace TauCeti.BergmanSpace.Cech

variable {ι F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {U V W : ι → Opens ℂ}

/-- The continuous degree-zero Čech differential for Bergman sections. -/
def coboundary (U : ι → Opens ℂ) :
    ((i : ι) → bergmanSpace F (U i)) →L[ℂ]
      ((i j : ι) → bergmanSpace F (U i ⊓ U j)) :=
  ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.pi fun j ↦
    (restrict inf_le_right).comp (ContinuousLinearMap.proj j) -
      (restrict inf_le_left).comp (ContinuousLinearMap.proj i)

@[simp]
theorem coboundary_apply (c : (i : ι) → bergmanSpace F (U i)) (i j : ι) :
    coboundary U c i j = restrict inf_le_right (c j) - restrict inf_le_left (c i) := (rfl)

/-- The holomorphic representative of a coboundary is the difference of representatives. -/
theorem representative_coboundary (c : (i : ι) → bergmanSpace F (U i))
    {i j : ι} {x : ℂ} (hx : x ∈ U i ⊓ U j) :
    representative (coboundary U c i j) x = representative (c j) x - representative (c i) x := by
  simp only [coboundary_apply, representative_sub _ _ hx, representative_restrict _ _ hx]

/-- The continuous degree-one Čech differential for Bergman sections. -/
def differential (U : ι → Opens ℂ) :
    ((i j : ι) → bergmanSpace F (U i ⊓ U j)) →L[ℂ]
      ((i j k : ι) → bergmanSpace F ((U i ⊓ U j) ⊓ U k)) :=
  ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.pi fun j ↦
    ContinuousLinearMap.pi fun k ↦
      (restrict (le_inf (inf_le_left.trans inf_le_right) inf_le_right)).comp
        ((ContinuousLinearMap.proj (φ := fun k ↦ bergmanSpace F (U j ⊓ U k)) k).comp
          (ContinuousLinearMap.proj (φ := fun j ↦ (k : ι) → bergmanSpace F (U j ⊓ U k)) j)) -
      (restrict (le_inf (inf_le_left.trans inf_le_left) inf_le_right)).comp
        ((ContinuousLinearMap.proj (φ := fun k ↦ bergmanSpace F (U i ⊓ U k)) k).comp
          (ContinuousLinearMap.proj (φ := fun i ↦ (k : ι) → bergmanSpace F (U i ⊓ U k)) i)) +
      (restrict inf_le_left).comp
        ((ContinuousLinearMap.proj (φ := fun j ↦ bergmanSpace F (U i ⊓ U j)) j).comp
          (ContinuousLinearMap.proj (φ := fun i ↦ (j : ι) → bergmanSpace F (U i ⊓ U j)) i))

@[simp]
theorem differential_apply (c : (i j : ι) → bergmanSpace F (U i ⊓ U j)) (i j k : ι) :
    differential U c i j k =
      restrict (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (c j k) -
      restrict (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (c i k) +
      restrict inf_le_left (c i j) := (rfl)

/-- The holomorphic representative of the differential is the alternating sum on the triple
intersection. -/
theorem representative_differential (c : (i j : ι) → bergmanSpace F (U i ⊓ U j))
    {i j k : ι} {x : ℂ} (hx : x ∈ (U i ⊓ U j) ⊓ U k) :
    representative (differential U c i j k) x =
      representative (c j k) x - representative (c i k) x + representative (c i j) x := by
  simp only [differential_apply, representative_add _ _ hx, representative_sub _ _ hx,
    representative_restrict _ _ hx]

/-- A Čech coboundary is a cocycle, with the actual Bergman restriction maps. -/
@[simp]
theorem differential_coboundary (c : (i : ι) → bergmanSpace F (U i)) :
    differential U (coboundary U c) = 0 := by
  funext i j k
  apply BergmanSpace.ext
  intro x hx
  have hxjk : x ∈ U j ⊓ U k := ⟨hx.1.2, hx.2⟩
  have hxik : x ∈ U i ⊓ U k := ⟨hx.1.1, hx.2⟩
  simp only [representative_differential _ hx, representative_coboundary _ hxjk,
    representative_coboundary _ hxik, representative_coboundary _ hx.1,
    Pi.zero_apply, representative_zero hx]
  abel

/-- The closed subspace of square-integrable holomorphic Čech one-cocycles. -/
def cocycles (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F] (U : ι → Opens ℂ) :
    Submodule ℂ ((i j : ι) → bergmanSpace F (U i ⊓ U j)) :=
  (differential (F := F) U).ker

/-- The cocycle condition is the vanishing of the alternating sum on every triple overlap. -/
@[simp]
theorem mem_cocycles_iff {c : (i j : ι) → bergmanSpace F (U i ⊓ U j)} :
    c ∈ cocycles F U ↔ ∀ i j k, differential U c i j k = 0 := by
  rw [cocycles, LinearMap.mem_ker]
  exact ⟨fun h i j k ↦ congrFun (congrFun (congrFun h i) j) k,
    fun h ↦ funext fun i ↦ funext fun j ↦ funext fun k ↦ h i j k⟩

/-- Bergman cocycles are exactly the cochains whose holomorphic representatives satisfy the
usual pointwise Čech cocycle identity. -/
theorem mem_cocycles_iff_representative {c : (i j : ι) → bergmanSpace F (U i ⊓ U j)} :
    c ∈ cocycles F U ↔ ∀ i j k, ∀ x ∈ (U i ⊓ U j) ⊓ U k,
      representative (c j k) x - representative (c i k) x + representative (c i j) x = 0 := by
  rw [mem_cocycles_iff]
  constructor
  · intro h i j k x hx
    have heq := congrArg (fun u ↦ representative u x) (h i j k)
    simpa only [representative_differential _ hx, representative_zero hx] using heq
  · intro h i j k
    apply BergmanSpace.ext
    intro x hx
    simpa only [representative_differential _ hx, representative_zero hx] using h i j k x hx

/-- The Bergman cocycle space is closed in the product of the overlap Bergman spaces. -/
theorem isClosed_cocycles :
    IsClosed (cocycles F U : Set ((i j : ι) → bergmanSpace F (U i ⊓ U j))) :=
  (differential U).isClosed_ker

instance [CompleteSpace F] : CompleteSpace (cocycles F U) :=
  isClosed_cocycles.completeSpace_coe

/-- Coboundaries define elements of the closed cocycle space. -/
def coboundaryToCocycles (U : ι → Opens ℂ) :
    ((i : ι) → bergmanSpace F (U i)) →L[ℂ] cocycles F U :=
  (coboundary U).codRestrict _ fun c ↦
    (mem_cocycles_iff.2 fun i j k ↦ congrFun (congrFun (congrFun
      (differential_coboundary c) i) j) k)

@[simp]
theorem coe_coboundaryToCocycles (c : (i : ι) → bergmanSpace F (U i)) :
    (coboundaryToCocycles U c : (i j : ι) → bergmanSpace F (U i ⊓ U j)) =
      coboundary U c := (rfl)

/-- Componentwise restriction of Bergman one-cochains to a smaller family of open sets. -/
def restrictOne (h : ∀ i, V i ≤ U i) :
    ((i j : ι) → bergmanSpace F (U i ⊓ U j)) →L[ℂ]
      ((i j : ι) → bergmanSpace F (V i ⊓ V j)) :=
  ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.pi fun j ↦
    (restrict (inf_le_inf (h i) (h j))).comp
      ((ContinuousLinearMap.proj (φ := fun j ↦ bergmanSpace F (U i ⊓ U j)) j).comp
        (ContinuousLinearMap.proj (φ := fun i ↦ (j : ι) → bergmanSpace F (U i ⊓ U j)) i))

@[simp]
theorem restrictOne_apply (h : ∀ i, V i ≤ U i)
    (c : (i j : ι) → bergmanSpace F (U i ⊓ U j)) (i j : ι) :
    restrictOne h c i j = restrict (inf_le_inf (h i) (h j)) (c i j) := (rfl)

/-- Restriction to the same family is the identity on one-cochains. -/
@[simp]
theorem restrictOne_refl :
    restrictOne (F := F) (fun i ↦ le_refl (U i)) = ContinuousLinearMap.id ℂ _ := by
  ext c i j
  simp only [restrictOne_apply, restrict_refl, ContinuousLinearMap.id_apply]

/-- Successive restrictions of one-cochains agree with direct restriction. -/
theorem restrictOne_comp (hVU : ∀ i, V i ≤ U i) (hWV : ∀ i, W i ≤ V i) :
    (restrictOne (F := F) hWV).comp (restrictOne hVU) =
      restrictOne (fun i ↦ (hWV i).trans (hVU i)) := by
  apply ContinuousLinearMap.ext
  intro c
  funext i j
  exact congrArg (fun T ↦ T (c i j))
    (restrict_comp_restrict (inf_le_inf (hVU i) (hVU j)) (inf_le_inf (hWV i) (hWV j)))

/-- For finite families, restriction decreases the actual product `L²` norm. -/
theorem norm_restrictOne_apply_le [Fintype ι] (h : ∀ i, V i ≤ U i)
    (c : (i j : ι) → bergmanSpace F (U i ⊓ U j)) : ‖restrictOne h c‖ ≤ ‖c‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg c)).2
  intro i
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg c)).2
  intro j
  exact (norm_restrict_apply_le _ (c i j)).trans
    ((norm_le_pi_norm (c i) j).trans (norm_le_pi_norm c i))

/-- Restricting a cocycle gives a cocycle. -/
theorem restrictOne_mem_cocycles (h : ∀ i, V i ≤ U i) {c}
    (hc : c ∈ cocycles F U) : restrictOne h c ∈ cocycles F V := by
  rw [mem_cocycles_iff_representative] at hc ⊢
  intro i j k x hx
  have hxjk : x ∈ V j ⊓ V k := ⟨hx.1.2, hx.2⟩
  have hxik : x ∈ V i ⊓ V k := ⟨hx.1.1, hx.2⟩
  simpa only [restrictOne_apply, representative_restrict _ _ hxjk,
    representative_restrict _ _ hxik, representative_restrict _ _ hx.1] using
    hc i j k x ⟨⟨h i hx.1.1, h j hx.1.2⟩, h k hx.2⟩

/-- Componentwise restriction commutes with taking coboundaries. -/
theorem restrictOne_coboundary (h : ∀ i, V i ≤ U i)
    (c : (i : ι) → bergmanSpace F (U i)) :
    restrictOne h (coboundary U c) = coboundary V (fun i ↦ restrict (h i) (c i)) := by
  funext i j
  apply BergmanSpace.ext
  intro x hx
  have hxU : x ∈ U i ⊓ U j := ⟨h i hx.1, h j hx.2⟩
  simp only [restrictOne_apply, representative_restrict _ _ hx,
    representative_coboundary _ hxU, representative_coboundary _ hx,
    representative_restrict _ _ hx.1, representative_restrict _ _ hx.2]

/-- Restriction between the closed spaces of Bergman one-cocycles. -/
def restrictCocycles (h : ∀ i, V i ≤ U i) : cocycles F U →L[ℂ] cocycles F V :=
  ((restrictOne h).comp (cocycles F U).subtypeL).codRestrict _ fun c ↦
    restrictOne_mem_cocycles h c.property

@[simp]
theorem coe_restrictCocycles (h : ∀ i, V i ≤ U i) (c : cocycles F U) :
    (restrictCocycles h c : (i j : ι) → bergmanSpace F (V i ⊓ V j)) =
      restrictOne h c.val := (rfl)

/-- Restricting to the same family is the identity. -/
@[simp]
theorem restrictCocycles_refl :
    restrictCocycles (F := F) (fun i ↦ le_refl (U i)) = ContinuousLinearMap.id ℂ _ := by
  ext c i j
  simp only [coe_restrictCocycles, restrictOne_apply, restrict_refl,
    ContinuousLinearMap.id_apply]

/-- Successive restrictions of cocycles equal direct restriction. -/
theorem restrictCocycles_comp (hVU : ∀ i, V i ≤ U i) (hWV : ∀ i, W i ≤ V i) :
    (restrictCocycles (F := F) hWV).comp (restrictCocycles hVU) =
      restrictCocycles (fun i ↦ (hWV i).trans (hVU i)) := by
  apply ContinuousLinearMap.ext
  intro c
  apply Subtype.ext
  exact congrArg (fun T ↦ T c.val) (restrictOne_comp hVU hWV)

/-- The cocycle bonding map is a contraction for finite families. -/
theorem norm_restrictCocycles_apply_le [Fintype ι] (h : ∀ i, V i ≤ U i)
    (c : cocycles F U) : ‖restrictCocycles h c‖ ≤ ‖c‖ :=
  norm_restrictOne_apply_le h c.val

variable [Finite ι] [ProperSpace F]

/-- Relatively compact componentwise shrinking gives a compact restriction of one-cochains. -/
theorem isCompactOperator_restrictOne (hV : ∀ i, IsCompact (closure (V i : Set ℂ)))
    (hVU : ∀ i, closure (V i : Set ℂ) ⊆ U i) :
    IsCompactOperator (restrictOne (F := F) (fun i ↦ subset_closure.trans (hVU i))) := by
  apply IsCompactOperator.pi
  intro i
  apply IsCompactOperator.pi
  intro j
  have hK : IsCompact (closure ((V i ⊓ V j : Opens ℂ) : Set ℂ)) :=
    (hV i).of_isClosed_subset isClosed_closure
      (closure_mono (show (V i ⊓ V j : Opens ℂ) ≤ V i from inf_le_left))
  have hKU : closure ((V i ⊓ V j : Opens ℂ) : Set ℂ) ⊆ U i ⊓ U j :=
    fun x hx ↦ ⟨hVU i (closure_mono inf_le_left hx),
      hVU j (closure_mono inf_le_right hx)⟩
  let P : ((i j : ι) → bergmanSpace F (U i ⊓ U j)) →L[ℂ]
      bergmanSpace F (U i ⊓ U j) :=
    (ContinuousLinearMap.proj (φ := fun j ↦ bergmanSpace F (U i ⊓ U j)) j).comp
      (ContinuousLinearMap.proj (φ := fun i ↦ (j : ι) → bergmanSpace F (U i ⊓ U j)) i)
  exact (BergmanSpace.isCompactOperator_restrict (F := F) hK hKU).comp_clm P

/-- Relatively compact shrinking gives a compact operator on the closed Bergman cocycle
spaces. This compactness assertion does not assume that the coboundary range is closed. -/
theorem isCompactOperator_restrictCocycles (hV : ∀ i, IsCompact (closure (V i : Set ℂ)))
    (hVU : ∀ i, closure (V i : Set ℂ) ⊆ U i) :
    IsCompactOperator (restrictCocycles (F := F) (fun i ↦ subset_closure.trans (hVU i))) :=
  ((isCompactOperator_restrictOne hV hVU).comp_clm (cocycles F U).subtypeL).codRestrict
    (fun c ↦ restrictOne_mem_cocycles _ c.property) isClosed_cocycles

end TauCeti.BergmanSpace.Cech
