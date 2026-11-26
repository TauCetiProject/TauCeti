/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.AdditionTheorem
public import Mathlib.GroupTheory.Index

/-!
# Scalar maps between period lattices

Let `L` and `L'` be period pairs with lattices `Λ` and `Λ'`, and let `α ∈ ℂ` with `α Λ ⊆ Λ'`.
Multiplication by `α` induces a group homomorphism `ℂ / Λ → ℂ / Λ'`. Through the complex
uniformizations `ℂ / Λ ≃+ E_Λ(ℂ)` (`PeriodPair.weierstrassPointEquiv`), induced by the point maps
with `P(z) = (℘(z), ℘'(z) / 2)` for `z ∉ Λ` and `P(z) = 0` for `z ∈ Λ`, this is a group
homomorphism between the points of the two Weierstrass curves,

  `PeriodPair.scalarPointHom α h : E_Λ(ℂ) →+ E_Λ'(ℂ)`,   `P_Λ(z) ↦ P_Λ'(α z)`.

For `α ≠ 0` these are the analytic isogenies of the complex uniformization. This file proves the
basic dictionary between them and the lattices:

* the identity and composition laws: `α = 1` gives the identity and `β ∘ α` is `β α`;
* integer scalars give the multiplication-by-`n` maps of the group law;
* the kernel of the map of `α ≠ 0` is the image of `α⁻¹ Λ'`, and its cardinality (the degree) is
  the index `[Λ' : α Λ]`, which is finite and nonzero;
* the **dual**: for `α ≠ 0`, if `n = [Λ' : α Λ]` then `(n / α) Λ' ⊆ Λ`, and the two composites
  of the maps of `α` and of `n / α` are multiplication by `n`.

## Main definitions

* `PeriodPair.scalarPointHom`: the homomorphism `E_Λ(ℂ) →+ E_Λ'(ℂ)` induced by `z ↦ α z`.

## Main results

* `PeriodPair.scalarPointHom_weierstrassPoint`: `P_Λ(z) ↦ P_Λ'(α z)`.
* `PeriodPair.scalarPointHom_one`, `PeriodPair.scalarPointHom_comp`,
  `PeriodPair.scalarPointHom_scalarPointHom`: functoriality.
* `PeriodPair.scalarPointHom_intCast`: the map of `n : ℤ` is multiplication by `n`.
* `PeriodPair.weierstrassPoint_mem_ker_scalarPointHom_iff`: `P_Λ(z)` lies in the kernel iff
  `α z ∈ Λ'`.
* `PeriodPair.scalarPointHom_surjective`: the map of `α ≠ 0` is surjective.
* `PeriodPair.natCard_ker_scalarPointHom`: its kernel has `[Λ' : α Λ]` elements; this index is
  computed as a determinant, and shown finite, by `PeriodPair.relIndex_lattice_smul_eq_natAbs` and
  `PeriodPair.relIndex_lattice_smul_ne_zero`.
* `PeriodPair.scalarPointHom_dual_comp`, `PeriodPair.scalarPointHom_comp_dual`: the dual map.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in Mathematics
  106, Springer, 2009, §VI.4.
-/

public noncomputable section

namespace PeriodPair

variable {L L' L'' : PeriodPair}

/-! ### The homomorphism induced by a scalar -/

/-- The homomorphism `E_Λ(ℂ) →+ E_Λ'(ℂ)` induced by multiplication by `α` on `ℂ`, for `α Λ ⊆ Λ'`:
it sends `P_Λ(z)` to `P_Λ'(α z)` (`PeriodPair.scalarPointHom_weierstrassPoint`). -/
def scalarPointHom (α : ℂ) (h : ∀ z ∈ L.lattice, α * z ∈ L'.lattice) :
    L.weierstrassCurve.toAffine.Point →+ L'.weierstrassCurve.toAffine.Point :=
  (L'.weierstrassPointEquiv.toAddMonoidHom.comp
    (QuotientAddGroup.map _ _ (AddMonoidHom.mulLeft α) fun z hz ↦ by simpa using h z hz)).comp
      L.weierstrassPointEquiv.symm.toAddMonoidHom

/-- The characteristic property of the scalar map: `P_Λ(z) ↦ P_Λ'(α z)`. -/
@[simp]
lemma scalarPointHom_weierstrassPoint (α : ℂ) (h : ∀ z ∈ L.lattice, α * z ∈ L'.lattice) (z : ℂ) :
    scalarPointHom α h (L.weierstrassPoint z) = L'.weierstrassPoint (α * z) := by
  simp [scalarPointHom, weierstrassPointEquiv_symm_weierstrassPoint, weierstrassPointEquiv_mk]

/-- The scalar `1` induces the identity. -/
@[simp]
lemma scalarPointHom_one :
    scalarPointHom (L := L) (L' := L) 1 (fun z hz ↦ by simpa using hz) = AddMonoidHom.id _ :=
  L.pointHom_ext fun z ↦ by simp

/-- **Functoriality.** The composite of the maps induced by `α` and by `β` is the map induced by
`β α`. -/
lemma scalarPointHom_comp {α β : ℂ} (hα : ∀ z ∈ L.lattice, α * z ∈ L'.lattice)
    (hβ : ∀ z ∈ L'.lattice, β * z ∈ L''.lattice) :
    (scalarPointHom β hβ).comp (scalarPointHom α hα) =
      scalarPointHom (β * α) (fun z hz ↦ by simpa [mul_assoc] using hβ _ (hα z hz)) :=
  L.pointHom_ext fun z ↦ by simp [mul_assoc]

/-- **Functoriality, pointwise.** Applying the maps induced by `α` and then by `β` is applying the
map induced by `β α`. -/
@[simp]
lemma scalarPointHom_scalarPointHom {α β : ℂ} (hα : ∀ z ∈ L.lattice, α * z ∈ L'.lattice)
    (hβ : ∀ z ∈ L'.lattice, β * z ∈ L''.lattice) (P : L.weierstrassCurve.toAffine.Point) :
    scalarPointHom β hβ (scalarPointHom α hα P) =
      scalarPointHom (β * α) (fun z hz ↦ by simpa [mul_assoc] using hβ _ (hα z hz)) P :=
  DFunLike.congr_fun (scalarPointHom_comp hα hβ) P

/-- The scalar `n : ℤ` induces multiplication by `n` in the group of points. -/
lemma scalarPointHom_intCast (n : ℤ) (P : L.weierstrassCurve.toAffine.Point) :
    scalarPointHom (n : ℂ) (fun _ hz ↦ L.intCast_mul_mem_lattice n hz) P = n • P := by
  obtain ⟨z, rfl⟩ := L.weierstrassPoint_surjective P
  rw [scalarPointHom_weierstrassPoint, zsmul_weierstrassPoint]

/-! ### Kernel and degree -/

/-- `P_Λ(z)` is in the kernel of the map induced by `α` exactly when `α z ∈ Λ'`. -/
lemma weierstrassPoint_mem_ker_scalarPointHom_iff {α : ℂ}
    (h : ∀ z ∈ L.lattice, α * z ∈ L'.lattice) (z : ℂ) :
    L.weierstrassPoint z ∈ (scalarPointHom α h).ker ↔ α * z ∈ L'.lattice := by
  rw [AddMonoidHom.mem_ker, scalarPointHom_weierstrassPoint, weierstrassPoint_eq_zero_iff]

/-- The map induced by a nonzero scalar is surjective. -/
lemma scalarPointHom_surjective {α : ℂ} (hα : α ≠ 0) (h : ∀ z ∈ L.lattice, α * z ∈ L'.lattice) :
    Function.Surjective (scalarPointHom α h) := by
  intro P
  obtain ⟨w, rfl⟩ := L'.weierstrassPoint_surjective P
  exact ⟨L.weierstrassPoint (α⁻¹ * w), by simp [mul_inv_cancel_left₀ hα]⟩

/-- The homomorphism `Λ' →+ E_Λ(ℂ)`, `l' ↦ P_Λ(α⁻¹ l')`. For `α ≠ 0` its kernel is `α Λ ∩ Λ'`,
and if moreover `α Λ ⊆ Λ'` then its range is the kernel of the map induced by `α`. -/
private def kerParam (α : ℂ) : L'.lattice.toAddSubgroup →+ L.weierstrassCurve.toAffine.Point :=
  (L.weierstrassPointHom.comp (AddMonoidHom.mulLeft α⁻¹)).comp
    L'.lattice.toAddSubgroup.subtype

/-- The value of `kerParam` on `l'` is `P_Λ(α⁻¹ l')`. -/
private lemma kerParam_apply (α : ℂ) (l : L'.lattice.toAddSubgroup) :
    kerParam (L := L) α l = L.weierstrassPoint (α⁻¹ * l) := by
  simp [kerParam]

/-- The range of `kerParam` is the kernel of the map induced by `α ≠ 0`. -/
private lemma range_kerParam {α : ℂ} (hα : α ≠ 0) (h : ∀ z ∈ L.lattice, α * z ∈ L'.lattice) :
    (kerParam (L := L) (L' := L') α).range = (scalarPointHom α h).ker := by
  ext P
  obtain ⟨z, rfl⟩ := L.weierstrassPoint_surjective P
  rw [AddMonoidHom.mem_range, weierstrassPoint_mem_ker_scalarPointHom_iff]
  constructor
  · rintro ⟨l, hl⟩
    rw [kerParam_apply] at hl
    have hmem : α * (α⁻¹ * l) ∈ L'.lattice := by
      rw [mul_inv_cancel_left₀ hα]
      exact l.property
    have hsub : α * (α⁻¹ * l) - α * z ∈ L'.lattice := by
      rw [← mul_sub]
      exact h _ (L.weierstrassPoint_eq_weierstrassPoint_iff.mp hl)
    simpa using L'.lattice.sub_mem hmem hsub
  · intro hz
    exact ⟨⟨α * z, hz⟩, by simp [kerParam_apply, inv_mul_cancel_left₀ hα]⟩

/-- The kernel of `kerParam` is `c Λ ∩ Λ'`, as a subgroup of `Λ'`. -/
private lemma ker_kerParam (c : ℂˣ) :
    (kerParam (L := L) (L' := L') (c : ℂ)).ker =
      (c • L).lattice.toAddSubgroup.addSubgroupOf L'.lattice.toAddSubgroup := by
  ext l
  rw [AddMonoidHom.mem_ker, kerParam_apply, weierstrassPoint_eq_zero_iff,
    AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup]
  conv_rhs => rw [← mul_inv_cancel_left₀ c.ne_zero (l : ℂ)]
  rw [mul_mem_lattice_smul_iff]

/-- **The degree is the index.** For `c ≠ 0` with `c Λ ⊆ Λ'`, the kernel of the map induced by `c`
has `[Λ' : c Λ]` elements. -/
theorem natCard_ker_scalarPointHom (c : ℂˣ) (h : ∀ z ∈ L.lattice, (c : ℂ) * z ∈ L'.lattice) :
    Nat.card (scalarPointHom (c : ℂ) h).ker =
      (c • L).lattice.toAddSubgroup.relIndex L'.lattice.toAddSubgroup := by
  rw [AddSubgroup.relIndex, ← ker_kerParam, AddSubgroup.index_ker, range_kerParam c.ne_zero h]

/-! ### The dual -/

/-- **The dual, on the source.** With `n = [Λ' : c Λ]`, the map induced by `n / c` after the map
induced by `c` is multiplication by `n` on `E_Λ(ℂ)`. -/
theorem scalarPointHom_dual_comp (c : ℂˣ) (h : ∀ z ∈ L.lattice, (c : ℂ) * z ∈ L'.lattice) :
    (scalarPointHom _ fun _ ↦ relIndex_div_mul_mem_lattice c).comp (scalarPointHom (c : ℂ) h) =
      (c • L).lattice.toAddSubgroup.relIndex L'.lattice.toAddSubgroup •
        AddMonoidHom.id L.weierstrassCurve.toAffine.Point := by
  refine L.pointHom_ext fun z ↦ ?_
  simp [nsmul_weierstrassPoint, ← mul_assoc, div_mul_cancel₀ _ c.ne_zero]

/-- **The dual, on the target.** With `n = [Λ' : c Λ]`, the map induced by `c` after the map
induced by `n / c` is multiplication by `n` on `E_Λ'(ℂ)`. -/
theorem scalarPointHom_comp_dual (c : ℂˣ) (h : ∀ z ∈ L.lattice, (c : ℂ) * z ∈ L'.lattice) :
    (scalarPointHom (c : ℂ) h).comp (scalarPointHom _ fun _ ↦ relIndex_div_mul_mem_lattice c) =
      (c • L).lattice.toAddSubgroup.relIndex L'.lattice.toAddSubgroup •
        AddMonoidHom.id L'.weierstrassCurve.toAffine.Point := by
  refine L'.pointHom_ext fun z ↦ ?_
  simp [nsmul_weierstrassPoint, ← mul_assoc, mul_div_cancel₀ _ c.ne_zero]

end PeriodPair
