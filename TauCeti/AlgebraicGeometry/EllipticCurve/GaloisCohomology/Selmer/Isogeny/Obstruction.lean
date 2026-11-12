/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Isogeny.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Separability
import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.KummerComparison

/-!
# The obstruction to lifting a dual-isogeny Selmer class

Let `φ : E₁ → E₂` have degree `n` invertible in the base field, and fix a family of
localisations. The comparison `Sel_φ → Sel_n(E₁) → Sel_φ̂` need not be surjective at the
right. Its cokernel is

`Sha(E₂)[φ̂] / φ(Sha(E₁)[n])`.

This file constructs the obstruction map to that quotient and proves exactness and
surjectivity. In particular a dual-isogeny Selmer class lifts precisely when its Sha class
is the image of an `n`-torsion Sha class. No finiteness or nondegeneracy of a pairing on
Sha is assumed. This isolates the Sha term in comparisons of isogeny Selmer orders.

## Main results

* `TauCeti.Isogeny.exact_selmerGroupTorsionToDual_selmerDualShaMap`: the comparison sequence
  continues exactly to the Sha quotient.
* `TauCeti.Isogeny.selmerDualShaMap_surjective`: the obstruction map is onto.
* `TauCeti.Isogeny.selmerTorsionToDualCokernelEquiv`: the resulting cokernel identification.

## References

* E. F. Schaefer and M. Stoll, *How to do a p-descent on an elliptic curve*,
  Trans. Amer. Math. Soc. 356 (2004), 1209–1231, §2.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.4.
-/

public section

noncomputable section

namespace TauCeti.Isogeny

open WeierstrassCurve TauCeti.ContCohomology Hom

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K}
  [W₁.IsElliptic] [W₂.IsElliptic]
  {ι : Type*} {L : ι → Type*} [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
  (φ : Isogeny W₁.toAffine W₂.toAffine)
  (τ : ∀ i, SeparableClosure K →ₐ[K] SeparableClosure (L i))

/-- The isogeny sends degree-torsion in `Sha(E₁)` into the dual-isogeny kernel in `Sha(E₂)`. -/
def shaTorsionToDualKer :
    AddSubgroup.torsionBy (W₁.shafarevichTateGroup τ) φ.degree →+
      φ.dual.shafarevichTateGroupKer τ :=
  (((ofIsogeny φ).shafarevichTateMap τ).comp
    (AddSubgroup.torsionBy (W₁.shafarevichTateGroup τ) φ.degree).subtype).codRestrict _ fun c ↦ by
      rw [shafarevichTateGroupKer_eq_ker_shafarevichTateMap, AddMonoidHom.mem_ker,
        AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, ← dual_ofIsogeny,
        dual_shafarevichTateMap_shafarevichTateMap, degree_ofIsogeny]
      exact AddSubgroup.torsionBy.nsmul_iff.mp c.2

/-- On Sha classes, `shaTorsionToDualKer` is the map induced by the isogeny. -/
@[simp]
theorem coe_shaTorsionToDualKer
    (c : AddSubgroup.torsionBy (W₁.shafarevichTateGroup τ) φ.degree) :
    (φ.shaTorsionToDualKer τ c : W₂.shafarevichTateGroup τ) =
      (ofIsogeny φ).shafarevichTateMap τ c :=
  (rfl)

/-- Passing from a degree-Selmer class to its dual-isogeny Selmer class commutes with the
maps to Sha. -/
@[simp]
theorem selmerShaMap_selmerGroupTorsionToDual (c : W₁.selmerGroup τ φ.degree) :
    φ.dual.selmerShaMap τ (φ.selmerGroupTorsionToDual τ c) =
      φ.shaTorsionToDualKer τ (W₁.selmerShaMap τ φ.degree c) := by
  ext
  simp only [coe_selmerShaMap, coe_selmerGroupTorsionToDual, coe_shaTorsionToDualKer,
    coe_shafarevichTateMap, pointH1Map_def, WeierstrassCurve.coe_selmerShaMap,
    explicitCoeff1_kerCoeffIncl_torsionCoeffToDualKerCoeff]

/-- The obstruction to lifting a dual-isogeny Selmer class to a degree-Selmer class:
its image in `Sha(E₂)[φ̂] / φ(Sha(E₁)[deg φ])`. -/
def selmerDualShaMap : φ.dual.selmerGroup τ →+
    (φ.dual.shafarevichTateGroupKer τ ⧸ (φ.shaTorsionToDualKer τ).range) :=
  (QuotientAddGroup.mk' (φ.shaTorsionToDualKer τ).range).comp (φ.dual.selmerShaMap τ)

/-- The obstruction is the quotient class of the image in Sha. -/
@[simp]
theorem selmerDualShaMap_apply (c : φ.dual.selmerGroup τ) :
    φ.selmerDualShaMap τ c = QuotientAddGroup.mk (φ.dual.selmerShaMap τ c) :=
  (rfl)

/-- For a separable dual isogeny, the obstruction map onto the Sha quotient is surjective. -/
theorem selmerDualShaMap_surjective
    [Algebra.IsSeparable φ.dual.fieldPullback.fieldRange W₂.toAffine.FunctionField] :
    Function.Surjective (φ.selmerDualShaMap τ) :=
  (QuotientAddGroup.mk'_surjective _).comp (φ.dual.selmerShaMap_surjective τ)

section InvertibleDegree

variable (hn : IsUnit (φ.degree : K))

/-- The map to the dual-isogeny Selmer group sends the multiplication Kummer class of a
rational point to its dual-isogeny Kummer class. -/
theorem selmerGroupTorsionToDual_kummerSelmerMap [DecidableEq K] (P : W₁.toAffine.Point) :
    letI := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).1
    φ.selmerGroupTorsionToDual τ (W₁.kummerSelmerMap τ hn (QuotientAddGroup.mk P)) =
      φ.dual.kummerSelmerMap τ (QuotientAddGroup.mk P) := by
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).1
  apply Subtype.ext
  simp only [coe_selmerGroupTorsionToDual, WeierstrassCurve.coe_kummerSelmerMap,
    WeierstrassCurve.kummerClassMap_mk, coe_kummerSelmerMap, kummerClassMap_mk]
  exact φ.explicitCoeff1_torsionCoeffToDualKerCoeff_kummerMap hn P

include hn in
private theorem mem_range_selmerGroupTorsionToDual_of_selmerShaMap_eq_zero
    (c : φ.dual.selmerGroup τ) (hc : φ.dual.selmerShaMap τ c = 0) :
    c ∈ (φ.selmerGroupTorsionToDual τ).range := by
  classical
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).1
  obtain ⟨x, hx⟩ := (φ.dual.exact_kummerSelmerMap_selmerShaMap τ c).mp hc
  obtain ⟨P, hP⟩ :=
    QuotientAddGroup.mk'_surjective (ofIsogeny φ.dual).pointMapHom.range x
  refine ⟨W₁.kummerSelmerMap τ hn (QuotientAddGroup.mk P), ?_⟩
  rw [φ.selmerGroupTorsionToDual_kummerSelmerMap τ hn, ← QuotientAddGroup.mk'_apply, hP, hx]

include hn in
/-- The sequence `Sel_n(E₁) → Sel_φ̂ → Sha(E₂)[φ̂] / φ(Sha(E₁)[n])` is exact,
where `n = deg φ` is invertible in the base field. -/
theorem exact_selmerGroupTorsionToDual_selmerDualShaMap :
    Function.Exact (φ.selmerGroupTorsionToDual τ) (φ.selmerDualShaMap τ) := by
  have hcomm : (φ.dual.selmerShaMap τ).comp (φ.selmerGroupTorsionToDual τ) =
      (φ.shaTorsionToDualKer τ).comp (W₁.selmerShaMap τ φ.degree) := by
    apply AddMonoidHom.ext
    intro c
    exact φ.selmerShaMap_selmerGroupTorsionToDual τ c
  have hrange : (φ.selmerGroupTorsionToDual τ).range.map (φ.dual.selmerShaMap τ) =
      (φ.shaTorsionToDualKer τ).range := by
    rw [← AddMonoidHom.range_comp, hcomm, AddMonoidHom.range_comp,
      AddMonoidHom.range_eq_top.mpr (W₁.selmerShaMap_surjective τ hn), AddSubgroup.map_top]
  apply AddMonoidHom.exact_iff.mpr
  rw [selmerDualShaMap, ← AddMonoidHom.comap_ker, QuotientAddGroup.ker_mk', ← hrange]
  apply AddSubgroup.comap_map_eq_self
  intro c hc
  exact φ.mem_range_selmerGroupTorsionToDual_of_selmerShaMap_eq_zero τ hn c hc

/-- The cokernel of `Sel_n(E₁) → Sel_φ̂` is the Sha quotient
`Sha(E₂)[φ̂] / φ(Sha(E₁)[n])`, for `n = deg φ` invertible in the base field. -/
def selmerTorsionToDualCokernelEquiv :
    (φ.dual.selmerGroup τ ⧸ (φ.selmerGroupTorsionToDual τ).range) ≃+
      (φ.dual.shafarevichTateGroupKer τ ⧸ (φ.shaTorsionToDualKer τ).range) := by
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).1
  exact (QuotientAddGroup.quotientAddEquivOfEq
    (AddMonoidHom.exact_iff.mp
      (φ.exact_selmerGroupTorsionToDual_selmerDualShaMap τ hn)).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (φ.selmerDualShaMap_surjective τ))

/-- The cokernel equivalence sends a Selmer class to the quotient of its Sha class. -/
@[simp]
theorem selmerTorsionToDualCokernelEquiv_mk (c : φ.dual.selmerGroup τ) :
    φ.selmerTorsionToDualCokernelEquiv τ hn (QuotientAddGroup.mk c) =
      QuotientAddGroup.mk (φ.dual.selmerShaMap τ c) := by
  simp [selmerTorsionToDualCokernelEquiv]

end InvertibleDegree

end TauCeti.Isogeny
