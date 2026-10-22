/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Isometry.OrthogonalExtension
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Transvection
public import TauCeti.LinearAlgebra.IntegralLattice.Restriction
public import TauCeti.NumberTheory.IntegralLattice.Binary.NormOne
import TauCeti.GroupTheory.Index.Basic

/-!
# Isometry groups of indefinite lattices are infinite

A nondegenerate indefinite integral lattice `L` of rank at least three has infinitely many
isometries, in contrast with the finiteness of `O(L)` for definite lattices. The proof splits
according to whether the rational norm form of `L` is isotropic. The isotropic case, in which the
Eichler transvections already form an infinite group, is
`TauCeti.IntegralLattice.infinite_isometry_of_not_anisotropic`. This file treats the anisotropic
case and assembles the two.

Suppose the rational norm form is anisotropic and indefinite; no rank or nondegeneracy hypothesis
is needed. Choose lattice vectors `x` and `y` of positive and negative norm. They span a binary
sublattice `M` whose rational norm form is indefinite and anisotropic, so its primitive
discriminant is positive and not a square, and `O(M)` is infinite by Pell's equation. Its rational
form is nondegenerate, so every isometry of `M` extends to a rational isometry of `L` acting as the
identity on the orthogonal complement of `ℚ x + ℚ y`
(`LinearMap.BilinForm.Isometry.isometryGroupExtend`). Such an extension need not preserve `L`, but
a nonzero integer `d` carries the orthogonal projection of `L` into `M`, and then every isometry of
`M` acting trivially on `M / d M` extends to an isometry of `L`. These isometries form a subgroup
of finite index in the infinite group `O(M)`, and distinct ones have distinct extensions.

In rank two an indefinite lattice with isotropic norm form, such as the hyperbolic plane, can have
a finite isometry group, so the rank hypothesis of the combined statement cannot be dropped.

## Main results

* `TauCeti.IntegralLattice.infinite_isometry_of_isIndefinite_of_anisotropic`: an indefinite lattice
  with anisotropic rational norm form has infinite `O(L)`, and
  `TauCeti.IntegralLattice.infinite_specialOrthogonalGroup_of_isIndefinite_of_anisotropic`
  infinite `SO(L)`.
* `TauCeti.IntegralLattice.infinite_isometry_of_isIndefinite` and
  `TauCeti.IntegralLattice.infinite_specialOrthogonalGroup_of_isIndefinite`: a nondegenerate
  indefinite lattice of rank at least three has infinite `O(L)` and `SO(L)`.

## References

* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 13.
* M. Eichler, *Quadratische Formen und orthogonale Gruppen*, Springer (1952).
-/

public section

open Module LinearMap.BilinForm TauCeti.BilinForm
open scoped Pointwise TensorProduct

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

/-! ## A binary sublattice of an indefinite lattice -/

/-- Two lattice vectors of opposite signs span an indefinite binary sublattice. -/
private theorem restrict_span_pair {L : IntegralLattice V} {x y : L} (hx : 0 < L.form x x)
    (hy : L.form y y < 0) :
    (L.restrict (Submodule.span ℤ (Set.range ![x, y]))).IsIndefinite ∧
      finrank ℚ (ℚ ⊗[ℤ] Submodule.span ℤ (Set.range ![x, y])) = 2 := by
  set S := Submodule.span ℤ (Set.range ![x, y])
  have hmem (z : L) (hz : z ∈ Set.range ![x, y]) :
      L.restrictMap S (1 ⊗ₜ ⟨z, Submodule.subset_span hz⟩) = z := by
    rw [restrictMap_tmul, one_smul]
  have hind : (L.restrict S).IsIndefinite := by
    refine (L.restrict S).isIndefinite_iff_exists_pos_and_exists_neg.mpr
      ⟨⟨1 ⊗ₜ ⟨x, Submodule.subset_span ⟨0, rfl⟩⟩, ?_⟩,
        ⟨1 ⊗ₜ ⟨y, Submodule.subset_span ⟨1, rfl⟩⟩, ?_⟩⟩
    · rwa [← form_restrictMap, hmem x ⟨0, rfl⟩]
    · rwa [← form_restrictMap, hmem y ⟨1, rfl⟩]
  refine ⟨hind, le_antisymm ?_ ?_⟩
  · rw [← (L.restrict S).finrank_carrier, ← (L.restrictCarrierEquiv S).finrank_eq]
    exact (finrank_range_le_card (R := ℤ) ![x, y]).trans (by simp)
  · have := (L.restrict S).signature_sum_eq_finrank
    obtain ⟨h₁, h₂⟩ := (L.restrict S).isIndefinite_iff_not_semidef.mp hind
    rw [isPosSemidef_iff_sigNeg_eq_zero] at h₁
    rw [isNegSemidef_iff_sigPos_eq_zero] at h₂
    omega

/-! ## Extending isometries of the binary sublattice -/

/-- **The extension preserves the lattice.** Let `M` be the restriction of `L` to a submodule `S`
with nondegenerate rational form, and let `d ≠ 0` carry the orthogonal projection of `L` into the
carrier of `M`. Then the extension of an isometry of `M` acting trivially on `M / d M` maps `L`
into itself. -/
private theorem isometryGroupExtend_mem_carrier {L : IntegralLattice V} {S : Submodule ℤ L}
    (hS : (L.restrict S).form.Nondegenerate) {d : ℤ} (hd : d ≠ 0)
    (hdπ : ∀ x ∈ L.carrier,
      d • (L.restrictIsometry S).orthogonalProjection hS x ∈ (L.restrict S).carrier)
    {g : Isometry (L.restrict S) (L.restrict S)}
    (hg : g ∈ Isometry.congruenceSubgroup (L.restrict S) d) {x : V} (hx : x ∈ L.carrier) :
    ((L.restrictIsometry S).isometryGroupExtend L.isSymm hS (Isometry.toIsometryGroup _ g) :
      V ≃ₗ[ℚ] V) x ∈ L.carrier := by
  set p := (L.restrictIsometry S).orthogonalProjection hS x
  rw [LinearMap.BilinForm.Isometry.isometryGroupExtend_apply, Isometry.toIsometryGroup_apply]
  obtain ⟨y, hy⟩ := Isometry.mem_congruenceSubgroup_iff.mp hg ⟨d • p, hdπ x hx⟩
  -- Dividing the congruence by `d`, the displacement `g p - p` is the lattice vector `y`.
  have hgp : g p - p = (y : ℚ ⊗[ℤ] S) := by
    have hy' := congrArg (fun z : (L.restrict S) ↦ (z : ℚ ⊗[ℤ] S)) hy
    simp only [Submodule.coe_sub, Isometry.coe_carrierEquiv_apply, Submodule.coe_smul_of_tower,
      ← Int.cast_smul_eq_zsmul ℚ, map_smul, ← smul_sub] at hy'
    exact smul_right_injective _ (Int.cast_ne_zero.mpr hd) hy'
  have hy'' := Submodule.mem_map_of_mem (f := (L.restrictMap S).restrictScalars ℤ) y.2
  rw [map_restrictMap_restrict_carrier] at hy''
  obtain ⟨z, -, hz⟩ := hy''
  rw [restrictIsometry_apply, hgp]
  exact L.carrier.add_mem hx (hz ▸ z.2)

/-! ## The anisotropic case -/

/-- **The anisotropic case of the infiniteness of `O(L)`.** An indefinite integral lattice whose
rational norm form is anisotropic has infinitely many isometries. No rank or nondegeneracy
hypothesis is needed: anisotropy forces nondegeneracy, and in rank two this is the Pell case. -/
theorem infinite_isometry_of_isIndefinite_of_anisotropic {L : IntegralLattice V}
    (hL : L.IsIndefinite) (haniso : L.norm.Anisotropic) : Infinite (Isometry L L) := by
  obtain ⟨x, y, hx, hy⟩ := hL.exists_carrier_pos_and_neg
  set S := Submodule.span ℤ (Set.range ![x, y])
  set M := L.restrict S
  obtain ⟨hMind, hV⟩ := restrict_span_pair hx hy
  have hManiso := anisotropic_restrict haniso S
  have hS := (isNondegenerate_of_anisotropic hManiso).nondegenerate
  have : Infinite (Isometry M M) := infinite_isometry_of_binaryDiscriminant_pos_of_not_isSquare hV
    (M.binaryDiscriminant_pos_of_isIndefinite hV hMind)
    (M.not_isSquare_binaryDiscriminant_of_anisotropic hV hManiso)
  set ι := L.restrictIsometry S
  -- A single nonzero integer `d` carries the orthogonal projection of `L` into `M`.
  obtain ⟨d, hd, hdπ⟩ := Submodule.IsLattice.exists_ne_zero_forall_smul_mem ℚ M.carrier
    ((Module.Finite.fg_top (M := L)).map ((ι.orthogonalProjection hS).restrictScalars ℤ ∘ₗ
      L.carrier.subtype))
  -- The isometries of `M` acting trivially on `M / d M` form an infinite group.
  let Γ := Isometry.congruenceSubgroup M d
  have := Isometry.finiteIndex_congruenceSubgroup M hd
  have : Infinite Γ := Γ.infinite_of_finiteIndex
  -- Their extensions are distinct isometries of `L`.
  let φ := (ι.isometryGroupExtend L.isSymm hS).comp ((Isometry.toIsometryGroup M).comp Γ.subtype)
  have hφ : Function.Injective φ := (ι.isometryGroupExtend_injective L.isSymm hS).comp
    ((Isometry.toIsometryGroup_injective M).comp Subtype.val_injective)
  have hrange : φ.range ≤ (Isometry.toIsometryGroup L).range := by
    refine Isometry.le_range_toIsometryGroup ?_
    rintro _ ⟨g, rfl⟩ z hz
    exact isometryGroupExtend_mem_carrier hS hd
      (fun w hw ↦ hdπ _ ⟨⟨w, hw⟩, Submodule.mem_top, rfl⟩) g.2 hz
  have : Infinite (Isometry.toIsometryGroup L).range :=
    Infinite.of_injective (fun g ↦ ⟨φ g, hrange ⟨g, rfl⟩⟩) fun g h hgh ↦
      hφ (congrArg Subtype.val hgh)
  exact Infinite.of_surjective _ (Isometry.toIsometryGroup L).rangeRestrict_surjective

/-- **The anisotropic case of the infiniteness of `SO(L)`.** An indefinite integral lattice whose
rational norm form is anisotropic has infinitely many proper isometries. -/
theorem infinite_specialOrthogonalGroup_of_isIndefinite_of_anisotropic {L : IntegralLattice V}
    (hL : L.IsIndefinite) (haniso : L.norm.Anisotropic) : Infinite (specialOrthogonalGroup L) := by
  have := infinite_isometry_of_isIndefinite_of_anisotropic hL haniso
  exact (specialOrthogonalGroup L).infinite_of_finiteIndex

/-! ## Indefinite lattices of rank at least three -/

/-- **Indefinite lattices have infinite isometry groups.** A nondegenerate indefinite integral
lattice of rank at least three has infinitely many isometries. -/
theorem infinite_isometry_of_isIndefinite {L : IntegralLattice V} [L.IsNondegenerate]
    (hrank : 3 ≤ finrank ℤ L) (hL : L.IsIndefinite) : Infinite (Isometry L L) := by
  by_cases haniso : L.norm.Anisotropic
  · exact infinite_isometry_of_isIndefinite_of_anisotropic hL haniso
  · exact infinite_isometry_of_not_anisotropic hrank haniso

/-- **Indefinite lattices have infinite special isometry groups.** A nondegenerate indefinite
integral lattice of rank at least three has infinitely many proper isometries. -/
theorem infinite_specialOrthogonalGroup_of_isIndefinite {L : IntegralLattice V}
    [L.IsNondegenerate] (hrank : 3 ≤ finrank ℤ L) (hL : L.IsIndefinite) :
    Infinite (specialOrthogonalGroup L) := by
  by_cases haniso : L.norm.Anisotropic
  · exact infinite_specialOrthogonalGroup_of_isIndefinite_of_anisotropic hL haniso
  · exact infinite_specialOrthogonalGroup_of_not_anisotropic hrank haniso

end TauCeti.IntegralLattice
