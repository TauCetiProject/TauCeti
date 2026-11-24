/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import TauCeti.Geometry.Symplectic.CompatibleMetric
public import TauCeti.Geometry.Symplectic.Lagrangian.Basic
import TauCeti.Geometry.Symplectic.Lagrangian.Constructions

/-!
# Metric orthogonal complements in symplectic vector spaces

When a real inner product space `V` carries a symplectic form `ω` and an almost complex structure
`J` whose associated bilinear form `ω(·, J ·)` is the inner product `⟪·, ·⟫`, the metric orthogonal
complement `Wᗮ` of any subspace `W` is the `J`-image of its symplectic orthogonal complement `W^ω`,
and equivalently `W^ω = (J W)ᗮ`. Consequently, in any dimension:

* if `W` is isotropic, then `J W ≤ Wᗮ` and `Wᗮ` is coisotropic (`Wᗮ` is coisotropic iff `W` is
  isotropic);
* if `W` is coisotropic, then `Wᗮ ≤ J W` and `Wᗮ` is isotropic (an equivalence when `W` admits an
  orthogonal projection);
* `W` is Lagrangian if and only if `Wᗮ = J W`, in which case `Wᗮ` is again Lagrangian (an
  equivalence when `W` admits an orthogonal projection).

For an orthogonal almost complex structure `J` with symplectic form `ω = ⟪J ·, ·⟫`
(`TauCeti.AlmostComplexStructure.symplecticForm`), these specialize directly to
`orthogonal_symplecticForm` and `isLagrangian_symplecticForm_iff_orthogonal_eq`.

## Main declarations

* `TauCeti.SymplecticForm.submodule_orthogonal_eq_map_orthogonal` and
  `TauCeti.SymplecticForm.submodule_orthogonal_map_eq_orthogonal`: `Wᗮ = J(W^ω)` and
  `(J W)ᗮ = W^ω`.
* `TauCeti.SymplecticForm.isLagrangian_iff_submodule_orthogonal_eq_map`: `W` is Lagrangian if and
  only if `Wᗮ = J W`, in any dimension.
* `TauCeti.SymplecticForm.IsCoisotropic.isIsotropic_submodule_orthogonal`,
  `TauCeti.SymplecticForm.IsIsotropic.isCoisotropic_submodule_orthogonal`, and
  `TauCeti.SymplecticForm.IsLagrangian.isLagrangian_submodule_orthogonal`: duality of isotropic,
  coisotropic, and Lagrangian subspaces under metric orthogonal complementation, with
  `isCoisotropic_submodule_orthogonal_iff` unconditional and `isIsotropic_submodule_orthogonal_iff`
  and `isLagrangian_submodule_orthogonal_iff` under `[W.HasOrthogonalProjection]`.
* `TauCeti.AlmostComplexStructure.orthogonal_symplecticForm` and
  `TauCeti.AlmostComplexStructure.isLagrangian_symplecticForm_iff_orthogonal_eq`: specializations to
  `ω = ⟪J ·, ·⟫` for an orthogonal almost complex structure `J`.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 2, 9, and 12.
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Sections 2.1, 2.3, and 2.5.
-/

public section

namespace TauCeti

namespace SymplecticForm

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V}

/-- When the inner product is `ω(·, J ·)`, a vector lies in the metric orthogonal complement `Wᗮ`
if and only if its `J`-image lies in the symplectic orthogonal complement `W^ω`. -/
theorem mem_submodule_orthogonal_iff_apply_mem_orthogonal
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {W : Submodule ℝ V} {v : V} :
    v ∈ Wᗮ ↔ J v ∈ ω.orthogonal W := by
  rw [Submodule.mem_orthogonal, mem_orthogonal_iff]
  exact forall₂_congr fun u _ ↦ by rw [hg]

/-- When the inner product is `ω(·, J ·)`, the metric orthogonal complement `Wᗮ` is the preimage
under `J` of the symplectic orthogonal complement `W^ω`. -/
theorem submodule_orthogonal_eq_comap_orthogonal
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (W : Submodule ℝ V) :
    Wᗮ = (ω.orthogonal W).comap J.toLinearMap := by
  ext v
  exact ω.mem_submodule_orthogonal_iff_apply_mem_orthogonal hg

/-- When the inner product is `ω(·, J ·)`, the metric orthogonal complement `Wᗮ` is the `J`-image
of the symplectic orthogonal complement `W^ω`. -/
theorem submodule_orthogonal_eq_map_orthogonal
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (W : Submodule ℝ V) :
    Wᗮ = (ω.orthogonal W).map J.toLinearMap := by
  ext v
  rw [ω.mem_submodule_orthogonal_iff_apply_mem_orthogonal hg, Submodule.mem_map]
  constructor
  · intro hv
    refine ⟨-J v, neg_mem hv, ?_⟩
    simp
  · rintro ⟨w, hw, rfl⟩
    simpa using neg_mem hw

/-- When the inner product is `ω(·, J ·)`, the metric orthogonal complement of `J W` is the
symplectic orthogonal complement `W^ω`. -/
theorem submodule_orthogonal_map_eq_orthogonal
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (W : Submodule ℝ V) :
    (W.map J.toLinearMap)ᗮ = ω.orthogonal W := by
  ext v
  rw [ω.mem_submodule_orthogonal_iff_apply_mem_orthogonal hg,
    ← (ω.invariant_of_apply_apply_eq_inner hg).map_orthogonal W, Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, hwv⟩
    exact J.linearEquiv.injective hwv ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

/-- If `W` is isotropic and the inner product is `ω(·, J ·)`, then `J W ≤ Wᗮ`. -/
theorem IsIsotropic.map_le_submodule_orthogonal {W : Submodule ℝ V} (hW : ω.IsIsotropic W)
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) : W.map J.toLinearMap ≤ Wᗮ := by
  rw [ω.submodule_orthogonal_eq_map_orthogonal hg]
  exact Submodule.map_mono (isIsotropic_iff_le.1 hW)

/-- If `W` is coisotropic and the inner product is `ω(·, J ·)`, then `Wᗮ ≤ J W`. -/
theorem IsCoisotropic.submodule_orthogonal_le_map {W : Submodule ℝ V} (hW : ω.IsCoisotropic W)
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) : Wᗮ ≤ W.map J.toLinearMap := by
  rw [ω.submodule_orthogonal_eq_map_orthogonal hg]
  exact Submodule.map_mono (isCoisotropic_iff_le.1 hW)

/-- When the inner product is `ω(·, J ·)`, a subspace `W` is Lagrangian if and only if its metric
orthogonal complement `Wᗮ` equals `J W`, in any dimension. -/
theorem isLagrangian_iff_submodule_orthogonal_eq_map
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {W : Submodule ℝ V} :
    ω.IsLagrangian W ↔ Wᗮ = W.map J.toLinearMap := by
  rw [isLagrangian_iff, isIsotropic_iff_le, isCoisotropic_iff_le, and_comm, ← le_antisymm_iff,
    ω.submodule_orthogonal_eq_map_orthogonal hg]
  exact (Submodule.map_injective_of_injective J.linearEquiv.injective).eq_iff.symm

/-- For a Lagrangian subspace `L` and an inner product satisfying `ω(·, J ·) = ⟪·, ·⟫`, the metric
orthogonal complement `Lᗮ` is `J L`. -/
theorem IsLagrangian.submodule_orthogonal_eq_map {L : Submodule ℝ V} (hL : ω.IsLagrangian L)
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) : Lᗮ = L.map J.toLinearMap :=
  (ω.isLagrangian_iff_submodule_orthogonal_eq_map hg).1 hL

/-- For an inner product satisfying `ω(·, J ·) = ⟪·, ·⟫`, the metric orthogonal complement of a
coisotropic subspace is isotropic, in any dimension. -/
theorem IsCoisotropic.isIsotropic_submodule_orthogonal {W : Submodule ℝ V} (hW : ω.IsCoisotropic W)
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) : ω.IsIsotropic Wᗮ := by
  rw [ω.submodule_orthogonal_eq_map_orthogonal hg,
    (ω.invariant_of_apply_apply_eq_inner hg).isIsotropic_map_iff]
  exact hW.isIsotropic_orthogonal

/-- For an inner product satisfying `ω(·, J ·) = ⟪·, ·⟫`, the metric orthogonal complement of an
isotropic subspace is coisotropic, in any dimension. -/
theorem IsIsotropic.isCoisotropic_submodule_orthogonal {W : Submodule ℝ V} (hW : ω.IsIsotropic W)
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) : ω.IsCoisotropic Wᗮ := by
  refine isCoisotropic_iff_le.2 ?_
  calc
    ω.orthogonal Wᗮ ≤ ω.orthogonal (W.map J.toLinearMap) :=
      ω.orthogonal_le (hW.map_le_submodule_orthogonal hg)
    _ = (ω.orthogonal W).map J.toLinearMap :=
      ((ω.invariant_of_apply_apply_eq_inner hg).map_orthogonal W).symm
    _ = Wᗮ := (ω.submodule_orthogonal_eq_map_orthogonal hg W).symm

/-- For an inner product satisfying `ω(·, J ·) = ⟪·, ·⟫`, the metric orthogonal complement of a
Lagrangian subspace is again Lagrangian, in any dimension. -/
theorem IsLagrangian.isLagrangian_submodule_orthogonal {L : Submodule ℝ V} (hL : ω.IsLagrangian L)
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) : ω.IsLagrangian Lᗮ :=
  isLagrangian_iff.2
    ⟨hL.isCoisotropic.isIsotropic_submodule_orthogonal hg,
      hL.isIsotropic.isCoisotropic_submodule_orthogonal hg⟩

/-- When `W` admits an orthogonal projection and `ω(·, J ·) = ⟪·, ·⟫`, `Wᗮ` is isotropic if and
only if `W` is coisotropic. -/
theorem isIsotropic_submodule_orthogonal_iff {W : Submodule ℝ V} [W.HasOrthogonalProjection]
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) : ω.IsIsotropic Wᗮ ↔ ω.IsCoisotropic W :=
  ⟨fun h ↦ W.orthogonal_orthogonal ▸ h.isCoisotropic_submodule_orthogonal hg,
    fun h ↦ h.isIsotropic_submodule_orthogonal hg⟩

/-- When `ω(·, J ·) = ⟪·, ·⟫`, `Wᗮ` is coisotropic if and only if `W` is isotropic, in any
dimension and without assuming `W` admits an orthogonal projection. -/
theorem isCoisotropic_submodule_orthogonal_iff {W : Submodule ℝ V}
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) : ω.IsCoisotropic Wᗮ ↔ ω.IsIsotropic W :=
  ⟨fun h ↦ isIsotropic_iff_le.2 (W.le_orthogonal_orthogonal.trans
      ((isIsotropic_iff_le.1 (h.isIsotropic_submodule_orthogonal hg)).trans
        (ω.orthogonal_le W.le_orthogonal_orthogonal))),
    fun h ↦ h.isCoisotropic_submodule_orthogonal hg⟩

/-- When `W` admits an orthogonal projection and `ω(·, J ·) = ⟪·, ·⟫`, `Wᗮ` is Lagrangian if and
only if `W` is Lagrangian. -/
theorem isLagrangian_submodule_orthogonal_iff {W : Submodule ℝ V} [W.HasOrthogonalProjection]
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) : ω.IsLagrangian Wᗮ ↔ ω.IsLagrangian W := by
  rw [isLagrangian_iff, isLagrangian_iff, ω.isIsotropic_submodule_orthogonal_iff hg,
    ω.isCoisotropic_submodule_orthogonal_iff hg, and_comm]

end SymplecticForm

namespace AlmostComplexStructure

open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {J : AlmostComplexStructure V} (hJ : ∀ v w, ⟪J v, J w⟫_ℝ = ⟪v, w⟫_ℝ)
include hJ

/-- For an orthogonal complex structure `J`, the symplectic complement of a subspace `W` for
`ω = ⟪J ·, ·⟫` is the orthogonal complement of its image `J W`. -/
theorem orthogonal_symplecticForm (W : Submodule ℝ V) :
    (J.symplecticForm hJ).orthogonal W = (W.map J.toLinearMap)ᗮ :=
  ((J.symplecticForm hJ).submodule_orthogonal_map_eq_orthogonal
    (J.symplecticForm_associatedBilinForm_apply hJ) W).symm

/-- For an orthogonal complex structure `J`, a subspace `W` is Lagrangian for `ω = ⟪J ·, ·⟫`
exactly when its orthogonal complement is its image `J W`, in any dimension. -/
theorem isLagrangian_symplecticForm_iff_orthogonal_eq {W : Submodule ℝ V} :
    (J.symplecticForm hJ).IsLagrangian W ↔ Wᗮ = W.map J.toLinearMap :=
  (J.symplecticForm hJ).isLagrangian_iff_submodule_orthogonal_eq_map
    (J.symplecticForm_associatedBilinForm_apply hJ)

end AlmostComplexStructure

end TauCeti
