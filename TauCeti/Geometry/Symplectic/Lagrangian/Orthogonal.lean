/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import TauCeti.Geometry.Symplectic.CompatibleMetric
public import TauCeti.Geometry.Symplectic.Lagrangian.Constructions

/-!
# Metric orthogonal complements in symplectic vector spaces

Let `(V, ω)` be a real symplectic vector space. When `J` is an `ω`-invariant almost complex
structure, `J` acts on `V` as a linear symplectomorphism, so `J` commutes with the symplectic
orthogonal complement `W^ω` and preserves isotropic, coisotropic, Lagrangian, and symplectic
subspaces.

When `V` also carries a real inner product identified with the bilinear form `ω(·, J ·)`, the
metric orthogonal complement `Wᗮ` of any subspace `W` is the `J`-image of its symplectic
orthogonal complement:

`Wᗮ = J(W^ω)`.

Consequently:

* if `W` is isotropic, then `J(W) ≤ Wᗮ` and `Wᗮ` is coisotropic;
* if `W` is coisotropic, then `Wᗮ ≤ J(W)` and `Wᗮ` is isotropic;
* if `L` is Lagrangian, then `Lᗮ = J(L)` and `Lᗮ` is again Lagrangian.

None of these implications uses finite dimension; when `W` admits an orthogonal projection, so
that `Wᗮᗮ = W`, the isotropic, coisotropic, and Lagrangian characterizations of `Wᗮ` become
equivalences. Together with the cross-pairing identity `IsIsotropic.apply_add` for sums of vectors
from two isotropic subspaces, this gives the linear step of Weinstein's Lagrangian neighborhood
theorem: the Riemannian normal space `Lᗮ` of a Lagrangian tangent space `L` for a compatible
metric is itself isotropic, so `ω(u₁ + n₁, u₂ + n₂) = ω(u₁, n₂) - ω(u₂, n₁)`.

## Main results

* `TauCeti.SymplecticForm.IsCoisotropic.isIsotropic_orthogonal`: the symplectic complement of a
  coisotropic subspace is isotropic.
* `TauCeti.SymplecticForm.IsCoisotropic.finite` and `TauCeti.SymplecticForm.IsLagrangian.finite`: a
  symplectic vector space admitting a finite-dimensional coisotropic (or Lagrangian) subspace is
  itself finite-dimensional.
* `TauCeti.SymplecticForm.IsIsotropic.apply_add`: on sums of vectors from two isotropic subspaces,
  `ω` reduces to the cross-pairings `ω(u₁ + n₁, u₂ + n₂) = ω(u₁, n₂) - ω(u₂, n₁)`.
* `TauCeti.SymplecticForm.Invariant.isSymplectomorphism` and `Invariant.map_orthogonal`: an
  `ω`-invariant almost complex structure is a linear symplectomorphism and commutes with `W^ω`.
* `TauCeti.SymplecticForm.submodule_orthogonal_eq_map_orthogonal`: for an inner product satisfying
  `ω(v, J w) = ⟪v, w⟫`, `Wᗮ = (ω.orthogonal W).map J.toLinearMap`.
* `TauCeti.SymplecticForm.IsCoisotropic.isIsotropic_submodule_orthogonal`,
  `TauCeti.SymplecticForm.IsIsotropic.isCoisotropic_submodule_orthogonal`, and
  `TauCeti.SymplecticForm.IsLagrangian.isLagrangian_submodule_orthogonal`: duality of isotropic,
  coisotropic, and Lagrangian subspaces under metric orthogonal complementation, with
  `isCoisotropic_submodule_orthogonal_iff` unconditional and `isIsotropic_submodule_orthogonal_iff`
  and `isLagrangian_submodule_orthogonal_iff` under `[W.HasOrthogonalProjection]`.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 2, 9, and 12.
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  University Press, 2017, Sections 2.1 and 2.5.
-/

public section

namespace TauCeti.SymplecticForm

section Algebraic

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V}

/-- The symplectic orthogonal complement of a coisotropic subspace is isotropic. -/
theorem IsCoisotropic.isIsotropic_orthogonal {W : Submodule ℝ V} (hW : ω.IsCoisotropic W) :
    ω.IsIsotropic (ω.orthogonal W) :=
  isIsotropic_iff_le.2 (ω.orthogonal_le (isCoisotropic_iff_le.1 hW))

/-- A symplectic vector space containing a finite-dimensional coisotropic subspace `W` is itself
finite-dimensional: `W^ω ≤ W` is finite-dimensional and `V ⧸ W^ω` embeds into `W →ₗ[ℝ] ℝ`. -/
theorem IsCoisotropic.finite {W : Submodule ℝ V} (hW : ω.IsCoisotropic W)
    [Module.Finite ℝ W] : Module.Finite ℝ V := by
  let φ : V →ₗ[ℝ] (W →ₗ[ℝ] ℝ) :=
    { toFun v := ω.toBilinForm.flip v ∘ₗ W.subtype
      map_add' u v := by ext w; simp
      map_smul' c v := by ext w; simp }
  have hker : LinearMap.ker φ = ω.orthogonal W := by
    ext v
    simp [φ, LinearMap.ext_iff, mem_orthogonal_iff]
  have : Module.Finite ℝ (V ⧸ LinearMap.ker φ) :=
    Module.Finite.equiv φ.quotKerEquivRange.symm
  rw [hker] at this
  have : Module.Finite ℝ (ω.orthogonal W) :=
    Module.Finite.of_injective (Submodule.inclusion (isCoisotropic_iff_le.1 hW))
      (Submodule.inclusion_injective _)
  exact Module.Finite.of_submodule_quotient (ω.orthogonal W)

/-- A symplectic vector space containing a finite-dimensional Lagrangian subspace is itself
finite-dimensional. -/
theorem IsLagrangian.finite {L : Submodule ℝ V} (hL : ω.IsLagrangian L)
    [Module.Finite ℝ L] : Module.Finite ℝ V :=
  hL.isCoisotropic.finite

/-- Evaluating a symplectic form on sums of vectors from two isotropic subspaces leaves only the
skew-symmetric cross-pairing `ω(u₁, n₂) - ω(u₂, n₁)`. -/
theorem IsIsotropic.apply_add {S T : Submodule ℝ V} (hS : ω.IsIsotropic S) (hT : ω.IsIsotropic T)
    {u₁ u₂ n₁ n₂ : V} (hu₁ : u₁ ∈ S) (hu₂ : u₂ ∈ S) (hn₁ : n₁ ∈ T) (hn₂ : n₂ ∈ T) :
    ω (u₁ + n₁) (u₂ + n₂) = ω u₁ n₂ - ω u₂ n₁ := by
  have hu : ω u₁ u₂ = 0 := isIsotropic_iff.1 hS u₁ hu₁ u₂ hu₂
  have hn : ω n₁ n₂ = 0 := isIsotropic_iff.1 hT n₁ hn₁ n₂ hn₂
  have hswap : -ω n₁ u₂ = ω u₂ n₁ := ω.neg_eq n₁ u₂
  have hexp : ω (u₁ + n₁) (u₂ + n₂) = ω u₁ u₂ + ω n₁ u₂ + (ω u₁ n₂ + ω n₁ n₂) := by
    simp only [map_add, LinearMap.add_apply]
  linarith

/-- An `ω`-invariant almost complex structure is a linear symplectomorphism of `(V, ω)`. -/
theorem Invariant.isSymplectomorphism (hJ : ω.Invariant J) :
    ω.IsSymplectomorphism ω J.linearEquiv :=
  isSymplectomorphism_iff.2 hJ.apply

/-- An `ω`-invariant almost complex structure commutes with symplectic orthogonal complements. -/
theorem Invariant.map_orthogonal (hJ : ω.Invariant J) (W : Submodule ℝ V) :
    (ω.orthogonal W).map J.toLinearMap = ω.orthogonal (W.map J.toLinearMap) :=
  hJ.isSymplectomorphism.map_orthogonal W

/-- An `ω`-invariant almost complex structure preserves and reflects isotropic subspaces. -/
@[simp]
theorem Invariant.isIsotropic_map_iff (hJ : ω.Invariant J) {W : Submodule ℝ V} :
    ω.IsIsotropic (W.map J.toLinearMap) ↔ ω.IsIsotropic W := by
  have ht : ω.transport J.linearEquiv = ω :=
    isSymplectomorphism_iff_transport_eq.1 hJ.isSymplectomorphism
  have h := isIsotropic_map_transport_iff (ω := ω) (L := W) (e := J.linearEquiv)
  rwa [ht] at h

/-- An `ω`-invariant almost complex structure preserves and reflects coisotropic subspaces. -/
@[simp]
theorem Invariant.isCoisotropic_map_iff (hJ : ω.Invariant J) {W : Submodule ℝ V} :
    ω.IsCoisotropic (W.map J.toLinearMap) ↔ ω.IsCoisotropic W := by
  have ht : ω.transport J.linearEquiv = ω :=
    isSymplectomorphism_iff_transport_eq.1 hJ.isSymplectomorphism
  have h := isCoisotropic_map_transport_iff (ω := ω) (L := W) (e := J.linearEquiv)
  rwa [ht] at h

/-- An `ω`-invariant almost complex structure preserves and reflects Lagrangian subspaces. -/
@[simp]
theorem Invariant.isLagrangian_map_iff (hJ : ω.Invariant J) {W : Submodule ℝ V} :
    ω.IsLagrangian (W.map J.toLinearMap) ↔ ω.IsLagrangian W := by
  rw [isLagrangian_iff, isLagrangian_iff, hJ.isIsotropic_map_iff, hJ.isCoisotropic_map_iff]

/-- An `ω`-invariant almost complex structure preserves and reflects symplectic subspaces. -/
@[simp]
theorem Invariant.isSymplectic_map_iff (hJ : ω.Invariant J) {W : Submodule ℝ V} :
    ω.IsSymplectic (W.map J.toLinearMap) ↔ ω.IsSymplectic W := by
  have ht : ω.transport J.linearEquiv = ω :=
    isSymplectomorphism_iff_transport_eq.1 hJ.isSymplectomorphism
  have h := isSymplectic_map_transport_iff (ω := ω) (L := W) (e := J.linearEquiv)
  rwa [ht] at h

end Algebraic

section InnerProductSpace

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

/-- When the inner product is `ω(·, J ·)`, the metric orthogonal complement of `J(W)` is the
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

/-- If `W` is isotropic and the inner product is `ω(·, J ·)`, then `J(W) ≤ Wᗮ`. -/
theorem IsIsotropic.map_le_submodule_orthogonal {W : Submodule ℝ V} (hW : ω.IsIsotropic W)
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) : W.map J.toLinearMap ≤ Wᗮ := by
  rw [ω.submodule_orthogonal_eq_map_orthogonal hg]
  exact Submodule.map_mono (isIsotropic_iff_le.1 hW)

/-- If `W` is coisotropic and the inner product is `ω(·, J ·)`, then `Wᗮ ≤ J(W)`. -/
theorem IsCoisotropic.submodule_orthogonal_le_map {W : Submodule ℝ V} (hW : ω.IsCoisotropic W)
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) : Wᗮ ≤ W.map J.toLinearMap := by
  rw [ω.submodule_orthogonal_eq_map_orthogonal hg]
  exact Submodule.map_mono (isCoisotropic_iff_le.1 hW)

/-- For a Lagrangian subspace `L` and an inner product satisfying `ω(·, J ·) = ⟪·, ·⟫`, the metric
orthogonal complement `Lᗮ` is `J(L)`. -/
theorem IsLagrangian.submodule_orthogonal_eq_map {L : Submodule ℝ V} (hL : ω.IsLagrangian L)
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) : Lᗮ = L.map J.toLinearMap := by
  have heq : ω.orthogonal L = L :=
    le_antisymm (isCoisotropic_iff_le.1 hL.isCoisotropic) (isIsotropic_iff_le.1 hL.isIsotropic)
  rw [ω.submodule_orthogonal_eq_map_orthogonal hg, heq]

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

end InnerProductSpace

end TauCeti.SymplecticForm
