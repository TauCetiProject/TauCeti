/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Weyl.Chamber

/-!
# Stabilizer types of the adjoint action and the faces of a closed Weyl chamber

Let `T` be a maximal torus of a compact Lie group `G`, with Lie algebra `𝔱 ⊆ 𝔤` and Weyl group
`W = N(T) / T` acting on `𝔱` (`Subgroup.weylAdjointRepresentation`), and write
`Z_G(X) = {g | Ad_g X = X}` for the adjoint stabilizer of `X ∈ 𝔤`. The *stabilizer type* of `X`
is the conjugacy class of `Z_G(X)`. This file compares the stabilizer types of points of `𝔱`
with the root data, and so with the faces of a closed Weyl chamber.

* **Conjugate stabilizers are Weyl conjugate.** For `X, Y ∈ 𝔱`, the stabilizers `Z_G(X)` and
  `Z_G(Y)` are conjugate in `G` exactly when `Z_G(w X) = Z_G(Y)` for some `w ∈ W`
  (`TauCeti.Lie.IsMaximalTorus.exists_map_conj_stabilizer_eq_iff`). If `g Z_G(X) g⁻¹ = Z_G(Y)`,
  then `T` and `g T g⁻¹` are maximal tori of the closed subgroup `Z_G(Y)`, so some `c ∈ Z_G(Y)`
  conjugates the second to the first; `c g` normalizes `T` and still conjugates `Z_G(X)` to
  `Z_G(Y)`, because `c` normalizes `Z_G(Y)`; this holds for any two closed subgroups containing
  `T` (`TauCeti.Lie.IsMaximalTorus.exists_mem_normalizer_map_conj_eq_of_map_conj_eq`). Neither `G`
  nor the stabilizers need be connected.
* **Stabilizer types and root vanishing patterns.** Decompose `𝔤 = 𝔱 ⊕ E₁ ⊕ ⋯ ⊕ E_r` into
  nonzero root planes with roots `α_i` (`TauCeti.IsRootPlaneDecomposition`). For a compact
  connected group, `Z_G(X)` is determined by the set of roots vanishing at `X`
  (`TauCeti.IsRootPlaneDecomposition.stabilizer_continuousAdjointRepresentation_eq_stabilizer_iff`).
  Hence `Z_G(X)` and `Z_G(Y)` are conjugate exactly when some `w ∈ W` carries the roots vanishing
  at `X` onto those vanishing at `Y`, in the sense that `α_i(w X) = 0 ↔ α_i(Y) = 0` for every `i`
  (`TauCeti.Lie.IsMaximalTorus.exists_map_conj_stabilizer_eq_iff_exists_apply_eq_zero_iff`).
* **Faces of the closed chamber.** On the closed Weyl chamber
  `C = {X ∈ 𝔱 | 0 ≤ α_i(X₀) α_i(X) for every i}` of a regular `X₀`
  (`TauCeti.sameSideChamber`), the vanishing pattern of a point says which walls contain it, so
  it names the open face of `C` through that point. The stabilizer is therefore constant on each
  open face, and distinct open faces have distinct stabilizers; by the previous item, two open
  faces have conjugate stabilizers exactly when their patterns are related by the Weyl group. The
  correspondence is not injective on types: in `SU(3)`, a point on the wall of `α₁` only and one on
  the wall of `α₂` only have conjugate stabilizers. Every stabilizer type of the adjoint action
  occurs on `C`: each `Z_G(Z)`, `Z ∈ 𝔤`, is conjugate to `Z_G(Y)` for a point `Y` of `C`
  (`TauCeti.Lie.IsMaximalTorus.exists_mem_sameSideChamber_map_conj_stabilizer_eq`).
* **The stabilizer comparison of a cross-section.** For a compact connected group and a regular
  `X₀`, an element `g` of `G` carrying a point `Y` of the closed chamber into the chamber fixes
  `Y`, so `g ∈ Z_G(Y)` (`TauCeti.Lie.IsMaximalTorus.mem_stabilizer_of_Ad_apply_eq`), by the
  uniqueness of chamber representatives of adjoint orbits. Every `Y ∈ 𝔱` close enough to a point
  `X` of `𝔱` has `Z_G(Y) ≤ Z_G(X)`, since the roots not vanishing at `X` do not vanish near `X`
  (`TauCeti.IsRootPlaneDecomposition.eventually_stabilizer_continuousAdjointRepresentation_le`).
  Hence for `Y` near `X` every such `g` lies in `Z_G(X)`
  (`TauCeti.Lie.IsMaximalTorus.eventually_mem_stabilizer_of_Ad_apply_eq`). This is the stabilizer
  comparison behind the symplectic cross-section of a Hamiltonian action of a compact connected
  group at a point of the closed chamber.

Connectedness of `G` is used for the vanishing-pattern, face-pattern and cross-section results,
but not for `TauCeti.Lie.IsMaximalTorus.exists_map_conj_stabilizer_eq_iff` or for
`TauCeti.Lie.IsMaximalTorus.exists_mem_sameSideChamber_map_conj_stabilizer_eq`. Without it the
vanishing pattern alone does not determine the stabilizer: for `G = O(2)` and `T = SO(2)` there
are no roots, so every point of `𝔱` has the same vanishing pattern, while the stabilizer of `0` is
`O(2)` and that of a nonzero point is `SO(2)`.

## Main results

* `TauCeti.Lie.IsMaximalTorus.exists_map_conj_stabilizer_eq_iff`: adjoint stabilizers of points of
  `𝔱` are conjugate in `G` exactly when they are conjugate by the Weyl group.
* `TauCeti.Lie.IsMaximalTorus.exists_map_conj_stabilizer_eq_iff_exists_apply_eq_zero_iff`: they are
  conjugate exactly when the Weyl group relates the roots vanishing at the two points.
* `TauCeti.Lie.IsMaximalTorus.exists_mem_sameSideChamber_map_conj_stabilizer_eq`: every adjoint
  stabilizer is conjugate to the stabilizer of a point of a closed chamber.
* `TauCeti.Lie.IsMaximalTorus.mem_stabilizer_of_Ad_apply_eq`,
  `TauCeti.Lie.IsMaximalTorus.eventually_mem_stabilizer_of_Ad_apply_eq`: elements of `G` relating
  two points of the closed chamber stabilize them, and near a point `X` of the chamber they lie
  in `Z_G(X)`.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Graduate Texts in
  Mathematics 98, Springer, 1985, Chapter V, § 2 (Weyl chambers and the Weyl group).
* E. Lerman, E. Meinrenken, S. Tolman and C. Woodward, *Nonabelian convexity by symplectic cuts*,
  Topology 37 (1998), 245–259 (the symplectic cross-section).
-/

public section

noncomputable section

open Module (Dual)
open Filter Topology
open scoped ContDiff Manifold

namespace TauCeti

open Lie

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

namespace Lie

/-! ### Conjugate stabilizers in the Lie algebra of a maximal torus -/

variable [CompactSpace G] {T : Subgroup G} [IsMulCommutative T]

/-- **Conjugate adjoint stabilizers in a torus Lie algebra are Weyl conjugate.** For `X, Y` in the
Lie algebra `𝔱` of a maximal torus `T` of a compact Lie group, the adjoint stabilizers `Z_G(X)` and
`Z_G(Y)` are conjugate in `G` exactly when `Z_G(w X) = Z_G(Y)` for some element `w` of the Weyl
group `N(T) / T`. Neither `G` nor the stabilizers need be connected. -/
theorem IsMaximalTorus.exists_map_conj_stabilizer_eq_iff (hT : IsMaximalTorus T)
    (X Y : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) :
    (∃ g : G,
      ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
          (X : LeftInvariantDerivation I G)).map (MulAut.conj g).toMonoidHom =
        (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
          (Y : LeftInvariantDerivation I G)) ↔
      ∃ w : T.normalizerQuotient,
        (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
            (T.weylAdjointRepresentation (I := I) w X : LeftInvariantDerivation I G) =
          (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
            (Y : LeftInvariantDerivation I G) := by
  refine ⟨fun ⟨g, hg⟩ ↦ ?_, fun ⟨w, hw⟩ ↦ ?_⟩
  · -- Both stabilizers are closed and contain `T`, so they are conjugate by the normalizer.
    obtain ⟨n, hn, hnY⟩ := hT.exists_mem_normalizer_map_conj_eq_of_map_conj_eq I
      (isClosed_stabilizer_continuousAdjointRepresentation _)
      (le_stabilizer_continuousAdjointRepresentation X.property)
      (le_stabilizer_continuousAdjointRepresentation Y.property) hg
    refine ⟨QuotientGroup.mk ⟨n, hn⟩, ?_⟩
    rw [Subgroup.coe_weylAdjointRepresentation_mk_apply,
      stabilizer_continuousAdjointRepresentation_Ad, hnY]
  · obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
    refine ⟨n, ?_⟩
    rw [← hw, Subgroup.coe_weylAdjointRepresentation_mk_apply,
      stabilizer_continuousAdjointRepresentation_Ad]

/-- **Every adjoint stabilizer is conjugate to the stabilizer of a point of a closed chamber.** Let
`T` be a maximal torus of a compact Lie group, `B` a symmetric positive definite invariant form on
`𝔤`, and `α_i` the roots of nonzero root planes of `𝔱`. For every `X₀ ∈ 𝔱` and `Z ∈ 𝔤`, the adjoint
stabilizer `Z_G(Z)` is conjugate to `Z_G(Y)` for some `Y` in the closed chamber of `X₀`. -/
theorem IsMaximalTorus.exists_mem_sameSideChamber_map_conj_stabilizer_eq (hT : IsMaximalTorus T)
    {B : LinearMap.BilinForm ℝ (LeftInvariantDerivation I G)} {ι : Type*}
    {α : ι → Dual ℝ (lieSubalgebraOfSubgroup (I := I) T).toSubmodule}
    {V : ι → Submodule ℝ (LeftInvariantDerivation I G)} {J : (i : ι) → Module.End ℝ (V i)}
    (hBs : B.IsSymm) (hBp : B.toQuadraticMap.PosDef)
    (hB : B.lieInvariant (LeftInvariantDerivation I G))
    (h : ∀ i, IsRootPlane B (lieSubalgebraOfSubgroup (I := I) T).toSubmodule (α i) (V i) (J i))
    (hV : ∀ i, V i ≠ ⊥) (X₀ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule)
    (Z : LeftInvariantDerivation I G) :
    ∃ Y ∈ sameSideChamber α X₀, ∃ g : G,
      ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer Z).map
          (MulAut.conj g).toMonoidHom =
        (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
          (Y : LeftInvariantDerivation I G) := by
  -- Conjugate `Z` into `𝔱`, then into the chamber by the Weyl group.
  obtain ⟨g, hg⟩ := hT.exists_Ad_mem_lieSubalgebraOfSubgroup Z
  obtain ⟨w, hw⟩ := hT.exists_weylAdjointRepresentation_mem_sameSideChamber hBs hBp hB h hV X₀
    ⟨_, hg⟩
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  refine ⟨_, hw, n * g, ?_⟩
  rw [Subgroup.coe_weylAdjointRepresentation_mk_apply, ← LieEquiv.trans_apply, ← Ad_mul,
    stabilizer_continuousAdjointRepresentation_Ad]

section Connected

variable [ConnectedSpace G] {B : LinearMap.BilinForm ℝ (LeftInvariantDerivation I G)}
  {ι : Type*} [Finite ι] {α : ι → Dual ℝ (lieSubalgebraOfSubgroup (I := I) T).toSubmodule}
  {V : ι → Submodule ℝ (LeftInvariantDerivation I G)} {J : (i : ι) → Module.End ℝ (V i)}

/-- **Stabilizer types in a torus Lie algebra are Weyl classes of root vanishing patterns.** Let
`T` be a maximal torus of a compact connected Lie group, `B` a separating invariant form, and
`𝔤 = 𝔱 ⊕ E₁ ⊕ ⋯ ⊕ E_r` a decomposition into nonzero root planes with roots `α_i`. For `X, Y ∈ 𝔱`,
the adjoint stabilizers `Z_G(X)` and `Z_G(Y)` are conjugate in `G` exactly when some element `w`
of the Weyl group makes the same roots vanish at `w X` as at `Y`. On a closed Weyl chamber the
roots vanishing at a point name the open face containing it, so this compares stabilizer types
with faces. -/
theorem IsMaximalTorus.exists_map_conj_stabilizer_eq_iff_exists_apply_eq_zero_iff
    (hT : IsMaximalTorus T) (hB : B.lieInvariant (LeftInvariantDerivation I G))
    (hsep : B.SeparatingLeft)
    (hD : IsRootPlaneDecomposition B (lieSubalgebraOfSubgroup (I := I) T).toSubmodule α V J)
    (hV : ∀ i, V i ≠ ⊥) (X Y : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) :
    (∃ g : G,
      ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
          (X : LeftInvariantDerivation I G)).map (MulAut.conj g).toMonoidHom =
        (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
          (Y : LeftInvariantDerivation I G)) ↔
      ∃ w : T.normalizerQuotient,
        ∀ i, α i (T.weylAdjointRepresentation (I := I) w X) = 0 ↔ α i Y = 0 := by
  simp_rw [hT.exists_map_conj_stabilizer_eq_iff,
    hD.stabilizer_continuousAdjointRepresentation_eq_stabilizer_iff hB hsep hV]

/-! ### The stabilizer comparison on a closed chamber -/

variable (hT : IsMaximalTorus T) (hBs : B.IsSymm) (hBp : B.toQuadraticMap.PosDef)
  (hB : B.lieInvariant (LeftInvariantDerivation I G))
  (hD : IsRootPlaneDecomposition B (lieSubalgebraOfSubgroup (I := I) T).toSubmodule α V J)
  (hV : ∀ i, V i ≠ ⊥)
  {X₀ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule} (hX₀ : ∀ i, α i X₀ ≠ 0)

include hT hBs hBp hB hD hV hX₀

/-- **Elements relating two points of a closed chamber stabilize them.** For a maximal torus of
a compact connected Lie group, a root-plane decomposition with nonzero planes for a symmetric
positive definite invariant form, and a regular `X₀`, if `Ad_g Y = Y'` for points `Y, Y'` of the
closed chamber of `X₀`, then `Y = Y'`, so `g` lies in the adjoint stabilizer of `Y`. -/
theorem IsMaximalTorus.mem_stabilizer_of_Ad_apply_eq
    {Y Y' : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule} (hY : Y ∈ sameSideChamber α X₀)
    (hY' : Y' ∈ sameSideChamber α X₀) {g : G} (hg : Ad (I := I) g Y = Y') :
    g ∈ (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
      (Y : LeftInvariantDerivation I G) := by
  have hYY' : Y = Y' := (hT.existsUnique_mem_sameSideChamber_Ad hBs hBp hB hD hV hX₀
    (Y : LeftInvariantDerivation I G)).unique ⟨hY, 1, by simp⟩ ⟨hY', g, hg⟩
  rw [mem_stabilizer_continuousAdjointRepresentation_iff, hg, hYY']

/-- **The stabilizer comparison of a cross-section.** For a maximal torus of a compact connected
Lie group, a root-plane decomposition with nonzero planes for a symmetric positive definite
invariant form, a regular `X₀` with closed chamber `C`, and `X ∈ 𝔱`, for instance a point of `C`:
for every `Y` of `C` close enough to `X`, every `g ∈ G` carrying `Y` into `C` lies in the adjoint
stabilizer `Z_G(X)`. -/
theorem IsMaximalTorus.eventually_mem_stabilizer_of_Ad_apply_eq
    (X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) :
    ∀ᶠ Y : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule in 𝓝 X,
      Y ∈ sameSideChamber α X₀ →
      ∀ (Y' : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule), Y' ∈ sameSideChamber α X₀ →
        ∀ g : G, Ad (I := I) g Y = Y' →
          g ∈ (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
            (X : LeftInvariantDerivation I G) := by
  have hsep : B.SeparatingLeft := LinearMap.BilinForm.separatingLeft_of_anisotropic hBp.anisotropic
  filter_upwards [hD.eventually_stabilizer_continuousAdjointRepresentation_le hB hsep hV X]
    with Y hYX hY Y' hY' g hg
  exact hYX (hT.mem_stabilizer_of_Ad_apply_eq hBs hBp hB hD hV hX₀ hY hY' hg)

end Connected

end Lie

end TauCeti
