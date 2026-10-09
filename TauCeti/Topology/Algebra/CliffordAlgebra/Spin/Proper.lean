/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.CliffordAlgebra.Lipschitz.OpenMap
public import TauCeti.Topology.Algebra.CliffordAlgebra.Lipschitz.Norm
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Closed
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Projection
public import TauCeti.Topology.Algebra.QuadraticForm.OrthogonalGroup.Compact
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Analysis.Normed.Field.ProperSpace
import TauCeti.FieldTheory.SquareClassGroup.Multiplicative
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Basic
import TauCeti.LinearAlgebra.QuadraticForm.Representation
import TauCeti.Topology.Compactness.LocallyCompact

/-!
# The Spin projection is proper over a local field

Let `Q` be a nondegenerate quadratic form on a finite-dimensional space over a locally compact
nontrivially normed field `K` in which `2` is invertible, such as `ℝ` or `ℚ_p`. The projections
from the Spin group to the orthogonal and special orthogonal groups are proper maps for the
canonical topologies. Consequently the Spin group is compact exactly when `Q` is anisotropic.

Properness is not a formal consequence of having a continuous homomorphism with finite kernel,
so the proof goes through the Lipschitz group. The vector representation of the Lipschitz group is
an open surjection onto `O(Q)` from a locally compact group, so every compact set of isometries is
contained in the image of a compact set `L` of Lipschitz elements. A Spin element `x` lying over
that compact set differs from some `y ∈ L` by a scalar `c`, since the kernel of the vector
representation consists of the scalars. Comparing Clifford norms gives `1 = c ^ 2 * N y`, and
`N y` stays away from zero on `L`, so `c` is bounded. Hence `x` lies in the compact set of scalar
multiples `c • y` with `c` bounded and `y ∈ L`, and the Spin group is closed.

For the compactness criterion, an anisotropic form has a compact orthogonal group, whose preimage
is the whole Spin group. An isotropic form has a hyperbolic pair, and the split torus element at
every square parameter has trivial spinor norm, so it lifts to the Spin group; these torus elements
form an unbounded family. This direction holds over any nontrivially normed field.

## Main results

* `CliffordAlgebra.isCompact_preimage_spinToOrthogonal`: compact sets of isometries have compact
  preimages in the Spin group.
* `CliffordAlgebra.isProperMap_spinToOrthogonal`: the projection from Spin to `O(Q)` is proper.
* `CliffordAlgebra.isProperMap_spinToSpecialOrthogonal`: the projection from Spin to `SO(Q)` is
  proper.
* `CliffordAlgebra.not_isCompact_spinGroup`: the Spin group of an isotropic nondegenerate form is
  not compact.
* `CliffordAlgebra.isCompact_spinGroup_iff`: the Spin group of a nondegenerate form is compact
  exactly when the form is anisotropic.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §55.
* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
-/

public section

open Set Topology

namespace CliffordAlgebra

open TauCeti

section Noncompact

variable {K V : Type*} [NontriviallyNormedField K] [Invertible (2 : K)] [AddCommGroup V]
  [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V)

/-- **The Spin group of an isotropic form is not compact.** For an isotropic nondegenerate
quadratic form on a finite-dimensional space over a nontrivially normed field in which `2` is
invertible, the Spin group is not a compact subset of the Clifford algebra. -/
theorem not_isCompact_spinGroup (hQ : Q.Nondegenerate) (hiso : ¬Q.Anisotropic) :
    ¬IsCompact (spinGroup Q : Set (CliffordAlgebra Q)) := by
  intro hcpt
  obtain ⟨u, v, -, hu, hv, huv⟩ :=
    _root_.QuadraticMap.exists_isotropic_pair_of_radical_eq_bot hQ.radical_eq_bot hiso
  have : CompactSpace (spinGroup Q) := isCompact_iff_compactSpace.mp hcpt
  refine QuadraticMap.not_isCompact_of_hyperbolicPairTorus_sq_mem Q hu hv huv
    (S := range fun x => ((spinToOrthogonal Q x : QuadraticMap.orthogonalGroup Q) : V ≃ₗ[K] V))
    (fun t => ?_) (isCompact_range (by fun_prop))
  -- The torus element at `t` is proper, so its square has trivial spinor norm and lifts to Spin.
  let g : QuadraticMap.specialOrthogonalGroup Q :=
    ⟨QuadraticMap.hyperbolicPairTorus Q hu hv huv t,
      QuadraticMap.hyperbolicPairTorus_mem_specialOrthogonalGroup hu hv huv t⟩
  have hg : g ^ 2 ∈ (spinorNorm Q hQ).ker := by
    obtain ⟨a, ha⟩ := squareClassHom_surjective (spinorNorm Q hQ g)
    rw [MonoidHom.mem_ker, map_pow, ← ha, ← map_pow, ← MonoidHom.mem_ker, ker_squareClassHom]
    exact ⟨a, sq a⟩
  rw [← range_spinToSpecialOrthogonal_eq_ker_spinorNorm] at hg
  obtain ⟨x, hx⟩ := hg
  refine ⟨x, ?_⟩
  dsimp only
  rw [← specialOrthogonalToOrthogonal_spinToSpecialOrthogonal, hx, map_pow, map_pow,
    Subgroup.coe_pow, Subgroup.coe_pow, QuadraticMap.coe_specialOrthogonalToOrthogonal]

end Noncompact

variable {K V : Type*} [NontriviallyNormedField K] [WeaklyLocallyCompactSpace K]
  [Invertible (2 : K)] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V)

/-- **Compact sets of isometries have compact preimages in Spin.** For a nondegenerate quadratic
form on a finite-dimensional space over a locally compact nontrivially normed field in which `2`
is invertible, the preimage in the Spin group of a compact set of isometries is compact. -/
theorem isCompact_preimage_spinToOrthogonal (hQ : Q.Nondegenerate)
    {C : Set (QuadraticMap.orthogonalGroup Q)} (hC : IsCompact C) :
    IsCompact (spinToOrthogonal Q ⁻¹' C) := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact (Set.toFinite _).isCompact
  have : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  have : LocallyCompactSpace (lipschitzGroup Q) :=
    (isClosed_lipschitzGroup Q hQ).locallyCompactSpace
  have hv : ∃ v, IsUnit (Q v) := hQ.exists_isUnit
  -- The vector representation is an open surjection, so `C` lies in the image of a compact `L`.
  obtain ⟨L, hL, hCL⟩ := (isOpenMap_lipschitzToOrthogonal Q hQ).exists_isCompact_subset_image
    (lipschitzToOrthogonal_surjective Q hQ) hC
  -- The inverse Clifford norm is bounded on the compact set `L`.
  obtain ⟨R, hR⟩ : ∃ R, ∀ y ∈ L, ‖(((cliffordNorm Q y)⁻¹ : Kˣ) : K)‖ ≤ R :=
    (hL.image (Units.continuous_coe_inv.comp (continuous_cliffordNorm Q)).norm).bddAbove
      |>.imp fun R hR y hy => hR ⟨y, hy, rfl⟩
  let S : Set (CliffordAlgebra Q) :=
    (fun p : K × lipschitzGroup Q => p.1 • ((p.2 : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) ''
      (Metric.closedBall 0 (max 1 R) ×ˢ L)
  have hS : IsCompact S := ((isCompact_closedBall _ _).prod hL).image (by fun_prop)
  -- A Spin element over `C` is a bounded scalar multiple of an element of `L`.
  have hsub : ((↑) : spinGroup Q → CliffordAlgebra Q) '' (spinToOrthogonal Q ⁻¹' C) ⊆ S := by
    rintro _ ⟨x, hx, rfl⟩
    let ℓ := pinToLipschitz Q (spinToPin Q x)
    have hℓ : lipschitzToOrthogonal Q ℓ = spinToOrthogonal Q x := by
      rw [← pinToOrthogonal_eq_lipschitzToOrthogonal, pinToOrthogonal_spinToPin]
    obtain ⟨y, hyL, hy⟩ := hCL hx
    have hker : ℓ * y⁻¹ ∈ (lipschitzToOrthogonal Q).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hy, hℓ, mul_inv_cancel]
    rw [ker_lipschitzToOrthogonal hQ hv] at hker
    obtain ⟨c, hc⟩ := hker
    have hcy : ((ℓ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
        algebraMap K (CliffordAlgebra Q) c * ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
      rw [← coe_scalarUnits hv, ← Units.val_mul, ← Subgroup.coe_mul, hc, inv_mul_cancel_right]
    have hnorm : c ^ 2 = (cliffordNorm Q y)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← cliffordNorm_eq_sq_mul_of_coe_eq_algebraMap_mul hcy]
      exact cliffordNorm_pinToLipschitz_spinToPin x
    have hc2 : ‖(c : K)‖ ^ 2 ≤ R := by
      rw [← norm_pow, ← Units.val_pow_eq_pow_val, hnorm]
      exact hR y hyL
    refine ⟨((c : K), y), ⟨?_, hyL⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      nlinarith [norm_nonneg (c : K), le_max_left 1 R, le_max_right 1 R]
    · simp only [Algebra.smul_def, ← hcy, ℓ, coe_pinToLipschitz_apply, coe_spinToPin_apply]
  have hemb : IsClosedEmbedding ((↑) : spinGroup Q → CliffordAlgebra Q) :=
    (isClosed_spinGroup Q hQ).isClosedEmbedding_subtypeVal
  rw [hemb.isCompact_iff]
  exact hS.of_isClosed_subset (hemb.isClosedMap _ (hC.isClosed.preimage (by fun_prop))) hsub

/-- **The Spin projection to `O(Q)` is proper.** For a nondegenerate quadratic form on a
finite-dimensional space over a locally compact nontrivially normed field in which `2` is
invertible, such as `ℝ` or `ℚ_p`, the projection from the Spin group to the orthogonal group is a
proper map. -/
theorem isProperMap_spinToOrthogonal (hQ : Q.Nondegenerate) :
    IsProperMap (spinToOrthogonal Q) :=
  isProperMap_iff_isCompact_preimage.mpr
    ⟨by fun_prop, fun _ hC => isCompact_preimage_spinToOrthogonal Q hQ hC⟩

/-- **The Spin projection to `SO(Q)` is proper.** Under the hypotheses of
`isProperMap_spinToOrthogonal`, the projection from the Spin group to the special orthogonal group
is a proper map. -/
theorem isProperMap_spinToSpecialOrthogonal (hQ : Q.Nondegenerate) :
    IsProperMap (spinToSpecialOrthogonal Q) := by
  have h : QuadraticMap.specialOrthogonalToOrthogonal Q ∘ spinToSpecialOrthogonal Q =
      spinToOrthogonal Q :=
    funext (specialOrthogonalToOrthogonal_spinToSpecialOrthogonal Q)
  exact isProperMap_of_comp_of_t2 (by fun_prop)
    (_root_.QuadraticMap.continuous_specialOrthogonalToOrthogonal Q)
    (h ▸ isProperMap_spinToOrthogonal Q hQ)

/-- **Compactness of the Spin group.** For a nondegenerate quadratic form on a finite-dimensional
space over a locally compact nontrivially normed field in which `2` is invertible, such as `ℝ` or
`ℚ_p`, the Spin group is compact exactly when the form is anisotropic. -/
theorem isCompact_spinGroup_iff (hQ : Q.Nondegenerate) :
    IsCompact (spinGroup Q : Set (CliffordAlgebra Q)) ↔ Q.Anisotropic := by
  refine ⟨fun h => by_contra fun hiso => not_isCompact_spinGroup Q hQ hiso h, fun hani => ?_⟩
  have hO : IsCompact (univ : Set (QuadraticMap.orthogonalGroup Q)) := by
    rw [Topology.IsInducing.subtypeVal.isCompact_iff, image_univ, Subtype.range_coe]
    exact QuadraticMap.isCompact_orthogonalGroup Q hani
  have := isCompact_preimage_spinToOrthogonal Q hQ hO
  rw [preimage_univ, Topology.IsInducing.subtypeVal.isCompact_iff, image_univ,
    Subtype.range_coe] at this
  exact this

end CliffordAlgebra
