/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Coadjoint.Height.Perfect
public import TauCeti.Geometry.Symplectic.Coadjoint.Height.Weyl

/-!
# The Poincaré polynomial of a coadjoint orbit

Let `T` be a maximal torus of a compact Lie group `G`, with Lie algebra `𝔱` and Weyl group
`W = N(T) / T`, let `B` be an `Ad`-invariant bilinear form on `𝔤` with trivial left radical, and
let `𝔤 = t + Σ F_i` be a root-plane decomposition over the image `t` of `𝔱`, with planes `F_i` of
dimension two and roots `α_i : t → ℝ`. For `μ ∈ 𝔱` let `O_μ = G ⧸ G_ν` be the coadjoint orbit of
`ν = B (e μ)`, and let `X ∈ t` be regular: no root vanishes at `X`.

The height `f_X` is a perfect Morse function on `O_μ`
(`Module.Dual.isPerfectMorse_orbitMap_coadjointRepresentation_apply`), its critical points are
the Weyl group points `[n_w]`, indexed by `W / W_μ` (`weylQuotientEquivCriticalPoints`), and its
Morse index at `[n_w]` is `2 n(w)`
(`manifoldMorseIndex_normalizerQuotientToCoadjointOrbit_eq_two_mul_card`), where

`n(w) = #{i | α_i(w μ) α_i(X) > 0}`

and `w μ` is read in `t` (`TauCeti.Lie.weylOrbitPoint`). The Weyl indexing and the Morse index
are in the namespace `TauCeti.IsRootPlaneDecomposition`, like the results of this file. Combining
the three, this file computes every Betti number of `O_μ`, over every division ring `k`, from the
Weyl orbit of `μ` and the signs of the roots, following Bott:

* the Betti number `b_{2j}(O_μ; k)` is the number of points `p` of the Weyl orbit `W μ`, read in
  `t`, with `#{i | α_i(p) α_i(X) > 0} = j`
  (`bettiNumber_quotient_stabilizer_coadjointRepresentation_two_mul_eq_ncard`);
* counted over the whole Weyl group, `|W_μ| b_j(O_μ; k)` is the number of `w ∈ W` with
  `2 n(w) = j`
  (`card_stabilizer_mul_bettiNumber_quotient_stabilizer_coadjointRepresentation_eq_ncard`), so
  the **index generating polynomial** is

  `|W_μ| Σ_j b_j(O_μ; k) tʲ = Σ_{w ∈ W} t^{2 n(w)}`

  (`card_stabilizer_smul_sum_monomial_bettiNumber_eq_sum_X_pow`). When `W_μ` is trivial, for
  instance for the full flag manifold `G / T`, the Poincaré polynomial of `O_μ` is
  `Σ_{w ∈ W} t^{2 n(w)}`.

The odd Betti numbers vanish
(`Module.Dual.bettiNumber_quotient_stabilizer_coadjointRepresentation_eq_zero_of_odd`). The
formulas do not involve `k`, so the Betti numbers of a coadjoint orbit are the same over every
division ring.

## Main results

In the namespace `TauCeti.IsRootPlaneDecomposition`:

* `bettiNumber_quotient_stabilizer_coadjointRepresentation_two_mul_eq_ncard`: `b_{2j}(O_μ; k)`
  counts the points of `W μ` at which exactly `j` roots have the sign they have at `X`.
* `card_stabilizer_mul_bettiNumber_quotient_stabilizer_coadjointRepresentation_eq_ncard`:
  `|W_μ| b_j(O_μ; k) = #{w ∈ W | 2 n(w) = j}`.
* `card_stabilizer_smul_sum_monomial_bettiNumber_eq_sum_X_pow`: the index generating polynomial.

## References

* R. Bott, *An application of the Morse theory to the topology of Lie-groups*, Bull. Soc. Math.
  France 84 (1956), 251–281, Theorem III and Proposition 11.5.
* M. Audin, *Torus Actions on Symplectic Manifolds*, 2nd ed., Progress in Mathematics 93,
  Birkhäuser, 2004, Chapter II.
-/

public section

noncomputable section

open Function Module Manifold Polynomial TauCeti TauCeti.Lie
open scoped Manifold ContDiff Finset

universe u

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
  isClosed_stabilizer_coadjointRepresentation

namespace TauCeti.IsRootPlaneDecomposition

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type u} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  [CompactSpace G]
  {T : Subgroup G} [IsMulCommutative T] {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)}
  {ι : Type*} [Fintype ι] {t : Submodule ℝ (GroupLieAlgebra I G)} {α : ι → Dual ℝ t}
  {F : ι → Submodule ℝ (GroupLieAlgebra I G)} {J : (i : ι) → End ℝ (F i)}
  (k : Type u) [DivisionRing k]

/-- **Betti numbers of a coadjoint orbit from the Weyl group.** In a root-plane decomposition
`𝔤 = t + Σ F_i` with planes of dimension two over the image `t` of the Lie algebra of a maximal
torus `T` of a compact Lie group, for an invariant form `B` with trivial left radical, `μ ∈ 𝔱` and
`X ∈ t` at which no root vanishes, the Betti number `b_j(O_μ; k)` of the coadjoint orbit of
`B (e μ)`, multiplied by the order of the stabilizer `W_μ` of `μ` in the Weyl group `W`, is the
number of `w ∈ W` with `2 #{i | α_i(w μ) α_i(X) > 0} = j`. -/
theorem card_stabilizer_mul_bettiNumber_quotient_stabilizer_coadjointRepresentation_eq_ncard
    (hD : IsRootPlaneDecomposition B t α F J) (hT : IsMaximalTorus T)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft) (hF : ∀ i, finrank ℝ (F i) = 2)
    (ht : t = (lieSubalgebraOfSubgroup (I := I) T).toSubmodule.map
      (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
        BoundarylessManifold.isInteriorPoint).toLinearEquiv.toLinearMap)
    (μ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) {X : t} (hX : ∀ i, α i X ≠ 0)
    (j : ℕ) :
    Nat.card ((T.weylAdjointRepresentation (I := I)).stabilizer μ) *
        bettiNumber k (G ⧸ (coadjointRepresentation ℝ I G).stabilizer
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ))) j =
      {w : T.normalizerQuotient |
        2 * #{i | 0 < α i (weylOrbitPoint ht μ w) * α i X} = j}.ncard := by
  rw [Module.Dual.bettiNumber_quotient_stabilizer_coadjointRepresentation_eq_ncard _ k
    (hD.isMorse_orbitMap_coadjointRepresentation_apply
      (lieInvariant_of_isInvariantForm_adjointRepresentation hB) hsep hX) j]
  set M := 𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
    (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
      BoundarylessManifold.isInteriorPoint μ))))
  set e := hD.weylQuotientEquivCriticalPoints hT hB hsep ht μ hX
  have he (w : T.normalizerQuotient) : (e w).val = normalizerQuotientToCoadjointOrbit B hB μ w :=
    hD.coe_weylQuotientEquivCriticalPoints_mk hT hB hsep ht μ hX w
  -- The critical points of index `j` are the images under `e` of a set `S ⊆ W / W_μ`, whose
  -- preimage in `W` is the set of `w` with `2 n(w) = j`.
  set S := {c | manifoldMorseIndex M
    (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap _ y X) (e c).val = j}
  have himage : {x ∈ criticalPoints M (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap _ y X) |
      manifoldMorseIndex M (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap _ y X) x = j} =
      (fun c ↦ (e c).val) '' S := by
    ext x
    refine ⟨fun ⟨hx, hj⟩ ↦ ⟨e.symm ⟨x, hx⟩, by simpa [S] using hj, by simp⟩, ?_⟩
    rintro ⟨c, hc, rfl⟩
    exact ⟨(e c).property, hc⟩
  have hpreimage : QuotientGroup.mk ⁻¹' S =
      {w : T.normalizerQuotient | 2 * #{i | 0 < α i (weylOrbitPoint ht μ w) * α i X} = j} := by
    ext w
    rw [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_ofPred_eq, he,
      hD.manifoldMorseIndex_normalizerQuotientToCoadjointOrbit_eq_two_mul_card hB hF ht μ X w]
  rw [himage, Set.ncard_image_of_injective (f := fun c ↦ (e c).val) _
      (Subtype.val_injective.comp e.injective),
    ← hpreimage, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    QuotientGroup.card_preimage_mk]

/-- **Even Betti numbers of a coadjoint orbit count Weyl orbit points.** In a root-plane
decomposition `𝔤 = t + Σ F_i` with planes of dimension two over the image `t` of the Lie algebra of
a maximal torus `T` of a compact Lie group, for an invariant form `B` with trivial left radical,
`μ ∈ 𝔱` and `X ∈ t` at which no root vanishes, the Betti number `b_{2j}(O_μ; k)` of the coadjoint
orbit of `B (e μ)` is the number of points `p` of the Weyl orbit of `μ`, read in `t`, at which
exactly `j` roots have the sign they have at `X`. -/
theorem bettiNumber_quotient_stabilizer_coadjointRepresentation_two_mul_eq_ncard
    (hD : IsRootPlaneDecomposition B t α F J) (hT : IsMaximalTorus T)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft) (hF : ∀ i, finrank ℝ (F i) = 2)
    (ht : t = (lieSubalgebraOfSubgroup (I := I) T).toSubmodule.map
      (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
        BoundarylessManifold.isInteriorPoint).toLinearEquiv.toLinearMap)
    (μ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) {X : t} (hX : ∀ i, α i X ≠ 0)
    (j : ℕ) :
    bettiNumber k (G ⧸ (coadjointRepresentation ℝ I G).stabilizer
        (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint μ))) (2 * j) =
      {p : t | p ∈ Set.range (weylOrbitPoint ht μ) ∧ #{i | 0 < α i p * α i X} = j}.ncard := by
  rw [Module.Dual.bettiNumber_quotient_stabilizer_coadjointRepresentation_eq_ncard _ k
    (hD.isMorse_orbitMap_coadjointRepresentation_apply
      (lieInvariant_of_isInvariantForm_adjointRepresentation hB) hsep hX) (2 * j)]
  -- Both sets are compared through their injective images in `𝔤*`: the orbit map on the
  -- coadjoint orbit, and `p ↦ B p` on `t`.
  have hBt : Injective fun p : t ↦ B p :=
    (LinearMap.ker_eq_bot.mp (LinearMap.separatingLeft_iff_ker_eq_bot.mp hsep)).comp
      Subtype.val_injective
  rw [← Set.ncard_image_of_injective _ ((coadjointRepresentation ℝ I G).orbitMap_injective _),
    ← Set.ncard_image_of_injective _ hBt,
    hD.criticalPoints_eq_range_normalizerQuotientToCoadjointOrbit hT hB hsep ht μ hX]
  congr 1
  ext ν
  constructor
  · rintro ⟨_, ⟨⟨w, rfl⟩, hj⟩, rfl⟩
    rw [hD.manifoldMorseIndex_normalizerQuotientToCoadjointOrbit_eq_two_mul_card hB hF ht μ X w]
      at hj
    exact ⟨weylOrbitPoint ht μ w, ⟨⟨w, rfl⟩, by omega⟩,
      (congrArg B (coe_weylOrbitPoint ht μ w)).trans
        (orbitMap_normalizerQuotientToCoadjointOrbit hB μ w).symm⟩
  · rintro ⟨_, ⟨⟨w, rfl⟩, hj⟩, rfl⟩
    refine ⟨_, ⟨⟨w, rfl⟩, ?_⟩, (orbitMap_normalizerQuotientToCoadjointOrbit hB μ w).trans
      (congrArg B (coe_weylOrbitPoint ht μ w)).symm⟩
    rw [hD.manifoldMorseIndex_normalizerQuotientToCoadjointOrbit_eq_two_mul_card hB hF ht μ X w,
      hj]

/-- **The index generating polynomial of a coadjoint orbit.** In a root-plane decomposition
`𝔤 = t + Σ F_i` with planes of dimension two over the image `t` of the Lie algebra of a maximal
torus `T` of a compact Lie group, for an invariant form `B` with trivial left radical, `μ ∈ 𝔱` and
`X ∈ t` at which no root vanishes, the Poincaré polynomial `Σ_j b_j(O_μ; k) tʲ` of the coadjoint
orbit of `B (e μ)`, multiplied by the order of the stabilizer `W_μ` of `μ` in the Weyl group `W`,
is `Σ_{w ∈ W} t^{2 n(w)}`, where `n(w) = #{i | α_i(w μ) α_i(X) > 0}`. The sum over `j` runs up to
the dimension of the orbit, above which the Betti numbers vanish. -/
theorem card_stabilizer_smul_sum_monomial_bettiNumber_eq_sum_X_pow [Fintype T.normalizerQuotient]
    (hD : IsRootPlaneDecomposition B t α F J) (hT : IsMaximalTorus T)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft) (hF : ∀ i, finrank ℝ (F i) = 2)
    (ht : t = (lieSubalgebraOfSubgroup (I := I) T).toSubmodule.map
      (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
        BoundarylessManifold.isInteriorPoint).toLinearEquiv.toLinearMap)
    (μ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) {X : t} (hX : ∀ i, α i X ≠ 0) :
    Nat.card ((T.weylAdjointRepresentation (I := I)).stabilizer μ) •
        ∑ j ∈ Finset.range (finrank ℝ (Subgroup.QuotientModelSpace I
          ((coadjointRepresentation ℝ I G).stabilizer
            (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
              BoundarylessManifold.isInteriorPoint μ)))) + 1),
          monomial j (bettiNumber k (G ⧸ (coadjointRepresentation ℝ I G).stabilizer
            (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
              BoundarylessManifold.isInteriorPoint μ))) j) =
      ∑ w : T.normalizerQuotient,
        (Polynomial.X : ℕ[X]) ^ (2 * #{i | 0 < α i (weylOrbitPoint ht μ w) * α i X}) := by
  set n : T.normalizerQuotient → ℕ := fun w ↦ #{i | 0 < α i (weylOrbitPoint ht μ w) * α i X}
  -- Each `2 n(w)` is a Morse index, so at most the dimension of the orbit.
  have hn : ∀ w ∈ (Finset.univ : Finset T.normalizerQuotient), 2 * n w ∈ Finset.range
      (finrank ℝ (Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
        (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint μ)))) + 1) := fun w _ ↦ by
    rw [Finset.mem_range, Nat.lt_succ_iff,
      ← hD.manifoldMorseIndex_normalizerQuotientToCoadjointOrbit_eq_two_mul_card hB hF ht μ X w]
    exact manifoldMorseIndex_le_finrank
  rw [← Finset.sum_fiberwise_of_maps_to hn, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_congr rfl fun w hw ↦ by rw [(Finset.mem_filter.mp hw).2], Finset.sum_const,
    ← smul_X_eq_monomial, smul_smul,
    hD.card_stabilizer_mul_bettiNumber_quotient_stabilizer_coadjointRepresentation_eq_ncard k hT hB
      hsep hF ht μ hX j, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]

end TauCeti.IsRootPlaneDecomposition
