/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.InvariantForm
public import TauCeti.Geometry.Lie.Subgroup.Weyl.AdjointOrbit
public import TauCeti.Geometry.Lie.Subgroup.Weyl.Finite
public import TauCeti.Geometry.Symplectic.Coadjoint.Height.RootPlane

/-!
# The Weyl group indexes the critical points of a regular height

Let `T` be a maximal torus of a compact Lie group `G`, with Lie algebra `𝔱` and Weyl group
`W = N(T) / T` acting on `𝔱` by `Subgroup.weylAdjointRepresentation`. Let `B` be an
`Ad`-invariant bilinear form on `𝔤 = GroupLieAlgebra I G` with trivial left radical, for instance
an invariant inner product, and let `e : LeftInvariantDerivation I G ≃ 𝔤` be evaluation at the
identity. For `μ ∈ 𝔱`, let `O = G ⧸ G_ν` be the coadjoint orbit of `ν = B (e μ)`, with orbit map
`Φ : [g] ↦ Ad*_g ν`, and call `x ∈ O` a *torus point* when `Φ x = B (e q)` for some `q ∈ 𝔱`.

Through `B`, the orbit map is `Φ [g] = B (e (Ad_g μ))`
(`TauCeti.Lie.orbitMap_coadjointRepresentation_bilinForm_mk`, in
`TauCeti.Geometry.Lie.Adjoint.InvariantForm`). Since `T` fixes `μ`, it lies in the
stabilizer `G_ν`
(`TauCeti.Lie.le_stabilizer_coadjointRepresentation_of_mem_lieSubalgebraOfSubgroup`, in
`TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Stabilizer`), so a representative
`n ∈ N(T)` of `w ∈ W` gives a well-defined point `[n_w]` of `O`
(`TauCeti.Lie.normalizerQuotientToCoadjointOrbit`), with `Φ [n_w] = B (e (w μ))`.
This file proves:

* `[n_w] = [n_w']` exactly when `w μ = w' μ`
  (`TauCeti.Lie.normalizerQuotientToCoadjointOrbit_eq_iff`);
* the points `[n_w]` are exactly the torus points of `O`
  (`TauCeti.Lie.range_normalizerQuotientToCoadjointOrbit`). This is the theorem that an adjoint
  orbit meets `𝔱` in one Weyl orbit, read on the orbit manifold: `O ∩ 𝔱 = W μ`. Its Lie algebra
  form is `TauCeti.Lie.IsMaximalTorus.exists_weylAdjointRepresentation_eq_iff`.

Hence the torus points of `O` are indexed by `W / W_μ`, where `W_μ` is the stabilizer of `μ` in
`W`. Now let `X` be *regular*, in the sense that every element commuting with `X` lies in `𝔱`.
A point `x` of `O` is a critical point of the height `f_X(x) = Φ x (e X)` exactly when
`⁅e X, q⁆ = 0` for `Φ x = B q`
(`Module.Dual.mem_criticalPoints_orbitMap_coadjointRepresentation_apply_iff_lie_eq_zero`), that is
exactly when `x` is a torus point. So

`Crit(f_X) = {[n_w] | w ∈ W} ≃ W / W_μ`

(`TauCeti.Lie.criticalPoints_eq_range_normalizerQuotientToCoadjointOrbit`,
`TauCeti.Lie.weylQuotientEquivCriticalPoints`). In particular the critical set is finite and has
`[W : W_μ]` points (`TauCeti.Lie.card_criticalPoints_orbitMap_coadjointRepresentation`), and for a
point `μ` whose stabilizer in `W` is trivial it has `|W|` points. An element `X` of a root-plane
decomposition of `𝔤` over `𝔱` at which no root vanishes is regular in this sense
(`TauCeti.IsRootPlaneDecomposition.mem_lieSubalgebraOfSubgroup_of_lie_eq_zero`), so the same
holds for it
(`TauCeti.IsRootPlaneDecomposition.criticalPoints_eq_range_normalizerQuotientToCoadjointOrbit`,
`TauCeti.IsRootPlaneDecomposition.weylQuotientEquivCriticalPoints`), and then the Morse index of
`f_X` at the critical point `[n_w]` is `2 #{i | α_i(w μ) α_i(X) > 0}`
(`manifoldMorseIndex_normalizerQuotientToCoadjointOrbit_eq_two_mul_card`, in the same namespace).

## Main definitions

* `TauCeti.Lie.normalizerQuotientToCoadjointOrbit`: the point `[n_w]` of the coadjoint orbit of
  `B (e μ)` represented by a Weyl group element `w`.
* `TauCeti.Lie.weylQuotientEquivCriticalPoints`: for a regular height, the bijection
  `W / W_μ ≃ Crit(f_X)`.
* `TauCeti.IsRootPlaneDecomposition.weylQuotientEquivCriticalPoints`: the same bijection for an
  `X` at which no root of a root-plane decomposition vanishes.

## Main results

* `TauCeti.Lie.range_normalizerQuotientToCoadjointOrbit`: the Weyl group points are exactly the
  torus points of the orbit.
* `TauCeti.Lie.mk_mem_criticalPoints_orbitMap_coadjointRepresentation_iff`: the point `[g]` is a
  critical point of `f_X` exactly when `⁅X, Ad_g μ⁆ = 0`.
* `TauCeti.Lie.criticalPoints_eq_range_normalizerQuotientToCoadjointOrbit`: for a regular `X`,
  the critical points of `f_X` are the Weyl group points.
* `TauCeti.Lie.card_criticalPoints_orbitMap_coadjointRepresentation`: the critical set has
  `[W : W_μ]` points.
* `TauCeti.IsRootPlaneDecomposition.mem_lieSubalgebraOfSubgroup_of_lie_eq_zero`: an `X` at which
  no root of a root-plane decomposition vanishes is regular.
* `TauCeti.IsRootPlaneDecomposition.criticalPoints_eq_range_normalizerQuotientToCoadjointOrbit`,
  `TauCeti.IsRootPlaneDecomposition.card_criticalPoints_orbitMap_coadjointRepresentation`: the
  critical set and its count for such an `X`.
* `manifoldMorseIndex_normalizerQuotientToCoadjointOrbit_eq_two_mul_card`, in the namespace
  `TauCeti.IsRootPlaneDecomposition`: the Morse index at the critical point `[n_w]`.

## References

* R. Bott, *An application of the Morse theory to the topology of Lie-groups*, Bull. Soc. Math.
  France 84 (1956), 251–281.
* M. Audin, *Torus Actions on Symplectic Manifolds*, 2nd ed., Progress in Mathematics 93,
  Birkhäuser, 2004, Chapter II.
* J. J. Duistermaat, J. A. C. Kolk and V. S. Varadarajan, *Functions, flows and oscillatory
  integrals on flag manifolds and conjugacy classes in real semisimple Lie groups*, Compositio
  Math. 49 (1983), 309–398.
-/

public section

noncomputable section

open Function Module Manifold TauCeti TauCeti.Lie
open scoped Manifold ContDiff Finset

namespace TauCeti.Lie

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  {T : Subgroup G} [IsMulCommutative T] {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)}

/-! ### Weyl group points of a coadjoint orbit -/

section Points

omit [T2Space G] in
/-- An injective invariant-form covector map: `a ↦ B (e a)` is injective when `B` has trivial
left radical. -/
theorem injective_bilinForm_comp_leftInvariantDerivationLieEquivGroupLieAlgebra
    (hsep : B.SeparatingLeft) :
    Injective fun D : LeftInvariantDerivation I G ↦
      B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
        BoundarylessManifold.isInteriorPoint D) :=
  (LinearMap.ker_eq_bot.mp (LinearMap.separatingLeft_iff_ker_eq_bot.mp hsep)).comp
    (LieEquiv.injective _)

variable (B) in
/-- **The Weyl group points of a coadjoint orbit.** For an invariant form `B` and `μ` in the Lie
algebra of a commutative subgroup `T`, the class of `n ∈ N(T)` in the Weyl group `N(T) / T` is
sent to the point `[n]` of the coadjoint orbit `G ⧸ G_ν` of `ν = B (e μ)`. It is well defined
because `T ≤ G_ν`. -/
def normalizerQuotientToCoadjointOrbit
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (μ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) :
    T.normalizerQuotient → G ⧸ (coadjointRepresentation ℝ I G).stabilizer
      (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
        BoundarylessManifold.isInteriorPoint μ)) :=
  Quotient.map' Subtype.val fun _ _ hab ↦ by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    exact le_stabilizer_coadjointRepresentation_of_mem_lieSubalgebraOfSubgroup hB μ.property
      (Subgroup.mem_subgroupOf.mp hab)

/-- The Weyl group point of the class of `n ∈ N(T)` is the coset of `n`. -/
@[simp]
theorem normalizerQuotientToCoadjointOrbit_mk
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (μ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) (n : Subgroup.normalizer (T : Set G)) :
    normalizerQuotientToCoadjointOrbit B hB μ (n : T.normalizerQuotient) = ((n : G) : G ⧸ _) :=
  (rfl)

/-- **The image of a Weyl group point.** The orbit map sends the point `[n_w]` of the coadjoint
orbit of `B (e μ)` to `B (e (w μ))`. -/
theorem orbitMap_normalizerQuotientToCoadjointOrbit
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (μ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) (w : T.normalizerQuotient) :
    (coadjointRepresentation ℝ I G).orbitMap _ (normalizerQuotientToCoadjointOrbit B hB μ w) =
      B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
        BoundarylessManifold.isInteriorPoint (T.weylAdjointRepresentation (I := I) w μ)) := by
  induction w using QuotientGroup.induction_on with | H n =>
  rw [normalizerQuotientToCoadjointOrbit_mk, orbitMap_coadjointRepresentation_bilinForm_mk hB,
    Subgroup.coe_weylAdjointRepresentation_mk_apply]

/-- **Two Weyl group points agree exactly when the Weyl group elements agree on `μ`.** For an
invariant form `B` with trivial left radical, `[n_w] = [n_w']` in the coadjoint orbit of
`B (e μ)` exactly when `w μ = w' μ`. -/
theorem normalizerQuotientToCoadjointOrbit_eq_iff
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft) (μ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule)
    {w w' : T.normalizerQuotient} :
    normalizerQuotientToCoadjointOrbit B hB μ w = normalizerQuotientToCoadjointOrbit B hB μ w' ↔
      T.weylAdjointRepresentation (I := I) w μ = T.weylAdjointRepresentation (I := I) w' μ := by
  rw [← ((coadjointRepresentation ℝ I G).orbitMap_injective _).eq_iff,
    orbitMap_normalizerQuotientToCoadjointOrbit, orbitMap_normalizerQuotientToCoadjointOrbit,
    (injective_bilinForm_comp_leftInvariantDerivationLieEquivGroupLieAlgebra hsep).eq_iff,
    Subtype.ext_iff]

/-- **The Weyl group points are the torus points.** Let `T` be a maximal torus of a compact Lie
group, `B` an invariant form with trivial left radical and `μ` in the Lie algebra `𝔱` of `T`. A
point of the coadjoint orbit of `B (e μ)` is a Weyl group point `[n_w]` exactly when its image is
`B (e q)` for some `q ∈ 𝔱`: the orbit meets `𝔱` in the Weyl orbit of `μ`. -/
theorem range_normalizerQuotientToCoadjointOrbit [CompactSpace G] (hT : IsMaximalTorus T)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft) (μ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) :
    Set.range (normalizerQuotientToCoadjointOrbit B hB μ) =
      {x | ∃ q ∈ lieSubalgebraOfSubgroup (I := I) T,
        (coadjointRepresentation ℝ I G).orbitMap _ x =
          B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint q)} := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨_, (T.weylAdjointRepresentation (I := I) w μ).property,
      orbitMap_normalizerQuotientToCoadjointOrbit hB μ w⟩
  · rintro ⟨q, hq, hx⟩
    induction x using QuotientGroup.induction_on with | H g =>
    -- The point `[g]` has image `B (e (Ad_g μ))`, so `Ad_g μ = q ∈ 𝔱`, and the Weyl theorem gives
    -- `w` with `w μ = q`.
    rw [orbitMap_coadjointRepresentation_bilinForm_mk hB] at hx
    have hAd := injective_bilinForm_comp_leftInvariantDerivationLieEquivGroupLieAlgebra hsep hx
    obtain ⟨w, hw⟩ := (hT.exists_weylAdjointRepresentation_eq_iff μ ⟨q, hq⟩).mpr ⟨g, hAd⟩
    refine ⟨w, (coadjointRepresentation ℝ I G).orbitMap_injective _ ?_⟩
    rw [orbitMap_normalizerQuotientToCoadjointOrbit, hw,
      orbitMap_coadjointRepresentation_bilinForm_mk hB, hAd]

end Points

/-! ### Critical points of a regular height -/

section Critical

omit [T2Space G] [IsMulCommutative T] in
/-- **The critical points of a height in coset coordinates.** For an invariant form `B` with trivial
left radical, the point `[g]` of the coadjoint orbit of `B (e μ)` is a critical point of the height
`f_X = ⟨·, e X⟩` exactly when `⁅X, Ad_g μ⁆ = 0`. -/
theorem mk_mem_criticalPoints_orbitMap_coadjointRepresentation_iff
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft) (μ X : LeftInvariantDerivation I G) (g : G) :
    (g : G ⧸ (coadjointRepresentation ℝ I G).stabilizer
        (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint μ))) ∈
      criticalPoints
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ))))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ)) y
          (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint X)) ↔
      ⁅X, Ad (I := I) g μ⁆ = 0 := by
  rw [Module.Dual.mem_criticalPoints_orbitMap_coadjointRepresentation_apply_iff_lie_eq_zero
    (lieInvariant_of_isInvariantForm_adjointRepresentation hB) hsep
    (orbitMap_coadjointRepresentation_bilinForm_mk hB μ g), ← LieEquiv.map_lie,
    EmbeddingLike.map_eq_zero_iff]

/-- **The critical points of a regular height are the Weyl group points.** Let `T` be a maximal
torus of a compact Lie group, `B` an invariant form with trivial left radical and `μ` in the Lie
algebra `𝔱` of `T`. If `X` is regular, in the sense that every derivation commuting with `X` lies
in `𝔱`, then the critical points of the height `f_X = ⟨·, e X⟩` on the coadjoint orbit of
`B (e μ)` are exactly the Weyl group points `[n_w]`. -/
theorem criticalPoints_eq_range_normalizerQuotientToCoadjointOrbit [CompactSpace G]
    (hT : IsMaximalTorus T) (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft) (μ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule)
    {X : LeftInvariantDerivation I G}
    (hX : ∀ Y : LeftInvariantDerivation I G, ⁅X, Y⁆ = 0 → Y ∈ lieSubalgebraOfSubgroup (I := I) T) :
    criticalPoints
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ))))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap _ y
          (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint X)) =
      Set.range (normalizerQuotientToCoadjointOrbit B hB μ) := by
  have hXT : X ∈ lieSubalgebraOfSubgroup (I := I) T := hX X (lie_self X)
  rw [range_normalizerQuotientToCoadjointOrbit hT hB hsep μ]
  ext x
  induction x using QuotientGroup.induction_on with | H g =>
  -- The point `[g]` has image `B (e (Ad_g μ))`; both sides say that `Ad_g μ` lies in `𝔱`.
  have hq := orbitMap_coadjointRepresentation_bilinForm_mk hB μ g
  rw [mk_mem_criticalPoints_orbitMap_coadjointRepresentation_iff hB hsep, Set.mem_ofPred_eq]
  constructor
  · exact fun h ↦ ⟨_, hX _ h, hq⟩
  · rintro ⟨D', hD', hx⟩
    rw [hq] at hx
    rw [injective_bilinForm_comp_leftInvariantDerivationLieEquivGroupLieAlgebra hsep hx]
    exact lie_eq_zero_of_mem_lieSubalgebraOfSubgroup hXT hD'

variable (B) in
/-- **The Weyl indexing of the critical points of a regular height.** Let `T` be a maximal torus
of a compact Lie group, `B` an invariant form with trivial left radical, `μ` in the Lie algebra
`𝔱` of `T`, and `X` regular, in the sense that every derivation commuting with `X` lies in `𝔱`.
Then `w ↦ [n_w]` induces a bijection from `W / W_μ` onto the critical points of the height
`f_X = ⟨·, e X⟩` on the coadjoint orbit of `B (e μ)`, where `W_μ` is the stabilizer of `μ` in the
Weyl group `W`. -/
def weylQuotientEquivCriticalPoints [CompactSpace G] (hT : IsMaximalTorus T)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft) (μ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule)
    {X : LeftInvariantDerivation I G}
    (hX : ∀ Y : LeftInvariantDerivation I G, ⁅X, Y⁆ = 0 → Y ∈ lieSubalgebraOfSubgroup (I := I) T) :
    T.normalizerQuotient ⧸ (T.weylAdjointRepresentation (I := I)).stabilizer μ ≃
      criticalPoints
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ))))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ)) y
          (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint X)) := by
  refine (Equiv.ofInjective (Quotient.lift (normalizerQuotientToCoadjointOrbit B hB μ)
    fun w w' h ↦ ?_) ?_).trans
      (Set.equivOfEq ((Set.range_quotient_lift (s := QuotientGroup.leftRel _) _).trans
        (criticalPoints_eq_range_normalizerQuotientToCoadjointOrbit hT hB hsep μ hX).symm))
  -- Both obligations are read off the orbit map `W / W_μ → 𝔱`, `[w] ↦ w μ`.
  · simpa only [normalizerQuotientToCoadjointOrbit_eq_iff hB hsep, Representation.orbitMap_mk]
      using congrArg ((T.weylAdjointRepresentation (I := I)).orbitMap μ)
        (QuotientGroup.eq.mpr (QuotientGroup.leftRel_apply.mp h))
  · intro a b hab
    induction a using QuotientGroup.induction_on with | H w =>
    induction b using QuotientGroup.induction_on with | H w' =>
    refine (T.weylAdjointRepresentation (I := I)).orbitMap_injective μ ?_
    simpa only [Representation.orbitMap_mk] using
      (normalizerQuotientToCoadjointOrbit_eq_iff hB hsep μ).mp hab

/-- The Weyl indexing sends the class of `w` modulo `W_μ` to the Weyl group point `[n_w]`. -/
@[simp]
theorem coe_weylQuotientEquivCriticalPoints_mk [CompactSpace G] (hT : IsMaximalTorus T)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft) (μ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule)
    {X : LeftInvariantDerivation I G}
    (hX : ∀ Y : LeftInvariantDerivation I G, ⁅X, Y⁆ = 0 → Y ∈ lieSubalgebraOfSubgroup (I := I) T)
    (w : T.normalizerQuotient) :
    (weylQuotientEquivCriticalPoints B hT hB hsep μ hX (w : T.normalizerQuotient ⧸ _) :
        G ⧸ (coadjointRepresentation ℝ I G).stabilizer
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ))) =
      normalizerQuotientToCoadjointOrbit B hB μ w :=
  (rfl)

/-- **The critical set of a regular height is finite, with `[W : W_μ]` points.** Let `T` be a
maximal torus of a compact Lie group, `B` an invariant form with trivial left radical, `μ` in the
Lie algebra `𝔱` of `T` and `X` regular. The height `f_X` on the coadjoint orbit of `B (e μ)` has
exactly as many critical points as the index of the stabilizer `W_μ` of `μ` in the Weyl group. -/
theorem card_criticalPoints_orbitMap_coadjointRepresentation [CompactSpace G]
    (hT : IsMaximalTorus T) (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft) (μ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule)
    {X : LeftInvariantDerivation I G}
    (hX : ∀ Y : LeftInvariantDerivation I G, ⁅X, Y⁆ = 0 → Y ∈ lieSubalgebraOfSubgroup (I := I) T) :
    Nat.card (criticalPoints
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ))))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ)) y
          (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint X))) =
      ((T.weylAdjointRepresentation (I := I)).stabilizer μ).index :=
  (Nat.card_congr (weylQuotientEquivCriticalPoints B hT hB hsep μ hX)).symm

/-- **The critical set of a regular height is finite.** -/
theorem finite_criticalPoints_orbitMap_coadjointRepresentation [CompactSpace G]
    (hT : IsMaximalTorus T) (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft) (μ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule)
    {X : LeftInvariantDerivation I G}
    (hX : ∀ Y : LeftInvariantDerivation I G, ⁅X, Y⁆ = 0 → Y ∈ lieSubalgebraOfSubgroup (I := I) T) :
    (criticalPoints
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ))))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ)) y
          (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint X))).Finite := by
  have := hT.finite_normalizerQuotient (I := I)
  exact Set.finite_coe_iff.mp (.of_equiv _ (weylQuotientEquivCriticalPoints B hT hB hsep μ hX))

/-- **A point with trivial Weyl stabilizer gives `|W|` critical points.** If no nontrivial element
of the Weyl group fixes `μ`, the height `f_X` of a regular `X` on the
coadjoint orbit of `B (e μ)` has exactly `|W|` critical points. -/
theorem card_criticalPoints_orbitMap_coadjointRepresentation_of_stabilizer_eq_bot
    [CompactSpace G] (hT : IsMaximalTorus T)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft) (μ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule)
    (hμ : (T.weylAdjointRepresentation (I := I)).stabilizer μ = ⊥)
    {X : LeftInvariantDerivation I G}
    (hX : ∀ Y : LeftInvariantDerivation I G, ⁅X, Y⁆ = 0 → Y ∈ lieSubalgebraOfSubgroup (I := I) T) :
    Nat.card (criticalPoints
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ))))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ)) y
          (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint X))) =
      Nat.card T.normalizerQuotient := by
  rw [card_criticalPoints_orbitMap_coadjointRepresentation hT hB hsep μ hX, hμ,
    Subgroup.index_bot]

end Critical

end TauCeti.Lie

/-! ### Regular heights in a root-plane decomposition -/

namespace TauCeti.IsRootPlaneDecomposition

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  {T : Subgroup G} [IsMulCommutative T] {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)}
  {ι : Type*} {t : Submodule ℝ (GroupLieAlgebra I G)} {α : ι → Dual ℝ t}
  {F : ι → Submodule ℝ (GroupLieAlgebra I G)} {J : (i : ι) → End ℝ (F i)}

omit [IsMulCommutative T] in
/-- **A regular element of a root-plane decomposition is regular.** Let `T` be a subgroup, `B` a
Lie-invariant form with trivial left radical, and `𝔤 = t + Σ F_i` a root-plane decomposition over
the image `t` of the Lie algebra `𝔱` of `T`. If no root vanishes at `X ∈ t` and `e D = X`, then
every derivation commuting with `D` lies in `𝔱`. -/
theorem mem_lieSubalgebraOfSubgroup_of_lie_eq_zero [Finite ι]
    (hD : IsRootPlaneDecomposition B t α F J)
    (hB : B.lieInvariant (GroupLieAlgebra I G))
    (hsep : B.SeparatingLeft)
    (ht : t = (lieSubalgebraOfSubgroup (I := I) T).toSubmodule.map
      (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
        BoundarylessManifold.isInteriorPoint).toLinearEquiv.toLinearMap)
    {X : t} (hX : ∀ i, α i X ≠ 0) {D : LeftInvariantDerivation I G}
    (hDX : leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
      BoundarylessManifold.isInteriorPoint D = X)
    {Y : LeftInvariantDerivation I G} (hY : ⁅D, Y⁆ = 0) :
    Y ∈ lieSubalgebraOfSubgroup (I := I) T := by
  have hYt := hD.mem_of_lie_eq_zero hB hsep hX (q := leftInvariantDerivationLieEquivGroupLieAlgebra
    (I := I) (G := G) BoundarylessManifold.isInteriorPoint Y)
    (by rw [← hDX, ← LieEquiv.map_lie, hY, map_zero])
  rw [ht] at hYt
  obtain ⟨Y', hY', hY'Y⟩ := hYt
  rwa [← (LieEquiv.injective _) hY'Y]

/-- **The critical points of a regular height in a root-plane decomposition.** Let `T` be a
maximal torus of a compact Lie group, `B` an invariant form with trivial left radical, and
`𝔤 = t + Σ F_i` a root-plane decomposition over the image `t` of the Lie algebra of `T`. For
`μ ∈ 𝔱` and `X ∈ t` at which no root vanishes, the critical points of the height `f_X` on the
coadjoint orbit of `B (e μ)` are exactly the Weyl group points `[n_w]`. -/
theorem criticalPoints_eq_range_normalizerQuotientToCoadjointOrbit [CompactSpace G] [Finite ι]
    (hD : IsRootPlaneDecomposition B t α F J) (hT : IsMaximalTorus T)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft)
    (ht : t = (lieSubalgebraOfSubgroup (I := I) T).toSubmodule.map
      (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
        BoundarylessManifold.isInteriorPoint).toLinearEquiv.toLinearMap)
    (μ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) {X : t} (hX : ∀ i, α i X ≠ 0) :
    criticalPoints
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ))))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap _ y X) =
      Set.range (normalizerQuotientToCoadjointOrbit B hB μ) := by
  have hDX := LieEquiv.apply_symm_apply (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I)
    (G := G) BoundarylessManifold.isInteriorPoint) X
  rw [← TauCeti.Lie.criticalPoints_eq_range_normalizerQuotientToCoadjointOrbit hT hB hsep μ
    fun Y hY ↦ hD.mem_lieSubalgebraOfSubgroup_of_lie_eq_zero
      (lieInvariant_of_isInvariantForm_adjointRepresentation hB) hsep ht hX hDX hY, hDX]

/-- **The Weyl indexing of the critical points of a regular height in a root-plane
decomposition.** Let `T` be a maximal torus of a compact Lie group, `B` an invariant form with
trivial left radical, and `𝔤 = t + Σ F_i` a root-plane decomposition over the image `t` of the
Lie algebra of `T`. For `μ ∈ 𝔱` and `X ∈ t` at which no root vanishes, `w ↦ [n_w]` induces a
bijection from `W / W_μ` onto the critical points of the height `f_X` on the coadjoint orbit of
`B (e μ)`. This is `TauCeti.Lie.weylQuotientEquivCriticalPoints` for `e⁻¹ X`. -/
def weylQuotientEquivCriticalPoints [CompactSpace G] [Finite ι]
    (hD : IsRootPlaneDecomposition B t α F J) (hT : IsMaximalTorus T)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft)
    (ht : t = (lieSubalgebraOfSubgroup (I := I) T).toSubmodule.map
      (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
        BoundarylessManifold.isInteriorPoint).toLinearEquiv.toLinearMap)
    (μ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) {X : t} (hX : ∀ i, α i X ≠ 0) :
    T.normalizerQuotient ⧸ (T.weylAdjointRepresentation (I := I)).stabilizer μ ≃
      criticalPoints
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ))))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ)) y X) :=
  have hDX := LieEquiv.apply_symm_apply (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I)
    (G := G) BoundarylessManifold.isInteriorPoint) X
  (TauCeti.Lie.weylQuotientEquivCriticalPoints B hT hB hsep μ
    fun Y hY ↦ hD.mem_lieSubalgebraOfSubgroup_of_lie_eq_zero
      (lieInvariant_of_isInvariantForm_adjointRepresentation hB) hsep ht hX hDX hY).trans
      (Set.equivOfEq (by rw [hDX]))

/-- The Weyl indexing in a root-plane decomposition sends the class of `w` modulo `W_μ` to the
Weyl group point `[n_w]`. -/
@[simp]
theorem coe_weylQuotientEquivCriticalPoints_mk [CompactSpace G] [Finite ι]
    (hD : IsRootPlaneDecomposition B t α F J) (hT : IsMaximalTorus T)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft)
    (ht : t = (lieSubalgebraOfSubgroup (I := I) T).toSubmodule.map
      (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
        BoundarylessManifold.isInteriorPoint).toLinearEquiv.toLinearMap)
    (μ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) {X : t} (hX : ∀ i, α i X ≠ 0)
    (w : T.normalizerQuotient) :
    (hD.weylQuotientEquivCriticalPoints hT hB hsep ht μ hX (w : T.normalizerQuotient ⧸ _) :
        G ⧸ (coadjointRepresentation ℝ I G).stabilizer
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ))) =
      normalizerQuotientToCoadjointOrbit B hB μ w :=
  (rfl)

/-- **The critical set of a regular height in a root-plane decomposition has `[W : W_μ]`
points.** For `X ∈ t` at which no root vanishes, the height `f_X` on the coadjoint orbit of
`B (e μ)` has exactly as many critical points as the index of the stabilizer `W_μ` of `μ` in the
Weyl group. -/
theorem card_criticalPoints_orbitMap_coadjointRepresentation [CompactSpace G] [Finite ι]
    (hD : IsRootPlaneDecomposition B t α F J) (hT : IsMaximalTorus T)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft)
    (ht : t = (lieSubalgebraOfSubgroup (I := I) T).toSubmodule.map
      (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
        BoundarylessManifold.isInteriorPoint).toLinearEquiv.toLinearMap)
    (μ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) {X : t} (hX : ∀ i, α i X ≠ 0) :
    Nat.card (criticalPoints
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ))))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ)) y X)) =
      ((T.weylAdjointRepresentation (I := I)).stabilizer μ).index :=
  (Nat.card_congr (hD.weylQuotientEquivCriticalPoints hT hB hsep ht μ hX)).symm

/-- **The critical set of a regular height in a root-plane decomposition is finite.** -/
theorem finite_criticalPoints_orbitMap_coadjointRepresentation [CompactSpace G] [Finite ι]
    (hD : IsRootPlaneDecomposition B t α F J) (hT : IsMaximalTorus T)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft)
    (ht : t = (lieSubalgebraOfSubgroup (I := I) T).toSubmodule.map
      (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
        BoundarylessManifold.isInteriorPoint).toLinearEquiv.toLinearMap)
    (μ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) {X : t} (hX : ∀ i, α i X ≠ 0) :
    (criticalPoints
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ))))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ)) y X)).Finite := by
  have := hT.finite_normalizerQuotient (I := I)
  exact Set.finite_coe_iff.mp (.of_equiv _ (hD.weylQuotientEquivCriticalPoints hT hB hsep ht μ hX))

/-- **The Morse index at a Weyl group point.** In a root-plane decomposition `𝔤 = t + Σ F_i` with
planes of dimension two over the image `t` of the Lie algebra of `T`, for an invariant form `B`,
`μ ∈ 𝔱` and `X ∈ t`, the Morse index of the height `f_X` on the coadjoint orbit of `B (e μ)` at
the Weyl group point `[n_w]` is `2 #{i | α_i(w μ) α_i(X) > 0}`. -/
theorem manifoldMorseIndex_normalizerQuotientToCoadjointOrbit_eq_two_mul_card [Fintype ι]
    (hD : IsRootPlaneDecomposition B t α F J)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hF : ∀ i, finrank ℝ (F i) = 2)
    (ht : t = (lieSubalgebraOfSubgroup (I := I) T).toSubmodule.map
      (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
        BoundarylessManifold.isInteriorPoint).toLinearEquiv.toLinearMap)
    (μ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) (X : t) (w : T.normalizerQuotient) :
    manifoldMorseIndex
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ))))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap _ y X)
        (normalizerQuotientToCoadjointOrbit B hB μ w) =
      2 * #{i | 0 < α i ⟨leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint (T.weylAdjointRepresentation (I := I) w μ),
          ht ▸ Submodule.mem_map_of_mem (T.weylAdjointRepresentation (I := I) w μ).property⟩ *
        α i X} :=
  hD.manifoldMorseIndex_orbitMap_coadjointRepresentation_apply_eq_two_mul_card
    (lieInvariant_of_isInvariantForm_adjointRepresentation hB) hF
    (orbitMap_normalizerQuotientToCoadjointOrbit hB μ w)

end TauCeti.IsRootPlaneDecomposition
