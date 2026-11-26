/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import TauCeti.Geometry.Symplectic.Coadjoint.Height.Weyl

/-!
# Critical sets of degenerate heights on coadjoint orbits

Let `T` be a maximal torus of a compact Lie group `G`, with Lie algebra `𝔱` and Weyl group
`W = N(T) / T`, let `B` be an `Ad`-invariant bilinear form on `𝔤` with trivial left radical, and
let `O = G ⧸ G_ν` be the coadjoint orbit of `ν = B (e μ)` for `μ ∈ 𝔱`, with orbit map `Φ`. For
`X ∈ 𝔱` the height `f_X(x) = Φ x (e X)` has as critical points the `x` with `Φ x = B (e q)` and
`⁅X, q⁆ = 0`. When `X` is regular these are the finitely many Weyl group points `[n_w]`
(`TauCeti.Lie.criticalPoints_eq_range_normalizerQuotientToCoadjointOrbit`). This file treats an
arbitrary `X ∈ 𝔱`, for instance `X = 0` or `X` on a wall, where the critical set can have
positive dimension.

The adjoint stabilizer `Z_G(X) = {k | Ad_k X = X}` acts on `O` and preserves `f_X`. Every element
commuting with `X` is conjugated into `𝔱` by an element of `Z_G(X)`
(`TauCeti.Lie.IsMaximalTorus.exists_mem_stabilizer_Ad_mem_lieSubalgebraOfSubgroup`), so every
critical point is carried by `Z_G(X)` to a Weyl group point. Hence the critical set is the finite
union of the `Z_G(X)`-orbits of the Weyl group points:

`Crit(f_X) = ⋃_{w ∈ W} Z_G(X) · [n_w]`

(`TauCeti.Lie.criticalPoints_eq_iUnion_orbit_normalizerQuotientToCoadjointOrbit`). Two of these
orbits agree exactly when the Weyl group elements lie in one double coset `W_X w W_μ`, where `W_X`
and `W_μ` are the stabilizers of `X` and `μ` in `W`
(`TauCeti.Lie.orbit_normalizerQuotientToCoadjointOrbit_eq_iff`): a conjugacy `Ad_k (w μ) = w' μ`
by `k ∈ Z_G(X)` is realized by an element of `Z_G(X)` normalizing `T`
(`TauCeti.Lie.IsMaximalTorus.exists_mem_stabilizer_mem_normalizer_Ad_eq`). So the
`Z_G(X)`-orbits of critical points are indexed by the double coset space `W_X \ W / W_μ`
(`TauCeti.Lie.doubleCosetQuotientEquivOrbitCriticalPoints`), and there are finitely many of them.

For `X = 0` the stabilizer `Z_G(X)` is all of `G`, the height is constant and the whole orbit is
one critical orbit. At the other extreme, for regular `X` the union is the finite set of Weyl
group points, as in the regular case above. For a connected group `G` the adjoint stabilizers are
connected (`TauCeti.Lie.isConnected_stabilizer_adjointRepresentation`), so the critical set is a
finite union of connected orbits. For instance, on the full flag manifold of `U(3)` and
`X = diag(i, i, 0)`, there are `|S₂ \ S₃| = 3` such orbits, of the group `U(2) × U(1)`.

## Main results

* `TauCeti.Lie.criticalPoints_eq_iUnion_orbit_normalizerQuotientToCoadjointOrbit`: the critical
  set of `f_X` is the union of the `Z_G(X)`-orbits of the Weyl group points.
* `TauCeti.Lie.orbit_normalizerQuotientToCoadjointOrbit_eq_iff`: two such orbits agree exactly when
  the Weyl group elements lie in one double coset `W_X \ W / W_μ`.
* `TauCeti.Lie.doubleCosetQuotientEquivOrbitCriticalPoints`: the bijection from `W_X \ W / W_μ`
  onto the set of `Z_G(X)`-orbits of critical points.
* `TauCeti.Lie.finite_image_orbit_criticalPoints`: there are finitely many such orbits.

## References

* R. Bott, *An application of the Morse theory to the topology of Lie-groups*, Bull. Soc. Math.
  France 84 (1956), 251–281.
* J. J. Duistermaat, J. A. C. Kolk and V. S. Varadarajan, *Functions, flows and oscillatory
  integrals on flag manifolds and conjugacy classes in real semisimple Lie groups*, Compositio
  Math. 49 (1983), 309–398, Section 3.
-/

public section

noncomputable section

open Function Module Manifold TauCeti TauCeti.Lie
open scoped Manifold ContDiff

namespace TauCeti.Lie

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  {T : Subgroup G} [IsMulCommutative T] {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)}

/-! ### The critical set as a union of stabilizer orbits -/

/-- **The critical set of a height is a finite union of stabilizer orbits.** Let `T` be a maximal
torus of a compact Lie group, `B` an invariant form with trivial left radical, and `μ`, `X` in the
Lie algebra `𝔱` of `T`. The critical points of the height `f_X = ⟨·, e X⟩` on the coadjoint orbit
of `B (e μ)` are exactly the points `k • [n_w]` with `k` in the adjoint stabilizer `Z_G(X)` of `X`
and `w` in the Weyl group. No regularity of `X` is assumed. -/
theorem criticalPoints_eq_iUnion_orbit_normalizerQuotientToCoadjointOrbit [CompactSpace G]
    (hT : IsMaximalTorus T) (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft) (μ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule)
    {X : LeftInvariantDerivation I G} (hX : X ∈ lieSubalgebraOfSubgroup (I := I) T) :
    criticalPoints
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ))))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ)) y
          (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint X)) =
      ⋃ w : T.normalizerQuotient,
        MulAction.orbit
          ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer X)
          (normalizerQuotientToCoadjointOrbit B hB μ w) := by
  ext x
  induction x using QuotientGroup.induction_on with | H g =>
  rw [mk_mem_criticalPoints_orbitMap_coadjointRepresentation_iff hB hsep, Set.mem_iUnion]
  constructor
  · -- Conjugate `Ad_g μ` into `𝔱` by `c ∈ Z_G(X)`: then `[c g]` is a Weyl group point `[n_w]`,
    -- and `[g] = c⁻¹ • [n_w]`.
    intro h
    obtain ⟨c, hc, hcT⟩ := hT.exists_mem_stabilizer_Ad_mem_lieSubalgebraOfSubgroup hX h
    have hmem : ((c * g : G) : G ⧸ _) ∈ Set.range (normalizerQuotientToCoadjointOrbit B hB μ) := by
      rw [range_normalizerQuotientToCoadjointOrbit hT hB hsep μ]
      refine ⟨_, hcT, ?_⟩
      rw [orbitMap_coadjointRepresentation_bilinForm_mk hB, Ad_mul, LieEquiv.trans_apply]
    obtain ⟨w, hw⟩ := hmem
    refine ⟨w, MulAction.mem_orbit_iff.mpr ⟨⟨c, hc⟩⁻¹, ?_⟩⟩
    rw [hw, Subgroup.smul_def, MulAction.Quotient.smul_mk, smul_eq_mul, InvMemClass.coe_inv,
      inv_mul_cancel_left]
  · -- A point `k • [n] = [k n]` has `⁅X, Ad_k (Ad_n μ)⁆ = Ad_k ⁅X, Ad_n μ⁆ = 0`, since `Ad_k X = X`
    -- and `X`, `Ad_n μ` lie in the commutative Lie algebra `𝔱`.
    rintro ⟨w, hw⟩
    obtain ⟨k, hkw⟩ := MulAction.mem_orbit_iff.mp hw
    induction w using QuotientGroup.induction_on with | H n =>
    rw [normalizerQuotientToCoadjointOrbit_mk, Subgroup.smul_def, MulAction.Quotient.smul_mk,
      smul_eq_mul] at hkw
    have hkX := mem_stabilizer_continuousAdjointRepresentation_iff.mp k.property
    rw [← (mk_mem_criticalPoints_orbitMap_coadjointRepresentation_iff hB hsep μ X g), ← hkw,
      mk_mem_criticalPoints_orbitMap_coadjointRepresentation_iff hB hsep, Ad_mul,
      LieEquiv.trans_apply]
    calc ⁅X, Ad (I := I) (k : G) (Ad (I := I) (n : G) μ)⁆
        = Ad (I := I) (k : G) ⁅X, Ad (I := I) (n : G) μ⁆ := by rw [LieEquiv.map_lie, hkX]
      _ = 0 := by
        rw [lie_eq_zero_of_mem_lieSubalgebraOfSubgroup hX
          (Ad_mem_lieSubalgebraOfSubgroup n.property μ.property), map_zero]

/-! ### Indexing the stabilizer orbits by double cosets -/

/-- The adjoint stabilizer `Z_G(X)` maps a Weyl group point `[n_w]` to the Weyl group point of
`v w` for every `v` in the stabilizer `W_X` of `X` in the Weyl group. -/
private theorem exists_smul_normalizerQuotientToCoadjointOrbit_eq_mul
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (μ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule)
    {X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule} {v : T.normalizerQuotient}
    (hv : v ∈ (T.weylAdjointRepresentation (I := I)).stabilizer X) (w : T.normalizerQuotient) :
    ∃ k : (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
        (X : LeftInvariantDerivation I G),
      k • normalizerQuotientToCoadjointOrbit B hB μ w =
        normalizerQuotientToCoadjointOrbit B hB μ (v * w) := by
  induction v using QuotientGroup.induction_on with | H m =>
  induction w using QuotientGroup.induction_on with | H n =>
  have hm : Ad (I := I) (m : G) X = X := by
    rw [← T.coe_weylAdjointRepresentation_mk_apply, Representation.mem_stabilizer.mp hv]
  refine ⟨⟨m, mem_stabilizer_continuousAdjointRepresentation_iff.mpr hm⟩, ?_⟩
  rw [← QuotientGroup.mk_mul, normalizerQuotientToCoadjointOrbit_mk,
    normalizerQuotientToCoadjointOrbit_mk, Subgroup.smul_def, MulAction.Quotient.smul_mk,
    smul_eq_mul, Subgroup.coe_mul]

/-- **Stabilizer orbits of Weyl group points are indexed by double cosets.** Let `T` be a maximal
torus of a compact Lie group, `B` an invariant form with trivial left radical, and `μ`, `X` in the
Lie algebra `𝔱` of `T`. The orbits of the Weyl group points `[n_w]` and `[n_w']` of the coadjoint
orbit of `B (e μ)` under the adjoint stabilizer `Z_G(X)` agree exactly when `w'` lies in the double
coset `W_X w W_μ`, where `W_X` and `W_μ` are the stabilizers of `X` and `μ` in the Weyl group. -/
theorem orbit_normalizerQuotientToCoadjointOrbit_eq_iff [CompactSpace G] (hT : IsMaximalTorus T)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft) (μ X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule)
    {w w' : T.normalizerQuotient} :
    MulAction.orbit
        ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
          (X : LeftInvariantDerivation I G))
        (normalizerQuotientToCoadjointOrbit B hB μ w) =
      MulAction.orbit
        ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
          (X : LeftInvariantDerivation I G))
        (normalizerQuotientToCoadjointOrbit B hB μ w') ↔
      w' ∈ DoubleCoset.doubleCoset w ((T.weylAdjointRepresentation (I := I)).stabilizer X)
        ((T.weylAdjointRepresentation (I := I)).stabilizer μ) := by
  rw [eq_comm, MulAction.orbit_eq_iff, MulAction.mem_orbit_iff, DoubleCoset.mem_doubleCoset]
  constructor
  · -- If `k • [n_w] = [n_w']` with `k ∈ Z_G(X)`, then `Ad_k (w μ) = w' μ`, and an element `m` of
    -- `Z_G(X)` normalizing `T` does the same: its class `v` lies in `W_X` and
    -- `(v w)⁻¹ w' ∈ W_μ`.
    rintro ⟨⟨k, hk⟩, hkw⟩
    induction w using QuotientGroup.induction_on with | H n =>
    induction w' using QuotientGroup.induction_on with | H n' =>
    rw [normalizerQuotientToCoadjointOrbit_mk, normalizerQuotientToCoadjointOrbit_mk,
      Subgroup.smul_def, MulAction.Quotient.smul_mk, smul_eq_mul] at hkw
    have hAd := congrArg ((coadjointRepresentation ℝ I G).orbitMap _) hkw
    rw [orbitMap_coadjointRepresentation_bilinForm_mk hB,
      orbitMap_coadjointRepresentation_bilinForm_mk hB, Ad_mul, LieEquiv.trans_apply] at hAd
    obtain ⟨m, hmX, hmN, hm⟩ := hT.exists_mem_stabilizer_mem_normalizer_Ad_eq X.property
      (Ad_mem_lieSubalgebraOfSubgroup n.property μ.property)
      (Ad_mem_lieSubalgebraOfSubgroup n'.property μ.property) hk
      (injective_bilinForm_comp_leftInvariantDerivationLieEquivGroupLieAlgebra hsep hAd)
    set v : T.normalizerQuotient :=
      ((⟨m, hmN⟩ : Subgroup.normalizer (T : Set G)) : T.normalizerQuotient)
    have hv : v ∈ (T.weylAdjointRepresentation (I := I)).stabilizer X :=
      Representation.mem_stabilizer.mpr (Subtype.ext ((T.coe_weylAdjointRepresentation_mk_apply
        ⟨m, hmN⟩ X).trans (mem_stabilizer_continuousAdjointRepresentation_iff.mp hmX)))
    -- `v w` and `w'` agree on `μ`.
    have hvw : T.weylAdjointRepresentation (I := I) (v * (n : T.normalizerQuotient)) μ =
        T.weylAdjointRepresentation (I := I) (n' : T.normalizerQuotient) μ := by
      refine Subtype.ext ?_
      rw [← QuotientGroup.mk_mul, T.coe_weylAdjointRepresentation_mk_apply,
        T.coe_weylAdjointRepresentation_mk_apply, Subgroup.coe_mul, Ad_mul,
        LieEquiv.trans_apply, hm]
    refine ⟨v, hv, (v * n)⁻¹ * n', Representation.mem_stabilizer.mpr ?_, by group⟩
    rw [map_mul, mul_apply_eq_comp, ← hvw, ← mul_apply_eq_comp, ← map_mul, inv_mul_cancel,
      map_one, one_apply_eq_self]
  · -- Conversely `w' = v w u` with `v ∈ W_X` and `u ∈ W_μ`; a representative of `v` lies in
    -- `Z_G(X)` and maps `[n_w]` to `[n_(v w)] = [n_(v w u)]`.
    rintro ⟨v, hv, u, hu, rfl⟩
    obtain ⟨k, hk⟩ := exists_smul_normalizerQuotientToCoadjointOrbit_eq_mul hB μ hv w
    refine ⟨k, hk.trans ((normalizerQuotientToCoadjointOrbit_eq_iff hB hsep μ).mpr ?_)⟩
    rw [map_mul (T.weylAdjointRepresentation (I := I)) (v * w) u, mul_apply_eq_comp,
      Representation.mem_stabilizer.mp hu]

variable (B) in
/-- **The stabilizer orbits of critical points are indexed by `W_X \ W / W_μ`.** Let `T` be a
maximal torus of a compact Lie group, `B` an invariant form with trivial left radical, and `μ`, `X`
in the Lie algebra `𝔱` of `T`. Sending the double coset of `w` to the orbit of the Weyl group point
`[n_w]` under the adjoint stabilizer `Z_G(X)` is a bijection from the double coset space
`W_X \ W / W_μ` onto the set of `Z_G(X)`-orbits of critical points of the height `f_X` on the
coadjoint orbit of `B (e μ)`. -/
def doubleCosetQuotientEquivOrbitCriticalPoints [CompactSpace G] (hT : IsMaximalTorus T)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft) (μ X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) :
    DoubleCoset.Quotient
        ((T.weylAdjointRepresentation (I := I)).stabilizer X : Set T.normalizerQuotient)
        ((T.weylAdjointRepresentation (I := I)).stabilizer μ : Set T.normalizerQuotient) ≃
      MulAction.orbit
          ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
            (X : LeftInvariantDerivation I G)) ''
        criticalPoints
          𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
            (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
              BoundarylessManifold.isInteriorPoint μ))))
          (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap
            (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
              BoundarylessManifold.isInteriorPoint μ)) y
            (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
              BoundarylessManifold.isInteriorPoint X)) := by
  set Z := (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
    (X : LeftInvariantDerivation I G)
  have hrel (w w' : T.normalizerQuotient) :
      DoubleCoset.setoid
          ((T.weylAdjointRepresentation (I := I)).stabilizer X : Set T.normalizerQuotient)
          ((T.weylAdjointRepresentation (I := I)).stabilizer μ : Set T.normalizerQuotient) w w' ↔
        MulAction.orbit Z (normalizerQuotientToCoadjointOrbit B hB μ w) =
          MulAction.orbit Z (normalizerQuotientToCoadjointOrbit B hB μ w') := by
    rw [DoubleCoset.rel_iff, orbit_normalizerQuotientToCoadjointOrbit_eq_iff hT hB hsep,
      DoubleCoset.mem_doubleCoset]
    simp only [SetLike.mem_coe]
  -- The orbit map `w ↦ Z_G(X) · [n_w]` descends to an injective map on double cosets, whose range
  -- is the set of orbits of critical points.
  let f : DoubleCoset.Quotient
      ((T.weylAdjointRepresentation (I := I)).stabilizer X : Set T.normalizerQuotient)
      ((T.weylAdjointRepresentation (I := I)).stabilizer μ : Set T.normalizerQuotient) → Set _ :=
    Quotient.lift (fun w ↦ MulAction.orbit Z (normalizerQuotientToCoadjointOrbit B hB μ w))
      fun w w' h ↦ (hrel w w').mp h
  have hf : Injective f := fun a b hab ↦ by
    induction a using Quotient.inductionOn with | h w =>
    induction b using Quotient.inductionOn with | h w' =>
    exact Quotient.sound ((hrel w w').mpr hab)
  refine (Equiv.ofInjective f hf).trans (Set.equivOfEq ?_)
  rw [criticalPoints_eq_iUnion_orbit_normalizerQuotientToCoadjointOrbit hT hB hsep μ X.property]
  ext S
  simp only [Set.mem_range, Set.mem_image, Set.mem_iUnion]
  constructor
  · rintro ⟨a, rfl⟩
    induction a using Quotient.inductionOn with | h w =>
    exact ⟨_, ⟨w, MulAction.mem_orbit_self _⟩, rfl⟩
  · rintro ⟨x, ⟨w, hx⟩, rfl⟩
    exact ⟨Quotient.mk _ w, (MulAction.orbit_eq_iff.mpr hx).symm⟩

/-- The double coset of `w` corresponds to the orbit of the Weyl group point `[n_w]` under the
adjoint stabilizer `Z_G(X)`. -/
@[simp]
theorem coe_doubleCosetQuotientEquivOrbitCriticalPoints_mk [CompactSpace G]
    (hT : IsMaximalTorus T) (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft) (μ X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule)
    (w : T.normalizerQuotient) :
    (doubleCosetQuotientEquivOrbitCriticalPoints B hT hB hsep μ X
        (DoubleCoset.mk _ _ w) : Set (G ⧸ (coadjointRepresentation ℝ I G).stabilizer
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ)))) =
      MulAction.orbit
        ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
          (X : LeftInvariantDerivation I G))
        (normalizerQuotientToCoadjointOrbit B hB μ w) :=
  (rfl)

/-- **A height has finitely many critical stabilizer orbits.** Let `T` be a maximal torus of a
compact Lie group, `B` an invariant form with trivial left radical, and `μ`, `X` in the Lie algebra
`𝔱` of `T`. The critical points of the height `f_X` on the coadjoint orbit of `B (e μ)` form
finitely many orbits of the adjoint stabilizer `Z_G(X)`. -/
theorem finite_image_orbit_criticalPoints [CompactSpace G] (hT : IsMaximalTorus T)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft) (μ X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) :
    (MulAction.orbit
          ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
            (X : LeftInvariantDerivation I G)) ''
        criticalPoints
          𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
            (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
              BoundarylessManifold.isInteriorPoint μ))))
          (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap
            (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
              BoundarylessManifold.isInteriorPoint μ)) y
            (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
              BoundarylessManifold.isInteriorPoint X))).Finite := by
  have := hT.finite_normalizerQuotient (I := I)
  have : Finite (DoubleCoset.Quotient ((T.weylAdjointRepresentation (I := I)).stabilizer X :
      Set T.normalizerQuotient)
      ((T.weylAdjointRepresentation (I := I)).stabilizer μ : Set T.normalizerQuotient)) :=
    Quotient.finite _
  exact Set.finite_coe_iff.mp
    (Finite.of_equiv _ (doubleCosetQuotientEquivOrbitCriticalPoints B hT hB hsep μ X))

end TauCeti.Lie
