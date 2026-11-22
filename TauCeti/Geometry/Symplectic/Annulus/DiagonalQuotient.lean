/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.Quotient
public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import TauCeti.Geometry.Symplectic.Annulus.CyclicAction
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# The smooth diagonal quotient of configuration space

The configurations of a chain of strip maps are the points `q : ι → ℝ` of the position space, and
lifts of annulus maps make everything invariant under the simultaneous integer translation
`q ↦ q + k • 1`. This file makes the quotient

`(ι → ℝ) ⧸ ℤ 1`

of the position space by the diagonal integers a smooth manifold, identifies it with a circle times
a vector space, and descends the cyclic action of a chain of strip maps to it, together with its
critical points.

The quotient carries the manifold structure of a quotient of a vector space by a discrete subgroup
(`AddSubgroup.instChartedSpaceDiscreteQuotient`, `AddSubgroup.instIsManifoldDiscreteQuotient`),
modelled on the position space itself, for which the projection is a local diffeomorphism
(`AddSubgroup.isLocalDiffeomorph_quotientMk`).

**Coordinates.** For an index `i₀`, the map `q ↦ (q_(i₀) mod 1, (q_i - q_(i₀))_(i ≠ i₀))` descends
to a diffeomorphism

`(ι → ℝ) ⧸ ℤ 1 ≃ (ℝ / ℤ) × ({i // i ≠ i₀} → ℝ)`

(`TauCeti.diagonalQuotientDiffeomorph`), whose inverse sends `(t mod 1, v)` to the class of the
configuration with `q_(i₀) = t` and `q_i = t + v_i`
(`TauCeti.diagonalQuotientDiffeomorph_symm_coe`).
So the quotient is the product of a circle with a vector space of one dimension less than `ι → ℝ`.

**The cyclic action.** For generating functions `S_i`, `i ∈ ℤ/N`, invariant under the diagonal
translation `(x, X) ↦ (x + 1, X + 1)`, the cyclic action `W(q) = Σ_i S_i(q_i, q_(i+1))`
(`TauCeti.cyclicAction`) is invariant under the diagonal integers, and descends to the function
`TauCeti.quotientCyclicAction` on the quotient. It is `C^n` at the class of `q` as soon as every
`S_i` is `C^n` at the edge `(q_i, q_(i+1))` (`TauCeti.contMDiffAt_quotientCyclicAction`), and its
differential at the class of `q`, composed with the differential of the projection, is the
derivative of `W` at `q` (`TauCeti.mvfderiv_quotientCyclicAction_comp`). So the class of `q` is a
critical point of the descended action exactly when `q` is a critical point of `W`
(`TauCeti.mvfderiv_quotientCyclicAction_eq_zero_iff`). With this, the chain dictionary on the strip
(`TauCeti.exists_periodic_prodMap_coe_ne_of_isStripGenerating`) reads: two distinct critical points
of the descended action, at classes of configurations whose edges lie in the generating domains,
give two periodic chains whose initial states are distinct points of the annulus.

**Compactness.** The quotient is not compact, but a closed set of configurations which is invariant
under the diagonal integers and on which the differences `q_i - q_(i₀)` are bounded has compact
image (`TauCeti.isCompact_image_mk_of_forall_abs_sub_le`): every class has a representative with
`q_(i₀) ∈ [0, 1]`.

## Main definitions

* `TauCeti.diagonalQuotientDiffeomorph i₀ n`: the `C^n` diffeomorphism
  `(ι → ℝ) ⧸ ℤ 1 ≃ (ℝ / ℤ) × ({i // i ≠ i₀} → ℝ)`.
* `TauCeti.quotientCyclicAction hS`: the cyclic action on the diagonal quotient.

## Main results

* `TauCeti.diagonalQuotientDiffeomorph_coe`, `TauCeti.diagonalQuotientDiffeomorph_symm_coe`: the
  coordinates of the diagonal quotient and their inverse.
* `TauCeti.isCompact_image_mk_of_forall_abs_sub_le`: compact subsets of the diagonal quotient.
* `TauCeti.contMDiffAt_quotientCyclicAction`, `TauCeti.contMDiff_quotientCyclicAction`: the
  descended action is as smooth as the generating functions.
* `TauCeti.mvfderiv_quotientCyclicAction_comp`,
  `TauCeti.mvfderiv_quotientCyclicAction_eq_zero_iff`: its differential, and its critical points.

## References

* C. C. Conley and E. Zehnder, *The Birkhoff–Lewis fixed point theorem and a conjecture of
  V. I. Arnold*, Inventiones Mathematicae 73 (1983), 33–49 (the finite-dimensional action on
  broken configurations, on the quotient by the diagonal integers).
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

/-! ### The coordinates of the diagonal quotient -/

section Coordinates

variable {ι : Type*} (i₀ : ι)

/-- The **diagonal coordinates** `q ↦ (q_(i₀) mod 1, (q_i - q_(i₀))_(i ≠ i₀))` of the position
space, as an additive map to `(ℝ / ℤ) × ({i // i ≠ i₀} → ℝ)`. -/
def diagonalCoordinates : (ι → ℝ) →+ AddCircle (1 : ℝ) × ({i // i ≠ i₀} → ℝ) :=
  ((QuotientAddGroup.mk' _).comp (Pi.evalAddMonoidHom (fun _ ↦ ℝ) i₀)).prod
    { toFun := fun q (i : {i // i ≠ i₀}) ↦ q i - q i₀
      map_zero' := by ext; simp
      map_add' := fun q q' ↦ by ext; simp only [Pi.add_apply]; ring }

/-- The diagonal coordinates of `q` are `(q_(i₀) mod 1, (q_i - q_(i₀))_(i ≠ i₀))`. -/
@[simp]
theorem diagonalCoordinates_apply (q : ι → ℝ) :
    diagonalCoordinates i₀ q =
      ((q i₀ : AddCircle (1 : ℝ)), fun i : {i // i ≠ i₀} ↦ q i - q i₀) :=
  (rfl)

/-- The kernel of the diagonal coordinates is the group of diagonal integers. -/
theorem ker_diagonalCoordinates :
    (diagonalCoordinates i₀).ker = AddSubgroup.zmultiples (1 : ι → ℝ) := by
  ext q
  rw [AddMonoidHom.mem_ker, diagonalCoordinates_apply, Prod.mk_eq_zero,
    AddCircle.coe_eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨⟨k, hk⟩, hq⟩
    refine ⟨k, funext fun i ↦ ?_⟩
    by_cases h : i = i₀
    · subst h
      simpa using hk
    · have := congrFun hq ⟨i, h⟩
      simp only [Pi.zero_apply, sub_eq_zero] at this
      simpa [this] using hk
  · rintro ⟨k, rfl⟩
    exact ⟨⟨k, by simp⟩, funext fun i ↦ by simp⟩

variable [DecidableEq ι]

/-- The configuration `q_(i₀) = t`, `q_i = t + v_i` for `i ≠ i₀`, a section of the diagonal
coordinates over `ℝ × ({i // i ≠ i₀} → ℝ)`: the sum of the diagonal configuration `t • 1` and the
extension of `v` by zero at `i₀`. -/
def diagonalSection : ℝ × ({i // i ≠ i₀} → ℝ) →L[ℝ] (ι → ℝ) :=
  (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (1 : ι → ℝ)).coprod
    (ContinuousLinearMap.pi fun i ↦
      if h : i = i₀ then 0
      else ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : {i // i ≠ i₀} ↦ ℝ) ⟨i, h⟩)

/-- The coordinates of `diagonalSection`, as a single formula. -/
theorem diagonalSection_apply (p : ℝ × ({i // i ≠ i₀} → ℝ)) (i : ι) :
    diagonalSection i₀ p i = p.1 + if h : i = i₀ then 0 else p.2 ⟨i, h⟩ := by
  by_cases h : i = i₀ <;> simp [diagonalSection, h]

@[simp]
theorem diagonalSection_apply_self (p : ℝ × ({i // i ≠ i₀} → ℝ)) :
    diagonalSection i₀ p i₀ = p.1 := by
  simp [diagonalSection_apply]

@[simp]
theorem diagonalSection_apply_of_ne (p : ℝ × ({i // i ≠ i₀} → ℝ)) {i : ι} (h : i ≠ i₀) :
    diagonalSection i₀ p i = p.1 + p.2 ⟨i, h⟩ := by
  simp [diagonalSection_apply, h]

/-- The diagonal coordinates of the configuration `q_(i₀) = t`, `q_i = t + v_i` are
`(t mod 1, v)`. -/
theorem diagonalCoordinates_diagonalSection (p : ℝ × ({i // i ≠ i₀} → ℝ)) :
    diagonalCoordinates i₀ (diagonalSection i₀ p) = ((p.1 : AddCircle (1 : ℝ)), p.2) := by
  refine Prod.ext (by simp) (funext fun i ↦ ?_)
  simp [diagonalSection_apply_of_ne i₀ p i.property]

omit [DecidableEq ι] in
/-- The diagonal coordinates are onto: `diagonalSection` is a section. -/
theorem surjective_diagonalCoordinates : Function.Surjective (diagonalCoordinates i₀) := by
  classical
  rintro ⟨θ, v⟩
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
  exact ⟨diagonalSection i₀ (t, v), diagonalCoordinates_diagonalSection i₀ (t, v)⟩

omit [DecidableEq ι] in
/-- The additive equivalence `(ι → ℝ) ⧸ ℤ 1 ≃ (ℝ / ℤ) × ({i // i ≠ i₀} → ℝ)` induced by the
diagonal coordinates. -/
def diagonalQuotientAddEquiv :
    (ι → ℝ) ⧸ AddSubgroup.zmultiples (1 : ι → ℝ) ≃+ AddCircle (1 : ℝ) × ({i // i ≠ i₀} → ℝ) :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_diagonalCoordinates i₀).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (surjective_diagonalCoordinates i₀))

omit [DecidableEq ι] in
/-- The additive equivalence sends the class of `q` to its diagonal coordinates. -/
@[simp]
theorem diagonalQuotientAddEquiv_coe (q : ι → ℝ) :
    diagonalQuotientAddEquiv i₀ (q : (ι → ℝ) ⧸ AddSubgroup.zmultiples (1 : ι → ℝ)) =
      diagonalCoordinates i₀ q :=
  (rfl)

/-- The inverse of the additive equivalence sends `(t mod 1, v)` to the class of the configuration
`q_(i₀) = t`, `q_i = t + v_i`. -/
@[simp]
theorem diagonalQuotientAddEquiv_symm_coe (t : ℝ) (v : {i // i ≠ i₀} → ℝ) :
    (diagonalQuotientAddEquiv i₀).symm ((t : AddCircle (1 : ℝ)), v) =
      (diagonalSection i₀ (t, v) : (ι → ℝ) ⧸ AddSubgroup.zmultiples (1 : ι → ℝ)) := by
  rw [AddEquiv.symm_apply_eq, diagonalQuotientAddEquiv_coe,
    diagonalCoordinates_diagonalSection]

variable [Fintype ι] (n : ℕ∞ω)

/-- The diagonal coordinates descend to a `C^n` map on the diagonal quotient. -/
private theorem contMDiff_diagonalQuotientAddEquiv :
    ContMDiff 𝓘(ℝ, ι → ℝ) (𝓘(ℝ).prod 𝓘(ℝ, {i // i ≠ i₀} → ℝ)) n
      (diagonalQuotientAddEquiv i₀) := by
  refine ((AddSubgroup.zmultiples (1 : ι → ℝ)).contMDiff_quotient_iff (n := n) le_rfl _).2 ?_
  -- read through the projection, the map is the diagonal coordinates
  let P : (ι → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i₀
  let L : (ι → ℝ) →L[ℝ] ({i // i ≠ i₀} → ℝ) :=
    ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.proj i.val - P
  have h : ⇑(diagonalQuotientAddEquiv i₀) ∘ QuotientAddGroup.mk =
      fun q ↦ ((P q : AddCircle (1 : ℝ)), L q) :=
    funext (diagonalQuotientAddEquiv_coe i₀)
  rw [h]
  exact ((AddCircle.contMDiff_coe 1 n).comp P.contMDiff).prodMk L.contMDiff

/-- The inverse of the diagonal coordinates on the diagonal quotient is `C^n`. -/
private theorem contMDiff_diagonalQuotientAddEquiv_symm :
    ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, {i // i ≠ i₀} → ℝ)) 𝓘(ℝ, ι → ℝ) n
      (diagonalQuotientAddEquiv i₀).symm := by
  -- read through the covering `(t, v) ↦ (t mod 1, v)`, the inverse is the projection of the
  -- linear section `diagonalSection`
  have hp : IsLocalDiffeomorph (𝓘(ℝ).prod 𝓘(ℝ, {i // i ≠ i₀} → ℝ))
      (𝓘(ℝ).prod 𝓘(ℝ, {i // i ≠ i₀} → ℝ)) n
      (Prod.map ((↑) : ℝ → AddCircle (1 : ℝ)) (id : ({i // i ≠ i₀} → ℝ) → _)) :=
    IsLocalDiffeomorph.prodMap (AddCircle.isLocalDiffeomorph_coe 1 n)
      (Diffeomorph.refl 𝓘(ℝ, {i // i ≠ i₀} → ℝ) _ n).isLocalDiffeomorph
  refine (hp.contMDiff_comp_iff
    (QuotientAddGroup.mk_surjective.prodMap Function.surjective_id) le_rfl).1 ?_
  have h : ⇑(diagonalQuotientAddEquiv i₀).symm ∘ Prod.map (↑) id =
      QuotientAddGroup.mk ∘ diagonalSection i₀ :=
    funext fun p ↦ diagonalQuotientAddEquiv_symm_coe i₀ p.1 p.2
  have hs : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, {i // i ≠ i₀} → ℝ)) 𝓘(ℝ, ι → ℝ) n
      (diagonalSection i₀) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact (diagonalSection i₀).contMDiff
  rw [h]
  exact ((AddSubgroup.zmultiples (1 : ι → ℝ)).isLocalDiffeomorph_quotientMk
    (I := 𝓘(ℝ, ι → ℝ)) (n := n)).contMDiff.comp hs

/-- **The diagonal quotient is a circle times a vector space.** The `C^n` diffeomorphism

`(ι → ℝ) ⧸ ℤ 1 ≃ (ℝ / ℤ) × ({i // i ≠ i₀} → ℝ)`, `[q] ↦ (q_(i₀) mod 1, (q_i - q_(i₀))_(i ≠ i₀))`,

for the quotient manifold structure on the quotient of the position space by the diagonal integers.
It is additive. -/
def diagonalQuotientDiffeomorph :
    ((ι → ℝ) ⧸ AddSubgroup.zmultiples (1 : ι → ℝ))
      ≃ₘ^n⟮𝓘(ℝ, ι → ℝ), 𝓘(ℝ).prod 𝓘(ℝ, {i // i ≠ i₀} → ℝ)⟯
      AddCircle (1 : ℝ) × ({i // i ≠ i₀} → ℝ) where
  toEquiv := (diagonalQuotientAddEquiv i₀).toEquiv
  contMDiff_toFun := contMDiff_diagonalQuotientAddEquiv i₀ n
  contMDiff_invFun := contMDiff_diagonalQuotientAddEquiv_symm i₀ n

/-- The diffeomorphism sends the class of `q` to `(q_(i₀) mod 1, (q_i - q_(i₀))_(i ≠ i₀))`. -/
@[simp]
theorem diagonalQuotientDiffeomorph_coe (q : ι → ℝ) :
    diagonalQuotientDiffeomorph i₀ n (q : (ι → ℝ) ⧸ AddSubgroup.zmultiples (1 : ι → ℝ)) =
      ((q i₀ : AddCircle (1 : ℝ)), fun i : {i // i ≠ i₀} ↦ q i - q i₀) :=
  diagonalQuotientAddEquiv_coe i₀ q

/-- The inverse diffeomorphism sends `(t mod 1, v)` to the class of the configuration
`q_(i₀) = t`, `q_i = t + v_i`. -/
@[simp]
theorem diagonalQuotientDiffeomorph_symm_coe (t : ℝ) (v : {i // i ≠ i₀} → ℝ) :
    (diagonalQuotientDiffeomorph i₀ n).symm ((t : AddCircle (1 : ℝ)), v) =
      (diagonalSection i₀ (t, v) : (ι → ℝ) ⧸ AddSubgroup.zmultiples (1 : ι → ℝ)) :=
  diagonalQuotientAddEquiv_symm_coe i₀ t v

/-- The diffeomorphism is additive. -/
theorem diagonalQuotientDiffeomorph_add (x y : (ι → ℝ) ⧸ AddSubgroup.zmultiples (1 : ι → ℝ)) :
    diagonalQuotientDiffeomorph i₀ n (x + y) =
      diagonalQuotientDiffeomorph i₀ n x + diagonalQuotientDiffeomorph i₀ n y :=
  map_add (diagonalQuotientAddEquiv i₀) x y

end Coordinates

/-! ### Compact subsets of the diagonal quotient -/

section Compact

variable {ι : Type*} [Finite ι]

/-- **Compactness on the diagonal quotient.** Let `K` be a closed set of configurations, invariant
under the diagonal integer translations `q ↦ q + k • 1`, on which the differences `q_i - q_(i₀)`
from one position are bounded. Then the image of `K` in the diagonal quotient is compact, although
`K` itself is not bounded: every class has a representative with `q_(i₀) ∈ [0, 1]`. -/
theorem isCompact_image_mk_of_forall_abs_sub_le {K : Set (ι → ℝ)} (hK : IsClosed K)
    (hKper : ∀ q ∈ K, ∀ k : ℤ, q + k • (1 : ι → ℝ) ∈ K) (i₀ : ι) {C : ℝ}
    (hC : ∀ q ∈ K, ∀ i, |q i - q i₀| ≤ C) :
    IsCompact ((QuotientAddGroup.mk : (ι → ℝ) → (ι → ℝ) ⧸ AddSubgroup.zmultiples (1 : ι → ℝ)) ''
      K) := by
  have := Fintype.ofFinite ι
  -- the representatives with `q_(i₀) ∈ [0, 1]` form a closed bounded, hence compact, set
  have hcpt : IsCompact (K ∩ {q | q i₀ ∈ Set.Icc (0 : ℝ) 1}) := by
    refine Metric.isCompact_of_isClosed_isBounded
      (hK.inter (isClosed_Icc.preimage (continuous_apply i₀))) ?_
    refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨C + 1, fun q hq ↦ ?_⟩
    have h2 : q i₀ ∈ Set.Icc (0 : ℝ) 1 := hq.2
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (by linarith [(abs_nonneg _).trans (hC q hq.1 i₀)])).2
      fun i ↦ ?_
    have h1 := abs_le.1 (hC q hq.1 i)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  -- and every class has such a representative
  have himage : (QuotientAddGroup.mk : (ι → ℝ) → (ι → ℝ) ⧸ AddSubgroup.zmultiples (1 : ι → ℝ)) ''
      K = QuotientAddGroup.mk '' (K ∩ {q | q i₀ ∈ Set.Icc (0 : ℝ) 1}) := by
    refine Set.Subset.antisymm ?_ (Set.image_mono Set.inter_subset_left)
    rintro _ ⟨q, hq, rfl⟩
    have hk : (q + (-⌊q i₀⌋) • (1 : ι → ℝ)) i₀ = q i₀ - ⌊q i₀⌋ := by
      simp [sub_eq_add_neg]
    refine ⟨q + (-⌊q i₀⌋) • (1 : ι → ℝ), ⟨hKper q hq _, ?_⟩, ?_⟩
    · rw [Set.mem_ofPred, hk, Set.mem_Icc]
      constructor <;> linarith [Int.floor_le (q i₀), Int.lt_floor_add_one (q i₀)]
    · rw [QuotientAddGroup.eq_iff_sub_mem, add_sub_cancel_left]
      exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples 1) _
  rw [himage]
  exact hcpt.image continuous_quotient_mk'

end Compact

/-! ### The cyclic action on the diagonal quotient -/

section CyclicAction

variable {N : ℕ} [NeZero N] {S : ZMod N → ℝ × ℝ → ℝ} (hS : ∀ i, Function.Periodic (S i) (1, 1))

/-- **The cyclic action on the diagonal quotient.** If the generating functions `S_i` are invariant
under the diagonal translation `(x, X) ↦ (x + 1, X + 1)`, the cyclic action
`W(q) = Σ_i S_i(q_i, q_(i+1))` is invariant under the diagonal integers
(`TauCeti.periodic_cyclicAction`), and descends to the quotient of the configuration space by the
diagonal integers. -/
def quotientCyclicAction : (ZMod N → ℝ) ⧸ AddSubgroup.zmultiples (1 : ZMod N → ℝ) → ℝ :=
  (periodic_cyclicAction hS).lift

/-- On the class of a configuration, the descended action is the cyclic action. -/
@[simp]
theorem quotientCyclicAction_coe (q : ZMod N → ℝ) :
    quotientCyclicAction hS (q : (ZMod N → ℝ) ⧸ AddSubgroup.zmultiples (1 : ZMod N → ℝ)) =
      cyclicAction S q :=
  (periodic_cyclicAction hS).lift_coe q

/-- The descended action composed with the projection is the cyclic action. -/
theorem quotientCyclicAction_comp_mk :
    quotientCyclicAction hS ∘ QuotientAddGroup.mk = cyclicAction S :=
  funext (quotientCyclicAction_coe hS)

/-- The cyclic action on the diagonal quotient is `C^n` at the class of a configuration `q` if every
generating function `S_i` is `C^n` at the edge `(q_i, q_(i+1))`. -/
theorem contMDiffAt_quotientCyclicAction {n : ℕ∞ω} {q : ZMod N → ℝ}
    (h : ∀ i, ContDiffAt ℝ n (S i) (q i, q (i + 1))) :
    ContMDiffAt 𝓘(ℝ, ZMod N → ℝ) 𝓘(ℝ) n (quotientCyclicAction hS)
      (q : (ZMod N → ℝ) ⧸ AddSubgroup.zmultiples (1 : ZMod N → ℝ)) := by
  rw [← ((AddSubgroup.zmultiples (1 : ZMod N → ℝ)).isLocalDiffeomorph_quotientMk
    (I := 𝓘(ℝ, ZMod N → ℝ)) (n := n) q).contMDiffAt_comp_iff le_rfl,
    quotientCyclicAction_comp_mk, contMDiffAt_iff_contDiffAt]
  exact contDiffAt_cyclicAction h

/-- The cyclic action on the diagonal quotient is `C^n` if the generating functions are. -/
theorem contMDiff_quotientCyclicAction {n : ℕ∞ω} (h : ∀ i, ContDiff ℝ n (S i)) :
    ContMDiff 𝓘(ℝ, ZMod N → ℝ) 𝓘(ℝ) n (quotientCyclicAction hS) := by
  intro x
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact contMDiffAt_quotientCyclicAction hS fun i ↦ (h i).contDiffAt

/-- **The differential of the cyclic action on the diagonal quotient.** Composed with the
differential of the projection at a configuration `q`, it is the derivative of the cyclic action
`W` at `q`. No differentiability is assumed: where `W` is not differentiable, neither is its
descent, and both sides vanish. -/
theorem mvfderiv_quotientCyclicAction_comp (q : ZMod N → ℝ) :
    (mvfderiv 𝓘(ℝ, ZMod N → ℝ) (quotientCyclicAction hS)
        (q : (ZMod N → ℝ) ⧸ AddSubgroup.zmultiples (1 : ZMod N → ℝ))).comp
      (mfderiv 𝓘(ℝ, ZMod N → ℝ) 𝓘(ℝ, ZMod N → ℝ) QuotientAddGroup.mk q) =
      mvfderiv 𝓘(ℝ, ZMod N → ℝ) (cyclicAction S) q := by
  rw [mvfderiv, mvfderiv, ← quotientCyclicAction_comp_mk hS,
    ((AddSubgroup.zmultiples (1 : ZMod N → ℝ)).isLocalDiffeomorph_quotientMk
      (I := 𝓘(ℝ, ZMod N → ℝ)) (n := 1) q).mfderiv_comp one_ne_zero,
    ContinuousLinearMap.comp_assoc]
  -- the base points `quotientCyclicAction hS [q]` and `(quotientCyclicAction hS ∘ mk) q` of the
  -- two tangent identifications agree by `Function.comp_apply`
  rfl

/-- **Critical points of the cyclic action on the diagonal quotient.** The class of a configuration
`q` is a critical point of the descended cyclic action exactly when `q` is a critical point of the
cyclic action `W`. -/
theorem mvfderiv_quotientCyclicAction_eq_zero_iff (q : ZMod N → ℝ) :
    mvfderiv 𝓘(ℝ, ZMod N → ℝ) (quotientCyclicAction hS)
        (q : (ZMod N → ℝ) ⧸ AddSubgroup.zmultiples (1 : ZMod N → ℝ)) = 0 ↔
      fderiv ℝ (cyclicAction S) q = 0 := by
  -- the differential of the projection is invertible
  obtain ⟨e, he⟩ := ((AddSubgroup.zmultiples (1 : ZMod N → ℝ)).isLocalDiffeomorph_quotientMk
    (I := 𝓘(ℝ, ZMod N → ℝ)) (n := 1) q).isInvertible_mfderiv one_ne_zero
  rw [← ContinuousLinearMap.comp_continuousLinearEquiv_eq_zero_iff _ e, he,
    mvfderiv_quotientCyclicAction_comp, mvfderiv_eq_fderiv]
  exact ContinuousLinearMap.comp_continuousLinearEquiv_eq_zero_iff _ _

end CyclicAction

end TauCeti
