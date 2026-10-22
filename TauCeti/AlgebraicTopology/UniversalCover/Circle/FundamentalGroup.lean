/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.FundamentalGroupCircle
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange
import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
public import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
public import TauCeti.AlgebraicTopology.UniversalCover.AddCircle
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.FundamentalGroup.Basic
public import TauCeti.Topology.Circle.AddCircle
public import TauCeti.Topology.Circle.Degree
public import TauCeti.Topology.Circle.Loop

/-!
# Fundamental groups of additive and complex circles

The covering `(↑) : ℝ → AddCircle p` is the universal cover of the circle: its total space
`ℝ` is contractible, hence simply connected, and the cover is regular with deck group
`Multiplicative ℤ` (the translations by the period subgroup, computed in
`TauCeti.Deck.addCircleMulEquivInt`). The regular-cover comparison
`TauCeti.Deck.IsRegular.fundamentalGroupDeckEquiv` then identifies the fundamental group of
the base with the deck group itself (the opposite drops out because the deck group is
commutative), giving

  `FundamentalGroup (AddCircle p) x ≃* Multiplicative ℤ`

for any nonzero real period `p`. Specialising to the unit circle `UnitAddCircle = ℝ ⧸ ℤ`
yields the classical `π₁(S¹) ≅ ℤ`. For positive periods this equivalence agrees with
Mathlib's `AddCircle.windingNumberIso`, as shown using its lift-endpoint formula. The unit-circle
monodromy characterizations use that canonical isomorphism directly.

For a nonzero real period `T`, `AddCircle.homeomorphCircle` identifies `AddCircle T` with
Mathlib's complex unit circle `Circle`. Transporting the additive-circle computation across this
homeomorphism gives `FundamentalGroup Circle x ≃* Multiplicative ℤ` at every basepoint,
using Mathlib's winding-number isomorphism at the positive period `2 * π`.

The regularity input is elementary and holds for an arbitrary topological additive group:
two points of `𝕜` with the same image under `(↑) : 𝕜 → AddCircle p` differ by an element of
the period subgroup `zmultiples p`, and translation by that element is a deck
transformation, so `deck ((↑) : 𝕜 → AddCircle p)` acts transitively on every fibre.

## Main declarations

* `AddCircle.fundamentalGroupMulEquivZMultiples`: for a covering projection from a simply
  connected additive group, the fundamental group of `AddCircle p` is the period subgroup.
* `AddCircle.fundamentalGroupMulEquivInt`: for a covering projection from a simply connected
  additive group with non-torsion period, the fundamental group of `AddCircle p` is
  `Multiplicative ℤ`.
* `AddCircle.fundamentalGroupMulEquiv`: for a nonzero real period, the fundamental group of
  `AddCircle p` (based at any point with a chosen lift) is `Multiplicative ℤ`.
* `AddCircle.fundamentalGroupMulEquivZero`: the basepoint-`0` specialisation, using the lift
  `0 : ℝ`.
* `AddCircle.fundamentalGroupMulEquiv_eq_windingNumberIso`: for positive periods the
  chosen-lift computation agrees with Mathlib, including the sign of the generator.
* `Circle.fundamentalGroupMulEquiv`: `π₁(Circle, x) ≃* Multiplicative ℤ`.
* `Circle.expLoop` and `Circle.fundamentalGroupMulEquiv_expLoop`: the loop `t ↦ exp(2πit)`,
  going once counterclockwise around the circle, is sent to the generator `ofAdd 1`.
* `Circle.mapOfEq_toCircle_expLoop`: a loop `γ`, read as a map from the circle, sends the class
  of `Circle.expLoop` to the class of `γ`.
* `Circle.fundamentalGroupMulEquiv_fromPath`: the class of a loop is sent to its degree
  `Circle.degree`, computed from angle lifts.
* `Circle.fundamentalGroupMulEquiv_map_pow`: the `n`-th power map of the circle acts on the
  fundamental group as multiplication by `n`.
* `Circle.zpowers_fromPath_eq_top_of_degree_map_eq_one`,
  `Circle.homotopic_trans_of_degree_map_eq`: for a map `d : X → Circle` injective on
  fundamental groups, the degree of the image of a loop detects generators and conjugate loops.

## References

It consumes Mathlib's `AddCircle` covering map (`AddCircle.isCoveringMap_coe`, Junyan Xu) and
the contractibility of a real topological vector space, together with Tau Ceti's
deck-transformation theory.
-/

public section

open TauCeti AddSubgroup

namespace AddCircle

variable {𝕜 : Type*} [AddCommGroup 𝕜] [TopologicalSpace 𝕜] [IsTopologicalAddGroup 𝕜]
  {p : 𝕜} [SimplyConnectedSpace 𝕜]
  [TotallyDisconnectedSpace (zmultiples p)]

/-- For a covering projection `(↑) : 𝕜 → AddCircle p` from a simply connected preconnected
topological additive commutative group with totally disconnected period subgroup, the
fundamental group of `AddCircle p` is the multiplicative period subgroup. -/
noncomputable def fundamentalGroupMulEquivZMultiples (hcov : IsCoveringMap ((↑) : 𝕜 → AddCircle p))
    {x : AddCircle p} (e : ((↑) : 𝕜 → AddCircle p) ⁻¹' {x}) :
    FundamentalGroup (AddCircle p) x ≃* Multiplicative (zmultiples p) :=
  (Deck.isRegular_addCircleCoe.fundamentalGroupDeckEquiv hcov e
    (fun a b => Deck.addCircleMulEquiv.symm.injective (by simp [mul_comm]))).trans
    Deck.addCircleMulEquiv.symm

/-- Characterization of the period-subgroup element assigned by
`fundamentalGroupMulEquivZMultiples`: a loop class maps to `n` exactly when its monodromy
translate of the chosen lift differs by the element `n`. -/
lemma fundamentalGroupMulEquivZMultiples_apply_eq_iff (hcov : IsCoveringMap ((↑) : 𝕜 → AddCircle p))
    {x : AddCircle p} (e : ((↑) : 𝕜 → AddCircle p) ⁻¹' {x})
    (γ : FundamentalGroup (AddCircle p) x) (n : Multiplicative (zmultiples p)) :
    fundamentalGroupMulEquivZMultiples hcov e γ = n ↔
      (hcov.monodromy γ.toPath e : 𝕜) = (e : 𝕜) + (n.toAdd : 𝕜) := by
  rw [fundamentalGroupMulEquivZMultiples, MulEquiv.trans_apply, MulEquiv.symm_apply_eq,
    Deck.IsRegular.fundamentalGroupDeckEquiv_apply_eq_iff]
  simp only [deck.smul_eq_apply, Deck.addCircleMulEquiv_apply,
    Deck.addRightZMultiples_apply, eq_comm]

/-- The inverse of the period-subgroup equivalence sends `n` to the loop class whose monodromy
translates the chosen lift by `n`. -/
@[simp]
lemma fundamentalGroupMulEquivZMultiples_symm_monodromy
    (hcov : IsCoveringMap ((↑) : 𝕜 → AddCircle p))
    {x : AddCircle p} (e : ((↑) : 𝕜 → AddCircle p) ⁻¹' {x}) (n : Multiplicative (zmultiples p)) :
    (hcov.monodromy ((fundamentalGroupMulEquivZMultiples hcov e).symm n).toPath e : 𝕜) =
      (e : 𝕜) + (n.toAdd : 𝕜) := by
  exact (fundamentalGroupMulEquivZMultiples_apply_eq_iff hcov e
    ((fundamentalGroupMulEquivZMultiples hcov e).symm n) n).1
      (MulEquiv.apply_symm_apply _ _)

/-- A loop class maps to `1` under the period-subgroup equivalence exactly when its monodromy
fixes the chosen lift. -/
lemma fundamentalGroupMulEquivZMultiples_eq_one_iff (hcov : IsCoveringMap ((↑) : 𝕜 → AddCircle p))
    {x : AddCircle p} (e : ((↑) : 𝕜 → AddCircle p) ⁻¹' {x}) (γ : FundamentalGroup (AddCircle p) x) :
    fundamentalGroupMulEquivZMultiples hcov e γ = 1 ↔ hcov.monodromy γ.toPath e = e := by
  rw [fundamentalGroupMulEquivZMultiples_apply_eq_iff]
  simpa using (Iff.symm Subtype.ext_iff :
    ((hcov.monodromy γ.toPath e : 𝕜) = (e : 𝕜) ↔ hcov.monodromy γ.toPath e = e))

/-- For a covering projection `(↑) : 𝕜 → AddCircle p` from a simply connected preconnected
topological additive commutative group with totally disconnected non-torsion period subgroup,
the fundamental group of `AddCircle p` is infinite cyclic:
`FundamentalGroup (AddCircle p) x ≃* Multiplicative ℤ`. -/
noncomputable def fundamentalGroupMulEquivInt
    (hcov : IsCoveringMap ((↑) : 𝕜 → AddCircle p)) (hp : ¬ IsOfFinAddOrder p)
    {x : AddCircle p} (e : ((↑) : 𝕜 → AddCircle p) ⁻¹' {x}) :
    FundamentalGroup (AddCircle p) x ≃* Multiplicative ℤ :=
  (fundamentalGroupMulEquivZMultiples hcov e).trans (intEquivZMultiples hp).toMultiplicative.symm

/-- Characterization of the integer assigned by `fundamentalGroupMulEquivInt`: a loop
class maps to `n` exactly when its monodromy translate of the chosen lift differs by `n • p`. -/
lemma fundamentalGroupMulEquivInt_apply_eq_iff
    (hcov : IsCoveringMap ((↑) : 𝕜 → AddCircle p)) (hp : ¬ IsOfFinAddOrder p)
    {x : AddCircle p} (e : ((↑) : 𝕜 → AddCircle p) ⁻¹' {x})
    (γ : FundamentalGroup (AddCircle p) x) (n : Multiplicative ℤ) :
    fundamentalGroupMulEquivInt hcov hp e γ = n ↔
      (hcov.monodromy γ.toPath e : 𝕜) = (e : 𝕜) + n.toAdd • p := by
  dsimp [fundamentalGroupMulEquivInt]
  rw [MulEquiv.symm_apply_eq]
  simpa using fundamentalGroupMulEquivZMultiples_apply_eq_iff hcov e γ
    ((intEquivZMultiples hp).toMultiplicative n)

/-- The inverse generic integer equivalence sends `n` to the loop class whose monodromy
translates the chosen lift by `n • p`. -/
@[simp]
lemma fundamentalGroupMulEquivInt_symm_monodromy
    (hcov : IsCoveringMap ((↑) : 𝕜 → AddCircle p)) (hp : ¬ IsOfFinAddOrder p)
    {x : AddCircle p} (e : ((↑) : 𝕜 → AddCircle p) ⁻¹' {x}) (n : Multiplicative ℤ) :
    (hcov.monodromy ((fundamentalGroupMulEquivInt hcov hp e).symm n).toPath e : 𝕜) =
      (e : 𝕜) + n.toAdd • p := by
  exact (fundamentalGroupMulEquivInt_apply_eq_iff hcov hp e
    ((fundamentalGroupMulEquivInt hcov hp e).symm n) n).1
      (MulEquiv.apply_symm_apply _ _)

/-- A loop class maps to `1` under the generic integer equivalence exactly when its monodromy
fixes the chosen lift. -/
lemma fundamentalGroupMulEquivInt_eq_one_iff
    (hcov : IsCoveringMap ((↑) : 𝕜 → AddCircle p)) (hp : ¬ IsOfFinAddOrder p)
    {x : AddCircle p} (e : ((↑) : 𝕜 → AddCircle p) ⁻¹' {x}) (γ : FundamentalGroup (AddCircle p) x) :
    fundamentalGroupMulEquivInt hcov hp e γ = 1 ↔ hcov.monodromy γ.toPath e = e := by
  rw [fundamentalGroupMulEquivInt_apply_eq_iff]
  simpa using (Iff.symm Subtype.ext_iff :
    ((hcov.monodromy γ.toPath e : 𝕜) = (e : 𝕜) ↔ hcov.monodromy γ.toPath e = e))

variable (p : ℝ)

/-- For a nonzero real period `p`, the fundamental group of the circle `AddCircle p`, based at
any point `x` with a chosen lift `e : (↑) ⁻¹' {x}`, is infinite cyclic:
`FundamentalGroup (AddCircle p) x ≃* Multiplicative ℤ`. -/
noncomputable def fundamentalGroupMulEquiv (hp : p ≠ 0) {x : AddCircle p}
    (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) :
    FundamentalGroup (AddCircle p) x ≃* Multiplicative ℤ :=
  fundamentalGroupMulEquivInt (AddCircle.isCoveringMap_coe p)
    (not_isOfFinAddOrder_of_isAddTorsionFree hp) e

/-- Characterization of the integer assigned by `fundamentalGroupMulEquiv`: a loop class maps
to `n` exactly when its monodromy translate of the chosen lift differs by `n • p`. -/
lemma fundamentalGroupMulEquiv_apply_eq_iff (hp : p ≠ 0) {x : AddCircle p}
    (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) (γ : FundamentalGroup (AddCircle p) x)
    (n : Multiplicative ℤ) :
    fundamentalGroupMulEquiv p hp e γ = n ↔
      ((AddCircle.isCoveringMap_coe p).monodromy γ.toPath e : ℝ) = (e : ℝ) + n.toAdd • p :=
  fundamentalGroupMulEquivInt_apply_eq_iff (AddCircle.isCoveringMap_coe p)
    (not_isOfFinAddOrder_of_isAddTorsionFree hp) e γ n

/-- The inverse equivalence sends `n` to the loop class whose monodromy translates the chosen
lift by `n • p`. -/
@[simp]
lemma fundamentalGroupMulEquiv_symm_monodromy (hp : p ≠ 0) {x : AddCircle p}
    (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) (n : Multiplicative ℤ) :
    ((AddCircle.isCoveringMap_coe p).monodromy ((fundamentalGroupMulEquiv p hp e).symm n).toPath e :
      ℝ) = (e : ℝ) + n.toAdd • p :=
  fundamentalGroupMulEquivInt_symm_monodromy (AddCircle.isCoveringMap_coe p)
    (not_isOfFinAddOrder_of_isAddTorsionFree hp) e n

/-- A loop class maps to `1` under `fundamentalGroupMulEquiv` exactly when its monodromy fixes
the chosen lift. -/
lemma fundamentalGroupMulEquiv_eq_one_iff (hp : p ≠ 0) {x : AddCircle p}
    (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) (γ : FundamentalGroup (AddCircle p) x) :
    fundamentalGroupMulEquiv p hp e γ = 1 ↔
      (AddCircle.isCoveringMap_coe p).monodromy γ.toPath e = e :=
  fundamentalGroupMulEquivInt_eq_one_iff (AddCircle.isCoveringMap_coe p)
    (not_isOfFinAddOrder_of_isAddTorsionFree hp) e γ

/-- The fundamental group of the circle `AddCircle p` based at `0`, with the lift `0 : ℝ`, is
`Multiplicative ℤ`. -/
noncomputable def fundamentalGroupMulEquivZero (hp : p ≠ 0) :
    FundamentalGroup (AddCircle p) 0 ≃* Multiplicative ℤ :=
  fundamentalGroupMulEquiv p hp ⟨0, by simp⟩

/-- Characterization of the integer assigned by the basepoint-`0` specialization. -/
lemma fundamentalGroupMulEquivZero_apply_eq_iff (hp : p ≠ 0)
    (γ : FundamentalGroup (AddCircle p) 0) (n : Multiplicative ℤ) :
    fundamentalGroupMulEquivZero p hp γ = n ↔
      ((AddCircle.isCoveringMap_coe p).monodromy γ.toPath ⟨0, by simp⟩ : ℝ) = n.toAdd • p := by
  rw [fundamentalGroupMulEquivZero]
  simpa using fundamentalGroupMulEquiv_apply_eq_iff p hp ⟨0, by simp⟩ γ n

@[simp]
lemma fundamentalGroupMulEquivZero_apply (hp : p ≠ 0) (γ : FundamentalGroup (AddCircle p) 0) :
    fundamentalGroupMulEquivZero p hp γ = fundamentalGroupMulEquiv p hp ⟨0, by simp⟩ γ := by
  apply (fundamentalGroupMulEquivZero_apply_eq_iff p hp γ _).2
  simpa using (fundamentalGroupMulEquiv_apply_eq_iff p hp ⟨0, by simp⟩ γ _).1 rfl

@[simp]
lemma fundamentalGroupMulEquivZero_symm_apply (hp : p ≠ 0) (n : Multiplicative ℤ) :
    (fundamentalGroupMulEquivZero p hp).symm n =
      (fundamentalGroupMulEquiv p hp ⟨0, by simp⟩).symm n := by
  apply (fundamentalGroupMulEquivZero p hp).injective
  rw [MulEquiv.apply_symm_apply, fundamentalGroupMulEquivZero_apply, MulEquiv.apply_symm_apply]

/-- The inverse of the basepoint-`0` specialization has monodromy translation `n • p`. -/
lemma fundamentalGroupMulEquivZero_symm_monodromy (hp : p ≠ 0) (n : Multiplicative ℤ) :
    ((AddCircle.isCoveringMap_coe p).monodromy ((fundamentalGroupMulEquivZero p hp).symm n).toPath
      ⟨0, by simp⟩ : ℝ) = n.toAdd • p := by
  rw [fundamentalGroupMulEquivZero]
  simp

/-- A loop class maps to `1` under the basepoint-`0` specialization exactly when its monodromy
fixes the zero lift. -/
lemma fundamentalGroupMulEquivZero_eq_one_iff (hp : p ≠ 0) (γ : FundamentalGroup (AddCircle p) 0) :
    fundamentalGroupMulEquivZero p hp γ = 1 ↔
      (AddCircle.isCoveringMap_coe p).monodromy γ.toPath ⟨0, by simp⟩ = ⟨0, by simp⟩ := by
  rw [fundamentalGroupMulEquivZero]
  exact fundamentalGroupMulEquiv_eq_one_iff p hp ⟨0, by simp⟩ γ

/-- For positive periods, the chosen-lift equivalence agrees with Mathlib's winding-number
isomorphism. In particular it is independent of the chosen lift and has the same orientation. -/
lemma fundamentalGroupMulEquiv_eq_windingNumberIso [hp : Fact (0 < p)] {x : AddCircle p}
    (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) :
    fundamentalGroupMulEquiv p hp.out.ne' e = windingNumberIso x := by
  ext ⟨γ⟩ : 1
  induction γ using Path.Homotopic.Quotient.ind with
  | _ γ =>
    obtain ⟨f, hf, hf0⟩ := (isCoveringMap_coe p).exists_path_lifts γ.toContinuousMap e
      (γ.source.trans e.2.symm)
    have hm := (isCoveringMap_coe p).monodromy_eq_apply_one hf hf0
    have hn := (fundamentalGroupMulEquiv_apply_eq_iff p hp.out.ne' e
      (FundamentalGroup.fromPath (.mk γ)) _).mp rfl
    rw [hm] at hn
    apply Multiplicative.toAdd.injective
    apply Int.cast_injective (α := ℝ)
    have hw := windingNumber_eq_div γ f hf
    rw [hf0, hn, zsmul_eq_mul] at hw
    simpa [windingNumber, hp.out.ne'] using hw.symm

/-- Mathlib's winding-number isomorphism sends a loop class to `n` exactly when monodromy
translates any chosen lift by `n • p`. -/
lemma windingNumberIso_apply_eq_iff [hp : Fact (0 < p)] {x : AddCircle p}
    (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) (γ : FundamentalGroup (AddCircle p) x)
    (n : Multiplicative ℤ) :
    windingNumberIso x γ = n ↔
      ((isCoveringMap_coe p).monodromy γ.toPath e : ℝ) = (e : ℝ) + n.toAdd • p := by
  rw [← fundamentalGroupMulEquiv_eq_windingNumberIso p e]
  exact fundamentalGroupMulEquiv_apply_eq_iff p hp.out.ne' e γ n

end AddCircle

namespace UnitAddCircle

/-- Characterization of the integer assigned by the unit-circle equivalence. -/
lemma windingNumberIso_apply_eq_iff (γ : FundamentalGroup UnitAddCircle 0)
    (n : Multiplicative ℤ) :
    AddCircle.windingNumberIso (p := 1) 0 γ = n ↔
      ((AddCircle.isCoveringMap_coe 1).monodromy γ.toPath ⟨0, by simp⟩ : ℝ) = n.toAdd := by
  simpa using AddCircle.windingNumberIso_apply_eq_iff 1 ⟨0, by simp⟩ γ n

/-- The inverse of the unit-circle equivalence has monodromy translation by `n`. -/
@[simp]
lemma windingNumberIso_symm_monodromy (n : Multiplicative ℤ) :
    ((AddCircle.isCoveringMap_coe 1).monodromy
      ((AddCircle.windingNumberIso (p := 1) 0).symm n).toPath ⟨0, by simp⟩ : ℝ) = n.toAdd := by
  exact (windingNumberIso_apply_eq_iff _ n).mp (MulEquiv.apply_symm_apply _ _)

/-- A unit-circle loop class maps to `1` exactly when its monodromy fixes the zero lift. -/
lemma windingNumberIso_eq_one_iff (γ : FundamentalGroup UnitAddCircle 0) :
    AddCircle.windingNumberIso (p := 1) 0 γ = 1 ↔
      (AddCircle.isCoveringMap_coe 1).monodromy γ.toPath ⟨0, by simp⟩ = ⟨0, by simp⟩ := by
  rw [windingNumberIso_apply_eq_iff]
  constructor
  · intro h
    apply Subtype.ext
    simpa using h
  · intro h
    simpa using congrArg Subtype.val h

end UnitAddCircle

noncomputable section

namespace Circle

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- The fundamental group of the complex unit circle `Circle = {z : ℂ | ‖z‖ = 1}`, based at
`x`, is `Multiplicative ℤ`: `π₁(S¹, x) ≅ ℤ`. It is obtained by changing the basepoint to
`1 : Circle`, then transporting the additive-circle computation at `0` across
`AddCircle.homeomorphCircle : AddCircle (2 * π) ≃ₜ Circle`. -/
def fundamentalGroupMulEquiv (x : Circle) : FundamentalGroup Circle x ≃* Multiplicative ℤ :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x 1).trans
    ((TauCeti.FundamentalGroup.homeomorphMulEquivOfEq
          (AddCircle.homeomorphCircle (T := 2 * Real.pi) Real.two_pi_pos.ne').symm
          (AddCircle.homeomorphCircle_symm_one Real.two_pi_pos.ne')).trans
      (AddCircle.windingNumberIso (p := 2 * Real.pi) 0))

/-- `fundamentalGroupMulEquiv` factors as Mathlib's basepoint-change isomorphism
`FundamentalGroup Circle x ≃* FundamentalGroup Circle 1`, followed by the canonical-basepoint
computation transported from `AddCircle (2 * π)` along `AddCircle.homeomorphCircle`. -/
theorem fundamentalGroupMulEquiv_def (x : Circle) :
    fundamentalGroupMulEquiv x =
      (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x 1).trans
        ((TauCeti.FundamentalGroup.homeomorphMulEquivOfEq
          (AddCircle.homeomorphCircle (T := 2 * Real.pi) Real.two_pi_pos.ne').symm
            (AddCircle.homeomorphCircle_symm_one Real.two_pi_pos.ne')).trans
          (AddCircle.windingNumberIso (p := 2 * Real.pi) 0)) :=
  (rfl)

/-- **The angle lift computes the monodromy.** Transport a loop `γ` at `1 : Circle` to
`AddCircle (2 * π)` along `AddCircle.homeomorphCircle`. Its monodromy carries the lift `0` of the
basepoint to the endpoint of any continuous angle lift `θ` of `γ` starting at `0`. -/
private theorem monodromy_homeomorphMulEquivOfEq_fromPath (γ : Path (1 : Circle) 1) {a : ℝ}
    (θ : Path (0 : ℝ) a) (hθ : ∀ t, exp (θ t) = γ t) :
    ((AddCircle.isCoveringMap_coe (2 * Real.pi)).monodromy
      ((TauCeti.FundamentalGroup.homeomorphMulEquivOfEq
        (AddCircle.homeomorphCircle (T := 2 * Real.pi) Real.two_pi_pos.ne').symm
          (AddCircle.homeomorphCircle_symm_one Real.two_pi_pos.ne'))
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))).toPath
      ⟨0, by simp⟩ : ℝ) = a := by
  -- The additive-circle point of an angle `r` corresponds to `exp r` on the complex circle.
  have hcoe (r : ℝ) : ((r : ℝ) : AddCircle (2 * Real.pi)) =
      (AddCircle.homeomorphCircle Real.two_pi_pos.ne').symm (exp r) := by
    rw [Homeomorph.eq_symm_apply, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
    congr 1
    field_simp
  have ha : a ∈ ((↑) : ℝ → AddCircle (2 * Real.pi)) ⁻¹' {0} := by
    rw [Set.mem_preimage, Set.mem_singleton_iff, hcoe, ← θ.target, hθ, γ.target,
      AddCircle.homeomorphCircle_symm_one]
  refine congrArg Subtype.val ((AddCircle.isCoveringMap_coe (2 * Real.pi)).monodromy_eq_of_map_eq
    (ey := ⟨a, ha⟩) (Path.Homotopic.Quotient.mk θ) ?_)
  rw [TauCeti.FundamentalGroup.homeomorphMulEquivOfEq_apply, FundamentalGroup.mapOfEq_apply,
    ← Path.Homotopic.Quotient.mk_map]
  -- Casting a path class casts its representative, and `Path.cast` does not change the
  -- underlying function. Both are unfolded definitionally rather than by `mk_cast` and
  -- `Path.cast_coe`, because the endpoint proofs supplied by `monodromy_eq_of_map_eq` are fibre
  -- memberships, which `rw` and `simp` cannot see as the endpoint equations `cast` expects.
  refine congrArg Path.Homotopic.Quotient.mk (Path.ext (funext fun t => ?_))
  have ht : ((θ t : ℝ) : AddCircle (2 * Real.pi)) =
      (AddCircle.homeomorphCircle Real.two_pi_pos.ne').symm (γ t) := by
    rw [hcoe, hθ]
  exact ht

/-- **The degree at the basepoint `1`.** The additive-circle computation, transported to `Circle`
along `AddCircle.homeomorphCircle`, sends the class of a loop at `1` to its degree. -/
private theorem homeomorphMulEquivOfEq_trans_windingNumberIso_fromPath
    (γ : Path (1 : Circle) 1) :
    ((TauCeti.FundamentalGroup.homeomorphMulEquivOfEq
          (AddCircle.homeomorphCircle (T := 2 * Real.pi) Real.two_pi_pos.ne').symm
          (AddCircle.homeomorphCircle_symm_one Real.two_pi_pos.ne')).trans
      (AddCircle.windingNumberIso (p := 2 * Real.pi) 0))
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) =
      Multiplicative.ofAdd (degree γ) := by
  rw [MulEquiv.trans_apply, AddCircle.windingNumberIso_apply_eq_iff (2 * Real.pi) ⟨0, by simp⟩]
  simp only [zero_add]
  obtain ⟨θ, hθ, hθ0⟩ := isCoveringMap_exp.exists_path_lifts γ.toContinuousMap 0 (by simp)
  have hθγ (t : unitInterval) : exp (θ t) = γ t := congr_fun hθ t
  rw [monodromy_homeomorphMulEquivOfEq_fromPath γ ⟨θ, hθ0, rfl⟩ hθγ]
  simpa [hθ0, zsmul_eq_mul] using sub_eq_degree_mul γ θ.continuous hθγ

/-- **The isomorphism `π₁(S¹) ≃* ℤ` is the degree.** The class of a loop is sent to its degree
`Circle.degree`, the number of full turns of any continuous angle lift. -/
theorem fundamentalGroupMulEquiv_fromPath {x : Circle} (γ : Path x x) :
    fundamentalGroupMulEquiv x (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) =
      Multiplicative.ofAdd (degree γ) := by
  -- Changing the basepoint to `1` along a path `p` replaces `γ` by `p⁻¹ ⬝ γ ⬝ p`, of the same
  -- degree.
  rw [fundamentalGroupMulEquiv_def, MulEquiv.trans_apply,
    FundamentalGroup.fundamentalGroupMulEquivOfPathConnected,
    FundamentalGroup.fundamentalGroupMulEquivOfPath_apply]
  exact (homeomorphMulEquivOfEq_trans_windingNumberIso_fromPath _).trans
    (congrArg Multiplicative.ofAdd (degree_symm_trans_trans γ _))

/-- The loop `t ↦ exp(2πit)` at `1`, going once counterclockwise around the unit circle. -/
def expLoop : Path (1 : Circle) 1 where
  toFun t := Circle.exp (2 * Real.pi * t)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

@[simp]
theorem expLoop_apply (t : unitInterval) : expLoop t = Circle.exp (2 * Real.pi * t) :=
  (rfl)

/-- **The counterclockwise loop generates `π₁(S¹)` positively.** The isomorphism
`π₁(Circle, 1) ≃* Multiplicative ℤ` sends the class of `t ↦ exp(2πit)` to `ofAdd 1`. -/
@[simp]
theorem fundamentalGroupMulEquiv_expLoop :
    fundamentalGroupMulEquiv 1
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk expLoop)) =
      Multiplicative.ofAdd 1 := by
  rw [fundamentalGroupMulEquiv_fromPath,
    degree_eq_of_sub_eq expLoop (θ := fun t => 2 * Real.pi * t) (by fun_prop) (fun _ => rfl)
      (n := 1) (by simp)]

/-- A loop `γ`, read as a map from the circle by `Path.toCircle`, sends the class of the
counterclockwise loop `expLoop` to the class of `γ`. So every element of a fundamental group is
the image of the generator of `π₁(S¹)` under a based map from the circle. -/
theorem mapOfEq_toCircle_expLoop {X : Type*} [TopologicalSpace X] {x : X} (γ : Path x x) :
    FundamentalGroup.mapOfEq γ.toCircle γ.toCircle_one
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk expLoop)) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) := by
  have h : (expLoop.map γ.toCircle.continuous).cast γ.toCircle_one.symm γ.toCircle_one.symm =
      γ := by
    ext t
    exact γ.toCircle_exp t
  conv_rhs => rw [← h, Path.Homotopic.Quotient.mk_cast, Path.Homotopic.Quotient.mk_map]
  exact FundamentalGroup.mapOfEq_apply _ _ _

/-- **The `n`-th power map of the circle acts on `π₁(S¹) ≅ ℤ` as multiplication by `n`.** The
isomorphism `fundamentalGroupMulEquiv` sends the image of a loop class under `z ↦ z ^ n` to the
`n`-th power of the image of the class. -/
theorem fundamentalGroupMulEquiv_map_pow (n : ℕ) {x : Circle} (γ : FundamentalGroup Circle x) :
    fundamentalGroupMulEquiv _ (FundamentalGroup.map ⟨(· ^ n), continuous_pow n⟩ x γ) =
      fundamentalGroupMulEquiv x γ ^ n := by
  obtain ⟨γ⟩ := γ
  induction γ using Path.Homotopic.Quotient.ind with | mk γ => ?_
  calc _ = Multiplicative.ofAdd (degree (γ.map (continuous_pow n))) :=
        fundamentalGroupMulEquiv_fromPath _
    _ = Multiplicative.ofAdd (degree γ) ^ n := by
        rw [degree_map_pow, ← ofAdd_nsmul, nsmul_eq_mul]
    _ = _ := congrArg (· ^ n) (fundamentalGroupMulEquiv_fromPath γ).symm

section Detect

variable {X : Type*} [TopologicalSpace X] {d : C(X, Circle)}

/-- **A loop of degree one generates.** If `d : X → Circle` induces an injection of fundamental
groups at `x`, then the class of a loop at `x` whose image under `d` has degree `1` generates
`π₁(X, x)`. -/
theorem zpowers_fromPath_eq_top_of_degree_map_eq_one {x : X}
    (hd : Function.Injective (FundamentalGroup.map d x)) {γ : Path x x}
    (hγ : degree (γ.map d.continuous) = 1) :
    Subgroup.zpowers (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) = ⊤ := by
  have h : fundamentalGroupMulEquiv _
      (FundamentalGroup.map d x (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))) =
        Multiplicative.ofAdd 1 := by
    rw [FundamentalGroup.map_fromPath d x γ, fundamentalGroupMulEquiv_fromPath, hγ]
  refine (Subgroup.eq_top_iff' _).mpr fun g =>
    ⟨(fundamentalGroupMulEquiv _ (FundamentalGroup.map d x g)).toAdd,
      hd ((fundamentalGroupMulEquiv _).injective ?_)⟩
  rw [map_zpow, map_zpow, h, ← ofAdd_zsmul, zsmul_one, Int.cast_id, ofAdd_toAdd]

/-- **Loops whose images have the same degree are conjugate.** If `d : X → Circle` induces an
injection of fundamental groups at `x`, and the images under `d` of a loop `γ` at `x` and a loop
`δ` at `y` have the same degree, then `γ` is homotopic to `δ` conjugated by any path `α` from `x`
to `y`. -/
theorem homotopic_trans_of_degree_map_eq {x y : X}
    (hd : Function.Injective (FundamentalGroup.map d x)) {γ : Path x x} {δ : Path y y}
    (h : degree (γ.map d.continuous) = degree (δ.map d.continuous)) (α : Path x y) :
    γ.Homotopic (α.trans (δ.trans α.symm)) := by
  refine Path.Homotopic.Quotient.exact (congrArg CategoryTheory.End.asHom
    (@hd (FundamentalGroup.fromPath (.mk γ))
      (FundamentalGroup.fromPath (.mk (α.trans (δ.trans α.symm))))
      ((fundamentalGroupMulEquiv _).injective ?_)))
  rw [FundamentalGroup.map_fromPath d x γ, FundamentalGroup.map_fromPath d x _,
    fundamentalGroupMulEquiv_fromPath,
    fundamentalGroupMulEquiv_fromPath, Path.map_trans, Path.map_trans, ← Path.map_symm, h]
  -- Conjugating by the image of `α` does not change the degree.
  simpa using (degree_symm_trans_trans (δ.map d.continuous) (α.map d.continuous).symm).symm

end Detect

end Circle

end
