/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.FreeLoop
public import TauCeti.AlgebraicTopology.UniversalCover.Circle.FundamentalGroup
public import TauCeti.Topology.Circle.FreeLoop

/-!
# Path components of the free loop space of the circle

The path components of the free loop space `C(S¹, S¹)` are indexed by the winding number: a free
loop `f` has the degree `ContinuousMap.circleDegree f` of its loop `t ↦ f(e^{2πit})`, and two
free loops are joined by a path in `C(S¹, S¹)` exactly when they have the same degree
(`Circle.joined_iff_circleDegree_eq`). Every integer is a degree, so

`π₀(C(S¹, S¹)) ≃ ℤ` (`Circle.freeLoopComponentsEquivInt`),

and the same holds for the Moore free loop space (`Circle.mooreFreeLoopComponentsEquivInt`).

The degree is locally constant on `C(S¹, S¹)` (`ContinuousMap.continuous_circleDegree`), hence
constant along paths (`Joined.circleDegree_eq`), which is one direction. For the other, each free
loop is joined to a loop at `1` (`ContinuousMap.joined_toCircle_trans_trans_symm_toBasedLoop`), and
loops at `1` of equal degree have the same class in `π₁(S¹, 1) ≅ ℤ`
(`Circle.fundamentalGroupMulEquiv_fromPath`), hence are joined (`Path.joined_toCircle_iff_isConj`).

## Main declarations

* `Circle.joined_iff_circleDegree_eq`: free loops of the circle are joined exactly when they
  have the same degree.
* `ContinuousMap.circleDegree_zpow`: the free loop `ζ ↦ ζⁿ` has degree `n`.
* `Circle.freeLoopComponentsEquivInt`: `π₀(C(S¹, S¹)) ≃ ℤ`, by the degree.
* `Circle.mooreFreeLoopComponentsEquivInt`: the same for the Moore free loop space.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §1.1.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4 (the components of `𝓛S¹`).
-/

public section

noncomputable section

namespace Circle

open TauCeti

/-- **The degree is constant on path components of the free loop space.** -/
theorem _root_.Joined.circleDegree_eq {f g : C(Circle, Circle)} (h : Joined f g) :
    f.circleDegree = g.circleDegree := by
  -- the degree is locally constant, hence constant along a path from `f` to `g`
  simpa using
    (ContinuousMap.continuous_circleDegree.comp h.somePath.continuous).isConst_of_preconnectedSpace
      0 1

/-- The free loop `ζ ↦ ζⁿ` of the circle has degree `n`. -/
@[simp]
theorem _root_.ContinuousMap.circleDegree_zpow (n : ℤ) :
    (⟨(· ^ n), continuous_zpow n⟩ : C(Circle, Circle)).circleDegree = n := by
  rw [← degree_toBasedLoop]
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [degree_congr _ (expLoop.map (continuous_pow k)) fun t ↦ by
        rw [ContinuousMap.toBasedLoop_apply]
        simp [unitToCircle_apply],
      degree_map_pow, degree_expLoop, mul_one]
  · rw [degree_congr _ (expLoop.map (continuous_pow k)).inv fun t ↦ by
        rw [ContinuousMap.toBasedLoop_apply]
        simp [unitToCircle_apply],
      degree_inv, degree_map_pow, degree_expLoop, mul_one]

/-- **Free loops of the circle are classified by their degree.** Two maps `S¹ → S¹` are joined by
a path in `C(S¹, S¹)` exactly when they have the same degree. -/
theorem joined_iff_circleDegree_eq {f g : C(Circle, Circle)} :
    Joined f g ↔ f.circleDegree = g.circleDegree := by
  refine ⟨Joined.circleDegree_eq, fun hfg ↦ ?_⟩
  -- Move both free loops to loops at `1`, where the degree detects the class in `π₁(S¹, 1)`.
  let χf := PathConnectedSpace.somePath (1 : Circle) (f 1)
  let χg := PathConnectedSpace.somePath (1 : Circle) (g 1)
  have hf := f.joined_toCircle_trans_trans_symm_toBasedLoop χf
  have hg := g.joined_toCircle_trans_trans_symm_toBasedLoop χg
  have hdeg : degree ((χf.trans f.toBasedLoop).trans χf.symm) =
      degree ((χg.trans g.toBasedLoop).trans χg.symm) := by
    rw [← ContinuousMap.circleDegree_toCircle, hf.circleDegree_eq, hfg, ← hg.circleDegree_eq,
      ContinuousMap.circleDegree_toCircle]
  have hπ := congrArg Multiplicative.ofAdd hdeg
  rw [← fundamentalGroupMulEquiv_fromPath, ← fundamentalGroupMulEquiv_fromPath] at hπ
  exact (hf.symm.trans (Path.joined_toCircle_iff_isConj.2
    (((fundamentalGroupMulEquiv 1).injective hπ) ▸ IsConj.refl _))).trans hg

/-- **The path components of the free loop space of the circle are the integers**, by the degree
of the free loops: `π₀(C(S¹, S¹)) ≃ ℤ`. -/
def freeLoopComponentsEquivInt : ZerothHomotopy C(Circle, Circle) ≃ ℤ :=
  Equiv.ofBijective
    (Quotient.lift ContinuousMap.circleDegree fun _ _ h ↦ h.circleDegree_eq)
    ⟨fun c d h ↦ by
      obtain ⟨f, rfl⟩ := ZerothHomotopy.mk_surjective c
      obtain ⟨g, rfl⟩ := ZerothHomotopy.mk_surjective d
      exact Quotient.sound (joined_iff_circleDegree_eq.2 h),
    fun n ↦ by
      obtain ⟨⟨γ⟩, hγ⟩ := (fundamentalGroupMulEquiv (1 : Circle)).surjective (.ofAdd n)
      induction γ using Path.Homotopic.Quotient.ind with | mk γ => ?_
      refine ⟨ZerothHomotopy.mk γ.toCircle, ?_⟩
      -- `ZerothHomotopy.mk` is the quotient map, on which `Quotient.lift` computes; the
      -- characterizing lemma `freeLoopComponentsEquivInt_mk` is stated only after this definition.
      change γ.toCircle.circleDegree = n
      rw [ContinuousMap.circleDegree_toCircle, ← Multiplicative.ofAdd.injective.eq_iff,
        ← fundamentalGroupMulEquiv_fromPath]
      exact hγ⟩

@[simp]
theorem freeLoopComponentsEquivInt_mk (f : C(Circle, Circle)) :
    freeLoopComponentsEquivInt (.mk f) = f.circleDegree :=
  (rfl)

theorem freeLoopComponentsEquivInt_mk_toCircle {x : Circle} (γ : Path x x) :
    freeLoopComponentsEquivInt (.mk γ.toCircle) = degree γ := by
  simp

/-- The path components of the Moore free loop space of the circle are the integers, through the
homotopy equivalence with `C(S¹, S¹)`. -/
def mooreFreeLoopComponentsEquivInt : ZerothHomotopy (MooreFreeLoopSpace Circle) ≃ ℤ :=
  (MooreFreeLoopSpace.homotopyEquivCircleMap Circle).zerothHomotopyCongr.trans
    freeLoopComponentsEquivInt

@[simp]
theorem mooreFreeLoopComponentsEquivInt_mk (γ : MooreFreeLoopSpace Circle) :
    mooreFreeLoopComponentsEquivInt (.mk γ) =
      (MooreFreeLoopSpace.toCircleMap γ).circleDegree := by
  simp [mooreFreeLoopComponentsEquivInt]

end Circle
