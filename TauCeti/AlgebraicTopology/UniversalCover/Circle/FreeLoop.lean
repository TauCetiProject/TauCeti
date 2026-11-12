/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.FreeLoop
public import TauCeti.AlgebraicTopology.UniversalCover.Circle.FundamentalGroup

/-!
# Path components of the free loop space of the circle

The path components of the free loop space `C(S¹, S¹)` are indexed by the winding number: a free
loop `f` has the degree `Circle.degree f.toBasedLoop` of its loop `t ↦ f(e^{2πit})`, and two free
loops are joined by a path in `C(S¹, S¹)` exactly when they have the same degree
(`Circle.joined_iff_degree_toBasedLoop_eq`). Every integer is a degree, so

`π₀(C(S¹, S¹)) ≃ ℤ` (`Circle.freeLoopComponentsEquivInt`),

and the same holds for the Moore free loop space (`Circle.mooreFreeLoopComponentsEquivInt`).

The degree is invariant under homotopies through loops (`Circle.degree_eq_of_homotopy`), which is
one direction. For the other, each free loop is joined to a loop at `1`
(`ContinuousMap.joined_toCircle_trans_trans_symm_toBasedLoop`), and loops at `1` of equal degree
have the same class in `π₁(S¹, 1) ≅ ℤ` (`Circle.fundamentalGroupMulEquiv_fromPath`), hence are
joined (`Path.joined_toCircle_iff_isConj`).

## Main declarations

* `Circle.joined_iff_degree_toBasedLoop_eq`: free loops of the circle are joined exactly when they
  have the same degree.
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

/-- The loop at the base point of a loop read as a map from the circle has the degree of the
loop. -/
@[simp]
theorem degree_toBasedLoop_toCircle {x : Circle} (γ : Path x x) :
    degree γ.toCircle.toBasedLoop = degree γ :=
  degree_congr _ _ fun t ↦ by simp

/-- **The degree is constant on path components of the free loop space.** -/
theorem degree_toBasedLoop_eq_of_joined {f g : C(Circle, Circle)} (h : Joined f g) :
    degree f.toBasedLoop = degree g.toBasedLoop := by
  rw [← f.toBasedLoop_toCircle, ← g.toBasedLoop_toCircle,
    Path.joined_toCircle_iff_homotopicWith] at h
  obtain ⟨H⟩ := h
  exact degree_eq_of_homotopy _ _ H.toContinuousMap (fun t ↦ H.apply_zero t)
    (fun t ↦ H.apply_one t) H.prop

/-- **Free loops of the circle are classified by their degree.** Two maps `S¹ → S¹` are joined by
a path in `C(S¹, S¹)` exactly when they have the same degree. -/
theorem joined_iff_degree_toBasedLoop_eq {f g : C(Circle, Circle)} :
    Joined f g ↔ degree f.toBasedLoop = degree g.toBasedLoop := by
  refine ⟨degree_toBasedLoop_eq_of_joined, fun hfg ↦ ?_⟩
  -- Move both free loops to loops at `1`, where the degree detects the class in `π₁(S¹, 1)`.
  let χf := PathConnectedSpace.somePath (1 : Circle) (f 1)
  let χg := PathConnectedSpace.somePath (1 : Circle) (g 1)
  have hf := f.joined_toCircle_trans_trans_symm_toBasedLoop χf
  have hg := g.joined_toCircle_trans_trans_symm_toBasedLoop χg
  have hdeg : degree ((χf.trans f.toBasedLoop).trans χf.symm) =
      degree ((χg.trans g.toBasedLoop).trans χg.symm) := by
    rw [← degree_toBasedLoop_toCircle, degree_toBasedLoop_eq_of_joined hf, hfg,
      ← degree_toBasedLoop_eq_of_joined hg, degree_toBasedLoop_toCircle]
  have hπ := congrArg Multiplicative.ofAdd hdeg
  rw [← fundamentalGroupMulEquiv_fromPath, ← fundamentalGroupMulEquiv_fromPath] at hπ
  exact (hf.symm.trans (Path.joined_toCircle_iff_isConj.2
    (((fundamentalGroupMulEquiv 1).injective hπ) ▸ IsConj.refl _))).trans hg

/-- **The path components of the free loop space of the circle are the integers**, by the degree
of the free loops: `π₀(C(S¹, S¹)) ≃ ℤ`. -/
def freeLoopComponentsEquivInt : ZerothHomotopy C(Circle, Circle) ≃ ℤ :=
  Equiv.ofBijective
    (Quotient.lift (fun f : C(Circle, Circle) ↦ degree f.toBasedLoop)
      fun _ _ h ↦ degree_toBasedLoop_eq_of_joined h)
    ⟨fun c d h ↦ by
      obtain ⟨f, rfl⟩ := ZerothHomotopy.mk_surjective c
      obtain ⟨g, rfl⟩ := ZerothHomotopy.mk_surjective d
      exact Quotient.sound (joined_iff_degree_toBasedLoop_eq.2 h),
    fun n ↦ by
      obtain ⟨⟨γ⟩, hγ⟩ := (fundamentalGroupMulEquiv (1 : Circle)).surjective (.ofAdd n)
      induction γ using Path.Homotopic.Quotient.ind with | mk γ => ?_
      refine ⟨ZerothHomotopy.mk γ.toCircle, ?_⟩
      -- `ZerothHomotopy.mk` is the quotient map, on which `Quotient.lift` computes; the
      -- characterizing lemma `freeLoopComponentsEquivInt_mk` is stated only after this definition.
      change degree γ.toCircle.toBasedLoop = n
      rw [degree_toBasedLoop_toCircle, ← Multiplicative.ofAdd.injective.eq_iff,
        ← fundamentalGroupMulEquiv_fromPath]
      exact hγ⟩

@[simp]
theorem freeLoopComponentsEquivInt_mk (f : C(Circle, Circle)) :
    freeLoopComponentsEquivInt (.mk f) = degree f.toBasedLoop :=
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
      degree (MooreFreeLoopSpace.toCircleMap γ).toBasedLoop := by
  simp [mooreFreeLoopComponentsEquivInt]

end Circle
