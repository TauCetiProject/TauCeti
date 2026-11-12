/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import TauCeti.Topology.Homotopy.HomotopyEquiv
public import TauCeti.Topology.MappingSpace.FreeLoop
public import TauCeti.Topology.PathComponent
public import TauCeti.Topology.PathSpace.Moore.Comparison.FreeLoop
import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace
import TauCeti.Topology.Homotopy.Path

/-!
# Path components of the free loop space

The path components of the free loop space `𝓛X = C(S¹, X)`, with the compact-open topology, are
the free homotopy classes of loops in `X`. For a point `x` of `X`, reading a loop at `x` as a map
from the circle (`Path.toCircle`) identifies these classes with the conjugacy classes of
`π₁(X, x)`, as soon as `X` is path connected:

`π₀(𝓛X) ≃ ConjClasses π₁(X, x)`.

Two loops `γ₀`, `γ₁` at `x` lie in one path component of `𝓛X` exactly when their classes are
conjugate in `π₁(X, x)` (`Path.joined_toCircle_iff_isConj`). In one direction, a path from
`γ₀.toCircle` to `γ₁.toCircle` is a homotopy through closed paths
(`Path.joined_toCircle_iff_homotopicWith`), and its track `δ` at the base point is a loop with
`γ₀ · δ ≃ δ · γ₁`. In the other direction, a conjugate `χ · ℓ · χ⁻¹` of a loop `ℓ` is homotopic to
`ℓ` through closed paths (`Path.homotopicWith_trans_trans_symm`). The same conjugation moves the
loop `t ↦ f(e^{2πit})` of any free loop `f` (`ContinuousMap.toBasedLoop`) to a loop at `x` freely
homotopic to `f` (`ContinuousMap.joined_toCircle_trans_trans_symm_toBasedLoop`), which gives
surjectivity onto `π₀(𝓛X)` for path-connected `X`.

For a space that is not path connected, choose a basepoint in each path component
(`TauCeti.PathComponentBasepoints`). Evaluation at `1 ∈ S¹` sends each path component of `𝓛X` to
a path component of `X`, and over the component of a chosen basepoint `b` the path components of
`𝓛X` are the conjugacy classes of `π₁(X, b)`:

`π₀(𝓛X) ≃ Σ (c : π₀(X)), ConjClasses π₁(X, b_c)`.

The Moore free loop space `MooreFreeLoopSpace X` is homotopy equivalent to `C(S¹, X)`
(`TauCeti.MooreFreeLoopSpace.homotopyEquivCircleMap`), so both descriptions hold for it as well.

## Main declarations

* `Path.joined_toCircle_trans_trans_symm`: a conjugate `χ · ℓ · χ⁻¹` of a loop `ℓ` is joined to
  `ℓ` in `C(S¹, X)`.
* `ContinuousMap.joined_toCircle_trans_trans_symm_toBasedLoop`: every free loop is joined to a
  loop at any point of the path component of its base point.
* `Path.joined_toCircle_iff_isConj`: two loops at `x` are joined in `C(S¹, X)` exactly when their
  classes are conjugate in `π₁(X, x)`.
* `TauCeti.freeLoopComponentOfConjClass`: the injective map `ConjClasses π₁(X, x) → π₀(C(S¹, X))`,
  whose range is the set of components of free loops based in the path component of `x`.
* `TauCeti.conjClassesEquivFreeLoopComponents`: `ConjClasses π₁(X, x) ≃ π₀(C(S¹, X))` for
  path-connected `X`.
* `TauCeti.freeLoopComponentsEquivSigma`: `π₀(C(S¹, X)) ≃ Σ c, ConjClasses π₁(X, b_c)`.
* `TauCeti.MooreFreeLoopSpace.conjClassesEquivZerothHomotopy`,
  `TauCeti.MooreFreeLoopSpace.zerothHomotopyEquivSigma`: the same on the Moore free loop space.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §1.1, Exercise 1.1.2.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4 (local systems on `𝓛X`, one
  basepoint in each free homotopy class).
-/

public section

noncomputable section

open scoped unitInterval

variable {X : Type*} [TopologicalSpace X]

namespace Path

variable {x y : X}

/-- Homotopic loops are joined in the free loop space. -/
theorem Homotopic.joined_toCircle {γ γ' : Path x x} (h : γ.Homotopic γ') :
    Joined γ.toCircle γ'.toCircle :=
  (Path.joined_iff_homotopic.2 h).map (continuous_toCircle x)

/-- A conjugate `χ · ℓ · χ⁻¹` of a loop `ℓ` is joined to `ℓ` in the free loop space. -/
theorem joined_toCircle_trans_trans_symm (χ : Path x y) (ℓ : Path y y) :
    Joined ((χ.trans ℓ).trans χ.symm).toCircle ℓ.toCircle :=
  (joined_toCircle_iff_homotopicWith _ _).2 (homotopicWith_trans_trans_symm χ ℓ)

/-- **Free homotopy classes of loops at a point are conjugacy classes.** Two loops at `x` are
joined by a path in the free loop space `C(S¹, X)` exactly when their classes are conjugate in
`π₁(X, x)`. -/
theorem joined_toCircle_iff_isConj {γ₀ γ₁ : Path x x} :
    Joined γ₀.toCircle γ₁.toCircle ↔
      IsConj (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ₀))
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ₁)) := by
  -- In `π₁(X, x)` concatenation is multiplication in the reverse order and reversal is inversion;
  -- these are `FundamentalGroup.mul_def` and `FundamentalGroup.inv_def`, which hold by `rfl`.
  have hmul (p q : Path x x) : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (p.trans q)) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q) *
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) := rfl
  have hinv (p : Path x x) : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p.symm) =
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))⁻¹ := rfl
  constructor
  · intro h
    obtain ⟨δ, hδ⟩ := exists_trans_homotopic_trans_of_homotopicWith
      ((joined_toCircle_iff_homotopicWith γ₀ γ₁).1 h)
    have h' := congrArg FundamentalGroup.fromPath (Path.Homotopic.Quotient.eq.2 hδ)
    rw [hmul, hmul] at h'
    exact isConj_iff.2 ⟨_, by rw [h', mul_inv_cancel_right]⟩
  · intro h
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    obtain ⟨c⟩ := c
    induction c using Path.Homotopic.Quotient.ind with | mk δ => ?_
    -- `c * γ₀ * c⁻¹ = γ₁` says that `γ₁` is homotopic to the conjugate `δ⁻¹ · γ₀ · δ`.
    have h₁ : γ₁.Homotopic ((δ.symm.trans γ₀).trans δ) := by
      have hc' : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ₁) =
          FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((δ.symm.trans γ₀).trans δ)) := by
        rw [← hc, hmul, hmul, hinv, mul_assoc]
      exact Path.Homotopic.Quotient.eq.1 (congrArg FundamentalGroup.toPath hc')
    have h₂ := joined_toCircle_trans_trans_symm δ.symm γ₀
    rw [Path.symm_symm] at h₂
    exact (h₁.joined_toCircle.trans h₂).symm

end Path

namespace ContinuousMap

variable {x : X}

/-- **Every free loop is freely homotopic to a loop at a given point.** If `χ` is a path from `x`
to the base point `f 1` of a free loop `f`, then the loop `χ · f · χ⁻¹` at `x` is joined to `f` in
the free loop space. -/
theorem joined_toCircle_trans_trans_symm_toBasedLoop (f : C(Circle, X)) (χ : Path x (f 1)) :
    Joined ((χ.trans f.toBasedLoop).trans χ.symm).toCircle f := by
  simpa using Path.joined_toCircle_trans_trans_symm χ f.toBasedLoop

end ContinuousMap

namespace TauCeti

variable {x : X}

variable (x) in
/-- The path component of the free loop space `C(S¹, X)` of the free homotopy class of loops at
`x` with a given conjugacy class in `π₁(X, x)`. It is injective
(`TauCeti.injective_freeLoopComponentOfConjClass`), and for path-connected `X` a bijection
(`TauCeti.conjClassesEquivFreeLoopComponents`). -/
def freeLoopComponentOfConjClass :
    ConjClasses (FundamentalGroup X x) → ZerothHomotopy C(Circle, X) :=
  Quotient.lift
    (fun g : FundamentalGroup X x ↦
      Quotient.lift (fun γ : Path x x ↦ ZerothHomotopy.mk γ.toCircle)
        (fun _ _ h ↦ Quotient.sound (Path.Homotopic.joined_toCircle h))
        (FundamentalGroup.toPath g))
    (by
      intro a b h
      obtain ⟨a⟩ := a
      obtain ⟨b⟩ := b
      induction a using Path.Homotopic.Quotient.ind with | mk γ₀ => ?_
      induction b using Path.Homotopic.Quotient.ind with | mk γ₁ => ?_
      exact Quotient.sound (Path.joined_toCircle_iff_isConj.2 h))

@[simp]
theorem freeLoopComponentOfConjClass_mk_fromPath (γ : Path x x) :
    freeLoopComponentOfConjClass x
        (ConjClasses.mk (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))) =
      ZerothHomotopy.mk γ.toCircle :=
  (rfl)

theorem injective_freeLoopComponentOfConjClass :
    Function.Injective (freeLoopComponentOfConjClass (X := X) x) := by
  intro a b h
  obtain ⟨⟨a⟩, rfl⟩ := ConjClasses.mk_surjective a
  obtain ⟨⟨b⟩, rfl⟩ := ConjClasses.mk_surjective b
  induction a using Path.Homotopic.Quotient.ind with | mk γ₀ => ?_
  induction b using Path.Homotopic.Quotient.ind with | mk γ₁ => ?_
  exact ConjClasses.mk_eq_mk_iff_isConj.2 (Path.joined_toCircle_iff_isConj.1 (Quotient.exact h))

variable (X) in
/-- The path component of the base points of the free loops in a path component of the free loop
space `C(S¹, X)`: evaluation at `1 ∈ S¹` on path components. -/
def freeLoopComponentBase : ZerothHomotopy C(Circle, X) → ZerothHomotopy X :=
  Quotient.map (fun f ↦ f 1) fun _ _ h ↦ h.map (continuous_eval_const 1)

@[simp]
theorem freeLoopComponentBase_mk (f : C(Circle, X)) :
    freeLoopComponentBase X (.mk f) = .mk (f 1) :=
  (rfl)

@[simp]
theorem freeLoopComponentBase_freeLoopComponentOfConjClass
    (g : ConjClasses (FundamentalGroup X x)) :
    freeLoopComponentBase X (freeLoopComponentOfConjClass x g) = .mk x := by
  obtain ⟨⟨g⟩, rfl⟩ := ConjClasses.mk_surjective g
  induction g using Path.Homotopic.Quotient.ind with | mk γ => ?_
  rw [freeLoopComponentOfConjClass_mk_fromPath, freeLoopComponentBase_mk, Path.toCircle_one]

/-- The free homotopy classes of loops at `x` are the path components of the free loop space whose
loops are based in the path component of `x`. -/
theorem range_freeLoopComponentOfConjClass :
    Set.range (freeLoopComponentOfConjClass x) =
      freeLoopComponentBase X ⁻¹' {ZerothHomotopy.mk x} := by
  refine Set.Subset.antisymm ?_ fun c hc ↦ ?_
  · rintro _ ⟨g, rfl⟩
    exact freeLoopComponentBase_freeLoopComponentOfConjClass g
  · obtain ⟨f, rfl⟩ := ZerothHomotopy.mk_surjective c
    rw [Set.mem_preimage, freeLoopComponentBase_mk, Set.mem_singleton_iff] at hc
    have h : Joined x (f 1) := Quotient.exact hc.symm
    exact ⟨ConjClasses.mk (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        ((h.somePath.trans f.toBasedLoop).trans h.somePath.symm))),
      Quotient.sound (f.joined_toCircle_trans_trans_symm_toBasedLoop h.somePath)⟩

variable (x) in
/-- **The path components of the free loop space of a path-connected space are the conjugacy
classes of its fundamental group:** `ConjClasses π₁(X, x) ≃ π₀(C(S¹, X))`, sending the class of a
loop `γ` at `x` to the path component of `γ.toCircle`. -/
def conjClassesEquivFreeLoopComponents [PathConnectedSpace X] :
    ConjClasses (FundamentalGroup X x) ≃ ZerothHomotopy C(Circle, X) :=
  Equiv.ofBijective (freeLoopComponentOfConjClass x)
    ⟨injective_freeLoopComponentOfConjClass, fun c ↦ by
      have hc : c ∈ Set.range (freeLoopComponentOfConjClass x) := by
        rw [range_freeLoopComponentOfConjClass, Set.mem_preimage, Set.mem_singleton_iff]
        exact Subsingleton.elim _ _
      exact hc⟩

@[simp]
theorem conjClassesEquivFreeLoopComponents_apply [PathConnectedSpace X]
    (g : ConjClasses (FundamentalGroup X x)) :
    conjClassesEquivFreeLoopComponents x g = freeLoopComponentOfConjClass x g :=
  (rfl)

@[simp]
theorem conjClassesEquivFreeLoopComponents_symm_mk_toCircle [PathConnectedSpace X]
    (γ : Path x x) :
    (conjClassesEquivFreeLoopComponents x).symm (.mk γ.toCircle) =
      ConjClasses.mk (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) := by
  rw [Equiv.symm_apply_eq, conjClassesEquivFreeLoopComponents_apply,
    freeLoopComponentOfConjClass_mk_fromPath]

/-- **The path components of the free loop space of any space.** Given a basepoint `b_c` in each
path component `c` of `X`, the path components of `C(S¹, X)` lying over `c` are the conjugacy
classes of `π₁(X, b_c)`: `π₀(C(S¹, X)) ≃ Σ c, ConjClasses π₁(X, b_c)`. -/
def freeLoopComponentsEquivSigma (B : PathComponentBasepoints X) :
    ZerothHomotopy C(Circle, X) ≃
      Σ c : ZerothHomotopy X, ConjClasses (FundamentalGroup X (B.point c)) :=
  (Equiv.ofBijective (fun p ↦ freeLoopComponentOfConjClass (B.point p.1) p.2)
    ⟨fun ⟨c, a⟩ ⟨c', b⟩ h ↦ by
      have hc : c = c' := by
        simpa using congrArg (freeLoopComponentBase X) h
      subst hc
      exact congrArg (Sigma.mk c) (injective_freeLoopComponentOfConjClass h),
    fun d ↦ by
      have hd : d ∈
          Set.range (freeLoopComponentOfConjClass (B.point (freeLoopComponentBase X d))) := by
        rw [range_freeLoopComponentOfConjClass, Set.mem_preimage, Set.mem_singleton_iff,
          B.mk_point]
      obtain ⟨g, hg⟩ := hd
      exact ⟨⟨_, g⟩, hg⟩⟩).symm

@[simp]
theorem freeLoopComponentsEquivSigma_symm_apply (B : PathComponentBasepoints X)
    (p : Σ c : ZerothHomotopy X, ConjClasses (FundamentalGroup X (B.point c))) :
    (freeLoopComponentsEquivSigma B).symm p = freeLoopComponentOfConjClass (B.point p.1) p.2 :=
  (rfl)

@[simp]
theorem freeLoopComponentsEquivSigma_apply_fst (B : PathComponentBasepoints X)
    (c : ZerothHomotopy C(Circle, X)) :
    (freeLoopComponentsEquivSigma B c).1 = freeLoopComponentBase X c := by
  conv_rhs => rw [← (freeLoopComponentsEquivSigma B).symm_apply_apply c]
  rw [freeLoopComponentsEquivSigma_symm_apply, freeLoopComponentBase_freeLoopComponentOfConjClass,
    B.mk_point]

namespace MooreFreeLoopSpace

variable (x) in
/-- The path components of the Moore free loop space of a path-connected space are the conjugacy
classes of its fundamental group, through the homotopy equivalence with `C(S¹, X)`. -/
def conjClassesEquivZerothHomotopy [PathConnectedSpace X] :
    ConjClasses (FundamentalGroup X x) ≃ ZerothHomotopy (MooreFreeLoopSpace X) :=
  (conjClassesEquivFreeLoopComponents x).trans (homotopyEquivCircleMap X).zerothHomotopyCongr.symm

@[simp]
theorem conjClassesEquivZerothHomotopy_symm_mk [PathConnectedSpace X] (γ : MooreFreeLoopSpace X) :
    (conjClassesEquivZerothHomotopy x).symm (.mk γ) =
      (conjClassesEquivFreeLoopComponents x).symm (.mk (toCircleMap γ)) := by
  simp [conjClassesEquivZerothHomotopy]

/-- The path components of the Moore free loop space of any space, given a basepoint `b_c` in each
path component `c`: `π₀(𝓛X) ≃ Σ c, ConjClasses π₁(X, b_c)`. -/
def zerothHomotopyEquivSigma (B : PathComponentBasepoints X) :
    ZerothHomotopy (MooreFreeLoopSpace X) ≃
      Σ c : ZerothHomotopy X, ConjClasses (FundamentalGroup X (B.point c)) :=
  (homotopyEquivCircleMap X).zerothHomotopyCongr.trans (freeLoopComponentsEquivSigma B)

@[simp]
theorem zerothHomotopyEquivSigma_mk (B : PathComponentBasepoints X) (γ : MooreFreeLoopSpace X) :
    zerothHomotopyEquivSigma B (.mk γ) = freeLoopComponentsEquivSigma B (.mk (toCircleMap γ)) := by
  simp [zerothHomotopyEquivSigma]

end MooreFreeLoopSpace

end TauCeti
