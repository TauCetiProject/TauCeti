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
public import TauCeti.Topology.PathSpace.Moore.Comparison.FundamentalGroup
import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange
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
* `TauCeti.apply_fromPath_eq_of_joined_toCircle`: a family of characters of the fundamental groups
  invariant under change of base point takes equal values on freely homotopic loops.
* `TauCeti.freeLoopComponentOfConjClass`: the injective map `ConjClasses π₁(X, x) → π₀(C(S¹, X))`,
  whose range is the set of components of free loops based in the path component of `x`.
* `TauCeti.conjClassesEquivFreeLoopComponents`: `ConjClasses π₁(X, x) ≃ π₀(C(S¹, X))` for
  path-connected `X`.
* `TauCeti.freeLoopComponentsEquivSigma`: `π₀(C(S¹, X)) ≃ Σ c, ConjClasses π₁(X, b_c)`.
* `TauCeti.MooreFreeLoopSpace.conjClassesEquivZerothHomotopy`,
  `TauCeti.MooreFreeLoopSpace.zerothHomotopyEquivSigma`: the same on the Moore free loop space.
* `TauCeti.MooreFreeLoopSpace.apply_fundamentalGroupHom_toMooreLoop_eq_of_joined`: a family of
  characters invariant under change of base point is constant on the path components of the
  Moore free loop space.
* `TauCeti.MooreFreeLoopSpace.signExponent`: for a family of characters with values in `ℤˣ`, the
  exponent `0` or `-1` of a free Moore loop, constant on path components
  (`TauCeti.MooreFreeLoopSpace.signExponent_eq_of_joined`).

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

/-- **Characters invariant under change of base point are free homotopy invariants.** Let `χ` be
a family of homomorphisms from the fundamental groups of `X` to a commutative monoid, unchanged by
transport along paths. If two loops `ℓ₀` at `x` and `ℓ₁` at `y` are joined in the free loop space
`C(S¹, X)`, then `χ x` and `χ y` agree on their classes: after transport along the track of the
base point the loops are conjugate, and a homomorphism to a commutative monoid is constant on
conjugacy classes. -/
theorem apply_fromPath_eq_of_joined_toCircle {G : Type*} [CommMonoid G]
    (χ : ∀ x : X, FundamentalGroup X x →* G)
    (hχ : ∀ {x y : X} (p : Path x y) (g : FundamentalGroup X x),
      χ y (FundamentalGroup.fundamentalGroupMulEquivOfPath p g) = χ x g)
    {x y : X} {ℓ₀ : Path x x} {ℓ₁ : Path y y} (h : Joined ℓ₀.toCircle ℓ₁.toCircle) :
    χ x (.fromPath (Path.Homotopic.Quotient.mk ℓ₀)) =
      χ y (.fromPath (Path.Homotopic.Quotient.mk ℓ₁)) := by
  -- the track of the base point joins `x` to `y`
  obtain ⟨δ⟩ : Joined x y := by
    simpa only [ContinuousMap.eval_apply, Path.toCircle_one] using
      h.map (continuous_eval_const (1 : Circle))
  -- `ℓ₀` is conjugate to the loop `δ · ℓ₁ · δ⁻¹` at `x`
  have hconj := Path.joined_toCircle_iff_isConj.1
    (h.trans (Path.joined_toCircle_trans_trans_symm δ ℓ₁).symm)
  rw [isConj_iff_eq.1 ((χ x).map_isConj hconj), ← hχ δ.symm]
  congr 1
  rw [FundamentalGroup.fundamentalGroupMulEquivOfPath_apply]
  have hq : Path.Homotopic.Quotient.mk ((δ.trans ℓ₁).trans δ.symm) =
      (Path.Homotopic.Quotient.mk δ.symm).symm.trans
        ((Path.Homotopic.Quotient.mk ℓ₁).trans (Path.Homotopic.Quotient.mk δ.symm)) := by
    rw [← Path.Homotopic.Quotient.mk_symm, Path.symm_symm, Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.trans_assoc]
  exact congrArg FundamentalGroup.fromPath hq

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

/-! ### Characters of free Moore loops -/

/-- **Characters invariant under change of base point are constant on the path components of the
Moore free loop space.** Let `χ` be a family of homomorphisms from the fundamental groups of `X` to
a commutative group, unchanged by transport along paths. Joined free Moore loops `γ` and `γ'`,
each read as a loop at its own base point, have the same value under `χ`. -/
theorem apply_fundamentalGroupHom_toMooreLoop_eq_of_joined {G : Type*} [CommGroup G]
    (χ : ∀ x : X, FundamentalGroup X x →* G)
    (hχ : ∀ {x y : X} (p : Path x y) (g : FundamentalGroup X x),
      χ y (FundamentalGroup.fundamentalGroupMulEquivOfPath p g) = χ x g)
    {γ γ' : MooreFreeLoopSpace X} (h : Joined γ γ') :
    χ γ.basepoint (MooreLoopSpace.fundamentalGroupHom γ.basepoint γ.toMooreLoop) =
      χ γ'.basepoint (MooreLoopSpace.fundamentalGroupHom γ'.basepoint γ'.toMooreLoop) := by
  have h' := h.map (toCircleMap (X := X)).continuous
  rw [toCircleMap_eq_toCircle, toCircleMap_eq_toCircle] at h'
  rw [MooreLoopSpace.fundamentalGroupHom_apply, MooreLoopSpace.fundamentalGroupHom_apply, map_inv,
    map_inv, apply_fromPath_eq_of_joined_toCircle χ hχ h']

variable (χ : ∀ x : X, FundamentalGroup X x →* ℤˣ)

/-- The **sign exponent** `w(γ)` of a free Moore loop `γ` for a family `χ` of characters of the
fundamental groups with values in `ℤˣ`: `0` when `χ` at the base point of `γ` takes the value `1`
on `γ`, read as a loop there, and `-1` otherwise. It is the exponent `w` of the twists
`ev₀^*(o⁻¹) ⊗ ev₀^*(o^{-w})` on the free loop space of Barraud–Damian–Humilière–Oancea (§4.1),
where `o` is the rank-one local system with monodromy `χ`. -/
def signExponent (γ : MooreFreeLoopSpace X) : ℤ :=
  if χ γ.basepoint (MooreLoopSpace.fundamentalGroupHom γ.basepoint γ.toMooreLoop) = 1 then 0
  else -1

/-- The sign exponent of a free loop is `0` exactly when `χ` takes the value `1` on it. -/
@[simp]
theorem signExponent_eq_zero_iff (γ : MooreFreeLoopSpace X) :
    signExponent χ γ = 0 ↔
      χ γ.basepoint (MooreLoopSpace.fundamentalGroupHom γ.basepoint γ.toMooreLoop) = 1 := by
  rw [signExponent]
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (by decide) h

/-- The sign exponent of a free loop is `-1` exactly when `χ` takes the value `-1` on it. -/
@[simp]
theorem signExponent_eq_neg_one_iff (γ : MooreFreeLoopSpace X) :
    signExponent χ γ = -1 ↔
      χ γ.basepoint (MooreLoopSpace.fundamentalGroupHom γ.basepoint γ.toMooreLoop) = -1 := by
  rcases Int.units_eq_one_or
    (χ γ.basepoint (MooreLoopSpace.fundamentalGroupHom γ.basepoint γ.toMooreLoop)) with h | h <;>
    rw [signExponent, h] <;> decide

variable {χ} in
/-- For a family of characters invariant under change of base point, the sign exponent is
constant on the path components of the Moore free loop space. -/
theorem signExponent_eq_of_joined
    (hχ : ∀ {x y : X} (p : Path x y) (g : FundamentalGroup X x),
      χ y (FundamentalGroup.fundamentalGroupMulEquivOfPath p g) = χ x g)
    {γ γ' : MooreFreeLoopSpace X} (h : Joined γ γ') : signExponent χ γ = signExponent χ γ' := by
  rw [signExponent, signExponent, apply_fundamentalGroupHom_toMooreLoop_eq_of_joined χ hχ h]

/-- Constant loops have sign exponent `0`. -/
@[simp]
theorem signExponent_const (x : X) : signExponent χ (const x) = 0 := by
  rw [signExponent_eq_zero_iff, toMooreLoop_const, map_one, map_one]

end MooreFreeLoopSpace

end TauCeti
