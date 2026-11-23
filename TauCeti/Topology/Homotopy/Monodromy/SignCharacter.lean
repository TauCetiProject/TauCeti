/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import TauCeti.AlgebraicTopology.FundamentalGroup.FreeLoop
public import TauCeti.Topology.Homotopy.Monodromy.BasepointChange

/-!
# The sign character of a covering with finite fibres

Let `p : E → X` be a covering map whose fibre over `x` is finite. Path lifting along a loop at `x`
permutes the fibre over `x`, and the sign of this permutation is a homomorphism
`π₁(X, x) →* ℤˣ`, the **sign character** of the covering (`IsCoveringMap.signCharacter`).
Changing the basepoint along a path conjugates the monodromy permutations by path lifting, so it
does not change the character (`IsCoveringMap.signCharacter_fundamentalGroupMulEquivOfPath`).

For a double cover, whose fibres are the pairs `{e, σ e}` for a map `σ : E → E` with `σ e ≠ e`,
the character is `1` on a loop exactly when its lift starting at a point `e` of the fibre is
closed, and `-1` exactly when that lift ends at `σ e`
(`IsCoveringMap.signCharacter_eq_one_iff_monodromy_eq`,
`IsCoveringMap.signCharacter_eq_neg_one_iff`). This character classifies the double cover; for
the orientation double cover of a real vector bundle it is the orientation character `w₁`.

The character is a homomorphism to the commutative group `ℤˣ`, so it is constant on conjugacy
classes. Free loops `f : S¹ → X` in one path component of the free loop space `C(S¹, X)` give
conjugate classes after a change of basepoint (`Path.joined_toCircle_iff_isConj`), so the
character of the loop `t ↦ f(e^{2πit})` at `f 1` is an invariant of the path component of `f`
(`IsCoveringMap.freeLoopSignCharacter`, `IsCoveringMap.freeLoopSignCharacter_eq_of_joined`). For
a double cover it is `1` exactly when `f` lifts to the cover
(`IsCoveringMap.freeLoopSignCharacter_eq_one_iff`). On the Moore free loop space, the
**sign exponent** of a free loop is `0` when its sign is `1` and `-1` otherwise
(`IsCoveringMap.freeLoopSignExponent`); it is constant on path components
(`IsCoveringMap.freeLoopSignExponent_eq_of_joined`).

## Main definitions

* `IsCoveringMap.signCharacter`: the sign of the monodromy permutation of a finite fibre, as a
  homomorphism `π₁(X, x) →* ℤˣ`.
* `IsCoveringMap.freeLoopSignCharacter`: the sign character of a free loop `S¹ → X`.
* `IsCoveringMap.freeLoopSignExponent`: the exponent `w`, `0` or `-1`, of a Moore free loop.

## Main results

* `IsCoveringMap.signCharacter_eq_one_iff_monodromy_eq`,
  `IsCoveringMap.signCharacter_eq_neg_one_iff`: for a double cover, the character is `1` where
  the lift of a loop is closed and `-1` where it ends at the other point of the fibre.
* `IsCoveringMap.signCharacter_fundamentalGroupMulEquivOfPath`: invariance under change of
  basepoint.
* `IsCoveringMap.freeLoopSignCharacter_eq_of_joined`: the character of a free loop only depends on
  its path component in `C(S¹, X)`.
* `IsCoveringMap.freeLoopSignCharacter_eq_one_iff`: for a double cover, the character of a free
  loop is `1` exactly when the loop lifts to the cover.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.3 (the action of
  the fundamental group on a fibre by path lifting) and Section 3.3 (the orientation double cover).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §12 (`w₁` as the character of the orientation double cover).
-/

public section

noncomputable section

namespace IsCoveringMap

open TauCeti

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}
  (hp : IsCoveringMap p)

open Classical in
/-- The **sign character** of a covering `p` with finite fibre over `x`: the sign of the
permutation of the fibre over `x` given by path lifting along a loop at `x`. -/
def signCharacter {x : X} (hx : (p ⁻¹' {x}).Finite) : FundamentalGroup X x →* ℤˣ :=
  letI := hx.fintype
  Equiv.Perm.sign.comp (hp.monodromyPerm x)

/-- The sign character is the sign of the monodromy permutation, for any choice of the finiteness
and decidability instances on the fibre. -/
theorem signCharacter_apply {x : X} (hx : (p ⁻¹' {x}).Finite) [Fintype (p ⁻¹' {x})]
    [DecidableEq (p ⁻¹' {x})] (g : FundamentalGroup X x) :
    hp.signCharacter hx g = Equiv.Perm.sign (hp.monodromyPerm x g) := by
  rw [signCharacter, MonoidHom.comp_apply]
  congr!

/-- On a fibre with at most two points, the sign character is trivial on a loop exactly when
path lifting along the loop fixes the fibre pointwise. -/
theorem signCharacter_eq_one_iff {x : X} (hx : (p ⁻¹' {x}).Finite)
    (hcard : Nat.card (p ⁻¹' {x}) ≤ 2) (g : FundamentalGroup X x) :
    hp.signCharacter hx g = 1 ↔ hp.monodromyPerm x g = 1 := by
  classical
  let := hx.fintype
  -- A permutation of a set with at most two elements has sign `1` exactly when it is the
  -- identity, since the alternating group of such a set is trivial.
  rw [signCharacter_apply, ← Equiv.Perm.mem_alternatingGroup,
    alternatingGroup.eq_bot_of_card_le_two hcard, Subgroup.mem_bot]

/-! ### Double covers -/

section DoubleCover

variable {σ : E → E} (hfix : ∀ e, σ e ≠ e) (hfib : ∀ e e', p e' = p e → e' = e ∨ e' = σ e)

omit [TopologicalSpace E] [TopologicalSpace X] in
include hfib in
/-- A fibre of a double cover containing a point `e` is contained in `{e, σ e}`, so it has at
most two points. -/
private theorem natCard_fiber_le_two {x : X} (e : p ⁻¹' {x}) : Nat.card (p ⁻¹' {x}) ≤ 2 := by
  rw [Nat.card_coe_set_eq]
  refine (Set.ncard_le_ncard (t := {(e : E), σ e}) fun e' he' ↦ ?_).trans
    ((Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]))
  rcases hfib e e' (he'.trans e.property.symm) with h | h
  · exact .inl h
  · exact .inr h

include hfib in
/-- **The sign character of a double cover detects closed lifts.** It is `1` on a loop exactly
when the lift of the loop starting at a given point `e` of the fibre is closed. -/
theorem signCharacter_eq_one_iff_monodromy_eq {x : X} (hx : (p ⁻¹' {x}).Finite)
    (g : FundamentalGroup X x) (e : p ⁻¹' {x}) :
    hp.signCharacter hx g = 1 ↔ hp.monodromy g.toPath e = e := by
  rw [signCharacter_eq_one_iff hp hx (natCard_fiber_le_two hfib e)]
  refine ⟨fun h ↦ by simpa using Equiv.ext_iff.1 h e, fun h ↦ Equiv.ext fun e' ↦ ?_⟩
  simp only [IsCoveringMap.coe_monodromyPerm, Equiv.Perm.coe_one, id_eq]
  rcases hfib e e' (e'.property.trans e.property.symm) with he' | he'
  · rw [Subtype.ext he', h]
  -- The other point `σ e` goes to itself if it does not go to `e = monodromy e`.
  rcases hfib e _ ((hp.monodromy g.toPath e').property.trans e.property.symm) with hm | hm
  · rw [(hp.monodromy_bijective g.toPath).1 ((Subtype.ext hm).trans h.symm), h]
  · exact Subtype.ext (hm.trans he'.symm)

include hfix hfib in
/-- **The sign character of a double cover detects lifts exchanging the sheets.** It is `-1` on a
loop exactly when the lift of the loop starting at a given point `e` of the fibre ends at `σ e`. -/
theorem signCharacter_eq_neg_one_iff {x : X} (hx : (p ⁻¹' {x}).Finite)
    (g : FundamentalGroup X x) (e : p ⁻¹' {x}) :
    hp.signCharacter hx g = -1 ↔ (hp.monodromy g.toPath e : E) = σ e := by
  rw [← Int.units_ne_iff_eq_neg, Ne, signCharacter_eq_one_iff_monodromy_eq hp hfib hx g e]
  rcases hfib e _ ((hp.monodromy g.toPath e).property.trans e.property.symm) with hm | hm
  · exact ⟨fun h ↦ absurd (Subtype.ext hm) h, fun h ↦ absurd (hm.symm.trans h).symm (hfix e)⟩
  · exact ⟨fun _ ↦ hm, fun _ h ↦ hfix e (hm.symm.trans (congrArg Subtype.val h))⟩

end DoubleCover

/-! ### Change of basepoint -/

/-- **Invariance under change of basepoint.** Transporting a loop class back along a path `γ`
does not change its sign character: the two monodromy permutations are conjugate by path lifting
along `γ`. -/
theorem signCharacter_fundamentalGroupMulEquivOfPath_symm {x₀ x₁ : X}
    (hx₀ : (p ⁻¹' {x₀}).Finite) (hx₁ : (p ⁻¹' {x₁}).Finite) (γ : Path x₀ x₁)
    (g : FundamentalGroup X x₁) :
    hp.signCharacter hx₀ ((FundamentalGroup.fundamentalGroupMulEquivOfPath γ).symm g) =
      hp.signCharacter hx₁ g := by
  classical
  let := hx₀.fintype
  let := hx₁.fintype
  rw [signCharacter_apply, signCharacter_apply, monodromyPerm_fundamentalGroupMulEquivOfPath_symm,
    Equiv.Perm.sign_permCongr]

/-- **Invariance under change of basepoint.** Transporting a loop class along a path `γ` does not
change its sign character. -/
theorem signCharacter_fundamentalGroupMulEquivOfPath {x₀ x₁ : X}
    (hx₀ : (p ⁻¹' {x₀}).Finite) (hx₁ : (p ⁻¹' {x₁}).Finite) (γ : Path x₀ x₁)
    (g : FundamentalGroup X x₀) :
    hp.signCharacter hx₁ (FundamentalGroup.fundamentalGroupMulEquivOfPath γ g) =
      hp.signCharacter hx₀ g := by
  rw [← signCharacter_fundamentalGroupMulEquivOfPath_symm hp hx₀ hx₁ γ, MulEquiv.symm_apply_apply]

/-- The sign character of a loop is unchanged by casting the loop along an equality of
basepoints. -/
private theorem signCharacter_fromPath_cast {x x' : X} (hx : (p ⁻¹' {x}).Finite)
    (hx' : (p ⁻¹' {x'}).Finite) (h : x' = x) (γ : Path x x) :
    hp.signCharacter hx' (FundamentalGroup.fromPath (.mk (γ.cast h h))) =
      hp.signCharacter hx (FundamentalGroup.fromPath (.mk γ)) := by
  subst h
  rfl

/-! ### Free loops -/

/-- The **sign character of a free loop** `f : S¹ → X` in a covering with finite fibres: the sign
character of the loop `t ↦ f(e^{2πit})` at `f 1`. It is constant on the path components of the
free loop space (`IsCoveringMap.freeLoopSignCharacter_eq_of_joined`), and for a double cover it is
`1` exactly when `f` lifts to the cover (`IsCoveringMap.freeLoopSignCharacter_eq_one_iff`). -/
def freeLoopSignCharacter (hfin : ∀ x, (p ⁻¹' {x}).Finite) (f : C(Circle, X)) : ℤˣ :=
  hp.signCharacter (hfin (f 1)) (FundamentalGroup.fromPath (.mk f.toBasedLoop))

variable (hfin : ∀ x, (p ⁻¹' {x}).Finite)

/-- The sign character of a free loop is the sign character of its based loop at `f 1`. -/
theorem freeLoopSignCharacter_def (f : C(Circle, X)) :
    hp.freeLoopSignCharacter hfin f =
      hp.signCharacter (hfin (f 1)) (FundamentalGroup.fromPath (.mk f.toBasedLoop)) :=
  (rfl)

/-- The sign character of the free loop `γ.toCircle` of a loop `γ` at `x` is the sign character
of `γ`. -/
@[simp]
theorem freeLoopSignCharacter_toCircle {x : X} (γ : Path x x) :
    hp.freeLoopSignCharacter hfin γ.toCircle =
      hp.signCharacter (hfin x) (FundamentalGroup.fromPath (.mk γ)) := by
  have hγ : γ.toCircle.toBasedLoop = γ.cast γ.toCircle_one γ.toCircle_one := by
    ext t
    rw [ContinuousMap.toBasedLoop_apply, Path.cast_coe, Path.toCircle_unitToCircle]
  rw [freeLoopSignCharacter_def, hγ, signCharacter_fromPath_cast]

/-- **The sign character of a free loop is an invariant of its path component** in the free loop
space `C(S¹, X)`. Joined free loops are, after transport of the basepoint along the track of the
basepoint, conjugate loops, and the character is invariant under both operations. -/
theorem freeLoopSignCharacter_eq_of_joined {f g : C(Circle, X)} (h : Joined f g) :
    hp.freeLoopSignCharacter hfin f = hp.freeLoopSignCharacter hfin g := by
  -- The track `δ` of the basepoint, and the loop `δ · g · δ⁻¹` at `f 1`, joined to `f`.
  let δ : Path (f 1) (g 1) := h.somePath.map ((continuous_eval_const (1 : Circle)))
  have hj : Joined f.toBasedLoop.toCircle ((δ.trans g.toBasedLoop).trans δ.symm).toCircle := by
    rw [ContinuousMap.toBasedLoop_toCircle]
    exact h.trans (g.joined_toCircle_trans_trans_symm_toBasedLoop δ).symm
  have hconj :=
    (hp.signCharacter (hfin (f 1))).map_isConj (Path.joined_toCircle_iff_isConj.1 hj)
  rw [isConj_iff_eq] at hconj
  rw [freeLoopSignCharacter_def, freeLoopSignCharacter_def, hconj,
    ← signCharacter_fundamentalGroupMulEquivOfPath_symm hp (hfin _) (hfin _) δ,
    FundamentalGroup.fundamentalGroupMulEquivOfPath_symm_apply]
  have hq : Path.Homotopic.Quotient.mk ((δ.trans g.toBasedLoop).trans δ.symm) =
      (Path.Homotopic.Quotient.mk δ).trans
        ((Path.Homotopic.Quotient.mk g.toBasedLoop).trans (Path.Homotopic.Quotient.mk δ).symm) := by
    rw [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_symm, Path.Homotopic.Quotient.trans_assoc]
  exact congrArg (fun q ↦ hp.signCharacter (hfin (f 1)) (FundamentalGroup.fromPath q)) hq

/-- The sign character of a constant loop is `1`. -/
@[simp]
theorem freeLoopSignCharacter_const (x : X) :
    hp.freeLoopSignCharacter hfin (ContinuousMap.const Circle x) = 1 := by
  have h : (ContinuousMap.const Circle x).toBasedLoop = Path.refl x := by
    ext t
    rw [ContinuousMap.toBasedLoop_apply, ContinuousMap.const_apply]
    rfl
  rw [freeLoopSignCharacter_def, h]
  exact map_one _

/-- **Lifting a free loop to a double cover.** The sign character of a free loop `f` is `1`
exactly when `f` lifts to the cover, provided the fibre over `f 1` is nonempty. -/
theorem freeLoopSignCharacter_eq_one_iff {σ : E → E}
    (hfib : ∀ e e', p e' = p e → e' = e ∨ e' = σ e) (f : C(Circle, X))
    (hf : f 1 ∈ Set.range p) :
    hp.freeLoopSignCharacter hfin f = 1 ↔ ∃ s : C(Circle, E), ∀ z, p (s z) = f z := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := hf
    rw [freeLoopSignCharacter_def,
      signCharacter_eq_one_iff_monodromy_eq hp hfib _ _ (⟨e, he⟩ : p ⁻¹' {f 1})] at h
    -- The lift of the loop `t ↦ f(e^{2πit})` starting at `e` is closed, so it descends to the
    -- circle.
    let Γ : Path e e :=
      { toContinuousMap := hp.liftPath f.toBasedLoop.toContinuousMap e (by simp [he])
        source' := hp.liftPath_zero ..
        target' := by
          -- `FundamentalGroup.toPath` and `FundamentalGroup.fromPath` are abbreviations, inverse
          -- to each other by definition.
          have h' : hp.monodromy (Path.Homotopic.Quotient.mk f.toBasedLoop) ⟨e, he⟩ = ⟨e, he⟩ := h
          have := congrArg Subtype.val h'
          rwa [IsCoveringMap.coe_monodromy_mk] at this }
    refine ⟨Γ.toCircle, fun z ↦ ?_⟩
    obtain ⟨t, rfl⟩ := unitToCircle_surjective z
    rw [Path.toCircle_unitToCircle, ← ContinuousMap.toBasedLoop_apply]
    exact congrFun (hp.liftPath_lifts f.toBasedLoop.toContinuousMap e (by simp [he])) t
  · -- The loop `t ↦ s(e^{2πit})` is a closed lift of the loop of `f`, from `s 1`.
    rintro ⟨s, hs⟩
    rw [freeLoopSignCharacter_def,
      signCharacter_eq_one_iff_monodromy_eq hp hfib _ _ (⟨s 1, hs 1⟩ : p ⁻¹' {f 1})]
    refine Subtype.ext ((hp.monodromy_eq_apply_one (γ := f.toBasedLoop)
      (Γ := s.comp unitToCircle) (funext fun t ↦ by
        rw [Function.comp_apply, ContinuousMap.comp_apply, ContinuousMap.toBasedLoop_apply]
        exact hs _)
      (by simp)).trans ?_)
    simp

/-- **The sign exponent** `w` of a Moore free loop: `0` when the loop has sign `1`, so that
for the orientation cover of a vector bundle the bundle pulled back along the loop is orientable,
and `-1` otherwise. -/
def freeLoopSignExponent (γ : MooreFreeLoopSpace X) : ℤ :=
  if hp.freeLoopSignCharacter hfin (MooreFreeLoopSpace.toCircleMap γ) = 1 then 0 else -1

/-- The sign exponent of a free loop is `0` exactly when its sign in `ℤˣ` is `1`. -/
@[simp]
theorem freeLoopSignExponent_eq_zero_iff (γ : MooreFreeLoopSpace X) :
    hp.freeLoopSignExponent hfin γ = 0 ↔
      hp.freeLoopSignCharacter hfin (MooreFreeLoopSpace.toCircleMap γ) = 1 := by
  simp [freeLoopSignExponent]

/-- The sign exponent of a free loop is `-1` exactly when its sign in `ℤˣ` is `-1`. -/
@[simp]
theorem freeLoopSignExponent_eq_neg_one_iff (γ : MooreFreeLoopSpace X) :
    hp.freeLoopSignExponent hfin γ = -1 ↔
      hp.freeLoopSignCharacter hfin (MooreFreeLoopSpace.toCircleMap γ) = -1 := by
  rcases Int.units_eq_one_or (hp.freeLoopSignCharacter hfin (MooreFreeLoopSpace.toCircleMap γ))
    with h | h <;> simp [freeLoopSignExponent, h]

/-- The sign exponent is constant on the path components of the free loop space. -/
theorem freeLoopSignExponent_eq_of_joined {γ δ : MooreFreeLoopSpace X} (h : Joined γ δ) :
    hp.freeLoopSignExponent hfin γ = hp.freeLoopSignExponent hfin δ := by
  rw [freeLoopSignExponent, freeLoopSignExponent, hp.freeLoopSignCharacter_eq_of_joined hfin
    (h.map MooreFreeLoopSpace.toCircleMap.continuous)]

end IsCoveringMap
