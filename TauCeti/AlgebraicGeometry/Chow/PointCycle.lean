/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Chow.Pushforward
public import TauCeti.AlgebraicGeometry.RationalPoint.Basic
public import TauCeti.AlgebraicGeometry.Scheme.SpecOver

/-!
# Cycles of closed points

A closed point `x` of a scheme `X` has height zero for the specialization order
(`AlgebraicGeometry.Scheme.height_of_isClosed`), so the cycle `n [x]` is a zero-cycle. Over a
field `k`, its degree is `[κ(x) : k] n`, and its pushforward along a morphism `f` over `k` is
`[κ(x) : κ(f x)] n [f x]` (`Chow.cyclesMap_single`, for a point cycle of any dimension). In
particular, pushing forward along the structure morphism of a quasi-compact `k`-scheme sends
`[P]` to `[κ(P) : k] [pt]`. At a `k`-rational point the degree is `n`; the origin of the affine
line `Spec k[X]` is such a point, so `[0]` is a zero-cycle of degree `1` on `𝔸¹_k`
(`Chow.cyclesDegree_single_affineLine_origin`).

## Main statements

* `Chow.single_mem_cyclesOfDimension`: `n [x]` is a `d`-cycle for a point `x` of dimension `d`.
* `Chow.single_mem_cyclesOfDimension_zero`: `n [x]` is a zero-cycle for a closed point `x`.
* `Chow.cyclesDegree_single`: `deg (n [x]) = [κ(x) : k] n`.
* `Chow.cyclesMap_single`: `f_* (n [x]) = n [κ(x) : κ(f x)] [f x]`.
* `Chow.cyclesDegree_single_of_section`: at a `k`-rational point, `deg (n [x]) = n`.
* `Chow.cyclesDegree_single_affineLine_origin`: on `𝔸¹_k = Spec k[X]`, `deg [0] = 1`.
-/

public section

open AlgebraicGeometry Order CategoryTheory

universe u

namespace TauCeti.AlgebraicGeometry.Chow

/-- For a point `x` of dimension `d`, the cycle `n [x]` is a `d`-cycle. -/
lemma single_mem_cyclesOfDimension {X : Scheme.{u}} [DecidableEq X] {d : ℤ} {x : X}
    (hx : x ∈ pointsOfDimension X d) (n : ℤ) :
    Function.locallyFinsuppWithin.single x n ∈ cyclesOfDimension X d := by
  rw [mem_cyclesOfDimension_iff]
  intro y hy
  have : y = x := by
    by_contra h
    exact hy (by simp [Function.locallyFinsuppWithin.single_apply, h])
  subst this
  exact hx

/-- For a closed point `x`, the cycle `n [x]` is a zero-cycle. -/
lemma single_mem_cyclesOfDimension_zero {X : Scheme.{u}} [DecidableEq X] {x : X}
    (hx : IsClosed ({x} : Set X)) (n : ℤ) :
    Function.locallyFinsuppWithin.single x n ∈ cyclesOfDimension X 0 :=
  single_mem_cyclesOfDimension
    (mem_pointsOfDimension.2 ⟨0, by simp [Scheme.height_of_isClosed hx]⟩) n

variable (k : Type u) [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))]

/-- The degree of the zero-cycle `n [x]` is `[κ(x) : k] n`. For a closed point `x`, the membership
hypothesis is `single_mem_cyclesOfDimension_zero`. -/
@[simp]
lemma cyclesDegree_single [CompactSpace X] [DecidableEq X] {x : X} {n : ℤ}
    (h : Function.locallyFinsuppWithin.single x n ∈ cyclesOfDimension X 0) :
    cyclesDegree k X ⟨_, h⟩ = (X ↘ Spec (.of k)).residueDegree x * n := by
  rw [cyclesDegree_eq_degree, AlgebraicCycle.degree_single, nsmul_eq_mul]

/-- At a `k`-rational point, given by a section `s` of the structure morphism, the zero-cycle
`n [s pt]` has degree `n`. -/
lemma cyclesDegree_single_of_section [CompactSpace X] [DecidableEq X] {s : Spec (.of k) ⟶ X}
    (hs : s ≫ (X ↘ Spec (.of k)) = 𝟙 _) (n : ℤ) :
    cyclesDegree k X ⟨_, single_mem_cyclesOfDimension_zero
      (TauCeti.AlgebraicGeometry.isClosed_singleton_of_section hs) n⟩ = n := by
  rw [cyclesDegree_single k]
  have h : (X ↘ Spec (.of k)).residueDegree (s (IsLocalRing.closedPoint k)) = 1 :=
    TauCeti.AlgebraicGeometry.residueDegree_eq_one_of_section hs _
  rw [h, Nat.cast_one, one_mul]

variable [Y.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))]

/-- The pushforward of the `d`-cycle `n [x]` along a morphism `f` over `k` is
`n [κ(x) : κ(f x)] [f x]`. For a point `x` of dimension `d`, the membership hypothesis is
`single_mem_cyclesOfDimension`. -/
@[simp]
lemma cyclesMap_single [DecidableEq X] [DecidableEq Y] (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [QuasiCompact f] {d : ℤ} {x : X} {n : ℤ}
    (h : Function.locallyFinsuppWithin.single x n ∈ cyclesOfDimension X d) :
    (cyclesMap k f ⟨_, h⟩ : AlgebraicCycle Y ℤ) =
      Function.locallyFinsuppWithin.single (f x) (n * f.residueDegree x) := by
  ext y
  rw [cyclesMap_apply, Function.locallyFinsuppWithin.single_apply]
  rw [finsum_eq_single _ x fun z hz => by
    simp [Function.locallyFinsuppWithin.single_apply, hz]]
  by_cases h : y = f x
  · simp [h, Function.locallyFinsuppWithin.single_apply]
  · simp [Function.locallyFinsuppWithin.single_apply, h, Ne.symm h]

open Polynomial

/-- On the affine line `𝔸¹_k = Spec k[X]`, the zero-cycle `[0]` of the origin, the spectrum of
evaluation at `0`, has degree `1`. -/
theorem cyclesDegree_single_affineLine_origin [DecidableEq (Spec (.of k[X]))] :
    cyclesDegree k (Spec (.of k[X])) ⟨_, single_mem_cyclesOfDimension_zero
      (TauCeti.AlgebraicGeometry.isClosed_singleton_of_section
        (TauCeti.AlgebraicGeometry.SpecMap_algHom_comp_eq_id (aeval (0 : k)))) 1⟩ =
      1 :=
  cyclesDegree_single_of_section k
    (TauCeti.AlgebraicGeometry.SpecMap_algHom_comp_eq_id (aeval (0 : k))) 1

end TauCeti.AlgebraicGeometry.Chow
