/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Lift.BasicSeq
public import TauCeti.GroupTheory.GroupAlgGeom.Lift.Twist.Lift

/-!
# Towers of extensions of centralizers along a sequence of twists

Let `v : X → H` be a point of the free `G`-group `G[X]` in a group `H`, with coefficient map
`ι : G →* H`, and let `d₁, …, d_L` be twist data (`TauCeti.GroupAlgGeom.TwistData`): words `Aᵢ`
of `G[X]` with exponents `eᵢ` such that the substitution `x ↦ Aᵢ ^ l * x * Aᵢ ^ r` fixes `Aᵢ`.
Following [IFT], §7.2, Proposition 4, the point is lifted along the twists one after the other:
the first step is the extension `H(u₁, t₁)` of the centralizer of `u₁ = A₁(v)` with the point
`x ↦ t₁ ^ l * v x * t₁ ^ r` (`TauCeti.GroupAlgGeom.Lift.twistLift`), and each further step lifts
the point of the previous stage along the next twist. The stages are bundled as
`TowerStage G X`: a group, a coefficient map and a point. The result is the tower
`H = Z₀ ≤ Z₁ ≤ ⋯ ≤ Z_L` of [IFT], p. 104, with its point `λ` (`twistTower`); the base `H`
embeds in `Z_L` through the inclusions of the steps (`towerInclusion`).

Retracting the letters from the top, `t_L ↦ u_L ^ {p_L}`, then `t_{L-1} ↦ u_{L-1} ^ {p_{L-1}}`
and so on (`towerRetraction`), gives a left inverse of the inclusion of the base. For exponents
`p = (p₁, …, p_m)` with `m ≤ L` (the steps above the `m`-th getting the exponent `0`), it
sends `λ` to the point `φ_{m,p} v` obtained from `v` by the twists with exponents `p` ([IFT],
p. 104: `λ_β ξ_p = φ_{2K,p} β`, the case `m = L`; `eval_towerRetraction`). The bound `m ≤ L` is
needed: the retraction ignores the exponents beyond the `L`-th, whereas `φ_{m,p}` (`phi`)
continues the sequence of twists periodically. The retraction `t ↦ u ^ k` of one step sends the
lifted point to the point twisted `k` times (`TowerStage.twisted`,
`TowerStage.retraction_comp_lift_point`; [IFT], §7.2: (84) is the specialisation of (85)).

A tower is nondegenerate (`TowerStage.IsNondegenerate`) when every step extends the centralizer
of a nonidentity element; this holds, for example, when every twisting word has nontrivial value
at the base point (`TowerStage.isNondegenerate_of_forall_ne_one`). [IFT] does not state this
condition, but it is needed: if the twisting word vanishes at the current point, the step is the
extension of the centralizer of `1`, a direct product `H × ℤ`, which is not fully residually free
when `H` is nonabelian. A nondegenerate tower over a fully residually free group is fully
residually free, and its point solves every system that the twists fix and the base point
solves. For the equation `[x, y] = [a, b]` over `F(a, b)` and its
basic sequence this is the tower of [IFT], p. 102 (`twistTower_mem_V_oneCommutatorEquation`).

## Main definitions

* `TauCeti.GroupAlgGeom.Lift.TowerStage`: a point of `G[X]` in a group, with the group and the
  coefficient map.
* `TauCeti.GroupAlgGeom.Lift.TowerStage.lift`: one step of the tower.
* `TauCeti.GroupAlgGeom.Lift.TowerStage.twisted`: the stage with its point twisted `k` times.
* `TauCeti.GroupAlgGeom.Lift.twistTower`: the tower along a list of twist data.
* `TauCeti.GroupAlgGeom.Lift.towerInclusion`: the inclusion of the base into the tower.
* `TauCeti.GroupAlgGeom.Lift.towerRetraction`: the retraction of the tower with given exponents.
* `TauCeti.GroupAlgGeom.Lift.TowerStage.IsNondegenerate`: every step extends the centralizer of
  a nonidentity element.

## Main results

* `TauCeti.GroupAlgGeom.Lift.towerRetraction_towerInclusion`: every retraction of the tower is a
  left inverse of the inclusion of the base.
* `TauCeti.GroupAlgGeom.Lift.eval_towerRetraction`: the retraction with exponents
  `p = (p₁, …, p_m)`, `m ≤ L`, sends the top point to `φ_{m,p} v`.
* `TauCeti.GroupAlgGeom.Lift.isFullyResiduallyFree_twistTower`,
  `TauCeti.GroupAlgGeom.Lift.twistTower_mem_V`: a nondegenerate tower over a fully residually free
  group is fully residually free, and its point solves every system the twists fix.
* `TauCeti.GroupAlgGeom.Lift.twistTower_mem_V_oneCommutatorEquation`: the point of the tower of the
  solution `(a, b)` of `[x, y] = [a, b]` along any number of rounds of its basic sequence is a
  solution.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §7.2, (84)–(85), Propositions 4 and 5, and p. 104.
-/

public section

universe u v w

open Monoid.Coprod TauCeti.LimitGroup
open scoped commutatorElement

namespace TauCeti.GroupAlgGeom.Lift

variable {G : Type u} [Group G] {X : Type v}

/-- A point of the free `G`-group `G[X]` in a group, bundled with the group and the coefficient
map: a stage of a tower of extensions of centralizers. Unlike for `TauCeti.GroupAlgGeom.GGroup`,
the coefficient map need not be injective. -/
structure TowerStage (G : Type u) [Group G] (X : Type v) where
  /-- The group of the stage. -/
  carrier : Type w
  [instGroup : Group carrier]
  /-- The coefficient map. -/
  coeff : G →* carrier
  /-- The point. -/
  point : X → carrier

attribute [instance] TowerStage.instGroup

namespace TowerStage

/-- Lifting a stage along a twist datum `d = (A, e)`: the extension `H(u, t)` of the centralizer of
`u = A(v)`, with the point `x ↦ t ^ l * v x * t ^ r` ([IFT], §7.2, (85)). -/
@[expose] noncomputable def lift (P : TowerStage.{u, v, w} G X) (d : TwistData G X) :
    TowerStage.{u, v, w} G X where
  carrier := CentralizerExt (eval P.coeff P.point d.A) 1
  coeff := CentralizerExt.of.comp P.coeff
  point := twistLift (eval P.coeff P.point d.A) P.point d.e

@[simp]
theorem lift_coeff (P : TowerStage.{u, v, w} G X) (d : TwistData G X) :
    (P.lift d).coeff = CentralizerExt.of.comp P.coeff := (rfl)

@[simp]
theorem lift_point (P : TowerStage.{u, v, w} G X) (d : TwistData G X) :
    (P.lift d).point = twistLift (eval P.coeff P.point d.A) P.point d.e := (rfl)

/-- The stage with the same group and the point `x ↦ (γ ^ k x)(v)` twisted `k` times along the
twist `γ` of a datum, for an integer `k` ([IFT], §7.2, (84)). -/
@[expose] noncomputable def twisted (P : TowerStage.{u, v, w} G X) (d : TwistData G X) (k : ℤ) :
    TowerStage.{u, v, w} G X where
  carrier := P.carrier
  coeff := P.coeff
  point := wordMap P.coeff (fun x => (d.toMulAut ^ k) (inr (.of x))) P.point

@[simp]
theorem twisted_coeff (P : TowerStage.{u, v, w} G X) (d : TwistData G X) (k : ℤ) :
    (P.twisted d k).coeff = P.coeff := (rfl)

@[simp]
theorem twisted_point (P : TowerStage.{u, v, w} G X) (d : TwistData G X) (k : ℤ) :
    (P.twisted d k).point = wordMap P.coeff (fun x => (d.toMulAut ^ k) (inr (.of x))) P.point :=
  (rfl)

/-- The retraction `t ↦ u ^ k` of the lift along a twist datum, `u = A(v)`, sends the lifted point
to the point twisted `k` times, for every integer `k` ([IFT], §7.2: in the extension of the
centralizer, the solution (84) is (85) with `t` in place of the power `u ^ q`). -/
theorem retraction_comp_lift_point (P : TowerStage.{u, v, w} G X) (d : TwistData G X) (k : ℤ) :
    ⇑(CentralizerExt.retraction fun _ => k) ∘ (P.lift d).point = (P.twisted d k).point := by
  rw [lift_point, retraction_comp_twistLift d.e _ (B := d.A ^ k) (map_zpow _ _ _).symm]
  simp

end TowerStage

/-- The tower of a stage along a list of twist data, the head of the list lifted first. -/
@[expose] noncomputable def twistTower :
    List (TwistData G X) → TowerStage.{u, v, w} G X → TowerStage.{u, v, w} G X
  | [], P => P
  | d :: l, P => twistTower l (P.lift d)

@[simp]
theorem twistTower_nil (P : TowerStage.{u, v, w} G X) : twistTower [] P = P := (rfl)

@[simp]
theorem twistTower_cons (d : TwistData G X) (l : List (TwistData G X))
    (P : TowerStage.{u, v, w} G X) : twistTower (d :: l) P = twistTower l (P.lift d) := (rfl)

/-- The inclusion of the base of the tower into its top group: the composition of the inclusions
of each stage into the extension of a centralizer of it. -/
noncomputable def towerInclusion : (l : List (TwistData G X)) → (P : TowerStage.{u, v, w} G X) →
    P.carrier →* (twistTower l P).carrier
  | [], P => MonoidHom.id P.carrier
  | d :: l, P => (towerInclusion l (P.lift d)).comp CentralizerExt.of

@[simp]
theorem towerInclusion_nil (P : TowerStage.{u, v, w} G X) :
    towerInclusion [] P = MonoidHom.id P.carrier := (rfl)

theorem towerInclusion_cons (d : TwistData G X) (l : List (TwistData G X))
    (P : TowerStage.{u, v, w} G X) :
    towerInclusion (d :: l) P = (towerInclusion l (P.lift d)).comp CentralizerExt.of := (rfl)

theorem towerInclusion_cons_apply (d : TwistData G X) (l : List (TwistData G X))
    (P : TowerStage.{u, v, w} G X) (x : P.carrier) :
    towerInclusion (d :: l) P x = towerInclusion l (P.lift d) (CentralizerExt.of x) := (rfl)

/-- The inclusion of the base of the tower commutes with the coefficient maps. -/
@[simp]
theorem towerInclusion_coeff (l : List (TwistData G X)) (P : TowerStage.{u, v, w} G X) (g : G) :
    towerInclusion l P (P.coeff g) = (twistTower l P).coeff g := by
  induction l generalizing P with
  | nil => rfl
  | cons d _ ih => exact ih (P.lift d)

@[simp]
theorem towerInclusion_comp_coeff (l : List (TwistData G X)) (P : TowerStage.{u, v, w} G X) :
    (towerInclusion l P).comp P.coeff = (twistTower l P).coeff :=
  MonoidHom.ext (towerInclusion_coeff l P)

/-- The retraction of the tower onto its base with exponents `p`: the letter of the top step is
sent to a power of the element whose centralizer it extends, then the letter of the step below,
and so on. The exponent of the `i`-th step (from the bottom) is the `i`-th entry of `p`, and `0`
when `p` is shorter; the entries of `p` beyond the length of the tower are ignored. -/
noncomputable def towerRetraction : (l : List (TwistData G X)) → (P : TowerStage.{u, v, w} G X) →
    List ℕ → (twistTower l P).carrier →* P.carrier
  | [], P, _ => MonoidHom.id P.carrier
  | d :: l, P, p => (CentralizerExt.retraction fun _ => ((p.headD 0 : ℕ) : ℤ)).comp
      (towerRetraction l (P.lift d) p.tail)

@[simp]
theorem towerRetraction_nil (P : TowerStage.{u, v, w} G X) (p : List ℕ) :
    towerRetraction [] P p = MonoidHom.id P.carrier := (rfl)

theorem towerRetraction_cons (d : TwistData G X) (l : List (TwistData G X))
    (P : TowerStage.{u, v, w} G X) (p : List ℕ) :
    towerRetraction (d :: l) P p = (CentralizerExt.retraction fun _ => ((p.headD 0 : ℕ) : ℤ)).comp
      (towerRetraction l (P.lift d) p.tail) := (rfl)

theorem towerRetraction_cons_apply (d : TwistData G X) (l : List (TwistData G X))
    (P : TowerStage.{u, v, w} G X) (p : List ℕ) (x : (twistTower (d :: l) P).carrier) :
    towerRetraction (d :: l) P p x = CentralizerExt.retraction (fun _ => ((p.headD 0 : ℕ) : ℤ))
      (towerRetraction l (P.lift d) p.tail x) := (rfl)

/-- Every retraction of the tower is a left inverse of the inclusion of the base. -/
@[simp]
theorem towerRetraction_towerInclusion (l : List (TwistData G X)) (P : TowerStage.{u, v, w} G X)
    (p : List ℕ) (x : P.carrier) : towerRetraction l P p (towerInclusion l P x) = x := by
  induction l generalizing P p with
  | nil => rfl
  | cons d l ih => exact (congrArg (CentralizerExt.retraction _)
      (ih (P.lift d) p.tail (CentralizerExt.of x))).trans (CentralizerExt.retraction_of _ x)

@[simp]
theorem towerRetraction_comp_towerInclusion (l : List (TwistData G X))
    (P : TowerStage.{u, v, w} G X) (p : List ℕ) :
    (towerRetraction l P p).comp (towerInclusion l P) = MonoidHom.id P.carrier :=
  MonoidHom.ext (towerRetraction_towerInclusion l P p)

/-- The retractions of the tower commute with the coefficient maps. -/
@[simp]
theorem towerRetraction_coeff (l : List (TwistData G X)) (P : TowerStage.{u, v, w} G X)
    (p : List ℕ) (g : G) : towerRetraction l P p ((twistTower l P).coeff g) = P.coeff g := by
  rw [← towerInclusion_coeff, towerRetraction_towerInclusion]

@[simp]
theorem towerRetraction_comp_coeff (l : List (TwistData G X)) (P : TowerStage.{u, v, w} G X)
    (p : List ℕ) : (towerRetraction l P p).comp (twistTower l P).coeff = P.coeff :=
  MonoidHom.ext (towerRetraction_coeff l P p)

/-- The base of the tower embeds in its top group. -/
theorem towerInclusion_injective (l : List (TwistData G X)) (P : TowerStage.{u, v, w} G X) :
    Function.Injective (towerInclusion l P) :=
  Function.LeftInverse.injective (towerRetraction_towerInclusion l P [])

/-- For a tower of `L` steps and exponents `p = (p₁, …, p_m)` with `m ≤ L`, the retraction with
exponents `p` sends the value of a word at the top point of the tower to its value at the point
`φ_{m,p} v` ([IFT], p. 104, `λ_β ξ_p = φ_{2K,p} β`, the case `m = L`). The bound `m ≤ L` is
needed: the retraction ignores the entries of `p` beyond the `L`-th, whereas `phi` continues the
sequence of twists periodically. -/
theorem eval_towerRetraction (l : List (TwistData G X)) (P : TowerStage.{u, v, w} G X) {p : List ℕ}
    (hp : p.length ≤ l.length) (w : GX G X) :
    towerRetraction l P p (eval (twistTower l P).coeff (twistTower l P).point w) =
      eval P.coeff P.point (phi (l.map TwistData.toMulAut) p w) := by
  -- The tower along `d :: l` is, by definition, the tower along `l` over the lift along `d`;
  -- the types of the stages only agree up to unfolding, so the steps are glued by `Eq.trans`.
  induction l generalizing P p with
  | nil =>
    rw [List.map_nil, phi_nil_left, MulAut.one_apply]
    rfl
  | cons d l ih =>
    rw [towerRetraction_cons_apply]
    refine (congrArg _ (ih (P.lift d) (by grind))).trans <|
      (retraction_eval_twistLift d.e _ (B := d.A ^ p.headD 0)
        (by rw [zpow_natCast, map_pow]) _).trans ?_
    rcases p with _ | ⟨k, q⟩
    · simp
    · rw [List.map_cons, phi_cons_cons _ _ _ (by simpa using hp)]
      simp

namespace TowerStage

/-- A tower is nondegenerate when at every step the word of the twist datum has nontrivial value
at the point of the stage below, so that every step extends the centralizer of a nonidentity
element. -/
def IsNondegenerate (P : TowerStage.{u, v, w} G X) (l : List (TwistData G X)) : Prop :=
  ∀ i (hi : i < l.length),
    eval (twistTower (l.take i) P).coeff (twistTower (l.take i) P).point l[i].A ≠ 1

theorem isNondegenerate_iff (P : TowerStage.{u, v, w} G X) (l : List (TwistData G X)) :
    P.IsNondegenerate l ↔ ∀ i (hi : i < l.length),
      eval (twistTower (l.take i) P).coeff (twistTower (l.take i) P).point l[i].A ≠ 1 :=
  Iff.rfl

@[simp]
theorem isNondegenerate_nil (P : TowerStage.{u, v, w} G X) : P.IsNondegenerate [] :=
  fun _ hi => absurd hi (Nat.not_lt_zero _)

theorem isNondegenerate_cons_iff (P : TowerStage.{u, v, w} G X) (d : TwistData G X)
    (l : List (TwistData G X)) :
    P.IsNondegenerate (d :: l) ↔ eval P.coeff P.point d.A ≠ 1 ∧ (P.lift d).IsNondegenerate l := by
  -- The stages of the tower along `d :: l` are, by definition, the base and the stages of the tower
  -- along `l` over the lift along `d`.
  refine ⟨fun h => ⟨h 0 (by simp), fun i hi => h (i + 1) (by simpa)⟩, fun ⟨h0, h⟩ i hi => ?_⟩
  rcases i with _ | i
  · exact h0
  · exact h i (by simpa using hi)

/-- A tower along twist data whose words all have nontrivial values at the base point is
nondegenerate. -/
theorem isNondegenerate_of_forall_ne_one {P : TowerStage.{u, v, w} G X} {l : List (TwistData G X)}
    (hl : ∀ d ∈ l, eval P.coeff P.point d.A ≠ 1) : P.IsNondegenerate l := fun i hi heq =>
  hl l[i] (List.getElem_mem hi) <| by
    -- The retraction of the stage with all exponents zero sends the value of the word to its value
    -- at the base point.
    simpa [heq] using (eval_towerRetraction (l.take i) P (p := []) (by simp) l[i].A).symm

end TowerStage

/-- A nondegenerate tower over a fully residually free group is fully residually free ([IFT],
§7.2, proof of Proposition 5: the intermediate groups are fully residually free). -/
theorem isFullyResiduallyFree_twistTower {P : TowerStage.{u, v, w} G X}
    (hP : IsFullyResiduallyFree P.carrier) {l : List (TwistData G X)} (hl : P.IsNondegenerate l) :
    IsFullyResiduallyFree (twistTower l P).carrier := by
  induction l generalizing P with
  | nil => exact hP
  | cons d l ih =>
    obtain ⟨hd, hl⟩ := (P.isNondegenerate_cons_iff d l).1 hl
    exact ih (isFullyResiduallyFree_centralizerExt hP hd) hl

/-- The point of a nondegenerate tower over a fully residually free group solves every system that
the twists fix and that the base point solves ([IFT], §7.2, proof of Proposition 4: the mapping
`α_{4n-1}` gives rise to a `G`-homomorphism `G_S → G_{4n-1}`). -/
theorem twistTower_mem_V {P : TowerStage.{u, v, w} G X} (hP : IsFullyResiduallyFree P.carrier)
    {l : List (TwistData G X)} (hl : P.IsNondegenerate l) {S : Set (GX G X)}
    (hS : ∀ d ∈ l, ∀ s ∈ S, twistHom d.A d.e s = s) (hv : P.point ∈ V P.coeff S) :
    (twistTower l P).point ∈ V (twistTower l P).coeff S := by
  induction l generalizing P with
  | nil => exact hv
  | cons d l ih =>
    obtain ⟨hd, hl⟩ := (P.isNondegenerate_cons_iff d l).1 hl
    exact ih (isFullyResiduallyFree_centralizerExt hP hd) hl
      (fun d' hd' => hS d' (List.mem_cons_of_mem _ hd'))
      (twistLift_mem_V hP.isBP hP.isCSA hd (Commute.refl _) d.twistHom_self
        (hS d List.mem_cons_self) hv)

/-! ### The one-commutator equation -/

/-- For the equation `x⁻¹ y⁻¹ x y = a⁻¹ b⁻¹ a b` over the free group `F(a, b)`
(`TauCeti.GroupAlgGeom.Quadratic.oneCommutatorEquation`), the point of the tower of the solution
`(a, b)` along `J` rounds of the twist data of the basic sequence `y ↦ x y`, `x ↦ y x`, `y ↦ x y`
is a solution ([IFT], §7.2, p. 102, for `n = 1`; the point `λ_β` there is the case `J = 2`). -/
theorem twistTower_mem_V_oneCommutatorEquation (J : ℕ) :
    (twistTower (List.replicate J (basicWordSeqData (G := FreeGroup (Fin 2)) (x := ![0])
        (y := ![1]) (z := Fin.elim0) (by decide) Fin.elim0)).flatten
        ⟨FreeGroup (Fin 2), .id _, ![.of 0, .of 1]⟩).point ∈
      V (twistTower (List.replicate J (basicWordSeqData (G := FreeGroup (Fin 2)) (x := ![0])
        (y := ![1]) (z := Fin.elim0) (by decide) Fin.elim0)).flatten
        ⟨FreeGroup (Fin 2), .id _, ![.of 0, .of 1]⟩).coeff
        {Quadratic.oneCommutatorEquation (.of 0) (.of 1)} := by
  refine twistTower_mem_V (isFullyResiduallyFree_of_isFreeGroup (G := FreeGroup (Fin 2)))
    (TowerStage.isNondegenerate_of_forall_ne_one ?_) (fun d hd s hs => ?_)
    (Quadratic.mem_V_oneCommutatorEquation.2 rfl)
  · simp [basicWordSeqData_def, or_imp, forall_and]
  · obtain ⟨l, hl, hdl⟩ := List.mem_flatten.1 hd
    obtain rfl := List.eq_of_mem_replicate hl
    have hw : Quadratic.oneCommutatorEquation (.of 0 : FreeGroup (Fin 2)) (.of 1) =
        basicWord ![0] ![1] Fin.elim0 Fin.elim0 *
          inl ⁅(FreeGroup.of (0 : Fin 2))⁻¹, (FreeGroup.of 1)⁻¹⁆⁻¹ := by
      rw [Quadratic.oneCommutatorEquation_def, basicWord_def]
      congr 1
      simp [commAtom_def]
    rw [Set.mem_singleton_iff.1 hs, hw, map_mul, twistHom_basicWord_of_mem_basicWordSeqData _ _ hdl,
      twistHom_inl]

end TauCeti.GroupAlgGeom.Lift
