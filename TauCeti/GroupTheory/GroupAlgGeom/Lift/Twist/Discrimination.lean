/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Lift.Twist.Tower
public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Map
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite

/-!
# Twist towers are discriminated along dominated exponents

Let `v : X → H` be a point of `G[X]` in a group `H` and `d₁, …, d_L` twist data. The tower
`H = Z₀ ≤ Z₁ ≤ ⋯ ≤ Z_L` of extensions of centralizers along the twists, with its top point `λ`
(`TauCeti.GroupAlgGeom.Lift.twistTower`, [IFT], §7.2, Proposition 4), retracts onto `H` with
exponents `p = (p₁, …, p_L)`, sending `λ` to the twisted point `φ_{L,p} v`
(`TauCeti.GroupAlgGeom.Lift.eval_towerRetraction`). This file shows that over a CSA group with
the big powers property these retractions discriminate the image of `λ`: every word with
nontrivial value at the top point of a nondegenerate tower keeps a nontrivial value at
`φ_{L,p} v` for all tuples `p` in which each exponent is large compared with the earlier ones
(`exists_bound_forall_eval_phi_ne_one`). In particular the kernel of `λ` is the set of words
vanishing at all the points `φ_{L,p} v` (`eval_twistTower_eq_one_iff`).

A morphism of stages (`TowerStage.Hom`, a `G`-homomorphism carrying one point to the other)
induces homomorphisms of the towers built on them (`TowerStage.Hom.tower`). If morphisms eventually
keep every nonidentity element of the base, the induced homomorphisms of towers eventually keep
every nonidentity element of the tower (`TowerStage.Hom.eventually_tower_ne_one`); for one step
this is the normal form theorem for the amalgams
(`TauCeti.LimitGroup.CentralizerExt.eventually_map_ne_one`). The retractions `t₁ ↦ u₁ ^ k` of
the first step are morphisms onto the stage twisted `k` times (`TowerStage.liftRetraction`,
[IFT], §7.2, (84)–(85)), and by the theorem of [IFT], §2.5, they eventually keep every
nonidentity element (`TowerStage.eventually_liftRetraction_ne_one`). So for large `k` the tower
over the twisted point `v ∘ γ₁ ^ k` is again nondegenerate with the given words nontrivial at its
top; this is why the bound for each exponent depends on the earlier ones.

The order of the quantifiers matters. Retracting the top letter first, as in [IFT], §2.5, gives
instead the tuples in which each exponent is large compared with the later ones. Neither order
gives all tuples with all exponents large: for two successive extensions of the centralizer of one
element `u`, by `t₁` and then by `t₂`, the element `t₂ t₁⁻¹` is nontrivial but every tuple with two
equal exponents kills it. The corollary of [IFT], §2.5, which claims all such tuples, is false as
stated.

For a standard orientable quadratic equation `S = 1` and a solution `β`, lifting `β` along `J`
rounds of the twist data of the basic sequence gives the tower of [IFT], §7.2, Proposition 4
(`basicTower`, the case `J = 2`). When it is nondegenerate, every word of the radical of `S`
vanishes at its top point (`eval_basicTower_eq_one_of_mem_Rad`): the top point is a point of the
coordinate group `G_{R(S)}` (the homomorphism `λ_β : G_{R(S)} → G(U, T)` of [IFT]). No regularity
of `S` is needed, since the twisted points `φ_{JK,p} β` are solutions.

## Main definitions

* `TauCeti.GroupAlgGeom.Lift.TowerStage.Hom`: morphisms of stages.
* `TauCeti.GroupAlgGeom.Lift.TowerStage.Hom.tower`: the induced homomorphism of towers.
* `TauCeti.GroupAlgGeom.Lift.TowerStage.liftRetraction`: the retraction `t ↦ u ^ k` of one step,
  as a morphism to the twisted stage.
* `TauCeti.GroupAlgGeom.Lift.basicTower`: the tower of `J` rounds of the basic sequence over a
  point.

## Main results

* `TauCeti.GroupAlgGeom.Lift.TowerStage.Hom.eventually_tower_ne_one`: morphisms that eventually
  keep every nonidentity element of the base induce homomorphisms of towers that eventually keep
  every nonidentity element of the tower.
* `TauCeti.GroupAlgGeom.Lift.exists_bound_forall_eval_phi_ne_one`: survival at `φ_{L,p} v` for
  exponent tuples dominating a bound function.
* `TauCeti.GroupAlgGeom.Lift.eval_twistTower_eq_one_iff`: the kernel of the top point.
* `TauCeti.GroupAlgGeom.Lift.eval_basicTower_eq_one_of_mem_Rad`: the top point of the basic tower
  of a solution vanishes on the radical.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.5 (the theorem of [40] and its corollary) and §7.2, (84)–(85), Proposition 4 and
  p. 104.
-/

public section

universe u v w

open Monoid.Coprod TauCeti.LimitGroup Filter

namespace TauCeti.GroupAlgGeom.Lift

variable {G : Type u} [Group G] {X : Type v}

namespace TowerStage

/-- Evaluating at the stage twisted `k` times along a twist datum is evaluating at the stage after
applying the `k`-th power of the twist. -/
theorem eval_twisted (P : TowerStage.{u, v, w} G X) (d : TwistData G X) (k : ℤ) (w : GX G X) :
    eval (P.twisted d k).coeff (P.twisted d k).point w =
      eval P.coeff P.point ((d.toMulAut ^ k) w) := by
  have h := DFunLike.congr_fun (eval_wordMap (ι := P.coeff)
    (.ofMulEquiv (d.toMulAut ^ k) fun g => by simp) P.point) w
  simp only [GHom.coe_ofMulEquiv, MonoidHom.comp_apply, GHom.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass] at h
  -- The point of the twisted stage is, by definition, the word map of the twist; the two sides
  -- differ only in the (definitionally equal) types of the stages, which `simpa` does not unfold.
  exact h

/-! ### Morphisms of stages -/

/-- A morphism of stages: a `G`-homomorphism of the groups (`TauCeti.GroupAlgGeom.GHom`) carrying
the point of the first stage to the point of the second. -/
structure Hom (P Q : TowerStage.{u, v, w} G X) extends GHom P.coeff Q.coeff where
  /-- The homomorphism carries the point of the first stage to the point of the second. -/
  comp_point : toFun ∘ P.point = Q.point

/-- The `G`-homomorphism underlying a morphism of stages. -/
add_decl_doc Hom.toGHom

namespace Hom

variable {P Q : TowerStage.{u, v, w} G X}

/-- A morphism of stages carries the value of a word at the first point to its value at the
second. -/
theorem map_eval (f : P.Hom Q) (w : GX G X) :
    f.toMonoidHom (eval P.coeff P.point w) = eval Q.coeff Q.point w :=
  (GroupAlgGeom.map_eval f.toGHom w).trans (by rw [← f.comp_point]; rfl)

/-- A morphism of stages lifts to their lifts along a twist datum: the homomorphism of extensions
of centralizers induced by it (`TauCeti.LimitGroup.CentralizerExt.map`), followed by the
identification of the extensions of the centralizers of the equal elements `f (A(v))` and
`A(f ∘ v)`. -/
noncomputable def lift (f : P.Hom Q) (d : TwistData G X) : (P.lift d).Hom (Q.lift d) where
  toMonoidHom :=
    (CentralizerExt.congr (n := 1) (u := f.toMonoidHom (eval P.coeff P.point d.A))
      (v := eval Q.coeff Q.point d.A) (by rw [f.map_eval])).toMonoidHom.comp
      (CentralizerExt.map f.toMonoidHom _ 1)
  map_coeff' g := by
    -- The groups of the lifted stages are extensions of centralizers by definition, with the
    -- coefficient maps through `CentralizerExt.of`.
    change CentralizerExt.congr _ (CentralizerExt.map f.toMonoidHom _ 1
      (CentralizerExt.of (P.coeff g))) = CentralizerExt.of (Q.coeff g)
    rw [CentralizerExt.map_of, CentralizerExt.congr_of, ← f.map_coeff' g]
    rfl
  comp_point := funext fun x => by
    -- The points of the lifted stages are the lifted points by definition.
    change CentralizerExt.congr _ (CentralizerExt.map f.toMonoidHom _ 1
      (twistLift (eval P.coeff P.point d.A) P.point d.e x)) =
        twistLift (eval Q.coeff Q.point d.A) Q.point d.e x
    simp only [twistLift_apply, map_mul, map_zpow, CentralizerExt.map_t, CentralizerExt.map_of,
      CentralizerExt.congr_t, CentralizerExt.congr_of]
    rw [← f.comp_point]
    rfl

theorem toMonoidHom_lift (f : P.Hom Q) (d : TwistData G X) :
    (f.lift d).toMonoidHom =
      (CentralizerExt.congr (n := 1) (u := f.toMonoidHom (eval P.coeff P.point d.A))
        (v := eval Q.coeff Q.point d.A) (by rw [f.map_eval])).toMonoidHom.comp
        (CentralizerExt.map f.toMonoidHom _ 1) := (rfl)

/-- The homomorphism of towers induced by a morphism of their bases. -/
noncomputable def tower {P Q : TowerStage.{u, v, w} G X} : (l : List (TwistData G X)) → P.Hom Q →
    (twistTower l P).Hom (twistTower l Q)
  | [], f => f
  | d :: l, f => tower l (f.lift d)

@[simp]
theorem tower_nil (f : P.Hom Q) : f.tower [] = f := (rfl)

@[simp]
theorem tower_cons (f : P.Hom Q) (d : TwistData G X) (l : List (TwistData G X)) :
    f.tower (d :: l) = (f.lift d).tower l := (rfl)

end Hom

/-- The retraction `t ↦ u ^ k` of the lift along `d`, as a morphism to the stage twisted `k`
times along `d` ([IFT], §7.2: the transformation (84) is the specialisation `t ↦ u ^ q` of
(85)). -/
noncomputable def liftRetraction (P : TowerStage.{u, v, w} G X) (d : TwistData G X) (k : ℤ) :
    (P.lift d).Hom (P.twisted d k) where
  toMonoidHom := CentralizerExt.retraction fun _ => k
  map_coeff' g := CentralizerExt.retraction_of _ (P.coeff g)
  comp_point := P.retraction_comp_lift_point d k

theorem toMonoidHom_liftRetraction (P : TowerStage.{u, v, w} G X) (d : TwistData G X) (k : ℤ) :
    (P.liftRetraction d k).toMonoidHom = CentralizerExt.retraction fun _ => k := (rfl)

/-- Over a CSA group with the big powers property, the retractions `t ↦ u ^ k` of the lift along
a twist datum with `u ≠ 1` eventually keep every nonidentity element ([IFT], §2.5, the theorem
of [40]). -/
theorem eventually_liftRetraction_ne_one (P : TowerStage.{u, v, w} G X) (d : TwistData G X)
    (hBP : Group.IsBP P.carrier) (hCSA : Group.IsCSA P.carrier) (hd : eval P.coeff P.point d.A ≠ 1)
    {g : (P.lift d).carrier} (hg : g ≠ 1) :
    ∀ᶠ k : ℕ in atTop, (P.liftRetraction d k).toMonoidHom g ≠ 1 := by
  -- The group of the lift is, by definition, the extension of the centralizer of `A(v)`.
  obtain ⟨N, hN⟩ := CentralizerExt.exists_forall_retraction_ne_one hBP hCSA hd hg
  exact eventually_atTop.2 ⟨N, fun k hk => by rw [toMonoidHom_liftRetraction]; exact hN k hk⟩

/-- If morphisms of stages `fᵢ : P → Qᵢ` eventually keep every nonidentity element of the base
along a filter, the induced homomorphisms of the towers along any list of twist data eventually
keep every nonidentity element of the tower. -/
theorem Hom.eventually_tower_ne_one {ι : Type*} {F : Filter ι} {P : TowerStage.{u, v, w} G X}
    {Q : ι → TowerStage.{u, v, w} G X} (f : ∀ i, P.Hom (Q i))
    (hf : ∀ g : P.carrier, g ≠ 1 → ∀ᶠ i in F, (f i).toMonoidHom g ≠ 1) (l : List (TwistData G X))
    {x : (twistTower l P).carrier} (hx : x ≠ 1) : ∀ᶠ i in F, ((f i).tower l).toMonoidHom x ≠ 1 := by
  induction l generalizing P Q with
  | nil => exact hf x hx
  | cons d l ih =>
    -- By definition, the towers along `d :: l` and their homomorphisms are those along `l` over
    -- the lifts along `d`. The lifts of the `fᵢ` are the maps of extensions of centralizers they
    -- induce, followed by isomorphisms, so they eventually keep every nonidentity element.
    refine ih (fun i => (f i).lift d) (fun g hg => ?_) hx
    filter_upwards [CentralizerExt.eventually_map_ne_one (f := fun i => (f i).toMonoidHom) hf _ 1
      hg] with i hi
    rw [toMonoidHom_lift]
    exact (MulEquiv.map_ne_one_iff _).2 hi

/-- If morphisms of stages `fᵢ : P → Qᵢ` eventually keep every nonidentity element of the base,
a word with nontrivial value at the top point of the tower over `P` eventually has nontrivial
value at the top point of the tower over `Qᵢ`. -/
private theorem Hom.eventually_eval_ne_one {ι : Type*} {F : Filter ι} {P : TowerStage.{u, v, w} G X}
    {Q : ι → TowerStage.{u, v, w} G X} (f : ∀ i, P.Hom (Q i))
    (hf : ∀ g : P.carrier, g ≠ 1 → ∀ᶠ i in F, (f i).toMonoidHom g ≠ 1) (l : List (TwistData G X))
    {w : GX G X} (hw : eval (twistTower l P).coeff (twistTower l P).point w ≠ 1) :
    ∀ᶠ i in F, eval (twistTower l (Q i)).coeff (twistTower l (Q i)).point w ≠ 1 := by
  filter_upwards [Hom.eventually_tower_ne_one f hf l hw] with i hi
  rwa [Hom.map_eval] at hi

/-- If morphisms of stages `fᵢ : P → Qᵢ` eventually keep every nonidentity element of the base,
the towers over the `Qᵢ` along a list along which the tower over `P` is nondegenerate are
eventually nondegenerate. -/
private theorem Hom.eventually_isNondegenerate {ι : Type*} {F : Filter ι}
    {P : TowerStage.{u, v, w} G X} {Q : ι → TowerStage.{u, v, w} G X} (f : ∀ i, P.Hom (Q i))
    (hf : ∀ g : P.carrier, g ≠ 1 → ∀ᶠ i in F, (f i).toMonoidHom g ≠ 1) {l : List (TwistData G X)}
    (hl : P.IsNondegenerate l) : ∀ᶠ i in F, (Q i).IsNondegenerate l := by
  have h (j : Fin l.length) :=
    Hom.eventually_eval_ne_one f hf (l.take j) ((P.isNondegenerate_iff l).1 hl j j.isLt)
  filter_upwards [eventually_all.2 h] with i hi using
    ((Q i).isNondegenerate_iff l).2 fun j hj => hi ⟨j, hj⟩

end TowerStage

/-! ### Discrimination along dominated exponents -/

/-- For every bound function `N` on tuples and every length there is a tuple of that length in
which each entry is at least `N` of the tuple of the earlier entries. -/
private theorem exists_length_eq_forall_le_getElem (N : List ℕ → ℕ) (n : ℕ) :
    ∃ p : List ℕ, p.length = n ∧ ∀ i (hi : i < p.length), N (p.take i) ≤ p[i] := by
  induction n with
  | zero => exact ⟨[], rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨p, hp, hN⟩ := ih
    refine ⟨p ++ [N p], by simp [hp], fun i hi => ?_⟩
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 (by simpa using hi)) with hi' | rfl
    · simpa [List.take_append_of_le_length hi'.le, List.getElem_append_left hi'] using hN i hi'
    · simp

/-- **Survival along dominated exponents.** Let `P` be a point in a CSA group with the big powers
property and `l` a list of twist data along which the tower over `P` is nondegenerate. For every
finite set `M` of words with nontrivial values at the top point of the tower there is a bound
function `N` such that every word of `M` has nontrivial value at `φ_{L,p} v` for every tuple `p`
of length `L` in which each exponent is at least `N` of the tuple of the earlier ones. -/
theorem exists_bound_forall_eval_phi_ne_one {P : TowerStage.{u, v, w} G X}
    (hBP : Group.IsBP P.carrier) (hCSA : Group.IsCSA P.carrier) {l : List (TwistData G X)}
    (hl : P.IsNondegenerate l) {M : Finset (GX G X)}
    (hM : ∀ w ∈ M, eval (twistTower l P).coeff (twistTower l P).point w ≠ 1) :
    ∃ N : List ℕ → ℕ, ∀ p : List ℕ, p.length = l.length →
      (∀ i (hi : i < p.length), N (p.take i) ≤ p[i]) →
        ∀ w ∈ M, eval P.coeff P.point (phi (l.map TwistData.toMulAut) p w) ≠ 1 := by
  induction l generalizing P with
  | nil =>
    -- The tower along the empty list is the base stage.
    exact ⟨0, fun p _ _ w hw => by simpa using (show eval P.coeff P.point w ≠ 1 from hM w hw)⟩
  | cons d l ih =>
    obtain ⟨hd, hl⟩ := (P.isNondegenerate_cons_iff d l).1 hl
    -- For `k` large, the tower along `l` over the point twisted `k` times along `d` is
    -- nondegenerate and the words of `M` are nontrivial at its top.
    have hf := fun g (hg : g ≠ 1) => P.eventually_liftRetraction_ne_one d hBP hCSA hd hg
    obtain ⟨K, hK⟩ := eventually_atTop.1 ((TowerStage.Hom.eventually_isNondegenerate _ hf hl).and
      ((eventually_all_finset M).2 fun w hw => TowerStage.Hom.eventually_eval_ne_one _ hf l
        (hM w hw)))
    -- The stage twisted `k` times has the same group as `P`; the induction hypothesis gives a
    -- bound function for the remaining exponents.
    have hN (k : ℕ) : ∃ N : List ℕ → ℕ, K ≤ k → ∀ q : List ℕ, q.length = l.length →
        (∀ i (hi : i < q.length), N (q.take i) ≤ q[i]) → ∀ w ∈ M,
          eval P.coeff P.point ((d.toMulAut ^ k) (phi (l.map TwistData.toMulAut) q w)) ≠ 1 := by
      by_cases hk : K ≤ k
      · obtain ⟨N, hN⟩ := ih (P := P.twisted d k) hBP hCSA (hK k hk).1 (hK k hk).2
        refine ⟨N, fun _ q hq hdom w hw => ?_⟩
        rw [← zpow_natCast, ← TowerStage.eval_twisted]
        exact hN q hq hdom w hw
      · exact ⟨0, fun h => absurd h hk⟩
    choose N hN using hN
    refine ⟨fun | [] => K | k :: q => N k q, ?_⟩
    rintro (_ | ⟨k, q⟩) hp hdom w hw
    · simp at hp
    · have hq : q.length = l.length := by simpa using hp
      rw [List.map_cons, phi_cons_cons _ _ _ (by simp [hq]), MulAut.mul_apply]
      exact hN k (hdom 0 (by simp)) q hq (fun i hi => hdom (i + 1) (by simpa)) w hw

/-- The kernel of the point of a nondegenerate tower over a CSA group with the big powers property
is the set of words that vanish at every point `φ_{L,p} v`. -/
theorem eval_twistTower_eq_one_iff {P : TowerStage.{u, v, w} G X} (hBP : Group.IsBP P.carrier)
    (hCSA : Group.IsCSA P.carrier) {l : List (TwistData G X)} (hl : P.IsNondegenerate l)
    (w : GX G X) :
    eval (twistTower l P).coeff (twistTower l P).point w = 1 ↔
      ∀ p : List ℕ, p.length = l.length →
        eval P.coeff P.point (phi (l.map TwistData.toMulAut) p w) = 1 := by
  refine ⟨fun h p hp => ?_, fun h => ?_⟩
  · rw [← eval_towerRetraction l P hp.le, h, map_one]
  · by_contra hne
    obtain ⟨N, hN⟩ := exists_bound_forall_eval_phi_ne_one hBP hCSA hl (M := {w}) (by simpa)
    obtain ⟨p, hp, hdom⟩ := exists_length_eq_forall_le_getElem N l.length
    exact hN p hp hdom w (Finset.mem_singleton_self w) (h p hp)

/-! ### The tower of the basic sequence -/

variable {S : Quadratic.Standard G X}

/-- The tower of extensions of centralizers obtained by lifting a point `β` of `G[X]` in `G` along
`J` rounds of the basic sequence of a standard orientable quadratic equation ([IFT], §7.2,
Proposition 4, for `J = 2`). -/
noncomputable def basicTower (S : Quadratic.Standard G X) (hS : S.IsOrientable) (β : X → G)
    (J : ℕ) : TowerStage.{u, v, u} G X :=
  twistTower (List.replicate J (basicSeqData S hS)).flatten ⟨G, .id G, β⟩

theorem basicTower_def (S : Quadratic.Standard G X) (hS : S.IsOrientable) (β : X → G) (J : ℕ) :
    basicTower S hS β J = twistTower (List.replicate J (basicSeqData S hS)).flatten ⟨G, .id G, β⟩ :=
  (rfl)

/-- The point of a nondegenerate tower of a solution `β` over a CSA group with the big powers
property is a point of the coordinate group: every word of the radical of `S` vanishes at it
([IFT], §7.2, Proposition 4, `λ_β : G_{R(S)} → G(U, T)`). -/
theorem eval_basicTower_eq_one_of_mem_Rad (hBP : Group.IsBP G) (hCSA : Group.IsCSA G)
    (hS : S.IsOrientable) {β : X → G} (hβ : β ∈ V (.id G) {S.toWord}) (J : ℕ)
    (hnd : (⟨G, .id G, β⟩ : TowerStage.{u, v, u} G X).IsNondegenerate
      (List.replicate J (basicSeqData S hS)).flatten) {w : GX G X}
    (hw : w ∈ Rad (.id G) {S.toWord}) :
    eval (basicTower S hS β J).coeff (basicTower S hS β J).point w = 1 := by
  rw [basicTower_def, eval_twistTower_eq_one_iff hBP hCSA hnd]
  intro p _
  rcases eq_or_ne J 0 with rfl | hJ
  · simpa using mem_Rad.1 hw β hβ
  · rw [List.map_flatten, List.map_replicate, map_toMulAut_basicSeqData,
      phi_flatten_replicate _ hJ, ← eval_twistPoint]
    exact mem_Rad.1 hw _ (twistPoint_mem_V hS hβ p)

end TauCeti.GroupAlgGeom.Lift
