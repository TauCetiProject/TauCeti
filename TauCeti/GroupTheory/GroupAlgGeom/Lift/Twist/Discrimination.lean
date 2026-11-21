/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Lift.Twist.Map
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite
import TauCeti.Data.List.TakeDrop

/-!
# Twist towers are discriminated along dominated exponents

Let `v : X → H` be a point of `G[X]` in a group `H` and `d₁, …, d_L` twist data. The tower
`H = Z₀ ≤ Z₁ ≤ ⋯ ≤ Z_L` of extensions of centralizers along the twists, with its top point `λ`
(`TauCeti.GroupAlgGeom.Lift.twistTower`, [IFT], §7.2, Proposition 4), retracts onto `H` with
exponents `p = (p₁, …, p_L)` (`TauCeti.GroupAlgGeom.Lift.towerRetraction`), sending `λ` to the
twisted point `φ_{L,p} v` (`TauCeti.GroupAlgGeom.Lift.eval_towerRetraction`). This file shows that
over a CSA group with the big powers property these retractions discriminate a nondegenerate
tower: every finite set of nonidentity elements of the tower is kept by the retractions with
all tuples `p` of `L` natural numbers in which each exponent is large compared with the earlier
ones (`exists_bound_forall_towerRetraction_ne_one`). In particular every word with nontrivial
value at the top point keeps a nontrivial value at `φ_{L,p} v` for these tuples
(`exists_bound_forall_eval_phi_ne_one`), and the kernel of `λ` is the set of words vanishing at
all the points `φ_{L,p} v` with `p` a tuple of `L` natural numbers (`eval_twistTower_eq_one_iff`).

The proof retracts the bottom letter first. Morphisms of stages
(`TauCeti.GroupAlgGeom.Lift.TowerStage.Hom`) that eventually keep every nonidentity element of the
base induce homomorphisms of towers that eventually keep every nonidentity element of the tower
(`TowerStage.Hom.eventually_tower_ne_one`); for one step this is the normal form theorem for the
amalgams (`TauCeti.LimitGroup.CentralizerExt.eventually_map_ne_one`). The retractions `t₁ ↦ u₁ ^ k`
of the first step are morphisms onto the stage twisted `k` times
(`TauCeti.GroupAlgGeom.Lift.TowerStage.liftRetraction`), and by the theorem of [IFT], §2.5, they
eventually keep every nonidentity element
(`TauCeti.LimitGroup.CentralizerExt.exists_forall_retraction_ne_one`). So for large `k` the tower
over the twisted point `v ∘ γ₁ ^ k` is again nondegenerate and keeps the given elements; this is
why the bound for each exponent depends on the earlier ones.

The order of the quantifiers matters. Retracting the top letter first, as in [IFT], §2.5, gives
instead the tuples in which each exponent is large compared with the later ones. Neither order
gives all tuples with all exponents large: for two successive extensions of the centralizer of one
element `u`, by `t₁` and then by `t₂`, the element `t₂ t₁⁻¹` is nontrivial but every tuple with two
equal exponents kills it. The corollary of [IFT], §2.5, which claims all such tuples, is false as
stated.

If the twists fix every equation of a system `S` and `v` is a solution of `S`, the twisted points
`φ_{L,p} v` are solutions, so for a nondegenerate tower over a CSA group with the big powers
property every word of the radical of `S` vanishes at the top point
(`eval_twistTower_eq_one_of_mem_Rad`): the top point is a point of the coordinate group `G_{R(S)}`,
which maps to the tower (`twistTowerGHom`). For the basic tower of a solution `β` of a standard
orientable quadratic equation (`TauCeti.GroupAlgGeom.Lift.basicTower`) this is the homomorphism
`λ_β : G_{R(S)} → G(U, T)` of [IFT], §7.2, Proposition 4 (`eval_basicTower_eq_one_of_mem_Rad`); no
regularity of the equation is needed.

## Main definitions

* `TauCeti.GroupAlgGeom.Lift.twistTowerGHom`: the `G`-homomorphism from the coordinate group of a
  system fixed by the twists to a nondegenerate tower over a solution, over a CSA group with the
  big powers property.

## Main results

* `TauCeti.GroupAlgGeom.Lift.TowerStage.Hom.eventually_tower_ne_one`: morphisms that eventually
  keep every nonidentity element of the base induce homomorphisms of towers that eventually keep
  every nonidentity element of the tower.
* `TauCeti.GroupAlgGeom.Lift.exists_bound_forall_towerRetraction_ne_one`: the retractions with
  exponent tuples dominating a bound function keep a given finite set of nonidentity elements.
* `TauCeti.GroupAlgGeom.Lift.exists_bound_forall_eval_phi_ne_one`: survival at `φ_{L,p} v` for
  exponent tuples dominating a bound function.
* `TauCeti.GroupAlgGeom.Lift.eval_twistTower_eq_one_iff`: the kernel of the top point, tested on
  the tuples of `L` natural numbers.
* `TauCeti.GroupAlgGeom.Lift.eval_twistTower_eq_one_of_mem_Rad`,
  `TauCeti.GroupAlgGeom.Lift.eval_basicTower_eq_one_of_mem_Rad`: over a CSA group with the big
  powers property, the top point of a nondegenerate tower over a solution of a system fixed by the
  twists, in particular of a nondegenerate basic tower of a solution, vanishes on the radical.

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

/-- If morphisms of stages `fᵢ : P → Qᵢ` eventually keep every nonidentity element of the base
along a filter, the induced homomorphisms of the towers along any list of twist data eventually
keep every nonidentity element of the tower. -/
theorem Hom.eventually_tower_ne_one {ι : Type*} {F : Filter ι} {P : TowerStage.{u, v, w} G X}
    {Q : ι → TowerStage.{u, v, w} G X} (f : ∀ i, P.Hom (Q i))
    (hf : ∀ g : P.carrier, g ≠ 1 → ∀ᶠ i in F, f i g ≠ 1) (l : List (TwistData G X))
    {x : (twistTower l P).carrier} (hx : x ≠ 1) : ∀ᶠ i in F, (f i).tower l x ≠ 1 := by
  induction l generalizing P Q with
  | nil => exact hf x hx
  | cons d l ih =>
    -- The lifts of the `fᵢ` are the maps of extensions of centralizers they induce, followed by
    -- isomorphisms, so they eventually keep every nonidentity element.
    refine ih (fun i => (f i).lift d) (fun g hg => ?_) hx
    filter_upwards [CentralizerExt.eventually_map_ne_one (f := fun i => (f i).toMonoidHom) hf _ 1
      hg] with i hi
    rw [lift_apply]
    exact (MulEquiv.map_ne_one_iff _).2 hi

/-- If morphisms of stages `fᵢ : P → Qᵢ` eventually keep every nonidentity element of the base,
the towers over the `Qᵢ` along a list along which the tower over `P` is nondegenerate are
eventually nondegenerate. -/
private theorem Hom.eventually_isNondegenerate {ι : Type*} {F : Filter ι}
    {P : TowerStage.{u, v, w} G X} {Q : ι → TowerStage.{u, v, w} G X} (f : ∀ i, P.Hom (Q i))
    (hf : ∀ g : P.carrier, g ≠ 1 → ∀ᶠ i in F, f i g ≠ 1) {l : List (TwistData G X)}
    (hl : P.IsNondegenerate l) : ∀ᶠ i in F, (Q i).IsNondegenerate l := by
  have h (j : Fin l.length) := (Hom.eventually_tower_ne_one f hf (l.take j)
    ((P.isNondegenerate_iff l).1 hl j j.isLt)).mono fun i hi => by rwa [Hom.map_eval] at hi
  filter_upwards [eventually_all.2 h] with i hi using
    ((Q i).isNondegenerate_iff l).2 fun j hj => hi ⟨j, hj⟩

end TowerStage

/-! ### Discrimination along dominated exponents -/

/-- **Discrimination along dominated exponents.** Let `P` be a point in a CSA group with the big
powers property and `l` a list of `L` twist data along which the tower over `P` is nondegenerate.
For every finite set `M` of nonidentity elements of the tower there is a bound function `N` such
that the retraction of the tower with exponents `p` keeps every element of `M`, for every tuple `p`
of `L` natural numbers in which each exponent is at least `N` of the tuple of the earlier ones. -/
theorem exists_bound_forall_towerRetraction_ne_one {P : TowerStage.{u, v, w} G X}
    (hBP : Group.IsBP P.carrier) (hCSA : Group.IsCSA P.carrier) {l : List (TwistData G X)}
    (hl : P.IsNondegenerate l) {M : Finset (twistTower l P).carrier} (hM : ∀ x ∈ M, x ≠ 1) :
    ∃ N : List ℕ → ℕ, ∀ p : List ℕ, p.length = l.length →
      (∀ i (hi : i < p.length), N (p.take i) ≤ p[i]) → ∀ x ∈ M, towerRetraction l P p x ≠ 1 := by
  classical
  induction l generalizing P with
  | nil => exact ⟨0, fun p _ _ x hx => by rw [towerRetraction_nil]; exact hM x hx⟩
  | cons d l ih =>
    obtain ⟨hd, hl⟩ := (P.isNondegenerate_cons_iff d l).1 hl
    -- The retractions `t ↦ u ^ k` of the first step eventually keep every nonidentity element, so
    -- for `k` large the tower along `l` over the point twisted `k` times along `d` is
    -- nondegenerate and the homomorphism onto it induced by the retraction keeps `M`.
    have hf (g : (P.lift d).carrier) (hg : g ≠ 1) :
        ∀ᶠ k : ℕ in atTop, P.liftRetraction d k g ≠ 1 := by
      obtain ⟨N, hN⟩ := CentralizerExt.exists_forall_retraction_ne_one hBP hCSA hd hg
      exact eventually_atTop.2 ⟨N, fun k hk => by
        rw [TowerStage.liftRetraction_apply]
        exact hN k hk⟩
    obtain ⟨K, hK⟩ := eventually_atTop.1 ((TowerStage.Hom.eventually_isNondegenerate _ hf hl).and
      ((eventually_all_finset M).2 fun x hx => TowerStage.Hom.eventually_tower_ne_one _ hf l
        (hM x hx)))
    -- The stage twisted `k` times has the same group as `P`; the induction hypothesis gives a
    -- bound function for the remaining exponents.
    have hN (k : ℕ) : ∃ N : List ℕ → ℕ, K ≤ k → ∀ q : List ℕ, q.length = l.length →
        (∀ i (hi : i < q.length), N (q.take i) ≤ q[i]) → ∀ x ∈ M,
          towerRetraction (d :: l) P (k :: q) x ≠ 1 := by
      by_cases hk : K ≤ k
      · obtain ⟨N, hN⟩ := ih (P := P.twisted d k) hBP hCSA (hK k hk).1
          (M := M.image ((P.liftRetraction d k).tower l)) (Finset.forall_mem_image.2 (hK k hk).2)
        refine ⟨N, fun _ q hq hdom x hx h1 => hN q hq hdom _ (Finset.mem_image_of_mem _ hx) ?_⟩
        rw [towerRetraction_cons_apply, List.headD_cons, List.tail_cons] at h1
        exact ((TowerStage.Hom.towerRetraction_tower _ l q x).trans
          (TowerStage.liftRetraction_apply _ _ _ _)).trans h1
      · exact ⟨0, fun h => absurd h hk⟩
    choose N hN using hN
    refine ⟨fun | [] => K | k :: q => N k q, ?_⟩
    rintro (_ | ⟨k, q⟩) hp hdom x hx
    · simp at hp
    · exact hN k (hdom 0 (by simp)) q (by simpa using hp) (fun i hi => hdom (i + 1) (by simpa)) x hx

/-- **Survival along dominated exponents.** Let `P` be a point in a CSA group with the big powers
property and `l` a list of `L` twist data along which the tower over `P` is nondegenerate. For
every finite set `M` of words with nontrivial values at the top point of the tower there is a
bound function `N` such that every word of `M` has nontrivial value at `φ_{L,p} v` for every tuple
`p` of `L` natural numbers in which each exponent is at least `N` of the tuple of the earlier
ones. -/
theorem exists_bound_forall_eval_phi_ne_one {P : TowerStage.{u, v, w} G X}
    (hBP : Group.IsBP P.carrier) (hCSA : Group.IsCSA P.carrier) {l : List (TwistData G X)}
    (hl : P.IsNondegenerate l) {M : Finset (GX G X)}
    (hM : ∀ w ∈ M, eval (twistTower l P).coeff (twistTower l P).point w ≠ 1) :
    ∃ N : List ℕ → ℕ, ∀ p : List ℕ, p.length = l.length →
      (∀ i (hi : i < p.length), N (p.take i) ≤ p[i]) →
        ∀ w ∈ M, eval P.coeff P.point (phi (l.map TwistData.toMulAut) p w) ≠ 1 := by
  classical
  obtain ⟨N, hN⟩ := exists_bound_forall_towerRetraction_ne_one hBP hCSA hl
    (M := M.image (eval (twistTower l P).coeff (twistTower l P).point))
    (Finset.forall_mem_image.2 hM)
  refine ⟨N, fun p hp hdom w hw => ?_⟩
  rw [← eval_towerRetraction l P hp.le]
  exact hN p hp hdom _ (Finset.mem_image_of_mem _ hw)

/-- The kernel of the point of a nondegenerate tower of `L` steps over a CSA group with the big
powers property is the set of words that vanish at every point `φ_{L,p} v`, `p` a tuple of `L`
natural numbers. -/
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
    obtain ⟨p, hp, hdom⟩ := List.exists_length_eq_forall_le_getElem N l.length
    exact hN p hp hdom w (Finset.mem_singleton_self w) (h p hp)

/-! ### Points of coordinate groups -/

/-- Let `P` be a solution of a system `S` in a CSA group with the big powers property, `l` a list
of twist data whose substitutions fix every equation of `S`, and suppose that the tower over `P`
along `l` is nondegenerate. Then every word of the radical of `S` vanishes at the point of the
tower. -/
theorem eval_twistTower_eq_one_of_mem_Rad {P : TowerStage.{u, v, w} G X}
    (hBP : Group.IsBP P.carrier) (hCSA : Group.IsCSA P.carrier) {l : List (TwistData G X)}
    (hl : P.IsNondegenerate l) {S : Set (GX G X)} (hS : ∀ d ∈ l, ∀ s ∈ S, twistHom d.A d.e s = s)
    (hv : P.point ∈ V P.coeff S) {w : GX G X} (hw : w ∈ Rad P.coeff S) :
    eval (twistTower l P).coeff (twistTower l P).point w = 1 := by
  refine (eval_twistTower_eq_one_iff hBP hCSA hl w).2 fun p _ => ?_
  -- The automorphism `φ_{L,p}` of `G[X]` fixes the coefficients and the equations of `S`, so it
  -- maps the radical of `S` into itself.
  have hfix {u : GX G X} (hu : ∀ d ∈ l, twistHom d.A d.e u = u) :
      phi (l.map TwistData.toMulAut) p u = u :=
    phi_apply_of_forall_mem (by simpa using hu) p
  have hσ (g : G) := hfix fun d _ => twistHom_inl d.A d.e g
  simpa using mem_Rad.1 (Rad_preimage_le_comap P.coeff (.ofMulEquiv _ hσ) S
    (Rad_monotone P.coeff (fun s hs => by simpa [hfix fun d hd => hS d hd s hs]) hw)) P.point hv

/-- The `G`-homomorphism `G_{R(S)} → Z_L` from the coordinate group of a system `S` over the
group of `P` to a nondegenerate tower over a solution `P` of `S` in a CSA group with the big powers
property, along twist data whose substitutions fix every equation of `S`: the evaluation at the
point of the tower. For the basic tower of a solution `β` of a standard orientable quadratic
equation (`TauCeti.GroupAlgGeom.Lift.basicTower`), this is the homomorphism
`λ_β : G_{R(S)} → G(U, T)` of [IFT], §7.2, Proposition 4. -/
noncomputable def twistTowerGHom {P : TowerStage.{u, v, w} G X} (hBP : Group.IsBP P.carrier)
    (hCSA : Group.IsCSA P.carrier) {l : List (TwistData G X)} (hl : P.IsNondegenerate l)
    {S : Set (GX G X)} (hS : ∀ d ∈ l, ∀ s ∈ S, twistHom d.A d.e s = s)
    (hv : P.point ∈ V P.coeff S) : GHom (CoordGroup.coeff P.coeff S) (twistTower l P).coeff where
  toMonoidHom := QuotientGroup.lift _ (eval (twistTower l P).coeff (twistTower l P).point)
    fun _ hw => MonoidHom.mem_ker.2 (eval_twistTower_eq_one_of_mem_Rad hBP hCSA hl hS hv hw)
  map_coeff' g := by simp

@[simp]
theorem twistTowerGHom_mk {P : TowerStage.{u, v, w} G X} (hBP : Group.IsBP P.carrier)
    (hCSA : Group.IsCSA P.carrier) {l : List (TwistData G X)} (hl : P.IsNondegenerate l)
    {S : Set (GX G X)} (hS : ∀ d ∈ l, ∀ s ∈ S, twistHom d.A d.e s = s)
    (hv : P.point ∈ V P.coeff S) (w : GX G X) :
    twistTowerGHom hBP hCSA hl hS hv (w : CoordGroup P.coeff S) =
      eval (twistTower l P).coeff (twistTower l P).point w := by
  simp [twistTowerGHom]

/-- The point of a nondegenerate basic tower of a solution `β` of a standard orientable quadratic
equation `S = 1` over a CSA group with the big powers property is a point of the coordinate group:
every word of the radical of `S` vanishes at it ([IFT], §7.2, Proposition 4,
`λ_β : G_{R(S)} → G(U, T)`). -/
theorem eval_basicTower_eq_one_of_mem_Rad (hBP : Group.IsBP G) (hCSA : Group.IsCSA G)
    {S : Quadratic.Standard G X} (hS : S.IsOrientable) {β : X → G}
    (hβ : β ∈ V (.id G) {S.toWord}) (J : ℕ)
    (hnd : (⟨G, .id G, β⟩ : TowerStage.{u, v, u} G X).IsNondegenerate
      (List.replicate J (basicSeqData S hS)).flatten) {w : GX G X}
    (hw : w ∈ Rad (.id G) {S.toWord}) :
    eval (basicTower S hS β J).coeff (basicTower S hS β J).point w = 1 := by
  rw [basicTower_def]
  refine eval_twistTower_eq_one_of_mem_Rad (P := ⟨G, .id G, β⟩) hBP hCSA hnd
    (fun d hd s hs => ?_) hβ hw
  obtain ⟨_, hl, hdl⟩ := List.mem_flatten.1 hd
  obtain rfl := List.eq_of_mem_replicate hl
  rw [Set.mem_singleton_iff.1 hs, twistHom_toWord_of_mem_basicSeqData hS hdl]

end TauCeti.GroupAlgGeom.Lift
