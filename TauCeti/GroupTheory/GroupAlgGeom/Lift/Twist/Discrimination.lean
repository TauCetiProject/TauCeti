/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Lift.Twist.Map
import Mathlib.Order.Filter.AtTopBot.Basic
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
(`TauCeti.GroupAlgGeom.Lift.TowerStage.Hom.eventually_tower_ne_one`). The retractions `t₁ ↦ u₁ ^ k`
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

If the twists map the radical of a system `S` into itself and `v` is a solution of `S`, the
twisted points `φ_{L,p} v` are solutions (`wordMap_phi_mem_V`), so for a nondegenerate tower over a
CSA group with the big powers property every word of the radical of `S` vanishes at the top point
(`eval_twistTower_eq_one_of_mem_Rad`): the top point is a point of the coordinate group `G_{R(S)}`,
which maps to the tower (`twistTowerGHom`), and the retraction with exponents `p` composed with this
map is evaluation at `φ_{L,p} v` (`towerRetraction_twistTowerGHom`). This holds for the basic tower
of `J` rounds of the basic sequence over a solution `β` of a standard orientable quadratic equation
(`TauCeti.GroupAlgGeom.Lift.basicTower`, `eval_basicTower_eq_one_of_mem_Rad`), whose twists fix the
equation; for `J = 2` the map is the homomorphism `λ_β : G_{R(S)} → G(U, T)` of [IFT], §7.2,
Proposition 4, and no regularity of the equation is needed.

## Main definitions

* `TauCeti.GroupAlgGeom.Lift.twistTowerGHom`: the `G`-homomorphism from the coordinate group of a
  system whose radical the twists preserve to a nondegenerate tower over a solution, over a CSA
  group with the big powers property.

## Main results

* `TauCeti.GroupAlgGeom.Lift.exists_bound_forall_towerRetraction_ne_one`: the retractions with
  exponent tuples dominating a bound function keep a given finite set of nonidentity elements.
* `TauCeti.GroupAlgGeom.Lift.exists_bound_forall_eval_phi_ne_one`: survival at `φ_{L,p} v` for
  exponent tuples dominating a bound function.
* `TauCeti.GroupAlgGeom.Lift.eval_twistTower_eq_one_iff`: the kernel of the top point, tested on
  the tuples of `L` natural numbers.
* `TauCeti.GroupAlgGeom.Lift.eval_wordMap_phi`: evaluating at the point `φ_{L,p} v` is
  evaluating at `v` after applying `φ_{L,p}`.
* `TauCeti.GroupAlgGeom.Lift.wordMap_phi_mem_V`: the points `φ_{L,p} v` of a solution `v` of a
  system whose radical the twists preserve are solutions.
* `TauCeti.GroupAlgGeom.Lift.eval_twistTower_eq_one_of_mem_Rad`,
  `TauCeti.GroupAlgGeom.Lift.eval_basicTower_eq_one_of_mem_Rad`: over a CSA group with the big
  powers property, the top point of a nondegenerate tower over a solution of a system whose radical
  the twists preserve, in particular of a nondegenerate basic tower of a solution, vanishes on the
  radical.
* `TauCeti.GroupAlgGeom.Lift.towerRetraction_twistTowerGHom`: the retraction with exponents `p`
  composed with `twistTowerGHom` is evaluation at `φ_{L,p} v`.

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
    refine List.exists_bound_of_forall_cons K fun k hk => ?_
    obtain ⟨N, hN⟩ := ih (P := P.twisted d k) hBP hCSA (hK k hk).1
      (M := M.image ((P.liftRetraction d k).tower l)) (Finset.forall_mem_image.2 (hK k hk).2)
    refine ⟨N, fun q hq hdom x hx h1 => hN q hq hdom _ (Finset.mem_image_of_mem _ hx) ?_⟩
    rw [towerRetraction_cons_apply, List.headD_cons, List.tail_cons] at h1
    exact ((TowerStage.Hom.towerRetraction_tower _ l q x).trans
      (TowerStage.liftRetraction_apply _ _ _ _)).trans h1

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
    obtain ⟨p, hp, hdom⟩ := List.exists_length_eq_forall_getElem_eq N l.length
    exact hN p hp (fun i hi => (hdom i hi).ge) w (Finset.mem_singleton_self w) (h p hp)

/-! ### Points of coordinate groups -/

/-- If the substitutions of the twist data of `l` map a set of words into itself, so do the
automorphisms `φ_{L,p}`. -/
private theorem mapsTo_phi_map_toMulAut {l : List (TwistData G X)} {s : Set (GX G X)}
    (hs : ∀ d ∈ l, Set.MapsTo (twistHom d.A d.e) s s) (p : List ℕ) :
    Set.MapsTo ⇑(phi (l.map TwistData.toMulAut) p) s s :=
  mapsTo_phi (List.forall_mem_map.2 fun d hd x hx => by
    rw [TwistData.toMulAut_apply]
    exact hs d hd hx) p

/-- The automorphisms `φ_{L,p}` fix the coefficients. -/
private theorem phi_map_toMulAut_inl (l : List (TwistData G X)) (p : List ℕ) (g : G) :
    phi (l.map TwistData.toMulAut) p (inl g) = inl g :=
  phi_apply_of_forall_mem (List.forall_mem_map.2 fun d _ => by simp [twistHom_inl]) p

/-- Evaluating at the point `φ_{L,p} v`, whose coordinates are the values at `v` of the words
`φ_{L,p}(x)`, is evaluating at `v` after applying `φ_{L,p}`. -/
theorem eval_wordMap_phi {H : Type*} [Group H] (ι : G →* H) (l : List (TwistData G X))
    (p : List ℕ) (v : X → H) (w : GX G X) :
    eval ι (wordMap ι (fun x => phi (l.map TwistData.toMulAut) p (inr (.of x))) v) w =
      eval ι v (phi (l.map TwistData.toMulAut) p w) := by
  have h := DFunLike.congr_fun
    (eval_wordMap (ι := ι) (.ofMulEquiv _ (phi_map_toMulAut_inl l p)) v) w
  simpa only [GHom.coe_ofMulEquiv, MonoidHom.comp_apply, GHom.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass] using h

/-- If the substitutions of the twist data of `l` map the radical of a system `S` into itself, the
points `φ_{L,p} v` obtained from a solution `v` of `S` are solutions of `S`. -/
theorem wordMap_phi_mem_V {H : Type*} [Group H] {ι : G →* H} {l : List (TwistData G X)}
    {S : Set (GX G X)} (hS : ∀ d ∈ l, Set.MapsTo (twistHom d.A d.e) (Rad ι S) (Rad ι S))
    {v : X → H} (hv : v ∈ V ι S) (p : List ℕ) :
    wordMap ι (fun x => phi (l.map TwistData.toMulAut) p (inr (.of x))) v ∈ V ι S :=
  mem_V.2 fun s hs => by
    rw [eval_wordMap_phi]
    exact mem_Rad.1 (mapsTo_phi_map_toMulAut hS p (subset_Rad S hs)) v hv

/-- Let `P` be a solution of a system `S` in a CSA group with the big powers property, `l` a list
of twist data whose substitutions map the radical of `S` into itself, and suppose that the tower
over `P` along `l` is nondegenerate. Then every word of the radical of `S` vanishes at the point of
the tower. -/
theorem eval_twistTower_eq_one_of_mem_Rad {P : TowerStage.{u, v, w} G X}
    (hBP : Group.IsBP P.carrier) (hCSA : Group.IsCSA P.carrier) {l : List (TwistData G X)}
    (hl : P.IsNondegenerate l) {S : Set (GX G X)}
    (hS : ∀ d ∈ l, Set.MapsTo (twistHom d.A d.e) (Rad P.coeff S) (Rad P.coeff S))
    (hv : P.point ∈ V P.coeff S) {w : GX G X} (hw : w ∈ Rad P.coeff S) :
    eval (twistTower l P).coeff (twistTower l P).point w = 1 :=
  (eval_twistTower_eq_one_iff hBP hCSA hl w).2 fun p _ =>
    mem_Rad.1 (mapsTo_phi_map_toMulAut hS p hw) P.point hv

/-- The `G`-homomorphism `G_{R(S)} → Z_L` from the coordinate group of a system `S` over the
group of `P` to a nondegenerate tower over a solution `P` of `S` in a CSA group with the big powers
property, along twist data whose substitutions map the radical of `S` into itself: the evaluation
at the point of the tower. For the basic tower of two rounds (`J = 2`) of the basic sequence over a
solution `β` of a standard orientable quadratic equation (`TauCeti.GroupAlgGeom.Lift.basicTower`),
this is the homomorphism `λ_β : G_{R(S)} → G(U, T)` of [IFT], §7.2, Proposition 4. -/
noncomputable def twistTowerGHom {P : TowerStage.{u, v, w} G X} (hBP : Group.IsBP P.carrier)
    (hCSA : Group.IsCSA P.carrier) {l : List (TwistData G X)} (hl : P.IsNondegenerate l)
    {S : Set (GX G X)} (hS : ∀ d ∈ l, Set.MapsTo (twistHom d.A d.e) (Rad P.coeff S) (Rad P.coeff S))
    (hv : P.point ∈ V P.coeff S) : GHom (CoordGroup.coeff P.coeff S) (twistTower l P).coeff :=
  CoordGroup.evalGHomOfMemVRad (twistTower l P).point
    (mem_V.2 fun _ hw => eval_twistTower_eq_one_of_mem_Rad hBP hCSA hl hS hv hw)

@[simp]
theorem twistTowerGHom_mk {P : TowerStage.{u, v, w} G X} (hBP : Group.IsBP P.carrier)
    (hCSA : Group.IsCSA P.carrier) {l : List (TwistData G X)} (hl : P.IsNondegenerate l)
    {S : Set (GX G X)} (hS : ∀ d ∈ l, Set.MapsTo (twistHom d.A d.e) (Rad P.coeff S) (Rad P.coeff S))
    (hv : P.point ∈ V P.coeff S) (w : GX G X) :
    twistTowerGHom hBP hCSA hl hS hv (w : CoordGroup P.coeff S) =
      eval (twistTower l P).coeff (twistTower l P).point w :=
  CoordGroup.evalGHomOfMemVRad_mk _ w

/-- The retraction of the tower with exponents `p`, a tuple no longer than `l`, composed with
`twistTowerGHom`, is evaluation at the solution `φ_{L,p} v` of `S`. -/
theorem towerRetraction_twistTowerGHom {P : TowerStage.{u, v, w} G X}
    (hBP : Group.IsBP P.carrier) (hCSA : Group.IsCSA P.carrier) {l : List (TwistData G X)}
    (hl : P.IsNondegenerate l) {S : Set (GX G X)}
    (hS : ∀ d ∈ l, Set.MapsTo (twistHom d.A d.e) (Rad P.coeff S) (Rad P.coeff S))
    (hv : P.point ∈ V P.coeff S) {p : List ℕ} (hp : p.length ≤ l.length)
    (q : CoordGroup P.coeff S) :
    towerRetraction l P p (twistTowerGHom hBP hCSA hl hS hv q) =
      CoordGroup.evalGHom _ (wordMap_phi_mem_V hS hv p) q := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
  rw [twistTowerGHom_mk, eval_towerRetraction l P hp, CoordGroup.evalGHom_mk, eval_wordMap_phi]

/-- The point of a nondegenerate basic tower of `J` rounds over a solution `β` of a standard
orientable quadratic equation `S = 1` over a CSA group with the big powers property is a point of
the coordinate group: every word of the radical of `S` vanishes at it. For `J = 2` this says that
the homomorphism `λ_β : G_{R(S)} → G(U, T)` of [IFT], §7.2, Proposition 4, is defined. -/
theorem eval_basicTower_eq_one_of_mem_Rad (hBP : Group.IsBP G) (hCSA : Group.IsCSA G)
    {S : Quadratic.Standard G X} (hS : S.IsOrientable) {β : X → G}
    (hβ : β ∈ V (.id G) {S.toWord}) (J : ℕ)
    (hnd : (⟨G, .id G, β⟩ : TowerStage.{u, v, u} G X).IsNondegenerate
      (List.replicate J (basicSeqData S hS)).flatten) {w : GX G X}
    (hw : w ∈ Rad (.id G) {S.toWord}) :
    eval (basicTower S hS β J).coeff (basicTower S hS β J).point w = 1 := by
  rw [basicTower_def]
  refine eval_twistTower_eq_one_of_mem_Rad (P := ⟨G, .id G, β⟩) hBP hCSA hnd
    (fun d hd u hu => ?_) hβ hw
  obtain ⟨_, hl, hdl⟩ := List.mem_flatten.1 hd
  obtain rfl := List.eq_of_mem_replicate hl
  -- The twist fixes the coefficients and the equation, so it maps the radical into itself.
  simpa using Rad_preimage_le_comap (.id G)
    (.ofMulEquiv d.toMulAut fun g => (d.toMulAut_apply _).trans (twistHom_inl d.A d.e g))
    {S.toWord} (Rad_monotone (.id G) (fun s hs => by
      simp [Set.mem_singleton_iff.1 hs, twistHom_toWord_of_mem_basicSeqData hS hdl]) hu)

end TauCeti.GroupAlgGeom.Lift
