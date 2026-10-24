/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.GaussCode.Polygon.Basic
public import TauCeti.KnotTheory.GaussCode.Unbased

/-!
# Relabelling the vertices of a polygonal knot changes its Gauss code only by a base point

The cyclic relabelling `poly.rotate` of a polygonal knot `poly`, whose vertex `i` is vertex `i + 1`
of `poly`, is the elementary move `TauCeti.SimplePolygon.IsElementaryMove.rotate`. It does not move
the knot, but it moves the point from which `Polygon.gaussCode` starts traversing it, from vertex
`0` to vertex `1`, and the crossings are numbered in the order of their first visits from there.
This file proves that this is all that changes: the Gauss code of a regular projection of
`poly.rotate` is obtained from that of `poly` by moving the base point forward past the visits
between vertices `0` and `1` and relabelling the crossings
(`Polygon.exists_gaussCode_rotate_eq_relabel`). Forgetting the base point, the two unbased oriented
Gauss codes differ only by a relabelling of the crossings
(`Polygon.exists_forgetBasepoint_gaussCode_rotate_eq_relabel`).

Cyclic relabelling keeps a polygon simple (`Polygon.isSimple_rotate_iff`) and a projection regular
(`Polygon.isRegularProjection_rotate_iff`). As for subdividing an edge
(`Polygon.gaussCode_insertVertex`), the numbers of crossings of the two codes are equal but not
definitionally equal, and the codes are compared together with them.

The traversal of `poly.rotate` at time `t` is the traversal of `poly` at time `t + 1`
(`Polygon.boundaryParam_rotate`). So if `poly` has `k` crossing times in `[0, 1)`, its `i`-th
crossing time `t`, shifted back into `[0, n)` by `t ↦ t - 1` or `t ↦ t + n - 1`, is the
`(i - k)`-th crossing time of `poly.rotate`, read modulo the number of visits. The two traversals
meet each crossing at the same point and along edges with the same directions, so the two codes
have the same crossings, over/under data and signs at corresponding visits.

## Main results

* `Polygon.exists_gaussCode_rotate_eq_relabel`: the Gauss code of `poly.rotate` is a basepoint
  rotation of that of `poly`, with the crossings relabelled.
* `Polygon.exists_forgetBasepoint_gaussCode_rotate_eq_relabel`: the unbased oriented Gauss codes of
  `poly` and `poly.rotate` differ by a relabelling of the crossings.

## References

* G. Burde, H. Zieschang, *Knots*, 2nd ed., De Gruyter Studies in Mathematics 5 (2003),
  Chapter 1, for the elementary moves on polygonal knots and their regular projections.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1, for
  knot diagrams and Gauss codes.
-/

public section

open Set Function Module TauCeti

namespace Polygon

variable {V P : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V P] {n : ℕ}
  {poly : Polygon P n} {p₀ : P} {d : V}

/-! ### The change of time -/

variable (n) in
/-- The time in `[0, n)` at which the traversal of `poly.rotate` reaches the point that the
traversal of `poly` reaches at time `t ∈ [0, n)`. -/
private noncomputable def rotateTime (t : ℝ) : ℝ :=
  if t < 1 then t + n - 1 else t - 1

private theorem rotateTime_add_one (t : ℝ) :
    rotateTime n t + 1 = t + n ∨ rotateTime n t + 1 = t := by
  unfold rotateTime
  split_ifs
  exacts [.inl (by ring), .inr (by ring)]

/-- Let `τ` be an increasing sequence of times in `[0, n)` whose terms below `1` are its first `k`
terms. Shifting it cyclically past these `k` terms and applying the change of time `rotateTime`
keeps it increasing: the terms from the `k`-th on move back by `1`, into `[0, n - 1)`, and the
first `k` terms move forward by `n - 1`, into `[n - 1, n)`. -/
private theorem strictMono_rotateTime_finRotate_pow {N k : ℕ} {τ : Fin N → ℝ} (hτ : StrictMono τ)
    (hτ₀ : ∀ i, 0 ≤ τ i) (hτn : ∀ i, τ i < n) (hkN : k ≤ N) (hk : ∀ i, τ i < 1 ↔ (i : ℕ) < k) :
    StrictMono fun j ↦ rotateTime n (τ ((finRotate N ^ k) j)) := by
  intro j j' hjj'
  have hj := j.isLt
  have hj' := j'.isLt
  have hlt : (j : ℕ) < j' := hjj'
  have hσ (j : Fin N) : ((finRotate N ^ k) j : ℕ) = (j + k) % N := Fin.coe_finRotate_pow k j
  have h₀ := hτ₀ ((finRotate N ^ k) j)
  have hn := hτn ((finRotate N ^ k) j)
  simp only [rotateTime]
  by_cases h₁ : (j : ℕ) + k < N <;> by_cases h₂ : (j' : ℕ) + k < N
  · have e₁ : ((finRotate N ^ k) j : ℕ) = j + k := by rw [hσ, Nat.mod_eq_of_lt h₁]
    have e₂ : ((finRotate N ^ k) j' : ℕ) = j' + k := by rw [hσ, Nat.mod_eq_of_lt h₂]
    have hv := hτ (show (finRotate N ^ k) j < (finRotate N ^ k) j' from Fin.lt_def.2 (by omega))
    rw [ite_eq_right (by rw [hk]; omega), ite_eq_right (by rw [hk]; omega)]
    linarith
  · have e₁ : ((finRotate N ^ k) j : ℕ) = j + k := by rw [hσ, Nat.mod_eq_of_lt h₁]
    have e₂ : ((finRotate N ^ k) j' : ℕ) = j' + k - N := by
      rw [hσ, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have h₀' := hτ₀ ((finRotate N ^ k) j')
    rw [ite_eq_right (by rw [hk]; omega), ite_eq_left (by rw [hk]; omega)]
    linarith
  · omega
  · have e₁ : ((finRotate N ^ k) j : ℕ) = j + k - N := by
      rw [hσ, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have e₂ : ((finRotate N ^ k) j' : ℕ) = j' + k - N := by
      rw [hσ, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have hv := hτ (show (finRotate N ^ k) j < (finRotate N ^ k) j' from Fin.lt_def.2 (by omega))
    rw [ite_eq_left (by rw [hk]; omega), ite_eq_left (by rw [hk]; omega)]
    linarith

variable [NeZero n]

private theorem boundaryParam_rotate_rotateTime (t : ℝ) :
    poly.rotate.boundaryParam (rotateTime n t) = poly.boundaryParam t := by
  rw [boundaryParam_rotate]
  rcases rotateTime_add_one (n := n) t with h | h <;> rw [h]
  exact poly.periodic_boundaryParam t

private theorem finRotate_edgeIndexAt_rotateTime (t : ℝ) :
    finRotate n (edgeIndexAt n (rotateTime n t)) = edgeIndexAt n t := by
  rw [← edgeIndexAt_add_one]
  rcases rotateTime_add_one (n := n) t with h | h <;> rw [h]
  exact periodic_edgeIndexAt t

/-- The change of time carries the crossing times of `poly` onto those of `poly.rotate`. -/
private theorem image_rotateTime_crossingTimes :
    rotateTime n '' poly.crossingTimes p₀ d = poly.rotate.crossingTimes p₀ d := by
  have hn : (1 : ℝ) ≤ n := Nat.one_le_cast.2 (Nat.pos_of_neZero n)
  have hDP : poly.rotate.doublePoints ℝ (projAlong ℝ p₀ d) =
      poly.doublePoints ℝ (projAlong ℝ p₀ d) :=
    doublePoints_eq_of_boundary_eq (boundary_rotate poly)
  refine Subset.antisymm ?_ fun t' ht' ↦ ?_
  · rintro _ ⟨t, ht, rfl⟩
    obtain ⟨⟨ht₀, htn⟩, ht⟩ := mem_crossingTimes.1 ht
    refine mem_crossingTimes.2 ⟨?_, by rw [boundaryParam_rotate_rotateTime, hDP]; exact ht⟩
    unfold rotateTime
    split_ifs with h
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
  · obtain ⟨⟨ht'₀, ht'n⟩, ht'⟩ := mem_crossingTimes.1 ht'
    rw [hDP, boundaryParam_rotate] at ht'
    by_cases h : t' + 1 < n
    · refine ⟨t' + 1, mem_crossingTimes.2 ⟨⟨by linarith, h⟩, ht'⟩, ?_⟩
      rw [rotateTime, ite_eq_right (by linarith)]
      ring
    · refine ⟨t' + 1 - n, mem_crossingTimes.2 ⟨⟨by linarith, by linarith⟩, ?_⟩, ?_⟩
      · rwa [poly.periodic_boundaryParam.sub_eq]
      · rw [rotateTime, ite_eq_left (by linarith)]
        ring

/-- **Visit times after relabelling the vertices.** If `poly` has `k` crossing times in `[0, 1)`,
then the `j`-th visit of `poly.rotate` is the change of time of the `(j + k)`-th visit of `poly`,
read modulo the number of visits. -/
private theorem exists_visitTime_rotate (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) (hs' : poly.rotate.IsSimple ℝ)
    (hπ' : poly.rotate.IsRegularProjection ℝ (projAlong ℝ p₀ d))
    (h : 2 * ((poly.doublePoints ℝ (projAlong ℝ p₀ d)).ncard / 2) =
      2 * ((poly.rotate.doublePoints ℝ (projAlong ℝ p₀ d)).ncard / 2)) :
    ∃ k : ℕ, ∀ j, visitTime hs' hπ' (Fin.cast h j) =
      rotateTime n (visitTime hs hπ ((finRotate _ ^ k) j)) := by
  have hmem (i) := (mem_crossingTimes.1 (visitTime_mem_crossingTimes hs hπ i)).1
  -- The visits before time `1` form a lower set, so they are the first `k` visits.
  obtain ⟨k, hkN, hk⟩ : ∃ k ≤ 2 * ((poly.doublePoints ℝ (projAlong ℝ p₀ d)).ncard / 2),
      ∀ i, visitTime hs hπ i < 1 ↔ (i : ℕ) < k := by
    rcases ((IsLowerSet.Iio (1 : ℝ)).preimage
      (strictMono_visitTime hs hπ).monotone).eq_univ_or_Iio with h | ⟨a, h⟩
    · exact ⟨_, le_rfl, fun i ↦ iff_of_true (h.symm ▸ mem_univ i : i ∈ _) i.isLt⟩
    · exact ⟨a, a.isLt.le, fun i ↦ (Set.ext_iff.1 h i).trans Fin.lt_def⟩
  have hf := strictMono_rotateTime_finRotate_pow (strictMono_visitTime hs hπ)
    (fun i ↦ (hmem i).1) (fun i ↦ (hmem i).2) hkN hk
  have hf' : StrictMono (visitTime hs' hπ' ∘ Fin.cast h) :=
    (strictMono_visitTime hs' hπ').comp (Fin.cast_strictMono h)
  have hrange : range (visitTime hs' hπ' ∘ Fin.cast h) =
      range (rotateTime n ∘ visitTime hs hπ ∘ (finRotate _ ^ k)) := by
    have hcast : Surjective (Fin.cast h) := fun x ↦ ⟨Fin.cast h.symm x, by simp⟩
    rw [range_comp, hcast.range_eq, image_univ, range_visitTime, range_comp, range_comp,
      (finRotate _ ^ k).surjective.range_eq, image_univ, range_visitTime,
      image_rotateTime_crossingTimes]
  exact ⟨k, congrFun ((hf'.range_inj_of_wellFoundedLT hf).1 hrange)⟩

/-! ### The Gauss code -/

/-- **Relabelling the vertices changes the Gauss code only by a base point.** Let `poly` be a
simple polygon in a three-dimensional real affine space, oriented by the basis `b`, and let the
projection along `d` be regular. Then the Gauss code of its cyclic relabelling `poly.rotate`,
which starts the traversal at vertex `1` instead of vertex `0`, is obtained from the Gauss code of
`poly` by moving the base point forward `k` visits, for some `k`, and relabelling the crossings.
The numbers of crossings agree, and the codes are compared together with them. -/
theorem exists_gaussCode_rotate_eq_relabel (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) (b : Basis (Fin 3) ℝ V) :
    ∃ (k : ℕ) (e : Equiv.Perm (Fin ((poly.doublePoints ℝ (projAlong ℝ p₀ d)).ncard / 2))),
      (⟨_, gaussCode ((isSimple_rotate_iff poly).2 hs) (isRegularProjection_rotate_iff.2 hπ) b⟩ :
          Σ m, BasedOrientedGaussCode m) =
        ⟨_, ((BasedOrientedGaussCode.rotateBasepoint _ ^ k) (gaussCode hs hπ b)).relabel e⟩ := by
  have hs' := (isSimple_rotate_iff poly).2 hs
  have hπ' := (isRegularProjection_rotate_iff (R := ℝ)).2 hπ
  set π := projAlong ℝ p₀ d
  set D := gaussCode hs hπ b
  set D' := gaussCode hs' hπ' b
  have hb : poly.rotate.boundary ℝ = poly.boundary ℝ := boundary_rotate poly
  have hDP : poly.rotate.doublePoints ℝ π = poly.doublePoints ℝ π :=
    doublePoints_eq_of_boundary_eq hb
  have hm : (poly.doublePoints ℝ π).ncard / 2 = (poly.rotate.doublePoints ℝ π).ncard / 2 := by
    rw [hDP]
  have h2 : 2 * ((poly.doublePoints ℝ π).ncard / 2) =
      2 * ((poly.rotate.doublePoints ℝ π).ncard / 2) := by
    rw [hm]
  obtain ⟨k, hvt⟩ := exists_visitTime_rotate hs hπ hs' hπ' h2
  refine ⟨k, ?_⟩
  set σ := finRotate (2 * ((poly.doublePoints ℝ π).ncard / 2)) ^ k
  -- Corresponding visits are at the same point, along edges with the same direction.
  have hbp (j) : poly.rotate.boundaryParam (visitTime hs' hπ' (Fin.cast h2 j)) =
      poly.boundaryParam (visitTime hs hπ (σ j)) := by
    rw [hvt, boundaryParam_rotate_rotateTime]
  have hedge (j) : finRotate n (edgeIndexAt n (visitTime hs' hπ' (Fin.cast h2 j))) =
      edgeIndexAt n (visitTime hs hπ (σ j)) := by
    rw [hvt, finRotate_edgeIndexAt_rotateTime]
  -- Their partner visits are at the same point.
  have hpp (j) : poly.rotate.boundaryParam (visitTime hs' hπ' (D'.partner.val (Fin.cast h2 j))) =
      poly.boundaryParam (visitTime hs hπ (D.partner.val (σ j))) := by
    rw [boundaryParam_visitTime_partner, boundaryParam_visitTime_partner, hbp]
    have hx := (mem_crossingTimes.1 (visitTime_mem_crossingTimes hs hπ (σ j))).2
    have hx' : poly.boundaryParam (visitTime hs hπ (σ j)) ∈ poly.rotate.doublePoints ℝ π := by
      rwa [hDP]
    exact hπ.eq_doublePointPartner (doublePoints_subset_boundary hx)
      (hb ▸ doublePointPartner_mem_boundary (doublePoints_subset_boundary hx'))
      (doublePointPartner_ne hx') (apply_doublePointPartner _)
  have hpartner (j) : D'.partner.val (Fin.cast h2 j) = Fin.cast h2 (σ.symm (D.partner.val (σ j))) :=
    (strictMono_visitTime hs' hπ').injective (hs'.injOn_boundaryParam
      (mem_crossingTimes.1 (visitTime_mem_crossingTimes hs' hπ' _)).1
      (mem_crossingTimes.1 (visitTime_mem_crossingTimes hs' hπ' _)).1
      (by rw [hpp, hbp, Equiv.apply_symm_apply]))
  have hvisit (i j) : D.visit (σ i) = D.visit (σ j) ↔
      D'.visit (Fin.cast h2 i) = D'.visit (Fin.cast h2 j) := by
    rw [gaussCode_visit_eq_visit_iff, gaussCode_visit_eq_visit_iff, hbp, hbp]
  have hover (i) : D.over (σ i) = D'.over (Fin.cast h2 i) := by
    rw [Bool.eq_iff_iff, gaussCode_over_eq_true_iff, gaussCode_over_eq_true_iff, hbp, hpp]
  -- The crossing signs agree, first at an over visit and then at its partner.
  have hsign_over (i) (hi : D.over (σ i) = true) :
      D.sign (D.visit (σ i)) = D'.sign (D'.visit (Fin.cast h2 i)) := by
    have hi' : D'.over (Fin.cast h2 i) = true := by rw [← hover, hi]
    refine Units.ext ?_
    rw [gaussCode_sign_visit b hs hπ hi, gaussCode_sign_visit b hs' hπ' hi', hpartner]
    simp only [rotate_apply, hedge, Equiv.apply_symm_apply, D]
  set E := (BasedOrientedGaussCode.rotateBasepoint _ ^ k) D
  have hsign (i) : E.sign (E.visit i) = D'.sign (D'.visit (Fin.cast h2 i)) := by
    simp only [E, BasedOrientedGaussCode.sign_rotateBasepoint_pow,
      BasedOrientedGaussCode.visit_rotateBasepoint_pow]
    cases hi : D.over (σ i)
    · -- The partner visit of `E` is over, and meets the same crossing.
      set i₂ := E.partner.val i
      have hv : E.visit i₂ = E.visit i := E.visit_partner i
      have ho : E.over i₂ = true := by
        rw [E.over_partner, BasedOrientedGaussCode.over_rotateBasepoint_pow, hi, Bool.not_false]
      simp only [E, BasedOrientedGaussCode.visit_rotateBasepoint_pow,
        BasedOrientedGaussCode.over_rotateBasepoint_pow] at hv ho
      rw [← hv, hsign_over i₂ ho, (hvisit i₂ i).1 hv]
    · exact hsign_over i hi
  exact BasedOrientedGaussCode.exists_sigma_mk_eq_relabel_of_visit_eq_visit_iff hm
    (fun i j ↦ by simpa only [E, BasedOrientedGaussCode.visit_rotateBasepoint_pow] using hvisit i j)
    (fun i ↦ by simpa only [E, BasedOrientedGaussCode.over_rotateBasepoint_pow] using hover i)
    hsign

/-- **Relabelling the vertices changes the unbased Gauss code only by relabelling crossings.**
Under the hypotheses of `Polygon.exists_gaussCode_rotate_eq_relabel`, the unbased oriented Gauss
codes of `poly` and of its cyclic relabelling `poly.rotate` differ by a relabelling of the
crossings. -/
theorem exists_forgetBasepoint_gaussCode_rotate_eq_relabel (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) (b : Basis (Fin 3) ℝ V) :
    ∃ e : Equiv.Perm (Fin ((poly.doublePoints ℝ (projAlong ℝ p₀ d)).ncard / 2)),
      (⟨_, (gaussCode ((isSimple_rotate_iff poly).2 hs) (isRegularProjection_rotate_iff.2 hπ)
          b).forgetBasepoint⟩ : Σ m, OrientedGaussCode m) =
        ⟨_, (gaussCode hs hπ b).forgetBasepoint.relabel e⟩ := by
  obtain ⟨k, e, h⟩ := exists_gaussCode_rotate_eq_relabel hs hπ b
  refine ⟨e, ?_⟩
  have := congrArg (fun D : Σ m, BasedOrientedGaussCode m ↦
    (⟨D.1, D.2.forgetBasepoint⟩ : Σ m, OrientedGaussCode m)) h
  simpa only [← OrientedGaussCode.relabel_forgetBasepoint,
    BasedOrientedGaussCode.forgetBasepoint_rotateBasepoint_pow] using this

end Polygon
