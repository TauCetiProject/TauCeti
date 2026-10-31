/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Planar
public import TauCeti.KnotTheory.PDCode.ResolvedCircle.Adjacent
import TauCeti.Algebra.GroupAction.OrbitRelQuotient
import TauCeti.GroupTheory.Perm.SigmaCongr
import TauCeti.GroupTheory.Perm.SwapFactors

/-!
# Planar cube edges merge or split circles

Along an edge of the cube of resolutions, from a state `s` to the state `t` differing from it
only at the crossing `c`, two circles of `s` through `c` merge into one circle of `t`, one circle
of `s` through `c` splits into two circles of `t`, or one circle through `c` is replaced by one
circle (`TauCeti.PDCode.card_circlesAt_add_card_circlesAt_le_three`). The last case occurs for
the nonplanar code of two circles meeting in a single crossing. This file proves that it never
occurs for a planar code: then exactly three circles pass through `c` in the two smoothings
together (`TauCeti.PDCode.IsPlanar.card_circlesAt_add_card_circlesAt_eq_three`), so every edge of
the cube of resolutions is a merge or a split, and the number of circles changes by exactly one.
These are the two kinds of edges carrying the merge and split maps of the Khovanov complex.

## Main results

* `TauCeti.PDCode.IsPlanar.card_circlesAt_add_card_circlesAt_eq_three`: for a planar code, three
  circles pass through the crossing at which two states differ, in the two smoothings together.
* `TauCeti.PDCode.IsPlanar.card_circlesAt_eq_two_or_card_circlesAt_eq_two`: every edge of the
  cube of resolutions of a planar code is a merge or a split.
* `TauCeti.PDCode.IsPlanar.stateLoopCount_eq_add_one_or_stateLoopCount_eq_add_one`: along every
  edge the number of circles changes by exactly one.

## Implementation notes

The proof is a finite Euler-characteristic count, read off from the transposition bound
`TauCeti.card_add_orbitCount_le_length_add_two_mul_card_orbits`. Smoothing the crossings
according to `s` gives the perfect matching `σ` of the half-edges, and the rotation `ρ` to the
next slot at each crossing is `σ * (σ * ρ)`, where `σ * ρ` transposes two opposite slots at each
crossing. So the face permutation `α * ρ` of the underlying graph, with `α` the arc matching, is
conjugate to `(σ * ρ) * (α * σ)`, and `α * σ` is the inverse of the traversal
`TauCeti.PDCode.statePerm`, whose cycles are the circles of `s` in both directions of travel.
Writing this product with `n` transpositions for `σ * ρ`, and `2 * n` each for `α` and `σ`, the
bound is Euler's bound `TauCeti.PDCode.faceCount_le`, attained exactly by planar codes.

Now suppose one circle of `s` and one circle of `t` pass through `c`. Then the two slots `x` and
`y` transposed by `σ * ρ` at `c` lie on one circle of `s`, but they do not lie on one directed
traversal orbit: otherwise, the reversal of directed orbits along the smoothing would put the
other two slots at `c` on one other directed orbit, and resmoothing `c` would split both, leaving
`t` one circle more than `s`. A transposition joining two directed orbits of one circle merges two
faces without joining two components, so the bound is not attained
(`TauCeti.card_add_orbitCount_add_two_le_length_add_two_mul_card_orbits`), and the code is not
planar.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), 359-426,
  §2 and §4.2 (the merge and split maps on the edges of the cube).
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*, Algebr. Geom. Topol. 2
  (2002), 337-370, §2.
* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.3 (faces of rotation systems).
-/

public section

namespace TauCeti

open Equiv Equiv.Perm Finset

namespace PDCode

variable {n : ℕ} (D : PDCode n)

/-! ### The crossing transpositions of a smoothing -/

/-- Turning to the next slot and then following the smoothing `b` acts at each crossing by a local
permutation of the slots. -/
private theorem smoothingTurn_mul_crossingRotation_crossing (b : Fin n → Bool) (i : Fin n)
    (k : Fin 4) :
    (D.smoothingTurn b * D.crossingRotation) (D.crossing i k) =
      D.crossing i (slotSmoothing (b i) (k + 1)) := by
  rw [Perm.mul_apply, crossing_apply, crossingRotation_crossing, crossing_apply,
    smoothingTurn_crossing]

/-- At each crossing, turning to the next slot and then following a local smoothing exchanges two
opposite slots and fixes the other two. -/
private theorem slotSmoothing_mul_finRotate (β : Bool) :
    slotSmoothing β * finRotate 4 = bif β then swap 1 3 else swap 0 2 := by
  ext k
  rw [Perm.mul_apply, finRotate_apply]
  revert k
  cases β <;>
    simp only [slotSmoothing_true, slotSmoothing_false, Bool.cond_true, Bool.cond_false] <;>
    decide

/-- Turning to the next slot and then following a smoothing transposes two opposite slots at each
crossing, so it has `3` orbits for each crossing. -/
private theorem orbitCount_smoothingTurn_mul_crossingRotation (b : Fin n → Bool) :
    orbitCount (D.smoothingTurn b * D.crossingRotation) = 3 * n := by
  have h : D.smoothingTurn b * D.crossingRotation =
      D.halfEdge.permCongr ((crossingSlotEquiv n).permCongr
        ((sigmaEquivProd (Fin n) (Fin 4)).permCongr
          (Perm.sigmaCongrRight fun i ↦ slotSmoothing (b i) * finRotate 4))) := by
    ext h
    obtain ⟨x, rfl⟩ := D.halfEdge.surjective h
    obtain ⟨⟨i, k⟩, rfl⟩ := (crossingSlotEquiv n).surjective x
    rw [← crossing_apply, smoothingTurn_mul_crossingRotation_crossing]
    simp [crossing_apply, permCongr_apply, add_comm k 1]
  have hswap {k l : Fin 4} (hkl : k ≠ l) : orbitCount (swap k l) = 3 := by
    have h := orbitCount_swap_add_one hkl
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
    omega
  have hfiber (i : Fin n) : orbitCount (slotSmoothing (b i) * finRotate 4) = 3 := by
    rw [slotSmoothing_mul_finRotate]
    cases b i <;> exact hswap (by decide)
  rw [h, orbitCount_permCongr, orbitCount_permCongr, orbitCount_permCongr,
    orbitCount_sigmaCongrRight]
  simp [hfiber, mul_comm]

/-- The face permutation is conjugate to the crossing transpositions of a smoothing `b`, followed
by the arc matching and the smoothing. -/
private theorem faceCount_eq_orbitCount_smoothingTurn_mul_crossingRotation_mul (b : Fin n → Bool) :
    D.faceCount = orbitCount ((D.smoothingTurn b * D.crossingRotation) *
      (D.edgePair.val * D.smoothingTurn b)) := by
  have hσ : D.smoothingTurn b * D.smoothingTurn b = 1 := Equiv.ext (D.smoothingTurn_apply_apply b)
  rw [faceCount_def, facePerm_def, orbitCount_mul_comm (D.smoothingTurn b * D.crossingRotation),
    mul_assoc, ← mul_assoc (D.smoothingTurn b), hσ, one_mul]

/-- Two half-edges on one circle of `s` are connected by every subgroup containing the arc
matching and the smoothing of `s`. -/
private theorem mem_orbit_of_mk_eq_mk {s : Fin n → Bool} {H : Subgroup (Perm (Fin (4 * n)))}
    (hα : D.edgePair.val ∈ H) (hσ : D.smoothingTurn (D.smoothingChoice s) ∈ H)
    {x y : Fin (4 * n)} (h : (⟦x⟧ : D.CrossingCircle s) = ⟦y⟧) : y ∈ MulAction.orbit H x := by
  have key : ∀ p q, Relation.EqvGen (D.CircleStep s) p q → q ∈ MulAction.orbit H p := by
    intro p q hpq
    induction hpq with
    | rel p q hpq =>
      rcases hpq with rfl | rfl
      · exact ⟨⟨_, hα⟩, rfl⟩
      · exact ⟨⟨_, hσ⟩, rfl⟩
    | refl p => exact MulAction.mem_orbit_self p
    | symm p q _ ih => exact MulAction.mem_orbit_symm.mp ih
    | trans p q r _ _ ihpq ihqr =>
      rw [← MulAction.orbit_eq_iff.mpr ihpq]
      exact ihqr
  exact key x y (Quotient.exact h)

/-! ### Joining two directed orbits of a circle is not planar -/

/-- If the two slots `x` and `y` exchanged at their crossing by turning to the next slot and then
following the smoothing of `s` lie on one circle of `s`, but on different directed traversal
orbits, then the code is not planar. -/
private theorem not_isPlanar_of_not_sameCycle {s : Fin n → Bool} {x y : Fin (4 * n)}
    (hxy : (D.smoothingTurn (D.smoothingChoice s) * D.crossingRotation) x = y) (hne : x ≠ y)
    (hcirc : (⟦x⟧ : D.CrossingCircle s) = ⟦y⟧) (hcyc : ¬ (D.statePerm s).SameCycle x y) :
    ¬ D.IsPlanar := by
  set σ := D.smoothingTurn (D.smoothingChoice s)
  set α := D.edgePair.val
  set τ := σ * D.crossingRotation with hτdef
  have hσσ : σ * σ = 1 := Equiv.ext (D.smoothingTurn_apply_apply _)
  have hαα : α * α = 1 := Equiv.ext D.edgePair.apply_apply
  -- Factor `τ = (τ * swap x y) * swap x y`, `α` and `σ` into transpositions.
  obtain ⟨LT, hLT, hLTprod, hLTlen⟩ :=
    (τ * swap x y).exists_isSwap_list_prod_eq_and_orbitCount_add_length_eq_card
  obtain ⟨Lα, hLα, hLαprod, hLαlen⟩ :=
    α.exists_isSwap_list_prod_eq_and_orbitCount_add_length_eq_card
  obtain ⟨Lσ, hLσ, hLσprod, hLσlen⟩ :=
    σ.exists_isSwap_list_prod_eq_and_orbitCount_add_length_eq_card
  have hM : ∀ g ∈ Lα ++ Lσ, g.IsSwap := fun g hg ↦ (List.mem_append.mp hg).elim (hLα g) (hLσ g)
  have hMprod : (Lα ++ Lσ).prod = α * σ := by rw [List.prod_append, hLαprod, hLσprod]
  have hsub {L L' : List (Perm (Fin (4 * n)))} (h : L ⊆ L') :
      L.prod ∈ Subgroup.closure {g | g ∈ L'} :=
    Subgroup.list_prod_mem _ fun g hg ↦ Subgroup.subset_closure (h hg)
  -- The two slots lie on one circle, so the arcs and the smoothing connect them.
  have hα : α ∈ Subgroup.closure {g | g ∈ Lα ++ Lσ} :=
    hLαprod ▸ hsub (List.subset_append_left _ _)
  have hσ : σ ∈ Subgroup.closure {g | g ∈ Lα ++ Lσ} :=
    hLσprod ▸ hsub (List.subset_append_right _ _)
  have hab : y ∈ MulAction.orbit (Subgroup.closure {g | g ∈ Lα ++ Lσ}) x :=
    D.mem_orbit_of_mk_eq_mk hα hσ hcirc
  -- They lie on different cycles of `α * σ`, the inverse of the traversal.
  have hcyc' : ¬ (Lα ++ Lσ).prod.SameCycle x y := by
    have hinv : α * σ = (D.statePerm s)⁻¹ := by
      rw [statePerm_def, mul_inv_rev, inv_eq_of_mul_eq_one_right hσσ,
        inv_eq_of_mul_eq_one_right hαα]
    rwa [hMprod, hinv, sameCycle_inv]
  have hbound := card_add_orbitCount_add_two_le_length_add_two_mul_card_orbits hLT hM hab hcyc'
  have hprod : (LT ++ swap x y :: (Lα ++ Lσ)).prod = τ * (α * σ) := by
    rw [List.prod_append, List.prod_cons, hLTprod, hMprod, mul_assoc, swap_mul_self_mul]
  -- The transpositions generate the monodromy group of the underlying graph.
  have hmono : D.toPermutationTriple.monodromyGroup ≤
      Subgroup.closure {g | g ∈ LT ++ swap x y :: (Lα ++ Lσ)} := by
    rw [← PermutationTriple.closure_pair_eq_monodromyGroup, Subgroup.closure_le]
    have hLTmem : τ * swap x y ∈ Subgroup.closure {g | g ∈ LT ++ swap x y :: (Lα ++ Lσ)} :=
      hLTprod ▸ hsub (List.subset_append_left _ _)
    have hswap : swap x y ∈ Subgroup.closure {g | g ∈ LT ++ swap x y :: (Lα ++ Lσ)} :=
      Subgroup.subset_closure (List.mem_append_right _ List.mem_cons_self)
    have hαmem : α ∈ Subgroup.closure {g | g ∈ LT ++ swap x y :: (Lα ++ Lσ)} :=
      hLαprod ▸ hsub fun g hg ↦ List.mem_append_right _
        (List.mem_cons_of_mem _ (List.mem_append_left _ hg))
    have hσmem : σ ∈ Subgroup.closure {g | g ∈ LT ++ swap x y :: (Lα ++ Lσ)} :=
      hLσprod ▸ hsub fun g hg ↦ List.mem_append_right _
        (List.mem_cons_of_mem _ (List.mem_append_right _ hg))
    have hρ : D.crossingRotation = σ * ((τ * swap x y) * swap x y) := by
      rw [mul_assoc τ, swap_mul_self, mul_one, hτdef, ← mul_assoc, hσσ, one_mul]
    rintro g (rfl | rfl)
    · rw [toPermutationTriple_σ0, hρ]
      exact mul_mem hσmem (mul_mem hLTmem hswap)
    · rw [toPermutationTriple_σ1]
      exact hαmem
  have hcomp := MulAction.card_orbitRelQuotient_anti (X := Fin (4 * n)) hmono
  -- Count the transpositions.
  have hτ : τ.SameCycle x y := ⟨1, by simpa using hxy⟩
  have horbT := orbitCount_mul_swap_of_sameCycle hne hτ
  have horbτ : orbitCount τ = 3 * n :=
    D.orbitCount_smoothingTurn_mul_crossingRotation (D.smoothingChoice s)
  have horbα : orbitCount α = 2 * n := D.orbitCount_edgePair
  have horbσ : 2 * orbitCount σ = Nat.card (Fin (4 * n)) :=
    (D.isPerfectMatching_smoothingTurn (D.smoothingChoice s)).two_mul_orbitCount
  rw [hprod, List.length_append, List.length_cons, List.length_append] at hbound
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hbound hLTlen hLαlen hLσlen horbσ
  have hface : D.faceCount = orbitCount (τ * (α * σ)) :=
    D.faceCount_eq_orbitCount_smoothingTurn_mul_crossingRotation_mul (D.smoothingChoice s)
  rw [isPlanar_iff_faceCount_eq, hface]
  intro hplanar
  have hcomp' : Nat.card (MulAction.orbitRel.Quotient
      (Subgroup.closure {g | g ∈ LT ++ swap x y :: (Lα ++ Lσ)}) (Fin (4 * n))) ≤
      Nat.card D.toPermutationTriple.MonodromyOrbit := hcomp
  omega

/-! ### One circle through a crossing in both smoothings -/

variable {D} {s t : Fin n → Bool} {c : Fin n}

/-- The slots `u` and `u + 2` exchanged at a crossing by turning to the next slot and following
the local smoothing `β`, and their partners under `β`: the other local smoothing pairs the slots as
`β` does, followed by the transpositions of these two pairs. -/
private theorem slotSmoothing_not_apply {β : Bool} {u : Fin 4} (hu : u = bif β then 1 else 0)
    (k : Fin 4) :
    slotSmoothing (!β) k = swap (slotSmoothing β u) (slotSmoothing β (u + 2))
      (swap u (u + 2) (slotSmoothing β k)) := by
  subst hu
  revert k
  cases β <;> simp only [Bool.not_false, Bool.not_true, slotSmoothing_true,
    slotSmoothing_false, Bool.cond_true, Bool.cond_false] <;> decide

/-- Changing the smoothing at `c` transposes the two pairs of slots there: the slots `u` and
`u + 2` exchanged by turning to the next slot and following the smoothing of `s`, and their
partners under that smoothing. -/
private theorem smoothingTurn_smoothingChoice_eq_swap_mul_swap_mul (hst : ∀ j, j ≠ c → s j = t j)
    (hc : s c ≠ t c) {u : Fin 4} (hu : u = bif D.smoothingChoice s c then 1 else 0) :
    D.smoothingTurn (D.smoothingChoice t) =
      swap (D.crossing c (slotSmoothing (D.smoothingChoice s c) u))
          (D.crossing c (slotSmoothing (D.smoothingChoice s c) (u + 2))) *
        swap (D.crossing c u) (D.crossing c (u + 2)) * D.smoothingTurn (D.smoothingChoice s) := by
  ext h
  obtain ⟨z, rfl⟩ := D.halfEdge.surjective h
  obtain ⟨⟨j, k⟩, rfl⟩ := (crossingSlotEquiv n).surjective z
  simp only [← crossing_apply, Perm.mul_apply]
  have hturn (r : Fin n → Bool) : D.smoothingTurn (D.smoothingChoice r) (D.crossing j k) =
      D.crossing j (slotSmoothing (D.smoothingChoice r j) k) := by
    simp [crossing_apply]
  rw [hturn, hturn]
  by_cases hj : j = c
  · subst hj
    have hinj : Function.Injective (D.crossing j) :=
      fun k l h ↦ (D.crossing_eq_crossing_iff.mp h).2
    rw [D.smoothingChoice_eq_not_smoothingChoice hc, slotSmoothing_not_apply hu,
      hinj.swap_apply, hinj.swap_apply]
  · have hne (l m : Fin 4) : D.crossing j l ≠ D.crossing c m :=
      fun h ↦ hj (D.crossing_eq_crossing_iff.mp h).1
    rw [swap_apply_of_ne_of_ne (hne _ _) (hne _ _), swap_apply_of_ne_of_ne (hne _ _) (hne _ _),
      D.smoothingChoice_eq_smoothingChoice (hst j hj)]

/-- If one circle passes through `c` in both smoothings, then the two slots at `c` exchanged by
turning to the next slot and following the smoothing of `s` lie on different directed traversal
orbits of `s`. -/
private theorem not_sameCycle_statePerm_crossing (hst : ∀ j, j ≠ c → s j = t j) (hc : s c ≠ t c)
    (hs : #(D.circlesAt s c) = 1) (ht : #(D.circlesAt t c) = 1) {u : Fin 4}
    (hu : u = bif D.smoothingChoice s c then 1 else 0) :
    ¬ (D.statePerm s).SameCycle (D.crossing c u) (D.crossing c (u + 2)) := by
  -- Otherwise reversal along the smoothing puts the partners of the two slots on one other
  -- directed orbit, and resmoothing `c` splits both orbits, so `t` has one circle more than `s`.
  set σ := D.smoothingTurn (D.smoothingChoice s)
  set π := D.statePerm s with hπdef
  set x := D.crossing c u
  set y := D.crossing c (u + 2)
  have hσapply (k : Fin 4) :
      σ (D.crossing c k) = D.crossing c (slotSmoothing (D.smoothingChoice s c) k) := by
    simp [σ, crossing_apply]
  have hu2 : ∀ v : Fin 4, v ≠ v + 2 := by decide
  have hxy : x ≠ y := fun h ↦ hu2 u (D.crossing_eq_crossing_iff.mp h).2
  have hσxy : σ x ≠ σ y := σ.injective.ne hxy
  have hπt : D.statePerm t = swap (σ x) (σ y) * (swap x y * π) := by
    rw [statePerm_def, hπdef, statePerm_def, smoothingTurn_smoothingChoice_eq_swap_mul_swap_mul
      hst hc hu, hσapply, hσapply, mul_assoc, mul_assoc]
  intro hcyc
  -- Reversal along the smoothing: `σ * π * σ⁻¹ = π⁻¹`.
  have hσσ : σ * σ = 1 := Equiv.ext (D.smoothingTurn_apply_apply _)
  have hαα : D.edgePair.val * D.edgePair.val = 1 := Equiv.ext D.edgePair.apply_apply
  have hconj : σ * π * σ⁻¹ = π⁻¹ := by
    rw [hπdef, statePerm_def, mul_inv_rev, inv_eq_of_mul_eq_one_right hσσ,
      inv_eq_of_mul_eq_one_right hαα, ← mul_assoc, hσσ, one_mul]
  have hcycσ : π.SameCycle (σ x) (σ y) := by
    rw [← sameCycle_inv, ← hconj, sameCycle_conj]
    simpa [inv_eq_of_mul_eq_one_right hσσ, ← Perm.mul_apply, hσσ] using hcyc
  -- No directed orbit is its own reverse.
  have hfree : ¬ π.SameCycle x (σ x) := by
    intro h
    have hrev := (isPerfectMatching_iff.mp (D.isPerfectMatching_stateCycleReversal s)).2 ⟦x⟧
    rw [stateCycleReversal_mk] at hrev
    refine hrev (Quotient.sound ?_)
    have h' : π.SameCycle x (π (D.edgePair.val x)) := by
      simpa [hπdef, statePerm_apply, σ] using h
    exact (sameCycle_apply_right.mp h').symm
  -- Resmoothing splits both directed orbits.
  set π' := swap x y * π
  have horb' : orbitCount π' = orbitCount π + 1 := orbitCount_swap_mul_of_sameCycle hxy hcyc
  have hcyc' : π'.SameCycle (σ x) (σ y) := by
    have hback : π = swap x y * π' := (swap_mul_self_mul x y π).symm
    have hsplit : (swap x y * π').SameCycle x y := hback ▸ hcyc
    rcases (hback ▸ hcycσ : (swap x y * π').SameCycle (σ x) (σ y)).sameCycle_or_of_swap_mul with
      h | ⟨h | h, -⟩
    · exact h
    · exact absurd (hback ▸ hsplit.swap_mul_of_sameCycle h).symm hfree
    · exact absurd (hcyc.trans (hback ▸ hsplit.swap_mul_of_sameCycle h).symm) hfree
  have horbt : orbitCount (D.statePerm t) = orbitCount π + 2 := by
    rw [hπt, orbitCount_swap_mul_of_sameCycle hσxy hcyc', horb']
  -- But one circle passes through `c` in both smoothings, so they have equally many circles.
  have hloops := D.stateLoopCount_add_card_circlesAt hst
  rw [hs, ht, stateLoopCount_def, stateLoopCount_def, horbt, ← hπdef] at hloops
  omega

/-! ### Planar cube edges -/

/-- **Every edge of the cube of resolutions of a planar code is a merge or a split.** If two
states differ exactly at the crossing `c` of a planar code, then three circles pass through `c` in
the two smoothings together: two circles of one smoothing and one circle of the other. -/
theorem IsPlanar.card_circlesAt_add_card_circlesAt_eq_three (hD : D.IsPlanar)
    (hst : ∀ j, j ≠ c → s j = t j) (hc : s c ≠ t c) :
    #(D.circlesAt s c) + #(D.circlesAt t c) = 3 := by
  have hle := D.card_circlesAt_add_card_circlesAt_le_three hst hc
  have hs₀ := (D.circlesAt_nonempty s c).card_pos
  have ht₀ := (D.circlesAt_nonempty t c).card_pos
  by_contra hne
  have hs : #(D.circlesAt s c) = 1 := by omega
  have ht : #(D.circlesAt t c) = 1 := by omega
  set u : Fin 4 := bif D.smoothingChoice s c then 1 else 0 with hu
  have hslots : slotSmoothing (D.smoothingChoice s c) (u + 1) = u + 2 ∧ u ≠ u + 2 := by
    rw [hu]
    cases D.smoothingChoice s c <;>
      simp only [Bool.cond_true, Bool.cond_false, slotSmoothing_true, slotSmoothing_false] <;>
      decide
  obtain ⟨C, hC⟩ := card_eq_one.mp hs
  have hmem (k : Fin 4) : (⟦D.crossing c k⟧ : D.CrossingCircle s) = C :=
    mem_singleton.mp (hC ▸ D.mk_crossing_mem_circlesAt s c k)
  refine D.not_isPlanar_of_not_sameCycle ?_ (fun h ↦ hslots.2 (D.crossing_eq_crossing_iff.mp h).2)
    ((hmem u).trans (hmem (u + 2)).symm) (not_sameCycle_statePerm_crossing hst hc hs ht hu) hD
  rw [smoothingTurn_mul_crossingRotation_crossing, hslots.1]

/-- **Every edge of the cube of resolutions of a planar code is a merge or a split.** If two
states differ exactly at the crossing `c` of a planar code, then two circles pass through `c` in
one of the two smoothings: two circles of `s` merge into one circle of `t`, or one circle of `s`
splits into two circles of `t`. -/
theorem IsPlanar.card_circlesAt_eq_two_or_card_circlesAt_eq_two (hD : D.IsPlanar)
    (hst : ∀ j, j ≠ c → s j = t j) (hc : s c ≠ t c) :
    #(D.circlesAt s c) = 2 ∨ #(D.circlesAt t c) = 2 := by
  have h := hD.card_circlesAt_add_card_circlesAt_eq_three hst hc
  have hs := D.card_circlesAt_le_two s c
  have ht := D.card_circlesAt_le_two t c
  omega

/-- **Along every edge of the cube of resolutions of a planar code, the number of circles changes
by exactly one.** -/
theorem IsPlanar.stateLoopCount_eq_add_one_or_stateLoopCount_eq_add_one (hD : D.IsPlanar)
    (hst : ∀ j, j ≠ c → s j = t j) (hc : s c ≠ t c) :
    D.stateLoopCount s = D.stateLoopCount t + 1 ∨ D.stateLoopCount t = D.stateLoopCount s + 1 := by
  have h := hD.card_circlesAt_add_card_circlesAt_eq_three hst hc
  have hloops := D.stateLoopCount_add_card_circlesAt hst
  have hs := D.card_circlesAt_le_two s c
  have ht := D.card_circlesAt_le_two t c
  omega

end PDCode

end TauCeti
