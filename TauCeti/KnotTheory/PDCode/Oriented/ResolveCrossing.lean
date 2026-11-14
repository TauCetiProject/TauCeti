/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Oriented.Component
public import TauCeti.KnotTheory.PDCode.ResolvedCircle.Seifert
public import TauCeti.KnotTheory.PDCode.VertexResolution
import TauCeti.GroupTheory.Perm.SwapFactors

/-!
# Orienting resolutions and component counts of PD-codes

Resolving one crossing `c` of an oriented PD-code `D` produces two unoriented resolutions,
`D.toPDCode.resolveCrossing c true` and `D.toPDCode.resolveCrossing c false`. Only the coherent
smoothing — the one selected by `TauCeti.OrientedPDCode.seifertState` at `c` — joins incoming
strands to outgoing ones and therefore inherits the half-edge directions of `D`
(`TauCeti.OrientedPDCode.resolveCrossingSeifert`), while retaining explicit Boolean orientation
labels for any newly detached crossing-free circles. The other smoothing merges strands of opposite
local directions; orienting it chooses a direction on each of its unoriented components via
`TauCeti.PDCode.orient` (`TauCeti.OrientedPDCode.resolveCrossingOriented`).

For an oriented PD-code `D` with `m = D.componentCount` link components, whether the two smoothings
at `c` merge or split components depends only on whether the two strands meeting at `c` belong to
the same component of `D`:

* if the two strands lie on different components, both smoothings merge those two components into
  one, so both resolutions have `m - 1` components
  (`TauCeti.OrientedPDCode.componentCount_resolveCrossing_add_one_of_ne`);
* if the two strands lie on the same component, the coherent smoothing splits that component in two
  (`m + 1` components, `TauCeti.OrientedPDCode.componentCount_resolveCrossing_seifertState_of_eq`)
  whereas the incoherent smoothing reconnects it into a single component (`m` components,
  `TauCeti.OrientedPDCode.componentCount_resolveCrossing_not_seifertState_of_eq`), so the two
  component counts are `{m, m + 1}`.

Because every unoriented `PDCode` admits an orientation (`TauCeti.PDCode.orient`), the combined
component-count dichotomy holds for any unoriented `PDCode`
(`TauCeti.PDCode.componentCount_resolveCrossing_dichotomy`). No planarity hypothesis is required for
any of these constructions or component counts.

## Main definitions

* `TauCeti.OrientedPDCode.resolveCrossingSeifert`: the coherent smoothing of an oriented code at a
  crossing `c`, inheriting its half-edge directions and adding explicit Boolean labels for the
  detached circles.
* `TauCeti.OrientedPDCode.resolveCrossingSeifertCrossinglessLabeling`: combine a crossing-free
  circle labelling of `D` with the detached-circle orientation labels.
* `TauCeti.OrientedPDCode.resolveCrossingOriented`: orient either resolution of a crossing `c`,
  using the inherited orientation on the coherent smoothing and a chosen component orientation on
  the other.

## Main results

* `TauCeti.OrientedPDCode.componentCount_resolveCrossing_add_one_of_ne`: when the strands at `c`
  lie on different components of `D` (with `m = D.componentCount`), both resolutions have `m - 1`
  components.
* `TauCeti.OrientedPDCode.componentCount_resolveCrossing_seifertState_of_eq`,
  `TauCeti.OrientedPDCode.componentCount_resolveCrossing_not_seifertState_of_eq`,
  `TauCeti.OrientedPDCode.componentCount_resolveCrossing_true_and_false_of_eq`: when the strands at
  `c` lie on the same component of `D` (with `m = D.componentCount`), the coherent resolution has
  `m + 1` components and the incoherent resolution has `m` components.
* `TauCeti.PDCode.componentCount_resolveCrossing_dichotomy`: for any unoriented `PDCode` `D` with
  `m = D.componentCount`, the `A`- and `B`-resolutions at `c` have component counts either
  `(m - 1, m - 1)` or `{m, m + 1}`.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §3.4.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1 and
  Chapter 3.
-/

public section

namespace TauCeti

open Equiv Equiv.Perm Finset

namespace OrientedPDCode

variable {n : ℕ}

/-! ### Oriented smoothings of a crossing -/

section Smoothings

variable (D : OrientedPDCode (n + 1)) (c : Fin (n + 1))

/-- At crossing `c`, the coherent local smoothing selected by `D.seifertState c` joins half-edges of
opposite orientation. -/
theorem orientation_crossing_slotSmoothing_seifertState (k : Fin 4) :
    D.orientation
        (D.crossing c (PDCode.slotSmoothing
          (bif D.seifertState c then D.overPair c else !D.overPair c) k)) =
      !D.orientation (D.crossing c k) := by
  have hturn : D.crossing c
      (PDCode.slotSmoothing
        (bif D.seifertState c then D.overPair c else !D.overPair c) k) =
      D.smoothingTurn (D.smoothingChoice D.seifertState) (D.crossing c k) := by
    rw [PDCode.crossing_apply (slot := k), PDCode.smoothingTurn_crossing]
    congr 2
    cases hs : D.seifertState c <;> simp [hs]
  rw [hturn, D.orientation_smoothingTurn_seifertState]

/-- **The coherent oriented smoothing** of `D` at crossing `c`: the resolution selected by
`D.seifertState c`, inheriting the half-edge directions of `D` at all remaining crossings and
recording explicit Boolean orientation labels `detached` on the circles detached at `c`. -/
def resolveCrossingSeifert
    (detached : Fin (D.toPDCode.detachedCircleCount c (D.seifertState c)) → Bool) :
    OrientedPDCode n where
  toPDCode := D.toPDCode.resolveCrossing c (D.seifertState c)
  orientation y := D.orientation
    (D.crossing (c.succAbove ((PDCode.crossingSlotEquiv n).symm y).1)
      ((PDCode.crossingSlotEquiv n).symm y).2)
  orientation_edgePair := D.toPDCode.apply_crossing_resolveCrossing_edgePair_eq_not c
    (D.seifertState c) D.orientation_edgePair (D.orientation_crossing_slotSmoothing_seifertState c)
  orientation_oppositeCrossingSlot i slot := by
    simp only [PDCode.resolveCrossing_halfEdge, Perm.one_apply, Equiv.symm_apply_apply,
      PDCode.crossing_apply]
    exact D.orientation_oppositeCrossingSlot (c.succAbove i) slot
  crossinglessComponents := D.crossinglessComponents + Finset.univ.val.map detached
  card_crossinglessComponents := by simp

/-- The underlying unoriented PD-code of `resolveCrossingSeifert` is the coherent resolution. -/
@[simp] theorem toPDCode_resolveCrossingSeifert
    (detached : Fin (D.toPDCode.detachedCircleCount c (D.seifertState c)) → Bool) :
    (D.resolveCrossingSeifert c detached).toPDCode =
      D.toPDCode.resolveCrossing c (D.seifertState c) :=
  (rfl)

/-- The crossing-free circle count of `resolveCrossingSeifert` adds the detached circles at `c`. -/
theorem crossinglessComponentCount_resolveCrossingSeifert
    (detached : Fin (D.toPDCode.detachedCircleCount c (D.seifertState c)) → Bool) :
    (D.resolveCrossingSeifert c detached).crossinglessComponentCount =
      D.crossinglessComponentCount + D.toPDCode.detachedCircleCount c (D.seifertState c) :=
  D.toPDCode.resolveCrossing_crossinglessComponentCount c (D.seifertState c)

/-- Half-edges of `resolveCrossingSeifert` inherit their orientation from `D`. -/
@[simp] theorem orientation_resolveCrossingSeifert
    (detached : Fin (D.toPDCode.detachedCircleCount c (D.seifertState c)) → Bool)
    (i : Fin n) (k : Fin 4) :
    (D.resolveCrossingSeifert c detached).orientation (PDCode.crossingSlotEquiv n (i, k)) =
      D.orientation (D.crossing (c.succAbove i) k) := by
  simp [resolveCrossingSeifert]

/-- The crossing-free circle orientations of `resolveCrossingSeifert` append `detached` to those of
`D`. -/
@[simp] theorem crossinglessComponents_resolveCrossingSeifert
    (detached : Fin (D.toPDCode.detachedCircleCount c (D.seifertState c)) → Bool) :
    (D.resolveCrossingSeifert c detached).crossinglessComponents =
      D.crossinglessComponents + Finset.univ.val.map detached :=
  (rfl)

/-- Every remaining crossing keeps its crossing sign in the coherent smoothing. -/
@[simp] theorem crossingSign_resolveCrossingSeifert
    (detached : Fin (D.toPDCode.detachedCircleCount c (D.seifertState c)) → Bool) (i : Fin n) :
    (D.resolveCrossingSeifert c detached).crossingSign i = D.crossingSign (c.succAbove i) := by
  rw [crossingSign_def, crossingSign_def]
  simp

/-- Combine a crossing-free circle labelling of `D` with the explicit Boolean orientation labels of
the detached circles to obtain a crossing-free labelling of
`D.resolveCrossingSeifert c detached`. -/
def resolveCrossingSeifertCrossinglessLabeling (o : D.CrossinglessLabeling)
    (detached : Fin (D.toPDCode.detachedCircleCount c (D.seifertState c)) → Bool) :
    (D.resolveCrossingSeifert c detached).CrossinglessLabeling :=
  let e : Fin (D.resolveCrossingSeifert c detached).crossinglessComponentCount ≃
      Fin D.crossinglessComponentCount ⊕
        Fin (D.toPDCode.detachedCircleCount c (D.seifertState c)) :=
    (finCongr (by simp)).trans finSumFinEquiv.symm
  ⟨Sum.elim o.val detached ∘ e, by
    ext b
    rw [crossinglessComponents_resolveCrossingSeifert, Multiset.count_add, ← o.occCount_val b,
      ← Function.occCount_eq_count_map_univ, ← Function.occCount_eq_count_map_univ,
      Function.occCount_eq_sum, Function.occCount_eq_sum, Function.occCount_eq_sum]
    simp only [Function.comp_apply]
    rw [e.sum_comp (fun x ↦ if Sum.elim o.val detached x = b then 1 else 0), Fintype.sum_sum_type]
    rfl⟩

/-- On an inherited crossing-free circle of `D`, `resolveCrossingSeifertCrossinglessLabeling`
retains its orientation from `o`. -/
@[simp] theorem resolveCrossingSeifertCrossinglessLabeling_apply_castAdd
    (o : D.CrossinglessLabeling)
    (detached : Fin (D.toPDCode.detachedCircleCount c (D.seifertState c)) → Bool)
    (i : Fin D.crossinglessComponentCount) :
    (D.resolveCrossingSeifertCrossinglessLabeling c o detached).val
        ((Fin.castAdd (D.toPDCode.detachedCircleCount c (D.seifertState c)) i).cast
          (D.crossinglessComponentCount_resolveCrossingSeifert c detached).symm) =
      o.val i := by
  simp [resolveCrossingSeifertCrossinglessLabeling]

/-- On a newly detached circle at `c`, `resolveCrossingSeifertCrossinglessLabeling` reads its
orientation from `detached`. -/
@[simp] theorem resolveCrossingSeifertCrossinglessLabeling_apply_natAdd
    (o : D.CrossinglessLabeling)
    (detached : Fin (D.toPDCode.detachedCircleCount c (D.seifertState c)) → Bool)
    (j : Fin (D.toPDCode.detachedCircleCount c (D.seifertState c))) :
    (D.resolveCrossingSeifertCrossinglessLabeling c o detached).val
        ((Fin.natAdd D.crossinglessComponentCount j).cast
          (D.crossinglessComponentCount_resolveCrossingSeifert c detached).symm) =
      detached j := by
  simp [resolveCrossingSeifertCrossinglessLabeling]

/-- **Orienting either resolution of a crossing.** On the coherent smoothing `t = D.seifertState c`,
inherit the orientation of `D` and use `detached` on the newly detached circles; on the other
smoothing `t = !D.seifertState c`, orient the resolved code using `choice`. -/
noncomputable def resolveCrossingOriented (t : Bool)
    (detached : Fin (D.toPDCode.detachedCircleCount c (D.seifertState c)) → Bool)
    (choice : (D.toPDCode.resolveCrossing c (!D.seifertState c)).UnorientedComponent → Bool) :
    OrientedPDCode n :=
  if t = D.seifertState c then
    D.resolveCrossingSeifert c detached
  else
    (D.toPDCode.resolveCrossing c (!D.seifertState c)).orient choice

/-- When `t = D.seifertState c`, `resolveCrossingOriented` reduces to `resolveCrossingSeifert`. -/
theorem resolveCrossingOriented_of_eq {t : Bool} (ht : t = D.seifertState c)
    (detached : Fin (D.toPDCode.detachedCircleCount c (D.seifertState c)) → Bool)
    (choice : (D.toPDCode.resolveCrossing c (!D.seifertState c)).UnorientedComponent → Bool) :
    D.resolveCrossingOriented c t detached choice = D.resolveCrossingSeifert c detached := by
  simp [resolveCrossingOriented, ht]

/-- When `t ≠ D.seifertState c`, `resolveCrossingOriented` orients the incoherent resolution via
`choice`. -/
theorem resolveCrossingOriented_of_ne {t : Bool} (ht : t ≠ D.seifertState c)
    (detached : Fin (D.toPDCode.detachedCircleCount c (D.seifertState c)) → Bool)
    (choice : (D.toPDCode.resolveCrossing c (!D.seifertState c)).UnorientedComponent → Bool) :
    D.resolveCrossingOriented c t detached choice =
      (D.toPDCode.resolveCrossing c (!D.seifertState c)).orient choice := by
  simp [resolveCrossingOriented, ht]

/-- At `D.seifertState c`, `resolveCrossingOriented` is `resolveCrossingSeifert`. -/
@[simp] theorem resolveCrossingOriented_seifertState
    (detached : Fin (D.toPDCode.detachedCircleCount c (D.seifertState c)) → Bool)
    (choice : (D.toPDCode.resolveCrossing c (!D.seifertState c)).UnorientedComponent → Bool) :
    D.resolveCrossingOriented c (D.seifertState c) detached choice =
      D.resolveCrossingSeifert c detached :=
  D.resolveCrossingOriented_of_eq c rfl detached choice

/-- At `!D.seifertState c`, `resolveCrossingOriented` orients the incoherent resolution via
`choice`. -/
@[simp] theorem resolveCrossingOriented_not_seifertState
    (detached : Fin (D.toPDCode.detachedCircleCount c (D.seifertState c)) → Bool)
    (choice : (D.toPDCode.resolveCrossing c (!D.seifertState c)).UnorientedComponent → Bool) :
    D.resolveCrossingOriented c (!D.seifertState c) detached choice =
      (D.toPDCode.resolveCrossing c (!D.seifertState c)).orient choice :=
  D.resolveCrossingOriented_of_ne c (Bool.not_ne_self _) detached choice

/-- Forgetting orientation after `resolveCrossingOriented` recovers `PDCode.resolveCrossing`. -/
@[simp] theorem toPDCode_resolveCrossingOriented (t : Bool)
    (detached : Fin (D.toPDCode.detachedCircleCount c (D.seifertState c)) → Bool)
    (choice : (D.toPDCode.resolveCrossing c (!D.seifertState c)).UnorientedComponent → Bool) :
    (D.resolveCrossingOriented c t detached choice).toPDCode = D.toPDCode.resolveCrossing c t := by
  by_cases ht : t = D.seifertState c
  · subst ht; simp
  · rw [Bool.eq_not_of_ne ht]; simp

end Smoothings

/-! ### Component-count alternatives for `resolveCrossing` -/

section ComponentCount

private theorem not_sameCycle_of_apply_eq_not {α : Type*} {τ : Perm α} {f : α → Bool}
    (hf : ∀ x, f (τ x) = f x) {x y : α} (hxy : f y = !f x) : ¬τ.SameCycle x y := by
  intro h
  have ho := h.apply_eq_of_apply_eq hf
  rw [hxy] at ho
  cases f x <;> simp at ho

private theorem sameCycle_swap_mul_iff_of_apply_eq_not {α : Type*} [DecidableEq α]
    {τ : Perm α} {f : α → Bool} (hf : ∀ x, f (τ x) = f x) {a₁ b₁ a₂ b₂ : α}
    (hoa₂ : f a₂ = !f a₁) (hob₂ : f a₂ = f b₂) :
    (swap a₂ b₂ * τ).SameCycle a₁ b₁ ↔ τ.SameCycle a₁ b₁ := by
  have hf' (x : α) : f ((swap a₂ b₂ * τ) x) = f x := by
    rw [Perm.mul_apply, Equiv.apply_swap_eq_self hob₂, hf]
  have haux {ρ : Perm α} (hρ : ∀ x, f (ρ x) = f x)
      (h : (swap a₂ b₂ * ρ).SameCycle a₁ b₁) : ρ.SameCycle a₁ b₁ :=
    h.sameCycle_or_of_swap_mul.elim id fun ⟨h1, _⟩ ↦
      h1.elim (fun h2 ↦ absurd h2 (not_sameCycle_of_apply_eq_not hρ hoa₂))
        (fun h2 ↦ absurd h2 (not_sameCycle_of_apply_eq_not hρ (hob₂.symm.trans hoa₂)))
  exact ⟨haux hf, fun h ↦ haux hf' (by rwa [swap_mul_self_mul])⟩

variable (D : OrientedPDCode (n + 1)) (c : Fin (n + 1))

/-- Under either local smoothing, the partners of slots `0` and `2` are slots `1` and `3`. -/
private theorem slotSmoothing_zero_and_two (b : Bool) :
    (PDCode.slotSmoothing b 0 = 1 ∨ PDCode.slotSmoothing b 0 = 3) ∧
      (PDCode.slotSmoothing b 2 = 1 ∨ PDCode.slotSmoothing b 2 = 3) := by
  cases b <;> simp only [PDCode.slotSmoothing_true, PDCode.slotSmoothing_false] <;> decide

private theorem crossing_zero_ne_slotSmoothing_two (b : Bool) :
    D.crossing c 0 ≠ D.crossing c (PDCode.slotSmoothing b 2) := fun h ↦ by
  have hk := (D.toPDCode.crossing_eq_crossing_iff.mp h).2
  rcases (slotSmoothing_zero_and_two b).2 with h2 | h2 <;> omega

private theorem crossing_two_ne_slotSmoothing_zero (b : Bool) :
    D.crossing c 2 ≠ D.crossing c (PDCode.slotSmoothing b 0) := fun h ↦ by
  have hk := (D.toPDCode.crossing_eq_crossing_iff.mp h).2
  rcases (slotSmoothing_zero_and_two b).1 with h0 | h0 <;> omega

/-- Both `slotSmoothing b 0` and `slotSmoothing b 2` lie on the `1`-`3` strand at `c`, so their
half-edges belong to the component of `D.crossing c 1`. -/
private theorem crossingComponentOfHalfEdge_slotSmoothing_zero_and_two (b : Bool) :
    D.crossingComponentOfHalfEdge (D.crossing c (PDCode.slotSmoothing b 0)) =
        D.crossingComponentOfHalfEdge (D.crossing c 1) ∧
      D.crossingComponentOfHalfEdge (D.crossing c (PDCode.slotSmoothing b 2)) =
        D.crossingComponentOfHalfEdge (D.crossing c 1) := by
  have h3 : D.crossingComponentOfHalfEdge (D.crossing c 3) =
      D.crossingComponentOfHalfEdge (D.crossing c 1) :=
    D.crossingComponentOfHalfEdge_crossing_add_two c 1
  obtain ⟨h0, h2⟩ := slotSmoothing_zero_and_two b
  refine ⟨?_, ?_⟩
  · rcases h0 with h0 | h0 <;> rw [h0]
    exact h3
  · rcases h2 with h2 | h2 <;> rw [h2]
    exact h3

/-- At slot level, the non-Seifert smoothing preserves the orientation of all four slots. -/
private theorem slotSmoothing_not_xor_orientation_all (p q : Bool) (k : Fin 4) :
    ![p, q, !p, !q] (PDCode.slotSmoothing (!Bool.xor p q) k) = ![p, q, !p, !q] k := by
  cases p <;> cases q <;> revert k <;>
    simp only [Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true,
      PDCode.slotSmoothing_true, PDCode.slotSmoothing_false] <;> decide

/-- At crossing `c`, the local smoothing opposite to `D.seifertState c` joins half-edges of equal
orientation. -/
private theorem orientation_crossing_slotSmoothing_not_seifertState (k : Fin 4) :
    D.orientation
        (D.crossing c (PDCode.slotSmoothing
          (bif !D.seifertState c then D.overPair c else !D.overPair c) k)) =
      D.orientation (D.crossing c k) := by
  have hb : (bif !D.seifertState c then D.overPair c else !D.overPair c) =
      !Bool.xor (D.orientation (D.crossing c 0)) (D.orientation (D.crossing c 1)) := by
    have hS := D.smoothingChoice_seifertState c
    cases hs : D.seifertState c
    · rw [D.smoothingChoice_of_false hs] at hS
      simpa [hs] using congrArg Bool.not hS
    · rw [D.smoothingChoice_of_true hs] at hS
      simpa [hs] using congrArg Bool.not hS
  rw [hb, D.orientation_crossing_eq c _, D.orientation_crossing_eq c k]
  exact slotSmoothing_not_xor_orientation_all _ _ k

open Classical in
/-- Orbit-count step for the coherent smoothing at `c`. -/
private theorem orbitCount_resolveCrossingTurn_seifertState :
    orbitCount
        (D.toPDCode.resolveCrossingTurn c (D.seifertState c) * D.edgePair.val) +
        (if D.crossingComponentOfHalfEdge (D.crossing c 0) =
            D.crossingComponentOfHalfEdge (D.crossing c 1) then 0 else 2) =
      orbitCount D.toPDCode.componentPerm +
        (if D.crossingComponentOfHalfEdge (D.crossing c 0) =
            D.crossingComponentOfHalfEdge (D.crossing c 1) then 2 else 0) := by
  set b := bif D.seifertState c then D.overPair c else !D.overPair c
  set a₁ := D.crossing c 0
  set b₁ := D.crossing c (PDCode.slotSmoothing b 2) with hb₁
  set a₂ := D.crossing c 2
  set b₂ := D.crossing c (PDCode.slotSmoothing b 0) with hb₂
  set σ := D.toPDCode.componentPerm
  have hori : ∀ x, D.orientation (σ x) = D.orientation x := D.orientation_componentPerm
  have hfac : D.toPDCode.resolveCrossingTurn c (D.seifertState c) * D.edgePair.val =
      swap a₁ b₁ * (swap a₂ b₂ * σ) := by
    rw [PDCode.resolveCrossingTurn_eq_swap_mul_swap_mul_crossingTurn, mul_assoc, mul_assoc,
      ← PDCode.componentPerm_def]
  have hoa₂ : D.orientation a₂ = !D.orientation a₁ :=
    D.orientation_crossing_of_add_two_eq c rfl
  have hob₁ : D.orientation a₁ = D.orientation b₁ := by
    rw [hb₁, D.orientation_crossing_slotSmoothing_seifertState c 2, hoa₂, Bool.not_not]
  have hob₂ : D.orientation a₂ = D.orientation b₂ := by
    rw [hb₂, D.orientation_crossing_slotSmoothing_seifertState c 0, hoa₂]
  have hcomp := D.crossingComponentOfHalfEdge_slotSmoothing_zero_and_two c b
  have hca₂ : D.crossingComponentOfHalfEdge a₂ = D.crossingComponentOfHalfEdge a₁ :=
    D.crossingComponentOfHalfEdge_crossing_add_two c 0
  have hsc₁₂ := sameCycle_swap_mul_iff_of_apply_eq_not hori (b₁ := b₁) hoa₂ hob₂
  rw [hfac]
  by_cases hc : D.crossingComponentOfHalfEdge a₁ = D.crossingComponentOfHalfEdge (D.crossing c 1)
  · have hc₁ : σ.SameCycle a₁ b₁ :=
      (D.sameCycle_componentPerm_iff_crossingComponentOfHalfEdge_eq hob₁).mpr
        (hc.trans hcomp.2.symm)
    have hc₂ : σ.SameCycle a₂ b₂ :=
      (D.sameCycle_componentPerm_iff_crossingComponentOfHalfEdge_eq hob₂).mpr
        (hca₂.trans (hc.trans hcomp.1.symm))
    simp only [hc, ↓reduceIte]
    rw [orbitCount_swap_mul_of_sameCycle (D.crossing_zero_ne_slotSmoothing_two c b)
        (hsc₁₂.mpr hc₁),
      orbitCount_swap_mul_of_sameCycle (D.crossing_two_ne_slotSmoothing_zero c b) hc₂]
  · have hc₁ : ¬σ.SameCycle a₁ b₁ := fun h ↦ hc <|
      ((D.sameCycle_componentPerm_iff_crossingComponentOfHalfEdge_eq hob₁).mp h).trans hcomp.2
    have hc₂ : ¬σ.SameCycle a₂ b₂ := fun h ↦ hc <| hca₂.symm.trans <|
      ((D.sameCycle_componentPerm_iff_crossingComponentOfHalfEdge_eq hob₂).mp h).trans hcomp.1
    have hstep₁ := orbitCount_swap_mul_add_one_of_not_sameCycle (hsc₁₂.not.mpr hc₁)
    have hstep₂ := orbitCount_swap_mul_add_one_of_not_sameCycle hc₂
    simp only [hc, ↓reduceIte]
    omega

open Classical in
/-- Orbit-count step for the incoherent smoothing at `c`. -/
private theorem orbitCount_resolveCrossingTurn_not_seifertState :
    orbitCount
        (D.toPDCode.resolveCrossingTurn c (!D.seifertState c) * D.edgePair.val) +
        (if D.crossingComponentOfHalfEdge (D.crossing c 0) =
            D.crossingComponentOfHalfEdge (D.crossing c 1) then 0 else 2) =
      orbitCount D.toPDCode.componentPerm := by
  set b := bif !D.seifertState c then D.overPair c else !D.overPair c
  set a₁ := D.crossing c 0
  set b₁ := D.crossing c (PDCode.slotSmoothing b 2)
  set a₂ := D.crossing c 2
  set b₂ := D.crossing c (PDCode.slotSmoothing b 0)
  set σ := D.toPDCode.componentPerm
  have hori : ∀ x, D.orientation (σ x) = D.orientation x := D.orientation_componentPerm
  have hfac : D.toPDCode.resolveCrossingTurn c (!D.seifertState c) * D.edgePair.val =
      swap a₁ b₁ * (swap a₂ b₂ * σ) := by
    rw [PDCode.resolveCrossingTurn_eq_swap_mul_swap_mul_crossingTurn, mul_assoc, mul_assoc,
      ← PDCode.componentPerm_def]
  have hoa₂ : D.orientation a₂ = !D.orientation a₁ := D.orientation_crossing_of_add_two_eq c rfl
  have hob₁ : D.orientation b₁ = D.orientation a₂ :=
    D.orientation_crossing_slotSmoothing_not_seifertState c 2
  have hob₂ : D.orientation b₂ = D.orientation a₁ :=
    D.orientation_crossing_slotSmoothing_not_seifertState c 0
  have hcomp := D.crossingComponentOfHalfEdge_slotSmoothing_zero_and_two c b
  have hca₂ : D.crossingComponentOfHalfEdge a₂ = D.crossingComponentOfHalfEdge a₁ :=
    D.crossingComponentOfHalfEdge_crossing_add_two c 0
  have hnot₂ : ¬σ.SameCycle a₂ b₂ :=
    not_sameCycle_of_apply_eq_not hori (by rw [hob₂, hoa₂, Bool.not_not])
  have hstep₂ := orbitCount_swap_mul_add_one_of_not_sameCycle hnot₂
  have hab₂ : (swap a₂ b₂ * σ).SameCycle a₂ b₂ :=
    sameCycle_swap_mul_of_mem_periodicPts_of_not_sameCycle (σ.injective.mem_periodicPts b₂) hnot₂
  rw [hfac]
  by_cases hc : D.crossingComponentOfHalfEdge a₁ = D.crossingComponentOfHalfEdge (D.crossing c 1)
  · have hc₁₂ : σ.SameCycle a₁ b₂ :=
      (D.sameCycle_componentPerm_iff_crossingComponentOfHalfEdge_eq hob₂.symm).mpr
        (hc.trans hcomp.1.symm)
    have hc₂₁ : σ.SameCycle a₂ b₁ :=
      (D.sameCycle_componentPerm_iff_crossingComponentOfHalfEdge_eq hob₁.symm).mpr
        (hca₂.trans (hc.trans hcomp.2.symm))
    have hsc₁ : (swap a₂ b₂ * σ).SameCycle a₁ b₁ :=
      (hab₂.swap_mul_of_sameCycle hc₁₂).trans (hab₂.symm.trans (hab₂.swap_mul_of_sameCycle hc₂₁))
    simp only [hc, ↓reduceIte]
    rw [orbitCount_swap_mul_of_sameCycle (D.crossing_zero_ne_slotSmoothing_two c b) hsc₁]
    omega
  · have hnot₁ : ¬(swap a₂ b₂ * σ).SameCycle a₁ b₁ := fun h ↦
      h.sameCycle_or_of_swap_mul.elim (not_sameCycle_of_apply_eq_not hori (hob₁.trans hoa₂))
        fun ⟨h1, _⟩ ↦ h1.elim (not_sameCycle_of_apply_eq_not hori hoa₂) fun h2 ↦ hc <|
          ((D.sameCycle_componentPerm_iff_crossingComponentOfHalfEdge_eq hob₂.symm).mp h2).trans
            hcomp.1
    have hstep₁ := orbitCount_swap_mul_add_one_of_not_sameCycle hnot₁
    simp only [hc, ↓reduceIte]
    omega

/-- **Different-component resolution.** If the two strands at `c` lie on different components of
`D`, then both smoothings of `c` merge those two components and therefore have one component fewer
than `D`. -/
theorem componentCount_resolveCrossing_add_one_of_ne
    (hc : D.crossingComponentOfHalfEdge (D.crossing c 0) ≠
      D.crossingComponentOfHalfEdge (D.crossing c 1)) (t : Bool) :
    (D.toPDCode.resolveCrossing c t).componentCount + 1 = D.componentCount := by
  have htwo := D.toPDCode.two_mul_componentCount_resolveCrossing c t
  have hD := D.toPDCode.two_mul_componentCount
  by_cases ht : t = D.seifertState c
  · subst ht
    have hs := D.orbitCount_resolveCrossingTurn_seifertState c
    simp only [hc, ↓reduceIte] at hs
    omega
  · have hnot : t = !D.seifertState c := Bool.eq_not_of_ne ht
    subst hnot
    have hs := D.orbitCount_resolveCrossingTurn_not_seifertState c
    simp only [hc, ↓reduceIte] at hs
    omega

/-- Subtracted form of `componentCount_resolveCrossing_add_one_of_ne`: both smoothings at a
crossing between two distinct components have `D.componentCount - 1` components. -/
theorem componentCount_resolveCrossing_of_ne
    (hc : D.crossingComponentOfHalfEdge (D.crossing c 0) ≠
      D.crossingComponentOfHalfEdge (D.crossing c 1)) (t : Bool) :
    (D.toPDCode.resolveCrossing c t).componentCount = D.componentCount - 1 := by
  have h := D.componentCount_resolveCrossing_add_one_of_ne c hc t
  omega

/-- **Same-component coherent resolution.** If the two strands at `c` belong to the same component
of `D`, then the coherent smoothing `D.seifertState c` splits that component in two, giving
`D.componentCount + 1` components. -/
theorem componentCount_resolveCrossing_seifertState_of_eq
    (hc : D.crossingComponentOfHalfEdge (D.crossing c 0) =
      D.crossingComponentOfHalfEdge (D.crossing c 1)) :
    (D.toPDCode.resolveCrossing c (D.seifertState c)).componentCount = D.componentCount + 1 := by
  have htwo := D.toPDCode.two_mul_componentCount_resolveCrossing c (D.seifertState c)
  have hD := D.toPDCode.two_mul_componentCount
  have hs := D.orbitCount_resolveCrossingTurn_seifertState c
  simp only [hc, ↓reduceIte] at hs
  omega

/-- **Same-component incoherent resolution.** If the two strands at `c` belong to the same
component of `D`, then the incoherent smoothing `!D.seifertState c` reconnects that component into
one component, preserving `D.componentCount`. -/
theorem componentCount_resolveCrossing_not_seifertState_of_eq
    (hc : D.crossingComponentOfHalfEdge (D.crossing c 0) =
      D.crossingComponentOfHalfEdge (D.crossing c 1)) :
    (D.toPDCode.resolveCrossing c (!D.seifertState c)).componentCount = D.componentCount := by
  have htwo := D.toPDCode.two_mul_componentCount_resolveCrossing c (!D.seifertState c)
  have hD := D.toPDCode.two_mul_componentCount
  have hs := D.orbitCount_resolveCrossingTurn_not_seifertState c
  simp only [hc, ↓reduceIte] at hs
  omega

/-- At a self-crossing `c` of one component of `D` (with `m = D.componentCount`), the `A`- and
`B`-resolutions have component counts `{m + 1, m}` (in the order determined by
`D.seifertState c`). -/
theorem componentCount_resolveCrossing_true_and_false_of_eq
    (hc : D.crossingComponentOfHalfEdge (D.crossing c 0) =
      D.crossingComponentOfHalfEdge (D.crossing c 1)) :
    ((D.toPDCode.resolveCrossing c true).componentCount = D.componentCount + 1 ∧
        (D.toPDCode.resolveCrossing c false).componentCount = D.componentCount) ∨
      ((D.toPDCode.resolveCrossing c true).componentCount = D.componentCount ∧
        (D.toPDCode.resolveCrossing c false).componentCount = D.componentCount + 1) := by
  have hS := D.componentCount_resolveCrossing_seifertState_of_eq c hc
  have hN := D.componentCount_resolveCrossing_not_seifertState_of_eq c hc
  cases hs : D.seifertState c
  · rw [hs] at hS hN
    exact .inr ⟨by simpa using hN, hS⟩
  · rw [hs] at hS hN
    exact .inl ⟨hS, by simpa using hN⟩

end ComponentCount

end OrientedPDCode

namespace PDCode

variable {n : ℕ}

/-- **Component-count dichotomy for `resolveCrossing`.** At any crossing `c` of an unoriented
PD-code `D` with `m = D.componentCount` components, either both resolutions have `m - 1` components
(when `c` joins two distinct components), or their component counts are `{m + 1, m}` (when `c` is a
self-crossing of one component). -/
theorem componentCount_resolveCrossing_dichotomy (D : PDCode (n + 1)) (c : Fin (n + 1)) :
    ((D.resolveCrossing c true).componentCount + 1 = D.componentCount ∧
        (D.resolveCrossing c false).componentCount + 1 = D.componentCount) ∨
      ((D.resolveCrossing c true).componentCount = D.componentCount + 1 ∧
          (D.resolveCrossing c false).componentCount = D.componentCount) ∨
        ((D.resolveCrossing c true).componentCount = D.componentCount ∧
          (D.resolveCrossing c false).componentCount = D.componentCount + 1) := by
  let E := D.orient fun _ ↦ true
  by_cases hc : E.crossingComponentOfHalfEdge (E.crossing c 0) =
      E.crossingComponentOfHalfEdge (E.crossing c 1)
  · right
    simpa [E] using E.componentCount_resolveCrossing_true_and_false_of_eq c hc
  · left
    exact ⟨by simpa [E] using E.componentCount_resolveCrossing_add_one_of_ne c hc true,
      by simpa [E] using E.componentCount_resolveCrossing_add_one_of_ne c hc false⟩

end PDCode

end TauCeti
