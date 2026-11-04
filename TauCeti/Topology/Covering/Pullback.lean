/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Homotopy.Lifting
public import TauCeti.Data.Set.Prod
public import TauCeti.Topology.Constructions.Basic

/-!
# Pulling a covering map back along a continuous map

Let `g : Z → Y` be a covering map and `f : X → Y` a continuous map. The fibre product
`X ×_Y Z = {(x, z) | f x = g z}` (Mathlib's `Function.Pullback f g`), with the subspace topology
of `X × Z`, projects to `X` by `Function.Pullback.fst`, and that projection is again a covering map
whose fibre over `x` is the fibre of `g` over `f x`. If `H : g ⁻¹' U ≃ₜ U × I` trivialises `g` over
an open `U ∋ f x`, then `(x', z) ↦ (x', (H z).2)` trivialises the projection over `f ⁻¹' U`.

The relative version is what produces covers from equations: for `n ≠ 0` the power map
`y ↦ y ^ n` is a covering of `ℂ` over `ℂ ∖ {0}`, so for a continuous `h : X → ℂ` without zeros
the curve `{(x, y) | h x = y ^ n}` is a covering of `X`.

Pulling a covering back along a homotopy equivalence `e : A ≃ₕ B` does not change the homotopy
type of the total space: the projection `A ×_B E → E` is a homotopy equivalence. With
`φ : A → B`, `ψ : B → A` and homotopies `φ ∘ ψ ≃ id` and `ψ ∘ φ ≃ id`, the homotopy inverse sends
`e ∈ E` to `ψ (p e)` together with the end of the lift at `e` of the path from `p e` to
`φ (ψ (p e))`. That this is a right homotopy inverse follows from the lifted homotopy. For the other
side, the same construction for the pulled-back covering `A ×_B E → A` and the map `ψ` gives a right
homotopy inverse of the projection `B ×_A (A ×_B E) → A ×_B E`; following a path forwards and back
returns to its start by uniqueness of lifts, and the two one-sided inverses combine. Only the
homotopy lifting property of coverings and uniqueness of path lifts are used; no compatibility
between the two homotopies is needed.

## Main results

* `IsEvenlyCovered.pullback_fst`: a point evenly covered by `g` pulls back to evenly covered points
  of the projection, with the same fibre.
* `IsCoveringMap.pullback_fst`: the pullback of a covering map is a covering map.
* `IsCoveringMapOn.pullback_fst`: the pullback of a map that is a covering over `s` is a covering
  over the preimage of `s`.
* `IsCoveringMapOn.isCoveringMap_pullback_fst`: the pullback of a map that is a covering over `s`
  along a map into `s` is a covering map.
* `IsCoveringMap.pullbackHomotopyEquiv`: the pullback of a covering map along a homotopy
  equivalence has homotopy equivalent total space.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §1.3 (covering spaces and
  their lifting properties, Proposition 1.30 for homotopy lifting).
* J. P. May, *A Concise Course in Algebraic Topology*, University of Chicago Press, 1999,
  Chapter 7 (fibrations; the pullback of a fibration along a homotopy equivalence).
-/

public section

open Function

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {f : X → Y}
  {g : Z → Y}

/-- If `f x` is evenly covered by `g` with fibre `I`, then `x` is evenly covered with fibre `I` by
the projection `X ×_Y Z → X` of the fibre product of `f` and `g`. -/
theorem IsEvenlyCovered.pullback_fst {I : Type*} [TopologicalSpace I] {x : X} (hf : Continuous f)
    (h : IsEvenlyCovered g (f x) I) :
    IsEvenlyCovered (Pullback.fst : f.Pullback g → X) x I := by
  obtain ⟨hI, U, hxU, hU, hgU, H, hH⟩ := h
  -- The point of `g ⁻¹' U` under a point of the fibre product over `f ⁻¹' U`.
  let k (w : Pullback.fst ⁻¹' (f ⁻¹' U)) : g ⁻¹' U :=
    ⟨w.1.snd, by
      rw [Set.mem_preimage, ← (show f w.1.fst = g w.1.snd from w.1.2)]
      exact w.2⟩
  have hk : Continuous k := (Pullback.continuous_snd.comp continuous_subtype_val).subtype_mk _
  -- A point of the fibre of `g` over `f x'`, for `x' ∈ f ⁻¹' U`, from its sheet index.
  let l (v : f ⁻¹' U × I) : g ⁻¹' U := H.symm (⟨f v.1, v.1.2⟩, v.2)
  have hl : Continuous l :=
    H.symm.continuous.comp ((((hf.comp continuous_subtype_val).comp continuous_fst).subtype_mk
      _).prodMk continuous_snd)
  have hgl (v : f ⁻¹' U × I) : f v.1 = g (l v) := by
    rw [← hH, Homeomorph.apply_symm_apply]
  -- `l` inverts the sheet index of the point of `g ⁻¹' U` under a point of the fibre product.
  have hlk (w : Pullback.fst ⁻¹' (f ⁻¹' U)) : l (⟨w.1.fst, w.2⟩, (H (k w)).2) = k w := by
    have hHk : H (k w) = (⟨f w.1.fst, w.2⟩, (H (k w)).2) :=
      Prod.ext (Subtype.ext ((hH (k w)).trans w.1.2.symm)) rfl
    simp only [l, ← hHk, Homeomorph.symm_apply_apply]
  refine ⟨hI, f ⁻¹' U, hxU, hU.preimage hf, (hU.preimage hf).preimage Pullback.continuous_fst,
    { toFun w := (⟨w.1.fst, w.2⟩, (H (k w)).2)
      invFun v := ⟨⟨(v.1, l v), hgl v⟩, v.1.2⟩
      left_inv w := Subtype.ext (Subtype.ext (Prod.ext rfl (congrArg Subtype.val (hlk w))))
      right_inv v := by
        refine Prod.ext rfl ?_
        -- `k` of the inverse image of `v` is `l v`, up to eta for subtypes.
        exact (congrArg Prod.snd (H.apply_symm_apply (⟨f v.1, v.1.2⟩, v.2)) :)
      continuous_toFun :=
        ((Pullback.continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
          (continuous_snd.comp (H.continuous.comp hk))
      continuous_invFun := by
        refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
        exact (continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp hl) },
    fun _ ↦ rfl⟩

/-- **The pullback of a covering map is a covering map**: for a covering map `g : Z → Y` and a
continuous `f : X → Y`, the projection `X ×_Y Z → X` of the fibre product is a covering map. -/
theorem IsCoveringMap.pullback_fst (hg : IsCoveringMap g) (hf : Continuous f) :
    IsCoveringMap (Pullback.fst : f.Pullback g → X) :=
  fun x ↦ ((hg (f x)).pullback_fst hf).to_isEvenlyCovered_preimage

/-- If `g : Z → Y` is a covering map over `s` and `f : X → Y` is continuous, then the projection
`X ×_Y Z → X` of the fibre product is a covering map over `f ⁻¹' s`. -/
theorem IsCoveringMapOn.pullback_fst {s : Set Y} (hg : IsCoveringMapOn g s) (hf : Continuous f) :
    IsCoveringMapOn (Pullback.fst : f.Pullback g → X) (f ⁻¹' s) :=
  fun x hx ↦ ((hg (f x) hx).pullback_fst hf).to_isEvenlyCovered_preimage

/-- If `g : Z → Y` is a covering map over `s` and the continuous map `f : X → Y` takes values in
`s`, then the projection `X ×_Y Z → X` of the fibre product is a covering map. -/
theorem IsCoveringMapOn.isCoveringMap_pullback_fst {s : Set Y} (hg : IsCoveringMapOn g s)
    (hf : Continuous f) (hfs : ∀ x, f x ∈ s) :
    IsCoveringMap (Pullback.fst : f.Pullback g → X) :=
  fun x ↦ hg.pullback_fst hf x (hfs x)

/-! ### Pulling back along a homotopy equivalence -/

section HomotopyEquiv

open ContinuousMap unitInterval

namespace IsCoveringMap

variable {E B A : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace A]
  {p : E → B} (hp : IsCoveringMap p) {φ : C(A, B)} {ψ : C(B, A)}

/-- The lift, starting at the identity of `E`, of the homotopy `H` run backwards from `p`
to `φ ∘ ψ ∘ p`. -/
private noncomputable def revLift (H : (φ.comp ψ).Homotopy (.id B)) : C(I × E, E) :=
  hp.liftHomotopy
    (H.symm.toContinuousMap.comp ((ContinuousMap.id I).prodMap ⟨p, hp.continuous⟩))
    (.id E) fun e ↦ by simp

private theorem revLift_lifts (H : (φ.comp ψ).Homotopy (.id B)) (t : I) (e : E) :
    p (hp.revLift H (t, e)) = H (σ t, p e) :=
  congr_fun (hp.liftHomotopy_lifts _ _ _) (t, e)

private theorem revLift_zero (H : (φ.comp ψ).Homotopy (.id B)) (e : E) :
    hp.revLift H (0, e) = e :=
  hp.liftHomotopy_zero _ _ _ e

private theorem revLift_one (H : (φ.comp ψ).Homotopy (.id B)) (e : E) :
    p (hp.revLift H (1, e)) = φ (ψ (p e)) := by
  rw [hp.revLift_lifts, symm_one, H.apply_zero, ContinuousMap.comp_apply]

/-- The homotopy inverse of the projection `A ×_B E → E`: a point `e` goes to `ψ (p e)`,
together with the endpoint of the lift at `e` of the path `H` from `p e` back to
`φ (ψ (p e))`. -/
private noncomputable def pullbackInv (H : (φ.comp ψ).Homotopy (.id B)) :
    C(E, Pullback φ p) where
  toFun e := ⟨(ψ (p e), hp.revLift H (1, e)), (hp.revLift_one H e).symm⟩
  continuous_toFun := ((ψ.continuous.comp hp.continuous).prodMk
    ((hp.revLift H).continuous.comp (continuous_const.prodMk continuous_id))).subtype_mk _

/-- The projection `A ×_B E → E` is a left homotopy inverse of `pullbackInv`. -/
private theorem homotopic_pullbackSnd_comp_pullbackInv (H : (φ.comp ψ).Homotopy (.id B)) :
    ((pullbackSnd φ p).comp (hp.pullbackInv H)).Homotopic (.id E) :=
  ⟨{ toContinuousMap :=
       (hp.revLift H).comp ((ContinuousMap.mk σ continuous_symm).prodMap (.id E))
     map_zero_left e := by simp [pullbackInv, Pullback.snd]
     map_one_left e := by simp [hp.revLift_zero] }⟩

/-- The lift of the homotopy `H`, run forwards along the first coordinate of the iterated fibre
product `B ×_A (A ×_B E)`, starting at its last coordinate. -/
private noncomputable def fwdLift (H : (φ.comp ψ).Homotopy (.id B)) :
    C(I × Pullback ψ (Pullback.fst : Pullback φ p → A), E) :=
  hp.liftHomotopy (H.toContinuousMap.comp ((ContinuousMap.id I).prodMap (pullbackFst ψ _)))
    ((pullbackSnd φ p).comp (pullbackSnd ψ _)) fun x ↦ by
    simp only [ContinuousMap.comp_apply, prodMap_apply, coe_pullbackFst, coe_pullbackSnd, Prod.map,
      ContinuousMap.id_apply, Homotopy.coe_toContinuousMap, H.apply_zero]
    exact (congrArg φ x.2).trans x.1.2.2

private theorem fwdLift_lifts (H : (φ.comp ψ).Homotopy (.id B)) (t : I)
    (x : Pullback ψ (Pullback.fst : Pullback φ p → A)) :
    p (hp.fwdLift H (t, x)) = H (t, x.fst) :=
  (congr_fun (hp.liftHomotopy_lifts _ _ _) (t, x) : p (hp.fwdLift H (t, x)) = _).trans (by simp)

private theorem fwdLift_zero (H : (φ.comp ψ).Homotopy (.id B))
    (x : Pullback ψ (Pullback.fst : Pullback φ p → A)) :
    hp.fwdLift H (0, x) = x.snd.snd :=
  (hp.liftHomotopy_zero _ _ _ x : hp.fwdLift H (0, x) = _).trans (by simp)

/-- The endpoint of `fwdLift`. -/
private noncomputable def fwdEnd (H : (φ.comp ψ).Homotopy (.id B)) :
    C(Pullback ψ (Pullback.fst : Pullback φ p → A), E) :=
  (hp.fwdLift H).comp ((ContinuousMap.const _ 1).prodMk (.id _))

/-- The map `E → B ×_A (A ×_B E)` sending `e` to `(p e, pullbackInv e)`. -/
private noncomputable def pullbackInvLift (H : (φ.comp ψ).Homotopy (.id B)) :
    C(E, Pullback ψ (Pullback.fst : Pullback φ p → A)) where
  toFun e := ⟨(p e, hp.pullbackInv H e), rfl⟩
  continuous_toFun := (hp.continuous.prodMk (hp.pullbackInv H).continuous).subtype_mk _

/-- The last coordinate of `pullbackInvLift e` is `pullbackInv e`. -/
private theorem pullbackSnd_comp_pullbackInvLift (H : (φ.comp ψ).Homotopy (.id B)) :
    (pullbackSnd ψ (Pullback.fst : Pullback φ p → A)).comp (hp.pullbackInvLift H) =
      hp.pullbackInv H := by
  -- `pullbackInvLift` is defined with `pullbackInv` as its second coordinate
  ext1 e
  rw [ContinuousMap.comp_apply, coe_pullbackSnd]
  rfl

/-- Following `H` forwards and then backwards returns to the start: `pullbackInvLift` is a left
inverse of `fwdEnd`. -/
private theorem pullbackInvLift_comp_fwdEnd (H : (φ.comp ψ).Homotopy (.id B)) :
    (hp.pullbackInvLift H).comp (hp.fwdEnd H) = .id _ := by
  ext1 x
  have hb : p (hp.fwdLift H (1, x)) = x.fst := by rw [hp.fwdLift_lifts, H.apply_one]; rfl
  -- the backward lift from the endpoint is the forward lift traversed in reverse
  have hpath : (fun t ↦ hp.revLift H (t, hp.fwdLift H (1, x))) =
      fun t ↦ hp.fwdLift H (σ t, x) := by
    refine hp.eq_of_comp_eq (by fun_prop) (by fun_prop) (funext fun t ↦ ?_) 0 ?_
    · simp only [Function.comp_apply, hp.revLift_lifts, hp.fwdLift_lifts, H.apply_one,
        ContinuousMap.id_apply]
    · simp only [hp.revLift_zero, symm_zero]
  have he : hp.revLift H (1, hp.fwdLift H (1, x)) = x.snd.snd := by
    rw [congr_fun hpath 1, symm_one, hp.fwdLift_zero]
  exact Pullback.ext hb (Pullback.ext ((congrArg ψ hb).trans x.2) he)

/-- The projection `A ×_B E → E` is a right homotopy inverse of `pullbackInv`. -/
private theorem homotopic_pullbackInv_comp_pullbackSnd (H : (φ.comp ψ).Homotopy (.id B))
    (K : (ψ.comp φ).Homotopy (.id A)) :
    ((hp.pullbackInv H).comp (pullbackSnd φ p)).Homotopic (.id (Pullback φ p)) := by
  have hq : IsCoveringMap (Pullback.fst : Pullback φ p → A) := hp.pullback_fst φ.continuous
  set s := pullbackSnd ψ (Pullback.fst : Pullback φ p → A)
  -- `pullbackInv` for the pulled back covering, with the roles of `φ` and `ψ` exchanged, is a
  -- right homotopy inverse of the projection `s`
  have h₁ : (s.comp (hq.pullbackInv K)).Homotopic (.id _) :=
    hq.homotopic_pullbackSnd_comp_pullbackInv K
  -- the two projections to `E` are homotopic to the endpoint of `fwdLift`
  have h₂ : ((pullbackSnd φ p).comp s).Homotopic (hp.fwdEnd H) :=
    ⟨{ toContinuousMap := hp.fwdLift H
       map_zero_left x := by simpa [s] using hp.fwdLift_zero H x
       map_one_left _ := rfl }⟩
  -- `pullbackInv = s ∘ pullbackInvLift`; insert `s ∘ hq.pullbackInv K ≃ id` on the right
  rw [← hp.pullbackSnd_comp_pullbackInvLift H, ← ContinuousMap.comp_id ((s.comp _).comp _)]
  refine ((Homotopic.refl _).comp h₁.symm).trans ?_
  -- regroup so that `s` followed by the projection to `E` appears, and replace it by `fwdEnd`
  rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc,
    ← ContinuousMap.comp_assoc (pullbackSnd φ p) s]
  refine ((Homotopic.refl _).comp ((Homotopic.refl _).comp (h₂.comp (Homotopic.refl _)))).trans ?_
  rw [← ContinuousMap.comp_assoc (hp.pullbackInvLift H), hp.pullbackInvLift_comp_fwdEnd H,
    ContinuousMap.id_comp]
  exact h₁

/-- **Pulling a covering back along a homotopy equivalence.** If `p : E → B` is a covering map
and `e : A ≃ₕ B` is a homotopy equivalence, then the projection `A ×_B E → E` from the fibre
product of `e` and `p` is a homotopy equivalence. -/
noncomputable def pullbackHomotopyEquiv (e : A ≃ₕ B) : Pullback e p ≃ₕ E where
  toFun := pullbackSnd e p
  invFun := hp.pullbackInv e.right_inv.some
  left_inv := hp.homotopic_pullbackInv_comp_pullbackSnd e.right_inv.some e.left_inv.some
  right_inv := hp.homotopic_pullbackSnd_comp_pullbackInv e.right_inv.some

@[simp]
theorem coe_pullbackHomotopyEquiv (e : A ≃ₕ B) :
    ⇑(hp.pullbackHomotopyEquiv e) = Pullback.snd :=
  coe_pullbackSnd _ _

/-- The first coordinate of the homotopy inverse of the projection `A ×_B E → E` at `x` is
`e.symm (p x)`. -/
@[simp]
theorem pullbackHomotopyEquiv_symm_apply_fst (e : A ≃ₕ B) (x : E) :
    ((hp.pullbackHomotopyEquiv e).symm x).fst = e.symm (p x) :=
  (rfl)

end IsCoveringMap

end HomotopyEquiv
