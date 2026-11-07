/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Presentation.Schreier.Rewriting
public import TauCeti.GroupTheory.PresentedGroup

/-!
# Presentations of stabilizers by signed Schreier rewriting

For a group given by signed relator words, choose a transitive action and representative words
whose inverses carry a base point to every state. The stabilizer has generators indexed by
positive edges. Its relators are the rewrites of the original relators at every state, together
with the rewrites of the representative words at the base point.

`TauCeti.Schreier.stabilizerEquiv` identifies this presentation with the actual stabilizer.
Representatives need not form a prefix-closed Schreier transversal: the representative-word
relators account for redundant edge generators. No finite-index or involution assumption is used.
This permits subsequent Tietze elimination without assuming a free basis for the stabilizer.

## References

* D. L. Johnson, *Presentations of Groups*, second edition, Chapter 9
  (Reidemeister--Schreier rewriting).
-/

public section

namespace TauCeti.Schreier

variable {α Q : Type*}

/-- Rewritten defining relators at every state, and the representative-word relators which
remove redundant positive-edge generators. -/
def stabilizerRelators (σ : α → Equiv.Perm Q) (W : Set (PresentationWord α))
    (b : Q) (r : Q → PresentationWord α) : Set (FreeGroup (Q × α)) :=
  {v | (∃ q w, w ∈ W ∧ FreeGroup.mk (rewrite σ q w) = v) ∨
    ∃ q, FreeGroup.mk (rewrite σ b (r q)) = v}

@[simp]
theorem mem_stabilizerRelators (σ : α → Equiv.Perm Q) (W : Set (PresentationWord α))
    (b : Q) (r : Q → PresentationWord α) (v : FreeGroup (Q × α)) :
    v ∈ stabilizerRelators σ W b r ↔
      (∃ q w, w ∈ W ∧ FreeGroup.mk (rewrite σ q w) = v) ∨
        ∃ q, FreeGroup.mk (rewrite σ b (r q)) = v := Iff.rfl

variable (W : Set (PresentationWord α))
local notation "G" => PresentedGroup (FreeGroup.mk '' W)
local notation "f" => (PresentedGroup.of : α → G)

variable [action : MulAction (PresentedGroup (FreeGroup.mk '' W)) Q]
  (b : Q) (r : Q → PresentationWord α)
local notation "σ" => actionPerm (Q := Q) f
local notation "R" => stabilizerRelators σ W b r
local notation "K" => PresentedGroup R
local notation "ev" => (PresentedGroup.mk (FreeGroup.mk '' W))

variable (hr : ∀ q : Q,
  ((PresentedGroup.mk (FreeGroup.mk '' W)) (FreeGroup.mk (r q)))⁻¹ • b = q)
  (hb : (PresentedGroup.mk (FreeGroup.mk '' W)) (FreeGroup.mk (r b)) = 1)

include hr hb in
private theorem rewritten_relators_sound (v : FreeGroup (Q × α)) (hv : v ∈ R) :
    FreeGroup.lift (stabilizerGenerator f b (fun q => ev (FreeGroup.mk (r q))) hr) v = 1 := by
  apply Subtype.ext
  have hc : (FreeGroup.lift
      (stabilizerGenerator f b (fun q => ev (FreeGroup.mk (r q))) hr) v : G) =
      FreeGroup.lift (generator σ f (fun q => ev (FreeGroup.mk (r q)))) v :=
    FreeGroup.lift_unique ((MulAction.stabilizer G b).subtype.comp
      (FreeGroup.lift (stabilizerGenerator f b (fun q => ev (FreeGroup.mk (r q))) hr)))
      (by intro e; simp)
  rw [hc]
  rcases hv with ⟨q, w, hw, rfl⟩ | ⟨q, rfl⟩
  · exact lift_rewrite_eq_one f _ q w (by
      simpa only [FreeGroup.lift_mk, ← PresentedGroup.mk_mk] using
        (PresentedGroup.one_of_mem ⟨w, hw, rfl⟩ : ev (FreeGroup.mk w) = 1))
  · rw [lift_rewrite, trace_actionPerm]
    simp only [FreeGroup.lift_mk, ← PresentedGroup.mk_mk, hr, hb]
    simp

/-- The canonical map from the rewritten presentation to the actual stabilizer. An edge
`(q,a)` denotes `r_q a r_{σ(a)(q)}⁻¹`. -/
def stabilizerHom : K →* MulAction.stabilizer G b :=
  PresentedGroup.toGroup (rewritten_relators_sound W b r hr hb)

@[simp]
theorem stabilizerHom_of (e : Q × α) :
    stabilizerHom W b r hr hb (PresentedGroup.of e) =
      stabilizerGenerator f b (fun q => ev (FreeGroup.mk (r q))) hr e :=
  PresentedGroup.toGroup.of _

/-- Rewriting a word fixing the base point gives its preimage in the stabilizer presentation. -/
theorem stabilizerHom_rewrite (w : PresentationWord α)
    (hw : ev (FreeGroup.mk w) ∈ MulAction.stabilizer G b) :
    stabilizerHom W b r hr hb (PresentedGroup.mk R (FreeGroup.mk (rewrite σ b w))) =
      ⟨ev (FreeGroup.mk w), hw⟩ := by
  apply Subtype.ext
  have hh : (stabilizerHom W b r hr hb).comp (PresentedGroup.mk R) =
      FreeGroup.lift (stabilizerGenerator f b (fun q => ev (FreeGroup.mk (r q))) hr) := by
    apply FreeGroup.ext_hom
    intro e
    simpa only [MonoidHom.comp_apply, FreeGroup.lift_apply_of, PresentedGroup.of] using
      stabilizerHom_of W b r hr hb e
  rw [← MonoidHom.comp_apply, hh]
  have hw' : FreeGroup.lift f (FreeGroup.mk w) ∈ MulAction.stabilizer G b := by
    simpa only [FreeGroup.lift_mk, ← PresentedGroup.mk_mk] using hw
  rw [coe_lift_stabilizerGenerator_rewrite f b _ hr hb w hw']
  simp only [FreeGroup.lift_mk, ← PresentedGroup.mk_mk]

/-- The canonical stabilizer map is onto; signed rewriting supplies a preimage for every
word fixing the base point. -/
theorem stabilizerHom_surjective : Function.Surjective (stabilizerHom W b r hr hb) := by
  intro g
  obtain ⟨v, hv⟩ := PresentedGroup.mk_surjective _ (g : G)
  obtain ⟨w, rfl⟩ := Quot.mk_surjective v
  have hw : ev (FreeGroup.mk w) ∈ MulAction.stabilizer G b := hv ▸ g.property
  refine ⟨PresentedGroup.mk R (FreeGroup.mk (rewrite σ b w)), ?_⟩
  rw [stabilizerHom_rewrite W b r hr hb w hw]
  exact Subtype.ext hv

/- The auxiliary permutation action proves injectivity, rather than just soundness and
surjectivity of the presentation map. -/
private def sourcePerm : G →* Equiv.Perm (Q × K) :=
  @PresentedGroup.toGroup α (Equiv.Perm (Q × K)) _
    (fun a => (pathPerm σ PresentedGroup.of a)⁻¹) (FreeGroup.mk '' W) (by
    rintro _ ⟨w, hw, rfl⟩
    apply inv_injective
    apply Equiv.ext
    rintro ⟨q, h⟩
    rw [lift_pathPerm, trace_actionPerm]
    have hw' : ev (FreeGroup.mk w) = 1 := PresentedGroup.one_of_mem ⟨w, hw, rfl⟩
    simp only [FreeGroup.lift_mk, ← PresentedGroup.mk_mk, hw']
    have he : PresentedGroup.mk R (FreeGroup.mk (rewrite σ q w)) = 1 :=
      PresentedGroup.one_of_mem (Or.inl ⟨q, w, hw, rfl⟩)
    simp [he])

private theorem sourcePerm_of (a : α) :
    sourcePerm W b r (PresentedGroup.of a) =
      (pathPerm σ (PresentedGroup.of : Q × α → K) a)⁻¹ :=
  PresentedGroup.toGroup.of _

private theorem sourcePerm_word (q : Q) (h : K) (w : PresentationWord α) :
    (sourcePerm W b r (ev (FreeGroup.mk w)))⁻¹ (q, h) =
      (trace σ q w, h * PresentedGroup.mk R (FreeGroup.mk (rewrite σ q w))) := by
  have hc : (sourcePerm W b r).comp ev =
      FreeGroup.lift (fun a => (pathPerm σ (PresentedGroup.of : Q × α → K) a)⁻¹) := by
    apply FreeGroup.ext_hom
    intro a
    exact sourcePerm_of W b r a
  rw [← MonoidHom.comp_apply, hc, lift_pathPerm]
  simp only [FreeGroup.lift_mk, ← PresentedGroup.mk_mk]

include hr in
private theorem sourcePerm_representative (q : Q) (h : K) :
    (sourcePerm W b r (ev (FreeGroup.mk (r q))))⁻¹ (b, h) = (q, h) := by
  rw [sourcePerm_word, trace_actionPerm]
  have he : PresentedGroup.mk R (FreeGroup.mk (rewrite σ b (r q))) = 1 :=
    PresentedGroup.one_of_mem (Or.inr ⟨q, rfl⟩)
  simp only [FreeGroup.lift_mk, ← PresentedGroup.mk_mk, hr, he, mul_one]

private theorem sourcePerm_edge (e : Q × α) (h : K) :
    (sourcePerm W b r
      (stabilizerHom W b r hr hb (PresentedGroup.of e) : G))⁻¹ (b, h) =
      (b, h * PresentedGroup.of e) := by
  rcases e with ⟨q, a⟩
  simp only [stabilizerHom_of, coe_stabilizerGenerator, generator_apply,
    map_mul, map_inv, mul_inv_rev, inv_inv, Equiv.Perm.mul_apply]
  rw [sourcePerm_representative W b r hr]
  rw [sourcePerm_of, inv_inv, pathPerm_apply]
  apply (Equiv.eq_symm_apply _).mp
  exact (sourcePerm_representative W b r hr (σ a q) _).symm

private theorem sourcePerm_stabilizerHom (x : K) (h : K) :
    (sourcePerm W b r (stabilizerHom W b r hr hb x : G))⁻¹ (b, h) = (b, h * x) := by
  have hx : x ∈ Subgroup.closure (Set.range (PresentedGroup.of : Q × α → K)) := by simp
  induction hx using Subgroup.closure_induction generalizing h with
  | mem x hx => obtain ⟨e, rfl⟩ := hx; exact sourcePerm_edge W b r hr hb e h
  | one => simp
  | mul x y _ _ ihx ihy =>
    simp only [map_mul, Subgroup.coe_mul, mul_inv_rev, Equiv.Perm.mul_apply]
    rw [ihx, ihy, mul_assoc]
  | inv x _ ih =>
    simp only [map_inv, Subgroup.coe_inv, inv_inv]
    apply (Equiv.eq_symm_apply _).mp
    simpa using (ih (h * x⁻¹)).symm

/-- Rewritten relators are complete: the canonical map to the stabilizer has trivial kernel.
This is stronger than checking the relations in a permutation image. -/
theorem stabilizerHom_injective : Function.Injective (stabilizerHom W b r hr hb) := by
  intro x y hxy
  have hx := sourcePerm_stabilizerHom W b r hr hb x 1
  have hy := sourcePerm_stabilizerHom W b r hr hb y 1
  rw [hxy] at hx
  simpa using congrArg Prod.snd (hx.symm.trans hy)

/-- **Reidemeister--Schreier presentation theorem.** Rewriting the defining relations at
every state and killing representative-word rewrites presents the actual point stabilizer.
All generators, including redundant edges, retain their specified word dictionary. -/
noncomputable def stabilizerEquiv : K ≃* MulAction.stabilizer G b :=
  MulEquiv.ofBijective (stabilizerHom W b r hr hb)
    ⟨stabilizerHom_injective W b r hr hb, stabilizerHom_surjective W b r hr hb⟩

@[simp]
theorem stabilizerEquiv_of (e : Q × α) :
    stabilizerEquiv W b r hr hb (PresentedGroup.of e) =
      stabilizerGenerator f b (fun q => ev (FreeGroup.mk (r q))) hr e :=
  stabilizerHom_of W b r hr hb e

/-- The inverse word dictionary of the Schreier presentation equivalence. -/
@[simp]
theorem stabilizerEquiv_symm_word (w : PresentationWord α)
    (hw : ev (FreeGroup.mk w) ∈ MulAction.stabilizer G b) :
    (stabilizerEquiv W b r hr hb).symm ⟨ev (FreeGroup.mk w), hw⟩ =
      PresentedGroup.mk R (FreeGroup.mk (rewrite σ b w)) := by
  apply (stabilizerEquiv W b r hr hb).injective
  exact ((stabilizerEquiv W b r hr hb).apply_symm_apply _).trans
    (stabilizerHom_rewrite W b r hr hb w hw).symm

end TauCeti.Schreier
