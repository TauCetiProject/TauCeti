/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.Basic
public import TauCeti.Algebra.Module.ZLattice.Family.Fiber
public import TauCeti.Algebra.Module.ZLattice.Family.Translation
public import Mathlib.Topology.LocalAtTarget

/-!
# Base change of period quotients

Pulling a period family `P` back along `f : Z → Y` gives the period family `P ∘ f`.
The map `[z, v] ↦ [f z, v]` on the standard orbit quotients is functorial, commutes with
fibrewise translation and fibre inclusions, and together with its projection to `Z`
identifies the quotient for `P ∘ f` with the literal pullback
`{r : Z × (Y × E)/Λ | p r.2 = f r.1}` (`TauCeti.torusFamilyBaseChangeEquiv`).

For continuous `f` and continuous periods this identification is a homeomorphism for the
inherited product and subtype topologies (`TauCeti.torusFamilyBaseChangeHomeomorph`), and
an open map or open embedding of bases induces an open map or open embedding of period
quotients. No choice of basis, injectivity, discreteness, or fullness is needed. In
particular, the construction applies to varying full period lattices without replacing them
by a constant family. This is a topological comparison; it makes no assertion of
holomorphic local triviality.

## Main definitions

* `TauCeti.torusFamilyBaseChangeMap`: the map `[z, v] ↦ [f z, v]` from `(Z × E)/Λ` to `(Y × E)/Λ`.
* `TauCeti.torusFamilyBaseChangeEquiv`: the algebraic identification of `(Z × E)/Λ` with the
  fibre product `Z ×_Y (Y × E)/Λ`.
* `TauCeti.torusFamilyBaseChangeHomeomorph`: the homeomorphism onto `Z ×_Y (Y × E)/Λ` for
  continuous periods and continuous `f`.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 8 (families of
  complex tori given by period matrices).
-/

public section

open Set Function Topology

namespace TauCeti

variable {Y Z W Λ E : Type*} [AddCommGroup Λ] [AddCommGroup E]
  (P : Y → Λ →ₗ[ℤ] E) (f : Z → Y)

/-- The map from the pulled-back period quotient to the original quotient,
sending `[z, v]` to `[f z, v]`. -/
def torusFamilyBaseChangeMap :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    AddAction.orbitRel.Quotient Λ (Z × E) → AddAction.orbitRel.Quotient Λ (Y × E) :=
  letI := periodAddAction P
  letI := periodAddAction (P ∘ f)
  Quotient.map (Prod.map f id) fun a b h ↦ by
    obtain ⟨h₁, l, h₂⟩ := (mem_orbit_periodAddAction_iff (P ∘ f)).1 h
    exact (mem_orbit_periodAddAction_iff P).2 ⟨congrArg f h₁, l, h₂⟩

/-- Base change acts on representatives by applying `f` to the parameter. -/
@[simp] theorem torusFamilyBaseChangeMap_mk (z : Z) (v : E) :
    torusFamilyBaseChangeMap P f (Quotient.mk _ (z, v)) = Quotient.mk _ (f z, v) := (rfl)

/-- The base-change map lies over `f`. -/
@[simp] theorem torusFamilyProjection_baseChangeMap
    (x : letI := periodAddAction (P ∘ f); AddAction.orbitRel.Quotient Λ (Z × E)) :
    torusFamilyProjection P (torusFamilyBaseChangeMap P f x) =
      f (torusFamilyProjection (P ∘ f) x) := by
  induction x using Quotient.inductionOn with | h a =>
    rcases a with ⟨z, v⟩
    simp

/-- Pullback along the identity induces the identity on period quotients. -/
@[simp] theorem torusFamilyBaseChangeMap_id
    (x : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) :
    torusFamilyBaseChangeMap P id x = x := by
  induction x using Quotient.inductionOn with | h a =>
    rcases a with ⟨y, v⟩
    simp

/-- Base-change maps compose in the same order as the maps of parameter spaces. -/
@[simp] theorem torusFamilyBaseChangeMap_comp (g : W → Z)
    (x : letI := periodAddAction (P ∘ (f ∘ g));
      AddAction.orbitRel.Quotient Λ (W × E)) :
    torusFamilyBaseChangeMap P f (torusFamilyBaseChangeMap (P ∘ f) g x) =
      torusFamilyBaseChangeMap P (f ∘ g) x := by
  induction x using Quotient.inductionOn with | h a =>
    rcases a with ⟨w, v⟩
    simp

/-- Base change commutes with fibrewise translation by vectors of `E`. -/
@[simp] theorem torusFamilyBaseChangeMap_vadd (v : E)
    (x : letI := periodAddAction (P ∘ f); AddAction.orbitRel.Quotient Λ (Z × E)) :
    letI := torusFamilyTranslationAddAction P
    letI := torusFamilyTranslationAddAction (P ∘ f)
    torusFamilyBaseChangeMap P f (v +ᵥ x) = v +ᵥ torusFamilyBaseChangeMap P f x := by
  induction x using Quotient.inductionOn with | h a =>
    rcases a with ⟨z, w⟩
    simp

/-- Base change commutes with the canonical inclusion of each torus fibre. -/
@[simp] theorem torusFamilyBaseChangeMap_fiberMap (z : Z)
    (w : AddAction.orbitRel.Quotient (LinearMap.range ((P ∘ f) z)) E) :
    torusFamilyBaseChangeMap P f (torusFamilyFiberMap (P ∘ f) z w) =
      torusFamilyFiberMap P (f z) w := by
  induction w using Quotient.ind with | _ v =>
    rw [torusFamilyFiberMap_mk, torusFamilyBaseChangeMap_mk]
    exact (torusFamilyFiberMap_mk P (f z) v).symm

/-- The image of the base-change map is the preimage of `range f` under the family projection. -/
theorem range_torusFamilyBaseChangeMap :
    range (torusFamilyBaseChangeMap P f) = torusFamilyProjection P ⁻¹' range f := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨torusFamilyProjection (P ∘ f) w, (torusFamilyProjection_baseChangeMap P f w).symm⟩
  · induction x using Quotient.inductionOn with | h a =>
      rintro ⟨z, hz⟩
      have ha : f z = a.1 := by simpa using hz
      exact ⟨Quotient.mk _ (z, a.2), congrArg (Quotient.mk _) (Prod.ext ha rfl)⟩

/-- Lift a point of `(Y × E)/Λ` lying over `f z` to the fibre of `(Z × E)/Λ` over `z`. -/
private def torusFamilyBaseChangeInv (z : Z) :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    ∀ x : AddAction.orbitRel.Quotient Λ (Y × E),
      torusFamilyProjection P x = f z → AddAction.orbitRel.Quotient Λ (Z × E) :=
  letI := periodAddAction P
  letI := periodAddAction (P ∘ f)
  fun x ↦ Quotient.hrecOn x (fun a _ ↦ Quotient.mk _ (z, a.2)) fun a b h ↦
    Function.hfunext (congrArg (torusFamilyProjection P · = f z) (Quotient.sound h))
      fun ha _ _ ↦ heq_of_eq <| by
        obtain ⟨h₁, l, hl⟩ := (mem_orbit_periodAddAction_iff P).1 h
        have ha' : a.1 = f z := by simpa using ha
        have hb : b.1 = f z := h₁.symm.trans ha'
        exact Quotient.sound
          ((mem_orbit_periodAddAction_iff (P ∘ f)).2 ⟨rfl, l, by simpa [hb] using hl⟩)

private theorem torusFamilyBaseChangeInv_eq_mk (z : Z)
    {x : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)}
    (hx : torusFamilyProjection P x = f z) (a : Y × E) (ha : x = Quotient.mk _ a) :
    torusFamilyBaseChangeInv P f z x hx = Quotient.mk _ (z, a.2) := by
  subst ha
  rfl

/-- **Algebraic pullback of a period quotient.** Together with its projection to `Z`, the
base-change map identifies `(Z × E)/Λ` with the fibre product
`{r : Z × (Y × E)/Λ | torusFamilyProjection P r.2 = f r.1}`, sending `[z, v]` to `(z, [f z, v])`.
No topology or lattice hypotheses are required. -/
def torusFamilyBaseChangeEquiv :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    AddAction.orbitRel.Quotient Λ (Z × E) ≃
      {r : Z × AddAction.orbitRel.Quotient Λ (Y × E) |
        torusFamilyProjection P r.2 = f r.1} :=
  letI := periodAddAction P
  letI := periodAddAction (P ∘ f)
  { toFun := fun x ↦ ⟨(torusFamilyProjection (P ∘ f) x, torusFamilyBaseChangeMap P f x),
      torusFamilyProjection_baseChangeMap P f x⟩
    invFun := fun r ↦ torusFamilyBaseChangeInv P f r.1.1 r.1.2 r.2
    left_inv := fun x ↦ by
      induction x using Quotient.ind with | _ a =>
        rcases a with ⟨z, v⟩
        dsimp only
        rw [torusFamilyBaseChangeInv_eq_mk P f _ _ (f z, v) (torusFamilyBaseChangeMap_mk P f z v),
          torusFamilyProjection_mk]
    right_inv := fun ⟨⟨z, x⟩, hx⟩ ↦ by
      induction x using Quotient.inductionOn with | h a =>
        have ha : a.1 = f z := by simpa using hx
        exact Subtype.ext (Prod.ext (torusFamilyProjection_mk (P ∘ f) (z, a.2))
          (congrArg (Quotient.mk _) (Prod.ext ha.symm rfl))) }

/-- The algebraic pullback equivalence has first coordinate the family projection and second
coordinate the base-change map. -/
@[simp] theorem coe_torusFamilyBaseChangeEquiv
    (x : letI := periodAddAction (P ∘ f); AddAction.orbitRel.Quotient Λ (Z × E)) :
    (torusFamilyBaseChangeEquiv P f x).1 =
      (torusFamilyProjection (P ∘ f) x, torusFamilyBaseChangeMap P f x) := (rfl)

/-- On representatives, the algebraic pullback equivalence sends `[z, v]` to `(z, [f z, v])`. -/
@[simp] theorem torusFamilyBaseChangeEquiv_mk (z : Z) (v : E) :
    torusFamilyBaseChangeEquiv P f (Quotient.mk _ (z, v)) =
      ⟨(z, Quotient.mk _ (f z, v)), torusFamilyProjection_mk P (f z, v)⟩ :=
  Subtype.ext (Prod.ext (torusFamilyProjection_mk (P ∘ f) (z, v)) rfl)

/-- The inverse algebraic pullback equivalence sends `(z, [f z, v])` to `[z, v]`. -/
@[simp] theorem torusFamilyBaseChangeEquiv_symm_mk (z : Z) (v : E) :
    (torusFamilyBaseChangeEquiv P f).symm
      ⟨(z, Quotient.mk _ (f z, v)), torusFamilyProjection_mk P (f z, v)⟩ =
      Quotient.mk _ (z, v) := (rfl)

/-- The inverse pullback equivalence projects to the given point of `Z`. -/
@[simp] theorem torusFamilyProjection_baseChangeEquiv_symm {z : Z}
    {x : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)}
    (hx : torusFamilyProjection P x = f z) :
    torusFamilyProjection (P ∘ f) ((torusFamilyBaseChangeEquiv P f).symm ⟨(z, x), hx⟩) = z :=
  congrArg (fun r ↦ r.1.1) ((torusFamilyBaseChangeEquiv P f).apply_symm_apply ⟨(z, x), hx⟩)

/-- Composing the inverse pullback equivalence with `torusFamilyBaseChangeMap` recovers the
given point of `(Y × E)/Λ`. -/
@[simp] theorem torusFamilyBaseChangeMap_baseChangeEquiv_symm {z : Z}
    {x : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)}
    (hx : torusFamilyProjection P x = f z) :
    torusFamilyBaseChangeMap P f ((torusFamilyBaseChangeEquiv P f).symm ⟨(z, x), hx⟩) = x :=
  congrArg (fun r ↦ r.1.2) ((torusFamilyBaseChangeEquiv P f).apply_symm_apply ⟨(z, x), hx⟩)

/-- Two points of a pulled-back period quotient are equal as soon as they have the same base
point in `Z` and the same image in `(Y × E)/Λ`. -/
theorem torusFamilyBaseChange_ext
    {x y : letI := periodAddAction (P ∘ f); AddAction.orbitRel.Quotient Λ (Z × E)}
    (hproj : torusFamilyProjection (P ∘ f) x = torusFamilyProjection (P ∘ f) y)
    (hmap : torusFamilyBaseChangeMap P f x = torusFamilyBaseChangeMap P f y) :
    x = y :=
  (torusFamilyBaseChangeEquiv P f).injective (Subtype.ext (Prod.ext hproj hmap))

/-- A point of `(Z × E)/Λ` equals the pullback of `(z, x)` if and only if it lies over `z` and
maps to `x` in `(Y × E)/Λ`. -/
theorem eq_torusFamilyBaseChangeEquiv_symm_iff
    {y : letI := periodAddAction (P ∘ f); AddAction.orbitRel.Quotient Λ (Z × E)} {z : Z}
    {x : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)}
    (hx : torusFamilyProjection P x = f z) :
    y = (torusFamilyBaseChangeEquiv P f).symm ⟨(z, x), hx⟩ ↔
      torusFamilyProjection (P ∘ f) y = z ∧ torusFamilyBaseChangeMap P f y = x := by
  rw [Equiv.eq_symm_apply, Subtype.ext_iff, Prod.ext_iff]
  rfl

/-- On a fibre inclusion, the inverse pullback equivalence sends `(z, [f z, v])` to `[z, v]`. -/
@[simp] theorem torusFamilyBaseChangeEquiv_symm_fiberMap (z : Z)
    (w : AddAction.orbitRel.Quotient (LinearMap.range ((P ∘ f) z)) E) :
    (torusFamilyBaseChangeEquiv P f).symm
      ⟨(z, torusFamilyFiberMap P (f z) w), torusFamilyProjection_fiberMap P (f z) w⟩ =
      torusFamilyFiberMap (P ∘ f) z w :=
  ((eq_torusFamilyBaseChangeEquiv_symm_iff P f _).2
    ⟨torusFamilyProjection_fiberMap (P ∘ f) z w,
      torusFamilyBaseChangeMap_fiberMap P f z w⟩).symm

/-- An injective map of bases induces an injective map of period quotients. -/
theorem torusFamilyBaseChangeMap_injective (hf : Injective f) :
    Injective (torusFamilyBaseChangeMap P f) := fun x y h ↦
  torusFamilyBaseChange_ext P f (hf <| by
    rw [← torusFamilyProjection_baseChangeMap P f,
      ← torusFamilyProjection_baseChangeMap P f, h]) h

variable [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace E]

/-- A continuous map of parameter spaces induces a continuous map of period quotients. -/
theorem continuous_torusFamilyBaseChangeMap (hf : Continuous f) :
    Continuous (torusFamilyBaseChangeMap P f) :=
  (hf.prodMap continuous_id).quotient_map' _

variable [ContinuousAdd E]

/-- An open map of parameter spaces induces an open map of period quotients when the periods
depend continuously on the parameter. -/
theorem isOpenMap_torusFamilyBaseChangeMap (hcont : ∀ l, Continuous fun y ↦ P y l)
    (hf : IsOpenMap f) : IsOpenMap (torusFamilyBaseChangeMap P f) := by
  let _ := periodAddAction P
  let _ := periodAddAction (P ∘ f)
  have := continuousConstVAdd_periodAddAction P hcont
  have hopen : IsOpenMap (torusFamilyBaseChangeMap P f ∘ (Quotient.mk _ : Z × E → _)) := by
    have hcomm : torusFamilyBaseChangeMap P f ∘ (Quotient.mk _ : Z × E → _) =
        Quotient.mk _ ∘ Prod.map f id :=
      funext fun a ↦ torusFamilyBaseChangeMap_mk P f a.1 a.2
    rw [hcomm]
    exact AddAction.isOpenQuotientMap_quotientMk.isOpenMap.comp (hf.prodMap IsOpenMap.id)
  exact IsOpenMap.of_comp continuous_quot_mk Quotient.mk_surjective hopen

/-- An open embedding of parameter spaces induces an open embedding of period quotients when
the periods depend continuously on the parameter. -/
theorem isOpenEmbedding_torusFamilyBaseChangeMap (hcont : ∀ l, Continuous fun y ↦ P y l)
    (hf : IsOpenEmbedding f) : IsOpenEmbedding (torusFamilyBaseChangeMap P f) :=
  .of_continuous_injective_isOpenMap (continuous_torusFamilyBaseChangeMap P f hf.continuous)
    (torusFamilyBaseChangeMap_injective P f hf.injective)
    (isOpenMap_torusFamilyBaseChangeMap P f hcont hf.isOpenMap)

/-- The period quotient commutes with continuous base change. The target has the subspace
topology of the product, and the map is `[z, v] ↦ (z, [f z, v])`. -/
noncomputable def torusFamilyBaseChangeHomeomorph
    (hcont : ∀ l, Continuous fun y ↦ P y l) (hf : Continuous f) :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    AddAction.orbitRel.Quotient Λ (Z × E) ≃ₜ
      {r : Z × AddAction.orbitRel.Quotient Λ (Y × E) |
        torusFamilyProjection P r.2 = f r.1} := by
  letI := periodAddAction P
  letI := periodAddAction (P ∘ f)
  have hFc : Continuous (torusFamilyBaseChangeEquiv P f) :=
    ((continuous_torusFamilyProjection (P ∘ f)).prodMk
      (continuous_torusFamilyBaseChangeMap P f hf)).subtype_mk _
  -- Restrict `id × q` to the preimage of the pullback. Its domain is the graph
  -- `y = f z`, canonically homeomorphic to `Z × E`.
  let q : Y × E → AddAction.orbitRel.Quotient Λ (Y × E) := Quotient.mk _
  let S : Set (Z × AddAction.orbitRel.Quotient Λ (Y × E)) :=
    {r | torusFamilyProjection P r.2 = f r.1}
  let e : Z × E ≃ₜ (Prod.map id q ⁻¹' S) :=
    { toFun := fun a ↦ ⟨(a.1, (f a.1, a.2)), torusFamilyProjection_mk P (f a.1, a.2)⟩
      invFun := fun a ↦ (a.1.1, a.1.2.2)
      left_inv := fun _ ↦ rfl
      right_inv := fun a ↦ Subtype.ext <| Prod.ext rfl (Prod.ext
        (by simpa [S, q] using a.2.symm) rfl)
      continuous_toFun :=
        (continuous_fst.prodMk ((hf.comp continuous_fst).prodMk continuous_snd)).subtype_mk _
      continuous_invFun :=
        (continuous_fst.comp continuous_subtype_val).prodMk
          (continuous_snd.comp (continuous_snd.comp continuous_subtype_val)) }
  letI := continuousConstVAdd_periodAddAction P hcont
  have hopen : IsOpenMap (torusFamilyBaseChangeEquiv P f ∘ (Quotient.mk _ : Z × E → _)) := by
    have heq : torusFamilyBaseChangeEquiv P f ∘ Quotient.mk _ =
        S.restrictPreimage (Prod.map id q) ∘ e := by
      funext a
      apply Subtype.ext
      exact Prod.ext (torusFamilyProjection_mk (P ∘ f) a) rfl
    rw [heq]
    exact ((IsOpenMap.id.prodMap
      (AddAction.isOpenQuotientMap_quotientMk.isOpenMap)).restrictPreimage S).comp e.isOpenMap
  exact (torusFamilyBaseChangeEquiv P f).toHomeomorphOfContinuousOpen hFc
    (IsOpenMap.of_comp continuous_quot_mk Quotient.mk_surjective hopen)

variable (hcont : ∀ l, Continuous fun y ↦ P y l) (hf : Continuous f)

/-- The underlying equivalence of the pullback homeomorphism is the algebraic pullback
equivalence. -/
@[simp] theorem torusFamilyBaseChangeHomeomorph_toEquiv :
    (torusFamilyBaseChangeHomeomorph P f hcont hf).toEquiv = torusFamilyBaseChangeEquiv P f :=
  Equiv.ext fun _ ↦ rfl

/-- The inverse of the pullback homeomorphism agrees with the inverse of the algebraic
pullback equivalence. -/
@[simp] theorem coe_torusFamilyBaseChangeHomeomorph_symm :
    ⇑(torusFamilyBaseChangeHomeomorph P f hcont hf).symm =
      ⇑(torusFamilyBaseChangeEquiv P f).symm :=
  congrArg (fun e : _ ≃ _ ↦ ⇑e.symm) (torusFamilyBaseChangeHomeomorph_toEquiv P f hcont hf)

/-- The pullback homeomorphism has first coordinate the family projection and second
coordinate the base-change map. -/
@[simp] theorem coe_torusFamilyBaseChangeHomeomorph
    (x : letI := periodAddAction (P ∘ f); AddAction.orbitRel.Quotient Λ (Z × E)) :
    (torusFamilyBaseChangeHomeomorph P f hcont hf x).1 =
      (torusFamilyProjection (P ∘ f) x, torusFamilyBaseChangeMap P f x) := (rfl)

/-- On representatives, the pullback homeomorphism sends `[z, v]` to `(z, [f z, v])`. -/
@[simp] theorem torusFamilyBaseChangeHomeomorph_mk (z : Z) (v : E) :
    torusFamilyBaseChangeHomeomorph P f hcont hf (Quotient.mk _ (z, v)) =
      ⟨(z, Quotient.mk _ (f z, v)), torusFamilyProjection_mk P (f z, v)⟩ :=
  torusFamilyBaseChangeEquiv_mk P f z v

/-- The inverse comparison sends `(z, [f z, v])` to `[z, v]`. -/
@[simp] theorem torusFamilyBaseChangeHomeomorph_symm_mk (z : Z) (v : E) :
    (torusFamilyBaseChangeHomeomorph P f hcont hf).symm
      ⟨(z, Quotient.mk _ (f z, v)), torusFamilyProjection_mk P (f z, v)⟩ =
      Quotient.mk _ (z, v) := by
  rw [← torusFamilyBaseChangeHomeomorph_mk P f hcont hf]
  exact Homeomorph.symm_apply_apply _ _

end TauCeti
