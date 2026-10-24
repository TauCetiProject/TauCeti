/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.Basic
public import Mathlib.Topology.LocalAtTarget

/-!
# Base change of period quotients

Pulling a period family `P` back along `f : Z → Y` gives the period family `P ∘ f`.
The map `[z, v] ↦ [f z, v]` on the standard orbit quotients is functorial. Together with
its projection to `Z`, it identifies the quotient for `P ∘ f` with the literal pullback
`{r : Z × (Y × E)/Λ | p r.2 = f r.1}`.

For continuous `f` and continuous periods this identification is a homeomorphism for the
inherited product and subtype topologies. No choice of basis, injectivity, discreteness,
or fullness is needed. In particular, the construction applies to varying full period
lattices without replacing them by a constant family. This is a topological comparison;
it makes no assertion of holomorphic local triviality.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Chapter 8 (families of complex tori given by period matrices).
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

variable [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace E]

/-- A continuous map of parameter spaces induces a continuous map of period quotients. -/
theorem continuous_torusFamilyBaseChangeMap (hf : Continuous f) :
    Continuous (torusFamilyBaseChangeMap P f) :=
  (hf.prodMap continuous_id).quotient_map' _

variable [ContinuousAdd E]

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
  let F : AddAction.orbitRel.Quotient Λ (Z × E) →
      {r : Z × AddAction.orbitRel.Quotient Λ (Y × E) |
        torusFamilyProjection P r.2 = f r.1} :=
    fun x ↦ ⟨(torusFamilyProjection (P ∘ f) x, torusFamilyBaseChangeMap P f x),
      torusFamilyProjection_baseChangeMap P f x⟩
  have hF : Bijective F := by
    constructor
    · intro a b h
      induction a using Quotient.inductionOn with | h a =>
        induction b using Quotient.inductionOn with | h b =>
          have h₁ : a.1 = b.1 := by
            simpa [F] using congrArg (fun r ↦ r.1.1) h
          have h₂ := Quotient.exact (congrArg (fun r ↦ r.1.2) h)
          obtain ⟨_, l, hl⟩ := (mem_orbit_periodAddAction_iff P).1 h₂
          exact Quotient.sound <| (mem_orbit_periodAddAction_iff (P ∘ f)).2
            ⟨h₁, l, hl⟩
    · rintro ⟨⟨z, x⟩, hx⟩
      induction x using Quotient.inductionOn with | h a =>
        have ha : a.1 = f z := by simpa using hx
        refine ⟨Quotient.mk _ (z, a.2), ?_⟩
        apply Subtype.ext
        exact Prod.ext (torusFamilyProjection_mk (P ∘ f) (z, a.2))
          (congrArg (Quotient.mk _) (Prod.ext ha.symm rfl))
  have hFc : Continuous F :=
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
  have hopen : IsOpenMap (F ∘ (Quotient.mk _ : Z × E → _)) := by
    have heq : F ∘ Quotient.mk _ = S.restrictPreimage (Prod.map id q) ∘ e := by
      funext a
      apply Subtype.ext
      exact Prod.ext (torusFamilyProjection_mk (P ∘ f) a) rfl
    rw [heq]
    exact ((IsOpenMap.id.prodMap
      (AddAction.isOpenQuotientMap_quotientMk.isOpenMap)).restrictPreimage S).comp e.isOpenMap
  exact (Equiv.ofBijective F hF).toHomeomorphOfContinuousOpen hFc
    (IsOpenMap.of_comp continuous_quot_mk Quotient.mk_surjective hopen)

variable (hcont : ∀ l, Continuous fun y ↦ P y l) (hf : Continuous f)

/-- The pullback homeomorphism has first coordinate the family projection and second
coordinate the base-change map. -/
@[simp] theorem coe_torusFamilyBaseChangeHomeomorph
    (x : letI := periodAddAction (P ∘ f); AddAction.orbitRel.Quotient Λ (Z × E)) :
    (torusFamilyBaseChangeHomeomorph P f hcont hf x).1 =
      (torusFamilyProjection (P ∘ f) x, torusFamilyBaseChangeMap P f x) := (rfl)

/-- On representatives, the pullback homeomorphism sends `[z, v]` to `(z, [f z, v])`. -/
@[simp] theorem torusFamilyBaseChangeHomeomorph_mk (z : Z) (v : E) :
    torusFamilyBaseChangeHomeomorph P f hcont hf (Quotient.mk _ (z, v)) =
      ⟨(z, Quotient.mk _ (f z, v)), torusFamilyProjection_mk P (f z, v)⟩ := by
  apply Subtype.ext
  simp

/-- The inverse comparison sends `(z, [f z, v])` to `[z, v]`. -/
@[simp] theorem torusFamilyBaseChangeHomeomorph_symm_mk (z : Z) (v : E) :
    (torusFamilyBaseChangeHomeomorph P f hcont hf).symm
      ⟨(z, Quotient.mk _ (f z, v)), torusFamilyProjection_mk P (f z, v)⟩ =
      Quotient.mk _ (z, v) := by
  rw [← torusFamilyBaseChangeHomeomorph_mk P f hcont hf]
  exact Homeomorph.symm_apply_apply _ _

end TauCeti
