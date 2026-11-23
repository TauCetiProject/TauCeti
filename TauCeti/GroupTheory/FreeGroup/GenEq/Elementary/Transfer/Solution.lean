/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.GenEq.Elementary.Transfer.Basic
public import TauCeti.GroupTheory.FreeGroup.GenEq.Transformation
import Mathlib.Data.Fin.VecNotation

/-!
# Solutions and coordinate groups under transferring a base

When `Ω` is a formally consistent generalised equation and `ψ` is transferable along a carrier `μ`
(`TauCeti.GenEq.IsTransferable`), the transferred equation `Ω′ = Ω.transferBase hΩ h` of
elementary transformation ET2 keeps `μ` and `Δ(μ)` distinct from `ψ` and `Δ(ψ)`. Hence the basic
equation of `μ` and all boundary equations through `μ` belong to both `Ω` and `Ω′`, identifying
each segment between `μ`-tied boundaries with the corresponding segment of `Δ(μ)` (or its inverse).
Consequently:

* `Ω*` and `Ω′*` have the same points in every `F(A)`-group
  (`TauCeti.GenEq.V_toSystem_transferBase`), so the identity on the items induces an
  `F(A)`-isomorphism `F_{R(Ω)} → F_{R(Ω′)}` (`TauCeti.GenEq.transferBaseHom`,
  `TauCeti.GenEq.transferBaseHom_bijective`);
* `Ω` and `Ω′` have the exact same graphical solutions, with the same words
  (`TauCeti.GenEq.solutionEquivTransferBase`): unlike the removal of a matched pair (ET3), no
  reducedness condition is lost because the covering bases `μ` and `Δ(μ)` remain in both equations;
* if `Ω` has a solution then `Ω′` is formally consistent
  (`TauCeti.GenEq.isFormallyConsistent_transferBase_of_nonempty_solution`); without a solution,
  flipping the sign of `ψ` across an opposite-sign carrier can place `ψ` over `Δ(ψ)` with opposite
  sign and break formal consistency, as shown in the examples at the end of the file;
* keeping `Ω′` when it is formally consistent packages ET2 as a transformation of `Ω` that
  transfers solutions uniquely (`TauCeti.GenEq.transferBaseTransformation`,
  `TauCeti.GenEq.transfersUniquely_transferBaseTransformation`).

## Main definitions

* `TauCeti.GenEq.transferBaseHom`: the `F(A)`-homomorphism `F_{R(Ω)} → F_{R(Ω′)}` of coordinate
  groups induced by the identity on the items.
* `TauCeti.GenEq.solutionEquivTransferBase`: equivalence between the graphical solutions of `Ω`
  and those of `Ω.transferBase hΩ h`.
* `TauCeti.GenEq.transferBaseTransformation`: ET2 as a `TauCeti.GenEq.Transformation`.

## Main results

* `TauCeti.GenEq.V_toSystem_transferBase`: ET2 preserves the points of `Ω*` in every `F(A)`-group.
* `TauCeti.GenEq.transferBaseHom_bijective`: `transferBaseHom` is an isomorphism of coordinate
  groups.
* `TauCeti.GenEq.isFormallyConsistent_transferBase_of_nonempty_solution`: ET2 preserves formal
  consistency whenever `Ω` has a solution.
* `TauCeti.GenEq.toHom_comp_transferBaseHom_eq_iff`: ET2 transfers solutions uniquely along
  `transferBaseHom`.
* `TauCeti.GenEq.transfersUniquely_transferBaseTransformation`: `transferBaseTransformation`
  transfers solutions uniquely.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §5.1, ET2.
* O. Kharlampovich, A. Myasnikov, *Effective JSJ decompositions*, Contemp. Math. 378 (2005),
  §5.1, ET2.
* O. Kharlampovich, A. Myasnikov, D. Serbin, *Actions, length functions, and non-archimedean
  words*, Internat. J. Algebra Comput. 23 (2013), §11.3, ET2.
-/

public section

namespace TauCeti

namespace GenEq

open GroupAlgGeom Monoid.Coprod
open FreeGroup (substituteVars)

variable {A : Type*} {Ω : GenEq A} {μ ψ : Fin Ω.numBases}

section Consistent

variable (hΩ : Ω.IsFormallyConsistent) (h : Ω.IsTransferable μ ψ)

/-! ### Equations and group solutions -/

/-- The segments `h[i, j] ^ ±1` only depend on the items, which `transferBase` keeps. -/
@[simp]
theorem segment_transferBase (i j : ℕ) (s : Bool) :
    (Ω.transferBase hΩ h).segment i j s = Ω.segment i j s := by
  cases s <;> simp only [segment_false, segment_true]

/-- Transferring a variable base keeps the coefficient equations. -/
@[simp]
theorem coeffEquation_transferBase (b : Fin Ω.numItems × (A × Bool)) :
    (Ω.transferBase hΩ h).coeffEquation b = Ω.coeffEquation b :=
  Prod.ext (by simp) (by simp)

/-- The basic equation of any base outside `{ψ, Δ(ψ)}` is unchanged by `transferBase`. -/
theorem basicEquation_transferBase_of_ne {ν : Fin Ω.numBases} (h₁ : ν ≠ ψ) (h₂ : ν ≠ Ω.dual ψ) :
    (Ω.transferBase hΩ h).basicEquation ν = Ω.basicEquation ν := by
  have hd : Ω.dual ν ≠ ψ := mt Ω.dual_involutive.eq_iff.1 h₂
  exact Prod.ext (by simp [h₁]) (by simp [hd])

/-- The boundary equation of any triple outside `{ψ, Δ(ψ)}` is unchanged by `transferBase`. -/
theorem boundaryEquation_transferBase_of_ne
    {c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)}
    (h₁ : c.2.1 ≠ ψ) (h₂ : c.2.1 ≠ Ω.dual ψ) :
    (Ω.transferBase hΩ h).boundaryEquation c = Ω.boundaryEquation c := by
  have hd : Ω.dual c.2.1 ≠ ψ := mt Ω.dual_involutive.eq_iff.1 h₂
  refine Prod.ext (by simp [h₁]) ?_
  by_cases hs : Ω.sign c.2.1 = Ω.sign (Ω.dual c.2.1) <;>
    simp [boundaryEquation_snd_of_sign_eq, boundaryEquation_snd_of_sign_ne, h₁, hd, hs]

/-- Under any group assignment satisfying the basic and boundary equations of the carrier `μ`, the
transferred segment of `ψ` evaluates to the same group element as the original segment of `ψ`. -/
private theorem lift_mk_segment_transferBase_self {H : Type*} [Group H]
    (f : Fin Ω.numItems ⊕ A → H)
    (hb : FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).1) =
      FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).2))
    (hc : ∀ c ∈ Ω.connections, c.2.1 = μ →
      FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).2)) :
    FreeGroup.lift f (FreeGroup.mk ((Ω.transferBase hΩ h).segment
        ((Ω.transferBase hΩ h).left ψ) ((Ω.transferBase hΩ h).right ψ)
        ((Ω.transferBase hΩ h).sign ψ))) =
      FreeGroup.lift f (FreeGroup.mk (Ω.segment (Ω.left ψ) (Ω.right ψ) (Ω.sign ψ))) := by
  rw [segment_transferBase, left_transferBase_self, right_transferBase_self, sign_transferBase_self,
    Ω.lift_mk_segment f _ _ (if Ω.sign μ = Ω.sign (Ω.dual μ) then Ω.sign ψ else !Ω.sign ψ),
    Ω.lift_mk_segment f _ _ (Ω.sign ψ)]
  by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
  · simp only [hs, ite_true]
    rw [hΩ.lift_mk_segment_eq_of_isTiedTo_of_sign_eq hs h.isTiedTo_tiedBoundary_left
      h.isTiedTo_tiedBoundary_right hb (hc _ · rfl) (hc _ · rfl)]
  · simp only [hs, ite_false]
    rw [hΩ.lift_mk_segment_eq_inv_of_isTiedTo_of_sign_ne hs h.isTiedTo_tiedBoundary_left
      h.isTiedTo_tiedBoundary_right hb (hc _ · rfl) (hc _ · rfl)]
    cases Ω.sign ψ <;>
      simp only [Bool.not_false, Bool.not_true, Bool.cond_false, Bool.cond_true, inv_inv]

/-- Under any group assignment satisfying the equations of `μ`, every basic equation of
`Ω.transferBase hΩ h` has the exact same side values in the group as the corresponding basic
equation of `Ω`. -/
private theorem lift_mk_basicEquation_transferBase_iff {H : Type*} [Group H]
    (f : Fin Ω.numItems ⊕ A → H)
    (hb : FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).1) =
      FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).2))
    (hc : ∀ c ∈ Ω.connections, c.2.1 = μ →
      FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).2))
    (ν : Fin Ω.numBases) :
    FreeGroup.lift f (FreeGroup.mk ((Ω.transferBase hΩ h).basicEquation ν).1) =
        FreeGroup.lift f (FreeGroup.mk ((Ω.transferBase hΩ h).basicEquation ν).2) ↔
      FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation ν).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation ν).2) := by
  have hside : ∀ κ : Fin Ω.numBases,
      FreeGroup.lift f (FreeGroup.mk ((Ω.transferBase hΩ h).segment
          ((Ω.transferBase hΩ h).left κ) ((Ω.transferBase hΩ h).right κ)
          ((Ω.transferBase hΩ h).sign κ))) =
        FreeGroup.lift f (FreeGroup.mk (Ω.segment (Ω.left κ) (Ω.right κ) (Ω.sign κ))) := by
    intro κ
    by_cases hκ : κ = ψ
    · exact hκ ▸ lift_mk_segment_transferBase_self hΩ h f hb hc
    · rw [segment_transferBase, left_transferBase_of_ne hΩ h hκ, right_transferBase_of_ne hΩ h hκ,
        sign_transferBase_of_ne hΩ h hκ]
  simp only [basicEquation_fst, basicEquation_snd]
  rw [hside ν, hside (Ω.dual ν)]

/-- Under any group assignment satisfying the equations of `μ`, for `ψ ≠ Δ(ψ)`, the relocated dual
connection `(p, Δψ, tiedBoundary μ r)` has the same right-hand side value in `Ω.transferBase hΩ h`
as `(p, Δψ, r)` in `Ω`. -/
private theorem lift_mk_boundaryEquation_snd_transferConnection_dual {H : Type*} [Group H]
    (hself : ψ ≠ Ω.dual ψ) (f : Fin Ω.numItems ⊕ A → H)
    (hb : FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).1) =
      FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).2))
    (hc : ∀ c ∈ Ω.connections, c.2.1 = μ →
      FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).2))
    {p r : Fin (Ω.numItems + 1)} (hc_mem : (p, Ω.dual ψ, r) ∈ Ω.connections) :
    FreeGroup.lift f (FreeGroup.mk ((Ω.transferBase hΩ h).boundaryEquation
        (p, Ω.dual ψ, Ω.tiedBoundary μ r)).2) =
      FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation (p, Ω.dual ψ, r)).2) := by
  have hd_mem : (r, ψ, p) ∈ Ω.connections := by
    simpa [Ω.dual_involutive ψ] using Ω.dual_mem_connections _ hc_mem
  have hr_tied := h.isTiedTo_tiedBoundary_of_mem_connections hd_mem rfl
  have hsign : (Ω.transferBase hΩ h).sign (Ω.dual ψ) =
        (Ω.transferBase hΩ h).sign (Ω.dual (Ω.dual ψ)) ↔
      (Ω.sign ψ = Ω.sign (Ω.dual ψ) ↔ Ω.sign μ = Ω.sign (Ω.dual μ)) := by
    rw [Ω.dual_involutive ψ, eq_comm, sign_transferBase_eq_sign_dual_iff hΩ h hself]
  by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
  · by_cases hsψ : Ω.sign ψ = Ω.sign (Ω.dual ψ)
    · rw [(Ω.transferBase hΩ h).boundaryEquation_snd_of_sign_eq (hsign.2 (iff_of_true hsψ hs)),
        Ω.boundaryEquation_snd_of_sign_eq (by rw [Ω.dual_involutive ψ, hsψ]),
        Ω.dual_involutive ψ, segment_transferBase, left_transferBase_self, ite_eq_left hs]
      exact (hΩ.lift_mk_segment_eq_of_isTiedTo_of_sign_eq hs h.isTiedTo_tiedBoundary_left hr_tied
        hb (hc _ · rfl) (hc _ · rfl)).symm
    · rw [(Ω.transferBase hΩ h).boundaryEquation_snd_of_sign_ne
          (mt hsign.1 (fun hiff => hsψ (hiff.2 hs))),
        Ω.boundaryEquation_snd_of_sign_ne (by rw [Ω.dual_involutive ψ]; exact Ne.symm hsψ),
        Ω.dual_involutive ψ, segment_transferBase, right_transferBase_self, ite_eq_left hs,
        Ω.lift_mk_segment_false, Ω.lift_mk_segment_false, inv_inj]
      exact (hΩ.lift_mk_segment_eq_of_isTiedTo_of_sign_eq hs hr_tied h.isTiedTo_tiedBoundary_right
        hb (hc _ · rfl) (hc _ · rfl)).symm
  · by_cases hsψ : Ω.sign ψ = Ω.sign (Ω.dual ψ)
    · rw [(Ω.transferBase hΩ h).boundaryEquation_snd_of_sign_ne
          (mt hsign.1 (fun hiff => hs (hiff.1 hsψ))),
        Ω.boundaryEquation_snd_of_sign_eq (by rw [Ω.dual_involutive ψ, hsψ]),
        Ω.dual_involutive ψ, segment_transferBase, right_transferBase_self, ite_eq_right hs,
        Ω.lift_mk_segment_false]
      exact (hΩ.lift_mk_segment_eq_inv_of_isTiedTo_of_sign_ne hs h.isTiedTo_tiedBoundary_left
        hr_tied hb (hc _ · rfl) (hc _ · rfl)).symm
    · rw [(Ω.transferBase hΩ h).boundaryEquation_snd_of_sign_eq (hsign.2 (iff_of_false hsψ hs)),
        Ω.boundaryEquation_snd_of_sign_ne (by rw [Ω.dual_involutive ψ]; exact Ne.symm hsψ),
        Ω.dual_involutive ψ, segment_transferBase, left_transferBase_self, ite_eq_right hs,
        Ω.lift_mk_segment_false,
        hΩ.lift_mk_segment_eq_inv_of_isTiedTo_of_sign_ne hs hr_tied
          h.isTiedTo_tiedBoundary_right hb (hc _ · rfl) (hc _ · rfl),
        inv_inv]

/-- Under any group assignment satisfying the equations of `μ` and the basic equation of `ψ`, every
relocated connection `transferConnection μ ψ c` holds in `Ω.transferBase hΩ h` if and only if `c`
holds in `Ω`. -/
private theorem lift_mk_boundaryEquation_transferConnection_iff {H : Type*} [Group H]
    (f : Fin Ω.numItems ⊕ A → H)
    (hbμ : FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).1) =
      FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).2))
    (hcμ : ∀ c ∈ Ω.connections, c.2.1 = μ →
      FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).2))
    (hbψ : FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation ψ).1) =
      FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation ψ).2))
    {c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)} (hc : c ∈ Ω.connections) :
    FreeGroup.lift f (FreeGroup.mk
        ((Ω.transferBase hΩ h).boundaryEquation (Ω.transferConnection μ ψ c)).1) =
      FreeGroup.lift f (FreeGroup.mk
        ((Ω.transferBase hΩ h).boundaryEquation (Ω.transferConnection μ ψ c)).2) ↔
    FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).1) =
      FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).2) := by
  have hdual : ψ ≠ Ω.dual ψ → ∀ {p r : Fin (Ω.numItems + 1)},
      (p, Ω.dual ψ, r) ∈ Ω.connections →
      (FreeGroup.lift f (FreeGroup.mk ((Ω.transferBase hΩ h).boundaryEquation
          (Ω.transferConnection μ ψ (p, Ω.dual ψ, r))).1) =
        FreeGroup.lift f (FreeGroup.mk ((Ω.transferBase hΩ h).boundaryEquation
          (Ω.transferConnection μ ψ (p, Ω.dual ψ, r))).2) ↔
      FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation (p, Ω.dual ψ, r)).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation (p, Ω.dual ψ, r)).2)) := by
    intro hself p r hmem
    rw [transferConnection_of_eq_dual hself rfl, boundaryEquation_fst,
      segment_transferBase, left_transferBase_of_ne hΩ h hself.symm,
      ← Ω.boundaryEquation_fst (c := (p, Ω.dual ψ, r)),
      lift_mk_boundaryEquation_snd_transferConnection_dual hΩ h hself f hbμ hcμ hmem]
  obtain ⟨p, ν, r⟩ := c
  by_cases h₁ : ν = ψ
  · subst ν
    by_cases hself : ψ = Ω.dual ψ
    · have hpr : p = r := hΩ.eq_of_left_eq _ hc (by rw [← hself])
      subst hpr
      have h1 : ((Ω.transferBase hΩ h).boundaryEquation (Ω.transferConnection μ ψ (p, ψ, p))).1 =
          ((Ω.transferBase hΩ h).boundaryEquation (Ω.transferConnection μ ψ (p, ψ, p))).2 := by
        rw [boundaryEquation_fst,
          (Ω.transferBase hΩ h).boundaryEquation_snd_of_sign_eq
            (by rw [transferConnection_snd_fst, ← hself])]
        simp only [transferConnection_fst, transferConnection_snd_fst, transferConnection_snd_snd,
          ← hself, ite_true]
      have h2 : (Ω.boundaryEquation (p, ψ, p)).1 = (Ω.boundaryEquation (p, ψ, p)).2 := by
        rw [boundaryEquation_fst, Ω.boundaryEquation_snd_of_sign_eq (by rw [← hself]), ← hself]
      exact iff_of_true (by rw [h1]) (by rw [h2])
    · have hc' : Ω.transferConnection μ ψ (p, ψ, r) ∈ (Ω.transferBase hΩ h).connections :=
        (mem_connections_transferBase hΩ h).2 ⟨_, hc, rfl⟩
      obtain ⟨hp₁', hp₂', hr₁', hr₂'⟩ := (Ω.transferBase hΩ h).bounds_of_mem_connections _ hc'
      obtain ⟨hp₁, hp₂, hr₁, hr₂⟩ := Ω.bounds_of_mem_connections _ hc
      have hbψ' := (lift_mk_basicEquation_transferBase_iff hΩ h f hbμ hcμ ψ).2 hbψ
      rw [transferConnection_of_eq hself rfl] at hc' hp₁' hp₂' hr₁' hr₂' ⊢
      rw [← (Ω.transferBase hΩ h).lift_mk_boundaryEquation_dual_iff f hp₁'.le hp₂'.le hr₁'.le
          hr₂'.le hbψ', ← transferConnection_of_eq_dual hself (c := (r, Ω.dual ψ, p)) rfl,
        hdual hself (Ω.dual_mem_connections _ hc),
        Ω.lift_mk_boundaryEquation_dual_iff f hp₁.le hp₂.le hr₁.le hr₂.le hbψ]
  · by_cases h₂ : ν = Ω.dual ψ
    · subst ν
      exact hdual (Ne.symm h₁) hc
    · rw [transferConnection_of_ne h₁ h₂, boundaryEquation_transferBase_of_ne hΩ h h₁ h₂]

/-- **ET2 on group solutions.** Transferring a base `ψ` along a carrier `μ` in a formally
consistent generalised equation preserves the points of `Ω*` in every `F(A)`-group. -/
theorem V_toSystem_transferBase {H : Type*} [Group H] (ι : FreeGroup A →* H) :
    V ι (Ω.transferBase hΩ h).toSystem = V ι Ω.toSystem := by
  ext v
  rw [mem_V_toSystem_iff, mem_V_toSystem_iff, (Ω.transferBase hΩ h).forall_mem_equations,
    Ω.forall_mem_equations]
  set f : Fin Ω.numItems ⊕ A → H := Sum.elim v (ι ∘ FreeGroup.of)
  have hμ₁ : μ ≠ ψ := h.ne_carrier.symm
  have hμ₂ : μ ≠ Ω.dual ψ := h.dual_ne_carrier.symm
  refine ⟨fun ⟨hb', hcoeff', hc'⟩ => ?_, fun ⟨hb, hcoeff, hc⟩ => ?_⟩
  · have hbμ : FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).2) := by
      simpa [basicEquation_transferBase_of_ne hΩ h hμ₁ hμ₂] using hb' μ
    have hcμ : ∀ c ∈ Ω.connections, c.2.1 = μ →
        FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).1) =
          FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).2) := by
      intro c hc_mem hc_eq
      have hc'_mem : c ∈ (Ω.transferBase hΩ h).connections :=
        (mem_connections_transferBase_of_ne hΩ h (hc_eq ▸ hμ₁) (hc_eq ▸ hμ₂)).2 hc_mem
      simpa [boundaryEquation_transferBase_of_ne hΩ h (hc_eq ▸ hμ₁) (hc_eq ▸ hμ₂)] using
        hc' c hc'_mem
    have hb : ∀ ν, FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation ν).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation ν).2) :=
      fun ν => (lift_mk_basicEquation_transferBase_iff hΩ h f hbμ hcμ ν).1 (hb' ν)
    refine ⟨hb, fun b hb_mem => by simpa using hcoeff' b hb_mem, fun c hc_mem => ?_⟩
    exact (lift_mk_boundaryEquation_transferConnection_iff hΩ h f hbμ hcμ (hb ψ) hc_mem).1
      (hc' _ ((mem_connections_transferBase hΩ h).2 ⟨_, hc_mem, rfl⟩))
  · have hcμ : ∀ c ∈ Ω.connections, c.2.1 = μ →
        FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).1) =
          FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).2) :=
      fun c hc_mem _ => hc c hc_mem
    refine ⟨fun ν => (lift_mk_basicEquation_transferBase_iff hΩ h f (hb μ) hcμ ν).2 (hb ν),
      fun b hb_mem => by simpa using hcoeff b hb_mem, fun c' hc'_mem => ?_⟩
    obtain ⟨c, hc_mem, rfl⟩ := (mem_connections_transferBase hΩ h).1 hc'_mem
    exact (lift_mk_boundaryEquation_transferConnection_iff hΩ h f (hb μ) hcμ (hb ψ) hc_mem).2
      (hc c hc_mem)

/-- **ET2 on coordinate groups.** The `F(A)`-homomorphism `F_{R(Ω)} → F_{R(Ω′)}` induced by the
identity on the items, where `Ω′ = Ω.transferBase hΩ h`. -/
def transferBaseHom : GHom (CoordGroup.coeff (.id (FreeGroup A)) Ω.toSystem)
    (CoordGroup.coeff (.id (FreeGroup A)) (Ω.transferBase hΩ h).toSystem) :=
  CoordGroup.homOfVSubset (V_toSystem_transferBase hΩ h _).le

/-- The homomorphism `F_{R(Ω)} → F_{R(Ω′)}` of ET2 is the identity on the words in the items. -/
-- Not `@[simp]`: the reducible `transferBase` in the codomain keeps `simp` from indexing this
-- lemma uninstantiated, so it is used through `rw`.
theorem transferBaseHom_mk (w : GX (FreeGroup A) (Fin Ω.numItems)) :
    transferBaseHom hΩ h (w : Ω.coordGroup) = (w : (Ω.transferBase hΩ h).coordGroup) :=
  CoordGroup.homOfVSubset_mk _ w

/-- **ET2 on coordinate groups.** If `Ω` is formally consistent and `ψ` is transferable along `μ`,
the identity on the items induces an `F(A)`-isomorphism of the coordinate groups of `Ω` and
`Ω.transferBase hΩ h`. -/
theorem transferBaseHom_bijective : Function.Bijective (transferBaseHom hΩ h) :=
  ⟨CoordGroup.homOfVSubset_injective _ (V_toSystem_transferBase hΩ h _).ge,
    CoordGroup.homOfVSubset_surjective _⟩

/-! ### Graphical solutions and the transformation of ET2 -/

namespace Solution

/-- A solution of `Ω` as a solution of `Ω.transferBase hΩ h`, with the same words: the word of the
transferred base `ψ` lies inside `U[α(Δμ), β(Δμ)]`, which is reduced as written. -/
def transferBase (U : Ω.Solution) : (Ω.transferBase hΩ h).Solution :=
  Solution.ofMemV U.word U.isReduced_word U.word_ne_nil
    (((Ω.transferBase hΩ h).forall_mem_equations_isReduced_iff U.isReduced_word).2 fun ν => by
      rw [segment_transferBase]
      by_cases hν : ν = ψ
      · subst ν
        exact U.isReduced_substituteVars_segment_of_le (Ω.dual μ)
          (left_dual_le_left_transferBase hΩ h) (right_transferBase_le_right_dual hΩ h)
      · rw [left_transferBase_of_ne hΩ h hν, right_transferBase_of_ne hΩ h hν]
        exact U.isReduced_substituteVars_segment ν)
    (funext U.point_apply ▸ (V_toSystem_transferBase hΩ h _).ge U.point_mem_V)

/-- Transferring a base keeps the words of a solution. -/
@[simp]
theorem transferBase_word (U : Ω.Solution) : (U.transferBase hΩ h).word = U.word :=
  Solution.ofMemV_word ..

/-- Transferring a base keeps the point of a solution. -/
@[simp]
theorem transferBase_point (U : Ω.Solution) : (U.transferBase hΩ h).point = U.point := by
  ext
  simp

/-- Transferring a base keeps the positions of the boundaries in the words of a solution. -/
@[simp]
theorem transferBase_prefixLength (U : Ω.Solution) :
    (U.transferBase hΩ h).prefixLength = U.prefixLength := by
  ext
  simp [prefixLength_def]

/-- A solution of `Ω.transferBase hΩ h` as a solution of `Ω`, with the same words: `ψ` lies inside
the carrier `μ`, which remains a base of `Ω.transferBase hΩ h`, so `U[α(ψ), β(ψ)]` is reduced as
written. -/
def ofTransferBase (U : (Ω.transferBase hΩ h).Solution) : Ω.Solution :=
  Solution.ofMemV U.word U.isReduced_word U.word_ne_nil
    ((Ω.forall_mem_equations_isReduced_iff U.isReduced_word).2 fun ν => by
      by_cases hν : ν = ψ
      · subst ν
        have hμ' : μ ≠ ψ := h.ne_carrier.symm
        have hseg := U.isReduced_substituteVars_segment_of_le μ
          ((left_transferBase_of_ne hΩ h hμ').symm ▸ h.left_le)
          ((right_transferBase_of_ne hΩ h hμ').symm ▸ h.right_le)
        rwa [segment_transferBase] at hseg
      · have hseg := U.isReduced_substituteVars_segment ν
        rwa [segment_transferBase, left_transferBase_of_ne hΩ h hν,
          right_transferBase_of_ne hΩ h hν] at hseg)
    (funext U.point_apply ▸ (V_toSystem_transferBase hΩ h _).le U.point_mem_V)

/-- Reading a solution of `Ω.transferBase hΩ h` back as a solution of `Ω` keeps its words. -/
@[simp]
theorem ofTransferBase_word (U : (Ω.transferBase hΩ h).Solution) :
    (U.ofTransferBase hΩ h).word = U.word :=
  Solution.ofMemV_word ..

/-- Reading a solution of `Ω.transferBase hΩ h` back as a solution of `Ω` keeps its point. -/
@[simp]
theorem ofTransferBase_point (U : (Ω.transferBase hΩ h).Solution) :
    (U.ofTransferBase hΩ h).point = U.point := by
  ext
  simp

/-- Reading a solution of `Ω.transferBase hΩ h` back as a solution of `Ω` keeps its boundary
positions. -/
@[simp]
theorem ofTransferBase_prefixLength (U : (Ω.transferBase hΩ h).Solution) :
    (U.ofTransferBase hΩ h).prefixLength = U.prefixLength := by
  ext
  simp [prefixLength_def]

/-- Transferring a solution and reading it back recovers the original solution. -/
@[simp]
theorem ofTransferBase_transferBase (U : Ω.Solution) :
    (U.transferBase hΩ h).ofTransferBase hΩ h = U :=
  Solution.ext (by simp)

/-- Reading a solution of `Ω.transferBase hΩ h` back and transferring it recovers the solution. -/
@[simp]
theorem transferBase_ofTransferBase (U : (Ω.transferBase hΩ h).Solution) :
    (U.ofTransferBase hΩ h).transferBase hΩ h = U :=
  Solution.ext (by simp)

/-- Reading a solution of `Ω.transferBase hΩ h` back as a solution of `Ω` composes its homomorphism
with `transferBaseHom`. -/
theorem ofTransferBase_toHom (U : (Ω.transferBase hΩ h).Solution) :
    (U.ofTransferBase hΩ h).toHom = U.toHom.comp (transferBaseHom hΩ h) := by
  ext k
  rw [GHom.coe_comp, Function.comp_apply, transferBaseHom_mk]
  simp

end Solution

/-- **ET2 on solutions.** If `Ω` is formally consistent and `ψ` is transferable along `μ`, the
graphical solutions of `Ω` and of `Ω.transferBase hΩ h` are in canonical bijection with identical
item words. -/
def solutionEquivTransferBase : Ω.Solution ≃ (Ω.transferBase hΩ h).Solution where
  toFun U := U.transferBase hΩ h
  invFun U := U.ofTransferBase hΩ h
  left_inv := Solution.ofTransferBase_transferBase hΩ h
  right_inv := Solution.transferBase_ofTransferBase hΩ h

/-- `solutionEquivTransferBase` sends `U` to `U.transferBase hΩ h`. -/
@[simp]
theorem solutionEquivTransferBase_apply (U : Ω.Solution) :
    solutionEquivTransferBase hΩ h U = U.transferBase hΩ h :=
  (rfl)

/-- The inverse of `solutionEquivTransferBase` sends `U` to `U.ofTransferBase hΩ h`. -/
@[simp]
theorem solutionEquivTransferBase_symm_apply (U : (Ω.transferBase hΩ h).Solution) :
    (solutionEquivTransferBase hΩ h).symm U = U.ofTransferBase hΩ h :=
  (rfl)

/-- The homomorphism `F_{R(Ω′)} → F(A)` of `U.transferBase hΩ h` composed with `transferBaseHom`
is the homomorphism of `U`. -/
theorem toHom_comp_transferBaseHom (U : Ω.Solution) :
    (U.transferBase hΩ h).toHom.comp (transferBaseHom hΩ h) = U.toHom := by
  rw [← Solution.ofTransferBase_toHom, Solution.ofTransferBase_transferBase]

/-- If `Ω` has a solution, `Ω.transferBase hΩ h` is formally consistent. -/
theorem isFormallyConsistent_transferBase_of_nonempty_solution (hne : Nonempty Ω.Solution) :
    (Ω.transferBase hΩ h).IsFormallyConsistent :=
  let ⟨U⟩ := hne
  (U.transferBase hΩ h).isFormallyConsistent

-- `@[expose]` so the index type `.ι` and dependent target family `.target` reduce publicly.
/-- **ET2 as a transformation.** The transformation of `Ω` given by transferring `ψ` along `μ`,
keeping `Ω.transferBase hΩ h` as a successor when it is formally consistent. -/
@[expose] def transferBaseTransformation : Transformation Ω :=
  Transformation.ofFamily (κ := Unit) (fun _ => Ω.transferBase hΩ h)
    (fun _ => transferBaseHom hΩ h) (fun _ => (transferBaseHom_bijective hΩ h).2)
    (fun U => ⟨(), U.transferBase hΩ h⟩) (fun U => toHom_comp_transferBaseHom hΩ h U)

/-- `transferBaseTransformation` has at most one successor. -/
instance : Subsingleton (Ω.transferBaseTransformation hΩ h).ι :=
  inferInstanceAs (Subsingleton { _x : Unit // (Ω.transferBase hΩ h).IsFormallyConsistent })

/-- Every successor of `transferBaseTransformation` is `Ω.transferBase hΩ h`. -/
@[simp]
theorem transferBaseTransformation_target (i : (Ω.transferBaseTransformation hΩ h).ι) :
    (Ω.transferBaseTransformation hΩ h).target i = Ω.transferBase hΩ h :=
  (rfl)

/-- Every homomorphism of `transferBaseTransformation` is `transferBaseHom hΩ h`. -/
@[simp]
theorem transferBaseTransformation_hom (i : (Ω.transferBaseTransformation hΩ h).ι) :
    (Ω.transferBaseTransformation hΩ h).hom i = transferBaseHom hΩ h :=
  (rfl)

/-- `transferBaseTransformation` transfers every solution `U` to `U.transferBase hΩ h`. -/
@[simp]
theorem transferBaseTransformation_transfer_snd (U : Ω.Solution) :
    ((Ω.transferBaseTransformation hΩ h).transfer U).2 = U.transferBase hΩ h :=
  (rfl)

/-- **ET2 transfers solutions uniquely.** The solution of `Ω.transferBase hΩ h` whose homomorphism
composed with `transferBaseHom` equals `U.toHom` is `U.transferBase hΩ h`. -/
theorem toHom_comp_transferBaseHom_eq_iff (U : Ω.Solution) (U' : (Ω.transferBase hΩ h).Solution) :
    U'.toHom.comp (transferBaseHom hΩ h) = U.toHom ↔ U' = U.transferBase hΩ h :=
  ⟨fun heq => (Ω.transferBaseTransformation hΩ h).eq_of_toHom_comp_hom_eq
      ⟨(), U'.isFormallyConsistent⟩ (heq.trans (toHom_comp_transferBaseHom hΩ h U).symm),
    fun hU' => hU' ▸ toHom_comp_transferBaseHom hΩ h U⟩

/-- `transferBaseTransformation` transfers every solution of `Ω` uniquely. -/
theorem transfersUniquely_transferBaseTransformation :
    (Ω.transferBaseTransformation hΩ h).TransfersUniquely :=
  Transformation.transfersUniquely_of_subsingleton _

/-- `transferBaseTransformation` has a successor if and only if `Ω.transferBase hΩ h` is formally
consistent. -/
theorem nonempty_ι_transferBaseTransformation_iff :
    Nonempty (Ω.transferBaseTransformation hΩ h).ι ↔ (Ω.transferBase hΩ h).IsFormallyConsistent :=
  ⟨fun ⟨i⟩ => i.property, fun h' => ⟨⟨(), h'⟩⟩⟩

end Consistent

/-! ### Examples -/

section Examples

/-- Six items `h₀, …, h₅`, equal-sign carrier `μ = [0, 3]` and `Δ(μ) = [3, 6]` with boundary
connections `(1, μ, 4)` and `(2, μ, 5)`, and transfer base `ψ = [0, 2]` with `Δ(ψ) = [4, 6]` and
interior boundary connection `(1, ψ, 5)`. -/
private abbrev equalSignExample : GenEq (Fin 2) where
  numItems := 6
  numBases := 4
  left := ![0, 3, 0, 4]
  right := ![3, 6, 2, 6]
  left_lt_right := by decide
  sign := fun _ => true
  dual := ![1, 0, 3, 2]
  dual_involutive := by unfold Function.Involutive; decide
  constBases := ∅
  connections := {(1, 0, 4), (4, 1, 1), (2, 0, 5), (5, 1, 2), (1, 2, 5), (5, 3, 1)}
  bounds_of_mem_connections := by simp
  dual_mem_connections := by simp

/-- Transferring `ψ = [0, 2]` along the equal-sign carrier `μ = [0, 3]` moves `ψ` to `[3, 5]`,
keeps its sign `+1`, relocates the connection `(1, ψ, 5)` to `(4, ψ, 5)` (and `(5, Δψ, 1)` to
`(5, Δψ, 4)`), and drops the degree of `h₀` from `2` to `1`. -/
example :
    ∃ (hΩ : equalSignExample.IsFormallyConsistent)
      (h : equalSignExample.IsTransferable 0 2),
      let Ω' := equalSignExample.transferBase hΩ h
      Ω'.left 2 = 3 ∧ Ω'.right 2 = 5 ∧ Ω'.sign 2 = true ∧
        (4, 2, 5) ∈ Ω'.connections ∧ (5, 3, 4) ∈ Ω'.connections ∧ Ω'.degree 0 = 1 := by
  have hΩ : equalSignExample.IsFormallyConsistent := by decide
  have h : equalSignExample.IsTransferable 0 2 := by decide
  have ht0 : equalSignExample.tiedBoundary 0 0 = 3 := hΩ.tiedBoundary_eq isTiedTo_left
  have ht1 : equalSignExample.tiedBoundary 0 1 = 4 :=
    hΩ.tiedBoundary_eq (isTiedTo_of_mem_connections (by decide))
  have ht2 : equalSignExample.tiedBoundary 0 2 = 5 :=
    hΩ.tiedBoundary_eq (isTiedTo_of_mem_connections (by decide))
  have hdeg := degree_transferBase_add_one hΩ h (k := 0)
    (equalSignExample.mem_baseItems.2 (by decide))
    (fun hm => absurd (baseItems_transferBase_subset_dual hΩ h hm)
      (by rw [equalSignExample.mem_baseItems]; decide))
  have hdeg₀ : equalSignExample.degree 0 = 2 := by
    simp only [degree_def, equalSignExample.mem_baseItems]
    decide
  refine ⟨hΩ, h, by simp [ht0], by simp [ht2], rfl, ?_, ?_, by omega⟩
  · exact (mem_connections_transferBase hΩ h).2 ⟨(1, 2, 5), by decide,
      by rw [equalSignExample.transferConnection_of_eq (ψ := 2) (by decide) rfl, ht1]⟩
  · exact (mem_connections_transferBase hΩ h).2 ⟨(5, 3, 1), by decide,
      by rw [equalSignExample.transferConnection_of_eq_dual (ψ := 2) (by decide) (by decide), ht1]⟩

/-- Five items `h₀, …, h₄`, opposite-sign carrier `μ = [0, 2]` (`+1`) and `Δ(μ) = [2, 4]` (`-1`)
with boundary connection `(1, μ, 3)`, and transfer base `ψ = [0, 1]` (`+1`) with `Δ(ψ) = [4, 5]`
(`+1`). Its equations are `h₀h₁ = (h₂h₃)⁻¹`, `h₀ = h₃⁻¹` and `h₀ = h₄`. -/
private abbrev oppSignExample : GenEq (Fin 2) where
  numItems := 5
  numBases := 4
  left := ![0, 2, 0, 4]
  right := ![2, 4, 1, 5]
  left_lt_right := by decide
  sign := ![true, false, true, true]
  dual := ![1, 0, 3, 2]
  dual_involutive := by unfold Function.Involutive; decide
  constBases := ∅
  connections := {(1, 0, 3), (3, 1, 1)}
  bounds_of_mem_connections := by simp
  dual_mem_connections := by simp

/-- The graphical solution `(a, b, b⁻¹, a⁻¹, a)` (with `a = 0` and `b = 1`) of `oppSignExample`. -/
private def oppSignSolution : oppSignExample.Solution where
  word := ![[(0, true)], [(1, true)], [(1, false)], [(0, false)], [(0, true)]]
  isReduced_word := by unfold FreeGroup.IsReduced; decide
  word_ne_nil := by decide
  isReduced_subst := (oppSignExample.forall_mem_equations_isReduced_iff
    (by unfold FreeGroup.IsReduced; decide)).2
    (by simp only [segment_true]; unfold FreeGroup.IsReduced; decide)
  subst_eq := (forall_mem_equations _).2
    ⟨by
      have hseg (i j : ℕ) (s : Bool) : oppSignExample.segment i j s =
          let w := (((List.finRange 5).take j).drop i).map fun k => (Sum.inl k, true)
          if s then w else FreeGroup.invRev w := by
        cases s <;> simp [segment_false, segment_true]
      simp only [basicEquation_fst, basicEquation_snd, hseg]
      decide,
    fun _ hb => absurd hb (Finset.notMem_empty _),
    by
      intro c hc
      rw [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl <;>
      · rw [boundaryEquation_fst, oppSignExample.boundaryEquation_snd_of_sign_ne (by decide),
          segment_false, segment_true, segment_true]
        decide⟩

/-- Transferring `ψ = [0, 1]` along the opposite-sign carrier `μ = [0, 2]` moves `ψ` onto `[3, 4]`
and flips its sign to `-1`, turning `h₀ = h₄` into `h₃⁻¹ = h₄`, and transports the solution
`(a, b, b⁻¹, a⁻¹, a)`. -/
example :
    ∃ (hΩ : oppSignExample.IsFormallyConsistent)
      (h : oppSignExample.IsTransferable 0 2),
      let Ω' := oppSignExample.transferBase hΩ h
      Ω'.left 2 = 3 ∧ Ω'.right 2 = 4 ∧ Ω'.sign 2 = false ∧ Ω'.IsFormallyConsistent ∧
        ∃ U : Ω'.Solution, U.word = ![[(0, true)], [(1, true)], [(1, false)], [(0, false)],
          [(0, true)]] := by
  have hΩ : oppSignExample.IsFormallyConsistent := oppSignSolution.isFormallyConsistent
  have h : oppSignExample.IsTransferable 0 2 := by decide
  have ht0 : oppSignExample.tiedBoundary 0 0 = 4 := hΩ.tiedBoundary_eq isTiedTo_left
  have ht1 : oppSignExample.tiedBoundary 0 1 = 3 :=
    hΩ.tiedBoundary_eq (isTiedTo_of_mem_connections (by decide))
  exact ⟨hΩ, h, by simp [ht1], by simp [ht0], rfl,
    (oppSignSolution.transferBase hΩ h).isFormallyConsistent,
    oppSignSolution.transferBase hΩ h, Solution.transferBase_word hΩ h oppSignSolution⟩

/-- Four items `h₀, …, h₃`, opposite-sign carrier `μ = [0, 2]` (`+1`) and `Δ(μ) = [2, 4]` (`-1`)
with boundary connection `(1, μ, 3)` (`h₀ = h₃⁻¹`), and transfer base `ψ = [0, 1]` (`+1`) with
`Δ(ψ) = [3, 4]` (`+1`) (`h₀ = h₃`). This equation is formally consistent, yet transferring `ψ`
along `μ` places `ψ` at `[3, 4]` with sign `-1` on top of `Δ(ψ) = [3, 4]` (`+1`), breaking formal
consistency and witnessing that `Ω` has no graphical solution. -/
private abbrev inconsistentAfterTransfer : GenEq (Fin 2) where
  numItems := 4
  numBases := 4
  left := ![0, 2, 0, 3]
  right := ![2, 4, 1, 4]
  left_lt_right := by decide
  sign := ![true, false, true, true]
  dual := ![1, 0, 3, 2]
  dual_involutive := by unfold Function.Involutive; decide
  constBases := ∅
  connections := {(1, 0, 3), (3, 1, 1)}
  bounds_of_mem_connections := by decide
  dual_mem_connections := by decide

/-- Formal consistency is not preserved by `transferBase` in general when `Ω` has no solution:
`inconsistentAfterTransfer` is formally consistent, `IsTransferable 0 2` holds, its transferred
equation is not formally consistent, `transferBaseTransformation` has no successors, and
`inconsistentAfterTransfer` has no solution. -/
example :
    ∃ (hΩ : inconsistentAfterTransfer.IsFormallyConsistent)
      (h : inconsistentAfterTransfer.IsTransferable 0 2),
      ¬ (inconsistentAfterTransfer.transferBase hΩ h).IsFormallyConsistent ∧
        IsEmpty (inconsistentAfterTransfer.transferBaseTransformation hΩ h).ι ∧
        IsEmpty inconsistentAfterTransfer.Solution := by
  have hΩ : inconsistentAfterTransfer.IsFormallyConsistent := by decide
  have h : inconsistentAfterTransfer.IsTransferable 0 2 := by decide
  have ht1 : inconsistentAfterTransfer.tiedBoundary 0 1 = 3 :=
    hΩ.tiedBoundary_eq (isTiedTo_of_mem_connections (by decide))
  have hnot : ¬ (inconsistentAfterTransfer.transferBase hΩ h).IsFormallyConsistent := fun hΩ' => by
    have hsign := hΩ'.sign_eq_of_left_eq (μ := 2) (by simp [ht1])
    simp at hsign
  exact ⟨hΩ, h, hnot, ⟨fun i => hnot i.property⟩,
    ⟨fun U => hnot (isFormallyConsistent_transferBase_of_nonempty_solution hΩ h ⟨U⟩)⟩⟩

end Examples

end GenEq

end TauCeti
