/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Multiprojective.Local
public import TauCeti.Geometry.RealAlgebraic.Multiprojective.Map
public import TauCeti.Geometry.RealAlgebraic.Nash.Basic
import TauCeti.Geometry.RealAlgebraic.Nash.Graph

/-!
# Real Nash maps between multiprojective and mixed spaces

Graph semialgebraicity (`TauCeti.IsMixedSemialgebraicOn`,
`TauCeti.IsMultiprojectiveSemialgebraicMap`) does not by itself imply continuity. Over `ℝ`, a *Nash
map* on an open subset `U` (`TauCeti.IsMixedNashOn`) combines openness of `U`, graph
semialgebraicity on `U`, continuity on `U`, and real analyticity in every pair of standard product
affine charts around every point of `U`.

Using the local Nash graph criterion (`TauCeti.forall_isNashAt_apply_iff_exists_isSemialgebraicOn`)
and the local-to-global semialgebraicity of real multiprojective sets
(`TauCeti.isMultiprojectiveSemialgebraic_iff_exists_semialgebraicAt`), we prove that a continuous
map between real multiprojective spaces is a global Nash map if and only if every local chart
coordinate is a Nash germ (`TauCeti.IsNashAt`).

## Main declarations

* `TauCeti.IsMixedNashOn`, `TauCeti.IsMixedNashMap`: Nash maps on open subsets and globally between
  real mixed affine–multiprojective spaces.
* `TauCeti.IsMultiprojectiveNashMap`: global Nash maps between real multiprojective spaces, related
  to `TauCeti.IsMixedNashMap` via `TauCeti.isMixedNashMap_isEmpty_prod_iff`.
* `TauCeti.IsMixedNashOn.isNashAt_chart`, `TauCeti.IsMixedNashMap.isNashAt_chart`,
  `TauCeti.IsMultiprojectiveNashMap.isNashAt_chart`: every local chart coordinate of a Nash map is a
  Nash germ.
* `TauCeti.isMultiprojectiveNashMap_iff_forall_isNashAt`: local-to-global characterization of
  `TauCeti.IsMultiprojectiveNashMap` via `TauCeti.IsNashAt`.
* `TauCeti.isNashAt_multiprojectiveAffineChart_symm_trans`, `TauCeti.isMixedNashOn_id`,
  `TauCeti.isMixedNashMap_id`, `TauCeti.isMultiprojectiveNashMap_id`,
  `TauCeti.IsMixedNashOn.comp`, `TauCeti.IsMixedNashMap.comp`,
  `TauCeti.IsMultiprojectiveNashMap.comp`: chart transition Nash germs, identity, and composition
  closure for Nash maps.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete (3) 36, Springer, 1998, Section 8.1.
* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §3.
-/

public section

open Set Topology
open scoped LinearAlgebra.Projectivization

namespace TauCeti

section Definitions

variable {σ₁ σ₂ ι₁ ι₂ : Type*} [Fintype σ₁] [Fintype σ₂] [Fintype ι₁] [Fintype ι₂]
  {n₁ : ι₁ → ℕ} {n₂ : ι₂ → ℕ}

/-- A map `f` between real mixed affine–multiprojective spaces is a *Nash map on* `U` if `U` is
open and `f` is mixed semialgebraic on `U`, continuous on `U`, and real-analytic in every pair of
standard product affine charts around every point of `U`. -/
def IsMixedNashOn
    (f : ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) →
      ((σ₂ → ℝ) × ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ)))
    (U : Set ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ))) : Prop :=
  IsOpen U ∧ IsMixedSemialgebraicOn f U ∧ ContinuousOn f U ∧
    ∀ x ∈ U, ∀ (I₁ : ∀ i : ι₁, Fin (n₁ i + 1)) (I₂ : ∀ j : ι₂, Fin (n₂ j + 1)),
      x ∈ mixedAffineOpen σ₁ I₁ → f x ∈ mixedAffineOpen σ₂ I₂ →
        AnalyticAt ℝ (mixedAffineChart σ₂ I₂ ∘ f ∘ ⇑(mixedAffineChart σ₁ I₁).symm)
          (mixedAffineChart σ₁ I₁ x)

/-- A global Nash map between real mixed affine–multiprojective spaces. -/
def IsMixedNashMap
    (f : ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) →
      ((σ₂ → ℝ) × ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ))) : Prop :=
  IsMixedSemialgebraicMap f ∧ Continuous f ∧
    ∀ x (I₁ : ∀ i : ι₁, Fin (n₁ i + 1)) (I₂ : ∀ j : ι₂, Fin (n₂ j + 1)),
      x ∈ mixedAffineOpen σ₁ I₁ → f x ∈ mixedAffineOpen σ₂ I₂ →
        AnalyticAt ℝ (mixedAffineChart σ₂ I₂ ∘ f ∘ ⇑(mixedAffineChart σ₁ I₁).symm)
          (mixedAffineChart σ₁ I₁ x)

/-- A global Nash map between real multiprojective spaces. -/
def IsMultiprojectiveNashMap
    (f : (∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) → ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ)) : Prop :=
  IsMultiprojectiveSemialgebraicMap f ∧ Continuous f ∧
    ∀ p (I₁ : ∀ i : ι₁, Fin (n₁ i + 1)) (I₂ : ∀ j : ι₂, Fin (n₂ j + 1)),
      p ∈ multiprojectiveAffineOpen I₁ → f p ∈ multiprojectiveAffineOpen I₂ →
        AnalyticAt ℝ
          (multiprojectiveAffineChart (K := ℝ) I₂ ∘ f ∘
            ⇑(multiprojectiveAffineChart (K := ℝ) I₁).symm)
          (multiprojectiveAffineChart (K := ℝ) I₁ p)

theorem isMixedNashOn_def
    {f : ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) →
      ((σ₂ → ℝ) × ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ))}
    {U : Set ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ))} :
    IsMixedNashOn f U ↔
      IsOpen U ∧ IsMixedSemialgebraicOn f U ∧ ContinuousOn f U ∧
        ∀ x ∈ U, ∀ (I₁ : ∀ i : ι₁, Fin (n₁ i + 1)) (I₂ : ∀ j : ι₂, Fin (n₂ j + 1)),
          x ∈ mixedAffineOpen σ₁ I₁ → f x ∈ mixedAffineOpen σ₂ I₂ →
            AnalyticAt ℝ (mixedAffineChart σ₂ I₂ ∘ f ∘ ⇑(mixedAffineChart σ₁ I₁).symm)
              (mixedAffineChart σ₁ I₁ x) :=
  Iff.rfl

theorem isMixedNashMap_def
    {f : ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) →
      ((σ₂ → ℝ) × ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ))} :
    IsMixedNashMap f ↔
      IsMixedSemialgebraicMap f ∧ Continuous f ∧
        ∀ x (I₁ : ∀ i : ι₁, Fin (n₁ i + 1)) (I₂ : ∀ j : ι₂, Fin (n₂ j + 1)),
          x ∈ mixedAffineOpen σ₁ I₁ → f x ∈ mixedAffineOpen σ₂ I₂ →
            AnalyticAt ℝ (mixedAffineChart σ₂ I₂ ∘ f ∘ ⇑(mixedAffineChart σ₁ I₁).symm)
              (mixedAffineChart σ₁ I₁ x) :=
  Iff.rfl

theorem isMultiprojectiveNashMap_def
    {f : (∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) → ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ)} :
    IsMultiprojectiveNashMap f ↔
      IsMultiprojectiveSemialgebraicMap f ∧ Continuous f ∧
        ∀ p (I₁ : ∀ i : ι₁, Fin (n₁ i + 1)) (I₂ : ∀ j : ι₂, Fin (n₂ j + 1)),
          p ∈ multiprojectiveAffineOpen I₁ → f p ∈ multiprojectiveAffineOpen I₂ →
            AnalyticAt ℝ
              (multiprojectiveAffineChart (K := ℝ) I₂ ∘ f ∘
                ⇑(multiprojectiveAffineChart (K := ℝ) I₁).symm)
              (multiprojectiveAffineChart (K := ℝ) I₁ p) :=
  Iff.rfl

@[simp]
theorem isMixedNashOn_univ
    {f : ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) →
      ((σ₂ → ℝ) × ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ))} :
    IsMixedNashOn f univ ↔ IsMixedNashMap f := by
  simp [IsMixedNashOn, IsMixedNashMap, continuousOn_univ]

theorem IsMixedNashOn.isOpen
    {f : ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) →
      ((σ₂ → ℝ) × ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ))}
    {U : Set ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ))}
    (hf : IsMixedNashOn f U) : IsOpen U :=
  hf.1

theorem IsMixedNashOn.isMixedSemialgebraicOn
    {f : ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) →
      ((σ₂ → ℝ) × ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ))}
    {U : Set ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ))}
    (hf : IsMixedNashOn f U) : IsMixedSemialgebraicOn f U :=
  hf.2.1

theorem IsMixedNashOn.continuousOn
    {f : ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) →
      ((σ₂ → ℝ) × ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ))}
    {U : Set ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ))}
    (hf : IsMixedNashOn f U) : ContinuousOn f U :=
  hf.2.2.1

theorem IsMixedNashOn.analyticAt_chart
    {f : ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) →
      ((σ₂ → ℝ) × ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ))}
    {U : Set ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ))}
    (hf : IsMixedNashOn f U) {x : (σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)}
    (hxU : x ∈ U) {I₁ : ∀ i : ι₁, Fin (n₁ i + 1)} {I₂ : ∀ j : ι₂, Fin (n₂ j + 1)}
    (hx₁ : x ∈ mixedAffineOpen σ₁ I₁) (hx₂ : f x ∈ mixedAffineOpen σ₂ I₂) :
    AnalyticAt ℝ (mixedAffineChart σ₂ I₂ ∘ f ∘ ⇑(mixedAffineChart σ₁ I₁).symm)
      (mixedAffineChart σ₁ I₁ x) :=
  hf.2.2.2 x hxU I₁ I₂ hx₁ hx₂

theorem IsMixedNashMap.isMixedSemialgebraicMap
    {f : ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) →
      ((σ₂ → ℝ) × ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ))}
    (hf : IsMixedNashMap f) : IsMixedSemialgebraicMap f :=
  hf.1

theorem IsMixedNashMap.continuous
    {f : ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) →
      ((σ₂ → ℝ) × ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ))}
    (hf : IsMixedNashMap f) : Continuous f :=
  hf.2.1

theorem IsMixedNashMap.analyticAt_chart
    {f : ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) →
      ((σ₂ → ℝ) × ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ))}
    (hf : IsMixedNashMap f) {x : (σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)}
    {I₁ : ∀ i : ι₁, Fin (n₁ i + 1)} {I₂ : ∀ j : ι₂, Fin (n₂ j + 1)}
    (hx₁ : x ∈ mixedAffineOpen σ₁ I₁) (hx₂ : f x ∈ mixedAffineOpen σ₂ I₂) :
    AnalyticAt ℝ (mixedAffineChart σ₂ I₂ ∘ f ∘ ⇑(mixedAffineChart σ₁ I₁).symm)
      (mixedAffineChart σ₁ I₁ x) :=
  hf.2.2 x I₁ I₂ hx₁ hx₂

theorem IsMultiprojectiveNashMap.isMultiprojectiveSemialgebraicMap
    {f : (∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) → ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ)}
    (hf : IsMultiprojectiveNashMap f) : IsMultiprojectiveSemialgebraicMap f :=
  hf.1

theorem IsMultiprojectiveNashMap.continuous
    {f : (∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) → ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ)}
    (hf : IsMultiprojectiveNashMap f) : Continuous f :=
  hf.2.1

theorem IsMultiprojectiveNashMap.analyticAt_chart
    {f : (∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) → ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ)}
    (hf : IsMultiprojectiveNashMap f) {p : ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)}
    {I₁ : ∀ i : ι₁, Fin (n₁ i + 1)} {I₂ : ∀ j : ι₂, Fin (n₂ j + 1)}
    (hp₁ : p ∈ multiprojectiveAffineOpen I₁) (hp₂ : f p ∈ multiprojectiveAffineOpen I₂) :
    AnalyticAt ℝ
      (multiprojectiveAffineChart (K := ℝ) I₂ ∘ f ∘
        ⇑(multiprojectiveAffineChart (K := ℝ) I₁).symm)
      (multiprojectiveAffineChart (K := ℝ) I₁ p) :=
  hf.2.2 p I₁ I₂ hp₁ hp₂

/-- Pure multiprojective Nash maps coincide with global mixed Nash maps after adjoining an
arbitrary finite domain affine factor `σ₁` and an empty target affine factor `σ₂`. -/
theorem isMixedNashMap_isEmpty_prod_iff [IsEmpty σ₂]
    {f : (∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) → ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ)} :
    IsMixedNashMap
        (fun xp : (σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ) ↦
          ((isEmptyElim : σ₂ → ℝ), f xp.2)) ↔
      IsMultiprojectiveNashMap f := by
  let F : ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) →
      ((σ₂ → ℝ) × ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ)) :=
    fun xp ↦ ((isEmptyElim : σ₂ → ℝ), f xp.2)
  have hsemi : IsMixedSemialgebraicMap F ↔ IsMultiprojectiveSemialgebraicMap f := by
    rw [← isMixedSemialgebraicOn_univ, ← univ_prod_univ,
      isMixedSemialgebraicOn_univ_prod_iff, isMultiprojectiveSemialgebraicOn_univ]
  refine ⟨fun hF ↦ ⟨hsemi.1 hF.1, ?_, fun p I₁ I₂ hp₁ hp₂ ↦ ?_⟩,
    fun hf ↦ ⟨hsemi.2 hf.1, continuous_const.prodMk (hf.2.1.comp continuous_snd),
      fun x I₁ I₂ hx₁ hx₂ ↦ ?_⟩⟩
  · have hcomp : f = Prod.snd ∘ F ∘ fun p ↦ ((0 : σ₁ → ℝ), p) := rfl
    rw [hcomp]
    exact continuous_snd.comp (hF.2.1.comp (continuous_const.prodMk continuous_id))
  · let inrEmb : ((Σ i, Fin (n₁ i)) → ℝ) → ((σ₁ ⊕ Σ i, Fin (n₁ i)) → ℝ) :=
      fun w ↦ Sum.elim 0 w
    have hinr_pt : inrEmb (multiprojectiveAffineChart (K := ℝ) I₁ p) =
        mixedAffineChart σ₁ I₁ ((0 : σ₁ → ℝ), p) := by
      ext (a | q) <;> simp [inrEmb]
    have hinr_an : AnalyticAt ℝ inrEmb (multiprojectiveAffineChart (K := ℝ) I₁ p) :=
      AnalyticAt.pi fun
        | .inl _ => analyticAt_const
        | .inr q => by simpa [inrEmb] using analyticAt_pi_iff.1 analyticAt_id q
    have hF_an := hF.analyticAt_chart (x := ((0 : σ₁ → ℝ), p))
      (mem_mixedAffineOpen.2 hp₁) (mem_mixedAffineOpen.2 hp₂)
    rw [← hinr_pt] at hF_an
    have hcomp := hF_an.comp hinr_an
    exact AnalyticAt.pi fun q ↦ by
      simpa [F, inrEmb, Function.comp_def, Sum.elim_comp_inr] using
        analyticAt_pi_iff.1 hcomp (.inr q)
  · let projInr : ((σ₁ ⊕ Σ i, Fin (n₁ i)) → ℝ) → ((Σ i, Fin (n₁ i)) → ℝ) :=
      fun z ↦ z ∘ Sum.inr
    have hproj_pt : projInr (mixedAffineChart σ₁ I₁ x) =
        multiprojectiveAffineChart (K := ℝ) I₁ x.2 :=
      funext fun q ↦ by simp [projInr]
    have hproj_an : AnalyticAt ℝ projInr (mixedAffineChart σ₁ I₁ x) :=
      AnalyticAt.pi fun q ↦ by simpa [projInr] using analyticAt_pi_iff.1 analyticAt_id (Sum.inr q)
    have hf_an := hf.analyticAt_chart (mem_mixedAffineOpen.1 hx₁) (mem_mixedAffineOpen.1 hx₂)
    rw [← hproj_pt] at hf_an
    have hcomp := hf_an.comp hproj_an
    exact AnalyticAt.pi fun
      | .inl a => isEmptyElim a
      | .inr q => by
          simpa [F, projInr, Function.comp_def] using analyticAt_pi_iff.1 hcomp q

/-- Every local chart coordinate of a `TauCeti.IsMixedNashOn` map is a Nash germ
(`TauCeti.IsNashAt`). -/
theorem IsMixedNashOn.isNashAt_chart
    {f : ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) →
      ((σ₂ → ℝ) × ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ))}
    {U : Set ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ))}
    (hf : IsMixedNashOn f U) {x : (σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)}
    (hxU : x ∈ U) {I₁ : ∀ i : ι₁, Fin (n₁ i + 1)} {I₂ : ∀ j : ι₂, Fin (n₂ j + 1)}
    (hx₁ : x ∈ mixedAffineOpen σ₁ I₁) (hx₂ : f x ∈ mixedAffineOpen σ₂ I₂)
    (c : σ₂ ⊕ Σ j, Fin (n₂ j)) :
    IsNashAt (fun z ↦ (mixedAffineChart σ₂ I₂ ∘ f ∘ ⇑(mixedAffineChart σ₁ I₁).symm) z c)
      (mixedAffineChart σ₁ I₁ x) := by
  refine forall_isNashAt_apply_iff_exists_isSemialgebraicOn.2
    ⟨hf.analyticAt_chart hxU hx₁ hx₂,
      mixedAffineChart σ₁ I₁ '' (U ∩ mixedAffineOpen σ₁ I₁ ∩ f ⁻¹' mixedAffineOpen σ₂ I₂),
      ?_, ⟨x, ⟨⟨hxU, hx₁⟩, hx₂⟩, rfl⟩,
      (isMixedSemialgebraicOn_iff_forall_isSemialgebraicOn.1 hf.isMixedSemialgebraicOn) I₁ I₂⟩ c
  rw [inter_right_comm U, mixedAffineChart_image_inter_affineOpen]
  exact (hf.continuousOn.isOpen_inter_preimage hf.isOpen (isOpen_mixedAffineOpen I₂)).preimage
    (continuous_mixedAffineChart_symm I₁)

/-- Every local chart coordinate of a `TauCeti.IsMixedNashMap` is a Nash germ. -/
theorem IsMixedNashMap.isNashAt_chart
    {f : ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) →
      ((σ₂ → ℝ) × ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ))}
    (hf : IsMixedNashMap f) {x : (σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)}
    {I₁ : ∀ i : ι₁, Fin (n₁ i + 1)} {I₂ : ∀ j : ι₂, Fin (n₂ j + 1)}
    (hx₁ : x ∈ mixedAffineOpen σ₁ I₁) (hx₂ : f x ∈ mixedAffineOpen σ₂ I₂)
    (c : σ₂ ⊕ Σ j, Fin (n₂ j)) :
    IsNashAt (fun z ↦ (mixedAffineChart σ₂ I₂ ∘ f ∘ ⇑(mixedAffineChart σ₁ I₁).symm) z c)
      (mixedAffineChart σ₁ I₁ x) :=
  (isMixedNashOn_univ.2 hf).isNashAt_chart (mem_univ x) hx₁ hx₂ c

/-- Every local chart coordinate of a `TauCeti.IsMultiprojectiveNashMap` is a Nash germ. -/
theorem IsMultiprojectiveNashMap.isNashAt_chart
    {f : (∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) → ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ)}
    (hf : IsMultiprojectiveNashMap f) {p : ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)}
    {I₁ : ∀ i : ι₁, Fin (n₁ i + 1)} {I₂ : ∀ j : ι₂, Fin (n₂ j + 1)}
    (hp₁ : p ∈ multiprojectiveAffineOpen I₁) (hp₂ : f p ∈ multiprojectiveAffineOpen I₂)
    (q : Σ j, Fin (n₂ j)) :
    IsNashAt
      (fun z ↦ (multiprojectiveAffineChart (K := ℝ) I₂ ∘ f ∘
        ⇑(multiprojectiveAffineChart (K := ℝ) I₁).symm) z q)
      (multiprojectiveAffineChart (K := ℝ) I₁ p) := by
  have hmixed := ((isMixedNashMap_isEmpty_prod_iff (σ₁ := Empty) (σ₂ := Empty)).2 hf).isNashAt_chart
    (x := (isEmptyElim, p)) (mem_mixedAffineOpen.2 hp₁) (mem_mixedAffineOpen.2 hp₂) (.inr q)
  obtain ⟨_, U, hUo, hxU, hU, hG⟩ := isNashAt_iff_exists_isSemialgebraicOn.1 hmixed
  let e : (Σ i, Fin (n₁ i)) ≃ (Empty ⊕ Σ i, Fin (n₁ i)) := (Equiv.emptySum Empty _).symm
  have hpt : (mixedAffineChart Empty I₁ (isEmptyElim, p)) ∘ e =
      multiprojectiveAffineChart (K := ℝ) I₁ p :=
    funext fun k ↦ by simp [e]
  refine isNashAt_iff_exists_isSemialgebraicOn.2
    ⟨(analyticAt_pi_iff.1 (hf.analyticAt_chart hp₁ hp₂)) q,
      (fun z ↦ z ∘ e.symm) ⁻¹' U,
      hUo.preimage (continuous_pi fun c ↦ continuous_apply (e.symm c)),
      by simpa [← hpt, Function.comp_def] using hxU,
      hU.preimage_comp e.symm, ?_⟩
  exact ((isSemialgebraicOn_preimage_comp_equiv_iff e.symm).2 hG).congr fun z _ ↦
    funext fun _ ↦ by simp [e, Function.comp_def]

end Definitions

section LocalToGlobal

private theorem multiprojectiveAffineChart_comp_sumSigmaDistrib_inl
    {ι₁ ι₂ : Type*} {n₁ : ι₁ → ℕ} {n₂ : ι₂ → ℕ}
    (I₁ : ∀ i : ι₁, Fin (n₁ i + 1)) (I₂ : ∀ j : ι₂, Fin (n₂ j + 1))
    (r : ∀ k : ι₁ ⊕ ι₂, ℙ ℝ (Fin (Sum.elim n₁ n₂ k + 1) → ℝ)) :
    (fun q : Σ i : ι₁, Fin (n₁ i) ↦
        multiprojectiveAffineChart (sumPiFinIndex I₁ I₂) r ⟨.inl q.1, q.2⟩) =
      multiprojectiveAffineChart I₁ (fun i ↦ r (.inl i)) :=
  funext fun ⟨i, k⟩ ↦ multiprojectiveAffineChart_sumPiFinIndex_inl I₁ I₂ r i k

private theorem multiprojectiveAffineChart_comp_sumSigmaDistrib_inr
    {ι₁ ι₂ : Type*} {n₁ : ι₁ → ℕ} {n₂ : ι₂ → ℕ}
    (I₁ : ∀ i : ι₁, Fin (n₁ i + 1)) (I₂ : ∀ j : ι₂, Fin (n₂ j + 1))
    (r : ∀ k : ι₁ ⊕ ι₂, ℙ ℝ (Fin (Sum.elim n₁ n₂ k + 1) → ℝ)) :
    (fun q : Σ j : ι₂, Fin (n₂ j) ↦
        multiprojectiveAffineChart (sumPiFinIndex I₁ I₂) r ⟨.inr q.1, q.2⟩) =
      multiprojectiveAffineChart I₂ (fun j ↦ r (.inr j)) :=
  funext fun ⟨j, l⟩ ↦ multiprojectiveAffineChart_sumPiFinIndex_inr I₁ I₂ r j l

private theorem sumPiEquivProdPi_multiprojectiveAffineChart_symm
    {ι₁ ι₂ : Type*} {n₁ : ι₁ → ℕ} {n₂ : ι₂ → ℕ}
    (I₁ : ∀ i : ι₁, Fin (n₁ i + 1)) (I₂ : ∀ j : ι₂, Fin (n₂ j + 1))
    (w : (Σ k : ι₁ ⊕ ι₂, Fin (Sum.elim n₁ n₂ k)) → ℝ) :
    Equiv.sumPiEquivProdPi (fun k : ι₁ ⊕ ι₂ ↦ ℙ ℝ (Fin (Sum.elim n₁ n₂ k + 1) → ℝ))
        ((multiprojectiveAffineChart (K := ℝ) (sumPiFinIndex I₁ I₂)).symm w) =
      ((multiprojectiveAffineChart (K := ℝ) I₁).symm (fun q ↦ w ⟨.inl q.1, q.2⟩),
        (multiprojectiveAffineChart (K := ℝ) I₂).symm (fun q ↦ w ⟨.inr q.1, q.2⟩)) :=
  (Equiv.sumPiEquivProdPi_apply _ _).trans <| Prod.ext
    (funext fun i ↦
      (multiprojectiveAffineChart_symm_apply (sumPiFinIndex I₁ I₂) w (.inl i)).trans <| by
        rw [sumPiFinIndex_inl]
        exact (multiprojectiveAffineChart_symm_apply I₁ (fun q ↦ w ⟨.inl q.1, q.2⟩) i).symm)
    (funext fun j ↦
      (multiprojectiveAffineChart_symm_apply (sumPiFinIndex I₁ I₂) w (.inr j)).trans <| by
        rw [sumPiFinIndex_inr]
        exact (multiprojectiveAffineChart_symm_apply I₂ (fun q ↦ w ⟨.inr q.1, q.2⟩) j).symm)

private theorem semialgebraicAt_graphOn_of_forall_isNashAt_of_eq
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Finite ι₂] {n₁ : ι₁ → ℕ} {n₂ : ι₂ → ℕ}
    {f : (∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) → ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ)}
    (hf_cont : Continuous f)
    (hf_nash : ∀ p (I₁ : ∀ i : ι₁, Fin (n₁ i + 1)) (I₂ : ∀ j : ι₂, Fin (n₂ j + 1)),
      p ∈ multiprojectiveAffineOpen I₁ → f p ∈ multiprojectiveAffineOpen I₂ →
      ∀ q : Σ j, Fin (n₂ j),
        IsNashAt (fun z ↦
          (multiprojectiveAffineChart (K := ℝ) I₂ ∘ f ∘
            ⇑(multiprojectiveAffineChart (K := ℝ) I₁).symm) z q)
          (multiprojectiveAffineChart (K := ℝ) I₁ p))
    (r : ∀ k : ι₁ ⊕ ι₂, ℙ ℝ (Fin (Sum.elim n₁ n₂ k + 1) → ℝ))
    (I₁ : ∀ i : ι₁, Fin (n₁ i + 1)) (I₂ : ∀ j : ι₂, Fin (n₂ j + 1))
    (hp₁ : (fun i ↦ r (.inl i)) ∈ multiprojectiveAffineOpen I₁)
    (hy₂ : (fun j ↦ r (.inr j)) ∈ multiprojectiveAffineOpen I₂)
    (hyf : (fun j ↦ r (.inr j)) = f (fun i ↦ r (.inl i))) :
    SemialgebraicAt
      (multiprojectiveAffineChart (sumPiFinIndex I₁ I₂) ''
        ((Equiv.sumPiEquivProdPi (fun k : ι₁ ⊕ ι₂ ↦
          ℙ ℝ (Fin (Sum.elim n₁ n₂ k + 1) → ℝ)) ⁻¹' univ.graphOn f) ∩
          multiprojectiveAffineOpen (sumPiFinIndex I₁ I₂)))
      (multiprojectiveAffineChart (sumPiFinIndex I₁ I₂) r) := by
  have := Fintype.ofFinite ι₂
  let sc : ((Σ i : ι₁, Fin (n₁ i)) ⊕ (Σ j : ι₂, Fin (n₂ j))) →
      Σ k : ι₁ ⊕ ι₂, Fin (Sum.elim n₁ n₂ k) :=
    (Equiv.sumSigmaDistrib fun k : ι₁ ⊕ ι₂ ↦ Fin (Sum.elim n₁ n₂ k)).symm
  obtain ⟨_, W, hWo, hzW, hW_semi⟩ := forall_isNashAt_apply_iff_exists_isSemialgebraicOn.1
    (hf_nash (fun i ↦ r (.inl i)) I₁ I₂ hp₁ (hyf ▸ hy₂))
  let W₀ := (multiprojectiveAffineChart (K := ℝ) I₁).symm ⁻¹' (f ⁻¹' multiprojectiveAffineOpen I₂)
  have hNo : IsOpen ((fun w : (Σ k, Fin (Sum.elim n₁ n₂ k)) → ℝ ↦ w ∘ sc ∘ Sum.inl) ⁻¹'
      (W ∩ W₀)) :=
    (hWo.inter ((isOpen_multiprojectiveAffineOpen I₂).preimage
      (hf_cont.comp (continuous_multiprojectiveAffineChart_symm I₁)))).preimage
      (continuous_pi fun q ↦ continuous_apply (sc (.inl q)))
  have hsc_inl : multiprojectiveAffineChart (sumPiFinIndex I₁ I₂) r ∘ sc ∘ Sum.inl =
      multiprojectiveAffineChart I₁ (fun i ↦ r (.inl i)) :=
    multiprojectiveAffineChart_comp_sumSigmaDistrib_inl I₁ I₂ r
  have hrN : multiprojectiveAffineChart (sumPiFinIndex I₁ I₂) r ∈
      (fun w ↦ w ∘ sc ∘ Sum.inl) ⁻¹' (W ∩ W₀) := by
    rw [mem_preimage, mem_inter_iff]; dsimp only [W₀]; rw [mem_preimage, mem_preimage]
    exact ⟨hsc_inl.symm ▸ hzW,
      ((congrArg (multiprojectiveAffineChart (K := ℝ) I₁).symm hsc_inl).trans
        ((multiprojectiveAffineChart (K := ℝ) I₁).left_inv
          (by rw [multiprojectiveAffineChart_source]; exact hp₁))).symm ▸ (hyf ▸ hy₂ :
            f (fun i ↦ r (.inl i)) ∈ multiprojectiveAffineOpen I₂)⟩
  rw [multiprojectiveAffineChart_image_inter_affineOpen]
  refine ((hW_semi.graph.preimage_comp sc).semialgebraicAt
      (multiprojectiveAffineChart (sumPiFinIndex I₁ I₂) r)).congr (Filter.eventuallyEqSet_iff.2
      (Filter.eventually_of_mem (hNo.mem_nhds hrN) fun w ⟨hwW, hwW₀⟩ ↦ ?_))
  have hw_inl : (w ∘ sc) ∘ Sum.inl = fun q : Σ i : ι₁, Fin (n₁ i) ↦ w ⟨.inl q.1, q.2⟩ := rfl
  have hw_inr : (w ∘ sc) ∘ Sum.inr = fun q : Σ j : ι₂, Fin (n₂ j) ↦ w ⟨.inr q.1, q.2⟩ := rfl
  rw [mem_preimage, mem_preimage_sumArrowEquivProdArrow_graphOn, hw_inl, hw_inr,
    mem_preimage, mem_preimage, sumPiEquivProdPi_multiprojectiveAffineChart_symm]
  refine ⟨fun ⟨_, hfg⟩ ↦ mem_graphOn.2 ⟨trivial, ?_⟩, fun hmem ↦ ⟨hwW, ?_⟩⟩
  · simp only [Function.comp_apply] at hfg
    rw [← hfg]
    exact ((multiprojectiveAffineChart (K := ℝ) I₂).left_inv
      (by rw [multiprojectiveAffineChart_source]; exact hwW₀)).symm
  · obtain ⟨_, hfg⟩ := mem_graphOn.1 hmem
    simp only [Function.comp_apply, hfg]
    exact (multiprojectiveAffineChart (K := ℝ) I₂).right_inv
      (by rw [multiprojectiveAffineChart_target]; exact mem_univ _)

private theorem semialgebraicAt_graphOn_of_continuous_of_ne
    {ι₁ ι₂ : Type*} [Finite ι₁] [Finite ι₂] {n₁ : ι₁ → ℕ} {n₂ : ι₂ → ℕ}
    {f : (∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) → ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ)}
    (hf_cont : Continuous f)
    (r : ∀ k : ι₁ ⊕ ι₂, ℙ ℝ (Fin (Sum.elim n₁ n₂ k + 1) → ℝ))
    (I₁ : ∀ i : ι₁, Fin (n₁ i + 1)) (I₂ : ∀ j : ι₂, Fin (n₂ j + 1))
    (hp₁ : (fun i ↦ r (.inl i)) ∈ multiprojectiveAffineOpen I₁)
    (hy₂ : (fun j ↦ r (.inr j)) ∈ multiprojectiveAffineOpen I₂)
    (hyf : (fun j ↦ r (.inr j)) ≠ f (fun i ↦ r (.inl i))) :
    SemialgebraicAt
      (multiprojectiveAffineChart (sumPiFinIndex I₁ I₂) ''
        ((Equiv.sumPiEquivProdPi (fun k : ι₁ ⊕ ι₂ ↦
          ℙ ℝ (Fin (Sum.elim n₁ n₂ k + 1) → ℝ)) ⁻¹' univ.graphOn f) ∩
          multiprojectiveAffineOpen (sumPiFinIndex I₁ I₂)))
      (multiprojectiveAffineChart (sumPiFinIndex I₁ I₂) r) := by
  rw [multiprojectiveAffineChart_image_inter_affineOpen]
  set I := sumPiFinIndex I₁ I₂
  set G : Set (∀ k : ι₁ ⊕ ι₂, ℙ ℝ (Fin (Sum.elim n₁ n₂ k + 1) → ℝ)) :=
    Equiv.sumPiEquivProdPi (fun k : ι₁ ⊕ ι₂ ↦ ℙ ℝ (Fin (Sum.elim n₁ n₂ k + 1) → ℝ)) ⁻¹'
      univ.graphOn f
  have hrI : r ∈ multiprojectiveAffineOpen I :=
    mem_multiprojectiveAffineOpen_sumPiFinIndex.2 ⟨hp₁, hy₂⟩
  have hclosed : IsClosed G := by
    have hG : G = {r' | f (fun i ↦ r' (.inl i)) = fun j ↦ r' (.inr j)} := by
      ext r'
      exact ⟨fun h ↦ (mem_graphOn.1 h).2, fun h ↦ mem_graphOn.2 ⟨trivial, h⟩⟩
    rw [hG]
    exact isClosed_eq
      (hf_cont.comp (continuous_pi fun i ↦ continuous_apply (Sum.inl i : ι₁ ⊕ ι₂)))
      (continuous_pi fun j ↦ continuous_apply (Sum.inr j : ι₁ ⊕ ι₂))
  let N : Set ((Σ k : ι₁ ⊕ ι₂, Fin (Sum.elim n₁ n₂ k)) → ℝ) :=
    (multiprojectiveAffineChart (K := ℝ) I).symm ⁻¹' Gᶜ
  have hNo : IsOpen N :=
    hclosed.isOpen_compl.preimage (continuous_multiprojectiveAffineChart_symm I)
  have hrN : multiprojectiveAffineChart I r ∈ N := by
    simp only [N, mem_preimage, mem_compl_iff]
    rw [(multiprojectiveAffineChart (K := ℝ) I).left_inv
      (by rw [multiprojectiveAffineChart_source]; exact hrI)]
    exact fun hrG ↦ hyf (mem_graphOn.1 hrG).2.symm
  refine semialgebraicAt_empty.congr
    (Filter.eventuallyEqSet_iff.2 (Filter.eventually_of_mem (hNo.mem_nhds hrN) fun w hw ↦ ?_))
  simpa [N] using hw

private theorem semialgebraicAt_graphOn_of_forall_isNashAt
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Finite ι₂] {n₁ : ι₁ → ℕ} {n₂ : ι₂ → ℕ}
    {f : (∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) → ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ)}
    (hf_cont : Continuous f)
    (hf_nash : ∀ p (I₁ : ∀ i : ι₁, Fin (n₁ i + 1)) (I₂ : ∀ j : ι₂, Fin (n₂ j + 1)),
      p ∈ multiprojectiveAffineOpen I₁ → f p ∈ multiprojectiveAffineOpen I₂ →
      ∀ q : Σ j, Fin (n₂ j),
        IsNashAt (fun z ↦
          (multiprojectiveAffineChart (K := ℝ) I₂ ∘ f ∘
            ⇑(multiprojectiveAffineChart (K := ℝ) I₁).symm) z q)
          (multiprojectiveAffineChart (K := ℝ) I₁ p))
    (r : ∀ k : ι₁ ⊕ ι₂, ℙ ℝ (Fin (Sum.elim n₁ n₂ k + 1) → ℝ))
    (I₁ : ∀ i : ι₁, Fin (n₁ i + 1)) (I₂ : ∀ j : ι₂, Fin (n₂ j + 1))
    (hp₁ : (fun i ↦ r (.inl i)) ∈ multiprojectiveAffineOpen I₁)
    (hy₂ : (fun j ↦ r (.inr j)) ∈ multiprojectiveAffineOpen I₂) :
    SemialgebraicAt
      (multiprojectiveAffineChart (sumPiFinIndex I₁ I₂) ''
        ((Equiv.sumPiEquivProdPi (fun k : ι₁ ⊕ ι₂ ↦
          ℙ ℝ (Fin (Sum.elim n₁ n₂ k + 1) → ℝ)) ⁻¹' univ.graphOn f) ∩
          multiprojectiveAffineOpen (sumPiFinIndex I₁ I₂)))
      (multiprojectiveAffineChart (sumPiFinIndex I₁ I₂) r) := by
  by_cases hyf : (fun j ↦ r (.inr j)) = f (fun i ↦ r (.inl i))
  · exact semialgebraicAt_graphOn_of_forall_isNashAt_of_eq hf_cont hf_nash r I₁ I₂ hp₁ hy₂ hyf
  · exact semialgebraicAt_graphOn_of_continuous_of_ne hf_cont r I₁ I₂ hp₁ hy₂ hyf

/-- **Local-to-global characterization of real multiprojective Nash maps.** A map `f` between real
multiprojective spaces is a global Nash map (`TauCeti.IsMultiprojectiveNashMap f`) if and only if
`f` is continuous and in every pair of standard product affine charts `(I₁, I₂)` around `(p, f p)`,
every coordinate of `multiprojectiveAffineChart I₂ ∘ f ∘ (multiprojectiveAffineChart I₁).symm` is a
Nash germ at `multiprojectiveAffineChart I₁ p`. -/
theorem isMultiprojectiveNashMap_iff_forall_isNashAt
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] {n₁ : ι₁ → ℕ} {n₂ : ι₂ → ℕ}
    {f : (∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) → ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ)} :
    IsMultiprojectiveNashMap f ↔ Continuous f ∧
      ∀ p (I₁ : ∀ i : ι₁, Fin (n₁ i + 1)) (I₂ : ∀ j : ι₂, Fin (n₂ j + 1)),
        p ∈ multiprojectiveAffineOpen I₁ → f p ∈ multiprojectiveAffineOpen I₂ →
        ∀ q : Σ j, Fin (n₂ j),
          IsNashAt (fun z ↦
            (multiprojectiveAffineChart (K := ℝ) I₂ ∘ f ∘
              ⇑(multiprojectiveAffineChart (K := ℝ) I₁).symm) z q)
            (multiprojectiveAffineChart (K := ℝ) I₁ p) := by
  refine ⟨fun hf ↦ ⟨hf.continuous, fun p I₁ I₂ hp₁ hp₂ q ↦ hf.isNashAt_chart hp₁ hp₂ q⟩,
    fun ⟨hf_cont, hf_nash⟩ ↦
      ⟨isMultiprojectiveSemialgebraicOn_univ.1
        (isMultiprojectiveSemialgebraicOn_def.2 ⟨isMultiprojectiveSemialgebraic_univ, ?_⟩),
        hf_cont,
        fun p I₁ I₂ hp₁ hp₂ ↦ AnalyticAt.pi fun q ↦ (hf_nash p I₁ I₂ hp₁ hp₂ q).analyticAt⟩⟩
  rw [isMultiprojectiveSemialgebraic_iff_exists_semialgebraicAt]
  intro r
  obtain ⟨I₁, hp₁⟩ := exists_mem_multiprojectiveAffineOpen (fun i ↦ r (.inl i))
  obtain ⟨I₂, hy₂⟩ := exists_mem_multiprojectiveAffineOpen (fun j ↦ r (.inr j))
  exact ⟨sumPiFinIndex I₁ I₂, mem_multiprojectiveAffineOpen_sumPiFinIndex.2 ⟨hp₁, hy₂⟩,
    semialgebraicAt_graphOn_of_forall_isNashAt hf_cont hf_nash r I₁ I₂ hp₁ hy₂⟩

end LocalToGlobal

section Calculus

variable {σ σ₁ σ₂ σ₃ ι ι₁ ι₂ ι₃ : Type*} [Fintype σ] [Fintype σ₁] [Fintype σ₂] [Fintype σ₃]
  [Fintype ι] [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
  {n : ι → ℕ} {n₁ : ι₁ → ℕ} {n₂ : ι₂ → ℕ} {n₃ : ι₃ → ℕ}

/-- Every coordinate of the transition map between two real standard product affine charts is a
Nash germ at every point of its source. -/
theorem isNashAt_multiprojectiveAffineChart_symm_trans (I J : ∀ i, Fin (n i + 1))
    {z : (Σ i, Fin (n i)) → ℝ}
    (hz : z ∈ ((multiprojectiveAffineChart (K := ℝ) I).symm.trans
      (multiprojectiveAffineChart J)).source)
    (q : Σ i, Fin (n i)) :
    IsNashAt (fun w ↦ (multiprojectiveAffineChart I).symm.trans
      (multiprojectiveAffineChart J) w q) z := by
  rw [multiprojectiveAffineChart_symm_trans_source] at hz
  have hins (l : Fin (n q.1 + 1)) :
      IsNashAt (fun w : (Σ i, Fin (n i)) → ℝ ↦
        Fin.insertNth (α := fun _ ↦ ℝ) (I q.1) 1 (fun k ↦ w ⟨q.1, k⟩) l) z := by
    induction l using (I q.1).succAboveCases with
    | x => simpa using isNashAt_const 1
    | p k => simpa using isNashAt_apply (⟨q.1, k⟩ : Σ i, Fin (n i))
  simp only [multiprojectiveAffineChart_symm_trans_apply]
  exact (hins ((J q.1).succAbove q.2)).fun_div (hins (J q.1)) (hz q.1)

/-- The identity map on an open mixed semialgebraic subset of a real mixed space is a Nash map. -/
theorem isMixedNashOn_id
    {U : Set ((σ → ℝ) × ∀ i : ι, ℙ ℝ (Fin (n i + 1) → ℝ))}
    (hUo : IsOpen U) (hUs : IsMixedSemialgebraic U) :
    IsMixedNashOn id U := by
  refine ⟨hUo, isMixedSemialgebraicOn_id hUs, continuousOn_id, fun x _ I₁ I₂ hx₁ hx₂ ↦ ?_⟩
  have hsrc : multiprojectiveAffineChart (K := ℝ) I₁ x.2 ∈
      ((multiprojectiveAffineChart (K := ℝ) I₁).symm.trans
        (multiprojectiveAffineChart (K := ℝ) I₂)).source := by
    rw [PartialEquiv.trans_source, PartialEquiv.symm_source, multiprojectiveAffineChart_target,
      multiprojectiveAffineChart_source, mem_inter_iff, mem_preimage,
      (multiprojectiveAffineChart (K := ℝ) I₁).left_inv
        (by rw [multiprojectiveAffineChart_source]; exact mem_mixedAffineOpen.1 hx₁)]
    exact ⟨trivial, mem_mixedAffineOpen.1 hx₂⟩
  let projInr : ((σ ⊕ Σ i, Fin (n i)) → ℝ) → ((Σ i, Fin (n i)) → ℝ) :=
    fun z ↦ z ∘ Sum.inr
  have hproj_pt : projInr (mixedAffineChart σ I₁ x) =
      multiprojectiveAffineChart (K := ℝ) I₁ x.2 :=
    funext fun q ↦ by simp [projInr]
  have hproj_an : AnalyticAt ℝ projInr (mixedAffineChart σ I₁ x) :=
    AnalyticAt.pi fun q ↦ by
      simpa [projInr] using analyticAt_pi_iff.1 analyticAt_id (Sum.inr q)
  refine AnalyticAt.pi fun
    | .inl a => by
        simpa [Function.comp_def] using
          analyticAt_pi_iff.1 (analyticAt_id (z := mixedAffineChart σ I₁ x)) (Sum.inl a)
    | .inr q => ?_
  have hq := (isNashAt_multiprojectiveAffineChart_symm_trans I₁ I₂ hsrc q).analyticAt
  rw [← hproj_pt] at hq
  simpa [projInr, Function.comp_def, PartialEquiv.trans_apply] using hq.comp hproj_an

/-- The identity map on a real mixed space is a global Nash map. -/
@[simp]
theorem isMixedNashMap_id :
    IsMixedNashMap
      (id : ((σ → ℝ) × ∀ i : ι, ℙ ℝ (Fin (n i + 1) → ℝ)) →
        ((σ → ℝ) × ∀ i : ι, ℙ ℝ (Fin (n i + 1) → ℝ))) :=
  isMixedNashOn_univ.1 (isMixedNashOn_id isOpen_univ isMixedSemialgebraic_univ)

/-- The identity map on a real multiprojective space is a global Nash map. -/
@[simp]
theorem isMultiprojectiveNashMap_id :
    IsMultiprojectiveNashMap
      (id : (∀ i : ι, ℙ ℝ (Fin (n i + 1) → ℝ)) → ∀ i : ι, ℙ ℝ (Fin (n i + 1) → ℝ)) := by
  refine (isMixedNashMap_isEmpty_prod_iff (σ₁ := Empty) (σ₂ := Empty)).1 ?_
  have hid : (fun xp : (Empty → ℝ) × ∀ i : ι, ℙ ℝ (Fin (n i + 1) → ℝ) ↦
      ((isEmptyElim : Empty → ℝ), id xp.2)) = id :=
    funext fun ⟨_, _⟩ ↦ Prod.ext (Subsingleton.elim _ _) rfl
  rw [hid]
  exact isMixedNashMap_id

/-- Composing `TauCeti.IsMixedNashOn` maps on open domains preserves `TauCeti.IsMixedNashOn`. -/
theorem IsMixedNashOn.comp
    {g : ((σ₂ → ℝ) × ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ)) →
      ((σ₃ → ℝ) × ∀ l : ι₃, ℙ ℝ (Fin (n₃ l + 1) → ℝ))}
    {f : ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) →
      ((σ₂ → ℝ) × ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ))}
    {U : Set ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ))}
    {V : Set ((σ₂ → ℝ) × ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ))}
    (hg : IsMixedNashOn g V) (hf : IsMixedNashOn f U) (hUV : MapsTo f U V) :
    IsMixedNashOn (g ∘ f) U := by
  refine ⟨hf.isOpen, hg.isMixedSemialgebraicOn.comp hf.isMixedSemialgebraicOn hUV,
    hg.continuousOn.comp hf.continuousOn hUV, fun x hxU I₁ I₃ hx₁ hx₃ ↦ ?_⟩
  obtain ⟨I₂, hx₂⟩ := exists_mem_mixedAffineOpen (σ := σ₂) (f x)
  have hga := hg.analyticAt_chart (hUV hxU) hx₂ hx₃
  have hfa := hf.analyticAt_chart hxU hx₁ hx₂
  have hpt : (mixedAffineChart σ₂ I₂ ∘ f ∘ ⇑(mixedAffineChart σ₁ I₁).symm)
      (mixedAffineChart σ₁ I₁ x) = mixedAffineChart σ₂ I₂ (f x) := by
    simp only [Function.comp_apply]
    rw [(mixedAffineChart σ₁ I₁).left_inv (by rw [mixedAffineChart_source]; exact hx₁)]
  rw [← hpt] at hga
  refine (hga.comp hfa).congr ?_
  have hmem : mixedAffineChart σ₁ I₁ x ∈
      (mixedAffineChart σ₁ I₁).symm ⁻¹' (U ∩ f ⁻¹' mixedAffineOpen σ₂ I₂) := by
    simp only [mem_preimage, mem_inter_iff]
    rw [(mixedAffineChart σ₁ I₁).left_inv (by rw [mixedAffineChart_source]; exact hx₁)]
    exact ⟨hxU, hx₂⟩
  have hopen : IsOpen ((mixedAffineChart σ₁ I₁).symm ⁻¹' (U ∩ f ⁻¹' mixedAffineOpen σ₂ I₂)) :=
    (hf.continuousOn.isOpen_inter_preimage hf.isOpen (isOpen_mixedAffineOpen I₂)).preimage
      (continuous_mixedAffineChart_symm I₁)
  refine Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem) fun z ⟨_, hz₂⟩ ↦ ?_
  simp only [Function.comp_apply]
  rw [(mixedAffineChart σ₂ I₂).left_inv (by rw [mixedAffineChart_source]; exact hz₂)]

/-- Composing global real mixed Nash maps produces a global real mixed Nash map. -/
theorem IsMixedNashMap.comp
    {g : ((σ₂ → ℝ) × ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ)) →
      ((σ₃ → ℝ) × ∀ l : ι₃, ℙ ℝ (Fin (n₃ l + 1) → ℝ))}
    {f : ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) →
      ((σ₂ → ℝ) × ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ))}
    (hg : IsMixedNashMap g) (hf : IsMixedNashMap f) :
    IsMixedNashMap (g ∘ f) :=
  isMixedNashOn_univ.1 ((isMixedNashOn_univ.2 hg).comp (isMixedNashOn_univ.2 hf) (mapsTo_univ _ _))

/-- Composing global real multiprojective Nash maps produces a global real multiprojective Nash
map. -/
theorem IsMultiprojectiveNashMap.comp
    {g : (∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ)) → ∀ l : ι₃, ℙ ℝ (Fin (n₃ l + 1) → ℝ)}
    {f : (∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) → ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ)}
    (hg : IsMultiprojectiveNashMap g) (hf : IsMultiprojectiveNashMap f) :
    IsMultiprojectiveNashMap (g ∘ f) :=
  (isMixedNashMap_isEmpty_prod_iff (σ₁ := Empty) (σ₂ := Empty)).1 <|
    ((isMixedNashMap_isEmpty_prod_iff (σ₁ := Empty) (σ₂ := Empty)).2 hg).comp
      ((isMixedNashMap_isEmpty_prod_iff (σ₁ := Empty) (σ₂ := Empty)).2 hf)

end Calculus

end TauCeti
