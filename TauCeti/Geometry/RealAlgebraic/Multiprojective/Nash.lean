/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Multiprojective.Map
public import TauCeti.Geometry.RealAlgebraic.Nash.Basic
import TauCeti.Geometry.RealAlgebraic.Nash.Graph

/-!
# Real Nash maps between multiprojective and mixed spaces

Graph semialgebraicity (`TauCeti.IsMixedSemialgebraicOn`,
`TauCeti.IsMultiprojectiveSemialgebraicMap`) does not by itself imply continuity. Over `ℝ`, a *Nash
map* combines graph semialgebraicity, continuity on its domain, and real analyticity in every pair
of standard product affine charts.

Using the local Nash graph criterion (`TauCeti.forall_isNashAt_apply_iff_exists_isSemialgebraicOn`)
and the local-to-global semialgebraicity of real multiprojective sets
(`TauCeti.isMultiprojectiveSemialgebraic_iff_exists_semialgebraicAt`), we prove that a continuous
map between real multiprojective spaces is a global Nash map if and only if every local chart
coordinate is a Nash germ (`TauCeti.IsNashAt`).

## Main declarations

* `TauCeti.IsMixedNashOn`, `TauCeti.IsMixedNashMap`: Nash maps on open subsets and globally between
  real mixed affine–multiprojective spaces.
* `TauCeti.IsMultiprojectiveNashMap`: global Nash maps between real multiprojective spaces.
* `TauCeti.IsMixedNashOn.isNashAt_chart`, `TauCeti.IsMultiprojectiveNashMap.isNashAt_chart`:
  every local chart coordinate of a Nash map is a Nash germ.
* `TauCeti.isMultiprojectiveNashMap_iff_forall_isNashAt`: local-to-global characterization of
  `TauCeti.IsMultiprojectiveNashMap` via `TauCeti.IsNashAt`.
* `TauCeti.isNashAt_multiprojectiveAffineChart_symm_trans`, `TauCeti.isMultiprojectiveNashMap_id`,
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

/-- A map `f` between real mixed affine–multiprojective spaces is a *Nash map on* `U` if it is
mixed semialgebraic on `U`, continuous on `U`, and real-analytic in every pair of standard product
affine charts around every point of `U`. -/
def IsMixedNashOn
    (f : ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) →
      ((σ₂ → ℝ) × ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ)))
    (U : Set ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ))) : Prop :=
  IsMixedSemialgebraicOn f U ∧ ContinuousOn f U ∧
    ∀ x ∈ U, ∀ (I₁ : ∀ i : ι₁, Fin (n₁ i + 1)) (I₂ : ∀ j : ι₂, Fin (n₂ j + 1)),
      x ∈ mixedAffineOpen σ₁ I₁ → f x ∈ mixedAffineOpen σ₂ I₂ →
        AnalyticAt ℝ (mixedAffineChart σ₂ I₂ ∘ f ∘ ⇑(mixedAffineChart σ₁ I₁).symm)
          (mixedAffineChart σ₁ I₁ x)

/-- A global Nash map between real mixed affine–multiprojective spaces. -/
def IsMixedNashMap
    (f : ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) →
      ((σ₂ → ℝ) × ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ))) : Prop :=
  IsMixedNashOn f univ

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

@[simp]
theorem isMixedNashOn_univ
    {f : ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) →
      ((σ₂ → ℝ) × ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ))} :
    IsMixedNashOn f univ ↔ IsMixedNashMap f :=
  Iff.rfl

theorem IsMixedNashOn.isMixedSemialgebraicOn
    {f : ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) →
      ((σ₂ → ℝ) × ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ))}
    {U : Set ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ))}
    (hf : IsMixedNashOn f U) : IsMixedSemialgebraicOn f U :=
  hf.1

theorem IsMixedNashOn.continuousOn
    {f : ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) →
      ((σ₂ → ℝ) × ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ))}
    {U : Set ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ))}
    (hf : IsMixedNashOn f U) : ContinuousOn f U :=
  hf.2.1

theorem IsMultiprojectiveNashMap.isMultiprojectiveSemialgebraicMap
    {f : (∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) → ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ)}
    (hf : IsMultiprojectiveNashMap f) : IsMultiprojectiveSemialgebraicMap f :=
  hf.1

theorem IsMultiprojectiveNashMap.continuous
    {f : (∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) → ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ)}
    (hf : IsMultiprojectiveNashMap f) : Continuous f :=
  hf.2.1

/-- On an open domain `U`, every local chart coordinate of a `TauCeti.IsMixedNashOn` map is a Nash
germ (`TauCeti.IsNashAt`). -/
theorem IsMixedNashOn.isNashAt_chart
    {f : ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) →
      ((σ₂ → ℝ) × ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ))}
    {U : Set ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ))}
    (hf : IsMixedNashOn f U) (hUo : IsOpen U) {x : (σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)}
    (hxU : x ∈ U) {I₁ : ∀ i : ι₁, Fin (n₁ i + 1)} {I₂ : ∀ j : ι₂, Fin (n₂ j + 1)}
    (hx₁ : x ∈ mixedAffineOpen σ₁ I₁) (hx₂ : f x ∈ mixedAffineOpen σ₂ I₂)
    (c : σ₂ ⊕ Σ j, Fin (n₂ j)) :
    IsNashAt (fun z ↦ (mixedAffineChart σ₂ I₂ ∘ f ∘ ⇑(mixedAffineChart σ₁ I₁).symm) z c)
      (mixedAffineChart σ₁ I₁ x) := by
  refine forall_isNashAt_apply_iff_exists_isSemialgebraicOn.2
    ⟨hf.2.2 x hxU I₁ I₂ hx₁ hx₂,
      mixedAffineChart σ₁ I₁ '' (U ∩ mixedAffineOpen σ₁ I₁ ∩ f ⁻¹' mixedAffineOpen σ₂ I₂),
      ?_, ⟨x, ⟨⟨hxU, hx₁⟩, hx₂⟩, rfl⟩,
      (isMixedSemialgebraicOn_iff_forall_isSemialgebraicOn.1 hf.1) I₁ I₂⟩ c
  have hpre : mixedAffineChart σ₁ I₁ ''
      (U ∩ mixedAffineOpen σ₁ I₁ ∩ f ⁻¹' mixedAffineOpen σ₂ I₂) =
      (mixedAffineChart σ₁ I₁).symm ⁻¹' (U ∩ f ⁻¹' mixedAffineOpen σ₂ I₂) := by
    ext z
    simp only [mem_image, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨y, ⟨⟨hyU, hy₁⟩, hy₂⟩, rfl⟩
      have hl : (mixedAffineChart σ₁ I₁).symm (mixedAffineChart σ₁ I₁ y) = y :=
        (mixedAffineChart σ₁ I₁).left_inv (by rw [mixedAffineChart_source]; exact hy₁)
      rw [hl]
      exact ⟨hyU, hy₂⟩
    · rintro ⟨hzU, hz₂⟩
      exact ⟨(mixedAffineChart σ₁ I₁).symm z,
        ⟨⟨hzU, mixedAffineChart_symm_mem_affineOpen I₁ z⟩, hz₂⟩,
        (mixedAffineChart (K := ℝ) σ₁ I₁).right_inv (by rw [mixedAffineChart_target]; trivial)⟩
  rw [hpre]
  exact (hf.2.1.isOpen_inter_preimage hUo (isOpen_mixedAffineOpen I₂)).preimage
    (continuous_mixedAffineChart_symm I₁)

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
  let W : Set ((Σ i, Fin (n₁ i)) → ℝ) :=
    (multiprojectiveAffineChart (K := ℝ) I₁).symm ⁻¹' (f ⁻¹' multiprojectiveAffineOpen I₂)
  have hWo : IsOpen W := (isOpen_multiprojectiveAffineOpen I₂).preimage
    (hf.2.1.comp (continuous_multiprojectiveAffineChart_symm I₁))
  have hpW : multiprojectiveAffineChart (K := ℝ) I₁ p ∈ W := by
    simp only [W, mem_preimage]
    rwa [(multiprojectiveAffineChart (K := ℝ) I₁).left_inv
      (by rw [multiprojectiveAffineChart_source]; exact hp₁)]
  have hmixed := (isMixedSemialgebraicOn_empty_prod_iff (K := ℝ)).2
    (isMultiprojectiveSemialgebraicOn_univ.2 hf.1)
  have hchart := (isMixedSemialgebraicOn_iff_forall_isSemialgebraicOn.1 hmixed) I₁ I₂
  let e : (Σ i, Fin (n₁ i)) ≃ (Empty ⊕ Σ i, Fin (n₁ i)) := (Equiv.emptySum Empty _).symm
  let e₂ : (Σ j, Fin (n₂ j)) ≃ (Empty ⊕ Σ j, Fin (n₂ j)) := (Equiv.emptySum Empty _).symm
  have hW_eq : (fun z : (Σ i, Fin (n₁ i)) → ℝ ↦ z ∘ e.symm) ⁻¹'
      (mixedAffineChart Empty I₁ ''
        (((univ : Set (Empty → ℝ)) ×ˢ univ) ∩ mixedAffineOpen Empty I₁ ∩
          (fun xp : (Empty → ℝ) × _ ↦ (xp.1, f xp.2)) ⁻¹' mixedAffineOpen Empty I₂)) = W := by
    ext z
    simp only [W, mem_preimage, mem_image, mem_inter_iff, mem_prod, mem_univ, and_self,
      true_and, mem_mixedAffineOpen, Prod.exists]
    constructor
    · rintro ⟨_, p', ⟨hp'₁, hp'₂⟩, hzp'⟩
      have heq : multiprojectiveAffineChart (K := ℝ) I₁ p' = z :=
        funext fun k ↦ (mixedAffineChart_apply_inr I₁ _ k).symm.trans (congrFun hzp' (.inr k))
      rw [← heq, (multiprojectiveAffineChart (K := ℝ) I₁).left_inv
        (by rw [multiprojectiveAffineChart_source]; exact hp'₁)]
      exact hp'₂
    · intro hz
      refine ⟨Empty.elim, (multiprojectiveAffineChart (K := ℝ) I₁).symm z,
        ⟨multiprojectiveAffineChart_symm_mem_affineOpen I₁ z, hz⟩, ?_⟩
      ext (emp | k)
      · exact emp.elim
      · rw [mixedAffineChart_apply_inr]
        exact congrFun ((multiprojectiveAffineChart (K := ℝ) I₁).right_inv
          (by rw [multiprojectiveAffineChart_target]; trivial)) k
  have hW_semi : IsSemialgebraicOn
      (multiprojectiveAffineChart (K := ℝ) I₂ ∘ f ∘
        ⇑(multiprojectiveAffineChart (K := ℝ) I₁).symm) W := by
    have h₁ := (isSemialgebraicOn_preimage_comp_equiv_iff e.symm).2 hchart
    rw [hW_eq] at h₁
    exact ((isSemialgebraicOn_comp_equiv_iff e₂).2 h₁).congr fun z _ ↦ funext fun k ↦ by
      simp [e, e₂, Function.comp_def]
  exact forall_isNashAt_apply_iff_exists_isSemialgebraicOn.2
    ⟨hf.2.2 p I₁ I₂ hp₁ hp₂, W, hWo, hpW, hW_semi⟩ q

end Definitions

section LocalToGlobal

private def sumChartSigmaEquiv {ι₁ ι₂ : Type*} (n₁ : ι₁ → ℕ) (n₂ : ι₂ → ℕ) :
    ((Σ i, Fin (n₁ i)) ⊕ (Σ j, Fin (n₂ j))) ≃ Σ k : ι₁ ⊕ ι₂, Fin (Sum.elim n₁ n₂ k) where
  toFun := fun | .inl ⟨i, k⟩ => ⟨.inl i, k⟩ | .inr ⟨j, l⟩ => ⟨.inr j, l⟩
  invFun := fun | ⟨.inl i, k⟩ => .inl ⟨i, k⟩ | ⟨.inr j, l⟩ => .inr ⟨j, l⟩
  left_inv := fun | .inl ⟨_, _⟩ | .inr ⟨_, _⟩ => rfl
  right_inv := fun | ⟨.inl _, _⟩ | ⟨.inr _, _⟩ => rfl

private theorem multiprojectiveAffineChart_comp_sumChartSigmaEquiv_inl
    {ι₁ ι₂ : Type*} {n₁ : ι₁ → ℕ} {n₂ : ι₂ → ℕ}
    (I₁ : ∀ i : ι₁, Fin (n₁ i + 1)) (I₂ : ∀ j : ι₂, Fin (n₂ j + 1))
    (r : ∀ k : ι₁ ⊕ ι₂, ℙ ℝ (Fin (Sum.elim n₁ n₂ k + 1) → ℝ)) :
    multiprojectiveAffineChart (sumPiFinIndex I₁ I₂) r ∘ sumChartSigmaEquiv n₁ n₂ ∘ Sum.inl =
      multiprojectiveAffineChart I₁ ((sumPiProjectivizationEquiv n₁ n₂).symm r).1 :=
  funext fun ⟨i, k⟩ ↦ multiprojectiveAffineChart_sumPiFinIndex_inl I₁ I₂ r i k

private theorem multiprojectiveAffineChart_comp_sumChartSigmaEquiv_inr
    {ι₁ ι₂ : Type*} {n₁ : ι₁ → ℕ} {n₂ : ι₂ → ℕ}
    (I₁ : ∀ i : ι₁, Fin (n₁ i + 1)) (I₂ : ∀ j : ι₂, Fin (n₂ j + 1))
    (r : ∀ k : ι₁ ⊕ ι₂, ℙ ℝ (Fin (Sum.elim n₁ n₂ k + 1) → ℝ)) :
    multiprojectiveAffineChart (sumPiFinIndex I₁ I₂) r ∘ sumChartSigmaEquiv n₁ n₂ ∘ Sum.inr =
      multiprojectiveAffineChart I₂ ((sumPiProjectivizationEquiv n₁ n₂).symm r).2 :=
  funext fun ⟨j, l⟩ ↦ multiprojectiveAffineChart_sumPiFinIndex_inr I₁ I₂ r j l

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
    (hp₁ : ((sumPiProjectivizationEquiv n₁ n₂).symm r).1 ∈ multiprojectiveAffineOpen I₁)
    (hy₂ : ((sumPiProjectivizationEquiv n₁ n₂).symm r).2 ∈ multiprojectiveAffineOpen I₂)
    (hyf : ((sumPiProjectivizationEquiv n₁ n₂).symm r).2 =
      f ((sumPiProjectivizationEquiv n₁ n₂).symm r).1) :
    SemialgebraicAt
      (multiprojectiveAffineChart (sumPiFinIndex I₁ I₂) ''
        (((sumPiProjectivizationEquiv n₁ n₂).symm ⁻¹' univ.graphOn f) ∩
          multiprojectiveAffineOpen (sumPiFinIndex I₁ I₂)))
      (multiprojectiveAffineChart (sumPiFinIndex I₁ I₂) r) := by
  have := Fintype.ofFinite ι₂
  obtain ⟨_, W, hWo, hzW, hW_semi⟩ := forall_isNashAt_apply_iff_exists_isSemialgebraicOn.1
    (hf_nash ((sumPiProjectivizationEquiv n₁ n₂).symm r).1 I₁ I₂ hp₁ (hyf ▸ hy₂))
  let W₀ := (multiprojectiveAffineChart I₁).symm ⁻¹' (f ⁻¹' multiprojectiveAffineOpen I₂)
  have hNo : IsOpen ((fun w : (Σ k, Fin (Sum.elim n₁ n₂ k)) → ℝ ↦
      w ∘ sumChartSigmaEquiv n₁ n₂ ∘ Sum.inl) ⁻¹' (W ∩ W₀)) :=
    (hWo.inter ((isOpen_multiprojectiveAffineOpen I₂).preimage
      (hf_cont.comp (continuous_multiprojectiveAffineChart_symm I₁)))).preimage
      (continuous_pi fun q ↦ continuous_apply (sumChartSigmaEquiv n₁ n₂ (.inl q)))
  have hrN : multiprojectiveAffineChart (sumPiFinIndex I₁ I₂) r ∈
      (fun w ↦ w ∘ sumChartSigmaEquiv n₁ n₂ ∘ Sum.inl) ⁻¹' (W ∩ W₀) := by
    simp only [mem_preimage, multiprojectiveAffineChart_comp_sumChartSigmaEquiv_inl, mem_inter_iff,
      W₀]
    rw [(multiprojectiveAffineChart (K := ℝ) I₁).left_inv
      (by rw [multiprojectiveAffineChart_source]; exact hp₁)]
    exact ⟨hzW, hyf ▸ hy₂⟩
  refine ((hW_semi.graph.preimage_comp (sumChartSigmaEquiv n₁ n₂)).semialgebraicAt
      (multiprojectiveAffineChart (sumPiFinIndex I₁ I₂) r)).congr (Filter.eventuallyEqSet_iff.2
      (Filter.eventually_of_mem (hNo.mem_nhds hrN) fun w ⟨hwW, hwW₀⟩ ↦ ?_))
  rw [mem_preimage, mem_preimage_sumArrowEquivProdArrow_graphOn, mem_image]
  refine ⟨fun ⟨_, hfg⟩ ↦ ?_, fun ⟨r', ⟨hr'G, hr'I⟩, hwr'⟩ ↦ ?_⟩
  · let r' := sumPiProjectivizationEquiv n₁ n₂
      ((multiprojectiveAffineChart (K := ℝ) I₁).symm (w ∘ sumChartSigmaEquiv n₁ n₂ ∘ Sum.inl),
        f ((multiprojectiveAffineChart (K := ℝ) I₁).symm (w ∘ sumChartSigmaEquiv n₁ n₂ ∘ Sum.inl)))
    refine ⟨r', ⟨by rw [mem_preimage, Equiv.symm_apply_apply]; exact mem_graphOn.2 ⟨trivial, rfl⟩,
      by rw [mem_multiprojectiveAffineOpen_sumPiFinIndex, Equiv.symm_apply_apply]
         exact ⟨multiprojectiveAffineChart_symm_mem_affineOpen I₁ _, hwW₀⟩⟩, ?_⟩
    ext c
    obtain ⟨⟨i, k⟩ | ⟨j, l⟩, rfl⟩ := (sumChartSigmaEquiv n₁ n₂).surjective c
    · have h₁ := congrFun (multiprojectiveAffineChart_comp_sumChartSigmaEquiv_inl I₁ I₂ r') ⟨i, k⟩
      rw [Equiv.symm_apply_apply] at h₁
      exact h₁.trans (congrFun ((multiprojectiveAffineChart (K := ℝ) I₁).right_inv
        (by rw [multiprojectiveAffineChart_target]; trivial)) ⟨i, k⟩)
    · have h₂ := congrFun (multiprojectiveAffineChart_comp_sumChartSigmaEquiv_inr I₁ I₂ r') ⟨j, l⟩
      rw [Equiv.symm_apply_apply] at h₂
      exact h₂.trans (congrFun hfg ⟨j, l⟩)
  · subst hwr'
    obtain ⟨_, hfr'⟩ := mem_graphOn.1 hr'G
    obtain ⟨hr'₁, _⟩ := mem_multiprojectiveAffineOpen_sumPiFinIndex.1 hr'I
    have hsymm := (congrArg ⇑(multiprojectiveAffineChart (K := ℝ) I₁).symm
        (multiprojectiveAffineChart_comp_sumChartSigmaEquiv_inl I₁ I₂ r')).trans
      ((multiprojectiveAffineChart (K := ℝ) I₁).left_inv
        (by rw [multiprojectiveAffineChart_source]; exact hr'₁))
    refine ⟨hwW, ?_⟩
    rw [Function.comp_apply, Function.comp_apply, Function.comp_assoc, hsymm, hfr',
      Function.comp_assoc]
    exact (multiprojectiveAffineChart_comp_sumChartSigmaEquiv_inr I₁ I₂ r').symm

private theorem semialgebraicAt_graphOn_of_continuous_of_ne
    {ι₁ ι₂ : Type*} [Finite ι₁] [Finite ι₂] {n₁ : ι₁ → ℕ} {n₂ : ι₂ → ℕ}
    {f : (∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) → ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ)}
    (hf_cont : Continuous f)
    (r : ∀ k : ι₁ ⊕ ι₂, ℙ ℝ (Fin (Sum.elim n₁ n₂ k + 1) → ℝ))
    (I₁ : ∀ i : ι₁, Fin (n₁ i + 1)) (I₂ : ∀ j : ι₂, Fin (n₂ j + 1))
    (hp₁ : ((sumPiProjectivizationEquiv n₁ n₂).symm r).1 ∈ multiprojectiveAffineOpen I₁)
    (hy₂ : ((sumPiProjectivizationEquiv n₁ n₂).symm r).2 ∈ multiprojectiveAffineOpen I₂)
    (hyf : ((sumPiProjectivizationEquiv n₁ n₂).symm r).2 ≠
      f ((sumPiProjectivizationEquiv n₁ n₂).symm r).1) :
    SemialgebraicAt
      (multiprojectiveAffineChart (sumPiFinIndex I₁ I₂) ''
        (((sumPiProjectivizationEquiv n₁ n₂).symm ⁻¹' univ.graphOn f) ∩
          multiprojectiveAffineOpen (sumPiFinIndex I₁ I₂)))
      (multiprojectiveAffineChart (sumPiFinIndex I₁ I₂) r) := by
  let I := sumPiFinIndex I₁ I₂
  have hrI : r ∈ multiprojectiveAffineOpen I :=
    mem_multiprojectiveAffineOpen_sumPiFinIndex.2 ⟨hp₁, hy₂⟩
  have hcont_symm : Continuous (sumPiProjectivizationEquiv (K := ℝ) n₁ n₂).symm := by
    rw [funext sumPiProjectivizationEquiv_symm_apply]
    exact (continuous_pi fun i ↦ continuous_apply (Sum.inl i : ι₁ ⊕ ι₂)).prodMk
      (continuous_pi fun j ↦ continuous_apply (Sum.inr j : ι₁ ⊕ ι₂))
  have hclosed : IsClosed
      ((sumPiProjectivizationEquiv n₁ n₂).symm ⁻¹'
        (univ : Set (∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ))).graphOn f) := by
    have hG : (univ : Set (∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ))).graphOn f =
        {qy | f qy.1 = qy.2} := by ext; simp
    rw [hG]
    exact (isClosed_eq (hf_cont.comp continuous_fst) continuous_snd).preimage hcont_symm
  let N : Set ((Σ k : ι₁ ⊕ ι₂, Fin (Sum.elim n₁ n₂ k)) → ℝ) :=
    (multiprojectiveAffineChart (K := ℝ) I).symm ⁻¹'
      ((sumPiProjectivizationEquiv n₁ n₂).symm ⁻¹' univ.graphOn f)ᶜ
  have hNo : IsOpen N :=
    hclosed.isOpen_compl.preimage (continuous_multiprojectiveAffineChart_symm I)
  have hrN : multiprojectiveAffineChart I r ∈ N := by
    simp only [N, mem_preimage, mem_compl_iff]
    rw [(multiprojectiveAffineChart (K := ℝ) I).left_inv
      (by rw [multiprojectiveAffineChart_source]; exact hrI)]
    exact fun hrG ↦ hyf (mem_graphOn.1 hrG).2.symm
  refine semialgebraicAt_empty.congr
    (Filter.eventuallyEqSet_iff.2 (Filter.eventually_of_mem (hNo.mem_nhds hrN) fun w hw ↦ ?_))
  simp only [mem_empty_iff_false, false_iff, mem_image, not_exists, not_and]
  rintro r' ⟨hr'G, hr'I⟩ rfl
  have hw' : (multiprojectiveAffineChart (K := ℝ) I).symm
      (multiprojectiveAffineChart (K := ℝ) I r') ∉
      (sumPiProjectivizationEquiv n₁ n₂).symm ⁻¹' univ.graphOn f := hw
  rw [(multiprojectiveAffineChart (K := ℝ) I).left_inv
    (by rw [multiprojectiveAffineChart_source]; exact hr'I)] at hw'
  exact hw' hr'G

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
    (hp₁ : ((sumPiProjectivizationEquiv n₁ n₂).symm r).1 ∈ multiprojectiveAffineOpen I₁)
    (hy₂ : ((sumPiProjectivizationEquiv n₁ n₂).symm r).2 ∈ multiprojectiveAffineOpen I₂) :
    SemialgebraicAt
      (multiprojectiveAffineChart (sumPiFinIndex I₁ I₂) ''
        (((sumPiProjectivizationEquiv n₁ n₂).symm ⁻¹' univ.graphOn f) ∩
          multiprojectiveAffineOpen (sumPiFinIndex I₁ I₂)))
      (multiprojectiveAffineChart (sumPiFinIndex I₁ I₂) r) := by
  by_cases hyf : ((sumPiProjectivizationEquiv n₁ n₂).symm r).2 =
      f ((sumPiProjectivizationEquiv n₁ n₂).symm r).1
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
  refine ⟨fun hf ↦ ⟨hf.2.1, fun p I₁ I₂ hp₁ hp₂ q ↦ hf.isNashAt_chart hp₁ hp₂ q⟩,
    fun ⟨hf_cont, hf_nash⟩ ↦
      ⟨isMultiprojectiveSemialgebraicOn_univ.1
        (isMultiprojectiveSemialgebraicOn_def.2 ⟨isMultiprojectiveSemialgebraic_univ, ?_⟩),
        hf_cont,
        fun p I₁ I₂ hp₁ hp₂ ↦ AnalyticAt.pi fun q ↦ (hf_nash p I₁ I₂ hp₁ hp₂ q).analyticAt⟩⟩
  rw [isMultiprojectiveSemialgebraic_iff_exists_semialgebraicAt]
  intro r
  obtain ⟨I₁, hp₁⟩ :=
    exists_mem_multiprojectiveAffineOpen ((sumPiProjectivizationEquiv n₁ n₂).symm r).1
  obtain ⟨I₂, hy₂⟩ :=
    exists_mem_multiprojectiveAffineOpen ((sumPiProjectivizationEquiv n₁ n₂).symm r).2
  exact ⟨sumPiFinIndex I₁ I₂, mem_multiprojectiveAffineOpen_sumPiFinIndex.2 ⟨hp₁, hy₂⟩,
    semialgebraicAt_graphOn_of_forall_isNashAt hf_cont hf_nash r I₁ I₂ hp₁ hy₂⟩

end LocalToGlobal

section Calculus

variable {σ₁ σ₂ σ₃ ι ι₁ ι₂ ι₃ : Type*} [Fintype σ₁] [Fintype σ₂] [Fintype σ₃]
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

/-- The identity map on a real multiprojective space is a global Nash map. -/
@[simp]
theorem isMultiprojectiveNashMap_id :
    IsMultiprojectiveNashMap
      (id : (∀ i : ι, ℙ ℝ (Fin (n i + 1) → ℝ)) → ∀ i : ι, ℙ ℝ (Fin (n i + 1) → ℝ)) := by
  rw [isMultiprojectiveNashMap_iff_forall_isNashAt]
  refine ⟨continuous_id, fun p I₁ I₂ hp₁ hp₂ q ↦ ?_⟩
  have hsrc : multiprojectiveAffineChart (K := ℝ) I₁ p ∈
      ((multiprojectiveAffineChart (K := ℝ) I₁).symm.trans
        (multiprojectiveAffineChart (K := ℝ) I₂)).source := by
    rw [PartialEquiv.trans_source, PartialEquiv.symm_source, multiprojectiveAffineChart_target,
      multiprojectiveAffineChart_source, mem_inter_iff, mem_preimage,
      (multiprojectiveAffineChart (K := ℝ) I₁).left_inv
        (by rw [multiprojectiveAffineChart_source]; exact hp₁)]
    exact ⟨trivial, hp₂⟩
  exact isNashAt_multiprojectiveAffineChart_symm_trans I₁ I₂ hsrc q

/-- Composing `TauCeti.IsMixedNashOn` maps preserves the Nash property. -/
theorem IsMixedNashOn.comp
    {g : ((σ₂ → ℝ) × ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ)) →
      ((σ₃ → ℝ) × ∀ l : ι₃, ℙ ℝ (Fin (n₃ l + 1) → ℝ))}
    {f : ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) →
      ((σ₂ → ℝ) × ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ))}
    {U : Set ((σ₁ → ℝ) × ∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ))}
    {V : Set ((σ₂ → ℝ) × ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ))}
    (hg : IsMixedNashOn g V) (hf : IsMixedNashOn f U) (hUV : MapsTo f U V) (hUo : IsOpen U) :
    IsMixedNashOn (g ∘ f) U := by
  refine ⟨hg.1.comp hf.1 hUV, hg.2.1.comp hf.2.1 hUV, fun x hxU I₁ I₃ hx₁ hx₃ ↦ ?_⟩
  obtain ⟨I₂, hx₂⟩ := exists_mem_mixedAffineOpen (σ := σ₂) (f x)
  have hga := hg.2.2 (f x) (hUV hxU) I₂ I₃ hx₂ hx₃
  have hfa := hf.2.2 x hxU I₁ I₂ hx₁ hx₂
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
    (hf.2.1.isOpen_inter_preimage hUo (isOpen_mixedAffineOpen I₂)).preimage
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
  IsMixedNashOn.comp hg hf (mapsTo_univ _ _) isOpen_univ

/-- Composing global real multiprojective Nash maps produces a global real multiprojective Nash
map. -/
theorem IsMultiprojectiveNashMap.comp
    {g : (∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ)) → ∀ l : ι₃, ℙ ℝ (Fin (n₃ l + 1) → ℝ)}
    {f : (∀ i : ι₁, ℙ ℝ (Fin (n₁ i + 1) → ℝ)) → ∀ j : ι₂, ℙ ℝ (Fin (n₂ j + 1) → ℝ)}
    (hg : IsMultiprojectiveNashMap g) (hf : IsMultiprojectiveNashMap f) :
    IsMultiprojectiveNashMap (g ∘ f) := by
  refine ⟨hg.1.comp hf.1, hg.2.1.comp hf.2.1, fun p I₁ I₃ hp₁ hp₃ ↦ ?_⟩
  obtain ⟨I₂, hp₂⟩ := exists_mem_multiprojectiveAffineOpen (f p)
  have hga := hg.2.2 (f p) I₂ I₃ hp₂ hp₃
  have hfa := hf.2.2 p I₁ I₂ hp₁ hp₂
  have hpt : (multiprojectiveAffineChart (K := ℝ) I₂ ∘ f ∘
      ⇑(multiprojectiveAffineChart (K := ℝ) I₁).symm)
      (multiprojectiveAffineChart (K := ℝ) I₁ p) =
      multiprojectiveAffineChart (K := ℝ) I₂ (f p) := by
    simp only [Function.comp_apply]
    rw [(multiprojectiveAffineChart (K := ℝ) I₁).left_inv
      (by rw [multiprojectiveAffineChart_source]; exact hp₁)]
  rw [← hpt] at hga
  refine (hga.comp hfa).congr ?_
  have hopen : IsOpen ((multiprojectiveAffineChart (K := ℝ) I₁).symm ⁻¹'
      (f ⁻¹' multiprojectiveAffineOpen I₂)) :=
    (isOpen_multiprojectiveAffineOpen I₂).preimage
      (hf.2.1.comp (continuous_multiprojectiveAffineChart_symm I₁))
  have hmem : multiprojectiveAffineChart (K := ℝ) I₁ p ∈
      (multiprojectiveAffineChart (K := ℝ) I₁).symm ⁻¹' (f ⁻¹' multiprojectiveAffineOpen I₂) := by
    simp only [mem_preimage]
    rwa [(multiprojectiveAffineChart (K := ℝ) I₁).left_inv
      (by rw [multiprojectiveAffineChart_source]; exact hp₁)]
  refine Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem) fun z hz₂ ↦ ?_
  simp only [Function.comp_apply]
  rw [(multiprojectiveAffineChart (K := ℝ) I₂).left_inv
    (by rw [multiprojectiveAffineChart_source]; exact hz₂)]

end Calculus

end TauCeti
