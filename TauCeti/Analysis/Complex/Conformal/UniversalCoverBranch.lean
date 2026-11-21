/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Action
public import TauCeti.Analysis.Complex.Conformal.Continuation.Trans
public import TauCeti.Analysis.Complex.Conformal.Monodromy
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Topology.ContinuousMap.Compact

/-!
# The branch of a continuable germ on the universal cover

By `TauCeti.monodromy_theorem`, the terminal germ of any analytic continuation of `f₀` along a path
in `U ⊆ ℂ` from `z₀ ∈ U` depends only on its homotopy class in `U`, assembling into
`H.universalCoverBranch : TauCeti.UniversalCover z₀ → E` for any complex normed space `E`.

* `ContinuesInside.eventuallyEq_of_homotopic`, `ContinuesInside.universalCoverBranch`: homotopy
  invariance in `U` and the universal-cover branch, with intro/elim, basepoint, congruence, `trans`,
  algebra (`add`, `neg`, `sub`, `mul`, `pow`), `eval_apply`, `analyticOnNhd_univ_comp`, global
  comparison, and loop monodromy (`universalCoverBranch_inv_smul_of_loop`).
* `ContinuesInside.eventuallyEq_universalCoverBranch_of_isAnalyticContinuationAlong`,
  `ContinuesInside.continuous_universalCoverBranch`,
  `ContinuesInside.analyticOnNhd_universalCoverBranch_comp`,
  `ContinuesInside.eqOn_universalCoverBranch_comp_of_analyticOnNhd`: local cover characterization,
  continuity, analyticity, and `EqOn` principal-branch agreement of local determinations along
  continuous sections (see `TauCeti.AlgebraicTopology.UniversalCover.Section` for topological
  section existence and uniqueness).

## References

* L. Ahlfors, *Complex Analysis*, Ch. 8 §1.3; J. Oesterlé, *Polylogarithmes*, Astérisque 216, §2.
-/

public section

namespace TauCeti

open Filter Metric Set Topology unitInterval

namespace ContinuesInside

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Homotopy invariance of analytic continuation inside `U`.** -/
theorem eventuallyEq_of_homotopic {U : Set ℂ} {z₀ z : U} {f₀ : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) {γ δ : Path z₀ z} (hγδ : Path.Homotopic γ δ)
    {f g : I → ℂ → E} (hf : IsAnalyticContinuationAlong f (fun t => (γ t : ℂ)) univ)
    (hf0 : f 0 =ᶠ[𝓝 (z₀ : ℂ)] f₀) (hg : IsAnalyticContinuationAlong g (fun t => (δ t : ℂ)) univ)
    (hg0 : g 0 =ᶠ[𝓝 (z₀ : ℂ)] f₀) : f 1 =ᶠ[𝓝 (z : ℂ)] g 1 := by
  let e : E →L[ℂ] UniformSpace.Completion E := UniformSpace.Completion.toComplL; obtain ⟨K⟩ := hγδ
  let incl : C(U, ℂ) := ⟨Subtype.val, continuous_subtypeVal⟩
  let K' : (γ.map incl.continuous).Homotopy (δ.map incl.continuous) := K.map incl
  have hHe := H.analyticOnNhd_univ_comp (e.analyticOnNhd univ)
  have hKzero : ∀ t : I, K' (t, 0) = (z₀ : ℂ) := fun t => by simp [K', incl]
  choose F hF hF₀ using fun t : I => continuesAlong_iff_exists.1
    (hHe.continuesAlong (by fun_prop) (fun x => (K (t, x)).property) (hKzero t))
  have hF₀' : ∀ t : I, F t 0 =ᶠ[𝓝 (z₀ : ℂ)] e ∘ f₀ := fun t => by simpa [hKzero t] using hF₀ t
  have hmono := monodromy_theorem K' hF (fun t => (hF₀' t).trans (hF₀' 0).symm) 1
  have hKp : (fun x => K' (0, x)) = fun x => (γ x : ℂ) := funext fun x => by simp [K', incl]
  have hKq : (fun x => K' (1, x)) = fun x => (δ x : ℂ) := funext fun x => by simp [K', incl]
  have e₀ : e ∘ f 1 =ᶠ[𝓝 (z : ℂ)] F 0 1 := by
    rw [← γ.target]; exact (hf.analyticAt_comp fun _ _ => e.analyticAt _).eventuallyEq (hKp ▸ hF 0)
      isPreconnected_univ (mem_univ 0) (mem_univ 1)
      (by rw [γ.source]; exact (hf0.fun_comp e).trans (hF₀' 0).symm)
  have e₁ : e ∘ g 1 =ᶠ[𝓝 (z : ℂ)] F 1 1 := by
    rw [← δ.target]; exact (hg.analyticAt_comp fun _ _ => e.analyticAt _).eventuallyEq (hKq ▸ hF 1)
      isPreconnected_univ (mem_univ 0) (mem_univ 1)
      (by rw [δ.source]; exact (hg0.fun_comp e).trans (hF₀' 1).symm)
  exact ((e₀.trans hmono.symm).trans e₁.symm).mono fun _ hx =>
    UniformSpace.Completion.coe_injective E hx

/-- A germ continuing inside `U` from `z₀` continues along every `γ : Path z₀ z` in `U`. -/
theorem continuesAlong_path {U : Set ℂ} {z₀ z : U} {f₀ : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) (γ : Path z₀ z) : ContinuesAlong f₀ (fun t => (γ t : ℂ)) :=
  H.continuesAlong (continuous_subtypeVal.comp γ.continuous) (fun t => (γ t).property)
    (congrArg Subtype.val γ.source)

/-- **The universal-cover branch of a continuable germ** on `UniversalCover z₀`. -/
noncomputable def universalCoverBranch {U : Set ℂ} {z₀ : U} {f₀ : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) (p : UniversalCover z₀) : E :=
  Quotient.liftOn p.path
    (fun γ : Path z₀ p.proj =>
      (continuesAlong_iff_exists.1 (H.continuesAlong_path γ)).choose 1 (p.proj : ℂ))
    fun γ δ hγδ => by
      let hc₁ := continuesAlong_iff_exists.1 (H.continuesAlong_path γ)
      let hc₂ := continuesAlong_iff_exists.1 (H.continuesAlong_path δ)
      exact (H.eventuallyEq_of_homotopic hγδ hc₁.choose_spec.1
        (by simpa [γ.source] using hc₁.choose_spec.2) hc₂.choose_spec.1
        (by simpa [δ.source] using hc₂.choose_spec.2)).eq_of_nhds

/-- **Introduction/uniqueness rule for `universalCoverBranch`.** -/
theorem universalCoverBranch_eq_of_isAnalyticContinuationAlong {U : Set ℂ} {z₀ z : U} {f₀ : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) {γ : Path z₀ z} {f : I → ℂ → E}
    (hf : IsAnalyticContinuationAlong f (fun t => (γ t : ℂ)) univ) (hf0 : f 0 =ᶠ[𝓝 (z₀ : ℂ)] f₀) :
    H.universalCoverBranch ⟨z, Path.Homotopic.Quotient.mk γ⟩ = f 1 (z : ℂ) := by
  let hc := continuesAlong_iff_exists.1 (H.continuesAlong_path γ)
  have hc0 : hc.choose 0 =ᶠ[𝓝 (z₀ : ℂ)] f₀ := by simpa [γ.source] using hc.choose_spec.2
  have heq := hc.choose_spec.1.eventuallyEq hf isPreconnected_univ (mem_univ 0) (mem_univ 1)
    (by simpa [γ.source] using hc0.trans hf0.symm)
  rw [γ.target] at heq; exact heq.eq_of_nhds

/-- **Elimination rule for `universalCoverBranch`.** -/
theorem exists_isAnalyticContinuationAlong_universalCoverBranch {U : Set ℂ} {z₀ z : U} {f₀ : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) (γ : Path z₀ z) :
    ∃ f : I → ℂ → E, IsAnalyticContinuationAlong f (fun t => (γ t : ℂ)) univ ∧
      (f 0 =ᶠ[𝓝 (z₀ : ℂ)] f₀) ∧
      H.universalCoverBranch ⟨z, Path.Homotopic.Quotient.mk γ⟩ = f 1 (z : ℂ) := by
  obtain ⟨f, hf, hf0⟩ := continuesAlong_iff_exists.1 (H.continuesAlong_path γ)
  have hf0' : f 0 =ᶠ[𝓝 (z₀ : ℂ)] f₀ := by simpa [γ.source] using hf0
  exact ⟨f, hf, hf0', H.universalCoverBranch_eq_of_isAnalyticContinuationAlong hf hf0'⟩

/-- At the constant-path class over `z₀`, `universalCoverBranch` equals `f₀ z₀`. -/
@[simp] theorem universalCoverBranch_mk_refl {U : Set ℂ} {z₀ : U} {f₀ : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) :
    H.universalCoverBranch ⟨z₀, Path.Homotopic.Quotient.refl z₀⟩ = f₀ (z₀ : ℂ) := by
  rw [← Path.Homotopic.Quotient.mk_refl]
  exact H.universalCoverBranch_eq_of_isAnalyticContinuationAlong
    (.const (continuous_subtypeVal.comp (Path.refl z₀).continuous).continuousOn
      fun _ _ => H.analyticAt z₀.property) .rfl

/-- At `UniversalCover.basepointLift z₀`, `universalCoverBranch` equals `f₀ z₀`. -/
theorem universalCoverBranch_basepointLift {U : Set ℂ} {z₀ : U} {f₀ : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) :
    H.universalCoverBranch (UniversalCover.basepointLift z₀) = f₀ (z₀ : ℂ) := by simp

/-- Replacing `f₀` by an eventually equal germ at `z₀` leaves `universalCoverBranch` unchanged. -/
theorem universalCoverBranch_congr {U : Set ℂ} {z₀ : U} {f₀ g₀ : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) (hfg : f₀ =ᶠ[𝓝 (z₀ : ℂ)] g₀) :
    (H.congr hfg).universalCoverBranch = H.universalCoverBranch := by
  funext ⟨z, q⟩; induction q with | mk γ =>
    obtain ⟨f, hf, hf0, hval⟩ := H.exists_isAnalyticContinuationAlong_universalCoverBranch γ
    exact ((H.congr hfg).universalCoverBranch_eq_of_isAnalyticContinuationAlong hf
      (hf0.trans hfg)).trans hval.symm

/-- **Concatenation rule for `universalCoverBranch`.** -/
theorem universalCoverBranch_trans {U : Set ℂ} {z₀ z₁ z₂ : U} {f₀ : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) {γ : Path z₀ z₁} {δ : Path z₁ z₂} {f g : I → ℂ → E}
    (hf : IsAnalyticContinuationAlong f (fun t => (γ t : ℂ)) univ) (hf0 : f 0 =ᶠ[𝓝 (z₀ : ℂ)] f₀)
    (hg : IsAnalyticContinuationAlong g (fun t => (δ t : ℂ)) univ) (hg0 : g 0 =ᶠ[𝓝 (z₁ : ℂ)] f 1) :
    H.universalCoverBranch ⟨z₂, Path.Homotopic.Quotient.mk (γ.trans δ)⟩ = g 1 (z₂ : ℂ) := by
  have htr : IsAnalyticContinuationAlong (transFamily f g) (fun t => ((γ.trans δ) t : ℂ)) univ :=
    (hf.trans (p := γ.map continuous_subtypeVal) (q := δ.map continuous_subtypeVal) hg
      hg0.symm).congr_path fun _ _ => by rw [← Path.map_trans]; rfl
  simpa using H.universalCoverBranch_eq_of_isAnalyticContinuationAlong htr
    (transFamily_zero f g ▸ hf0)

/-- The universal-cover branch of `f₀ + g₀` is the sum of the universal-cover branches. -/
theorem universalCoverBranch_add {U : Set ℂ} {z₀ : U} {f₀ g₀ : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) (H' : ContinuesInside g₀ U (z₀ : ℂ)) :
    (H.add H').universalCoverBranch = H.universalCoverBranch + H'.universalCoverBranch := by
  funext ⟨z, q⟩; induction q with | mk γ =>
    obtain ⟨f, hf, hf0, hval⟩ := H.exists_isAnalyticContinuationAlong_universalCoverBranch γ
    obtain ⟨g, hg, hg0, hval'⟩ := H'.exists_isAnalyticContinuationAlong_universalCoverBranch γ
    exact ((H.add H').universalCoverBranch_eq_of_isAnalyticContinuationAlong (hf.add hg)
      (hf0.add hg0)).trans (by simp [hval, hval'])

/-- The universal-cover branch of `-f₀` is the negation of the universal-cover branch of `f₀`. -/
theorem universalCoverBranch_neg {U : Set ℂ} {z₀ : U} {f₀ : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) :
    H.neg.universalCoverBranch = -H.universalCoverBranch := by
  funext ⟨z, q⟩; induction q with | mk γ =>
    obtain ⟨f, hf, hf0, hval⟩ := H.exists_isAnalyticContinuationAlong_universalCoverBranch γ
    exact (H.neg.universalCoverBranch_eq_of_isAnalyticContinuationAlong hf.neg hf0.neg).trans
      (by simp [hval])

/-- The universal-cover branch of `f₀ - g₀` is the difference of the universal-cover branches. -/
theorem universalCoverBranch_sub {U : Set ℂ} {z₀ : U} {f₀ g₀ : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) (H' : ContinuesInside g₀ U (z₀ : ℂ)) :
    (H.sub H').universalCoverBranch = H.universalCoverBranch - H'.universalCoverBranch := by
  funext ⟨z, q⟩; induction q with | mk γ =>
    obtain ⟨f, hf, hf0, hval⟩ := H.exists_isAnalyticContinuationAlong_universalCoverBranch γ
    obtain ⟨g, hg, hg0, hval'⟩ := H'.exists_isAnalyticContinuationAlong_universalCoverBranch γ
    exact ((H.sub H').universalCoverBranch_eq_of_isAnalyticContinuationAlong (hf.sub hg)
      (hf0.sub hg0)).trans (by simp [hval, hval'])

section Algebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

/-- The universal-cover branch of `f₀ * g₀` is the product of the universal-cover branches. -/
theorem universalCoverBranch_mul {U : Set ℂ} {z₀ : U} {f₀ g₀ : ℂ → A}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) (H' : ContinuesInside g₀ U (z₀ : ℂ)) :
    (H.mul H').universalCoverBranch = H.universalCoverBranch * H'.universalCoverBranch := by
  funext ⟨z, q⟩; induction q with | mk γ =>
    obtain ⟨f, hf, hf0, hval⟩ := H.exists_isAnalyticContinuationAlong_universalCoverBranch γ
    obtain ⟨g, hg, hg0, hval'⟩ := H'.exists_isAnalyticContinuationAlong_universalCoverBranch γ
    exact ((H.mul H').universalCoverBranch_eq_of_isAnalyticContinuationAlong (hf.mul hg)
      (hf0.mul hg0)).trans (by simp [hval, hval'])

/-- The universal-cover branch of `f₀ ^ n` is the `n`-th power of the universal-cover branch. -/
theorem universalCoverBranch_pow {U : Set ℂ} {z₀ : U} {f₀ : ℂ → A}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) (n : ℕ) :
    (H.pow n).universalCoverBranch = H.universalCoverBranch ^ n := by
  funext ⟨z, q⟩; induction q with | mk γ =>
    obtain ⟨f, hf, hf0, hval⟩ := H.exists_isAnalyticContinuationAlong_universalCoverBranch γ
    exact ((H.pow n).universalCoverBranch_eq_of_isAnalyticContinuationAlong (hf.pow n)
      (hf0.pow_const n)).trans (by simp [hval])

end Algebra

/-- Coordinate `i` of `H.universalCoverBranch` is the universal-cover branch of `H.eval i`. -/
theorem universalCoverBranch_eval_apply {ι : Type*} [Fintype ι] {F : ι → Type*}
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℂ (F i)] {U : Set ℂ} {z₀ : U}
    {f₀ : ℂ → ∀ i, F i} (H : ContinuesInside f₀ U (z₀ : ℂ)) (i : ι) (p : UniversalCover z₀) :
    (H.eval i).universalCoverBranch p = H.universalCoverBranch p i := by
  rcases p with ⟨z, q⟩; induction q with | mk γ =>
    obtain ⟨f, hf, hf0, hval⟩ := H.exists_isAnalyticContinuationAlong_universalCoverBranch γ
    rw [hval]; exact (H.eval i).universalCoverBranch_eq_of_isAnalyticContinuationAlong (hf.eval i)
      (hf0.mono fun _ hz => congrFun hz i)

/-- **Naturality of `universalCoverBranch` under entire post-composition.** -/
theorem universalCoverBranch_analyticOnNhd_univ_comp {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] {U : Set ℂ} {z₀ : U} {f₀ : ℂ → E} (H : ContinuesInside f₀ U (z₀ : ℂ))
    {Φ : E → F} (hΦ : AnalyticOnNhd ℂ Φ univ) (p : UniversalCover z₀) :
    (H.analyticOnNhd_univ_comp hΦ).universalCoverBranch p = Φ (H.universalCoverBranch p) := by
  rcases p with ⟨z, q⟩; induction q with | mk γ =>
    obtain ⟨f, hf, hf0, hval⟩ := H.exists_isAnalyticContinuationAlong_universalCoverBranch γ
    rw [hval]
    exact (H.analyticOnNhd_univ_comp hΦ).universalCoverBranch_eq_of_isAnalyticContinuationAlong
      (hf.analyticAt_comp fun _ _ => hΦ _ (mem_univ _)) (hf0.fun_comp Φ)

/-- **Comparison with a single-valued function analytic along a path.** -/
theorem universalCoverBranch_eq_of_analyticAt {U : Set ℂ} {z₀ z : U} {f₀ : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) (γ : Path z₀ z) {F : ℂ → E}
    (hF : ∀ t, AnalyticAt ℂ F (γ t)) (hF0 : F =ᶠ[𝓝 (z₀ : ℂ)] f₀) :
    H.universalCoverBranch ⟨z, Path.Homotopic.Quotient.mk γ⟩ = F (z : ℂ) :=
  H.universalCoverBranch_eq_of_isAnalyticContinuationAlong
    (.const (continuous_subtypeVal.comp γ.continuous).continuousOn fun t _ => hF t) hF0

/-- **Comparison with a single-valued function analytic throughout `U`.** -/
theorem universalCoverBranch_eq_of_analyticOnNhd {U : Set ℂ} {z₀ : U} {f₀ F : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) (hF : AnalyticOnNhd ℂ F U) (hF0 : F =ᶠ[𝓝 (z₀ : ℂ)] f₀)
    (p : UniversalCover z₀) : H.universalCoverBranch p = F (p.proj : ℂ) := by
  rcases p with ⟨z, q⟩; induction q with
  | mk γ => exact H.universalCoverBranch_eq_of_analyticAt γ (fun t => hF _ (γ t).property) hF0

/-- **Monodromy along a single loop.** -/
theorem universalCoverBranch_inv_smul_of_loop {U : Set ℂ} {z₀ : U} {f₀ : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) {γ : Path z₀ z₀} {f : I → ℂ → E}
    (hf : IsAnalyticContinuationAlong f (fun t => (γ t : ℂ)) univ) (hf0 : f 0 =ᶠ[𝓝 (z₀ : ℂ)] f₀)
    {Φ : E → E} (hΦ : AnalyticOnNhd ℂ Φ univ) (hf1 : f 1 =ᶠ[𝓝 (z₀ : ℂ)] Φ ∘ f₀)
    (p : UniversalCover z₀) :
    H.universalCoverBranch ((FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))⁻¹ • p) =
      Φ (H.universalCoverBranch p) := by
  rcases p with ⟨z, q⟩; induction q with | mk δ =>
    obtain ⟨g, hg, hg0, hval⟩ := H.exists_isAnalyticContinuationAlong_universalCoverBranch δ
    rw [UniversalCover.inv_smul_mk, FundamentalGroup.toPath_fromPath,
      ← Path.Homotopic.Quotient.mk_trans, hval]
    exact H.universalCoverBranch_trans hf hf0 (hg.analyticAt_comp fun _ _ => hΦ _ (mem_univ _))
      ((hg0.fun_comp Φ).trans hf1.symm)

end General

private def germSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set ℂ} (z₀ : U)
    (f₀ : ℂ → E) (w : ℂ) (ρ₀ : ℝ) (G : ℂ → E) : Set (UniversalCover z₀) :=
  {q | (q.proj : ℂ) ∈ ball w ρ₀ ∧
    ∀ (δ : Path z₀ q.proj) (g : I → ℂ → E), Path.Homotopic.Quotient.mk δ = q.path →
      IsAnalyticContinuationAlong g (fun t => (δ t : ℂ)) univ →
      (g 0 =ᶠ[𝓝 (z₀ : ℂ)] f₀) → g 1 =ᶠ[𝓝 (q.proj : ℂ)] G}

private theorem isOpen_germSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {U : Set ℂ} {z₀ : U} {f₀ : ℂ → E} (H : ContinuesInside f₀ U (z₀ : ℂ))
    {w : ℂ} {ρ₀ : ℝ} {G : ℂ → E} (hGan : AnalyticOnNhd ℂ G (ball w ρ₀)) :
    IsOpen (germSet z₀ f₀ w ρ₀ G) := by
  rw [← (UniversalCover.isQuotientMap_ofBasedPath z₀).isOpen_preimage, isOpen_iff_forall_mem_open]
  intro α hα
  simp only [mem_preimage, UniversalCover.ofBasedPath_def, germSet, Set.mem_ofPred_eq] at hα
  let z₁ : ℂ := (α 1 : ℂ)
  have hz₁ : z₁ ∈ ball w ρ₀ := by have h := hα.1; rwa [BasedPath.endpoint_def] at h
  obtain ⟨g, hg, hg0, -⟩ := H.exists_isAnalyticContinuationAlong_universalCoverBranch α.toPath
  have hgG : g 1 =ᶠ[𝓝 z₁] G := by
    have h := hα.2 α.toPath g rfl hg hg0; rwa [BasedPath.endpoint_def] at h
  obtain ⟨ρ₁, hρ₁, K, hKg, hKcont⟩ :=
    hg.exists_isAnalyticContinuationAlong_of_dist_lt isCompact_univ
  have hKG : K 1 =ᶠ[𝓝 z₁] G := (hKg 1 (mem_univ 1)).trans hgG
  obtain ⟨ρ₂, hρ₂, hρ₂eq⟩ := Metric.eventually_nhds_iff.mp
    (eventually_eventuallyEq_iff_of_analyticAt ((hGan z₁ hz₁).congr hKG.symm) (hGan z₁ hz₁))
  let r := min ρ₁ (min ρ₂ (ρ₀ - dist z₁ w))
  have hr : 0 < r := lt_min hρ₁ (lt_min hρ₂ (sub_pos.mpr (mem_ball.mp hz₁)))
  refine ⟨Subtype.val ⁻¹' Metric.ball α.val r, fun β hβ => ?_,
    Metric.isOpen_ball.preimage continuous_subtypeVal, Metric.mem_ball_self hr⟩
  simp only [mem_preimage, UniversalCover.ofBasedPath_def, germSet, Set.mem_ofPred_eq]
  have hβ_le : ∀ t : I, dist (β t : ℂ) (α t : ℂ) < r := fun t =>
    lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist (f := β.val) (g := α.val) t)
      (Metric.mem_ball.mp hβ)
  have hr_le : r ≤ ρ₀ - dist z₁ w := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨?_, fun δ g' hδ hg' hg'0 => ?_⟩
  · rw [BasedPath.endpoint_def]
    exact mem_ball.mpr (by linarith [dist_triangle (β 1 : ℂ) z₁ w, hr_le, hβ_le 1])
  · have hKβ : IsAnalyticContinuationAlong K (fun t => (β.toPath t : ℂ)) univ :=
      hKcont _ (continuous_subtypeVal.comp β.toPath.continuous).continuousOn
        fun t _ => lt_of_lt_of_le (hβ_le t) (min_le_left _ _)
    have hK0 : K 0 =ᶠ[𝓝 (z₀ : ℂ)] f₀ :=
      (by simpa [α.toPath.source] using hKg 0 (mem_univ 0) : K 0 =ᶠ[𝓝 (z₀ : ℂ)] g 0).trans hg0
    have hK1G : K 1 =ᶠ[𝓝 (β.endpoint : ℂ)] G := by
      rw [BasedPath.endpoint_def]
      exact (hρ₂eq (lt_of_lt_of_le (hβ_le 1) ((min_le_right _ _).trans (min_le_left _ _)))).mpr hKG
    exact (H.eventuallyEq_of_homotopic (Path.Homotopic.Quotient.exact hδ) hg' hg'0 hKβ hK0).trans
      hK1G

private theorem exists_isOpen_universalCoverBranch_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {U : Set ℂ} {z₀ : U} {f₀ : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) (p : UniversalCover z₀) {γ : Path z₀ p.proj}
    (hγ : Path.Homotopic.Quotient.mk γ = p.path) {f : I → ℂ → E}
    (hf : IsAnalyticContinuationAlong f (fun t => (γ t : ℂ)) univ) (hf0 : f 0 =ᶠ[𝓝 (z₀ : ℂ)] f₀) :
    ∃ (S : Set (UniversalCover z₀)) (G : ℂ → E),
      IsOpen S ∧ p ∈ S ∧ AnalyticAt ℂ G (p.proj : ℂ) ∧ (G =ᶠ[𝓝 (p.proj : ℂ)] f 1) ∧
      ∀ q ∈ S, H.universalCoverBranch q = G (q.proj : ℂ) := by
  obtain ⟨ρ₀, hρ₀, F₀, hF₀an, hF₀eq, -⟩ := hf.exists_representatives isCompact_univ
  let w : ℂ := (p.proj : ℂ)
  have hw_eq : (γ 1 : ℂ) = w := congrArg Subtype.val γ.target
  have hGan : AnalyticOnNhd ℂ (F₀ 1) (ball w ρ₀) := hw_eq ▸ hF₀an 1 (mem_univ 1)
  have hGf : F₀ 1 =ᶠ[𝓝 w] f 1 := hw_eq ▸ hF₀eq 1 (mem_univ 1)
  refine ⟨germSet z₀ f₀ w ρ₀ (F₀ 1), F₀ 1, isOpen_germSet H hGan,
    ⟨mem_ball_self hρ₀, fun δ g hδ hg hg0 => (H.eventuallyEq_of_homotopic
      (Path.Homotopic.Quotient.exact (hδ.trans hγ.symm)) hg hg0 hf hf0).trans hGf.symm⟩,
    hGan w (mem_ball_self hρ₀), hGf, ?_⟩
  rintro ⟨z, qpath⟩ hq; induction qpath with | mk δ =>
    obtain ⟨g, hg, hg0, hbr⟩ := H.exists_isAnalyticContinuationAlong_universalCoverBranch δ
    exact hbr.trans (hq.2 δ g rfl hg hg0).eq_of_nhds

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Local characterization of `universalCoverBranch` on the cover.** Near `p : UniversalCover z₀`,
`H.universalCoverBranch` equals the terminal representative `f 1` of any analytic continuation along
a representing path `γ` of `p`, composed with the projection `UniversalCover.proj`. -/
theorem eventuallyEq_universalCoverBranch_of_isAnalyticContinuationAlong {U : Set ℂ} {z₀ : U}
    {f₀ : ℂ → E} (H : ContinuesInside f₀ U (z₀ : ℂ)) (p : UniversalCover z₀) {γ : Path z₀ p.proj}
    (hγ : Path.Homotopic.Quotient.mk γ = p.path) {f : I → ℂ → E}
    (hf : IsAnalyticContinuationAlong f (fun t => (γ t : ℂ)) univ) (hf0 : f 0 =ᶠ[𝓝 (z₀ : ℂ)] f₀) :
    H.universalCoverBranch =ᶠ[𝓝 p] fun q => f 1 (q.proj : ℂ) := by
  let e : E →L[ℂ] UniformSpace.Completion E := UniformSpace.Completion.toComplL
  obtain ⟨S, G, hSo, hpS, -, hGf, hval⟩ := exists_isOpen_universalCoverBranch_eq
    (H.analyticOnNhd_univ_comp (e.analyticOnNhd univ)) p hγ
    (hf.analyticAt_comp fun _ _ => e.analyticAt _) (hf0.fun_comp e)
  have hproj : ContinuousAt (fun q : UniversalCover z₀ => (q.proj : ℂ)) p :=
    (continuous_subtypeVal.comp (UniversalCover.continuous_proj z₀)).continuousAt
  filter_upwards [hSo.mem_nhds hpS, hproj.eventually hGf] with q hqS hqG
  exact UniformSpace.Completion.coe_injective E <|
    (H.universalCoverBranch_analyticOnNhd_univ_comp (e.analyticOnNhd univ) q).symm.trans
      ((hval q hqS).trans hqG)

/-- **Continuity of the universal-cover branch.** -/
@[fun_prop] theorem continuous_universalCoverBranch {U : Set ℂ} {z₀ : U} {f₀ : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) : Continuous H.universalCoverBranch := by
  rw [continuous_iff_continuousAt]; intro p
  obtain ⟨γ, hγ⟩ := Path.Homotopic.Quotient.mk_surjective p.path
  obtain ⟨f, hf, hf0, -⟩ := H.exists_isAnalyticContinuationAlong_universalCoverBranch γ
  have hf1 : ContinuousAt (f 1) (p.proj : ℂ) :=
    ((congrArg Subtype.val γ.target).symm ▸ hf.analyticAt 1 (mem_univ 1)).continuousAt
  exact (hf1.comp (f := fun q : UniversalCover z₀ => (q.proj : ℂ))
    (continuous_subtypeVal.comp (UniversalCover.continuous_proj z₀)).continuousAt).congr
    (H.eventuallyEq_universalCoverBranch_of_isAnalyticContinuationAlong p hγ hf hf0).symm

/-- **Germ of a local determination along a continuous section.** -/
theorem eventuallyEq_universalCoverBranch_comp_of_continuousAt {U : Set ℂ} {z₀ : U} {f₀ : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) {sec : ℂ → UniversalCover z₀} {w : ℂ}
    (hsec : ContinuousAt sec w) (hproj : (fun z => ((sec z).proj : ℂ)) =ᶠ[𝓝 w] id)
    {γ : Path z₀ (sec w).proj} (hγ : Path.Homotopic.Quotient.mk γ = (sec w).path) {f : I → ℂ → E}
    (hf : IsAnalyticContinuationAlong f (fun t => (γ t : ℂ)) univ) (hf0 : f 0 =ᶠ[𝓝 (z₀ : ℂ)] f₀) :
    (H.universalCoverBranch ∘ sec) =ᶠ[𝓝 w] f 1 := by
  filter_upwards [hsec.eventually
    (H.eventuallyEq_universalCoverBranch_of_isAnalyticContinuationAlong (sec w) hγ hf hf0),
    hproj] with z hz hzp
  exact hz.trans (by simp [hzp])

/-- **Local determinations are complex analytic.** -/
theorem analyticAt_universalCoverBranch_comp_of_continuousAt {U : Set ℂ} {z₀ : U} {f₀ : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) {sec : ℂ → UniversalCover z₀} {w : ℂ}
    (hsec : ContinuousAt sec w) (hproj : (fun z => ((sec z).proj : ℂ)) =ᶠ[𝓝 w] id) :
    AnalyticAt ℂ (H.universalCoverBranch ∘ sec) w := by
  obtain ⟨γ, hγ⟩ := Path.Homotopic.Quotient.mk_surjective (sec w).path
  obtain ⟨f, hf, hf0, -⟩ := H.exists_isAnalyticContinuationAlong_universalCoverBranch γ
  have hw : (γ 1 : ℂ) = w := (congrArg Subtype.val γ.target).trans hproj.self_of_nhds
  exact (hw ▸ hf.analyticAt 1 (mem_univ 1)).congr
    (H.eventuallyEq_universalCoverBranch_comp_of_continuousAt hsec hproj hγ hf hf0).symm

/-- **Determinations over open sets are complex analytic.** -/
theorem analyticOnNhd_universalCoverBranch_comp {U : Set ℂ} {z₀ : U} {f₀ : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) {V : Set ℂ} (hVo : IsOpen V)
    {sec : ℂ → UniversalCover z₀} (hsec : ContinuousOn sec V)
    (hproj : ∀ z ∈ V, ((sec z).proj : ℂ) = z) :
    AnalyticOnNhd ℂ (H.universalCoverBranch ∘ sec) V := fun _ hw =>
  H.analyticAt_universalCoverBranch_comp_of_continuousAt (hsec.continuousAt (hVo.mem_nhds hw))
    (eventually_of_mem (hVo.mem_nhds hw) hproj)

/-- **Agreement with an analytic branch on a preconnected open set** through `basepointLift z₀`. -/
theorem eqOn_universalCoverBranch_comp_of_analyticOnNhd {U : Set ℂ} {z₀ : U} {f₀ F : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) {V : Set ℂ} (hVo : IsOpen V) (hVc : IsPreconnected V)
    (hz₀ : (z₀ : ℂ) ∈ V) {sec : ℂ → UniversalCover z₀} (hsec : ContinuousOn sec V)
    (hproj : ∀ z ∈ V, ((sec z).proj : ℂ) = z)
    (hsec0 : sec (z₀ : ℂ) = UniversalCover.basepointLift z₀) (hF : AnalyticOnNhd ℂ F V)
    (hF0 : F =ᶠ[𝓝 (z₀ : ℂ)] f₀) : EqOn (H.universalCoverBranch ∘ sec) F V := by
  have hev_base := H.eventuallyEq_universalCoverBranch_of_isAnalyticContinuationAlong
    ⟨z₀, Path.Homotopic.Quotient.refl z₀⟩ (Path.Homotopic.Quotient.mk_refl z₀)
    (.const (continuous_subtypeVal.comp (Path.refl z₀).continuous).continuousOn
      fun _ _ => hF _ hz₀) hF0
  have hsec_eq : sec (z₀ : ℂ) = ⟨z₀, Path.Homotopic.Quotient.refl z₀⟩ := by
    rw [hsec0, UniversalCover.basepointLift_coe]
  have hev : (H.universalCoverBranch ∘ sec) =ᶠ[𝓝 (z₀ : ℂ)] F := by
    filter_upwards [(hsec.continuousAt (hVo.mem_nhds hz₀)).eventually (hsec_eq ▸ hev_base),
      eventually_of_mem (hVo.mem_nhds hz₀) hproj] with z hz hzp
    exact hz.trans (by simp [hzp])
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (H.analyticOnNhd_universalCoverBranch_comp hVo hsec hproj) hF hVc hz₀ hev

end Normed
end ContinuesInside

end TauCeti
