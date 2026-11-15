/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Action
public import TauCeti.Analysis.Complex.Conformal.Continuation.Trans
public import TauCeti.Analysis.Complex.Conformal.Monodromy
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Topology.ContinuousMap.Compact

/-!
# The branch of a continuable germ on the universal cover

On a multiply connected domain `U ⊆ ℂ` — such as `ℂ \ {0}` for `Complex.log`, or `ℂ \ {0, 1}` for
the polylogarithm tower — loops around punctures carry nontrivial monodromy, so a germ `f₀` at
`z₀ ∈ U` satisfying `TauCeti.ContinuesInside f₀ U z₀` need not admit a single-valued analytic
extension on `U`. By `TauCeti.monodromy_theorem`, the terminal germ at `z ∈ U` depends only on the
endpoint-preserving homotopy class in `U` of the path from `z₀` to `z`, assembling into a
single-valued **universal-cover branch** `H.universalCoverBranch : TauCeti.UniversalCover z₀ → E`.

## Main definitions and results

* `TauCeti.ContinuesInside.eventuallyEq_of_homotopic` — two continuations of `f₀` along homotopic
  paths in `U` carry the same terminal germ.
* `TauCeti.ContinuesInside.continuesAlong_path`, `TauCeti.ContinuesInside.universalCoverBranch` —
  continuability along paths in `U` and the induced function on `UniversalCover z₀`, valued in any
  complex normed space `E` (via `UniformSpace.Completion E`).
* `TauCeti.ContinuesInside.universalCoverBranch_eq_of_isAnalyticContinuationAlong`,
  `TauCeti.ContinuesInside.exists_isAnalyticContinuationAlong_universalCoverBranch`,
  `TauCeti.ContinuesInside.universalCoverBranch_mk_refl`,
  `TauCeti.ContinuesInside.universalCoverBranch_basepointLift`,
  `TauCeti.ContinuesInside.universalCoverBranch_congr`,
  `TauCeti.ContinuesInside.universalCoverBranch_trans`,
  `TauCeti.ContinuesInside.universalCoverBranch_comp_analyticOnNhd_univ`,
  `TauCeti.ContinuesInside.universalCoverBranch_eq_of_analyticAt` — characterization, basepoint,
  congruence, concatenation, entire post-composition, and single-valued comparison rules.
* `TauCeti.ContinuesInside.universalCoverBranch_inv_smul_of_loop`,
  `TauCeti.ContinuesInside.universalCoverBranch_smul_of_closure` — deck-transformation monodromy
  along loops and fundamental-group equivariance from generators.
* `TauCeti.ContinuesInside.continuous_universalCoverBranch`,
  `TauCeti.ContinuesInside.eventuallyEq_universalCoverBranch_comp_of_continuousAt`,
  `TauCeti.ContinuesInside.analyticAt_universalCoverBranch_comp_of_continuousAt`,
  `TauCeti.ContinuesInside.analyticOnNhd_universalCoverBranch_comp` — continuity on
  `UniversalCover z₀` and complex analyticity of local determinations along continuous sections.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 8 §1.3.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. IX §§2–3.
* J. Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993), §2.
-/

public section

namespace TauCeti

open Filter Metric Set Topology unitInterval

namespace ContinuesInside

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Homotopy invariance of analytic continuation inside `U`.** Two continuations of one initial
germ along paths in `U` homotopic rel endpoints in `U` deliver the same terminal germ, without
assuming completeness of `E`. -/
theorem eventuallyEq_of_homotopic {U : Set ℂ} {z₀ z : U} {f₀ : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) {γ δ : Path z₀ z} (hγδ : Path.Homotopic γ δ)
    {f g : I → ℂ → E}
    (hf : IsAnalyticContinuationAlong f (fun t => (γ t : ℂ)) univ)
    (hf0 : f 0 =ᶠ[𝓝 (z₀ : ℂ)] f₀)
    (hg : IsAnalyticContinuationAlong g (fun t => (δ t : ℂ)) univ)
    (hg0 : g 0 =ᶠ[𝓝 (z₀ : ℂ)] f₀) :
    f 1 =ᶠ[𝓝 (z : ℂ)] g 1 := by
  let e : E →L[ℂ] UniformSpace.Completion E := UniformSpace.Completion.toComplL
  obtain ⟨K⟩ := hγδ
  let incl : C(U, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩
  let K' : (γ.map incl.continuous).Homotopy (δ.map incl.continuous) := K.map incl
  have hHe : ContinuesInside (e ∘ f₀) U (z₀ : ℂ) := H.comp_analyticOnNhd_univ (e.analyticOnNhd univ)
  have hKzero : ∀ t : I, K' (t, 0) = (z₀ : ℂ) := fun t => by simp [K', incl]
  have hcont : ∀ t : I, ContinuesAlong (e ∘ f₀) fun x => K' (t, x) := fun t =>
    hHe.continuesAlong (by fun_prop) (fun x => (K (t, x)).2) (hKzero t)
  choose F hF hF₀ using fun t => continuesAlong_iff_exists.1 (hcont t)
  have hF₀' : ∀ t : I, F t 0 =ᶠ[𝓝 (z₀ : ℂ)] e ∘ f₀ := fun t => by
    simpa only [hKzero t] using hF₀ t
  have hmono := monodromy_theorem K' hF (fun t => (hF₀' t).trans (hF₀' 0).symm) 1
  have hKp : (fun x => K' (0, x)) = fun x => (γ x : ℂ) := funext fun x => by simp [K', incl]
  have hKq : (fun x => K' (1, x)) = fun x => (δ x : ℂ) := funext fun x => by simp [K', incl]
  have he_f : IsAnalyticContinuationAlong (fun t => e ∘ f t) (fun t => (γ t : ℂ)) univ :=
    hf.comp_analyticAt fun _ _ => e.analyticAt _
  have he_g : IsAnalyticContinuationAlong (fun t => e ∘ g t) (fun t => (δ t : ℂ)) univ :=
    hg.comp_analyticAt fun _ _ => e.analyticAt _
  have e₀ : e ∘ f 1 =ᶠ[𝓝 (z : ℂ)] F 0 1 := by
    simpa [γ.target] using he_f.eventuallyEq (hKp ▸ hF 0) isPreconnected_univ (mem_univ 0)
      (mem_univ 1) (by simpa [γ.source] using (hf0.fun_comp e).trans (hF₀' 0).symm)
  have e₁ : e ∘ g 1 =ᶠ[𝓝 (z : ℂ)] F 1 1 := by
    simpa [δ.target] using he_g.eventuallyEq (hKq ▸ hF 1) isPreconnected_univ (mem_univ 0)
      (mem_univ 1) (by simpa [δ.source] using (hg0.fun_comp e).trans (hF₀' 1).symm)
  exact ((e₀.trans hmono.symm).trans e₁.symm).mono fun _ hx =>
    UniformSpace.Completion.coe_injective E hx

/-- A germ `f₀` that continues inside `U` from `z₀` continues along the underlying `ℂ`-path of
every path `γ : Path z₀ z` in `U`. -/
theorem continuesAlong_path {U : Set ℂ} {z₀ z : U} {f₀ : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) (γ : Path z₀ z) :
    ContinuesAlong f₀ (fun t => (γ t : ℂ)) :=
  H.continuesAlong (continuous_subtype_val.comp γ.continuous) (fun t => (γ t).2)
    (congrArg Subtype.val γ.source)

/-- **The universal-cover branch of a continuable germ.** Evaluates at `p.proj` the terminal germ
of any analytic continuation of `f₀` along a representative path of `p.path`. -/
noncomputable def universalCoverBranch {U : Set ℂ} {z₀ : U} {f₀ : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) (p : UniversalCover z₀) : E :=
  Quotient.liftOn p.path
    (fun γ : Path z₀ p.proj =>
      (continuesAlong_iff_exists.1 (H.continuesAlong_path γ)).choose 1 (p.proj : ℂ))
    fun γ δ hγδ => by
      let hc₁ := continuesAlong_iff_exists.1 (H.continuesAlong_path γ)
      let hc₂ := continuesAlong_iff_exists.1 (H.continuesAlong_path δ)
      have h1 : hc₁.choose 0 =ᶠ[𝓝 (z₀ : ℂ)] f₀ := by simpa [γ.source] using hc₁.choose_spec.2
      have h2 : hc₂.choose 0 =ᶠ[𝓝 (z₀ : ℂ)] f₀ := by simpa [δ.source] using hc₂.choose_spec.2
      exact (H.eventuallyEq_of_homotopic hγδ hc₁.choose_spec.1 h1 hc₂.choose_spec.1 h2).eq_of_nhds

/-- **Introduction/uniqueness rule for `universalCoverBranch`.** Any analytic continuation `f` of
`f₀` along `γ` evaluates at time `1` and endpoint `z` to `H.universalCoverBranch ⟨z, ⟦γ⟧⟩`. -/
theorem universalCoverBranch_eq_of_isAnalyticContinuationAlong {U : Set ℂ} {z₀ z : U} {f₀ : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) {γ : Path z₀ z} {f : I → ℂ → E}
    (hf : IsAnalyticContinuationAlong f (fun t => (γ t : ℂ)) univ)
    (hf0 : f 0 =ᶠ[𝓝 (z₀ : ℂ)] f₀) :
    H.universalCoverBranch ⟨z, Path.Homotopic.Quotient.mk γ⟩ = f 1 (z : ℂ) := by
  let hc := continuesAlong_iff_exists.1 (H.continuesAlong_path γ)
  have hc0 : hc.choose 0 =ᶠ[𝓝 (z₀ : ℂ)] f₀ := by simpa [γ.source] using hc.choose_spec.2
  have heq := hc.choose_spec.1.eventuallyEq hf isPreconnected_univ (mem_univ 0) (mem_univ 1)
    (by simpa [γ.source] using hc0.trans hf0.symm)
  rw [γ.target] at heq
  exact heq.eq_of_nhds

/-- **Elimination rule for `universalCoverBranch`.** Every `γ : Path z₀ z` in `U` admits an
analytic continuation of `f₀` whose terminal value at `z` is `H.universalCoverBranch ⟨z, ⟦γ⟧⟩`. -/
theorem exists_isAnalyticContinuationAlong_universalCoverBranch {U : Set ℂ} {z₀ z : U}
    {f₀ : ℂ → E} (H : ContinuesInside f₀ U (z₀ : ℂ)) (γ : Path z₀ z) :
    ∃ f : I → ℂ → E,
      IsAnalyticContinuationAlong f (fun t => (γ t : ℂ)) univ ∧
      (f 0 =ᶠ[𝓝 (z₀ : ℂ)] f₀) ∧
      H.universalCoverBranch ⟨z, Path.Homotopic.Quotient.mk γ⟩ = f 1 (z : ℂ) := by
  obtain ⟨f, hf, hf0⟩ := continuesAlong_iff_exists.1 (H.continuesAlong_path γ)
  have hf0' : f 0 =ᶠ[𝓝 (z₀ : ℂ)] f₀ := by simpa [γ.source] using hf0
  exact ⟨f, hf, hf0', H.universalCoverBranch_eq_of_isAnalyticContinuationAlong hf hf0'⟩

/-- At the constant-path class over `z₀`, `universalCoverBranch` equals `f₀ z₀`. -/
@[simp]
theorem universalCoverBranch_mk_refl {U : Set ℂ} {z₀ : U} {f₀ : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) :
    H.universalCoverBranch ⟨z₀, Path.Homotopic.Quotient.refl z₀⟩ = f₀ (z₀ : ℂ) := by
  rw [← Path.Homotopic.Quotient.mk_refl]
  exact H.universalCoverBranch_eq_of_isAnalyticContinuationAlong
    (.const (continuous_subtype_val.comp (Path.refl z₀).continuous).continuousOn
      fun _ _ => H.analyticAt z₀.2) .rfl

/-- At `UniversalCover.basepointLift z₀`, `universalCoverBranch` equals `f₀ z₀`. -/
theorem universalCoverBranch_basepointLift {U : Set ℂ} {z₀ : U} {f₀ : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) :
    H.universalCoverBranch (UniversalCover.basepointLift z₀ : UniversalCover z₀) = f₀ (z₀ : ℂ) := by
  simp

/-- Replacing `f₀` by an eventually equal germ at `z₀` leaves `universalCoverBranch` unchanged. -/
theorem universalCoverBranch_congr {U : Set ℂ} {z₀ : U} {f₀ g₀ : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) (hfg : f₀ =ᶠ[𝓝 (z₀ : ℂ)] g₀) :
    (H.congr hfg).universalCoverBranch = H.universalCoverBranch := by
  funext ⟨z, q⟩
  induction q with
  | mk γ =>
    obtain ⟨f, hf, hf0, hval⟩ := H.exists_isAnalyticContinuationAlong_universalCoverBranch γ
    exact ((H.congr hfg).universalCoverBranch_eq_of_isAnalyticContinuationAlong hf
      (hf0.trans hfg)).trans hval.symm

/-- **Concatenation rule for `universalCoverBranch`.** Continuing `f₀` along `γ` to `f 1` and then
along `δ` to `g 1` evaluates `universalCoverBranch` on `⟦γ.trans δ⟧` to `g 1 z₂`. -/
theorem universalCoverBranch_trans {U : Set ℂ} {z₀ z₁ z₂ : U} {f₀ : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) {γ : Path z₀ z₁} {δ : Path z₁ z₂} {f g : I → ℂ → E}
    (hf : IsAnalyticContinuationAlong f (fun t => (γ t : ℂ)) univ)
    (hf0 : f 0 =ᶠ[𝓝 (z₀ : ℂ)] f₀)
    (hg : IsAnalyticContinuationAlong g (fun t => (δ t : ℂ)) univ)
    (hg0 : g 0 =ᶠ[𝓝 (z₁ : ℂ)] f 1) :
    H.universalCoverBranch ⟨z₂, Path.Homotopic.Quotient.mk (γ.trans δ)⟩ = g 1 (z₂ : ℂ) := by
  let γ' : Path (z₀ : ℂ) (z₁ : ℂ) := γ.map continuous_subtype_val
  let δ' : Path (z₁ : ℂ) (z₂ : ℂ) := δ.map continuous_subtype_val
  have htr : IsAnalyticContinuationAlong (transFamily f g) (fun t => ((γ.trans δ) t : ℂ)) univ :=
    (hf.trans (p := γ') (q := δ') hg hg0.symm).congr_path fun t _ => by rw [← Path.map_trans]; rfl
  have htr0 : transFamily f g 0 =ᶠ[𝓝 (z₀ : ℂ)] f₀ := transFamily_zero f g ▸ hf0
  simpa using H.universalCoverBranch_eq_of_isAnalyticContinuationAlong htr htr0

/-- **Naturality of `universalCoverBranch` under entire post-composition.** -/
theorem universalCoverBranch_comp_analyticOnNhd_univ
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {U : Set ℂ} {z₀ : U} {f₀ : ℂ → E} (H : ContinuesInside f₀ U (z₀ : ℂ))
    {Φ : E → F} (hΦ : AnalyticOnNhd ℂ Φ univ) (p : UniversalCover z₀) :
    (H.comp_analyticOnNhd_univ hΦ).universalCoverBranch p = Φ (H.universalCoverBranch p) := by
  rcases p with ⟨z, q⟩
  induction q with
  | mk γ =>
    obtain ⟨f, hf, hf0, hval⟩ := H.exists_isAnalyticContinuationAlong_universalCoverBranch γ
    rw [hval]
    exact (H.comp_analyticOnNhd_univ hΦ).universalCoverBranch_eq_of_isAnalyticContinuationAlong
      (hf.comp_analyticAt fun _ _ => hΦ _ (mem_univ _)) (hf0.fun_comp Φ)

/-- **Comparison with a single-valued function analytic along a path.** -/
theorem universalCoverBranch_eq_of_analyticAt {U : Set ℂ} {z₀ z : U} {f₀ : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) (γ : Path z₀ z) {F : ℂ → E}
    (hF : ∀ t, AnalyticAt ℂ F (γ t)) (hF0 : F =ᶠ[𝓝 (z₀ : ℂ)] f₀) :
    H.universalCoverBranch ⟨z, Path.Homotopic.Quotient.mk γ⟩ = F (z : ℂ) :=
  H.universalCoverBranch_eq_of_isAnalyticContinuationAlong
    (.const (continuous_subtype_val.comp γ.continuous).continuousOn fun t _ => hF t) hF0

/-! ### Deck-transformation monodromy -/

/-- **Monodromy along a single loop.** If continuing `f₀` around a loop `γ` at `z₀` delivers
`Φ ∘ f₀` for an entire map `Φ : E → E`, then acting by `(fromPath ⟦γ⟧)⁻¹` applies `Φ`. -/
theorem universalCoverBranch_inv_smul_of_loop {U : Set ℂ} {z₀ : U} {f₀ : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) {γ : Path z₀ z₀} {f : I → ℂ → E}
    (hf : IsAnalyticContinuationAlong f (fun t => (γ t : ℂ)) univ)
    (hf0 : f 0 =ᶠ[𝓝 (z₀ : ℂ)] f₀) {Φ : E → E} (hΦ : AnalyticOnNhd ℂ Φ univ)
    (hf1 : f 1 =ᶠ[𝓝 (z₀ : ℂ)] Φ ∘ f₀) (p : UniversalCover z₀) :
    H.universalCoverBranch
      ((FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))⁻¹ • p) =
      Φ (H.universalCoverBranch p) := by
  rcases p with ⟨z, q⟩
  induction q with
  | mk δ =>
    obtain ⟨g, hg, hg0, hval⟩ := H.exists_isAnalyticContinuationAlong_universalCoverBranch δ
    rw [UniversalCover.inv_smul_mk, hval,
      show (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)).toPath.trans
        (Path.Homotopic.Quotient.mk δ) = Path.Homotopic.Quotient.mk (γ.trans δ) from
        (Path.Homotopic.Quotient.mk_trans γ δ).symm]
    exact H.universalCoverBranch_trans hf hf0 (hg.comp_analyticAt fun _ _ => hΦ _ (mem_univ _))
      ((hg0.fun_comp Φ).trans hf1.symm)

/-- **Equivariance from generators of the fundamental group.** -/
theorem universalCoverBranch_smul_of_closure {U : Set ℂ} {z₀ : U} {f₀ : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) {ρ : FundamentalGroup U z₀ →* Equiv.Perm E}
    {S : Set (FundamentalGroup U z₀)} (hS : Subgroup.closure S = ⊤)
    (hgen : ∀ g ∈ S, ∀ p, H.universalCoverBranch (g⁻¹ • p) = ρ g⁻¹ (H.universalCoverBranch p))
    (g : FundamentalGroup U z₀) (p : UniversalCover z₀) :
    H.universalCoverBranch (g • p) = ρ g (H.universalCoverBranch p) := by
  have hmem : g ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top g
  induction hmem using Subgroup.closure_induction generalizing p with
  | mem x hx =>
    have hinv := hgen x hx (x • p)
    rw [inv_smul_smul] at hinv
    simpa using (congrArg (ρ x) hinv).symm
  | one => simp
  | mul x y _ _ ihx ihy => rw [mul_smul, ihx, ihy, map_mul, Equiv.Perm.mul_apply]
  | inv x _ ih =>
    have h := ih (x⁻¹ • p)
    rw [smul_inv_smul] at h
    simpa using congrArg (ρ x⁻¹) h.symm

end General

/-! ### Local germ neighborhoods, continuity, and analyticity of local determinations -/

section LocalSheet

/-- Points of `UniversalCover z₀` over `ball w ρ₀` where every continuation delivers `G`. -/
private def germSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set ℂ} (z₀ : U) (f₀ : ℂ → E) (w : ℂ) (ρ₀ : ℝ) (G : ℂ → E) : Set (UniversalCover z₀) :=
  {q | (q.proj : ℂ) ∈ ball w ρ₀ ∧
    ∀ (δ : Path z₀ q.proj) (g : I → ℂ → E),
      Path.Homotopic.Quotient.mk δ = q.path →
      IsAnalyticContinuationAlong g (fun t => (δ t : ℂ)) univ →
      (g 0 =ᶠ[𝓝 (z₀ : ℂ)] f₀) → g 1 =ᶠ[𝓝 (q.proj : ℂ)] G}

private theorem isOpen_germSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {U : Set ℂ} {z₀ : U} {f₀ : ℂ → E} (H : ContinuesInside f₀ U (z₀ : ℂ))
    {w : ℂ} {ρ₀ : ℝ} {G : ℂ → E} (hGan : AnalyticOnNhd ℂ G (ball w ρ₀)) :
    IsOpen (germSet z₀ f₀ w ρ₀ G) := by
  rw [← (UniversalCover.isQuotientMap_ofBasedPath z₀).isOpen_preimage, isOpen_iff_forall_mem_open]
  intro α hα
  rw [mem_preimage, UniversalCover.ofBasedPath_def] at hα
  let z₁ : ℂ := (α 1 : ℂ)
  have hz₁ : z₁ ∈ ball w ρ₀ := hα.1
  obtain ⟨g, hg, hg0, -⟩ := H.exists_isAnalyticContinuationAlong_universalCoverBranch α.toPath
  have hgG : g 1 =ᶠ[𝓝 z₁] G := hα.2 α.toPath g rfl hg hg0
  obtain ⟨ρ₁, hρ₁, K, hKg, hKcont⟩ :=
    hg.exists_isAnalyticContinuationAlong_of_dist_lt isCompact_univ
  have hKG : K 1 =ᶠ[𝓝 z₁] G := (hKg 1 (mem_univ 1)).trans hgG
  have hKan : AnalyticAt ℂ (K 1) z₁ := (hGan z₁ hz₁).congr hKG.symm
  obtain ⟨ρ₂, hρ₂, hρ₂eq⟩ :=
    Metric.eventually_nhds_iff.mp (eventually_eventuallyEq_iff_of_analyticAt hKan (hGan z₁ hz₁))
  let r := min ρ₁ (min ρ₂ (ρ₀ - dist z₁ w))
  have hr : 0 < r := lt_min hρ₁ (lt_min hρ₂ (sub_pos.mpr (mem_ball.mp hz₁)))
  refine ⟨Subtype.val ⁻¹' Metric.ball α.1 r, fun β hβ => ?_,
    Metric.isOpen_ball.preimage continuous_subtype_val, Metric.mem_ball_self hr⟩
  rw [mem_preimage, UniversalCover.ofBasedPath_def]
  have hβ_le : ∀ t : I, dist (β t : ℂ) (α t : ℂ) < r := fun t =>
    lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist (f := β.1) (g := α.1) t)
      (Metric.mem_ball.mp hβ)
  have hβ1 := hβ_le 1
  have hr_le : r ≤ ρ₀ - dist z₁ w := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨show (β 1 : ℂ) ∈ ball w ρ₀ from mem_ball.mpr
      (by linarith [dist_triangle (β 1 : ℂ) z₁ w, hr_le, hβ1]),
    fun δ g' hδ hg' hg'0 => ?_⟩
  have hKβ : IsAnalyticContinuationAlong K (fun t => (β.toPath t : ℂ)) univ :=
    hKcont _ (continuous_subtype_val.comp β.toPath.continuous).continuousOn
      fun t _ => lt_of_lt_of_le (hβ_le t) (min_le_left _ _)
  have hK0 : K 0 =ᶠ[𝓝 (z₀ : ℂ)] f₀ :=
    (by simpa [α.toPath.source] using hKg 0 (mem_univ 0) : K 0 =ᶠ[𝓝 (z₀ : ℂ)] g 0).trans hg0
  have hK1G : K 1 =ᶠ[𝓝 (β 1 : ℂ)] G :=
    (hρ₂eq (lt_of_lt_of_le hβ1 ((min_le_right _ _).trans (min_le_left _ _)))).mpr hKG
  exact (H.eventuallyEq_of_homotopic (Path.Homotopic.Quotient.exact hδ) hg' hg'0 hKβ hK0).trans hK1G

private theorem exists_isOpen_universalCoverBranch_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {U : Set ℂ} {z₀ : U} {f₀ : ℂ → E} (H : ContinuesInside f₀ U (z₀ : ℂ))
    (p : UniversalCover z₀) {γ : Path z₀ p.proj} (hγ : Path.Homotopic.Quotient.mk γ = p.path)
    {f : I → ℂ → E} (hf : IsAnalyticContinuationAlong f (fun t => (γ t : ℂ)) univ)
    (hf0 : f 0 =ᶠ[𝓝 (z₀ : ℂ)] f₀) :
    ∃ (S : Set (UniversalCover z₀)) (G : ℂ → E),
      IsOpen S ∧ p ∈ S ∧ AnalyticAt ℂ G (p.proj : ℂ) ∧ (G =ᶠ[𝓝 (p.proj : ℂ)] f 1) ∧
      ∀ q ∈ S, H.universalCoverBranch q = G (q.proj : ℂ) := by
  obtain ⟨ρ₀, hρ₀, F₀, hF₀an, hF₀eq, -⟩ := hf.exists_representatives isCompact_univ
  let w : ℂ := (p.proj : ℂ)
  have hw_eq : (γ 1 : ℂ) = w := congrArg Subtype.val γ.target
  have hGan : AnalyticOnNhd ℂ (F₀ 1) (ball w ρ₀) := hw_eq ▸ hF₀an 1 (mem_univ 1)
  have hGf : F₀ 1 =ᶠ[𝓝 w] f 1 := hw_eq ▸ hF₀eq 1 (mem_univ 1)
  refine ⟨germSet z₀ f₀ w ρ₀ (F₀ 1), F₀ 1, isOpen_germSet H hGan,
    ⟨mem_ball_self hρ₀, fun δ g hδ hg hg0 =>
      (H.eventuallyEq_of_homotopic (Path.Homotopic.Quotient.exact (hδ.trans hγ.symm))
        hg hg0 hf hf0).trans hGf.symm⟩,
    hGan w (mem_ball_self hρ₀), hGf, ?_⟩
  rintro ⟨z, qpath⟩ hq
  induction qpath with
  | mk δ =>
    obtain ⟨g, hg, hg0, hbr⟩ := H.exists_isAnalyticContinuationAlong_universalCoverBranch δ
    exact hbr.trans (hq.2 δ g rfl hg hg0).eq_of_nhds

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Continuity of the universal-cover branch.** -/
theorem continuous_universalCoverBranch {U : Set ℂ} {z₀ : U} {f₀ : ℂ → E}
    (H : ContinuesInside f₀ U (z₀ : ℂ)) :
    Continuous H.universalCoverBranch := by
  let e : E →L[ℂ] UniformSpace.Completion E := UniformSpace.Completion.toComplL
  rw [(UniformSpace.Completion.isUniformInducing_coe E).isInducing.continuous_iff]
  have heq : ((↑) : E → UniformSpace.Completion E) ∘ H.universalCoverBranch =
      (H.comp_analyticOnNhd_univ (e.analyticOnNhd univ)).universalCoverBranch :=
    funext fun p => (H.universalCoverBranch_comp_analyticOnNhd_univ (e.analyticOnNhd univ) p).symm
  rw [heq, continuous_iff_continuousAt]
  intro p
  obtain ⟨γ, hγ⟩ := Path.Homotopic.Quotient.mk_surjective p.path
  let H' := H.comp_analyticOnNhd_univ (e.analyticOnNhd univ)
  obtain ⟨f, hf, hf0, -⟩ := H'.exists_isAnalyticContinuationAlong_universalCoverBranch γ
  obtain ⟨S, G, hSo, hpS, hGan, -, hval⟩ := exists_isOpen_universalCoverBranch_eq H' p hγ hf hf0
  have hcontG : ContinuousAt (fun q : UniversalCover z₀ => G (q.proj : ℂ)) p :=
    ContinuousAt.comp (g := G) (f := fun q : UniversalCover z₀ => (q.proj : ℂ)) hGan.continuousAt
      (continuous_subtype_val.comp (UniversalCover.continuous_proj z₀)).continuousAt
  exact hcontG.congr (eventually_of_mem (hSo.mem_nhds hpS) fun q hq => (hval q hq).symm)

/-- **Germ of a local determination along a continuous section.** -/
theorem eventuallyEq_universalCoverBranch_comp_of_continuousAt
    {U : Set ℂ} {z₀ : U} {f₀ : ℂ → E} (H : ContinuesInside f₀ U (z₀ : ℂ))
    {sec : ℂ → UniversalCover z₀} {w : ℂ} (hsec : ContinuousAt sec w)
    (hproj : (fun z => ((sec z).proj : ℂ)) =ᶠ[𝓝 w] id)
    {γ : Path z₀ (sec w).proj} (hγ : Path.Homotopic.Quotient.mk γ = (sec w).path)
    {f : I → ℂ → E} (hf : IsAnalyticContinuationAlong f (fun t => (γ t : ℂ)) univ)
    (hf0 : f 0 =ᶠ[𝓝 (z₀ : ℂ)] f₀) :
    (H.universalCoverBranch ∘ sec) =ᶠ[𝓝 w] f 1 := by
  let e : E →L[ℂ] UniformSpace.Completion E := UniformSpace.Completion.toComplL
  let H' := H.comp_analyticOnNhd_univ (e.analyticOnNhd univ)
  have hw : ((sec w).proj : ℂ) = w := hproj.self_of_nhds
  obtain ⟨S, G, hSo, hpS, -, hGf, hval⟩ := exists_isOpen_universalCoverBranch_eq H' (sec w) hγ
    (hf.comp_analyticAt fun _ _ => e.analyticAt _) (hf0.fun_comp e)
  rw [hw] at hGf
  filter_upwards [hsec.eventually (hSo.mem_nhds hpS), hproj, hGf] with z hzS hzproj hzG
  apply UniformSpace.Completion.coe_injective E
  have hcomp := H.universalCoverBranch_comp_analyticOnNhd_univ (e.analyticOnNhd univ) (sec z)
  exact hcomp.symm.trans ((hval (sec z) hzS).trans (by simpa [hzproj, e] using hzG))

/-- **Local determinations are complex analytic.** -/
theorem analyticAt_universalCoverBranch_comp_of_continuousAt
    {U : Set ℂ} {z₀ : U} {f₀ : ℂ → E} (H : ContinuesInside f₀ U (z₀ : ℂ))
    {sec : ℂ → UniversalCover z₀} {w : ℂ} (hsec : ContinuousAt sec w)
    (hproj : (fun z => ((sec z).proj : ℂ)) =ᶠ[𝓝 w] id) :
    AnalyticAt ℂ (H.universalCoverBranch ∘ sec) w := by
  obtain ⟨γ, hγ⟩ := Path.Homotopic.Quotient.mk_surjective (sec w).path
  obtain ⟨f, hf, hf0, -⟩ := H.exists_isAnalyticContinuationAlong_universalCoverBranch γ
  have hw : (γ 1 : ℂ) = w := (congrArg Subtype.val γ.target).trans hproj.self_of_nhds
  have han : AnalyticAt ℂ (f 1) w := hw ▸ hf.analyticAt 1 (mem_univ 1)
  exact han.congr
    (H.eventuallyEq_universalCoverBranch_comp_of_continuousAt hsec hproj hγ hf hf0).symm

/-- **Determinations over open sets are analytic.** -/
theorem analyticOnNhd_universalCoverBranch_comp
    {U : Set ℂ} {z₀ : U} {f₀ : ℂ → E} (H : ContinuesInside f₀ U (z₀ : ℂ))
    {V : Set ℂ} (hVo : IsOpen V) {sec : ℂ → UniversalCover z₀} (hsec : ContinuousOn sec V)
    (hproj : ∀ z ∈ V, ((sec z).proj : ℂ) = z) :
    AnalyticOnNhd ℂ (H.universalCoverBranch ∘ sec) V := fun _ hw =>
  H.analyticAt_universalCoverBranch_comp_of_continuousAt (hsec.continuousAt (hVo.mem_nhds hw))
    (eventually_of_mem (hVo.mem_nhds hw) hproj)

end Normed

end LocalSheet

end ContinuesInside

end TauCeti
