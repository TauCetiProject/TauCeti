/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Capacity.HoferZehnder
public import TauCeti.Geometry.Symplectic.Hamiltonian.AlmostExistence
import Mathlib.Geometry.Manifold.IntegralCurve.Transform
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Manifold.MFDeriv.Constancy
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone
import TauCeti.Topology.Homotopy.AddCircle

/-!
# Short closed characteristics on the levels of an energy function

Let `σ` be a nondegenerate two-form on a finite-dimensional manifold `M`, `W ⊆ M`, and
`F : M → ℝ` a smooth function whose sublevel set `{F ≤ b}` is compact and lies in the interiors of
`W` and of `M`. Let `a < b`, and assume that `F` takes a value below `a` somewhere and a value above
`b` somewhere in the interior of `W`; all results below rely on these assumptions. Consider the
Hamiltonians `μ ∘ F`, where `μ` is a smooth nonincreasing step from its maximum `v` on `(-∞, a]`
down to `0` on `[b, ∞)`. Since `X_{μ ∘ F} = μ'(F) X_F`, the function `F` is constant along the
orbits of `μ ∘ F`, and on the level `F⁻¹(s)` these orbits are those of `X_F` run at the constant
speed `μ'(s)`. A `T`-periodic orbit of `μ ∘ F` is therefore either constant or a closed orbit of
`X_F` on a level `s ∈ (a, b)`, of period `|μ'(s)| T`. If no level of `F` in `(a, b)` carries a
nonconstant periodic orbit of `X_F` of period at most `τ` whose loop is contractible in `W`, then
every `μ ∘ F` with `|μ'| ≤ τ` is `HZ°`-admissible for `W`
(`TauCeti.SmoothTwoForm.IsNondegenerate.isContractibleHZAdmissible_comp`). Such steps exist for
every `v < τ (b - a)` (`TauCeti.exists_contDiff_antitone_cutoff_abs_deriv_le`), so the
`π₁`-sensitive Hofer–Zehnder capacity of `W` is at least `τ (b - a)`
(`TauCeti.SmoothTwoForm.IsNondegenerate.ofReal_mul_sub_le_contractibleHZCapacity`).

Read the other way, this is the step of the Hofer–Zehnder and Struwe argument that turns
finiteness of the capacity into periodic orbits: if `c°_HZ(W) < τ (b - a)`, some level of `F`
in `(a, b)` carries a nonconstant periodic orbit of `X_F` of period at most `τ`, contractible in
`W` (`TauCeti.SmoothTwoForm.IsNondegenerate.exists_isMIntegralCurve_of_contractibleHZCapacity_lt`).
In particular, if `c°_HZ(W)` is finite, every interval of levels `(a, b)` satisfying the
assumptions above contains a level carrying a closed characteristic contractible in `W`
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_mem_Ioo_hasContractibleClosedCharacteristic`):
since subintervals of such an interval again satisfy these assumptions, closed characteristics
exist on a dense subset of the union of such intervals. Passing from a dense set of levels to
almost every level, as in the Hofer–Zehnder–Struwe theorem, additionally needs the monotonicity of
a capacity in the level, to bound the periods `τ` on shrinking intervals of levels, and a
compactness argument for the resulting orbits; neither is treated here.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.isContractibleHZAdmissible_comp`: in the absence of
  short contractible closed orbits on the levels in `(a, b)`, `μ ∘ F` is `HZ°`-admissible.
* `TauCeti.SmoothTwoForm.IsNondegenerate.ofReal_mul_sub_le_contractibleHZCapacity`: in the
  absence of short contractible closed orbits on the levels in `(a, b)`, the capacity is at least
  `τ (b - a)`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.exists_isMIntegralCurve_of_contractibleHZCapacity_lt`:
  if the capacity is less than `τ (b - a)`, a level in `(a, b)` carries a nonconstant contractible
  closed orbit of period at most `τ`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.exists_mem_Ioo_hasContractibleClosedCharacteristic`:
  finite capacity gives a closed characteristic on some level in every interval `(a, b)`
  satisfying the assumptions above.

## References

* H. Hofer, E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Sections 4.1 and 4.2.
* M. Struwe, *Existence of periodic solutions of Hamiltonian systems on almost every energy
  surface*, Bol. Soc. Brasil. Mat. (N.S.) 20 (1990), 49–58.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 6.3.
-/

public section

noncomputable section

open Function Set
open scoped ContDiff ENNReal Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [FiniteDimensional ℝ E] {σ : SmoothTwoForm I M} {W : Set M} {F : M → ℝ} {a b τ : ℝ}

/-- **Orbits of `φ ∘ F`.** A `T`-periodic orbit `γ` of `X_{φ ∘ F}` whose loop is contractible in
`W` is constant as soon as, writing `c = φ'(F (γ 0))`, every periodic orbit `γ'` of `X_F` through
`γ 0` of period at most `T |c|` whose loop is contractible in `W` is constant when `c ≠ 0`. Indeed
`F` is constant along `γ`, and along its level `X_{φ ∘ F} = c X_F`: if `c = 0` then `γ` is an
integral curve with zero derivative, hence constant, and otherwise `t ↦ γ (t / c)` is such an orbit
`γ'`. -/
private theorem IsNondegenerate.eq_of_isMIntegralCurve_comp (hσ : σ.IsNondegenerate)
    (hF : MDifferentiable I 𝓘(ℝ) F) {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ) {T : ℝ} (hT : 0 < T)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ (σ.hamiltonianVectorField (φ ∘ F)))
    {g : C(AddCircle T, W)} (hg : g.Nullhomotopic) (hgγ : ∀ t : ℝ, (g t : M) = γ t)
    (horb : deriv φ (F (γ 0)) ≠ 0 → ∀ (P : ℝ) (γ' : ℝ → M), 0 < P →
      P ≤ T * |deriv φ (F (γ 0))| → IsMIntegralCurve γ' (σ.hamiltonianVectorField F) →
      Periodic γ' P → γ' 0 = γ 0 →
      (∃ g' : C(AddCircle P, W), g'.Nullhomotopic ∧ ∀ t : ℝ, (g' t : M) = γ' t) →
      ∀ t, γ' t = γ' 0) :
    ∀ t, γ t = γ 0 := by
  set c := deriv φ (F (γ 0))
  have hX (x : M) :
      σ.hamiltonianVectorField (φ ∘ F) x = deriv φ (F x) • σ.hamiltonianVectorField F x :=
    hamiltonianVectorField_comp (hφ _) (hF x)
  -- `F` is constant along `γ`, since `dF(X_{φ ∘ F}) = φ'(F) dF(X_F) = 0`.
  have hlev (t : ℝ) : F (γ t) = F (γ 0) :=
    (hγ.isMIntegralCurveOn univ).apply_eq_of_mvfderiv_apply_eq_zero isOpen_univ
      isPreconnected_univ (fun u _ ↦ hF _) (fun u _ ↦ by
        rw [hX, map_smul,
          (hσ.isHamiltonianVectorField_hamiltonianVectorField F).mvfderiv_apply_self, smul_zero])
      (mem_univ 0) (mem_univ t)
  have hXγ (t : ℝ) :
      σ.hamiltonianVectorField (φ ∘ F) (γ t) = c • σ.hamiltonianVectorField F (γ t) := by
    rw [hX, hlev]
  by_cases hc : c = 0
  · exact fun t ↦ MDifferentiable.apply_eq_of_mfderiv_eq_zero (I := 𝓘(ℝ))
      (fun u ↦ (hγ u).mdifferentiableAt)
      (fun u ↦ by rw [(hγ u).mfderiv, hXγ, hc, zero_smul, ContinuousLinearMap.smulRight_zero]; rfl)
      t 0
  -- Otherwise `γ' t = γ (t / c)` is a periodic orbit of `X_F` with a contractible loop.
  obtain ⟨g', hg', hgg'⟩ := hg.exists_addCircle_comp_mul hT.ne' (inv_ne_zero hc)
  have hgγ' (t : ℝ) : (g' t : M) = γ (t * c⁻¹) := by rw [hgg', hgγ]
  have hγ' : IsMIntegralCurve (fun t ↦ γ (t * c⁻¹)) (σ.hamiltonianVectorField F) := fun t ↦ by
    have h : σ.hamiltonianVectorField F (γ (t * c⁻¹)) =
        c⁻¹ • σ.hamiltonianVectorField (φ ∘ F) (γ (t * c⁻¹)) := by
      rw [hXγ, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [h]
    exact hγ.comp_mul c⁻¹ t
  have hconst := horb hc (T / |c⁻¹|) (fun t ↦ γ (t * c⁻¹))
    (div_pos hT (abs_pos.2 (inv_ne_zero hc))) (by rw [abs_inv, div_inv_eq_mul]) hγ'
    (fun t ↦ by simp only [← hgγ', AddCircle.coe_add_period]) (by simp) ⟨g', hg', hgγ'⟩
  intro t
  simpa [mul_inv_cancel_right₀ hc] using hconst (t * c)

/-- **Admissibility of `μ ∘ F`.** Let `F` be smooth with `{F ≤ b}` compact and contained in the
interiors of `W` and of `M`, taking values below `a < b` somewhere and above `b` somewhere in the
interior of `W`. Let `μ ≥ 0` be smooth and nonincreasing, constant on `(-∞, a]` and zero on
`[b, ∞)`, with `|μ'| ≤ τ` everywhere and `μ' = 0` outside `(a, b)`. If no level `F⁻¹(s)`,
`s ∈ (a, b)`, carries a nonconstant `T`-periodic orbit of `X_F` with `T ≤ τ` whose loop is
contractible in `W`, then `μ ∘ F` is `HZ°`-admissible for `W`. -/
theorem IsNondegenerate.isContractibleHZAdmissible_comp (hσ : σ.IsNondegenerate)
    (hF : ContMDiff I 𝓘(ℝ) ∞ F) (hcpt : IsCompact {x | F x ≤ b})
    (hW : {x | F x ≤ b} ⊆ interior W) (hM : {x | F x ≤ b} ⊆ I.interior M)
    (ha : ∃ x, F x < a) (hb : ∃ x ∈ interior W, b < F x) {μ : ℝ → ℝ} (hμ : ContDiff ℝ ∞ μ)
    (hanti : Antitone μ) (hnn : ∀ r, 0 ≤ μ r) (hhigh : ∀ r, b ≤ r → μ r = 0)
    (hlow : ∀ r ≤ a, μ r = μ a) (habs : ∀ r, |deriv μ r| ≤ τ)
    (hzero : ∀ r ∉ Ioo a b, deriv μ r = 0)
    (horb : ∀ (T : ℝ) (γ : ℝ → M), 0 < T → T ≤ τ →
      IsMIntegralCurve γ (σ.hamiltonianVectorField F) → Periodic γ T → F (γ 0) ∈ Ioo a b →
      (∃ g : C(AddCircle T, W), g.Nullhomotopic ∧ ∀ t : ℝ, (g t : M) = γ t) →
      ∀ t, γ t = γ 0) :
    σ.IsContractibleHZAdmissible W (μ ∘ F) := by
  have hle (r : ℝ) : μ r ≤ μ a := by
    rcases le_total r a with h | h
    · exact (hlow r h).le
    · exact hanti h
  obtain ⟨x₀, hx₀⟩ := ha
  have hFc : Continuous F := hF.continuous
  -- The support of `μ ∘ F` lies in `{F ≤ b}`, since `μ` vanishes on `[b, ∞)`.
  have hsupp : tsupport (μ ∘ F) ⊆ {x | F x ≤ b} :=
    closure_minimal (fun x hx ↦ not_lt.1 fun h ↦ hx (hhigh _ h.le))
      (isClosed_le hFc continuous_const)
  exact
    { contMDiff := hμ.comp_contMDiff hF
      isCompact_tsupport := hcpt.of_isClosed_subset (isClosed_tsupport _) hsupp
      tsupport_subset_interior := hsupp.trans hW
      tsupport_subset_interior_manifold := hsupp.trans hM
      nonneg := fun x ↦ hnn _
      exists_isOpen_eqOn_zero := by
        obtain ⟨x, hxW, hx⟩ := hb
        exact ⟨interior W ∩ {x | b < F x}, isOpen_interior.inter (isOpen_lt continuous_const hFc),
          ⟨x, hxW, hx⟩, inter_subset_left.trans interior_subset,
          fun y hy ↦ hhigh _ (le_of_lt hy.2)⟩
      exists_isOpen_isMaxOn := ⟨{x | F x < a}, isOpen_lt hFc continuous_const, ⟨x₀, hx₀⟩,
        fun x hx ↦ isMaxOn_iff.2 fun y _ ↦ by simpa [hlow _ (le_of_lt hx)] using hle (F y)⟩
      eq_of_isMIntegralCurve := by
        rintro T γ hT hT1 hγ - ⟨g, hg, hgγ⟩
        refine hσ.eq_of_isMIntegralCurve_comp (hF.mdifferentiable (by simp))
          (hμ.differentiable (by simp)) hT hγ hg hgγ fun hc P γ' hP hPT hγ' hper hγ'0 hg' ↦ ?_
        -- A nonzero slope `μ'(s)` forces `s ∈ (a, b)` and `|μ'(s)| ≤ τ`.
        refine horb P γ' hP (hPT.trans ?_) hγ' hper ?_ hg'
        · simpa using mul_le_mul hT1 (habs _) (abs_nonneg _) zero_le_one
        · rw [hγ'0]
          by_contra hs
          exact hc (hzero _ hs) }

/-- **A lower bound for the `π₁`-sensitive Hofer–Zehnder capacity from the levels of an energy
function.** Let `F` be smooth with `{F ≤ b}` compact and contained in the interiors of `W` and of
`M`, taking values below `a < b` somewhere and above `b` somewhere in the interior of `W`. If no
level `F⁻¹(s)`, `s ∈ (a, b)`, carries a nonconstant `T`-periodic orbit of `X_F` with `T ≤ τ`
whose loop is contractible in `W`, then `c°_HZ(W) ≥ τ (b - a)`. -/
theorem IsNondegenerate.ofReal_mul_sub_le_contractibleHZCapacity (hσ : σ.IsNondegenerate)
    (hF : ContMDiff I 𝓘(ℝ) ∞ F) (hab : a < b) (hcpt : IsCompact {x | F x ≤ b})
    (hW : {x | F x ≤ b} ⊆ interior W) (hM : {x | F x ≤ b} ⊆ I.interior M)
    (ha : ∃ x, F x < a) (hb : ∃ x ∈ interior W, b < F x)
    (horb : ∀ (T : ℝ) (γ : ℝ → M), 0 < T → T ≤ τ →
      IsMIntegralCurve γ (σ.hamiltonianVectorField F) → Periodic γ T → F (γ 0) ∈ Ioo a b →
      (∃ g : C(AddCircle T, W), g.Nullhomotopic ∧ ∀ t : ℝ, (g t : M) = γ t) →
      ∀ t, γ t = γ 0) :
    ENNReal.ofReal (τ * (b - a)) ≤ σ.contractibleHZCapacity W := by
  refine le_of_forall_lt_imp_le_of_dense fun e he ↦ ?_
  have hvτ : e.toReal < τ * (b - a) := ENNReal.toReal_lt_of_lt_ofReal he
  rw [← ENNReal.ofReal_toReal he.ne_top]
  obtain ⟨μ, hμ, hanti, hnn, hhigh, hlow, habs, hzero⟩ :=
    exists_contDiff_antitone_cutoff_abs_deriv_le hab ENNReal.toReal_nonneg hvτ
  set v := e.toReal
  have hle (r : ℝ) : μ r ≤ v := by
    rcases le_total r a with h | h
    · exact (hlow r h).le
    · exact (hanti h).trans (hlow a le_rfl).le
  obtain ⟨x₀, hx₀⟩ := ha
  have : Nonempty M := ⟨x₀⟩
  have hsup : ⨆ x, (μ ∘ F) x = v :=
    ciSup_eq_of_forall_le_of_forall_lt_exists_gt (fun x ↦ hle _) fun w hw ↦
      ⟨x₀, by simpa [hlow _ hx₀.le] using hw⟩
  have hadm := hσ.isContractibleHZAdmissible_comp hF hcpt hW hM ⟨x₀, hx₀⟩ hb hμ hanti hnn hhigh
    (fun r hr ↦ by rw [hlow r hr, hlow a le_rfl]) habs hzero horb
  calc ENNReal.ofReal v = ENNReal.ofReal (⨆ x, (μ ∘ F) x) := by rw [hsup]
    _ ≤ _ := hadm.ofReal_iSup_le_contractibleHZCapacity

/-- **Short contractible closed orbits from a capacity bound.** Let `F` be smooth with
`{F ≤ b}` compact and contained in the interiors of `W` and of `M`, taking values below `a < b`
somewhere and above `b` somewhere in the interior of `W`. If `c°_HZ(W) < τ (b - a)`, then some
level `F⁻¹(s)`, `s ∈ (a, b)`, carries a nonconstant `T`-periodic orbit of `X_F` with
`0 < T ≤ τ` whose loop is contractible in `W`. -/
theorem IsNondegenerate.exists_isMIntegralCurve_of_contractibleHZCapacity_lt
    (hσ : σ.IsNondegenerate) (hF : ContMDiff I 𝓘(ℝ) ∞ F) (hab : a < b)
    (hcpt : IsCompact {x | F x ≤ b}) (hW : {x | F x ≤ b} ⊆ interior W)
    (hM : {x | F x ≤ b} ⊆ I.interior M) (ha : ∃ x, F x < a) (hb : ∃ x ∈ interior W, b < F x)
    (hcap : σ.contractibleHZCapacity W < ENNReal.ofReal (τ * (b - a))) :
    ∃ (T : ℝ) (γ : ℝ → M), 0 < T ∧ T ≤ τ ∧ IsMIntegralCurve γ (σ.hamiltonianVectorField F) ∧
      Periodic γ T ∧ F (γ 0) ∈ Ioo a b ∧ (∃ t, γ t ≠ γ 0) ∧
      ∃ g : C(AddCircle T, W), g.Nullhomotopic ∧ ∀ t : ℝ, (g t : M) = γ t := by
  by_contra h
  refine hcap.not_ge (hσ.ofReal_mul_sub_le_contractibleHZCapacity hF hab hcpt hW hM ha hb ?_)
  intro T γ hT hTτ hγ hper hs hg
  by_contra hne
  exact h ⟨T, γ, hT, hTτ, hγ, hper, hs, not_forall.1 hne, hg⟩

/-- **Dense existence of contractible closed characteristics.** If the `π₁`-sensitive
Hofer–Zehnder capacity of `W` is finite, then for every `a < b` such that `{F ≤ b}` is compact and
contained in the interiors of `W` and of `M`, with `F` taking values below `a` somewhere and above
`b` somewhere in the interior of `W`, some level `F⁻¹(s)` with `s ∈ (a, b)` carries a closed
characteristic contractible in `W`. -/
theorem IsNondegenerate.exists_mem_Ioo_hasContractibleClosedCharacteristic
    (hσ : σ.IsNondegenerate) (hF : ContMDiff I 𝓘(ℝ) ∞ F) (hab : a < b)
    (hcpt : IsCompact {x | F x ≤ b}) (hW : {x | F x ≤ b} ⊆ interior W)
    (hM : {x | F x ≤ b} ⊆ I.interior M) (ha : ∃ x, F x < a) (hb : ∃ x ∈ interior W, b < F x)
    (hcap : σ.contractibleHZCapacity W < ⊤) :
    ∃ s ∈ Ioo a b, σ.HasContractibleClosedCharacteristic W F s := by
  have hba : 0 < b - a := sub_pos.2 hab
  -- Choose `τ` with `τ (b - a)` above the capacity.
  have hτ : σ.contractibleHZCapacity W <
      ENNReal.ofReal (((σ.contractibleHZCapacity W).toReal + 1) / (b - a) * (b - a)) := by
    rw [div_mul_cancel₀ _ hba.ne']
    calc σ.contractibleHZCapacity W
        = ENNReal.ofReal (σ.contractibleHZCapacity W).toReal := (ENNReal.ofReal_toReal hcap.ne).symm
      _ < _ := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (lt_add_one _)
  obtain ⟨T, γ, hT, -, hγ, hper, hs, hne, hg⟩ :=
    hσ.exists_isMIntegralCurve_of_contractibleHZCapacity_lt hF hab hcpt hW hM ha hb hτ
  -- The energy `F` is conserved along `γ`.
  have hlev (t : ℝ) : F (γ t) = F (γ 0) :=
    (hσ.isHamiltonianVectorField_hamiltonianVectorField F).apply_eq_of_isMIntegralCurve hγ
      (fun _ ↦ hF.mdifferentiable (by simp) _) 0 t
  exact ⟨F (γ 0), hs, hasContractibleClosedCharacteristic_iff.2
    ⟨T, γ, hT, hγ, hper, hne, hlev, hg⟩⟩

end SmoothTwoForm

end TauCeti
