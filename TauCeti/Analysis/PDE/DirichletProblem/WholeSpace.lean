/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.DirichletProblem
public import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.Analysis.PDE.EnergyForm.SmallDrift
import TauCeti.Analysis.Sobolev.W1p.Density

/-!
# The whole-space equation with a zero-order shift

Let `ι` be a finite index type and write `ℝ^ι` for `EuclideanSpace ℝ ι`. Let `a` be a
measurable coefficient matrix on `ℝ^ι`, uniformly elliptic with constants
`λ, Λ`, not necessarily symmetric, and let `κ > 0`. This file treats the weak formulation of

`-∂ᵢ(aⁱʲ ∂ⱼu) + κ u = f - div G` in `ℝ^ι`,

namely `∫ ⟨a ∇u, ∇φ⟩ + κ ∫ u φ = ∫ f φ + ∫ ⟨G, ∇φ⟩` for every test function `φ`, with
`f, G ∈ L²`.

* `TauCeti.PDE.UniformlyEllipticOn.existsUnique_forall_energyFormH1_eq_of_pos`: the equation has
  exactly one solution in `H¹(ℝ^ι)`. The zero-order term makes the energy form coercive on
  `H¹(ℝ^ι)`, so this is Lax–Milgram. It is the whole-space counterpart of
  `TauCeti.PDE.UniformlyEllipticOn.existsUnique_forall_energyFormH1_eq_of_measure_ne_top`.
* `TauCeti.PDE.forall_energyFormH1_zero_zero_eq_of_shift`: tested against test functions, the
  shifted equation is the unshifted one with the scalar datum `f - κ u`.
* `TauCeti.PDE.forall_energyFormH1_eq_dirichletForcing_add_divergenceForcing`: a solution against
  test functions solves the equation against all of `H¹(ℝ^ι)`, with the right side written
  as `TauCeti.PDE.dirichletForcing` plus `TauCeti.PDE.divergenceForcing`.

Regularity of the solution on `ℝ^{n+1}`, for coefficients of small mean oscillation and data
also in `Lᵖ`, is in `TauCeti/Analysis/PDE/Regularity/VanishingMeanOscillation/ZeroOrderShift.lean`.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Distributions Gradient InnerProductSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι]

/-- The shifted equation `-∂ᵢ(aⁱʲ ∂ⱼu) + κ u = f - div G` on `ℝ^ι`, tested against test
functions, is the unshifted equation with the scalar datum `f - κ u`. -/
theorem forall_energyFormH1_zero_zero_eq_of_shift
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {κ : ℝ}
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤
      (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) :
        Set (EuclideanSpace ℝ ι))))
    {u : W1p volume (⊤ : Opens (EuclideanSpace ℝ ι)) 2}
    {G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {f : EuclideanSpace ℝ ι → ℝ} (hf : MemLp f 2 volume)
    (hu : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ ι)), ℝ),
      energyFormH1 a 0 (fun _ => κ) u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
        ∫ x, f x * φ x ∂volume +
          ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ ∂volume)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ ι)), ℝ)) :
    energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
      ∫ x in (⊤ : Opens (EuclideanSpace ℝ ι)),
          ⟪G x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ ∂volume +
        ∫ x in (⊤ : Opens (EuclideanSpace ℝ ι)),
          (f x - κ * W1p.value u x) * φ x ∂volume := by
  have hu2 := W1p.memLp_value u
  have hφ2 : MemLp (φ : EuclideanSpace ℝ ι → ℝ) 2 volume :=
    φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  have hsplit := energyFormH1_eq_energyFormH1_zero_add_setIntegral (b := 0) hcoeff
    (memLp_top_const κ) u (W1p.ofTestFunctionₗ volume ⊤ 2 φ)
  have hval : ∫ x in (⊤ : Opens (EuclideanSpace ℝ ι)),
      κ * W1p.value u x * W1p.value (W1p.ofTestFunctionₗ volume ⊤ 2 φ) x =
        ∫ x, κ * W1p.value u x * φ x := by
    simp only [Opens.coe_top, Measure.restrict_univ]
    exact integral_congr_ae ((W1p.value_ofTestFunctionₗ_top_ae φ).mono
      fun x hx => congrArg (κ * W1p.value u x * ·) hx)
  have hsub : ∫ x, (f x - κ * W1p.value u x) * φ x =
      (∫ x, f x * φ x) - ∫ x, κ * W1p.value u x * φ x :=
    (integral_congr_ae (ae_of_all _ fun x => sub_mul _ _ _)).trans
      (integral_sub (hf.integrable_mul hφ2) ((hu2.const_mul κ).integrable_mul hφ2))
  have h := hu φ
  simp only [Opens.coe_top, Measure.restrict_univ] at hsplit hval ⊢
  rw [hsub]
  linarith

/-- The shifted equation tested against test functions holds against all of `H¹(ℝ^ι)`, in
the form of `TauCeti.PDE.UniformlyEllipticOn.eLpNorm_value_le_of_forall_energyFormH1_eq`. -/
theorem forall_energyFormH1_eq_dirichletForcing_add_divergenceForcing
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {κ : ℝ}
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤
      (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) :
        Set (EuclideanSpace ℝ ι))))
    {u : W1p volume (⊤ : Opens (EuclideanSpace ℝ ι)) 2}
    {G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {f : EuclideanSpace ℝ ι → ℝ}
    (hfT : MemLp f 2 (volume.restrict
      ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))))
    (hκuT : MemLp (fun x => κ * W1p.value u x) 2 (volume.restrict
      ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))))
    (hGT : MemLp (fun x => G x - 0) 2 (volume.restrict
      ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))))
    (hu' : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ ι)), ℝ),
      energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
        ∫ x in (⊤ : Opens (EuclideanSpace ℝ ι)),
            ⟪G x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ ∂volume +
          ∫ x in (⊤ : Opens (EuclideanSpace ℝ ι)),
            (f x - κ * W1p.value u x) * φ x ∂volume)
    (v : W1p0 volume (⊤ : Opens (EuclideanSpace ℝ ι)) 2) :
    energyFormH1 a 0 (fun _ => κ) u (v : W1p volume ⊤ 2) =
      dirichletForcing hfT.toLp v + divergenceForcing (-hGT.toLp) v := by
  have h1 := forall_energyFormH1_restrictL_eq_inner_add_inner le_rfl hcoeff hu' hGT
    (hfT.sub hκuT) v
  rw [W1p.restrictL_self] at h1
  have hsubLp : MemLp.toLp (fun x => f x - κ * W1p.value u x) (hfT.sub hκuT) =
      hfT.toLp - hκuT.toLp := MemLp.toLp_sub hfT hκuT
  have hκint : ⟪hκuT.toLp, W1p.value (v : W1p volume ⊤ 2)⟫_ℝ =
      ∫ x in ((⊤ : Opens (EuclideanSpace ℝ ι)) :
        Set (EuclideanSpace ℝ ι)),
        κ * W1p.value u x * W1p.value (v : W1p volume ⊤ 2) x := by
    rw [L2.inner_def]
    exact integral_congr_ae (hκuT.coeFn_toLp.mono fun x hx => by
      simp [hx, mul_comm])
  rw [energyFormH1_eq_energyFormH1_zero_add_setIntegral (b := 0) hcoeff (memLp_top_const κ), h1,
    dirichletForcing_apply, divergenceForcing_apply, inner_neg_left, neg_neg, hsubLp,
    inner_sub_left, hκint]
  ring

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace in
/-- On a test function `φ`, the functional `v ↦ ∫ f v + ∫ ⟪G, ∇v⟫` of the shifted equation on
`ℝ^ι`, in the form of
`TauCeti.PDE.UniformlyEllipticOn.eLpNorm_value_le_of_forall_energyFormH1_eq`, is
`∫ f φ + ∫ ⟪G, ∇φ⟫`. -/
private theorem dirichletForcing_add_divergenceForcing_ofTestFunctionₗ
    {G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {f : EuclideanSpace ℝ ι → ℝ}
    (hfT : MemLp f 2 (volume.restrict
      ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))))
    (hGT : MemLp (fun x => G x - 0) 2 (volume.restrict
      ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ ι)), ℝ)) :
    (dirichletForcing hfT.toLp + divergenceForcing (-hGT.toLp))
        ⟨W1p.ofTestFunctionₗ volume ⊤ 2 φ, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩ =
      ∫ x, f x * φ x ∂volume +
        ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ ∂volume := by
  rw [add_apply, dirichletForcing_apply_eq_setIntegral, divergenceForcing_apply_eq_neg_setIntegral,
    ← integral_neg]
  simp only [Opens.coe_top, Measure.restrict_univ]
  congr 1
  · refine integral_congr_ae ?_
    have hf1 := hfT.coeFn_toLp
    simp only [Opens.coe_top, Measure.restrict_univ] at hf1
    filter_upwards [hf1, W1p.value_ofTestFunctionₗ_top_ae (mu := volume) (p := 2) φ]
      with x hx hφx
    rw [hx, hφx]
  · refine integral_congr_ae ?_
    have hneg := (Lp.coeFn_neg hGT.toLp).trans hGT.coeFn_toLp.neg
    simp only [Opens.coe_top, Measure.restrict_univ] at hneg
    filter_upwards [hneg, W1p.gradient_ofTestFunctionₗ_top_ae (mu := volume) (p := 2) φ]
      with x hx hgx
    rw [hx, hgx, Pi.neg_apply, sub_zero, inner_neg_left, neg_neg]

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace in
/-- **Existence and uniqueness for the whole-space equation with a zero-order shift.** Let `a` be
a measurable coefficient matrix on `ℝ^ι = EuclideanSpace ℝ ι`, uniformly elliptic with constants
`λ, Λ`, not necessarily symmetric, and let `κ > 0`. For all `f ∈ L²(ℝ^ι)` and `G ∈ L²(ℝ^ι; ℝ^ι)`
there is exactly one `u ∈ H¹(ℝ^ι)` solving

`-∂ᵢ(aⁱʲ ∂ⱼu) + κ u = f - div G`

weakly, that is `∫ ⟨a ∇u, ∇φ⟩ + κ ∫ u φ = ∫ f φ + ∫ ⟨G, ∇φ⟩` for every test function `φ`. The
zero-order term makes the energy form coercive on `H¹(ℝ^ι)`, so this is Lax–Milgram. On
`ℝ^{n+1}`, for coefficients of small mean oscillation and data also in `Lᵖ`, `2 < p < ∞`, the
solution lies in `W^{1,p}(ℝ^{n+1})`
(`TauCeti.PDE.exists_memLp_gradient_and_memLp_value_of_vmoModulus_le`). -/
theorem UniformlyEllipticOn.existsUnique_forall_energyFormH1_eq_of_pos [DecidableEq ι]
    {lam Lam κ : ℝ}
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (hell : UniformlyEllipticOn univ a lam Lam) (ham : AEStronglyMeasurable a volume)
    (hκ : 0 < κ) {G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {f : EuclideanSpace ℝ ι → ℝ} (hG : MemLp G 2 volume) (hf : MemLp f 2 volume) :
    ∃! u : W1p volume (⊤ : Opens (EuclideanSpace ℝ ι)) 2,
      ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ ι)), ℝ),
        energyFormH1 a 0 (fun _ => κ) u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
          ∫ x, f x * φ x ∂volume +
            ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ ∂volume := by
  set T := (⊤ : Opens (EuclideanSpace ℝ ι))
  have hT : (T : Set (EuclideanSpace ℝ ι)) = univ := Opens.coe_top
  have hfT : MemLp f 2 (volume.restrict (T : Set (EuclideanSpace ℝ ι))) := by
    rwa [hT, Measure.restrict_univ]
  have hGT : MemLp (fun x => G x - 0) 2
      (volume.restrict (T : Set (EuclideanSpace ℝ ι))) := by
    simpa only [hT, Measure.restrict_univ, sub_zero] using hG
  have hellT : UniformlyEllipticOn (T : Set (EuclideanSpace ℝ ι)) a lam Lam :=
    hell.mono_set (subset_univ _)
  have hb : ∀ x ∈ (T : Set (EuclideanSpace ℝ ι)),
      ‖(0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x‖ ≤ 0 :=
    fun _ _ => by simp
  have hc : ∀ x ∈ (T : Set (EuclideanSpace ℝ ι)),
      ‖(fun _ : EuclideanSpace ℝ ι => κ) x‖ ≤ κ :=
    fun _ _ => (Real.norm_of_nonneg hκ.le).le
  have hcoeff := memLp_energyIntegrand_of_bounds (b := 0) (c := fun _ => κ) hellT.upper_nonneg
    ham.restrict aestronglyMeasurable_zero aestronglyMeasurable_const
    (fun _ hx eta xi => hellT.upper_bound hx eta xi) hb hc
  have hB := hellT.isCoercive_energyFormH1L0_of_mass_lower_bound (b := 0) (c := fun _ => κ)
    ham.restrict aestronglyMeasurable_zero aestronglyMeasurable_const hb hc (fun _ _ => le_rfl)
    (by rw [zero_pow two_ne_zero]; exact mul_pos (mul_pos four_pos hellT.pos) hκ) hcoeff
  obtain ⟨w, hw, hwu⟩ := hB.existsUnique_forall_eq
    (dirichletForcing hfT.toLp + divergenceForcing (-hGT.toLp))
  simp only [energyFormH1L0_apply] at hw hwu
  refine ⟨(w : W1p volume T 2), fun φ => ?_, fun u hu => ?_⟩
  · -- The Lax–Milgram solution solves the equation against test functions.
    rw [← dirichletForcing_add_divergenceForcing_ofTestFunctionₗ hfT hGT φ]
    exact hw ⟨W1p.ofTestFunctionₗ volume ⊤ 2 φ, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩
  · -- A solution against test functions solves the equation against `H¹(ℝ^ι)`.
    have hcoeff₀ := (hell.mono_set (subset_univ _)).memLp_energyIntegrand_zero_zero
      (Omega := T) ham.restrict
    have hκuT : MemLp (fun x => κ * W1p.value u x) 2
        (volume.restrict (T : Set (EuclideanSpace ℝ ι))) := by
      simpa only [hT, Measure.restrict_univ] using (W1p.memLp_value u).const_mul κ
    have h := forall_energyFormH1_eq_dirichletForcing_add_divergenceForcing hcoeff₀ hfT hκuT hGT
      (forall_energyFormH1_zero_zero_eq_of_shift hcoeff₀ hf hu)
    exact congrArg Subtype.val (hwu ⟨u, W1p.mem_w1p0Submodule_top (by norm_num) u⟩ fun v => by
      rw [h v, add_apply])

end PDE

end TauCeti
