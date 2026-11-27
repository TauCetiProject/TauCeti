/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.HalfSpace.HigherOrder
import TauCeti.Analysis.PDE.Ellipticity.PosDef
import TauCeti.Analysis.InnerProductSpace.HalfSpace
import TauCeti.Analysis.PDE.Regularity.HigherOrder
import TauCeti.Analysis.Sobolev.W1p.Localization
import TauCeti.Analysis.PDE.Regularity.Interior.Localization

/-!
# All-order local regularity at a flat Dirichlet boundary

Let `Ω ∩ U = H ∩ U` for an open half-space `H`, allowing the empty and whole-space
degeneracies. A scalar weak solution on `Ω ∩ U` of
`-div(a ∇u) = f`, with smooth coefficients and forcing on `U` and a uniform positive
lower bound on the quadratic form of `a` on `Ω ∩ U`, is in every Sobolev order on `Ω ∩ V`
whenever `closure V` is compact and contained in `U`. The homogeneous
boundary condition is imposed by requiring every cutoff supported in `U` times the
solution to lie in `H¹₀(Ω)` when the half-space has a nonzero normal.

For each Sobolev order, an intermediate open set supplies the derivatives used in the
localized forcing. The cutoff one on `closure V` then gives the same solution there
as the global half-space problem, where tangential differentiation and the conormal
flux recover all derivatives.

The global theorem in `Regularity/HalfSpace/HigherOrder.lean` gives `H^{k+2}` regularity
for `H^k` forcing and coefficients with bounded derivatives. The finite-order local theorem
accepts `H^k` forcing on the chart patch; the smooth-forcing theorem gives every Sobolev
order on a fixed patch.

The cutoff localization adapts the proofs in `Regularity/FlatBoundary.lean` and reuses
the global regularity theorem from `Regularity/HalfSpace/HigherOrder.lean`.

## Main results

* `UniformlyEllipticOn.exists_value_succ_succ_eq_value_restrictL_of_mapsTo`:
  finite-order regularity with Sobolev forcing on a chart patch.
* `exists_value_eq_value_restrictL_allOrders_of_halfSpace`:
  every finite Sobolev order on a fixed patch with smooth local data.

Reference: L. C. Evans, *Partial Differential Equations*, §6.3.2, Theorem 5.
-/

public section

section LocalRegularity

open Filter MeasureTheory Set TopologicalSpace
open scoped BigOperators ContDiff Distributions Gradient InnerProductSpace

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega H U V : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam c₀ : ℝ} {ν : EuclideanSpace ℝ ι}
  {f : EuclideanSpace ℝ ι → ℝ} {u : W1p mu Omega 2}

local notation "E" => EuclideanSpace ℝ ι

omit [Fintype ι] [DecidableEq ι] in
private theorem mem_iff_mem_of_inter_eq (hΩU : (Omega : Set E) ∩ U = (H : Set E) ∩ U)
    {x : E} (hx : x ∈ (U : Set E)) : x ∈ Omega ↔ x ∈ H := by
  simpa only [← SetLike.mem_coe, mem_inter_iff, hx, and_true] using Set.ext_iff.1 hΩU x

private theorem exists_value_eq_value_restrictL_of_mapsTo_of_order
    (hν : ν ≠ 0) (hHc : Convex ℝ (H : Set E))
    (hH : ∀ τ, ⟪τ, ν⟫_ℝ = 0 → ∀ t : ℝ, MapsTo (· + t • τ) H H)
    (hΩU : (Omega : Set E) ∩ U = (H : Set E) ∩ U)
    (ha : UniformlyEllipticOn ((Omega : Set E) ∩ U) a lam Lam)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ a x i j) U)
    (k : ℕ) (F : Wkp mu (Omega ⊓ U) 2 k)
    (hu : ∀ v : W1p0 mu (Omega ⊓ U) 2,
      energyFormH1 a 0 0 (W1p.restrictL inf_le_left u) (v : W1p mu (Omega ⊓ U) 2) =
        ∫ x in Omega ⊓ U, Wkp.value k F x * W1p.value (v : W1p mu (Omega ⊓ U) 2) x ∂mu)
    (hu0 : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∃ v : W1p0 mu Omega 2,
        W1p.value (v : W1p mu Omega 2) =ᵐ[mu.restrict Omega] fun x ↦ ψ x * W1p.value u x)
    {W : Opens E} (hW : IsCompact (closure (W : Set E)))
    (hWU : closure (W : Set E) ⊆ U) (hV : IsCompact (closure (V : Set E)))
    (hVW : closure (V : Set E) ⊆ W) (Z : Wkp mu (Omega ⊓ W) 2 (k + 1))
    (hZ : Wkp.value (k + 1) Z = W1p.value (W1p.restrictL inf_le_left u)) :
    ∃ Q : Wkp mu (Omega ⊓ V) 2 (k + 2),
      Wkp.value (k + 2) Q = W1p.value (W1p.restrictL inf_le_left u) := by
  have hHU : (H : Set E) ∩ U ⊆ (Omega : Set E) ∩ U := hΩU.ge
  obtain ⟨a', L, _, M, W', hWW', -, ha', hsm', hL, -, hM, hagree', K, hK, -, hconst⟩ :=
    ha.exists_contDiff_eqOn_inter hsmooth hHU hW hWU
  have hagree : EqOn a' a (closure (W : Set E)) := fun x hx ↦ hagree' (hWW' hx)
  let D := Omega ⊓ W
  have hD : D ≤ Omega := inf_le_left
  have hWsub : (W : Set E) ⊆ U := subset_closure.trans hWU
  have hΩH (x : E) (hx : x ∈ (U : Set E)) : x ∈ Omega ↔ x ∈ H :=
    mem_iff_mem_of_inter_eq hΩU hx
  have hDU : D ≤ Omega ⊓ U := fun _ hx ↦ ⟨hx.1, hWsub hx.2⟩
  have hDH : D ≤ H := fun x hx ↦ (hΩH x (hWsub hx.2)).1 hx.1
  have hz₁ : Wkp.firstOrder k Z = W1p.restrictL hD u :=
    W1p.ext_value ((Wkp.value_firstOrder k Z).trans hZ)
  let FD := Wkp.restrictL hDU k F
  have huD (v : W1p0 mu D 2) :
      energyFormH1 a' 0 0 (Wkp.firstOrder k Z) (v : W1p mu D 2) =
        ∫ x in D, Wkp.value k FD x * W1p.value (v : W1p mu D 2) x ∂mu := by
    rw [hz₁, ← W1p.restrictL_restrictL inf_le_left hDU,
      energyFormH1_restrictL_eq_setIntegral_of_eqOn hDU
      (fun x hx ↦ hagree (subset_closure hx.2)) hu]
    exact integral_congr_ae ((Wkp.value_restrictL_ae hDU k F).mono fun x hx ↦
      congrArg (· * W1p.value (v : W1p mu D 2) x) hx.symm)
  obtain ⟨ψ, N, hψ, -, hψ1, hψc, hψs, hN, hψN, hgradN⟩ :=
    hV.exists_contDiff_cutoff_with_bounds W.isOpen hVW
  obtain ⟨d, hd⟩ := W1p.exists_w1p0_value_ae_eq_mul_restrictL hWsub hu0 hψ hψc hψs
  have hψu : W1p.contDiffSMul ψ hψ hN (fun x _ ↦ hψN x) (fun x _ ↦ hgradN x)
      (Wkp.firstOrder k Z) = (d : W1p mu D 2) := by
    refine W1p.ext_value (Lp.ext ?_)
    filter_upwards [W1p.value_contDiffSMul_ae hψ hN (fun x _ ↦ hψN x) (fun x _ ↦ hgradN x)
      (Wkp.firstOrder k Z), hd] with x h₁ h₂
    rw [h₁, h₂, hz₁, smul_eq_mul]
  have hts : tsupport ψ ∩ H ⊆ (D : Set E) := fun x hx ↦
    ⟨(hΩH x (hWsub (hψs hx.1))).2 hx.2, hψs hx.1⟩
  obtain ⟨w, G, hw, hwv⟩ := exists_isWeakSolutionDirichlet_value_ae_eq_indicator
    hM hL hsm' hDH k FD Z huD hψ hψc hts hN _ _ (hψu ▸ d.property)
  obtain ⟨C, hC⟩ := exists_coefficient_derivative_bound hK hconst hsm' k
  obtain ⟨Q, hQ⟩ := ha'.exists_value_eq_value_of_mapsTo_of_contDiffOn
    hν hHc hH hL.lipschitzOnWith k
    (fun i j ↦ (hsm' i j).contDiffOn.of_le (by simp))
    (fun i j r hr hrk x _ ↦ hC i j r hr hrk x) hw
  have hVD : Omega ⊓ V ≤ D := fun _ hx ↦ ⟨hx.1, hVW (subset_closure hx.2)⟩
  have hVH : Omega ⊓ V ≤ H := hVD.trans hDH
  refine ⟨Wkp.restrictL hVH (k + 2) Q, Lp.ext ?_⟩
  filter_upwards [Wkp.value_restrictL_ae hVH (k + 2) Q,
    ae_restrict_of_ae_restrict_of_subset hVH hwv,
    ae_restrict_of_ae_restrict_of_subset hVD (W1p.value_restrictL_ae hD u),
    W1p.value_restrictL_ae (inf_le_left : Omega ⊓ V ≤ Omega) u,
    ae_restrict_mem (Omega ⊓ V).isOpen.measurableSet] with x h₁ h₂ h₃ h₄ hx
  have hψx : ψ x = 1 := interior_subset (hψ1 (subset_closure hx.2))
  rw [h₁, hQ, h₂, indicator_of_mem (hVD hx), hψx, one_mul, hz₁, h₃, h₄]

/-- Local `H^{k+2}` regularity for `H^k` forcing near a flat homogeneous Dirichlet boundary.
The model domain is convex and invariant under translations orthogonal to a nonzero normal;
in particular it may be a half-space or a slab. The equation and coefficient assumptions
are local to `Ω ∩ U`, and the forcing need only belong to `H^k(Ω ∩ U)`. -/
theorem UniformlyEllipticOn.exists_value_succ_succ_eq_value_restrictL_of_mapsTo
    (hν : ν ≠ 0) (hHc : Convex ℝ (H : Set E))
    (hH : ∀ τ, ⟪τ, ν⟫_ℝ = 0 → ∀ t : ℝ, MapsTo (· + t • τ) H H)
    (hΩU : (Omega : Set E) ∩ U = (H : Set E) ∩ U)
    (ha : UniformlyEllipticOn ((Omega : Set E) ∩ U) a lam Lam)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ a x i j) U)
    (k : ℕ) (F : Wkp mu (Omega ⊓ U) 2 k)
    (hu : ∀ v : W1p0 mu (Omega ⊓ U) 2,
      energyFormH1 a 0 0 (W1p.restrictL inf_le_left u) (v : W1p mu (Omega ⊓ U) 2) =
        ∫ x in Omega ⊓ U, Wkp.value k F x * W1p.value (v : W1p mu (Omega ⊓ U) 2) x ∂mu)
    (hu0 : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∃ v : W1p0 mu Omega 2,
        W1p.value (v : W1p mu Omega 2) =ᵐ[mu.restrict Omega] fun x ↦ ψ x * W1p.value u x)
    (hV : IsCompact (closure (V : Set E))) (hVU : closure (V : Set E) ⊆ U) :
    ∃ Q : Wkp mu (Omega ⊓ V) 2 (k + 2),
      Wkp.value (k + 2) Q = W1p.value (W1p.restrictL inf_le_left u) := by
  induction k using Nat.strong_induction_on generalizing V with
  | ind k ih =>
    obtain ⟨W₀, hWo, hVW, hWU, hW⟩ :=
      exists_open_between_and_isCompact_closure hV U.isOpen hVU
    let W : Opens E := ⟨W₀, hWo⟩
    have hZ : ∃ Z : Wkp mu (Omega ⊓ W) 2 (k + 1),
        Wkp.value (k + 1) Z = W1p.value (W1p.restrictL inf_le_left u) := by
      cases k with
      | zero => exact ⟨W1p.restrictL inf_le_left u, Wkp.value_one _⟩
      | succ k =>
        exact ih k (Nat.lt_succ_self k) (Wkp.lowerOrder k F)
          (by simpa only [← Wkp.value_succ] using hu) hW hWU
    obtain ⟨Z, hZ⟩ := hZ
    exact exists_value_eq_value_restrictL_of_mapsTo_of_order hν hHc hH hΩU ha hsmooth
      k F hu hu0 hW hWU hV hVW Z hZ

private theorem exists_value_eq_value_restrictL_allOrders_of_ne_zero
    (hν : ν ≠ 0) (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (hΩU : (Omega : Set E) ∩ U = (H : Set E) ∩ U)
    (ha : UniformlyEllipticOn ((Omega : Set E) ∩ U) a lam Lam)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ a x i j) U)
    (hf : ContDiffOn ℝ ∞ f U)
    (hu : ∀ v : W1p0 mu (Omega ⊓ U) 2,
      energyFormH1 a 0 0 (W1p.restrictL inf_le_left u) (v : W1p mu (Omega ⊓ U) 2) =
        ∫ x in Omega ⊓ U, f x * W1p.value (v : W1p mu (Omega ⊓ U) 2) x ∂mu)
    (hu0 : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∃ v : W1p0 mu Omega 2,
        W1p.value (v : W1p mu Omega 2) =ᵐ[mu.restrict Omega] fun x ↦ ψ x * W1p.value u x)
    (hV : IsCompact (closure (V : Set E))) (hVU : closure (V : Set E) ⊆ U) :
    ∀ k : ℕ, ∃ Q : Wkp mu (Omega ⊓ V) 2 k,
      Wkp.value k Q = W1p.value (W1p.restrictL inf_le_left u) := by
  obtain ⟨W₀, hWo, hVW, hWU, hW⟩ :=
    exists_open_between_and_isCompact_closure hV U.isOpen hVU
  let W : Opens E := ⟨W₀, hWo⟩
  have hWsub : (W : Set E) ⊆ U := subset_closure.trans hWU
  have hDU : Omega ⊓ W ≤ Omega ⊓ U := fun _ hx ↦ ⟨hx.1, hWsub hx.2⟩
  have hΩW : (Omega : Set E) ∩ W = (H : Set E) ∩ W := by
    ext x
    simp only [mem_inter_iff]
    exact and_congr_left fun hx ↦ mem_iff_mem_of_inter_eq hΩU (hWsub hx)
  intro k
  obtain ⟨F, hF⟩ := Wkp.exists_value_ae_eq_of_contDiffOn_of_isCompact
    (mu := mu) (Omega := Omega ⊓ W) (p := 2) k U.isOpen (hf.of_le (by simp)) hW
    (fun x hx ↦ subset_closure hx.2) hWU
  have huD (v : W1p0 mu (Omega ⊓ W) 2) :
      energyFormH1 a 0 0 (W1p.restrictL inf_le_left u) (v : W1p mu (Omega ⊓ W) 2) =
        ∫ x in Omega ⊓ W, Wkp.value k F x * W1p.value (v : W1p mu (Omega ⊓ W) 2) x ∂mu := by
    rw [← W1p.restrictL_restrictL inf_le_left hDU,
      energyFormH1_restrictL_eq_setIntegral hDU hu]
    exact integral_congr_ae (hF.mono fun x hx ↦
      congrArg (· * W1p.value (v : W1p mu (Omega ⊓ W) 2) x) hx.symm)
  obtain ⟨Q, hQ⟩ := (ha.mono_set hDU).exists_value_succ_succ_eq_value_restrictL_of_mapsTo
    hν (TauCeti.convex_of_halfSpace hH)
    (fun _ hτ ↦ TauCeti.mapsTo_add_smul_of_halfSpace hH hτ) hΩW
    (fun i j ↦ (hsmooth i j).mono hWsub) k F huD
    (fun ψ hψ hψc hψs ↦ hu0 ψ hψ hψc (hψs.trans hWsub)) hV hVW
  exact ⟨Wkp.toOrderL (by omega : k ≤ k + 2) Q, (Wkp.value_toOrderL _ Q).trans hQ⟩

private theorem exists_value_eq_value_restrictL_allOrders_of_interior
    (hUΩ : U ≤ Omega) (ha : UniformlyEllipticOn ((Omega : Set E) ∩ U) a lam Lam)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ a x i j) U)
    (hf : ContDiffOn ℝ ∞ f U)
    (hu : ∀ v : W1p0 mu (Omega ⊓ U) 2,
      energyFormH1 a 0 0 (W1p.restrictL inf_le_left u) (v : W1p mu (Omega ⊓ U) 2) =
        ∫ x in Omega ⊓ U, f x * W1p.value (v : W1p mu (Omega ⊓ U) 2) x ∂mu)
    (hV : IsCompact (closure (V : Set E))) (hVU : closure (V : Set E) ⊆ U) :
    ∀ k : ℕ, ∃ Q : Wkp mu (Omega ⊓ V) 2 k,
      Wkp.value k Q = W1p.value (W1p.restrictL inf_le_left u) := by
  obtain ⟨W₀, hWo, hVW, hWU, hW⟩ :=
    exists_open_between_and_isCompact_closure hV U.isOpen hVU
  let W : Opens E := ⟨W₀, hWo⟩
  have hWsub : (W : Set E) ⊆ U := subset_closure.trans hWU
  have hWΩU : W ≤ Omega ⊓ U := fun _ hx ↦ ⟨hUΩ (hWsub hx), hWsub hx⟩
  have hWΩ : W ≤ Omega := hWΩU.trans inf_le_left
  have haW : UniformlyEllipticOn (W : Set E) a lam Lam := ha.mono_set hWΩU
  have hY : closure ((Omega ⊓ V : Opens E) : Set E) ⊆ closure (V : Set E) :=
    closure_mono inter_subset_right
  intro k
  obtain ⟨F, hF⟩ := Wkp.exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := mu) (Omega := W)
    (p := 2) k U.isOpen (hf.of_le (by simp)) hW subset_closure hWU
  have huW (v : W1p0 mu W 2) :
      energyFormH1 a 0 0 (W1p.restrictL hWΩ u) (v : W1p mu W 2) =
        ∫ x in W, Wkp.value k F x * W1p.value (v : W1p mu W 2) x ∂mu := by
    rw [← W1p.restrictL_restrictL inf_le_left hWΩU,
      energyFormH1_restrictL_eq_setIntegral hWΩU hu]
    exact integral_congr_ae (hF.mono fun x hx ↦
      congrArg (· * W1p.value (v : W1p mu W 2) x) hx.symm)
  obtain ⟨Q, hQ⟩ := haW.exists_value_eq_value_restrictL_of_contDiffOn k
    (fun i j ↦ ((hsmooth i j).mono hWsub).of_le (by simp))
    (b := 0) (c := 0) contDiffOn_const contDiffOn_const huW
    (V := Omega ⊓ V) (hV.of_isClosed_subset isClosed_closure hY) (hY.trans hVW)
  have hk : k ≤ k + 2 := by omega
  refine ⟨Wkp.toOrderL hk Q, ?_⟩
  rw [Wkp.value_toOrderL, hQ, W1p.restrictL_restrictL]

private theorem exists_value_eq_value_restrictL_allOrders_of_uniformlyElliptic
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (hΩU : (Omega : Set E) ∩ U = (H : Set E) ∩ U)
    (ha : UniformlyEllipticOn ((Omega : Set E) ∩ U) a lam Lam)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ a x i j) U)
    (hf : ContDiffOn ℝ ∞ f U)
    (hu : ∀ v : W1p0 mu (Omega ⊓ U) 2,
      energyFormH1 a 0 0 (W1p.restrictL inf_le_left u) (v : W1p mu (Omega ⊓ U) 2) =
        ∫ x in Omega ⊓ U, f x * W1p.value (v : W1p mu (Omega ⊓ U) 2) x ∂mu)
    (hu0 : ν ≠ 0 → ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∃ v : W1p0 mu Omega 2,
        W1p.value (v : W1p mu Omega 2) =ᵐ[mu.restrict Omega] fun x ↦ ψ x * W1p.value u x)
    (hV : IsCompact (closure (V : Set E))) (hVU : closure (V : Set E) ⊆ U) :
    ∀ k : ℕ, ∃ Q : Wkp mu (Omega ⊓ V) 2 k,
      Wkp.value k Q = W1p.value (W1p.restrictL inf_le_left u) := by
  by_cases hν : ν = 0
  · have hH₀ (x : E) : x ∈ H ↔ c₀ < 0 := by simpa [hν] using hH x
    have hΩH (x : E) (hx : x ∈ (U : Set E)) : x ∈ Omega ↔ x ∈ H :=
      mem_iff_mem_of_inter_eq hΩU hx
    by_cases hc : c₀ < 0
    · exact exists_value_eq_value_restrictL_allOrders_of_interior
        (fun x hx ↦ (hΩH x hx).2 ((hH₀ x).2 hc)) ha hsmooth hf hu hV hVU
    · intro k
      refine ⟨0, Lp.ext ?_⟩
      filter_upwards [ae_restrict_mem (Omega ⊓ V).isOpen.measurableSet] with x hx
      exact (hc ((hH₀ x).1 ((hΩH x (hVU (subset_closure hx.2))).1 hx.1))).elim
  · exact exists_value_eq_value_restrictL_allOrders_of_ne_zero
      hν hH hΩU ha hsmooth hf hu (hu0 hν) hV hVU

omit [DecidableEq ι] in
/-- A scalar weak solution with smooth coefficients and forcing has every finite Sobolev
order locally up to a flat homogeneous Dirichlet boundary.

The weak equation and the uniform positive lower bound for the coefficient field are required
only on the chart patch. The equation is tested against smooth compactly supported functions.
No upper bound on the coefficients is assumed; smoothness on `U` suffices.
A zero normal gives an interior or empty patch, for which there is no trace condition. -/
theorem exists_value_eq_value_restrictL_allOrders_of_halfSpace
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (hΩU : (Omega : Set E) ∩ U = (H : Set E) ∩ U)
    (hlam : 0 < lam) (ha : ∀ x ∈ (Omega : Set E) ∩ U, ∀ v : E,
      lam * ‖v‖ ^ 2 ≤ matrixBilinearForm (a x) v v)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ a x i j) U)
    (hf : ContDiffOn ℝ ∞ f U)
    (hu : ∀ φ : 𝓓(Omega ⊓ U, ℝ),
      energyFormH1 a 0 0 (W1p.restrictL inf_le_left u)
        (W1p.ofTestFunctionₗ mu (Omega ⊓ U) 2 φ) =
          ∫ x in Omega ⊓ U, f x * φ x ∂mu)
    (hu0 : ν ≠ 0 → ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∃ v : W1p0 mu Omega 2,
        W1p.value (v : W1p mu Omega 2) =ᵐ[mu.restrict Omega] fun x ↦ ψ x * W1p.value u x)
    (hV : IsCompact (closure (V : Set E))) (hVU : closure (V : Set E) ⊆ U) :
    ∀ k : ℕ, ∃ Q : Wkp mu (Omega ⊓ V) 2 k,
      Wkp.value k Q = W1p.value (W1p.restrictL inf_le_left u) := by
  classical
  obtain ⟨W₀, hWo, hVW, hWU, hW⟩ :=
    exists_open_between_and_isCompact_closure hV U.isOpen hVU
  let W : Opens E := ⟨W₀, hWo⟩
  have hWsub : (W : Set E) ⊆ U := subset_closure.trans hWU
  have hWΩU : Omega ⊓ W ≤ Omega ⊓ U := fun _ hx ↦ ⟨hx.1, hWsub hx.2⟩
  have hΩW : (Omega : Set E) ∩ W = (H : Set E) ∩ W := by
    ext x
    simp only [mem_inter_iff]
    exact and_congr_left fun hx ↦ mem_iff_mem_of_inter_eq hΩU (hWsub hx)
  obtain ⟨_, haW⟩ :=
    exists_uniformlyEllipticOn_inter_of_isCompact_closure (W := W) hW hWU hlam
      ha (fun i j ↦ (hsmooth i j).continuousOn)
  have huW (v : W1p0 mu (Omega ⊓ W) 2) :
      energyFormH1 a 0 0 (W1p.restrictL inf_le_left u) (v : W1p mu (Omega ⊓ W) 2) =
        ∫ x in Omega ⊓ W, f x * W1p.value (v : W1p mu (Omega ⊓ W) 2) x ∂mu := by
    rw [← W1p.restrictL_restrictL inf_le_left hWΩU]
    have hcl : closure ((Omega ⊓ W : Opens E) : Set E) ⊆ closure (W : Set E) :=
      closure_mono inter_subset_right
    have hcoeff := memLp_energyIntegrand_of_continuousOn (mu := mu) (b := 0) (c := 0)
      (hW.of_isClosed_subset isClosed_closure hcl)
      ((continuousOn_pi.2 fun i ↦ continuousOn_pi.2 fun j ↦
        (hsmooth i j).continuousOn).mono (hcl.trans hWU))
      continuousOn_const continuousOn_const (Omega := Omega ⊓ W)
    obtain ⟨F, hF⟩ := Wkp.exists_value_ae_eq_of_contDiffOn_of_isCompact
      (mu := mu) (Omega := Omega ⊓ W) (p := 2) 0 U.isOpen (hf.of_le (by simp))
      hW (fun x hx ↦ subset_closure hx.2) hWU
    have hfLp : MemLp f 2 (mu.restrict (Omega ⊓ W)) := (Lp.memLp (Wkp.value 0 F)).ae_eq hF
    exact forall_energyFormH1_restrictL_eq_setIntegral hWΩU hcoeff hu hfLp v
  exact exists_value_eq_value_restrictL_allOrders_of_uniformlyElliptic hH hΩW haW
    (fun i j ↦ (hsmooth i j).mono hWsub) (hf.mono hWsub) huW
    (fun hν ψ hψ hψc hψs ↦ hu0 hν ψ hψ hψc (hψs.trans hWsub)) hV hVW

end TauCeti.PDE

end LocalRegularity
