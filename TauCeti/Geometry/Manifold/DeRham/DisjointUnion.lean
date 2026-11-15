/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.PoincarePairing
public import Mathlib.LinearAlgebra.DFinsupp

/-!
# De Rham cohomology and Poincaré pairing on disjoint open unions

For pairwise disjoint open subsets `U : ι → Opens M` with union `W = ⨆ i, U i`:
* Restriction gives `SmoothForm.piEquiv : Ω^k(W) ≃ₗ[ℝ] ∀ i, Ω^k(U i)` commuting with `d`, hence
  `deRhamCohomology.piEquiv : H^k_dR(⨆ i, U i) ≃ₗ[ℝ] ∀ i, H^k_dR(U i)`.
* On a Hausdorff manifold, summing extensions by zero gives `compactlySupportedForms.dfinsuppEquiv`
  and `compactlySupportedDeRhamCohomology.dfinsuppEquiv : (Π₀ i, H^l_c(U i)) ≃ₗ[ℝ] H^l_c(⨆ i, U i)`.
* Under `DFinsupp.lsum`, `TauCeti.poincarePairing` decomposes componentwise, giving
  `TauCeti.bijective_poincarePairing_iSup`.

## References
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17 and Problem 18-7.
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §5.
-/

public section

noncomputable section

open Function Set TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

section DisjointHelpers

variable {M ι : Type*} [TopologicalSpace M] {U : ι → Opens M}

private theorem eq_of_mem_disjoint_opens (hdisj : Pairwise (Disjoint on U)) {i j : ι} {x : M}
    (hi : x ∈ U i) (hj : x ∈ U j) : i = j :=
  by_contra fun hij ↦ ((hdisj hij).le_bot ⟨hi, hj⟩).elim

private theorem isClosed_setOf_mem_disjoint_opens (hdisj : Pairwise (Disjoint on U)) (i : ι) :
    IsClosed {x : (⨆ j, U j : Opens M) | (x : M) ∈ U i} := by
  rw [← isOpen_compl_iff]
  have hcompl : {x : (⨆ j, U j : Opens M) | (x : M) ∈ U i}ᶜ =
      ⋃ (j : ι) (_ : j ≠ i), {x : (⨆ k, U k : Opens M) | (x : M) ∈ U j} := by
    ext x; simp only [mem_compl_iff, mem_ofPred_eq, mem_iUnion, exists_prop]
    refine ⟨fun hni ↦ ?_, fun ⟨j, hji, hj⟩ hxi ↦ hji (eq_of_mem_disjoint_opens hdisj hj hxi)⟩
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp x.2
    exact ⟨j, fun hji ↦ hni (hji ▸ hj), hj⟩
  rw [hcompl]
  exact isOpen_iUnion fun j ↦ isOpen_iUnion fun _ ↦ (U j).isOpen.preimage continuous_subtype_val

end DisjointHelpers

section PiecewiseForms

variable {E H M F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {U : ι → Opens M} {k : ℕ}

private theorem ext_roughForm_iSup {γ₁ γ₂ : RoughForm I (⨆ i, U i : Opens M) F k}
    (h : ∀ i, TauCeti.mpullback I I (Opens.inclusion (le_iSup U i)) γ₁ =
      TauCeti.mpullback I I (Opens.inclusion (le_iSup U i)) γ₂) : γ₁ = γ₂ := by
  funext x; obtain ⟨i, hi⟩ := Opens.mem_iSup.mp x.2; ext v
  have hx := DFunLike.congr_fun (congrFun (h i) ⟨x, hi⟩) v
  rwa [mpullback_inclusion_apply, mpullback_inclusion_apply] at hx

private def piecewiseRoughForm (U : ι → Opens M) (η : ∀ i, RoughForm I (U i) F k) :
    RoughForm I (⨆ i, U i : Opens M) F k :=
  fun x ↦ η (Classical.choose (Opens.mem_iSup.mp x.2))
    ⟨x, Classical.choose_spec (Opens.mem_iSup.mp x.2)⟩

private theorem mpullback_inclusion_piecewiseRoughForm (hdisj : Pairwise (Disjoint on U))
    (η : ∀ i, RoughForm I (U i) F k) (i : ι) :
    TauCeti.mpullback I I (Opens.inclusion (le_iSup U i)) (piecewiseRoughForm U η) = η i := by
  funext y; ext v; rw [mpullback_inclusion_apply]
  have haux : ∀ {j : ι} (hj : (y : M) ∈ U j), (η j ⟨y, hj⟩ : E [⋀^Fin k]→L[ℝ] F) = η i y := by
    intro j hj; obtain rfl := eq_of_mem_disjoint_opens hdisj hj y.2; rfl
  exact DFunLike.congr_fun
    (haux (Classical.choose_spec (Opens.mem_iSup.mp (Opens.inclusion (le_iSup U i) y).2))) v

variable (I) in
/-- Smooth forms on a union of pairwise disjoint opens `U i` are linearly equivalent to families of
smooth forms on the `U i`, via restriction along the open inclusions. -/
def SmoothForm.piEquiv [IsManifold I 1 M] (hdisj : Pairwise (Disjoint on U)) (k : ℕ) :
    SmoothForm I (⨆ i, U i : Opens M) F k ≃ₗ[ℝ] ∀ i, SmoothForm I (U i) F k where
  toFun φ i := SmoothForm.mpullback (Opens.inclusion (le_iSup U i)) (contMDiff_inclusion _) φ
  map_add' φ ψ := funext fun _ ↦ map_add _ φ ψ
  map_smul' c φ := funext fun _ ↦ map_smul _ c φ
  invFun η := ⟨piecewiseRoughForm U fun i ↦ (η i).1,
    (IsSmoothForm.of_mpullback_inclusion (le_iSup U) (fun x ↦ Opens.mem_iSup.mp x.2) fun i ↦ by
      rw [mpullback_inclusion_piecewiseRoughForm hdisj]; exact (η i).isSmoothForm
    ).mem_smoothBundleForms⟩
  left_inv _ := Subtype.ext <| ext_roughForm_iSup fun _ ↦ by
    dsimp only; rw [mpullback_inclusion_piecewiseRoughForm hdisj, SmoothForm.coe_mpullback]
  right_inv _ := funext fun _ ↦ Subtype.ext <| by
    dsimp only; rw [SmoothForm.coe_mpullback, mpullback_inclusion_piecewiseRoughForm hdisj]

variable (I) in
/-- Component `i` of `SmoothForm.piEquiv` is pullback along `U i ≤ ⨆ j, U j`. -/
@[simp]
theorem SmoothForm.piEquiv_apply [IsManifold I 1 M] (hdisj : Pairwise (Disjoint on U)) (k : ℕ)
    (φ : SmoothForm I (⨆ i, U i : Opens M) F k) (i : ι) :
    SmoothForm.piEquiv I hdisj k φ i =
      SmoothForm.mpullback (Opens.inclusion (le_iSup U i)) (contMDiff_inclusion _) φ := (rfl)

variable (I) in
/-- The product decomposition of smooth forms on pairwise disjoint opens commutes with `d`. -/
theorem SmoothForm.piEquiv_mextDerivₗ [IsManifold I 2 M] (hdisj : Pairwise (Disjoint on U))
    (k : ℕ) (φ : SmoothForm I (⨆ i, U i : Opens M) F k) (i : ι) :
    SmoothForm.piEquiv I hdisj (k + 1) (mextDerivₗ I k φ) i =
      mextDerivₗ I k (SmoothForm.piEquiv I hdisj k φ i) :=
  (SmoothForm.mextDerivₗ_mpullback (Opens.inclusion (le_iSup U i)) (contMDiff_inclusion _) k φ).symm

end PiecewiseForms

section DeRhamCohomology

variable {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {U : ι → Opens M}

/-- Restriction to the members of a pairwise disjoint open family is bijective on de Rham
cohomology. -/
theorem deRhamCohomology.bijective_pi_map (hdisj : Pairwise (Disjoint on U)) (k : ℕ) :
    Bijective (LinearMap.pi fun i ↦
      deRhamCohomology.map (I := I) (I' := I) (Opens.inclusion (le_iSup U i))
        (contMDiff_inclusion _) k) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun c hc ↦ ?_, fun c ↦ ?_⟩
  · obtain ⟨φ, rfl⟩ := deRhamCohomology.mk_surjective I k c
    have hexact (i : ι) : SmoothForm.piEquiv I hdisj k φ.1 i ∈ exactForms I (U i) k := by
      simpa only [LinearMap.pi_apply, Pi.zero_apply, deRhamCohomology.map_mk,
        deRhamCohomology.mk_eq_zero_iff, closedForms.coe_mpullback,
        SmoothForm.piEquiv_apply] using congrFun hc i
    rw [deRhamCohomology.mk_eq_zero_iff]
    cases k with
    | zero =>
      rw [exactForms_zero, Submodule.mem_bot]
      refine (SmoothForm.piEquiv I hdisj 0).injective (funext fun i ↦ ?_)
      simpa only [exactForms_zero, Submodule.mem_bot, map_zero, Pi.zero_apply] using hexact i
    | succ m =>
      simp only [exactForms_succ, LinearMap.mem_range] at hexact ⊢
      choose η hη using hexact
      refine ⟨(SmoothForm.piEquiv I hdisj m).symm η,
        (SmoothForm.piEquiv I hdisj (m + 1)).injective (funext fun i ↦ ?_)⟩
      rw [SmoothForm.piEquiv_mextDerivₗ, LinearEquiv.apply_symm_apply, hη]
  · choose φ hφ using fun i ↦ deRhamCohomology.mk_surjective I k (c i)
    let Φ := (SmoothForm.piEquiv I hdisj k).symm (fun i ↦ (φ i).1)
    have hΦ : Φ ∈ closedForms I (⨆ i, U i : Opens M) k :=
      (mem_closedForms_iff_mextDerivₗ_eq_zero I Φ).mpr <|
        (SmoothForm.piEquiv I hdisj (k + 1)).injective <| funext fun i ↦ by
          rw [SmoothForm.piEquiv_mextDerivₗ, map_zero, Pi.zero_apply]
          simpa only [Φ, LinearEquiv.apply_symm_apply] using
            (mem_closedForms_iff_mextDerivₗ_eq_zero I (φ i).1).mp (φ i).2
    refine ⟨deRhamCohomology.mk I k ⟨Φ, hΦ⟩, funext fun i ↦ ?_⟩
    rw [LinearMap.pi_apply, deRhamCohomology.map_mk, ← hφ i]
    exact congrArg (deRhamCohomology.mk I k) <| Subtype.ext <|
      (closedForms.coe_mpullback _ _ _ _).trans <|
        congrFun ((SmoothForm.piEquiv I hdisj k).apply_symm_apply (fun j ↦ (φ j).1)) i

/-- **De Rham cohomology of a disjoint open union.** -/
def deRhamCohomology.piEquiv (hdisj : Pairwise (Disjoint on U)) (k : ℕ) :
    deRhamCohomology I (⨆ i, U i : Opens M) k ≃ₗ[ℝ] ∀ i, deRhamCohomology I (U i) k :=
  LinearEquiv.ofBijective _ (deRhamCohomology.bijective_pi_map I hdisj k)

/-- Component `i` of `deRhamCohomology.piEquiv` is restriction along `U i ≤ ⨆ j, U j`. -/
@[simp]
theorem deRhamCohomology.piEquiv_apply (hdisj : Pairwise (Disjoint on U)) (k : ℕ)
    (x : deRhamCohomology I (⨆ i, U i : Opens M) k) (i : ι) :
    deRhamCohomology.piEquiv I hdisj k x i =
      deRhamCohomology.map (Opens.inclusion (le_iSup U i)) (contMDiff_inclusion _) k x :=
  congrFun (LinearEquiv.ofBijective_apply _ x) i

end DeRhamCohomology

section CompactlySupported

variable {E H M ι : Type*} [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] {U : ι → Opens M}

namespace compactlySupportedForms

section Forms

variable [IsManifold I 1 M]

private theorem mpullback_inclusion_lsum_extendByZero (hdisj : Pairwise (Disjoint on U)) (k : ℕ)
    (f : Π₀ i, compactlySupportedForms I (U i) k) (j : ι) :
    TauCeti.mpullback I I (Opens.inclusion (le_iSup U j))
      ((DFinsupp.lsum ℝ (fun i ↦ extendByZero (le_iSup U i) k) f :
        SmoothForm I (⨆ i, U i : Opens M) ℝ k).1) = (f j : SmoothForm I (U j) ℝ k).1 := by
  induction f using DFinsupp.induction with
  | h0 => funext y; simp only [map_zero, Submodule.coe_zero, mpullback_inclusion_apply]; rfl
  | ha i ψ f _ _ ih =>
    simp only [map_add, DFinsupp.lsum_single, Submodule.coe_add, mpullback_add, ih,
      DFinsupp.add_apply]
    by_cases hij : i = j
    · subst hij; rw [DFinsupp.single_eq_same, coe_extendByZero,
        RoughForm.mpullback_inclusion_extendByZero]
    · have hzero : TauCeti.mpullback I I (Opens.inclusion (le_iSup U j))
          ((extendByZero (le_iSup U i) k ψ : SmoothForm I (⨆ i, U i : Opens M) ℝ k).1) = 0 := by
        rw [coe_extendByZero, RoughForm.mpullback_inclusion_extendByZero_eq_extendByZero]
        exact funext fun y ↦ RoughForm.extendByZero_apply_of_notMem _
          fun hy ↦ hij (eq_of_mem_disjoint_opens hdisj hy y.2)
      rw [hzero, DFinsupp.single_eq_of_ne (Ne.symm hij), Submodule.coe_zero, Submodule.coe_zero]

omit [DecidableEq ι] in
private theorem exists_extendByZero_eq_restrict (hdisj : Pairwise (Disjoint on U)) {k : ℕ}
    (φ : compactlySupportedForms I (⨆ i, U i : Opens M) k) (i : ι) :
    ∃ ψ : compactlySupportedForms I (U i) k,
      ((extendByZero (le_iSup U i) k ψ : SmoothForm I (⨆ j, U j : Opens M) ℝ k).1) =
        RoughForm.extendByZero (⨆ j, U j : Opens M)
          (TauCeti.mpullback I I (Opens.inclusion (le_iSup U i)) φ.1.1) := by
  let W : Opens M := ⨆ j, U j
  let θ : RoughForm I W ℝ k :=
    RoughForm.extendByZero W (TauCeti.mpullback I I (Opens.inclusion (le_iSup U i)) φ.1.1)
  have hθ_smooth : IsSmoothForm I ∞ θ :=
    IsSmoothForm.of_mpullback_inclusion (le_iSup U) (fun x ↦ Opens.mem_iSup.mp x.2) fun j ↦ by
      by_cases hij : i = j
      · subst hij; dsimp only [θ]
        rw [RoughForm.mpullback_inclusion_extendByZero,
          ← SmoothForm.coe_mpullback (Opens.inclusion (le_iSup U i)) (contMDiff_inclusion _) φ.1]
        exact (SmoothForm.mpullback (Opens.inclusion (le_iSup U i))
          (contMDiff_inclusion _) φ.1).isSmoothForm
      · have hzero : TauCeti.mpullback I I (Opens.inclusion (le_iSup U j)) θ = 0 := by
          dsimp only [θ]; rw [RoughForm.mpullback_inclusion_extendByZero_eq_extendByZero]
          exact funext fun y ↦ RoughForm.extendByZero_apply_of_notMem _
            fun hy ↦ hij (eq_of_mem_disjoint_opens hdisj hy y.2)
        exact hzero ▸ IsSmoothForm.zero ∞
  have hθ_supp : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) θ ⊆
      _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ.1.1 ∩ {x : W | (x : M) ∈ U i} :=
    closure_minimal
      (fun x (hx0 : θ x ≠ 0) ↦ by
        have hxi : (x : M) ∈ U i :=
          by_contra fun hni ↦ hx0 (RoughForm.extendByZero_apply_of_notMem _ hni)
        refine ⟨subset_tsupport _ fun hφ0 ↦ hx0 ?_, hxi⟩
        dsimp only [θ]; rw [RoughForm.extendByZero_apply_of_mem _ hxi, mpullback_inclusion_apply]
        exact hφ0)
      ((_root_.isClosed_tsupport _).inter (isClosed_setOf_mem_disjoint_opens hdisj i))
  let Θ : compactlySupportedForms I W k :=
    ⟨⟨θ, hθ_smooth.mem_smoothBundleForms⟩, (mem_compactlySupportedForms I).mpr <|
      ((mem_compactlySupportedForms I).mp φ.2).of_isClosed_subset (_root_.isClosed_tsupport _)
        (hθ_supp.trans inter_subset_left)⟩
  obtain ⟨ψ, hψ⟩ := (mem_range_extendByZero_iff (le_iSup U i) (φ := Θ)).mpr
    (hθ_supp.trans inter_subset_right)
  exact ⟨ψ, congrArg (fun χ : compactlySupportedForms I W k ↦ χ.1.1) hψ⟩

variable (I) in
/-- Summing extensions by zero from pairwise disjoint opens `U i` is bijective on compactly
supported smooth forms. -/
theorem bijective_lsum_extendByZero (hdisj : Pairwise (Disjoint on U)) (k : ℕ) :
    Bijective (DFinsupp.lsum ℝ fun i ↦ extendByZero (I := I) (le_iSup U i) k) := by
  refine ⟨fun f₁ f₂ hf ↦ DFinsupp.ext fun j ↦ Subtype.ext <| Subtype.ext ?_, fun φ ↦ ?_⟩
  · rw [← mpullback_inclusion_lsum_extendByZero hdisj k f₁ j,
      ← mpullback_inclusion_lsum_extendByZero hdisj k f₂ j, hf]
  · choose ψ hψ using exists_extendByZero_eq_restrict hdisj φ
    obtain ⟨s, hs⟩ := ((mem_compactlySupportedForms I).mp φ.2).elim_finite_subcover
      (fun i ↦ {x : (⨆ j, U j : Opens M) | (x : M) ∈ U i})
      (fun i ↦ (U i).isOpen.preimage continuous_subtype_val) fun x _ ↦
        let ⟨i, hi⟩ := Opens.mem_iSup.mp x.2; mem_iUnion.mpr ⟨i, hi⟩
    refine ⟨DFinsupp.mk s (fun i ↦ ψ i.1),
      Subtype.ext <| Subtype.ext <| ext_roughForm_iSup fun j ↦ ?_⟩
    rw [mpullback_inclusion_lsum_extendByZero hdisj, DFinsupp.mk_apply]
    split_ifs with hjs
    · rw [← RoughForm.mpullback_inclusion_extendByZero (le_iSup U j) (ψ j).1.1,
        ← coe_extendByZero (le_iSup U j), hψ j, RoughForm.mpullback_inclusion_extendByZero]
    · rw [Submodule.coe_zero, Submodule.coe_zero]; funext y; rw [mpullback_inclusion_apply]
      refine (_root_.image_eq_zero_of_notMem_tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) fun hyK ↦ ?_).symm
      obtain ⟨i, his, hyi⟩ := mem_iUnion₂.mp (hs hyK)
      exact hjs (eq_of_mem_disjoint_opens hdisj y.2 hyi ▸ his)

variable (I) in
/-- **Compactly supported forms on a disjoint open union.** -/
def dfinsuppEquiv (hdisj : Pairwise (Disjoint on U)) (k : ℕ) :
    (Π₀ i, compactlySupportedForms I (U i) k) ≃ₗ[ℝ]
      compactlySupportedForms I (⨆ i, U i : Opens M) k :=
  LinearEquiv.ofBijective _ (bijective_lsum_extendByZero I hdisj k)

/-- On a single summand, `compactlySupportedForms.dfinsuppEquiv` is extension by zero. -/
@[simp]
theorem dfinsuppEquiv_single (hdisj : Pairwise (Disjoint on U)) (k : ℕ) (i : ι)
    (φ : compactlySupportedForms I (U i) k) :
    dfinsuppEquiv I hdisj k (DFinsupp.single i φ) = extendByZero (le_iSup U i) k φ := by
  rw [dfinsuppEquiv, LinearEquiv.ofBijective_apply, DFinsupp.lsum_single]

end Forms

/-- The direct-sum equivalence on compactly supported forms commutes with `d`. -/
theorem mextDerivₗ_dfinsuppEquiv [IsManifold I 2 M] (hdisj : Pairwise (Disjoint on U)) (k : ℕ)
    (f : Π₀ i, compactlySupportedForms I (U i) k) :
    mextDerivₗ I (⨆ i, U i : Opens M) k (dfinsuppEquiv I hdisj k f) =
      dfinsuppEquiv I hdisj (k + 1)
        (DFinsupp.mapRange.linearMap (fun i ↦ mextDerivₗ I (U i) k) f) :=
  LinearMap.congr_fun
    (f := (mextDerivₗ I (⨆ i, U i : Opens M) k).comp (dfinsuppEquiv I hdisj k).toLinearMap)
    (g := (dfinsuppEquiv I hdisj (k + 1)).toLinearMap.comp
      (DFinsupp.mapRange.linearMap fun i ↦ mextDerivₗ I (U i) k))
    (DFinsupp.lhom_ext' fun _ ↦ LinearMap.ext fun _ ↦ by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, DFinsupp.lsingle_apply,
        dfinsuppEquiv_single, DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_single,
        mextDerivₗ_extendByZero]) f

end compactlySupportedForms

namespace compactlySupportedClosedForms

variable [IsManifold I 2 M]

/-- Relating extension by zero of closed forms to `compactlySupportedForms.dfinsuppEquiv`. -/
theorem coe_lsum_extendByZero (hdisj : Pairwise (Disjoint on U)) (l : ℕ)
    (φ : Π₀ i, compactlySupportedClosedForms I (U i) l) :
    (DFinsupp.lsum ℝ (fun i ↦ extendByZero (le_iSup U i) l) φ).1 =
      (compactlySupportedForms.dfinsuppEquiv I hdisj l
        (DFinsupp.mapRange.linearMap
          (fun i ↦ Submodule.inclusion
            (compactlySupportedClosedForms_le_compactlySupportedForms I l)) φ)).1 :=
  LinearMap.congr_fun
    (f := (compactlySupportedClosedForms I (⨆ i, U i : Opens M) l).subtype.comp
      (DFinsupp.lsum ℝ fun i ↦ extendByZero (le_iSup U i) l))
    (g := (compactlySupportedForms I (⨆ i, U i : Opens M) l).subtype.comp
      ((compactlySupportedForms.dfinsuppEquiv I hdisj l).toLinearMap.comp
        (DFinsupp.mapRange.linearMap fun i ↦ Submodule.inclusion
          (compactlySupportedClosedForms_le_compactlySupportedForms I l))))
    (DFinsupp.lhom_ext' fun _ ↦ LinearMap.ext fun _ ↦ Subtype.ext <| by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, DFinsupp.lsingle_apply,
        DFinsupp.lsum_single, Submodule.subtype_apply, DFinsupp.mapRange.linearMap_apply,
        DFinsupp.mapRange_single, compactlySupportedForms.dfinsuppEquiv_single,
        coe_extendByZero, compactlySupportedForms.coe_extendByZero, Submodule.coe_inclusion]) φ

variable (I) in
/-- Summing extensions by zero from pairwise disjoint opens `U i` is bijective on compactly
supported closed forms. -/
theorem bijective_lsum_extendByZero (hdisj : Pairwise (Disjoint on U)) (l : ℕ) :
    Bijective (DFinsupp.lsum ℝ fun i ↦ extendByZero (I := I) (le_iSup U i) l) := by
  classical
  refine ⟨fun φ₁ φ₂ hφ ↦ DFinsupp.ext fun i ↦ ?_, fun Φ ↦ ?_⟩
  · have h := (compactlySupportedForms.dfinsuppEquiv I hdisj l).injective <| Subtype.ext <|
      (coe_lsum_extendByZero hdisj l φ₁).symm.trans <|
        (congrArg Subtype.val hφ).trans (coe_lsum_extendByZero hdisj l φ₂)
    simpa only [DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_apply,
      Submodule.coe_inclusion, Subtype.ext_iff] using
      congrArg Subtype.val (DFunLike.congr_fun h i)
  · let φ := (compactlySupportedForms.dfinsuppEquiv I hdisj l).symm
      ⟨Φ.1, compactlySupportedClosedForms_le_compactlySupportedForms I l Φ.2⟩
    have hd : compactlySupportedForms.mextDerivₗ I (⨆ i, U i : Opens M) l
        (compactlySupportedForms.dfinsuppEquiv I hdisj l φ) = 0 :=
      Subtype.ext <| by
        rw [LinearEquiv.apply_symm_apply, compactlySupportedForms.coe_mextDerivₗ,
          Submodule.coe_zero]
        exact (mem_closedForms_iff_mextDerivₗ_eq_zero I Φ.1).mp
          (compactlySupportedClosedForms_le_closedForms I l Φ.2)
    rw [compactlySupportedForms.mextDerivₗ_dfinsuppEquiv] at hd
    have hclosed (i : ι) : (φ i).1 ∈ closedForms I (U i) l := by
      have hi := congrArg Subtype.val <| DFunLike.congr_fun
        ((compactlySupportedForms.dfinsuppEquiv I hdisj (l + 1)).map_eq_zero_iff.mp hd) i
      rw [DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_apply, DFinsupp.zero_apply,
        compactlySupportedForms.coe_mextDerivₗ, Submodule.coe_zero] at hi
      exact (mem_closedForms_iff_mextDerivₗ_eq_zero I (φ i).1).mpr hi
    let liftClosed (i : ι) (ψ : compactlySupportedForms I (U i) l) :
        compactlySupportedClosedForms I (U i) l :=
      if h : ψ.1 ∈ closedForms I (U i) l then
        ⟨ψ.1, (mem_compactlySupportedClosedForms I).mpr ⟨ψ.2, h⟩⟩
      else 0
    let φc := φ.mapRange liftClosed fun i ↦ by simp [liftClosed]
    have hφc : DFinsupp.mapRange.linearMap
        (fun i ↦ Submodule.inclusion
          (compactlySupportedClosedForms_le_compactlySupportedForms I l)) φc = φ :=
      DFinsupp.ext fun j ↦ Subtype.ext <| by
        simp only [φc, liftClosed, DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_apply,
          dite_eq_left (hclosed j), Submodule.coe_inclusion]
    refine ⟨φc, Subtype.ext ?_⟩
    rw [coe_lsum_extendByZero hdisj, hφc, LinearEquiv.apply_symm_apply]

variable (I) in
/-- **Compactly supported closed forms on a disjoint open union.** -/
def dfinsuppEquiv (hdisj : Pairwise (Disjoint on U)) (l : ℕ) :
    (Π₀ i, compactlySupportedClosedForms I (U i) l) ≃ₗ[ℝ]
      compactlySupportedClosedForms I (⨆ i, U i : Opens M) l :=
  LinearEquiv.ofBijective _ (bijective_lsum_extendByZero I hdisj l)

/-- On a single summand, `compactlySupportedClosedForms.dfinsuppEquiv` is extension by zero. -/
@[simp]
theorem dfinsuppEquiv_single (hdisj : Pairwise (Disjoint on U)) (l : ℕ) (i : ι)
    (ψ : compactlySupportedClosedForms I (U i) l) :
    dfinsuppEquiv I hdisj l (DFinsupp.single i ψ) = extendByZero (le_iSup U i) l ψ := by
  rw [dfinsuppEquiv, LinearEquiv.ofBijective_apply, DFinsupp.lsum_single]

end compactlySupportedClosedForms

namespace compactlySupportedDeRhamCohomology

variable [IsManifold I 2 M]

private theorem lsum_extendByZero_mapRange_mk (hdisj : Pairwise (Disjoint on U)) (l : ℕ)
    (φ : Π₀ i, compactlySupportedClosedForms I (U i) l) :
    DFinsupp.lsum ℝ (fun i ↦ extendByZero (le_iSup U i) l)
      (DFinsupp.mapRange.linearMap (fun i ↦ mk I l) φ) =
        mk I l (compactlySupportedClosedForms.dfinsuppEquiv I hdisj l φ) :=
  LinearMap.congr_fun
    (f := (DFinsupp.lsum ℝ fun i ↦ extendByZero (le_iSup U i) l).comp
      (DFinsupp.mapRange.linearMap fun i ↦ mk I l))
    (g := (mk I l).comp (compactlySupportedClosedForms.dfinsuppEquiv I hdisj l).toLinearMap)
    (DFinsupp.lhom_ext' fun _ ↦ LinearMap.ext fun _ ↦ by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, DFinsupp.lsingle_apply,
        DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_single, DFinsupp.lsum_single,
        extendByZero_mk, compactlySupportedClosedForms.dfinsuppEquiv_single]) φ

private theorem mem_exactCompactlySupportedForms_of_dfinsuppEquiv
    (hdisj : Pairwise (Disjoint on U)) {l : ℕ}
    {φ : Π₀ i, compactlySupportedClosedForms I (U i) l}
    (hexact : (compactlySupportedClosedForms.dfinsuppEquiv I hdisj l φ).1 ∈
      exactCompactlySupportedForms I (⨆ i, U i : Opens M) l) (i : ι) :
    (φ i).1 ∈ exactCompactlySupportedForms I (U i) l := by
  classical
  rw [compactlySupportedClosedForms.dfinsuppEquiv, LinearEquiv.ofBijective_apply,
    compactlySupportedClosedForms.coe_lsum_extendByZero hdisj l φ] at hexact
  cases l with
  | zero =>
    rw [exactCompactlySupportedForms_zero, Submodule.mem_bot] at hexact ⊢
    have h0i := DFunLike.congr_fun
      ((compactlySupportedForms.dfinsuppEquiv I hdisj 0).map_eq_zero_iff.mp (Subtype.ext hexact)) i
    simpa only [DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_apply, DFinsupp.zero_apply,
      Submodule.coe_inclusion, Submodule.coe_zero] using congrArg Subtype.val h0i
  | succ m =>
    rw [exactCompactlySupportedForms_succ, Submodule.mem_map] at hexact ⊢
    obtain ⟨η, hηc, hη⟩ := hexact
    let ψ := (compactlySupportedForms.dfinsuppEquiv I hdisj m).symm ⟨η, hηc⟩
    have hd : compactlySupportedForms.mextDerivₗ I (⨆ j, U j : Opens M) m
        (compactlySupportedForms.dfinsuppEquiv I hdisj m ψ) =
        compactlySupportedForms.dfinsuppEquiv I hdisj (m + 1)
          (DFinsupp.mapRange.linearMap
            (fun j ↦ Submodule.inclusion
              (compactlySupportedClosedForms_le_compactlySupportedForms I (m + 1))) φ) :=
      Subtype.ext <| by
        simpa only [ψ, LinearEquiv.apply_symm_apply, compactlySupportedForms.coe_mextDerivₗ]
          using hη
    rw [compactlySupportedForms.mextDerivₗ_dfinsuppEquiv] at hd
    have hcomp := DFunLike.congr_fun
      ((compactlySupportedForms.dfinsuppEquiv I hdisj (m + 1)).injective hd) i
    simp only [DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_apply] at hcomp
    exact ⟨(ψ i).1, (ψ i).2, by
      rw [← compactlySupportedForms.coe_mextDerivₗ]; exact congrArg Subtype.val hcomp⟩

variable (I) in
/-- Summing extensions by zero from pairwise disjoint opens `U i` is bijective on compactly
supported de Rham cohomology. -/
theorem bijective_lsum_extendByZero (hdisj : Pairwise (Disjoint on U)) (l : ℕ) :
    Bijective (DFinsupp.lsum ℝ fun i ↦ extendByZero (I := I) (le_iSup U i) l) := by
  classical
  refine ⟨(injective_iff_map_eq_zero _).mpr fun c hc ↦ ?_, fun y ↦ ?_⟩
  · let liftClosed (i : ι) (x : compactlySupportedDeRhamCohomology I (U i) l) :
        compactlySupportedClosedForms I (U i) l :=
      if x = 0 then 0 else Classical.choose (mk_surjective I l x)
    have hlift (i : ι) (x : compactlySupportedDeRhamCohomology I (U i) l) :
        mk I l (liftClosed i x) = x := by
      dsimp only [liftClosed]; split_ifs with hx
      · exact hx ▸ map_zero _
      · exact Classical.choose_spec (mk_surjective I l x)
    let φ := c.mapRange liftClosed (fun _ ↦ by simp [liftClosed])
    have hcφ : DFinsupp.mapRange.linearMap (fun i ↦ mk I l) φ = c :=
      DFinsupp.ext fun i ↦ hlift i (c i)
    rw [← hcφ, lsum_extendByZero_mapRange_mk hdisj, mk_eq_zero_iff] at hc
    exact hcφ ▸ DFinsupp.ext fun i ↦ by
      simpa only [DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_apply, DFinsupp.zero_apply,
        mk_eq_zero_iff] using mem_exactCompactlySupportedForms_of_dfinsuppEquiv hdisj hc i
  · obtain ⟨Φ, rfl⟩ := mk_surjective I l y
    exact ⟨DFinsupp.mapRange.linearMap (fun i ↦ mk I l)
        ((compactlySupportedClosedForms.dfinsuppEquiv I hdisj l).symm Φ),
      (lsum_extendByZero_mapRange_mk hdisj l _).trans
        (congrArg _ (LinearEquiv.apply_symm_apply _ Φ))⟩

variable (I) in
/-- **Compactly supported de Rham cohomology of a disjoint open union.** -/
def dfinsuppEquiv (hdisj : Pairwise (Disjoint on U)) (l : ℕ) :
    (Π₀ i, compactlySupportedDeRhamCohomology I (U i) l) ≃ₗ[ℝ]
      compactlySupportedDeRhamCohomology I (⨆ i, U i : Opens M) l :=
  LinearEquiv.ofBijective _ (bijective_lsum_extendByZero I hdisj l)

/-- On a single summand, `compactlySupportedDeRhamCohomology.dfinsuppEquiv` is extension by zero. -/
@[simp]
theorem dfinsuppEquiv_single (hdisj : Pairwise (Disjoint on U)) (l : ℕ) (i : ι)
    (y : compactlySupportedDeRhamCohomology I (U i) l) :
    dfinsuppEquiv I hdisj l (DFinsupp.single i y) = extendByZero (le_iSup U i) l y := by
  rw [dfinsuppEquiv, LinearEquiv.ofBijective_apply, DFinsupp.lsum_single]

end compactlySupportedDeRhamCohomology

end CompactlySupported

section PoincarePairing

variable {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] {U : ι → Opens M} {k l : ℕ}

/-- On a single summand `U i` of a pairwise disjoint open union, the Poincaré pairing on `⨆ j, U j`
evaluates via `deRhamCohomology.piEquiv` and the Poincaré pairing on `U i`. -/
theorem poincarePairing_dfinsuppEquiv_single [DecidableEq ι]
    (o : Manifold.Orientation I M (Fin (k + l)))
    [∀ i, SigmaCompactSpace (U i)] [SigmaCompactSpace (⨆ i, U i : Opens M)]
    (hdisj : Pairwise (Disjoint on U)) (x : deRhamCohomology I (⨆ i, U i : Opens M) k) (i : ι)
    (y : compactlySupportedDeRhamCohomology I (U i) l) :
    poincarePairing I (⨆ j, U j : Opens M) (o.restrict _) x
      (compactlySupportedDeRhamCohomology.dfinsuppEquiv I hdisj l (DFinsupp.single i y)) =
        poincarePairing I (U i) (o.restrict (U i))
          (deRhamCohomology.piEquiv I hdisj k x i) y := by
  rw [compactlySupportedDeRhamCohomology.dfinsuppEquiv_single, poincarePairing_extendByZero,
    deRhamCohomology.piEquiv_apply]

/-- **Disjoint-union step for Poincaré duality.** -/
theorem bijective_poincarePairing_iSup (o : Manifold.Orientation I M (Fin (k + l)))
    [∀ i, SigmaCompactSpace (U i)] [SigmaCompactSpace (⨆ i, U i : Opens M)]
    (hdisj : Pairwise (Disjoint on U))
    (hbij : ∀ i, Bijective (poincarePairing I (U i) (o.restrict (U i)))) :
    Bijective (poincarePairing I (⨆ i, U i : Opens M) (o.restrict (⨆ i, U i : Opens M))) := by
  classical
  let e₂ := compactlySupportedDeRhamCohomology.dfinsuppEquiv I hdisj l
  let eTot := (deRhamCohomology.piEquiv I hdisj k).trans <|
    (LinearEquiv.piCongrRight fun i ↦
      LinearEquiv.ofBijective (poincarePairing I (U i) (o.restrict (U i))) (hbij i)).trans
      (DFinsupp.lsum ℝ)
  have hcomm : e₂.dualMap.toLinearMap.comp
      (poincarePairing I (⨆ i, U i : Opens M) (o.restrict _)) = eTot.toLinearMap := by
    ext x : 1
    refine DFinsupp.lhom_ext' fun i ↦ LinearMap.ext fun y ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.dualMap_apply,
      DFinsupp.lsingle_apply, LinearEquiv.trans_apply, DFinsupp.lsum_single,
      LinearEquiv.piCongrRight_apply, LinearEquiv.ofBijective_apply, e₂, eTot,
      poincarePairing_dfinsuppEquiv_single]
  refine (Bijective.of_comp_iff' e₂.dualMap.bijective _).mp ?_
  change Bijective (e₂.dualMap.toLinearMap.comp
    (poincarePairing I (⨆ i, U i : Opens M) (o.restrict _)))
  exact hcomm ▸ eTot.bijective

end PoincarePairing

end TauCeti
