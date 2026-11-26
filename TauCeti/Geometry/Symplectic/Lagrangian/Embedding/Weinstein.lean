/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.Riemannian.Basic
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Normal
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.DifferentialForm.Opens.Diffeomorph
import TauCeti.Geometry.Manifold.TubularNeighborhood.Riemannian.Coordinates
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Lift
import TauCeti.Geometry.Symplectic.Lagrangian.CompatibleMetric
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.CompatibleMetric
import TauCeti.Geometry.Symplectic.Manifold.Opens
import TauCeti.Geometry.Symplectic.Manifold.RelativeMoser

/-!
# Weinstein's Lagrangian neighborhood theorem

Every compact boundaryless Lagrangian submanifold `i : Q → M` embedded in a boundaryless Hausdorff
symplectic manifold `(M, σ)` has an open neighborhood `U` symplectomorphic to an open neighborhood
`V` of the zero section of the cotangent bundle `T*Q` with its canonical symplectic form
`CotangentBundle.symplecticForm`, by a diffeomorphism sending each `i q` to the zero covector at `q`
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_diffeomorph_opens_cotangent_of_isLagrangianEmbedding`).

Consequently, given a compact boundaryless embedded Lagrangian `i : Q → (M, σ)`, a boundaryless
embedded Lagrangian `j : Q' → (N, τ)`, and any smooth diffeomorphism `f : Q ≃ₘ Q'`, open
neighborhoods of `i(Q)` and `j(Q')` are symplectomorphic by a diffeomorphism extending `j ∘ f`
along `i(Q)`
(`SmoothTwoForm.IsSymplectic.exists_diffeomorph_opens_of_isLagrangianEmbedding_comp_diffeomorph`,
with `f = Diffeomorph.refl` in
`TauCeti.SmoothTwoForm.IsSymplectic.exists_diffeomorph_opens_of_isLagrangianEmbedding`).

## Proof outline

1. When `Q` is empty, the empty open subsets are vacuously symplectomorphic. When `Q` is nonempty,
   `Q` is compact Hausdorff (`hi.isEmbedding.t2Space`), hence locally compact, so Riesz's theorem on
   manifolds (`FiniteDimensional.of_locallyCompact_manifold`) and
   `SymplecticForm.IsLagrangian.finite` give `FiniteDimensional ℝ F` and `FiniteDimensional ℝ E`
   (`IsLagrangianEmbedding.finiteDimensional`). Covering the compact image `i(Q)` by finitely many
   chart domains (`ChartedSpace.exists_opens_secondCountableTopology`) produces a second-countable
   open neighborhood `M₀ : Opens M` of `i(Q)` to which `σ` and `i` restrict.
2. On `M₀`, choose a `σ|_{M₀}`-compatible smooth almost complex structure `J`
   (`SmoothTwoForm.IsNondegenerate.exists_compatible`) and endow `TM₀` with its smooth compatible
   Riemannian metric `g_x(u, w) = σ_x(u, J x w)` (`SmoothTwoForm.Compatible.metric`).
3. Identify the intrinsic normal bundle of `i` with `T*Q` via `[v] ↦ σ(di_q ·, v)`
   (`SmoothEmbedding.normalBundleDiffeomorphOfIsLagrangianMap`) and compose its inverse with the
   Riemannian normal exponential map (`SmoothEmbedding.exists_partialDiffeomorph_normalExp_subset`)
   to obtain a diffeomorphism `Ψ : W₀ ≃ₘ W` from an open neighborhood `W₀` of the zero section of
   `T*Q` onto an open neighborhood `W` of `i(Q)` in `M₀`.
4. At each zero covector `(q, 0) ∈ T*Q`, the differential of `Ψ` sends `(u, α)` to
   `di_q u + n_α`, where `n_α` is the metric-orthogonal normal representative of `[n_α] ↔ α`
   (`SmoothEmbedding.mfderiv_normalExp_comp_normalBundleDiffeomorph_symm_zeroSection`). Because
   `di_q(T_q Q)` is Lagrangian and `g` is a `σ`-compatible metric, `(di_q(T_q Q))ᗮ` is also
   Lagrangian (`SymplecticForm.IsLagrangian.isLagrangian_submodule_orthogonal`), hence isotropic; by
   `SymplecticForm.IsIsotropic.apply_add`, `Ψ^* σ` agrees on all full tangent spaces along the zero
   section with `CotangentBundle.symplecticForm`.
5. Apply the open-neighborhood relative Moser transport
   (`SmoothTwoForm.exists_diffeomorph_opens_of_mpullback_symm_eq_along`) on `M₀` to deform
   `(Ψ⁻¹)^* ω_can` to `σ|_W` while fixing `i(Q)` pointwise, then flatten the open domain in `M₀`
   to `M` via `Diffeomorph.opensImage`.

## Main results

* `TauCeti.SmoothEmbedding.mfderiv_normalExp_comp_normalBundleDiffeomorph_symm_zeroSection`: the
  differential of cotangent normal-exponential coordinates at a zero covector `(q, 0)` sends
  `w` to `df_q w.1 + n_(w.2)`.
* `TauCeti.SmoothEmbedding.mpullback_normalExp_comp_normalBundleDiffeomorph_symm_zeroSection`: when
  `(df_q(T_q Q))ᗮ` is isotropic, cotangent normal-exponential coordinates pull `σ` back at `(q, 0)`
  to `CotangentBundle.symplecticForm`.
* `TauCeti.SmoothTwoForm.IsSymplectic.exists_diffeomorph_opens_cotangent_of_isLagrangianEmbedding`:
  Weinstein's Lagrangian neighborhood theorem (Cannas da Silva, Theorem 9.3).
* `SmoothTwoForm.IsSymplectic.exists_diffeomorph_opens_of_isLagrangianEmbedding_comp_diffeomorph`
  and `TauCeti.SmoothTwoForm.IsSymplectic.exists_diffeomorph_opens_of_isLagrangianEmbedding`:
  equivalence of neighborhoods of diffeomorphic compact embedded Lagrangians (Cannas da Silva,
  Theorem 8.4 and Corollary 9.4).

## References

* A. Weinstein, *Symplectic manifolds and their Lagrangian submanifolds*, Advances in Mathematics 6
  (1971), 329–346, Theorem 6.1.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Theorem 8.4 (p. 48) and Theorem 9.3 (p. 51).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  University Press, 2017, Theorem 3.4.13.
-/

public noncomputable section

open Bundle Manifold Set TopologicalSpace
open scoped ContDiff Manifold RealInnerProductSpace Topology

namespace TauCeti

/-! ### Cotangent normal-exponential coordinates along the zero section -/

namespace SmoothEmbedding

variable {F E H' H Q M : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H'] [TopologicalSpace H]
  {J : ModelWithCorners ℝ F H'} {I : ModelWithCorners ℝ E H}
  [TopologicalSpace Q] [ChartedSpace H' Q] [IsManifold J ∞ Q]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]
  [RiemannianBundle (fun y : M ↦ TangentSpace I y)]
  [IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y)]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate}

/-- Vertical component of the differential of cotangent normal-exponential coordinates at `(q, 0)`:
along the fiber line `t ↦ (q, t • α)`, the derivative is the orthogonal normal representative of
the normal class corresponding to `α`. -/
private theorem mfderiv_normalExp_comp_normalBundleDiffeomorph_symm_inr
    (f : SmoothEmbedding J I ∞ Q M) (hf : hσ.IsLagrangianMap J f)
    (hdim : Module.finrank ℝ (F →L[ℝ] ℝ) = Module.finrank ℝ E - Module.finrank ℝ F) (q : Q)
    (α : TangentSpace J q →L[ℝ] ℝ) :
    haveI : IsManifold J 1 Q := .of_le (n := ∞) (by simp)
    haveI : IsManifold J (∞ + 1) Q := by simpa using (inferInstance : IsManifold J ∞ Q)
    letI := f.normalSpaceFiberBundle (by simp) hdim
    mfderiv (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) I
        (f.normalExp (P := F →L[ℝ] ℝ) (by simp) ∘
          (f.normalBundleDiffeomorphOfIsLagrangianMap (m := ∞) (P := F →L[ℝ] ℝ)
            hf (by simp) (by simp) (by simp) hdim).symm)
        (zeroSection (F →L[ℝ] ℝ) (fun x : Q ↦ TangentSpace J x →L[ℝ] ℝ) q)
        ((Bundle.zeroSectionTangentEquiv (I := J) (F := F →L[ℝ] ℝ)
          (V := fun x : Q ↦ TangentSpace J x →L[ℝ] ℝ) q).symm (0, α)) =
      f.normalRepresentative q (by simp)
        ((f.normalSpaceEquivOfIsLagrangianMap hf (by simp) q).symm α) := by
  have : IsManifold J 1 Q := .of_le (n := ∞) (by simp)
  have : IsManifold J (1 + 1) Q := .of_le (n := ∞) (by norm_cast)
  have : IsManifold I (1 + 1) M := .of_le (n := ∞) (by norm_cast)
  have : IsManifold J (∞ + 1) Q := by simpa using (inferInstance : IsManifold J ∞ Q)
  let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  let := f.normalSpaceContMDiffVectorBundle (m := 1) hn (by simp) hdim
  let E_eq := f.normalBundleDiffeomorphOfIsLagrangianMap (m := ∞) (P := F →L[ℝ] ℝ)
    hf hn (by simp) (by simp) hdim
  let z₀ := zeroSection (F →L[ℝ] ℝ) (fun x : Q ↦ TangentSpace J x →L[ℝ] ℝ) q
  let n₀ := zeroSection (F →L[ℝ] ℝ) (fun x : Q ↦ f.NormalSpace x hn) q
  have hEn : E_eq.symm z₀ = n₀ :=
    (f.normalBundleDiffeomorphOfIsLagrangianMap_symm_apply (m := ∞) (P := F →L[ℝ] ℝ)
      hf hn (by simp) (by simp) hdim ⟨q, 0⟩).trans (by simp [n₀, zeroSection])
  have he : MDifferentiableAt (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) I (f.normalExp (P := F →L[ℝ] ℝ) hn) n₀ :=
    ((f.contMDiffOn_normalExp (m := 1) hn (by simp) hdim).contMDiffAt
      ((f.isOpen_normalExpDomain hn hdim).mem_nhds
        (f.zeroSection_mem_normalExpDomain hn q))).mdifferentiableAt one_ne_zero
  have hG : MDifferentiableAt (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) I
      (f.normalExp (P := F →L[ℝ] ℝ) hn ∘ E_eq.symm) z₀ :=
    (hEn ▸ he).comp z₀ (E_eq.symm.contMDiff.mdifferentiableAt hn)
  rw [Bundle.zeroSectionTangentEquiv_symm_inr]
  let v := (f.normalSpaceEquivOfIsLagrangianMap hf hn q).symm α
  have hlC : ContMDiff 𝓘(ℝ) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) 1
      (fun t : ℝ ↦ (⟨q, t • α⟩ : CotangentBundle J Q)) :=
    contMDiff_id.smul_totalSpace (contMDiff_const (c := (⟨q, α⟩ : CotangentBundle J Q)))
  have hlN : ContMDiff 𝓘(ℝ) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) 1
      (fun t : ℝ ↦ (⟨q, t • v⟩ : TotalSpace (F →L[ℝ] ℝ) (fun x ↦ f.NormalSpace x hn))) :=
    contMDiff_id.smul_totalSpace
      (contMDiff_const (c := (⟨q, v⟩ : TotalSpace (F →L[ℝ] ℝ) (fun x ↦ f.NormalSpace x hn))))
  have h1 := mfderiv_comp_apply_of_eq (0 : ℝ) hG
    (hlC.mdifferentiableAt one_ne_zero) (by simp [z₀, zeroSection]) (1 : ℝ)
  have h2 := mfderiv_comp_apply_of_eq (0 : ℝ) he
    (hlN.mdifferentiableAt one_ne_zero) (by simp [n₀, zeroSection]) (1 : ℝ)
  have hlines : (f.normalExp (P := F →L[ℝ] ℝ) hn ∘ E_eq.symm) ∘
      (fun t : ℝ ↦ (⟨q, t • α⟩ : CotangentBundle J Q)) =
      f.normalExp (P := F →L[ℝ] ℝ) hn ∘ fun t : ℝ ↦ ⟨q, t • v⟩ := funext fun t ↦ by
    simpa [E_eq, v, map_smul] using congrArg (f.normalExp hn)
      (f.normalBundleDiffeomorphOfIsLagrangianMap_symm_apply (m := ∞) (P := F →L[ℝ] ℝ)
        hf hn (by simp) (by simp) hdim ⟨q, t • α⟩)
  have h3 := f.mfderiv_normalExp_zeroSection_apply (P := F →L[ℝ] ℝ) hn (by simp) hdim q 0 v
  rw [Bundle.zeroSectionTangentEquiv_symm_inr, map_zero, zero_add] at h3
  exact h1.symm.trans
    ((congrArg (fun g ↦ mfderiv 𝓘(ℝ) I g 0 (1 : ℝ)) hlines).trans (h2.trans h3))

/-- **Differential of cotangent normal-exponential coordinates at the zero section.** Identifying
the normal bundle of a smooth Lagrangian embedding `f : Q → M` with `T*Q` and following by the
Riemannian normal exponential map gives a map whose differential at `(q, 0)` sends `(u, α)` to
`df_q u` plus the orthogonal normal representative of the normal class corresponding to `α`. -/
theorem mfderiv_normalExp_comp_normalBundleDiffeomorph_symm_zeroSection
    (f : SmoothEmbedding J I ∞ Q M) (hf : hσ.IsLagrangianMap J f)
    (hdim : Module.finrank ℝ (F →L[ℝ] ℝ) = Module.finrank ℝ E - Module.finrank ℝ F) (q : Q)
    (w : TangentSpace (J.prod 𝓘(ℝ, F →L[ℝ] ℝ))
      (zeroSection (F →L[ℝ] ℝ) (fun x : Q ↦ TangentSpace J x →L[ℝ] ℝ) q)) :
    haveI : IsManifold J 1 Q := .of_le (n := ∞) (by simp)
    haveI : IsManifold J (∞ + 1) Q := by simpa using (inferInstance : IsManifold J ∞ Q)
    letI := f.normalSpaceFiberBundle (by simp) hdim
    mfderiv (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) I
        (f.normalExp (P := F →L[ℝ] ℝ) (by simp) ∘
          (f.normalBundleDiffeomorphOfIsLagrangianMap (m := ∞) (P := F →L[ℝ] ℝ)
            hf (by simp) (by simp) (by simp) hdim).symm)
        (zeroSection (F →L[ℝ] ℝ) (fun x : Q ↦ TangentSpace J x →L[ℝ] ℝ) q) w =
      mfderiv J I f q w.1 +
        f.normalRepresentative q (by simp)
          ((f.normalSpaceEquivOfIsLagrangianMap hf (by simp) q).symm w.2) := by
  have : IsManifold J 1 Q := .of_le (n := ∞) (by simp)
  have : IsManifold J (1 + 1) Q := .of_le (n := ∞) (by norm_cast)
  have : IsManifold I (1 + 1) M := .of_le (n := ∞) (by norm_cast)
  have : IsManifold J (∞ + 1) Q := by simpa using (inferInstance : IsManifold J ∞ Q)
  let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  let := f.normalSpaceContMDiffVectorBundle (m := 1) hn (by simp) hdim
  let E_eq := f.normalBundleDiffeomorphOfIsLagrangianMap (m := ∞) (P := F →L[ℝ] ℝ)
    hf hn (by simp) (by simp) hdim
  let z₀ := zeroSection (F →L[ℝ] ℝ) (fun x : Q ↦ TangentSpace J x →L[ℝ] ℝ) q
  let n₀ := zeroSection (F →L[ℝ] ℝ) (fun x : Q ↦ f.NormalSpace x hn) q
  have hEn (y : Q) : E_eq.symm (zeroSection (F →L[ℝ] ℝ) (fun x : Q ↦ TangentSpace J x →L[ℝ] ℝ) y) =
      zeroSection (F →L[ℝ] ℝ) (fun x : Q ↦ f.NormalSpace x hn) y :=
    (f.normalBundleDiffeomorphOfIsLagrangianMap_symm_apply (m := ∞) (P := F →L[ℝ] ℝ)
      hf hn (by simp) (by simp) hdim ⟨y, 0⟩).trans (by simp [zeroSection])
  have hEn₀ : E_eq.symm z₀ = n₀ := hEn q
  have he : MDifferentiableAt (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) I (f.normalExp (P := F →L[ℝ] ℝ) hn) n₀ :=
    ((f.contMDiffOn_normalExp (m := 1) hn (by simp) hdim).contMDiffAt
      ((f.isOpen_normalExpDomain hn hdim).mem_nhds
        (f.zeroSection_mem_normalExpDomain hn q))).mdifferentiableAt one_ne_zero
  have hG : MDifferentiableAt (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) I
      (f.normalExp (P := F →L[ℝ] ℝ) hn ∘ E_eq.symm) z₀ :=
    (hEn₀ ▸ he).comp z₀ (E_eq.symm.contMDiff.mdifferentiableAt hn)
  let e := Bundle.zeroSectionTangentEquiv (I := J)
    (F := F →L[ℝ] ℝ) (V := fun x : Q ↦ TangentSpace J x →L[ℝ] ℝ) q
  have hw : w = e.symm ((e w).1, (e w).2) := (e.symm_apply_apply w).symm
  have he1 : (e w).1 = w.1 := by
    dsimp only [e]
    rw [Bundle.zeroSectionTangentEquiv_apply]
  have he2 : (e w).2 = w.2 := by
    dsimp only [e]
    rw [Bundle.zeroSectionTangentEquiv_apply, CotangentBundle.symmL_trivializationAt_self]
  rw [congrArg (mfderiv (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) I _ z₀) hw,
    Bundle.zeroSectionTangentEquiv_symm_eq, map_add, ← he1, ← he2]
  congr 1
  · have h := mfderiv_comp_apply q hG (mdifferentiableAt_zeroSection ℝ _) (e w).1
    have hfun : (f.normalExp (P := F →L[ℝ] ℝ) hn ∘ E_eq.symm) ∘
        zeroSection (F →L[ℝ] ℝ) (fun x : Q ↦ TangentSpace J x →L[ℝ] ℝ) = f := funext fun y ↦ by
      simp [hEn]
    exact (hfun ▸ h).symm
  · exact f.mfderiv_normalExp_comp_normalBundleDiffeomorph_symm_inr hf hdim q (e w).2

/-- **Form agreement along the zero section.** When the metric orthogonal complement
`(df_q(T_q Q))ᗮ` is isotropic for `σ_(f q)`, the cotangent normal-exponential map pulls `σ` back
at `(q, 0) ∈ T*Q` to the canonical symplectic form `CotangentBundle.symplecticForm J Q` on the
full tangent space of `T*Q`. -/
theorem mpullback_normalExp_comp_normalBundleDiffeomorph_symm_zeroSection
    (f : SmoothEmbedding J I ∞ Q M) (hf : hσ.IsLagrangianMap J f)
    (hdim : Module.finrank ℝ (F →L[ℝ] ℝ) = Module.finrank ℝ E - Module.finrank ℝ F) (q : Q)
    (hiso : (hσ.symplecticFormAt (f q)).IsIsotropic (f.tangentRange q (by simp))ᗮ) :
    haveI : IsManifold J 1 Q := .of_le (n := ∞) (by simp)
    haveI : IsManifold J (∞ + 1) Q := by simpa using (inferInstance : IsManifold J ∞ Q)
    letI := f.normalSpaceFiberBundle (by simp) hdim
    mpullback (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) I
        (f.normalExp (P := F →L[ℝ] ℝ) (by simp) ∘
          (f.normalBundleDiffeomorphOfIsLagrangianMap (m := ∞) (P := F →L[ℝ] ℝ)
            hf (by simp) (by simp) (by simp) hdim).symm)
        σ.val (zeroSection (F →L[ℝ] ℝ) (fun x : Q ↦ TangentSpace J x →L[ℝ] ℝ) q) =
      (CotangentBundle.symplecticForm J Q).val
        (zeroSection (F →L[ℝ] ℝ) (fun x : Q ↦ TangentSpace J x →L[ℝ] ℝ) q) := by
  have : IsManifold J 1 Q := .of_le (n := ∞) (by simp)
  have : IsManifold J (∞ + 1) Q := by simpa using (inferInstance : IsManifold J ∞ Q)
  let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  let := f.normalSpaceFiberBundle hn hdim
  let z₀ := zeroSection (F →L[ℝ] ℝ) (fun x : Q ↦ TangentSpace J x →L[ℝ] ℝ) q
  let E_eq := f.normalBundleDiffeomorphOfIsLagrangianMap (m := ∞) (P := F →L[ℝ] ℝ)
    hf hn (by simp) (by simp) hdim
  let G := f.normalExp (P := F →L[ℝ] ℝ) hn ∘ E_eq.symm
  have hEz : E_eq.symm z₀ = zeroSection (F →L[ℝ] ℝ) (fun x : Q ↦ f.NormalSpace x hn) q :=
    (f.normalBundleDiffeomorphOfIsLagrangianMap_symm_apply (m := ∞) (P := F →L[ℝ] ℝ)
      hf hn (by simp) (by simp) hdim ⟨q, 0⟩).trans (by simp [zeroSection])
  have hGz : G z₀ = f q := by simp [G, hEz]
  ext v
  let nF (α : TangentSpace J q →L[ℝ] ℝ) : TangentSpace I (f q) :=
    f.normalRepresentative q hn ((f.normalSpaceEquivOfIsLagrangianMap hf hn q).symm α)
  have hpair (u : TangentSpace J q) (α : TangentSpace J q →L[ℝ] ℝ) :
      (hσ.symplecticFormAt (f q)) (mfderiv J I f q u) (nF α) = α u := by
    have hcov : f.pairingCovector σ q (nF α) = α := by
      rw [← f.normalSpaceEquivOfIsLagrangianMap_normalClass hf hn q (nF α),
        f.normalClass_normalRepresentative, ContinuousLinearEquiv.apply_symm_apply]
    simpa only [SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply,
      ← f.pairingCovector_apply_apply] using DFunLike.congr_fun hcov u
  have hd (i : Fin 2) :
      mfderiv (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) I G z₀ (v i) =
        mfderiv J I f q (v i).1 + nF (v i).2 :=
    f.mfderiv_normalExp_comp_normalBundleDiffeomorph_symm_zeroSection hf hdim q (v i)
  have hv : mfderiv (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) I G z₀ ∘ v =
      ![mfderiv (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) I G z₀ (v 0),
        mfderiv (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) I G z₀ (v 1)] :=
    funext fun i ↦ by fin_cases i <;> rfl
  -- Transport evaluation at `G z₀` along `hGz : G z₀ = f q`, where both tangent spaces are `E`.
  have hσ_eq {y₁ y₂ : M} (hy : y₁ = y₂) (a b : E) : σ.val y₁ ![a, b] = σ.val y₂ ![a, b] := by
    cases hy; rfl
  have heval : σ.val (G z₀) (mfderiv (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) I G z₀ ∘ v) =
      (hσ.symplecticFormAt (f q))
        (mfderiv J I f q (v 0).1 + nF (v 0).2)
        (mfderiv J I f q (v 1).1 + nF (v 1).2) := by
    rw [hv, hd 0, hd 1, SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply,
      SmoothBundleForm.eval₂_apply]
    exact hσ_eq hGz _ _
  refine (TauCeti.mpullback_apply G σ.val z₀ v).trans (heval.trans ?_)
  refine (((SmoothTwoForm.IsNondegenerate.isLagrangianMap_iff_forall.1 hf q).isIsotropic).apply_add
    hiso ⟨(v 0).1, rfl⟩ ⟨(v 1).1, rfl⟩
    (f.normalRepresentative_mem_orthogonal q hn _)
    (f.normalRepresentative_mem_orthogonal q hn _)).trans ?_
  refine (congrArg₂ Sub.sub (hpair (v 0).1 (v 1).2) (hpair (v 1).1 (v 0).2)).trans ?_
  exact ((CotangentBundle.symplecticForm_apply z₀ v).trans
    (strongDualCotangentSymplecticForm_apply (V := F) (v 0) (v 1))).symm

end SmoothEmbedding

/-! ### Weinstein's Lagrangian neighborhood theorem -/

section WeinsteinHelpers

/-- Normal-exponential coordinates on an open neighborhood of the zero section of `T*Q` for a
nonempty Lagrangian embedding into a Riemannian manifold: restricting `f.normalExp` along the
normal-bundle identification with `T*Q` yields open subsets `W₀ ⊆ T*Q` and `W ⊆ M` and a
diffeomorphism `Ψ : W₀ ≃ₘ W` agreeing with `f.normalExp ∘ E_eq.symm`. -/
private theorem exists_cotangent_normalExp_opens_diffeomorph
    {F E H' H Q M : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H'] [TopologicalSpace H]
    {J : ModelWithCorners ℝ F H'} {I : ModelWithCorners ℝ E H}
    [TopologicalSpace Q] [ChartedSpace H' Q] [IsManifold J ∞ Q] [J.Boundaryless] [Nonempty Q]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [SecondCountableTopology M]
    [RiemannianBundle (fun y : M ↦ TangentSpace I y)]
    [IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y)]
    {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate}
    (f : SmoothEmbedding J I ∞ Q M) (hf : hσ.IsLagrangianMap J f)
    (hdim : Module.finrank ℝ (F →L[ℝ] ℝ) = Module.finrank ℝ E - Module.finrank ℝ F) :
    ∃ (W₀ : Opens (CotangentBundle J Q)) (W : Opens M)
      (Ψ : W₀ ≃ₘ⟮J.prod 𝓘(ℝ, F →L[ℝ] ℝ), I⟯ W),
      (∀ q, ∃ hq : zeroSection (F →L[ℝ] ℝ) (fun x : Q ↦ TangentSpace J x →L[ℝ] ℝ) q ∈ W₀,
        (Ψ ⟨zeroSection (F →L[ℝ] ℝ) (fun x : Q ↦ TangentSpace J x →L[ℝ] ℝ) q, hq⟩ : M) = f q) ∧
      (∀ z : W₀,
        haveI : IsManifold J 1 Q := .of_le (n := ∞) (by simp)
        haveI : IsManifold J (∞ + 1) Q := by simpa using (inferInstance : IsManifold J ∞ Q)
        letI := f.normalSpaceFiberBundle (by simp) hdim
        (Ψ z : M) = f.normalExp (P := F →L[ℝ] ℝ) (by simp)
          ((f.normalBundleDiffeomorphOfIsLagrangianMap (m := ∞) (P := F →L[ℝ] ℝ)
            hf (by simp) (by simp) (by simp) hdim).symm z)) := by
  have : IsManifold J 1 Q := .of_le (n := ∞) (by simp)
  have : IsManifold J (∞ + 1) Q := by simpa using (inferInstance : IsManifold J ∞ Q)
  let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  let := f.normalSpaceFiberBundle hn hdim
  let E_eq := f.normalBundleDiffeomorphOfIsLagrangianMap (m := ∞) (P := F →L[ℝ] ℝ)
    hf hn (by simp) (by simp) hdim
  obtain ⟨Ψ₀, hzero₀, -, -, -, hΨ₀⟩ :=
    f.exists_partialDiffeomorph_normalExp_subset (P := F →L[ℝ] ℝ) (m := ∞)
      hn (by simp) (by simp) hdim isOpen_univ (subset_univ _)
  let S₀ : Opens (TotalSpace (F →L[ℝ] ℝ) (fun x ↦ f.NormalSpace x hn)) :=
    ⟨Ψ₀.source, Ψ₀.open_source⟩
  let W : Opens M := ⟨Ψ₀.target, Ψ₀.open_target⟩
  let W₀ : Opens (CotangentBundle J Q) := ⟨E_eq.symm ⁻¹' Ψ₀.source,
    Ψ₀.open_source.preimage E_eq.symm.continuous⟩
  have hiff (z : CotangentBundle J Q) : z ∈ W₀ ↔ E_eq.symm z ∈ S₀ := Iff.rfl
  let Ψ : W₀ ≃ₘ⟮J.prod 𝓘(ℝ, F →L[ℝ] ℝ), I⟯ W :=
    (E_eq.symm.subtype hiff).trans Ψ₀.toDiffeomorphSourceTarget
  have hΨ_val (z : W₀) : (Ψ z : M) = f.normalExp hn (E_eq.symm z) :=
    (Ψ₀.toDiffeomorphSourceTarget_apply_coe ((E_eq.symm.subtype hiff) z)).trans
      ((congrFun hΨ₀ _).trans
        (congrArg (f.normalExp hn) (E_eq.symm.subtype_apply_coe hiff z)))
  refine ⟨W₀, W, Ψ, fun q ↦ ?_, hΨ_val⟩
  have hEq0 : E_eq.symm (zeroSection (F →L[ℝ] ℝ) (fun x : Q ↦ TangentSpace J x →L[ℝ] ℝ) q) =
      zeroSection (F →L[ℝ] ℝ) (fun x ↦ f.NormalSpace x hn) q :=
    (f.normalBundleDiffeomorphOfIsLagrangianMap_symm_apply (m := ∞) (P := F →L[ℝ] ℝ)
      hf hn (by simp) (by simp) hdim ⟨q, 0⟩).trans (by simp [zeroSection])
  have hq : zeroSection (F →L[ℝ] ℝ) (fun x : Q ↦ TangentSpace J x →L[ℝ] ℝ) q ∈ W₀ :=
    Opens.mem_mk.2 (mem_preimage.2 (hEq0.symm ▸ hzero₀ q))
  refine ⟨hq, (hΨ_val ⟨_, hq⟩).trans ?_⟩
  rw [hEq0, f.normalExp_zeroSection hn]

/-- For a nonempty Lagrangian embedding `i : Q → (M, σ)`, compatible Riemannian normal-exponential
coordinates give open subsets `W₀ ⊆ T*Q` and `W ⊆ M` and a diffeomorphism `Ψ : W₀ ≃ₘ W` sending
`(q, 0)` to `i q` whose inverse pulls `CotangentBundle.symplecticForm|_{W₀}` back to `σ|_W` at
every point of `i(Q)`. -/
private theorem exists_cotangent_normalExp_mpullback_eq_along
    {E H M F H' Q : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SecondCountableTopology M]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
    [TopologicalSpace Q] [ChartedSpace H' Q] [IsManifold J ∞ Q] [Nonempty Q]
    {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
    {i : Q → M} (hi : hσ.isNondegenerate.IsLagrangianEmbedding J i) :
    ∃ (W₀ : Opens (CotangentBundle J Q)) (W : Opens M)
      (Ψ : W₀ ≃ₘ⟮J.prod 𝓘(ℝ, F →L[ℝ] ℝ), I⟯ W),
      (∀ q, ∃ hq : TotalSpace.mk' (F →L[ℝ] ℝ) q 0 ∈ W₀, (Ψ ⟨_, hq⟩ : M) = i q) ∧
      ∀ (q : Q) (hx : i q ∈ W),
        (SmoothForm.mpullback Ψ.symm Ψ.symm.contMDiff
          (SmoothForm.mpullback (Subtype.val : W₀ → CotangentBundle J Q) contMDiff_subtypeVal
            (CotangentBundle.symplecticForm J Q))).val ⟨i q, hx⟩ =
        (SmoothForm.mpullback (Subtype.val : W → M) contMDiff_subtypeVal σ).val ⟨i q, hx⟩ := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨J_acs, hJ⟩ := hσ.isNondegenerate.exists_compatible
  let : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
    ⟨hJ.metric.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y) :=
    Bundle.instIsContMDiffRiemannianBundle hJ.metric
  let f : SmoothEmbedding J I ∞ Q M := .ofIsSmoothEmbedding i hi.isSmoothEmbedding
  have hf : hσ.isNondegenerate.IsLagrangianMap J f := by
    rw [SmoothEmbedding.coe_ofIsSmoothEmbedding]
    exact hi.isLagrangianMap
  have hdim : Module.finrank ℝ (F →L[ℝ] ℝ) = Module.finrank ℝ E - Module.finrank ℝ F :=
    f.finrank_continuousLinearMap_eq_sub_of_isLagrangianMap hf (by simp)
  obtain ⟨W₀, W, Ψ, hΨzero, hΨexp⟩ := exists_cotangent_normalExp_opens_diffeomorph f hf hdim
  refine ⟨W₀, W, Ψ, fun q ↦ ?_, fun q hx ↦ ?_⟩
  · obtain ⟨hq, hval⟩ := hΨzero q
    exact ⟨hq, hval.trans (SmoothEmbedding.ofIsSmoothEmbedding_apply _ _ q)⟩
  · obtain ⟨hq, hqval⟩ := hΨzero q
    let zq : W₀ := ⟨zeroSection (F →L[ℝ] ℝ) (fun x : Q ↦ TangentSpace J x →L[ℝ] ℝ) q, hq⟩
    have hzx : Ψ zq = ⟨i q, hx⟩ := Subtype.ext
      (hqval.trans (SmoothEmbedding.ofIsSmoothEmbedding_apply _ _ q))
    have : IsManifold J 1 Q := .of_le (n := ∞) (by simp)
    have : IsManifold J (∞ + 1) Q := by simpa using (inferInstance : IsManifold J ∞ Q)
    let := f.normalSpaceFiberBundle (by simp) hdim
    have hiso : (hσ.isNondegenerate.symplecticFormAt (f q)).IsIsotropic
        (f.tangentRange q (by simp))ᗮ :=
      ((SmoothTwoForm.IsNondegenerate.isLagrangianMap_iff_forall.1 hf q)
        |>.isLagrangian_submodule_orthogonal (J := J_acs.almostComplexStructureAt (f q))
        fun v w ↦ by
          rw [SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply,
            SmoothAlmostComplexStructure.almostComplexStructureAt_apply,
            hJ.inner_eq_eval₂]).isIsotropic
    exact SmoothForm.mpullback_symm_subtype_eq_of_apply_eq Ψ hzx
      (f.mpullback_normalExp_comp_normalBundleDiffeomorph_symm_zeroSection hf hdim q hiso)
      hΨexp

end WeinsteinHelpers

namespace SmoothTwoForm.IsSymplectic

/-- **Weinstein's Lagrangian neighborhood theorem** (Weinstein 1971, Theorem 6.1; Cannas da Silva,
Theorem 9.3, p. 51). Let `(M, σ)` be a boundaryless Hausdorff symplectic manifold and `i : Q → M`
a Lagrangian embedding of a compact boundaryless smooth manifold `Q`. Then there exist an open
neighborhood `U` of `i(Q)` in `M`, an open neighborhood `V` of the zero section in
`CotangentBundle J Q`, and a diffeomorphism `φ : U ≃ₘ V` sending `i q` to the zero covector at `q`
for every `q : Q` and pulling the restriction of `CotangentBundle.symplecticForm J Q` to `V` back
to the restriction of `σ` to `U`. -/
theorem exists_diffeomorph_opens_cotangent_of_isLagrangianEmbedding
    {E H M F H' Q : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
    [TopologicalSpace Q] [ChartedSpace H' Q] [IsManifold J ∞ Q] [CompactSpace Q]
    {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
    {i : Q → M} (hi : hσ.isNondegenerate.IsLagrangianEmbedding J i) :
    ∃ (U : Opens M) (V : Opens (CotangentBundle J Q))
      (φ : U ≃ₘ⟮I, J.prod 𝓘(ℝ, F →L[ℝ] ℝ)⟯ V),
      (∀ q, ∃ h : i q ∈ U,
        (φ ⟨i q, h⟩ : CotangentBundle J Q) = TotalSpace.mk' (F →L[ℝ] ℝ) q 0) ∧
      SmoothForm.mpullback φ φ.contMDiff
          (SmoothForm.mpullback (Subtype.val : V → CotangentBundle J Q) contMDiff_subtypeVal
            (CotangentBundle.symplecticForm J Q)) =
        SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtypeVal σ := by
  by_cases hQ : Nonempty Q
  · have : Nonempty Q := hQ
    obtain ⟨hF, hE⟩ := hi.finiteDimensional
    have : FiniteDimensional ℝ F := hF
    have : FiniteDimensional ℝ E := hE
    have : SecondCountableTopology H := I.secondCountableTopology
    obtain ⟨M₀, hM₀, hM₀sc⟩ :=
      ChartedSpace.exists_opens_secondCountableTopology H
        (isCompact_range hi.isEmbedding.continuous)
    have : SecondCountableTopology M₀ := hM₀sc
    let i₀ : Q → M₀ := fun q ↦ ⟨i q, hM₀ (mem_range_self q)⟩
    have hσ₀ := hσ.mpullback_subtype_val M₀
    have hi₀ : hσ₀.isNondegenerate.IsLagrangianEmbedding J i₀ :=
      (hσ.isNondegenerate.isLagrangianEmbedding_subtype_val_comp_iff (U := M₀) (g := i₀)).1 hi
    obtain ⟨W₀, W, Ψ, hΨzero, hΨform⟩ := exists_cotangent_normalExp_mpullback_eq_along hσ₀ hi₀
    let f₀ : SmoothEmbedding J I ∞ Q M₀ := .ofIsSmoothEmbedding i₀ hi₀.isSmoothEmbedding
    have hf₀_coe : ⇑f₀ = i₀ := SmoothEmbedding.coe_ofIsSmoothEmbedding i₀ hi₀.isSmoothEmbedding
    obtain ⟨U₀, V, φ₀, hφ₀, hform₀⟩ :=
      SmoothTwoForm.exists_diffeomorph_opens_of_mpullback_symm_eq_along f₀ hσ₀.isClosed
        CotangentBundle.isSymplectic_symplecticForm.isClosed
        (fun q ↦ hσ₀.isNondegenerate.nondegenerate_bilinFormAt (f₀ q)) Ψ
        (by simpa only [hf₀_coe] using hΨzero)
        (fun q ↦ by rw [congrFun hf₀_coe q]; exact hΨform q)
    refine ⟨_, V, (Diffeomorph.opensImage (I := I) U₀).symm.trans φ₀, fun q ↦ ?_, ?_⟩
    · obtain ⟨hq₀, hval₀⟩ := hφ₀ q
      rw [hf₀_coe] at hq₀
      have hiU : i q ∈
          (⟨Subtype.val '' (U₀ : Set M₀), M₀.isOpen.isOpenMap_subtypeVal _ U₀.isOpen⟩ : Opens M) :=
        ⟨i₀ q, hq₀, rfl⟩
      have hinc : (Diffeomorph.opensImage (I := I) (n := ∞) U₀).symm ⟨i q, hiU⟩ =
          ⟨f₀ q, by rwa [hf₀_coe]⟩ :=
        Subtype.ext ((Diffeomorph.opensImage_symm_apply_coe (I := I) (n := ∞) U₀ ⟨i q, hiU⟩).trans
          (congrFun hf₀_coe q).symm)
      exact ⟨hiU, (congrArg (fun z ↦ (φ₀ z : CotangentBundle J Q)) hinc).trans hval₀⟩
    · rw [SmoothForm.mpullback_trans, hform₀, SmoothForm.mpullback_opensImage_symm]
  · have : IsEmpty Q := not_nonempty_iff.1 hQ
    have : IsEmpty (⊥ : Opens M) := ⟨fun x ↦ x.property⟩
    have : IsEmpty (⊥ : Opens (CotangentBundle J Q)) := ⟨fun y ↦ y.property⟩
    exact ⟨⊥, ⊥, ⟨Equiv.equivOfIsEmpty _ _, fun x ↦ isEmptyElim x, fun y ↦ isEmptyElim y⟩,
      fun q ↦ isEmptyElim q, Subtype.ext (funext fun x ↦ isEmptyElim x)⟩

/-- **Equivalence of Lagrangian neighborhoods over a diffeomorphism** (Cannas da Silva, Theorem 8.4,
p. 48). Given a compact boundaryless Lagrangian embedding `i : Q → (M, σ)`, a boundaryless
Lagrangian embedding `j : Q' → (N, τ)` into boundaryless Hausdorff symplectic manifolds, and a
smooth diffeomorphism `f : Q ≃ₘ Q'`, there exist open neighborhoods `U` of `i(Q)` and `V` of
`j(Q')` and a symplectomorphism `Φ : U ≃ₘ V` sending `i q` to `j (f q)` for every `q : Q`. -/
theorem exists_diffeomorph_opens_of_isLagrangianEmbedding_comp_diffeomorph
    {E H M E' H' N F G Q F' G' Q' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N] [T2Space N]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
    [TopologicalSpace Q] [ChartedSpace G Q] [IsManifold J ∞ Q] [CompactSpace Q]
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [TopologicalSpace G'] {J' : ModelWithCorners ℝ F' G'} [J'.Boundaryless]
    [TopologicalSpace Q'] [ChartedSpace G' Q'] [IsManifold J' ∞ Q']
    {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
    {τ : SmoothTwoForm I' N} (hτ : τ.IsSymplectic)
    {i : Q → M} (hi : hσ.isNondegenerate.IsLagrangianEmbedding J i)
    {j : Q' → N} (hj : hτ.isNondegenerate.IsLagrangianEmbedding J' j)
    (f : Q ≃ₘ⟮J, J'⟯ Q') :
    ∃ (U : Opens M) (V : Opens N) (Φ : U ≃ₘ⟮I, I'⟯ V),
      (∀ q, ∃ h : i q ∈ U, (Φ ⟨i q, h⟩ : N) = j (f q)) ∧
      SmoothForm.mpullback Φ Φ.contMDiff
          (SmoothForm.mpullback (Subtype.val : V → N) contMDiff_subtypeVal τ) =
        SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtypeVal σ := by
  have : CompactSpace Q' := f.toHomeomorph.compactSpace
  obtain ⟨U₁, V₁, φ₁, hφ₁, hform₁⟩ :=
    hσ.exists_diffeomorph_opens_cotangent_of_isLagrangianEmbedding hi
  obtain ⟨U₂, V₂, φ₂, hφ₂, hform₂⟩ :=
    hτ.exists_diffeomorph_opens_cotangent_of_isLagrangianEmbedding hj
  let O₁ : Opens (CotangentBundle J Q) :=
    V₁ ⊓ ⟨f.cotangent ⁻¹' V₂, V₂.isOpen.preimage f.cotangent.continuous⟩
  let O₂ : Opens (CotangentBundle J' Q') :=
    ⟨f.cotangent.symm ⁻¹' V₁, V₁.isOpen.preimage f.cotangent.symm.continuous⟩ ⊓ V₂
  have hO₁₂ (z : CotangentBundle J Q) : z ∈ O₁ ↔ f.cotangent z ∈ O₂ :=
    ⟨fun ⟨hz₁, hz₂⟩ ↦
      ⟨Opens.mem_mk.2 (mem_preimage.2 ((f.cotangent.symm_apply_apply z).symm ▸ hz₁)), hz₂⟩,
     fun ⟨hz₁, hz₂⟩ ↦ ⟨(f.cotangent.symm_apply_apply z) ▸ mem_preimage.1 (Opens.mem_mk.1 hz₁),
      hz₂⟩⟩
  let g : O₁ ≃ₘ⟮J.prod 𝓘(ℝ, F →L[ℝ] ℝ), J'.prod 𝓘(ℝ, F' →L[ℝ] ℝ)⟯ O₂ := f.cotangent.subtype hO₁₂
  obtain ⟨U, hU, ψ₁, hU_mem, hψ₁, hψ₁form⟩ :=
    SmoothForm.exists_diffeomorph_opens_of_le φ₁ hform₁ (inf_le_left : O₁ ≤ V₁)
  obtain ⟨V, hV, ψ₂, hV_mem, hψ₂, hψ₂form⟩ :=
    SmoothForm.exists_diffeomorph_opens_of_le φ₂ hform₂ (inf_le_right : O₂ ≤ V₂)
  refine ⟨U, V, (ψ₁.trans g).trans ψ₂.symm, fun q ↦ ?_, ?_⟩
  · obtain ⟨hx₁, hval₁⟩ := hφ₁ q
    obtain ⟨hy₂, hval₂⟩ := hφ₂ (f q)
    have hcot : f.cotangent (TotalSpace.mk' (F →L[ℝ] ℝ) q 0) =
        TotalSpace.mk' (F' →L[ℝ] ℝ) (f q) 0 := f.cotangent_zeroSection q
    have hxO₁ : (φ₁ ⟨i q, hx₁⟩ : CotangentBundle J Q) ∈ O₁ :=
      ⟨(φ₁ ⟨i q, hx₁⟩).property, Opens.mem_mk.2 (mem_preimage.2 (by
        rw [hval₁, hcot, ← hval₂]
        exact (φ₂ ⟨j (f q), hy₂⟩).property))⟩
    have hxU : i q ∈ U := (hU_mem ⟨i q, hx₁⟩).2 hxO₁
    have hyO₂ : (φ₂ ⟨j (f q), hy₂⟩ : CotangentBundle J' Q') ∈ O₂ := by
      rw [hval₂, ← hcot, ← hval₁]
      exact (hO₁₂ _).1 hxO₁
    have hyV : j (f q) ∈ V := (hV_mem ⟨j (f q), hy₂⟩).2 hyO₂
    refine ⟨hxU, ?_⟩
    have hgeq : g (ψ₁ ⟨i q, hxU⟩) = ψ₂ ⟨j (f q), hyV⟩ :=
      Subtype.ext (by simp [g, hψ₁, hval₁, hcot, hψ₂, hval₂])
    have hΦq : ((ψ₁.trans g).trans ψ₂.symm) ⟨i q, hxU⟩ = ⟨j (f q), hyV⟩ := by simp [hgeq]
    exact congrArg Subtype.val hΦq
  · rw [SmoothForm.mpullback_trans, SmoothForm.mpullback_trans,
      SmoothForm.mpullback_symm_eq_of_mpullback_eq hψ₂form, SmoothForm.mpullback_subtype,
      f.mpullback_cotangent_symplecticForm, hψ₁form]

/-- **Equivalence of neighborhoods of two Lagrangian embeddings of a compact manifold** (Cannas da
Silva, Theorem 8.4, p. 48, and Corollary 9.4, p. 51). Two Lagrangian embeddings `i : Q → (M, σ)`
and `j : Q → (N, τ)` of a compact boundaryless smooth manifold `Q` into boundaryless Hausdorff
symplectic manifolds have symplectomorphic open neighborhoods, by a diffeomorphism sending `i q`
to `j q` for every `q : Q`. -/
theorem exists_diffeomorph_opens_of_isLagrangianEmbedding
    {E H M E' H' N F G Q : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N] [T2Space N]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
    [TopologicalSpace Q] [ChartedSpace G Q] [IsManifold J ∞ Q] [CompactSpace Q]
    {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
    {τ : SmoothTwoForm I' N} (hτ : τ.IsSymplectic)
    {i : Q → M} (hi : hσ.isNondegenerate.IsLagrangianEmbedding J i)
    {j : Q → N} (hj : hτ.isNondegenerate.IsLagrangianEmbedding J j) :
    ∃ (U : Opens M) (V : Opens N) (Φ : U ≃ₘ⟮I, I'⟯ V),
      (∀ q, ∃ h : i q ∈ U, (Φ ⟨i q, h⟩ : N) = j q) ∧
      SmoothForm.mpullback Φ Φ.contMDiff
          (SmoothForm.mpullback (Subtype.val : V → N) contMDiff_subtypeVal τ) =
        SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtypeVal σ := by
  simpa using hσ.exists_diffeomorph_opens_of_isLagrangianEmbedding_comp_diffeomorph hτ hi hj
    (Diffeomorph.refl J Q ∞)

end SmoothTwoForm.IsSymplectic

end TauCeti
