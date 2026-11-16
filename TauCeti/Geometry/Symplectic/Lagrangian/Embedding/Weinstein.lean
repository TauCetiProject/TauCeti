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
import TauCeti.Geometry.Manifold.DifferentialForm.Opens
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.TubularNeighborhood.Riemannian.Coordinates
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Lift
import TauCeti.Geometry.Symplectic.Lagrangian.Orthogonal
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

Consequently, given two compact boundaryless embedded Lagrangians `i : Q → (M, σ)` and
`j : Q' → (N, τ)` and any smooth diffeomorphism `f : Q ≃ₘ Q'`, open neighborhoods of `i(Q)` and
`j(Q')` are symplectomorphic by a diffeomorphism extending `j ∘ f` along `i(Q)`
(`SmoothTwoForm.IsSymplectic.exists_diffeomorph_opens_of_isLagrangianEmbedding_comp_diffeomorph`,
with `f = Diffeomorph.refl` in
`TauCeti.SmoothTwoForm.IsSymplectic.exists_diffeomorph_opens_of_isLagrangianEmbedding`).

## Proof outline

1. When `Q` is empty, the empty open subsets are vacuously symplectomorphic. When `Q` is nonempty,
   `Q` is compact Hausdorff (`hi.isEmbedding.t2Space`), hence locally compact, so Riesz's theorem on
   manifolds (`FiniteDimensional.of_locallyCompact_manifold`) gives `FiniteDimensional ℝ F`, and
   `SymplecticForm.IsLagrangian.finite` gives `FiniteDimensional ℝ E`. Covering the compact image
   `i(Q)` by finitely many chart domains produces a second-countable open neighborhood
   `M₀ : Opens M` of `i(Q)` to which `σ` and `i` restrict.
2. On `M₀`, choose a `σ|_{M₀}`-compatible smooth almost complex structure `J`
   (`SmoothTwoForm.IsNondegenerate.exists_compatible`) and endow `TM₀` with its smooth compatible
   Riemannian metric `g_x(u, w) = σ_x(u, J x w)`
   (`SmoothTwoForm.Compatible.riemannianMetric`).
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
5. Apply the relative Moser theorem
   (`SmoothTwoForm.exists_diffeomorph_fix_embedding_eventually_mpullback_eq`) on `W` to deform
   `(Ψ⁻¹)^* ω_can` to `σ|_W` while fixing `i(Q)` pointwise, then push the open domain in `M₀`
   forward to `M`.

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
        σ.1 (zeroSection (F →L[ℝ] ℝ) (fun x : Q ↦ TangentSpace J x →L[ℝ] ℝ) q) =
      (CotangentBundle.symplecticForm J Q).1
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
  have hσ_eq {y₁ y₂ : M} (hy : y₁ = y₂) (a b : E) : σ.1 y₁ ![a, b] = σ.1 y₂ ![a, b] := by
    cases hy; rfl
  have heval : σ.1 (G z₀) (mfderiv (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) I G z₀ ∘ v) =
      (hσ.symplecticFormAt (f q))
        (mfderiv J I f q (v 0).1 + nF (v 0).2)
        (mfderiv J I f q (v 1).1 + nF (v 1).2) := by
    rw [hv, hd 0, hd 1, SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply,
      SmoothBundleForm.eval₂_apply]
    exact hσ_eq hGz _ _
  refine (TauCeti.mpullback_apply G σ.1 z₀ v).trans (heval.trans ?_)
  refine (((SmoothTwoForm.IsNondegenerate.isLagrangianMap_iff_forall.1 hf q).isIsotropic).apply_add
    hiso ⟨(v 0).1, rfl⟩ ⟨(v 1).1, rfl⟩
    (f.normalRepresentative_mem_orthogonal q hn _)
    (f.normalRepresentative_mem_orthogonal q hn _)).trans ?_
  refine (congrArg₂ Sub.sub (hpair (v 0).1 (v 1).2) (hpair (v 1).1 (v 0).2)).trans ?_
  exact ((CotangentBundle.symplecticForm_apply z₀ v).trans
    (strongDualCotangentSymplecticForm_apply (V := F) (v 0) (v 1))).symm

end SmoothEmbedding

/-! ### Lifting and composing open-neighborhood symplectomorphisms -/

section OpenHelpers

/-- An open subset `S'` of an open subset `W : Opens M` is canonically diffeomorphic to its image
in `M` as an open subset of `M`. -/
private def opensImageDiffeomorph
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {W : Opens M} (S' : Opens W) :
    (⟨Subtype.val '' (S' : Set W), W.isOpen.isOpenMap_subtype_val _ S'.isOpen⟩ : Opens M) ≃ₘ⟮I, I⟯
      S' :=
  let U : Opens M := ⟨Subtype.val '' (S' : Set W), W.isOpen.isOpenMap_subtype_val _ S'.isOpen⟩
  have hUW : U ≤ W := by rintro _ ⟨z, -, rfl⟩; exact z.2
  have memS (x : U) : Opens.inclusion hUW x ∈ S' := by
    rcases x.2 with ⟨z, hz, hzx⟩
    exact (Subtype.ext hzx : z = Opens.inclusion hUW x) ▸ hz
  { toFun := fun x ↦ ⟨Opens.inclusion hUW x, memS x⟩
    invFun := fun z ↦ ⟨z.1.1, ⟨z.1, z.2, rfl⟩⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    contMDiff_toFun := (TauCeti.ContMDiff.subtypeVal_comp_iff S' _).1 (contMDiff_inclusion hUW)
    contMDiff_invFun := (TauCeti.ContMDiff.subtypeVal_comp_iff U _).1
      (ContMDiff.comp (g := (Subtype.val : W → M)) (f := (Subtype.val : S' → W))
        contMDiff_subtype_val contMDiff_subtype_val) }

/-- Given a diffeomorphism `Ξ : W ≃ₘ W₀` between open subsets of `M` and `N` that pulls `τ|_{W₀}`
back to `σ|_W` at every point of an open subset `S ⊆ W`, restricting `Ξ` to `S` and `Ξ '' S`
produces open subsets `U` of `M` and `V` of `N` and a diffeomorphism `φ : U ≃ₘ V` pulling `τ|_V`
back to `σ|_U`. -/
private theorem exists_opens_diffeomorph_of_mpullback_eq_on
    {E H M E' H' N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
    {W : Opens M} {W₀ : Opens N} (Ξ : W ≃ₘ⟮I, I'⟯ W₀)
    {σ : SmoothTwoForm I M} {τ : SmoothTwoForm I' N}
    {S : Set W} (hS : IsOpen S)
    (heq : ∀ z ∈ S,
      (SmoothForm.mpullback Ξ Ξ.contMDiff
        (SmoothForm.mpullback (Subtype.val : W₀ → N) contMDiff_subtype_val τ)).1 z =
      (SmoothForm.mpullback (Subtype.val : W → M) contMDiff_subtype_val σ).1 z) :
    ∃ (U : Opens M) (V : Opens N) (φ : U ≃ₘ⟮I, I'⟯ V),
      (∀ z ∈ S, ∃ hz : (z : M) ∈ U, (φ ⟨z, hz⟩ : N) = Ξ z) ∧
      SmoothForm.mpullback φ φ.contMDiff
          (SmoothForm.mpullback (Subtype.val : V → N) contMDiff_subtype_val τ) =
        SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtype_val σ := by
  let S' : Opens W := ⟨S, hS⟩
  let T' : Opens W₀ := ⟨Ξ.symm ⁻¹' S, hS.preimage Ξ.symm.continuous⟩
  have hST (z : W) : z ∈ S' ↔ Ξ z ∈ T' := by simp [S', T']
  let eU := opensImageDiffeomorph (I := I) S'
  let eV := (opensImageDiffeomorph (I := I') T').symm
  let U : Opens M := ⟨Subtype.val '' (S' : Set W), W.isOpen.isOpenMap_subtype_val _ S'.isOpen⟩
  let V : Opens N := ⟨Subtype.val '' (T' : Set W₀), W₀.isOpen.isOpenMap_subtype_val _ T'.isOpen⟩
  have hUW : U ≤ W := by rintro _ ⟨z, -, rfl⟩; exact z.2
  let φ : U ≃ₘ⟮I, I'⟯ V := (eU.trans (Ξ.subtype hST)).trans eV
  have hφ_apply (u : U) : (φ u : N) = Ξ (Opens.inclusion hUW u) :=
    congrArg Subtype.val (Ξ.subtype_apply_coe hST (eU u))
  refine ⟨U, V, φ, fun z hz ↦ ⟨⟨z, hz, rfl⟩, hφ_apply ⟨z, z, hz, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  funext x
  have hcomp : (Subtype.val : V → N) ∘ ⇑φ =
      ((Subtype.val : W₀ → N) ∘ ⇑Ξ) ∘ Opens.inclusion hUW := funext hφ_apply
  have hxS : Opens.inclusion hUW x ∈ S := (eU x).2
  rw [SmoothForm.mpullback_mpullback_of_comp_eq φ.contMDiff contMDiff_subtype_val
    (contMDiff_inclusion hUW) (contMDiff_subtype_val.comp Ξ.contMDiff) hcomp,
    ← SmoothForm.mpullback_mpullback Ξ (Subtype.val : W₀ → N) Ξ.contMDiff contMDiff_subtype_val,
    SmoothForm.coe_mpullback, TauCeti.mpullback_inclusion_apply, heq _ hxS,
    SmoothForm.coe_mpullback_subtype_val_apply, SmoothForm.coe_mpullback_subtype_val_apply]

/-- When `Q` is empty, the empty open subsets of `M` and `N` are vacuously symplectomorphic. -/
private theorem exists_diffeomorph_opens_of_isEmpty
    {E H M E' H' N Q : Type*} [IsEmpty Q]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
    (σ : SmoothTwoForm I M) (τ : SmoothTwoForm I' N) (i : Q → M) (j : Q → N) :
    ∃ (U : Opens M) (V : Opens N) (φ : U ≃ₘ⟮I, I'⟯ V),
      (∀ q, ∃ h : i q ∈ U, (φ ⟨i q, h⟩ : N) = j q) ∧
      SmoothForm.mpullback φ φ.contMDiff
          (SmoothForm.mpullback (Subtype.val : V → N) contMDiff_subtype_val τ) =
        SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtype_val σ := by
  let U : Opens M := ⊥
  let V : Opens N := ⊥
  have : IsEmpty U := ⟨fun x ↦ x.2⟩
  have : IsEmpty V := ⟨fun y ↦ y.2⟩
  let φ : U ≃ₘ⟮I, I'⟯ V :=
    { toEquiv := Equiv.equivOfIsEmpty U V
      contMDiff_toFun := fun x ↦ IsEmpty.elim inferInstance x
      contMDiff_invFun := fun y ↦ IsEmpty.elim inferInstance y }
  refine ⟨U, V, φ, fun q ↦ IsEmpty.elim ‹IsEmpty Q› q, ?_⟩
  apply Subtype.ext
  funext x
  exact IsEmpty.elim inferInstance x

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

/-- If `∀ w, ↑(Ψ w) = G ↑w` and `G` pulls `σ` back at `z : X₁` to `τ`, then `Ψ.symm` pulls
`τ|_{W₀}` back at `x = Ψ z` to `σ|_W`. -/
private theorem mpullback_symm_subtype_eq_of_apply_eq
    {E₁ H₁ X₁ E₂ H₂ X₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace X₁] [ChartedSpace H₁ X₁] [IsManifold I₁ ∞ X₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace X₂] [ChartedSpace H₂ X₂] [IsManifold I₂ ∞ X₂]
    {W₀ : Opens X₁} {W : Opens X₂} (Ψ : W₀ ≃ₘ⟮I₁, I₂⟯ W)
    {τ : SmoothTwoForm I₁ X₁} {σ : SmoothTwoForm I₂ X₂}
    {z : W₀} {x : W} (hzx : Ψ z = x) {G : X₁ → X₂}
    (h : TauCeti.mpullback I₁ I₂ G σ.1 (z : X₁) = τ.1 (z : X₁))
    (hG : ∀ w : W₀, (Ψ w : X₂) = G (w : X₁)) :
    (SmoothForm.mpullback Ψ.symm Ψ.symm.contMDiff
      (SmoothForm.mpullback (Subtype.val : W₀ → X₁) contMDiff_subtype_val τ)).1 x =
    (SmoothForm.mpullback (Subtype.val : W → X₂) contMDiff_subtype_val σ).1 x := by
  subst hzx
  have hz : TauCeti.mpullback I₁ I₂ ((Subtype.val : W → X₂) ∘ ⇑Ψ) σ.1 z = τ.1 z := by
    have hcomp : (Subtype.val : W → X₂) ∘ ⇑Ψ = G ∘ (Subtype.val : W₀ → X₁) := funext hG
    ext v
    have h1 := TauCeti.mpullback_apply (I := I₁) (I' := I₂)
      ((Subtype.val : W → X₂) ∘ ⇑Ψ) σ.1 z v
    have h2 := TauCeti.mpullback_apply (I := I₁) (I' := I₂) G σ.1 (z : X₁) v
    have h12 :
        σ.1 (((Subtype.val : W → X₂) ∘ ⇑Ψ) z)
            (fun k ↦ mfderiv I₁ I₂ ((Subtype.val : W → X₂) ∘ ⇑Ψ) z (v k)) =
          σ.1 (G z.1) (fun k ↦ mfderiv I₁ I₂ G z.1 (v k)) := by
      rw [hcomp, Function.comp_apply]
      exact congrArg (σ.1 (G z.1))
        (funext fun k ↦ TauCeti.Manifold.mfderiv_comp_subtype_val_apply (v k))
    exact (h1.trans (h12.trans h2.symm)).trans (DFunLike.congr_fun h v)
  have h1 := SmoothForm.mpullback_apply_eq_smul_iff Ψ
    (SmoothForm.mpullback Ψ.symm Ψ.symm.contMDiff
      (SmoothForm.mpullback (Subtype.val : W₀ → X₁) contMDiff_subtype_val τ))
    (SmoothForm.mpullback (Subtype.val : W → X₂) contMDiff_subtype_val σ) 1 z
  rw [one_smul, one_smul, SmoothForm.mpullback_mpullback_symm,
    SmoothForm.coe_mpullback_subtype_val_apply, SmoothForm.mpullback_mpullback,
    SmoothForm.coe_mpullback] at h1
  exact h1.1 hz.symm

/-- Given `Φ : W ≃ₘ W` and `Ψ : W₀ ≃ₘ W` such that `Φ` pulls `(Ψ.symm)^* (τ|_{W₀})` back to
`σ|_W` on an open subset `S ⊆ W`, restricting `Φ.trans Ψ.symm` to `S` gives open subsets `U ⊆ X₁`
and `V ⊆ X₂` and a diffeomorphism `φ : U ≃ₘ V` pulling `τ|_V` back to `σ|_U`. -/
private theorem exists_opens_diffeomorph_trans_symm_of_eq_on
    {E₁ H₁ X₁ E₂ H₂ X₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace X₁] [ChartedSpace H₁ X₁] [IsManifold I₁ ∞ X₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace X₂] [ChartedSpace H₂ X₂] [IsManifold I₂ ∞ X₂]
    {W : Opens X₁} {W₀ : Opens X₂} (Φ : W ≃ₘ⟮I₁, I₁⟯ W) (Ψ : W₀ ≃ₘ⟮I₂, I₁⟯ W)
    {σ : SmoothTwoForm I₁ X₁} {τ : SmoothTwoForm I₂ X₂}
    {S : Set W} (hS : IsOpen S)
    (hSΦ : ∀ z ∈ S,
      (SmoothForm.mpullback Φ Φ.contMDiff
        (SmoothForm.mpullback Ψ.symm Ψ.symm.contMDiff
          (SmoothForm.mpullback (Subtype.val : W₀ → X₂) contMDiff_subtype_val τ))).1 z =
      (SmoothForm.mpullback (Subtype.val : W → X₁) contMDiff_subtype_val σ).1 z) :
    ∃ (U : Opens X₁) (V : Opens X₂) (φ : U ≃ₘ⟮I₁, I₂⟯ V),
      (∀ z ∈ S, ∃ hz : (z : X₁) ∈ U, (φ ⟨z, hz⟩ : X₂) = Ψ.symm (Φ z)) ∧
      SmoothForm.mpullback φ φ.contMDiff
          (SmoothForm.mpullback (Subtype.val : V → X₂) contMDiff_subtype_val τ) =
        SmoothForm.mpullback (Subtype.val : U → X₁) contMDiff_subtype_val σ :=
  exists_opens_diffeomorph_of_mpullback_eq_on (Φ.trans Ψ.symm) hS fun z hz ↦ by
    rw [SmoothForm.mpullback_trans]
    exact hSΦ z hz

/-- Relative Moser step on abstract manifolds: if `Ψ : W₀ ≃ₘ W` sends `z q` to `i q` and
`(Ψ.symm)^* (τ|_{W₀})` agrees with `σ|_W` along the compact embedded submanifold `i : Q → X₁`,
then open neighborhoods `U` of `i(Q)` and `V` of `z(Q)` are symplectomorphic via `φ : U ≃ₘ V`
sending `i q` to `z q`. -/
private theorem exists_opens_diffeomorph_of_mpullback_symm_eq_along
    {E₁ H₁ X₁ E₂ H₂ X₂ F H' Q : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁} [I₁.Boundaryless]
    [TopologicalSpace X₁] [ChartedSpace H₁ X₁] [IsManifold I₁ ∞ X₁]
    [T2Space X₁] [SecondCountableTopology X₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace X₂] [ChartedSpace H₂ X₂] [IsManifold I₂ ∞ X₂]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
    [TopologicalSpace Q] [ChartedSpace H' Q] [IsManifold J ∞ Q] [CompactSpace Q]
    {σ : SmoothTwoForm I₁ X₁} (hσ : σ.IsSymplectic)
    {τ : SmoothTwoForm I₂ X₂} (hτ : τ.IsClosed)
    {i : Q → X₁} (hi : IsSmoothEmbedding J I₁ ∞ i) {z : Q → X₂}
    {W₀ : Opens X₂} {W : Opens X₁} (Ψ : W₀ ≃ₘ⟮I₂, I₁⟯ W)
    (hΨzero : ∀ q, ∃ hq : z q ∈ W₀, (Ψ ⟨z q, hq⟩ : X₁) = i q)
    (hΨform : ∀ (q : Q) (hx : i q ∈ W),
      (SmoothForm.mpullback Ψ.symm Ψ.symm.contMDiff
        (SmoothForm.mpullback (Subtype.val : W₀ → X₂) contMDiff_subtype_val τ)).1 ⟨i q, hx⟩ =
      (SmoothForm.mpullback (Subtype.val : W → X₁) contMDiff_subtype_val σ).1 ⟨i q, hx⟩) :
    ∃ (U : Opens X₁) (V : Opens X₂) (φ : U ≃ₘ⟮I₁, I₂⟯ V),
      (∀ q, ∃ h : i q ∈ U, (φ ⟨i q, h⟩ : X₂) = z q) ∧
      SmoothForm.mpullback φ φ.contMDiff
          (SmoothForm.mpullback (Subtype.val : V → X₂) contMDiff_subtype_val τ) =
        SmoothForm.mpullback (Subtype.val : U → X₁) contMDiff_subtype_val σ := by
  have hiW_mem (q : Q) : i q ∈ W :=
    let ⟨hq, hval⟩ := hΨzero q; hval ▸ (Ψ ⟨z q, hq⟩).2
  let fW : SmoothEmbedding J I₁ ∞ Q W := .ofIsSmoothEmbedding (fun q ↦ ⟨i q, hiW_mem q⟩)
    (TauCeti.isSmoothEmbedding_subtypeVal_comp_iff.1 hi)
  have hfW_apply (q : Q) : fW q = ⟨i q, hiW_mem q⟩ :=
    SmoothEmbedding.ofIsSmoothEmbedding_apply _ _ q
  have hσ₀ := hσ.mpullback_subtype_val W
  have hσ₁_closed := (hτ.mpullback (Subtype.val : W₀ → X₂) contMDiff_subtype_val).mpullback
    Ψ.symm Ψ.symm.contMDiff
  obtain ⟨Φ, hΦf, -, hΦ⟩ := SmoothTwoForm.exists_diffeomorph_fix_embedding_eventually_mpullback_eq
    fW hσ₀.isClosed hσ₁_closed (fun q ↦ hσ₀.isNondegenerate.nondegenerate_bilinFormAt (fW q))
    fun q ↦ by
      rw [hfW_apply]
      exact hΨform q (hiW_mem q)
  obtain ⟨S, ⟨hS, hfS⟩, hSΦ⟩ := (hasBasis_nhdsSet (range fW)).mem_iff.1 hΦ
  obtain ⟨U, V, φ, hφS, hφform⟩ :=
    exists_opens_diffeomorph_trans_symm_of_eq_on Φ Ψ hS fun _ hz ↦ hSΦ hz
  refine ⟨U, V, φ, fun q ↦ ?_, hφform⟩
  obtain ⟨hzU, hval⟩ := hφS (fW q) (hfS (mem_range_self q))
  have hfi : (fW q : X₁) = i q := congrArg Subtype.val (hfW_apply q)
  obtain ⟨hq, hqval⟩ := hΨzero q
  have hsub : (⟨i q, hfi ▸ hzU⟩ : U) = ⟨fW q, hzU⟩ := Subtype.ext hfi.symm
  have hΨq : Ψ.symm (fW q) = ⟨z q, hq⟩ :=
    Ψ.symm_apply_eq.2 (Subtype.ext (hfi.trans hqval.symm))
  exact ⟨hfi ▸ hzU, (congrArg (fun u : U ↦ (φ u : X₂)) hsub).trans
    (hval.trans ((congrArg (fun w : W ↦ (Ψ.symm w : X₂)) (hΦf q)).trans
      (congrArg Subtype.val hΨq)))⟩

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
          (SmoothForm.mpullback (Subtype.val : W₀ → CotangentBundle J Q) contMDiff_subtype_val
            (CotangentBundle.symplecticForm J Q))).1 ⟨i q, hx⟩ =
        (SmoothForm.mpullback (Subtype.val : W → M) contMDiff_subtype_val σ).1 ⟨i q, hx⟩ := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨J_acs, hJ⟩ := hσ.isNondegenerate.exists_compatible
  let : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
    ⟨hJ.riemannianMetric.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y) :=
    Bundle.instIsContMDiffRiemannianBundle hJ.riemannianMetric
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
            hJ.inner_eq_eval₂_riemannianMetric]).isIsotropic
    exact mpullback_symm_subtype_eq_of_apply_eq Ψ hzx
      (f.mpullback_normalExp_comp_normalBundleDiffeomorph_symm_zeroSection hf hdim q hiso)
      hΨexp

/-- A nonempty compact manifold admitting a Lagrangian embedding into a Hausdorff symplectic
manifold has finite-dimensional model space, as does the ambient symplectic manifold. -/
private theorem finiteDimensional_of_isLagrangianEmbedding
    {E H M F H' Q : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
    {J : ModelWithCorners ℝ F H'} [TopologicalSpace Q] [ChartedSpace H' Q]
    [CompactSpace Q] [Nonempty Q]
    {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate}
    {i : Q → M} (hi : hσ.IsLagrangianEmbedding J i) :
    FiniteDimensional ℝ F ∧ FiniteDimensional ℝ E := by
  have : T2Space Q := hi.isEmbedding.t2Space
  have : FiniteDimensional ℝ F := .of_locallyCompact_manifold Q J
  obtain ⟨q₀⟩ := ‹Nonempty Q›
  have hL := SmoothTwoForm.IsNondegenerate.isLagrangianMap_iff_forall.1 hi.isLagrangianMap q₀
  exact ⟨inferInstance, hL.finite⟩

/-- Every compact subset `K` of a manifold over a finite-dimensional real normed space has a
second-countable open neighborhood (covered by finitely many chart domains). -/
private theorem exists_secondCountable_opens_subset
    {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    {K : Set M} (hK : IsCompact K) :
    ∃ M₀ : Opens M, K ⊆ M₀ ∧ SecondCountableTopology M₀ := by
  have : SecondCountableTopology H := I.secondCountableTopology
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : M ↦ (chartAt H x).source)
    (fun x ↦ (chartAt H x).open_source) fun x _ ↦ mem_iUnion.2 ⟨x, mem_chart_source H x⟩
  let M₀ : Opens M :=
    ⟨⋃ x ∈ t, (chartAt H x).source, isOpen_biUnion fun x _ ↦ (chartAt H x).open_source⟩
  let U : t → Set M₀ := fun x ↦ (Subtype.val : M₀ → M) ⁻¹' (chartAt H (x : M)).source
  have : ∀ x : t, SecondCountableTopology (U x) := fun x ↦ by
    have : SecondCountableTopology (chartAt H (x : M)).source :=
      (chartAt (H := H) (x : M)).secondCountableTopology_source
    let f : U x → (chartAt H (x : M)).source := fun z ↦ ⟨z.1.1, z.2⟩
    have hf : Continuous f := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    have hgf : Topology.IsInducing ((Subtype.val : (chartAt H (x : M)).source → M) ∘ f) :=
      (Topology.IsInducing.subtypeVal : Topology.IsInducing (Subtype.val : M₀ → M)).comp
        (Topology.IsInducing.subtypeVal : Topology.IsInducing (Subtype.val : U x → M₀))
    exact (Topology.IsInducing.of_comp hf continuous_subtype_val hgf).secondCountableTopology
  refine ⟨M₀, ht, secondCountableTopology_of_countable_cover (U := U)
    (fun x : t ↦ (chartAt H (x : M)).open_source.preimage continuous_subtype_val)
    (eq_univ_iff_forall.2 fun y ↦ ?_)⟩
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 y.2
  exact mem_iUnion.2 ⟨⟨x, hxt⟩, hyx⟩

end OpenHelpers

/-! ### Weinstein's Lagrangian neighborhood theorem -/

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
          (SmoothForm.mpullback (Subtype.val : V → CotangentBundle J Q) contMDiff_subtype_val
            (CotangentBundle.symplecticForm J Q)) =
        SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtype_val σ := by
  by_cases hQ : Nonempty Q
  · have : Nonempty Q := hQ
    obtain ⟨hF, hE⟩ := finiteDimensional_of_isLagrangianEmbedding hi
    have : FiniteDimensional ℝ F := hF
    have : FiniteDimensional ℝ E := hE
    obtain ⟨M₀, hM₀, hM₀sc⟩ :=
      exists_secondCountable_opens_subset I (isCompact_range hi.isEmbedding.continuous)
    have : SecondCountableTopology M₀ := hM₀sc
    let i₀ : Q → M₀ := fun q ↦ ⟨i q, hM₀ (mem_range_self q)⟩
    have hσ₀ := hσ.mpullback_subtype_val M₀
    have hi₀ : hσ₀.isNondegenerate.IsLagrangianEmbedding J i₀ :=
      (hσ.isNondegenerate.isLagrangianEmbedding_subtype_val_comp_iff (U := M₀) (g := i₀)).1 hi
    obtain ⟨W₀, W, Ψ, hΨzero, hΨform⟩ := exists_cotangent_normalExp_mpullback_eq_along hσ₀ hi₀
    obtain ⟨U₀, V, φ₀, hφ₀, hform₀⟩ := exists_opens_diffeomorph_of_mpullback_symm_eq_along hσ₀
      CotangentBundle.isSymplectic_symplecticForm.isClosed hi₀.isSmoothEmbedding Ψ hΨzero hΨform
    let eU := opensImageDiffeomorph (I := I) U₀
    refine ⟨_, V, eU.trans φ₀, fun q ↦ ?_, ?_⟩
    · obtain ⟨hq₀, hval₀⟩ := hφ₀ q
      exact ⟨⟨i₀ q, hq₀, rfl⟩, hval₀⟩
    · rw [SmoothForm.mpullback_trans, hform₀, SmoothForm.mpullback_mpullback,
        SmoothForm.mpullback_mpullback]
      rfl
  · have : IsEmpty Q := not_nonempty_iff.1 hQ
    exact exists_diffeomorph_opens_of_isEmpty σ (CotangentBundle.symplecticForm J Q) i
      (fun q ↦ TotalSpace.mk' (F →L[ℝ] ℝ) q 0)

/-- Restricting a diffeomorphism `φ : U₁ ≃ₘ V₁` (pulling `β|_{V₁}` back to `α|_{U₁}`) to an open
subset `O ≤ V₁` yields an open subset `U ≤ U₁` and a diffeomorphism `ψ : U ≃ₘ O` pulling `β|_O`
back to `α|_U`. -/
private theorem restrict_opens_diffeomorph_of_le
    {E H M E' H' P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {K : ModelWithCorners ℝ E' H'} [TopologicalSpace P] [ChartedSpace H' P] [IsManifold K ∞ P]
    {U₁ : Opens M} {V₁ : Opens P} (φ : U₁ ≃ₘ⟮I, K⟯ V₁)
    {α : SmoothTwoForm I M} {β : SmoothTwoForm K P}
    (hform : SmoothForm.mpullback φ φ.contMDiff
        (SmoothForm.mpullback (Subtype.val : V₁ → P) contMDiff_subtype_val β) =
      SmoothForm.mpullback (Subtype.val : U₁ → M) contMDiff_subtype_val α)
    {O : Opens P} (hO : O ≤ V₁) :
    ∃ (U : Opens M) (ψ : U ≃ₘ⟮I, K⟯ O),
      (∀ (x : M) (hx₁ : x ∈ U₁), (φ ⟨x, hx₁⟩ : P) ∈ O →
        ∃ hx : x ∈ U, (ψ ⟨x, hx⟩ : P) = (φ ⟨x, hx₁⟩ : P)) ∧
      SmoothForm.mpullback ψ ψ.contMDiff
          (SmoothForm.mpullback (Subtype.val : O → P) contMDiff_subtype_val β) =
        SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtype_val α := by
  let S : Set U₁ := {x : U₁ | (φ x : P) ∈ O}
  have hS : IsOpen S := O.isOpen.preimage (continuous_subtype_val.comp φ.continuous)
  let S' : Opens U₁ := ⟨S, hS⟩
  let U : Opens M := ⟨Subtype.val '' (S' : Set U₁), U₁.isOpen.isOpenMap_subtype_val _ S'.isOpen⟩
  have hUU₁ : U ≤ U₁ := by rintro _ ⟨x, -, rfl⟩; exact x.2
  let eU : U ≃ₘ⟮I, I⟯ S' := opensImageDiffeomorph (I := I) S'
  have hφ_symm_mem (y : O) : (φ (φ.symm (Opens.inclusion hO y)) : P) ∈ O := by
    rw [congrArg (Subtype.val : V₁ → P) (φ.apply_symm_apply (Opens.inclusion hO y))]
    exact y.2
  let φO : S' ≃ₘ⟮I, K⟯ O :=
    { toFun := fun z ↦ ⟨(φ z.1 : P), z.2⟩
      invFun := fun y ↦ ⟨φ.symm (Opens.inclusion hO y), hφ_symm_mem y⟩
      left_inv := fun z ↦ Subtype.ext (φ.left_inv z.1)
      right_inv := fun y ↦
        Subtype.ext (congrArg (Subtype.val : V₁ → P) (φ.apply_symm_apply (Opens.inclusion hO y)))
      contMDiff_toFun := (TauCeti.ContMDiff.subtypeVal_comp_iff O _).1
        (ContMDiff.comp (g := (Subtype.val : V₁ → P)) contMDiff_subtype_val
          (φ.contMDiff.comp contMDiff_subtype_val))
      contMDiff_invFun := (TauCeti.ContMDiff.subtypeVal_comp_iff S' _).1
        (φ.symm.contMDiff.comp (contMDiff_inclusion hO)) }
  let ψ : U ≃ₘ⟮I, K⟯ O := eU.trans φO
  refine ⟨U, ψ, fun x hx₁ hxO ↦ ⟨⟨⟨x, hx₁⟩, hxO, rfl⟩, rfl⟩, ?_⟩
  have hcomp : (Subtype.val : O → P) ∘ ⇑ψ =
      ((Subtype.val : V₁ → P) ∘ ⇑φ) ∘ Opens.inclusion hUU₁ := rfl
  rw [SmoothForm.mpullback_mpullback_of_comp_eq ψ.contMDiff contMDiff_subtype_val
    (contMDiff_inclusion hUU₁) (contMDiff_subtype_val.comp φ.contMDiff) hcomp,
    ← SmoothForm.mpullback_mpullback φ (Subtype.val : V₁ → P) φ.contMDiff contMDiff_subtype_val,
    hform, SmoothForm.mpullback_mpullback]
  rfl

/-- Restricting a diffeomorphism `F_map : X₁ ≃ₘ X₂` (pulling `ω₂` back to `ω₁`) to open subsets
`O₁` and `O₂` that it maps onto each other yields a diffeomorphism pulling `ω₂|_{O₂}` back to
`ω₁|_{O₁}`. -/
private theorem mpullback_subtype_diffeomorph_eq
    {E₁ H₁ X₁ E₂ H₂ X₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace X₁] [ChartedSpace H₁ X₁] [IsManifold I₁ ∞ X₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace X₂] [ChartedSpace H₂ X₂] [IsManifold I₂ ∞ X₂]
    (F_map : X₁ ≃ₘ⟮I₁, I₂⟯ X₂) {O₁ : Opens X₁} {O₂ : Opens X₂}
    (hO₁₂ : ∀ z, z ∈ O₁ ↔ F_map z ∈ O₂)
    {ω₁ : SmoothTwoForm I₁ X₁} {ω₂ : SmoothTwoForm I₂ X₂}
    (hF : SmoothForm.mpullback F_map F_map.contMDiff ω₂ = ω₁) :
    SmoothForm.mpullback (F_map.subtype hO₁₂) (F_map.subtype hO₁₂).contMDiff
        (SmoothForm.mpullback (Subtype.val : O₂ → X₂) contMDiff_subtype_val ω₂) =
      SmoothForm.mpullback (Subtype.val : O₁ → X₁) contMDiff_subtype_val ω₁ := by
  rw [SmoothForm.mpullback_mpullback_of_comp_eq (F_map.subtype hO₁₂).contMDiff
    contMDiff_subtype_val contMDiff_subtype_val F_map.contMDiff
    (funext (F_map.subtype_apply_coe hO₁₂)), hF]

/-- Composing `ψ₁ : U ≃ₘ O₁` (pulling `ω₁` back to `α`), `g : O₁ ≃ₘ O₂` (pulling `ω₂` back to
`ω₁`), and `ψ₂.symm : O₂ ≃ₘ V` (with `ψ₂` pulling `ω₂` back to `β`) yields a diffeomorphism
pulling `β` back to `α`. -/
private theorem mpullback_trans_trans_symm_eq
    {E₁ H₁ X₁ E₂ H₂ X₂ E₃ H₃ X₃ E₄ H₄ X₄ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace X₁] [ChartedSpace H₁ X₁] [IsManifold I₁ ∞ X₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace X₂] [ChartedSpace H₂ X₂] [IsManifold I₂ ∞ X₂]
    [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [TopologicalSpace H₃]
    {I₃ : ModelWithCorners ℝ E₃ H₃} [TopologicalSpace X₃] [ChartedSpace H₃ X₃] [IsManifold I₃ ∞ X₃]
    [NormedAddCommGroup E₄] [NormedSpace ℝ E₄] [TopologicalSpace H₄]
    {I₄ : ModelWithCorners ℝ E₄ H₄} [TopologicalSpace X₄] [ChartedSpace H₄ X₄] [IsManifold I₄ ∞ X₄]
    (ψ₁ : X₁ ≃ₘ⟮I₁, I₂⟯ X₂) (g : X₂ ≃ₘ⟮I₂, I₃⟯ X₃) (ψ₂ : X₄ ≃ₘ⟮I₄, I₃⟯ X₃)
    {α : SmoothTwoForm I₁ X₁} {ω₁ : SmoothTwoForm I₂ X₂}
    {ω₂ : SmoothTwoForm I₃ X₃} {β : SmoothTwoForm I₄ X₄}
    (h₁ : SmoothForm.mpullback ψ₁ ψ₁.contMDiff ω₁ = α)
    (hg : SmoothForm.mpullback g g.contMDiff ω₂ = ω₁)
    (h₂ : SmoothForm.mpullback ψ₂ ψ₂.contMDiff ω₂ = β) :
    SmoothForm.mpullback ((ψ₁.trans g).trans ψ₂.symm) ((ψ₁.trans g).trans ψ₂.symm).contMDiff β =
      α := by
  rw [SmoothForm.mpullback_trans, SmoothForm.mpullback_trans,
    SmoothForm.mpullback_symm_eq_of_mpullback_eq h₂, hg, h₁]

/-- **Equivalence of Lagrangian neighborhoods over a diffeomorphism** (Cannas da Silva, Theorem 8.4,
p. 48). Given compact boundaryless Lagrangian embeddings `i : Q → (M, σ)` and `j : Q' → (N, τ)`
into boundaryless Hausdorff symplectic manifolds and a smooth diffeomorphism `f : Q ≃ₘ Q'`, there
exist open neighborhoods `U` of `i(Q)` and `V` of `j(Q')` and a symplectomorphism `Φ : U ≃ₘ V`
sending `i q` to `j (f q)` for every `q : Q`. -/
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
    [TopologicalSpace Q'] [ChartedSpace G' Q'] [IsManifold J' ∞ Q'] [CompactSpace Q']
    {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
    {τ : SmoothTwoForm I' N} (hτ : τ.IsSymplectic)
    {i : Q → M} (hi : hσ.isNondegenerate.IsLagrangianEmbedding J i)
    {j : Q' → N} (hj : hτ.isNondegenerate.IsLagrangianEmbedding J' j)
    (f : Q ≃ₘ⟮J, J'⟯ Q') :
    ∃ (U : Opens M) (V : Opens N) (Φ : U ≃ₘ⟮I, I'⟯ V),
      (∀ q, ∃ h : i q ∈ U, (Φ ⟨i q, h⟩ : N) = j (f q)) ∧
      SmoothForm.mpullback Φ Φ.contMDiff
          (SmoothForm.mpullback (Subtype.val : V → N) contMDiff_subtype_val τ) =
        SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtype_val σ := by
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
  obtain ⟨U, ψ₁, hψ₁, hψ₁form⟩ :=
    restrict_opens_diffeomorph_of_le φ₁ hform₁ (inf_le_left : O₁ ≤ V₁)
  obtain ⟨V, ψ₂, hψ₂, hψ₂form⟩ :=
    restrict_opens_diffeomorph_of_le φ₂ hform₂ (inf_le_right : O₂ ≤ V₂)
  refine ⟨U, V, (ψ₁.trans g).trans ψ₂.symm, fun q ↦ ?_, ?_⟩
  · obtain ⟨hx₁, hval₁⟩ := hφ₁ q
    obtain ⟨hy₂, hval₂⟩ := hφ₂ (f q)
    have hcot : f.cotangent (TotalSpace.mk' (F →L[ℝ] ℝ) q 0) =
        TotalSpace.mk' (F' →L[ℝ] ℝ) (f q) 0 := f.cotangent_zeroSection q
    have hxO₁ : (φ₁ ⟨i q, hx₁⟩ : CotangentBundle J Q) ∈ O₁ :=
      ⟨(φ₁ ⟨i q, hx₁⟩).2, Opens.mem_mk.2 (mem_preimage.2 (by
        rw [hval₁, hcot, ← hval₂]
        exact (φ₂ ⟨j (f q), hy₂⟩).2))⟩
    obtain ⟨hxU, hψ₁q⟩ := hψ₁ (i q) hx₁ hxO₁
    have hyO₂ : (φ₂ ⟨j (f q), hy₂⟩ : CotangentBundle J' Q') ∈ O₂ := by
      rw [hval₂, ← hcot, ← hval₁]
      exact (hO₁₂ _).1 hxO₁
    obtain ⟨hyV, hψ₂q⟩ := hψ₂ (j (f q)) hy₂ hyO₂
    refine ⟨hxU, ?_⟩
    have hgeq : g (ψ₁ ⟨i q, hxU⟩) = ψ₂ ⟨j (f q), hyV⟩ :=
      Subtype.ext (by simp [g, hψ₁q, hval₁, hcot, hψ₂q, hval₂])
    have hΦq : ((ψ₁.trans g).trans ψ₂.symm) ⟨i q, hxU⟩ = ⟨j (f q), hyV⟩ := by simp [hgeq]
    exact congrArg Subtype.val hΦq
  · exact mpullback_trans_trans_symm_eq ψ₁ g ψ₂ hψ₁form
      (mpullback_subtype_diffeomorph_eq f.cotangent hO₁₂ f.mpullback_cotangent_symplecticForm)
      hψ₂form

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
          (SmoothForm.mpullback (Subtype.val : V → N) contMDiff_subtype_val τ) =
        SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtype_val σ := by
  simpa using hσ.exists_diffeomorph_opens_of_isLagrangianEmbedding_comp_diffeomorph hτ hi hj
    (Diffeomorph.refl J Q ∞)

end SmoothTwoForm.IsSymplectic

end TauCeti
