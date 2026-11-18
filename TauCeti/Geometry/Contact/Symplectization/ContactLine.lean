/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Distribution
public import TauCeti.Geometry.Contact.Symplectization.Cotangent
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Annihilator
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville
public import TauCeti.Geometry.Symplectic.Manifold.Opens
public import TauCeti.Topology.VectorBundle.ZeroSection

/-!
# The symplectization of a contact structure

Let `ξ` be a smooth hyperplane field on a manifold `M`, with contact line `L = TM ⧸ ξ`. The dual
line `L*` is the annihilator line of `ξ` in `T*M`: the covectors vanishing on `ξ`, which form a
smooth line bundle smoothly embedded in `T*M`
(`TauCeti.CotangentBundle.annihilatorSpace`,
`TauCeti.CotangentBundle.isSmoothEmbedding_annihilatorInclusion`). Its **tautological one-form**
(`TauCeti.CotangentBundle.annihilatorLiouvilleForm`) is the restriction of the Liouville form `λ`
of `T*M`:

`θ_(x, ℓ)(v) = ℓ(dπ v)`

(`TauCeti.CotangentBundle.annihilatorLiouvilleForm_apply`), where `π` is the bundle projection and
`ℓ` a covector at `x` vanishing on `ξ_x`; since `ℓ` vanishes on `ξ_x`, this is `ℓ` applied to the
class of `dπ v` in `L_x`.

The **symplectization** of `ξ` is the open complement `L* ∖ 0` of the zero section
(`TauCeti.CotangentBundle.annihilatorSymplectization`) with the two-form `dθ`
(`TauCeti.CotangentBundle.annihilatorSymplecticForm`). On a Hausdorff manifold, `dθ` is
nondegenerate at a nonzero covector over `x` exactly when the Levi form of `ξ` is nondegenerate at
`x` (`TauCeti.CotangentBundle.nondegenerate_bilinFormAt_mextDerivₗ_annihilatorLiouvilleForm_iff`).
Hence `ξ` is a contact structure exactly when `dθ` is nondegenerate on all of `L* ∖ 0`
(`TauCeti.CotangentBundle.isContactDistribution_iff_forall_nondegenerate`), that is, exactly when
`(L* ∖ 0, dθ)` is a symplectic manifold
(`TauCeti.CotangentBundle.isSymplectic_annihilatorSymplecticForm_iff`). With the convention
`ω = -dλ` of exact symplectic manifolds, its Liouville primitive is `-θ`. The inclusion into `T*M`
pulls the canonical symplectic form `ω` back to `-dθ`
(`TauCeti.CotangentBundle.mpullback_annihilatorInclusion_symplecticForm`), as for the
symplectization of a contact form in `TauCeti.Geometry.Contact.Symplectization.Cotangent`.

No coorientation of `ξ` is chosen: `L` need not be trivial, and `L* ∖ 0` need not split into two
halves. The proof is local. A nonzero covector `ℓ` over `x` vanishing on `ξ` is the value at `x` of
a smooth one-form `β` vanishing on `ξ` everywhere and with kernel `ξ` near `x`
(`TauCeti.CotangentBundle.exists_degreeOneEquiv_eq_of_mem_annihilatorSpace`). The map
`(t, y) ↦ eᵗ β_y` into `L*` (`TauCeti.SmoothForm.symplectizationToAnnihilator`) pulls `θ` back to
the symplectization form `eᵗ β` of `TauCeti.Geometry.Contact.Symplectization.Basic`
(`TauCeti.SmoothForm.mpullback_symplectizationToAnnihilator_annihilatorLiouvilleForm`). Its
differential at `(0, x)` is injective, because `d(eᵗ β)` pairs the real direction with a vector on
which `β_x` is nonzero, so by counting dimensions it identifies `dθ` at `ℓ` with `d(eᵗ β)` at
`(0, x)`
(`TauCeti.SmoothForm.nondegenerate_bilinFormAt_mextDerivₗ_iff_of_mpullback_eq_symplectization`).
That form is nondegenerate exactly when `β` is a contact form at `x`
(`TauCeti.SmoothForm.nondegenerate_bilinFormAt_mextDerivₗ_symplectization_iff`), which is Levi
nondegeneracy of `ξ` at `x`.

## Main definitions

* `TauCeti.CotangentBundle.annihilatorLiouvilleForm`: the tautological one-form `θ` of the
  annihilator line of `ξ`.
* `TauCeti.CotangentBundle.annihilatorSymplectization`: the open complement `L* ∖ 0` of its zero
  section.
* `TauCeti.CotangentBundle.annihilatorSymplecticForm`: the two-form `dθ` on `L* ∖ 0`.
* `TauCeti.SmoothForm.symplectizationToAnnihilator`: the map `(t, y) ↦ eᵗ β_y` into `L*` of a
  one-form `β` vanishing on `ξ`.

## Main results

* `TauCeti.CotangentBundle.nondegenerate_bilinFormAt_mextDerivₗ_annihilatorLiouvilleForm_iff`:
  pointwise, `dθ` is nondegenerate at a nonzero covector exactly when the Levi form is
  nondegenerate at its base point.
* `TauCeti.CotangentBundle.isContactDistribution_iff_forall_nondegenerate`: `ξ` is a contact
  structure exactly when `dθ` is nondegenerate on `L* ∖ 0`.
* `TauCeti.CotangentBundle.isSymplectic_annihilatorSymplecticForm_iff`: `ξ` is a contact structure
  exactly when `L* ∖ 0` with `dθ` is a symplectic manifold.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008, Section 1.1
  and Appendix B (the symplectization as the annihilator of the contact structure).
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Springer, 1989,
  Appendix 4 (the symplectification of a contact manifold).
-/

public section

noncomputable section

open Bundle Filter Function Manifold Module Set Topology
open scoped Manifold ContDiff

namespace TauCeti.CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {k : ℕ} {D : Π x : M, Submodule ℝ (TangentSpace I x)}

/-! ### The tautological one-form -/

/-- The **tautological one-form** `θ` of the annihilator line of a smooth hyperplane field `D`: the
pullback of the Liouville form `λ` of `T*M` along the inclusion of the annihilator line. At a
covector `ℓ` vanishing on `D`, it evaluates a tangent vector `v` to `ℓ(dπ v)`
(`TauCeti.CotangentBundle.annihilatorLiouvilleForm_apply`). -/
def annihilatorLiouvilleForm (hD : IsContMDiffDistribution I ∞ k D) (hk : k + 1 = finrank ℝ E) :
    letI := annihilatorFiberBundle hD (m := ∞) (by simp) hk
    letI := annihilatorVectorBundle hD (m := ∞) (by simp) hk
    letI := annihilatorContMDiffVectorBundle hD (m := ∞) (by simp) hk
    SmoothForm (I.prod 𝓘(ℝ, Fin 1 → ℝ)) (TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace D x)
      ℝ 1 :=
  letI := annihilatorFiberBundle hD (m := ∞) (by simp) hk
  letI := annihilatorVectorBundle hD (m := ∞) (by simp) hk
  letI := annihilatorContMDiffVectorBundle hD (m := ∞) (by simp) hk
  SmoothForm.mpullback (annihilatorInclusion (Fin 1 → ℝ) D)
    (contMDiff_annihilatorInclusion hD (m := ∞) (by simp) hk) (liouvilleForm I M)

/-- The tautological one-form evaluates a tangent vector `v` at a covector `ℓ` of the annihilator
line by applying `ℓ` to the image of `v` under the derivative of the bundle projection. -/
theorem annihilatorLiouvilleForm_apply (hD : IsContMDiffDistribution I ∞ k D)
    (hk : k + 1 = finrank ℝ E) :
    letI := annihilatorFiberBundle hD (m := ∞) (by simp) hk
    letI := annihilatorVectorBundle hD (m := ∞) (by simp) hk
    letI := annihilatorContMDiffVectorBundle hD (m := ∞) (by simp) hk
    ∀ (z : TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace D x)
      (v : TangentSpace (I.prod 𝓘(ℝ, Fin 1 → ℝ)) z),
      (annihilatorLiouvilleForm hD hk).1 z ![v] =
        (z.2 : TangentSpace I z.proj →L[ℝ] ℝ)
          (mfderiv (I.prod 𝓘(ℝ, Fin 1 → ℝ)) I TotalSpace.proj z v) := by
  let := annihilatorFiberBundle hD (m := ∞) (by simp) hk
  let := annihilatorVectorBundle hD (m := ∞) (by simp) hk
  let := annihilatorContMDiffVectorBundle hD (m := ∞) (by simp) hk
  intro z v
  rw [annihilatorLiouvilleForm, SmoothForm.coe_mpullback,
    mpullback_liouvilleForm_apply_of_proj_comp_eq (ψ := annihilatorInclusion (Fin 1 → ℝ) D)
      (g := TotalSpace.proj) (annihilatorInclusion_proj _ D)
      ((contMDiff_annihilatorInclusion hD (m := ∞) (by simp) hk z).mdifferentiableAt
        (by simp)), annihilatorInclusion_snd]
  -- `![v] 0` reduces to `v`.
  rfl

/-- The inclusion of the annihilator line pulls the canonical symplectic form `ω = -dλ` of `T*M`
back to `-dθ`. -/
theorem mpullback_annihilatorInclusion_symplecticForm (hD : IsContMDiffDistribution I ∞ k D)
    (hk : k + 1 = finrank ℝ E) :
    letI := annihilatorFiberBundle hD (m := ∞) (by simp) hk
    letI := annihilatorVectorBundle hD (m := ∞) (by simp) hk
    letI := annihilatorContMDiffVectorBundle hD (m := ∞) (by simp) hk
    SmoothForm.mpullback (annihilatorInclusion (Fin 1 → ℝ) D)
        (contMDiff_annihilatorInclusion hD (m := ∞) (by simp) hk) (symplecticForm I M) =
      -mextDerivₗ (I.prod 𝓘(ℝ, Fin 1 → ℝ)) 1 (annihilatorLiouvilleForm hD hk) := by
  let := annihilatorFiberBundle hD (m := ∞) (by simp) hk
  let := annihilatorVectorBundle hD (m := ∞) (by simp) hk
  let := annihilatorContMDiffVectorBundle hD (m := ∞) (by simp) hk
  have hinc := contMDiff_annihilatorInclusion hD (m := ∞) (by simp) hk
  rw [symplecticForm_eq_neg_mextDerivₗ]
  refine ((SmoothForm.mpullback (annihilatorInclusion (Fin 1 → ℝ) D) hinc).map_neg
    (mextDerivₗ (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1 (liouvilleForm I M))).trans ?_
  exact congrArg Neg.neg (SmoothForm.mextDerivₗ_mpullback _ hinc 1 (liouvilleForm I M)).symm

end TauCeti.CotangentBundle

namespace TauCeti.SmoothForm

open CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {k : ℕ} {D : Π x : M, Submodule ℝ (TangentSpace I x)}

/-! ### Parametrizations by annihilating one-forms -/

/-- The map `(t, y) ↦ eᵗ β_y` from `ℝ × M` into the annihilator line of `D`, for a one-form `β`
vanishing on `D`. Followed by the inclusion into `T*M`, it is the map
`TauCeti.SmoothForm.symplectizationToCotangent` of `β`
(`TauCeti.SmoothForm.annihilatorInclusion_comp_symplectizationToAnnihilator`). Where `β`
does not vanish, it parametrizes the nonzero covectors of the annihilator line that are positive
multiples of `β`. -/
def symplectizationToAnnihilator (β : SmoothForm I M ℝ 1)
    (hβ : ∀ y, SmoothForm.degreeOneEquiv β y ∈ annihilatorSpace D y) (p : ℝ × M) :
    TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace D x :=
  ⟨p.2, ⟨Real.exp p.1 • SmoothForm.degreeOneEquiv β p.2, Submodule.smul_mem _ _ (hβ p.2)⟩⟩

/-- The covector `eᵗ β_y` lies over `y`. -/
@[simp]
theorem proj_symplectizationToAnnihilator (β : SmoothForm I M ℝ 1)
    (hβ : ∀ y, SmoothForm.degreeOneEquiv β y ∈ annihilatorSpace D y) (p : ℝ × M) :
    (symplectizationToAnnihilator β hβ p).proj = p.2 := (rfl)

/-- The covector carried by `(t, y) ↦ eᵗ β_y` is `eᵗ β_y`. -/
@[simp]
theorem coe_snd_symplectizationToAnnihilator (β : SmoothForm I M ℝ 1)
    (hβ : ∀ y, SmoothForm.degreeOneEquiv β y ∈ annihilatorSpace D y) (p : ℝ × M) :
    ((symplectizationToAnnihilator β hβ p).2 :
        TangentSpace I (symplectizationToAnnihilator β hβ p).proj →L[ℝ] ℝ) =
      Real.exp p.1 • SmoothForm.degreeOneEquiv β p.2 := (rfl)

/-- The covectors `eᵗ β_y`, as a map into `T*M`, form the map
`TauCeti.SmoothForm.symplectizationToCotangent` of `β`. -/
private theorem mk_exp_smul_degreeOneEquiv_eq (β : SmoothForm I M ℝ 1) :
    (fun p : ℝ × M ↦ (⟨p.2, Real.exp p.1 • SmoothForm.degreeOneEquiv β p.2⟩ :
      CotangentBundle I M)) = β.symplectizationToCotangent := by
  funext p
  refine CotangentBundle.ext (by simp) fun v ↦ ?_
  simp [SmoothForm.symplectizationToCotangent_snd_apply, SmoothForm.degreeOneEquiv_apply_apply_vec]

/-- The map `(t, y) ↦ eᵗ β_y` into the annihilator line, followed by the inclusion into `T*M`, is
the map `(t, y) ↦ eᵗ β_y` into `T*M`. -/
theorem annihilatorInclusion_comp_symplectizationToAnnihilator (β : SmoothForm I M ℝ 1)
    (hβ : ∀ y, SmoothForm.degreeOneEquiv β y ∈ annihilatorSpace D y) :
    annihilatorInclusion (Fin 1 → ℝ) D ∘ symplectizationToAnnihilator β hβ =
      β.symplectizationToCotangent := by
  rw [← mk_exp_smul_degreeOneEquiv_eq]
  funext p
  refine CotangentBundle.ext (by simp) fun v ↦ ?_
  rw [Function.comp_apply, annihilatorInclusion_snd, coe_snd_symplectizationToAnnihilator]
  -- Both sides are now `(eᵗ β_y) v`, but as functionals on tangent spaces at base points that agree
  -- only after unfolding `annihilatorInclusion`, so `simp` cannot close the goal.
  rfl

/-- The map `(t, y) ↦ eᵗ β_y` into the annihilator line is smooth. -/
theorem contMDiff_symplectizationToAnnihilator (hD : IsContMDiffDistribution I ∞ k D)
    (hk : k + 1 = finrank ℝ E) (β : SmoothForm I M ℝ 1)
    (hβ : ∀ y, SmoothForm.degreeOneEquiv β y ∈ annihilatorSpace D y) :
    letI := annihilatorFiberBundle hD (m := ∞) (by simp) hk
    ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, Fin 1 → ℝ)) ∞ (symplectizationToAnnihilator β hβ) := by
  let := annihilatorFiberBundle hD (m := ∞) (by simp) hk
  intro p
  have h := β.contMDiff_symplectizationToCotangent p
  rw [← mk_exp_smul_degreeOneEquiv_eq] at h
  exact contMDiffAt_annihilatorSpace_mk hD (m := ∞) (by simp) hk (b := Prod.snd)
    (w := fun p ↦ Real.exp p.1 • SmoothForm.degreeOneEquiv β p.2) h _

/-- The map `(t, y) ↦ eᵗ β_y` pulls the tautological one-form of the annihilator line back to the
symplectization form `eᵗ β`. -/
@[simp]
theorem mpullback_symplectizationToAnnihilator_annihilatorLiouvilleForm
    (hD : IsContMDiffDistribution I ∞ k D) (hk : k + 1 = finrank ℝ E) (β : SmoothForm I M ℝ 1)
    (hβ : ∀ y, SmoothForm.degreeOneEquiv β y ∈ annihilatorSpace D y) :
    letI := annihilatorFiberBundle hD (m := ∞) (by simp) hk
    letI := annihilatorVectorBundle hD (m := ∞) (by simp) hk
    letI := annihilatorContMDiffVectorBundle hD (m := ∞) (by simp) hk
    SmoothForm.mpullback (symplectizationToAnnihilator β hβ)
        (contMDiff_symplectizationToAnnihilator hD hk β hβ) (annihilatorLiouvilleForm hD hk) =
      β.symplectization := by
  let := annihilatorFiberBundle hD (m := ∞) (by simp) hk
  let := annihilatorVectorBundle hD (m := ∞) (by simp) hk
  let := annihilatorContMDiffVectorBundle hD (m := ∞) (by simp) hk
  rw [annihilatorLiouvilleForm, SmoothForm.mpullback_mpullback_of_comp_eq
    (contMDiff_symplectizationToAnnihilator hD hk β hβ)
    (contMDiff_annihilatorInclusion hD (m := ∞) (by simp) hk)
    β.contMDiff_symplectizationToCotangent contMDiff_id
    ((annihilatorInclusion_comp_symplectizationToAnnihilator β hβ).trans
      (Function.id_comp _).symm), SmoothForm.mpullback_id, LinearMap.id_apply,
    SmoothForm.mpullback_symplectizationToCotangent_liouvilleForm]

end TauCeti.SmoothForm

namespace TauCeti.CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {k : ℕ} {D : Π x : M, Submodule ℝ (TangentSpace I x)}

/-! ### Nondegeneracy and the Levi form -/

section Nondegenerate

variable [FiniteDimensional ℝ E] [T2Space M]

/-- **The symplectization of a hyperplane field is symplectic exactly where it is contact.** For a
smooth hyperplane field `D` on a Hausdorff manifold, the exterior derivative `dθ` of the
tautological one-form of its annihilator line is nondegenerate at a nonzero covector `ℓ` over `x`
exactly when the Levi form of `D` is nondegenerate at `x`. -/
theorem nondegenerate_bilinFormAt_mextDerivₗ_annihilatorLiouvilleForm_iff
    (hD : IsContMDiffDistribution I ∞ k D) (hk : k + 1 = finrank ℝ E) :
    letI := annihilatorFiberBundle hD (m := ∞) (by simp) hk
    letI := annihilatorVectorBundle hD (m := ∞) (by simp) hk
    letI := annihilatorContMDiffVectorBundle hD (m := ∞) (by simp) hk
    ∀ {z : TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace D x}, z.2 ≠ 0 →
      (((mextDerivₗ (I.prod 𝓘(ℝ, Fin 1 → ℝ)) 1 (annihilatorLiouvilleForm hD hk)).bilinFormAt
        z).Nondegenerate ↔ Bijective (distributionLeviForm D z.proj)) := by
  let := annihilatorFiberBundle hD (m := ∞) (by simp) hk
  let := annihilatorVectorBundle hD (m := ∞) (by simp) hk
  let := annihilatorContMDiffVectorBundle hD (m := ∞) (by simp) hk
  rintro ⟨x, c, hc⟩ hz
  have hc0 : c ≠ 0 := fun h ↦ hz ((Submodule.mk_eq_zero _ hc).2 h)
  obtain ⟨β, hβD, hβx, hβker⟩ := exists_degreeOneEquiv_eq_of_mem_annihilatorSpace hD hk hc hc0
  have hφx : β.symplectizationToAnnihilator hβD ((0 : ℝ), x) = ⟨x, ⟨c, hc⟩⟩ := by
    have h := SmoothForm.coe_snd_symplectizationToAnnihilator β hβD ((0 : ℝ), x)
    rw [Real.exp_zero, one_smul, hβx] at h
    exact congrArg (TotalSpace.mk x) (Subtype.ext h)
  have hβ0 : β.1 x ≠ 0 := by
    intro h
    apply hc0
    rw [← hβx]
    ext v
    simp [SmoothForm.degreeOneEquiv_apply_apply_vec, h]
  have key := SmoothForm.nondegenerate_bilinFormAt_mextDerivₗ_iff_of_mpullback_eq_symplectization
    (SmoothForm.contMDiff_symplectizationToAnnihilator hD hk β hβD) (q := TotalSpace.proj)
    ((Bundle.contMDiff_proj (n := ∞) (fun x ↦ annihilatorSpace D x)).mdifferentiable
      (by simp)) rfl
      (SmoothForm.mpullback_symplectizationToAnnihilator_annihilatorLiouvilleForm hD hk β hβD)
    (by simp) (p := ((0 : ℝ), x)) hβ0
  rw [hφx] at key
  rw [key]
  -- The contact condition for `β` at `x` is Levi nondegeneracy of `D`.
  obtain ⟨V, hV, hxV, X, hX⟩ := isContMDiffDistribution_iff.1 hD x
  exact (RoughForm.isContactFormAt_iff_bijective_distributionLeviForm (hX.of_le (by simp))
    (hV.mem_nhds hxV) (β.mdifferentiableAt x) hβker).trans (and_iff_right hβ0)

/-- **A hyperplane field is a contact structure exactly when its symplectization is symplectic.**
A smooth hyperplane field `D` on a Hausdorff manifold is a contact structure exactly when the
exterior derivative `dθ` of the tautological one-form of its annihilator line is nondegenerate at
every nonzero covector. -/
theorem isContactDistribution_iff_forall_nondegenerate (hD : IsContMDiffDistribution I ∞ k D)
    (hk : k + 1 = finrank ℝ E) :
    letI := annihilatorFiberBundle hD (m := ∞) (by simp) hk
    letI := annihilatorVectorBundle hD (m := ∞) (by simp) hk
    letI := annihilatorContMDiffVectorBundle hD (m := ∞) (by simp) hk
    IsContactDistribution I ∞ D ↔ ∀ z : TotalSpace (Fin 1 → ℝ) (fun x ↦ annihilatorSpace D x),
      z.2 ≠ 0 →
        ((mextDerivₗ (I.prod 𝓘(ℝ, Fin 1 → ℝ)) 1 (annihilatorLiouvilleForm hD hk)).bilinFormAt
          z).Nondegenerate := by
  let := annihilatorFiberBundle hD (m := ∞) (by simp) hk
  let := annihilatorVectorBundle hD (m := ∞) (by simp) hk
  let := annihilatorContMDiffVectorBundle hD (m := ∞) (by simp) hk
  have : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
  refine ⟨fun h z hz ↦ (nondegenerate_bilinFormAt_mextDerivₗ_annihilatorLiouvilleForm_iff hD hk
    hz).2 (h.bijective_distributionLeviForm z.proj), fun h ↦ ⟨by convert hD; omega,
    fun x hx ↦ ?_, fun x ↦ ?_⟩⟩
  · -- A hyperplane is a proper subspace.
    have hfin := hD.finrank_eq x
    rw [hx, finrank_top] at hfin
    have hT : finrank ℝ (TangentSpace I x) = finrank ℝ E := rfl
    omega
  · -- Some nonzero covector over `x` vanishes on `D`.
    obtain ⟨U, α, -, hxU, -, hα⟩ := hD.exists_local_annihilator hk x
    have hz : (⟨x, ⟨α x, mem_annihilatorSpace_iff_le_ker.2 (hα x hxU).2.ge⟩⟩ :
        TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace D x).2 ≠ 0 :=
      fun h ↦ (hα x hxU).1 (congrArg Subtype.val h)
    exact (nondegenerate_bilinFormAt_mextDerivₗ_annihilatorLiouvilleForm_iff hD hk hz).1 (h _ hz)

end Nondegenerate

/-! ### The symplectization as a symplectic manifold -/

/-- The **symplectization** `L* ∖ 0` of a smooth hyperplane field `D` with contact line `L`: the
open set `TauCeti.zeroSectionCompl` of nonzero covectors vanishing on `D`. -/
def annihilatorSymplectization (hD : IsContMDiffDistribution I ∞ k D) (hk : k + 1 = finrank ℝ E) :
    TopologicalSpace.Opens (TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace D x) :=
  letI := annihilatorFiberBundle hD (m := ∞) (by simp) hk
  ⟨zeroSectionCompl _ _, by
    have := annihilatorVectorBundle hD (m := ∞) (by simp) hk
    exact isOpen_zeroSectionCompl _ _⟩

/-- A covector of the annihilator line lies in the symplectization exactly when it is nonzero. -/
@[simp]
theorem mem_annihilatorSymplectization (hD : IsContMDiffDistribution I ∞ k D)
    (hk : k + 1 = finrank ℝ E) {z : TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace D x} :
    z ∈ annihilatorSymplectization hD hk ↔ z.2 ≠ 0 :=
  mem_zeroSectionCompl

/-- The symplectic form `dθ` of the symplectization `L* ∖ 0` of a smooth hyperplane field, the
restriction of the exterior derivative of its tautological one-form. It is symplectic exactly when
the hyperplane field is a contact structure
(`TauCeti.CotangentBundle.isSymplectic_annihilatorSymplecticForm_iff`). -/
def annihilatorSymplecticForm (hD : IsContMDiffDistribution I ∞ k D) (hk : k + 1 = finrank ℝ E) :
    letI := annihilatorFiberBundle hD (m := ∞) (by simp) hk
    letI := annihilatorVectorBundle hD (m := ∞) (by simp) hk
    letI := annihilatorContMDiffVectorBundle hD (m := ∞) (by simp) hk
    SmoothTwoForm (I.prod 𝓘(ℝ, Fin 1 → ℝ)) (annihilatorSymplectization hD hk) :=
  letI := annihilatorFiberBundle hD (m := ∞) (by simp) hk
  letI := annihilatorVectorBundle hD (m := ∞) (by simp) hk
  letI := annihilatorContMDiffVectorBundle hD (m := ∞) (by simp) hk
  SmoothForm.mpullback Subtype.val contMDiff_subtype_val
    (mextDerivₗ (I.prod 𝓘(ℝ, Fin 1 → ℝ)) 1 (annihilatorLiouvilleForm hD hk))

/-- The symplectic form of the symplectization `L* ∖ 0` is the restriction of `dθ` to `L* ∖ 0`. -/
theorem annihilatorSymplecticForm_eq_mpullback (hD : IsContMDiffDistribution I ∞ k D)
    (hk : k + 1 = finrank ℝ E) :
    letI := annihilatorFiberBundle hD (m := ∞) (by simp) hk
    letI := annihilatorVectorBundle hD (m := ∞) (by simp) hk
    letI := annihilatorContMDiffVectorBundle hD (m := ∞) (by simp) hk
    annihilatorSymplecticForm hD hk = SmoothForm.mpullback Subtype.val contMDiff_subtype_val
      (mextDerivₗ (I.prod 𝓘(ℝ, Fin 1 → ℝ)) 1 (annihilatorLiouvilleForm hD hk)) :=
  (rfl)

/-- **The symplectization of a contact structure.** On a Hausdorff manifold, a smooth hyperplane
field `D` is a contact structure exactly when its symplectization `L* ∖ 0`, with the exterior
derivative `dθ` of the tautological one-form, is a symplectic manifold. -/
theorem isSymplectic_annihilatorSymplecticForm_iff [FiniteDimensional ℝ E] [T2Space M]
    (hD : IsContMDiffDistribution I ∞ k D) (hk : k + 1 = finrank ℝ E) :
    letI := annihilatorFiberBundle hD (m := ∞) (by simp) hk
    letI := annihilatorVectorBundle hD (m := ∞) (by simp) hk
    letI := annihilatorContMDiffVectorBundle hD (m := ∞) (by simp) hk
    (annihilatorSymplecticForm hD hk).IsSymplectic ↔ IsContactDistribution I ∞ D := by
  let := annihilatorFiberBundle hD (m := ∞) (by simp) hk
  let := annihilatorVectorBundle hD (m := ∞) (by simp) hk
  let := annihilatorContMDiffVectorBundle hD (m := ∞) (by simp) hk
  rw [isContactDistribution_iff_forall_nondegenerate hD hk,
    annihilatorSymplecticForm_eq_mpullback hD hk]
  refine ⟨fun h z hz ↦ ?_, fun h ↦ ⟨?_, ?_⟩⟩
  · exact SmoothTwoForm.isNondegenerate_mpullback_subtype_val_iff.1 h.isNondegenerate z
      ((mem_annihilatorSymplectization hD hk).2 hz)
  · rw [← SmoothForm.mextDerivₗ_mpullback]
    exact SmoothForm.isClosed_mextDerivₗ _
  · exact SmoothTwoForm.isNondegenerate_mpullback_subtype_val_iff.2 fun z hz ↦
      h z ((mem_annihilatorSymplectization hD hk).1 hz)

end TauCeti.CotangentBundle
