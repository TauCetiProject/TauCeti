/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Fiberwise
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Graph

/-!
# Twisted cotangent bundles

A two-form `β` on a manifold `M` twists the canonical symplectic form `ω = -dλ` of the cotangent
bundle `T*M` by the *magnetic term* `π^*β`, where `π : T*M → M` is the projection. The result is
the **twisted symplectic form**

`ω_β = ω + π^*β`

(`TauCeti.CotangentBundle.twistedSymplecticForm`). For a closed `β` the pair `(T*M, ω_β)` is the
phase space of a charged particle in the magnetic field `β`, and it is the model space of cotangent
bundle reduction at a nonzero momentum value, where `β` is the curvature term of a principal
connection. The exact magnetic forms `ω + π^*dσ` are the special case `β = dσ`
(`TauCeti.CotangentBundle.magneticSymplecticForm`).

The magnetic term vanishes on vertical vectors, those in the kernel of the differential of `π`,
and the fibres are Lagrangian for `ω` (`TauCeti.CotangentBundle.isLagrangian_ker_mfderiv_proj`).
So `ω_β` agrees with `ω` as soon as one argument is vertical. This gives:

* `ω_β` is nondegenerate for every two-form `β`
  (`TauCeti.CotangentBundle.isNondegenerate_twistedSymplecticForm`): a vector `v` with
  `ω_β(v, ·) = 0` is `ω`-orthogonal to the fibre, hence vertical, hence in the kernel of `ω`;
* the fibres stay Lagrangian for `ω_β`
  (`TauCeti.CotangentBundle.isLagrangian_ker_mfderiv_proj_twistedSymplecticForm`).

Since `π^*` is injective and commutes with `d`, the form `ω_β` is closed, hence symplectic, exactly
when `β` is closed (`TauCeti.CotangentBundle.isSymplectic_twistedSymplecticForm_iff`).

Fibre translations change the magnetic term by exact forms. Translating the fibres by a one-form
`α`, `p ↦ p + α_x`, pulls `ω_β` back to `ω_(β - dα)`
(`TauCeti.CotangentBundle.mpullback_vectorBundleTranslateDiffeomorph_twistedSymplecticForm`). So
cohomologous magnetic terms give symplectomorphic twisted cotangent bundles, and the translation
realizing this covers the identity of `M`. Unlike an exact magnetic term, a closed `β` which is not
exact cannot be removed in this way. In cotangent reduction this is the effect of changing
the principal connection.

Sections detect the class of `β`. The section `s_α` of `T*M` defined by a one-form `α` pulls `ω_β`
back to `β - dα` (`TauCeti.CotangentBundle.mpullback_section_twistedSymplecticForm`), so on a
finite-dimensional manifold it is a Lagrangian map for `ω_β` exactly when `dα = β`
(`TauCeti.CotangentBundle.isLagrangianMap_section_twistedSymplecticForm_iff`). Hence `ω_β` admits a
Lagrangian section exactly when `β` is exact
(`TauCeti.CotangentBundle.exists_isLagrangianMap_section_twistedSymplecticForm_iff`); in
particular, the zero section is Lagrangian only when `β = 0`.

## Main declarations

* `TauCeti.CotangentBundle.twistedSymplecticForm`: the twisted form `ω + π^*β`.
* `TauCeti.CotangentBundle.isNondegenerate_twistedSymplecticForm`: `ω_β` is nondegenerate.
* `TauCeti.CotangentBundle.isSymplectic_twistedSymplecticForm_iff`: `ω_β` is symplectic exactly
  when `β` is closed.
* `TauCeti.CotangentBundle.isLagrangian_ker_mfderiv_proj_twistedSymplecticForm`: the fibres are
  Lagrangian for `ω_β`.
* `TauCeti.CotangentBundle.mpullback_vectorBundleTranslateDiffeomorph_twistedSymplecticForm`:
  translation by `α` pulls `ω_β` back to `ω_(β - dα)`.
* `TauCeti.CotangentBundle.isLagrangianMap_section_twistedSymplecticForm_iff`: the graph of `α` is
  Lagrangian for `ω_β` exactly when `dα = β`.
* `TauCeti.CotangentBundle.exists_isLagrangianMap_section_twistedSymplecticForm_iff`: `ω_β` has a
  Lagrangian section exactly when `β` is exact.

## References

* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Springer, 1999,
  Section 6.6 (magnetic terms on cotangent bundles).
* V. Guillemin, S. Sternberg, *Symplectic Techniques in Physics*, Cambridge University Press,
  1984 (minimal coupling and twisted cotangent bundles).
* J. E. Marsden, G. Misiołek, J.-P. Ortega, M. Perlmutter, T. S. Ratiu, *Hamiltonian Reduction by
  Stages*, Lecture Notes in Mathematics 1913, Springer, 2007, Chapter 2 (cotangent bundle
  reduction, magnetic terms and the change of connection).
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

namespace CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- The **twisted symplectic form** `ω_β = ω + π^*β` of the cotangent bundle `T*M`, for a two-form
`β` on `M`: the canonical symplectic form `ω` twisted by the pullback of the magnetic term `β`
along the projection `π : T*M → M`. It is nondegenerate for every `β`, and symplectic exactly when
`β` is closed. -/
def twistedSymplecticForm (β : SmoothTwoForm I M) :
    SmoothTwoForm (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (CotangentBundle I M) :=
  symplecticForm I M +
    SmoothForm.mpullback (TotalSpace.proj : CotangentBundle I M → M) (contMDiff_proj _) β

theorem twistedSymplecticForm_def (β : SmoothTwoForm I M) :
    twistedSymplecticForm β = symplecticForm I M +
      SmoothForm.mpullback (TotalSpace.proj : CotangentBundle I M → M) (contMDiff_proj _) β :=
  (rfl)

/-- Without a magnetic term the twisted symplectic form is the canonical one. -/
@[simp]
theorem twistedSymplecticForm_zero :
    twistedSymplecticForm (0 : SmoothTwoForm I M) = symplecticForm I M := by
  rw [twistedSymplecticForm_def, map_zero, add_zero]

/-- The magnetic term is determined by the twisted symplectic form. -/
theorem twistedSymplecticForm_injective :
    Function.Injective (twistedSymplecticForm : SmoothTwoForm I M → _) := fun _ _ h ↦
  SmoothForm.mpullback_proj_injective <| add_left_cancel <| by
    rwa [twistedSymplecticForm_def, twistedSymplecticForm_def] at h

/-- The twisted symplectic form is the canonical one exactly when the magnetic term vanishes. -/
theorem twistedSymplecticForm_eq_symplecticForm_iff (β : SmoothTwoForm I M) :
    twistedSymplecticForm β = symplecticForm I M ↔ β = 0 := by
  rw [← twistedSymplecticForm_zero (I := I) (M := M), twistedSymplecticForm_injective.eq_iff]

/-- The twisted symplectic form evaluates as the canonical symplectic form plus the magnetic term
evaluated on the projections of the two tangent vectors to `M`. -/
theorem eval₂_twistedSymplecticForm (β : SmoothTwoForm I M) (z : CotangentBundle I M)
    (v w : TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) z) :
    SmoothBundleForm.eval₂ (twistedSymplecticForm β) z v w =
      SmoothBundleForm.eval₂ (symplecticForm I M) z v w +
        SmoothBundleForm.eval₂ β z.proj
          (mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I (TotalSpace.proj : CotangentBundle I M → M) z v)
          (mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I (TotalSpace.proj : CotangentBundle I M → M) z w) := by
  rw [twistedSymplecticForm_def, SmoothBundleForm.eval₂_add, SmoothForm.eval₂_mpullback]

/-- **The twisted symplectic form agrees with `ω` on vertical vectors.** If `v` is vertical, in
the kernel of the differential of the projection, then `ω_β(v, w) = ω(v, w)` for every `w`. -/
theorem eval₂_twistedSymplecticForm_of_mem_ker (β : SmoothTwoForm I M) {z : CotangentBundle I M}
    {v : TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) z}
    (hv : v ∈ (mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I
      (TotalSpace.proj : CotangentBundle I M → M) z).ker)
    (w : TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) z) :
    SmoothBundleForm.eval₂ (twistedSymplecticForm β) z v w =
      SmoothBundleForm.eval₂ (symplecticForm I M) z v w := by
  have h0 : mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I (TotalSpace.proj : CotangentBundle I M → M) z v =
      0 :=
    LinearMap.mem_ker.1 hv
  rw [eval₂_twistedSymplecticForm, h0, SmoothBundleForm.eval₂_zero_left, add_zero]

/-- The twisted symplectic form agrees with `ω` when its second argument is vertical. -/
theorem eval₂_twistedSymplecticForm_of_mem_ker_right (β : SmoothTwoForm I M)
    {z : CotangentBundle I M} (v : TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) z)
    {w : TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) z}
    (hw : w ∈ (mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I
      (TotalSpace.proj : CotangentBundle I M → M) z).ker) :
    SmoothBundleForm.eval₂ (twistedSymplecticForm β) z v w =
      SmoothBundleForm.eval₂ (symplecticForm I M) z v w := by
  have h0 : mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I (TotalSpace.proj : CotangentBundle I M → M) z w =
      0 :=
    LinearMap.mem_ker.1 hw
  rw [eval₂_twistedSymplecticForm, h0, SmoothBundleForm.eval₂_zero_right, add_zero]

/-- **Twisted symplectic forms are nondegenerate.** For every two-form `β` on `M`, the form
`ω + π^*β` on `T*M` is fiberwise nondegenerate; closedness of `β` is not needed. -/
theorem isNondegenerate_twistedSymplecticForm (β : SmoothTwoForm I M) :
    (twistedSymplecticForm β).IsNondegenerate := by
  have hω := (isSymplectic_symplecticForm (I := I) (M := M)).isNondegenerate
  rw [SmoothTwoForm.isNondegenerate_iff_separatingLeft]
  intro z v hv
  -- Since the magnetic term vanishes on vertical vectors, `v` is `ω`-orthogonal to the fibre,
  -- which is Lagrangian for `ω`. So `v` is vertical, and then `ω(v, ·) = ω_β(v, ·) = 0`.
  have hvert : v ∈ (mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I
      (TotalSpace.proj : CotangentBundle I M → M) z).ker := by
    refine SymplecticForm.isCoisotropic_iff_le.1 (isLagrangian_ker_mfderiv_proj z).isCoisotropic
      (SymplecticForm.mem_orthogonal_iff'.2 fun w hw ↦ ?_)
    rw [SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply,
      ← eval₂_twistedSymplecticForm_of_mem_ker_right β v hw]
    exact hv w
  rw [SmoothTwoForm.isNondegenerate_iff_separatingLeft] at hω
  exact hω z v fun w ↦ (eval₂_twistedSymplecticForm_of_mem_ker β hvert w).symm.trans (hv w)

/-- **The fibres of a twisted cotangent bundle are Lagrangian.** At every covector, the vertical
tangent space is a Lagrangian subspace for the twisted symplectic form `ω + π^*β`. -/
theorem isLagrangian_ker_mfderiv_proj_twistedSymplecticForm (β : SmoothTwoForm I M)
    (z : CotangentBundle I M) :
    ((isNondegenerate_twistedSymplecticForm β).symplecticFormAt z).IsLagrangian
      (mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I (TotalSpace.proj : CotangentBundle I M → M) z).ker := by
  have h := isLagrangian_ker_mfderiv_proj (I := I) (M := M) z
  -- Pairing with a vertical vector, `ω_β` and `ω` agree, so the two orthogonals of the fibre agree.
  have horth : ((isNondegenerate_twistedSymplecticForm β).symplecticFormAt z).orthogonal
      (mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I (TotalSpace.proj : CotangentBundle I M → M) z).ker =
      ((isSymplectic_symplecticForm (I := I) (M := M)).isNondegenerate.symplecticFormAt
        z).orthogonal
        (mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I (TotalSpace.proj : CotangentBundle I M → M) z).ker := by
    ext v
    simp only [SymplecticForm.mem_orthogonal_iff,
      SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply]
    exact forall₂_congr fun y hy ↦ by rw [eval₂_twistedSymplecticForm_of_mem_ker β hy]
  rw [SymplecticForm.isLagrangian_iff, SymplecticForm.isIsotropic_iff_le,
    SymplecticForm.isCoisotropic_iff_le, horth]
  exact ⟨SymplecticForm.isIsotropic_iff_le.1 h.isIsotropic,
    SymplecticForm.isCoisotropic_iff_le.1 h.isCoisotropic⟩

/-- The twisted symplectic form is closed exactly when the magnetic term is closed. -/
theorem isClosed_twistedSymplecticForm_iff (β : SmoothTwoForm I M) :
    (twistedSymplecticForm β).IsClosed ↔ β.IsClosed := by
  rw [SmoothForm.isClosed_iff_mextDerivₗ_eq_zero, SmoothForm.isClosed_iff_mextDerivₗ_eq_zero,
    twistedSymplecticForm_def, map_add,
    (SmoothForm.isClosed_iff_mextDerivₗ_eq_zero _).1 isSymplectic_symplecticForm.isClosed,
    zero_add, SmoothForm.mextDerivₗ_mpullback,
    map_eq_zero_iff _ SmoothForm.mpullback_proj_injective]

/-- **The twisted symplectic form is symplectic exactly when the magnetic term is closed.** -/
theorem isSymplectic_twistedSymplecticForm_iff (β : SmoothTwoForm I M) :
    (twistedSymplecticForm β).IsSymplectic ↔ β.IsClosed :=
  ⟨fun h ↦ (isClosed_twistedSymplecticForm_iff β).1 h.isClosed, fun h ↦
    ⟨(isClosed_twistedSymplecticForm_iff β).2 h, isNondegenerate_twistedSymplecticForm β⟩⟩

/-- **Twisting by a closed two-form gives a symplectic form.** For a closed two-form `β` on `M`,
the form `ω + π^*β` makes `T*M` a symplectic manifold. -/
theorem isSymplectic_twistedSymplecticForm {β : SmoothTwoForm I M} (hβ : β.IsClosed) :
    (twistedSymplecticForm β).IsSymplectic :=
  (isSymplectic_twistedSymplecticForm_iff β).2 hβ

/-- **Fibre translation changes the magnetic term by an exact form.** Translating the fibres of
the cotangent bundle by a one-form `α` pulls the twisted symplectic form `ω_β` back to
`ω_(β - dα)`. So for closed `β` the translation is a symplectomorphism from
`(T*M, ω_(β - dα))` to `(T*M, ω_β)`, covering the identity of `M`: cohomologous magnetic terms
give symplectomorphic twisted cotangent bundles. -/
theorem mpullback_vectorBundleTranslateDiffeomorph_twistedSymplecticForm (α : SmoothForm I M ℝ 1)
    (β : SmoothTwoForm I M) :
    SmoothForm.mpullback _
        (vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
          (SmoothForm.degreeOneEquiv α).contMDiff).contMDiff (twistedSymplecticForm β) =
      twistedSymplecticForm (β - mextDerivₗ I 1 α) := by
  rw [twistedSymplecticForm_def, map_add, mpullback_vectorBundleTranslateDiffeomorph_symplecticForm,
    SmoothForm.mpullback_mpullback]
  -- The translation covers the identity of `M`.
  have hproj : (TotalSpace.proj : CotangentBundle I M → M) ∘
      vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
        (SmoothForm.degreeOneEquiv α).contMDiff = TotalSpace.proj :=
    funext fun p ↦ by rw [Function.comp_apply, vectorBundleTranslateDiffeomorph_apply]
  simp only [hproj, twistedSymplecticForm_def, map_sub]
  abel

/-- **A section pulls the twisted symplectic form back to `β - dα`.** The section of the
cotangent bundle defined by a smooth one-form `α` pulls `ω + π^*β` back to `β - dα`. -/
theorem mpullback_section_twistedSymplecticForm (α : SmoothForm I M ℝ 1) (β : SmoothTwoForm I M) :
    SmoothForm.mpullback (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv α x))
      (SmoothForm.degreeOneEquiv α).contMDiff (twistedSymplecticForm β) =
        β - mextDerivₗ I 1 α := by
  rw [twistedSymplecticForm_def, map_add, mpullback_symplecticForm, SmoothForm.mpullback_mpullback]
  -- The projection is a left inverse of the section.
  have hproj : (TotalSpace.proj : CotangentBundle I M → M) ∘
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv α x)) = id :=
    rfl
  simp only [hproj, SmoothForm.mpullback_id, LinearMap.id_apply]
  abel

/-- **The graph of a one-form is isotropic for `ω_β` exactly when `dα = β`.** -/
theorem isIsotropicMap_section_twistedSymplecticForm_iff (α : SmoothForm I M ℝ 1)
    (β : SmoothTwoForm I M) :
    (isNondegenerate_twistedSymplecticForm β).IsIsotropicMap I
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv α x)) ↔
      mextDerivₗ I 1 α = β := by
  rw [SmoothTwoForm.IsNondegenerate.isIsotropicMap_iff_mpullback_eq_zero
      (SmoothForm.degreeOneEquiv α).contMDiff, mpullback_section_twistedSymplecticForm,
    sub_eq_zero, eq_comm]

variable [FiniteDimensional ℝ E]

/-- **The graph of a one-form is Lagrangian for `ω_β` exactly when `dα = β`.** On a
finite-dimensional manifold, the section of the cotangent bundle defined by a smooth one-form `α`
is a Lagrangian map for the twisted symplectic form `ω + π^*β` if and only if `dα = β`. -/
theorem isLagrangianMap_section_twistedSymplecticForm_iff (α : SmoothForm I M ℝ 1)
    (β : SmoothTwoForm I M) :
    (isNondegenerate_twistedSymplecticForm β).IsLagrangianMap I
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv α x)) ↔
      mextDerivₗ I 1 α = β := by
  rw [isLagrangianMap_section_iff_isIsotropicMap, isIsotropicMap_section_twistedSymplecticForm_iff]

/-- **A twisted cotangent bundle has a Lagrangian section exactly when the magnetic term is
exact.** On a finite-dimensional manifold, some smooth one-form `α` has a Lagrangian graph for
`ω + π^*β` if and only if `β = dα` for some `α`. In particular the zero section is Lagrangian only
for `β = 0`. -/
theorem exists_isLagrangianMap_section_twistedSymplecticForm_iff (β : SmoothTwoForm I M) :
    (∃ α : SmoothForm I M ℝ 1, (isNondegenerate_twistedSymplecticForm β).IsLagrangianMap I
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv α x))) ↔
      ∃ α : SmoothForm I M ℝ 1, mextDerivₗ I 1 α = β :=
  exists_congr fun α ↦ isLagrangianMap_section_twistedSymplecticForm_iff α β

end CotangentBundle

end TauCeti
