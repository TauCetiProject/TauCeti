/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.WittExtension
import TauCeti.LinearAlgebra.BilinearForm.Basic

/-!
# The linear coisotropic embedding model

Let `B` be an alternating bilinear form on a real vector space `W`, with kernel
`K = ker B = {w | B(w, ·) = 0}`. Gotay's coisotropic embedding theorem realizes a presymplectic
manifold `(Q, σ)` as a coisotropic submanifold of a neighbourhood of the zero section of the dual
`(ker σ)*` of its kernel bundle. This file is its pointwise linear model.

Choose a projection `P : W → K`, that is a linear map with `P k = k` for `k ∈ K` (equivalently, a
complement `ker P` of `K`). On `W × K*` the bilinear form

`Ω((w, a), (w', a')) = B(w, w') + a'(P w) - a(P w')`

(`LinearMap.BilinForm.IsAlt.coisotropicModel`) is symplectic. Restricted to the zero section
`W × 0` it is `B`, and the zero section is coisotropic: its symplectic orthogonal is `K × 0`, the
kernel of `B` (`LinearMap.BilinForm.IsAlt.orthogonal_range_inl_coisotropicModel`). For `B = 0`
the kernel is all of `W`, `P` is the identity, and the formula is that of the canonical form
`β(v) - α(w)` of the linear cotangent space `W × W*` (`TauCeti.cotangentSymplecticForm`).

The model is universal. For a linear map `ι : W → V` into a symplectic vector space `(V, ω)`
with `ω(ι w, ι w') = B(w, w')`, the kernel of `B` is the preimage under `ι` of the symplectic
orthogonal of the image of `ι` (`TauCeti.SymplecticForm.ker_eq_comap_orthogonal_range`). When `ι`
is injective with coisotropic image, `ι` therefore carries `K` onto that orthogonal, so the kernel
of `B` has the codimension of the image: `dim K + dim W = dim V`
(`TauCeti.SymplecticForm.finrank_ker_add_finrank_of_isCoisotropic`). By Witt's extension theorem,
`ι` then extends to a linear symplectomorphism `W × K* ≃ V` from the model
(`LinearMap.BilinForm.IsAlt.exists_isSymplectomorphism_coisotropicModel`). In particular the model
does not depend on the projection `P` up to symplectomorphisms fixing the zero section
(`LinearMap.BilinForm.IsAlt.exists_isSymplectomorphism_coisotropicModel_coisotropicModel`).

## Main definitions

* `LinearMap.BilinForm.IsAlt.coisotropicModel`: the symplectic form on `W × (ker B)*`.

## Main results

* `LinearMap.BilinForm.IsAlt.orthogonal_range_inl_coisotropicModel`,
  `LinearMap.BilinForm.IsAlt.isCoisotropic_range_inl_coisotropicModel`: the zero section is
  coisotropic, with orthogonal `ker B × 0`.
* `LinearMap.BilinForm.IsAlt.exists_isSymplectomorphism_coisotropicModel`: uniqueness of
  coisotropic embeddings inducing `B`.

## References

* M. J. Gotay, *On coisotropic imbeddings of presymplectic manifolds*, Proceedings of the
  American Mathematical Society 84 (1982), 111–114.
* V. Guillemin and S. Sternberg, *Symplectic Techniques in Physics*, Cambridge University Press,
  1984, Section 39 (the coisotropic embedding theorem).
-/

public section

open Module

namespace LinearMap.BilinForm.IsAlt

open TauCeti

variable {W : Type*} [AddCommGroup W] [Module ℝ W] {B : LinearMap.BilinForm ℝ W}

/-- The bilinear form `((w, a), (w', a')) ↦ B(w, w') + a'(P w) - a(P w')` underlying the
coisotropic model. -/
private def coisotropicModelBilinForm (P : W →ₗ[ℝ] LinearMap.ker B) :
    LinearMap.BilinForm ℝ (W × Module.Dual ℝ (LinearMap.ker B)) :=
  B.compl₁₂ (LinearMap.fst ℝ _ _) (LinearMap.fst ℝ _ _) +
    (Module.Dual.eval ℝ (LinearMap.ker B)).compl₁₂ (P ∘ₗ LinearMap.fst ℝ _ _)
      (LinearMap.snd ℝ _ _) -
    (LinearMap.id : Module.Dual ℝ (LinearMap.ker B) →ₗ[ℝ] _).compl₁₂ (LinearMap.snd ℝ _ _)
      (P ∘ₗ LinearMap.fst ℝ _ _)

private theorem coisotropicModelBilinForm_apply (P : W →ₗ[ℝ] LinearMap.ker B)
    (x y : W × Module.Dual ℝ (LinearMap.ker B)) :
    coisotropicModelBilinForm P x y = B x.1 y.1 + y.2 (P x.1) - x.2 (P y.1) :=
  (rfl)

private theorem coisotropicModelBilinForm_isAlt (hB : B.IsAlt) (P : W →ₗ[ℝ] LinearMap.ker B) :
    (coisotropicModelBilinForm P).IsAlt := fun x ↦ by
  simp [coisotropicModelBilinForm_apply, hB.self_eq_zero]

private theorem coisotropicModelBilinForm_nondegenerate (hB : B.IsAlt)
    {P : W →ₗ[ℝ] LinearMap.ker B} (hP : ∀ k : LinearMap.ker B, P k = k) :
    (coisotropicModelBilinForm P).Nondegenerate := by
  refine ((coisotropicModelBilinForm_isAlt hB P).isRefl.nondegenerate_iff_separatingLeft).2 ?_
  rintro ⟨w, a⟩ h
  simp only [coisotropicModelBilinForm_apply] at h
  -- Pairing with the fibre `0 × K*` forces `P w = 0`.
  have hPw : P w = 0 := (Module.forall_dual_apply_eq_zero_iff ℝ (P w)).1 fun a' ↦ by
    simpa using h (0, a')
  -- Pairing with `K × 0` forces `a = 0`, since `B w k = 0` and `P k = k` there.
  have ha : a = 0 := LinearMap.ext fun k ↦ by
    simpa [hP, hB.isRefl.apply_eq_zero_of_mem_ker _ k.2] using h ((k : W), 0)
  -- Pairing with `W × 0` then puts `w` in `K`, where `P` is the identity.
  have hw : w ∈ LinearMap.ker B := LinearMap.mem_ker.2 <| LinearMap.ext fun w' ↦ by
    simpa [hPw, ha] using h (w', 0)
  have hw0 : (⟨w, hw⟩ : LinearMap.ker B) = 0 := (hP ⟨w, hw⟩).symm.trans hPw
  exact Prod.ext (congrArg Subtype.val hw0) ha

/-- **The linear coisotropic embedding model.** For an alternating form `B` on `W` and a
projection `P` of `W` onto the kernel `K` of `B` (`P k = k` for `k ∈ K`), the symplectic form

`((w, a), (w', a')) ↦ B(w, w') + a'(P w) - a(P w')`

on `W × K*`. It restricts to `B` on the zero section `W × 0`, which is coisotropic. -/
noncomputable def coisotropicModel (hB : B.IsAlt) (P : W →ₗ[ℝ] LinearMap.ker B)
    (hP : ∀ k : LinearMap.ker B, P k = k) :
    SymplecticForm (W × Module.Dual ℝ (LinearMap.ker B)) where
  toBilinForm := coisotropicModelBilinForm P
  isAlt := coisotropicModelBilinForm_isAlt hB P
  nondegenerate := coisotropicModelBilinForm_nondegenerate hB hP

variable (hB : B.IsAlt) {P : W →ₗ[ℝ] LinearMap.ker B} (hP : ∀ k : LinearMap.ker B, P k = k)

/-- The defining formula of the coisotropic model. -/
@[simp]
theorem coisotropicModel_apply (x y : W × Module.Dual ℝ (LinearMap.ker B)) :
    hB.coisotropicModel P hP x y = B x.1 y.1 + y.2 (P x.1) - x.2 (P y.1) :=
  (rfl)

/-- The symplectic orthogonal of the zero section `W × 0` of the coisotropic model is `K × 0`,
where `K` is the kernel of `B`. -/
theorem orthogonal_range_inl_coisotropicModel :
    (hB.coisotropicModel P hP).orthogonal (LinearMap.range (LinearMap.inl ℝ W _)) =
      (LinearMap.ker B).map (LinearMap.inl ℝ W _) := by
  ext ⟨w, a⟩
  simp only [SymplecticForm.mem_orthogonal_iff, LinearMap.mem_range, LinearMap.inl_apply,
    forall_exists_index, forall_apply_eq_imp_iff, coisotropicModel_apply, LinearMap.zero_apply,
    sub_zero, Submodule.mem_map, Prod.mk.injEq]
  constructor
  · intro h
    -- Testing against `K × 0` kills `a`; then `B w' w = 0` for all `w'` puts `w` in `K`.
    have ha : a = 0 := LinearMap.ext fun k ↦ by
      simpa [hP, LinearMap.mem_ker.1 k.2] using h k
    refine ⟨w, LinearMap.mem_ker.2 <| LinearMap.ext fun w' ↦ ?_, rfl, ha.symm⟩
    rw [LinearMap.zero_apply, ← hB.neg_eq, neg_eq_zero]
    simpa [ha] using h w'
  · rintro ⟨k, hk, rfl, rfl⟩ w'
    simpa using hB.isRefl.apply_eq_zero_of_mem_ker w' hk

/-- The zero section `W × 0` of the coisotropic model is coisotropic. -/
theorem isCoisotropic_range_inl_coisotropicModel :
    (hB.coisotropicModel P hP).IsCoisotropic (LinearMap.range (LinearMap.inl ℝ W _)) := by
  rw [SymplecticForm.isCoisotropic_iff_le, orthogonal_range_inl_coisotropicModel,
    LinearMap.range_eq_map]
  exact Submodule.map_mono le_top

/-- **Uniqueness of the linear coisotropic embedding.** Let `ι : W → V` be an injective linear map
into a finite-dimensional symplectic vector space `(V, ω)` with coisotropic image, pulling `ω`
back to `B`. Then `ι` extends to a linear symplectomorphism from the coisotropic model `W × K*`
onto `V`: its restriction to the zero section is `w ↦ ι w`. -/
theorem exists_isSymplectomorphism_coisotropicModel {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (ω : SymplecticForm V) {ι : W →ₗ[ℝ] V} (hι : Function.Injective ι)
    (hω : ∀ w w', ω (ι w) (ι w') = B w w') (hC : ω.IsCoisotropic (LinearMap.range ι)) :
    ∃ e : (W × Module.Dual ℝ (LinearMap.ker B)) ≃ₗ[ℝ] V,
      SymplecticForm.IsSymplectomorphism (hB.coisotropicModel P hP) ω e ∧
        ∀ w, e (w, 0) = ι w := by
  have : FiniteDimensional ℝ W := .of_injective ι hι
  have hdim := ω.finrank_ker_add_finrank_of_isCoisotropic hι hω hC
  let S := LinearMap.range (LinearMap.inl ℝ W (Module.Dual ℝ (LinearMap.ker B)))
  have hS (x : S) : (x : W × Module.Dual ℝ (LinearMap.ker B)).2 = 0 := by
    obtain ⟨w, hw⟩ := x.2
    rw [← hw, LinearMap.inl_apply]
  obtain ⟨e, he, hext⟩ := SymplecticForm.exists_isSymplectomorphism_extend
    (hB.coisotropicModel P hP) ω
    (by rw [Module.finrank_prod, Subspace.dual_finrank_eq, add_comm, hdim])
    (ι ∘ₗ LinearMap.fst ℝ _ _ ∘ₗ S.subtype)
    (fun x y hxy ↦ Subtype.ext <| Prod.ext (hι hxy) ((hS x).trans (hS y).symm))
    (fun x y ↦ by simp [hω, hS])
  exact ⟨e, he, fun w ↦ hext ⟨(w, 0), w, rfl⟩⟩

/-- The coisotropic model does not depend on the projection onto the kernel: for two projections
`P` and `P'` there is a linear symplectomorphism between the two models fixing the zero section
pointwise. -/
theorem exists_isSymplectomorphism_coisotropicModel_coisotropicModel [FiniteDimensional ℝ W]
    {P' : W →ₗ[ℝ] LinearMap.ker B} (hP' : ∀ k : LinearMap.ker B, P' k = k) :
    ∃ e : (W × Module.Dual ℝ (LinearMap.ker B)) ≃ₗ[ℝ] (W × Module.Dual ℝ (LinearMap.ker B)),
      SymplecticForm.IsSymplectomorphism (hB.coisotropicModel P hP)
        (hB.coisotropicModel P' hP') e ∧ ∀ w, e (w, 0) = (w, 0) :=
  hB.exists_isSymplectomorphism_coisotropicModel hP _ LinearMap.inl_injective (by simp)
    (hB.isCoisotropic_range_inl_coisotropicModel hP')

end LinearMap.BilinForm.IsAlt
