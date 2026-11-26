/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.End.Stable.Constructions
public import TauCeti.LinearAlgebra.LinearMap.Comp
import TauCeti.Algebra.Module.Equiv.Basic
import TauCeti.LinearAlgebra.End.Prod

/-!
# Stability of precomposition on Hom modules

For an `R`-linear endomorphism `T` of a module `M` over a ring `R` and any coefficient `(R, S)`
bimodule `D` (`[SMulCommClass R S D]`), precomposition `LinearMap.lcomp S D T` is an `S`-linear
endomorphism of `M →ₗ[R] D`. When `T` is stable at `c`, `LinearMap.lcomp S D T` is also stable at
`c`, with nilpotent summand `S`-linearly isomorphic to `(LinearMap.ker (T ^ c)) →ₗ[R] D` and
invertible summand `S`-linearly isomorphic to `(LinearMap.range (T ^ c)) →ₗ[R] D` via restriction.

In particular, on a product `M₁ × M₂` where `T₁` is nilpotent and `T₂` is bijective (even over a
semiring `R`), the invertible summand of precomposition by `T₁.prodMap T₂` on `(M₁ × M₂) →ₗ[R] D`
identifies `S`-linearly with `M₂ →ₗ[R] D`.

## References

* D. Helm, *The Bernstein center of the category of smooth `W(k)[GL_n(F)]`-modules*,
  arXiv:1201.1874v3, Lemma 11.10.
* J.-F. Dat, D. Helm, R. Kurinczuk, and G. Moss, *Finiteness for Hecke algebras of `p`-adic groups*,
  arXiv:2203.04929v2, Section 4.
-/

public section

namespace Module.End

section Ring

variable {R M : Type*} (S D : Type*) [Ring R] [Semiring S] [AddCommGroup M] [AddCommMonoid D]
  [Module R M] [Module R D] [Module S D] [SMulCommClass R S D]

/-- If `T : End R M` is stable at `c`, the kernel of `(LinearMap.lcomp S D T) ^ c` on `M →ₗ[R] D`
identifies `S`-linearly with `(LinearMap.ker (T ^ c)) →ₗ[R] D` by restriction. -/
noncomputable def IsStableAt.kerPowLcompEquiv {T : End R M} {c : ℕ} (h : T.IsStableAt c) :
    ↥(LinearMap.ker ((LinearMap.lcomp S D T : End S (M →ₗ[R] D)) ^ c)) ≃ₗ[S]
      (↥(LinearMap.ker (T ^ c)) →ₗ[R] D) :=
  let hKI := h.isCompl_ker_pow_range_pow
  let pK := (LinearMap.ker (T ^ c)).projectionOnto (LinearMap.range (T ^ c)) hKI
  LinearEquiv.ofLinearMap
    (LinearMap.lcomp S D (LinearMap.ker (T ^ c)).subtype ∘ₗ
      (LinearMap.ker ((LinearMap.lcomp S D T : End S (M →ₗ[R] D)) ^ c)).subtype)
    ((LinearMap.lcomp S D pK).codRestrict _ fun ψ ↦ by
      rw [LinearMap.mem_ker, LinearMap.lcomp_pow]
      ext x
      simp [pK, Submodule.projectionOnto_apply_of_mem_right hKI
        (LinearMap.mem_range_self (T ^ c) x)])
    (LinearMap.ext fun ψ ↦ LinearMap.ext fun x ↦ by
      simp [pK, Submodule.projectionOnto_apply_left])
    (LinearMap.ext fun ⟨φ, hφ_mem⟩ ↦ Subtype.ext <| LinearMap.ext fun x ↦ by
      have hφ : φ ∘ₗ (T ^ c) = 0 := by
        have hmem : ((LinearMap.lcomp S D T : End S (M →ₗ[R] D)) ^ c) φ = 0 :=
          LinearMap.mem_ker.mp hφ_mem
        rwa [LinearMap.lcomp_pow, LinearMap.lcomp_apply'] at hmem
      have hI : ∀ z : M, φ ((T ^ c) z) = 0 := fun z ↦ LinearMap.congr_fun hφ z
      obtain ⟨z, hz⟩ := Submodule.projection_apply_mem hKI.symm x
      simp only [LinearMap.id_apply, LinearMap.comp_apply, LinearMap.codRestrict_apply,
        LinearMap.lcomp_apply, Submodule.coe_subtype, pK]
      conv_rhs => rw [← Submodule.projection_add_projection_eq_self hKI x]
      rw [map_add, ← hz, hI z, add_zero, Submodule.coe_projectionOnto_apply])

/-- Evaluating `IsStableAt.kerPowLcompEquiv` restricts the linear map to `ker (T ^ c)`. -/
@[simp]
theorem IsStableAt.kerPowLcompEquiv_apply {T : End R M} {c : ℕ} (h : T.IsStableAt c)
    (φ : ↥(LinearMap.ker ((LinearMap.lcomp S D T : End S (M →ₗ[R] D)) ^ c)))
    (x : ↥(LinearMap.ker (T ^ c))) :
    h.kerPowLcompEquiv S D φ x = φ.val x.val :=
  (rfl)

/-- The inverse of `IsStableAt.kerPowLcompEquiv` extends a linear map on `ker (T ^ c)` along the
canonical projection `Submodule.projectionOnto` with kernel `range (T ^ c)`. -/
@[simp]
theorem IsStableAt.coe_kerPowLcompEquiv_symm_apply {T : End R M} {c : ℕ} (h : T.IsStableAt c)
    (ψ : ↥(LinearMap.ker (T ^ c)) →ₗ[R] D) :
    ((h.kerPowLcompEquiv S D).symm ψ : M →ₗ[R] D) =
      ψ ∘ₗ (LinearMap.ker (T ^ c)).projectionOnto (LinearMap.range (T ^ c))
        h.isCompl_ker_pow_range_pow :=
  (rfl)

/-- When `T : End R M` is stable at `c`, the range of `(LinearMap.lcomp S D T) ^ c` on `M →ₗ[R] D`
is the submodule of `R`-linear maps vanishing on `LinearMap.ker (T ^ c)`. -/
theorem IsStableAt.range_pow_lcomp_eq_ker_lcomp_subtype {T : End R M} {c : ℕ}
    (h : T.IsStableAt c) :
    LinearMap.range ((LinearMap.lcomp S D T : End S (M →ₗ[R] D)) ^ c) =
      LinearMap.ker (LinearMap.lcomp S D (LinearMap.ker (T ^ c)).subtype) := by
  let hKI := h.isCompl_ker_pow_range_pow
  let pI := (LinearMap.range (T ^ c)).projectionOnto (LinearMap.ker (T ^ c)) hKI.symm
  let eI := LinearEquiv.ofBijective _ h.bijective_restrict_range_pow
  have heI_pow (y : ↥(LinearMap.range (T ^ c))) : ((eI ^ c) y).val = (T ^ c) y.val := by
    have hcoe := LinearEquiv.coe_ofBijective_pow h.bijective_restrict_range_pow c
    simpa [eI, pow_restrict c] using congrArg Subtype.val (LinearMap.congr_fun hcoe y)
  refine le_antisymm ?_ fun φ hφ ↦ ?_
  · rintro _ ⟨θ, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.lcomp_pow]
    ext x
    simp [LinearMap.mem_ker.mp x.property]
  · refine ⟨φ ∘ₗ (LinearMap.range (T ^ c)).subtype ∘ₗ (eI ^ c).symm.toLinearMap ∘ₗ pI, ?_⟩
    rw [LinearMap.lcomp_pow]
    ext x
    simp only [LinearMap.lcomp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    have hpI : pI ((T ^ c) x) = (eI ^ c) (pI x) := by
      conv_lhs => rw [← Submodule.projection_add_projection_eq_self hKI x]
      rw [map_add, LinearMap.mem_ker.mp (Submodule.projection_apply_mem hKI x), zero_add,
        ← Submodule.coe_projectionOnto_apply, ← heI_pow (pI x)]
      exact Submodule.projectionOnto_apply_left hKI.symm _
    rw [hpI, LinearEquiv.symm_apply_apply]
    conv_rhs => rw [← Submodule.projection_add_projection_eq_self hKI x]
    have hφK : φ ((LinearMap.ker (T ^ c)).projection _ hKI x) = 0 :=
      LinearMap.congr_fun (LinearMap.mem_ker.mp hφ) ⟨_, Submodule.projection_apply_mem hKI x⟩
    rw [map_add, hφK, zero_add, Submodule.coe_subtype, Submodule.coe_projectionOnto_apply]

/-- When `T : End R M` is stable at `c`, a linear map `φ : M →ₗ[R] D` lies in the range of
`(LinearMap.lcomp S D T) ^ c` if and only if its restriction to `LinearMap.ker (T ^ c)` vanishes. -/
theorem IsStableAt.mem_range_pow_lcomp_iff {T : End R M} {c : ℕ} (h : T.IsStableAt c)
    {φ : M →ₗ[R] D} :
    φ ∈ LinearMap.range ((LinearMap.lcomp S D T : End S (M →ₗ[R] D)) ^ c) ↔
      φ ∘ₗ (LinearMap.ker (T ^ c)).subtype = 0 := by
  rw [h.range_pow_lcomp_eq_ker_lcomp_subtype S D, LinearMap.mem_ker, LinearMap.lcomp_apply']

/-- If `T : End R M` is stable at `c`, the range of `(LinearMap.lcomp S D T) ^ c` on `M →ₗ[R] D`
identifies `S`-linearly with `(LinearMap.range (T ^ c)) →ₗ[R] D` by restriction. -/
noncomputable def IsStableAt.rangePowLcompEquiv {T : End R M} {c : ℕ} (h : T.IsStableAt c) :
    ↥(LinearMap.range ((LinearMap.lcomp S D T : End S (M →ₗ[R] D)) ^ c)) ≃ₗ[S]
      (↥(LinearMap.range (T ^ c)) →ₗ[R] D) :=
  let hKI := h.isCompl_ker_pow_range_pow
  let pI := (LinearMap.range (T ^ c)).projectionOnto (LinearMap.ker (T ^ c)) hKI.symm
  LinearEquiv.ofLinearMap
    (LinearMap.lcomp S D (LinearMap.range (T ^ c)).subtype ∘ₗ
      (LinearMap.range ((LinearMap.lcomp S D T : End S (M →ₗ[R] D)) ^ c)).subtype)
    ((LinearMap.lcomp S D pI).codRestrict _ fun ψ ↦ by
      rw [h.mem_range_pow_lcomp_iff S D]
      ext x
      simp [pI, Submodule.projectionOnto_apply_right])
    (LinearMap.ext fun ψ ↦ LinearMap.ext fun x ↦ by
      simp [pI, Submodule.projectionOnto_apply_left])
    (LinearMap.ext fun φ ↦ Subtype.ext <| LinearMap.ext fun x ↦ by
      have hφ : φ.val ∘ₗ (LinearMap.ker (T ^ c)).subtype = 0 :=
        (h.mem_range_pow_lcomp_iff S D).mp φ.property
      have hφK : φ.val ((LinearMap.ker (T ^ c)).projection _ hKI x) = 0 :=
        LinearMap.congr_fun hφ ⟨_, Submodule.projection_apply_mem hKI x⟩
      simp only [LinearMap.id_apply, LinearMap.comp_apply, LinearMap.codRestrict_apply,
        LinearMap.lcomp_apply, Submodule.coe_subtype, pI]
      conv_rhs => rw [← Submodule.projection_add_projection_eq_self hKI x]
      rw [map_add, hφK, zero_add, Submodule.coe_projectionOnto_apply])

/-- Evaluating `IsStableAt.rangePowLcompEquiv` restricts the linear map to `range (T ^ c)`. -/
@[simp]
theorem IsStableAt.rangePowLcompEquiv_apply {T : End R M} {c : ℕ} (h : T.IsStableAt c)
    (φ : ↥(LinearMap.range ((LinearMap.lcomp S D T : End S (M →ₗ[R] D)) ^ c)))
    (x : ↥(LinearMap.range (T ^ c))) :
    h.rangePowLcompEquiv S D φ x = φ.val x.val :=
  (rfl)

/-- The inverse of `IsStableAt.rangePowLcompEquiv` extends a linear map on `range (T ^ c)` along
the canonical projection `Submodule.projectionOnto` with kernel `ker (T ^ c)`. -/
@[simp]
theorem IsStableAt.coe_rangePowLcompEquiv_symm_apply {T : End R M} {c : ℕ} (h : T.IsStableAt c)
    (ψ : ↥(LinearMap.range (T ^ c)) →ₗ[R] D) :
    ((h.rangePowLcompEquiv S D).symm ψ : M →ₗ[R] D) =
      ψ ∘ₗ (LinearMap.range (T ^ c)).projectionOnto (LinearMap.ker (T ^ c))
        h.isCompl_ker_pow_range_pow.symm :=
  (rfl)

/-- If `T : End R M` is stable at `c`, the kernel and range of `(LinearMap.lcomp S D T) ^ c` are
complementary `S`-submodules of `M →ₗ[R] D`. -/
theorem IsStableAt.isCompl_ker_pow_range_pow_lcomp {T : End R M} {c : ℕ} (h : T.IsStableAt c) :
    IsCompl (LinearMap.ker ((LinearMap.lcomp S D T : End S (M →ₗ[R] D)) ^ c))
      (LinearMap.range ((LinearMap.lcomp S D T : End S (M →ₗ[R] D)) ^ c)) := by
  let hKI := h.isCompl_ker_pow_range_pow
  let pK := (LinearMap.ker (T ^ c)).projectionOnto (LinearMap.range (T ^ c)) hKI
  let pI := (LinearMap.range (T ^ c)).projectionOnto (LinearMap.ker (T ^ c)) hKI.symm
  refine ⟨Submodule.disjoint_def.mpr fun φ hφK hφI ↦ LinearMap.ext fun x ↦ ?_,
    codisjoint_iff.mpr (eq_top_iff.mpr fun φ _ ↦ ?_)⟩
  · have hK0 : φ ((LinearMap.ker (T ^ c)).projection _ hKI x) = 0 :=
      LinearMap.congr_fun ((h.mem_range_pow_lcomp_iff S D).mp hφI)
        ⟨_, Submodule.projection_apply_mem hKI x⟩
    obtain ⟨z, hz⟩ := Submodule.projection_apply_mem hKI.symm x
    have hI0 : φ ((LinearMap.range (T ^ c)).projection _ hKI.symm x) = 0 := by
      rw [← hz]
      have hmem : ((LinearMap.lcomp S D T : End S (M →ₗ[R] D)) ^ c) φ = 0 :=
        LinearMap.mem_ker.mp hφK
      rw [LinearMap.lcomp_pow, LinearMap.lcomp_apply'] at hmem
      exact LinearMap.congr_fun hmem z
    conv_lhs => rw [← Submodule.projection_add_projection_eq_self hKI x]
    rw [map_add, hK0, hI0, add_zero, LinearMap.zero_apply]
  · refine Submodule.mem_sup.mpr
      ⟨(φ ∘ₗ (LinearMap.ker (T ^ c)).subtype) ∘ₗ pK, ?_,
        (φ ∘ₗ (LinearMap.range (T ^ c)).subtype) ∘ₗ pI, ?_, LinearMap.ext fun x ↦ ?_⟩
    · rw [LinearMap.mem_ker, LinearMap.lcomp_pow]
      ext x
      simp [pK, Submodule.projectionOnto_apply_of_mem_right hKI
        (LinearMap.mem_range_self (T ^ c) x)]
    · rw [h.mem_range_pow_lcomp_iff S D]
      ext x
      simp [pI, Submodule.projectionOnto_apply_right]
    · conv_rhs => rw [← Submodule.projection_add_projection_eq_self hKI x]
      simp [pK, pI, map_add, Submodule.coe_projectionOnto_apply]

/-- If `T : End R M` is stable at `c`, precomposition `LinearMap.lcomp S D T` on `M →ₗ[R] D` is
stable at `c`. -/
theorem IsStableAt.lcomp {T : End R M} {c : ℕ} (h : T.IsStableAt c) :
    IsStableAt (LinearMap.lcomp S D T) c := by
  let eI := LinearEquiv.ofBijective _ h.bijective_restrict_range_pow
  rw [isStableAt_iff_isCompl_and_bijective_restrict_range_pow]
  refine ⟨h.one_le, h.isCompl_ker_pow_range_pow_lcomp S D, fun φ₁ φ₂ hEq ↦ ?_, fun φ ↦ ?_⟩
  · refine (h.rangePowLcompEquiv S D).injective <| LinearMap.ext fun y ↦ ?_
    obtain ⟨z, hz⟩ := eI.surjective y
    have hval : φ₁.val (T z.val) = φ₂.val (T z.val) :=
      LinearMap.congr_fun (congrArg Subtype.val hEq) z.val
    have hz' : T z.val = y.val := congrArg Subtype.val hz
    simp only [IsStableAt.rangePowLcompEquiv_apply, ← hz']
    exact hval
  · let ψ := (h.rangePowLcompEquiv S D φ) ∘ₗ eI.symm.toLinearMap
    refine ⟨(h.rangePowLcompEquiv S D).symm ψ, (h.rangePowLcompEquiv S D).injective ?_⟩
    ext y
    have hy : ((h.rangePowLcompEquiv S D).symm ψ).val (T y.val) = ψ (eI y) :=
      LinearMap.congr_fun ((h.rangePowLcompEquiv S D).apply_symm_apply ψ) (eI y)
    simpa [ψ] using hy

/-- Precomposition on `M →ₗ[R] D` by a stable endomorphism `T : End R M` is stable. -/
theorem IsStable.lcomp {T : End R M} (h : T.IsStable) :
    IsStable (LinearMap.lcomp S D T) := by
  rw [isStable_def] at h ⊢
  obtain ⟨c, hc⟩ := h
  exact ⟨c, hc.lcomp S D⟩

end Ring

section Semiring

variable {R M₁ M₂ : Type*} (S D : Type*) [Semiring R] [Semiring S] [AddCommMonoid M₁]
  [AddCommMonoid M₂] [AddCommMonoid D] [Module R M₁] [Module R M₂] [Module R D] [Module S D]
  [SMulCommClass R S D]

/-- For a nilpotent endomorphism `T₁` on `M₁` and a bijective endomorphism `T₂` on `M₂`, the
invertible summand of precomposition by `T₁.prodMap T₂` on `(M₁ × M₂) →ₗ[R] D` identifies
`S`-linearly with `M₂ →ₗ[R] D` by restricting along `LinearMap.inr` (with inverse precomposing with
`LinearMap.snd`). -/
def iInfRangePowLcompProdMapEquiv {T₁ : End R M₁} {T₂ : End R M₂}
    (h₁ : IsNilpotent T₁) (h₂ : Function.Bijective T₂) :
    ↥(⨅ n, LinearMap.range ((LinearMap.lcomp S D (T₁.prodMap T₂) : End S ((M₁ × M₂) →ₗ[R] D)) ^ n))
      ≃ₗ[S] (M₂ →ₗ[R] D) :=
  LinearEquiv.ofLinearMap
    (LinearMap.lcomp S D (LinearMap.inr R M₁ M₂) ∘ₗ
      (⨅ n, LinearMap.range
        ((LinearMap.lcomp S D (T₁.prodMap T₂) : End S ((M₁ × M₂) →ₗ[R] D)) ^ n)).subtype)
    ((LinearMap.lcomp S D (LinearMap.snd R M₁ M₂)).codRestrict _ fun ψ ↦
      (Submodule.mem_iInf _).mpr fun n ↦ by
        let e₂ := LinearEquiv.ofBijective T₂ h₂
        have he₂ (y : M₂) : (e₂ ^ n) y = (T₂ ^ n) y := by
          simpa [e₂] using LinearMap.congr_fun (LinearEquiv.coe_ofBijective_pow h₂ n) y
        refine ⟨ψ ∘ₗ (e₂ ^ n).symm.toLinearMap ∘ₗ LinearMap.snd R M₁ M₂, ?_⟩
        rw [LinearMap.lcomp_pow, LinearMap.prodMap_pow]
        exact LinearMap.ext fun ⟨x₁, x₂⟩ ↦ by simp [← he₂ x₂])
    (LinearMap.ext fun ψ ↦ LinearMap.ext fun y ↦ by simp)
    (LinearMap.ext fun ⟨φ, hφ⟩ ↦ Subtype.ext <| LinearMap.ext fun ⟨x₁, x₂⟩ ↦ by
      obtain ⟨c, hc⟩ := h₁
      obtain ⟨θ, hθ⟩ := (Submodule.mem_iInf _).mp hφ c
      have hφ₁ : φ (x₁, 0) = 0 := by
        rw [← hθ, LinearMap.lcomp_pow, LinearMap.prodMap_pow]
        simp [hc, Prod.mk_zero_zero]
      have hsplit : (x₁, x₂) = (x₁, 0) + (0, x₂) := by simp
      simp only [LinearMap.id_apply, LinearMap.comp_apply, LinearMap.codRestrict_apply,
        LinearMap.lcomp_apply, Submodule.coe_subtype, LinearMap.inr_apply, LinearMap.snd_apply]
      conv_rhs => rw [hsplit]
      rw [map_add, hφ₁, zero_add])

/-- Evaluating `iInfRangePowLcompProdMapEquiv` restricts along `LinearMap.inr`. -/
@[simp]
theorem iInfRangePowLcompProdMapEquiv_apply {T₁ : End R M₁} {T₂ : End R M₂}
    (h₁ : IsNilpotent T₁) (h₂ : Function.Bijective T₂)
    (φ : ↥(⨅ n, LinearMap.range
      ((LinearMap.lcomp S D (T₁.prodMap T₂) : End S ((M₁ × M₂) →ₗ[R] D)) ^ n))) :
    iInfRangePowLcompProdMapEquiv S D h₁ h₂ φ = φ.val ∘ₗ LinearMap.inr R M₁ M₂ :=
  (rfl)

/-- The inverse of `iInfRangePowLcompProdMapEquiv` precomposes with `LinearMap.snd`. -/
@[simp]
theorem coe_iInfRangePowLcompProdMapEquiv_symm_apply {T₁ : End R M₁} {T₂ : End R M₂}
    (h₁ : IsNilpotent T₁) (h₂ : Function.Bijective T₂) (ψ : M₂ →ₗ[R] D) :
    ((iInfRangePowLcompProdMapEquiv S D h₁ h₂).symm ψ : (M₁ × M₂) →ₗ[R] D) =
      ψ ∘ₗ LinearMap.snd R M₁ M₂ :=
  (rfl)

end Semiring

end Module.End

end
