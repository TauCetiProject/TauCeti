/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearMap
public import TauCeti.LinearAlgebra.End.Stable.Constructions

/-!
# Stability of precomposition on Hom modules

For an `R`-linear endomorphism `T` of a module `M` over a ring `R` and any coefficient `(R, S)`
bimodule `D` (`[SMulCommClass R S D]`), precomposition `LinearMap.lcomp S D T` is an `S`-linear
endomorphism of `M →ₗ[R] D`. When `T` is stable at `c`, `LinearMap.lcomp S D T` is also stable at
`c`, with nilpotent summand `S`-linearly isomorphic to `(LinearMap.ker (T ^ c)) →ₗ[R] D` and
invertible summand `S`-linearly isomorphic to `(LinearMap.range (T ^ c)) →ₗ[R] D` via restriction.

In particular, on a product `M₁ × M₂` where `T₁` is nilpotent and `T₂` is bijective, the invertible
summand of precomposition by `T₁.prodMap T₂` on `(M₁ × M₂) →ₗ[R] D` identifies `S`-linearly with
`M₂ →ₗ[R] D`.

## References

* D. Helm, *The Bernstein center of the category of smooth `W(k)[GL_n(F)]`-modules*,
  arXiv:1201.1874v3, Lemma 11.10.
* J.-F. Dat, D. Helm, R. Kurinczuk, and G. Moss, *Finiteness for Hecke algebras of `p`-adic groups*,
  arXiv:2203.04929v2, Section 4.
-/

public section

namespace Module.End

@[simp]
theorem lcomp_pow {R S M D : Type*} [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid D]
    [Module R M] [Module R D] [Module S D] [SMulCommClass R S D] (T : End R M) (n : ℕ) :
    (LinearMap.lcomp S D T : End S (M →ₗ[R] D)) ^ n = LinearMap.lcomp S D (T ^ n) := by
  induction n with
  | zero => ext φ x; simp
  | succ n ih =>
    rw [pow_succ, pow_succ', mul_eq_comp, ih]
    ext φ x
    rfl

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
      rw [LinearMap.mem_ker, lcomp_pow]
      ext x
      simp [pK, Submodule.projectionOnto_apply_of_mem_right hKI
        (LinearMap.mem_range_self (T ^ c) x)])
    (LinearMap.ext fun ψ ↦ LinearMap.ext fun x ↦ by
      simp [pK, Submodule.projectionOnto_apply_left])
    (LinearMap.ext fun ⟨φ, hφ_mem⟩ ↦ Subtype.ext <| LinearMap.ext fun x ↦ by
      have hφ : φ ∘ₗ (T ^ c) = 0 := by
        have hmem : ((LinearMap.lcomp S D T : End S (M →ₗ[R] D)) ^ c) φ = 0 :=
          LinearMap.mem_ker.mp hφ_mem
        rwa [lcomp_pow, LinearMap.lcomp_apply'] at hmem
      have hI : ∀ z : M, φ ((T ^ c) z) = 0 := fun z ↦ LinearMap.congr_fun hφ z
      obtain ⟨z, hz⟩ := Submodule.projection_apply_mem hKI.symm x
      simp only [LinearMap.id_apply, LinearMap.comp_apply, LinearMap.codRestrict_apply,
        LinearMap.lcomp_apply, Submodule.coe_subtype, pK]
      conv_rhs => rw [← Submodule.projection_add_projection_eq_self hKI x]
      rw [map_add, ← hz, hI z, add_zero, Submodule.coe_projectionOnto_apply])

@[simp]
theorem IsStableAt.kerPowLcompEquiv_apply {T : End R M} {c : ℕ} (h : T.IsStableAt c)
    (φ : ↥(LinearMap.ker ((LinearMap.lcomp S D T : End S (M →ₗ[R] D)) ^ c)))
    (x : ↥(LinearMap.ker (T ^ c))) :
    h.kerPowLcompEquiv S D φ x = φ.1 x.1 :=
  (rfl)

private theorem range_lcomp_pow_eq_ker_lcomp_subtype {T : End R M} {c : ℕ} (h : T.IsStableAt c) :
    LinearMap.range ((LinearMap.lcomp S D T : End S (M →ₗ[R] D)) ^ c) =
      LinearMap.ker (LinearMap.lcomp S D (LinearMap.ker (T ^ c)).subtype) := by
  let hKI := h.isCompl_ker_pow_range_pow
  let pI := (LinearMap.range (T ^ c)).projectionOnto (LinearMap.ker (T ^ c)) hKI.symm
  let eI := LinearEquiv.ofBijective _ h.bijective_restrict_range_pow
  have heI_pow :
      ∀ k (y : ↥(LinearMap.range (T ^ c))), ((eI.toLinearMap ^ k) y).1 = (T ^ k) y.1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro y
      rw [pow_succ, pow_succ, mul_apply_eq_comp, mul_apply_eq_comp, ih]
      rfl
  have heI_inv : ∀ k (y : ↥(LinearMap.range (T ^ c))),
      (eI.symm.toLinearMap ^ k) ((eI.toLinearMap ^ k) y) = y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro y
      rw [pow_succ', pow_succ, mul_apply_eq_comp, mul_apply_eq_comp, ih]
      exact eI.symm_apply_apply y
  refine le_antisymm ?_ fun φ hφ ↦ ?_
  · rintro _ ⟨θ, rfl⟩
    rw [LinearMap.mem_ker, lcomp_pow]
    ext x
    simp [LinearMap.mem_ker.mp x.2]
  · refine ⟨φ ∘ₗ (LinearMap.range (T ^ c)).subtype ∘ₗ (eI.symm.toLinearMap ^ c) ∘ₗ pI, ?_⟩
    rw [lcomp_pow]
    ext x
    simp only [LinearMap.lcomp_apply, LinearMap.comp_apply]
    have hpI : pI ((T ^ c) x) = (eI.toLinearMap ^ c) (pI x) := by
      conv_lhs => rw [← Submodule.projection_add_projection_eq_self hKI x]
      rw [map_add, LinearMap.mem_ker.mp (Submodule.projection_apply_mem hKI x), zero_add,
        ← Submodule.coe_projectionOnto_apply, ← heI_pow c (pI x)]
      exact Submodule.projectionOnto_apply_left hKI.symm _
    rw [hpI, heI_inv]
    conv_rhs => rw [← Submodule.projection_add_projection_eq_self hKI x]
    have hφK : φ ((LinearMap.ker (T ^ c)).projection _ hKI x) = 0 :=
      LinearMap.congr_fun (LinearMap.mem_ker.mp hφ) ⟨_, Submodule.projection_apply_mem hKI x⟩
    rw [map_add, hφK, zero_add, Submodule.coe_subtype, Submodule.coe_projectionOnto_apply]

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
      rw [range_lcomp_pow_eq_ker_lcomp_subtype S D h, LinearMap.mem_ker]
      ext x
      simp [pI, Submodule.projectionOnto_apply_right])
    (LinearMap.ext fun ψ ↦ LinearMap.ext fun x ↦ by
      simp [pI, Submodule.projectionOnto_apply_left])
    (LinearMap.ext fun φ ↦ Subtype.ext <| LinearMap.ext fun x ↦ by
      have hφ : φ.1 ∈ LinearMap.ker (LinearMap.lcomp S D (LinearMap.ker (T ^ c)).subtype) :=
        range_lcomp_pow_eq_ker_lcomp_subtype S D h ▸ φ.2
      have hφK : φ.1 ((LinearMap.ker (T ^ c)).projection _ hKI x) = 0 :=
        LinearMap.congr_fun (LinearMap.mem_ker.mp hφ) ⟨_, Submodule.projection_apply_mem hKI x⟩
      simp only [LinearMap.id_apply, LinearMap.comp_apply, LinearMap.codRestrict_apply,
        LinearMap.lcomp_apply, Submodule.coe_subtype, pI]
      conv_rhs => rw [← Submodule.projection_add_projection_eq_self hKI x]
      rw [map_add, hφK, zero_add, Submodule.coe_projectionOnto_apply])

@[simp]
theorem IsStableAt.rangePowLcompEquiv_apply {T : End R M} {c : ℕ} (h : T.IsStableAt c)
    (φ : ↥(LinearMap.range ((LinearMap.lcomp S D T : End S (M →ₗ[R] D)) ^ c)))
    (x : ↥(LinearMap.range (T ^ c))) :
    h.rangePowLcompEquiv S D φ x = φ.1 x.1 :=
  (rfl)

theorem IsStableAt.isCompl_ker_pow_range_pow_lcomp {T : End R M} {c : ℕ} (h : T.IsStableAt c) :
    IsCompl (LinearMap.ker ((LinearMap.lcomp S D T : End S (M →ₗ[R] D)) ^ c))
      (LinearMap.range ((LinearMap.lcomp S D T : End S (M →ₗ[R] D)) ^ c)) := by
  let hKI := h.isCompl_ker_pow_range_pow
  let pK := (LinearMap.ker (T ^ c)).projectionOnto (LinearMap.range (T ^ c)) hKI
  let pI := (LinearMap.range (T ^ c)).projectionOnto (LinearMap.ker (T ^ c)) hKI.symm
  refine ⟨Submodule.disjoint_def.mpr fun φ hφK hφI ↦ LinearMap.ext fun x ↦ ?_,
    codisjoint_iff.mpr (eq_top_iff.mpr fun φ _ ↦ ?_)⟩
  · have hK0 : φ ((LinearMap.ker (T ^ c)).projection _ hKI x) = 0 :=
      LinearMap.congr_fun
        (LinearMap.mem_ker.mp (range_lcomp_pow_eq_ker_lcomp_subtype S D h ▸ hφI))
        ⟨_, Submodule.projection_apply_mem hKI x⟩
    obtain ⟨z, hz⟩ := Submodule.projection_apply_mem hKI.symm x
    have hI0 : φ ((LinearMap.range (T ^ c)).projection _ hKI.symm x) = 0 := by
      rw [← hz]
      have hmem : ((LinearMap.lcomp S D T : End S (M →ₗ[R] D)) ^ c) φ = 0 :=
        LinearMap.mem_ker.mp hφK
      rw [lcomp_pow, LinearMap.lcomp_apply'] at hmem
      exact LinearMap.congr_fun hmem z
    conv_lhs => rw [← Submodule.projection_add_projection_eq_self hKI x]
    rw [map_add, hK0, hI0, add_zero, LinearMap.zero_apply]
  · refine Submodule.mem_sup.mpr
      ⟨(φ ∘ₗ (LinearMap.ker (T ^ c)).subtype) ∘ₗ pK, ?_,
        (φ ∘ₗ (LinearMap.range (T ^ c)).subtype) ∘ₗ pI, ?_, LinearMap.ext fun x ↦ ?_⟩
    · rw [LinearMap.mem_ker, lcomp_pow]
      ext x
      simp [pK, Submodule.projectionOnto_apply_of_mem_right hKI
        (LinearMap.mem_range_self (T ^ c) x)]
    · rw [range_lcomp_pow_eq_ker_lcomp_subtype S D h, LinearMap.mem_ker]
      ext x
      simp [pI, Submodule.projectionOnto_apply_right]
    · conv_rhs => rw [← Submodule.projection_add_projection_eq_self hKI x]
      rw [map_add]
      rfl

/-- If `T : End R M` is stable at `c`, precomposition `LinearMap.lcomp S D T` on `M →ₗ[R] D` is
stable at `c`. -/
theorem IsStableAt.lcomp {T : End R M} {c : ℕ} (h : T.IsStableAt c) :
    IsStableAt (LinearMap.lcomp S D T) c := by
  let eI := LinearEquiv.ofBijective _ h.bijective_restrict_range_pow
  rw [isStableAt_iff_isCompl_and_bijective_restrict_range_pow]
  refine ⟨h.one_le, h.isCompl_ker_pow_range_pow_lcomp S D, fun φ₁ φ₂ hEq ↦ ?_, fun φ ↦ ?_⟩
  · refine (h.rangePowLcompEquiv S D).injective <| LinearMap.ext fun y ↦ ?_
    obtain ⟨z, hz⟩ := eI.surjective y
    have hval : φ₁.1 (T z.1) = φ₂.1 (T z.1) :=
      LinearMap.congr_fun (congrArg Subtype.val hEq) z.1
    have hz' : T z.1 = y.1 := congrArg Subtype.val hz
    simp only [IsStableAt.rangePowLcompEquiv_apply, ← hz']
    exact hval
  · let ψ := (h.rangePowLcompEquiv S D φ) ∘ₗ eI.symm.toLinearMap
    refine ⟨(h.rangePowLcompEquiv S D).symm ψ, (h.rangePowLcompEquiv S D).injective ?_⟩
    ext y
    have hy : ((h.rangePowLcompEquiv S D).symm ψ).1 (T y.1) = ψ (eI y) :=
      LinearMap.congr_fun ((h.rangePowLcompEquiv S D).apply_symm_apply ψ) (eI y)
    simpa [ψ] using hy

theorem IsStable.lcomp {T : End R M} (h : T.IsStable) :
    IsStable (LinearMap.lcomp S D T) := by
  rw [isStable_def] at h ⊢
  obtain ⟨c, hc⟩ := h
  exact ⟨c, hc.lcomp S D⟩

/-- For a nilpotent endomorphism `T₁` on `M₁` and a bijective endomorphism `T₂` on `M₂`, the
invertible summand of precomposition by `T₁.prodMap T₂` on `(M₁ × M₂) →ₗ[R] D` identifies
`S`-linearly with `M₂ →ₗ[R] D`. -/
noncomputable def iInfRangePowLcompProdMapEquiv {M₁ M₂ : Type*} [AddCommGroup M₁]
    [AddCommGroup M₂] [Module R M₁] [Module R M₂] {T₁ : End R M₁} {T₂ : End R M₂}
    (h₁ : IsNilpotent T₁) (h₂ : Function.Bijective T₂) :
    ↥(⨅ n, LinearMap.range ((LinearMap.lcomp S D (T₁.prodMap T₂) : End S ((M₁ × M₂) →ₗ[R] D)) ^ n))
      ≃ₗ[S] (M₂ →ₗ[R] D) := by
  let c := Classical.choose h₁ + 1
  have hc0 : T₁ ^ c = 0 := by
    rw [pow_succ, Classical.choose_spec h₁, zero_mul]
  have hprod : IsStableAt (T₁.prodMap T₂) c :=
    (IsStableAt.of_pow_eq_zero (Nat.succ_le_succ (Nat.zero_le _)) hc0).prodMap
      (IsStableAt.of_bijective h₂ (Nat.succ_le_succ (Nat.zero_le _)))
  have hInf :
      (⨅ n, LinearMap.range
        ((LinearMap.lcomp S D (T₁.prodMap T₂) : End S ((M₁ × M₂) →ₗ[R] D)) ^ n)) =
      LinearMap.range ((LinearMap.lcomp S D (T₁.prodMap T₂) : End S ((M₁ × M₂) →ₗ[R] D)) ^ c) := by
    refine LinearMap.iInf_range_pow_eq_of_range_pow_succ_eq ?_
    rw [range_lcomp_pow_eq_ker_lcomp_subtype S D (hprod.mono (Nat.le_succ c)),
      range_lcomp_pow_eq_ker_lcomp_subtype S D hprod, hprod.ker_pow_succ_eq]
  have hRange : LinearMap.range ((T₁.prodMap T₂ : End R (M₁ × M₂)) ^ c) =
      Submodule.snd R M₁ M₂ := by
    rw [← hprod.iInf_range_pow_eq]
    exact iInf_range_pow_prodMap_of_isNilpotent_of_bijective h₁ h₂
  let eSnd : ↥(LinearMap.range ((T₁.prodMap T₂ : End R (M₁ × M₂)) ^ c)) ≃ₗ[R] M₂ :=
    (LinearEquiv.ofEq _ _ hRange).trans (Submodule.sndEquiv R M₁ M₂)
  exact (LinearEquiv.ofEq _ _ hInf).trans
    ((hprod.rangePowLcompEquiv S D).trans (eSnd.congrLeft D S))

end Ring

end Module.End

end
