/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.Norm.Defs
import TauCeti.LinearAlgebra.Multilinear.Span

/-!
# The determinant-lattice norm of a submodule

Let `R` be a commutative ring, `K` a commutative `R`-algebra and `V` a `K`-module with a finite
`K`-basis `b` indexed by `ι`. The *determinant-lattice norm* of an `R`-submodule `M` of `V`
relative to `b` is the `R`-submodule `M.detNorm b` of `K` spanned by the determinants `b.det v`
of all families `v : ι → V` of vectors of `M`. No stability, finiteness or invertibility of `M`
is required.

When `R` is a domain with fraction field `K` and `V = L` is a finite `K`-algebra, this is the
norm of a lattice `I ⊆ L` used to parametrise orbits of integral forms by ideal classes in orders
of `L`: when `I` is free over `R` (for instance when `R = ℤ`), the condition `N(I) = s R` means
that `I` has an oriented basis of determinant `s`. The norm transforms by the inverse
determinant of a change of basis, and by the algebra norm under multiplication by an element of
`L`; for a finitely generated `M` it is a fractional ideal, which is nonzero exactly when `M`
spans `V` over `K`.

## Main definitions and results

* `Submodule.detNorm`: the determinant-lattice norm of `M` relative to `b`.
* `Submodule.detNorm_span`: the norm of a span is spanned by the determinants of families of
  generators.
* `Submodule.detNorm_span_range`: the norm of the `R`-span of `n` vectors `v` is `R ∙ b.det v`.
* `Submodule.detNorm_eq_smul_detNorm`: changing the basis multiplies the norm by a determinant,
  `M.detNorm b = b.det b' • M.detNorm b'`.
* `Submodule.detNorm_map`: applying a `K`-linear endomorphism `f` multiplies the norm by
  `LinearMap.det f`.
* `Submodule.detNorm_smul`: for a `K`-algebra `L` and `c : L`,
  `(c • M).detNorm b = Algebra.norm K c • M.detNorm b`.
* `Submodule.detNorm_eq_bot_iff`: over a field, the norm vanishes exactly when `M` does not span
  `V` over `K`.
* `Submodule.isFractional_detNorm`: the norm of a finitely generated submodule is fractional.

## References

* M. Bhargava, B. H. Gross, X. Wang, *A positive proportion of locally soluble hyperelliptic
  curves over ℚ have no point over any odd degree extension*, arXiv:1310.7692, Theorem 16 and its
  construction.
* E. M. O'Dorney, *Rings of small rank over a Dedekind domain and their ideals*, Res. Math. Sci. 3
  (2016), Section 2.
-/

public section

open Module Set
open scoped Pointwise

namespace Submodule

section CommRing

variable {R K V ι : Type*} [CommRing R] [CommRing K] [Algebra R K] [AddCommGroup V] [Module R V]
  [Module K V] [Fintype ι] [DecidableEq ι]

/-- The **determinant-lattice norm** of an `R`-submodule `M` of `V` relative to a `K`-basis `b`
of `V`: the `R`-submodule of `K` spanned by the determinants `b.det v` of all families `v` of
vectors of `M` indexed by `ι`. -/
noncomputable def detNorm (M : Submodule R V) (b : Basis ι K V) : Submodule R K :=
  span R (b.det '' univ.pi fun _ ↦ (M : Set V))

theorem detNorm_def (M : Submodule R V) (b : Basis ι K V) :
    M.detNorm b = span R (b.det '' univ.pi fun _ ↦ (M : Set V)) := by
  rw [detNorm]

variable {M N : Submodule R V} {b : Basis ι K V}

/-- The determinant of a family of vectors of `M` lies in the determinant-lattice norm of `M`. -/
theorem det_mem_detNorm {v : ι → V} (hv : ∀ i, v i ∈ M) : b.det v ∈ M.detNorm b := by
  rw [detNorm]
  exact subset_span ⟨v, fun i _ ↦ hv i, rfl⟩

/-- The determinant-lattice norm of `M` is contained in `P` exactly when the determinants of all
families of vectors of `M` lie in `P`. -/
theorem detNorm_le_iff {P : Submodule R K} :
    M.detNorm b ≤ P ↔ ∀ v : ι → V, (∀ i, v i ∈ M) → b.det v ∈ P := by
  rw [detNorm, span_le, image_subset_iff]
  exact ⟨fun h v hv ↦ h fun i _ ↦ hv i, fun h v hv ↦ h v fun i ↦ hv i trivial⟩

@[gcongr]
theorem detNorm_mono (h : M ≤ N) : M.detNorm b ≤ N.detNorm b :=
  detNorm_le_iff.2 fun _ hv ↦ det_mem_detNorm fun i ↦ h (hv i)

/-- The zero submodule has zero determinant-lattice norm in positive rank. -/
@[simp]
theorem detNorm_bot [Nonempty ι] (b : Basis ι K V) : (⊥ : Submodule R V).detNorm b = ⊥ := by
  refine eq_bot_iff.2 (detNorm_le_iff.2 fun v hv ↦ ?_)
  obtain ⟨i⟩ := ‹Nonempty ι›
  rw [b.det.map_coord_zero i ((mem_bot R).1 (hv i))]
  exact zero_mem _

/-- **Change of basis.** If `b'` is a second basis, the norms relative to `b` and `b'` differ by
the determinant `b.det b'` of the matrix expressing `b'` in `b`. -/
theorem detNorm_eq_smul_detNorm (M : Submodule R V) (b b' : Basis ι K V) :
    M.detNorm b = b.det b' • M.detNorm b' := by
  rw [detNorm, detNorm, ← span_smul, ← image_smul, image_image]
  congr 1
  exact image_congr fun v _ ↦ by
    rw [← smul_apply, ← b.det.eq_smul_basis_det b']

/-- **Change of basis.** Over a field, if `b'` is a second basis, the norm relative to `b'` is the
norm relative to `b` divided by the determinant `b.det b'` of the matrix expressing `b'` in `b`.
-/
theorem detNorm_eq_inv_smul_detNorm {K : Type*} [Field K] [Algebra R K] [Module K V]
    (M : Submodule R V) (b b' : Basis ι K V) :
    M.detNorm b' = (b.det b')⁻¹ • M.detNorm b := by
  rw [detNorm_eq_smul_detNorm M b b', smul_smul, inv_mul_cancel₀ (b.isUnit_det b').ne_zero,
    one_smul]

variable [IsScalarTower R K V]

/-- The determinant-lattice norm of the `R`-span of a set `s` is spanned by the determinants of
the families of vectors of `s`. -/
theorem detNorm_span (s : Set V) (b : Basis ι K V) :
    (span R s).detNorm b = span R (b.det '' univ.pi fun _ ↦ s) := by
  refine le_antisymm (detNorm_le_iff.2 fun v hv ↦ ?_) ?_
  · exact (b.det.toMultilinearMap.restrictScalars R).map_mem_span_image_pi (M := fun _ : ι ↦ V)
      (fun _ ↦ s) hv
  · rw [detNorm]
    exact span_mono (image_mono (Set.pi_mono fun _ _ ↦ subset_span))

/-- The determinant-lattice norm of the `R`-span of a family `v` of `n` vectors is the principal
`R`-submodule generated by `b.det v`. -/
theorem detNorm_span_range (v : ι → V) (b : Basis ι K V) :
    (span R (range v)).detNorm b = R ∙ b.det v := by
  rw [detNorm_span]
  refine le_antisymm (span_le.2 ?_) (span_le.2 ?_)
  · rintro _ ⟨w, hw, rfl⟩
    choose σ hσ using fun i ↦ hw i trivial
    have hw' : w = v ∘ σ := funext fun i ↦ (hσ i).symm
    by_cases hinj : Function.Injective σ
    · -- A bijective reindexing changes the determinant by a sign.
      have hσe : w = v ∘ Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hinj) := by
        ext i
        simp [hw']
      rw [hσe, AlternatingMap.map_perm, Units.smul_def]
      exact zsmul_mem (mem_span_singleton_self _) _
    · -- A non-injective reindexing repeats a vector, so the determinant vanishes.
      rw [b.det.map_eq_zero_of_not_injective w fun h ↦ hinj (hw' ▸ h).of_comp]
      exact zero_mem _
  · rintro _ rfl
    exact subset_span ⟨v, fun i _ ↦ mem_range_self i, rfl⟩

/-- The determinant-lattice norm of the `R`-span of a basis, relative to that basis, is `1`. -/
@[simp]
theorem detNorm_span_range_self (b : Basis ι K V) :
    (span R (range b)).detNorm b = 1 := by
  rw [detNorm_span_range, b.det_self, one_eq_span]

/-- Applying a `K`-linear endomorphism `f` of `V` multiplies the determinant-lattice norm by the
determinant of `f`. -/
theorem detNorm_map (M : Submodule R V) (b : Basis ι K V) (f : V →ₗ[K] V) :
    (M.map (f.restrictScalars R)).detNorm b = LinearMap.det f • M.detNorm b := by
  have h : (univ.pi fun _ : ι ↦ ((M.map (f.restrictScalars R) : Submodule R V) : Set V)) =
      (fun v : ι → V ↦ f ∘ v) '' univ.pi fun _ ↦ (M : Set V) := by
    rw [map_coe, ← piMap_image_univ_pi]
    ext w
    simp [funext_iff, Pi.map_apply]
  rw [detNorm, detNorm, h, image_image, ← span_smul, ← image_smul, image_image]
  simp_rw [b.det_comp, smul_eq_mul]

end CommRing

section Algebra

variable {R K L ι : Type*} [CommRing R] [CommRing K] [Algebra R K] [Ring L] [Algebra R L]
  [Algebra K L] [IsScalarTower R K L] [Fintype ι] [DecidableEq ι]

/-- **Scaling by an element of the algebra.** Multiplying an `R`-submodule `M` of a `K`-algebra
`L` by `c : L` multiplies its determinant-lattice norm by the algebra norm of `c`. -/
theorem detNorm_smul (M : Submodule R L) (b : Basis ι K L) (c : L) :
    (c • M).detNorm b = Algebra.norm K c • M.detNorm b := by
  have h : DistribSMul.toLinearMap R L c = (Algebra.lmul K L c).restrictScalars R :=
    LinearMap.ext fun x ↦ by simp [smul_eq_mul]
  rw [pointwise_smul_def, h, detNorm_map, Algebra.norm_apply]

end Algebra

section Field

variable {R K V ι : Type*} [CommRing R] [Field K] [Algebra R K] [AddCommGroup V] [Module R V]
  [Module K V] [Fintype ι] [DecidableEq ι]

/-- Over a field, the determinant-lattice norm of `M` vanishes exactly when `M` does not span `V`
over `K`. -/
theorem detNorm_eq_bot_iff {M : Submodule R V} {b : Basis ι K V} :
    M.detNorm b = ⊥ ↔ span K (M : Set V) ≠ ⊤ := by
  rw [detNorm, span_eq_bot, forall_mem_image]
  constructor
  · intro h htop
    have hb := b.det.toMultilinearMap.map_mem_span_image_pi (fun _ ↦ (M : Set V))
      (m := b) fun i ↦ htop ▸ mem_top
    rw [AlternatingMap.coe_multilinearMap, span_eq_bot.2 (forall_mem_image.2 h), mem_bot,
      b.det_self] at hb
    exact one_ne_zero hb
  · intro hM v hv
    by_contra hdet
    have hspan := ((b.is_basis_iff_det).2 (Ne.isUnit hdet)).2
    exact hM (eq_top_iff.2 (hspan ▸ span_mono (range_subset_iff.2 fun i ↦ hv i trivial)))

end Field

section Fractional

variable {R K V ι : Type*} [CommRing R] [CommRing K] [Algebra R K] [AddCommGroup V] [Module R V]
  [Module K V] [IsScalarTower R K V] [Fintype ι] [DecidableEq ι]

/-- The determinant-lattice norm of a finitely generated submodule is finitely generated. -/
theorem FG.detNorm {M : Submodule R V} (hM : M.FG) (b : Basis ι K V) : (M.detNorm b).FG := by
  obtain ⟨s, rfl⟩ := hM
  rw [detNorm_span]
  exact fg_span ((Set.Finite.pi fun _ ↦ s.finite_toSet).image _)

/-- The determinant-lattice norm of a finitely generated submodule relative to a basis over a
localization of `R` is a fractional ideal. -/
theorem isFractional_detNorm (S : Submonoid R) [IsLocalization S K] {M : Submodule R V}
    (hM : M.FG) (b : Basis ι K V) : IsFractional S (M.detNorm b) :=
  FractionalIdeal.isFractional_of_fg (hM.detNorm b)

end Fractional

end Submodule
