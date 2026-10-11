/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.Ostrowski
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.FieldTheory.Galois.Infinite
import TauCeti.Analysis.Normed.Ring.Ultra
import TauCeti.FieldTheory.Normal.Embeddings

/-!
# Subfields of `PadicAlgCl p` and their norms

The algebraic closure `PadicAlgCl p` of `ℚ_p` carries the spectral norm, which extends the norm of
`ℚ_p` and is preserved by `G_{ℚ_p}`. This file compares a number field `K ⊆ PadicAlgCl p` with the
`p`-adic field it generates.

* A `ℚ`-subfield `K` is dense in its `ℚ_p`-span.
* For `K / ℚ` finite Galois, a `ℚ`-embedding of `K` into `PadicAlgCl p` preserving the norm
  agrees on `K` with an element of `G_{ℚ_p}`: the embeddings of `K` inducing the given absolute
  value are the conjugates under `G_{ℚ_p}`. These are the embeddings whose product computes the
  norm down to `ℚ_p`.
* The norm `N_{K/ℚ}(Y)` is close to `N_{M/ℚ_p}(y)`, for `M` the field `K` generates over `ℚ_p`,
  when `Y` is close to `y` and every embedding of `K` not coming from `G_{ℚ_p}` sends `Y` close to
  `1`; and `N_{K/ℚ}(Y)` is close to `1` in `ℚ_q` when every embedding into `PadicAlgCl q` sends
  `Y` close to `1`.

## Main results

* `AlgEquiv.norm_apply`: elements of `G_{ℚ_p}` preserve the norm of `PadicAlgCl p`.
* `TauCeti.exists_mem_norm_sub_lt_of_mem_adjoin`
* `TauCeti.exists_algEquiv_apply_eq_of_norm_apply_eq`
* `TauCeti.algebraMap_norm_eq_prod_embeddings_of_le_adjoin`: the norm down to `ℚ_p` of an element
  of `K` is the product over the embeddings of `K` that extend to `G_{ℚ_p}`.
* `TauCeti.norm_algebraNorm_sub_one_lt`
* `TauCeti.norm_algebraNorm_sub_algebraNorm_lt`
* `TauCeti.place_ratCast_padicAlgCl`: an embedding into `PadicAlgCl q` restricts to the `q`-adic
  absolute value on `ℚ`.
-/

public section

open NumberField

namespace AlgEquiv

/-- `ℚ_[p]`-automorphisms of `AlgebraicClosure ℚ_[p]` preserve its (spectral) norm. -/
@[simp]
theorem norm_apply {p : ℕ} [Fact p.Prime]
    (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) (x : AlgebraicClosure ℚ_[p]) :
    ‖σ x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv σ x).symm

end AlgEquiv

namespace TauCeti

open scoped Classical in
/-- Let `K ⊆ M` with `M` contained in the field `K` generates over `ℚ_p`. The norm from `M` to
`ℚ_p` of an element of `K` is the product of its images under the `ℚ`-embeddings of `K` that
extend to elements of `G_{ℚ_p}`. -/
theorem algebraMap_norm_eq_prod_embeddings_of_le_adjoin (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ_[p])) [FiniteDimensional ℚ K]
    (M : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])) [FiniteDimensional ℚ_[p] M]
    (hKM : ∀ x ∈ K, x ∈ M)
    (hMK : M ≤ IntermediateField.adjoin ℚ_[p] (K : Set (AlgebraicClosure ℚ_[p]))) (Y : K) :
    algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) (Algebra.norm ℚ_[p] (⟨Y, hKM Y Y.2⟩ : M)) =
      ∏ φ ∈ Finset.univ.filter fun φ : K →ₐ[ℚ] AlgebraicClosure ℚ_[p] ↦
        ∃ h : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p], ∀ x : K, φ x = h x,
        φ Y := by
  classical
  -- Every `ℚ_[p]`-embedding of `M` extends to an automorphism of the algebraic closure.
  have hext : ∀ ψ : M →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p],
      ∃ h : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p], ∀ x : M, ψ x = h x := by
    intro ψ
    obtain ⟨h, hh⟩ := MulAction.exists_smul_eq
      (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) M.val ψ
    exact ⟨h, fun x ↦ by rw [← hh, AlgEquiv.smul_algHom_apply, IntermediateField.coe_val]⟩
  -- Two automorphisms agreeing on `K` agree on `M`.
  have hagree : ∀ h₁ h₂ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p],
      (∀ x ∈ K, h₁ x = h₂ x) → ∀ x ∈ M, h₁ x = h₂ x := by
    intro h₁ h₂ hK x hx
    refine IntermediateField.adjoin_induction ℚ_[p] (p := fun x _ ↦ h₁ x = h₂ x)
      (fun x hx ↦ hK x hx)
      (fun r ↦ by simp) (fun x y _ _ hx hy ↦ by rw [map_add, map_add, hx, hy])
      (fun x _ hx ↦ by rw [map_inv₀, map_inv₀, hx])
      (fun x y _ _ hx hy ↦ by rw [map_mul, map_mul, hx, hy]) (hMK hx)
  -- Restriction to `K` is a bijection from the embeddings of `M` onto the embeddings of `K`
  -- extending to `G_{ℚ_p}`.
  let res : (M →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) → (K →ₐ[ℚ] AlgebraicClosure ℚ_[p]) :=
    fun ψ ↦ ((hext ψ).choose.toAlgHom.restrictScalars ℚ).comp K.val
  have hres : ∀ ψ (x : K), res ψ x = ψ ⟨x, hKM x x.2⟩ := fun ψ x ↦
    ((hext ψ).choose_spec ⟨x, hKM x x.2⟩).symm
  rw [Algebra.norm_eq_prod_embeddings ℚ_[p] (AlgebraicClosure ℚ_[p])]
  refine Finset.prod_bij (fun ψ _ ↦ res ψ) (fun ψ _ ↦ ?_) (fun ψ₁ _ ψ₂ _ h ↦ ?_)
    (fun φ hφ ↦ ?_) (fun ψ _ ↦ (hres ψ Y).symm)
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (hext ψ).choose, fun x ↦ rfl⟩
  · ext x
    rw [(hext ψ₁).choose_spec, (hext ψ₂).choose_spec]
    refine hagree _ _ (fun z hz ↦ ?_) x x.2
    exact DFunLike.congr_fun h ⟨z, hz⟩
  · obtain ⟨h, hh⟩ := (Finset.mem_filter.1 hφ).2
    refine ⟨h.toAlgHom.comp M.val, Finset.mem_univ _, ?_⟩
    ext x
    rw [hres, hh, AlgHom.comp_apply, IntermediateField.coe_val]
    simp

/-- The global norm of `Y` is close to the local norm of `y` when `Y` is close to `y` and every
embedding of `K` that does not extend to a `ℚ_[p]`-automorphism sends `Y` close to `1`. -/
theorem norm_algebraNorm_sub_algebraNorm_lt (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ_[p])) [FiniteDimensional ℚ K]
    (M : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])) [FiniteDimensional ℚ_[p] M]
    (hKM : ∀ x ∈ K, x ∈ M)
    (hMK : M ≤ IntermediateField.adjoin ℚ_[p] (K : Set (AlgebraicClosure ℚ_[p])))
    (Y : K) (y : M) (hy : y ≠ 0) {ε : ℝ} (hε : ε ≤ 1)
    (hYy : ‖(Y : AlgebraicClosure ℚ_[p]) - y‖ < ε * ‖(y : AlgebraicClosure ℚ_[p])‖)
    (hφ : ∀ φ : K →ₐ[ℚ] AlgebraicClosure ℚ_[p],
      (∃ h : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p], ∀ x : K, φ x = h x) ∨
        ‖φ Y - 1‖ < ε) :
    ‖((Algebra.norm ℚ Y : ℚ) : ℚ_[p]) - Algebra.norm ℚ_[p] y‖ < ε * ‖Algebra.norm ℚ_[p] y‖ := by
  classical
  have hy' : (y : AlgebraicClosure ℚ_[p]) ≠ 0 := by simpa using hy
  have hε0 : 0 < ε := pos_of_mul_pos_left ((norm_nonneg _).trans_lt hYy) (norm_nonneg _)
  let O : (K →ₐ[ℚ] AlgebraicClosure ℚ_[p]) → Prop := fun φ ↦
    ∃ h : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p], ∀ x : K, φ x = h x
  -- Split `N_{K/ℚ}(Y)` into the factor `N_{M/ℚ_p}(Y)` over the embeddings extending to `G_{ℚ_p}`
  -- and the factor over the remaining embeddings, each of which is close to `1`.
  have hNK := Algebra.norm_eq_prod_embeddings ℚ (AlgebraicClosure ℚ_[p]) Y
  have hNM := Algebra.norm_eq_prod_embeddings ℚ_[p] (AlgebraicClosure ℚ_[p]) y
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ O,
    ← algebraMap_norm_eq_prod_embeddings_of_le_adjoin p K M hKM hMK Y,
    Algebra.norm_eq_prod_embeddings ℚ_[p] (AlgebraicClosure ℚ_[p]),
    IsScalarTower.algebraMap_apply ℚ ℚ_[p] (AlgebraicClosure ℚ_[p]), eq_ratCast] at hNK
  set a := algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) ((Algebra.norm ℚ Y : ℚ) : ℚ_[p])
  set b := algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) (Algebra.norm ℚ_[p] y)
  have hb : b ≠ 0 := (map_ne_zero _).2 (Algebra.norm_ne_zero_iff.2 hy)
  have key : ‖a / b - 1‖ < ε := by
    rw [hNK, hNM, mul_div_right_comm, ← Finset.prod_div_distrib]
    refine norm_mul_sub_one_lt hε (norm_prod_sub_one_lt _ _ hε0 hε fun ψ _ ↦ ?_)
      (norm_prod_sub_one_lt _ _ hε0 hε fun φ hφ' ↦ (hφ φ).resolve_left (Finset.mem_filter.1 hφ').2)
    obtain ⟨h, hh⟩ := MulAction.exists_smul_eq
      (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) M.val ψ
    rw [← hh, AlgEquiv.smul_algHom_apply, AlgEquiv.smul_algHom_apply, IntermediateField.coe_val,
      ← map_div₀, ← map_one h, ← map_sub, h.norm_apply, div_sub_one hy',
      norm_div]
    exact (div_lt_iff₀ (norm_pos_iff.2 hy')).2 hYy
  have hlt : ‖a - b‖ < ε * ‖b‖ := by
    have : a - b = (a / b - 1) * b := by field_simp
    rw [this, norm_mul]
    exact mul_lt_mul_of_pos_right key (norm_pos_iff.2 hb)
  have e1 : ‖a - b‖ = ‖((Algebra.norm ℚ Y : ℚ) : ℚ_[p]) - Algebra.norm ℚ_[p] y‖ := by
    rw [← map_sub]
    exact PadicAlgCl.norm_extends p _
  have e2 : ‖b‖ = ‖Algebra.norm ℚ_[p] y‖ := PadicAlgCl.norm_extends p _
  rwa [e1, e2] at hlt

/-- If every embedding of `K` into `PadicAlgCl q` sends `Y` within `ε ≤ 1` of `1`, then the norm of
`Y` down to `ℚ` is within `ε` of `1` in `ℚ_[q]`. -/
theorem norm_algebraNorm_sub_one_lt {K : Type*} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    (q : ℕ) [Fact q.Prime] (Y : K) {ε : ℝ} (hε : ε ≤ 1)
    (hY : ∀ φ : K →ₐ[ℚ] AlgebraicClosure ℚ_[q], ‖φ Y - 1‖ < ε) :
    ‖((Algebra.norm ℚ Y : ℚ) : ℚ_[q]) - 1‖ < ε := by
  have hε0 : 0 < ε := (norm_nonneg _).trans_lt
    (hY (IsAlgClosed.lift (M := AlgebraicClosure ℚ_[q]) (R := ℚ) (S := K)))
  have h := norm_prod_sub_one_lt Finset.univ (fun φ : K →ₐ[ℚ] AlgebraicClosure ℚ_[q] ↦ φ Y)
    hε0 hε fun φ _ ↦ hY φ
  rw [← Algebra.norm_eq_prod_embeddings, IsScalarTower.algebraMap_apply ℚ ℚ_[q]
    (AlgebraicClosure ℚ_[q]), ← map_one (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])),
    ← map_sub, ← PadicAlgCl.coe_eq] at h
  -- `AlgebraicClosure ℚ_[q]` is `PadicAlgCl q` by definition; restate to use `norm_extends`.
  have key : ‖((algebraMap ℚ ℚ_[q] (Algebra.norm ℚ Y) - 1 : ℚ_[q]) : PadicAlgCl q)‖ < ε := h
  rw [PadicAlgCl.norm_extends] at key
  simpa using key

/-- An element of a `ℚ`-subfield `K` of `PadicAlgCl p` lying in `ℚ_p` is fixed by every
`ℚ`-embedding of `K` into `PadicAlgCl p` that preserves the norm: `ℚ` is dense in `ℚ_p`. -/
theorem algHom_apply_eq_of_norm_apply_eq_of_mem_bot (p : ℕ) [Fact p.Prime]
    {K : IntermediateField ℚ (AlgebraicClosure ℚ_[p])} (φ : K →ₐ[ℚ] AlgebraicClosure ℚ_[p])
    (hφ : ∀ x : K, ‖φ x‖ = ‖(x : AlgebraicClosure ℚ_[p])‖) {y : K}
    (hy : (y : AlgebraicClosure ℚ_[p]) ∈ (⊥ : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]))) :
    φ y = y := by
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hy
  refine eq_of_forall_dist_le fun ε hε ↦ ?_
  obtain ⟨q, hq⟩ := Padic.rat_dense p c (half_pos hε)
  have hnorm : ‖(y : AlgebraicClosure ℚ_[p]) - q‖ = ‖c - q‖ := by
    rw [← hc, ← PadicAlgCl.norm_extends]
    simp
  have h := hφ (y - q)
  rw [map_sub, map_ratCast] at h
  push_cast at h
  rw [hnorm] at h
  calc dist (φ y) (y : AlgebraicClosure ℚ_[p])
      ≤ dist (φ y) (q : AlgebraicClosure ℚ_[p]) + dist (q : AlgebraicClosure ℚ_[p]) y :=
        dist_triangle _ _ _
    _ ≤ ε := by
      rw [dist_eq_norm, dist_comm, dist_eq_norm, h, hnorm]
      linarith

/-- **Embeddings with the same absolute value are conjugate under `G_{ℚ_p}`.** Let
`K ⊆ PadicAlgCl p` be finite Galois over `ℚ`. A `ℚ`-embedding of `K` into `PadicAlgCl p` preserving
the norm agrees on `K` with an element of `G_{ℚ_p}`, so these are exactly the embeddings
contributing to the norm down to `ℚ_p` in `algebraMap_norm_eq_prod_embeddings_of_le_adjoin`. -/
theorem exists_algEquiv_apply_eq_of_norm_apply_eq (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ_[p])) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (φ : K →ₐ[ℚ] AlgebraicClosure ℚ_[p])
    (hφ : ∀ x : K, ‖φ x‖ = ‖(x : AlgebraicClosure ℚ_[p])‖) :
    ∃ h : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p], ∀ x : K, h x = φ x := by
  let r : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) →* (K ≃ₐ[ℚ] K) :=
    (AlgEquiv.restrictNormalHom K).comp (AlgEquiv.restrictScalarsHom ℚ)
  have hr (g : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) (y : K) :
      (r g y : AlgebraicClosure ℚ_[p]) = g y :=
    AlgEquiv.restrictNormal_commutes (g.restrictScalars ℚ) K y
  -- `φ` maps `K` onto itself, since `K / ℚ` is normal.
  have hmem (x : K) : φ x ∈ K :=
    (SetLike.ext_iff.mp (AlgHom.fieldRange_of_normal φ) (φ x)).mp ⟨x, rfl⟩
  let φ' : K ≃ₐ[ℚ] K := AlgEquiv.ofBijective (φ.codRestrict K.toSubalgebra hmem)
    (Algebra.IsAlgebraic.algHom_bijective _)
  have hφ' (y : K) : (φ' y : AlgebraicClosure ℚ_[p]) = φ y :=
    AlgHom.coe_codRestrict φ K.toSubalgebra hmem y
  -- `φ'` fixes the field cut out in `K` by the restrictions of `G_{ℚ_p}`, since that field lies
  -- in `ℚ_p`; so by Galois theory in `K / ℚ` it is such a restriction.
  have key : φ' ∈ r.range := by
    rw [← IntermediateField.fixingSubgroup_fixedField r.range,
      IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    rw [IntermediateField.mem_fixedField_iff] at hy
    apply Subtype.val_injective
    rw [hφ']
    refine algHom_apply_eq_of_norm_apply_eq_of_mem_bot p φ hφ ?_
    rw [InfiniteGalois.mem_bot_iff_fixed]
    intro g
    rw [← hr, hy _ ⟨g, rfl⟩]
  obtain ⟨h, hh⟩ := key
  refine ⟨h, fun x ↦ ?_⟩
  rw [← hr, hh, hφ']

/-- **A `ℚ`-subfield of `PadicAlgCl p` is dense in the field it generates over `ℚ_p`.** -/
theorem exists_mem_norm_sub_lt_of_mem_adjoin (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ_[p])) {y : AlgebraicClosure ℚ_[p]}
    (hy : y ∈ IntermediateField.adjoin ℚ_[p] (K : Set (AlgebraicClosure ℚ_[p])))
    {ε : ℝ} (hε : 0 < ε) : ∃ y₀ ∈ K, ‖y - y₀‖ < ε := by
  have hy' : y ∈ Algebra.adjoin ℚ_[p] (K : Set (AlgebraicClosure ℚ_[p])) := by
    rwa [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      fun x _ ↦ Algebra.IsAlgebraic.isAlgebraic x]
  rw [Algebra.mem_adjoin_iff] at hy'
  have hle : Subring.closure (Set.range (algebraMap ℚ_[p] _) ∪ K) ≤
      K.toSubfield.toSubring.topologicalClosure := by
    refine Subring.closure_le.2 ?_
    rintro x (⟨c, rfl⟩ | hx)
    · refine map_mem_closure (continuous_algebraMap ℚ_[p] _)
        ((Padic.denseRange_ratCast (p := p)).closure_range ▸ Set.mem_univ c) ?_
      rintro _ ⟨q, rfl⟩
      simp
    · exact subset_closure hx
  obtain ⟨y₀, hy₀, h⟩ := Metric.mem_closure_iff.1 (hle hy') ε hε
  exact ⟨y₀, hy₀, by rwa [← dist_eq_norm]⟩

/-- An embedding into `PadicAlgCl q` restricts on `ℚ` to the `q`-adic absolute value. -/
theorem place_ratCast_padicAlgCl {K : Type*} [Field K] [Algebra ℚ K] (q : ℕ) [Fact q.Prime]
    (φ : K →ₐ[ℚ] AlgebraicClosure ℚ_[q]) (r : ℚ) :
    place φ.toRingHom (r : K) = Rat.AbsoluteValue.padic q r := by
  rw [place_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_ratCast,
    Rat.AbsoluteValue.padic_eq_padicNorm, ← Padic.eq_padicNorm, ← PadicAlgCl.norm_extends,
    map_ratCast]


end TauCeti
