/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import TauCeti.LinearAlgebra.ExteriorPower.WedgePairing
import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction

/-!
# Decomposable exterior vectors

An element `θ` of the exterior power `⋀ʳ V` is *decomposable* if it is an exterior product
`v₁ ∧ ⋯ ∧ vᵣ` of vectors, that is, if it lies in the range of `exteriorPower.ιMulti`. Over a field,
the nonzero decomposable vectors are the affine cone over the Plücker image of the Grassmannian of
`r`-dimensional subspaces of `V`, and this file gives the classical basis-free equations cutting
it out.

For `η ∈ ⋀ⁿ V*` and `θ ∈ ⋀ⁿ⁺¹ V` the contraction `ι_η θ ∈ V` (`exteriorPower.contract`) is
characterized by `ξ (ι_η θ) = ⟨η ∧ ξ, θ⟩` for `ξ ∈ V*`, where `⟨-, -⟩` is the natural pairing
`exteriorPower.pairingDual` between `⋀ⁿ⁺¹ V*` and `⋀ⁿ⁺¹ V`. It is defined for every reflexive
module over a commutative ring. On `θ = v₀ ∧ ⋯ ∧ vₙ` it is an explicit combination of the `vᵢ`
(`exteriorPower.contract_ιMulti`), so it takes values in the span of the `vᵢ`, and
for linearly independent `vᵢ` its values are exactly that span: contracting by the exterior
product of a dual family with one member removed returns the corresponding `vₚ` up to sign.

The main result is the decomposability criterion, in every characteristic: for `r + 1 ≥ 1` and
`θ ∈ ⋀ʳ⁺¹ V` with `V` finite-dimensional over a field,

`θ` is decomposable `↔ (ι_η θ) ∧ θ = 0` for every `η ∈ ⋀ʳ V*`.

Decomposable vectors satisfy the equations because each `ι_η θ` lies in the span of the factors
of `θ`. Conversely, let `A` be the subspace of vectors `w` with `θ ∧ w = 0`, and extend a basis of
`A` to a basis `e` of `V`. A coordinate of `θ` in the induced basis of `⋀ʳ⁺¹ V` vanishes if its
index set misses a basis vector of `A` (Laplace expansion of the pairing,
`exteriorPower.pairingDual_ιMulti_wedge`), and it also vanishes if its index set contains a
basis vector outside `A`, because the dual coordinate of that vector kills every `ι_η θ ∈ A`.
So `θ` has at most one nonzero coordinate and is decomposable.

The zero vector is decomposable in every positive degree. The criterion is stated in positive
degree `r + 1`; in degree `0` the exterior power is `K` (`exteriorPower.zeroEquiv`) and every
element is a multiple of the empty product. When `r + 1 > dim V` the exterior power vanishes
(`exteriorPower.eq_zero_of_finrank_lt`) and both sides of the criterion hold trivially.

## Main definitions

* `exteriorPower.contract`: the contraction `ι_η θ` of `θ ∈ ⋀ⁿ⁺¹ M` by `η ∈ ⋀ⁿ M*`.
* `exteriorPower.rangeContractBasis`: the basis `v₀, …, vᵣ` of the contraction image of
  `v₀ ∧ ⋯ ∧ vᵣ` for linearly independent `vᵢ`.

## Main results

* `exteriorPower.mem_range_ιMulti_iff_forall_ι_contract_mul_eq_zero`: **the decomposability
  criterion** `θ ∈ range ιMulti ↔ ∀ η, (ι_η θ) ∧ θ = 0`.
* `exteriorPower.range_contract_flip_ιMulti`: for linearly independent `v`, the contractions of
  `v₀ ∧ ⋯ ∧ vᵣ` form the span of the `vᵢ`.
* `exteriorPower.contract_ιMulti`: the expansion of `ι_η (v₀ ∧ ⋯ ∧ vₙ)` in the `vᵢ`.
* `exteriorPower.mem_range_ιMulti_of_subsingleton_support_repr`: an element with at most one
  nonzero coordinate in the basis induced by a basis of `M` is decomposable.

## References

* P. Griffiths, J. Harris, *Principles of Algebraic Geometry*, Wiley (1978), Chapter 1, §5
  (the Plücker relations).
* J. Harris, *Algebraic Geometry: A First Course*, GTM 133, Springer (1992), Lecture 6.
-/

public section

open Module Submodule

namespace exteriorPower

section Contract

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] [IsReflexive R M] (n : ℕ)

/-- The contraction `ι_η θ ∈ M` of `θ ∈ ⋀ⁿ⁺¹ M` by `η ∈ ⋀ⁿ M*`, characterized by
`ξ (ι_η θ) = ⟨η ∧ ξ, θ⟩` for every `ξ ∈ M*` (`exteriorPower.apply_contract`), where `⟨-, -⟩` is
`exteriorPower.pairingDual`. -/
noncomputable def contract : ⋀[R]^n (Dual R M) →ₗ[R] ⋀[R]^(n + 1) M →ₗ[R] M :=
  LinearMap.mk₂ R
    (fun η θ ↦ (evalEquiv R M).symm
      ((pairingDual R M (n + 1)).flip θ ∘ₗ wedge R (Dual R M) n 1 η ∘ₗ
        (oneEquiv R (Dual R M)).symm.toLinearMap))
    (fun η₁ η₂ θ ↦ by apply (evalEquiv R M).injective; ext ξ; simp)
    (fun c η θ ↦ by apply (evalEquiv R M).injective; ext ξ; simp)
    (fun η θ₁ θ₂ ↦ by apply (evalEquiv R M).injective; ext ξ; simp)
    (fun c η θ ↦ by apply (evalEquiv R M).injective; ext ξ; simp)

variable {R M n}

/-- The defining property of the contraction: `ξ (ι_η θ) = ⟨η ∧ ξ, θ⟩`. -/
theorem apply_contract (η : ⋀[R]^n (Dual R M)) (θ : ⋀[R]^(n + 1) M) (ξ : Dual R M) :
    ξ (contract R M n η θ) =
      pairingDual R M (n + 1) (wedge R (Dual R M) n 1 η ((oneEquiv R (Dual R M)).symm ξ)) θ := by
  simp [contract]

/-- The contraction by an exterior product `f₀ ∧ ⋯ ∧ fₙ₋₁` of linear forms:
`ξ (ι_η θ) = ⟨f₀ ∧ ⋯ ∧ fₙ₋₁ ∧ ξ, θ⟩`. -/
@[simp]
theorem apply_contract_ιMulti (f : Fin n → Dual R M) (θ : ⋀[R]^(n + 1) M) (ξ : Dual R M) :
    ξ (contract R M n (ιMulti R n f) θ) =
      pairingDual R M (n + 1) (ιMulti R (n + 1) (Fin.snoc f ξ)) θ := by
  rw [apply_contract, oneEquiv_symm_apply, wedge_ιMulti, Fin.append_right_eq_snoc]

/-- **Expansion of a contraction of a decomposable vector**:
`ι_η (v₀ ∧ ⋯ ∧ vₙ) = ∑ⱼ (-1) ^ (j + n) ⟨η, v₀ ∧ ⋯ ∧ v̂ⱼ ∧ ⋯ ∧ vₙ⟩ vⱼ`. -/
theorem contract_ιMulti (η : ⋀[R]^n (Dual R M)) (v : Fin (n + 1) → M) :
    contract R M n η (ιMulti R (n + 1) v) =
      ∑ j : Fin (n + 1),
        ((-1 : R) ^ (j + n : ℕ) * pairingDual R M n η (ιMulti R n (v ∘ j.succAbove))) • v j := by
  apply (evalEquiv R M).injective
  ext ξ
  simp only [evalEquiv_apply, Dual.eval_apply, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul]
  -- Both sides are linear in `η`, so it suffices to treat `η = f₀ ∧ ⋯ ∧ fₙ₋₁`.
  have h : ξ ∘ₗ (contract R M n).flip (ιMulti R (n + 1) v) =
      ∑ j : Fin (n + 1), ((-1 : R) ^ (j + n : ℕ) * ξ (v j)) •
        (pairingDual R M n).flip (ιMulti R n (v ∘ j.succAbove)) := by
    refine linearMap_ext (AlternatingMap.ext fun f ↦ ?_)
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply, LinearMap.flip_apply,
      LinearMap.sum_apply, apply_contract_ιMulti, pairingDual_ιMulti_ιMulti]
    rw [Matrix.det_succ_column _ (Fin.last n)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [LinearMap.smul_apply, LinearMap.flip_apply, pairingDual_ιMulti_ιMulti, smul_eq_mul]
    simp [Fin.succAbove_last, Matrix.submatrix]
  have hη := LinearMap.congr_fun h η
  rw [LinearMap.sum_apply] at hη
  simp only [LinearMap.comp_apply, LinearMap.flip_apply, LinearMap.smul_apply, smul_eq_mul] at hη
  rw [hη]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- Contracting `v₀ ∧ ⋯ ∧ vₙ` by the exterior product of a dual family with its `p`-th member
removed recovers `vₚ`, up to the sign `(-1) ^ (p + n)`. -/
theorem contract_ιMulti_comp_succAbove_ιMulti {g : Fin (n + 1) → Dual R M}
    {v : Fin (n + 1) → M} (hgv : ∀ i j, g i (v j) = if i = j then 1 else 0) (p : Fin (n + 1)) :
    contract R M n (ιMulti R n (g ∘ p.succAbove)) (ιMulti R (n + 1) v) =
      (-1 : R) ^ (p + n : ℕ) • v p := by
  rw [contract_ιMulti, Finset.sum_eq_single p]
  · have h1 : (Matrix.of fun i j ↦ (g ∘ p.succAbove) j ((v ∘ p.succAbove) i)) = 1 := by
      ext i j
      simp [hgv, Matrix.one_apply, eq_comm]
    rw [pairingDual_ιMulti_ιMulti, h1, Matrix.det_one, mul_one]
  · intro j _ hjp
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (Ne.symm hjp)
    rw [pairingDual_ιMulti_ιMulti, Matrix.det_eq_zero_of_row_eq_zero k fun i ↦ by
      simp [hk, hgv, Fin.succAbove_ne], mul_zero, zero_smul]
  · simp

/-- The contractions of `v₀ ∧ ⋯ ∧ vₙ` lie in the span of the `vᵢ`. -/
theorem contract_ιMulti_mem_span (η : ⋀[R]^n (Dual R M)) (v : Fin (n + 1) → M) :
    contract R M n η (ιMulti R (n + 1) v) ∈ span R (Set.range v) := by
  rw [contract_ιMulti]
  exact sum_mem fun j _ ↦ smul_mem _ _ (subset_span ⟨j, rfl⟩)

/-- A decomposable vector satisfies the contraction equations: `(ι_η θ) ∧ θ = 0` for
`θ = v₀ ∧ ⋯ ∧ vₙ`. -/
theorem ι_contract_mul_ιMulti_eq_zero (η : ⋀[R]^n (Dual R M)) (v : Fin (n + 1) → M) :
    ExteriorAlgebra.ι R (contract R M n η (ιMulti R (n + 1) v)) *
      ExteriorAlgebra.ιMulti R (n + 1) v = 0 := by
  rw [contract_ιMulti, map_sum, Finset.sum_mul]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  have h := (ExteriorAlgebra.ιMulti R (n + 2)).map_eq_zero_of_eq (Fin.cons (v j) v)
    (i := 0) (j := j.succ) (by simp) (Fin.succ_ne_zero j).symm
  rw [ExteriorAlgebra.ιMulti_succ_apply] at h
  simp only [Matrix.vecTail, Fin.cons_zero, Fin.cons_comp_succ] at h
  rw [map_smul, smul_mul_assoc, h, smul_zero]

end Contract

section Coordinates

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}

variable {I : Type*} [LinearOrder I] (b : Basis I R M)

/-- If `θ ∧ bᵢ = 0`, then every coordinate of `θ` in the basis `b.exteriorPower n` at an index set
not containing `i` vanishes. -/
theorem basis_repr_eq_zero_of_mul_ι_eq_zero (θ : ⋀[R]^n M) {i : I}
    (hi : (θ : ExteriorAlgebra R M) * ExteriorAlgebra.ι R (b i) = 0)
    {t : Set.powersetCard I n} (hit : i ∉ t.val) : (b.exteriorPower n).repr θ t = 0 := by
  classical
  set f := b.coord ∘ Set.powersetCard.ofFinEmbEquiv.symm t
  have hwedge : wedge R M n 1 θ ((oneEquiv R M).symm (b i)) = 0 := by
    ext1
    simpa [coe_wedge, oneEquiv_symm_apply, ExteriorAlgebra.ιMulti_succ_apply] using hi
  have hf (k : Fin n) : f k (b i) = 0 := by
    have hk : Set.powersetCard.ofFinEmbEquiv.symm t k ≠ i := fun hk ↦
      hit ((Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem t i).mp ⟨k, hk⟩)
    simp [f, Basis.coord_apply, hk]
  have h := pairingDual_ιMulti_wedge (Fin.snoc f (b.coord i)) θ (b i)
  rw [hwedge, map_zero, Fin.sum_univ_castSucc] at h
  rw [basis_repr_apply, ιMultiDual, ιMulti_family]
  simpa [hf, Fin.succAbove_last, Fin.snoc_comp_castSucc] using h.symm

/-- If the dual coordinate `bⱼ^*` kills every contraction of `θ`, then every coordinate of `θ` in
the basis `b.exteriorPower (n + 1)` at an index set containing `j` vanishes. -/
theorem basis_repr_eq_zero_of_coord_contract_eq_zero [IsReflexive R M] (θ : ⋀[R]^(n + 1) M)
    {j : I} (hj : ∀ η : ⋀[R]^n (Dual R M), b.coord j (contract R M n η θ) = 0)
    {t : Set.powersetCard I (n + 1)} (hjt : j ∈ t.val) :
    (b.exteriorPower (n + 1)).repr θ t = 0 := by
  classical
  set f := b.coord ∘ Set.powersetCard.ofFinEmbEquiv.symm t
  obtain ⟨p, hp⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem t j).mpr hjt
  set σ := Equiv.swap p (Fin.last n)
  have hlast : (f ∘ σ) (Fin.last n) = b.coord j := by simp [f, σ, hp]
  -- Move the index `j` to the last place; the pairing changes by the sign of `σ`.
  have h := hj (ιMulti R n (Fin.init (f ∘ σ)))
  rw [apply_contract_ιMulti, ← hlast, Fin.snoc_init_self, AlternatingMap.map_perm,
    Units.smul_def, map_zsmul, LinearMap.smul_apply] at h
  rw [basis_repr_apply, ιMultiDual, ιMulti_family]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simpa [hs] using h

/-- An element of `⋀ⁿ⁺¹ M` with at most one nonzero coordinate in the basis `b.exteriorPower`
is decomposable. -/
theorem mem_range_ιMulti_of_subsingleton_support_repr (θ : ⋀[R]^(n + 1) M)
    (h : (((b.exteriorPower (n + 1)).repr θ).support :
      Set (Set.powersetCard I (n + 1))).Subsingleton) :
    θ ∈ Set.range (ιMulti R (n + 1)) := by
  classical
  by_cases h0 : ∃ t, (b.exteriorPower (n + 1)).repr θ t ≠ 0
  · obtain ⟨t₀, ht₀⟩ := h0
    have hθ : θ = (b.exteriorPower (n + 1)).repr θ t₀ • b.exteriorPower (n + 1) t₀ := by
      have hs := Finsupp.support_subset_singleton.1
        ((Finset.coe_eq_singleton.1 (h.eq_singleton_of_mem (Finsupp.mem_support_iff.2 ht₀))).le)
      rw [← Basis.repr_symm_single, ← hs, LinearEquiv.symm_apply_apply]
    rw [hθ, basis_apply, ιMulti_family]
    set w := b ∘ Set.powersetCard.ofFinEmbEquiv.symm t₀
    refine ⟨Function.update w 0 ((b.exteriorPower (n + 1)).repr θ t₀ • w 0), ?_⟩
    rw [AlternatingMap.map_update_smul, Function.update_eq_self]
  · push Not at h0
    have hθ : θ = 0 := (b.exteriorPower (n + 1)).ext_elem (by simpa using h0)
    exact ⟨0, by rw [hθ, (ιMulti R (n + 1)).map_coord_zero 0 rfl]⟩

end Coordinates

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] {r : ℕ}

/-- **The contraction image of a nonzero decomposable vector.** For linearly independent
`v₀, …, vᵣ`, the contractions `ι_η (v₀ ∧ ⋯ ∧ vᵣ)`, `η ∈ ⋀ʳ V*`, form the span of the `vᵢ`. Its
basis `vᵢ` is `exteriorPower.rangeContractBasis`. -/
theorem range_contract_flip_ιMulti {v : Fin (r + 1) → V} (hv : LinearIndependent K v) :
    LinearMap.range ((contract K V r).flip (ιMulti K (r + 1) v)) = span K (Set.range v) := by
  refine le_antisymm ?_ (span_le.mpr ?_)
  · rintro _ ⟨η, rfl⟩
    exact contract_ιMulti_mem_span η v
  · rintro _ ⟨p, rfl⟩
    classical
    choose g hg using fun i ↦ LinearMap.exists_extend ((Basis.span hv).coord i)
    have hgv (i j : Fin (r + 1)) : g i (v j) = if i = j then 1 else 0 := by
      have hvj : v j = (span K (Set.range v)).subtype (Basis.span hv j) := by
        simp [Basis.span_apply]
      rw [hvj, ← LinearMap.comp_apply, hg, Basis.coord_apply, Basis.repr_self,
        Finsupp.single_apply]
      exact if_congr eq_comm rfl rfl
    refine ⟨(-1 : K) ^ (p + r : ℕ) • ιMulti K r (g ∘ p.succAbove), ?_⟩
    rw [LinearMap.flip_apply, map_smul, LinearMap.smul_apply,
      contract_ιMulti_comp_succAbove_ιMulti hgv, smul_smul, ← mul_pow]
    simp

/-- The basis `v₀, …, vᵣ` of the contraction image of `v₀ ∧ ⋯ ∧ vᵣ` for linearly independent
`vᵢ` (`exteriorPower.range_contract_flip_ιMulti`). -/
noncomputable def rangeContractBasis {v : Fin (r + 1) → V} (hv : LinearIndependent K v) :
    Basis (Fin (r + 1)) K (LinearMap.range ((contract K V r).flip (ιMulti K (r + 1) v))) :=
  (Basis.span hv).map (LinearEquiv.ofEq _ _ (range_contract_flip_ιMulti hv).symm)

@[simp]
theorem rangeContractBasis_apply {v : Fin (r + 1) → V} (hv : LinearIndependent K v)
    (i : Fin (r + 1)) : (rangeContractBasis hv i : V) = v i := by
  simp [rangeContractBasis, Basis.span_apply]

/-- **The decomposability criterion.** Over a field, an element `θ` of the `(r + 1)`-st exterior
power of a finite-dimensional vector space is decomposable, `θ = v₀ ∧ ⋯ ∧ vᵣ`, exactly when
`(ι_η θ) ∧ θ = 0` for every `η ∈ ⋀ʳ V*`. -/
theorem mem_range_ιMulti_iff_forall_ι_contract_mul_eq_zero (θ : ⋀[K]^(r + 1) V) :
    θ ∈ Set.range (ιMulti K (r + 1)) ↔
      ∀ η : ⋀[K]^r (Dual K V),
        ExteriorAlgebra.ι K (contract K V r η θ) * (θ : ExteriorAlgebra K V) = 0 := by
  refine ⟨fun ⟨v, hv⟩ η ↦ hv ▸ ι_contract_mul_ιMulti_eq_zero η v, fun h ↦ ?_⟩
  classical
  -- `A` is the subspace of vectors `w` with `θ ∧ w = 0`; it contains every contraction of `θ`.
  set A : Submodule K V :=
    LinearMap.ker (LinearMap.mulLeft K (θ : ExteriorAlgebra K V) ∘ₗ ExteriorAlgebra.ι K)
  have hmemA (w : V) : w ∈ A ↔ (θ : ExteriorAlgebra K V) * ExteriorAlgebra.ι K w = 0 := by
    simp [A]
  have hcA (η : ⋀[K]^r (Dual K V)) : contract K V r η θ ∈ A := by
    have hη := h η
    rw [ExteriorAlgebra.ι_mul_eq_neg_one_pow_smul_mul θ.2, smul_eq_zero] at hη
    exact (hmemA _).mpr (hη.resolve_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)))
  -- Extend a basis `s` of `A` to a basis `e` of `V`.
  obtain ⟨s, hsA, hspan, hs⟩ := exists_linearIndependent K (A : Set V)
  have hs' : LinearIndepOn K id s := linearIndependent_subtype_iff.mp hs
  let e := Basis.extend hs'
  let : LinearOrder (hs'.extend (Set.subset_univ s)) := linearOrderOfSTO WellOrderingRel
  -- The index set of a nonzero coordinate of `θ` consists of exactly the basis vectors of `A`.
  have key (t : Set.powersetCard (hs'.extend (Set.subset_univ s)) (r + 1))
      (ht : (e.exteriorPower (r + 1)).repr θ t ≠ 0) (x : hs'.extend (Set.subset_univ s)) :
      x ∈ t.val ↔ (x : V) ∈ s := by
    refine ⟨fun hxt ↦ ?_, fun hxs ↦ ?_⟩
    · by_contra hxs
      refine ht (basis_repr_eq_zero_of_coord_contract_eq_zero e θ (fun η ↦ ?_) hxt)
      have hle : A ≤ LinearMap.ker (e.coord x) := by
        rw [← span_eq A, ← hspan, span_le]
        intro y hy
        have hyx : (⟨y, hs'.subset_extend _ hy⟩ : hs'.extend (Set.subset_univ s)) ≠ x :=
          fun hyx ↦ hxs (hyx ▸ hy)
        have hey : e ⟨y, hs'.subset_extend _ hy⟩ = y := Basis.extend_apply_self hs' _
        rw [SetLike.mem_coe, LinearMap.mem_ker, ← hey, Basis.coord_apply, Basis.repr_self,
          Finsupp.single_apply]
        simp [hyx]
      exact hle (hcA η)
    · by_contra hxt
      refine ht (basis_repr_eq_zero_of_mul_ι_eq_zero e θ ?_ hxt)
      rw [← hmemA]
      simpa [e] using hsA hxs
  refine mem_range_ιMulti_of_subsingleton_support_repr e θ fun t ht t' ht' ↦ ?_
  rw [Finset.mem_coe, Finsupp.mem_support_iff] at ht ht'
  exact Subtype.ext (Finset.ext fun x ↦ (key t ht x).trans (key t' ht' x).symm)

end Field

end exteriorPower
