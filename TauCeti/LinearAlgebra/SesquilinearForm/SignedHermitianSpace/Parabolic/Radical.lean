/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SesquilinearForm.SignedHermitianSpace.Parabolic.Levi

/-!
# Radical elements and the Levi decomposition in hyperbolic coordinates

For a commutative ring `R` with involution `σ` and `ε = ±1`, the hyperbolic signed hermitian space
`H^ι` on `(ι → R) × (ι → R)` has the first coordinate subspace `L = {(x, 0)}` as a Lagrangian
(`TauCeti.SignedHermitianSpace.isLagrangian_range_inl_hyperbolic`), and every finite-dimensional
Lagrangian of a signed hermitian space over a field is the image of `L` under a complete hyperbolic
splitting (`TauCeti.SignedHermitianSpace.IsLagrangian.exists_isometryEquiv_map_range_inl_eq`).
The stabilizer of `L` in the unitary group is the Siegel parabolic subgroup of the splitting. This
file constructs its unipotent radical and proves the Levi decomposition.

* The **radical element** `n(β)` (`TauCeti.SignedHermitianSpace.hyperbolicRadical`), for a matrix
  `β`, is the shear `(x, y) ↦ (x + β y, y)`. It fixes `L` pointwise and acts trivially modulo `L`,
  and `n(β) n(β') = n(β + β')`. It is an isometry of `H^ι` exactly when `β` is `(-ε)`-hermitian,
  `(β.map σ)ᵀ = -(ε • β)` (`TauCeti.SignedHermitianSpace.hyperbolicRadicalParams`); for a hermitian
  form (`ε = 1`) these are the skew-hermitian matrices.
* The Levi elements `m(a)` (`TauCeti.SignedHermitianSpace.hyperbolicLevi`) normalize the radical:
  `m(a) n(β) m(a)⁻¹ = n(A β a⁻¹)` with `A = (σ(a⁻¹))ᵀ` the action of `m(a)` on `L`.
* **Levi decomposition**: an isometry of `H^ι` preserves `L` exactly when it is `n(β) m(a)` for a
  `(-ε)`-hermitian `β` and some `a ∈ GL_ι(R)`, and `β` and `a` are then unique.

Transport along a complete hyperbolic splitting `e : H^ι ≅ H` gives the radical elements
`TauCeti.SignedHermitianSpace.IsometryEquiv.radical` of the parabolic subgroup stabilizing the
Lagrangian `e(L)` of `H`, a faithful homomorphism from the additive group of `(-ε)`-hermitian
matrices to the unitary group of `H`, and the Levi decomposition of that parabolic subgroup into
radical and Levi elements (`TauCeti.SignedHermitianSpace.IsometryEquiv.levi`).

Everything works over a commutative ring, with no assumption on `2` or on trace-zero units,
because the radical is parametrized by the `(-ε)`-hermitian matrices themselves rather than by the
hermitian part of an arbitrary matrix. Write `k` for the frame of `L` (the images of the first
coordinate vectors) and `l` for the dual frame (those of the second). For a hermitian form over a
ring containing `½` and a unit `j` with `σ j = -j`, the element `n(ν)` that fixes `k` and sends `l`
to `l - k ½ j⁻¹ (ν + ν*)` is `n(β)` with `β = -½ j⁻¹ (ν + ν*)`. The same elements, written in a
fixed basis for a Witt decomposition with a core and with that normalization, are
`TauCeti.IsotropicSplitting.unipotent` and
`TauCeti.IsotropicSplitting.exists_eq_unipotent_mul_levi`.

## Main definitions

* `TauCeti.SignedHermitianSpace.hyperbolicRadical`: the shears `n(β)` of `H^ι`.
* `TauCeti.SignedHermitianSpace.hyperbolicRadicalParams σ ε ι`: the `(-ε)`-hermitian matrices.
* `TauCeti.SignedHermitianSpace.IsometryEquiv.radical`: the radical elements of the parabolic
  subgroup of a complete hyperbolic splitting.

## Main statements

* `TauCeti.SignedHermitianSpace.hyperbolicRadical_mem_isometryGroup_iff`: `n(β)` is an isometry
  exactly when `β` is `(-ε)`-hermitian.
* `TauCeti.SignedHermitianSpace.hyperbolicLevi_mul_hyperbolicRadical_mul_inv`: the conjugation
  action of the Levi elements on the radical.
* `TauCeti.SignedHermitianSpace.exists_eq_hyperbolicRadical_iff`: the radical is the group of the
  isometries fixing `L` pointwise and acting trivially modulo `L`.
* `TauCeti.SignedHermitianSpace.exists_eq_hyperbolicRadical_mul_hyperbolicLevi_iff`,
  `TauCeti.SignedHermitianSpace.hyperbolicRadical_mul_hyperbolicLevi_inj`: the Levi decomposition
  of the stabilizer of `L`, and its uniqueness.
* `TauCeti.SignedHermitianSpace.IsometryEquiv.exists_eq_radical_mul_levi_iff`,
  `TauCeti.SignedHermitianSpace.IsometryEquiv.radical_mul_levi_inj`: the same in a complete
  hyperbolic splitting.

## Provenance

The radical elements, their group law, the conjugation by Levi elements and the Levi decomposition
correspond to `New.Space.Splitting.radicalElement`, `New.Space.Splitting.radicalElement_mul`,
`New.Space.Splitting.levi_conj_radicalElement` and
`New.Space.Splitting.exists_eq_radicalElement_mul_levi` (file
`grh/src/Lib/Weil/MixedModel/IsotropicSplitting.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), which its complete
splittings `New.SiegelWeil.CompleteSplitting` use. There they are matrices in adelic frames over a
CM field, normalized by `½ j⁻¹`; here they are stated for the coordinate-free complete splittings
of a signed hermitian space over a commutative ring with involution.

## References

* W. Scharlau, *Quadratic and Hermitian Forms*, Springer (1985), Chapter 7.
* S. Kudla, *Notes on the local theta correspondence* (1996), §1.
-/

public section

open Matrix Multiplicative

namespace TauCeti.SignedHermitianSpace

variable {R : Type*}

section Params

variable [Ring R] (σ : R →+* R) (ε : ℤˣ) (ι : Type*)

/-- The **`(-ε)`-hermitian matrices** `β`, those with `(β.map σ)ᵀ = -(ε • β)`: the additive group
parametrizing the unipotent radical of the Siegel parabolic subgroup of the hyperbolic space `H^ι`.
For a hermitian form (`ε = 1`) these are the skew-hermitian matrices, and for a skew-hermitian form
(`ε = -1`) the hermitian ones. -/
def hyperbolicRadicalParams : AddSubgroup (Matrix ι ι R) where
  carrier := {β | (β.map σ)ᵀ = -(ε • β)}
  add_mem' {β β'} hβ hβ' := by
    simp only [Set.mem_ofPred_eq] at hβ hβ' ⊢
    rw [Matrix.map_add _ (map_add σ), transpose_add, hβ, hβ', smul_add, neg_add]
  zero_mem' := by simp
  neg_mem' {β} hβ := by
    simp only [Set.mem_ofPred_eq] at hβ ⊢
    rw [Matrix.map_neg _ (map_neg σ), transpose_neg, hβ, smul_neg]

variable {σ ε ι}

/-- Membership in the `(-ε)`-hermitian matrices. -/
@[simp]
theorem mem_hyperbolicRadicalParams {β : Matrix ι ι R} :
    β ∈ hyperbolicRadicalParams σ ε ι ↔ (β.map σ)ᵀ = -(ε • β) :=
  Iff.rfl

end Params

variable [CommRing R] {ι : Type*} [Fintype ι]

/-! ### Radical elements in hyperbolic coordinates -/

/-- The **radical element** `n(β)` of the hyperbolic space in coordinates: the shear
`(x, y) ↦ (x + β y, y)`, fixing the first coordinate subspace pointwise and acting trivially on the
quotient by it. It is a homomorphism from the additive group of matrices, and an isometry of the
hyperbolic form exactly for the `(-ε)`-hermitian `β`
(`TauCeti.SignedHermitianSpace.hyperbolicRadical_mem_isometryGroup_iff`). -/
def hyperbolicRadical :
    Multiplicative (Matrix ι ι R) →* ((ι → R) × (ι → R)) ≃ₗ[R] ((ι → R) × (ι → R)) where
  toFun β :=
    { toFun x := (x.1 + toAdd β *ᵥ x.2, x.2)
      invFun x := (x.1 - toAdd β *ᵥ x.2, x.2)
      map_add' x y := by
        ext <;> simp only [Prod.fst_add, Prod.snd_add, mulVec_add, Pi.add_apply]
        abel
      map_smul' c x := by ext <;> simp [mulVec_smul]
      left_inv x := by simp
      right_inv x := by simp }
  map_one' := by ext <;> simp
  map_mul' β β' := by
    ext x <;> simp [add_mulVec, add_assoc, add_comm (toAdd β' *ᵥ x.2)]

/-- The formula for the radical element `n(β)` in hyperbolic coordinates. -/
@[simp]
theorem hyperbolicRadical_apply (β : Multiplicative (Matrix ι ι R))
    (x : (ι → R) × (ι → R)) : hyperbolicRadical β x = (x.1 + toAdd β *ᵥ x.2, x.2) :=
  (rfl)

/-- The inverse of the radical element `n(β)` is the shear by `-β`. -/
@[simp]
theorem hyperbolicRadical_symm_apply (β : Multiplicative (Matrix ι ι R))
    (x : (ι → R) × (ι → R)) : (hyperbolicRadical β).symm x = (x.1 - toAdd β *ᵥ x.2, x.2) :=
  (rfl)

/-- The shear `n(β)` determines `β`. -/
theorem hyperbolicRadical_injective :
    Function.Injective (hyperbolicRadical (R := R) (ι := ι)) := by
  intro β β' h
  apply toAdd.injective
  apply mulVec_injective
  funext y
  simpa using congrArg Prod.fst (DFunLike.congr_fun h (0, y))

variable {σ : R →+* R} {ε : ℤˣ}

/-- Congruence by any matrix `N` preserves the `(-ε)`-hermitian matrices:
`(σ N)ᵀ β N` is `(-ε)`-hermitian with `β`. -/
theorem transpose_map_mul_mul_mem_hyperbolicRadicalParams [RingHomInvPair σ σ]
    (N : Matrix ι ι R) {β : Matrix ι ι R} (hβ : β ∈ hyperbolicRadicalParams σ ε ι) :
    (N.map σ)ᵀ * β * N ∈ hyperbolicRadicalParams σ ε ι := by
  rw [mem_hyperbolicRadicalParams] at hβ ⊢
  have hN : (((N.map σ)ᵀ).map σ)ᵀ = N := by
    ext i j
    simp
  rw [Matrix.map_mul (f := σ), Matrix.map_mul (f := σ), transpose_mul, transpose_mul, hN, hβ]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

/-- The Levi elements normalize the radical: `m(a) n(β) m(a)⁻¹ = n(A β a⁻¹)`, where
`A = (σ(a⁻¹))ᵀ` is the action of `m(a)` on the first coordinate subspace. -/
theorem hyperbolicLevi_mul_hyperbolicRadical_mul_inv [DecidableEq ι] (a : GL ι R)
    (β : Matrix ι ι R) :
    hyperbolicLevi σ a * hyperbolicRadical (ofAdd β) * (hyperbolicLevi σ a)⁻¹ =
      hyperbolicRadical (ofAdd
        ((((a⁻¹ : GL ι R) : Matrix ι ι R).map σ)ᵀ * β * ((a⁻¹ : GL ι R) : Matrix ι ι R))) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext x
  · simp [mul_apply_eq_comp, mulVec_add, mulVec_mulVec, Matrix.mul_assoc]
  · simp [mul_apply_eq_comp]

/-- The Levi decomposition `n(β) m(a)` is unique. -/
theorem hyperbolicRadical_mul_hyperbolicLevi_inj [DecidableEq ι] {β β' : Matrix ι ι R}
    {a a' : GL ι R} :
    hyperbolicRadical (ofAdd β) * hyperbolicLevi σ a =
        hyperbolicRadical (ofAdd β') * hyperbolicLevi σ a' ↔ β = β' ∧ a = a' := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  have ha : a = a' := by
    apply Units.ext
    apply mulVec_injective
    funext y
    simpa [mul_apply_eq_comp] using congrArg Prod.snd (DFunLike.congr_fun h (0, y))
  subst ha
  exact ⟨toAdd.symm.injective (hyperbolicRadical_injective (mul_right_cancel h)), rfl⟩

variable [RingHomInvPair σ σ]

/-- The hyperbolic form changes under the shear `n(β)` by the pairing of the second coordinates
through `(β.map σ)ᵀ + ε • β`. -/
theorem hyperbolic_form_hyperbolicRadical_apply (β : Matrix ι ι R) (x y : (ι → R) × (ι → R)) :
    (hyperbolic R σ ε ι).form (hyperbolicRadical (ofAdd β) x) (hyperbolicRadical (ofAdd β) y) =
      (hyperbolic R σ ε ι).form x y + (σ ∘ x.2) ⬝ᵥ (((β.map σ)ᵀ + ε • β) *ᵥ y.2) := by
  have hσ : σ ∘ (β *ᵥ x.2) = β.map σ *ᵥ (σ ∘ x.2) := funext (RingHom.map_mulVec σ β x.2)
  have h₁ : (σ ∘ (β *ᵥ x.2)) ⬝ᵥ y.2 = (σ ∘ x.2) ⬝ᵥ ((β.map σ)ᵀ *ᵥ y.2) := by
    rw [hσ, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
  have hadd : σ ∘ (x.1 + β *ᵥ x.2) = σ ∘ x.1 + σ ∘ (β *ᵥ x.2) := funext fun _ ↦ map_add σ _ _
  simp only [hyperbolic_form_apply_eq_dotProduct, hyperbolicRadical_apply, toAdd_ofAdd, hadd,
    add_dotProduct, dotProduct_add, h₁, add_mulVec, smul_mulVec, dotProduct_smul, smul_add]
  abel

/-- The radical element `n(β)` is an isometry of the hyperbolic space exactly when `β` is
`(-ε)`-hermitian. -/
theorem hyperbolicRadical_mem_isometryGroup_iff (β : Matrix ι ι R) :
    hyperbolicRadical (ofAdd β) ∈ (hyperbolic R σ ε ι).form.isometryGroup ↔
      β ∈ hyperbolicRadicalParams σ ε ι := by
  classical
  simp only [LinearMap.mem_isometryGroup_iff, hyperbolic_form_hyperbolicRadical_apply,
    add_eq_left, mem_hyperbolicRadicalParams, eq_neg_iff_add_eq_zero]
  refine ⟨fun h ↦ ?_, fun h x y ↦ by simp [h]⟩
  ext i j
  have hsingle : σ ∘ Pi.single i (1 : R) = Pi.single i 1 := by
    funext k
    simp [Pi.single_apply, apply_ite σ]
  simpa [hsingle, mulVec_single_one] using h (0, Pi.single i 1) (0, Pi.single j 1)

/-- The radical elements `n(β)`, for `(-ε)`-hermitian `β`, are exactly the isometries of the
hyperbolic space that fix the first coordinate subspace pointwise and act trivially modulo it. -/
theorem exists_eq_hyperbolicRadical_iff
    (g : ((ι → R) × (ι → R)) ≃ₗ[R] ((ι → R) × (ι → R))) :
    (∃ β ∈ hyperbolicRadicalParams σ ε ι, g = hyperbolicRadical (ofAdd β)) ↔
      g ∈ (hyperbolic R σ ε ι).form.isometryGroup ∧ (∀ x, g (x, 0) = (x, 0)) ∧
        ∀ y, (g (0, y)).2 = y := by
  constructor
  · rintro ⟨β, hβ, rfl⟩
    exact ⟨(hyperbolicRadical_mem_isometryGroup_iff β).2 hβ, by simp, by simp⟩
  · rintro ⟨hg, hfirst, hsecond⟩
    classical
    let β : Matrix ι ι R := LinearMap.toMatrix'
      ((LinearMap.fst R _ _).comp (g.toLinearMap.comp (LinearMap.inr R _ _)))
    have hβ (y : ι → R) : β *ᵥ y = (g (0, y)).1 := by simp [β, LinearMap.toMatrix'_mulVec]
    have hg_eq : g = hyperbolicRadical (ofAdd β) := by
      refine LinearEquiv.ext fun ⟨x, y⟩ ↦ ?_
      have hsplit : ((x, y) : (ι → R) × (ι → R)) = (x, 0) + (0, y) := by simp
      rw [hsplit, map_add, map_add, hfirst]
      ext <;> simp [hβ, hsecond, Prod.mk_zero_zero]
    refine ⟨β, ?_, hg_eq⟩
    rw [← hyperbolicRadical_mem_isometryGroup_iff, ← hg_eq]
    exact hg

/-- An isometry of the hyperbolic space preserving the first coordinate subspace acts on the second
coordinates through an invertible matrix `D`, and on the first coordinate subspace through
`(σ(D⁻¹))ᵀ`, the inverse `σ`-transpose of `D`, as a Levi element does. -/
theorem exists_hyperbolicLevi_apply_inl_eq [DecidableEq ι]
    (g : ((ι → R) × (ι → R)) ≃ₗ[R] ((ι → R) × (ι → R)))
    (hg : g ∈ (hyperbolic R σ ε ι).form.isometryGroup) (hfirst : ∀ x, (g (x, 0)).2 = 0) :
    ∃ a : GL ι R, (∀ x, g (x, 0) = hyperbolicLevi σ a (x, 0)) ∧
      ∀ y, (g (0, y)).2 = (a : Matrix ι ι R) *ᵥ y := by
  let A : Matrix ι ι R := LinearMap.toMatrix'
    ((LinearMap.fst R _ _).comp (g.toLinearMap.comp (LinearMap.inl R _ _)))
  let D : Matrix ι ι R := LinearMap.toMatrix'
    ((LinearMap.snd R _ _).comp (g.toLinearMap.comp (LinearMap.inr R _ _)))
  have hA (x : ι → R) : g (x, 0) = (A *ᵥ x, 0) :=
    Prod.ext (by simp [A, LinearMap.toMatrix'_mulVec]) (hfirst x)
  have hD (y : ι → R) : (g (0, y)).2 = D *ᵥ y := by simp [D, LinearMap.toMatrix'_mulVec]
  -- Pairing `g (x, 0)` with `g (0, y)` shows that `(σ A)ᵀ` is a left inverse of `D`.
  have hAD : (A.map σ)ᵀ * D = 1 := by
    ext i j
    have h := (LinearMap.mem_isometryGroup_iff.1 hg) (Pi.single i 1, 0) (0, Pi.single j 1)
    simp only [hA, hyperbolic_form_apply, hD] at h
    -- Both sides are the `(i, j)` entries: `∑ₖ σ (A k i) D k j` and `δᵢⱼ`.
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa [mulVec_single_one, Pi.single_apply, apply_ite σ, eq_comm] using h
  have hDA : D * (A.map σ)ᵀ = 1 := mul_eq_one_comm.1 hAD
  let a : GL ι R := ⟨D, (A.map σ)ᵀ, hDA, hAD⟩
  refine ⟨a, fun x ↦ ?_, hD⟩
  -- The action on `L` is the inverse `σ`-transpose of `D`, obtained from `hDA` by applying `σ`.
  have hAinv : (((a⁻¹ : GL ι R) : Matrix ι ι R).map σ)ᵀ = A := by
    have hval : ((a⁻¹ : GL ι R) : Matrix ι ι R) = (A.map σ)ᵀ := by
      simp only [a, Units.inv_mk]
    ext i j
    simp [hval]
  rw [hA, hyperbolicLevi_apply, hAinv, mulVec_zero]

/-- **Levi decomposition** of the Siegel parabolic subgroup in hyperbolic coordinates: an isometry
of the hyperbolic space preserves the first coordinate subspace exactly when it is `n(β) m(a)` for
a `(-ε)`-hermitian `β` and some `a ∈ GL_ι(R)`. -/
theorem exists_eq_hyperbolicRadical_mul_hyperbolicLevi_iff [DecidableEq ι]
    (g : ((ι → R) × (ι → R)) ≃ₗ[R] ((ι → R) × (ι → R))) :
    (∃ β ∈ hyperbolicRadicalParams σ ε ι, ∃ a : GL ι R,
        g = hyperbolicRadical (ofAdd β) * hyperbolicLevi σ a) ↔
      g ∈ (hyperbolic R σ ε ι).form.isometryGroup ∧ ∀ x, (g (x, 0)).2 = 0 := by
  constructor
  · rintro ⟨β, hβ, a, rfl⟩
    refine ⟨Subgroup.mul_mem _ ((hyperbolicRadical_mem_isometryGroup_iff β).2 hβ)
      (hyperbolicLevi_mem_isometryGroup a), fun x ↦ ?_⟩
    simp [mul_apply_eq_comp]
  · rintro ⟨hg, hfirst⟩
    obtain ⟨a, ha₁, ha₂⟩ := exists_hyperbolicLevi_apply_inl_eq g hg hfirst
    have hinv : (((a⁻¹ : GL ι R) : Matrix ι ι R).map σ)ᵀ * ((a : Matrix ι ι R).map σ)ᵀ = 1 := by
      rw [← transpose_mul, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.map_one _ (map_zero σ) (map_one σ), transpose_one]
    -- `g m(a)⁻¹` fixes the first coordinate subspace and acts trivially modulo it.
    obtain ⟨β, hβ, hn⟩ := (exists_eq_hyperbolicRadical_iff (g * (hyperbolicLevi σ a)⁻¹)).2
      ⟨Subgroup.mul_mem _ hg (Subgroup.inv_mem _ (hyperbolicLevi_mem_isometryGroup a)),
        fun x ↦ by
          rw [mul_apply_eq_comp, ← map_inv, hyperbolicLevi_apply, inv_inv, mulVec_zero, ha₁,
            hyperbolicLevi_apply, mulVec_mulVec, hinv, one_mulVec, mulVec_zero],
        fun y ↦ by
          rw [mul_apply_eq_comp, ← map_inv, hyperbolicLevi_apply, mulVec_zero, ha₂, mulVec_mulVec,
            Units.mul_inv, one_mulVec]⟩
    exact ⟨β, hβ, a, by rw [← hn, inv_mul_cancel_right]⟩

/-! ### Radical elements in a complete hyperbolic splitting -/

variable {V : Type*} [AddCommGroup V] [Module R V] {H : SignedHermitianSpace R V σ ε}

namespace IsometryEquiv

/-- The radical elements of the parabolic subgroup of a complete hyperbolic splitting
`e : H^ι ≅ H`, stabilizing the Lagrangian image of the first coordinate subspace: the conjugates
by `e` of the shears `n(β)`, for the `(-ε)`-hermitian matrices `β`. -/
def radical (e : IsometryEquiv (hyperbolic R σ ε ι) H) :
    Multiplicative (hyperbolicRadicalParams σ ε ι) →* H.form.isometryGroup where
  toFun β := e.isometryGroupCongr
    ⟨hyperbolicRadical (ofAdd ((toAdd β : hyperbolicRadicalParams σ ε ι) : Matrix ι ι R)),
      (hyperbolicRadical_mem_isometryGroup_iff _).2 (toAdd β).property⟩
  map_one' := by
    rw [← map_one e.isometryGroupCongr]
    congr 1
    exact Subtype.ext (by simp)
  map_mul' β β' := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext (by simp [← map_mul hyperbolicRadical, ← ofAdd_add])

/-- Conjugating a radical element by the splitting gives back the coordinate shear. -/
@[simp]
theorem coe_isometryGroupCongr_symm_radical (e : IsometryEquiv (hyperbolic R σ ε ι) H)
    (β : Multiplicative (hyperbolicRadicalParams σ ε ι)) :
    ((e.isometryGroupCongr.symm (e.radical β) : (hyperbolic R σ ε ι).form.isometryGroup) :
      ((ι → R) × (ι → R)) ≃ₗ[R] ((ι → R) × (ι → R))) =
      hyperbolicRadical (ofAdd ((toAdd β : hyperbolicRadicalParams σ ε ι) : Matrix ι ι R)) := by
  simp only [radical, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.symm_apply_apply]

/-- The defining conjugation formula for a radical element in a splitting. -/
theorem radical_apply (e : IsometryEquiv (hyperbolic R σ ε ι) H)
    (β : Multiplicative (hyperbolicRadicalParams σ ε ι)) (v : V) :
    (e.radical β : V ≃ₗ[R] V) v =
      e (hyperbolicRadical (ofAdd ((toAdd β : hyperbolicRadicalParams σ ε ι) : Matrix ι ι R))
        (e.symm v)) := by
  rw [← coe_isometryGroupCongr_symm_radical e β, coe_isometryGroupCongr_symm_apply,
    e.apply_symm_apply, e.apply_symm_apply]

/-- In the coordinates of the splitting, a radical element is the coordinate shear. -/
@[simp]
theorem radical_apply_image (e : IsometryEquiv (hyperbolic R σ ε ι) H)
    (β : Multiplicative (hyperbolicRadicalParams σ ε ι)) (x : (ι → R) × (ι → R)) :
    (e.radical β : V ≃ₗ[R] V) (e x) =
      e (hyperbolicRadical (ofAdd ((toAdd β : hyperbolicRadicalParams σ ε ι) : Matrix ι ι R))
        x) := by
  rw [radical_apply, e.symm_apply_apply]

/-- The radical elements of a complete splitting are parametrized faithfully. -/
theorem radical_injective (e : IsometryEquiv (hyperbolic R σ ε ι) H) :
    Function.Injective e.radical := by
  intro β β' h
  have h₀ := congrArg (fun g ↦ ((e.isometryGroupCongr.symm g :
    (hyperbolic R σ ε ι).form.isometryGroup) : ((ι → R) × (ι → R)) ≃ₗ[R] ((ι → R) × (ι → R)))) h
  simp only [coe_isometryGroupCongr_symm_radical] at h₀
  exact toAdd.injective (Subtype.ext (toAdd.symm.injective (hyperbolicRadical_injective h₀)))

variable [DecidableEq ι]

/-- Conjugating the Levi element of `a` by the splitting gives back the coordinate Levi element. -/
@[simp]
theorem coe_isometryGroupCongr_symm_levi (e : IsometryEquiv (hyperbolic R σ ε ι) H)
    (a : GL ι R) :
    ((e.isometryGroupCongr.symm (e.levi a) : (hyperbolic R σ ε ι).form.isometryGroup) :
      ((ι → R) × (ι → R)) ≃ₗ[R] ((ι → R) × (ι → R))) = hyperbolicLevi σ a := by
  ext x <;> simp

/-- The Levi elements of a splitting normalize its radical: `m(a) n(β) m(a)⁻¹ = n(A β a⁻¹)`, where
`A = (σ(a⁻¹))ᵀ`. -/
theorem levi_mul_radical_mul_inv (e : IsometryEquiv (hyperbolic R σ ε ι) H) (a : GL ι R)
    (β : hyperbolicRadicalParams σ ε ι) :
    e.levi a * e.radical (ofAdd β) * (e.levi a)⁻¹ =
      e.radical (ofAdd ⟨(((a⁻¹ : GL ι R) : Matrix ι ι R).map σ)ᵀ * β *
          ((a⁻¹ : GL ι R) : Matrix ι ι R),
        transpose_map_mul_mul_mem_hyperbolicRadicalParams _ β.property⟩) := by
  apply e.isometryGroupCongr.symm.injective
  apply Subtype.ext
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_isometryGroupCongr_symm_levi, coe_isometryGroupCongr_symm_radical, toAdd_ofAdd]
  exact hyperbolicLevi_mul_hyperbolicRadical_mul_inv a β

/-- **Levi decomposition** of the Siegel parabolic subgroup of a complete hyperbolic splitting
`e : H^ι ≅ H`: an isometry `g` of `H` preserves the Lagrangian `e(L)`, the image of the first
coordinate subspace, exactly when it is a radical element times a Levi element of the splitting. -/
theorem exists_eq_radical_mul_levi_iff (e : IsometryEquiv (hyperbolic R σ ε ι) H)
    (g : H.form.isometryGroup) :
    (∃ β a, g = e.radical β * e.levi a) ↔
      ∀ x, (e.symm ((g : V ≃ₗ[R] V) (e (x, 0)))).2 = 0 := by
  constructor
  · rintro ⟨β, a, rfl⟩ x
    simp [mul_apply_eq_comp]
  · intro h
    let g₀ := e.isometryGroupCongr.symm g
    obtain ⟨β, hβ, a, h₀⟩ := (exists_eq_hyperbolicRadical_mul_hyperbolicLevi_iff
      (g₀ : ((ι → R) × (ι → R)) ≃ₗ[R] ((ι → R) × (ι → R)))).2
        ⟨g₀.property, fun x ↦ by simpa [g₀] using h x⟩
    refine ⟨ofAdd ⟨β, hβ⟩, a, e.isometryGroupCongr.symm.injective (Subtype.ext ?_)⟩
    rw [map_mul, Subgroup.coe_mul, coe_isometryGroupCongr_symm_radical,
      coe_isometryGroupCongr_symm_levi]
    exact h₀

/-- The Levi decomposition in a complete hyperbolic splitting is unique. -/
theorem radical_mul_levi_inj (e : IsometryEquiv (hyperbolic R σ ε ι) H)
    {β β' : Multiplicative (hyperbolicRadicalParams σ ε ι)} {a a' : GL ι R} :
    e.radical β * e.levi a = e.radical β' * e.levi a' ↔ β = β' ∧ a = a' := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  have h₀ := congrArg (fun g ↦ ((e.isometryGroupCongr.symm g :
    (hyperbolic R σ ε ι).form.isometryGroup) : ((ι → R) × (ι → R)) ≃ₗ[R] ((ι → R) × (ι → R)))) h
  simp only [map_mul, Subgroup.coe_mul, coe_isometryGroupCongr_symm_levi,
    coe_isometryGroupCongr_symm_radical] at h₀
  obtain ⟨hβ, ha⟩ := hyperbolicRadical_mul_hyperbolicLevi_inj.1 h₀
  exact ⟨toAdd.injective (Subtype.ext hβ), ha⟩

end IsometryEquiv

end TauCeti.SignedHermitianSpace
