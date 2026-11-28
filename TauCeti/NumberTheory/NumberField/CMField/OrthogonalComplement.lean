/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.AdeleStar
public import TauCeti.NumberTheory.NumberField.Global.Adeles.GeneralizedIndex
import TauCeti.LinearAlgebra.Matrix.CokernelIndex
import TauCeti.LinearAlgebra.Matrix.ConjTranspose
import TauCeti.LinearAlgebra.Matrix.Congruence
import TauCeti.LinearAlgebra.Matrix.Determinant.OrthogonalComplement
import TauCeti.LinearAlgebra.Matrix.SubalgebraEntries
import TauCeti.LinearAlgebra.Matrix.Submatrix
import TauCeti.LinearAlgebra.Pi
import TauCeti.NumberTheory.NumberField.CMField.AdelicLattice
import TauCeti.NumberTheory.NumberField.Global.Adeles.Lattice
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.UnimodularFrame

/-!
# Jacobi's identity for an orthogonal complement over the integral finite adeles

Let `E` be a CM field, `𝔸_f` its finite adeles, `Ô` the integral ones, `[·]` the generalised
index and `Mᴴ = (M.map conj)ᵀ` the conjugate transpose for complex conjugation on `𝔸_f`
(`NumberField.IsCMField.finiteAdeleConj`). A matrix over `𝔸_f` is *integral* if its entries lie
in `Ô`. Let `J` be a hermitian `ν × ν` matrix that is integral with an integral inverse, `n` an
integral `ν × β` matrix with an integral left inverse, and `F` an integral `ν × a` matrix with
`Fᴴ J n = 0` and `a + #β = #ν`. If `F` has a left inverse over `𝔸_f` or `[det (Fᴴ J F)] ≠ 0`, then

* every `u` with `nᴴ J u = 0` is `F v` for some `v` over `𝔸_f`
  (`NumberField.IsCMField.exists_eq_mulVec_of_mulVec_eq_zero`);
* `[det (Fᴴ J F)] = [det (nᴴ J n)] · i²`, where `i` is the index of the integral vectors `Ô^a` in
  the `Ô`-module `{y : F y integral}`
  (`NumberField.IsCMField.genIndex_det_eq_genIndex_det_mul_relIndex_sq`).

The proof completes `n` to an element `g` of `GL_ν(Ô)`
(`IsDedekindDomain.FiniteAdeleRing.exists_submatrix_eq_of_mul_eq_one`), so that the columns of
`k = g H_{·, α}`, for `H` the inverse of `G = gᴴ J g`, are an integral basis of the
`J`-orthogonal complement of `n` with integral left inverse `λ = (gᴴ J)_{α, ·}`
(`TauCeti/LinearAlgebra/Matrix/Determinant/OrthogonalComplement.lean`). Then `F = k C`
for the integral square matrix `C = λ F`, and Jacobi's identity
`det (kᴴ J k) = det H * det (nᴴ J n)` with `[det H] = 1` gives
`[det (Fᴴ J F)] = [det C]² [det (nᴴ J n)]`. Finally `{y : F y integral} = C⁻¹ Ô^a`, whose index
over `Ô^a` is `[Ô^a : C Ô^a] = [det C]`
(`Matrix.relIndex_comap_mulVecLin_map_eq_cardQuot`,
`NumberField.FiniteAdeleRing.cardQuot_range_mulVecLin_eq_genIndex_det`).

## Main results

* `NumberField.IsCMField.exists_basis_orthogonalComplement`: for a unimodular `J` and a primitive
  `n`, integral `k` and `L` with `L k = 1`, `nᴴ J k = 0`, whose columns span the `J`-orthogonal
  complement of `n`.
* `NumberField.IsCMField.exists_eq_mulVec_of_mulVec_eq_zero`: the `J`-orthogonal complement of
  `n` is spanned by the columns of `F`.
* `NumberField.IsCMField.genIndex_det_eq_genIndex_det_mul_relIndex_sq`: Jacobi's identity
  `[det (Fᴴ J F)] = [det (nᴴ J n)] · i²`.

## References

The statements follow `New.Filling.jacobi_perp_discriminant` (in the case without an added
block) in the file `src/Lib/General/NumberTheory/LatticeCovolumes.lean` of the folder `grh` of
https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField NumberField.FiniteAdeleRing
open Matrix
open scoped NumberField.AdeleRing

namespace NumberField.IsCMField

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

section Integral

variable {p q : Type*}

/-- The conjugate transpose of an integral matrix is integral. -/
private theorem transpose_map_mem {M : Matrix q p 𝔸ᶠ[E]}
    (hM : ∀ i j, M i j ∈ integralAdeles (𝓞 E) E) (i : p) (j : q) :
    (M.map (finiteAdeleConj E))ᵀ i j ∈ integralAdeles (𝓞 E) E := by
  rw [transpose_apply, Matrix.map_apply, finiteAdeleConj_apply]
  exact star_mem_integralAdeles_iff.2 (hM j i)

end Integral

variable {ν β : Type*} [Fintype ν] [DecidableEq ν] [Fintype β] [DecidableEq β] {a : ℕ}

/-- The common construction behind Jacobi's identity: complete `n` to `g ∈ GL_ν(Ô)`, and take the
basis `k = g H_{·, α}` of the `J`-orthogonal complement of `n`, with left inverse `λ`, and the
factor `c = det H`, where `H` is the inverse of `gᴴ J g`. -/
private theorem exists_basis {J J' : Matrix ν ν 𝔸ᶠ[E]} {n : Matrix ν β 𝔸ᶠ[E]}
    {F : Matrix ν (Fin a) 𝔸ᶠ[E]} (hJ' : J' * J = 1)
    (hn : ∀ i j, n i j ∈ integralAdeles (𝓞 E) E)
    (hl : ∃ l : Matrix β ν 𝔸ᶠ[E], (∀ i j, l i j ∈ integralAdeles (𝓞 E) E) ∧ l * n = 1)
    (hFn : (F.map (finiteAdeleConj E))ᵀ * J * n = 0) (hab : Fintype.card β + a = Fintype.card ν) :
    ∃ (k : Matrix ν (Fin a) 𝔸ᶠ[E]) (L : Matrix (Fin a) ν 𝔸ᶠ[E]) (c : 𝔸ᶠ[E]),
      ((∀ i j, J' i j ∈ integralAdeles (𝓞 E) E) → ∀ i j, k i j ∈ integralAdeles (𝓞 E) E) ∧
      ((∀ i j, J i j ∈ integralAdeles (𝓞 E) E) → ∀ i j, L i j ∈ integralAdeles (𝓞 E) E) ∧
      ((∀ i j, J i j ∈ integralAdeles (𝓞 E) E) → (∀ i j, J' i j ∈ integralAdeles (𝓞 E) E) →
        genIndex E c = 1) ∧
      L * k = 1 ∧ (n.map (finiteAdeleConj E))ᵀ * J * k = 0 ∧
      ((J.map (finiteAdeleConj E))ᵀ = J → F = k * (L * F) ∧
        det ((F.map (finiteAdeleConj E))ᵀ * J * F) =
          finiteAdeleConj E (L * F).det * (L * F).det *
            (c * det ((n.map (finiteAdeleConj E))ᵀ * J * n))) ∧
      ∀ u, ((n.map (finiteAdeleConj E))ᵀ * J) *ᵥ u = 0 → u = k *ᵥ (L *ᵥ u) := by
  obtain ⟨l, hl, hln⟩ := hl
  let e : β ⊕ Fin a ≃ ν := Fintype.equivOfCardEq (by rw [Fintype.card_sum, Fintype.card_fin, hab])
  obtain ⟨g, rfl⟩ :=
    exists_submatrix_eq_of_mul_eq_one (e.injective.comp Sum.inl_injective) hn hl hln
  set G := (integralGL E ν g : Matrix ν ν 𝔸ᶠ[E])
  set Gi := ((integralGL E ν g)⁻¹ : GL ν 𝔸ᶠ[E]).val
  have hG (i j) : G i j ∈ integralAdeles (𝓞 E) E := by
    simp only [G, integralGL_apply, SetLike.coe_mem]
  have hGi (i j) : Gi i j ∈ integralAdeles (𝓞 E) E := by
    simp only [Gi, integralGL_inv_apply, SetLike.coe_mem]
  have hGGi : G * Gi = 1 := (integralGL E ν g).mul_inv
  -- `H = Gi J' Giᴴ` is the inverse of `Gᴴ J G`.
  set H := Gi * J' * (Gi.map (finiteAdeleConj E))ᵀ
  have hH : H * ((G.map (finiteAdeleConj E))ᵀ * J * G) = 1 := by
    have h1 : (Gi.map (finiteAdeleConj E))ᵀ * (G.map (finiteAdeleConj E))ᵀ = 1 := by
      rw [← transpose_map_mul, hGGi, Matrix.map_one _ (map_zero _) (map_one _), transpose_one]
    calc H * ((G.map (finiteAdeleConj E))ᵀ * J * G)
      _ = Gi * J' * ((Gi.map (finiteAdeleConj E))ᵀ * (G.map (finiteAdeleConj E))ᵀ) * J * G := by
        simp only [H, Matrix.mul_assoc]
      _ = 1 := by
        rw [h1, Matrix.mul_one, Matrix.mul_assoc Gi, hJ', Matrix.mul_one, mul_eq_one_comm.1 hGGi]
  refine ⟨G * H.submatrix id (e ∘ Sum.inr),
    ((G.map (finiteAdeleConj E))ᵀ * J).submatrix (e ∘ Sum.inr) id, H.det,
    fun hJ'_int i j ↦ ?_, fun hJ_int i j ↦ ?_, fun hJ_int hJ'_int ↦ ?_,
    submatrix_mul_mul_submatrix_eq_one hH e, transpose_map_submatrix_mul_mul_eq_zero hH e,
    fun hJ ↦ ?_, fun u hu ↦ eq_mulVec_of_mulVec_eq_zero hH e hu⟩
  · exact mul_apply_mem hG
      (fun i j ↦ mul_apply_mem (mul_apply_mem hGi hJ'_int) (transpose_map_mem hGi) _ _) i j
  · exact mul_apply_mem (transpose_map_mem hG) hJ_int _ _
  · exact genIndex_det_eq_one_of_mul_eq_one
      (mul_apply_mem (mul_apply_mem hGi hJ'_int) (transpose_map_mem hGi))
      (mul_apply_mem (mul_apply_mem (transpose_map_mem hG) hJ_int) hG) hH
  -- `nᴴ J F = 0`, the conjugate transpose of `Fᴴ J n = 0` for a hermitian `J`.
  have hnF : ((G.submatrix id (e ∘ Sum.inl)).map (finiteAdeleConj E))ᵀ * J * F = 0 := by
    have h := congrArg (fun M ↦ (M.map (finiteAdeleConj E))ᵀ) hFn
    simpa only [transpose_map_mul, hJ,
      transpose_map_transpose_map (fun x ↦ finiteAdeleConj_finiteAdeleConj x),
      Matrix.map_zero _ (map_zero _), transpose_zero, Matrix.mul_assoc] using h
  refine ⟨by rw [submatrix_id_mul]; exact eq_mul_of_mul_eq_zero hH e hnF, ?_⟩
  conv_lhs => rw [eq_mul_of_mul_eq_zero hH e hnF]
  rw [det_transpose_map_mul_mul_mul,
    det_transpose_map_mul_mul_eq_det_mul_det (fun x ↦ finiteAdeleConj_finiteAdeleConj x) hJ hH e,
    submatrix_id_mul]
  ring

omit [DecidableEq ν] in
/-- If `F = k C` for a square matrix `C`, then `det C` is a unit as soon as `F` has a left
inverse or `[det (Fᴴ J F)] ≠ 0`. -/
private theorem isUnit_det {J : Matrix ν ν 𝔸ᶠ[E]} {F : Matrix ν (Fin a) 𝔸ᶠ[E]}
    {k : Matrix ν (Fin a) 𝔸ᶠ[E]} {C : Matrix (Fin a) (Fin a) 𝔸ᶠ[E]} (hFk : F = k * C)
    (hF : (∃ L : Matrix (Fin a) ν 𝔸ᶠ[E], L * F = 1) ∨
      genIndex E (det ((F.map (finiteAdeleConj E))ᵀ * J * F)) ≠ 0) :
    IsUnit C.det := by
  rcases hF with ⟨L, hL⟩ | h
  · refine IsUnit.of_mul_eq_one_right (L * k).det ?_
    rw [← det_mul, Matrix.mul_assoc, ← hFk, hL, det_one]
  · have h_unit : IsUnit (det ((F.map (finiteAdeleConj E))ᵀ * J * F)) := by
      by_contra hc
      exact h (genIndex_eq_zero_iff.2 hc)
    rw [hFk, det_transpose_map_mul_mul_mul (finiteAdeleConj E) J k C] at h_unit
    exact isUnit_of_mul_isUnit_right h_unit

/-- **An integral basis of the orthogonal complement of a primitive matrix.** Let `J` be a `ν × ν`
matrix over `𝔸_f` with entries in `Ô` and an inverse with entries in `Ô`, and `n` a `ν × β`
matrix with entries in `Ô` and a left inverse with entries in `Ô`, where `Mᴴ = (M.map conj)ᵀ`. For
`#β + a = #ν` there are matrices `k : ν × a` and `L : a × ν` with entries in `Ô` such that
`L k = 1`, `nᴴ J k = 0`, and every `u` with `nᴴ J u = 0` is `k (L u)`. So the columns of `k` span
the `J`-orthogonal complement of `n`, and `u` is integral in it exactly when `L u` is. -/
theorem exists_basis_orthogonalComplement {J : Matrix ν ν 𝔸ᶠ[E]} {n : Matrix ν β 𝔸ᶠ[E]}
    (hJ_int : ∀ i j, J i j ∈ integralAdeles (𝓞 E) E)
    (hJ' : ∃ J' : Matrix ν ν 𝔸ᶠ[E], (∀ i j, J' i j ∈ integralAdeles (𝓞 E) E) ∧ J' * J = 1)
    (hn : ∀ i j, n i j ∈ integralAdeles (𝓞 E) E)
    (hl : ∃ l : Matrix β ν 𝔸ᶠ[E], (∀ i j, l i j ∈ integralAdeles (𝓞 E) E) ∧ l * n = 1)
    (hab : Fintype.card β + a = Fintype.card ν) :
    ∃ (k : Matrix ν (Fin a) 𝔸ᶠ[E]) (L : Matrix (Fin a) ν 𝔸ᶠ[E]),
      (∀ i j, k i j ∈ integralAdeles (𝓞 E) E) ∧ (∀ i j, L i j ∈ integralAdeles (𝓞 E) E) ∧
      L * k = 1 ∧ (n.map (finiteAdeleConj E))ᵀ * J * k = 0 ∧
      ∀ u, ((n.map (finiteAdeleConj E))ᵀ * J) *ᵥ u = 0 → u = k *ᵥ (L *ᵥ u) := by
  obtain ⟨J', hJ'_int, hJ'⟩ := hJ'
  obtain ⟨k, L, -, hk, hL, -, hLk, hnk, -, h_span⟩ :=
    exists_basis (F := (0 : Matrix ν (Fin a) 𝔸ᶠ[E])) hJ' hn hl (by simp) hab
  exact ⟨k, L, hk hJ'_int, hL hJ_int, hLk, hnk, h_span⟩

/-- **The orthogonal complement of a primitive matrix.** Let `J` be an invertible hermitian
`ν × ν` matrix over the finite adeles `𝔸_f` of a CM field, `n` a `ν × β` matrix with entries in
`Ô` and a left inverse with entries in `Ô`, and `F` a `ν × a` matrix with `Fᴴ J n = 0` and
`#β + a = #ν`, where `Mᴴ = (M.map conj)ᵀ`. If `F` has a left inverse or `[det (Fᴴ J F)] ≠ 0`, then
every `u` with `nᴴ J u = 0` is `F v` for some `v`. -/
theorem exists_eq_mulVec_of_mulVec_eq_zero {J : Matrix ν ν 𝔸ᶠ[E]} {n : Matrix ν β 𝔸ᶠ[E]}
    {F : Matrix ν (Fin a) 𝔸ᶠ[E]} (hJ : (J.map (finiteAdeleConj E))ᵀ = J) (hJ_unit : IsUnit J.det)
    (hn : ∀ i j, n i j ∈ integralAdeles (𝓞 E) E)
    (hl : ∃ l : Matrix β ν 𝔸ᶠ[E], (∀ i j, l i j ∈ integralAdeles (𝓞 E) E) ∧ l * n = 1)
    (hFn : (F.map (finiteAdeleConj E))ᵀ * J * n = 0) (hab : Fintype.card β + a = Fintype.card ν)
    (hF : (∃ L : Matrix (Fin a) ν 𝔸ᶠ[E], L * F = 1) ∨
      genIndex E (det ((F.map (finiteAdeleConj E))ᵀ * J * F)) ≠ 0)
    {u : ν → 𝔸ᶠ[E]} (hu : ((n.map (finiteAdeleConj E))ᵀ * J) *ᵥ u = 0) : ∃ v, u = F *ᵥ v := by
  obtain ⟨k, L, c, -, -, -, -, -, hF_det, h_span⟩ :=
    exists_basis (nonsing_inv_mul J hJ_unit) hn hl hFn hab
  obtain ⟨hFk, -⟩ := hF_det hJ
  have hC := isUnit_det hFk hF
  have hk : k = F * (L * F)⁻¹ := by
    calc k
      _ = k * ((L * F) * (L * F)⁻¹) := by rw [mul_nonsing_inv _ hC, Matrix.mul_one]
      _ = F * (L * F)⁻¹ := by rw [← Matrix.mul_assoc, ← hFk]
  refine ⟨(L * F)⁻¹ *ᵥ (L *ᵥ u), ?_⟩
  rw [mulVec_mulVec, mulVec_mulVec, ← hk, ← mulVec_mulVec]
  exact h_span u hu

/-- **Jacobi's identity for the orthogonal complement over `Ô`.** Let `J` be a hermitian `ν × ν`
matrix over the finite adeles `𝔸_f` of a CM field, with entries in `Ô` and an inverse with
entries in `Ô`; let `n` be a `ν × β` matrix with entries in `Ô` and a left inverse with entries in
`Ô`, and `F` a `ν × a` matrix with entries in `Ô`, with `Fᴴ J n = 0` and `#β + a = #ν`, where
`Mᴴ = (M.map conj)ᵀ`. If `F` has a left inverse or `[det (Fᴴ J F)] ≠ 0`, then
`[det (Fᴴ J F)] = [det (nᴴ J n)] · i²`, where `i` is the index of the integral vectors `Ô^a` in
`{y : F y ∈ Ô^ν}`. -/
theorem genIndex_det_eq_genIndex_det_mul_relIndex_sq {J : Matrix ν ν 𝔸ᶠ[E]}
    {n : Matrix ν β 𝔸ᶠ[E]} {F : Matrix ν (Fin a) 𝔸ᶠ[E]} (hJ : (J.map (finiteAdeleConj E))ᵀ = J)
    (hJ_int : ∀ i j, J i j ∈ integralAdeles (𝓞 E) E)
    (hJ' : ∃ J' : Matrix ν ν 𝔸ᶠ[E], (∀ i j, J' i j ∈ integralAdeles (𝓞 E) E) ∧ J' * J = 1)
    (hn : ∀ i j, n i j ∈ integralAdeles (𝓞 E) E)
    (hl : ∃ l : Matrix β ν 𝔸ᶠ[E], (∀ i j, l i j ∈ integralAdeles (𝓞 E) E) ∧ l * n = 1)
    (hF_int : ∀ i j, F i j ∈ integralAdeles (𝓞 E) E)
    (hFn : (F.map (finiteAdeleConj E))ᵀ * J * n = 0) (hab : Fintype.card β + a = Fintype.card ν)
    (hF : (∃ L : Matrix (Fin a) ν 𝔸ᶠ[E], L * F = 1) ∨
      genIndex E (det ((F.map (finiteAdeleConj E))ᵀ * J * F)) ≠ 0) :
    genIndex E (det ((F.map (finiteAdeleConj E))ᵀ * J * F)) =
      genIndex E (det ((n.map (finiteAdeleConj E))ᵀ * J * n)) *
        ((LinearMap.range ((Algebra.linearMap (integralAdeles (𝓞 E) E) 𝔸ᶠ[E]).compLeft
          (Fin a))).toAddSubgroup.relIndex
          ((LinearMap.range ((Algebra.linearMap (integralAdeles (𝓞 E) E) 𝔸ᶠ[E]).compLeft ν)).comap
            (F.mulVecLin.restrictScalars (integralAdeles (𝓞 E) E))).toAddSubgroup : ℚ) ^ 2 := by
  obtain ⟨J', hJ'_int, hJ'⟩ := hJ'
  obtain ⟨k, L, c, hk, hL, hc, -, -, hF_det, -⟩ := exists_basis hJ' hn hl hFn hab
  obtain ⟨hFk, h_det⟩ := hF_det hJ
  have hC := isUnit_det hFk hF
  -- `L F` is the image of a matrix `C` over `Ô`, and `{y : F y integral} = {y : C y integral}`.
  obtain ⟨C, hC_eq⟩ := Subalgebra.exists_map_algebraMap_eq (mul_apply_mem (hL hJ_int) hF_int)
  have h_Y : (LinearMap.range ((Algebra.linearMap (integralAdeles (𝓞 E) E) 𝔸ᶠ[E]).compLeft ν)).comap
      (F.mulVecLin.restrictScalars (integralAdeles (𝓞 E) E)) =
      (LinearMap.range ((Algebra.linearMap (integralAdeles (𝓞 E) E) 𝔸ᶠ[E]).compLeft
        (Fin a))).comap ((L * F).mulVecLin.restrictScalars (integralAdeles (𝓞 E) E)) := by
    ext y
    simp only [Submodule.mem_comap, LinearMap.restrictScalars_apply, mulVecLin_apply,
      Subalgebra.mem_range_compLeft_algebraLinearMap_iff]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rw [← mulVec_mulVec]
      exact mulVec_apply_mem (hL hJ_int) h
    · rw [hFk, ← mulVec_mulVec]
      exact mulVec_apply_mem (hk hJ'_int) h
  rw [h_Y, ← hC_eq, relIndex_comap_mulVecLin_map_eq_cardQuot Subtype.val_injective (hC_eq ▸ hC),
    cardQuot_range_mulVecLin_eq_genIndex_det, hC_eq, h_det,
    map_mul, map_mul, map_mul, finiteAdeleConj_apply, genIndex_star, hc hJ_int hJ'_int]
  ring

end NumberField.IsCMField
