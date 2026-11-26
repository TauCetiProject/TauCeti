/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.Analysis.Complex.Basic
public import TauCeti.LinearAlgebra.Matrix.DetDescent
import TauCeti.LinearAlgebra.Matrix.Nonsingular.Inverse

/-!
# Real matrices as complex matrices

A real matrix `N` is viewed as a complex matrix through the entrywise coercion
`N.map ((↑) : ℝ → ℂ)`, and more generally an `RCLike 𝕜` matrix embeds into `Matrix n n ℂ` via
`TauCeti.mapToComplexStarAlgHom`. This file records that a real orthogonal matrix is unitary, a
real symmetric matrix Hermitian and a real positive definite matrix positive definite as a complex
matrix, that `TauCeti.mapToComplexStarAlgHom` is injective, continuous, and preserves and reflects
positive semidefiniteness and positive definiteness, that the determinant does not change, and how
the real Gram matrix `Re (Mᴴ M)` of the columns of a complex matrix `M` behaves: it transforms by
congruence under a real change of basis, and it is positive definite when `Mᴴ M` is, in particular
when `M` has independent columns. The imaginary part `Im (Mᴴ M)`, the matrix of the symplectic form
`Im ⟪·, ·⟫` on the columns, transforms by the same congruence. For a symmetric complex matrix `Ω`,
the imaginary part is `Im Ω = (Ω - Ωᴴ) / 2i`.

## Main results

* `Matrix.map_ofReal_mul_transpose_map_ofReal_eq_one`: an orthogonal real matrix `O` satisfies
  `O Oᵀ = 1` as a complex matrix.
* `Matrix.map_ofReal_mem_unitaryGroup`: an orthogonal real matrix is unitary.
* `Matrix.IsHermitian.map_ofReal`: a real symmetric matrix is Hermitian.
* `Matrix.map_im_map_ofReal_of_transpose_eq`: for a symmetric complex matrix `Ω`, the complex
  matrix of `Im Ω` is `(Ω - Ωᴴ) / 2i`.
* `Matrix.map_ofReal_mul`, `Matrix.map_ofReal_one`, `Matrix.trace_map_ofReal`: the entrywise
  coercion is multiplicative, preserves the identity and commutes with the trace.
* `Matrix.isUnit_map_ofReal_iff`: a real matrix is invertible exactly when it is invertible as a
  complex matrix.
* `Matrix.det_map_ofReal`: the determinant of a real matrix is unchanged as a complex matrix.
* `Matrix.map_re_conjTranspose_mul_self_mul_map_ofReal`: the real Gram matrix of `M N` for a real
  matrix `N` is `Nᵀ Re (Mᴴ M) N`.
* `Matrix.map_im_conjTranspose_mul_self_mul_map_ofReal`: likewise, the imaginary part of the Gram
  matrix of `M N` is `Nᵀ Im (Mᴴ M) N`.
* `Matrix.PosDef.map_re`: the real part of a positive definite complex matrix is positive
  definite.
* `Matrix.PosDef.map_ofReal`: a real positive definite matrix is positive definite as a complex
  matrix.
* `Matrix.PosDef.map_re_conjTranspose_mul_self`: the real Gram matrix of a complex matrix with
  independent columns is positive definite.
* `TauCeti.mapToComplexStarAlgHom`, `TauCeti.posSemidef_mapToComplexStarAlgHom_iff`,
  `TauCeti.posDef_mapToComplexStarAlgHom_iff`: entrywise embedding of `Matrix n n 𝕜` into
  `Matrix n n ℂ`, preserving and reflecting positivity.
-/

public section

open scoped ComplexOrder

namespace TauCeti

section Complexification

open Matrix

variable {n 𝕜 : Type*} [RCLike 𝕜]

/-- The canonical complex embedding `TauCeti.toComplexStarAlgHom 𝕜` is injective. -/
theorem toComplexStarAlgHom_injective : Function.Injective (toComplexStarAlgHom 𝕜) :=
  (isometry_toComplexStarAlgHom 𝕜).injective

/-- An `RCLike` scalar is nonnegative iff its complex image under `toComplexStarAlgHom` is
nonnegative. -/
theorem toComplexStarAlgHom_nonneg_iff {x : 𝕜} :
    0 ≤ toComplexStarAlgHom 𝕜 x ↔ 0 ≤ x := by
  rw [Complex.nonneg_iff, RCLike.nonneg_iff (K := 𝕜)]
  simp only [toComplexStarAlgHom_apply, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, mul_zero, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
    Complex.ofReal_im, Complex.mul_im, zero_add]
  exact ⟨fun ⟨h1, h2⟩ ↦ ⟨h1, h2.symm⟩, fun ⟨h1, h2⟩ ↦ ⟨h1, h2.symm⟩⟩

/-- An `RCLike` scalar is positive iff its complex image under `toComplexStarAlgHom` is
positive. -/
theorem toComplexStarAlgHom_pos_iff {x : 𝕜} :
    0 < toComplexStarAlgHom 𝕜 x ↔ 0 < x := by
  rw [lt_iff_le_and_ne, lt_iff_le_and_ne, toComplexStarAlgHom_nonneg_iff]
  refine and_congr_right fun _ ↦ ?_
  rw [ne_eq, ne_eq, eq_comm (a := (0 : ℂ)), eq_comm (a := (0 : 𝕜)),
    ← map_zero (toComplexStarAlgHom 𝕜), toComplexStarAlgHom_injective.eq_iff]

/-- The canonical entrywise embedding `Matrix n n 𝕜 →⋆ₐ[ℝ] Matrix n n ℂ` lifted from
`TauCeti.toComplexStarAlgHom 𝕜`. -/
@[expose] noncomputable def mapToComplexStarAlgHom [Fintype n] [DecidableEq n] :
    Matrix n n 𝕜 →⋆ₐ[ℝ] Matrix n n ℂ :=
  { (toComplexStarAlgHom 𝕜).toAlgHom.mapMatrix with
    map_star' := fun A ↦ by
      ext i j
      simp [Matrix.star_eq_conjTranspose] }

/-- Evaluating `TauCeti.mapToComplexStarAlgHom` entrywise applies `toComplexStarAlgHom 𝕜`. -/
@[simp]
theorem mapToComplexStarAlgHom_apply [Fintype n] [DecidableEq n] (A : Matrix n n 𝕜) (i j : n) :
    mapToComplexStarAlgHom A i j = toComplexStarAlgHom 𝕜 (A i j) :=
  rfl

/-- The entrywise complex embedding `TauCeti.mapToComplexStarAlgHom` is continuous. -/
@[continuity, fun_prop]
theorem continuous_mapToComplexStarAlgHom [Fintype n] [DecidableEq n] :
    Continuous (mapToComplexStarAlgHom (n := n) (𝕜 := 𝕜)) :=
  continuous_id.matrix_map (continuous_toComplexStarAlgHom 𝕜)

/-- The entrywise complex embedding `TauCeti.mapToComplexStarAlgHom` is injective. -/
theorem mapToComplexStarAlgHom_injective [Fintype n] [DecidableEq n] :
    Function.Injective (mapToComplexStarAlgHom (n := n) (𝕜 := 𝕜)) := fun _ _ h ↦
  Matrix.ext fun i j ↦ toComplexStarAlgHom_injective <| by
    simpa [mapToComplexStarAlgHom_apply] using congrFun (congrFun h i) j

/-- A matrix over an `RCLike` field is Hermitian iff its entrywise complexification is Hermitian. -/
@[simp]
theorem isHermitian_mapToComplexStarAlgHom_iff [Fintype n] [DecidableEq n]
    {A : Matrix n n 𝕜} :
    (mapToComplexStarAlgHom A).IsHermitian ↔ A.IsHermitian := by
  refine ⟨fun h ↦ mapToComplexStarAlgHom_injective ?_, fun h ↦ ?_⟩
  · rw [Matrix.IsHermitian, ← Matrix.star_eq_conjTranspose, ← map_star,
      Matrix.star_eq_conjTranspose] at h
    exact h
  · rw [Matrix.IsHermitian, ← Matrix.star_eq_conjTranspose, ← map_star,
      Matrix.star_eq_conjTranspose, h.eq]

/-- Helper for `posSemidef_mapToComplexStarAlgHom_iff` and `posDef_mapToComplexStarAlgHom_iff`:
quadratic form compatibility under `mapToComplexStarAlgHom`. -/
private theorem toComplexStarAlgHom_dotProduct_mulVec [Fintype n] [DecidableEq n]
    (A : Matrix n n 𝕜) (x : n → 𝕜) :
    toComplexStarAlgHom 𝕜 (star x ⬝ᵥ (A *ᵥ x)) =
      star (toComplexStarAlgHom 𝕜 ∘ x) ⬝ᵥ
        ((mapToComplexStarAlgHom A) *ᵥ (toComplexStarAlgHom 𝕜 ∘ x)) := by
  let φ : 𝕜 →+* ℂ := (toComplexStarAlgHom 𝕜).toRingHom
  have hφ : ∀ c, φ c = toComplexStarAlgHom 𝕜 c := fun _ ↦ rfl
  have hmap : mapToComplexStarAlgHom A = A.map φ := by
    ext i j; simp [mapToComplexStarAlgHom_apply, hφ]
  have hstar_vec : φ ∘ star x = star (toComplexStarAlgHom 𝕜 ∘ x) :=
    funext fun i ↦ by simp [hφ]
  have hmul : (toComplexStarAlgHom 𝕜 ∘ x) = φ ∘ x := rfl
  have hmv : φ ∘ (A *ᵥ x) = (mapToComplexStarAlgHom A) *ᵥ (toComplexStarAlgHom 𝕜 ∘ x) := by
    ext i
    rw [Function.comp_apply, RingHom.map_mulVec, hmap, hmul]
  rw [← hφ, RingHom.map_dotProduct, hstar_vec, hmv]

/-- Helper for `posSemidef_mapToComplexStarAlgHom_iff` and `posDef_mapToComplexStarAlgHom_iff`:
for any Hermitian matrix `A` over `𝕜` and complex vector `z : n → ℂ`, the quadratic form of
`mapToComplexStarAlgHom A` at `z` equals the complexified sum of two real/𝕜 quadratic forms
of `A` at vectors `u, v : n → 𝕜` which cannot both vanish when `z ≠ 0`. -/
private theorem exists_quad_eq_of_isHermitian [Fintype n] [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (z : n → ℂ) :
    ∃ u v : n → 𝕜,
      star z ⬝ᵥ ((mapToComplexStarAlgHom A) *ᵥ z) =
        toComplexStarAlgHom 𝕜 (star u ⬝ᵥ (A *ᵥ u) + star v ⬝ᵥ (A *ᵥ v)) ∧
      (z ≠ 0 → u ≠ 0 ∨ v ≠ 0) := by
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with hI | hI
  · have him_zero (c : 𝕜) : RCLike.im c = 0 := by
      have h := congrArg RCLike.im (RCLike.re_add_im c)
      simpa [hI] using h.symm
    have hre_herm (i j : n) : A j i = A i j := by
      have hij := hA.apply i j
      have hstar (c : 𝕜) : star c = c := by
        rw [RCLike.star_def, RCLike.conj_eq_re_sub_im]
        simpa [him_zero c] using RCLike.re_add_im c
      simpa [hstar] using hij
    let u : n → 𝕜 := fun i ↦ algebraMap ℝ 𝕜 (z i).re
    let v : n → 𝕜 := fun i ↦ algebraMap ℝ 𝕜 (z i).im
    have hz (i : n) :
        z i = toComplexStarAlgHom 𝕜 (u i) + Complex.I * toComplexStarAlgHom 𝕜 (v i) := by
      simp [u, v, toComplexStarAlgHom_apply, Complex.ext_iff]
    have hcross :
        (toComplexStarAlgHom 𝕜 ∘ u) ⬝ᵥ
            ((mapToComplexStarAlgHom A) *ᵥ (toComplexStarAlgHom 𝕜 ∘ v)) =
          (toComplexStarAlgHom 𝕜 ∘ v) ⬝ᵥ
            ((mapToComplexStarAlgHom A) *ᵥ (toComplexStarAlgHom 𝕜 ∘ u)) := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Function.comp_apply,
        mapToComplexStarAlgHom_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hre_herm i j]
      ring
    have hreal (x : n → 𝕜) : star (toComplexStarAlgHom 𝕜 ∘ x) = toComplexStarAlgHom 𝕜 ∘ x := by
      ext i
      simp [him_zero (x i)]
    have hsplit : z = (toComplexStarAlgHom 𝕜 ∘ u) + Complex.I • (toComplexStarAlgHom 𝕜 ∘ v) := by
      ext i
      simp [hz i, smul_eq_mul]
    have hst :
        star z = (toComplexStarAlgHom 𝕜 ∘ u) - Complex.I • (toComplexStarAlgHom 𝕜 ∘ v) := by
      ext i
      simp [hsplit, Complex.ext_iff, him_zero (u i), him_zero (v i)]
    refine ⟨u, v, ?_, fun hzne ↦ ?_⟩
    · rw [hst, hsplit, Matrix.mulVec_add, Matrix.mulVec_smul, sub_dotProduct,
        dotProduct_add, dotProduct_add, dotProduct_smul, smul_dotProduct, smul_dotProduct,
        dotProduct_smul, hcross]
      simp only [map_add, toComplexStarAlgHom_dotProduct_mulVec, hreal, smul_eq_mul]
      ring_nf
      rw [Complex.I_sq]
      ring
    · by_contra hboth
      push Not at hboth
      exact hzne <| funext fun i ↦ by
        simp [hz i, congrFun hboth.1 i, congrFun hboth.2 i]
  · have hreI : RCLike.re (RCLike.I : 𝕜) = 0 := by
      have h := congrArg RCLike.re (RCLike.re_add_im (RCLike.I : 𝕜))
      rw [map_add, RCLike.ofReal_re, hI, RCLike.ofReal_one, one_mul] at h
      linarith
    let u : n → 𝕜 := fun i ↦ algebraMap ℝ 𝕜 (z i).re + algebraMap ℝ 𝕜 (z i).im * RCLike.I
    have hu : toComplexStarAlgHom 𝕜 ∘ u = z := by
      ext i
      simp [u, toComplexStarAlgHom_apply, hI, hreI]
    refine ⟨u, 0, ?_, fun hzne ↦ Or.inl fun h0 ↦ hzne (by simp [← hu, h0])⟩
    rw [← hu, ← toComplexStarAlgHom_dotProduct_mulVec]
    simp

/-- A finite matrix over an `RCLike` field is positive semidefinite iff its entrywise
complexification is positive semidefinite. -/
@[simp]
theorem posSemidef_mapToComplexStarAlgHom_iff [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜} :
    (mapToComplexStarAlgHom A).PosSemidef ↔ A.PosSemidef := by
  constructor
  · intro hC
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (isHermitian_mapToComplexStarAlgHom_iff.1 hC.isHermitian) fun x ↦ ?_
    rw [← toComplexStarAlgHom_nonneg_iff, toComplexStarAlgHom_dotProduct_mulVec]
    exact hC.dotProduct_mulVec_nonneg (toComplexStarAlgHom 𝕜 ∘ x)
  · intro hA
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (isHermitian_mapToComplexStarAlgHom_iff.2 hA.isHermitian) fun z ↦ ?_
    obtain ⟨u, v, hdecomp, -⟩ := exists_quad_eq_of_isHermitian hA.isHermitian z
    rw [hdecomp, toComplexStarAlgHom_nonneg_iff]
    exact add_nonneg (hA.dotProduct_mulVec_nonneg u) (hA.dotProduct_mulVec_nonneg v)

/-- A finite matrix over an `RCLike` field is positive definite iff its entrywise
complexification is positive definite. -/
@[simp]
theorem posDef_mapToComplexStarAlgHom_iff [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜} :
    (mapToComplexStarAlgHom A).PosDef ↔ A.PosDef := by
  constructor
  · intro hC
    refine Matrix.PosDef.of_dotProduct_mulVec_pos
      (isHermitian_mapToComplexStarAlgHom_iff.1 hC.isHermitian) fun x hx ↦ ?_
    have hφx : toComplexStarAlgHom 𝕜 ∘ x ≠ 0 := fun h0 ↦
      hx (funext fun i ↦ toComplexStarAlgHom_injective <| by simpa using congrFun h0 i)
    rw [← toComplexStarAlgHom_pos_iff, toComplexStarAlgHom_dotProduct_mulVec]
    exact hC.dotProduct_mulVec_pos hφx
  · intro hA
    refine Matrix.PosDef.of_dotProduct_mulVec_pos
      (isHermitian_mapToComplexStarAlgHom_iff.2 hA.isHermitian) fun z hz ↦ ?_
    obtain ⟨u, v, hdecomp, hnz⟩ := exists_quad_eq_of_isHermitian hA.isHermitian z
    rw [hdecomp, toComplexStarAlgHom_pos_iff]
    rcases hnz hz with hu | hv
    · exact add_pos_of_pos_of_nonneg (hA.dotProduct_mulVec_pos hu)
        (hA.posSemidef.dotProduct_mulVec_nonneg v)
    · exact add_pos_of_nonneg_of_pos (hA.posSemidef.dotProduct_mulVec_nonneg u)
        (hA.dotProduct_mulVec_pos hv)

end Complexification

end TauCeti

namespace Matrix

variable {l m n : Type*}

/-- Entrywise complexification preserves positive semidefiniteness. -/
theorem PosSemidef.mapToComplexStarAlgHom {𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    (TauCeti.mapToComplexStarAlgHom A).PosSemidef :=
  TauCeti.posSemidef_mapToComplexStarAlgHom_iff.2 hA

/-- Entrywise complexification preserves positive definiteness. -/
theorem PosDef.mapToComplexStarAlgHom {𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.PosDef) :
    (TauCeti.mapToComplexStarAlgHom A).PosDef :=
  TauCeti.posDef_mapToComplexStarAlgHom_iff.2 hA

/-- The complex image `O` of an orthogonal real matrix `O` satisfies `O Oᵀ = 1`. -/
theorem map_ofReal_mul_transpose_map_ofReal_eq_one [Fintype n] [DecidableEq n] {O : Matrix n n ℝ}
    (hO : O ∈ orthogonalGroup n ℝ) : O.map ((↑) : ℝ → ℂ) * (O.map ((↑) : ℝ → ℂ))ᵀ = 1 := by
  rw [← transpose_map]
  -- `N.map (↑)` is `Complex.ofRealHom.mapMatrix N`, which is multiplicative.
  exact (map_mul Complex.ofRealHom.mapMatrix _ _).symm.trans
    ((congrArg _ ((mem_orthogonalGroup_iff _ _).1 hO)).trans (map_one _))

/-- An orthogonal real matrix is unitary as a complex matrix. -/
theorem map_ofReal_mem_unitaryGroup [Fintype n] [DecidableEq n] {O : Matrix n n ℝ}
    (hO : O ∈ orthogonalGroup n ℝ) : O.map ((↑) : ℝ → ℂ) ∈ unitaryGroup n ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose,
    ← conjTranspose_map _ fun _ ↦ (Complex.conj_ofReal _).symm,
    conjTranspose_eq_transpose_of_trivial, transpose_map]
  exact map_ofReal_mul_transpose_map_ofReal_eq_one hO

/-- A real symmetric matrix is Hermitian as a complex matrix. -/
theorem IsHermitian.map_ofReal {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (A.map ((↑) : ℝ → ℂ)).IsHermitian :=
  hA.map _ fun _ ↦ by simp

/-- For a symmetric complex matrix `Ω`, the complex matrix of `Im Ω` is `(Ω - Ωᴴ) / 2i`. -/
theorem map_im_map_ofReal_of_transpose_eq {Ω : Matrix n n ℂ} (h : Ωᵀ = Ω) :
    (Ω.map Complex.im).map ((↑) : ℝ → ℂ) = (2 * Complex.I)⁻¹ • (Ω - Ωᴴ) := by
  ext i j
  have hij : Ω j i = Ω i j := by simpa using congrFun (congrFun h i) j
  simp [hij, Complex.ext_iff, Complex.sub_conj]

/-- The entrywise coercion of real matrices to complex matrices is multiplicative. -/
@[simp]
theorem map_ofReal_mul [Fintype m] (X : Matrix l m ℝ) (Y : Matrix m n ℝ) :
    (X * Y).map ((↑) : ℝ → ℂ) = X.map (↑) * Y.map (↑) :=
  Matrix.map_mul (f := Complex.ofRealHom)

/-- The entrywise coercion of the real identity matrix is the complex identity matrix. -/
theorem map_ofReal_one [DecidableEq n] : (1 : Matrix n n ℝ).map ((↑) : ℝ → ℂ) = 1 :=
  Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one

/-- The trace of a real matrix, viewed as a complex matrix, is the coercion of its trace. -/
@[simp]
theorem trace_map_ofReal [Fintype n] (X : Matrix n n ℝ) :
    trace (X.map ((↑) : ℝ → ℂ)) = ((trace X : ℝ) : ℂ) :=
  (AddMonoidHom.map_trace Complex.ofRealHom X).symm

/-- A real square matrix is invertible exactly when it is invertible as a complex matrix: the
case `ℝ → ℂ` of `Matrix.isUnit_map_iff`. -/
@[simp]
theorem isUnit_map_ofReal_iff [Fintype n] [DecidableEq n] {M : Matrix n n ℝ} :
    IsUnit (M.map ((↑) : ℝ → ℂ)) ↔ IsUnit M :=
  isUnit_map_iff Complex.ofRealHom M

/-- The determinant of the complex image of a real matrix is the image of its determinant. -/
@[simp]
theorem det_map_ofReal [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) :
    (M.map ((↑) : ℝ → ℂ)).det = M.det :=
  (Complex.ofRealHom.map_det M).symm

/-- The real Gram matrix `Re ((M N)ᴴ (M N))` of the columns of `M N`, for a real matrix `N`, is
`Nᵀ Re (Mᴴ M) N`. -/
theorem map_re_conjTranspose_mul_self_mul_map_ofReal [Fintype m] [Fintype n] (M : Matrix m n ℂ)
    (N : Matrix n l ℝ) :
    ((M * N.map ((↑) : ℝ → ℂ))ᴴ * (M * N.map ((↑) : ℝ → ℂ))).map Complex.re =
      Nᵀ * (Mᴴ * M).map Complex.re * N := by
  rw [conjTranspose_mul, ← conjTranspose_map _ fun _ ↦ (Complex.conj_ofReal _).symm,
    conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ]
  exact ((map_algebraMap_mul Complex.reLm Nᵀ _).trans
    (congrArg (Nᵀ * ·) (map_mul_algebraMap Complex.reLm N (Mᴴ * M)))).trans
      (Matrix.mul_assoc _ _ _).symm

/-- The imaginary part `Im ((M N)ᴴ (M N))` of the Gram matrix of the columns of `M N`, for a real
matrix `N`, is `Nᵀ Im (Mᴴ M) N`. -/
theorem map_im_conjTranspose_mul_self_mul_map_ofReal [Fintype m] [Fintype n] (M : Matrix m n ℂ)
    (N : Matrix n l ℝ) :
    ((M * N.map ((↑) : ℝ → ℂ))ᴴ * (M * N.map ((↑) : ℝ → ℂ))).map Complex.im =
      Nᵀ * (Mᴴ * M).map Complex.im * N := by
  rw [conjTranspose_mul, ← conjTranspose_map _ fun _ ↦ (Complex.conj_ofReal _).symm,
    conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ]
  exact ((map_algebraMap_mul Complex.imLm Nᵀ _).trans
    (congrArg (Nᵀ * ·) (map_mul_algebraMap Complex.imLm N (Mᴴ * M)))).trans
      (Matrix.mul_assoc _ _ _).symm

/-- The real part of a positive definite complex matrix is positive definite. -/
theorem PosDef.map_re [Finite n] {K : Matrix n n ℂ} (hK : K.PosDef) :
    (K.map Complex.re).PosDef := by
  have := Fintype.ofFinite n
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx ↦ ?_
  · ext i j
    have := congrFun (congrFun hK.1 i) j
    simp only [conjTranspose_apply, RCLike.star_def] at this
    simp only [conjTranspose_apply, map_apply, star_trivial, ← this, Complex.conj_re]
  · set xc : n → ℂ := fun i ↦ (x i : ℂ)
    have hxc : xc ≠ 0 := fun h ↦ hx (funext fun i ↦ by simpa [xc] using congrFun h i)
    have hre : (star xc ⬝ᵥ (K *ᵥ xc)).re = star x ⬝ᵥ (K.map Complex.re *ᵥ x) := by
      simp [xc, dotProduct, mulVec, Complex.re_sum, Finset.mul_sum]
    rw [← hre]
    exact (Complex.pos_iff.1 (hK.dotProduct_mulVec_pos hxc)).1

/-- A real positive definite matrix is positive definite as a complex matrix: for `x = a + i b`,
`x* Y x = aᵀ Y a + bᵀ Y b`. -/
theorem PosDef.map_ofReal [Finite n] {Y : Matrix n n ℝ} (hY : Y.PosDef) :
    (Y.map ((↑) : ℝ → ℂ)).PosDef := by
  classical
  have := Fintype.ofFinite n
  refine PosDef.of_dotProduct_mulVec_pos hY.isHermitian.map_ofReal fun x hx ↦ ?_
  set a : n → ℝ := fun i ↦ (x i).re
  set b : n → ℝ := fun i ↦ (x i).im
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra! h
    exact hx (funext fun i ↦ Complex.ext (by simpa [a] using congrFun h.1 i)
      (by simpa [b] using congrFun h.2 i))
  have hsymm : ∀ i j, Y i j = Y j i := fun i j ↦ by
    simpa using congrFun (congrFun hY.isHermitian.eq j) i
  -- the cross terms cancel by symmetry of `Y`
  have hcross : ∑ i, ∑ j, (a i * Y i j * b j - b i * Y i j * a j) = 0 := by
    simp only [Finset.sum_sub_distrib]
    rw [sub_eq_zero, Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
      rw [hsymm i j]; ring
  have key : star x ⬝ᵥ (Y.map ((↑) : ℝ → ℂ) *ᵥ x) =
      ((a ⬝ᵥ (Y *ᵥ a) + b ⬝ᵥ (Y *ᵥ b) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, map_apply, Complex.re_sum,
        Complex.ofReal_re, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      simp [a, b, Complex.mul_re, Complex.mul_im]
    · have : (star x ⬝ᵥ (Y.map ((↑) : ℝ → ℂ) *ᵥ x)).im =
          ∑ i, ∑ j, (a i * Y i j * b j - b i * Y i j * a j) := by
        simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, map_apply, Complex.im_sum]
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
        simp only [RCLike.star_def, Complex.mul_im, Complex.mul_re, Complex.conj_re,
          Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, a, b]
        ring
      rw [this, hcross, Complex.ofReal_im]
  rw [key, Complex.zero_lt_real]
  rcases hab with ha | hb
  · exact add_pos_of_pos_of_nonneg (by simpa using hY.dotProduct_mulVec_pos ha)
      (by simpa using hY.posSemidef.dotProduct_mulVec_nonneg b)
  · exact add_pos_of_nonneg_of_pos (by simpa using hY.posSemidef.dotProduct_mulVec_nonneg a)
      (by simpa using hY.dotProduct_mulVec_pos hb)

/-- The real Gram matrix `Re (Mᴴ M)` of a complex matrix `M` with linearly independent columns is
positive definite. -/
theorem PosDef.map_re_conjTranspose_mul_self [Fintype m] [Fintype n] (M : Matrix m n ℂ)
    (hM : Function.Injective M.mulVec) : ((Mᴴ * M).map Complex.re).PosDef :=
  (PosDef.conjTranspose_mul_self M hM).map_re

end Matrix
