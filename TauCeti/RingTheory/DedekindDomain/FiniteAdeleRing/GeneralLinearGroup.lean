/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.IntegralGL

/-!
# Matrices over the finite adeles, place by place

Let `R` be a Dedekind domain with fraction field `K` and finite adele ring `𝔸ᶠ = 𝔸ᶠ[R, K]`, and
let `ι` be a finite index type of size `n`. A matrix over `𝔸ᶠ` has a component in
`M_n(K_v)` at every finite place `v`, obtained by applying the projection
`IsDedekindDomain.FiniteAdeleRing.proj K v` to its entries, and it is determined by these
components. This file places a matrix of `M_n(K_v)`, or of `GL_n(K_v)`, at the single place `v`:
`IsDedekindDomain.FiniteAdeleRing.ofAdicCompletionGL K v g` is the element of `GL_n(𝔸ᶠ)` with
component `g` at `v` and `1` at every other place. It is the matrix counterpart of Mathlib's
`IsDedekindDomain.FiniteAdeleRing.ofAdicCompletion`, which does the same for `n = 1`, and it is a
continuous injective group homomorphism onto the elements of `GL_n(𝔸ᶠ)` trivial away from `v`.

These are the local factors from which elements of adelic groups supported at finitely many places
are built, such as the embedding of `GL_n(E_w)` in the finite adelic unitary group of a CM field
`E` at a split place `w` (`TauCeti.finiteAdelicUnitaryGroup.ofSplitPlace`). Elements of
`GL_n(𝔸ᶠ)` trivial at complementary sets of places commute
(`IsDedekindDomain.FiniteAdeleRing.commute_of_forall_map_proj_eq_one_or`).

## Main definitions

* `IsDedekindDomain.FiniteAdeleRing.ofAdicCompletionMatrix K v`: the multiplicative map
  `M_n(K_v) → M_n(𝔸ᶠ)` placing a matrix at `v`, with the identity matrix at the other places.
* `IsDedekindDomain.FiniteAdeleRing.ofAdicCompletionGL K v`: the induced group homomorphism
  `GL_n(K_v) → GL_n(𝔸ᶠ)`.

## Main results

* `IsDedekindDomain.FiniteAdeleRing.matrix_ext`: matrices over `𝔸ᶠ` are determined by their
  components. For invertible matrices, this file uses
  `IsDedekindDomain.FiniteAdeleRing.generalLinearGroup_ext` from `IntegralGL`.
* `IsDedekindDomain.FiniteAdeleRing.map_proj_ofAdicCompletionGL_self`,
  `IsDedekindDomain.FiniteAdeleRing.map_proj_ofAdicCompletionGL_of_ne`: the components of
  `ofAdicCompletionGL K v g`.
* `IsDedekindDomain.FiniteAdeleRing.range_ofAdicCompletionGL`: its range is the set of elements
  of `GL_n(𝔸ᶠ)` whose components away from `v` are `1`.
* `IsDedekindDomain.FiniteAdeleRing.ofAdicCompletionGL_injective`,
  `IsDedekindDomain.FiniteAdeleRing.continuous_ofAdicCompletionGL`: it is injective and
  continuous.
* `IsDedekindDomain.FiniteAdeleRing.commute_of_forall_map_proj_eq_one_or`: two elements of
  `GL_n(𝔸ᶠ)` commute when at every place one of them has component `1`.

## References

* A. Weil, *Basic Number Theory*, Chapter IV, §1.
* V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory*, Academic Press (1994),
  §5.1.
-/

public section
noncomputable section

open Matrix

namespace IsDedekindDomain.FiniteAdeleRing

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

/-! ### Components of matrices over the finite adeles -/

/-- **Matrices over the finite adeles are determined by their components**: two matrices whose
images under the projection to `K_v` agree at every finite place `v` are equal. -/
theorem matrix_ext {m n : Type*} {X Y : Matrix m n (FiniteAdeleRing R K)}
    (h : ∀ v : HeightOneSpectrum R, X.map (proj K v) = Y.map (proj K v)) : X = Y :=
  Matrix.ext fun i j ↦ FiniteAdeleRing.ext K fun v ↦ by
    simpa using congr_fun₂ (h v) i j

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Two elements of `GL_n(𝔸ᶠ)` **commute when at every place one of them has component `1`**,
for instance two elements trivial away from two different places. -/
theorem commute_of_forall_map_proj_eq_one_or {x y : GL ι (FiniteAdeleRing R K)}
    (h : ∀ v : HeightOneSpectrum R,
      GeneralLinearGroup.map (proj K v : _ →+* v.adicCompletion K) x = 1 ∨
        GeneralLinearGroup.map (proj K v : _ →+* v.adicCompletion K) y = 1) : Commute x y :=
  generalLinearGroup_ext fun v ↦ by
    change GeneralLinearGroup.map (proj K v : _ →+* v.adicCompletion K) (x * y) =
      GeneralLinearGroup.map (proj K v : _ →+* v.adicCompletion K) (y * x)
    rw [map_mul, map_mul]
    rcases h v with hv | hv <;> rw [hv, one_mul, mul_one]

/-! ### Matrices placed at a single place -/

omit [Fintype ι] in
/-- The component at a place `u` of the matrix `(A - 1).map (single K v) + 1`. -/
private theorem map_proj_sub_one_map_single_add_one (u v : HeightOneSpectrum R)
    (A : Matrix ι ι (v.adicCompletion K)) :
    ((A - 1).map (single K v) + 1).map (proj K u) = (A - 1).map (proj K u ∘ single K v) + 1 := by
  rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_map]

omit [Fintype ι] in
/-- The component at `v` of the matrix `(A - 1).map (single K v) + 1` is `A`. -/
private theorem map_proj_sub_one_map_single_add_one_self (v : HeightOneSpectrum R)
    (A : Matrix ι ι (v.adicCompletion K)) :
    ((A - 1).map (single K v) + 1).map (proj K v) = A := by
  rw [map_proj_sub_one_map_single_add_one, (leftInverse_proj_single v).comp_eq_id, Matrix.map_id,
    sub_add_cancel]

omit [Fintype ι] in
/-- The component at `u ≠ v` of the matrix `(A - 1).map (single K v) + 1` is `1`. -/
private theorem map_proj_sub_one_map_single_add_one_of_ne {u v : HeightOneSpectrum R}
    (h : u ≠ v) (A : Matrix ι ι (v.adicCompletion K)) :
    ((A - 1).map (single K v) + 1).map (proj K u) = 1 := by
  rw [map_proj_sub_one_map_single_add_one, add_eq_right]
  ext i j
  simp [single_apply_of_ne h]

variable (K) in
/-- The matrix over the finite adeles with **component `A` at the place `v`** and the identity
matrix at every other place, as a multiplicative map `M_n(K_v) → M_n(𝔸ᶠ)`. Its entries are
`single K v (A i j - δ i j) + δ i j`. -/
def ofAdicCompletionMatrix (v : HeightOneSpectrum R) :
    Matrix ι ι (v.adicCompletion K) →* Matrix ι ι (FiniteAdeleRing R K) where
  toFun A := (A - 1).map (single K v) + 1
  map_one' := by simp
  map_mul' A B := matrix_ext fun u ↦ by
    rw [← RingHom.coe_coe (proj K u), Matrix.map_mul, RingHom.coe_coe]
    rcases eq_or_ne u v with rfl | hu
    · simp only [map_proj_sub_one_map_single_add_one_self]
    · simp only [map_proj_sub_one_map_single_add_one_of_ne hu, one_mul]

/-- The entries of `ofAdicCompletionMatrix K v A` are `single K v (A i j - δ i j) + δ i j`. -/
theorem ofAdicCompletionMatrix_apply (v : HeightOneSpectrum R)
    (A : Matrix ι ι (v.adicCompletion K)) :
    ofAdicCompletionMatrix K v A = (A - 1).map (single K v) + 1 :=
  (rfl)

/-- The component of `ofAdicCompletionMatrix K v A` at `v` is `A`. -/
@[simp]
theorem map_proj_ofAdicCompletionMatrix_self (v : HeightOneSpectrum R)
    (A : Matrix ι ι (v.adicCompletion K)) :
    (ofAdicCompletionMatrix K v A).map (proj K v) = A :=
  map_proj_sub_one_map_single_add_one_self v A

/-- The component of `ofAdicCompletionMatrix K v A` at a place `u ≠ v` is the identity matrix. -/
@[simp]
theorem map_proj_ofAdicCompletionMatrix_of_ne {u v : HeightOneSpectrum R} (h : u ≠ v)
    (A : Matrix ι ι (v.adicCompletion K)) :
    (ofAdicCompletionMatrix K v A).map (proj K u) = 1 :=
  map_proj_sub_one_map_single_add_one_of_ne h A

variable (K) in
/-- The element of `GL_n(𝔸ᶠ)` with **component `g` at the place `v`** and `1` at every other
place, as a group homomorphism `GL_n(K_v) → GL_n(𝔸ᶠ)`: the units of
`ofAdicCompletionMatrix K v`. -/
def ofAdicCompletionGL (v : HeightOneSpectrum R) :
    GL ι (v.adicCompletion K) →* GL ι (FiniteAdeleRing R K) :=
  Units.map (ofAdicCompletionMatrix K v)

/-- The matrix underlying `ofAdicCompletionGL K v g` is `ofAdicCompletionMatrix K v g`. -/
@[simp]
theorem coe_ofAdicCompletionGL (v : HeightOneSpectrum R) (g : GL ι (v.adicCompletion K)) :
    (ofAdicCompletionGL K v g : Matrix ι ι (FiniteAdeleRing R K)) =
      ofAdicCompletionMatrix K v g :=
  (rfl)

/-- The component of `ofAdicCompletionGL K v g` at `v` is `g`. -/
@[simp]
theorem map_proj_ofAdicCompletionGL_self (v : HeightOneSpectrum R)
    (g : GL ι (v.adicCompletion K)) :
    GeneralLinearGroup.map (proj K v : _ →+* v.adicCompletion K) (ofAdicCompletionGL K v g) = g :=
  GeneralLinearGroup.ext fun i j ↦ by
    simpa using congr_fun₂ (map_proj_ofAdicCompletionMatrix_self (K := K) v g.val) i j

/-- The component of `ofAdicCompletionGL K v g` at a place `u ≠ v` is `1`. -/
@[simp]
theorem map_proj_ofAdicCompletionGL_of_ne {u v : HeightOneSpectrum R} (h : u ≠ v)
    (g : GL ι (v.adicCompletion K)) :
    GeneralLinearGroup.map (proj K u : _ →+* u.adicCompletion K) (ofAdicCompletionGL K v g) = 1 :=
  GeneralLinearGroup.ext fun i j ↦ by
    simpa using congr_fun₂ (map_proj_ofAdicCompletionMatrix_of_ne (K := K) h g.val) i j

/-- The projection to the component at `v` is a left inverse of `ofAdicCompletionGL K v`. -/
theorem leftInverse_map_proj_ofAdicCompletionGL (v : HeightOneSpectrum R) :
    Function.LeftInverse (GeneralLinearGroup.map (n := ι) (proj K v : _ →+* v.adicCompletion K))
      (ofAdicCompletionGL K v) :=
  map_proj_ofAdicCompletionGL_self v

/-- `ofAdicCompletionGL K v` is injective. -/
theorem ofAdicCompletionGL_injective (v : HeightOneSpectrum R) :
    Function.Injective (ofAdicCompletionGL (ι := ι) K v) :=
  (leftInverse_map_proj_ofAdicCompletionGL v).injective

/-- **The range of `ofAdicCompletionGL K v`** is the set of elements of `GL_n(𝔸ᶠ)` whose
component at every place other than `v` is `1`. -/
theorem range_ofAdicCompletionGL (v : HeightOneSpectrum R) :
    Set.range (ofAdicCompletionGL (ι := ι) K v) =
      {x | ∀ u ≠ v, GeneralLinearGroup.map (proj K u : _ →+* u.adicCompletion K) x = 1} := by
  ext x
  refine ⟨?_, fun hx ↦ ⟨GeneralLinearGroup.map (proj K v : _ →+* v.adicCompletion K) x,
    generalLinearGroup_ext fun u ↦ ?_⟩⟩
  · rintro ⟨g, rfl⟩ u hu
    exact map_proj_ofAdicCompletionGL_of_ne hu g
  · change GeneralLinearGroup.map (proj K u : FiniteAdeleRing R K →+* u.adicCompletion K) _ =
      GeneralLinearGroup.map (proj K u : _ →+* u.adicCompletion K) x
    rcases eq_or_ne u v with rfl | hu
    · exact map_proj_ofAdicCompletionGL_self u _
    · rw [map_proj_ofAdicCompletionGL_of_ne hu, hx u hu]

/-- `ofAdicCompletionMatrix K v` is continuous. -/
@[fun_prop]
theorem continuous_ofAdicCompletionMatrix (v : HeightOneSpectrum R) :
    Continuous (ofAdicCompletionMatrix (ι := ι) K v) :=
  ((continuous_id.sub continuous_const).matrix_map (single K v).continuous).add continuous_const

/-- `ofAdicCompletionGL K v` is continuous. -/
@[fun_prop]
theorem continuous_ofAdicCompletionGL (v : HeightOneSpectrum R) :
    Continuous (ofAdicCompletionGL (ι := ι) K v) :=
  Continuous.units_map _ (continuous_ofAdicCompletionMatrix v)

end IsDedekindDomain.FiniteAdeleRing
