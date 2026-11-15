/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Finite

/-!
# Change of coefficients for the type-A Hecke algebra

Let `S` be an `R`-algebra and let `q' : Sˣ` be the image of the parameter `q : Rˣ`. The defining
relations of `TauCeti.TypeAHeckeAlgebra R q n` are carried to those of
`TauCeti.TypeAHeckeAlgebra S q' n`, so there is a coefficient-change map
`TauCeti.TypeAHeckeAlgebra.map`, sending each generator `T i` to the generator `T i`. These maps
are functorial in the coefficient algebra, and compatible with the braid homomorphisms and the
tower maps.

Since the Hecke algebra is defined by generators and relations whose coefficients come from `R`,
its formation commutes with base change: `S ⊗[R] TypeAHeckeAlgebra R q n` is isomorphic as an
`S`-algebra to `TypeAHeckeAlgebra S q' n` (`TauCeti.TypeAHeckeAlgebra.algebraTensorAlgEquiv`).
This transports statements about the Hecke algebra over a ring of generic parameters, such as
`ℤ[q, q⁻¹]`, to its specializations at a particular parameter in a particular coefficient ring.

The defining relations of `TauCeti.InfiniteTypeAHeckeAlgebra R q` likewise map to those of
`TauCeti.InfiniteTypeAHeckeAlgebra S q'`, giving `TauCeti.InfiniteTypeAHeckeAlgebra.map`,
compatibly with the braid homomorphisms, the finite stages, and `toInfinite`.

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.map`: the coefficient-change map along an `R`-algebra `S`.
* `TauCeti.InfiniteTypeAHeckeAlgebra.map`: the coefficient-change map of infinite type-A Hecke
  algebras along an `R`-algebra `S`.
* `TauCeti.TypeAHeckeAlgebra.algebraTensorAlgEquiv`: the base change isomorphism
  `S ⊗[R] TypeAHeckeAlgebra R q n ≃ₐ[S] TypeAHeckeAlgebra S q' n`.

## Main results

* `TauCeti.TypeAHeckeAlgebra.map_id`, `TauCeti.TypeAHeckeAlgebra.map_map`,
  `TauCeti.InfiniteTypeAHeckeAlgebra.map_id`, and `TauCeti.InfiniteTypeAHeckeAlgebra.map_map`:
  functoriality.
* `TauCeti.TypeAHeckeAlgebra.map_braidHom`, `TauCeti.TypeAHeckeAlgebra.map_strandIncl`,
  `TauCeti.InfiniteTypeAHeckeAlgebra.map_braidHom`,
  `TauCeti.InfiniteTypeAHeckeAlgebra.map_mem_stage`, and
  `TauCeti.TypeAHeckeAlgebra.map_toInfinite`: compatibility with the braid homomorphisms, the
  tower maps, the stages, and the embeddings into the infinite algebra.
* `TauCeti.TypeAHeckeAlgebra.algebraTensorAlgEquiv_tmul` and
  `TauCeti.TypeAHeckeAlgebra.algebraTensorAlgEquiv_symm_T`: the base change isomorphism and its
  inverse on pure tensors and generators.

## References

* The base change isomorphism follows the pattern of `CliffordAlgebra.equivBaseChange` in
  `Mathlib.LinearAlgebra.CliffordAlgebra.BaseChange` and of `MvPolynomial.algebraTensorAlgEquiv`.
-/

public section

open scoped TensorProduct

namespace TauCeti

/-- The quadratic-relation coefficient `q - q⁻¹` maps to `q' - q'⁻¹`. -/
private theorem algebraMap_sub_inv_eq {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {q : Rˣ} {q' : Sˣ} (h : algebraMap R S q = q') :
    algebraMap R S ((q : R) - ↑q⁻¹) = (q' : S) - ↑q'⁻¹ := by
  rw [map_sub, h, ← Units.ext (u := Units.map (algebraMap R S : R →* S) q) h, Units.coe_map_inv,
    MonoidHom.coe_ofClass]

namespace InfiniteTypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {q : Rˣ}
variable {S : Type*} [CommRing S] [Algebra R S] {q' : Sˣ}

/-- The coefficient-change map of infinite type-A Hecke algebras along an `R`-algebra `S`, when
the parameter `q : Rˣ` maps to `q' : Sˣ`: the generator `T i` goes to the generator `T i`. -/
def map (h : algebraMap R S q = q') :
    InfiniteTypeAHeckeAlgebra R q →ₐ[R] InfiniteTypeAHeckeAlgebra S q' :=
  lift (fun i ↦ T q' i)
    (fun i ↦ by rw [T_mul_self, ← algebraMap_sub_inv_eq h, algebraMap_smul])
    (fun i ↦ T_braid i) (fun h ↦ (commute_T (Or.inl h)).eq)

/-- The coefficient-change map sends each generator to the generator with the same index. -/
@[simp]
theorem map_T (h : algebraMap R S q = q') (i : ℕ) : map h (T q i) = T q' i := by
  rw [map, lift_T]

/-- Changing coefficients along the identity of `R` is the identity. -/
@[simp]
theorem map_id (h : algebraMap R R q = q) : map h = AlgHom.id R _ :=
  hom_ext fun i ↦ by simp

/-- Changing coefficients along `R → S` and then along `S → S'` is changing coefficients along
the composite `R → S'`. -/
@[simp]
theorem map_map {S' : Type*} [CommRing S'] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
    {q'' : S'ˣ} (h : algebraMap R S q = q') (h' : algebraMap S S' q' = q'')
    (x : InfiniteTypeAHeckeAlgebra R q) :
    map h' (map h x) = map (by rw [IsScalarTower.algebraMap_apply R S S', h, h']) x := by
  have hcomp : ((map h').restrictScalars R).comp (map h) =
      map (by rw [IsScalarTower.algebraMap_apply R S S', h, h']) :=
    hom_ext fun i ↦ by simp
  exact DFunLike.congr_fun hcomp x

/-- The coefficient-change maps intertwine the braid homomorphisms into the infinite algebras. -/
@[simp]
theorem map_braidHom (h : algebraMap R S q = q') (n : ℕ) (b : BraidGroup n) :
    map h (braidHom R q n b) = braidHom S q' n b := by
  have hb : (Units.map (map h : InfiniteTypeAHeckeAlgebra R q →* _)).comp (braidHom R q n) =
      braidHom S q' n :=
    BraidGroup.hom_ext fun i ↦ Units.ext <| by simp
  exact congrArg Units.val (DFunLike.congr_fun hb b)

/-- The coefficient-change map carries the `n`-th stage into the `n`-th stage. -/
theorem map_mem_stage (h : algebraMap R S q = q') {n : ℕ} {x : InfiniteTypeAHeckeAlgebra R q}
    (hx : x ∈ stage R q n) : map h x ∈ stage S q' n := by
  have hle : stage R q n ≤ ((stage S q' n).restrictScalars R).comap (map h) :=
    stage_le_iff.2 fun i hi ↦ by
      simpa only [Subalgebra.mem_comap, Subalgebra.mem_restrictScalars, map_T] using T_mem_stage hi
  exact hle hx

end InfiniteTypeAHeckeAlgebra

namespace TypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {q : Rˣ} {n : ℕ}
variable {S : Type*} [CommRing S] [Algebra R S] {q' : Sˣ}

section Map

variable (n) in
/-- The coefficient-change map of type-A Hecke algebras along an `R`-algebra `S`, when the
parameter `q : Rˣ` maps to `q' : Sˣ`: the generator `T i` goes to the generator `T i`. -/
def map (h : algebraMap R S q = q') : TypeAHeckeAlgebra R q n →ₐ[R] TypeAHeckeAlgebra S q' n :=
  lift (fun i ↦ T q' i)
    (fun i ↦ by rw [T_mul_self, ← algebraMap_sub_inv_eq h, algebraMap_smul])
    (fun h ↦ T_braid (Or.inl h)) (fun h ↦ (commute_T (Or.inl h)).eq)

/-- The coefficient-change map sends each generator to the generator with the same index. -/
@[simp]
theorem map_T (h : algebraMap R S q = q') (i : Fin (n - 1)) : map n h (T q i) = T q' i := by
  rw [map, lift_T]

/-- Changing coefficients along the identity of `R` is the identity. -/
@[simp]
theorem map_id (h : algebraMap R R q = q) : map n h = AlgHom.id R _ :=
  hom_ext fun i ↦ by simp

/-- Changing coefficients along `R → S` and then along `S → S'` is changing coefficients along
the composite `R → S'`. -/
@[simp]
theorem map_map {S' : Type*} [CommRing S'] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
    {q'' : S'ˣ} (h : algebraMap R S q = q') (h' : algebraMap S S' q' = q'')
    (x : TypeAHeckeAlgebra R q n) :
    map n h' (map n h x) =
      map n (by rw [IsScalarTower.algebraMap_apply R S S', h, h']) x := by
  have hcomp : ((map n h').restrictScalars R).comp (map n h) =
      map n (by rw [IsScalarTower.algebraMap_apply R S S', h, h']) :=
    hom_ext fun i ↦ by simp
  exact DFunLike.congr_fun hcomp x

/-- The coefficient-change maps intertwine the braid homomorphisms. -/
@[simp]
theorem map_braidHom (h : algebraMap R S q = q') (b : BraidGroup n) :
    map n h (braidHom R q n b) = braidHom S q' n b := by
  have hb : (Units.map (map n h : TypeAHeckeAlgebra R q n →* _)).comp (braidHom R q n) =
      braidHom S q' n :=
    BraidGroup.hom_ext fun i ↦ Units.ext <| by simp
  exact congrArg Units.val (DFunLike.congr_fun hb b)

/-- The coefficient-change maps are compatible with the tower maps. -/
@[simp]
theorem map_strandIncl (h : algebraMap R S q = q') (x : TypeAHeckeAlgebra R q n) :
    map (n + 1) h (strandIncl R q n x) = strandIncl S q' n (map n h x) := by
  have hcomp : (map (n + 1) h).comp (strandIncl R q n) =
      ((strandIncl S q' n).restrictScalars R).comp (map n h) :=
    hom_ext fun i ↦ by simp
  exact DFunLike.congr_fun hcomp x

/-- The finite and infinite coefficient-change maps commute with `toInfinite`. -/
@[simp]
theorem map_toInfinite (h : algebraMap R S q = q') (x : TypeAHeckeAlgebra R q n) :
    InfiniteTypeAHeckeAlgebra.map h (toInfinite R q n x) = toInfinite S q' n (map n h x) := by
  have hcomp : (InfiniteTypeAHeckeAlgebra.map h).comp (toInfinite R q n) =
      ((toInfinite S q' n).restrictScalars R).comp (map n h) :=
    hom_ext fun i ↦ by simp
  exact DFunLike.congr_fun hcomp x

end Map

section BaseChange

variable (n) in
/-- The base change map `S ⊗[R] TypeAHeckeAlgebra R q n → TypeAHeckeAlgebra S q' n`,
`s ⊗ x ↦ s • map h x`. -/
private def ofBaseChange (h : algebraMap R S q = q') :
    S ⊗[R] TypeAHeckeAlgebra R q n →ₐ[S] TypeAHeckeAlgebra S q' n :=
  Algebra.TensorProduct.lift (Algebra.ofId S _) (map n h) fun s _ ↦ by
    rw [Algebra.ofId_apply]
    exact Algebra.commute_algebraMap_left s _

private theorem ofBaseChange_tmul (h : algebraMap R S q = q') (s : S)
    (x : TypeAHeckeAlgebra R q n) :
    ofBaseChange n h (s ⊗ₜ x) = s • map n h x := by
  rw [ofBaseChange, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Algebra.smul_def]

variable (n) in
/-- The inverse of the base change map, `T i ↦ 1 ⊗ T i`. -/
private def toBaseChange (h : algebraMap R S q = q') :
    TypeAHeckeAlgebra S q' n →ₐ[S] S ⊗[R] TypeAHeckeAlgebra R q n :=
  lift (fun i ↦ 1 ⊗ₜ T q i)
    (fun i ↦ by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, T_mul_self, TensorProduct.tmul_add,
        ← algebraMap_sub_inv_eq h, algebraMap_smul, TensorProduct.tmul_smul,
        Algebra.TensorProduct.one_def])
    (fun h ↦ by simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, T_braid (Or.inl h)])
    (fun h ↦ by simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, (commute_T (Or.inl h)).eq])

private theorem toBaseChange_T (h : algebraMap R S q = q') (i : Fin (n - 1)) :
    toBaseChange n h (T q' i) = 1 ⊗ₜ T q i :=
  lift_T ..

variable (n) in
/-- The type-A Hecke algebra commutes with base change: for an `R`-algebra `S` in which the
parameter `q` maps to `q'`, tensoring `TypeAHeckeAlgebra R q n` with `S` gives
`TypeAHeckeAlgebra S q' n`. -/
noncomputable def algebraTensorAlgEquiv (h : algebraMap R S q = q') :
    S ⊗[R] TypeAHeckeAlgebra R q n ≃ₐ[S] TypeAHeckeAlgebra S q' n :=
  AlgEquiv.ofAlgHom (ofBaseChange n h) (toBaseChange n h)
    (hom_ext fun i ↦ by simp [toBaseChange_T, ofBaseChange_tmul])
    (Algebra.TensorProduct.ext (Subsingleton.elim _ _)
      (hom_ext fun i ↦ by simp [toBaseChange_T, ofBaseChange_tmul]))

/-- The base change isomorphism on pure tensors. -/
@[simp]
theorem algebraTensorAlgEquiv_tmul (h : algebraMap R S q = q') (s : S)
    (x : TypeAHeckeAlgebra R q n) :
    algebraTensorAlgEquiv n h (s ⊗ₜ x) = s • map n h x :=
  ofBaseChange_tmul h s x

/-- The inverse of the base change isomorphism sends each generator `T i` to `1 ⊗ T i`. -/
@[simp]
theorem algebraTensorAlgEquiv_symm_T (h : algebraMap R S q = q') (i : Fin (n - 1)) :
    (algebraTensorAlgEquiv n h).symm (T q' i) = 1 ⊗ₜ T q i :=
  toBaseChange_T h i

/-- The inverse of the base change isomorphism sends the image of `x` under the
coefficient-change map to `1 ⊗ x`. -/
@[simp]
theorem algebraTensorAlgEquiv_symm_map (h : algebraMap R S q = q')
    (x : TypeAHeckeAlgebra R q n) :
    (algebraTensorAlgEquiv n h).symm (map n h x) = 1 ⊗ₜ x := by
  rw [AlgEquiv.symm_apply_eq, algebraTensorAlgEquiv_tmul, one_smul]

end BaseChange

end TypeAHeckeAlgebra

end TauCeti
