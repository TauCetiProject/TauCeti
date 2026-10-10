/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Trace

/-!
# Action and trace formulas in exterior-power bases

A basis of a module induces a basis of each exterior power, indexed by subsets of the basis
indices. An endomorphism diagonal in the original basis acts diagonally in this exterior-power
basis, with eigenvalues given by products over the indexing subsets. Their sum is the trace.

A basis indexed by `Fin n` identifies the degree-`n` exterior power with the scalars by sending an
exterior product to its determinant against that basis. The induced endomorphism acts by its
determinant in this degree. These formulas hold over every commutative ring, including the zero
ring. When the ring is nontrivial, `n` is the module's rank and this is its top exterior power.

## Main definitions

* `Module.Basis.exteriorPowerTopEquiv` identifies the degree-`n` exterior power with the scalars
  for a basis indexed by `Fin n`.

## Main results

* `Module.Basis.toMatrix_exteriorPower_map` expresses the induced matrix in terms of minors.
* `RingHom.map_toMatrix_exteriorPower` changes the coefficient ring of the induced matrix.
* `Module.Basis.map_exteriorPower_of_apply` gives the eigenvalues in the exterior-power basis.
* `Module.Basis.trace_map_exteriorPower_of_apply` sums those eigenvalues to compute the trace.
* `Module.Basis.exteriorPower_ιMulti_eq_det_smul` expands a degree-`n` exterior product in terms
  of the wedge of a basis indexed by `Fin n`.
* `Module.Basis.map_exteriorPower_top_eq_det_smul` gives the degree-`n` action as its determinant
  for a basis indexed by `Fin n`.
* `LinearMap.map_exteriorPower_finrank_eq_det_smul` gives the action in degree `Module.finrank`
  as its determinant.
* `Module.Basis.trace_map_exteriorPower_top` gives the degree-`n` trace as the determinant
  for a basis indexed by `Fin n`.

## References

The results use Mathlib's exterior-power basis from `Mathlib.LinearAlgebra.ExteriorPower.Basis`,
by Sophie Morel and Daniel Morrison, and the determinant of a family against a basis from
`Mathlib.LinearAlgebra.Determinant`.
-/

public section

open scoped BigOperators TensorProduct

universe u w

variable {R : Type u} {M : Type w}

namespace exteriorPower

section Diagonal

variable [CommRing R]
variable {I : Type*} [LinearOrder I]
variable [AddCommGroup M] [Module R M]

/-- **An endomorphism diagonal in a basis is diagonal in the induced basis of the exterior
power**: the basis vector indexed by the `d`-element subset `s` is an eigenvector, with eigenvalue
the product of the eigenvalues indexed by `s`. Summing those eigenvalues over all `s` gives the
trace, `Module.Basis.trace_map_exteriorPower_of_apply`. -/
theorem _root_.Module.Basis.map_exteriorPower_of_apply (b : Module.Basis I R M) (f : M →ₗ[R] M)
    (a : I → R) (hf : ∀ i, f (b i) = a i • b i) (d : ℕ) (s : Set.powersetCard I d) :
    map d f (b.exteriorPower d s) = (∏ i ∈ (s : Finset I), a i) • b.exteriorPower d s := by
  have hprod : ∏ j : Fin d, a (Set.powersetCard.ofFinEmbEquiv.symm s j)
      = ∏ i ∈ (s : Finset I), a i := by
    rw [← Finset.prod_coe_sort s.1 a]
    apply Fintype.prod_equiv (s.1.orderIsoOfFin s.2).toEquiv
    intro j
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
    exact congrArg a (Finset.coe_orderIsoOfFin_apply s.1 s.2 j)
  have hfun :
      (f ∘ b) ∘ Set.powersetCard.ofFinEmbEquiv.symm s =
        fun j => a (Set.powersetCard.ofFinEmbEquiv.symm s j) •
          b (Set.powersetCard.ofFinEmbEquiv.symm s j) := by
    funext j
    simp only [Function.comp_apply, hf]
  rw [basis_apply, map_apply_ιMulti_family, ιMulti_family, ιMulti_family, hfun, ← hprod]
  simpa only [Function.comp_def] using
    (ιMulti R d).map_smul_univ (fun j => a (Set.powersetCard.ofFinEmbEquiv.symm s j))
      (fun j => b (Set.powersetCard.ofFinEmbEquiv.symm s j))

end Diagonal

section Trace

variable [CommRing R]
variable {I : Type*} [Fintype I]
variable [AddCommGroup M] [Module R M]

/-- If an endomorphism is diagonal in a finite basis, then its trace on the `d`th exterior
power is the `d`th elementary symmetric sum of its eigenvalues. -/
theorem _root_.Module.Basis.trace_map_exteriorPower_of_apply (b : Module.Basis I R M)
    (f : M →ₗ[R] M)
    (a : I → R) (d : ℕ) (hf : ∀ i, f (b i) = a i • b i) :
    LinearMap.trace R (⋀[R]^d M) (map d f) =
      ∑ s : Set.powersetCard I d, ∏ i ∈ (s : Finset I), a i := by
  classical
  let : LinearOrder I := linearOrderOfSTO WellOrderingRel
  rw [LinearMap.trace_eq_matrix_trace R (b.exteriorPower d), Matrix.trace]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply,
    b.map_exteriorPower_of_apply f a hf d s, map_smul, Finsupp.smul_apply,
    Module.Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one]

end Trace

section Top

variable [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}

/-- Given a basis indexed by `Fin n`, an exterior product of `n` vectors is the determinant of
that family against the basis, times the exterior product of the basis. -/
theorem _root_.Module.Basis.exteriorPower_ιMulti_eq_det_smul (b : Module.Basis (Fin n) R M)
    (v : Fin n → M) :
    ιMulti R n v = b.det v • ιMulti R n ⇑b := by
  -- Compare both sides coordinatewise in the basis of `⋀[R]^n M` induced by `b`: each coordinate
  -- is an `R`-valued alternating form, hence a multiple of `b.det`.
  refine (b.exteriorPower n).ext_elem fun s ↦ ?_
  -- The `s`th coordinate of `ιMulti R n v` is an alternating form in `v`.
  set φ : M [⋀^Fin n]→ₗ[R] R := (ιMultiDual R n b s).compAlternatingMap (ιMulti R n) with hφ
  have hφ_apply (w : Fin n → M) :
      φ w = (b.exteriorPower n).repr (ιMulti R n w) s := by
    rw [hφ, basis_repr_apply, LinearMap.compAlternatingMap_apply]
  have hdet : φ = φ ⇑b • b.det := φ.eq_smul_basis_det b
  calc (b.exteriorPower n).repr (ιMulti R n v) s
      = φ v := (hφ_apply v).symm
    _ = φ ⇑b * b.det v := by rw [hdet]; simp [Module.Basis.det_self]
    _ = b.det v * (b.exteriorPower n).repr (ιMulti R n ⇑b) s := by
        rw [← hφ_apply ⇑b, mul_comm]
    _ = (b.exteriorPower n).repr (b.det v • ιMulti R n ⇑b) s := by simp

/-- For a basis indexed by `Fin n`, an endomorphism acts on the degree-`n` exterior power as
multiplication by its determinant. -/
theorem _root_.Module.Basis.map_exteriorPower_top_eq_det_smul (b : Module.Basis (Fin n) R M)
    (f : M →ₗ[R] M) :
    map n f = LinearMap.det f • LinearMap.id := by
  refine LinearMap.ext_on (ιMulti_span R n M) ?_
  rintro _ ⟨v, rfl⟩
  rw [map_apply_ιMulti, b.exteriorPower_ιMulti_eq_det_smul (f ∘ v),
    b.exteriorPower_ιMulti_eq_det_smul v, Module.Basis.det_comp, mul_smul]
  simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq]

/-- The basis-free form of `Module.Basis.map_exteriorPower_top_eq_det_smul`: an endomorphism of a
free module acts on the exterior power in degree `Module.finrank R M` by its determinant.
For a nonfinite module over a nontrivial ring, this is the identity in degree zero. -/
@[simp]
theorem _root_.LinearMap.map_exteriorPower_finrank_eq_det_smul
    [Module.Free R M]
    (f : M →ₗ[R] M) :
    map (Module.finrank R M) f = LinearMap.det f • LinearMap.id := by
  rcases subsingleton_or_nontrivial R with _ | _
  · have := Module.subsingleton R (⋀[R]^(Module.finrank R M) M)
    exact Subsingleton.elim _ _
  · classical
    by_cases h : Module.Finite R M
    · have := h
      exact (Module.finBasis R M).map_exteriorPower_top_eq_det_smul f
    · rw [Module.finrank_of_not_finite h, LinearMap.det_eq_one_of_not_module_finite h f,
        one_smul]
      exact (LinearMap.cancel_left (zeroEquiv R M).injective).mp
        (by simpa only [LinearMap.comp_id] using zeroEquiv_naturality f)

/-- A basis indexed by `Fin n` identifies the degree-`n` exterior power with the scalars by
sending an exterior product of vectors to their determinant against the basis. -/
noncomputable def _root_.Module.Basis.exteriorPowerTopEquiv (b : Module.Basis (Fin n) R M) :
    ⋀[R]^n M ≃ₗ[R] R :=
  LinearEquiv.ofLinearMap (alternatingMapLinearEquiv b.det)
    (LinearMap.toSpanSingleton R (⋀[R]^n M) (ιMulti R n ⇑b))
    (by
      ext
      simp [Module.Basis.det_self])
    (by
      refine LinearMap.ext_on (ιMulti_span R n M) ?_
      rintro _ ⟨v, rfl⟩
      simp [b.exteriorPower_ιMulti_eq_det_smul v, Module.Basis.det_self])

/-- The identification for a basis indexed by `Fin n` sends an exterior product to its determinant
against the basis. -/
@[simp]
lemma _root_.Module.Basis.exteriorPowerTopEquiv_apply_ιMulti (b : Module.Basis (Fin n) R M)
    (v : Fin n → M) :
    b.exteriorPowerTopEquiv (ιMulti R n v) = b.det v := by
  simp [Module.Basis.exteriorPowerTopEquiv]

/-- The inverse identification sends a scalar to that multiple of the basis wedge. -/
@[simp]
lemma _root_.Module.Basis.exteriorPowerTopEquiv_symm_apply (b : Module.Basis (Fin n) R M) (r : R) :
    b.exteriorPowerTopEquiv.symm r = r • ιMulti R n ⇑b := by
  simp [Module.Basis.exteriorPowerTopEquiv]

/-- For a basis indexed by `Fin n`, the trace of the induced endomorphism on the degree-`n`
exterior power is the determinant. -/
theorem _root_.Module.Basis.trace_map_exteriorPower_top
    (b : Module.Basis (Fin n) R M) (f : M →ₗ[R] M) :
    LinearMap.trace R (⋀[R]^n M) (map n f) = LinearMap.det f := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact Subsingleton.elim _ _
  · have := Module.Free.of_basis b
    have := Module.Finite.of_basis b
    -- The top exterior power is one-dimensional, the diagonal case `Nat.choose n n = 1`.
    rw [b.map_exteriorPower_top_eq_det_smul f, map_smul, LinearMap.trace_id, finrank_eq,
      Module.finrank_eq_card_basis b, Fintype.card_fin, Nat.choose_self]
    simp

end Top

end exteriorPower

namespace Module.Basis

variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [LinearOrder I] [Fintype I]

/-- The matrix of an exterior-power map consists of the corresponding minors. -/
theorem toMatrix_exteriorPower_map (b : Basis I R M) (n : ℕ) (f : M →ₗ[R] M)
    (s t : Set.powersetCard I n) :
    LinearMap.toMatrix (b.exteriorPower n) (b.exteriorPower n) (exteriorPower.map n f) s t =
      (Matrix.of fun i j : Fin n ↦
        LinearMap.toMatrix b b f (Set.powersetCard.ofFinEmbEquiv.symm s j)
          (Set.powersetCard.ofFinEmbEquiv.symm t i)).det := by
  simp [LinearMap.toMatrix_apply, exteriorPower.basis_repr_apply,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPower.map_apply_ιMulti, exteriorPower.ιMultiDual_apply_ιMulti,
    Basis.coord_apply]

end Module.Basis

namespace RingHom

variable {R S I : Type*} [CommRing R] [CommRing S] [LinearOrder I] [Fintype I]

/-- Exterior-power matrices commute with a change of coefficient ring. -/
theorem map_toMatrix_exteriorPower (φ : R →+* S) (n : ℕ) (A : Matrix I I R) :
    φ.mapMatrix (LinearMap.toMatrix ((Pi.basisFun R I).exteriorPower n)
      ((Pi.basisFun R I).exteriorPower n) (exteriorPower.map n A.toLin')) =
    LinearMap.toMatrix ((Pi.basisFun S I).exteriorPower n)
      ((Pi.basisFun S I).exteriorPower n) (exteriorPower.map n (φ.mapMatrix A).toLin') := by
  classical
  ext s t
  rw [RingHom.mapMatrix_apply, Matrix.map_apply,
    Module.Basis.toMatrix_exteriorPower_map, Module.Basis.toMatrix_exteriorPower_map]
  simp only [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  rw [RingHom.map_det]
  rfl

end RingHom
