/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Order.Hom.PowersetCard

/-!
# Action and trace formulas in exterior-power bases

A basis of a module induces a basis of each exterior power, indexed by subsets of the basis
indices. An endomorphism diagonal in the original basis acts diagonally in this exterior-power
basis, with eigenvalues given by products over the indexing subsets. Their sum is the trace.

A basis indexed by `Fin n` identifies the degree-`n` exterior power with the scalars by sending an
exterior product to its determinant against that basis. More generally, any finite linearly ordered
basis induces a trivialisation `Module.Basis.exteriorPowerFinrankEquiv` of the degree-`finrank`
exterior power sending its exterior-power basis vector to `1`. The induced endomorphism acts by its
determinant in this degree, and a change of `n` vectors by a square matrix multiplies their
exterior product by its determinant. These formulas hold over every commutative ring, including
the zero ring. When the ring is nontrivial, `n` is the module's rank and this is its top exterior
power.

## Main definitions

* `Module.Basis.exteriorPowerTopEquiv` identifies the degree-`n` exterior power with the scalars
  for a basis indexed by `Fin n`.
* `Module.Basis.exteriorPowerFinrankEquiv` identifies the degree-`Module.finrank R M` exterior
  power with the scalars for any finite linearly ordered basis.

## Main results

* `Module.Basis.toMatrix_exteriorPower_map` expresses the induced matrix in terms of minors.
* `RingHom.map_toMatrix_exteriorPower` changes the coefficient ring of the induced matrix.
* `Module.Basis.map_exteriorPower_of_apply` gives the eigenvalues in the exterior-power basis.
* `Module.Basis.trace_map_exteriorPower_of_apply` sums those eigenvalues to compute the trace.
* `Module.Basis.exteriorPower_ιMulti_eq_det_smul` expands a degree-`n` exterior product in terms
  of the wedge of a basis indexed by `Fin n`.
* `Module.Basis.map_exteriorPower_top_eq_det_smul` gives the degree-`n` action as its determinant
  for a basis indexed by `Fin n`.
* `Module.Basis.exteriorPowerTopEquiv_map` gives the scalar coordinate formula for every
  endomorphism in this identification.
* `LinearMap.map_exteriorPower_finrank_eq_det_smul` gives the action in degree `Module.finrank`
  as its determinant.
* `Module.Basis.trace_map_exteriorPower_top` gives the degree-`n` trace as the determinant
  for a basis indexed by `Fin n`.
* `exteriorPower.ιMulti_sum_smul` and `AlternatingMap.map_sum_smul`: replacing a family of `n`
  vectors by its combinations with the rows of a square matrix `A` multiplies its exterior
  product, and the value of every alternating map on it, by `det A`.

## References

The results use Mathlib's exterior-power basis from `Mathlib.LinearAlgebra.ExteriorPower.Basis`,
by Sophie Morel and Daniel Morrison, and the determinant of a family against a basis from
`Mathlib.LinearAlgebra.Determinant`.
-/

public section

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
      = ∏ i ∈ (s : Finset I), a i :=
    Set.powersetCard.prod_comp_ofFinEmbEquiv_symm s a
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
  have := congr($(((ιMultiDual R n b s).compAlternatingMap (ιMulti R n)).eq_smul_basis_det b) v)
  simpa [basis_repr_apply, mul_comm, -ιMultiDual_apply_ιMulti] using this

/-- For a basis indexed by `Fin n`, an endomorphism acts on the degree-`n` exterior power as
multiplication by its determinant. -/
theorem _root_.Module.Basis.map_exteriorPower_top_eq_det_smul (b : Module.Basis (Fin n) R M)
    (f : M →ₗ[R] M) :
    map n f = LinearMap.det f • LinearMap.id := by
  refine LinearMap.ext_on (ιMulti_span R n M) ?_
  rintro _ ⟨v, rfl⟩
  rw [map_apply_ιMulti, b.exteriorPower_ιMulti_eq_det_smul (f ∘ v),
    b.exteriorPower_ιMulti_eq_det_smul v, Module.Basis.det_comp, mul_smul, LinearMap.smul_apply,
    LinearMap.id_apply]

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
    · exact (Module.finBasis R M).map_exteriorPower_top_eq_det_smul f
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

/-- In top exterior-power coordinates, every endomorphism acts by its determinant. This includes
singular maps, rank zero and the zero coefficient ring. -/
theorem _root_.Module.Basis.exteriorPowerTopEquiv_map (b : Module.Basis (Fin n) R M)
    (f : M →ₗ[R] M) (x : ⋀[R]^n M) :
    b.exteriorPowerTopEquiv (map n f x) = LinearMap.det f * b.exteriorPowerTopEquiv x := by
  rw [b.map_exteriorPower_top_eq_det_smul, LinearMap.smul_apply, LinearMap.id_apply, map_smul,
    smul_eq_mul]

/-- For a basis indexed by `Fin n`, every element of the degree-`n` exterior power is a multiple
of the exterior product of the basis. -/
lemma _root_.Module.Basis.exists_smul_ιMulti_eq (b : Module.Basis (Fin n) R M) (x : ⋀[R]^n M) :
    ∃ r : R, r • ιMulti R n ⇑b = x :=
  ⟨b.exteriorPowerTopEquiv x, by
    rw [← Module.Basis.exteriorPowerTopEquiv_symm_apply, LinearEquiv.symm_apply_apply]⟩

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
    simp [b.map_exteriorPower_top_eq_det_smul f, Module.finrank_eq_card_basis b]

/-- Replacing a family of `n` vectors by the combinations `∑ i, A j i • v i` with the rows of a
square matrix `A` multiplies its exterior product by `det A`. No independence of `v` is needed. -/
theorem ιMulti_sum_smul (A : Matrix (Fin n) (Fin n) R) (v : Fin n → M) :
    ιMulti R n (fun j ↦ ∑ i, A j i • v i) = A.det • ιMulti R n v := by
  classical
  -- Both families are images under the synthesis map `Fin n → R → M` of `v`: the rows of `A`
  -- and the standard basis, whose determinant against each other is `det A`.
  let L := Fintype.linearCombination R v
  have hrows : (fun j ↦ ∑ i, A j i • v i) = L ∘ Matrix.of.symm A := by
    ext j
    simp [L, Fintype.linearCombination_apply]
  have hbasis : v = L ∘ Pi.basisFun R (Fin n) := by
    ext i
    simp [L, Fintype.linearCombination_apply_single]
  rw [hrows, ← map_apply_ιMulti, (Pi.basisFun R (Fin n)).exteriorPower_ιMulti_eq_det_smul,
    Pi.basisFun_det_apply, Equiv.apply_symm_apply, map_smul, map_apply_ιMulti, ← hbasis]

/-- For a finite linearly ordered basis `b` of `M`, the induced trivialisation of the
degree-`Module.finrank R M` exterior power sending its exterior-power basis vector to `1`. -/
noncomputable def _root_.Module.Basis.exteriorPowerFinrankEquiv
    {ι : Type*} [LinearOrder ι] [Fintype ι] (b : Module.Basis ι R M) :
    ⋀[R]^(Module.finrank R M) M ≃ₗ[R] R :=
  open Classical in
  if h : Nontrivial R then
    haveI : Subsingleton (Set.powersetCard ι (Module.finrank R M)) :=
      Set.powersetCard.subsingleton_of_card_eq (Module.finrank_eq_card_basis b)
    (b.exteriorPower (Module.finrank R M)).repr.trans
      (Finsupp.uniqueLinearEquiv R R ⟨Finset.univ, by simp [Module.finrank_eq_card_basis b]⟩)
  else
    haveI : Subsingleton R := not_nontrivial_iff_subsingleton.mp h
    haveI : Subsingleton (⋀[R]^(Module.finrank R M) M) := Module.subsingleton R _
    LinearEquiv.ofSubsingleton (⋀[R]^(Module.finrank R M) M) R

/-- `b.exteriorPowerFinrankEquiv` sends every exterior-power basis vector in degree
`Module.finrank R M` to `1`. -/
@[simp]
theorem _root_.Module.Basis.exteriorPowerFinrankEquiv_apply_ιMulti_family
    {ι : Type*} [LinearOrder ι] [Fintype ι] (b : Module.Basis ι R M)
    (s : Set.powersetCard ι (Module.finrank R M)) :
    b.exteriorPowerFinrankEquiv (ιMulti_family R (Module.finrank R M) b s) = 1 := by
  rcases subsingleton_or_nontrivial R with _ | h
  · exact Subsingleton.elim _ _
  · have : Subsingleton (Set.powersetCard ι (Module.finrank R M)) :=
      Set.powersetCard.subsingleton_of_card_eq (Module.finrank_eq_card_basis b)
    rw [Module.Basis.exteriorPowerFinrankEquiv, dite_eq_left h, LinearEquiv.trans_apply,
      Finsupp.uniqueLinearEquiv_apply,
      Subsingleton.elim ⟨Finset.univ, by simp [Module.finrank_eq_card_basis b]⟩ s,
      ← basis_apply, Module.Basis.repr_self, Finsupp.single_eq_same]

/-- The inverse of `b.exteriorPowerFinrankEquiv` sends a scalar to that multiple of any
exterior-power basis vector in degree `Module.finrank R M`. -/
theorem _root_.Module.Basis.exteriorPowerFinrankEquiv_symm_apply_eq_smul
    {ι : Type*} [LinearOrder ι] [Fintype ι] (b : Module.Basis ι R M)
    (s : Set.powersetCard ι (Module.finrank R M)) (r : R) :
    b.exteriorPowerFinrankEquiv.symm r = r • b.exteriorPower (Module.finrank R M) s := by
  apply b.exteriorPowerFinrankEquiv.injective
  simp

end Top

end exteriorPower

namespace AlternatingMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {n : ℕ}

/-- An alternating map takes the combinations `∑ i, A j i • v i` of a family with the rows of a
square matrix `A` to `det A` times its value on the family. -/
theorem map_sum_smul (f : M [⋀^Fin n]→ₗ[R] N) (A : Matrix (Fin n) (Fin n) R) (v : Fin n → M) :
    f (fun j ↦ ∑ i, A j i • v i) = A.det • f v := by
  rw [← exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, exteriorPower.ιMulti_sum_smul,
    map_smul, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]

end AlternatingMap

namespace Module.Basis

section Repr

variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M] [LinearOrder I]

/-- The exterior-algebra coordinate of `ω : ⋀[R]^r M` at `u.1` equals its `exteriorPower r`
coordinate at `u`. -/
theorem exteriorAlgebra_repr_coe_eq (b : Basis I R M) {r : ℕ} (ω : ⋀[R]^r M)
    (u : Set.powersetCard I r) :
    b.ExteriorAlgebra.repr ω.val u.val = (b.exteriorPower r).repr ω u := by
  classical
  rw [← Basis.coord_apply]
  conv_lhs => rw [← (b.exteriorPower r).linearCombination_repr ω, Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, Submodule.coe_sum, Submodule.coe_smul,
    ← ExteriorAlgebra.basis_eq_coe_basis, map_sum, map_smul, Basis.coord_apply, Basis.repr_self,
    Finsupp.single_apply, smul_eq_mul, mul_boole, ← Subtype.ext_iff, Finset.sum_ite_eq']
  split_ifs with hu <;> [rfl; exact (Finsupp.notMem_support_iff.mp hu).symm]

/-- The `{k}`-coordinate of `(exteriorPower.oneEquiv R M).symm m` in `b.exteriorPower 1` equals
the `k`-th coordinate of `m` in `b`. -/
theorem exteriorPower_one_repr_oneEquiv_symm (b : Basis I R M) (m : M) (k : I) :
    (b.exteriorPower 1).repr ((exteriorPower.oneEquiv R M).symm m)
        (Set.powersetCard.ofCard (Finset.card_singleton k)) = b.repr m k := by
  classical
  rw [← Basis.coord_apply]
  conv_lhs => rw [← b.linearCombination_repr m, Finsupp.linearCombination_apply]
  have hsingle (i : I) : (exteriorPower.oneEquiv R M).symm (b i) =
      b.exteriorPower 1 (Set.powersetCard.ofCard (Finset.card_singleton i)) := by
    rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, exteriorPower.oneEquiv_symm_apply]
    congr 1; funext j
    have hmem : (Set.powersetCard.ofFinEmbEquiv.symm
        (Set.powersetCard.ofCard (Finset.card_singleton i))) j ∈ ({i} : Finset I) := by
      rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]; exact Finset.orderEmbOfFin_mem _ _ j
    exact congrArg b (Finset.mem_singleton.mp hmem).symm
  simp only [Finsupp.sum, map_sum, map_smul, hsingle, Basis.coord_apply, Basis.repr_self,
    Finsupp.single_apply, Subtype.ext_iff, Set.powersetCard.val_ofCard, Finset.singleton_inj,
    smul_eq_mul, mul_boole, Finset.sum_ite_eq']
  split_ifs with hk <;> [rfl; exact (Finsupp.notMem_support_iff.mp hk).symm]

end Repr

variable {R M N I J : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [LinearOrder I] [Fintype I] [LinearOrder J] [Finite J]

/-- The matrix of an exterior-power map consists of the corresponding minors. -/
@[simp]
theorem toMatrix_exteriorPower_map (b : Basis I R M) (c : Basis J R N) (n : ℕ) (f : M →ₗ[R] N)
    (s : Set.powersetCard J n) (t : Set.powersetCard I n) :
    LinearMap.toMatrix (b.exteriorPower n) (c.exteriorPower n) (exteriorPower.map n f) s t =
      (Matrix.of fun i j : Fin n ↦
        LinearMap.toMatrix b c f (Set.powersetCard.ofFinEmbEquiv.symm s j)
          (Set.powersetCard.ofFinEmbEquiv.symm t i)).det := by
  simp [LinearMap.toMatrix_apply, exteriorPower.basis_repr_apply,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPower.map_apply_ιMulti, exteriorPower.ιMultiDual_apply_ιMulti,
    Basis.coord_apply]

end Module.Basis

namespace RingHom

variable {R S I J : Type*} [CommRing R] [CommRing S] [LinearOrder I] [Fintype I]
  [LinearOrder J] [_root_.Finite J]

/-- Exterior-power matrices commute with a change of coefficient ring. -/
theorem map_toMatrix_exteriorPower (φ : R →+* S) (n : ℕ) (A : Matrix J I R) :
    (LinearMap.toMatrix ((Pi.basisFun R I).exteriorPower n)
      ((Pi.basisFun R J).exteriorPower n) (exteriorPower.map n A.toLin')).map φ =
    LinearMap.toMatrix ((Pi.basisFun S I).exteriorPower n)
      ((Pi.basisFun S J).exteriorPower n) (exteriorPower.map n (A.map φ).toLin') := by
  ext s t
  simp only [Matrix.map_apply, Module.Basis.toMatrix_exteriorPower_map, RingHom.map_det]
  congr 1
  ext
  simp

end RingHom
