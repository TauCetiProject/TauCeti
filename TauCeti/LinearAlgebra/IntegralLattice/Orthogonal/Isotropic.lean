/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Orthogonal.UnitNorm
public import TauCeti.LinearAlgebra.IntegralLattice.RankOne.Basic
import TauCeti.LinearAlgebra.BilinearForm.Even.Basic
import TauCeti.LinearAlgebra.BilinearForm.LinearIndependent
import TauCeti.LinearAlgebra.BilinearForm.Modular

/-!
# Splitting a unimodular lattice at an isotropic vector

Let `L` be a unimodular integral lattice whose rational form is isotropic. Clearing denominators
and dividing by the content gives a primitive isotropic vector `v ∈ L`, and unimodularity gives a
partner `w ∈ L` with `B(v, w) = 1`. The plane spanned by `v` and `w` has Gram matrix
`!![0, 1; 1, B(w, w)]` of determinant `-1`, so it splits off orthogonally. From this:

* if `L` is even, `w` can be corrected to an isotropic vector, the plane is the hyperbolic plane
  `U`, and `L ≅ U ⊕ Y` with `Y` even and unimodular;
* if `L` is odd, then for either sign `ε = ±1` there are orthogonal vectors `u, y ∈ L` with
  `u² = ε` and `y² = -ε`, so `L ≅ ⟨ε⟩ ⊕ Y` with `Y` unimodular and containing a vector of norm
  `-ε`; in particular `Y` is odd again.

These are the integral steps of the classification of indefinite unimodular lattices: the
isotropic vector itself comes from the Hasse–Minkowski theorem, which is not used here. Neither
nondegeneracy beyond unimodularity nor any definiteness is assumed.

## Main results

* `TauCeti.IntegralLattice.exists_isPrimitive_integralNorm_eq_zero`: an isotropic rational form
  has a primitive isotropic lattice vector.
* `TauCeti.IntegralLattice.hyperbolicPlaneSplittingIsometry`: a hyperbolic pair `v, w` splits
  off a copy of `U`, with its orthogonal complement as the second summand.
* `TauCeti.IntegralLattice.IsUnimodular.exists_isometry_hyperbolicPlane_orthogonalSum`: an
  even unimodular lattice with isotropic rational form is `U ⊕ Y` with `Y` even unimodular.
* `TauCeti.IntegralLattice.IsUnimodular.exists_isometry_rankOne_orthogonalSum`: an odd
  unimodular lattice with isotropic rational form is `⟨ε⟩ ⊕ Y`, for either `ε = ±1`, with `Y`
  unimodular and representing `-ε`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter V, §2.2.
* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Chapter II.
-/

public section

open Module TensorProduct Submodule

namespace TauCeti.IntegralLattice

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-! ### Primitive isotropic vectors -/

variable (L : IntegralLattice V)

/-- If the rational form of `L` is isotropic, then `L` contains a primitive isotropic vector. -/
theorem exists_isPrimitive_integralNorm_eq_zero (hiso : ¬ L.norm.Anisotropic) :
    ∃ v : L, IsPrimitive v ∧ L.integralNorm v = 0 := by
  obtain ⟨x, hx, hx₀⟩ : ∃ x : V, L.norm x = 0 ∧ x ≠ 0 := by
    simpa [QuadraticMap.Anisotropic] using hiso
  -- Clear the denominators of `x`, then divide by the content.
  obtain ⟨s, hs, hsx⟩ := Submodule.IsLattice.exists_ne_zero_smul_mem ℚ L.carrier
    Submodule.IsFullLattice.span_eq_top x
  have hsx' : ((⟨s • x, hsx⟩ : L) : V) = (s : ℚ) • x := (Int.cast_smul_eq_zsmul ℚ s x).symm
  have hne : (⟨s • x, hsx⟩ : L) ≠ 0 := by
    intro h
    have h' := congrArg ((↑) : L → V) h
    rw [hsx', ZeroMemClass.coe_zero, smul_eq_zero] at h'
    exact h'.elim (Int.cast_ne_zero.mpr hs) hx₀
  obtain ⟨d, v, hd, hv, hdv⟩ := exists_eq_zsmul_isPrimitive hne
  refine ⟨v, hv, ?_⟩
  apply Int.cast_injective (α := ℚ)
  have hcoe : (s : ℚ) • x = (d : ℚ) • (v : V) := by
    rw [← hsx', hdv, Submodule.coe_smul, Int.cast_smul_eq_zsmul]
  have hnorm : L.norm ((d : ℚ) • (v : V)) = 0 := by
    rw [← hcoe, QuadraticMap.map_smul, hx, smul_zero]
  simpa [integralNorm_apply, integralForm_cast, ← norm_apply, hd.ne'] using hnorm

/-! ### The plane of an isotropic vector and a partner -/

section IsotropicPair

variable {v w : L} (hv : L.integralForm v v = 0) (hvw : L.integralForm v w = 1)
include hv hvw

/-- The Gram matrix of `v, w` is `!![0, 1; 1, w²]`, of determinant `-1`. -/
private theorem integralForm_pair (i j : Fin 2) :
    L.integralForm (![v, w] i) (![v, w] j) = 1 * !![0, 1; 1, L.integralForm w w] i j := by
  have hwv : L.integralForm w v = 1 := by rw [L.isSymm_integralForm.eq w v]; exact hvw
  fin_cases i <;> fin_cases j <;> simp [hv, hvw, hwv]

omit hv hvw in
private theorem isUnit_det_pair : IsUnit !![(0 : ℤ), 1; 1, L.integralForm w w].det := by
  simp [Matrix.det_fin_two_of]

/-- An isotropic vector and a partner pairing to `1` with it are linearly independent. -/
private theorem linearIndependent_pair : LinearIndependent ℤ ![v, w] :=
  LinearMap.BilinForm.linearIndependent_of_isUnit_det (one_mem _) (L.integralForm_pair hv hvw)
    L.isUnit_det_pair

/-- The integral form restricted to the plane spanned by an isotropic vector and a partner is
bijective onto the dual, since its Gram matrix is invertible over `ℤ`. -/
private theorem bijective_restrict_span_pair :
    Function.Bijective (L.integralForm.restrict (span ℤ (Set.range ![v, w]))) :=
  (LinearMap.BilinForm.isModular_one_iff.mp (LinearMap.BilinForm.isModular_restrict_span_range
    (one_mem _) (L.integralForm_pair hv hvw) L.isUnit_det_pair)).bijective_left

end IsotropicPair

/-! ### Splitting off a hyperbolic plane -/

section HyperbolicPair

variable {v w : L} (hv : L.integralForm v v = 0) (hw : L.integralForm w w = 0)
  (hvw : L.integralForm v w = 1)

/-- The integral basis `v, w` of the rationalized span of a hyperbolic pair. -/
private noncomputable def spanPairBasis :
    Basis (Fin 2) ℤ
      (ofIntegralForm (L.integralForm.restrict (span ℤ (Set.range ![v, w])))
        (L.isSymm_integralForm.restrict (span ℤ (Set.range ![v, w])))) :=
  (Basis.span (L.linearIndependent_pair hv hvw)).map (ofIntegralForm.carrierEquiv _ _)

private theorem coe_spanPairBasis (i : Fin 2) :
    (spanPairBasis L hv hvw i : ℚ ⊗[ℤ] span ℤ (Set.range ![v, w])) =
      1 ⊗ₜ[ℤ] (⟨![v, w] i, subset_span (Set.mem_range_self i)⟩ : span ℤ (Set.range ![v, w])) := by
  simp only [spanPairBasis, Basis.map_apply, Basis.span_apply,
    ofIntegralForm.coe_carrierEquiv_apply]

include hw in
private theorem gramMatrix_spanPairBasis :
    (ofIntegralForm (L.integralForm.restrict (span ℤ (Set.range ![v, w])))
      (L.isSymm_integralForm.restrict (span ℤ (Set.range ![v, w])))).gramMatrix
        (spanPairBasis L hv hvw) = !![0, 1; 1, 0] := by
  ext i j
  apply Int.cast_injective (α := ℚ)
  have h := L.integralForm_pair hv hvw i j
  rw [hw] at h
  simp [gramMatrix_apply, integralForm_cast, coe_spanPairBasis, LinearMap.BilinForm.restrict_apply,
    h]

include hw in
/-- The hyperbolic plane is carried onto the rationalized span of a hyperbolic pair, sending the
standard basis to `v, w`. -/
private noncomputable def spanPairIsometry :
    Isometry hyperbolicPlane
      (ofIntegralForm (L.integralForm.restrict (span ℤ (Set.range ![v, w])))
        (L.isSymm_integralForm.restrict (span ℤ (Set.range ![v, w])))) :=
  Isometry.ofGramMatrixEq hyperbolicPlaneBasis (spanPairBasis L hv hvw)
    (by rw [gramMatrix_hyperbolicPlaneBasis, gramMatrix_spanPairBasis L hv hw hvw])

private theorem spanPairIsometry_apply (x : Fin 2 → ℚ) :
    spanPairIsometry L hv hw hvw x =
      x 0 ⊗ₜ[ℤ] (⟨v, subset_span (Set.mem_range_self 0)⟩ : span ℤ (Set.range ![v, w])) +
        x 1 ⊗ₜ[ℤ] (⟨w, subset_span (Set.mem_range_self 1)⟩ : span ℤ (Set.range ![v, w])) := by
  have hx : x = x 0 • ((hyperbolicPlaneBasis 0 : hyperbolicPlane) : Fin 2 → ℚ) +
      x 1 • ((hyperbolicPlaneBasis 1 : hyperbolicPlane) : Fin 2 → ℚ) := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hx]
  simp [-coe_hyperbolicPlaneBasis, spanPairIsometry, Isometry.ofGramMatrixEq_apply_basis,
    coe_spanPairBasis, TensorProduct.smul_tmul']

/-- **Splitting off a hyperbolic plane.** A hyperbolic pair `v, w` of `L`, that is
`v² = w² = 0` and `v · w = 1`, spans a copy of the hyperbolic plane `U`, and `L` is the orthogonal
sum of that copy and the orthogonal complement of the pair, rationalized in its own ambient
space. -/
noncomputable def hyperbolicPlaneSplittingIsometry :
    Isometry
      (hyperbolicPlane.orthogonalSum
        (ofIntegralForm
          (L.integralForm.restrict (L.integralForm.orthogonal (span ℤ (Set.range ![v, w]))))
          (L.isSymm_integralForm.restrict
            (L.integralForm.orthogonal (span ℤ (Set.range ![v, w])))))) L :=
  ((spanPairIsometry L hv hw hvw).orthogonalSum (Isometry.refl _)).trans
    (L.orthogonalSplittingIsometry _ (L.bijective_restrict_span_pair hv hvw))

/-- The hyperbolic splitting sends the standard basis of `U` to `v, w`, and a pure tensor of the
orthogonal complement to its underlying scalar multiple. -/
@[simp]
theorem hyperbolicPlaneSplittingIsometry_apply_tmul (x : Fin 2 → ℚ) (r : ℚ)
    (t : L.integralForm.orthogonal (span ℤ (Set.range ![v, w]))) :
    L.hyperbolicPlaneSplittingIsometry hv hw hvw (x, r ⊗ₜ[ℤ] t) =
      x 0 • (v : V) + x 1 • (w : V) + r • ((t : L) : V) := by
  rw [hyperbolicPlaneSplittingIsometry, Isometry.trans_apply, Isometry.orthogonalSum_apply,
    Isometry.refl_apply, spanPairIsometry_apply,
    show r ⊗ₜ[ℤ] t = r ⊗ₜ[ℤ] t + (0 : ℚ) ⊗ₜ[ℤ] t by simp, ← Prod.mk_add_mk, map_add]
  simp only [orthogonalSplittingIsometry_apply_tmul, zero_smul, add_zero]
  abel

/-- The inverse hyperbolic splitting sends `v` to the first standard basis vector of `U`. -/
@[simp]
theorem hyperbolicPlaneSplittingIsometry_symm_apply_left :
    (L.hyperbolicPlaneSplittingIsometry hv hw hvw).symm (v : V) = (![1, 0], 0) := by
  have h := L.hyperbolicPlaneSplittingIsometry_apply_tmul hv hw hvw ![1, 0] 0 0
  simp only [zero_tmul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    one_smul, zero_smul, add_zero] at h
  rw [← h, Isometry.symm_apply_apply]

/-- The inverse hyperbolic splitting sends `w` to the second standard basis vector of `U`. -/
@[simp]
theorem hyperbolicPlaneSplittingIsometry_symm_apply_right :
    (L.hyperbolicPlaneSplittingIsometry hv hw hvw).symm (w : V) = (![0, 1], 0) := by
  have h := L.hyperbolicPlaneSplittingIsometry_apply_tmul hv hw hvw ![0, 1] 0 0
  simp only [zero_tmul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    one_smul, zero_smul, zero_add, add_zero] at h
  rw [← h, Isometry.symm_apply_apply]

/-- The inverse hyperbolic splitting sends a vector of the orthogonal complement of the pair to its
unit tensor in the second summand. -/
@[simp]
theorem hyperbolicPlaneSplittingIsometry_symm_apply_orthogonal
    (t : L.integralForm.orthogonal (span ℤ (Set.range ![v, w]))) :
    (L.hyperbolicPlaneSplittingIsometry hv hw hvw).symm ((t : L) : V) = (0, 1 ⊗ₜ[ℤ] t) := by
  have h := L.hyperbolicPlaneSplittingIsometry_apply_tmul hv hw hvw 0 1 t
  simp only [Pi.zero_apply, zero_smul, one_smul, zero_add] at h
  rw [← h, Isometry.symm_apply_apply]

end HyperbolicPair

/-! ### The even case -/

/-- **An even unimodular lattice with isotropic rational form splits off a hyperbolic plane.**
It is isometric to `U ⊕ Y`, where `Y` is the rationalized restriction of `L` to some sublattice
`S` and is again even and unimodular. -/
theorem IsUnimodular.exists_isometry_hyperbolicPlane_orthogonalSum {L : IntegralLattice V}
    (hL : L.IsUnimodular) (hE : L.IsEven) (hiso : ¬ L.norm.Anisotropic) :
    ∃ S : Submodule ℤ L,
      (ofIntegralForm (L.integralForm.restrict S) (L.isSymm_integralForm.restrict S)).IsEven ∧
      (ofIntegralForm (L.integralForm.restrict S) (L.isSymm_integralForm.restrict S)).IsUnimodular ∧
      Nonempty (Isometry (hyperbolicPlane.orthogonalSum
        (ofIntegralForm (L.integralForm.restrict S) (L.isSymm_integralForm.restrict S))) L) := by
  obtain ⟨u, hu, huu⟩ := L.exists_isPrimitive_integralNorm_eq_zero hiso
  rw [integralNorm_apply] at huu
  obtain ⟨w, huw⟩ := hL.exists_integralForm_eq_one hu
  obtain ⟨d, hd⟩ := (L.even_integralNorm_iff w).mpr (hE.exists_norm_eq_two_mul w)
  rw [integralNorm_apply, ← two_mul] at hd
  obtain ⟨v, w', hvw, hv, hw⟩ :=
    L.isSymm_integralForm.exists_hyperbolic_of_apply_self_eq_zero huu huw hd
  let e := L.hyperbolicPlaneSplittingIsometry hv hw hvw
  refine ⟨_, ?_, ?_, ⟨e⟩⟩
  · exact ((isEven_orthogonalSum_iff _ _).mp (e.isEven_iff.mpr hE)).2
  · exact ((isUnimodular_orthogonalSum_iff _ _).mp (e.isUnimodular_iff.mpr hL)).2

/-! ### The odd case -/

/-- In an odd lattice, a partner `w` of an isotropic vector `v`, with `v · w = 1`, can be replaced
by one of odd norm: if `w` has even norm, so has the plane spanned by `v` and `w`, and adding to
`w` the component of a vector of odd norm in the orthogonal complement of that plane gives one. -/
private theorem exists_odd_partner (hodd : ¬ L.IsEven) {v w : L} (hvv : L.integralForm v v = 0)
    (hvw : L.integralForm v w = 1) :
    ∃ w' : L, Odd (L.integralForm w' w') ∧ L.integralForm v w' = 1 := by
  obtain ⟨x, hx⟩ : ∃ x : L, ¬ Even (L.integralNorm x) := by
    by_contra h
    push Not at h
    exact hodd (L.isEven_iff_forall_norm.mpr fun x ↦ (L.even_integralNorm_iff x).mp (h x))
  rw [integralNorm_apply, Int.not_even_iff_odd] at hx
  set B := L.integralForm
  have hsymm (x y : L) : B x y = B y x := L.isSymm_integralForm.eq x y
  by_cases hw : Odd (B w w)
  · exact ⟨w, hw, hvw⟩
  rw [Int.not_odd_iff_even] at hw
  -- Decompose `x = p + z` along the plane `P` of `v, w` and its orthogonal complement.
  have hP :=
    L.isCompl_orthogonal_of_restrict_bijective _ (L.bijective_restrict_span_pair hvv hvw)
  obtain ⟨p, hp, z, hz, rfl⟩ := mem_sup.mp (hP.codisjoint.eq_top ▸ mem_top : x ∈ _ ⊔ _)
  obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).mp hp
  have hvz : B v z = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.1 hz) v
    (subset_span (Set.mem_range_self 0))
  have hwz : B w z = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.1 hz) w
    (subset_span (Set.mem_range_self 1))
  refine ⟨w + z, ?_, by simp [hvw, hvz]⟩
  obtain ⟨k, hk⟩ := hw
  have hnorm : B (c 0 • v + c 1 • w + z) (c 0 • v + c 1 • w + z) =
      2 * (c 0 * c 1 + c 1 * c 1 * k) + B z z := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hvz, hwz, hsymm z v, hsymm z w, hvv, hvw, hsymm w v, hk]
    ring
  have hwzwz : B (w + z) (w + z) = 2 * k + B z z := by
    simp only [map_add, LinearMap.add_apply, hwz, hsymm z w, hk]
    ring
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at hx
  rw [hnorm] at hx
  rw [hwzwz]
  exact (even_two_mul k).add_odd ((Int.odd_add'.mp hx).mpr (even_two_mul _))

/-- In an odd unimodular lattice with isotropic rational form, for either sign `ε = ±1` there are
orthogonal vectors `u, y` with `u² = ε` and `y² = -ε`. -/
theorem IsUnimodular.exists_integralForm_eq_and_eq_neg {L : IntegralLattice V}
    (hL : L.IsUnimodular) (hodd : ¬ L.IsEven) (hiso : ¬ L.norm.Anisotropic) {ε : ℤ}
    (hε : IsUnit ε) :
    ∃ u y : L, L.integralForm u u = ε ∧ L.integralForm y y = -ε ∧ L.integralForm u y = 0 := by
  obtain ⟨v, hv, hvv⟩ := L.exists_isPrimitive_integralNorm_eq_zero hiso
  rw [integralNorm_apply] at hvv
  obtain ⟨w, hvw⟩ := hL.exists_integralForm_eq_one hv
  obtain ⟨w', ⟨k, hk⟩, hvw'⟩ := L.exists_odd_partner hodd hvv hvw
  set B := L.integralForm
  have hsymm (x y : L) : B x y = B y x := L.isSymm_integralForm.eq x y
  -- Correct `w'` along `v` to a vector `u` of norm `ε` with `v · u = 1`; then `y = v - ε u`.
  have hεε : ε * ε = 1 := by
    rcases Int.isUnit_iff.mp hε with rfl | rfl <;> norm_num
  obtain ⟨m, hm⟩ : Odd ε := by
    rcases Int.isUnit_iff.mp hε with rfl | rfl <;> decide
  let u := w' + (m - k) • v
  have hwv' : B w' v = 1 := by rw [hsymm]; exact hvw'
  have hvu : B v u = 1 := by simp [u, hvw', hvv]
  have huv : B u v = 1 := by rw [hsymm]; exact hvu
  have huu : B u u = ε := by
    simp only [u, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hk, hvv, hvw', hwv', hm]
    ring
  refine ⟨u, v - ε • u, huu, ?_, ?_⟩
  · simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hvv,
      hvu, huv, huu]
    linear_combination ε * hεε
  · simp only [map_sub, map_smul, smul_eq_mul, huv, huu]
    linear_combination -hεε

/-- **An odd unimodular lattice with isotropic rational form splits off `⟨ε⟩` with odd
complement.** For either sign `ε = ±1` it is isometric to `⟨ε⟩ ⊕ Y`, where `Y` is the
rationalized restriction of `L` to some sublattice `S`, is unimodular, and contains a vector of
norm `-ε`. -/
theorem IsUnimodular.exists_isometry_rankOne_orthogonalSum {L : IntegralLattice V}
    (hL : L.IsUnimodular) (hodd : ¬ L.IsEven) (hiso : ¬ L.norm.Anisotropic) {ε : ℤ}
    (hε : IsUnit ε) :
    ∃ S : Submodule ℤ L,
      (ofIntegralForm (L.integralForm.restrict S) (L.isSymm_integralForm.restrict S)).IsUnimodular ∧
      (∃ y : ofIntegralForm (L.integralForm.restrict S) (L.isSymm_integralForm.restrict S),
        (ofIntegralForm (L.integralForm.restrict S)
          (L.isSymm_integralForm.restrict S)).integralNorm y = -ε) ∧
      Nonempty (Isometry ((rankOne ε).orthogonalSum
        (ofIntegralForm (L.integralForm.restrict S) (L.isSymm_integralForm.restrict S))) L) := by
  obtain ⟨u, y, huu, hyy, huy⟩ := hL.exists_integralForm_eq_and_eq_neg hodd hiso hε
  have hu : IsUnit (L.integralForm u u) := huu ▸ hε
  have e := L.unitNormSplittingIsometry u hu
  rw [ofGramMatrix_singleton_eq_rankOne ε huu] at e
  have hy : y ∈ L.integralForm.orthogonal (ℤ ∙ u) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    obtain ⟨a, rfl⟩ := mem_span_singleton.mp hn
    simp [huy]
  refine ⟨L.integralForm.orthogonal (ℤ ∙ u), ?_, ⟨ofIntegralForm.carrierEquiv _ _ ⟨y, hy⟩, ?_⟩, ⟨e⟩⟩
  · exact ((isUnimodular_orthogonalSum_iff _ _).mp (e.isUnimodular_iff.mpr hL)).2
  · rw [integralNorm_apply, ofIntegralForm.integralForm_carrierEquiv,
      LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply]
    exact hyy

end TauCeti.IntegralLattice
