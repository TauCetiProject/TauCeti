/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeE.CosetMinimum
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E6.MinusculeWeight
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Reflection

/-!
# The 27 minuscule weights as dual vectors of the E₆ lattice

The minuscule weight table of the pinned E₆ root datum uses fundamental-weight coordinates,
whereas the integral root lattice uses simple-root coordinates. Pairing with the simple roots
identifies the literal dual carrier with the weight lattice. This identification realizes the
27 weights as distinct vectors of norm `4/3` in the class of `ϖ₁`. Representatives in the
other nonzero discriminant class can then be obtained by negation.

The realization intertwines the table's simple reflections with lattice root reflections.
Thus the norm and discriminant class are transported along the already checked reflection
paths, without introducing another weight table. The coset minimum theorem proves that all
these representatives are shortest.

Conversely these exhaust the minimizers. A dual vector of squared norm `4/3` pairs with every
simple root to `-1`, `0` or `1`, by positivity at `x ± αᵢ`, and three times its norm is the value
of the integral thrice-inverse Cartan matrix on these pairings. The finite check of the weight
table then identifies it with a minuscule weight or the negative of one. Since the two nonzero
discriminant classes are distinct, the 27 weights are exactly the shortest vectors of the class
of `ϖ₁`, their negatives exactly those of the class of `-ϖ₁`, and there are 54 dual vectors of
squared norm `4/3` in all.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*,
  Chapter 4, §8.3.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate V.

The weight table and reflection paths are those of
`TauCeti.DynkinType.e6MinusculeWeight` and `exists_e6MinusculeReflections_eq`. The exhaustiveness
argument follows the parallel E₇ argument in
`TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeE.Minuscule.E7`, by the Tau Ceti
contributors in https://github.com/TauCetiProject/TauCeti/pull/30755.
-/

public section

namespace TauCeti.IntegralLattice

open Module DynkinType

/-- Pairing with the six simple roots identifies the dual E₆ lattice with the weight lattice
in fundamental-weight coordinates. -/
noncomputable def typeE₆DualWeightEquiv : typeE₆RootLattice.dualCarrier ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  (typeE₆RootLattice.dualCarrierBasis typeE₆SimpleRootBasis).equivFun

/-- The fundamental-weight coordinates of a dual vector are its simple-root pairings. -/
@[simp]
theorem typeE₆DualWeightEquiv_apply (x : typeE₆RootLattice.dualCarrier) (i : Fin 6) :
    (typeE₆DualWeightEquiv x i : ℚ) =
      typeE₆RootLattice.form x (typeE₆SimpleRoot i) := by
  simp only [typeE₆DualWeightEquiv, Basis.equivFun_apply, dualCarrierBasis_repr,
    Basis.dualBasis_repr, dualPairingEquiv_cast, coe_typeE₆SimpleRootBasis_apply]

/-- The minuscule weight table of the E₆ root datum, realized in the literal dual lattice. -/
noncomputable def typeE₆MinusculeDual (a : Fin 27) : typeE₆RootLattice.dualCarrier :=
  typeE₆DualWeightEquiv.symm (e6MinusculeWeight a)

/-- The realized weight has exactly the fundamental coordinates of the pinned weight table. -/
@[simp]
theorem typeE₆DualWeightEquiv_typeE₆MinusculeDual (a : Fin 27) :
    typeE₆DualWeightEquiv (typeE₆MinusculeDual a) = e6MinusculeWeight a :=
  typeE₆DualWeightEquiv.apply_symm_apply _

/-- Pairing a realized minuscule weight with a simple root reads its table entry. -/
@[simp]
theorem form_typeE₆MinusculeDual_typeE₆SimpleRoot (a : Fin 27) (i : Fin 6) :
    typeE₆RootLattice.form (typeE₆MinusculeDual a) (typeE₆SimpleRoot i) =
      (e6MinusculeWeight a i : ℚ) := by
  rw [← typeE₆DualWeightEquiv_apply, typeE₆DualWeightEquiv_typeE₆MinusculeDual]

/-- Distinct table weights give distinct vectors in the literal dual carrier. -/
theorem typeE₆MinusculeDual_injective : Function.Injective typeE₆MinusculeDual := by
  intro a b h
  apply e6MinusculeWeight_injective
  simpa only [typeE₆DualWeightEquiv_typeE₆MinusculeDual] using congrArg typeE₆DualWeightEquiv h

/-- The highest table weight realizes the previously chosen discriminant generator `ϖ₁`. -/
@[simp]
theorem typeE₆MinusculeDual_zero : typeE₆MinusculeDual 0 = typeE₆MinusculeWeightDual := by
  apply typeE₆DualWeightEquiv.injective
  ext i
  apply Int.cast_injective (α := ℚ)
  rw [typeE₆DualWeightEquiv_typeE₆MinusculeDual, typeE₆DualWeightEquiv_apply,
    coe_typeE₆MinusculeWeightDual, form_typeE₆MinusculeWeight_typeE₆SimpleRoot,
    e6MinusculeWeight_zero]
  simp [Pi.single_apply]

private noncomputable def e6SimpleDual (i : Fin 6) : typeE₆RootLattice.dualCarrier :=
  ⟨typeE₆SimpleRootBasis i,
    typeE₆RootLattice.le_dualCarrier (typeE₆SimpleRootBasis i).property⟩

private theorem weight_e6SimpleDual (i : Fin 6) :
    typeE₆DualWeightEquiv (e6SimpleDual i) = CartanMatrix.E 6 i := by
  ext j
  apply Int.cast_injective (α := ℚ)
  rw [typeE₆DualWeightEquiv_apply]
  exact (congrArg (fun x ↦ typeE₆RootLattice.form x (typeE₆SimpleRoot j))
    (coe_typeE₆SimpleRootBasis_apply i)).trans
    (form_typeE₆SimpleRoot_typeE₆SimpleRoot i j)

private theorem minusculeDual_reflection (i : Fin 6) (a : Fin 27) :
    typeE₆MinusculeDual (e6MinusculeReflection i a) =
      typeE₆MinusculeDual a - e6MinusculeWeight a i • e6SimpleDual i := by
  apply typeE₆DualWeightEquiv.injective
  simp only [typeE₆DualWeightEquiv_typeE₆MinusculeDual, map_sub, map_zsmul, weight_e6SimpleDual]
  exact (e6MinusculeWeight_reflection i a).trans
    (by rw [root_e6SimpleIndex])

/-- In simple-root coordinates the table reflection subtracts its coroot value times the
simple root, exactly the lattice root-reflection formula. -/
theorem typeE₆MinusculeDual_reflection (i : Fin 6) (a : Fin 27) :
    (typeE₆MinusculeDual (e6MinusculeReflection i a) : Fin 6 → ℚ) =
      (typeE₆MinusculeDual a : Fin 6 → ℚ) -
        (e6MinusculeWeight a i : ℚ) • typeE₆SimpleRoot i := by
  rw [minusculeDual_reflection]
  simp only [Submodule.coe_sub, SetLike.val_smul, e6SimpleDual,
    coe_typeE₆SimpleRootBasis_apply, Int.cast_smul_eq_zsmul]

/-- Lattice root reflections act on the realized weights by the pinned table reflections. -/
theorem rootReflection_typeE₆MinusculeDual (i : Fin 6) (a : Fin 27) :
    (typeE₆RootLattice.rootReflection (typeE₆SimpleRootBasis i)
      (integralNorm_typeE₆SimpleRootBasis i)) (typeE₆MinusculeDual a) =
        typeE₆MinusculeDual (e6MinusculeReflection i a) := by
  rw [rootReflection_apply, coe_typeE₆SimpleRootBasis_apply, typeE₆RootLattice.isSymm.eq,
    form_typeE₆MinusculeDual_typeE₆SimpleRoot, typeE₆MinusculeDual_reflection]

private theorem norm_minusculeDual_reflection (i : Fin 6) (a : Fin 27) :
    typeE₆RootLattice.form (typeE₆MinusculeDual (e6MinusculeReflection i a))
        (typeE₆MinusculeDual (e6MinusculeReflection i a)) =
      typeE₆RootLattice.form (typeE₆MinusculeDual a) (typeE₆MinusculeDual a) := by
  rw [← rootReflection_typeE₆MinusculeDual]
  exact Isometry.map_app _ _ _

private theorem mk_minusculeDual_reflection (i : Fin 6) (a : Fin 27) :
    (Submodule.Quotient.mk (typeE₆MinusculeDual (e6MinusculeReflection i a)) :
        typeE₆RootLattice.DiscriminantGroup) =
      Submodule.Quotient.mk (typeE₆MinusculeDual a) := by
  have hi : (Submodule.Quotient.mk (e6SimpleDual i) : typeE₆RootLattice.DiscriminantGroup) = 0 :=
    (typeE₆RootLattice.discriminantGroup_mk_eq_zero_iff _).mpr (typeE₆SimpleRootBasis i).property
  simp [minusculeDual_reflection, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, hi]

private theorem minusculeDual_norm_and_class (a : Fin 27) :
    typeE₆RootLattice.form (typeE₆MinusculeDual a) (typeE₆MinusculeDual a) = 4 / 3 ∧
      (Submodule.Quotient.mk (typeE₆MinusculeDual a) : typeE₆RootLattice.DiscriminantGroup) =
        typeE₆MinusculeWeightClass := by
  obtain ⟨l, rfl⟩ := exists_e6MinusculeReflections_eq a
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l i ih =>
      simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil,
        norm_minusculeDual_reflection, mk_minusculeDual_reflection] using ih

/-- All 27 realized weights have squared norm `4/3`. -/
@[simp]
theorem form_typeE₆MinusculeDual_self (a : Fin 27) :
    typeE₆RootLattice.form (typeE₆MinusculeDual a) (typeE₆MinusculeDual a) = 4 / 3 :=
  (minusculeDual_norm_and_class a).1

/-- All 27 realized weights represent the class of `ϖ₁`. -/
@[simp]
theorem mk_typeE₆MinusculeDual (a : Fin 27) :
    (Submodule.Quotient.mk (typeE₆MinusculeDual a) : typeE₆RootLattice.DiscriminantGroup) =
      typeE₆MinusculeWeightClass :=
  (minusculeDual_norm_and_class a).2

/-- Every realized weight is a shortest representative of its discriminant class. -/
theorem form_typeE₆MinusculeDual_self_le (a : Fin 27) (y : typeE₆RootLattice.dualCarrier)
    (hy : (Submodule.Quotient.mk y : typeE₆RootLattice.DiscriminantGroup) =
      Submodule.Quotient.mk (typeE₆MinusculeDual a)) :
    typeE₆RootLattice.form (typeE₆MinusculeDual a) (typeE₆MinusculeDual a) ≤
      typeE₆RootLattice.form y y := by
  rw [form_typeE₆MinusculeDual_self]
  exact isLeast_form_self_typeE₆MinusculeWeightClass.2 ⟨y, hy.trans (mk_typeE₆MinusculeDual a), rfl⟩

/-- The minuscule table realizes 27 distinct dual vectors. -/
theorem ncard_range_typeE₆MinusculeDual : (Set.range typeE₆MinusculeDual).ncard = 27 := by
  simpa using Set.ncard_range_of_injective typeE₆MinusculeDual_injective

/-! ## Exhaustiveness of the shortest dual vectors -/

private theorem simpleRoot_eq_basisFun (i : Fin 6) :
    typeE₆SimpleRoot i = Pi.basisFun ℚ (Fin 6) i := by
  ext j
  simp [typeE₆SimpleRoot_apply, Pi.basisFun_apply, Pi.single_apply]

private theorem form_eq_ofGramMatrix :
    typeE₆RootLattice.form =
      (ofGramMatrix (Pi.basisFun ℚ (Fin 6)) (CartanMatrix.E 6) (CartanMatrix.E_isSymm 6)).form := by
  apply LinearMap.BilinForm.ext_basis (Pi.basisFun ℚ (Fin 6))
  intro i j
  have h := form_typeE₆SimpleRoot_typeE₆SimpleRoot i j
  rw [simpleRoot_eq_basisFun, simpleRoot_eq_basisFun] at h
  exact h.trans (form_ofGramMatrix_basisFun_basisFun _ _ i j).symm

private theorem cartanMatrix_E6_mul_e6ThriceInverse_eq_smul :
    CartanMatrix.E 6 * e6ThriceInverse = (3 : ℤ) • 1 := by
  rw [cartanMatrix_E6_mul_e6ThriceInverse]
  decide

private theorem form_basisFun_eq (x : typeE₆RootLattice.dualCarrier) (i : Fin 6) :
    typeE₆RootLattice.form x (Pi.basisFun ℚ (Fin 6) i) = typeE₆DualWeightEquiv x i := by
  rw [typeE₆DualWeightEquiv_apply, simpleRoot_eq_basisFun]

/-- Rational simple-root coordinates of a dual vector with given fundamental-weight
coordinates are obtained by applying a third of the integral thrice-inverse Cartan matrix. -/
theorem coe_typeE₆DualWeightEquiv_symm_apply (w : Fin 6 → ℤ) (j : Fin 6) :
    (typeE₆DualWeightEquiv.symm w : Fin 6 → ℚ) j =
      (∑ i, (e6ThriceInverse j i : ℚ) * w i) / 3 := by
  refine (apply_eq_sum_mul_form_ofGramMatrix_basisFun_div _ (CartanMatrix.E_isSymm 6)
    cartanMatrix_E6_mul_e6ThriceInverse_eq_smul (by norm_num) _ j).trans ?_
  simp only [← form_eq_ofGramMatrix, form_basisFun_eq, LinearEquiv.apply_symm_apply,
    Int.cast_ofNat]

private theorem three_mul_form_self (x : typeE₆RootLattice.dualCarrier) :
    3 * typeE₆RootLattice.form x x =
      ((∑ i, (∑ j, e6ThriceInverse i j * typeE₆DualWeightEquiv x j) *
        typeE₆DualWeightEquiv x i : ℤ) : ℚ) := by
  have h := intCast_mul_form_ofGramMatrix_basisFun_self _ (CartanMatrix.E_isSymm 6)
    cartanMatrix_E6_mul_e6ThriceInverse_eq_smul (x : Fin 6 → ℚ)
  simp only [← form_eq_ofGramMatrix, form_basisFun_eq] at h
  push_cast
  exact h

private theorem pairing_bounds (x : typeE₆RootLattice.dualCarrier)
    (hx : typeE₆RootLattice.form x x = 4 / 3) (i : Fin 6) :
    -1 ≤ typeE₆DualWeightEquiv x i ∧ typeE₆DualWeightEquiv x i ≤ 1 := by
  -- Cauchy--Schwarz against the simple root `αᵢ`, of norm `2`, bounds the pairing by `8/3`.
  have hcs := LinearMap.BilinForm.apply_sq_le_of_symm typeE₆RootLattice.form
    (fun y ↦ by simpa using isPosDef_typeE₆RootLattice.nonneg y)
    (LinearMap.BilinForm.isSymm_iff.mp typeE₆RootLattice.isSymm)
    (x : Fin 6 → ℚ) (typeE₆SimpleRoot i)
  rw [hx, form_typeE₆SimpleRoot_typeE₆SimpleRoot, CartanMatrix.E_diag,
    ← typeE₆DualWeightEquiv_apply] at hcs
  have h : typeE₆DualWeightEquiv x i * typeE₆DualWeightEquiv x i < 3 := by
    have h : ((typeE₆DualWeightEquiv x i * typeE₆DualWeightEquiv x i : ℤ) : ℚ) < 3 := by
      push_cast
      nlinarith
    exact_mod_cast h
  constructor <;> nlinarith

private theorem mem_range_e6DoubledMinusculeWeight_iff (x : typeE₆RootLattice.dualCarrier) :
    typeE₆DualWeightEquiv x ∈ Set.range e6DoubledMinusculeWeight ↔
      x ∈ Set.range typeE₆MinusculeDual ∨ -x ∈ Set.range typeE₆MinusculeDual := by
  constructor
  · rintro ⟨a | a, h⟩
    · exact .inl ⟨a, typeE₆DualWeightEquiv.injective (by simpa using h)⟩
    · exact .inr ⟨a, typeE₆DualWeightEquiv.injective (by simp [← h])⟩
  · rintro (⟨a, rfl⟩ | ⟨a, ha⟩)
    · exact ⟨.inl a, by simp⟩
    · exact ⟨.inr a, by
        rw [e6DoubledMinusculeWeight_inr, ← typeE₆DualWeightEquiv_typeE₆MinusculeDual, ha,
          map_neg, neg_neg]⟩

/-- **The shortest nonzero dual vectors of `E₆`.** A dual vector has squared norm `4/3` exactly
when it or its negative is one of the 27 realized minuscule weights. -/
theorem form_self_eq_four_thirds_iff_mem_range_typeE₆MinusculeDual_or_neg_mem
    (x : typeE₆RootLattice.dualCarrier) :
    typeE₆RootLattice.form x x = 4 / 3 ↔
      x ∈ Set.range typeE₆MinusculeDual ∨ -x ∈ Set.range typeE₆MinusculeDual := by
  rw [← mem_range_e6DoubledMinusculeWeight_iff]
  constructor
  · intro hx
    refine mem_range_e6DoubledMinusculeWeight_of_bounded_of_quadratic_eq_four _
      (pairing_bounds x hx) ?_
    have h := three_mul_form_self x
    rw [hx, show (3 : ℚ) * (4 / 3) = 4 by norm_num] at h
    exact_mod_cast h.symm
  · intro h
    rcases (mem_range_e6DoubledMinusculeWeight_iff x).mp h with ⟨a, rfl⟩ | ⟨a, ha⟩
    · exact form_typeE₆MinusculeDual_self a
    · rw [← neg_neg x, ← ha]
      simp

private theorem typeE₆MinusculeWeightClass_ne_neg :
    typeE₆MinusculeWeightClass ≠ -typeE₆MinusculeWeightClass := by
  intro h
  have h2 : (2 : ℤ) • typeE₆MinusculeWeightClass = 0 := by
    rw [two_zsmul]
    nth_rw 2 [h]
    exact add_neg_cancel _
  exact absurd ((zsmul_typeE₆MinusculeWeightClass_eq_zero_iff 2).mp h2) (by decide)

/-- **The 27 realized minuscule weights are exactly the shortest representatives of the class
of `ϖ₁`.** -/
theorem form_self_eq_four_thirds_iff_mem_range_typeE₆MinusculeDual
    {x : typeE₆RootLattice.dualCarrier}
    (hx : (Submodule.Quotient.mk x : typeE₆RootLattice.DiscriminantGroup) =
      typeE₆MinusculeWeightClass) :
    typeE₆RootLattice.form x x = 4 / 3 ↔ x ∈ Set.range typeE₆MinusculeDual := by
  rw [form_self_eq_four_thirds_iff_mem_range_typeE₆MinusculeDual_or_neg_mem, or_iff_left]
  rintro ⟨a, ha⟩
  have h := mk_typeE₆MinusculeDual a
  rw [ha, Submodule.Quotient.mk_neg, hx] at h
  exact typeE₆MinusculeWeightClass_ne_neg h.symm

/-- **The negatives of the 27 realized minuscule weights are exactly the shortest
representatives of the class of `-ϖ₁`.** -/
theorem form_self_eq_four_thirds_iff_neg_mem_range_typeE₆MinusculeDual
    {x : typeE₆RootLattice.dualCarrier}
    (hx : (Submodule.Quotient.mk x : typeE₆RootLattice.DiscriminantGroup) =
      -typeE₆MinusculeWeightClass) :
    typeE₆RootLattice.form x x = 4 / 3 ↔ -x ∈ Set.range typeE₆MinusculeDual := by
  rw [form_self_eq_four_thirds_iff_mem_range_typeE₆MinusculeDual_or_neg_mem, or_iff_right]
  rintro ⟨a, rfl⟩
  exact typeE₆MinusculeWeightClass_ne_neg ((mk_typeE₆MinusculeDual a).symm.trans hx)

/-- There are exactly 54 dual vectors of squared norm `4/3`: the 27 realized minuscule weights
and their negatives. -/
theorem ncard_form_self_eq_four_thirds_typeE₆RootLattice :
    {x : typeE₆RootLattice.dualCarrier | typeE₆RootLattice.form x x = 4 / 3}.ncard = 54 := by
  have h : {x : typeE₆RootLattice.dualCarrier | typeE₆RootLattice.form x x = 4 / 3} =
      typeE₆DualWeightEquiv.symm '' Set.range e6DoubledMinusculeWeight := by
    ext x
    rw [Set.mem_ofPred_eq, form_self_eq_four_thirds_iff_mem_range_typeE₆MinusculeDual_or_neg_mem,
      ← mem_range_e6DoubledMinusculeWeight_iff, LinearEquiv.image_symm_eq_preimage,
      Set.mem_preimage]
  rw [h, Set.ncard_image_of_injective _ typeE₆DualWeightEquiv.symm.injective,
    ncard_range_e6DoubledMinusculeWeight]

end TauCeti.IntegralLattice
