/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.GroupTheory.Perm.FinThree.Dihedral
public import TauCeti.LinearAlgebra.SymmetricPower.Basis
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Rational.Dihedral.Three
public import TauCeti.RepresentationTheory.FDRep.Basic
public import TauCeti.RepresentationTheory.Induction.Permutation
public import TauCeti.RepresentationTheory.LinearCharacter.Basic
public import TauCeti.RepresentationTheory.Symmetric.SignCharacter
public import TauCeti.RepresentationTheory.Symmetric.Standard
public import TauCeti.RepresentationTheory.SymmetricPower
import TauCeti.GroupTheory.Perm.FinThree.Basic
import TauCeti.LinearAlgebra.SymmetricPower.Coordinates
import TauCeti.RepresentationTheory.Intertwining

/-!
# Symmetric powers of the standard representation of `S₃`

The symmetric group `S₃` acts on `V₃ = {(z₀, z₁, z₂) : z₀ + z₁ + z₂ = 0}` by
`(g · z)ᵢ = z_{g⁻¹(i)}`; this is `TauCeti.standardRepresentation k (Fin 3)`. Let `ω` be a primitive
cube root of unity in the field `k`, for instance `ω = exp(2πi/3)` in `ℂ`
(`Complex.isPrimitiveRoot_exp`), and let `σ = (0 1)` and `τ = (0 1 2) = finRotate 3`. The vectors

`α = (1, ω, ω²)` and `β = (ω, 1, ω²)`

form a basis of `V₃` in which `τ` is diagonal and `σ` is a permutation:

`τ α = ω² α`, `τ β = ω β`, `σ α = β`, `σ β = α`.

On the symmetric powers this gives the monomial bases `α², αβ, β²` of `Sym² V₃` and
`α³, α²β, αβ², β³` of `Sym³ V₃`, and the explicit equivariant isomorphisms

`1 ⊕ V₃ ≃ Sym² V₃`, `(1, α, β) ↦ (αβ, β², α²)`,

`1 ⊕ sgn ⊕ V₃ ≃ Sym³ V₃`, `(1, 1, α, β) ↦ (α³ + β³, α³ - β³, α²β, αβ²)`.

The second needs `2 ≠ 0` in `k`, to recover `α³` and `β³` from `α³ ± β³`. Both maps are
checked to commute with `σ` and `τ`, which generate `S₃`. In the class order identity,
transposition, `3`-cycle, the characters are `χ_{V₃} = (2, 0, -1)`, `χ_{Sym² V₃} = (3, 1, 0)` and
`χ_{Sym³ V₃} = (4, 0, 1)`, the characters of `1 ⊕ V₃` and `1 ⊕ sgn ⊕ V₃`. These hold over every
field, with no cube root of unity: the traces are computed in the monomial bases built from the
basis `e₀ - e₂`, `e₁ - e₂` of `V₃`. Finally, through the isomorphism
`TauCeti.dihedralGroupThreeMulEquivPerm : DihedralGroup 3 ≃* S₃` sending the rotation `r 1` to `τ`
and the reflection `sr 0` to `σ`, the three rows of the displayed integral character table
`TauCeti.dihedralGroupThreeCharacterTable`, whose columns are the identity, a rotation and a
reflection, are the characters of the trivial, sign and standard representations of `S₃`.

## Main definitions

* `TauCeti.symmetricGroupThreeAlpha`, `TauCeti.symmetricGroupThreeBeta`: the vectors `α` and `β`.
* `TauCeti.symmetricGroupThreeBasis`: the basis `α, β` of the standard module.
* `TauCeti.symmetricGroupThreeSymSqEquiv`: the equivariant isomorphism `1 ⊕ V₃ ≃ Sym² V₃`.
* `TauCeti.symmetricGroupThreeSymCubeEquiv`: the equivariant isomorphism
  `1 ⊕ sgn ⊕ V₃ ≃ Sym³ V₃`.

## Main results

* `TauCeti.standardRepresentation_finRotate_symmetricGroupThreeAlpha` and its three companions:
  the action of `τ` and `σ` on `α` and `β`.
* `TauCeti.symmetricPower_finRotate_tprod_symmetricGroupThreeAlpha` and its two companions: on the
  monomial basis `α², β², αβ` of `Sym² V₃` the eigenvalues of `τ` are `ω, ω², 1`.
* `TauCeti.symmetricGroupThreeSymSqEquiv_apply_one_zero`,
  `TauCeti.symmetricGroupThreeSymCubeEquiv_symm_tprod_alpha` and their companions: the two
  isomorphisms and their inverses on the generators and on the monomials.
* `TauCeti.character_standardRepresentation_one`, `TauCeti.character_standardRepresentation_swap`
  and `TauCeti.character_standardRepresentation_finRotate`: `χ_{V₃} = (2, 0, -1)`.
* `TauCeti.trace_symmetricPower_two_standardRepresentation` and
  `TauCeti.trace_symmetricPower_three_standardRepresentation`: the characters of `Sym² V₃` and
  `Sym³ V₃` are `1 + χ_{V₃}` and `1 + sgn + χ_{V₃}` over every field, with the values `(3, 1, 0)`
  and `(4, 0, 1)` recorded separately.
* `TauCeti.dihedralGroupThreeCharacterTable_eq_character`: the rows of the displayed character
  table are the characters of the trivial, sign and standard representations.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Springer GTM 129 (1991),
  §1.3 and §2.1.
-/

public section

open MonoidAlgebra Module
open scoped TensorProduct

namespace TauCeti

variable {k : Type} [Field k] {ω : k}

/-! ### The eigenbasis of the standard module -/

/-- **The vector `α = (1, ω, ω²)` of the standard module of `S₃`.** Its coordinates sum to zero
because `ω` is a primitive cube root of unity. -/
noncomputable def symmetricGroupThreeAlpha (hω : IsPrimitiveRoot ω 3) :
    (augmentationSubrepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).toSubmodule :=
  ⟨single 0 1 + ω • single 1 1 + ω ^ 2 • single 2 1, by
    rw [toSubmodule_augmentationSubrepresentation, LinearMap.mem_ker]
    simp only [← MonoidAlgebra.basis_apply, map_add, map_smul, Basis.sumCoords_self_apply,
      smul_eq_mul, mul_one]
    simpa [Finset.sum_range_succ] using hω.geom_sum_eq_zero (by norm_num)⟩

/-- **The vector `β = (ω, 1, ω²)` of the standard module of `S₃`**, the image of `α` under the
transposition `(0 1)`. -/
noncomputable def symmetricGroupThreeBeta (hω : IsPrimitiveRoot ω 3) :
    (augmentationSubrepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).toSubmodule :=
  ⟨ω • single 0 1 + single 1 1 + ω ^ 2 • single 2 1, by
    rw [toSubmodule_augmentationSubrepresentation, LinearMap.mem_ker]
    simp only [← MonoidAlgebra.basis_apply, map_add, map_smul, Basis.sumCoords_self_apply,
      smul_eq_mul, mul_one]
    have h : 1 + ω + ω ^ 2 = 0 := by
      simpa [Finset.sum_range_succ] using hω.geom_sum_eq_zero (by norm_num)
    linear_combination h⟩

variable (hω : IsPrimitiveRoot ω 3)

/-- The coordinates of `α`. -/
theorem coe_symmetricGroupThreeAlpha :
    (symmetricGroupThreeAlpha hω : MonoidAlgebra k (Fin 3)) =
      single 0 1 + ω • single 1 1 + ω ^ 2 • single 2 1 :=
  (rfl)

/-- The coordinates of `β`. -/
theorem coe_symmetricGroupThreeBeta :
    (symmetricGroupThreeBeta hω : MonoidAlgebra k (Fin 3)) =
      ω • single 0 1 + single 1 1 + ω ^ 2 • single 2 1 :=
  (rfl)

/-- The action of `τ = (0 1 2)` on the basis vectors of `k[Fin 3]`. -/
private theorem finRotate_three_smul :
    (finRotate 3) • (0 : Fin 3) = 1 ∧ (finRotate 3) • (1 : Fin 3) = 2 ∧
      (finRotate 3) • (2 : Fin 3) = 0 := by
  decide

/-- The action of `σ = (0 1)` on the basis vectors of `k[Fin 3]`. -/
private theorem swap_zero_one_smul :
    Equiv.swap (0 : Fin 3) 1 • (0 : Fin 3) = 1 ∧ Equiv.swap (0 : Fin 3) 1 • (1 : Fin 3) = 0 ∧
      Equiv.swap (0 : Fin 3) 1 • (2 : Fin 3) = 2 := by
  decide

/-- **`τ α = ω² α`.** -/
@[simp]
theorem standardRepresentation_finRotate_symmetricGroupThreeAlpha :
    standardRepresentation k (Fin 3) (finRotate 3) (symmetricGroupThreeAlpha hω) =
      ω ^ 2 • symmetricGroupThreeAlpha hω := by
  rw [← toRepresentation_augmentationSubrepresentation,
    Subrepresentation.toRepresentation_apply_coe]
  obtain ⟨h0, h1, h2⟩ := finRotate_three_smul
  simp only [coe_symmetricGroupThreeAlpha, Submodule.coe_smul, map_add, map_smul,
    Representation.ofMulAction_single, h0, h1, h2]
  linear_combination (norm := module)
    hω.pow_eq_one • (-(single 1 1 + ω • single 2 1) : MonoidAlgebra k (Fin 3))

/-- **`τ β = ω β`.** -/
@[simp]
theorem standardRepresentation_finRotate_symmetricGroupThreeBeta :
    standardRepresentation k (Fin 3) (finRotate 3) (symmetricGroupThreeBeta hω) =
      ω • symmetricGroupThreeBeta hω := by
  rw [← toRepresentation_augmentationSubrepresentation,
    Subrepresentation.toRepresentation_apply_coe]
  obtain ⟨h0, h1, h2⟩ := finRotate_three_smul
  simp only [coe_symmetricGroupThreeBeta, Submodule.coe_smul, map_add, map_smul,
    Representation.ofMulAction_single, h0, h1, h2]
  linear_combination (norm := module)
    hω.pow_eq_one • (-(single 2 1) : MonoidAlgebra k (Fin 3))

/-- **`σ α = β`.** -/
@[simp]
theorem standardRepresentation_swap_symmetricGroupThreeAlpha :
    standardRepresentation k (Fin 3) (Equiv.swap 0 1) (symmetricGroupThreeAlpha hω) =
      symmetricGroupThreeBeta hω := by
  rw [← toRepresentation_augmentationSubrepresentation,
    Subrepresentation.toRepresentation_apply_coe]
  obtain ⟨h0, h1, h2⟩ := swap_zero_one_smul
  simp only [coe_symmetricGroupThreeAlpha, coe_symmetricGroupThreeBeta, map_add, map_smul,
    Representation.ofMulAction_single, h0, h1, h2]
  abel

/-- **`σ β = α`.** -/
@[simp]
theorem standardRepresentation_swap_symmetricGroupThreeBeta :
    standardRepresentation k (Fin 3) (Equiv.swap 0 1) (symmetricGroupThreeBeta hω) =
      symmetricGroupThreeAlpha hω := by
  simpa using (standardRepresentation k (Fin 3)).inv_self_apply (Equiv.swap 0 1)
    (symmetricGroupThreeAlpha hω)

/-- The vectors `α` and `β` are linearly independent. -/
private theorem linearIndependent_symmetricGroupThreeAlpha_beta :
    LinearIndependent k ![symmetricGroupThreeAlpha hω, symmetricGroupThreeBeta hω] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hc : ∀ i : Fin 3, s * (symmetricGroupThreeAlpha hω : MonoidAlgebra k (Fin 3)).coeff i +
      t * (symmetricGroupThreeBeta hω : MonoidAlgebra k (Fin 3)).coeff i = 0 := fun i => by
    simpa using congrArg (fun v : MonoidAlgebra k (Fin 3) => v.coeff i) (Subtype.ext_iff.mp hst)
  have h0 := hc 0
  have h1 := hc 1
  simp only [coe_symmetricGroupThreeAlpha, coe_symmetricGroupThreeBeta, coeff_add, coeff_smul,
    coeff_single, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
    at h0 h1
  norm_num at h0 h1
  have hω2 : 1 - ω ^ 2 ≠ 0 := sub_ne_zero.mpr fun h =>
    hω.pow_ne_one_of_pos_of_lt two_ne_zero (by norm_num) h.symm
  have hs : s * (1 - ω ^ 2) = 0 := by linear_combination h0 - ω * h1
  have hs0 : s = 0 := (mul_eq_zero.mp hs).resolve_right hω2
  refine ⟨hs0, ?_⟩
  simpa [hs0] using h1

/-- **The basis `α, β` of the standard module of `S₃`**, in which `τ = (0 1 2)` is diagonal with
eigenvalues `ω², ω` and `σ = (0 1)` exchanges the two vectors. -/
noncomputable def symmetricGroupThreeBasis :
    Basis (Fin 2) k (augmentationSubrepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).toSubmodule :=
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_symmetricGroupThreeAlpha_beta hω)
    (by rw [finrank_augmentationSubrepresentation]; simp)

/-- The first basis vector is `α`. -/
@[simp]
theorem symmetricGroupThreeBasis_zero :
    symmetricGroupThreeBasis hω 0 = symmetricGroupThreeAlpha hω := by
  simp [symmetricGroupThreeBasis]

/-- The second basis vector is `β`. -/
@[simp]
theorem symmetricGroupThreeBasis_one :
    symmetricGroupThreeBasis hω 1 = symmetricGroupThreeBeta hω := by
  simp [symmetricGroupThreeBasis]

/-- `τ` is diagonal in the basis `α, β`, with eigenvalues `ω², ω`. -/
private theorem standardRepresentation_finRotate_symmetricGroupThreeBasis (i : Fin 2) :
    standardRepresentation k (Fin 3) (finRotate 3) (symmetricGroupThreeBasis hω i) =
      ![ω ^ 2, ω] i • symmetricGroupThreeBasis hω i := by
  fin_cases i <;> simp

/-- `σ` exchanges the two vectors of the basis `α, β`. -/
private theorem standardRepresentation_swap_symmetricGroupThreeBasis (i : Fin 2) :
    standardRepresentation k (Fin 3) (Equiv.swap 0 1) (symmetricGroupThreeBasis hω i) =
      symmetricGroupThreeBasis hω (Equiv.swap 0 1 i) := by
  fin_cases i <;> simp

/-! ### Characters of the standard module

These values hold over every field: the character of the standard module is the number of fixed
points minus one (`TauCeti.char_standardRepresentation`). -/

section Character

/-- **`χ_{V₃}(1) = 2`.** -/
theorem character_standardRepresentation_one (K : Type*) [Field K] :
    (standardRepresentation K (Fin 3)).character 1 = 2 := by
  rw [Representation.char_one, finrank_augmentationSubrepresentation]
  norm_num

/-- **`χ_{V₃}(σ) = 0`** for the transposition `σ = (0 1)`, which fixes one point. -/
theorem character_standardRepresentation_swap (K : Type*) [Field K] :
    (standardRepresentation K (Fin 3)).character (Equiv.swap 0 1) = 0 := by
  rw [char_standardRepresentation, char_ofMulAction, Nat.card_eq_fintype_card,
    show Fintype.card {x : Fin 3 // Equiv.swap (0 : Fin 3) 1 • x = x} = 1 by decide]
  simp

/-- **`χ_{V₃}(τ) = -1`** for the cycle `τ = (0 1 2)`, which fixes no point. -/
theorem character_standardRepresentation_finRotate (K : Type*) [Field K] :
    (standardRepresentation K (Fin 3)).character (finRotate 3) = -1 := by
  rw [char_standardRepresentation, char_ofMulAction, Nat.card_eq_fintype_card,
    show Fintype.card {x : Fin 3 // finRotate 3 • x = x} = 0 by decide]
  simp

end Character

/-! ### The monomial bases of the symmetric powers -/

/-- The basis `α, β` lists `α` and then `β`. -/
theorem coe_symmetricGroupThreeBasis :
    ⇑(symmetricGroupThreeBasis hω) =
      ![symmetricGroupThreeAlpha hω, symmetricGroupThreeBeta hω] := by
  ext i : 1
  fin_cases i <;> simp

/-- The monomial basis vector of `Symⁿ V₃` indexed by the unordered tuple `Sym.ofFn p` is the
pure symmetric tensor of the basis vectors listed by `p`. -/
private theorem symmetricPower_symmetricGroupThreeBasis_ofFn {n : ℕ} {p : Fin n → Fin 2}
    {m : Fin n → (augmentationSubrepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).toSubmodule}
    (hm : ∀ i, ![symmetricGroupThreeAlpha hω, symmetricGroupThreeBeta hω] (p i) = m i) :
    (symmetricGroupThreeBasis hω).symmetricPower n (Sym.ofFn p) = ⨂ₛ[k] i, m i := by
  rw [Module.Basis.symmetricPower_apply, SymmetricPower.tprodOfSym_ofFn,
    coe_symmetricGroupThreeBasis]
  exact congrArg _ (funext hm)

/-- `τ` acts on the monomial basis vector of `Symⁿ V₃` indexed by `Sym.ofFn p` by the product of
the eigenvalues `ω², ω` listed by `p`. -/
private theorem symmetricPower_finRotate_symmetricGroupThreeBasis_ofFn {n : ℕ}
    (p : Fin n → Fin 2) {c : k} (hc : ∏ i, ![ω ^ 2, ω] (p i) = c) :
    (standardRepresentation k (Fin 3)).symmetricPower n (finRotate 3)
        ((symmetricGroupThreeBasis hω).symmetricPower n (Sym.ofFn p)) =
      c • (symmetricGroupThreeBasis hω).symmetricPower n (Sym.ofFn p) := by
  rw [Representation.symmetricPower_apply, (symmetricGroupThreeBasis hω).map_symmetricPower_of_apply
    _ _ (standardRepresentation_finRotate_symmetricGroupThreeBasis hω), TauCeti.Sym.coe_ofFn,
    Multiset.map_coe, Multiset.prod_coe, List.map_ofFn, List.prod_ofFn, Function.comp_def, hc]

/-- `σ` sends the monomial basis vector of `Symⁿ V₃` indexed by `Sym.ofFn p` to the one indexed
by `Sym.ofFn q`, for any `q` listing the indices of `p` with `α` and `β` exchanged. -/
private theorem symmetricPower_swap_symmetricGroupThreeBasis_ofFn {n : ℕ}
    (p q : Fin n → Fin 2)
    (hq : (↑(List.ofFn (Equiv.swap 0 1 ∘ p)) : Multiset (Fin 2)) = ↑(List.ofFn q)) :
    (standardRepresentation k (Fin 3)).symmetricPower n (Equiv.swap 0 1)
        ((symmetricGroupThreeBasis hω).symmetricPower n (Sym.ofFn p)) =
      (symmetricGroupThreeBasis hω).symmetricPower n (Sym.ofFn q) := by
  rw [Representation.symmetricPower_apply,
    (symmetricGroupThreeBasis hω).map_symmetricPower_apply_eq_symmetricPower_map _ _ _
      (standardRepresentation_swap_symmetricGroupThreeBasis hω), TauCeti.Sym.map_ofFn]
  congr 1
  rwa [← Sym.coe_inj, TauCeti.Sym.coe_ofFn, TauCeti.Sym.coe_ofFn]

/-- `τ` scales a pure symmetric tensor of `τ`-eigenvectors by the product of their eigenvalues. -/
private theorem symmetricPower_finRotate_tprod {n : ℕ} {c : Fin n → k}
    {m : Fin n → (augmentationSubrepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).toSubmodule}
    (hm : ∀ i, standardRepresentation k (Fin 3) (finRotate 3) (m i) = c i • m i) :
    (standardRepresentation k (Fin 3)).symmetricPower n (finRotate 3) (⨂ₛ[k] i, m i) =
      (∏ i, c i) • ⨂ₛ[k] i, m i := by
  rw [Representation.symmetricPower_apply_tprod]
  simp_rw [hm]
  exact (SymmetricPower.tprod k).map_smul_univ c m

/-- **`τ α² = ω α²`**: the first eigenvalue of `τ` on the monomial basis `α², β², αβ` of
`Sym² V₃`. -/
theorem symmetricPower_finRotate_tprod_symmetricGroupThreeAlpha :
    (standardRepresentation k (Fin 3)).symmetricPower 2 (finRotate 3)
        (⨂ₛ[k] _ : Fin 2, symmetricGroupThreeAlpha hω) =
      ω • (⨂ₛ[k] _ : Fin 2, symmetricGroupThreeAlpha hω) := by
  rw [symmetricPower_finRotate_tprod (c := fun _ => ω ^ 2) fun _ => by simp]
  congr 1
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  linear_combination ω * hω.pow_eq_one

/-- **`τ β² = ω² β²`**: the second eigenvalue of `τ` on the monomial basis `α², β², αβ` of
`Sym² V₃`. -/
theorem symmetricPower_finRotate_tprod_symmetricGroupThreeBeta :
    (standardRepresentation k (Fin 3)).symmetricPower 2 (finRotate 3)
        (⨂ₛ[k] _ : Fin 2, symmetricGroupThreeBeta hω) =
      ω ^ 2 • (⨂ₛ[k] _ : Fin 2, symmetricGroupThreeBeta hω) := by
  rw [symmetricPower_finRotate_tprod (c := fun _ => ω) fun _ => by simp]
  simp

/-- **`τ (αβ) = αβ`**: the third eigenvalue of `τ` on the monomial basis `α², β², αβ` of
`Sym² V₃` is `1`. -/
theorem symmetricPower_finRotate_tprod_symmetricGroupThreeAlpha_beta :
    (standardRepresentation k (Fin 3)).symmetricPower 2 (finRotate 3)
        (⨂ₛ[k] i, ![symmetricGroupThreeAlpha hω, symmetricGroupThreeBeta hω] i) =
      ⨂ₛ[k] i, ![symmetricGroupThreeAlpha hω, symmetricGroupThreeBeta hω] i := by
  rw [symmetricPower_finRotate_tprod (c := ![ω ^ 2, ω]) fun i => by fin_cases i <;> simp]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← pow_succ, hω.pow_eq_one, one_smul]

/-- An equivalence of representations of `S₃` may be built from a linear equivalence commuting
with the generators `τ = (0 1 2)` and `σ = (0 1)`. -/
private noncomputable def equivOfFinRotateSwap {W W' : Type*} [AddCommMonoid W] [Module k W]
    [AddCommMonoid W'] [Module k W'] {π : Representation k (Equiv.Perm (Fin 3)) W}
    {π' : Representation k (Equiv.Perm (Fin 3)) W'} (f : W ≃ₗ[k] W')
    (hτ : ∀ v, f (π (finRotate 3) v) = π' (finRotate 3) (f v))
    (hσ : ∀ v, f (π (Equiv.swap 0 1) v) = π' (Equiv.swap 0 1) (f v)) : π.Equiv π' :=
  .mk f fun g => LinearMap.ext
    (((Representation.isIntertwiningMap_iff_of_closure_eq_top π π'
      closure_finRotate_three_swap_eq_top f.toLinearMap).2
        (by rintro g (rfl | rfl); exacts [hτ, hσ])).isIntertwining g)

/-! ### The symmetric square: `1 ⊕ V₃ ≃ Sym² V₃` -/

/-- The linear map `1 ⊕ V₃ → Sym² V₃` sending the generator of the trivial line to `αβ`, and `α`
and `β` to `β²` and `α²`. -/
private noncomputable def symSqMap :
    k × (augmentationSubrepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).toSubmodule →ₗ[k]
      Sym[k]^2 (augmentationSubrepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).toSubmodule :=
  (LinearMap.toSpanSingleton k _ ((symmetricGroupThreeBasis hω).symmetricPower 2
      (Sym.ofFn ![0, 1]))).coprod
    ((symmetricGroupThreeBasis hω).constr k
      ![(symmetricGroupThreeBasis hω).symmetricPower 2 (Sym.ofFn ![1, 1]),
        (symmetricGroupThreeBasis hω).symmetricPower 2 (Sym.ofFn ![0, 0])])

private theorem symSqMap_inl (c : k) :
    symSqMap hω (c, 0) = c • (symmetricGroupThreeBasis hω).symmetricPower 2 (Sym.ofFn ![0, 1]) := by
  simp [symSqMap]

private theorem symSqMap_zero_smul (c : k)
    (v : (augmentationSubrepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).toSubmodule) :
    symSqMap hω (0, c • v) = c • symSqMap hω (0, v) := by
  rw [← map_smul, Prod.smul_mk, smul_zero]

private theorem symSqMap_alpha :
    symSqMap hω (0, symmetricGroupThreeAlpha hω) =
      (symmetricGroupThreeBasis hω).symmetricPower 2 (Sym.ofFn ![1, 1]) := by
  simp [symSqMap, ← symmetricGroupThreeBasis_zero hω, -symmetricGroupThreeBasis_zero]

private theorem symSqMap_beta :
    symSqMap hω (0, symmetricGroupThreeBeta hω) =
      (symmetricGroupThreeBasis hω).symmetricPower 2 (Sym.ofFn ![0, 0]) := by
  simp [symSqMap, ← symmetricGroupThreeBasis_one hω, -symmetricGroupThreeBasis_one]

private theorem symSqMap_surjective : Function.Surjective (symSqMap hω) := by
  rw [← LinearMap.range_eq_top, eq_top_iff,
    ← ((symmetricGroupThreeBasis hω).symmetricPower 2).span_eq, Submodule.span_le]
  rintro _ ⟨s, rfl⟩
  have hs : s = Sym.ofFn ![0, 0] ∨ s = Sym.ofFn ![0, 1] ∨ s = Sym.ofFn ![1, 1] := by
    obtain ⟨p, rfl⟩ := TauCeti.Sym.ofFn_surjective s
    simp only [← Sym.coe_inj, TauCeti.Sym.coe_ofFn]
    revert p; decide
  rcases hs with rfl | rfl | rfl
  · exact ⟨(0, symmetricGroupThreeBeta hω), symSqMap_beta hω⟩
  · exact ⟨(1, 0), by rw [symSqMap_inl, one_smul]⟩
  · exact ⟨(0, symmetricGroupThreeAlpha hω), symSqMap_alpha hω⟩

private theorem symSqMap_bijective : Function.Bijective (symSqMap hω) := by
  -- The codomain is named explicitly: unifying it through `symSqMap` would have to identify the
  -- additive monoid structure of the symmetric power with the one underlying its additive group.
  refine ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (V₂ := Sym[k]^2 (augmentationSubrepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).toSubmodule)
    ?_ (f := symSqMap hω)).2 (symSqMap_surjective hω), symSqMap_surjective hω⟩
  rw [Module.finrank_prod, SymmetricPower.finrank_eq, finrank_augmentationSubrepresentation]
  simp [Nat.multichoose_eq]

/-- `symSqMap` commutes with `τ` and with `σ`. -/
private theorem symSqMap_comp {g : Equiv.Perm (Fin 3)}
    (hg : g = finRotate 3 ∨ g = Equiv.swap 0 1) :
    symSqMap hω ∘ₗ ((Representation.trivial k (Equiv.Perm (Fin 3)) k).prod
        (standardRepresentation k (Fin 3))) g =
      (standardRepresentation k (Fin 3)).symmetricPower 2 g ∘ₗ symSqMap hω := by
  have h3 := hω.pow_eq_one
  have τ01 := symmetricPower_finRotate_symmetricGroupThreeBasis_ofFn hω ![0, 1]
    (c := 1) (by simp [h3, ← pow_succ])
  have τ11 := symmetricPower_finRotate_symmetricGroupThreeBasis_ofFn hω ![1, 1]
    (c := ω ^ 2) (by simp [sq])
  have τ00 := symmetricPower_finRotate_symmetricGroupThreeBasis_ofFn hω ![0, 0]
    (c := ω) (by simp; linear_combination ω * h3)
  have σ01 := symmetricPower_swap_symmetricGroupThreeBasis_ofFn hω ![0, 1] ![0, 1] (by decide)
  have σ11 := symmetricPower_swap_symmetricGroupThreeBasis_ofFn hω ![1, 1] ![0, 0] (by decide)
  have σ00 := symmetricPower_swap_symmetricGroupThreeBasis_ofFn hω ![0, 0] ![1, 1] (by decide)
  refine LinearMap.prod_ext (LinearMap.ext_ring ?_) ((symmetricGroupThreeBasis hω).ext fun i => ?_)
  · rcases hg with rfl | rfl <;>
      simp only [LinearMap.comp_apply, LinearMap.inl_apply, Representation.prod_apply_apply,
        Representation.trivial_apply, map_zero, symSqMap_inl, one_smul, τ01, σ01]
  · rcases hg with rfl | rfl <;> fin_cases i <;>
      simp only [Fin.zero_eta, Fin.mk_one, symmetricGroupThreeBasis_zero,
        symmetricGroupThreeBasis_one, LinearMap.comp_apply, LinearMap.inr_apply,
        Representation.prod_apply_apply, map_zero,
        standardRepresentation_finRotate_symmetricGroupThreeAlpha,
        standardRepresentation_finRotate_symmetricGroupThreeBeta,
        standardRepresentation_swap_symmetricGroupThreeAlpha,
        standardRepresentation_swap_symmetricGroupThreeBeta, symSqMap_zero_smul,
        symSqMap_alpha, symSqMap_beta, τ11, τ00, σ11, σ00]

/-- **`1 ⊕ V₃ ≃ Sym² V₃`.** The equivariant isomorphism from the sum of the trivial and the
standard representation of `S₃` to the symmetric square of the standard representation, sending
the generator `1` of the trivial line to `αβ`, and `α` and `β` to `β²` and `α²`. So the symmetric
square is the sum of the trivial line spanned by `αβ` and a copy of the standard representation
spanned by `α²` and `β²`. -/
noncomputable def symmetricGroupThreeSymSqEquiv :
    ((Representation.trivial k (Equiv.Perm (Fin 3)) k).prod
      (standardRepresentation k (Fin 3))).Equiv
      ((standardRepresentation k (Fin 3)).symmetricPower 2) :=
  equivOfFinRotateSwap (LinearEquiv.ofBijective (symSqMap hω) (symSqMap_bijective hω))
    (LinearMap.congr_fun (symSqMap_comp hω (.inl rfl)))
    (LinearMap.congr_fun (symSqMap_comp hω (.inr rfl)))

private theorem symmetricGroupThreeSymSqEquiv_apply
    (v : k × (augmentationSubrepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).toSubmodule) :
    symmetricGroupThreeSymSqEquiv hω v = symSqMap hω v :=
  (rfl)

/-- **`1 ↦ αβ`.** -/
@[simp]
theorem symmetricGroupThreeSymSqEquiv_apply_one_zero :
    symmetricGroupThreeSymSqEquiv hω (1, 0) =
      ⨂ₛ[k] i, ![symmetricGroupThreeAlpha hω, symmetricGroupThreeBeta hω] i := by
  rw [symmetricGroupThreeSymSqEquiv_apply, symSqMap_inl, one_smul]
  exact symmetricPower_symmetricGroupThreeBasis_ofFn hω fun i => by fin_cases i <;> rfl

/-- **`α ↦ β²`.** -/
@[simp]
theorem symmetricGroupThreeSymSqEquiv_apply_zero_alpha :
    symmetricGroupThreeSymSqEquiv hω (0, symmetricGroupThreeAlpha hω) =
      ⨂ₛ[k] _ : Fin 2, symmetricGroupThreeBeta hω := by
  rw [symmetricGroupThreeSymSqEquiv_apply, symSqMap_alpha]
  exact symmetricPower_symmetricGroupThreeBasis_ofFn hω fun i => by fin_cases i <;> rfl

/-- **`β ↦ α²`.** -/
@[simp]
theorem symmetricGroupThreeSymSqEquiv_apply_zero_beta :
    symmetricGroupThreeSymSqEquiv hω (0, symmetricGroupThreeBeta hω) =
      ⨂ₛ[k] _ : Fin 2, symmetricGroupThreeAlpha hω := by
  rw [symmetricGroupThreeSymSqEquiv_apply, symSqMap_beta]
  exact symmetricPower_symmetricGroupThreeBasis_ofFn hω fun i => by fin_cases i <;> rfl

/-- The inverse of `1 ⊕ V₃ ≃ Sym² V₃` sends `αβ` to the generator `1` of the trivial line. -/
@[simp]
theorem symmetricGroupThreeSymSqEquiv_symm_tprod_alpha_beta :
    (symmetricGroupThreeSymSqEquiv hω).symm
        (⨂ₛ[k] i, ![symmetricGroupThreeAlpha hω, symmetricGroupThreeBeta hω] i) = (1, 0) := by
  rw [← symmetricGroupThreeSymSqEquiv_apply_one_zero, Representation.Equiv.symm_apply_apply]

/-- The inverse of `1 ⊕ V₃ ≃ Sym² V₃` sends `α²` to `β`. -/
@[simp]
theorem symmetricGroupThreeSymSqEquiv_symm_tprod_alpha :
    (symmetricGroupThreeSymSqEquiv hω).symm (⨂ₛ[k] _ : Fin 2, symmetricGroupThreeAlpha hω) =
      (0, symmetricGroupThreeBeta hω) := by
  rw [← symmetricGroupThreeSymSqEquiv_apply_zero_beta, Representation.Equiv.symm_apply_apply]

/-- The inverse of `1 ⊕ V₃ ≃ Sym² V₃` sends `β²` to `α`. -/
@[simp]
theorem symmetricGroupThreeSymSqEquiv_symm_tprod_beta :
    (symmetricGroupThreeSymSqEquiv hω).symm (⨂ₛ[k] _ : Fin 2, symmetricGroupThreeBeta hω) =
      (0, symmetricGroupThreeAlpha hω) := by
  rw [← symmetricGroupThreeSymSqEquiv_apply_zero_alpha, Representation.Equiv.symm_apply_apply]

/-! ### The symmetric cube: `1 ⊕ sgn ⊕ V₃ ≃ Sym³ V₃` -/

/-- The linear map `1 ⊕ sgn ⊕ V₃ → Sym³ V₃` sending the generators of the trivial and sign lines to
`α³ + β³` and `α³ - β³`, and `α` and `β` to `α²β` and `αβ²`. -/
private noncomputable def symCubeMap :
    k × k × (augmentationSubrepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).toSubmodule →ₗ[k]
      Sym[k]^3 (augmentationSubrepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).toSubmodule :=
  (LinearMap.toSpanSingleton k _
      ((symmetricGroupThreeBasis hω).symmetricPower 3 (Sym.ofFn ![0, 0, 0]) +
        (symmetricGroupThreeBasis hω).symmetricPower 3 (Sym.ofFn ![1, 1, 1]))).coprod
    ((LinearMap.toSpanSingleton k _
      ((symmetricGroupThreeBasis hω).symmetricPower 3 (Sym.ofFn ![0, 0, 0]) -
        (symmetricGroupThreeBasis hω).symmetricPower 3 (Sym.ofFn ![1, 1, 1]))).coprod
      ((symmetricGroupThreeBasis hω).constr k
        ![(symmetricGroupThreeBasis hω).symmetricPower 3 (Sym.ofFn ![0, 0, 1]),
          (symmetricGroupThreeBasis hω).symmetricPower 3 (Sym.ofFn ![0, 1, 1])]))

private theorem symCubeMap_trivial (c : k) :
    symCubeMap hω (c, 0) =
      c • ((symmetricGroupThreeBasis hω).symmetricPower 3 (Sym.ofFn ![0, 0, 0]) +
        (symmetricGroupThreeBasis hω).symmetricPower 3 (Sym.ofFn ![1, 1, 1])) := by
  simp [symCubeMap]

private theorem symCubeMap_sign (c : k) :
    symCubeMap hω (0, c, 0) =
      c • ((symmetricGroupThreeBasis hω).symmetricPower 3 (Sym.ofFn ![0, 0, 0]) -
        (symmetricGroupThreeBasis hω).symmetricPower 3 (Sym.ofFn ![1, 1, 1])) := by
  simp [symCubeMap]

private theorem symCubeMap_zero_smul (c : k)
    (v : (augmentationSubrepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).toSubmodule) :
    symCubeMap hω (0, 0, c • v) = c • symCubeMap hω (0, 0, v) := by
  rw [← map_smul, Prod.smul_mk, Prod.smul_mk, smul_zero]

private theorem symCubeMap_alpha :
    symCubeMap hω (0, 0, symmetricGroupThreeAlpha hω) =
      (symmetricGroupThreeBasis hω).symmetricPower 3 (Sym.ofFn ![0, 0, 1]) := by
  simp [symCubeMap, ← symmetricGroupThreeBasis_zero hω, -symmetricGroupThreeBasis_zero]

private theorem symCubeMap_beta :
    symCubeMap hω (0, 0, symmetricGroupThreeBeta hω) =
      (symmetricGroupThreeBasis hω).symmetricPower 3 (Sym.ofFn ![0, 1, 1]) := by
  simp [symCubeMap, ← symmetricGroupThreeBasis_one hω, -symmetricGroupThreeBasis_one]

/-- `α³` and `β³` are the images of `(1/2, 1/2, 0)` and `(1/2, -1/2, 0)`: half the sum and half
the difference of `α³ + β³` and `α³ - β³`. -/
private theorem symCubeMap_inv_two (h2 : (2 : k) ≠ 0) :
    symCubeMap hω (2⁻¹, 2⁻¹, 0) =
        (symmetricGroupThreeBasis hω).symmetricPower 3 (Sym.ofFn ![0, 0, 0]) ∧
      symCubeMap hω (2⁻¹, -2⁻¹, 0) =
        (symmetricGroupThreeBasis hω).symmetricPower 3 (Sym.ofFn ![1, 1, 1]) := by
  have hsplit (a b : k) :
      symCubeMap hω (a, b, 0) = symCubeMap hω (a, 0) + symCubeMap hω (0, b, 0) := by
    rw [← map_add]
    simp
  -- The identities `x = (x + y) / 2 + (x - y) / 2` and `y = (x + y) / 2 - (x - y) / 2`, stated in
  -- an arbitrary vector space so that they are not elaborated against the additive monoid
  -- structure of the symmetric power.
  have hhalf : ∀ {W : Type} [AddCommGroup W] [Module k W] (x y : W),
      (2 : k)⁻¹ • (x + y) + (2 : k)⁻¹ • (x - y) = x ∧
        (2 : k)⁻¹ • (x + y) + (-(2 : k)⁻¹) • (x - y) = y := by
    intro W _ _ x y
    constructor
    · rw [← smul_add, show x + y + (x - y) = (2 : k) • x by rw [two_smul]; abel,
        inv_smul_smul₀ h2]
    · rw [neg_smul, ← sub_eq_add_neg, ← smul_sub,
        show x + y - (x - y) = (2 : k) • y by rw [two_smul]; abel, inv_smul_smul₀ h2]
  have h := hhalf
    (W := Sym[k]^3 (augmentationSubrepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).toSubmodule)
    ((symmetricGroupThreeBasis hω).symmetricPower 3 (Sym.ofFn ![0, 0, 0]))
    ((symmetricGroupThreeBasis hω).symmetricPower 3 (Sym.ofFn ![1, 1, 1]))
  constructor <;> rw [hsplit, symCubeMap_trivial, symCubeMap_sign]
  exacts [h.1, h.2]

private theorem symCubeMap_surjective (h2 : (2 : k) ≠ 0) : Function.Surjective (symCubeMap hω) := by
  rw [← LinearMap.range_eq_top, eq_top_iff,
    ← ((symmetricGroupThreeBasis hω).symmetricPower 3).span_eq, Submodule.span_le]
  rintro _ ⟨s, rfl⟩
  have hs : s = Sym.ofFn ![0, 0, 0] ∨ s = Sym.ofFn ![0, 0, 1] ∨ s = Sym.ofFn ![0, 1, 1] ∨
      s = Sym.ofFn ![1, 1, 1] := by
    obtain ⟨p, rfl⟩ := TauCeti.Sym.ofFn_surjective s
    simp only [← Sym.coe_inj, TauCeti.Sym.coe_ofFn]
    revert p; decide
  rcases hs with rfl | rfl | rfl | rfl
  · exact ⟨_, (symCubeMap_inv_two hω h2).1⟩
  · exact ⟨(0, 0, symmetricGroupThreeAlpha hω), symCubeMap_alpha hω⟩
  · exact ⟨(0, 0, symmetricGroupThreeBeta hω), symCubeMap_beta hω⟩
  · exact ⟨_, (symCubeMap_inv_two hω h2).2⟩

private theorem symCubeMap_bijective (h2 : (2 : k) ≠ 0) : Function.Bijective (symCubeMap hω) := by
  -- The codomain is named explicitly, as in `symSqMap_bijective`.
  refine ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (V₂ := Sym[k]^3 (augmentationSubrepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).toSubmodule)
    ?_ (f := symCubeMap hω)).2 (symCubeMap_surjective hω h2), symCubeMap_surjective hω h2⟩
  rw [Module.finrank_prod, Module.finrank_prod, SymmetricPower.finrank_eq,
    finrank_augmentationSubrepresentation]
  simp [Nat.multichoose_eq]

/-- The sign of `τ = (0 1 2)` is `1`. -/
private theorem coe_signLinearCharacter_finRotate :
    ((signLinearCharacter k (Fin 3) (finRotate 3) : kˣ) : k) = 1 := by
  rw [coe_signLinearCharacter_apply, sign_finRotate]
  norm_num

/-- The sign of `σ = (0 1)` is `-1`. -/
private theorem coe_signLinearCharacter_swap :
    ((signLinearCharacter k (Fin 3) (Equiv.swap 0 1) : kˣ) : k) = -1 := by
  rw [signLinearCharacter_swap (by decide), Units.val_neg, Units.val_one]

/-- `symCubeMap` commutes with `τ` and with `σ`. -/
private theorem symCubeMap_comp {g : Equiv.Perm (Fin 3)}
    (hg : g = finRotate 3 ∨ g = Equiv.swap 0 1) :
    symCubeMap hω ∘ₗ ((Representation.trivial k (Equiv.Perm (Fin 3)) k).prod
        ((Representation.ofLinearCharacter (signLinearCharacter k (Fin 3))).prod
          (standardRepresentation k (Fin 3)))) g =
      (standardRepresentation k (Fin 3)).symmetricPower 3 g ∘ₗ symCubeMap hω := by
  have h3 := hω.pow_eq_one
  have τ000 := symmetricPower_finRotate_symmetricGroupThreeBasis_ofFn hω ![0, 0, 0]
    (c := 1) (by simp [Fin.prod_univ_three]; linear_combination (ω ^ 3 + 1) * h3)
  have τ111 := symmetricPower_finRotate_symmetricGroupThreeBasis_ofFn hω ![1, 1, 1]
    (c := 1) (by simp [Fin.prod_univ_three]; linear_combination h3)
  have τ001 := symmetricPower_finRotate_symmetricGroupThreeBasis_ofFn hω ![0, 0, 1]
    (c := ω ^ 2) (by simp [Fin.prod_univ_three]; linear_combination ω ^ 2 * h3)
  have τ011 := symmetricPower_finRotate_symmetricGroupThreeBasis_ofFn hω ![0, 1, 1]
    (c := ω) (by simp [Fin.prod_univ_three]; linear_combination ω * h3)
  have σ000 := symmetricPower_swap_symmetricGroupThreeBasis_ofFn hω ![0, 0, 0] ![1, 1, 1]
    (by decide)
  have σ111 := symmetricPower_swap_symmetricGroupThreeBasis_ofFn hω ![1, 1, 1] ![0, 0, 0]
    (by decide)
  have σ001 := symmetricPower_swap_symmetricGroupThreeBasis_ofFn hω ![0, 0, 1] ![0, 1, 1]
    (by decide)
  have σ011 := symmetricPower_swap_symmetricGroupThreeBasis_ofFn hω ![0, 1, 1] ![0, 0, 1]
    (by decide)
  refine LinearMap.prod_ext (LinearMap.ext_ring ?_) (LinearMap.prod_ext (LinearMap.ext_ring ?_)
    ((symmetricGroupThreeBasis hω).ext fun i => ?_))
  · rcases hg with rfl | rfl <;>
      simp only [LinearMap.comp_apply, LinearMap.inl_apply, Representation.prod_apply_apply,
        Representation.trivial_apply, map_zero, symCubeMap_trivial, one_smul, map_add, τ000,
        τ111, σ000, σ111]
    exact add_comm _ _
  · rcases hg with rfl | rfl <;>
      simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply,
        Representation.prod_apply_apply, Representation.ofLinearCharacter_apply,
        coe_signLinearCharacter_finRotate, coe_signLinearCharacter_swap, map_zero,
        symCubeMap_sign, mul_one, one_smul, map_sub, τ000, τ111, σ000, σ111]
    exact (neg_one_smul k _).trans (neg_sub _ _)
  · rcases hg with rfl | rfl <;> fin_cases i <;>
      simp only [Fin.zero_eta, Fin.mk_one, symmetricGroupThreeBasis_zero,
        symmetricGroupThreeBasis_one, LinearMap.comp_apply, LinearMap.inr_apply,
        Representation.prod_apply_apply, map_zero,
        standardRepresentation_finRotate_symmetricGroupThreeAlpha,
        standardRepresentation_finRotate_symmetricGroupThreeBeta,
        standardRepresentation_swap_symmetricGroupThreeAlpha,
        standardRepresentation_swap_symmetricGroupThreeBeta, symCubeMap_zero_smul,
        symCubeMap_alpha, symCubeMap_beta, τ001, τ011, σ001, σ011]

/-- **`1 ⊕ sgn ⊕ V₃ ≃ Sym³ V₃`.** When `2 ≠ 0` in `k`, the equivariant isomorphism from the sum of
the trivial, the sign and the standard representation of `S₃` to the symmetric cube of the
standard representation, sending the generators of the trivial and sign lines to `α³ + β³` and
`α³ - β³`, and `α` and `β` to `α²β` and `αβ²`. -/
noncomputable def symmetricGroupThreeSymCubeEquiv (h2 : (2 : k) ≠ 0) :
    ((Representation.trivial k (Equiv.Perm (Fin 3)) k).prod
      ((Representation.ofLinearCharacter (signLinearCharacter k (Fin 3))).prod
        (standardRepresentation k (Fin 3)))).Equiv
      ((standardRepresentation k (Fin 3)).symmetricPower 3) :=
  equivOfFinRotateSwap (LinearEquiv.ofBijective (symCubeMap hω) (symCubeMap_bijective hω h2))
    (LinearMap.congr_fun (symCubeMap_comp hω (.inl rfl)))
    (LinearMap.congr_fun (symCubeMap_comp hω (.inr rfl)))

private theorem symmetricGroupThreeSymCubeEquiv_apply (h2 : (2 : k) ≠ 0)
    (v : k × k × (augmentationSubrepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).toSubmodule) :
    symmetricGroupThreeSymCubeEquiv hω h2 v = symCubeMap hω v :=
  (rfl)

/-- The basis vector `α³` of the monomial basis of `Sym³ V₃`, as a pure tensor. -/
private theorem symmetricPower_symmetricGroupThreeBasis_three_alpha :
    (symmetricGroupThreeBasis hω).symmetricPower 3 (Sym.ofFn ![0, 0, 0]) =
      ⨂ₛ[k] _ : Fin 3, symmetricGroupThreeAlpha hω :=
  symmetricPower_symmetricGroupThreeBasis_ofFn hω fun i => by fin_cases i <;> rfl

/-- The basis vector `β³` of the monomial basis of `Sym³ V₃`, as a pure tensor. -/
private theorem symmetricPower_symmetricGroupThreeBasis_three_beta :
    (symmetricGroupThreeBasis hω).symmetricPower 3 (Sym.ofFn ![1, 1, 1]) =
      ⨂ₛ[k] _ : Fin 3, symmetricGroupThreeBeta hω :=
  symmetricPower_symmetricGroupThreeBasis_ofFn hω fun i => by fin_cases i <;> rfl

/-- **`1 ↦ α³ + β³`.** -/
@[simp]
theorem symmetricGroupThreeSymCubeEquiv_apply_one_zero (h2 : (2 : k) ≠ 0) :
    symmetricGroupThreeSymCubeEquiv hω h2 (1, 0) =
      (⨂ₛ[k] _ : Fin 3, symmetricGroupThreeAlpha hω) +
        ⨂ₛ[k] _ : Fin 3, symmetricGroupThreeBeta hω := by
  rw [symmetricGroupThreeSymCubeEquiv_apply, symCubeMap_trivial, one_smul,
    symmetricPower_symmetricGroupThreeBasis_three_alpha,
    symmetricPower_symmetricGroupThreeBasis_three_beta]

/-- **`sgn ↦ α³ - β³`**: the generator of the sign line goes to `α³ - β³`. -/
@[simp]
theorem symmetricGroupThreeSymCubeEquiv_apply_zero_one_zero (h2 : (2 : k) ≠ 0) :
    symmetricGroupThreeSymCubeEquiv hω h2 (0, 1, 0) =
      (⨂ₛ[k] _ : Fin 3, symmetricGroupThreeAlpha hω) -
        ⨂ₛ[k] _ : Fin 3, symmetricGroupThreeBeta hω := by
  rw [symmetricGroupThreeSymCubeEquiv_apply, symCubeMap_sign, one_smul,
    symmetricPower_symmetricGroupThreeBasis_three_alpha,
    symmetricPower_symmetricGroupThreeBasis_three_beta]

/-- **`α ↦ α²β`.** -/
@[simp]
theorem symmetricGroupThreeSymCubeEquiv_apply_zero_zero_alpha (h2 : (2 : k) ≠ 0) :
    symmetricGroupThreeSymCubeEquiv hω h2 (0, 0, symmetricGroupThreeAlpha hω) =
      ⨂ₛ[k] i, ![symmetricGroupThreeAlpha hω, symmetricGroupThreeAlpha hω,
        symmetricGroupThreeBeta hω] i := by
  rw [symmetricGroupThreeSymCubeEquiv_apply, symCubeMap_alpha]
  exact symmetricPower_symmetricGroupThreeBasis_ofFn hω fun i => by fin_cases i <;> rfl

/-- **`β ↦ αβ²`.** -/
@[simp]
theorem symmetricGroupThreeSymCubeEquiv_apply_zero_zero_beta (h2 : (2 : k) ≠ 0) :
    symmetricGroupThreeSymCubeEquiv hω h2 (0, 0, symmetricGroupThreeBeta hω) =
      ⨂ₛ[k] i, ![symmetricGroupThreeAlpha hω, symmetricGroupThreeBeta hω,
        symmetricGroupThreeBeta hω] i := by
  rw [symmetricGroupThreeSymCubeEquiv_apply, symCubeMap_beta]
  exact symmetricPower_symmetricGroupThreeBasis_ofFn hω fun i => by fin_cases i <;> rfl

/-- The inverse of `1 ⊕ sgn ⊕ V₃ ≃ Sym³ V₃` sends `α³` to `(1/2, 1/2, 0)`. -/
@[simp]
theorem symmetricGroupThreeSymCubeEquiv_symm_tprod_alpha (h2 : (2 : k) ≠ 0) :
    (symmetricGroupThreeSymCubeEquiv hω h2).symm
        (⨂ₛ[k] _ : Fin 3, symmetricGroupThreeAlpha hω) = (2⁻¹, 2⁻¹, 0) := by
  rw [← symmetricPower_symmetricGroupThreeBasis_three_alpha, ← (symCubeMap_inv_two hω h2).1,
    ← symmetricGroupThreeSymCubeEquiv_apply hω h2, Representation.Equiv.symm_apply_apply]

/-- The inverse of `1 ⊕ sgn ⊕ V₃ ≃ Sym³ V₃` sends `β³` to `(1/2, -1/2, 0)`. -/
@[simp]
theorem symmetricGroupThreeSymCubeEquiv_symm_tprod_beta (h2 : (2 : k) ≠ 0) :
    (symmetricGroupThreeSymCubeEquiv hω h2).symm
        (⨂ₛ[k] _ : Fin 3, symmetricGroupThreeBeta hω) = (2⁻¹, -2⁻¹, 0) := by
  rw [← symmetricPower_symmetricGroupThreeBasis_three_beta, ← (symCubeMap_inv_two hω h2).2,
    ← symmetricGroupThreeSymCubeEquiv_apply hω h2, Representation.Equiv.symm_apply_apply]

/-- The inverse of `1 ⊕ sgn ⊕ V₃ ≃ Sym³ V₃` sends `α²β` to `α`. -/
@[simp]
theorem symmetricGroupThreeSymCubeEquiv_symm_tprod_alpha_alpha_beta (h2 : (2 : k) ≠ 0) :
    (symmetricGroupThreeSymCubeEquiv hω h2).symm
        (⨂ₛ[k] i, ![symmetricGroupThreeAlpha hω, symmetricGroupThreeAlpha hω,
          symmetricGroupThreeBeta hω] i) = (0, 0, symmetricGroupThreeAlpha hω) := by
  rw [← symmetricGroupThreeSymCubeEquiv_apply_zero_zero_alpha hω h2,
    Representation.Equiv.symm_apply_apply]

/-- The inverse of `1 ⊕ sgn ⊕ V₃ ≃ Sym³ V₃` sends `αβ²` to `β`. -/
@[simp]
theorem symmetricGroupThreeSymCubeEquiv_symm_tprod_alpha_beta_beta (h2 : (2 : k) ≠ 0) :
    (symmetricGroupThreeSymCubeEquiv hω h2).symm
        (⨂ₛ[k] i, ![symmetricGroupThreeAlpha hω, symmetricGroupThreeBeta hω,
          symmetricGroupThreeBeta hω] i) = (0, 0, symmetricGroupThreeBeta hω) := by
  rw [← symmetricGroupThreeSymCubeEquiv_apply_zero_zero_beta hω h2,
    Representation.Equiv.symm_apply_apply]

/-! ### The characters of the symmetric square and cube

The characters of `Sym² V₃` and `Sym³ V₃` are stated as traces, `LinearMap.trace` of the action:
`Representation.character` asks for an additive group structure on the carrier, and the
representation `Representation.symmetricPower` is built on the additive monoid structure of the
symmetric power.

They are computed over every field, without a cube root of unity, in the monomial bases built
from the basis `x = e₀ - e₂`, `y = e₁ - e₂` of `V₃`. There `σ = (0 1)` exchanges `x` and `y`, so
it permutes the monomials, and `τ = (0 1 2)` acts by `τ x = y - x`, `τ y = -x`, so the diagonal
coefficients of its action on a monomial are read off by expanding the product. -/

/-- The vectors `x = e₀ - e₂` and `y = e₁ - e₂` of the standard module of `S₃`. -/
private noncomputable def symmetricGroupThreeDiffVec (i : Fin 2) :
    (augmentationSubrepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).toSubmodule :=
  ⟨single i.castSucc 1 - single 2 1, by
    rw [toSubmodule_augmentationSubrepresentation, LinearMap.mem_ker]
    simp only [← MonoidAlgebra.basis_apply, map_sub, Basis.sumCoords_self_apply, sub_self]⟩

/-- The vectors `x` and `y` are linearly independent. -/
private theorem linearIndependent_symmetricGroupThreeDiffVec :
    LinearIndependent k (symmetricGroupThreeDiffVec (k := k)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hcoeff : ∀ j : Fin 3, ∑ i, c i * ((symmetricGroupThreeDiffVec i :
      (augmentationSubrepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).toSubmodule) :
        MonoidAlgebra k (Fin 3)).coeff j = 0 := fun j => by
    simpa [Finset.sum_apply'] using
      congrArg (fun v : MonoidAlgebra k (Fin 3) => v.coeff j) (congrArg Subtype.val hc)
  have h0 := hcoeff 0
  have h1 := hcoeff 1
  simp [symmetricGroupThreeDiffVec, Fin.sum_univ_two, Finsupp.single_apply] at h0 h1
  fin_cases i <;> simpa

/-- The basis `x = e₀ - e₂`, `y = e₁ - e₂` of the standard module of `S₃`, over every field. -/
private noncomputable def symmetricGroupThreeDiffBasis :
    Basis (Fin 2) k (augmentationSubrepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).toSubmodule :=
  basisOfLinearIndependentOfCardEqFinrank linearIndependent_symmetricGroupThreeDiffVec
    (by rw [finrank_augmentationSubrepresentation]; simp)

/-- The basis vectors are `x` and `y`. -/
private theorem symmetricGroupThreeDiffBasis_apply (i : Fin 2) :
    symmetricGroupThreeDiffBasis (k := k) i = symmetricGroupThreeDiffVec i := by
  simp [symmetricGroupThreeDiffBasis]

/-- `σ` exchanges `x` and `y`. -/
private theorem standardRepresentation_swap_symmetricGroupThreeDiffBasis (i : Fin 2) :
    standardRepresentation k (Fin 3) (Equiv.swap 0 1) (symmetricGroupThreeDiffBasis i) =
      symmetricGroupThreeDiffBasis (Equiv.swap 0 1 i) := by
  rw [symmetricGroupThreeDiffBasis_apply, symmetricGroupThreeDiffBasis_apply,
    ← toRepresentation_augmentationSubrepresentation, Subrepresentation.toRepresentation_apply_coe]
  obtain ⟨h0, h1, h2⟩ := swap_zero_one_smul
  fin_cases i <;>
    simp [symmetricGroupThreeDiffVec, Representation.ofMulAction_single, h0, h1, h2]

/-- `τ x = y - x` and `τ y = -x`, as the matrix of `τ` in the basis `x, y`. -/
private theorem repr_standardRepresentation_finRotate_symmetricGroupThreeDiffBasis (i j : Fin 2) :
    symmetricGroupThreeDiffBasis.repr
        (standardRepresentation k (Fin 3) (finRotate 3) (symmetricGroupThreeDiffBasis j)) i =
      !![-1, -1; 1, 0] i j := by
  have hx : standardRepresentation k (Fin 3) (finRotate 3) (symmetricGroupThreeDiffBasis 0) =
      symmetricGroupThreeDiffBasis 1 - symmetricGroupThreeDiffBasis 0 := by
    rw [symmetricGroupThreeDiffBasis_apply, symmetricGroupThreeDiffBasis_apply,
      ← toRepresentation_augmentationSubrepresentation,
      Subrepresentation.toRepresentation_apply_coe]
    obtain ⟨h0, -, h2⟩ := finRotate_three_smul
    simp [symmetricGroupThreeDiffVec, Representation.ofMulAction_single, h0, h2]
  have hy : standardRepresentation k (Fin 3) (finRotate 3) (symmetricGroupThreeDiffBasis 1) =
      -symmetricGroupThreeDiffBasis 0 := by
    rw [symmetricGroupThreeDiffBasis_apply, symmetricGroupThreeDiffBasis_apply,
      ← toRepresentation_augmentationSubrepresentation,
      Subrepresentation.toRepresentation_apply_coe]
    obtain ⟨-, h1, h2⟩ := finRotate_three_smul
    simp [symmetricGroupThreeDiffVec, Representation.ofMulAction_single, h1, h2]
  fin_cases j <;> fin_cases i <;> simp [hx, hy]

/-- The trace of `σ` on `Symⁿ V₃` counts the monomials in `x, y` fixed by exchanging `x` and `y`. -/
private theorem trace_symmetricPower_standardRepresentation_swap (n : ℕ) :
    LinearMap.trace k _ ((standardRepresentation k (Fin 3)).symmetricPower n (Equiv.swap 0 1)) =
      (Finset.univ.filter fun s : Sym (Fin 2) n => s.map (Equiv.swap 0 1) = s).card := by
  classical
  rw [LinearMap.trace_eq_matrix_trace k (symmetricGroupThreeDiffBasis.symmetricPower n),
    Matrix.trace, ← Finset.sum_boole]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Representation.symmetricPower_apply,
    symmetricGroupThreeDiffBasis.map_symmetricPower_apply_eq_symmetricPower_map _ _ _
      standardRepresentation_swap_symmetricGroupThreeDiffBasis, Basis.repr_self,
    Finsupp.single_apply]

/-- The diagonal coefficient of `τ` on `Symⁿ V₃` at the monomial indexed by `Sym.ofFn p` is the
sum, over the orderings `q` of `p`, of the products of the matrix coefficients of `τ` at `q, p`. -/
private theorem symmetricPower_repr_finRotate_symmetricGroupThreeDiffBasis {n : ℕ}
    (p : Fin n → Fin 2) (S : Finset (Fin n → Fin 2))
    (hS : ∀ q, q ∈ S ↔ TauCeti.Sym.ofFn q = TauCeti.Sym.ofFn p) :
    (symmetricGroupThreeDiffBasis.symmetricPower n).repr
        ((standardRepresentation k (Fin 3)).symmetricPower n (finRotate 3)
          (symmetricGroupThreeDiffBasis.symmetricPower n (TauCeti.Sym.ofFn p)))
        (TauCeti.Sym.ofFn p) =
      ∑ q ∈ S, ∏ i, !![(-1 : k), -1; 1, 0] (q i) (p i) := by
  simp_rw [Basis.symmetricPower_apply, SymmetricPower.tprodOfSym_ofFn,
    Representation.symmetricPower_apply_tprod, Basis.symmetricPower_repr_tprod_apply,
    repr_standardRepresentation_finRotate_symmetricGroupThreeDiffBasis]
  exact finsum_cond_eq_sum_of_cond_iff _ fun {q} _ => (hS q).symm

/-- Traces of the symmetric powers are invariant under conjugation. -/
private theorem trace_symmetricPower_standardRepresentation_conj (n : ℕ)
    (x h : Equiv.Perm (Fin 3)) :
    LinearMap.trace k _ ((standardRepresentation k (Fin 3)).symmetricPower n (h * x * h⁻¹)) =
      LinearMap.trace k _ ((standardRepresentation k (Fin 3)).symmetricPower n x) := by
  rw [map_mul ((standardRepresentation k (Fin 3)).symmetricPower n),
    map_mul ((standardRepresentation k (Fin 3)).symmetricPower n), LinearMap.trace_mul_comm,
    ← mul_assoc, ← map_mul ((standardRepresentation k (Fin 3)).symmetricPower n), inv_mul_cancel,
    map_one, one_mul]

/-- **`χ_{Sym² V₃}(1) = 3`**: `Sym² V₃` has dimension `3`. -/
theorem trace_symmetricPower_two_standardRepresentation_one :
    LinearMap.trace k _ ((standardRepresentation k (Fin 3)).symmetricPower 2 1) = 3 := by
  -- The trace of the identity is stated for an additive group, so it is applied up to the
  -- definitional agreement of the two additive monoid structures, as explained above.
  rw [map_one]
  refine (LinearMap.trace_one k
    (Sym[k]^2 (augmentationSubrepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).toSubmodule)).trans ?_
  rw [SymmetricPower.finrank_eq, finrank_augmentationSubrepresentation]
  simp [Nat.multichoose_eq]

/-- **`χ_{Sym² V₃}(σ) = 1`** for the transposition `σ = (0 1)`, which fixes the monomial `xy` and
exchanges `x²` and `y²`. -/
theorem trace_symmetricPower_two_standardRepresentation_swap :
    LinearMap.trace k _
      ((standardRepresentation k (Fin 3)).symmetricPower 2 (Equiv.swap 0 1)) = 1 := by
  rw [trace_symmetricPower_standardRepresentation_swap, show (Finset.univ.filter
    fun s : Sym (Fin 2) 2 => s.map (Equiv.swap 0 1) = s).card = 1 by decide, Nat.cast_one]

/-- **`χ_{Sym² V₃}(τ) = 0`** for the cycle `τ = (0 1 2)`, whose diagonal coefficients on the
monomials `x², xy, y²` are `1, -1, 0`. -/
theorem trace_symmetricPower_two_standardRepresentation_finRotate :
    LinearMap.trace k _
      ((standardRepresentation k (Fin 3)).symmetricPower 2 (finRotate 3)) = 0 := by
  have huniv : (Finset.univ : Finset (Sym (Fin 2) 2)) =
      {TauCeti.Sym.ofFn ![0, 0], TauCeti.Sym.ofFn ![0, 1], TauCeti.Sym.ofFn ![1, 1]} := by
    refine (Finset.eq_univ_of_forall fun s => ?_).symm
    obtain ⟨p, rfl⟩ := TauCeti.Sym.ofFn_surjective s
    simp only [Finset.mem_insert, Finset.mem_singleton, ← Sym.coe_inj, TauCeti.Sym.coe_ofFn]
    revert p
    decide
  rw [LinearMap.trace_eq_matrix_trace k (symmetricGroupThreeDiffBasis.symmetricPower 2),
    Matrix.trace, huniv, Finset.sum_insert ?_, Finset.sum_insert ?_, Finset.sum_singleton]
  · simp only [Matrix.diag_apply, LinearMap.toMatrix_apply]
    rw [symmetricPower_repr_finRotate_symmetricGroupThreeDiffBasis _ {![0, 0]} ?_,
      symmetricPower_repr_finRotate_symmetricGroupThreeDiffBasis _ {![0, 1], ![1, 0]} ?_,
      symmetricPower_repr_finRotate_symmetricGroupThreeDiffBasis _ {![1, 1]} ?_]
    · simp [Fin.prod_univ_two]
    -- The orderings of each monomial.
    all_goals
      simp only [Finset.mem_insert, Finset.mem_singleton, ← Sym.coe_inj, TauCeti.Sym.coe_ofFn]
      decide
  -- The three monomials are distinct.
  all_goals
    simp only [Finset.mem_insert, Finset.mem_singleton, ← Sym.coe_inj, TauCeti.Sym.coe_ofFn]
    decide

/-- **The character of `Sym² V₃` is `1 + χ_{V₃}`**, the character of `1 ⊕ V₃`
(compare `TauCeti.symmetricGroupThreeSymSqEquiv`). Both sides are class functions, so it suffices
to compare them at the identity, at `σ = (0 1)` and at `τ = (0 1 2)`. This holds over every
field. -/
theorem trace_symmetricPower_two_standardRepresentation (g : Equiv.Perm (Fin 3)) :
    LinearMap.trace k _ ((standardRepresentation k (Fin 3)).symmetricPower 2 g) =
      1 + (standardRepresentation k (Fin 3)).character g := by
  obtain ⟨h, rfl | rfl | rfl⟩ := Equiv.Perm.fin_three_conj_cases g
  · rw [trace_symmetricPower_two_standardRepresentation_one, character_standardRepresentation_one]
    norm_num
  · rw [trace_symmetricPower_standardRepresentation_conj, Representation.char_conj,
      trace_symmetricPower_two_standardRepresentation_swap, character_standardRepresentation_swap,
      add_zero]
  · rw [trace_symmetricPower_standardRepresentation_conj, Representation.char_conj,
      trace_symmetricPower_two_standardRepresentation_finRotate,
      character_standardRepresentation_finRotate, add_neg_cancel]

/-- **`χ_{Sym³ V₃}(1) = 4`**: `Sym³ V₃` has dimension `4`. -/
theorem trace_symmetricPower_three_standardRepresentation_one :
    LinearMap.trace k _ ((standardRepresentation k (Fin 3)).symmetricPower 3 1) = 4 := by
  -- The trace of the identity is stated for an additive group, so it is applied up to the
  -- definitional agreement of the two additive monoid structures, as explained above.
  rw [map_one]
  refine (LinearMap.trace_one k
    (Sym[k]^3 (augmentationSubrepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).toSubmodule)).trans ?_
  rw [SymmetricPower.finrank_eq, finrank_augmentationSubrepresentation]
  simp [Nat.multichoose_eq]

/-- **`χ_{Sym³ V₃}(σ) = 0`** for the transposition `σ = (0 1)`, which permutes the monomials
`x³, x²y, xy², y³` without fixed points. -/
theorem trace_symmetricPower_three_standardRepresentation_swap :
    LinearMap.trace k _
      ((standardRepresentation k (Fin 3)).symmetricPower 3 (Equiv.swap 0 1)) = 0 := by
  rw [trace_symmetricPower_standardRepresentation_swap, show (Finset.univ.filter
    fun s : Sym (Fin 2) 3 => s.map (Equiv.swap 0 1) = s).card = 0 by decide, Nat.cast_zero]

/-- **`χ_{Sym³ V₃}(τ) = 1`** for the cycle `τ = (0 1 2)`, whose diagonal coefficients on the
monomials `x³, x²y, xy², y³` are `-1, 2, 0, 0`. -/
theorem trace_symmetricPower_three_standardRepresentation_finRotate :
    LinearMap.trace k _
      ((standardRepresentation k (Fin 3)).symmetricPower 3 (finRotate 3)) = 1 := by
  have huniv : (Finset.univ : Finset (Sym (Fin 2) 3)) = {TauCeti.Sym.ofFn ![0, 0, 0],
      TauCeti.Sym.ofFn ![0, 0, 1], TauCeti.Sym.ofFn ![0, 1, 1], TauCeti.Sym.ofFn ![1, 1, 1]} := by
    refine (Finset.eq_univ_of_forall fun s => ?_).symm
    obtain ⟨p, rfl⟩ := TauCeti.Sym.ofFn_surjective s
    simp only [Finset.mem_insert, Finset.mem_singleton, ← Sym.coe_inj, TauCeti.Sym.coe_ofFn]
    revert p
    decide
  rw [LinearMap.trace_eq_matrix_trace k (symmetricGroupThreeDiffBasis.symmetricPower 3),
    Matrix.trace, huniv, Finset.sum_insert ?_, Finset.sum_insert ?_, Finset.sum_insert ?_,
    Finset.sum_singleton]
  · simp only [Matrix.diag_apply, LinearMap.toMatrix_apply]
    rw [symmetricPower_repr_finRotate_symmetricGroupThreeDiffBasis _ {![0, 0, 0]} ?_,
      symmetricPower_repr_finRotate_symmetricGroupThreeDiffBasis _
        {![0, 0, 1], ![0, 1, 0], ![1, 0, 0]} ?_,
      symmetricPower_repr_finRotate_symmetricGroupThreeDiffBasis _
        {![0, 1, 1], ![1, 0, 1], ![1, 1, 0]} ?_,
      symmetricPower_repr_finRotate_symmetricGroupThreeDiffBasis _ {![1, 1, 1]} ?_]
    · simp [Fin.prod_univ_three]
    -- The orderings of each monomial.
    all_goals
      simp only [Finset.mem_insert, Finset.mem_singleton, ← Sym.coe_inj, TauCeti.Sym.coe_ofFn]
      decide
  -- The four monomials are distinct.
  all_goals
    simp only [Finset.mem_insert, Finset.mem_singleton, ← Sym.coe_inj, TauCeti.Sym.coe_ofFn]
    decide

/-- **The character of `Sym³ V₃` is `1 + sgn + χ_{V₃}`**, the character of `1 ⊕ sgn ⊕ V₃`
(compare `TauCeti.symmetricGroupThreeSymCubeEquiv`). Both sides are class functions, so it
suffices to compare them at the identity, at `σ = (0 1)` and at `τ = (0 1 2)`. Unlike the
isomorphism `1 ⊕ sgn ⊕ V₃ ≃ Sym³ V₃`, this holds over every field. -/
theorem trace_symmetricPower_three_standardRepresentation (g : Equiv.Perm (Fin 3)) :
    LinearMap.trace k _ ((standardRepresentation k (Fin 3)).symmetricPower 3 g) =
      1 + (Equiv.Perm.sign g : ℤ) + (standardRepresentation k (Fin 3)).character g := by
  have hsign : ∀ x h : Equiv.Perm (Fin 3), Equiv.Perm.sign (h * x * h⁻¹) = Equiv.Perm.sign x := by
    intro x h
    rw [map_mul, map_mul, Equiv.Perm.sign_inv, mul_right_comm, Int.units_mul_self, one_mul]
  obtain ⟨h, rfl | rfl | rfl⟩ := Equiv.Perm.fin_three_conj_cases g
  · rw [trace_symmetricPower_three_standardRepresentation_one, map_one,
      character_standardRepresentation_one]
    norm_num
  · rw [trace_symmetricPower_standardRepresentation_conj, hsign, Representation.char_conj,
      trace_symmetricPower_three_standardRepresentation_swap,
      character_standardRepresentation_swap, Equiv.Perm.sign_swap (by decide)]
    norm_num
  · rw [trace_symmetricPower_standardRepresentation_conj, hsign, Representation.char_conj,
      trace_symmetricPower_three_standardRepresentation_finRotate,
      character_standardRepresentation_finRotate, sign_finRotate]
    norm_num

/-! ### Comparison with the character table of the dihedral group of order six -/

/-- **The displayed character table of the dihedral group of order six is that of `S₃`.**
Through `TauCeti.dihedralGroupThreeMulEquivPerm`, the rows of
`TauCeti.dihedralGroupThreeCharacterTable` are the characters of the trivial representation, the
sign representation and the standard representation of `S₃`, evaluated at the numbered class
representatives: the identity, a rotation (a `3`-cycle) and a reflection (a transposition). This
holds over every field. -/
theorem dihedralGroupThreeCharacterTable_eq_character {K : Type*} [Field K]
    (i j : DihedralGroupThreeClassIndex) :
    (dihedralGroupThreeCharacterTable i j : K) =
      ![(Representation.trivial K (Equiv.Perm (Fin 3)) K).character,
        (Representation.ofLinearCharacter (signLinearCharacter K (Fin 3))).character,
        (standardRepresentation K (Fin 3)).character] i
        (dihedralGroupThreeMulEquivPerm ((dihedralClassData 3).rep j)) := by
  have hrep : ∀ j, (dihedralClassData 3).rep j = ![1, .r 2, .sr 2] j := by
    intro j
    fin_cases j <;> rfl
  rw [dihedralGroupThreeCharacterTable_apply, hrep]
  revert i j
  -- The class index type `Fin (dihedralClassData 3).numClasses` is `Fin 3` by evaluation of the
  -- class data; restating the goal over `Fin 3` lets `fin_cases` produce literal indices.
  change ∀ i j : Fin 3, ((!![1, 1, 1; 1, 1, -1; 2, -1, 0] i j : ℤ) : K) =
    ![(Representation.trivial K (Equiv.Perm (Fin 3)) K).character,
      (Representation.ofLinearCharacter (signLinearCharacter K (Fin 3))).character,
      (standardRepresentation K (Fin 3)).character] i
      (dihedralGroupThreeMulEquivPerm (![1, .r 2, .sr 2] j))
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [-dihedralGroupThreeMulEquivPerm_r, -dihedralGroupThreeMulEquivPerm_sr,
      -char_standardRepresentation, -Equiv.swap_inv, dihedralGroupThreeMulEquivPerm_r_two,
      dihedralGroupThreeMulEquivPerm_sr_two,
      Representation.char_conj, Representation.char_trivial,
      Representation.char_ofLinearCharacter, coe_signLinearCharacter_apply,
      character_standardRepresentation_swap, character_standardRepresentation_finRotate,
      sign_finRotate]

end TauCeti
