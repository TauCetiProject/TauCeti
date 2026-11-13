/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.FinFour.Alternating
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Cyclotomic.AlternatingFour
public import TauCeti.RepresentationTheory.Induction.Clifford.Alternating.FixedConstituents
public import TauCeti.RepresentationTheory.Induction.Clifford.Alternating.Standard
public import TauCeti.RepresentationTheory.Symmetric.Four.Basic
public import TauCeti.RingTheory.RootsOfUnity.PrimeOrder
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.RingTheory.RootsOfUnity.Basic
import TauCeti.RepresentationTheory.Induction.Clifford.Alternating.Classification
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Restricting the representations of `S₄` to `A₄`

Let `κ : A₄ →* Multiplicative (ZMod 3)` be the quotient of `A₄` by its Klein four-group
(`TauCeti.alternatingGroupFourZModThreeHom`), normalized by `κ((0 1 2)) = 1`. A cube root of
unity `ζ` in a commutative monoid `k` gives the linear character

`L_ζ : A₄ →* kˣ`, `g ↦ ζ ^ κ(g)`,

and distinct cube roots of unity give distinct characters. Let `ω ∈ ℂ` be the image of the cube
root of unity `TauCeti.alternatingGroupFourOmega` under the distinguished embedding of the sixth
cyclotomic integers into `ℂ`, that is `ω = exp (2πi/3)`. Then the characters of `L₁`, `L_ω`,
`L_{ω²}` and of the restriction `T` of the standard representation of `S₄` are the four rows of
the exact character table `TauCeti.alternatingGroupFourExactCharacterTable`, in its row and
column order.

The two-dimensional irreducible representation `E` of `S₄`
(`TauCeti.symmetricGroupFourTwoDimensionalRepresentation`) is the standard representation of
`S₃` on the sum-zero vectors of `k[Fin 3]`, pulled back along the action `q` on the three perfect
matchings `M₀`, `M₁`, `M₂` of `Fin 4`. For `g ∈ A₄`, `q g` is the power `c ^ κ(g)` of the
three-cycle `c = q((0 1 2))` of the matchings, so on restriction to `A₄` the representation `E`
splits along the eigenvectors of `c`. For a cube root of unity `ζ ≠ 1` in a field, the vector

`v_ζ = ∑ r, ζ⁻ʳ δ_{c^r M₀} = δ₀ + ζ² δ₁ + ζ δ₂`

has coefficient sum `1 + ζ + ζ² = 0`, so lies in `E`, and `g ∈ A₄` acts on it by `ζ ^ κ(g)`.
The vectors `v_ζ` and `v_{ζ²}` form a basis of `E`, which gives the equivalence of
representations `Res E ≃ L_ζ ⊕ L_{ζ²}`; over `ℂ` and for `ζ = ω` this is `Res E ≃ L_ω ⊕ L_{ω²}`.

The other irreducible representations of `S₄` restrict as follows: the trivial and sign
representations to `L₁` (`TauCeti.signLinearCharacter_comp_alternatingGroup_subtype`), and the
standard representation and its sign twist to `T` (`FDRep.resSignTwistAlternatingGroupIso`).
Hence, over an algebraically closed field of characteristic zero, each of the four irreducible
representations `L₁`, `L_ζ`, `L_{ζ²}`, `T` of `A₄` occurs in the restriction of an irreducible
representation of `S₄`: `E` lies over `L_ζ` and `L_{ζ²}` through the eigenvectors `v_ζ`, `v_{ζ²}`.

## Main definitions

* `TauCeti.alternatingGroupFourLinearCharacter`: the linear character `L_ζ` of `A₄`.
* `TauCeti.symmetricGroupFourTwoDimensionalEigenvector`: the vector `v_ζ` of `E`.
* `TauCeti.alternatingGroupFourTwoDimensionalEquiv`: the equivalence
  `Res E ≃ L_ζ ⊕ L_{ζ²}`.

## Main results

* `TauCeti.alternatingGroupFourZModThreeHom_classData_rep`: `κ` takes the values `0, 0, 1, 2`
  on the class representatives `1, (01)(23), (012), (021)` of `A₄`.
* `TauCeti.alternatingGroupFourLinearCharacter_injective`: distinct cube roots of unity give
  distinct linear characters.
* `TauCeti.complexEmbedding_alternatingGroupFourExactCharacterTable`: the rows of the exact
  character table of `A₄` are the characters of `L₁`, `L_ω`, `L_{ω²}` and `T`.
* `TauCeti.symmetricGroupFourTwoDimensionalRepresentation_apply_eigenvector`: `g ∈ A₄` acts on
  `v_ζ` by `L_ζ(g)`.
* `TauCeti.alternatingGroupFourTwoDimensionalEquiv_symm_apply`: the inverse of the equivalence
  sends `(a, b)` to `a v_ζ + b v_{ζ²}`.
* `TauCeti.symmetricGroupFourTwoDimensionalRepresentation_liesOver`: `E` lies over `L_ζ` for
  every cube root of unity `ζ ≠ 1`.
* `FDRep.exists_simple_liesOver_alternatingGroupFour`: every irreducible representation of
  `A₄` occurs in the restriction of an irreducible representation of `S₄`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Springer GTM 129 (1991),
  §2.3.
* G. James and M. Liebeck, *Representations and Characters of Groups*, Chapter 18.
-/

public section

namespace TauCeti

open Equiv

/-- **`κ((0 1 2)) = 1`**: the three-cycle `(0 1 2)` of `Fin 4` acts on the three perfect
matchings as the three-cycle `c = (0 1 2)` of the matchings. -/
@[simp]
theorem alternatingGroupFourZModThreeHom_threeCycle :
    alternatingGroupFourZModThreeHom alternatingGroupFourThreeCycle = Multiplicative.ofAdd 1 := by
  have hc : (alternatingGroupFourThreeCycle : Perm (Fin 4)) = [0, 1, 2].formPerm := by decide
  rw [alternatingGroupFourZModThreeHom_eq_iff, hc,
    symmetricGroupFourMatchingHom_formPerm_zero_one_two, toAdd_ofAdd, ZMod.val_one, pow_one]

/-- **`κ` on the class representatives of `A₄`**: it takes the values `0, 0, 1, 2` on the
identity, the double transposition `(01)(23)`, the three-cycle `(012)` and its inverse. -/
theorem alternatingGroupFourZModThreeHom_classData_rep
    (i : Fin alternatingGroupFourClassData.numClasses) :
    alternatingGroupFourZModThreeHom (alternatingGroupFourClassData.rep i) =
      Multiplicative.ofAdd ((![0, 0, 1, 2] : Fin 4 → ZMod 3)
        (i.cast numClasses_alternatingGroupFourClassData)) := by
  -- The class representatives `1, (01)(23), (012), (012)⁻¹` reduce by definitional unfolding of
  -- the exposed `TauCeti.alternatingGroupFourClassData`.
  fin_cases i
  · exact map_one _
  · rw [alternatingGroupFourZModThreeHom_eq_iff]
    exact symmetricGroupFourMatchingHom_swap_zero_one_mul_swap_two_three.trans (pow_zero _).symm
  · exact alternatingGroupFourZModThreeHom_threeCycle
  · exact (map_inv _ alternatingGroupFourThreeCycle).trans
      (by rw [alternatingGroupFourZModThreeHom_threeCycle]; decide)

section LinearCharacter

variable {k : Type*} [CommMonoid k]

/-- **The linear character `L_ζ` of `A₄`** attached to a cube root of unity `ζ`:
`g ↦ ζ ^ κ(g)`, where `κ : A₄ →* ℤ/3ℤ` is the quotient by the Klein four-group, normalized by
`κ((0 1 2)) = 1`. -/
noncomputable def alternatingGroupFourLinearCharacter (ζ : rootsOfUnity 3 k) :
    alternatingGroup (Fin 4) →* kˣ :=
  (AddChar.zmodChar 3 ((mem_rootsOfUnity 3 _).1 ζ.2)).toMonoidHom.comp
    alternatingGroupFourZModThreeHom

/-- `L_ζ(g) = ζ ^ κ(g)`. -/
theorem alternatingGroupFourLinearCharacter_apply (ζ : rootsOfUnity 3 k)
    (g : alternatingGroup (Fin 4)) :
    alternatingGroupFourLinearCharacter ζ g =
      (ζ : kˣ) ^ (Multiplicative.toAdd (alternatingGroupFourZModThreeHom g)).val :=
  (rfl)

/-- The trivial cube root of unity gives the trivial character. -/
@[simp]
theorem alternatingGroupFourLinearCharacter_one :
    alternatingGroupFourLinearCharacter (1 : rootsOfUnity 3 k) = 1 :=
  MonoidHom.ext fun g => by simp [alternatingGroupFourLinearCharacter_apply]

/-- **The values of `L_ζ`** on the class representatives `1, (01)(23), (012), (021)` of `A₄` are
`1, 1, ζ, ζ²`. -/
theorem alternatingGroupFourLinearCharacter_classData_rep (ζ : rootsOfUnity 3 k)
    (i : Fin alternatingGroupFourClassData.numClasses) :
    alternatingGroupFourLinearCharacter ζ (alternatingGroupFourClassData.rep i) =
      (![1, 1, (ζ : kˣ), (ζ : kˣ) ^ 2] : Fin 4 → kˣ)
        (i.cast numClasses_alternatingGroupFourClassData) := by
  rw [alternatingGroupFourLinearCharacter_apply, alternatingGroupFourZModThreeHom_classData_rep,
    toAdd_ofAdd]
  fin_cases i <;> simp [Fin.cast, Matrix.cons_val, ZMod.val_one, ZMod.val_ofNat]

/-- `L_ζ` takes the value `ζ` at the three-cycle `(0 1 2)`. -/
@[simp]
theorem alternatingGroupFourLinearCharacter_threeCycle (ζ : rootsOfUnity 3 k) :
    alternatingGroupFourLinearCharacter ζ alternatingGroupFourThreeCycle = ζ := by
  rw [alternatingGroupFourLinearCharacter_apply, alternatingGroupFourZModThreeHom_threeCycle,
    toAdd_ofAdd, ZMod.val_one, pow_one]

/-- **Distinct cube roots of unity give distinct linear characters of `A₄`**, since `L_ζ`
takes the value `ζ` at `(0 1 2)`. -/
theorem alternatingGroupFourLinearCharacter_injective :
    Function.Injective (alternatingGroupFourLinearCharacter (k := k)) := fun ζ ζ' h =>
  Subtype.ext <| by
    rw [← alternatingGroupFourLinearCharacter_threeCycle ζ,
      ← alternatingGroupFourLinearCharacter_threeCycle ζ', h]

/-- `L_{ζ⁻¹}` is the inverse character `(L_ζ)⁻¹`. -/
@[simp]
theorem alternatingGroupFourLinearCharacter_inv (ζ : rootsOfUnity 3 k) :
    alternatingGroupFourLinearCharacter ζ⁻¹ = (alternatingGroupFourLinearCharacter ζ)⁻¹ :=
  MonoidHom.ext fun g => by simp [alternatingGroupFourLinearCharacter_apply, inv_pow]

end LinearCharacter

section CharacterTable

/-- **The exact character table of `A₄` is the table of `L₁`, `L_ω`, `L_{ω²}` and `T`.** Let `ω`
be the image of the cube root of unity `TauCeti.alternatingGroupFourOmega = ζ₆²` under the pinned
embedding `TauCeti.Cyclotomic.complexEmbedding` (which sends `ζ₆` to `exp (2πi/6)`). The rows of
`TauCeti.alternatingGroupFourExactCharacterTable`, embedded in `ℂ`, are the characters of the
linear characters `L₁`, `L_ω`, `L_{ω²}` and of the restriction `T` of the standard representation
of `S₄`, evaluated at the class representatives `1, (01)(23), (012), (021)` of
`TauCeti.alternatingGroupFourClassData`. -/
theorem complexEmbedding_alternatingGroupFourExactCharacterTable (ω : rootsOfUnity 3 ℂ)
    (hω : ((ω : ℂˣ) : ℂ) = Cyclotomic.complexEmbedding alternatingGroupFourOmega)
    (i j : AlternatingGroupFourClassIndex) :
    Cyclotomic.complexEmbedding (alternatingGroupFourExactCharacterTable i j) =
      (![(Representation.ofLinearCharacter (alternatingGroupFourLinearCharacter 1)).character,
        (Representation.ofLinearCharacter (alternatingGroupFourLinearCharacter ω)).character,
        (Representation.ofLinearCharacter (alternatingGroupFourLinearCharacter (ω ^ 2))).character,
        (alternatingGroupFourStandard ℂ).character] : Fin 4 → alternatingGroup (Fin 4) → ℂ)
        (i.cast numClasses_alternatingGroupFourClassData)
        (alternatingGroupFourClassData.rep j) := by
  have h3 : ((ω : ℂˣ) : ℂ) ^ 3 = 1 := (mem_rootsOfUnity' 3 _).1 ω.2
  have h4 : (((ω : ℂˣ) : ℂ) ^ 2) ^ 2 = ((ω : ℂˣ) : ℂ) := by
    rw [← pow_mul]
    linear_combination ((ω : ℂˣ) : ℂ) * h3
  have hrep (ζ : rootsOfUnity 3 ℂ) := alternatingGroupFourLinearCharacter_classData_rep ζ j
  have hstd : (alternatingGroupFourStandard ℂ).character (alternatingGroupFourClassData.rep j) =
      (((![3, -1, 0, 0] : Fin 4 → ℤ) (j.cast numClasses_alternatingGroupFourClassData)) : ℂ) :=
    character_alternatingGroupFourStandard_rep ℂ j
  have ht : alternatingGroupFourExactCharacterTable i j =
      (!![1, 1, 1, 1;
          1, 1, alternatingGroupFourOmega, alternatingGroupFourOmega ^ 2;
          1, 1, alternatingGroupFourOmega ^ 2, alternatingGroupFourOmega;
          3, -1, 0, 0] : Matrix (Fin 4) (Fin 4) (Cyclotomic 6))
        (i.cast numClasses_alternatingGroupFourClassData)
        (j.cast numClasses_alternatingGroupFourClassData) :=
    alternatingGroupFourExactCharacterTable_apply i j
  rw [ht]
  generalize i.cast numClasses_alternatingGroupFourClassData = i
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val,
      Representation.char_ofLinearCharacter, hrep, hstd] <;>
    generalize j.cast numClasses_alternatingGroupFourClassData = j <;>
    fin_cases j <;> simp [map_ofNat, h4, ← hω]

end CharacterTable

section Decomposition

variable {k : Type*} [Field k]

/-- **The eigenvector `v_ζ = δ₀ + ζ² δ₁ + ζ δ₂` of `E`** for a cube root of unity `ζ ≠ 1`: the sum
`∑ r, ζ⁻ʳ δ_{c^r M₀}` over the orbit of the matching `M₀` under the three-cycle `c` of the
matchings. Its coefficients sum to `1 + ζ² + ζ = 0`, so it lies in the sum-zero submodule carrying
`E`, and `g ∈ A₄` acts on it by `L_ζ(g)`. -/
noncomputable def symmetricGroupFourTwoDimensionalEigenvector (ζ : rootsOfUnity 3 k)
    (hζ : ζ ≠ 1) : (augmentationSubrepresentation k (Perm (Fin 3)) (Fin 3)).toSubmodule :=
  ⟨MonoidAlgebra.single 0 1 + MonoidAlgebra.single 1 (((ζ : kˣ) : k) ^ 2) +
      MonoidAlgebra.single 2 ((ζ : kˣ) : k), by
    have h := (IsPrimitiveRoot.of_pow_eq_one_of_ne_one ((mem_rootsOfUnity' 3 _).1 ζ.2)
      (rootsOfUnity.coe_injective.ne hζ)).geom_sum_eq_zero (by norm_num)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at h
    simpa [Fin.sum_univ_three, add_right_comm _ (((ζ : kˣ) : k) ^ 2)] using h⟩

/-- The underlying element `δ₀ + ζ² δ₁ + ζ δ₂` of `k[Fin 3]` of the eigenvector `v_ζ`. -/
@[simp]
theorem coe_symmetricGroupFourTwoDimensionalEigenvector (ζ : rootsOfUnity 3 k) (hζ : ζ ≠ 1) :
    (symmetricGroupFourTwoDimensionalEigenvector ζ hζ : MonoidAlgebra k (Fin 3)) =
      MonoidAlgebra.single 0 1 + MonoidAlgebra.single 1 (((ζ : kˣ) : k) ^ 2) +
        MonoidAlgebra.single 2 ((ζ : kˣ) : k) :=
  (rfl)

/-- The three-cycle `c = (0 1 2)` of the matchings acts on `v_ζ` by `ζ`. -/
private theorem standardRepresentation_formPerm_eigenvector (ζ : rootsOfUnity 3 k)
    (hζ : ζ ≠ 1) :
    standardRepresentation k (Fin 3) [0, 1, 2].formPerm
        (symmetricGroupFourTwoDimensionalEigenvector ζ hζ) =
      ((ζ : kˣ) : k) • symmetricGroupFourTwoDimensionalEigenvector ζ hζ := by
  have h3 : ((ζ : kˣ) : k) ^ 3 = 1 := (mem_rootsOfUnity' 3 _).1 ζ.2
  apply Subtype.ext
  rw [coe_standardRepresentation_apply, Submodule.coe_smul,
    coe_symmetricGroupFourTwoDimensionalEigenvector]
  simp only [map_add, Representation.ofMulAction_single, smul_add, MonoidAlgebra.smul_single,
    smul_eq_mul, mul_one]
  have h0 : ([0, 1, 2].formPerm : Perm (Fin 3)) • (0 : Fin 3) = 1 := by decide
  have h1 : ([0, 1, 2].formPerm : Perm (Fin 3)) • (1 : Fin 3) = 2 := by decide
  have h2 : ([0, 1, 2].formPerm : Perm (Fin 3)) • (2 : Fin 3) = 0 := by decide
  rw [h0, h1, h2, ← pow_succ', h3, ← sq]
  abel

/-- **`A₄` acts on `v_ζ` by the linear character `L_ζ`**: `g ∈ A₄` acts on the matchings as the
power `c ^ κ(g)` of the three-cycle `c`, which acts on `v_ζ` by `ζ`. -/
theorem symmetricGroupFourTwoDimensionalRepresentation_apply_eigenvector (ζ : rootsOfUnity 3 k)
    (hζ : ζ ≠ 1) (g : alternatingGroup (Fin 4)) :
    symmetricGroupFourTwoDimensionalRepresentation k g
        (symmetricGroupFourTwoDimensionalEigenvector ζ hζ) =
      (alternatingGroupFourLinearCharacter ζ g : k) •
        symmetricGroupFourTwoDimensionalEigenvector ζ hζ := by
  rw [symmetricGroupFourTwoDimensionalRepresentation_apply,
    symmetricGroupFourMatchingHom_coe_eq_pow, alternatingGroupFourLinearCharacter_apply,
    Units.val_pow_eq_pow_val, map_pow]
  generalize (Multiplicative.toAdd (alternatingGroupFourZModThreeHom g)).val = n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_apply_eq_comp, standardRepresentation_formPerm_eigenvector, map_smul, ih,
      smul_smul, pow_succ, mul_comm]

/-- The map `(a, b) ↦ a v_ζ + b v_{ζ²}` from `L_ζ ⊕ L_{ζ²}` to `E`. -/
private noncomputable def eigenvectorMap (ζ : rootsOfUnity 3 k) (hζ : ζ ≠ 1) :
    k × k →ₗ[k] (augmentationSubrepresentation k (Perm (Fin 3)) (Fin 3)).toSubmodule :=
  (LinearMap.toSpanSingleton k _ (symmetricGroupFourTwoDimensionalEigenvector ζ hζ)).coprod
    (LinearMap.toSpanSingleton k _ (symmetricGroupFourTwoDimensionalEigenvector (ζ ^ 2)
      (rootsOfUnity.pow_ne_one_of_ne_one hζ two_ne_zero (by norm_num))))

private theorem eigenvectorMap_apply (ζ : rootsOfUnity 3 k) (hζ : ζ ≠ 1) (x : k × k) :
    eigenvectorMap ζ hζ x = x.1 • symmetricGroupFourTwoDimensionalEigenvector ζ hζ +
      x.2 • symmetricGroupFourTwoDimensionalEigenvector (ζ ^ 2)
        (rootsOfUnity.pow_ne_one_of_ne_one hζ two_ne_zero (by norm_num)) :=
  rfl

private theorem eigenvectorMap_bijective (ζ : rootsOfUnity 3 k) (hζ : ζ ≠ 1) :
    Function.Bijective (eigenvectorMap ζ hζ) := by
  have h3 : ((ζ : kˣ) : k) ^ 3 = 1 := (mem_rootsOfUnity' 3 _).1 ζ.2
  have h1 : ((ζ : kˣ) : k) ≠ 1 := rootsOfUnity.coe_injective.ne hζ
  have hinj : Function.Injective (eigenvectorMap ζ hζ) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a, b⟩ hab
    have hc (i : Fin 3) :
        ((eigenvectorMap ζ hζ (a, b) : MonoidAlgebra k (Fin 3))).coeff i = 0 := by
      rw [hab, ZeroMemClass.coe_zero, MonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
    have h0 := hc 0
    have h1' := hc 1
    simp only [eigenvectorMap_apply, Submodule.coe_add, Submodule.coe_smul,
      coe_symmetricGroupFourTwoDimensionalEigenvector, MonoidAlgebra.coeff_add,
      MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_single, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.single_apply, Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow] at h0 h1'
    norm_num at h0 h1'
    have hb : b = -a := by linear_combination h0
    subst hb
    have hζ0 : ((ζ : kˣ) : k) ≠ 0 := Units.ne_zero _
    have ha : a * (((ζ : kˣ) : k) * (((ζ : kˣ) : k) - 1)) = 0 := by
      linear_combination h1' + a * ((ζ : kˣ) : k) * h3
    have hne : ((ζ : kˣ) : k) * (((ζ : kˣ) : k) - 1) ≠ 0 :=
      mul_ne_zero hζ0 (sub_ne_zero.2 h1)
    have ha0 : a = 0 := (mul_eq_zero.1 ha).resolve_right hne
    simp [ha0]
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj⟩
  simp

/-- **The restriction of `E` to `A₄` is `L_ζ ⊕ L_{ζ²}`** for a cube root of unity `ζ ≠ 1` in a
field: the eigenvectors `v_ζ` and `v_{ζ²}` of the three-cycle of the matchings form a basis of
`E` on which `A₄` acts by `L_ζ` and `L_{ζ²}`. Over `ℂ` and for `ζ = ω = exp (2πi/3)` this is
`Res E ≃ L_ω ⊕ L_{ω²}`. -/
noncomputable def alternatingGroupFourTwoDimensionalEquiv (ζ : rootsOfUnity 3 k) (hζ : ζ ≠ 1) :
    Representation.Equiv
      ((symmetricGroupFourTwoDimensionalRepresentation k).comp (alternatingGroup (Fin 4)).subtype)
      ((Representation.ofLinearCharacter (alternatingGroupFourLinearCharacter ζ)).prod
        (Representation.ofLinearCharacter (alternatingGroupFourLinearCharacter (ζ ^ 2)))) :=
  (Representation.Equiv.mk (LinearEquiv.ofBijective _ (eigenvectorMap_bijective ζ hζ))
    fun g => LinearMap.ext fun x => by
      simp [-symmetricGroupFourTwoDimensionalRepresentation_apply, eigenvectorMap_apply,
        symmetricGroupFourTwoDimensionalRepresentation_apply_eigenvector, smul_smul, mul_comm]).symm

/-- The inverse of `TauCeti.alternatingGroupFourTwoDimensionalEquiv` sends `(a, b)` to
`a v_ζ + b v_{ζ²}`. -/
theorem alternatingGroupFourTwoDimensionalEquiv_symm_apply (ζ : rootsOfUnity 3 k) (hζ : ζ ≠ 1)
    (x : k × k) :
    (alternatingGroupFourTwoDimensionalEquiv ζ hζ).symm x =
      x.1 • symmetricGroupFourTwoDimensionalEigenvector ζ hζ +
        x.2 • symmetricGroupFourTwoDimensionalEigenvector (ζ ^ 2)
          (rootsOfUnity.pow_ne_one_of_ne_one hζ two_ne_zero (by norm_num)) :=
  (rfl)

end Decomposition

section LiesOver

open CategoryTheory

variable {k : Type*} [Field k]

/-- **`E` lies over `L_ζ`** for every cube root of unity `ζ ≠ 1` in a field: `x ↦ x v_ζ` is a
nonzero intertwiner from `L_ζ` to the restriction of `E` to `A₄`. -/
theorem symmetricGroupFourTwoDimensionalRepresentation_liesOver (ζ : rootsOfUnity 3 k)
    (hζ : ζ ≠ 1) :
    (FDRep.of (symmetricGroupFourTwoDimensionalRepresentation k)).LiesOver
      (alternatingGroup (Fin 4)).subtype
      (FDRep.ofLinearCharacter (alternatingGroupFourLinearCharacter ζ)) := by
  rw [FDRep.ofLinearCharacter_def]
  refine FDRep.liesOver_of_intertwiningMap _ _
    ((alternatingGroupFourTwoDimensionalEquiv ζ hζ).symm.toIntertwiningMap.comp
      (Representation.IntertwiningMap.inl k _ _)) fun h => ?_
  -- Evaluating at `1` gives `v_ζ = 0`, whose coefficient at `M₀` is `1`.
  have h1 : (alternatingGroupFourTwoDimensionalEquiv ζ hζ).symm (1, 0) = 0 :=
    DFunLike.congr_fun h (1 : k)
  rw [alternatingGroupFourTwoDimensionalEquiv_symm_apply, one_smul, zero_smul, add_zero] at h1
  have h0 := congrArg (fun v => MonoidAlgebra.coeff (Subtype.val v) 0) h1
  simp [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single] at h0

end LiesOver

end TauCeti

namespace FDRep

open CategoryTheory TauCeti Equiv

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]

/-- **Every irreducible representation of `A₄` occurs in the restriction of an irreducible
representation of `S₄`**, over an algebraically closed field of characteristic zero. -/
theorem exists_simple_liesOver_alternatingGroupFour (W : FDRep k (alternatingGroup (Fin 4)))
    [Simple W] :
    ∃ B : FDRep k (Perm (Fin 4)), Simple B ∧ B.LiesOver (alternatingGroup (Fin 4)).subtype W := by
  have : NeZero ((3 : ℕ) : k) := ⟨by norm_num⟩
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot k 3
  have hζ : hμ.toRootsOfUnity ≠ 1 := fun h => hμ.ne_one (by norm_num) <| by
    simpa using congrArg (fun u : rootsOfUnity 3 k => ((u : kˣ) : k)) h
  have hχ : alternatingGroupFourLinearCharacter hμ.toRootsOfUnity ≠ 1 := by
    rw [← alternatingGroupFourLinearCharacter_one]
    exact alternatingGroupFourLinearCharacter_injective.ne hζ
  have hE : Simple (FDRep.of (symmetricGroupFourTwoDimensionalRepresentation k)) :=
    (FDRep.simple_iff_isIrreducible _).mpr <| by
      rw [FDRep.of_ρ']
      exact isIrreducible_symmetricGroupFourTwoDimensionalRepresentation (by norm_num)
  have hV : Simple (FDRep.of (standardRepresentation k (Fin 4))) :=
    (FDRep.simple_iff_isIrreducible _).mpr <| by
      rw [FDRep.of_ρ']
      exact isIrreducible_standardRepresentation (by norm_num) (Or.inr (by norm_num))
  -- `W` is one of `L₁`, `L_ζ`, `L_{ζ⁻¹}` and `T`, which lie under the trivial representation,
  -- `E`, `E` and the standard representation respectively.
  rcases (simple_alternatingGroupFour_iff W hχ).mp ‹_› with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact ⟨_, inferInstance, ((liesOver_trivial_alternatingGroup_iff _).mpr
      (Or.inl ⟨Iso.refl _⟩)).of_iso_right e.symm⟩
  · exact ⟨_, hE, (symmetricGroupFourTwoDimensionalRepresentation_liesOver _ hζ).of_iso_right
      e.symm⟩
  · rw [← alternatingGroupFourLinearCharacter_inv] at e
    exact ⟨_, hE, (symmetricGroupFourTwoDimensionalRepresentation_liesOver _
      (inv_ne_one.mpr hζ)).of_iso_right e.symm⟩
  · exact ⟨_, hV, ((liesOver_alternatingGroupFourStandard_iff _).mpr
      (Or.inl ⟨Iso.refl _⟩)).of_iso_right e.symm⟩

end FDRep
