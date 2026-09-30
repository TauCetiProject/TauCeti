/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.WreathProduct.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Diagonal.Normalizer
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Weyl

/-!
# The Weyl group of the symplectic diagonal torus is the hyperoctahedral group

Over a field `k` with a unit different from its inverse, the normalizer quotient `N(T)/T` of the
paired diagonal torus `T` in `Sp₂ₘ(k)` acts faithfully on the `2m` coordinate lines
(`TauCeti.GLSymplecticFin.diagonalNormalizerQuotientPerm_injective`). This file computes the image
of that action: it consists exactly of the signed permutations. Hence `N(T)/T` is the
hyperoctahedral group `Sym(Bool) ≀ Sym(m)`.

The coordinate lines are labelled by `Fin m × Bool` through `signedCoordinateEquiv`: the line
`(i, false)` is the `i`-th line of the first block, on which the torus acts by `tᵢ`, and
`(i, true)` is the `i`-th line of the second block, on which it acts by `tᵢ⁻¹`. A normalizer
element conjugates `diag(t)` to another element of the torus, so it must carry the two lines of
each symplectic plane, on which the torus acts by mutually inverse characters, to the two lines of
a single plane; this is the commutation with the flip of `Bool`. Conversely the long-root Weyl
representative `n_{2eᵢ}` exchanges the two lines of the `i`-th plane and the short-root Weyl
representative `n_{eᵢ-eⱼ}` exchanges the `i`-th and `j`-th planes, and these generate the
hyperoctahedral group.

## Main definitions

* `TauCeti.GLSymplecticFin.signedCoordinateEquiv`: the labelling of the coordinates of
  `Fin (m + m)` by `Fin m × Bool`.
* `TauCeti.GLSymplecticFin.diagonalNormalizerQuotientMulEquivWreathProduct`: the normalizer
  quotient of the paired diagonal torus is the hyperoctahedral group.

## Main results

All in the namespace `TauCeti.GLSymplecticFin`:

* `signedCoordinateEquiv_diagonalNormalizerQuotientMulEquivWreathProduct_smul`: the equivalence
  is compatible with the actions on the coordinate lines.
* `diagonalNormalizerQuotientMulEquivWreathProduct_positiveLongRootWeylElement`: the long-root
  Weyl representative `n_{2eᵢ}` is the sign change of the `i`-th coordinate.
* `diagonalNormalizerQuotientMulEquivWreathProduct_differenceShortRootWeylElement`: the short-root
  Weyl representative `n_{eᵢ-eⱼ}` is the transposition of the `i`-th and `j`-th coordinates.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), Section 26.3 and the table of Weyl groups in
  Appendix A.
* J. S. Milne, *Algebraic Groups* (2017), Example 21.2 and Section 21.1.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate III.
-/

public section

open Matrix

namespace TauCeti.GLSymplecticFin

noncomputable section

variable {m : ℕ}

variable (m) in
/-- The labelling of the coordinates of `Fin (m + m)` by `Fin m × Bool`: `(i, false)` is the
`i`-th coordinate of the first block and `(i, true)` is the `i`-th coordinate of the second
block. On these, the paired diagonal torus acts by `tᵢ` and `tᵢ⁻¹` respectively. -/
def signedCoordinateEquiv : Fin m × Bool ≃ Fin (m + m) :=
  ((Equiv.prodComm (Fin m) Bool).trans (Equiv.boolProdEquivSum (Fin m))).trans finSumFinEquiv

@[simp]
theorem signedCoordinateEquiv_false (i : Fin m) :
    signedCoordinateEquiv m (i, false) = Fin.castAdd m i := by
  simp [signedCoordinateEquiv]

@[simp]
theorem signedCoordinateEquiv_true (i : Fin m) :
    signedCoordinateEquiv m (i, true) = i.addNat m := by
  simp [signedCoordinateEquiv, Fin.natAdd_eq_addNat]

/-- The diagonal entry of a paired diagonal matrix on the line `(i, s)` is `tᵢ` or `tᵢ⁻¹`
according to whether `s` is `false` or `true`. -/
@[simp]
theorem diagonalCoordinates_signedCoordinateEquiv {R : Type*} [Monoid R] (t : Fin m → Rˣ)
    (x : Fin m × Bool) :
    diagonalCoordinates t (signedCoordinateEquiv m x) = if x.2 then (t x.1)⁻¹ else t x.1 := by
  rcases x with ⟨i, _ | _⟩ <;> simp

/-- The two lines of each symplectic plane carry mutually inverse diagonal entries. -/
private theorem diagonalCoordinates_signedCoordinateEquiv_not {R : Type*} [Monoid R]
    (t : Fin m → Rˣ) (x : Fin m × Bool) :
    diagonalCoordinates t (signedCoordinateEquiv m (x.1, !x.2)) =
      (diagonalCoordinates t (signedCoordinateEquiv m x))⁻¹ := by
  rcases x with ⟨i, _ | _⟩ <;> simp

variable {k : Type*} [Field k] (u : kˣ) (hu : u ≠ u⁻¹)

include hu in
/-- If, for every torus element, the diagonal entry on the line `y` is the inverse of the entry on
the line `x`, then `y` is the other line of the symplectic plane of `x`. -/
private theorem eq_not_of_forall_diagonalCoordinates_eq_inv {x y : Fin m × Bool}
    (h : ∀ t : Fin m → kˣ, diagonalCoordinates t (signedCoordinateEquiv m y) =
      (diagonalCoordinates t (signedCoordinateEquiv m x))⁻¹) :
    y = (x.1, !x.2) := by
  have hu1 : u ≠ 1 := by
    rintro rfl
    exact hu inv_one.symm
  rcases x with ⟨i, s⟩
  rcases y with ⟨j, r⟩
  -- Test against the torus element that is `u` in the `i`-th plane and trivial elsewhere.
  have hi := h (Pi.mulSingle i u)
  simp only [diagonalCoordinates_signedCoordinateEquiv] at hi
  by_cases hji : j = i
  · subst hji
    cases s <;> cases r
    · exact (hu (by simpa using hi)).elim
    · rfl
    · rfl
    · exact (hu (by simpa using hi.symm)).elim
  · exfalso
    rw [Pi.mulSingle_eq_of_ne hji] at hi
    apply hu1
    cases s <;> cases r <;> simpa [eq_comm (b := u)] using hi

/-- The coordinate permutation of a normalizer element, relabelled by `Fin m × Bool`. -/
private def signedPerm :
    Subgroup.normalizer (diagonalTorus k m : Set (GLSymplecticFin m k)) →*
      Equiv.Perm (Fin m × Bool) :=
  (signedCoordinateEquiv m).symm.permCongrHom.toMonoidHom.comp (diagonalNormalizerPerm u hu)

private theorem signedPerm_apply
    (g : Subgroup.normalizer (diagonalTorus k m : Set (GLSymplecticFin m k))) (x : Fin m × Bool) :
    signedPerm u hu g x =
      (signedCoordinateEquiv m).symm (diagonalNormalizerPerm u hu g (signedCoordinateEquiv m x)) :=
  (rfl)

/-- A normalizer element carries the two lines of a symplectic plane to the two lines of a single
symplectic plane. -/
private theorem signedPerm_not
    (g : Subgroup.normalizer (diagonalTorus k m : Set (GLSymplecticFin m k))) (x : Fin m × Bool) :
    signedPerm u hu g (x.1, !x.2) = ((signedPerm u hu g x).1, !(signedPerm u hu g x).2) := by
  set e := signedCoordinateEquiv m
  set σ := diagonalNormalizerPerm u hu g
  -- Conjugation by `g⁻¹` moves the diagonal entries by `σ`, and the conjugate is again paired.
  have hentry (t : Fin m → kˣ) : ∃ t' : Fin m → kˣ, ∀ y, diagonalCoordinates t (σ y) =
      diagonalCoordinates t' y := by
    obtain ⟨t', ht'⟩ := mem_diagonalTorus_iff_exists_diagonal.mp
      ((Subgroup.mem_normalizer_iff.mp (g⁻¹).property (diagonal t)).mp
        (mem_diagonalTorus_iff_exists_diagonal.mpr ⟨t, rfl⟩))
    have hconj := coe_diagonalNormalizer_mul_diagonal_mul_inv u hu g⁻¹ t
    rw [← ht', coe_diagonal, map_inv, Equiv.Perm.inv_def, Equiv.symm_symm] at hconj
    exact ⟨t', fun y ↦ (congrFun (diagGL_injective hconj) y).symm⟩
  refine eq_not_of_forall_diagonalCoordinates_eq_inv u hu fun t ↦ ?_
  obtain ⟨t', ht'⟩ := hentry t
  rw [signedPerm_apply, signedPerm_apply, e.apply_symm_apply, e.apply_symm_apply, ht', ht',
    diagonalCoordinates_signedCoordinateEquiv_not]

/-- The coordinate permutation of a normalizer element is determined by how conjugation moves the
diagonal entries. -/
private theorem signedPerm_eq_of_forall
    (g : Subgroup.normalizer (diagonalTorus k m : Set (GLSymplecticFin m k)))
    (τ : Equiv.Perm (Fin m × Bool)) (f : (Fin m → kˣ) → Fin m → kˣ)
    (hf : ∀ t, (g : GLSymplecticFin m k) * diagonal t * (g : GLSymplecticFin m k)⁻¹ =
      diagonal (f t))
    (hτ : ∀ t x, diagonalCoordinates (f t) (signedCoordinateEquiv m (τ x)) =
      diagonalCoordinates t (signedCoordinateEquiv m x)) :
    signedPerm u hu g = τ := by
  have hentry (t : Fin m → kˣ) (x : Fin m × Bool) :
      diagonalCoordinates t ((diagonalNormalizerPerm u hu g).symm (signedCoordinateEquiv m (τ x))) =
        diagonalCoordinates t (signedCoordinateEquiv m x) := by
    have hconj := coe_diagonalNormalizer_mul_diagonal_mul_inv u hu g t
    rw [hf, coe_diagonal] at hconj
    rw [← congrFun (diagGL_injective hconj), hτ]
  have hsymm (x : Fin m × Bool) :
      (diagonalNormalizerPerm u hu g).symm (signedCoordinateEquiv m (τ x)) =
        signedCoordinateEquiv m x := by
    by_contra hne
    obtain ⟨t, ht⟩ := exists_diagonalCoordinates_ne u hu hne
    exact ht (hentry t x)
  ext1 x
  rw [signedPerm_apply, Equiv.symm_apply_eq, ← hsymm x, Equiv.apply_symm_apply]

private theorem signedPerm_positiveLongRootWeylElement (i : Fin m) :
    signedPerm u hu ⟨positiveLongRootWeylElement i,
        positiveLongRootWeylElement_mem_normalizer_diagonalTorus i⟩ =
      WreathProduct.imprimitiveToPerm (Equiv.Perm Bool) (Fin m) Bool
        (SemidirectProduct.inl (Pi.mulSingle i (Equiv.swap false true))) := by
  refine signedPerm_eq_of_forall u hu _ _ (fun t ↦ Function.update t i (t i)⁻¹)
    (fun t ↦ ?_) (fun t x ↦ ?_)
  · rw [positiveLongRootWeylElement_inv, positiveLongRootWeylElement_mul_diagonal_mul_inv]
  · rcases x with ⟨a, s⟩
    by_cases h : a = i
    · subst h
      cases s <;> simp
    · simp [h]

private theorem signedPerm_differenceShortRootWeylElement {i j : Fin m} (hij : i ≠ j) :
    signedPerm u hu ⟨differenceShortRootWeylElement hij,
        differenceShortRootWeylElement_mem_normalizer_diagonalTorus hij⟩ =
      WreathProduct.imprimitiveToPerm (Equiv.Perm Bool) (Fin m) Bool
        (SemidirectProduct.inr (Equiv.swap i j)) := by
  refine signedPerm_eq_of_forall u hu _ _ (fun t ↦ t ∘ Equiv.swap i j)
    (fun t ↦ ?_) (fun t x ↦ ?_)
  · rw [differenceShortRootWeylElement_inv, differenceShortRootWeylElement_mul_diagonal_mul_inv]
  · simp

/-- The action of the normalizer quotient on the coordinate lines, relabelled by `Fin m × Bool`. -/
private def signedQuotientPerm :
    Subgroup.normalizerQuotient (diagonalTorus k m) →* Equiv.Perm (Fin m × Bool) :=
  (signedCoordinateEquiv m).symm.permCongrHom.toMonoidHom.comp
    (diagonalNormalizerQuotientPerm u hu)

private theorem signedQuotientPerm_mk
    (g : Subgroup.normalizer (diagonalTorus k m : Set (GLSymplecticFin m k))) :
    signedQuotientPerm u hu (g : Subgroup.normalizerQuotient (diagonalTorus k m)) =
      signedPerm u hu g := by
  simp [signedQuotientPerm, signedPerm]

private theorem signedQuotientPerm_injective :
    Function.Injective (signedQuotientPerm (m := m) u hu) :=
  (signedCoordinateEquiv m).symm.permCongrHom.injective.comp
    (diagonalNormalizerQuotientPerm_injective u hu)

/-- The normalizer quotient acts on the coordinate lines exactly by the signed permutations. -/
private theorem range_signedQuotientPerm :
    (signedQuotientPerm (m := m) u hu).range =
      (WreathProduct.imprimitiveToPerm (Equiv.Perm Bool) (Fin m) Bool).range := by
  classical
  refine le_antisymm ?_ ?_
  · rintro _ ⟨q, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    exact WreathProduct.mem_range_imprimitiveToPerm_bool_iff.mpr (by
      simpa only [signedQuotientPerm_mk] using signedPerm_not u hu g)
  · rintro _ ⟨w, rfl⟩
    refine WreathProduct.mem_of_inl_mulSingle_swap_mem_of_inr_swap_mem
      (H := (signedQuotientPerm u hu).range.comap _) (fun i ↦ ?_) (fun i j hij ↦ ?_) w
    · exact ⟨_, (signedQuotientPerm_mk u hu _).trans
        (signedPerm_positiveLongRootWeylElement u hu i)⟩
    · exact ⟨_, (signedQuotientPerm_mk u hu _).trans
        (signedPerm_differenceShortRootWeylElement u hu hij)⟩

/-- **The Weyl group of the symplectic diagonal torus.** Over a field with a unit different from
its inverse, the normalizer quotient `N(T)/T` of the paired diagonal torus `T` in `Sp₂ₘ(k)` is the
hyperoctahedral group `Sym(Bool) ≀ Sym(m)` of signed permutations. The class of a normalizer
element acts on `Fin m × Bool` as its coordinate permutation does on the coordinate lines; see
`signedCoordinateEquiv_diagonalNormalizerQuotientMulEquivWreathProduct_smul`. -/
def diagonalNormalizerQuotientMulEquivWreathProduct :
    Subgroup.normalizerQuotient (diagonalTorus k m) ≃* WreathProduct (Equiv.Perm Bool) (Fin m) :=
  ((MonoidHom.ofInjective (signedQuotientPerm_injective u hu)).trans
    (MulEquiv.subgroupCongr (range_signedQuotientPerm u hu))).trans
      (MonoidHom.ofInjective
        (WreathProduct.imprimitiveToPerm_injective (Equiv.Perm Bool) (Fin m) Bool)).symm

private theorem imprimitiveToPerm_diagonalNormalizerQuotientMulEquivWreathProduct
    (q : Subgroup.normalizerQuotient (diagonalTorus k m)) :
    WreathProduct.imprimitiveToPerm (Equiv.Perm Bool) (Fin m) Bool
        (diagonalNormalizerQuotientMulEquivWreathProduct u hu q) =
      signedQuotientPerm u hu q := by
  rw [diagonalNormalizerQuotientMulEquivWreathProduct, MulEquiv.trans_apply,
    MonoidHom.apply_ofInjective_symm]
  simp [MonoidHom.ofInjective_apply]

/-- The hyperoctahedral element attached to a class moves the labelled coordinate lines as the
class moves the coordinate lines of `Fin (m + m)`. -/
@[simp]
theorem signedCoordinateEquiv_diagonalNormalizerQuotientMulEquivWreathProduct_smul
    (q : Subgroup.normalizerQuotient (diagonalTorus k m)) (x : Fin m × Bool) :
    signedCoordinateEquiv m (diagonalNormalizerQuotientMulEquivWreathProduct u hu q • x) =
      diagonalNormalizerQuotientPerm u hu q (signedCoordinateEquiv m x) := by
  have h := congrArg (fun π : Equiv.Perm (Fin m × Bool) ↦ π x)
    (imprimitiveToPerm_diagonalNormalizerQuotientMulEquivWreathProduct u hu q)
  simp only [WreathProduct.imprimitiveToPerm_apply] at h
  rw [WreathProduct.imprimitive_smul, h]
  simp [signedQuotientPerm]

/-- The class of the long-root Weyl representative `n_{2eᵢ}` is the sign change of the `i`-th
coordinate. -/
@[simp]
theorem diagonalNormalizerQuotientMulEquivWreathProduct_positiveLongRootWeylElement
    (i : Fin m) :
    diagonalNormalizerQuotientMulEquivWreathProduct u hu
        ((⟨positiveLongRootWeylElement i,
          positiveLongRootWeylElement_mem_normalizer_diagonalTorus i⟩ :
          Subgroup.normalizer (diagonalTorus k m : Set (GLSymplecticFin m k))) :
          Subgroup.normalizerQuotient (diagonalTorus k m)) =
      SemidirectProduct.inl (Pi.mulSingle i (Equiv.swap false true)) := by
  apply WreathProduct.imprimitiveToPerm_injective (Equiv.Perm Bool) (Fin m) Bool
  rw [imprimitiveToPerm_diagonalNormalizerQuotientMulEquivWreathProduct, signedQuotientPerm_mk,
    signedPerm_positiveLongRootWeylElement]

/-- The class of the short-root Weyl representative `n_{eᵢ-eⱼ}` is the transposition of the
`i`-th and `j`-th coordinates. -/
@[simp]
theorem diagonalNormalizerQuotientMulEquivWreathProduct_differenceShortRootWeylElement
    {i j : Fin m} (hij : i ≠ j) :
    diagonalNormalizerQuotientMulEquivWreathProduct u hu
        ((⟨differenceShortRootWeylElement hij,
          differenceShortRootWeylElement_mem_normalizer_diagonalTorus hij⟩ :
          Subgroup.normalizer (diagonalTorus k m : Set (GLSymplecticFin m k))) :
          Subgroup.normalizerQuotient (diagonalTorus k m)) =
      SemidirectProduct.inr (Equiv.swap i j) := by
  apply WreathProduct.imprimitiveToPerm_injective (Equiv.Perm Bool) (Fin m) Bool
  rw [imprimitiveToPerm_diagonalNormalizerQuotientMulEquivWreathProduct, signedQuotientPerm_mk,
    signedPerm_differenceShortRootWeylElement]

end

end TauCeti.GLSymplecticFin
