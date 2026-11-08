/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.GLSymplecticFin.signedCoordinateEquiv`, labelling the coordinates of the standard
-- representation by their weights.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Diagonal.WeylGroup
-- The rationality of the entries of the Levi embedding.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.PolynomialFunctions.SymplecticLevi
-- The weight-space decomposition of a rational representation of `GL m ℂ`.
public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Decomposition
-- The permutation symmetry of the weight spaces of `GL m`.
public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Weyl

/-!
# Weights of the symplectic group

The diagonal torus of the symplectic group `Sp₂ₘ`, in the `Fin (m + m)` coordinates of
`TauCeti.GLSymplecticFin`, consists of the matrices `diag(t₀, …, tₘ₋₁, t₀⁻¹, …, tₘ₋₁⁻¹)`
(`TauCeti.GLSymplecticFin.diagonal`). A vector of a representation `ρ` of `Sp₂ₘ` has **weight**
`l : Fin m → ℤ` when every such matrix scales it by `∏ i, tᵢ ^ lᵢ`, and these vectors form the
weight space `TauCeti.symplecticWeightSpace ρ l`. This file proves that a rational representation of
`Sp₂ₘ(ℂ)` is the internal direct sum of its weight spaces, computes the weights of the standard
representation, and shows that weight multiplicities are invariant under the Weyl group of type
`Cₘ`, the signed permutations of the coordinates.

## The Levi subgroup

The torus of `Sp₂ₘ` is the diagonal torus of its Levi subgroup `GL m`, embedded by
`A ↦ diag(A, (A⁻¹)ᵀ)` (`TauCeti.GLSymplecticFin.leviHom_diagGL`). So the weight spaces of `ρ` are
the weight spaces of its restriction `ρ.comp leviHom` to `GL m`, read through the existing weight
theory of the general linear group (`TauCeti.symplecticWeightSpace_eq_weightSpace_comp_leviHom`).
The work is to show that this restriction is rational when `ρ` is
(`TauCeti.IsRationalSpRep.isRationalRep_comp_leviHom`): each entry of the Levi matrix is an entry
of `A`, an entry of `A⁻¹`, or zero, and the entries of `A⁻¹` are rational functions of `A`
(`TauCeti.GLSymplecticFin.entry_leviHom_mem_rationalFunctions`). The weight-space
decomposition of rational representations of `GL m ℂ` then applies.

A **rational representation** of `Sp₂ₘ(ℂ)` (`TauCeti.IsRationalSpRep`) is one whose matrix entries,
in some basis, are polynomials in the entries of the symplectic matrix. As for `SL n`, no
determinant denominator is needed, because a symplectic matrix has determinant one
(`TauCeti.GLSymplecticFin.det_eq_one`); every rational representation of `GL (m + m) ℂ` restricts to
one (`TauCeti.IsRationalRep.isRationalSpRep_comp_subtype`).

## The Weyl group

The Weyl group of type `Cₘ` acts on weights by permuting and negating coordinates. Permutations are
realized in the Levi subgroup by permutation matrices, so they are inherited from `GL m`
(`TauCeti.symplecticWeightSpace_map_leviHom_permutationGL`). A sign change is realized by the
long-root Weyl representative `n_{2eᵢ}`, which exchanges the two coordinate lines of the `i`-th
symplectic plane and inverts the `i`-th coordinate of the torus
(`TauCeti.symplecticWeightSpace_map_positiveLongRootWeylElement`). Combining the two, every weight
is carried to its **dominant representative**, the absolute values of its coordinates sorted into
decreasing order (`TauCeti.exists_symplecticWeightSpace_map_eq_dominantWeightOf_abs`). This is the
dominant chamber of type `Cₘ`: weakly decreasing sequences of nonnegative integers.

## Main definitions

* `TauCeti.IsRationalSpRep`: a representation of `Sp₂ₘ(ℂ)` whose matrix entries are polynomials in
  the matrix entries of the group element.
* `TauCeti.symplecticWeightSpace`: the weight space of weight `l : Fin m → ℤ`.
* `TauCeti.symplecticCoordinateWeight`: the weight `±eᵢ` of a coordinate line of the standard
  representation.

## Main results

* `TauCeti.IsRationalSpRep.isInternal_symplecticWeightSpace`: **a rational representation of
  `Sp₂ₘ(ℂ)` is the internal direct sum of its weight spaces.**
* `TauCeti.isRationalSpRep_stdRep`,
  `TauCeti.symplecticWeightSpace_stdRep_symplecticCoordinateWeight` and
  `TauCeti.symplecticWeightSpace_stdRep_eq_bot`: the standard representation is rational, and
  its weights are the `±eᵢ`, each on a coordinate line.
* `TauCeti.finrank_symplecticWeightSpace_update_neg` and
  `TauCeti.finrank_symplecticWeightSpace_comp_perm`: weight multiplicities are invariant under sign
  changes and permutations of the coordinates.
* `TauCeti.finrank_symplecticWeightSpace_dominantWeightOf_abs` and
  `TauCeti.symplecticWeightSpace_eq_bot_dominantWeightOf_abs_iff`: the dominant representative of a
  weight carries the same multiplicity.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 16.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants* (2009), Chapters 2
  and 3.
-/

public section

open Matrix MvPolynomial TauCeti.Matrix.GeneralLinearGroup

universe u v

namespace TauCeti

variable {m : ℕ}

/-! ### Rational representations -/

section Rational

variable {W : Type v} [AddCommMonoid W] [Module ℂ W]

/-- **A rational representation** of `Sp₂ₘ(ℂ)`: in some basis of the carrier, every matrix entry
of `ρ s` is a polynomial in the entries of `s`. A symplectic matrix has determinant one, so no
determinant denominator is needed, and this is the condition `TauCeti.IsRationalRep` read on the
symplectic group. The carrier is forced to be finite-dimensional
(`TauCeti.IsRationalSpRep.finite`). The base field is `ℂ` for the reason recorded on
`TauCeti.IsPolynomialRep`. -/
def IsRationalSpRep (ρ : Representation ℂ (GLSymplecticFin m ℂ) W) : Prop :=
  ∃ (b : Module.Basis (Fin (Module.finrank ℂ W)) ℂ W)
    (P : Fin (Module.finrank ℂ W) → Fin (Module.finrank ℂ W) →
      MvPolynomial (Fin (m + m) × Fin (m + m)) ℂ),
    ∀ (s : GLSymplecticFin m ℂ) (i j : Fin (Module.finrank ℂ W)),
      LinearMap.toMatrix b b (ρ s) i j =
        MvPolynomial.eval (fun p => ((s : GL (Fin (m + m)) ℂ) :
          Matrix (Fin (m + m)) (Fin (m + m)) ℂ) p.1 p.2) (P i j)

/-- The coordinate-entry form of `TauCeti.IsRationalSpRep`, as a lemma. -/
theorem isRationalSpRep_iff (ρ : Representation ℂ (GLSymplecticFin m ℂ) W) :
    IsRationalSpRep ρ ↔ ∃ (b : Module.Basis (Fin (Module.finrank ℂ W)) ℂ W)
      (P : Fin (Module.finrank ℂ W) → Fin (Module.finrank ℂ W) →
        MvPolynomial (Fin (m + m) × Fin (m + m)) ℂ),
      ∀ (s : GLSymplecticFin m ℂ) (i j : Fin (Module.finrank ℂ W)),
        LinearMap.toMatrix b b (ρ s) i j =
          MvPolynomial.eval (fun p => ((s : GL (Fin (m + m)) ℂ) :
            Matrix (Fin (m + m)) (Fin (m + m)) ℂ) p.1 p.2) (P i j) :=
  (Iff.rfl)

/-- The carrier of a rational representation of `Sp₂ₘ(ℂ)` is finite-dimensional. -/
theorem IsRationalSpRep.finite {ρ : Representation ℂ (GLSymplecticFin m ℂ) W}
    (h : IsRationalSpRep ρ) : Module.Finite ℂ W := by
  obtain ⟨b, -⟩ := h
  exact Module.Finite.of_basis b

/-- **A rational representation of `GL (m + m) ℂ` restricts to a rational representation of
`Sp₂ₘ(ℂ)`**: the determinant denominator is `1` on the symplectic group. -/
theorem IsRationalRep.isRationalSpRep_comp_subtype {ρ : Representation ℂ (GL (Fin (m + m)) ℂ) W}
    (h : IsRationalRep ρ) : IsRationalSpRep (ρ.comp (GLSymplecticFin m ℂ).subtype) := by
  obtain ⟨b, P, d, hP⟩ := (isRationalRep_iff ρ).mp h
  refine ⟨b, P, fun s i j => ?_⟩
  rw [MonoidHom.comp_apply, hP, Subgroup.coe_subtype, GLSymplecticFin.det_eq_one, one_pow,
    inv_one, one_mul]

/-- **The restriction of a rational representation of `Sp₂ₘ(ℂ)` to its Levi subgroup `GL m ℂ` is
rational.** The matrix entries of `ρ (leviHom A)` are polynomials in the entries of the Levi matrix
`diag(A, (A⁻¹)ᵀ)`, and these are rational functions of `A`. -/
theorem IsRationalSpRep.isRationalRep_comp_leviHom {ρ : Representation ℂ (GLSymplecticFin m ℂ) W}
    (h : IsRationalSpRep ρ) : IsRationalRep (ρ.comp GLSymplecticFin.leviHom) := by
  obtain ⟨b, P, hP⟩ := h
  -- the matrix entries of the Levi embedding, as functions on `GL m ℂ`
  set x : Fin (m + m) × Fin (m + m) → GL (Fin m) ℂ → ℂ := fun p A =>
    (((GLSymplecticFin.leviHom A : GLSymplecticFin m ℂ) : GL (Fin (m + m)) ℂ) :
      Matrix (Fin (m + m)) (Fin (m + m)) ℂ) p.1 p.2 with hx
  have hrange : (MvPolynomial.aeval x).range ≤ rationalFunctions ℂ m := by
    rw [MvPolynomial.aeval_range]
    exact Algebra.adjoin_le
      (Set.range_subset_iff.mpr GLSymplecticFin.entry_leviHom_mem_rationalFunctions)
  refine (isRationalRep_iff_forall_mem_rationalFunctions b).mpr fun i j => ?_
  have hfun : (fun A : GL (Fin m) ℂ =>
      LinearMap.toMatrix b b ((ρ.comp GLSymplecticFin.leviHom) A) i j) =
        MvPolynomial.aeval x (P i j) := by
    funext A
    rw [MonoidHom.comp_apply, hP]
    simpa [aeval_eq_eval, hx] using
      (comp_aeval_apply x (Pi.evalAlgHom ℂ (fun _ : GL (Fin m) ℂ => ℂ) A) (P i j)).symm
  rw [hfun]
  exact hrange (AlgHom.mem_range_self _ _)

end Rational

/-! ### Weight spaces -/

section CommRing

variable {k : Type u} [CommRing k]
variable {W : Type v} [AddCommGroup W] [Module k W]

/-- The **weight space** of weight `l : Fin m → ℤ` of a representation of the symplectic group:
the vectors that every torus element `diag(t₀, …, tₘ₋₁, t₀⁻¹, …, tₘ₋₁⁻¹)` scales by
`∏ i, tᵢ ^ lᵢ` (`TauCeti.mem_symplecticWeightSpace_iff`). The torus is the diagonal torus of the
Levi subgroup `GL m`, so this is the weight space of the restriction of the representation to
that subgroup (`TauCeti.symplecticWeightSpace_eq_weightSpace_comp_leviHom`). -/
noncomputable def symplecticWeightSpace (ρ : Representation k (GLSymplecticFin m k) W)
    (l : Fin m → ℤ) : Submodule k W :=
  weightSpace (ρ.comp GLSymplecticFin.leviHom) l

/-- The weight spaces of a representation of `Sp₂ₘ` are those of its restriction to the Levi
subgroup `GL m`. -/
theorem symplecticWeightSpace_eq_weightSpace_comp_leviHom
    (ρ : Representation k (GLSymplecticFin m k) W) (l : Fin m → ℤ) :
    symplecticWeightSpace ρ l = weightSpace (ρ.comp GLSymplecticFin.leviHom) l :=
  (rfl)

/-- Membership in a weight space is the eigen-relation at every point of the torus. -/
@[simp]
theorem mem_symplecticWeightSpace_iff (ρ : Representation k (GLSymplecticFin m k) W)
    (l : Fin m → ℤ) (w : W) :
    w ∈ symplecticWeightSpace ρ l ↔
      ∀ t : Fin m → kˣ, ρ (GLSymplecticFin.diagonal t) w = ((weightChar k l t : kˣ) : k) • w := by
  simp only [symplecticWeightSpace_eq_weightSpace_comp_leviHom, mem_weightSpace_iff,
    MonoidHom.comp_apply, GLSymplecticFin.leviHom_diagGL]

/-- The action of a torus element on a weight vector. -/
theorem apply_of_mem_symplecticWeightSpace {ρ : Representation k (GLSymplecticFin m k) W}
    {l : Fin m → ℤ} {w : W} (hw : w ∈ symplecticWeightSpace ρ l) (t : Fin m → kˣ) :
    ρ (GLSymplecticFin.diagonal t) w = ((weightChar k l t : kˣ) : k) • w :=
  (mem_symplecticWeightSpace_iff ρ l w).mp hw t

end CommRing

section Field

variable {k : Type u} [Field k]
variable {W : Type v} [AddCommGroup W] [Module k W]

/-- **The weight spaces of a representation of `Sp₂ₘ` are independent**, as soon as distinct
weights give distinct characters of the torus. -/
theorem iSupIndep_symplecticWeightSpace (hchar : Function.Injective (weightChar k (κ := Fin m)))
    (ρ : Representation k (GLSymplecticFin m k) W) :
    iSupIndep fun l : Fin m → ℤ ↦ symplecticWeightSpace ρ l :=
  iSupIndep_weightSpace hchar (ρ.comp GLSymplecticFin.leviHom)

/-- **Spanning is the whole of the weight-space decomposition**: once distinct weights give
distinct characters, a representation whose weight spaces span it is their internal direct sum. -/
theorem isInternal_symplecticWeightSpace_of_iSup_eq_top
    (hchar : Function.Injective (weightChar k (κ := Fin m)))
    {ρ : Representation k (GLSymplecticFin m k) W}
    (h : ⨆ l : Fin m → ℤ, symplecticWeightSpace ρ l = ⊤) :
    DirectSum.IsInternal fun l : Fin m → ℤ ↦ symplecticWeightSpace ρ l :=
  isInternal_weightSpace_of_iSup_eq_top hchar h

/-- **A finite-dimensional representation of `Sp₂ₘ` has only finitely many weights**, as soon as
distinct weights give distinct characters of the torus. Without that condition the statement can
fail: over `𝔽₂` the torus is trivial and every weight space is the whole representation. -/
theorem finite_setOf_symplecticWeightSpace_ne_bot [Module.Finite k W]
    (hchar : Function.Injective (weightChar k (κ := Fin m)))
    (ρ : Representation k (GLSymplecticFin m k) W) :
    {l : Fin m → ℤ | symplecticWeightSpace ρ l ≠ ⊥}.Finite :=
  finite_setOf_weightSpace_ne_bot hchar (ρ.comp GLSymplecticFin.leviHom)

end Field

/-! ### The weight-space decomposition of a rational representation -/

section Decomposition

variable {W : Type v} [AddCommGroup W] [Module ℂ W]
variable {ρ : Representation ℂ (GLSymplecticFin m ℂ) W}

/-- **The weight spaces of a rational representation of `Sp₂ₘ(ℂ)` span it**, because those of its
rational restriction to the Levi subgroup do. -/
theorem IsRationalSpRep.iSup_symplecticWeightSpace_eq_top (h : IsRationalSpRep ρ) :
    ⨆ l : Fin m → ℤ, symplecticWeightSpace ρ l = ⊤ :=
  h.isRationalRep_comp_leviHom.iSup_weightSpace_eq_top

/-- **A nonzero rational representation of `Sp₂ₘ(ℂ)` has a weight.** -/
theorem IsRationalSpRep.exists_symplecticWeightSpace_ne_bot [Nontrivial W] (h : IsRationalSpRep ρ) :
    ∃ l : Fin m → ℤ, symplecticWeightSpace ρ l ≠ ⊥ :=
  h.isRationalRep_comp_leviHom.exists_weightSpace_ne_bot

/-- **The weight-space decomposition.** A rational representation of `Sp₂ₘ(ℂ)` is the internal
direct sum of its weight spaces: the diagonal torus is simultaneously diagonalizable on it, and
every joint eigencharacter is one of the monomial characters `t ↦ ∏ i, tᵢ ^ lᵢ`. Which weights
actually occur is not part of the statement. -/
theorem IsRationalSpRep.isInternal_symplecticWeightSpace (h : IsRationalSpRep ρ) :
    DirectSum.IsInternal fun l : Fin m → ℤ ↦ symplecticWeightSpace ρ l :=
  h.isRationalRep_comp_leviHom.isInternal_weightSpace

end Decomposition

/-! ### The standard representation

The standard representation of `Sp₂ₘ` is the restriction `(stdRep k (m + m)).comp subtype` of the
standard representation of `GL (m + m)`. The torus acts on the coordinate line of
`signedCoordinateEquiv m (i, false)` by `tᵢ` and on that of `signedCoordinateEquiv m (i, true)` by
`tᵢ⁻¹`, so these lines have the weights `eᵢ` and `-eᵢ`. -/

section Standard

variable {k : Type u} [CommRing k]

/-- The weight of a coordinate line of the standard representation of `Sp₂ₘ`: the line labelled
`(i, false)` by `TauCeti.GLSymplecticFin.signedCoordinateEquiv` has weight `eᵢ`, and the line
labelled `(i, true)` has weight `-eᵢ`. -/
def symplecticCoordinateWeight (x : Fin m × Bool) : Fin m → ℤ :=
  Pi.single x.1 (if x.2 then -1 else 1)

@[simp]
theorem symplecticCoordinateWeight_false (i : Fin m) :
    symplecticCoordinateWeight (i, false) = Pi.single i 1 :=
  (rfl)

@[simp]
theorem symplecticCoordinateWeight_true (i : Fin m) :
    symplecticCoordinateWeight (i, true) = Pi.single i (-1) :=
  (rfl)

/-- Distinct coordinate lines have distinct weights. -/
theorem symplecticCoordinateWeight_injective :
    Function.Injective (symplecticCoordinateWeight (m := m)) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  have hi := congrFun h i
  by_cases hij : j = i
  · subst hij
    cases a <;> cases b <;> simp_all [symplecticCoordinateWeight]
  · cases a <;> simp_all [symplecticCoordinateWeight]

/-- The character of the weight of a coordinate line is the diagonal entry of the torus on that
line. -/
theorem weightChar_symplecticCoordinateWeight (x : Fin m × Bool) (t : Fin m → kˣ) :
    weightChar k (symplecticCoordinateWeight x) t =
      GLSymplecticFin.diagonalCoordinates t (GLSymplecticFin.signedCoordinateEquiv m x) := by
  rw [GLSymplecticFin.diagonalCoordinates_signedCoordinateEquiv, weightChar_apply,
    symplecticCoordinateWeight, torusCharacter_single]
  cases x.2 <;> simp

/-- **The standard basis vector of a coordinate line is a weight vector** of the weight of that
line. -/
theorem basisFun_mem_symplecticWeightSpace_stdRep (x : Fin m × Bool) :
    Pi.basisFun k (Fin (m + m)) (GLSymplecticFin.signedCoordinateEquiv m x) ∈
      symplecticWeightSpace ((stdRep k (m + m)).comp (GLSymplecticFin m k).subtype)
        (symplecticCoordinateWeight x) := by
  rw [mem_symplecticWeightSpace_iff]
  intro t
  rw [MonoidHom.comp_apply, Subgroup.coe_subtype, GLSymplecticFin.coe_diagonal,
    stdRep_diagGL_apply_basisFun, weightChar_symplecticCoordinateWeight]

/-- The weight spaces of the standard representation of `Sp₂ₘ` span it, because the weight space
of each weight `±eᵢ` contains the corresponding standard basis vector. -/
theorem iSup_symplecticWeightSpace_stdRep_eq_top :
    ⨆ l : Fin m → ℤ,
      symplecticWeightSpace ((stdRep k (m + m)).comp (GLSymplecticFin m k).subtype) l = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← (Pi.basisFun k (Fin (m + m))).span_eq, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  obtain ⟨x, rfl⟩ := (GLSymplecticFin.signedCoordinateEquiv m).surjective a
  exact le_iSup (fun l : Fin m → ℤ ↦
      symplecticWeightSpace ((stdRep k (m + m)).comp (GLSymplecticFin m k).subtype) l)
    (symplecticCoordinateWeight x) (basisFun_mem_symplecticWeightSpace_stdRep x)

end Standard

section StandardDomain

variable {k : Type u} [CommRing k] [IsDomain k]

/-- **A nonzero coordinate pins the weight.** If a weight vector of weight `l` of the standard
representation of `Sp₂ₘ` has a nonzero coordinate on the line labelled `x`, then `l` is the weight
of that line. -/
theorem eq_symplecticCoordinateWeight_of_mem_symplecticWeightSpace_stdRep
    (hchar : Function.Injective (weightChar k (κ := Fin m))) {l : Fin m → ℤ}
    {w : Fin (m + m) → k}
    (hw : w ∈ symplecticWeightSpace ((stdRep k (m + m)).comp (GLSymplecticFin m k).subtype) l)
    {x : Fin m × Bool} (hx : w (GLSymplecticFin.signedCoordinateEquiv m x) ≠ 0) :
    l = symplecticCoordinateWeight x := by
  refine hchar (MonoidHom.ext fun t ↦ ?_)
  have h := congrFun (apply_of_mem_symplecticWeightSpace hw t)
    (GLSymplecticFin.signedCoordinateEquiv m x)
  rw [MonoidHom.comp_apply, Subgroup.coe_subtype, GLSymplecticFin.coe_diagonal,
    stdRep_diagGL_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [weightChar_symplecticCoordinateWeight]
  exact Units.ext (mul_right_cancel₀ hx h).symm

/-- Off the weights `±eᵢ` the standard representation of `Sp₂ₘ` has no weight vectors. -/
theorem symplecticWeightSpace_stdRep_eq_bot
    (hchar : Function.Injective (weightChar k (κ := Fin m))) {l : Fin m → ℤ}
    (hl : ∀ x : Fin m × Bool, l ≠ symplecticCoordinateWeight x) :
    symplecticWeightSpace ((stdRep k (m + m)).comp (GLSymplecticFin m k).subtype) l = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun w hw ↦ funext fun a ↦ ?_
  obtain ⟨x, rfl⟩ := (GLSymplecticFin.signedCoordinateEquiv m).surjective a
  by_contra hx
  exact hl x (eq_symplecticCoordinateWeight_of_mem_symplecticWeightSpace_stdRep hchar hw hx)

/-- **The weight spaces of the standard representation of `Sp₂ₘ` are its coordinate lines**: the
weight space of the weight `±eᵢ` of a coordinate line is that line. -/
theorem symplecticWeightSpace_stdRep_symplecticCoordinateWeight
    (hchar : Function.Injective (weightChar k (κ := Fin m))) (x : Fin m × Bool) :
    symplecticWeightSpace ((stdRep k (m + m)).comp (GLSymplecticFin m k).subtype)
        (symplecticCoordinateWeight x) =
      Submodule.span k
        {Pi.basisFun k (Fin (m + m)) (GLSymplecticFin.signedCoordinateEquiv m x)} := by
  refine le_antisymm (fun w hw ↦ ?_) ?_
  · rw [Submodule.mem_span_singleton]
    refine ⟨w (GLSymplecticFin.signedCoordinateEquiv m x), funext fun a ↦ ?_⟩
    obtain ⟨y, rfl⟩ := (GLSymplecticFin.signedCoordinateEquiv m).surjective a
    by_cases hyx : y = x
    · subst hyx
      simp
    · have hzero : w (GLSymplecticFin.signedCoordinateEquiv m y) = 0 := by
        by_contra hy
        exact hyx (symplecticCoordinateWeight_injective
          (eq_symplecticCoordinateWeight_of_mem_symplecticWeightSpace_stdRep hchar hw hy).symm)
      have hne : GLSymplecticFin.signedCoordinateEquiv m y ≠
          GLSymplecticFin.signedCoordinateEquiv m x :=
        (GLSymplecticFin.signedCoordinateEquiv m).injective.ne hyx
      simp [hzero, Pi.basisFun_apply, hne]
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact basisFun_mem_symplecticWeightSpace_stdRep x

end StandardDomain

/-- **The standard representation of `Sp₂ₘ` is the internal direct sum of its weight spaces.** -/
theorem isInternal_symplecticWeightSpace_stdRep {k : Type u} [Field k]
    (hchar : Function.Injective (weightChar k (κ := Fin m))) :
    DirectSum.IsInternal fun l : Fin m → ℤ ↦
      symplecticWeightSpace ((stdRep k (m + m)).comp (GLSymplecticFin m k).subtype) l :=
  isInternal_symplecticWeightSpace_of_iSup_eq_top hchar iSup_symplecticWeightSpace_stdRep_eq_top

/-- **The standard representation of `Sp₂ₘ(ℂ)` is rational**, being the restriction of the
polynomial standard representation of `GL (m + m) ℂ`. -/
theorem isRationalSpRep_stdRep :
    IsRationalSpRep ((stdRep ℂ (m + m)).comp (GLSymplecticFin m ℂ).subtype) :=
  (isPolynomialRep_stdRep (m + m)).isRationalRep.isRationalSpRep_comp_subtype

/-! ### The Weyl group of type `Cₘ` acting on the weights -/

section Weyl

variable {k : Type u} [CommRing k]

variable {W : Type v} [AddCommGroup W] [Module k W] (ρ : Representation k (GLSymplecticFin m k) W)

/-- An element conjugating the torus by the sign change of the `i`-th coordinate carries weight
vectors of `l` to weight vectors of `l` with its `i`-th coordinate negated. -/
private theorem apply_mem_symplecticWeightSpace_update_neg {g : GLSymplecticFin m k} {i : Fin m}
    (hg : ∀ t : Fin m → kˣ, g⁻¹ * GLSymplecticFin.diagonal t * g =
      GLSymplecticFin.diagonal (Function.update t i (t i)⁻¹))
    {l : Fin m → ℤ} {w : W} (hw : w ∈ symplecticWeightSpace ρ l) :
    ρ g w ∈ symplecticWeightSpace ρ (Function.update l i (-l i)) := by
  rw [mem_symplecticWeightSpace_iff]
  intro t
  have hconj : GLSymplecticFin.diagonal t * g =
      g * GLSymplecticFin.diagonal (Function.update t i (t i)⁻¹) := by
    rw [← hg t]
    group
  rw [← mul_apply_eq_comp, ← map_mul, hconj, map_mul, mul_apply_eq_comp,
    apply_of_mem_symplecticWeightSpace hw, map_smul, weightChar_update_neg]

/-- **The long-root Weyl representative `n_{2eᵢ}` carries the weight space of `l` onto the weight
space of `l` with its `i`-th coordinate negated.** -/
theorem symplecticWeightSpace_map_positiveLongRootWeylElement (i : Fin m) (l : Fin m → ℤ) :
    (symplecticWeightSpace ρ l).map (ρ (GLSymplecticFin.positiveLongRootWeylElement i)) =
      symplecticWeightSpace ρ (Function.update l i (-l i)) := by
  refine le_antisymm ?_ fun v hv ↦ ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact apply_mem_symplecticWeightSpace_update_neg ρ
      (GLSymplecticFin.positiveLongRootWeylElement_inv_mul_diagonal_mul i) hw
  · refine ⟨ρ (GLSymplecticFin.negativeLongRootWeylElement i) v, ?_, ?_⟩
    · simpa using apply_mem_symplecticWeightSpace_update_neg ρ
        (GLSymplecticFin.negativeLongRootWeylElement_inv_mul_diagonal_mul i) hv
    · rw [← GLSymplecticFin.positiveLongRootWeylElement_inv]
      exact ρ.self_inv_apply _ v

/-- **Weight multiplicities are invariant under the sign change of a coordinate.** -/
@[simp]
theorem finrank_symplecticWeightSpace_update_neg (i : Fin m) (l : Fin m → ℤ) :
    Module.finrank k (symplecticWeightSpace ρ (Function.update l i (-l i))) =
      Module.finrank k (symplecticWeightSpace ρ l) := by
  rw [← symplecticWeightSpace_map_positiveLongRootWeylElement]
  exact (LinearMap.GeneralLinearGroup.toLinearEquiv
    (ρ.asGroupHom (GLSymplecticFin.positiveLongRootWeylElement i))).finrank_map_eq _

/-- **The permutation matrix of `σ` in the Levi subgroup carries the weight space of `l` onto the
weight space of `l ∘ σ⁻¹`.** -/
theorem symplecticWeightSpace_map_leviHom_permutationGL (σ : Equiv.Perm (Fin m))
    (l : Fin m → ℤ) :
    (symplecticWeightSpace ρ l).map (ρ (GLSymplecticFin.leviHom (permutationGL (k := k) σ))) =
      symplecticWeightSpace ρ (l ∘ ⇑σ⁻¹) :=
  weightSpace_map_permutationGL (ρ.comp GLSymplecticFin.leviHom) σ l

/-- **Weight multiplicities are invariant under permutations of the coordinates.** -/
@[simp]
theorem finrank_symplecticWeightSpace_comp_perm (σ : Equiv.Perm (Fin m)) (l : Fin m → ℤ) :
    Module.finrank k (symplecticWeightSpace ρ (l ∘ ⇑σ)) =
      Module.finrank k (symplecticWeightSpace ρ l) :=
  finrank_weightSpace_comp_perm (ρ.comp GLSymplecticFin.leviHom) σ l

/-- Negating the coordinates of a weight in a finite set of indices is realized by a group
element. -/
private theorem exists_map_eq_symplecticWeightSpace_neg_ite (s : Finset (Fin m))
    (l : Fin m → ℤ) : ∃ g : GLSymplecticFin m k,
      (symplecticWeightSpace ρ l).map (ρ g) =
        symplecticWeightSpace ρ fun j ↦ if j ∈ s then -l j else l j := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp [Module.End.one_eq_id]⟩
  | insert a s ha ih =>
    obtain ⟨g, hg⟩ := ih
    refine ⟨GLSymplecticFin.positiveLongRootWeylElement a * g, ?_⟩
    have hupdate : (fun j ↦ if j ∈ insert a s then -l j else l j) =
        Function.update (fun j ↦ if j ∈ s then -l j else l j) a
          (-(fun j ↦ if j ∈ s then -l j else l j) a) := by
      funext j
      by_cases hja : j = a
      · subst hja
        simp [ha]
      · simp [hja]
    rw [map_mul, Module.End.mul_eq_comp, Submodule.map_comp, hg, hupdate,
      symplecticWeightSpace_map_positiveLongRootWeylElement]

/-- **Every weight is carried by a group element to its dominant representative**: the absolute
values of its coordinates, sorted into decreasing order. This is the dominant chamber of the Weyl
group of type `Cₘ`, the weakly decreasing sequences of nonnegative integers. -/
theorem exists_symplecticWeightSpace_map_eq_dominantWeightOf_abs (l : Fin m → ℤ) :
    ∃ g : GLSymplecticFin m k, (symplecticWeightSpace ρ l).map (ρ g) =
      symplecticWeightSpace ρ (dominantWeightOf fun i ↦ |l i| : Fin m → ℤ) := by
  classical
  obtain ⟨g, hg⟩ := exists_map_eq_symplecticWeightSpace_neg_ite ρ
    (Finset.univ.filter fun j ↦ l j < 0) l
  have habs : (fun j ↦ if j ∈ Finset.univ.filter (fun j ↦ l j < 0) then -l j else l j) =
      fun j ↦ |l j| := by
    funext j
    by_cases hj : l j < 0
    · simp [hj, abs_of_neg hj]
    · simp [hj, abs_of_nonneg (not_lt.mp hj)]
  rw [habs] at hg
  set σ := dominantSort fun i ↦ |l i|
  refine ⟨GLSymplecticFin.leviHom (permutationGL (k := k) σ⁻¹) * g, ?_⟩
  rw [map_mul, Module.End.mul_eq_comp, Submodule.map_comp, hg,
    symplecticWeightSpace_map_leviHom_permutationGL, inv_inv, coe_dominantWeightOf]

/-- **The dominant representative of a weight carries the same multiplicity.** -/
@[simp]
theorem finrank_symplecticWeightSpace_dominantWeightOf_abs (l : Fin m → ℤ) :
    Module.finrank k
        (symplecticWeightSpace ρ (dominantWeightOf fun i ↦ |l i| : Fin m → ℤ)) =
      Module.finrank k (symplecticWeightSpace ρ l) := by
  obtain ⟨g, hg⟩ := exists_symplecticWeightSpace_map_eq_dominantWeightOf_abs ρ l
  rw [← hg]
  exact (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g)).finrank_map_eq _

/-- **A weight occurs exactly when its dominant representative does**, so the weights of a
representation of `Sp₂ₘ` are determined by the dominant ones. -/
theorem symplecticWeightSpace_eq_bot_dominantWeightOf_abs_iff (l : Fin m → ℤ) :
    symplecticWeightSpace ρ (dominantWeightOf fun i ↦ |l i| : Fin m → ℤ) = ⊥ ↔
      symplecticWeightSpace ρ l = ⊥ := by
  obtain ⟨g, hg⟩ := exists_symplecticWeightSpace_map_eq_dominantWeightOf_abs ρ l
  rw [← hg]
  exact Submodule.map_eq_bot_iff
    (e := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g))

end Weyl

end TauCeti
