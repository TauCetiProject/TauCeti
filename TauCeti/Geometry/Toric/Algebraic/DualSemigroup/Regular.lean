/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Ray.Generation

/-!
# Regular coordinates on the dual semigroup of a toric cone

Let `σ` be a toric cone and let `b` be an integral basis of `N`, indexed by `ToricRay σ ⊕ ι`,
whose vectors at the ray indices are the primitive ray generators of `σ`. Evaluating integral
characters on `b` identifies `N →+ ℤ` with the integer-valued functions on the index set, and an
integral character lies in the dual semigroup of `σ` exactly when it is nonnegative on every
primitive ray generator. The dual semigroup is therefore the monoid of functions that are
nonnegative at the ray indices and arbitrary at the complementary indices, that is, to
`(ToricRay σ →₀ ℕ) × (ι →₀ ℤ)`.

This is the coordinate model `(ι →₀ ℕ) × (κ →₀ ℤ)` consumed by
`TauCeti.Toric.regularAffinePointEquiv`, so for a regular cone it exhibits the complex points of
the affine toric chart as `ℂ ^ k × (ℂ ^ *) ^ (n - k)`, with `k` the number of rays and `n` the
rank of the lattice. As a consequence, the dual semigroup of a regular cone is finitely
generated.

## Main declarations

* `TauCeti.Toric.regularDualSemigroupEquiv`: the regular-coordinate equivalence of the dual
  semigroup attached to a basis extending the primitive ray generators, with
  `TauCeti.Toric.coe_regularDualSemigroupEquiv_fst_apply`,
  `TauCeti.Toric.realCharacter_apply_primitiveGenerator`,
  `TauCeti.Toric.regularDualSemigroupEquiv_snd_apply`,
  `TauCeti.Toric.regularDualSemigroupEquiv_symm_apply_inl` and
  `TauCeti.Toric.regularDualSemigroupEquiv_symm_apply_inr` computing both directions.
* `TauCeti.Toric.dualSemigroupCoord`: the coordinate functional of an extending basis, as an
  element of the dual semigroup, with
  `TauCeti.Toric.regularDualSemigroupEquiv_fst_dualSemigroupCoord_inl`,
  `TauCeti.Toric.regularDualSemigroupEquiv_fst_dualSemigroupCoord_inr` and
  `TauCeti.Toric.regularDualSemigroupEquiv_snd_dualSemigroupCoord` computing the regular
  coordinates, with respect to one extending basis, of the dual basis characters of another.
* `TauCeti.Toric.IsRegularCone.nonempty_dualSemigroup_addEquiv`: the dual semigroup of a regular
  cone with `k` rays in a lattice of rank `n` is isomorphic to `ℕ ^ k × ℤ ^ (n - k)`.
* `TauCeti.Toric.IsRegularCone.fg_dualSemigroup`: the dual semigroup of a regular cone is
  finitely generated.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.2 and 2.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §1.2 and Example 1.2.21.
-/

public section

namespace TauCeti.Toric

variable {N V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}

variable (hi : IsIntegralLattice i) (hσ : IsToricCone i σ) {b : Module.Basis (ToricRay σ ⊕ ι) ℤ N}
  (hb : ∀ ρ, IsPrimitiveGenerator i ρ (b (Sum.inl ρ)))

/-- The regular coordinates of the dual semigroup of a toric cone, attached to an integral basis
indexed by `ToricRay σ ⊕ ι` whose ray vectors are the primitive ray generators. A character
corresponds to its values on the basis: natural numbers at the ray indices, since it is
nonnegative on the primitive ray generators, and arbitrary integers at the complementary
indices. -/
noncomputable def regularDualSemigroupEquiv :
    dualSemigroup hi σ ≃+ (ToricRay σ →₀ ℕ) × (ι →₀ ℤ) :=
  have := ToricRay.finite_of_fg hσ.fg
  have := hi.finite
  have := Module.Finite.finite_basis b
  have : Finite ι := Finite.of_injective (Sum.inr : ι → ToricRay σ ⊕ ι) Sum.inr_injective
  { toFun m := (Finsupp.equivFunOnFinite.symm fun ρ ↦ ((m : N →+ ℤ) (b (Sum.inl ρ))).toNat,
      Finsupp.equivFunOnFinite.symm fun j ↦ (m : N →+ ℤ) (b (Sum.inr j)))
    invFun p := ⟨(b.constr ℤ (Sum.elim (fun ρ ↦ (p.1 ρ : ℤ)) p.2)).toAddMonoidHom,
      (mem_dualSemigroup_iff_of_isPrimitiveGenerator hi hσ hb _).2 fun ρ ↦ by simp⟩
    left_inv m := by
      have hm := (mem_dualSemigroup_iff_of_isPrimitiveGenerator hi hσ hb m).1 m.2
      refine Subtype.ext <| AddMonoidHom.toIntLinearMap_injective <| b.ext fun k ↦ ?_
      rcases k with ρ | j
      · simp [hm ρ]
      · simp
    right_inv p := by
      ext ρ <;> simp
    map_add' m m' := by
      have hm := (mem_dualSemigroup_iff_of_isPrimitiveGenerator hi hσ hb m).1 m.2
      have hm' := (mem_dualSemigroup_iff_of_isPrimitiveGenerator hi hσ hb m').1 m'.2
      refine Prod.ext ?_ ?_
      · ext ρ
        simp [Int.toNat_add (hm ρ) (hm' ρ)]
      · ext j
        simp }

/-- The ray coordinates of a character in the dual semigroup are its values on the primitive ray
generators, which are natural numbers. -/
@[simp]
theorem coe_regularDualSemigroupEquiv_fst_apply (m : dualSemigroup hi σ) (ρ : ToricRay σ) :
    ((regularDualSemigroupEquiv hi hσ hb m).1 ρ : ℤ) = (m : N →+ ℤ) (b (Sum.inl ρ)) := by
  have hm := (mem_dualSemigroup_iff_of_isPrimitiveGenerator hi hσ hb m).1 m.2 ρ
  simp [regularDualSemigroupEquiv, hm]

/-- Evaluating the real character of a dual-semigroup element at a primitive ray generator gives
the corresponding regular ray coordinate, viewed in `ℝ`. -/
theorem realCharacter_apply_primitiveGenerator (m : dualSemigroup hi σ) (ρ : ToricRay σ) :
    hi.realCharacter (m : N →+ ℤ) (i (primitiveGenerator hi hσ ρ)) =
      ((regularDualSemigroupEquiv hi hσ hb m).1 ρ : ℝ) := by
  rw [hi.realCharacter_apply,
    ← (hb ρ).eq_primitiveGenerator hi hσ,
    ← coe_regularDualSemigroupEquiv_fst_apply]
  norm_cast

/-- The complementary coordinates of a character in the dual semigroup are its values on the
complementary basis vectors. -/
@[simp]
theorem regularDualSemigroupEquiv_snd_apply (m : dualSemigroup hi σ) (j : ι) :
    (regularDualSemigroupEquiv hi hσ hb m).2 j = (m : N →+ ℤ) (b (Sum.inr j)) := by
  simp [regularDualSemigroupEquiv]

/-- The character with prescribed regular coordinates takes the prescribed natural value on each
primitive ray generator. -/
@[simp]
theorem regularDualSemigroupEquiv_symm_apply_inl (p : (ToricRay σ →₀ ℕ) × (ι →₀ ℤ))
    (ρ : ToricRay σ) :
    ((regularDualSemigroupEquiv hi hσ hb).symm p : N →+ ℤ) (b (Sum.inl ρ)) = p.1 ρ := by
  simp [regularDualSemigroupEquiv]

/-- The character with prescribed regular coordinates takes the prescribed integral value on each
complementary basis vector. -/
@[simp]
theorem regularDualSemigroupEquiv_symm_apply_inr (p : (ToricRay σ →₀ ℕ) × (ι →₀ ℤ)) (j : ι) :
    ((regularDualSemigroupEquiv hi hσ hb).symm p : N →+ ℤ) (b (Sum.inr j)) = p.2 j := by
  simp [regularDualSemigroupEquiv]

/-! ### The dual basis characters -/

/-- The coordinate functional of a basis extending the primitive ray generators, as an element of
the dual semigroup of the cone: its values on the basis vectors are `0` and `1`, so it is
nonnegative on every primitive ray generator. These characters are the monomials whose values on a
complex point are the regular coordinates of the affine chart of the cone, the ray indices giving
the coordinates that may vanish. -/
noncomputable def dualSemigroupCoord (c : ToricRay σ ⊕ ι) : dualSemigroup hi σ :=
  ⟨(b.coord c).toAddMonoidHom, (mem_dualSemigroup_iff_of_isPrimitiveGenerator hi hσ hb _).2
    fun ρ ↦ by
      rcases eq_or_ne c (Sum.inl ρ) with rfl | hne
      · simp [Module.Basis.coord_apply]
      · simp [Module.Basis.coord_apply, Finsupp.single_eq_of_ne hne]⟩

@[simp]
theorem coe_dualSemigroupCoord (c : ToricRay σ ⊕ ι) :
    ((dualSemigroupCoord hi hσ hb c : dualSemigroup hi σ) : N →+ ℤ) =
      (b.coord c).toAddMonoidHom := by
  simp [dualSemigroupCoord]

/-- A dual basis character takes the value `1` on its own basis vector. -/
theorem dualSemigroupCoord_apply_basis_self (c : ToricRay σ ⊕ ι) :
    ((dualSemigroupCoord hi hσ hb c : dualSemigroup hi σ) : N →+ ℤ) (b c) = 1 := by
  simp [Module.Basis.coord_apply]

/-- A dual basis character vanishes on every other basis vector. -/
theorem dualSemigroupCoord_apply_basis_of_ne {c c' : ToricRay σ ⊕ ι} (h : c' ≠ c) :
    ((dualSemigroupCoord hi hσ hb c : dualSemigroup hi σ) : N →+ ℤ) (b c') = 0 := by
  simp [Module.Basis.coord_apply, Finsupp.single_eq_of_ne (Ne.symm h)]

section

variable {b' : Module.Basis (ToricRay σ ⊕ ι) ℤ N}
  (hb' : ∀ ρ, IsPrimitiveGenerator i ρ (b' (Sum.inl ρ)))

/-- The ray coordinates of the dual basis character of a ray index of a second extending basis form
the standard generator at that ray: both bases carry the primitive generator of a ray at the index
of that ray, so the ray block of the transition matrix is the identity. -/
@[simp]
theorem regularDualSemigroupEquiv_fst_dualSemigroupCoord_inl (ρ : ToricRay σ) :
    (regularDualSemigroupEquiv hi hσ hb (dualSemigroupCoord hi hσ hb' (Sum.inl ρ))).1 =
      Finsupp.single ρ 1 := by
  refine Finsupp.ext fun ρ' ↦ Nat.cast_injective (R := ℤ) ?_
  -- Both bases carry the primitive generator of the ray `ρ'`, and it is unique.
  rw [coe_regularDualSemigroupEquiv_fst_apply,
    (hb ρ').unique hi (hσ.salient.anti fun _ hx ↦ ρ'.1.isFaceOf.le hx) (hb' ρ')]
  rcases eq_or_ne ρ' ρ with rfl | hne
  · simp
  · rw [dualSemigroupCoord_apply_basis_of_ne hi hσ hb' (by simpa using hne),
      Finsupp.single_eq_of_ne hne]
    simp

/-- The dual basis character of a complementary index of a second extending basis has no ray
coordinates: it vanishes on every primitive ray generator, since both bases carry the primitive
generator of a ray at the index of that ray. -/
@[simp]
theorem regularDualSemigroupEquiv_fst_dualSemigroupCoord_inr (j : ι) :
    (regularDualSemigroupEquiv hi hσ hb (dualSemigroupCoord hi hσ hb' (Sum.inr j))).1 = 0 := by
  refine Finsupp.ext fun ρ ↦ Nat.cast_injective (R := ℤ) ?_
  -- Both bases carry the primitive generator of the ray `ρ`, and it is unique.
  rw [coe_regularDualSemigroupEquiv_fst_apply,
    (hb ρ).unique hi (hσ.salient.anti fun _ hx ↦ ρ.1.isFaceOf.le hx) (hb' ρ),
    dualSemigroupCoord_apply_basis_of_ne hi hσ hb' (by simp)]
  simp

/-- The complementary coordinates of the dual basis character of a second extending basis are the
entries of the transition matrix between the two bases. -/
theorem regularDualSemigroupEquiv_snd_dualSemigroupCoord (c : ToricRay σ ⊕ ι) (j : ι) :
    (regularDualSemigroupEquiv hi hσ hb (dualSemigroupCoord hi hσ hb' c)).2 j =
      b'.toMatrix b c (Sum.inr j) := by
  simp [Module.Basis.toMatrix_apply, Module.Basis.coord_apply]

end

/-- The character with a single standard ray coordinate is the dual basis character of that ray
index. -/
@[simp]
theorem regularDualSemigroupEquiv_symm_apply_single_zero (ρ : ToricRay σ) :
    (regularDualSemigroupEquiv hi hσ hb).symm (Finsupp.single ρ 1, 0) =
      dualSemigroupCoord hi hσ hb (Sum.inl ρ) := by
  rw [AddEquiv.symm_apply_eq]
  refine Prod.ext (regularDualSemigroupEquiv_fst_dualSemigroupCoord_inl hi hσ hb hb ρ).symm
    (Finsupp.ext fun j ↦ ?_)
  simp

/-- The character with a single standard complementary coordinate is the dual basis character of
that complementary index. -/
@[simp]
theorem regularDualSemigroupEquiv_symm_apply_zero_single (j : ι) :
    (regularDualSemigroupEquiv hi hσ hb).symm (0, Finsupp.single j 1) =
      dualSemigroupCoord hi hσ hb (Sum.inr j) := by
  rw [AddEquiv.symm_apply_eq]
  refine Prod.ext (regularDualSemigroupEquiv_fst_dualSemigroupCoord_inr hi hσ hb hb j).symm
    (Finsupp.ext fun j' ↦ ?_)
  rcases eq_or_ne j' j with rfl | hne
  · simp
  · rw [Finsupp.single_eq_of_ne hne, regularDualSemigroupEquiv_snd_apply,
      dualSemigroupCoord_apply_basis_of_ne hi hσ hb (c := Sum.inr j) (c' := Sum.inr j')
        (by simpa using hne)]

namespace IsRegularCone

/-- The dual semigroup of a regular cone with `k` rays in a lattice of rank `n` is isomorphic to
`ℕ ^ k × ℤ ^ (n - k)`, the ray coordinates being indexed by the rays themselves. -/
theorem nonempty_dualSemigroup_addEquiv (hi : IsIntegralLattice i) (hσ : IsRegularCone i σ) :
    Nonempty (dualSemigroup hi σ ≃+
      (ToricRay σ →₀ ℕ) × (Fin (Module.finrank ℤ N - Nat.card (ToricRay σ)) →₀ ℤ)) := by
  classical
  obtain ⟨l, b, hb⟩ := hσ.exists_basis_sum
  let _ := ToricRay.finite_of_fg hσ.fg
  let _ := Fintype.ofFinite (ToricRay σ)
  have hl : l = Module.finrank ℤ N - Nat.card (ToricRay σ) := by
    have hrank : Module.finrank ℤ N = Nat.card (ToricRay σ) + l := by
      simpa [Nat.card_sum] using Module.finrank_eq_card_basis b
    omega
  let e := Equiv.sumCongr (Equiv.refl (ToricRay σ)) (finCongr hl)
  exact ⟨regularDualSemigroupEquiv hi hσ.toIsToricCone (b := b.reindex e)
    fun ρ ↦ by simpa [e] using hb ρ⟩

/-- The dual semigroup of a regular cone is finitely generated. -/
theorem fg_dualSemigroup (hi : IsIntegralLattice i) (hσ : IsRegularCone i σ) :
    AddMonoid.FG (dualSemigroup hi σ) := by
  obtain ⟨e⟩ := hσ.nonempty_dualSemigroup_addEquiv hi
  have := ToricRay.finite_of_fg hσ.fg
  have : AddMonoid.FG (Fin (Module.finrank ℤ N - Nat.card (ToricRay σ)) →₀ ℤ) := by
    rw [← AddGroup.fg_iff_addMonoid_fg, ← Module.Finite.iff_addGroup_fg]
    infer_instance
  have : AddMonoid.FG (ToricRay σ →₀ ℕ) := by
    rw [← Module.Finite.iff_addMonoid_fg]
    infer_instance
  exact AddMonoid.fg_of_surjective e.symm.toAddMonoidHom e.symm.surjective

end IsRegularCone

end TauCeti.Toric
