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

* `TauCeti.Toric.mem_dualSemigroup_iff_of_isPrimitiveGenerator`: membership in the dual
  semigroup, read off from the values of a character on any choice of primitive ray generators.
* `TauCeti.Toric.regularDualSemigroupEquiv`: the regular-coordinate equivalence of the dual
  semigroup attached to a basis extending the primitive ray generators, with
  `TauCeti.Toric.coe_regularDualSemigroupEquiv_fst_apply`,
  `TauCeti.Toric.regularDualSemigroupEquiv_snd_apply`,
  `TauCeti.Toric.regularDualSemigroupEquiv_symm_apply_inl` and
  `TauCeti.Toric.regularDualSemigroupEquiv_symm_apply_inr` computing both directions.
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

/-- An integral character lies in the dual semigroup of a toric cone exactly when it is
nonnegative on a chosen primitive generator of each ray. -/
theorem mem_dualSemigroup_iff_of_isPrimitiveGenerator (hi : IsIntegralLattice i)
    (hσ : IsToricCone i σ) {v : ToricRay σ → N} (hv : ∀ ρ, IsPrimitiveGenerator i ρ (v ρ))
    (m : N →+ ℤ) : m ∈ dualSemigroup hi σ ↔ ∀ ρ : ToricRay σ, 0 ≤ m (v ρ) := by
  simp only [mem_dualSemigroup_iff_primitiveGenerator hi hσ, ← (hv _).eq_primitiveGenerator hi hσ]

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

namespace IsRegularCone

/-- The dual semigroup of a regular cone with `k` rays in a lattice of rank `n` is isomorphic to
`ℕ ^ k × ℤ ^ (n - k)`, the ray coordinates being indexed by the rays themselves. -/
theorem nonempty_dualSemigroup_addEquiv (hi : IsIntegralLattice i) (hσ : IsRegularCone i σ) :
    Nonempty (dualSemigroup hi σ ≃+
      (ToricRay σ →₀ ℕ) × (Fin (Module.finrank ℤ N - Nat.card (ToricRay σ)) →₀ ℤ)) := by
  classical
  obtain ⟨b, r, hb⟩ := hσ.exists_basis_finrank
  have _ : Fintype (ToricRay σ) := Fintype.ofInjective r r.injective
  -- Split the basis indices into the rays and their complement.
  let C := {j : Fin (Module.finrank ℤ N) // j ∉ Set.range r}
  have hC : Fintype.card C = Module.finrank ℤ N - Nat.card (ToricRay σ) := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Set.card_range_of_injective r.injective,
      Nat.card_eq_fintype_card]
  let e : ToricRay σ ⊕ Fin (Module.finrank ℤ N - Nat.card (ToricRay σ)) ≃
      Fin (Module.finrank ℤ N) :=
    (Equiv.sumCongr (Equiv.ofInjective r r.injective) (Fintype.equivFinOfCardEq hC).symm).trans
      (Equiv.sumCompl fun j ↦ j ∈ Set.range r)
  -- By construction the splitting sends each ray to its own basis index.
  have he : ∀ ρ, e (Sum.inl ρ) = r ρ := fun ρ ↦ rfl
  exact ⟨regularDualSemigroupEquiv hi hσ.toIsToricCone (b := b.reindex e.symm)
    fun ρ ↦ by simpa [he] using hb.isPrimitiveGenerator_apply ρ⟩

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
