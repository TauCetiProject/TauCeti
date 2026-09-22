/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Ideal
public import Mathlib.Algebra.Lie.SemiDirect

/-!
# Recognising a semidirect sum from an ideal and a complementary subalgebra

Mathlib's `LieAlgebra.SemiDirectSum K L ψ`, written `K ⋊⁅ψ⁆ L`, is the *external* semidirect sum
of two Lie algebras twisted by a Lie homomorphism `ψ : L →ₗ⁅R⁆ LieDerivation R K K`.  A Lie
algebra `L` is presented *internally* as a semidirect sum by an ideal `S`, a Lie subalgebra `H`,
and the requirement that the two underlying submodules be complementary.  This file connects the
two descriptions.

The twisting homomorphism is the adjoint action.  An ideal `S` of `L` is stable under `⁅x, -⁆` for
every `x : L`, and the Jacobi identity says exactly that the resulting endomorphism of `S` is a Lie
derivation; the assignment is itself a homomorphism of Lie algebras, so it gives
`LieIdeal.adDerivation S : L →ₗ⁅R⁆ LieDerivation R S S`.  Restricting it along the inclusion of a
Lie subalgebra `H` produces the `ψ` that a semidirect sum needs, and when `S` and `H` are
complementary as submodules, `(s, h) ↦ s + h` is an isomorphism `↥S ⋊⁅ψ⁆ ↥H ≃ₗ⁅R⁆ L`.

In the converse direction, an external semidirect sum `K ⋊⁅ψ⁆ L` carries such internal data
tautologically: the kernel of the projection to `L` is an ideal, the range of the inclusion of `L`
is a Lie subalgebra, and the two are complementary.  So neither presentation is more general than
the other, and a theorem may be stated against the external form without loss.

## Main definitions

* `LieIdeal.adDerivation`: the adjoint action of `L` on an ideal `S`, as a Lie homomorphism
  `L →ₗ⁅R⁆ LieDerivation R S S`.  The `ψ` attached to a Lie subalgebra `H` is the composite
  `(LieIdeal.adDerivation S).comp H.incl`.
* `LieIdeal.semiDirectSumHom`: the Lie homomorphism `↥S ⋊⁅ψ⁆ ↥H →ₗ⁅R⁆ L` given by `(s, h) ↦ s + h`.
* `LieIdeal.semiDirectSumEquiv`: that homomorphism as an isomorphism, when the underlying
  submodules of `S` and `H` are complementary.

## Main statements

* `LieIdeal.nonempty_lieEquiv_semiDirectSum` and `LieIdeal.exists_lieEquiv_semiDirectSum`:
  **the recognition theorem**, in the `Nonempty (L ≃ₗ⁅R⁆ ↥S ⋊⁅ψ⁆ ↥H)` form that consumers of a
  splitting hypothesis take as input.
* `LieIdeal.right_semiDirectSumEquiv_symm_eq_zero_iff` and
  `LieIdeal.left_semiDirectSumEquiv_symm_eq_zero_iff`: the recognition isomorphism carries `S` and
  `H` onto the two factors, which is what lets a statement about the left factor be read back as a
  statement about the ideal.
* `LieAlgebra.SemiDirectSum.isCompl_ker_projr_range_inr`: the converse, that an external semidirect
  sum is internally presented by the kernel of `projr` and the range of `inr`, with
  `LieAlgebra.SemiDirectSum.exists_lieEquiv_semiDirectSum_ker_projr` the resulting
  reconstruction.

## References

* [W. Fulton and J. Harris, *Representation Theory: A First Course*][fulton-harris1991],
  Appendix E, §E.2, where Ado's theorem extends a representation of a solvable ideal across a
  complementary subalgebra.
-/

public section

namespace LieIdeal

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

section AdDerivation

variable (S : LieIdeal R L)

/-- The adjoint action of a Lie algebra on one of its ideals, as a homomorphism into the Lie
algebra of Lie derivations of that ideal.  The ideal is stable under `⁅x, -⁆`, and the Jacobi
identity is both the Leibniz rule for each `⁅x, -⁆` and the statement that `x ↦ ⁅x, -⁆` preserves
brackets. -/
def adDerivation : L →ₗ⁅R⁆ LieDerivation R S S where
  toFun x :=
    { toLinearMap := LieModule.toEnd R L S x
      leibniz' := fun a b => by
        simp only [LieModule.toEnd_apply_apply]
        rw [leibniz_lie, ← lie_skew ⁅x, a⁆ b]
        abel_nf }
  map_add' x y := by ext a; simp
  map_smul' t x := by ext a; simp
  map_lie' {x y} := by
    ext a
    rw [LieDerivation.commutator_apply]
    simp only [LieDerivation.mk_coe, LieModule.toEnd_apply_apply]
    rw [leibniz_lie]
    abel_nf

@[simp]
theorem adDerivation_apply_apply (x : L) (a : S) : adDerivation S x a = ⁅x, a⁆ := (rfl)

end AdDerivation

section Internal

variable (S : LieIdeal R L) (H : LieSubalgebra R L)

/-- The canonical map from the semidirect sum of an ideal `S` and a Lie subalgebra `H` of `L`,
twisted by the adjoint action of `H` on `S`, back to `L`: it adds the two components.  It is a
homomorphism of Lie algebras because the twist is the adjoint action. -/
def semiDirectSumHom : (↥S ⋊⁅(adDerivation S).comp H.incl⁆ ↥H) →ₗ⁅R⁆ L where
  toFun z := (z.left : L) + (z.right : L)
  map_add' z w := by
    simp only [LieAlgebra.SemiDirectSum.add_eq_mk]
    push_cast
    abel
  map_smul' t z := by
    simp only [LieAlgebra.SemiDirectSum.smul_eq_mk, RingHom.id_apply, smul_add]
    push_cast
    rfl
  map_lie' {z w} := by
    simp only [LieAlgebra.SemiDirectSum.lie_eq_mk, LieHom.comp_apply, LieSubalgebra.coe_incl,
      adDerivation_apply_apply, LieIdeal.coe_bracket_of_module, LieSubmodule.coe_add,
      LieSubmodule.coe_sub, LieSubmodule.coe_bracket, LieSubalgebra.coe_bracket]
    rw [add_lie, lie_add, lie_add, ← lie_skew (z.left : L) (w.right : L)]
    abel_nf

@[simp]
theorem semiDirectSumHom_apply (z : ↥S ⋊⁅(adDerivation S).comp H.incl⁆ ↥H) :
    semiDirectSumHom S H z = (z.left : L) + (z.right : L) := (rfl)

variable {S H}

theorem semiDirectSumHom_injective (h : Disjoint S.toSubmodule H.toSubmodule) :
    Function.Injective (semiDirectSumHom S H) := by
  intro z w hzw
  simp only [semiDirectSumHom_apply] at hzw
  -- the difference of the two `S`-components equals the difference of the two `H`-components,
  -- so both lie in `S ⊓ H` and hence vanish
  have hswap : (z.left : L) - (w.left : L) = (w.right : L) - (z.right : L) := by
    rw [sub_eq_sub_iff_add_eq_add, hzw]
    abel
  have hleft : (z.left : L) = (w.left : L) := by
    rw [← sub_eq_zero]
    refine Submodule.disjoint_def.mp h _ (Submodule.sub_mem _ z.left.2 w.left.2) ?_
    rw [hswap]
    exact Submodule.sub_mem _ w.right.2 z.right.2
  refine LieAlgebra.SemiDirectSum.ext (Subtype.ext hleft) (Subtype.ext ?_)
  rwa [hleft, add_right_inj] at hzw

theorem semiDirectSumHom_surjective (h : Codisjoint S.toSubmodule H.toSubmodule) :
    Function.Surjective (semiDirectSumHom S H) := by
  intro x
  obtain ⟨s, hs, t, ht, hst⟩ :=
    Submodule.mem_sup.mp (by rw [h.eq_top]; trivial : x ∈ S.toSubmodule ⊔ H.toSubmodule)
  exact ⟨⟨⟨s, hs⟩, ⟨t, ht⟩⟩, hst⟩

theorem semiDirectSumHom_bijective (h : IsCompl S.toSubmodule H.toSubmodule) :
    Function.Bijective (semiDirectSumHom S H) :=
  ⟨semiDirectSumHom_injective h.disjoint, semiDirectSumHom_surjective h.codisjoint⟩

variable (S H)

/-- **Internal recognition of a semidirect sum.**  An ideal `S` and a Lie subalgebra `H` of `L`
whose underlying submodules are complementary exhibit `L` as the semidirect sum of `S` and `H`,
twisted by the adjoint action of `H` on `S`. -/
noncomputable def semiDirectSumEquiv (h : IsCompl S.toSubmodule H.toSubmodule) :
    (↥S ⋊⁅(adDerivation S).comp H.incl⁆ ↥H) ≃ₗ⁅R⁆ L :=
  LieEquiv.ofBijective _ (semiDirectSumHom_bijective h)

@[simp]
theorem semiDirectSumEquiv_apply (h : IsCompl S.toSubmodule H.toSubmodule)
    (z : ↥S ⋊⁅(adDerivation S).comp H.incl⁆ ↥H) :
    semiDirectSumEquiv S H h z = (z.left : L) + (z.right : L) := (rfl)

theorem semiDirectSumEquiv_inl (h : IsCompl S.toSubmodule H.toSubmodule) (s : S) :
    semiDirectSumEquiv S H h (LieAlgebra.SemiDirectSum.inl _ s) = (s : L) := by
  simp

theorem semiDirectSumEquiv_inr (h : IsCompl S.toSubmodule H.toSubmodule) (t : H) :
    semiDirectSumEquiv S H h (LieAlgebra.SemiDirectSum.inr _ t) = (t : L) := by
  simp

@[simp]
theorem semiDirectSumEquiv_symm_coe_left (h : IsCompl S.toSubmodule H.toSubmodule) (s : S) :
    (semiDirectSumEquiv S H h).symm (s : L) = LieAlgebra.SemiDirectSum.inl _ s := by
  rw [LieEquiv.symm_apply_eq, semiDirectSumEquiv_inl]

@[simp]
theorem semiDirectSumEquiv_symm_coe_right (h : IsCompl S.toSubmodule H.toSubmodule) (t : H) :
    (semiDirectSumEquiv S H h).symm (t : L) = LieAlgebra.SemiDirectSum.inr _ t := by
  rw [LieEquiv.symm_apply_eq, semiDirectSumEquiv_inr]

theorem semiDirectSumEquiv_symm_of_mem_left (h : IsCompl S.toSubmodule H.toSubmodule) {x : L}
    (hx : x ∈ S) :
    (semiDirectSumEquiv S H h).symm x = LieAlgebra.SemiDirectSum.inl _ ⟨x, hx⟩ :=
  semiDirectSumEquiv_symm_coe_left S H h ⟨x, hx⟩

theorem semiDirectSumEquiv_symm_of_mem_right (h : IsCompl S.toSubmodule H.toSubmodule) {x : L}
    (hx : x ∈ H) :
    (semiDirectSumEquiv S H h).symm x = LieAlgebra.SemiDirectSum.inr _ ⟨x, hx⟩ :=
  semiDirectSumEquiv_symm_coe_right S H h ⟨x, hx⟩

/-- The recognition isomorphism identifies the ideal `S` with the left factor: an element of `L`
lies in `S` exactly when its preimage has vanishing right component. -/
theorem right_semiDirectSumEquiv_symm_eq_zero_iff (h : IsCompl S.toSubmodule H.toSubmodule)
    {x : L} : ((semiDirectSumEquiv S H h).symm x).right = 0 ↔ x ∈ S := by
  refine ⟨fun hx => ?_, fun hx => by rw [semiDirectSumEquiv_symm_of_mem_left S H h hx]; rfl⟩
  have hxx := (semiDirectSumEquiv S H h).apply_symm_apply x
  rw [semiDirectSumEquiv_apply, hx, ZeroMemClass.coe_zero, add_zero] at hxx
  exact hxx ▸ ((semiDirectSumEquiv S H h).symm x).left.2

/-- The recognition isomorphism identifies the Lie subalgebra `H` with the right factor: an element
of `L` lies in `H` exactly when its preimage has vanishing left component. -/
theorem left_semiDirectSumEquiv_symm_eq_zero_iff (h : IsCompl S.toSubmodule H.toSubmodule)
    {x : L} : ((semiDirectSumEquiv S H h).symm x).left = 0 ↔ x ∈ H := by
  refine ⟨fun hx => ?_, fun hx => by rw [semiDirectSumEquiv_symm_of_mem_right S H h hx]; rfl⟩
  have hxx := (semiDirectSumEquiv S H h).apply_symm_apply x
  rw [semiDirectSumEquiv_apply, hx, ZeroMemClass.coe_zero, zero_add] at hxx
  exact hxx ▸ ((semiDirectSumEquiv S H h).symm x).right.2

/-- The recognition theorem in the external form a splitting hypothesis is stated in: an ideal and
a complementary Lie subalgebra make `L` isomorphic to a semidirect sum. -/
theorem nonempty_lieEquiv_semiDirectSum (h : IsCompl S.toSubmodule H.toSubmodule) :
    Nonempty (L ≃ₗ⁅R⁆ (↥S ⋊⁅(adDerivation S).comp H.incl⁆ ↥H)) :=
  ⟨(semiDirectSumEquiv S H h).symm⟩

/-- The recognition theorem with the twisting homomorphism existentially quantified, the form in
which a Levi-style decomposition theorem delivers its conclusion. -/
theorem exists_lieEquiv_semiDirectSum (h : IsCompl S.toSubmodule H.toSubmodule) :
    ∃ ψ : ↥H →ₗ⁅R⁆ LieDerivation R S S, Nonempty (L ≃ₗ⁅R⁆ (↥S ⋊⁅ψ⁆ ↥H)) :=
  ⟨_, nonempty_lieEquiv_semiDirectSum S H h⟩

end Internal

end LieIdeal

namespace LieAlgebra.SemiDirectSum

variable {R K L : Type*} [CommRing R] [LieRing K] [LieAlgebra R K] [LieRing L] [LieAlgebra R L]
variable (ψ : L →ₗ⁅R⁆ LieDerivation R K K)

/-- The range of the inclusion of the right factor consists of the elements whose left component
vanishes. -/
theorem mem_range_inr {z : K ⋊⁅ψ⁆ L} : z ∈ (inr ψ).range ↔ z.left = 0 := by
  rw [LieHom.mem_range]
  exact ⟨fun ⟨y, hy⟩ => hy ▸ rfl, fun hz => ⟨z.right, by ext <;> simp [hz]⟩⟩

/-- An external semidirect sum carries the internal data that recognises it: the kernel of the
projection onto the right factor is an ideal, the range of the inclusion of the right factor is a
Lie subalgebra, and their underlying submodules are complementary. -/
theorem isCompl_ker_projr_range_inr :
    IsCompl (LieSubmodule.toSubmodule (projr ψ).ker) (inr ψ).range.toSubmodule := by
  constructor
  · refine Submodule.disjoint_def.mpr fun z hz hz' => ?_
    rw [LieSubmodule.mem_toSubmodule, LieHom.mem_ker] at hz
    rw [LieSubalgebra.mem_toSubmodule, mem_range_inr] at hz'
    exact LieAlgebra.SemiDirectSum.ext hz' hz
  · refine codisjoint_iff.mpr (eq_top_iff.mpr fun z _ => ?_)
    refine Submodule.mem_sup.mpr ⟨⟨z.left, 0⟩, ?_, ⟨0, z.right⟩, ?_, ?_⟩
    · rw [LieSubmodule.mem_toSubmodule, LieHom.mem_ker]
      rfl
    · rw [LieSubalgebra.mem_toSubmodule, mem_range_inr]
    · ext <;> simp

/-- Every external semidirect sum is reconstructed by the internal recognition theorem applied to
the kernel of `projr` and the range of `inr`.  Nothing is lost by stating a splitting hypothesis in
the external form. -/
theorem exists_lieEquiv_semiDirectSum_ker_projr :
    ∃ ψ' : ↥(inr ψ).range →ₗ⁅R⁆ LieDerivation R ↥(projr ψ).ker ↥(projr ψ).ker,
      Nonempty ((K ⋊⁅ψ⁆ L) ≃ₗ⁅R⁆ (↥(projr ψ).ker ⋊⁅ψ'⁆ ↥(inr ψ).range)) :=
  LieIdeal.exists_lieEquiv_semiDirectSum _ _ (isCompl_ker_projr_range_inr ψ)

end LieAlgebra.SemiDirectSum
