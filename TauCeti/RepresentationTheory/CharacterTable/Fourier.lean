/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Table

/-!
# The Fourier transform of a finite group algebra

A family of representations `ρᵢ : G → End(Vᵢ)` of a monoid `G` gives the **Fourier transform**
`TauCeti.fourierAlgHom ρ : k[G] →ₐ[k] Π i, End(Vᵢ)`, which sends `f = ∑_g f(g) e_g` to the family
of operators `(∑_g f(g) ρᵢ(g))ᵢ`. Since the product of `k[G]` is the convolution
`(f * f')(x) = ∑_{y z = x} f(y) f'(z)` of coefficient functions, the Fourier transform turns
convolution into the product of operators, factor by factor. It is equivariant for the two-sided
actions of `G`: on `k[G]` the pair `(a, b)` multiplies by `e_a` on the left and by `e_b` on the
right, and on each `End(Vᵢ)` it multiplies by `ρᵢ(a)` and `ρᵢ(b)`. Changing a model `Vᵢ` by an
equivalence of representations conjugates its block.

Now let `G` be a finite group, `k` an algebraically closed field in which `|G|` is invertible, and
let the `ρᵢ` be a **complete family of irreducibles**: pairwise inequivalent irreducible
representations, as many as `G` has conjugacy classes, so that every irreducible representation of
`G` is equivalent to exactly one of them (`TauCeti.ClassFunction.exists_nonempty_equiv`). The
explicit **Fourier inversion formula**
`f(g) = |G|⁻¹ ∑ᵢ dim(Vᵢ) trace(ρᵢ(g⁻¹) Tᵢ)` for `T = (Tᵢ)ᵢ` the transform of `f` recovers `f`,
because `∑ᵢ dim(Vᵢ) χᵢ` is the character of the regular representation, `|G|` at the identity
and `0` elsewhere. With the dimension count `∑ᵢ dim(Vᵢ)² = |G|`, the Fourier transform is an
isomorphism of algebras `k[G] ≃ₐ[k] Π i, End(Vᵢ)`, a Wedderburn decomposition of the group
algebra whose blocks are the endomorphism algebras of the given irreducibles, with the inversion
formula as its inverse.

## Main definitions

* `TauCeti.fourierAlgHom`: the Fourier transform along an arbitrary family of representations.
* `TauCeti.fourierInv`: the inversion formula, as a linear map `(Π i, End(Vᵢ)) →ₗ[k] k[G]`.
* `TauCeti.fourierAlgEquiv`: the Fourier transform of a complete family of irreducibles, as an
  isomorphism of algebras.

## Main results

* `TauCeti.fourierAlgHom_single_mul_mul_single`: the two-sided equivariance.
* `TauCeti.fourierAlgHom_apply_eq_conjAlgEquiv`: changing the models conjugates the blocks.
* `TauCeti.exists_bijective_nonempty_equiv_irreducibleRepresentation`: a complete family of
  irreducibles is a relabelling of the rows of the character table.
* `TauCeti.sum_finrank_sq_eq_card`: the squares of the dimensions of a complete family of
  irreducibles add up to `|G|`.
* `TauCeti.sum_finrank_mul_character`: `∑ᵢ dim(Vᵢ) χᵢ(g)` is `|G|` at `g = 1` and `0` elsewhere.
* `TauCeti.fourierInv_fourierAlgHom` and `TauCeti.fourierAlgHom_fourierInv`: **Fourier inversion**,
  in both directions.
* `TauCeti.fourierAlgHom_bijective`: the Fourier transform of a complete family of irreducibles is
  bijective.

## References

See W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §3.4 and
Exercises 3.31–3.32, or J.-P. Serre, *Linear Representations of Finite Groups* (1977),
Section 6.2, Proposition 10.
-/

public section

open Module
open scoped MonoidAlgebra

namespace TauCeti

universe u v w w'

section FourierAlgHom

variable {k : Type u} {G : Type v} [CommSemiring k] [Monoid G] {ι : Type*} {V : ι → Type w}
  [∀ i, AddCommMonoid (V i)] [∀ i, Module k (V i)] (ρ : ∀ i, Representation k G (V i))

/-- **The Fourier transform** of the monoid algebra `k[G]` along a family of representations
`ρᵢ` of `G`: it sends `f = ∑_g f(g) e_g` to the family of operators `(∑_g f(g) ρᵢ(g))ᵢ`, the
action of `f` in each representation. -/
noncomputable def fourierAlgHom : k[G] →ₐ[k] Π i, Module.End k (V i) :=
  AlgHom.pi fun i => (ρ i).asAlgebraHom

@[simp]
theorem fourierAlgHom_apply (f : k[G]) (i : ι) :
    fourierAlgHom ρ f i = (ρ i).asAlgebraHom f :=
  (rfl)

/-- **The Fourier transform is equivariant for the two-sided actions of `G`**: multiplying by
`e_a` on the left and by `e_b` on the right multiplies each block by `ρᵢ(a)` on the left and by
`ρᵢ(b)` on the right. -/
theorem fourierAlgHom_single_mul_mul_single (a b : G) (f : k[G]) (i : ι) :
    fourierAlgHom ρ (MonoidAlgebra.single a 1 * f * MonoidAlgebra.single b 1) i =
      ρ i a * fourierAlgHom ρ f i * ρ i b := by
  simp

variable {W : ι → Type w'} [∀ i, AddCommMonoid (W i)] [∀ i, Module k (W i)]
  {σ : ∀ i, Representation k G (W i)}

/-- **Changing a model by an equivalence of representations conjugates its block of the Fourier
transform**: if `e : Vᵢ ≃ Wᵢ` is equivariant, the `i`-th block along `σ` is `e ∘ Tᵢ ∘ e⁻¹` for the
`i`-th block `Tᵢ` along `ρ`. -/
theorem fourierAlgHom_apply_eq_conjAlgEquiv (i : ι) (e : (ρ i).Equiv (σ i)) (f : k[G]) :
    fourierAlgHom σ f i = e.toLinearEquiv.conjAlgEquiv k (fourierAlgHom ρ f i) := by
  refine LinearMap.ext fun w => ?_
  obtain ⟨v, rfl⟩ := e.toLinearEquiv.surjective w
  simp only [fourierAlgHom_apply, LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [Representation.Equiv.toLinearEquiv_apply]
  exact (e.toIntertwiningMap.apply_asAlgebraHom f v).symm

end FourierAlgHom

section FourierInv

variable {k : Type u} {G : Type v} [Field k] [Group G] [Finite G] {ι : Type*} [Fintype ι]
  {V : ι → Type w} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
  (ρ : ∀ i, Representation k G (V i))

/-- **The Fourier inversion formula** along a family of representations `ρᵢ` of a finite group,
as a linear map: it sends a family `T = (Tᵢ)ᵢ` of operators to the element of `k[G]` whose
coefficient at `g` is `|G|⁻¹ ∑ᵢ dim(Vᵢ) trace(ρᵢ(g⁻¹) Tᵢ)`.

For a complete family of irreducibles this is the inverse of `TauCeti.fourierAlgHom`
(`TauCeti.fourierInv_fourierAlgHom`, `TauCeti.fourierAlgHom_fourierInv`). -/
noncomputable def fourierInv : (Π i, Module.End k (V i)) →ₗ[k] k[G] :=
  (MonoidAlgebra.coeffLinearEquiv k).symm.toLinearMap ∘ₗ
    (Finsupp.linearEquivFunOnFinite k k G).symm.toLinearMap ∘ₗ
      LinearMap.pi fun g => (Nat.card G : k)⁻¹ • ∑ i, (finrank k (V i) : k) •
        (LinearMap.trace k (V i) ∘ₗ LinearMap.mulLeft k (ρ i g⁻¹) ∘ₗ LinearMap.proj i)

@[simp]
theorem coeff_fourierInv (T : Π i, Module.End k (V i)) (g : G) :
    (fourierInv ρ T).coeff g =
      (Nat.card G : k)⁻¹ *
        ∑ i, (finrank k (V i) : k) * LinearMap.trace k (V i) (ρ i g⁻¹ * T i) := by
  simp [fourierInv]

end FourierInv

section Complete

variable {k : Type u} {G : Type v} [Field k] [Group G] [Finite G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)] {ι : Type*} {V : ι → Type w}
  [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
  (ρ : ∀ i, Representation k G (V i)) [∀ i, (ρ i).IsIrreducible]
  (hind : Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j)))
  (hcard : Nat.card ι = Nat.card (ConjClasses G))

include hind hcard

/-- **A complete family of irreducibles is a relabelling of the rows of the character table**: there
is a bijection from its index to the rows matching each member with an equivalent row
representation. -/
theorem exists_bijective_nonempty_equiv_irreducibleRepresentation :
    ∃ C : ι → Fin (Nat.card (ConjClasses G)), Function.Bijective C ∧
      ∀ i, Nonempty ((ρ i).Equiv (irreducibleRepresentation k (C i))) := by
  have : Finite ι := Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_pos.ne')
  let _ := Fintype.ofFinite ι
  choose C hC using fun i => ClassFunction.exists_nonempty_equiv
    (fun j : Fin (Nat.card (ConjClasses G)) => irreducibleRepresentation k j)
    (pairwise_isEmpty_equiv_irreducibleRepresentation k) (by simp) (ρ i)
  have hinj : Function.Injective C := by
    intro i j hij
    by_contra hne
    exact (hind hne).elim ((hC i).some.trans ((hij ▸ (hC j).some).symm))
  refine ⟨C, (Fintype.bijective_iff_injective_and_card C).2 ⟨hinj, ?_⟩, hC⟩
  rw [Fintype.card_fin, Fintype.card_eq_nat_card, hcard]

/-- **The squares of the dimensions of a complete family of irreducibles add up to `|G|`.** -/
theorem sum_finrank_sq_eq_card [Fintype ι] : ∑ i, finrank k (V i) ^ 2 = Nat.card G := by
  obtain ⟨C, hC, he⟩ := exists_bijective_nonempty_equiv_irreducibleRepresentation ρ hind hcard
  rw [← sum_characterDegree_sq_eq_card (k := k) (G := G)]
  refine Fintype.sum_bijective C hC _ _ fun i => ?_
  rw [(he i).some.toLinearEquiv.finrank_eq, Module.finrank_fin_fun]

/-- Each member of a complete family of irreducibles is finite-dimensional. -/
private theorem finite_of_complete : ∀ i, Module.Finite k (V i) := by
  obtain ⟨C, -, he⟩ := exists_bijective_nonempty_equiv_irreducibleRepresentation ρ hind hcard
  exact fun i => Module.Finite.equiv (he i).some.toLinearEquiv.symm

open scoped Classical in
/-- **The character of the regular representation**, expanded along a complete family of
irreducibles: `∑ᵢ dim(Vᵢ) χᵢ(g)` is `|G|` at the identity and `0` elsewhere. -/
theorem sum_finrank_mul_character [Fintype ι] (g : G) :
    ∑ i, (finrank k (V i) : k) * (ρ i).character g = if g = 1 then (Nat.card G : k) else 0 := by
  have := finite_of_complete ρ hind hcard
  split_ifs with hg
  · subst hg
    simp_rw [Representation.char_one, ← sq]
    have h := congrArg (Nat.cast : ℕ → k) (sum_finrank_sq_eq_card ρ hind hcard)
    push_cast at h
    exact h
  · have h := ClassFunction.sum_char_mul_char_inv ρ hind hcard g 1
    simp only [isConj_one_left, hg, ite_false, inv_one, Representation.char_one] at h
    simpa [mul_comm] using h

/-- **Fourier inversion**: the inversion formula recovers an element of `k[G]` from its Fourier
transform along a complete family of irreducibles. -/
theorem fourierInv_fourierAlgHom [Fintype ι] (f : k[G]) : fourierInv ρ (fourierAlgHom ρ f) = f := by
  classical
  induction f using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  | single h c =>
    ext g
    have key := sum_finrank_mul_character ρ hind hcard (g⁻¹ * h)
    simp only [Representation.character, map_mul] at key
    simp only [coeff_fourierInv, fourierAlgHom_apply, Representation.asAlgebraHom_single,
      mul_smul_comm, map_smul, smul_eq_mul, MonoidAlgebra.coeff_single, Finsupp.single_apply]
    simp_rw [mul_left_comm _ c, ← Finset.mul_sum, key, inv_mul_eq_one, eq_comm (a := h)]
    split_ifs
    · rw [mul_left_comm, inv_mul_cancel₀ (Invertible.ne_zero _), mul_one]
    · simp

/-- **The Fourier transform of a complete family of irreducibles is bijective.** -/
theorem fourierAlgHom_bijective : Function.Bijective (fourierAlgHom ρ) := by
  have : Finite ι := Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_pos.ne')
  let _ := Fintype.ofFinite ι
  have := finite_of_complete ρ hind hcard
  have hinj : Function.Injective (fourierAlgHom ρ) :=
    Function.LeftInverse.injective (fourierInv_fourierAlgHom ρ hind hcard)
  refine ⟨hinj, ?_⟩
  have hrank : finrank k k[G] = finrank k (Π i, Module.End k (V i)) := by
    rw [Module.finrank_pi_fintype, Module.finrank_eq_nat_card_basis (MonoidAlgebra.basis G k),
      ← sum_finrank_sq_eq_card ρ hind hcard]
    simp [Module.finrank_linearMap, sq]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank
    (f := (fourierAlgHom ρ).toLinearMap)).1 hinj

/-- **The Fourier transform of a complete family of irreducibles**, as an isomorphism of algebras
`k[G] ≃ₐ[k] Π i, End(Vᵢ)`: a Wedderburn decomposition of the group algebra, its blocks being the
endomorphism algebras of the given irreducible representations. Its inverse is the inversion formula
`TauCeti.fourierInv` (`TauCeti.fourierAlgEquiv_symm_apply`). -/
noncomputable def fourierAlgEquiv : k[G] ≃ₐ[k] Π i, Module.End k (V i) :=
  AlgEquiv.ofBijective (fourierAlgHom ρ) (fourierAlgHom_bijective ρ hind hcard)

@[simp]
theorem fourierAlgEquiv_apply (f : k[G]) :
    fourierAlgEquiv ρ hind hcard f = fourierAlgHom ρ f :=
  (rfl)

/-- **Fourier inversion**, in the other direction: every family of operators is the Fourier
transform of the element of `k[G]` given by the inversion formula. -/
theorem fourierAlgHom_fourierInv [Fintype ι] (T : Π i, Module.End k (V i)) :
    fourierAlgHom ρ (fourierInv ρ T) = T := by
  obtain ⟨f, rfl⟩ := (fourierAlgHom_bijective ρ hind hcard).2 T
  rw [fourierInv_fourierAlgHom ρ hind hcard]

@[simp]
theorem fourierAlgEquiv_symm_apply [Fintype ι] (T : Π i, Module.End k (V i)) :
    (fourierAlgEquiv ρ hind hcard).symm T = fourierInv ρ T :=
  (fourierAlgEquiv ρ hind hcard).symm_apply_eq.2 (fourierAlgHom_fourierInv ρ hind hcard T).symm

end Complete

end TauCeti
