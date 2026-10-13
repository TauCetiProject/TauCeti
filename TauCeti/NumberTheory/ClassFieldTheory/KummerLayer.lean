/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Kummer.Degree
public import TauCeti.NumberTheory.ClassFieldTheory.ClassField

/-!
# The Kummer layer of a subgroup of `Kˣ`

Let `K` be a field containing the `n`-th roots of unity and `Δ` a subgroup of `Kˣ` with finite
image in `Kˣ ⧸ (Kˣ)ⁿ`. The Kummer field `K(Δ^{1/n})` inside the separable closure `Kˢ` is a finite
abelian Galois extension of `K` (`TauCeti.isAbelianGalois_kummerField`), so it is the class field
of an open normal subgroup of the absolute Galois group `G_K`. This file names that subgroup, the
**Kummer layer** `kummerLayer n Δ`, and records its characteristic properties: it cuts out
`K(Δ^{1/n})`, it is an abelian layer, its degree is the index `[Δ : Δ ∩ (Kˣ)ⁿ]`, and the quotient
`G_K ⧸ kummerLayer n Δ` has exponent dividing `n`.

Kummer layers are the layers on which the Kummer-theoretic steps of class field theory take
place: over a number field containing the `p`-th roots of unity, the layer of the `S`-units cutting
out `K(U_S^{1/p})` is the abelian extension realizing the norm subgroup of the Kummer idele group in
the proof of global existence, and the extension whose Frobenius elements are counted in the
Kummer case of the second fundamental inequality.

## Main definitions

* `TauCeti.ClassFieldTheory.kummerLayer n Δ`: the open normal subgroup of `G_K` fixing
  `K(Δ^{1/n})`.

## Main results

* `TauCeti.ClassFieldTheory.classField_kummerLayer`: the class field of `kummerLayer n Δ` is
  `K(Δ^{1/n})`.
* `TauCeti.ClassFieldTheory.mem_kummerLayer_iff`: an element of `G_K` lies in the Kummer layer
  exactly when it fixes every `n`-th root of every element of `Δ`.
* `TauCeti.ClassFieldTheory.kummerLayer_antitone`: enlarging `Δ` shrinks the layer.
* `TauCeti.ClassFieldTheory.pow_mem_kummerLayer`: `σ ^ n` lies in the Kummer layer for every
  `σ ∈ G_K`.
* `TauCeti.ClassFieldTheory.isAbelianClassFieldLayer_kummerLayer`: the Kummer layer is abelian.
* `TauCeti.ClassFieldTheory.degree_kummerLayer`: its degree is `[Δ : Δ ∩ (Kˣ)ⁿ]`.

## References

* S. Lang, *Algebra*, Graduate Texts in Mathematics 211, Springer (2002), Chapter VI, §8.
* J. S. Milne, *Class Field Theory*, Chapter VII, §§5 and 9.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open IntermediateField

section Basic

variable {K : Type*} [Field K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n] (Δ : Subgroup Kˣ)
  [(powMonoidHom n : Kˣ →* Kˣ).range.IsFiniteRelIndex Δ]

/-- **The Kummer layer** of a subgroup `Δ` of `Kˣ`, for `K` containing the `n`-th roots of unity
and `Δ` of finite image in `Kˣ ⧸ (Kˣ)ⁿ`: the open normal subgroup of the absolute Galois group
`G_K` fixing the Kummer field `K(Δ^{1/n})` in the separable closure. -/
def kummerLayer : OpenNormalSubgroup (AbsoluteGaloisGroup K) where
  toSubgroup := (kummerField (SeparableClosure K) n Δ).fixingSubgroup
  isOpen' := (InfiniteGalois.isOpen_iff_finite _).2 inferInstance
  isNormal' := (InfiniteGalois.normal_iff_isGalois _).2 inferInstance

/-- The subgroup underlying the Kummer layer is the fixing subgroup of `K(Δ^{1/n})`. -/
theorem kummerLayer_toSubgroup :
    (kummerLayer n Δ).toSubgroup = (kummerField (SeparableClosure K) n Δ).fixingSubgroup :=
  (rfl)

/-- **The Kummer layer cuts out the Kummer field**: the class field of `kummerLayer n Δ` is
`K(Δ^{1/n})`. -/
@[simp]
theorem classField_kummerLayer :
    classField K (kummerLayer n Δ) = kummerField (SeparableClosure K) n Δ := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup (classField K _), fixingSubgroup_classField,
    kummerLayer_toSubgroup, InfiniteGalois.fixedField_fixingSubgroup]

variable {n Δ} in
/-- An element of `G_K` lies in the Kummer layer of `Δ` exactly when it fixes every `n`-th root
in `Kˢ` of every element of `Δ`. -/
theorem mem_kummerLayer_iff {σ : AbsoluteGaloisGroup K} :
    σ ∈ kummerLayer n Δ ↔
      ∀ a ∈ Δ, ∀ x : SeparableClosure K, x ^ n = algebraMap K _ a → σ x = x := by
  -- Membership in the open normal subgroup is membership in its underlying fixing subgroup.
  have hmem : σ ∈ kummerLayer n Δ ↔ σ ∈ (kummerField (SeparableClosure K) n Δ).fixingSubgroup :=
    Iff.rfl
  rw [hmem, ← Subgroup.zpowers_le, ← le_iff_le, kummerField_le_iff]
  simp only [mem_fixedField_iff, Subgroup.forall_mem_zpowers]
  refine forall₄_congr fun _ _ x _ ↦ ⟨fun h ↦ by simpa using h 1, fun h k ↦ ?_⟩
  -- The powers of `σ` fix `x` because they lie in the stabilizer of `x`, which contains `σ`.
  exact Subgroup.zpow_mem (MulAction.stabilizer (AbsoluteGaloisGroup K) x) h k

variable {Δ} in
/-- **Enlarging `Δ` shrinks the Kummer layer**: a larger group of radicands cuts out a larger
Kummer field. -/
theorem kummerLayer_antitone {Δ' : Subgroup Kˣ}
    [(powMonoidHom n : Kˣ →* Kˣ).range.IsFiniteRelIndex Δ'] (h : Δ ≤ Δ') :
    kummerLayer n Δ' ≤ kummerLayer n Δ := by
  rw [← classField_le_classField_iff, classField_kummerLayer, classField_kummerLayer]
  exact kummerField_mono h

/-- **The quotient `G_K ⧸ kummerLayer n Δ` has exponent dividing `n`**: for every `σ ∈ G_K`, the
power `σ ^ n` lies in the Kummer layer, since `σ` multiplies each `n`-th root of an element of `Δ`
by an `n`-th root of unity. -/
theorem pow_mem_kummerLayer (σ : AbsoluteGaloisGroup K) : σ ^ n ∈ kummerLayer n Δ := by
  refine mem_kummerLayer_iff.2 fun a _ x hx ↦ ?_
  have hx0 : x ≠ 0 := ne_zero_of_pow_eq_algebraMap hx
  -- The Kummer pairing `τ x / x` is multiplicative in `τ`, and `(σ x / x) ^ n = 1`.
  have hpow (k : ℕ) : (σ ^ k) x / x = (σ x / x) ^ k := by
    induction k with
    | zero => simp [hx0]
    | succ k ih => rw [pow_succ, AlgEquiv.mul_apply_div_self_of_pow_eq _ _ hx, ih, pow_succ]
  have hone : (σ x / x) ^ n = 1 := by
    rw [div_pow, ← map_pow, hx, AlgEquiv.commutes, div_self (by simp)]
  rw [← div_eq_one_iff_eq hx0, hpow, hone]

end Basic

section Layer

variable {K : Type} [Field K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n] (Δ : Subgroup Kˣ)
  [(powMonoidHom n : Kˣ →* Kˣ).range.IsFiniteRelIndex Δ]

/-- **The Kummer layer is abelian**: `K(Δ^{1/n})/K` is an abelian extension. -/
theorem isAbelianClassFieldLayer_kummerLayer : (kummerLayer n Δ).IsAbelianClassFieldLayer := by
  rw [← isAbelianGalois_classField_iff, classField_kummerLayer]
  infer_instance

/-- **The degree of the Kummer layer** is `[Δ : Δ ∩ (Kˣ)ⁿ]`, the order of the image of `Δ` in
`Kˣ ⧸ (Kˣ)ⁿ`. -/
theorem degree_kummerLayer :
    (NormalLayer.ofOpenNormal (kummerLayer n Δ)).degree =
      (powMonoidHom n : Kˣ →* Kˣ).range.relIndex Δ := by
  have : NeZero (n : K) := (HasEnoughRootsOfUnity.exists_primitiveRoot K n).choose_spec.neZero'
  have : NeZero (n : SeparableClosure K) := .nat_of_injective (algebraMap K _).injective
  rw [NormalLayer.degree_eq_natCard_gal,
    Nat.card_congr (NormalLayer.galOfOpenNormalEquiv (kummerLayer n Δ)).toEquiv,
    ← Subgroup.index_eq_card, ← finrank_classField, classField_kummerLayer]
  exact finrank_kummerField fun a _ ↦ IsSepClosed.exists_pow_nat_eq _ n

end Layer

end TauCeti.ClassFieldTheory
