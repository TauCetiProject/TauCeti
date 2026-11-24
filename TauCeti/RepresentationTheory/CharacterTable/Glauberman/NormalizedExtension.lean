/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.RepresentationTheory.Intertwining
public import TauCeti.Algebra.MonoidAlgebra.Twisted.Finite
public import TauCeti.GroupTheory.SemidirectProduct
public import TauCeti.RepresentationTheory.Intertwining
public import TauCeti.RepresentationTheory.ProjectiveRepresentation.Basic

/-!
# Gallagher's normalized extension to a semidirect product

Let a finite group `A` act on a group `Γ` by automorphisms through `φ : A →* MulAut Γ`, and
let `ρ` be a representation of `Γ` on a finite-dimensional vector space `V` over a field `F` whose
only `Γ`-equivariant endomorphisms are the scalars. Suppose that `ρ` is isomorphic to each of its
twists `g ↦ ρ (φ a g)`, and that `|A|` is coprime to `dim V`. Then `ρ` extends to exactly one
representation `ρ*` of the semidirect product `Γ ⋊[φ] A` on the same space `V` in which every
element of `A` acts with determinant `1`.

This is the representation-theoretic input to Glauberman's canonical extension of an invariant
irreducible character of `Γ` to `Γ ⋊ A` under a coprime action. Neither finiteness of `Γ` nor
coprimality of `|A|` with `|Γ|` is needed, and the field is arbitrary. The statements read `|A|`
as `Nat.card A` and `dim V` as `Module.finrank F V`, and assume neither finiteness of `A` nor of
`dim V`: when one of them is infinite its cardinal is `0`, and coprimality then forces
`dim V = 1` or `A` trivial.

The operators implementing the twists form a projective representation of `A`. Comparing
determinants shows that the `dim V`-th power of its factor set is a coboundary, so by
`TauCeti.IsFactorSet.exists_rescale_eq_one_of_pow_eq_coboundary` the factor set itself is one, and
rescaling gives a homomorphism `A → GL(V)`. Its determinant is a linear character of `A` of order
dividing `|A|`, which a further scalar twist removes. Two extensions with determinant `1` on `A`
differ by a homomorphism from `A` to the scalars whose values have order dividing both `dim V` and
`|A|`, hence by the trivial one.

## Main results

* `Representation.exists_semidirectProduct_extension_det_eq_one`: the normalized extension exists.
* `Representation.semidirectProduct_extension_det_eq_one_unique`: it is unique, even without the
  twist hypothesis.
* `Representation.existsUnique_semidirectProduct_extension_det_eq_one`: both together.

## References

* G. Glauberman, *Correspondences of characters for relatively prime operator groups*,
  Canad. J. Math. 20 (1968), 1465–1488, Theorem 1.
-/

public section

open Module SemidirectProduct

namespace Representation

variable {F Γ A V : Type*} [Field F] [Group Γ] [Group A] {φ : A →* MulAut Γ}
  [AddCommGroup V] [Module F V] {ρ : Representation F Γ V}

/-- An extension of `ρ` to `Γ ⋊ A` intertwines `ρ` with its twist by each element of `A`. -/
private theorem extension_inr_mul
    {ρ' : Representation F (Γ ⋊[φ] A) V}
    (h : ∀ g, ρ' (inl g) = ρ g) (a : A) (g : Γ) :
    ρ' (inr a) * ρ g = ρ (φ a g) * ρ' (inr a) := by
  rw [← h, ← h, ← map_mul, ← map_mul, inr_mul_inl]

omit [Group A] in
/-- If `|A|` is coprime to a dimension `0`, then `A` is trivial. -/
private theorem subsingleton_of_coprime_finrank_eq_zero
    (hcop : (Nat.card A).Coprime (finrank F V)) (h : finrank F V = 0) : Subsingleton A := by
  rw [h, Nat.coprime_zero_right, Nat.card_eq_one_iff_unique] at hcop
  exact hcop.1

/-- **Uniqueness of the normalized extension.** If every `Γ`-equivariant endomorphism of `V` is a
scalar and `|A|` is coprime to `dim V`, then two representations of `Γ ⋊[φ] A` that both restrict to
`ρ` on `Γ` and act with determinant `1` on `A` are equal. -/
theorem semidirectProduct_extension_det_eq_one_unique
    (hscalar : ∀ f : Module.End F V, (∀ g, Commute f (ρ g)) →
      ∃ c : F, f = algebraMap F (Module.End F V) c)
    (hcop : (Nat.card A).Coprime (finrank F V))
    {ρ₁ ρ₂ : Representation F (Γ ⋊[φ] A) V}
    (h₁ : ∀ g, ρ₁ (inl g) = ρ g) (h₂ : ∀ g, ρ₂ (inl g) = ρ g)
    (hd₁ : ∀ a, (ρ₁ (inr a)).det = 1) (hd₂ : ∀ a, (ρ₂ (inr a)).det = 1) : ρ₁ = ρ₂ := by
  suffices hinr : ∀ a, ρ₁ (inr a) = ρ₂ (inr a) by
    refine MonoidHom.ext fun x ↦ ?_
    rw [← inl_left_mul_inr_right x, map_mul, map_mul, h₁, h₂, hinr]
  intro a
  rcases (finrank F V).eq_zero_or_pos with h0 | hpos
  · have := subsingleton_of_coprime_finrank_eq_zero hcop h0
    simp [Subsingleton.elim a 1]
  have : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
  -- `ρ₁ (inr a)⁻¹ ρ₂ (inr a)` commutes with `ρ`, so it is a scalar `c`.
  obtain ⟨c, hc⟩ := hscalar (ρ₁ (inr a⁻¹) * ρ₂ (inr a)) fun g ↦ by
    refine (commute_iff_eq _ _).2 ?_
    rw [mul_assoc, extension_inr_mul h₂, ← mul_assoc, extension_inr_mul h₁, map_inv,
      MulAut.inv_apply_self, mul_assoc]
  have hrel : ρ₂ (inr a) = ρ₁ (inr a) * algebraMap F (Module.End F V) c := by
    rw [← hc, ← mul_assoc, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, one_mul]
  -- The scalar `c` has order dividing both `dim V` and `|A|`.
  have hm : c ^ finrank F V = 1 := by
    simpa [hd₁, hd₂, Module.algebraMap_end_eq_smul_id, eq_comm] using
      congrArg LinearMap.det hrel
  have hn : c ^ Nat.card A = 1 := by
    have hpow (ρ' : Representation F (Γ ⋊[φ] A) V) :
        ρ' (inr a) ^ Nat.card A = 1 := by
      rw [← map_pow, ← map_pow, pow_card_eq_one', map_one, map_one]
    have := congrArg (· ^ Nat.card A) hrel
    rw [(Algebra.commute_algebraMap_right c _).mul_pow, hpow, hpow, one_mul, ← map_pow] at this
    exact (algebraMap F (Module.End F V)).injective (by rw [← this, map_one])
  have hc₁ : c = 1 := by simpa [hcop.gcd_eq_one] using pow_gcd_eq_one.2 ⟨hn, hm⟩
  rw [hrel, hc₁, map_one, mul_one]

/-- The operators implementing the twists of `ρ` can be chosen to form a homomorphism from `A` to
`GL(V)` when `|A|` is coprime to `dim V`: their factor set has a coboundary as its `dim V`-th
power, by taking determinants, and is therefore a coboundary. -/
private theorem exists_monoidHom_intertwines [Nontrivial V]
    (hscalar : ∀ f : Module.End F V, (∀ g, Commute f (ρ g)) →
      ∃ c : F, f = algebraMap F (Module.End F V) c)
    (hcop : (Nat.card A).Coprime (finrank F V))
    (htwist : ∀ a : A, Nonempty (ρ.Equiv (ρ.comp (φ a).toMonoidHom))) :
    ∃ π : A →* (V ≃ₗ[F] V), ∀ a g x, π a (ρ g x) = ρ (φ a g) (π a x) := by
  classical
  -- Operators implementing the twists, normalized at `1`.
  have hT₀ (a : A) : ∃ U : V ≃ₗ[F] V, ∀ g x, U (ρ g x) = ρ (φ a g) (U x) := by
    obtain ⟨e⟩ := htwist a
    exact ⟨e.toLinearEquiv, fun g x ↦ by
      simpa using LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) x⟩
  choose T₀ hT₀ using hT₀
  let T (a : A) : V ≃ₗ[F] V := if a = 1 then 1 else T₀ a
  have hT (a : A) (g : Γ) (x : V) : T a (ρ g x) = ρ (φ a g) (T a x) := by
    by_cases ha : a = 1 <;> simp [T, ha, hT₀]
  -- They form a projective representation of `A`, with factor set `α`.
  have hα (a b : A) : ∃ c : Fˣ, ∀ x, T a (T b x) = (c : F) • T (a * b) x :=
    exists_unit_smul_of_intertwines (σ := ρ.comp (φ (a * b)).toMonoidHom) hscalar
      ((T b).trans (T a)) (T (a * b)) (fun g x ↦ by simp [hT]) (hT (a * b))
  choose α hα using hα
  have hproj : TauCeti.IsProjectiveRep T α :=
    TauCeti.IsProjectiveRep.of_map_one_mul_apply (by simp [T]) hα
  have := hproj.isFactorSet
  -- Taking determinants, `α ^ dim V` is a coboundary, hence so is `α`.
  let d (a : A) : Fˣ := LinearEquiv.det (T a)
  have hd (a b : A) : α a b ^ finrank F V = d a * d b * (d (a * b))⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    ext
    have := congrArg LinearMap.det (hproj.toLinearMap_mul a b)
    rw [map_mul, LinearMap.det_smul] at this
    simp [d, LinearEquiv.coe_det, this]
  obtain ⟨c, hc₁, hc⟩ :=
    TauCeti.IsFactorSet.exists_rescale_eq_one_of_pow_eq_coboundary α hcop.symm d hd
  have hproj₁ : TauCeti.IsProjectiveRep
      (fun a ↦ (T a).trans (LinearEquiv.smulOfUnit (c a))) (1 : A → A → Fˣ) := by
    convert hproj.rescale c hc₁ using 1
    exact funext₂ fun a b ↦ (hc a b).symm
  exact ⟨hproj₁.toMonoidHom, fun a g x ↦ by simp [hT]⟩

/-- The action of `A` in the normalized extension: a homomorphism from `A` to `GL(V)` whose value at
`a` implements the twist of `ρ` by `a` and has determinant `1`. It is obtained from the homomorphism
of `exists_monoidHom_intertwines` by twisting with a power of its determinant, a linear character of
`A` of order dividing `|A|`. -/
private theorem exists_monoidHom_intertwines_det_eq_one
    (hscalar : ∀ f : Module.End F V, (∀ g, Commute f (ρ g)) →
      ∃ c : F, f = algebraMap F (Module.End F V) c)
    (hcop : (Nat.card A).Coprime (finrank F V))
    (htwist : ∀ a : A, Nonempty (ρ.Equiv (ρ.comp (φ a).toMonoidHom))) :
    ∃ π : A →* (V ≃ₗ[F] V),
      (∀ a g x, π a (ρ g x) = ρ (φ a g) (π a x)) ∧ ∀ a, LinearEquiv.det (π a) = 1 := by
  rcases (finrank F V).eq_zero_or_pos with h0 | hpos
  · have := subsingleton_of_coprime_finrank_eq_zero hcop h0
    exact ⟨1, fun a g x ↦ by simp [Subsingleton.elim a 1], fun a ↦ by simp⟩
  have : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨π₁, hπ₁⟩ := exists_monoidHom_intertwines hscalar hcop htwist
  let δ : A →* Fˣ := LinearEquiv.det.comp π₁
  obtain ⟨u, v, huv⟩ := TauCeti.exists_zpow_mul_zpow_eq_of_coprime (G := Fˣ) hcop.symm
  -- Since `δ ^ |A| = 1`, we have `δ = (δ ^ dim V) ^ u`, so twisting by `δ ^ (-u)` makes every
  -- determinant `δ ^ (-u * dim V) * δ = 1`.
  let e : A →* Fˣ := (zpowGroupHom (-u)).comp δ
  have hproj : TauCeti.IsProjectiveRep
      (fun a ↦ (π₁ a).trans (LinearEquiv.smulOfUnit (e a))) (1 : A → A → Fˣ) := by
    convert (TauCeti.IsProjectiveRep.of_monoidHom π₁).rescale e e.map_one using 1
    funext a b
    simp only [map_mul, mul_inv_cancel, mul_one, Pi.one_apply]
  refine ⟨hproj.toMonoidHom, fun a g x ↦ by simp [hπ₁], fun a ↦ ?_⟩
  have hcoe : ((hproj.toMonoidHom a : V ≃ₗ[F] V) : V →ₗ[F] V) =
      (e a : F) • (π₁ a : V →ₗ[F] V) :=
    LinearMap.ext fun x ↦ by simp
  have hδ : δ a ^ Nat.card A = 1 := by rw [← map_pow, pow_card_eq_one', map_one]
  have he : e a ^ finrank F V * δ a = 1 := by
    have := huv (δ a)
    rw [hδ, one_zpow, mul_one] at this
    rw [← this]
    simp only [e, MonoidHom.comp_apply, zpowGroupHom_apply]
    group
  ext
  simp only [LinearEquiv.coe_det, hcoe, LinearMap.det_smul, Units.val_one]
  simpa [δ, LinearEquiv.coe_det] using congrArg Units.val he

/-- **Gallagher's normalized extension, existence.** Let a group `A` act on `Γ` by
automorphisms through `φ`, and let `ρ` be a representation of `Γ` whose `Γ`-equivariant
endomorphisms are all scalars and which is isomorphic to its twist `g ↦ ρ (φ a g)` by every
`a ∈ A`. If `|A|` is coprime to `dim V`, then `ρ` extends to a representation of `Γ ⋊[φ] A` on `V`
in which every element of `A` acts with determinant `1`. -/
theorem exists_semidirectProduct_extension_det_eq_one
    (hscalar : ∀ f : Module.End F V, (∀ g, Commute f (ρ g)) →
      ∃ c : F, f = algebraMap F (Module.End F V) c)
    (hcop : (Nat.card A).Coprime (finrank F V))
    (htwist : ∀ a : A, Nonempty (ρ.Equiv (ρ.comp (φ a).toMonoidHom))) :
    ∃ ρ' : Representation F (Γ ⋊[φ] A) V,
      (∀ g, ρ' (inl g) = ρ g) ∧ ∀ a, (ρ' (inr a)).det = 1 := by
  obtain ⟨π, hπ, hdet⟩ := exists_monoidHom_intertwines_det_eq_one hscalar hcop htwist
  let ρΓ : Γ →* (V ≃ₗ[F] V) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F V).toMonoidHom.comp ρ.asGroupHom
  have hρΓ (g : Γ) : ((ρΓ g : V ≃ₗ[F] V) : V →ₗ[F] V) = ρ g :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap _).trans (ρ.asGroupHom_apply g)
  have hρΓx (g : Γ) (x : V) : ρΓ g x = ρ g x := LinearMap.congr_fun (hρΓ g) x
  refine ⟨LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (lift ρΓ π fun a ↦ ?_),
    fun g ↦ ?_, fun a ↦ ?_⟩
  · refine MonoidHom.ext fun g ↦ LinearEquiv.ext fun x ↦ ?_
    have := hπ a g ((π a).symm x)
    rw [LinearEquiv.apply_symm_apply] at this
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      mul_apply_eq_comp, LinearEquiv.coe_inv, hρΓx]
    exact this.symm
  · simpa using hρΓ g
  · simpa [← LinearEquiv.coe_det] using congrArg Units.val (hdet a)

/-- **Gallagher's normalized extension.** Let a group `A` act on `Γ` by automorphisms through
`φ`, and let `ρ` be a representation of `Γ` whose `Γ`-equivariant endomorphisms are all scalars and
which is isomorphic to its twist `g ↦ ρ (φ a g)` by every `a ∈ A`. If `|A|` is coprime to `dim V`,
then `ρ` has exactly one extension to a representation of `Γ ⋊[φ] A` on `V` in which every element
of `A` acts with determinant `1`. -/
theorem existsUnique_semidirectProduct_extension_det_eq_one
    (hscalar : ∀ f : Module.End F V, (∀ g, Commute f (ρ g)) →
      ∃ c : F, f = algebraMap F (Module.End F V) c)
    (hcop : (Nat.card A).Coprime (finrank F V))
    (htwist : ∀ a : A, Nonempty (ρ.Equiv (ρ.comp (φ a).toMonoidHom))) :
    ∃! ρ' : Representation F (Γ ⋊[φ] A) V,
      (∀ g, ρ' (inl g) = ρ g) ∧ ∀ a, (ρ' (inr a)).det = 1 := by
  obtain ⟨ρ', hρ'⟩ := exists_semidirectProduct_extension_det_eq_one hscalar hcop htwist
  exact ⟨ρ', hρ', fun ρ'' hρ'' ↦
    semidirectProduct_extension_det_eq_one_unique hscalar hcop hρ''.1 hρ'.1 hρ''.2 hρ'.2⟩

end Representation
