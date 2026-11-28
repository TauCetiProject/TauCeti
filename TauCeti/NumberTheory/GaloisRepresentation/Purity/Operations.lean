/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.GaloisRepresentation.Purity
public import TauCeti.NumberTheory.WeilNumber.Pure
import Mathlib.NumberTheory.Real.Irrational
import TauCeti.LinearAlgebra.Charpoly.Quotient
import TauCeti.RepresentationTheory.Dual
import TauCeti.RepresentationTheory.Intertwining
import TauCeti.RepresentationTheory.Quotient
import TauCeti.RepresentationTheory.Rep.Subrepresentation

/-!
# Purity of representations under subquotients, extensions, direct sums and duals

Let `ρ` be a finite-dimensional representation of a group `G` over a field `E`, with inertia
subgroups `I v`, Frobenius elements `F v` and residue sizes `q v` at the places `v` of an index
type, as in `Representation.IsPureOutside`. This file shows how purity outside a set `T` of places
behaves under the linear algebra operations that do not change the eigenvalues of Frobenius beyond
inverting them.

* **Subquotients and extensions.** For a short exact sequence `0 → σ → ρ → τ → 0` of
  representations, `ρ` is pure of weight `w` outside `T` exactly when `ρ` is unramified outside
  `T` and `σ` and `τ` are pure of weight `w` outside `T`. Unramifiedness of the middle term is a
  genuine hypothesis in the converse: purity only constrains the characteristic polynomial of
  Frobenius, which does not see the extension class, and an extension of unramified
  representations can be ramified. The same holds for `ι`-purity of a real weight.
* **Direct sums.** A direct sum is pure of weight `w` exactly when both summands are.
* **Duals.** The contragredient of a representation pure of weight `w` is pure of weight `-w`,
  since geometric Frobenius acts on the dual with the inverse eigenvalues.

Integral characteristic polynomials behave differently. They are preserved by direct sums, but a
subrepresentation of a representation with integral characteristic polynomials need not have them:
on the sum of the lines on which Frobenius acts by `√2` and by `-√2`, Frobenius has characteristic
polynomial `X² - 2`, but on the first line `X - √2`, which is not rational. The file closes with
this example.

## Main results

* `Representation.isPureOutside_iff_isPure`: purity outside `T` is unramifiedness together with
  purity of each `ρ (F v)`, `v ∉ T`, in the sense of `TauCeti.IsPure`.
* `Representation.isPureOutside_iff_of_exact`,
  `Representation.isPureOutside_iff_subrepresentation_quotient`: purity along a short exact
  sequence, and on an invariant submodule and its quotient.
* `Representation.isPureOutside_prod_iff`: purity of a direct sum.
* `Representation.isPureOutside_dual_iff`: the dual of a representation of weight `w` has weight
  `-w`.
* `Representation.isIotaPureOutside_iff_of_exact`,
  `Representation.isIotaPureOutside_iff_subrepresentation_quotient`,
  `Representation.isIotaPureOutside_prod_iff`, `Representation.isIotaPureOutside_dual_iff`: the
  same statements for `ι`-purity.
* `Representation.HasIntegralCharpolyOutside.prod`: integral characteristic polynomials are
  preserved by direct sums.

## References

* P. Deligne, *La conjecture de Weil. II*, Publ. Math. IHÉS 52 (1980), §1.2, Stabilités
  (1.2.5).
* B. Lawrence, A. Venkatesh, *Diophantine problems and p-adic period mappings*, Invent. Math.
  221 (2020), §2.5.
-/

public section

open Module Polynomial TauCeti

namespace Representation

/-! ### Unramified representations -/

section IsUnramifiedOutside

variable {k G V W κ : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]
  [AddCommMonoid W] [Module k W] {ρ : Representation k G V} {σ : Representation k G W}
  {I : κ → Subgroup G} {T : Set κ}

/-- A representation mapping injectively into one unramified outside `T` is unramified
outside `T`. -/
theorem IsUnramifiedOutside.of_injective (h : ρ.IsUnramifiedOutside I T)
    (i : IntertwiningMap σ ρ) (hi : Function.Injective i) : σ.IsUnramifiedOutside I T :=
  h.of_ker_le (i.ker_le_ker_of_injective hi)

/-- A representation onto which one unramified outside `T` maps surjectively is unramified
outside `T`. -/
theorem IsUnramifiedOutside.of_surjective (h : ρ.IsUnramifiedOutside I T)
    (π : IntertwiningMap ρ σ) (hπ : Function.Surjective π) : σ.IsUnramifiedOutside I T :=
  h.of_ker_le (π.ker_le_ker_of_surjective hπ)

/-- A direct sum is unramified outside `T` exactly when both summands are. -/
@[simp]
theorem isUnramifiedOutside_prod_iff :
    (ρ.prod σ).IsUnramifiedOutside I T ↔ ρ.IsUnramifiedOutside I T ∧ σ.IsUnramifiedOutside I T := by
  simp only [isUnramifiedOutside_iff_le_ker, ker_prod, le_inf_iff, ← forall_and]

end IsUnramifiedOutside

/-- Over a field, the dual of a representation is unramified outside `T` exactly when the
representation is. -/
@[simp]
theorem isUnramifiedOutside_dual_iff {k G V κ : Type*} [Field k] [Group G] [AddCommGroup V]
    [Module k V] {ρ : Representation k G V} {I : κ → Subgroup G} {T : Set κ} :
    ρ.dual.IsUnramifiedOutside I T ↔ ρ.IsUnramifiedOutside I T := by
  simp only [isUnramifiedOutside_iff_le_ker, ker_dual]

variable {E G V V₁ V₂ κ : Type*} [Field E] [Group G] [AddCommGroup V] [Module E V]
  [FiniteDimensional E V] [AddCommGroup V₁] [Module E V₁] [FiniteDimensional E V₁]
  [AddCommGroup V₂] [Module E V₂] [FiniteDimensional E V₂] {ρ : Representation E G V}
  {σ : Representation E G V₁} {τ : Representation E G V₂} {I : κ → Subgroup G} {F : κ → G}
  {q : κ → ℕ} {T : Set κ}

/-! ### Purity of an integer weight -/

section IsPureOutside

variable [Algebra ℚ E] {w : ℤ}

/-- A representation is pure of weight `w` outside `T` exactly when it is unramified outside `T`
and each Frobenius element `ρ (F v)`, `v ∉ T`, is pure of weight `w` relative to `q v`. -/
theorem isPureOutside_iff_isPure : ρ.IsPureOutside I F q T w ↔
    ρ.IsUnramifiedOutside I T ∧ ∀ v ∉ T, IsPure (q v : ℝ) w (ρ (F v)) := by
  simp only [isPureOutside_iff, isPure_iff_forall_mem_aroots (AlgebraicClosure E)]

/-- A representation mapping injectively into one pure of weight `w` outside `T`, such as a
subrepresentation, is pure of weight `w` outside `T`. -/
theorem IsPureOutside.of_injective (h : ρ.IsPureOutside I F q T w) (i : IntertwiningMap σ ρ)
    (hi : Function.Injective i) : σ.IsPureOutside I F q T w := by
  rw [isPureOutside_iff_isPure] at h ⊢
  exact ⟨h.1.of_injective i hi, fun v hv ↦
    (h.2 v hv).of_injective (i := i.toLinearMap) hi (i.isIntertwining' (F v)).symm⟩

/-- A representation onto which one pure of weight `w` outside `T` maps surjectively, such as a
quotient, is pure of weight `w` outside `T`. -/
theorem IsPureOutside.of_surjective (h : ρ.IsPureOutside I F q T w) (π : IntertwiningMap ρ τ)
    (hπ : Function.Surjective π) : τ.IsPureOutside I F q T w := by
  rw [isPureOutside_iff_isPure] at h ⊢
  exact ⟨h.1.of_surjective π hπ, fun v hv ↦
    (h.2 v hv).of_surjective (π := π.toLinearMap) hπ (π.isIntertwining' (F v))⟩

/-- If the Frobenius characteristic polynomials of `ρ` are the products of those of `σ` and `τ`,
and `σ` and `τ` are unramified wherever `ρ` is, then `ρ` is pure exactly when it is unramified and
`σ` and `τ` are pure. -/
private theorem isPureOutside_iff_of_charpoly_eq_mul
    (hσ : ρ.IsUnramifiedOutside I T → σ.IsUnramifiedOutside I T)
    (hτ : ρ.IsUnramifiedOutside I T → τ.IsUnramifiedOutside I T)
    (h : ∀ v, (ρ (F v)).charpoly = (σ (F v)).charpoly * (τ (F v)).charpoly) :
    ρ.IsPureOutside I F q T w ↔ ρ.IsUnramifiedOutside I T ∧ σ.IsPureOutside I F q T w ∧
      τ.IsPureOutside I F q T w := by
  simp only [isPureOutside_iff_isPure, isPure_iff_of_charpoly_eq_mul (h _)]
  refine ⟨fun ⟨hρ, hF⟩ ↦ ⟨hρ, ⟨hσ hρ, fun v hv ↦ (hF v hv).1⟩, ⟨hτ hρ, fun v hv ↦ (hF v hv).2⟩⟩,
    fun ⟨hρ, ⟨_, h₁⟩, ⟨_, h₂⟩⟩ ↦ ⟨hρ, fun v hv ↦ ⟨h₁ v hv, h₂ v hv⟩⟩⟩

/-- **Purity along a short exact sequence.** If `0 → σ --i--> ρ --π--> τ → 0` is an exact
sequence of representations, then `ρ` is pure of weight `w` outside `T` exactly when it is
unramified outside `T` and `σ` and `τ` are pure of weight `w` outside `T`. -/
theorem isPureOutside_iff_of_exact (i : IntertwiningMap σ ρ) (π : IntertwiningMap ρ τ)
    (hi : Function.Injective i) (hπ : Function.Surjective π) (hex : Function.Exact i π) :
    ρ.IsPureOutside I F q T w ↔ ρ.IsUnramifiedOutside I T ∧ σ.IsPureOutside I F q T w ∧
      τ.IsPureOutside I F q T w :=
  isPureOutside_iff_of_charpoly_eq_mul
    (fun h ↦ h.of_ker_le (i.ker_le_ker_of_injective hi))
    (fun h ↦ h.of_ker_le (π.ker_le_ker_of_surjective hπ))
    fun v ↦ i.charpoly_apply_eq_mul_of_exact π hi hπ hex (F v)

/-- A representation is pure of weight `w` outside `T` exactly when it is unramified outside `T`
and its restriction to an invariant submodule and the induced representation on the quotient are
pure of weight `w` outside `T`. -/
theorem isPureOutside_iff_subrepresentation_quotient (U : Submodule E V)
    (hU : ∀ g, U ≤ U.comap (ρ g)) :
    ρ.IsPureOutside I F q T w ↔ ρ.IsUnramifiedOutside I T ∧
      (ρ.subrepresentation U hU).IsPureOutside I F q T w ∧
      (ρ.quotient U hU).IsPureOutside I F q T w :=
  isPureOutside_iff_of_exact (Rep.subtype (Rep.of ρ) U hU).hom (Rep.mkQ (Rep.of ρ) U hU).hom
    (by rw [Rep.coe_subtype_hom]; exact U.injective_subtype)
    (by rw [Rep.coe_mkQ_hom]; exact U.mkQ_surjective)
    (by rw [Rep.coe_subtype_hom, Rep.coe_mkQ_hom]; exact LinearMap.exact_subtype_mkQ U)

/-- A direct sum is pure of weight `w` outside `T` exactly when both summands are. -/
@[simp]
theorem isPureOutside_prod_iff :
    (σ.prod τ).IsPureOutside I F q T w ↔ σ.IsPureOutside I F q T w ∧ τ.IsPureOutside I F q T w := by
  rw [isPureOutside_iff_of_charpoly_eq_mul (fun h ↦ (isUnramifiedOutside_prod_iff.mp h).1)
    (fun h ↦ (isUnramifiedOutside_prod_iff.mp h).2) fun v ↦ charpoly_prod_apply σ τ (F v),
    isUnramifiedOutside_prod_iff]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨⟨h.1.isUnramifiedOutside, h.2.isUnramifiedOutside⟩, h⟩⟩

/-- The dual of a representation is pure of weight `w` outside `T` exactly when the
representation is pure of weight `-w` outside `T`: geometric Frobenius acts on the dual with the
inverse eigenvalues. -/
@[simp]
theorem isPureOutside_dual_iff :
    ρ.dual.IsPureOutside I F q T w ↔ ρ.IsPureOutside I F q T (-w) := by
  simp only [isPureOutside_iff, isUnramifiedOutside_dual_iff, aroots_charpoly_dual_apply,
    Multiset.forall_mem_map_iff, isWeilNumber_inv_iff]

/-- The dual of a representation pure of weight `w` outside `T` is pure of weight `-w` outside
`T`. -/
theorem IsPureOutside.dual (h : ρ.IsPureOutside I F q T w) : ρ.dual.IsPureOutside I F q T (-w) :=
  isPureOutside_dual_iff.mpr (by rwa [neg_neg])

end IsPureOutside

/-! ### `ι`-purity of a real weight -/

section IsIotaPureOutside

variable {ι : E →+* ℂ} {r : ℝ}

/-- A representation mapping injectively into one `ι`-pure of weight `r` outside `T`, such as a
subrepresentation, is `ι`-pure of weight `r` outside `T`. -/
theorem IsIotaPureOutside.of_injective (h : ρ.IsIotaPureOutside ι I F q T r)
    (i : IntertwiningMap σ ρ) (hi : Function.Injective i) : σ.IsIotaPureOutside ι I F q T r :=
  ⟨h.isUnramifiedOutside.of_injective i hi, fun v hv z hz ↦ h.norm_eq v hv z <|
    Multiset.mem_of_le (roots.le_of_dvd ((ρ (F v)).charpoly_monic.map ι).ne_zero <| map_dvd ι <|
      LinearMap.charpoly_dvd_of_injective_of_comp_eq_comp _ _ _ hi (i.isIntertwining' (F v))) hz⟩

/-- A representation onto which one `ι`-pure of weight `r` outside `T` maps surjectively, such as
a quotient, is `ι`-pure of weight `r` outside `T`. -/
theorem IsIotaPureOutside.of_surjective (h : ρ.IsIotaPureOutside ι I F q T r)
    (π : IntertwiningMap ρ τ) (hπ : Function.Surjective π) : τ.IsIotaPureOutside ι I F q T r :=
  ⟨h.isUnramifiedOutside.of_surjective π hπ, fun v hv z hz ↦ h.norm_eq v hv z <|
    Multiset.mem_of_le (roots.le_of_dvd ((ρ (F v)).charpoly_monic.map ι).ne_zero <| map_dvd ι <|
      LinearMap.charpoly_dvd_of_surjective_of_comp_eq_comp _ _ _ hπ (π.isIntertwining' (F v))) hz⟩

/-- If the Frobenius characteristic polynomials of `ρ` are the products of those of `σ` and `τ`,
and `σ` and `τ` are unramified wherever `ρ` is, then `ρ` is `ι`-pure exactly when it is
unramified and `σ` and `τ` are `ι`-pure. -/
private theorem isIotaPureOutside_iff_of_charpoly_eq_mul
    (hσ : ρ.IsUnramifiedOutside I T → σ.IsUnramifiedOutside I T)
    (hτ : ρ.IsUnramifiedOutside I T → τ.IsUnramifiedOutside I T)
    (h : ∀ v, (ρ (F v)).charpoly = (σ (F v)).charpoly * (τ (F v)).charpoly) :
    ρ.IsIotaPureOutside ι I F q T r ↔ ρ.IsUnramifiedOutside I T ∧
      σ.IsIotaPureOutside ι I F q T r ∧ τ.IsIotaPureOutside ι I F q T r := by
  have hroots (v : κ) : ((ρ (F v)).charpoly.map ι).roots =
      ((σ (F v)).charpoly.map ι).roots + ((τ (F v)).charpoly.map ι).roots := by
    rw [h, Polynomial.map_mul, roots_mul
      ((((σ (F v)).charpoly_monic.map ι).mul ((τ (F v)).charpoly_monic.map ι)).ne_zero)]
  simp only [isIotaPureOutside_iff, hroots, Multiset.mem_add, or_imp, forall_and]
  refine ⟨fun ⟨hρ, h₁, h₂⟩ ↦ ⟨hρ, ⟨hσ hρ, h₁⟩, ⟨hτ hρ, h₂⟩⟩,
    fun ⟨hρ, ⟨_, h₁⟩, ⟨_, h₂⟩⟩ ↦ ⟨hρ, h₁, h₂⟩⟩

/-- **`ι`-purity along a short exact sequence.** If `0 → σ --i--> ρ --π--> τ → 0` is an exact
sequence of representations, then `ρ` is `ι`-pure of weight `r` outside `T` exactly when it is
unramified outside `T` and `σ` and `τ` are `ι`-pure of weight `r` outside `T`. -/
theorem isIotaPureOutside_iff_of_exact (i : IntertwiningMap σ ρ) (π : IntertwiningMap ρ τ)
    (hi : Function.Injective i) (hπ : Function.Surjective π) (hex : Function.Exact i π) :
    ρ.IsIotaPureOutside ι I F q T r ↔ ρ.IsUnramifiedOutside I T ∧
      σ.IsIotaPureOutside ι I F q T r ∧ τ.IsIotaPureOutside ι I F q T r :=
  isIotaPureOutside_iff_of_charpoly_eq_mul
    (fun h ↦ h.of_ker_le (i.ker_le_ker_of_injective hi))
    (fun h ↦ h.of_ker_le (π.ker_le_ker_of_surjective hπ))
    fun v ↦ i.charpoly_apply_eq_mul_of_exact π hi hπ hex (F v)

/-- A representation is `ι`-pure of weight `r` outside `T` exactly when it is unramified outside
`T` and its restriction to an invariant submodule and the induced representation on the quotient
are `ι`-pure of weight `r` outside `T`. -/
theorem isIotaPureOutside_iff_subrepresentation_quotient (U : Submodule E V)
    (hU : ∀ g, U ≤ U.comap (ρ g)) :
    ρ.IsIotaPureOutside ι I F q T r ↔ ρ.IsUnramifiedOutside I T ∧
      (ρ.subrepresentation U hU).IsIotaPureOutside ι I F q T r ∧
      (ρ.quotient U hU).IsIotaPureOutside ι I F q T r :=
  isIotaPureOutside_iff_of_exact (Rep.subtype (Rep.of ρ) U hU).hom (Rep.mkQ (Rep.of ρ) U hU).hom
    (by rw [Rep.coe_subtype_hom]; exact U.injective_subtype)
    (by rw [Rep.coe_mkQ_hom]; exact U.mkQ_surjective)
    (by rw [Rep.coe_subtype_hom, Rep.coe_mkQ_hom]; exact LinearMap.exact_subtype_mkQ U)

/-- A direct sum is `ι`-pure of weight `r` outside `T` exactly when both summands are. -/
@[simp]
theorem isIotaPureOutside_prod_iff :
    (σ.prod τ).IsIotaPureOutside ι I F q T r ↔
      σ.IsIotaPureOutside ι I F q T r ∧ τ.IsIotaPureOutside ι I F q T r := by
  rw [isIotaPureOutside_iff_of_charpoly_eq_mul (fun h ↦ (isUnramifiedOutside_prod_iff.mp h).1)
    (fun h ↦ (isUnramifiedOutside_prod_iff.mp h).2) fun v ↦ charpoly_prod_apply σ τ (F v),
    isUnramifiedOutside_prod_iff]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨⟨h.1.isUnramifiedOutside, h.2.isUnramifiedOutside⟩, h⟩⟩

/-- The dual of a representation is `ι`-pure of weight `r` outside `T` exactly when the
representation is `ι`-pure of weight `-r` outside `T`. -/
@[simp]
theorem isIotaPureOutside_dual_iff :
    ρ.dual.IsIotaPureOutside ι I F q T r ↔ ρ.IsIotaPureOutside ι I F q T (-r) := by
  have hroots (g : G) : ((ρ.dual g).charpoly.map ι).roots = (((ρ g).charpoly.map ι).roots).map
      (·⁻¹) := by
    let _ := ι.toAlgebra
    rw [← RingHom.algebraMap_toAlgebra ι, ← aroots_def, ← aroots_def]
    exact aroots_charpoly_dual_apply ρ g
  simp only [isIotaPureOutside_iff, isUnramifiedOutside_dual_iff, hroots,
    Multiset.forall_mem_map_iff, norm_inv, neg_div, Real.rpow_neg (Nat.cast_nonneg _),
    inv_eq_iff_eq_inv]

/-- The dual of a representation `ι`-pure of weight `r` outside `T` is `ι`-pure of weight `-r`
outside `T`. -/
theorem IsIotaPureOutside.dual (h : ρ.IsIotaPureOutside ι I F q T r) :
    ρ.dual.IsIotaPureOutside ι I F q T (-r) :=
  isIotaPureOutside_dual_iff.mpr (by rwa [neg_neg])

end IsIotaPureOutside

/-! ### Integral characteristic polynomials -/

/-- A direct sum of representations with integral characteristic polynomials outside `T` has
integral characteristic polynomials outside `T`. -/
theorem HasIntegralCharpolyOutside.prod {R W₁ W₂ : Type*} [CommRing R] [AddCommGroup W₁]
    [Module R W₁] [Module.Free R W₁] [Module.Finite R W₁] [AddCommGroup W₂] [Module R W₂]
    [Module.Free R W₂] [Module.Finite R W₂] {σ₁ : Representation R G W₁}
    {σ₂ : Representation R G W₂} (h₁ : σ₁.HasIntegralCharpolyOutside I F T)
    (h₂ : σ₂.HasIntegralCharpolyOutside I F T) : (σ₁.prod σ₂).HasIntegralCharpolyOutside I F T :=
  ⟨isUnramifiedOutside_prod_iff.mpr ⟨h₁.isUnramifiedOutside, h₂.isUnramifiedOutside⟩,
    fun v hv ↦ by
      rw [charpoly_prod_apply]
      exact mul_mem (h₁.charpoly_mem_lifts v hv) (h₂.charpoly_mem_lifts v hv)⟩

/-! ### Examples

With one place, trivial inertia and Frobenius the generator of `Multiplicative ℤ`, the direct sum
of the lines on which Frobenius acts by `√2` and by `-√2` has integral characteristic polynomial
`X² - 2`, the product of `X - √2` and `X + √2`, while the first line alone has characteristic
polynomial `X - √2`. -/

/-- The character of `Multiplicative ℤ` sending the generator to `a`. -/
private noncomputable abbrev zpowChar (a : ℝ) (ha : a ≠ 0) : Multiplicative ℤ →* ℝˣ :=
  zpowersHom ℝˣ (Units.mk0 a ha)

/- The sum of the lines on which Frobenius acts by `√2` and by `-√2` has integral characteristic
polynomials, but its first summand, an invariant line, does not. -/
example : ((ofLinearCharacter (zpowChar √2 (Real.sqrt_ne_zero'.mpr two_pos))).prod
      (ofLinearCharacter (zpowChar (-√2) (neg_ne_zero.mpr (Real.sqrt_ne_zero'.mpr two_pos))))
      ).HasIntegralCharpolyOutside (fun _ : Unit ↦ ⊥) (fun _ ↦ .ofAdd 1) ∅ ∧
    ¬(ofLinearCharacter (zpowChar √2 (Real.sqrt_ne_zero'.mpr two_pos))).HasIntegralCharpolyOutside
      (fun _ : Unit ↦ ⊥) (fun _ ↦ .ofAdd 1) ∅ := by
  refine ⟨⟨by simp [isUnramifiedOutside_iff], fun _ _ ↦ ⟨X ^ 2 - 2, ?_⟩⟩, fun h ↦ ?_⟩
  · simp only [charpoly_prod_apply, charpoly_ofLinearCharacter_apply, zpowersHom_apply,
      toAdd_ofAdd, zpow_one, Units.val_mk0, map_neg, sub_neg_eq_add, coe_mapRingHom,
      Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_ofNat]
    rw [mul_comm, ← sq_sub_sq, ← C_pow, Real.sq_sqrt zero_le_two, map_ofNat]
  · obtain ⟨n, hn⟩ := ((hasIntegralCharpolyOutside_ofLinearCharacter_iff _).mp h).2 ()
      (Set.notMem_empty _)
    exact irrational_sqrt_two.ne_int n (by simpa using hn)

end Representation
