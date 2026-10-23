/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.RingHoms
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic
import TauCeti.Data.ZMod.Torsion

/-!
# Lifting characters of `ℤ_p^ι × ℤ_p ⧸ (q)` from `𝔽_p` to `ℤ/p²`

An additive homomorphism `ψ : ℤ_p → 𝔽_p` is determined by `ψ 1`: it kills `pℤ_p`, so it is
`x ↦ (x mod p) ψ(1)`. Consequently a continuous character of the abelian pro-`p` group
`A = ℤ_p^ι × ℤ_p ⧸ (q)`, `ι` finite and `p ∣ q`, with values in `𝔽_p` is a combination of the
reductions modulo `p` of the coordinates. This decides when such a character lifts to a continuous
character with values in `ℤ/p²`:

* if `p² ∣ q`, including `q = 0`, every character `A → 𝔽_p` lifts, the lift being the same
  combination of the truncations modulo `p²` of the coordinates;
* if `q = p`, the reduction `(x, y) ↦ y mod p` on the factor `ℤ_p ⧸ (p) = 𝔽_p` does not lift: a
  lift would take an element of order `p` to an element of `ℤ/p²` killed by `p`, whose reduction
  modulo `p` is `0`.

At `p = 2` this is the module-theoretic side of the fact that the cup square on `H¹(G, 𝔽₂)` of a
Demushkin group `G` vanishes identically exactly when its invariant `q` is not `2`: through
`G^{ab} ≅ ℤ_2^{n-1} × ℤ_2 ⧸ (q)`, the characters of `G` with values in `𝔽₂` that lift to `ℤ/4` are
exactly those with vanishing cup square.

## Main declarations

* `PadicInt.addMonoidHom_apply_eq_toZMod_mul_apply_one`: an additive homomorphism `ℤ_p → 𝔽_p` is
  `x ↦ (x mod p) ψ(1)`.
* `PadicInt.piProdQuotientSpanToZMod`: the character `(x, y) ↦ y mod p` of
  `ℤ_p^ι × ℤ_p ⧸ (q)`, for `p ∣ q`.
* `PadicInt.exists_forall_castHom_toAdd_eq_toAdd_of_pow_two_dvd`: **for `p² ∣ q`, every continuous
  character `ℤ_p^ι × ℤ_p ⧸ (q) → 𝔽_p` lifts to `ℤ/p²`.**
* `PadicInt.exists_castHom_toAdd_ne_toAdd_piProdQuotientSpanToZMod`: **the character
  `(x, y) ↦ y mod p` of `ℤ_p^ι × ℤ_p ⧸ (p)` does not lift to `ℤ/p²`.**
-/

public section

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- **An additive homomorphism `ℤ_p → 𝔽_p` is determined by its value at `1`**: it kills `pℤ_p`,
so it is `x ↦ (x mod p) ψ(1)`. -/
theorem addMonoidHom_apply_eq_toZMod_mul_apply_one (ψ : ℤ_[p] →+ ZMod p) (x : ℤ_[p]) :
    ψ x = toZMod x * ψ 1 := by
  have hmem : x - (ZMod.cast (toZMod x) : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p])} := by
    rw [← maximalIdeal_eq_span_p]
    exact toZMod_spec x
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
  rw [ZMod.cast_eq_val] at ha
  have hx : x = (toZMod x).val • (1 : ℤ_[p]) + p • a := by
    rw [nsmul_one, nsmul_eq_mul]
    linear_combination -ha
  conv_lhs => rw [hx]
  rw [map_add, map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul, ZMod.natCast_zmod_val,
    ZMod.natCast_self, zero_mul, add_zero]

variable {ι : Type*} {q : ℤ_[p]}

/-- **The character `(x, y) ↦ y mod p` of `ℤ_p^ι × ℤ_p ⧸ (q)`**, for `p ∣ q`: the reduction
modulo `p` of the second coordinate, as a continuous character with values in `𝔽_p`. -/
noncomputable def piProdQuotientSpanToZMod (hq : (p : ℤ_[p]) ∣ q) :
    Multiplicative ((ι → ℤ_[p]) × (ℤ_[p] ⧸ Ideal.span {q})) →ₜ* Multiplicative (ZMod p) where
  toFun a := Multiplicative.ofAdd (quotientSpanToZMod hq (Multiplicative.toAdd a).2)
  map_one' := by simp
  map_mul' a b := by simp [← ofAdd_add]
  continuous_toFun :=
    continuous_ofAdd.comp
      ((continuous_quotientSpanToZMod hq).comp (continuous_snd.comp continuous_toAdd))

/-- The character `(x, y) ↦ y mod p` takes the value `y mod p` at `(x, y)`. -/
@[simp]
theorem piProdQuotientSpanToZMod_ofAdd (hq : (p : ℤ_[p]) ∣ q) (x : ι → ℤ_[p])
    (y : ℤ_[p] ⧸ Ideal.span {q}) :
    piProdQuotientSpanToZMod hq (Multiplicative.ofAdd (x, y)) =
      Multiplicative.ofAdd (quotientSpanToZMod hq y) :=
  (rfl)

/-! ### Lifting from `𝔽_p` to `ℤ/p²` -/

/-- **For `p² ∣ q`, every continuous character `ℤ_p^ι × ℤ_p ⧸ (q) → 𝔽_p` lifts to `ℤ/p²`**: writing
the character as `(x, y) ↦ ∑ᵢ (xᵢ mod p) cᵢ + (y mod p) c₀`, the same combination of the
truncations modulo `p²` of the coordinates is a continuous character with values in `ℤ/p²` whose
reduction modulo `p` is the given one. This includes `q = 0`. -/
theorem exists_forall_castHom_toAdd_eq_toAdd_of_pow_two_dvd [Finite ι] (hq : (p : ℤ_[p]) ^ 2 ∣ q)
    (χ : Multiplicative ((ι → ℤ_[p]) × (ℤ_[p] ⧸ Ideal.span {q})) →ₜ* Multiplicative (ZMod p)) :
    ∃ φ : Multiplicative ((ι → ℤ_[p]) × (ℤ_[p] ⧸ Ideal.span {q})) →ₜ* Multiplicative (ZMod (p ^ 2)),
      ∀ a, ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) (Multiplicative.toAdd (φ a)) =
        Multiplicative.toAdd (χ a) := by
  classical
  cases nonempty_fintype ι
  set ρ := quotientSpanToZModPow 2 hq with hρ
  -- The additive form of `χ`.
  let χ' : (ι → ℤ_[p]) × (ℤ_[p] ⧸ Ideal.span {q}) →+ ZMod p :=
    { toFun := fun a ↦ Multiplicative.toAdd (χ (Multiplicative.ofAdd a))
      map_zero' := by simp
      map_add' := fun a b ↦ by simp [ofAdd_add] }
  -- Its coefficients on the coordinates.
  set c : ι → ZMod p := fun i ↦ χ' (Pi.single i 1, 0)
  set c₀ : ZMod p := χ' (0, 1)
  have hP : ∀ x : ι → ℤ_[p], χ' (x, 0) = ∑ i, toZMod (x i) * c i := by
    intro x
    have h := congrArg (χ'.comp (AddMonoidHom.inl (ι → ℤ_[p]) (ℤ_[p] ⧸ Ideal.span {q})))
      (Finset.univ_sum_single x).symm
    rw [map_sum] at h
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.inl_apply] at h
    rw [h]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simpa [AddMonoidHom.comp_apply] using addMonoidHom_apply_eq_toZMod_mul_apply_one
      (χ'.comp ((AddMonoidHom.inl _ _).comp (AddMonoidHom.single (fun _ ↦ ℤ_[p]) i))) (x i)
  have hQ : ∀ y : ℤ_[p], χ' (0, Ideal.Quotient.mk _ y) = toZMod y * c₀ := fun y ↦ by
    simpa [AddMonoidHom.comp_apply] using addMonoidHom_apply_eq_toZMod_mul_apply_one
      (χ'.comp ((AddMonoidHom.inr _ _).comp (Ideal.Quotient.mk _).toAddMonoidHom)) y
  -- The lift, as an additive homomorphism.
  let φ' : (ι → ℤ_[p]) × (ℤ_[p] ⧸ Ideal.span {q}) →+ ZMod (p ^ 2) :=
    { toFun := fun a ↦ ∑ i, toZModPow 2 (a.1 i) * (ZMod.cast (c i) : ZMod (p ^ 2)) +
        ρ a.2 * (ZMod.cast c₀ : ZMod (p ^ 2))
      map_zero' := by simp
      map_add' := fun a b ↦ by
        simp only [Prod.fst_add, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib,
          Prod.snd_add]
        abel }
  have hφ' : Continuous φ' :=
    (continuous_finsetSum _ fun i _ ↦ (((continuous_toZModPow 2).comp
      ((continuous_apply i).comp continuous_fst)).mul continuous_const)).add
      (((continuous_quotientSpanToZModPow 2 hq).comp continuous_snd).mul continuous_const)
  refine ⟨⟨AddMonoidHom.toMultiplicative φ', continuous_ofAdd.comp (hφ'.comp continuous_toAdd)⟩,
    fun a ↦ ?_⟩
  obtain ⟨⟨x, y⟩, rfl⟩ := Multiplicative.ofAdd.surjective a
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hχ : χ' (x, Ideal.Quotient.mk _ y) = ∑ i, toZMod (x i) * c i + toZMod y * c₀ := by
    rw [← hP, ← hQ, ← map_add, Prod.mk_add_mk, add_zero, zero_add]
  -- `AddMonoidHom.toMultiplicative` and `toAdd ∘ ofAdd` unfold definitionally, and `χ'` is `χ`
  -- read additively, so both sides are the additive maps evaluated at `(x, y)`.
  change ZMod.castHom _ (ZMod p) (φ' (x, Ideal.Quotient.mk _ y)) = χ' (x, Ideal.Quotient.mk _ y)
  rw [hχ]
  simp only [φ', AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_add, map_sum, map_mul,
    ZMod.castHom_apply, ZMod.cast_cast_zmod_of_le (Nat.le_self_pow two_ne_zero p), hρ,
    quotientSpanToZModPow_mk, cast_toZModPow_eq_toZMod two_ne_zero]

/-- **The character `(x, y) ↦ y mod p` of `ℤ_p^ι × ℤ_p ⧸ (p)` does not lift to `ℤ/p²`**: the
element `(0, 1)` has order `p`, so a lift would send it to an element of `ℤ/p²` killed by `p`,
whose reduction modulo `p` is `0`, while the character takes the value `1` there. -/
theorem exists_castHom_toAdd_ne_toAdd_piProdQuotientSpanToZMod
    (φ : Multiplicative ((ι → ℤ_[p]) × (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])})) →ₜ*
      Multiplicative (ZMod (p ^ 2))) :
    ∃ a, ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) (Multiplicative.toAdd (φ a)) ≠
      Multiplicative.toAdd (piProdQuotientSpanToZMod (q := (p : ℤ_[p])) (dvd_refl _) a) := by
  refine ⟨Multiplicative.ofAdd (0, Ideal.Quotient.mk _ 1), fun h ↦ ?_⟩
  rw [piProdQuotientSpanToZMod_ofAdd, quotientSpanToZMod_mk, toAdd_ofAdd, map_one toZMod] at h
  set t : Multiplicative ((ι → ℤ_[p]) × (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])})) :=
    Multiplicative.ofAdd (0, Ideal.Quotient.mk _ 1) with ht
  have hsq : t ^ p = 1 := by
    rw [← ofAdd_nsmul, Prod.smul_mk, smul_zero, ← map_nsmul, nsmul_one,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), ofAdd_eq_one]
    rfl
  have hp : (p : ZMod (p ^ 2)) * Multiplicative.toAdd (φ t) = 0 := by
    rw [← nsmul_eq_mul, ← toAdd_pow, ← map_pow, hsq, map_one, toAdd_one]
  rw [ZMod.castHom_apply, ZMod.cast_eq_zero_of_natCast_mul_eq_zero hp] at h
  exact zero_ne_one h

end PadicInt
