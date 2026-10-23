/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.DegreeOneForm
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Prescription
public import TauCeti.Topology.Algebra.Group.Profinite.Free.RelatorFunctional
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicUnits
import Mathlib.NumberTheory.Padics.ProperSpace
import TauCeti.Topology.Algebra.Group.Profinite.Free.PadicUnits

/-!
# The linearisation of crossed homomorphisms of a free pro-`p` group in the character

Let `F = freeProP p X` be the free pro-`p` group on a finite type `X`, and let `χ, χ' : F → ℤ_pˣ`
be two continuous characters. Their values lie in the principal units `1 + pℤ_p`, and if they are
congruent modulo `p ^ k` on the generators, then they are congruent modulo `p ^ k` everywhere
(`TauCeti.freeProP.pow_dvd_sub_of_forall_of`). Let `f` and `f'` be continuous crossed
homomorphisms `F → ℤ_p` for `χ` and `χ'` with the same values on the generators. Then `f' ≡ f`
modulo `p ^ k` (`TauCeti.IsCrossedHom.pow_dvd_sub_of_forall_of_eq`), and the quotient
`(f' - f) / p ^ k`, read modulo `p`, is a Heisenberg cochain for the two `𝔽_p`-characters
`(χ' - χ) / p ^ k mod p` and `f mod p`. On `λ_1(F)` a Heisenberg cochain is the degree-one form
of the class in `gr_1(F)`, evaluated at the two characters. Hence for `n ∈ λ_1(F)`,

  `f' n ≡ f n + Σ_{i,j} (χ'(x_i) - χ(x_i)) · f(x_j) · B_n(χ_i, χ_j)   mod p^(k+1)`,

where `x_i = of i` are the generators, `χ_i` the coordinate `𝔽_p`-characters, and `B_n` the
degree-one form of the class of `n` (`TauCeti.freeProP.degreeOneForm`), with its values lifted to
`ℤ_p` (`TauCeti.IsCrossedHom.pow_succ_dvd_sub_sub_sum_degreeOneForm`). This is a Taylor expansion
to first order in the character: the value of a crossed homomorphism on a fixed element of the
Frattini subgroup, as a function of the values of the character on the generators, has the
degree-one form of that element as its derivative modulo `p`. It is the linearisation that
Newton's method uses to find the canonical character of a Demushkin group.

## Main result

* `TauCeti.IsCrossedHom.pow_succ_dvd_sub_sub_sum_degreeOneForm`: the first-order expansion above,
  modulo `p ^ (k + 1)`, on the Frattini subgroup.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §2,
  Proposition 3 and Theorem 4.
-/

public section

namespace TauCeti

open ContCohomology freeProP

universe u

-- Preferring the ring path keeps a single additive structure on `ZMod p`, so that the trivial
-- action installed below is the one the cocycles and the degree-one form are stated against.
attribute [local instance 2000] Ring.toAddCommGroup

variable {p : ℕ} [Fact p.Prime] {X : Type u}

/-- **The first-order expansion of a crossed homomorphism in the character, on the Frattini
subgroup.** Let `χ, χ' : F → ℤ_pˣ` be continuous characters of the free pro-`p` group on a finite
type `X`, congruent modulo `p ^ k` on the generators `x_i = of i`, and let `f, f'` be continuous
crossed homomorphisms for `χ, χ'` with the same values on the generators. Then for `n ∈ λ_1(F)`,

  `f' n ≡ f n + Σ_{i,j} (χ'(x_i) - χ(x_i)) · f(x_j) · B_n(χ_i, χ_j)   mod p^(k+1)`,

where `B_n` is the degree-one form of the class of `n` in `gr_1(F)` and `χ_i` are the coordinate
`𝔽_p`-characters, the values of `B_n` being lifted from `𝔽_p` to `ℤ_p`. -/
theorem IsCrossedHom.pow_succ_dvd_sub_sub_sum_degreeOneForm [Fintype X]
    {χ χ' : freeProP p X →ₜ* ℤ_[p]ˣ} {k : ℕ}
    (hχ : ∀ x, (p : ℤ_[p]) ^ k ∣ (χ' (of x) : ℤ_[p]) - χ (of x))
    {f f' : freeProP p X → ℤ_[p]} (hf : IsCrossedHom χ f) (hf' : IsCrossedHom χ' f')
    (hfc : Continuous f) (hf'c : Continuous f') (hff' : ∀ x, f (of x) = f' (of x))
    (n : pLowerCentralSeries p (freeProP p X) 1) :
    (p : ℤ_[p]) ^ (k + 1) ∣ f' n - f n - ∑ i, ∑ j, ((χ' (of i) : ℤ_[p]) - χ (of i)) * f (of j) *
      (ZMod.cast (degreeOneForm (gradedMk p (freeProP p X) 1 n) (dualBasis p X i)
        (dualBasis p X j)) : ℤ_[p]) := by
  have hpk : ((p : ℤ_[p]) ^ k) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  -- The characters and the crossed homomorphisms are congruent modulo `p ^ k`; divide by `p ^ k`.
  choose η hη using fun g ↦ freeProP.pow_dvd_sub_of_forall_of hχ g
  choose D hD using fun g ↦ hf.pow_dvd_sub_of_forall_of_eq hχ hf' hfc hf'c hff' g
  -- Multiplication by `p ^ k` is a closed embedding of `ℤ_p`, so the quotients are continuous.
  have hemb : Topology.IsInducing fun y : ℤ_[p] ↦ (p : ℤ_[p]) ^ k * y :=
    ((continuous_const.mul continuous_id).isClosedEmbedding
      (mul_right_injective₀ hpk)).toIsEmbedding.toIsInducing
  have hηc : Continuous η := hemb.continuous_iff.2 (by
    refine ((Units.continuous_val.comp χ'.continuous).sub
      (Units.continuous_val.comp χ.continuous)).congr fun g ↦ ?_
    exact hη g)
  have hDc : Continuous D := hemb.continuous_iff.2 (by
    refine (hf'c.sub hfc).congr fun g ↦ ?_
    exact hD g)
  -- The characters are trivial modulo `p`.
  have hχ1 : ∀ g, PadicInt.toZMod (χ g : ℤ_[p]) = 1 := fun g ↦
    mem_unitsPrincipal_one_iff_toZMod.1 ((isProP_freeProP p X).mem_unitsPrincipal_one χ g)
  have hχ'1 : ∀ g, PadicInt.toZMod (χ' g : ℤ_[p]) = 1 := fun g ↦
    mem_unitsPrincipal_one_iff_toZMod.1 ((isProP_freeProP p X).mem_unitsPrincipal_one χ' g)
  -- The multiplication laws of the quotients.
  have hηmul : ∀ g h, η (g * h) = (χ' g : ℤ_[p]) * η h + η g * χ h := fun g h ↦ by
    refine mul_left_cancel₀ hpk ?_
    have e1 := hη (g * h)
    have e2 := hη g
    have e3 := hη h
    rw [_root_.map_mul, _root_.map_mul, Units.val_mul, Units.val_mul] at e1
    linear_combination -e1 + (χ' g : ℤ_[p]) * e3 + (χ h : ℤ_[p]) * e2
  have hDmul : ∀ g h, D (g * h) = (χ g : ℤ_[p]) * D h + D g + η g * f' h := fun g h ↦ by
    refine mul_left_cancel₀ hpk ?_
    have e1 := hD (g * h)
    have e2 := hD g
    have e3 := hD h
    have e4 := hη g
    rw [hf.map_mul g h, hf'.map_mul g h] at e1
    linear_combination -e1 + (χ g : ℤ_[p]) * e3 + e2 + f' h * e4
  -- The trivial action of `F` on `𝔽_p`, and the two `𝔽_p`-characters.
  let _ : DistribMulAction (freeProP p X) (ZMod p) :=
    DistribMulAction.compHom (ZMod p) (1 : freeProP p X →* (ZMod p)ˣ)
  have htriv : ∀ (g : freeProP p X) (x : ZMod p), g • x = x := fun _ x ↦ one_smul (ZMod p)ˣ x
  let a : Z1 (freeProP p X) (ZMod p) :=
    ⟨fun g ↦ PadicInt.toZMod (η g), mem_Z1_iff.2 ⟨PadicInt.continuous_toZMod.comp hηc,
      fun g h ↦ by
        dsimp only
        rw [htriv, hηmul, map_add, _root_.map_mul, _root_.map_mul, hχ'1, hχ1, one_mul, mul_one]⟩⟩
  let b : Z1 (freeProP p X) (ZMod p) :=
    ⟨fun g ↦ PadicInt.toZMod (f' g), mem_Z1_iff.2 ⟨PadicInt.continuous_toZMod.comp hf'c,
      fun g h ↦ by
        dsimp only
        rw [htriv, hf'.map_mul g h, map_add, _root_.map_mul, hχ'1, one_mul]⟩⟩
  -- `D mod p` is a Heisenberg cochain for `(a, b)`.
  have hh : IsHeisenbergCochain (AddMonoidHom.mul : ZMod p →+ ZMod p →+ ZMod p) a b
      fun g ↦ PadicInt.toZMod (D g) :=
    { continuous := PadicInt.continuous_toZMod.comp hDc
      apply_mul := fun g h ↦ by
        simp only [htriv, AddMonoidHom.mul_apply, a, b]
        rw [hDmul, map_add, map_add, _root_.map_mul, _root_.map_mul, hχ1, one_mul]
        ring }
  have hval := hh.apply_eq_heisenbergFunctional htriv n
  rw [← degreeOneForm_apply] at hval
  -- Expand the two characters in the dual basis of the generators.
  set ρ := gradedMk p (freeProP p X) 1 n
  set ψa := Z1EquivOfSmulEqSelf htriv a
  set ψb := Z1EquivOfSmulEqSelf htriv b
  have hrepr : ∀ (c : Z1 (freeProP p X) (ZMod p)) (i : X),
      (dualBasis p X).repr (Z1EquivOfSmulEqSelf htriv c) i = (c : freeProP p X → ZMod p) (of i) :=
    fun c i ↦ by rw [dualBasis_repr, Z1EquivOfSmulEqSelf_apply, toAdd_ofAdd]
  have hexp : degreeOneForm ρ ψa ψb = ∑ i, ∑ j, PadicInt.toZMod (η (of i)) *
      PadicInt.toZMod (f' (of j)) * degreeOneForm ρ (dualBasis p X i) (dualBasis p X j) := by
    conv_lhs => rw [← (dualBasis p X).sum_repr ψa, ← (dualBasis p X).sum_repr ψb]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum, hrepr, ψa, ψb, a, b]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  -- Assemble: the difference is `p ^ k` times an element divisible by `p`.
  have hsum : f' n - f n - ∑ i, ∑ j, ((χ' (of i) : ℤ_[p]) - χ (of i)) * f (of j) *
      (ZMod.cast (degreeOneForm ρ (dualBasis p X i) (dualBasis p X j)) : ℤ_[p]) =
      (p : ℤ_[p]) ^ k * (D n - ∑ i, ∑ j, η (of i) * f (of j) *
        (ZMod.cast (degreeOneForm ρ (dualBasis p X i) (dualBasis p X j)) : ℤ_[p])) := by
    rw [hD, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hη]
    ring
  rw [hsum, pow_succ]
  refine mul_dvd_mul_left _ ?_
  rw [← PadicInt.toZMod_eq_zero_iff_dvd, map_sub, map_sum, sub_eq_zero, hval, hexp]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [_root_.map_mul, _root_.map_mul, ZMod.ringHom_map_cast, hff']

end TauCeti
