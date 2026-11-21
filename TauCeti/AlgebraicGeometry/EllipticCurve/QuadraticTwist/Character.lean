/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import TauCeti.AlgebraicGeometry.EllipticCurve.QuadraticTwist.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Aut
import TauCeti.AlgebraicGeometry.EllipticCurve.QuadraticTwist.Classification
import TauCeti.FieldTheory.Galois.SqrtCharacter

/-!
# Quadratic twists by a Galois character

Let `K` be a field with `2 ≠ 0`, with absolute Galois group `G_K = Gal(Kᵃˡᵍ/K)`. For a unit `d` of
`K`, the group `G_K` acts on a square root `√d ∈ Kᵃˡᵍ` through a continuous character
`η : G_K → {±1}`, the character of `K(√d)/K` (`TauCeti.sqrtCharacter`). Twisting a Weierstrass
curve `W` by `η` means twisting it by `K(√d)`: the twist by the trace `0` and norm `-d` of `√d`,
which in short Weierstrass form is `y² = x³ + 4d a₂ x² + 16d² a₄ x + 64d³ a₆`.
`WeierstrassCurve.IsQuadraticTwistBy E W η` says that `E` is isomorphic over `K` to this twist,
recording `η` by its action on an actual square root of `d`; it allows the trivial character,
for which the twist is `W` itself (`WeierstrassCurve.isQuadraticTwistBy_one_iff`).

The twisting character is determined by `E` and `W` once `j(W) ∉ {0, 1728}`. Over `Kᵃˡᵍ` the twist
becomes isomorphic to `W` by a change of variables `ρ` whose scaling `u` is multiplied by `η(g)`
under every `g ∈ G_K` (`IsQuadraticTwistBy.exists_smul_baseChange_eq`), so `g ρ = ρ` or
`g ρ = ρ ∘ [-1]` according to the sign of `η(g)`. Two such `ρ` differ by an automorphism of
`W_Kᵃˡᵍ`, which is `±1` and defined over `K`, so they give the same character
(`IsQuadraticTwistBy.unique`). Conversely every elliptic curve with the same `j`-invariant as `W`
is a quadratic twist of `W`
(`WeierstrassCurve.exists_smul_eq_or_exists_smul_eq_quadraticTwist_of_j_eq`), hence a twist by a
unique character (`existsUnique_isQuadraticTwistBy_of_j_eq`).

For a Tate curve `W = E_q` this is the twisting character of the presentation `E ≅ E_q ⊗ η` of a
curve with nonintegral `j`-invariant over a complete nonarchimedean field.

## Main definitions

* `WeierstrassCurve.IsQuadraticTwistBy`: `E` is the quadratic twist of `W` by a character of
  `Gal(Kᵃˡᵍ/K)`.

## Main results

* `WeierstrassCurve.IsQuadraticTwistBy.exists_smul_baseChange_eq`: the Galois action on an
  isomorphism `W_Kᵃˡᵍ ≅ E_Kᵃˡᵍ` is through the twisting character.
* `WeierstrassCurve.IsQuadraticTwistBy.unique`: the twisting character is unique when
  `j(W) ∉ {0, 1728}`.
* `WeierstrassCurve.existsUnique_isQuadraticTwistBy_of_j_eq`: an elliptic curve with the same
  `j`-invariant as `W`, `j(W) ∉ {0, 1728}`, is the twist of `W` by a unique character.
* `WeierstrassCurve.isQuadraticTwistBy_one_iff`: the twist by the trivial character is `W`, up to
  a change of variables over `K`.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, X.2 and X.5.
* B. Mazur, K. Rubin, *Selmer companion curves*, Trans. Amer. Math. Soc. **367** (2015), §2.
-/

public section

namespace WeierstrassCurve

open TauCeti

variable {K : Type*} [Field K]

/-- **`E` is the quadratic twist of `W` by the character `η` of `Gal(Kᵃˡᵍ/K)`**: for a unit `d` of
`K` and a square root `a` of `d` in `Kᵃˡᵍ` on which `Gal(Kᵃˡᵍ/K)` acts through `η`, a change of
variables over `K` carries the twist of `W` by the trace `0` and norm `-d` of `a` to `E`.

The character is recorded by its action on an actual square root, so the trivial character is
allowed, with `d` a square. Away from characteristic two `η` is then the character of `K(√d)/K`
(`TauCeti.eq_sqrtCharacter`), and it is determined by `E` and `W` when `j(W) ∉ {0, 1728}`
(`WeierstrassCurve.IsQuadraticTwistBy.unique`). -/
def IsQuadraticTwistBy (E W : WeierstrassCurve K) (η : Field.absoluteGaloisGroup K →ₜ* ℤˣ) :
    Prop :=
  ∃ (d : Kˣ) (a : AlgebraicClosure K), a ^ 2 = algebraMap K (AlgebraicClosure K) d ∧
    (∀ g : Field.absoluteGaloisGroup K,
      DFunLike.coe (F := Gal(AlgebraicClosure K/K)) g a = (η g : ℤ) • a) ∧
    ∃ C : VariableChange K, C • W.quadraticTwistOf 0 (-d) = E

variable {E W : WeierstrassCurve K} {η η' : Field.absoluteGaloisGroup K →ₜ* ℤˣ}

/-- Unfolding `IsQuadraticTwistBy`: `E` is the twist of `W` by `η` exactly when, for some unit `d`
of `K` and square root `a` of `d` in `Kᵃˡᵍ` on which `Gal(Kᵃˡᵍ/K)` acts through `η`, a change of
variables over `K` carries the twist of `W` by `(0, -d)` to `E`. -/
theorem isQuadraticTwistBy_iff : E.IsQuadraticTwistBy W η ↔
    ∃ (d : Kˣ) (a : AlgebraicClosure K), a ^ 2 = algebraMap K (AlgebraicClosure K) d ∧
      (∀ g : Field.absoluteGaloisGroup K,
        DFunLike.coe (F := Gal(AlgebraicClosure K/K)) g a = (η g : ℤ) • a) ∧
      ∃ C : VariableChange K, C • W.quadraticTwistOf 0 (-d) = E :=
  Iff.rfl

/-- A twist of `W` by `η` stays one under a change of variables over `K`. -/
theorem IsQuadraticTwistBy.smul (C : VariableChange K) (h : E.IsQuadraticTwistBy W η) :
    (C • E).IsQuadraticTwistBy W η := by
  obtain ⟨d, a, ha, hg, C', hC'⟩ := h
  exact ⟨d, a, ha, hg, C * C', by rw [mul_smul, hC']⟩

/-- Being the twist of `W` by `η` is invariant under changes of variables over `K`. -/
@[simp]
theorem isQuadraticTwistBy_smul_iff (C : VariableChange K) :
    (C • E).IsQuadraticTwistBy W η ↔ E.IsQuadraticTwistBy W η :=
  ⟨fun h ↦ by simpa using h.smul C⁻¹, fun h ↦ h.smul C⟩

/-- **The Galois action on the isomorphism of a quadratic twist.** If `E` is the twist of `W` by
`η`, there is a change of variables `ρ` over `Kᵃˡᵍ` carrying `W` to `E` whose scaling factor `u` is
a square root of an element of `K` and is multiplied by `η(g)` under every `g ∈ Gal(Kᵃˡᵍ/K)`. -/
theorem IsQuadraticTwistBy.exists_smul_baseChange_eq (h2 : (2 : K) ≠ 0)
    (h : E.IsQuadraticTwistBy W η) :
    ∃ ρ : VariableChange (AlgebraicClosure K),
      ρ • W.baseChange (AlgebraicClosure K) = E.baseChange (AlgebraicClosure K) ∧
      (∃ c : K, (ρ.u : AlgebraicClosure K) ^ 2 = algebraMap K (AlgebraicClosure K) c) ∧
      ∀ g : Field.absoluteGaloisGroup K,
        DFunLike.coe (F := Gal(AlgebraicClosure K/K)) g (ρ.u : AlgebraicClosure K) =
          (η g : ℤ) • (ρ.u : AlgebraicClosure K) := by
  obtain ⟨d, a, ha, hg, C, hC⟩ := h
  have h2Ω : (2 : AlgebraicClosure K) ≠ 0 := by
    rw [← map_ofNat (algebraMap K (AlgebraicClosure K)) 2]
    exact (map_ne_zero _).mpr h2
  have ha₀ : a ≠ 0 := by
    rintro rfl
    simpa using ha.symm
  have hv : -2 * a ≠ 0 := mul_ne_zero (neg_ne_zero.mpr h2Ω) ha₀
  -- the twist by `(0, -d)` is the split twist by the roots `±a` over `Kᵃˡᵍ`
  set V := (W.baseChange (AlgebraicClosure K)).quadraticTwistOfVariableChange 1 0
    (Units.mk0 _ hv) a
  have hV : V • (W.quadraticTwistOf 0 (-d)).baseChange (AlgebraicClosure K) =
      W.baseChange (AlgebraicClosure K) := by
    have h := (W.baseChange (AlgebraicClosure K)).quadraticTwistOfVariableChange_smul 1 0
      (Units.mk0 _ hv) a
    rw [quadraticTwistOf_one_zero] at h
    rw [baseChange_quadraticTwistOf]
    convert h using 3
    · simp only [map_zero, Units.val_mk0]
      ring
    · simp only [map_neg, Units.val_mk0]
      linear_combination ha
  have hu : (((C.baseChange (AlgebraicClosure K) * V⁻¹).u : (AlgebraicClosure K)ˣ) :
      AlgebraicClosure K) = algebraMap K (AlgebraicClosure K) C.u * (-2 * a)⁻¹ := by
    simp [V, VariableChange.baseChange]
  refine ⟨C.baseChange (AlgebraicClosure K) * V⁻¹, ?_, ⟨C.u ^ 2 / (4 * d), ?_⟩, fun g ↦ ?_⟩
  · rw [mul_smul, ← hV, inv_smul_smul, baseChange_smul_baseChange, hC]
  · rw [hu]
    simp [mul_pow, ha, map_ofNat]
    ring
  · -- work with `g` as an automorphism of `Kᵃˡᵍ`, so that the ring-hom lemmas apply to it
    obtain ⟨σ, rfl⟩ : ∃ σ : Gal(AlgebraicClosure K/K), σ = g := ⟨g, rfl⟩
    rw [hu]
    rcases Int.units_eq_one_or (η σ) with h₁ | h₁ <;> simp [hg σ, h₁, mul_neg, map_ofNat]

/-- **The twisting character is unique** when `j(W) ∉ {0, 1728}`. Two isomorphisms `W_Kᵃˡᵍ ≅ E_Kᵃˡᵍ`
differ by an automorphism of `W_Kᵃˡᵍ`, which is `±1` and defined over `K`, so the Galois group acts
on their scaling factors through the same character. -/
theorem IsQuadraticTwistBy.unique [W.IsElliptic] (h2 : (2 : K) ≠ 0) (hj₀ : W.j ≠ 0)
    (hj₁₇₂₈ : W.j ≠ 1728) (h : E.IsQuadraticTwistBy W η) (h' : E.IsQuadraticTwistBy W η') :
    η = η' := by
  obtain ⟨ρ, hρ, ⟨c, hc⟩, hρg⟩ := h.exists_smul_baseChange_eq h2
  obtain ⟨ρ', hρ', -, hρg'⟩ := h'.exists_smul_baseChange_eq h2
  have hM : (ρ⁻¹ * ρ') • W.baseChange (AlgebraicClosure K) =
      W.baseChange (AlgebraicClosure K) := by
    rw [mul_smul, hρ', ← hρ, inv_smul_smul]
  -- `ρ'` is `ρ` or `ρ ∘ [-1]`, so its scaling factor is `± ρ.u`
  have hu : (ρ'.u : AlgebraicClosure K) = ρ.u ∨ (ρ'.u : AlgebraicClosure K) = -ρ.u := by
    rcases W.eq_one_or_eq_negVariableChange_map
      (FaithfulSMul.algebraMap_injective K (AlgebraicClosure K)) hj₀ hj₁₇₂₈ hM with h₁ | h₁
    · rw [inv_mul_eq_one.mp h₁]
      exact .inl rfl
    · rw [inv_mul_eq_iff_eq_mul.mp h₁, mul_negVariableChange_u, Units.val_neg]
      exact .inr rfl
  -- so `η'` also acts on the square root `ρ.u` of `c`, and both are its character
  have hρg'' : ∀ g : Field.absoluteGaloisGroup K,
      DFunLike.coe (F := Gal(AlgebraicClosure K/K)) g (ρ.u : AlgebraicClosure K) =
        (η' g : ℤ) • (ρ.u : AlgebraicClosure K) := fun g ↦ by
    -- work with `g` as an automorphism of `Kᵃˡᵍ`, so that `map_neg` applies to it
    obtain ⟨σ, rfl⟩ : ∃ σ : Gal(AlgebraicClosure K/K), σ = g := ⟨g, rfl⟩
    have := hρg' σ
    rcases hu with hu | hu
    · rwa [hu] at this
    · rwa [hu, map_neg, smul_neg, neg_inj] at this
  exact (eq_sqrtCharacter hc h2 ρ.u.ne_zero hρg).trans
    (eq_sqrtCharacter hc h2 ρ.u.ne_zero hρg'').symm

/-- **Existence and uniqueness of the twisting character**: an elliptic curve with the same
`j`-invariant as `W`, where `j(W) ∉ {0, 1728}` and `2 ≠ 0`, is the quadratic twist of `W` by
exactly one character of `Gal(Kᵃˡᵍ/K)`. By the classification of twists, `E` is isomorphic over `K`
to `W` or to its twist by a quadratic extension, which away from characteristic two is generated
by a square root; uniqueness is `IsQuadraticTwistBy.unique`. -/
theorem existsUnique_isQuadraticTwistBy_of_j_eq [E.IsElliptic] [W.IsElliptic] (h2 : (2 : K) ≠ 0)
    (hj₀ : W.j ≠ 0) (hj₁₇₂₈ : W.j ≠ 1728) (hj : E.j = W.j) :
    ∃! η, E.IsQuadraticTwistBy W η := by
  -- `E` is a twist of `W` by parameters `(t, n)` of nonzero discriminant
  obtain ⟨t, n, hD, C, hC⟩ : ∃ t n : K, t ^ 2 - 4 * n ≠ 0 ∧
      ∃ C : VariableChange K, C • E = W.quadraticTwistOf t n := by
    rcases W.exists_smul_eq_or_exists_smul_eq_quadraticTwist_of_j_eq (Ω := SeparableClosure K)
      hj₀ hj₁₇₂₈ E hj with ⟨C, hC⟩ | ⟨L, _, C, hC⟩
    · exact ⟨1, 0, by norm_num, C, by rw [quadraticTwistOf_one_zero, hC]⟩
    · obtain ⟨θ, -, hθ⟩ := W.exists_quadraticTwist_eq L
      have hE : (W.quadraticTwistOf (Algebra.trace K L θ) (Algebra.norm K θ)).IsElliptic := by
        rw [← hθ]
        infer_instance
      exact ⟨_, _, ((W.isElliptic_quadraticTwistOf_iff _ _).mp hE).1.ne_zero, C, hC.trans hθ⟩
  -- completing the square moves the twist to parameters `(0, -d)` with `d = (t² - 4n) / 4`
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  obtain ⟨C', hC'⟩ := W.exists_smul_quadraticTwistOf_eq t n (a := 1) (-(t / 2)) isUnit_one
  set d : Kˣ := Units.mk0 ((t ^ 2 - 4 * n) / 4) (div_ne_zero hD h4)
  have hd : W.quadraticTwistOf (1 * t + 2 * -(t / 2)) ((-(t / 2)) ^ 2 + 1 * -(t / 2) * t +
      1 ^ 2 * n) = W.quadraticTwistOf 0 (-d) := by
    congr 1
    · field_simp
      ring
    · simp only [d, Units.val_mk0]
      field_simp
      ring
  rw [hd] at hC'
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) d)
    two_pos
  have hη : E.IsQuadraticTwistBy W (sqrtCharacter ha) :=
    ⟨d, a, ha, apply_eq_sqrtCharacter_smul ha, (C' * C)⁻¹, by
      rw [inv_smul_eq_iff, mul_smul, hC, hC']⟩
  exact ⟨_, hη, fun _ hη' ↦ hη'.unique h2 hj₀ hj₁₇₂₈ hη⟩

/-- **The twist by the trivial character is the curve itself**: away from characteristic two,
`E` is the twist of `W` by the trivial character exactly when a change of variables over `K`
carries `W` to `E`. -/
theorem isQuadraticTwistBy_one_iff (h2 : (2 : K) ≠ 0) :
    E.IsQuadraticTwistBy W 1 ↔ ∃ C : VariableChange K, C • W = E := by
  -- for `x ≠ 0`, the twist by `(0, -x²)` is the split twist by the roots `±x`
  have hsplit (x : K) (hx : x ≠ 0) :
      ∃ C : VariableChange K, C • W = W.quadraticTwistOf 0 (-x ^ 2) := by
    have hx2 : -x - x ≠ 0 := by
      rw [show -x - x = -(2 * x) by ring]
      exact neg_ne_zero.mpr (mul_ne_zero h2 hx)
    obtain ⟨C, hC⟩ := W.exists_smul_eq_quadraticTwistOf_add_mul x (-x) (isUnit_iff_ne_zero.mpr hx2)
    exact ⟨C, hC.trans (by congr 1 <;> ring)⟩
  refine ⟨fun ⟨d, a, ha, hg, C, hC⟩ ↦ ?_, fun ⟨C, hC⟩ ↦ ?_⟩
  · have ha₀ : a ≠ 0 := by
      rintro rfl
      simpa using ha.symm
    have h1 : (1 : Field.absoluteGaloisGroup K →ₜ* ℤˣ) = sqrtCharacter ha :=
      eq_sqrtCharacter ha h2 ha₀ hg
    obtain ⟨x, rfl⟩ := ((sqrtCharacter_eq_one_iff ha h2).mp h1.symm)
    have hd : (d : K) = x ^ 2 :=
      FaithfulSMul.algebraMap_injective K (AlgebraicClosure K) (by rw [map_pow, ha])
    obtain ⟨C₀, hC₀⟩ := hsplit x (by rintro rfl; exact d.ne_zero (by rw [hd]; ring))
    exact ⟨C * C₀, by rw [mul_smul, hC₀, ← hd, hC]⟩
  · obtain ⟨C₀, hC₀⟩ := hsplit 1 one_ne_zero
    refine ⟨1, 1, ?_, fun g ↦ ?_, C * C₀⁻¹, ?_⟩
    · simp
    · rw [ContinuousMonoidHom.coe_one, Pi.one_apply, Units.val_one, one_smul]
      exact map_one (F := Gal(AlgebraicClosure K/K)) g
    · rw [mul_smul, Units.val_one, ← one_pow 2, ← hC₀, inv_smul_smul, hC]

end WeierstrassCurve
