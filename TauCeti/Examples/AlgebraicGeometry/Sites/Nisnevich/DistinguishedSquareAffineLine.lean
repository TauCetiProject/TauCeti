/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.StandardEtale
public import TauCeti.AlgebraicGeometry.Sites.Nisnevich.DistinguishedSquare.Pointwise
import TauCeti.AlgebraicGeometry.ResidueField

/-!
# Example: an elementary distinguished square over the affine line

Let `X = 𝔸¹_ℚ = Spec ℚ[t]`, `U = 𝔸¹ ∖ {0} = Spec ℚ[t, t⁻¹]` and `V = 𝔸¹ ∖ {−1, −2}` with
coordinate `s`, mapping to `X` by `p(s) = s² + 2s`. Then `p` is étale, since
`p'(s) = 2(s + 1)` is invertible on `V`, and the only point of `V` over the origin is `s = 0`, with
residue field `ℚ`: the other root `s = −2` of `s² + 2s` is removed. So `(U ⊂ X, p)` is an
elementary distinguished square (`affineLineSquare`), by the pointwise criterion
`TauCeti.AlgebraicGeometry.Scheme.ElementaryDistinguishedSquare.ofPointwise`.

`V` is written as the standard étale `ℚ[t]`-algebra `ℚ[t][s][1/g]/(f)` of the pair
`f = s² + 2s − t`, `g = 2(s + 1)(s + 2)` (`pair`); eliminating `t = s² + 2s`, this is
`ℚ[s][1/((s + 1)(s + 2))]`.

## Main declarations

* `TauCeti.AlgebraicGeometry.DistinguishedSquareAffineLineExample.affineLineSquare`: the elementary
  distinguished square over `𝔸¹_ℚ`.
* `TauCeti.AlgebraicGeometry.DistinguishedSquareAffineLineExample.existsUnique_p_eq`: exactly one
  point of `V` lies over each point outside `U`.
* `TauCeti.AlgebraicGeometry.DistinguishedSquareAffineLineExample.isIso_residueFieldMap_p`: `p`
  induces an isomorphism of residue fields at it.
-/

public section

open CategoryTheory AlgebraicGeometry Polynomial

namespace TauCeti.AlgebraicGeometry.DistinguishedSquareAffineLineExample

open TauCeti.AlgebraicGeometry.Scheme

/-- The coordinate `t` of the base `𝔸¹_ℚ = Spec ℚ[t]`. -/
noncomputable abbrev t : ℚ[X] := X

/-- The standard étale pair `f = s² + 2s − t`, `g = 2(s + 1)(s + 2)` over `ℚ[t]`: its algebra is
the coordinate ring of `V = 𝔸¹ ∖ {−1, −2}`, mapping to `𝔸¹` by `s ↦ s² + 2s`. -/
@[expose]
noncomputable def pair : StandardEtalePair ℚ[X] where
  f := X ^ 2 + (2 * X - C t)
  monic_f := monic_X_pow_add (by compute_degree!)
  g := 2 * (X + 1) * (X + 2)
  cond := ⟨X + 2, 0, 1, by
    simp only [derivative_add, derivative_sub, derivative_X_pow, derivative_mul, derivative_ofNat,
      derivative_X, derivative_C, mul_zero, add_zero, pow_one, zero_mul, sub_zero, Nat.cast_ofNat,
      map_ofNat]
    ring⟩

/-- The monic polynomial of `pair`. -/
theorem pair_f : pair.f = X ^ 2 + (2 * X - C t) :=
  rfl

/-- The localizing polynomial of `pair`. -/
theorem pair_g : pair.g = 2 * (X + 1) * (X + 2) :=
  rfl

/-- The base `X = 𝔸¹_ℚ`. -/
noncomputable abbrev base : Scheme := Spec (.of ℚ[X])

/-- The open immersion `j : 𝔸¹ ∖ {0} ⟶ 𝔸¹`. -/
noncomputable abbrev j : Spec (.of (Localization.Away t)) ⟶ base :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ[X] (Localization.Away t)))

/-- The étale morphism `p : 𝔸¹ ∖ {−1, −2} ⟶ 𝔸¹`, `s ↦ s² + 2s`. -/
noncomputable abbrev p : Spec (.of pair.Ring) ⟶ base :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ[X] pair.Ring))

/-- `p` is étale: `ℚ[t][s][1/g]/(f)` is a standard étale `ℚ[t]`-algebra. -/
instance etale_p : Etale p := by
  rw [HasRingHomProperty.Spec_iff (P := @Etale)]
  exact RingHom.etale_algebraMap.mpr inferInstance

/-- In the algebra of `pair`, `t = s (s + 2)`. -/
theorem algebraMap_t : algebraMap ℚ[X] pair.Ring t = pair.X * (pair.X + 2) := by
  have h := pair.hasMap_X.1
  rw [pair_f] at h
  simp only [map_add, map_sub, map_pow, map_mul, aeval_X, aeval_C, map_ofNat] at h
  linear_combination -h

/-- `s + 2` is a unit in the algebra of `pair`. -/
theorem isUnit_X_add_two : IsUnit (pair.X + 2) := by
  have h := pair.hasMap_X.2
  rw [pair_g] at h
  simp only [map_add, map_mul, aeval_X, map_one, map_ofNat] at h
  exact isUnit_of_mul_isUnit_right h

/-- `s = 0` is a point of `V` over `t = 0`: `f(0) = −t` vanishes at `t = 0`, and `g(0) = 4`. -/
theorem hasMap_zero :
    letI : Algebra ℚ[X] ℚ := (evalRingHom 0).toAlgebra
    pair.HasMap (0 : ℚ) := by
  let _ : Algebra ℚ[X] ℚ := (evalRingHom 0).toAlgebra
  refine ⟨?_, ?_⟩
  · rw [pair_f]
    simp only [map_add, map_sub, map_pow, map_mul, aeval_X, aeval_C, map_ofNat]
    change (0 : ℚ) ^ 2 + (2 * 0 - eval 0 X) = 0
    simp
  rw [pair_g]
  simp only [map_add, map_mul, aeval_X, map_one, map_ofNat]
  norm_num

/-- The point `s = 0` of `V`, as the ring map `ℚ[t][s][1/g]/(f) → ℚ`, `s ↦ 0` (so `t ↦ 0`). -/
@[expose]
noncomputable def evalZero : pair.Ring →+* ℚ :=
  letI : Algebra ℚ[X] ℚ := (evalRingHom 0).toAlgebra
  (pair.lift (0 : ℚ) hasMap_zero).toRingHom

/-- `evalZero` restricted to `ℚ[t]` is evaluation at `t = 0`. -/
theorem evalZero_algebraMap (q : ℚ[X]) : evalZero (algebraMap ℚ[X] pair.Ring q) = q.eval 0 := by
  let _ : Algebra ℚ[X] ℚ := (evalRingHom 0).toAlgebra
  exact (pair.lift (0 : ℚ) hasMap_zero).commutes q

/-- `evalZero` sends `s` to `0`. -/
theorem evalZero_X : evalZero pair.X = 0 := by
  let _ : Algebra ℚ[X] ℚ := (evalRingHom 0).toAlgebra
  exact pair.lift_X (0 : ℚ) hasMap_zero

/-- `evalZero` is surjective, through the constants of `ℚ[t]`. -/
theorem evalZero_surjective : Function.Surjective evalZero :=
  fun c ↦ ⟨algebraMap ℚ[X] pair.Ring (C c), by rw [evalZero_algebraMap, eval_C]⟩

/-- Modulo a prime containing `t`, every element of `ℚ[t][s][1/g]/(f)` is congruent to the image
of its value at `s = 0`. -/
theorem sub_mem_of_t_mem (v : Ideal pair.Ring) [v.IsPrime]
    (hv : algebraMap ℚ[X] pair.Ring t ∈ v) (a : pair.Ring) :
    a - algebraMap ℚ[X] pair.Ring (C (evalZero a)) ∈ v := by
  -- `s ∈ v`: `t = s (s + 2)` with `s + 2` a unit.
  have hX : pair.X ∈ v := by
    rw [algebraMap_t] at hv
    exact (‹v.IsPrime›.mem_or_mem hv).resolve_right fun h ↦
      ‹v.IsPrime›.ne_top (v.eq_top_of_isUnit_mem h isUnit_X_add_two)
  -- Every `q : ℚ[t]` is congruent to `q(0)` modulo `t`.
  have hC (q : ℚ[X]) : algebraMap ℚ[X] pair.Ring q - algebraMap ℚ[X] pair.Ring (C (q.eval 0)) ∈ v
      := by
    obtain ⟨r, hr⟩ := X_dvd_sub_C (p := q)
    rw [← map_sub, ← coeff_zero_eq_eval_zero, hr, map_mul]
    exact v.mul_mem_right _ hv
  let _ : Algebra ℚ[X] ℚ := (evalRingHom 0).toAlgebra
  -- The two `ℚ[t]`-algebra maps to `ℚ[t][s][1/g]/(f) ⧸ v` agreeing on `s` coincide.
  let ψ : ℚ →ₐ[ℚ[X]] pair.Ring ⧸ v :=
    { toRingHom := (Ideal.Quotient.mk v).comp ((algebraMap ℚ[X] pair.Ring).comp C)
      commutes' q := by
        simp only [RingHom.algebraMap_toAlgebra, coe_evalRingHom]
        exact Ideal.Quotient.eq.mpr (by simpa using v.neg_mem_iff.mpr (hC q)) }
  have key : ψ.comp (pair.lift (0 : ℚ) hasMap_zero) = Ideal.Quotient.mkₐ ℚ[X] v := by
    refine pair.hom_ext ?_
    simp only [AlgHom.comp_apply, pair.lift_X, Ideal.Quotient.mkₐ_eq_mk]
    rw [eq_comm, Ideal.Quotient.eq_zero_iff_mem.mpr hX]
    exact (map_zero ψ).symm
  have := congrArg (· a) key
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
  exact Ideal.Quotient.eq.mp (this.symm.trans rfl)

/-- The point `s = 0` of `V`. -/
@[expose]
noncomputable def zeroPoint : Spec (.of pair.Ring) :=
  ⟨RingHom.ker evalZero, RingHom.ker_isPrime _⟩

/-- The point `s = 0` is closed. -/
theorem zeroPoint_isMaximal : zeroPoint.asIdeal.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ evalZero_surjective

/-- A prime of `ℚ[t]` containing `t` is `(t)`. -/
theorem eq_span_t (x : base) (hx : t ∈ x.asIdeal) : x.asIdeal = Ideal.span {t} :=
  (PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X (R := ℚ))).eq_of_le
    x.isPrime.ne_top (Ideal.span_le.mpr (by simpa using hx)) |>.symm

/-- The points outside `U` are those whose prime contains `t`. -/
theorem mem_range_j_iff (x : base) : x ∈ Set.range j ↔ t ∉ x.asIdeal := by
  change x ∈ Set.range (PrimeSpectrum.comap (algebraMap ℚ[X] (Localization.Away t))) ↔ _
  rw [PrimeSpectrum.localization_away_comap_range (Localization.Away t) t]
  rfl

/-- The point of `V` over a prime `x` is the prime pulled back to `ℚ[t]`. -/
theorem p_apply (v : Spec (.of pair.Ring)) :
    (p v).asIdeal = v.asIdeal.comap (algebraMap ℚ[X] pair.Ring) :=
  rfl

/-- A point of `V` over a point outside `U` is `s = 0`. -/
theorem eq_zeroPoint (v : Spec (.of pair.Ring)) (hv : t ∈ (p v).asIdeal) : v = zeroPoint := by
  rw [p_apply, Ideal.mem_comap] at hv
  have := v.isPrime
  refine PrimeSpectrum.ext (zeroPoint_isMaximal.eq_of_le v.isPrime.ne_top fun a ha ↦ ?_).symm
  have := sub_mem_of_t_mem v.asIdeal hv a
  rwa [show evalZero a = 0 from ha, map_zero, map_zero, sub_zero] at this

/-- The point `s = 0` lies over the origin `t = 0`. -/
theorem t_mem_p_zeroPoint : t ∈ (p zeroPoint).asIdeal := by
  rw [p_apply, Ideal.mem_comap]
  change evalZero _ = 0
  rw [evalZero_algebraMap, eval_X]

/-- **Exactly one point of `V` lies over each point outside `U`**: the origin has the single
preimage `s = 0`, the root `s = −2` of `s² + 2s` being removed from `V`. -/
theorem existsUnique_p_eq (x : base) (hx : x ∉ Set.range j) : ∃! v, p v = x := by
  rw [mem_range_j_iff, not_not] at hx
  refine ⟨zeroPoint, PrimeSpectrum.ext ?_, fun v hv ↦ eq_zeroPoint v (hv ▸ hx)⟩
  rw [eq_span_t x hx]
  exact eq_span_t _ t_mem_p_zeroPoint

/-- **`p` induces an isomorphism of residue fields over the complement of `U`**: at `s = 0` the
residue field is `ℚ`, the residue field of the origin. -/
theorem isIso_residueFieldMap_p (v : Spec (.of pair.Ring)) (hv : p v ∉ Set.range j) :
    IsIso (p.residueFieldMap v) := by
  rw [mem_range_j_iff, not_not] at hv
  obtain rfl := eq_zeroPoint v hv
  have := zeroPoint_isMaximal
  rw [RingHom.isIso_SpecMap_residueFieldMap_iff _ _ _ rfl]
  refine ⟨RingHom.injective _, fun z ↦ ?_⟩
  obtain ⟨z, rfl⟩ := zeroPoint.asIdeal.bijective_algebraMap_quotient_residueField.surjective z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨algebraMap ℚ[X] _ (C (evalZero a)), ?_⟩
  rw [Ideal.ResidueField.map_algebraMap, IsScalarTower.algebraMap_apply pair.Ring
    (pair.Ring ⧸ zeroPoint.asIdeal) zeroPoint.asIdeal.ResidueField, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq.mpr (sub_mem_of_t_mem _ t_mem_p_zeroPoint a)]

/-- **The square of the affine line.** `X = 𝔸¹_ℚ`, `U = 𝔸¹ ∖ {0}`, `V = 𝔸¹ ∖ {−1, −2}` with
`p(s) = s² + 2s` form an elementary distinguished square. -/
noncomputable def affineLineSquare : ElementaryDistinguishedSquare base :=
  ElementaryDistinguishedSquare.ofPointwise j p existsUnique_p_eq isIso_residueFieldMap_p

end TauCeti.AlgebraicGeometry.DistinguishedSquareAffineLineExample
