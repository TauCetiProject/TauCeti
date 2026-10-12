/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.LinearAlgebra.CliffordAlgebra.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Filtration

/-!
# The vectors and the scalars inside a Clifford algebra

The generators of a Clifford algebra are the elements `ι Q m`, and the first thing one wants to
know about them is that they are a faithful copy of `M`: that `ι Q` is injective, so that `M` is
*the* module of vectors `LinearMap.range (ι Q)` sitting inside `CliffordAlgebra Q`, and that no
nonzero vector is a scalar.

Mathlib proves all of this for the exterior algebra, which is the Clifford algebra of the zero
form (`ExteriorAlgebra.ι_leftInverse`, `ExteriorAlgebra.ι_inj`,
`ExteriorAlgebra.ι_eq_algebraMap_iff`, `ExteriorAlgebra.ι_range_disjoint_one`), using the
square-zero extension `TrivSqZeroExt R M` as an auxiliary algebra. That trick is unavailable for a
general `Q`: in `TrivSqZeroExt R M` the square of a vector is `0`, so it computes `Q = 0` and
nothing else. What is available instead is Mathlib's module isomorphism
`CliffordAlgebra.equivExterior Q : CliffordAlgebra Q ≃ₗ[R] ExteriorAlgebra R M`, valid whenever
`2` is invertible, which sends generators to generators and scalars to scalars. This file
transports the exterior-algebra statements along it, so all of them hold for an arbitrary
quadratic form over a commutative ring in which `2` is invertible; no hypothesis on `Q` — no
nondegeneracy, no finiteness, no freeness — is needed.

The payoff is `CliffordAlgebra.ιRangeEquiv`, the linear equivalence `M ≃ₗ[R] range (ι Q)`.
It is what turns a statement about elements of `CliffordAlgebra Q` that happen to lie in
`range (ι Q)` into a statement about vectors of `M`: Mathlib's twisted conjugation lemmas
(`lipschitzGroup.conjAct_smul_range_ι`, `spinGroup.involute_act_ι_mem_range_ι`) say only that the
Lipschitz and spin groups act on `range (ι Q)`, and it is `ιRangeEquiv` that transports such an
action to an honest linear automorphism of `M`. Landing in the orthogonal group of `Q` is a
further step: a linear automorphism is not orthogonal for free, and that the transported action
preserves `Q` has to be proved separately.

Against the degree filtration `CliffordAlgebra.filtration`, whose first step is spanned by
the scalars and the vectors, the disjointness of the two pins that step down to `R ⊕ M`:
`CliffordAlgebra.filtrationOneEquiv`.

## Main definitions

* `CliffordAlgebra.ιInv`: the linear left inverse of `ι Q`, the *vector part* of an
  element of the Clifford algebra.
* `CliffordAlgebra.ιRangeEquiv`: the vector equivalence `M ≃ₗ[R] range (ι Q)`.
* `CliffordAlgebra.scalarAddVector` and
  `CliffordAlgebra.filtrationOneEquiv`: the map `(r, m) ↦ r + ι Q m` out of `R × M`, and
  the equivalence with the first step of the degree filtration that it induces.

## Main results

* `CliffordAlgebra.ι_injective`, `CliffordAlgebra.ι_inj` and
  `CliffordAlgebra.ι_eq_zero_iff`: the generators are a faithful copy of `M`.
* `CliffordAlgebra.commute_ι_iff_exists_eq_smul`: two vectors commute exactly when they are
  proportional, once the first has unit value under `Q`.
* `CliffordAlgebra.eq_zero_of_commute_ι_of_isOrtho`: over a field, a vector commuting with two
  orthogonal anisotropic vectors is zero.
* `CliffordAlgebra.eq_zero_or_exists_ι_eq_smul_of_mul_self_eq_algebraMap`: over a field, if a
  vector plus a multiple of a commuting element with nonzero scalar square has scalar square, then
  the multiple vanishes or the vector is a multiple of that element.
* `CliffordAlgebra.mul_ι_notMem_range_ι_of_mul_ι_eq_neg`: over a field, a nonzero element
  anticommuting with two orthogonal anisotropic companions of an anisotropic vector `v` sends
  `ι Q v` outside the vectors.
* `CliffordAlgebra.ι_eq_algebraMap_iff`, `CliffordAlgebra.ι_ne_one` and
  `CliffordAlgebra.ι_range_disjoint_one`: a vector is a scalar only when both vanish.
* `CliffordAlgebra.mem_range_ι_iff`: membership of `range (ι Q)` is detected by the vector
  part.
* `CliffordAlgebra.finrank_filtration_one`: the first step of the degree filtration has one
  more dimension than `M`.

## References

* [Clifford algebras, Pin and Spin, and spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 2, "Vectors from the Clifford algebra".
* N. Bourbaki, *Algebra I, Chapters 1-3* (1989), §9.
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
-/

public section


universe u v

namespace CliffordAlgebra

section CommRing

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M) [Invertible (2 : R)]

/-! ### The comparison with the exterior algebra

Mathlib's `CliffordAlgebra.equivExterior` is only a linear equivalence. Its scalar equation is
recorded in the general Clifford-algebra API; here we record the generator equation needed for
the vector API. Both are immediate from its definition as a `changeForm`. -/

/-- `CliffordAlgebra.equivExterior` sends a generator to the corresponding generator of the
exterior algebra. -/
theorem equivExterior_ι (m : M) : equivExterior Q (ι Q m) = ExteriorAlgebra.ι R m :=
  changeForm_ι changeForm.associated_neg_proof m

/-! ### The vector part -/

/-- The vector part of an element of a Clifford algebra: a linear left inverse of `ι Q`.

This is `ExteriorAlgebra.ιInv` transported along `CliffordAlgebra.equivExterior`, which is where
the hypothesis `[Invertible (2 : R)]` comes from; the square-zero extension that builds
`ExteriorAlgebra.ιInv` directly sees only the zero quadratic form. -/
def ιInv : CliffordAlgebra Q →ₗ[R] M :=
  ExteriorAlgebra.ιInv ∘ₗ (equivExterior Q).toLinearMap

@[simp]
theorem ιInv_ι (m : M) : ιInv Q (ι Q m) = m := by
  rw [ιInv, LinearMap.comp_apply, LinearEquiv.coe_coe, equivExterior_ι,
    ExteriorAlgebra.ι_leftInverse m]

theorem ι_leftInverse : Function.LeftInverse (ιInv Q) (ι Q) := ιInv_ι Q

/-- The vector part of a scalar vanishes.

The exterior-algebra half of the argument is that `ExteriorAlgebra.map 0` fixes scalars while it
kills vector parts (`ExteriorAlgebra.ιInv_comp_map`). -/
@[simp]
theorem ιInv_algebraMap (r : R) : ιInv Q (algebraMap R (CliffordAlgebra Q) r) = 0 := by
  rw [ιInv, LinearMap.comp_apply, LinearEquiv.coe_coe, equivExterior_algebraMap,
    ← (ExteriorAlgebra.map (0 : M →ₗ[R] M)).commutes r, ← AlgHom.toLinearMap_apply,
    ← LinearMap.comp_apply, ExteriorAlgebra.ιInv_comp_map, LinearMap.comp_apply,
    LinearMap.zero_apply]

/-! ### `ι` is injective -/

/-- **The generators of a Clifford algebra are a faithful copy of `M`.** When `2` is invertible
this needs no hypothesis on `Q`. -/
theorem ι_injective : Function.Injective (ι Q) := (ι_leftInverse Q).injective

/-- Two generators are equal exactly when the vectors they come from are. -/
@[simp]
theorem ι_inj (m n : M) : ι Q m = ι Q n ↔ m = n := (ι_injective Q).eq_iff

/-- The only generator that vanishes is the one coming from `0`. -/
@[simp]
theorem ι_eq_zero_iff (m : M) : ι Q m = 0 ↔ m = 0 := by
  rw [← ι_inj Q m 0, map_zero]

/-! ### Commuting vectors are proportional -/

/-- **Two vectors commute in the Clifford algebra exactly when they are proportional**, provided
the first has unit value under `Q`. -/
theorem commute_ι_iff_exists_eq_smul {u w : M} (hu : IsUnit (Q u)) :
    Commute (ι Q u) (ι Q w) ↔ ∃ c : R, w = c • u := by
  constructor
  · intro h
    -- `ι Q u * ι Q w * ι Q u` is the vector `polar Q u w • u - Q u • w` (`ι_mul_ι_mul_ι`); when the
    -- two vectors commute it is also `Q u • w`, and comparing the two expressions solves for `w`.
    obtain ⟨q, hq⟩ := hu
    have h1 : Q u • w = QuadraticMap.polar Q u w • u - Q u • w := by
      apply ι_injective Q
      rw [← ι_mul_ι_mul_ι, h.eq, mul_assoc, ι_sq_scalar, ← Algebra.commutes, ← Algebra.smul_def,
        map_smul]
    have h2 : (2 * Q u) • w = QuadraticMap.polar Q u w • u := by
      rw [mul_smul, two_smul, eq_sub_iff_add_eq.mp h1]
    refine ⟨⅟2 * (q⁻¹ : Rˣ) * QuadraticMap.polar Q u w, ?_⟩
    calc w = (⅟2 * (q⁻¹ : Rˣ) * (2 * Q u)) • w := by
          rw [← hq, mul_mul_mul_comm, invOf_mul_self, Units.inv_mul, one_mul, one_smul]
      _ = (⅟2 * (q⁻¹ : Rˣ) * QuadraticMap.polar Q u w) • u := by
          rw [mul_smul, h2, ← mul_smul]
  · rintro ⟨c, rfl⟩
    rw [map_smul]
    exact (Commute.refl (ι Q u)).smul_right c

/-! ### Vectors are not scalars -/

/-- A generator is a scalar only in the trivial way: both the vector and the scalar vanish. -/
@[simp]
theorem ι_eq_algebraMap_iff (m : M) (r : R) :
    ι Q m = algebraMap R (CliffordAlgebra Q) r ↔ m = 0 ∧ r = 0 := by
  rw [← (equivExterior Q).injective.eq_iff, equivExterior_ι, equivExterior_algebraMap,
    ExteriorAlgebra.ι_eq_algebraMap_iff]

/-- No generator is the unit of a Clifford algebra. -/
@[simp]
theorem ι_ne_one [Nontrivial R] (m : M) : ι Q m ≠ 1 := by
  rw [← map_one (algebraMap R (CliffordAlgebra Q)), Ne, ι_eq_algebraMap_iff]
  exact one_ne_zero ∘ And.right

/-- **The vectors of a Clifford algebra are disjoint from its scalars.** Together with
`TauCeti.Algebra.wordFiltration_one`, which writes the first step of the degree filtration as
`1 ⊔ LinearMap.range (ι Q)`, this is what makes that step a direct sum of `R` and `M`; see
`CliffordAlgebra.filtrationOneEquiv`. -/
theorem ι_range_disjoint_one :
    Disjoint (LinearMap.range (ι Q)) (1 : Submodule R (CliffordAlgebra Q)) := by
  rw [Submodule.disjoint_def]
  rintro _ ⟨m, rfl⟩ hx
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp hx
  rw [eq_comm, ι_eq_algebraMap_iff] at hr
  rw [hr.1, map_zero]

/-! ### The vector equivalence -/

/-- **The vector equivalence**: `M` is the module of vectors `LinearMap.range (ι Q)` inside its
Clifford algebra.

Mathlib's twisted-conjugation lemmas say that the Lipschitz and spin groups act on
`LinearMap.range (ι Q)`; this equivalence is what transports such an action to a linear
automorphism of `M`. It says nothing about `Q`: to place that automorphism in the orthogonal
group one still has to prove that it preserves `Q`. -/
noncomputable def ιRangeEquiv : M ≃ₗ[R] LinearMap.range (ι Q) :=
  LinearEquiv.ofInjective (ι Q) (ι_injective Q)

@[simp]
theorem coe_ιRangeEquiv_apply (m : M) : (ιRangeEquiv Q m : CliffordAlgebra Q) = ι Q m := by
  rw [ιRangeEquiv, LinearEquiv.ofInjective_apply]

@[simp]
theorem ι_ιRangeEquiv_symm_apply (x : LinearMap.range (ι Q)) :
    ι Q ((ιRangeEquiv Q).symm x) = x := by
  rw [← coe_ιRangeEquiv_apply, LinearEquiv.apply_symm_apply]

/-- The vector part reconstructs a vector. -/
theorem ι_ιInv_of_mem {x : CliffordAlgebra Q} (hx : x ∈ LinearMap.range (ι Q)) :
    ι Q (ιInv Q x) = x := by
  obtain ⟨m, rfl⟩ := hx
  rw [ιInv_ι]

/-- Membership of the module of vectors is detected by the vector part. -/
theorem mem_range_ι_iff {x : CliffordAlgebra Q} :
    x ∈ LinearMap.range (ι Q) ↔ ι Q (ιInv Q x) = x :=
  ⟨ι_ιInv_of_mem Q, fun h => ⟨_, h⟩⟩

/-- On a vector, the retraction `ιInv` computes the inverse of the vector equivalence. -/
theorem ιRangeEquiv_symm_apply (x : LinearMap.range (ι Q)) :
    (ιRangeEquiv Q).symm x = ιInv Q x :=
  (ι_injective Q) <| by rw [ι_ιRangeEquiv_symm_apply, ι_ιInv_of_mem Q x.2]

/-! ### The first step of the degree filtration -/

/-- The elements of degree at most one, as a map out of `R × M`: `(r, m) ↦ r + ι Q m`. It is
injective with image `CliffordAlgebra.filtration Q 1`. -/
def scalarAddVector : R × M →ₗ[R] CliffordAlgebra Q :=
  LinearMap.coprod (Algebra.linearMap R (CliffordAlgebra Q)) (ι Q)

omit [Invertible (2 : R)] in
@[simp]
theorem scalarAddVector_apply (x : R × M) :
    scalarAddVector Q x = algebraMap R (CliffordAlgebra Q) x.1 + ι Q x.2 := by
  rw [scalarAddVector, LinearMap.coprod_apply, Algebra.linearMap_apply]

omit [Invertible (2 : R)] in
/-- The scalars and the vectors span exactly the first step of the degree filtration. -/
theorem range_scalarAddVector : LinearMap.range (scalarAddVector Q) = filtration Q 1 := by
  rw [scalarAddVector, LinearMap.range_coprod, ← Submodule.one_eq_range]
  -- The Clifford filtration is the reducible alias of the generic word filtration.
  exact (TauCeti.Algebra.wordFiltration_one (ι Q)).symm

/-- A scalar and a vector summing to zero both vanish, the scalars and the vectors being disjoint
(`CliffordAlgebra.ι_range_disjoint_one`). -/
theorem scalarAddVector_injective : Function.Injective (scalarAddVector Q) := by
  have hd : Disjoint (LinearMap.range (Algebra.linearMap R (CliffordAlgebra Q)))
      (LinearMap.range (ι Q)) := by
    rw [← Submodule.one_eq_range]
    exact (ι_range_disjoint_one Q).symm
  rw [← LinearMap.ker_eq_bot, scalarAddVector, LinearMap.ker_coprod_of_disjoint_range _ _ hd,
    LinearMap.ker_eq_bot.2 (algebraMap_injective Q), LinearMap.ker_eq_bot.2 (ι_injective Q),
    Submodule.prod_bot]

/-- **The first step of the degree filtration is `R ⊕ M`.** The scalars and the vectors span it
(`TauCeti.Algebra.wordFiltration_one`) and meet only in `0`
(`CliffordAlgebra.ι_range_disjoint_one`), so together they parametrize it faithfully. -/
noncomputable def filtrationOneEquiv : (R × M) ≃ₗ[R] filtration Q 1 :=
  (LinearEquiv.ofInjective _ (scalarAddVector_injective Q)).trans
    (LinearEquiv.ofEq _ _ (range_scalarAddVector Q))

@[simp]
theorem coe_filtrationOneEquiv_apply (x : R × M) :
    (filtrationOneEquiv Q x : CliffordAlgebra Q)
      = algebraMap R (CliffordAlgebra Q) x.1 + ι Q x.2 := by
  rw [filtrationOneEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    LinearEquiv.ofInjective_apply, scalarAddVector_apply]

end CommRing

section Field

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  (Q : QuadraticForm K V) [Invertible (2 : K)]

/-- Counting dimensions in `CliffordAlgebra.filtrationOneEquiv`: the first step of the
degree filtration is one dimension bigger than the space of vectors. -/
theorem finrank_filtration_one [FiniteDimensional K V] :
    Module.finrank K (filtration Q 1) = Module.finrank K V + 1 := by
  rw [← (filtrationOneEquiv Q).finrank_eq, Module.finrank_prod, Module.finrank_self,
    Nat.add_comm]

/-! ### A vector commuting with two orthogonal anisotropic vectors is zero -/

variable {Q} in
/-- **A vector commuting with two orthogonal anisotropic vectors is zero.** Commuting with an
anisotropic `u` makes `w` proportional to `u` (`commute_ι_iff_exists_eq_smul`), so `w` is
proportional to both `u₁` and `u₂`, and pairing with `u₁` gives `2 c₁ Q u₁ = polar Q u₁ w = 0`. -/
theorem eq_zero_of_commute_ι_of_isOrtho {u₁ u₂ w : V} (hu₁ : Q u₁ ≠ 0) (hu₂ : Q u₂ ≠ 0)
    (hu₁u₂ : Q.IsOrtho u₁ u₂) (h₁ : Commute (ι Q u₁) (ι Q w)) (h₂ : Commute (ι Q u₂) (ι Q w)) :
    w = 0 := by
  obtain ⟨c₁, hc₁⟩ := (commute_ι_iff_exists_eq_smul Q (isUnit_iff_ne_zero.mpr hu₁)).mp h₁
  obtain ⟨c₂, hc₂⟩ := (commute_ι_iff_exists_eq_smul Q (isUnit_iff_ne_zero.mpr hu₂)).mp h₂
  -- Pairing `w` with `u₁` in the two expressions gives `2 c₁ Q u₁ = polar Q u₁ w = 0`.
  have hpolar₁ : QuadraticMap.polar Q u₁ w = c₁ * (2 * Q u₁) := by
    rw [hc₁, QuadraticMap.polar_smul_right, QuadraticMap.polar_self, two_nsmul, smul_eq_mul,
      two_mul]
  have hpolar₂ : QuadraticMap.polar Q u₁ w = 0 := by
    rw [hc₂, QuadraticMap.polar_smul_right, hu₁u₂.polar_eq_zero, smul_zero]
  have hc₁0 : c₁ = 0 := by
    rcases mul_eq_zero.mp (hpolar₁.symm.trans hpolar₂) with h | h
    · exact h
    · exact absurd h (mul_ne_zero (Invertible.ne_zero (2 : K)) hu₁)
  rw [hc₁, hc₁0, zero_smul]

/-! ### A vector plus a commuting element with scalar square -/

variable {Q} in
/-- **A vector plus a multiple of a commuting element with nonzero scalar square has scalar square
only if the multiple vanishes or the vector is itself a multiple of that element.** Let `ω` commute
with `ι Q w` and have `ω * ω` the nonzero scalar `s`. If `(ι Q w + c • ω) ^ 2` is a scalar, then
either `c = 0` or `ι Q w` is a multiple of `ω`: the cross term `2 c • (ω * ι Q w)` is a scalar, and
multiplying it by `ω` once more isolates `ι Q w`. Only commutation with the single vector `ι Q w`
is needed; a central `ω` (such as a volume element in odd dimension) supplies it. -/
theorem eq_zero_or_exists_ι_eq_smul_of_mul_self_eq_algebraMap {ω : CliffordAlgebra Q} {w : V}
    (hω : Commute ω (ι Q w)) {s : K} (hsq : ω * ω = algebraMap K _ s) (hs : s ≠ 0)
    {c q : K} (h : (ι Q w + c • ω) * (ι Q w + c • ω) = algebraMap K _ q) :
    c = 0 ∨ ∃ t : K, ι Q w = t • ω := by
  have hwω : ι Q w * ω = ω * ι Q w := hω.symm.eq
  have hexp : (2 * c) • (ω * ι Q w) = algebraMap K _ (q - Q w - c * c * s) := by
    have hsq' : (ι Q w + c • ω) * (ι Q w + c • ω) =
        algebraMap K _ (Q w) + (2 * c) • (ω * ι Q w) + algebraMap K _ (c * c * s) := by
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, ι_sq_scalar, hwω, hsq,
        smul_smul, Algebra.algebraMap_eq_smul_one]
      module
    rw [map_sub, map_sub, ← h, hsq']
    abel
  by_cases hc : c = 0
  · exact Or.inl hc
  · right
    have h2c : (2 * c) ≠ 0 := mul_ne_zero (Invertible.ne_zero 2) hc
    have hωw : ω * ι Q w = algebraMap K _ ((2 * c)⁻¹ * (q - Q w - c * c * s)) := by
      rw [map_mul, ← Algebra.smul_def, ← hexp, smul_smul, inv_mul_cancel₀ h2c, one_smul]
    refine ⟨s⁻¹ * ((2 * c)⁻¹ * (q - Q w - c * c * s)), ?_⟩
    -- Multiply by `ω` on the left: `s • ι Q w = r • ω`.
    have hmul : ω * (ω * ι Q w) = ω * algebraMap K _ ((2 * c)⁻¹ * (q - Q w - c * c * s)) := by
      rw [hωw]
    rw [← mul_assoc, hsq, ← Algebra.smul_def, ← Algebra.commutes, ← Algebra.smul_def] at hmul
    rw [mul_smul, ← hmul, smul_smul, inv_mul_cancel₀ hs, one_smul]

/-! ### An anticommuting element moves an anisotropic vector out of the vectors -/

variable {Q} in
/-- **A nonzero element anticommuting with two orthogonal anisotropic companions of an anisotropic
vector `v` sends `ι Q v` outside the vectors.** Only the two anticommutation relations are
required of `ω`; the volume element of an orthogonal list of even length containing `u₁` and `u₂`
satisfies them. -/
theorem mul_ι_notMem_range_ι_of_mul_ι_eq_neg {ω : CliffordAlgebra Q} (hω : ω ≠ 0) {v u₁ u₂ : V}
    (hv : Q v ≠ 0) (hu₁ : Q u₁ ≠ 0) (hu₂ : Q u₂ ≠ 0) (hvu₁ : Q.IsOrtho v u₁)
    (hvu₂ : Q.IsOrtho v u₂) (hu₁u₂ : Q.IsOrtho u₁ u₂) (h₁ : ω * ι Q u₁ = -(ι Q u₁ * ω))
    (h₂ : ω * ι Q u₂ = -(ι Q u₂ * ω)) : ω * ι Q v ∉ LinearMap.range (ι Q) := by
  -- If `ω * ι Q v` were a vector `ι Q w`, each companion `u` would commute with it, since `u`
  -- anticommutes with both `ω` and `ι Q v`; two orthogonal anisotropic companions then force
  -- `w = 0` (`eq_zero_of_commute_ι_of_isOrtho`), and `ω * ι Q v * ι Q v = Q v • ω` forces `ω = 0`.
  rintro ⟨w, hw⟩
  -- A companion `u` of `v` commutes with `ω * ι Q v`.
  have key : ∀ u : V, Q.IsOrtho v u → ω * ι Q u = -(ι Q u * ω) → Commute (ι Q u) (ι Q w) := by
    intro u huv hωu
    have hvu : ι Q u * ι Q v = -(ι Q v * ι Q u) := ι_mul_ι_comm_of_isOrtho huv.symm
    have huω : ι Q u * ω = -(ω * ι Q u) := by rw [hωu, neg_neg]
    have : ι Q u * (ω * ι Q v) = ω * ι Q v * ι Q u := by
      calc ι Q u * (ω * ι Q v) = -(ω * ι Q u) * ι Q v := by rw [← mul_assoc, huω]
        _ = -(ω * (ι Q u * ι Q v)) := by rw [neg_mul, mul_assoc]
        _ = ω * ι Q v * ι Q u := by rw [hvu, mul_neg, neg_neg, mul_assoc]
    rw [hw]
    exact this
  have hw0 : w = 0 :=
    eq_zero_of_commute_ι_of_isOrtho hu₁ hu₂ hu₁u₂ (key u₁ hvu₁ h₁) (key u₂ hvu₂ h₂)
  -- So `ω * ι Q v = 0`; multiplying by `ι Q v` once more gives `Q v • ω = 0`.
  have hωv : ω * ι Q v = 0 := by rw [← hw, hw0, map_zero]
  have hQω : Q v • ω = 0 := by
    rw [Algebra.smul_def, Algebra.commutes, ← ι_sq_scalar, ← mul_assoc, hωv, zero_mul]
  exact hω ((smul_eq_zero.mp hQω).resolve_left hv)

end Field

end CliffordAlgebra
