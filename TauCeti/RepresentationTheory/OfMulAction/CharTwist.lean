/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Character.Twist
public import TauCeti.RepresentationTheory.OfMulAction

/-!
# Invariants of permutation representations twisted by a character

Let a group `Γ` act on a type `X`, and let `χ : Γ →* kˣ` be a linear character. Twisting the
permutation representation `k[X]` by `χ` (`Representation.charTwist`) gives the representation
in which `g` sends the basis vector at `x` to `χ g` times the basis vector at `g • x`. It is the
tensor product of `k[X]` with the one-dimensional representation of `χ`
(`Representation.tprodEquivCharTwist`). Singular chains with coefficients in a rank-one sign
representation, such as an orientation line on which a finite isotropy group acts through the sign
of a determinant, are representations of this form: `X` is a set of singular simplices permuted by
the group, and `χ` is the sign character read in `k`.

This file describes the invariants of these twisted permutation representations. A vector is
invariant exactly when its coefficients satisfy `v (g • x) = χ g * v x`
(`TauCeti.mem_invariants_charTwist_ofMulAction_iff`). At a point `x` whose stabilizer contains an
element `h` with `χ h ≠ 1`, this forces `(χ h - 1) * v x = 0`, so an invariant vanishes there as
soon as `χ h - 1` is a non-zero-divisor (`TauCeti.coeff_eq_zero_of_mem_invariants_charTwist`);
for a sign character this is the condition that `2` is a non-zero-divisor in `k`. On the other
hand, if `χ` is trivial on the stabilizer of `x`, the coefficients `χ g` at the points `g • x`
are well defined, and when `Γ` is finite they form an invariant vector, the twisted orbit sum
(`TauCeti.twistedOrbitSum`, defined to be `0` at the other points). Whether `χ` is trivial on
stabilizers depends only on the orbit, since stabilizers along an orbit are conjugate and `χ`
takes values in a commutative group.

The main result is the orbit basis (`TauCeti.twistedInvariantOrbitSumBasis`): for a finite
group, and when `χ g - 1` is a non-zero-divisor whenever `χ g ≠ 1`, the invariants of the twisted
permutation representation are free, with basis the twisted orbit sums of the orbits on which `χ`
is trivial on stabilizers (`TauCeti.charTrivialOrbits`). The set `X` need not be finite, which is
the case of singular chains. Each orbit contributes a copy of `k` if `χ` is trivial on its
stabilizers and nothing otherwise. Over a field, the dimension of the invariants is the number of
those orbits (`TauCeti.finrank_invariants_charTwist_ofMulAction`).

For the trivial character every orbit counts, and the basis vector of an orbit is the indicator of
the orbit, as in `TauCeti.invariantOrbitSumBasis`. For the sign character of `ℤ/2` acting on two
points by exchanging them, the invariants are spanned by the difference of the two basis vectors;
for `ℤ/2` acting trivially on one point with the sign character, they are zero.

## Main definitions

* `TauCeti.charTrivialOrbits`: the orbits of `X` on which `χ` is trivial on stabilizers.
* `TauCeti.twistedOrbitSum`: the vector with coefficient `χ g` at `g • x` and `0` off the orbit of
  `x`.
* `TauCeti.charTwistOrbitVector`: the twisted orbit sum at the representative of an orbit, as an
  invariant vector.
* `TauCeti.twistedInvariantOrbitSumBasis`: the basis of twisted orbit sums of the invariants.

## Main results

* `TauCeti.mem_invariants_charTwist_ofMulAction_iff`: the coefficient description of invariants.
* `TauCeti.coeff_eq_zero_of_mem_invariants_charTwist`: invariants vanish at points whose
  stabilizer meets `χ` nontrivially.
* `TauCeti.stabilizer_smul_le_ker_iff`: whether `χ` is trivial on stabilizers depends only on the
  orbit.
* `TauCeti.twistedOrbitSum_mem_invariants`: twisted orbit sums are invariant.
* `TauCeti.twistedInvariantOrbitSumBasis_repr_apply`: the coordinate of an invariant at an orbit
  is its coefficient at the chosen representative.
* `TauCeti.finrank_invariants_charTwist_ofMulAction`: over a field, the dimension of the
  invariants is the number of orbits on which `χ` is trivial on stabilizers.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), Section 4.2, where the virtual chain
  complexes are the invariants of the isotropy groups on singular chains with coefficients in a
  dual orientation line.
-/

public section

open MonoidAlgebra MulAction Module Representation

namespace TauCeti

variable {k Γ X : Type*} [CommRing k] [Group Γ] [MulAction Γ X] (χ : Γ →* kˣ)

/-! ### The coefficient description of invariants -/

/-- The coefficient of the twisted permutation action at `y` is `χ g` times the coefficient at
`g⁻¹ • y`. -/
theorem coeff_charTwist_ofMulAction (g : Γ) (v : k[X]) (y : X) :
    (charTwist χ (ofMulAction k Γ X) g v).coeff y = χ g * v.coeff (g⁻¹ • y) := by
  simp

/-- **Invariants of a twisted permutation representation.** A vector of `k[X]` is invariant
under the permutation representation twisted by `χ` exactly when its coefficients satisfy
`v (g • x) = χ g * v x`. -/
theorem mem_invariants_charTwist_ofMulAction_iff {v : k[X]} :
    v ∈ (charTwist χ (ofMulAction k Γ X)).invariants ↔
      ∀ (g : Γ) (x : X), v.coeff (g • x) = χ g * v.coeff x := by
  refine ⟨fun hv g x ↦ ?_, fun hv g ↦ ?_⟩
  · simpa using (congrArg (fun w : k[X] ↦ w.coeff (g • x)) (hv g)).symm
  · ext y
    rw [coeff_charTwist_ofMulAction, ← hv, smul_inv_smul]

/-- An invariant of the twisted permutation representation vanishes at a point `x` whose
stabilizer contains an element `h` for which `χ h - 1` is a non-zero-divisor: invariance under
`h` gives `(χ h - 1) * v x = 0`. -/
theorem coeff_eq_zero_of_mem_invariants_charTwist {v : k[X]}
    (hv : v ∈ (charTwist χ (ofMulAction k Γ X)).invariants) {x : X} {h : Γ}
    (hh : h ∈ stabilizer Γ x) (hreg : IsLeftRegular ((χ h : k) - 1)) : v.coeff x = 0 := by
  have hx := (mem_invariants_charTwist_ofMulAction_iff χ).1 hv h x
  rw [mem_stabilizer_iff.1 hh] at hx
  refine hreg ?_
  simp only [mul_zero]
  linear_combination -hx

/-- When `k` has no zero divisors, `χ g - 1` is a non-zero-divisor whenever `χ g ≠ 1`. -/
theorem isLeftRegular_sub_one_of_ne_one [NoZeroDivisors k] {g : Γ} (hg : χ g ≠ 1) :
    IsLeftRegular ((χ g : k) - 1) :=
  IsLeftCancelMulZero.mul_left_cancel_of_ne_zero (sub_ne_zero.2 fun h ↦ hg (Units.val_eq_one.1 h))

/-! ### Orbits on which the character is trivial on stabilizers -/

variable {χ} in
/-- Whether `χ` is trivial on the stabilizer of a point depends only on its orbit: the
stabilizers along an orbit are conjugate, and `χ` takes values in a commutative group. -/
theorem stabilizer_smul_le_ker_iff {g : Γ} {x : X} :
    stabilizer Γ (g • x) ≤ χ.ker ↔ stabilizer Γ x ≤ χ.ker := by
  conv_lhs => rw [stabilizer_smul_eq_stabilizer_map_conj, ← Subgroup.Normal.map_conj_eq χ.ker g]
  exact Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective

variable (X) in
/-- The orbits of `X` on which `χ` is trivial on stabilizers: those on which the twisted orbit
sums are defined. Each of them contributes one basis vector to the invariants of the twisted
permutation representation. -/
def charTrivialOrbits : Set (orbitRel.Quotient Γ X) :=
  {ω | ∀ x : X, (Quotient.mk'' x : orbitRel.Quotient Γ X) = ω → stabilizer Γ x ≤ χ.ker}

variable {χ} in
/-- An orbit lies in `charTrivialOrbits` exactly when `χ` is trivial on the stabilizer of one,
equivalently every, of its points. -/
@[simp]
theorem mk_mem_charTrivialOrbits_iff {x : X} :
    (Quotient.mk'' x : orbitRel.Quotient Γ X) ∈ charTrivialOrbits X χ ↔
      stabilizer Γ x ≤ χ.ker := by
  refine ⟨fun h ↦ h x rfl, fun h y hy ↦ ?_⟩
  obtain ⟨g, rfl⟩ := mem_orbit_iff.1 (orbitRel_apply.1 (Quotient.exact' hy))
  exact stabilizer_smul_le_ker_iff.2 h

/-! ### Twisted orbit sums -/

variable [Finite Γ]

/-- The twisted orbit sum at `x`. When `χ` is trivial on the stabilizer of `x`, it is the vector
of `k[X]` with coefficient `χ g` at `g • x` and `0` off the orbit of `x`
(`TauCeti.coeff_twistedOrbitSum_smul`, `TauCeti.coeff_twistedOrbitSum_of_notMem`). Otherwise there
is no such vector, and it is `0` (`TauCeti.twistedOrbitSum_of_not_le`). -/
noncomputable def twistedOrbitSum (x : X) : k[X] :=
  open scoped Classical in
  ofCoeff <| Finsupp.ofSupportFinite
    (fun y ↦ if h : stabilizer Γ x ≤ χ.ker ∧ ∃ g : Γ, g • x = y then (χ h.2.choose : k) else 0)
    ((Set.finite_range fun g : Γ ↦ g • x).subset fun y hy ↦ by
      by_contra h
      exact hy (dite_eq_right fun h' ↦ h h'.2))

variable {χ}

/-- The coefficient of the twisted orbit sum at `g • x` is `χ g`. -/
theorem coeff_twistedOrbitSum_smul {x : X} (hx : stabilizer Γ x ≤ χ.ker) (g : Γ) :
    (twistedOrbitSum χ x).coeff (g • x) = χ g := by
  have h : stabilizer Γ x ≤ χ.ker ∧ ∃ c : Γ, c • x = g • x := ⟨hx, g, rfl⟩
  simp only [twistedOrbitSum, coeff_ofCoeff, Finsupp.ofSupportFinite_coe, dite_eq_left h]
  have hmem : g⁻¹ * h.2.choose ∈ stabilizer Γ x := by
    rw [mem_stabilizer_iff, mul_smul, h.2.choose_spec, inv_smul_smul]
  have := MonoidHom.mem_ker.1 (hx hmem)
  rw [map_mul, map_inv, inv_mul_eq_one] at this
  rw [← this]

/-- The twisted orbit sum at `x` vanishes off the orbit of `x`. -/
theorem coeff_twistedOrbitSum_of_notMem {x y : X} (hy : y ∉ orbit Γ x) :
    (twistedOrbitSum χ x).coeff y = 0 := by
  have h : ¬(stabilizer Γ x ≤ χ.ker ∧ ∃ g : Γ, g • x = y) := fun h ↦ hy h.2
  simp only [twistedOrbitSum, coeff_ofCoeff, Finsupp.ofSupportFinite_coe, dite_eq_right h]

/-- The twisted orbit sum at a point whose stabilizer is not contained in the kernel of `χ` is
`0`. -/
theorem twistedOrbitSum_of_not_le {x : X} (hx : ¬stabilizer Γ x ≤ χ.ker) :
    twistedOrbitSum χ x = 0 := by
  ext y
  have h : ¬(stabilizer Γ x ≤ χ.ker ∧ ∃ g : Γ, g • x = y) := fun h ↦ hx h.1
  simp only [twistedOrbitSum, coeff_ofCoeff, Finsupp.ofSupportFinite_coe, dite_eq_right h,
    coeff_zero, Finsupp.coe_zero, Pi.zero_apply]

@[simp]
theorem coeff_twistedOrbitSum_self {x : X} (hx : stabilizer Γ x ≤ χ.ker) :
    (twistedOrbitSum χ x).coeff x = 1 := by
  simpa using coeff_twistedOrbitSum_smul hx 1

/-- **Twisted orbit sums are invariant.** -/
theorem twistedOrbitSum_mem_invariants (x : X) :
    twistedOrbitSum χ x ∈ (charTwist χ (ofMulAction k Γ X)).invariants := by
  by_cases hx : stabilizer Γ x ≤ χ.ker
  · refine (mem_invariants_charTwist_ofMulAction_iff χ).2 fun g y ↦ ?_
    by_cases hy : y ∈ orbit Γ x
    · obtain ⟨c, rfl⟩ := hy
      rw [smul_smul, coeff_twistedOrbitSum_smul hx, coeff_twistedOrbitSum_smul hx, map_mul,
        Units.val_mul]
    · have hgy : g • y ∉ orbit Γ x := fun h ↦ hy (by simpa using mem_orbit_of_mem_orbit g⁻¹ h)
      rw [coeff_twistedOrbitSum_of_notMem hy, coeff_twistedOrbitSum_of_notMem hgy, mul_zero]
  · rw [twistedOrbitSum_of_not_le hx]
    exact Submodule.zero_mem _

/-! ### The orbit basis -/

omit [Finite Γ] in
/-- The representative of an orbit in `charTrivialOrbits` has stabilizer in the kernel of `χ`. -/
theorem stabilizer_out_le_ker {ω : orbitRel.Quotient Γ X} (hω : ω ∈ charTrivialOrbits X χ) :
    stabilizer Γ ω.out ≤ χ.ker :=
  mk_mem_charTrivialOrbits_iff.1 <| by rwa [Quotient.mk''_eq_mk, Quotient.out_eq]

/-- The twisted orbit sum at the representative of an orbit vanishes off that orbit. -/
theorem coeff_twistedOrbitSum_out_of_ne {ω : orbitRel.Quotient Γ X} {y : X}
    (hy : (Quotient.mk'' y : orbitRel.Quotient Γ X) ≠ ω) :
    (twistedOrbitSum χ ω.out).coeff y = 0 :=
  coeff_twistedOrbitSum_of_notMem fun h ↦ hy <| by
    rw [← orbitRel.Quotient.mem_orbit, orbitRel.Quotient.orbit_eq_orbit_out ω Quotient.out_eq']
    exact h

variable (χ) in
/-- The twisted orbit sum at the chosen representative of an orbit in `charTrivialOrbits`, as an
invariant vector. These vectors form the basis `TauCeti.twistedInvariantOrbitSumBasis`. -/
noncomputable def charTwistOrbitVector (ω : charTrivialOrbits X χ) :
    (charTwist χ (ofMulAction k Γ X)).invariants :=
  ⟨twistedOrbitSum χ ω.1.out, twistedOrbitSum_mem_invariants _⟩

@[simp]
theorem coe_charTwistOrbitVector (ω : charTrivialOrbits X χ) :
    (charTwistOrbitVector (k := k) χ ω : k[X]) = twistedOrbitSum χ ω.1.out :=
  (rfl)

/-- The coefficient of a combination of the vectors `charTwistOrbitVector χ ω` at a translate
`g • ω.out` of a representative is `χ g` times the coordinate at `ω`. -/
theorem coeff_linearCombination_charTwistOrbitVector_smul_out (c : charTrivialOrbits X χ →₀ k)
    (ω : charTrivialOrbits X χ) (g : Γ) :
    ((Finsupp.linearCombination k (charTwistOrbitVector χ) c : _) : k[X]).coeff (g • ω.1.out) =
      c ω * χ g := by
  classical
  have hmk : (Quotient.mk'' (g • ω.1.out) : orbitRel.Quotient Γ X) = ω.1 := by
    rw [← orbitRel.Quotient.mem_orbit, orbitRel.Quotient.orbit_eq_orbit_out _ Quotient.out_eq']
    exact mem_orbit _ g
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Submodule.coe_sum, coeff_sum,
    Finset.sum_apply', Finset.sum_eq_single ω]
  · simp [coeff_twistedOrbitSum_smul (stabilizer_out_le_ker ω.2)]
  · intro ω' _ hω'
    simp only [SetLike.val_smul, coeff_smul_apply, coe_charTwistOrbitVector, smul_eq_mul]
    rw [coeff_twistedOrbitSum_out_of_ne fun h ↦ hω' (Subtype.ext (hmk ▸ h).symm), mul_zero]
  · intro hω
    simp [Finsupp.notMem_support_iff.1 hω]

/-- A combination of the vectors `charTwistOrbitVector χ ω` vanishes at the points whose orbit is
not in `charTrivialOrbits`. -/
theorem coeff_linearCombination_charTwistOrbitVector_of_notMem (c : charTrivialOrbits X χ →₀ k)
    {y : X} (hy : (Quotient.mk'' y : orbitRel.Quotient Γ X) ∉ charTrivialOrbits X χ) :
    ((Finsupp.linearCombination k (charTwistOrbitVector χ) c : _) : k[X]).coeff y = 0 := by
  classical
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Submodule.coe_sum, coeff_sum,
    Finset.sum_apply']
  refine Finset.sum_eq_zero fun ω _ ↦ ?_
  simp only [SetLike.val_smul, coeff_smul_apply, coe_charTwistOrbitVector, smul_eq_mul]
  rw [coeff_twistedOrbitSum_out_of_ne fun h ↦ hy (h ▸ ω.2), mul_zero]

/-- The vectors `charTwistOrbitVector χ ω` are linearly independent. -/
theorem linearIndependent_charTwistOrbitVector :
    LinearIndependent k (charTwistOrbitVector (X := X) χ) := by
  refine linearIndependent_iff_injective_finsuppLinearCombination.2 <|
    (injective_iff_map_eq_zero _).2 fun c hc ↦ Finsupp.ext fun ω ↦ ?_
  have := coeff_linearCombination_charTwistOrbitVector_smul_out c ω 1
  rw [hc, one_smul] at this
  simpa using this.symm

/-- The vectors `charTwistOrbitVector χ ω` span the invariants, when `χ g - 1` is a
non-zero-divisor whenever `χ g ≠ 1`. -/
theorem span_range_charTwistOrbitVector
    (hχ : ∀ g : Γ, χ g ≠ 1 → IsLeftRegular ((χ g : k) - 1)) :
    Submodule.span k (Set.range (charTwistOrbitVector (X := X) χ)) = ⊤ := by
  rw [← Finsupp.range_linearCombination, LinearMap.range_eq_top]
  intro v
  have hfin :
      (Function.support fun ω : charTrivialOrbits X χ ↦ (v : k[X]).coeff ω.1.out).Finite := by
    convert ((v : k[X]).coeff.support.finite_toSet).preimage
      ((Quotient.out_injective.comp Subtype.val_injective).injOn) using 1
    ext ω
    simp
  refine ⟨Finsupp.ofSupportFinite (fun ω ↦ (v : k[X]).coeff ω.1.out) hfin, Subtype.ext ?_⟩
  ext y
  obtain ⟨g, hg⟩ := TauCeti.MulAction.exists_smul_out_eq (G := Γ) (y := y) rfl
  by_cases hy : (Quotient.mk'' y : orbitRel.Quotient Γ X) ∈ charTrivialOrbits X χ
  · have := coeff_linearCombination_charTwistOrbitVector_smul_out
      (Finsupp.ofSupportFinite (fun ω ↦ (v : k[X]).coeff ω.1.out) hfin) ⟨_, hy⟩ g
    rw [hg] at this
    rw [this]
    simp only [Finsupp.ofSupportFinite_coe]
    conv_rhs => rw [← hg, (mem_invariants_charTwist_ofMulAction_iff χ).1 v.2]
    exact mul_comm _ _
  · rw [coeff_linearCombination_charTwistOrbitVector_of_notMem _ hy]
    rw [mk_mem_charTrivialOrbits_iff, IsConcreteLE.not_le_iff_exists] at hy
    obtain ⟨h, hh, hχh⟩ := hy
    exact (coeff_eq_zero_of_mem_invariants_charTwist χ v.2 hh (hχ h hχh)).symm

/-- **The orbit basis of the invariants of a twisted permutation representation.** For a finite
group `Γ` acting on a type `X` and a character `χ` such that `χ g - 1` is a non-zero-divisor
whenever `χ g ≠ 1`, the invariants of `k[X]` twisted by `χ` are free, with basis the twisted orbit
sums of the orbits on which `χ` is trivial on stabilizers. -/
noncomputable def twistedInvariantOrbitSumBasis
    (hχ : ∀ g : Γ, χ g ≠ 1 → IsLeftRegular ((χ g : k) - 1)) :
    Basis (charTrivialOrbits X χ) k (charTwist χ (ofMulAction k Γ X)).invariants :=
  .mk linearIndependent_charTwistOrbitVector (span_range_charTwistOrbitVector hχ).ge

@[simp]
theorem twistedInvariantOrbitSumBasis_apply
    (hχ : ∀ g : Γ, χ g ≠ 1 → IsLeftRegular ((χ g : k) - 1)) (ω : charTrivialOrbits X χ) :
    twistedInvariantOrbitSumBasis hχ ω = charTwistOrbitVector χ ω := by
  simp [twistedInvariantOrbitSumBasis]

/-- The coordinate of an invariant at an orbit is its coefficient at the chosen representative of
that orbit. -/
@[simp]
theorem twistedInvariantOrbitSumBasis_repr_apply
    (hχ : ∀ g : Γ, χ g ≠ 1 → IsLeftRegular ((χ g : k) - 1))
    (v : (charTwist χ (ofMulAction k Γ X)).invariants) (ω : charTrivialOrbits X χ) :
    (twistedInvariantOrbitSumBasis hχ).repr v ω = (v : k[X]).coeff ω.1.out := by
  have hb : ⇑(twistedInvariantOrbitSumBasis (X := X) hχ) = charTwistOrbitVector χ :=
    funext (twistedInvariantOrbitSumBasis_apply hχ)
  conv_rhs => rw [← (twistedInvariantOrbitSumBasis hχ).linearCombination_repr v, hb]
  have := coeff_linearCombination_charTwistOrbitVector_smul_out
    ((twistedInvariantOrbitSumBasis hχ).repr v) ω 1
  rw [one_smul] at this
  rw [this, map_one, Units.val_one, mul_one]

/-- **The dimension of the invariants.** Over a field, the invariants of `k[X]` twisted by `χ`
have dimension the number of orbits on which `χ` is trivial on stabilizers. -/
theorem finrank_invariants_charTwist_ofMulAction {K : Type*} [Field K] (χ : Γ →* Kˣ) :
    finrank K (charTwist χ (ofMulAction K Γ X)).invariants = Nat.card (charTrivialOrbits X χ) :=
  finrank_eq_nat_card_basis
    (twistedInvariantOrbitSumBasis fun _ hg ↦ isLeftRegular_sub_one_of_ne_one χ hg)

end TauCeti
