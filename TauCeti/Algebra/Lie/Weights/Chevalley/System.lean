/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Weights.StructureConstant.Normalization

/-!
# Root vectors compatible with a Chevalley involution

Let `L` be a finite-dimensional Lie algebra with nondegenerate Killing form over a field of
characteristic zero, and let `H` be a splitting Cartan subalgebra. A normalized root-vector system
`x` satisfies

```text
⁅x α, x (-α)⁆ = α∨.
```

A *Chevalley system* additionally comes with a Lie automorphism `ω` exchanging opposite root
vectors with a sign:

```text
ω (x α) = -x (-α).
```

This file packages those two compatible pieces of data as `TauCeti.IsChevalleySystem`. The
compatibility already forces `ω` to act by negation on the Cartan subalgebra and to be an
involution on all of `L`: the coroots span `H`, while the root vectors together with `H` span `L`.

The main mathematical result is the integral normalization of every genuine root-sum bracket. If
`γ = α + β`, then

```text
⁅x α, x β⁆ = ±(p + 1) x γ,
```

where `p = chainBotCoeff α β`. The proof combines the Chevalley-involution symmetry and square
calculation from `TauCeti.Algebra.Lie.Weights.StructureConstant.Normalization` with the root-length
ratio from `TauCeti.Algebra.Lie.Weights.RootString`. The resulting integer-coefficient theorem is
stated both for the named structure constant and directly for the bracket, in the form consumed by
the integral root--coroot span.

## Main definitions and results

* `TauCeti.IsChevalleySystem`: a normalized root-vector system compatible with a Lie automorphism
  exchanging opposite root vectors with a sign.
* `TauCeti.IsChevalleySystem.map_coroot`: the automorphism negates every coroot.
* `TauCeti.IsChevalleySystem.map_cartan`: the automorphism negates the Cartan subalgebra.
* `TauCeti.IsChevalleySystem.involutive`: compatibility on the root vectors forces the
  automorphism to be an involution on all of `L`.
* `TauCeti.IsChevalleySystem.symm_eq`: the automorphism is its own inverse.
* `TauCeti.IsChevalleySystem.structureConstant_eq_natCast_or_eq_neg_natCast`: every genuine
  root-sum structure constant is `p + 1` or its negative.
* `TauCeti.IsChevalleySystem.exists_int_lie_eq_smul`: every root-sum bracket has an integral
  coefficient.
* `TauCeti.IsChevalleySystem.intStructureConstant`: that coefficient, named as an integer, with
  `lie_eq_intStructureConstant_zsmul` its defining equation and
  `intStructureConstant_eq_natCast_or_eq_neg_natCast` identifying it as `±(p + 1)`.
* `TauCeti.IsChevalleySystem.intStructureConstant₂`: the two-argument form `N(α,β)`, vanishing
  when `α + β` is not a root, with `intStructureConstant₂_skew` (antisymmetry),
  `intStructureConstant₂_eq_natCast_or_eq_neg_natCast` (values `±(p + 1)`),
  `intStructureConstant₂_neg_neg` (negating both roots negates the constant),
  `intStructureConstant₂_neg_swap` (swap-negation preserves it), and
  `intStructureConstant₂_cyclic_mul_killingForm` (cyclic symmetry up to Killing pairings).
* `TauCeti.IsChevalleySystem.intStructureConstant_neg_neg` and
  `TauCeti.IsChevalleySystem.intStructureConstant_cyclic_mul_killingForm`: the three-argument
  forms of the negation and cyclic symmetries, from which the two-argument versions follow.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §25.2.
* R. W. Carter, *Simple Groups of Lie Type*, §4.1.

This supplies the integral Chevalley-basis input to the explicit Chevalley--Demazure construction
in Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`, consumed by milestone L0 of the
`CFSGStatement` roadmap. The existence of a compatible Chevalley system remains downstream.
-/

public section

namespace TauCeti

open LieAlgebra LieAlgebra.IsKilling LieModule

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

/-- A normalized family of root vectors compatible with a Chevalley involution. The Lie
automorphism `ω` exchanges each root vector with the negative of its opposite.

There is no separate involutivity field: `TauCeti.IsChevalleySystem.involutive` proves it from this
compatibility and the fact that the root vectors and Cartan subalgebra span the ambient Lie
algebra. -/
structure IsChevalleySystem (ω : L ≃ₗ⁅K⁆ L) (x : Weight K H L → L) : Prop where
  /-- The root vectors are normalized against the coroots. -/
  toIsSl2System : IsSl2System x
  /-- The automorphism exchanges each root vector with the negative of its opposite. -/
  map_root (α : Weight K H L) : ω (x α) = -x (-α)

attribute [simp] IsChevalleySystem.map_root

namespace IsChevalleySystem

variable {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : IsChevalleySystem ω x)

include hx

/-- A Chevalley-system automorphism sends every coroot to its negative. This follows from the
normalization of opposite root vectors, rather than being separate data. -/
theorem map_coroot (α : Weight K H L) :
    ω (coroot α : L) = -(coroot α : L) := by
  by_cases hα : α.IsNonZero
  · calc
      ω (coroot α : L) = ω ⁅x α, x (-α)⁆ := by rw [hx.toIsSl2System.lie_neg α hα]
      _ = ⁅ω (x α), ω (x (-α))⁆ := ω.map_lie (x α) (x (-α))
      _ = ⁅-x (-α), -x (-(-α))⁆ := by rw [hx.map_root α, hx.map_root (-α)]
      _ = ⁅x (-α), x α⁆ := by simp
      _ = -⁅x α, x (-α)⁆ := (lie_skew (x (-α)) (x α)).symm
      _ = -(coroot α : L) := by rw [hx.toIsSl2System.lie_neg α hα]
  · rw [coroot_eq_zero_iff.2 (not_not.mp hα)]
    simp

/-- A Chevalley-system automorphism acts by negation on the splitting Cartan subalgebra. It is
enough to check the coroots because they span `H`. -/
theorem map_cartan (h : H) : ω (h : L) = -(h : L) := by
  have hh : h ∈ Submodule.span K (Set.range (rootSystem H).coroot) := by
    rw [RootPairing.IsRootSystem.span_coroot_eq_top]
    trivial
  induction hh using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨α, rfl⟩ := hy
      rw [rootSystem_coroot_apply]
      exact hx.map_coroot α.1
  | zero => simp
  | add y z _ _ hy hz =>
      -- Expose the ambient addition hidden by the subtype coercion in the induction goal.
      change ω ((y : L) + (z : L)) = -((y : L) + (z : L))
      rw [map_add, hy, hz]
      abel
  | smul c y _ hy =>
      -- Expose the ambient scalar action hidden by the subtype coercion in the induction goal.
      change ω (c • (y : L)) = -(c • (y : L))
      rw [map_smul, hy]
      simp

/-- **A Chevalley-system automorphism is an involution.** The compatibility equation on root
vectors forces this globally: the root vectors together with the Cartan subalgebra span `L`. -/
theorem involutive : Function.Involutive ω := by
  intro z
  let f : L →ₗ[K] L := ω.toLinearMap.comp ω.toLinearMap - LinearMap.id
  have hroot : Submodule.span K (Set.range x) ≤ LinearMap.ker f := by
    rw [Submodule.span_le]
    rintro y ⟨α, rfl⟩
    -- Membership in the kernel is presented through the submodule coercion here.
    change f (x α) = 0
    simp [f, hx.map_root]
  have hcartan : H.toSubmodule ≤ LinearMap.ker f := by
    intro h hh
    -- Membership in the kernel is presented through the submodule coercion here.
    change f h = 0
    simp [f, hx.map_cartan ⟨h, hh⟩]
  have htop : (⊤ : Submodule K L) ≤ LinearMap.ker f := by
    rw [← hx.toIsSl2System.span_range_sup_toSubmodule_eq_top]
    exact sup_le hroot hcartan
  have hz : z ∈ LinearMap.ker f := htop trivial
  rw [LinearMap.mem_ker] at hz
  exact sub_eq_zero.mp (by simpa [f] using hz)

/-- A Chevalley-system automorphism is its own inverse. -/
theorem symm_eq : ω.symm = ω := by
  ext z
  apply ω.injective
  -- Expose the applications hidden by the `LieEquiv` coercions after applying injectivity.
  change ω (ω.symm z) = ω (ω z)
  rw [ω.apply_symm_apply, hx.involutive z]

/-- **Chevalley normalization of structure constants.** If `γ = α + β` is a genuine root sum,
then the structure constant of a Chevalley system is `p + 1` or its negative, where
`p = chainBotCoeff α β`.

The root-length ratio is automatic for normalized root vectors; compatibility with `ω` supplies
the symmetry that turns the root-string product formula into a square. -/
theorem structureConstant_eq_natCast_or_eq_neg_natCast
    (α β γ : Weight K H L) (hα : α.IsNonZero) (hβ : β.IsNonZero) (hγ : γ.IsNonZero)
    (hαβ : (γ : H → K) = (α : H → K) + β) :
    hx.toIsSl2System.structureConstant α β γ hγ hαβ =
        ((chainBotCoeff α β + 1 : ℕ) : K) ∨
      hx.toIsSl2System.structureConstant α β γ hγ hαβ =
        -((chainBotCoeff α β + 1 : ℕ) : K) :=
  hx.toIsSl2System.structureConstant_eq_natCast_or_eq_neg_natCast_of_killingForm_ratio
    α β γ hα hβ hγ hαβ ω.toLieHom (hx.map_root α) (hx.map_root β) (hx.map_root γ)
    (hx.toIsSl2System.chainTopCoeff_mul_killingForm_root_neg_eq α β γ hα hβ hγ hαβ)

/-- The structure constant of a genuine root-sum bracket in a Chevalley system is the cast of an
integer. The preceding theorem identifies that integer more precisely as `±(p + 1)`. -/
theorem exists_int_structureConstant
    (α β γ : Weight K H L) (hγ : γ.IsNonZero)
    (hαβ : (γ : H → K) = (α : H → K) + β) :
    ∃ z : ℤ, hx.toIsSl2System.structureConstant α β γ hγ hαβ = (z : K) := by
  by_cases hα : α.IsNonZero
  · by_cases hβ : β.IsNonZero
    · rcases hx.structureConstant_eq_natCast_or_eq_neg_natCast α β γ hα hβ hγ hαβ with h | h
      · exact ⟨chainBotCoeff α β + 1, by simpa using h⟩
      · exact ⟨-(chainBotCoeff α β + 1 : ℤ), by simpa using h⟩
    · refine ⟨0, ?_⟩
      push_cast
      have hxβ : x β = 0 := hx.toIsSl2System.eq_zero_of_isZero β (not_not.mp hβ)
      have hlie : ⁅x α, x β⁆ = 0 := by rw [hxβ, lie_zero]
      rw [hx.toIsSl2System.lie_eq_structureConstant_smul α β γ hγ hαβ] at hlie
      exact smul_eq_zero.mp hlie |>.resolve_right (hx.toIsSl2System.ne_zero γ hγ)
  · refine ⟨0, ?_⟩
    push_cast
    have hxα : x α = 0 := hx.toIsSl2System.eq_zero_of_isZero α (not_not.mp hα)
    have hlie : ⁅x α, x β⁆ = 0 := by rw [hxα, zero_lie]
    rw [hx.toIsSl2System.lie_eq_structureConstant_smul α β γ hγ hαβ] at hlie
    exact smul_eq_zero.mp hlie |>.resolve_right (hx.toIsSl2System.ne_zero γ hγ)

/-- Every genuine root-sum bracket in a Chevalley system has an integral coefficient. This is the
form needed to prove that the integral span of root vectors and coroots is closed under the Lie
bracket. -/
theorem exists_int_lie_eq_smul
    (α β γ : Weight K H L) (hγ : γ.IsNonZero)
    (hαβ : (γ : H → K) = (α : H → K) + β) :
    ∃ z : ℤ, ⁅x α, x β⁆ = (z : K) • x γ := by
  obtain ⟨z, hz⟩ := hx.exists_int_structureConstant α β γ hγ hαβ
  refine ⟨z, ?_⟩
  rw [hx.toIsSl2System.lie_eq_structureConstant_smul α β γ hγ hαβ, hz]

/-- **The integer structure constant of a Chevalley system**: the unique integer `N` with
`⁅x α, x β⁆ = N • x γ` when the root `γ` is the sum of `α` and `β`.

The rational structure constant of a merely normalised system is a scalar of the base field. The
Chevalley normalization pins it to the image of an integer, and it is the integer, not its cast,
that a construction in characteristic `p` needs. The public interface is
`TauCeti.IsChevalleySystem.intStructureConstant_cast` and its uniqueness restatement
`TauCeti.IsChevalleySystem.eq_intStructureConstant_iff`; consumers need not unfold this choice. -/
noncomputable def intStructureConstant
    (α β γ : Weight K H L) (hγ : γ.IsNonZero)
    (hαβ : (γ : H → K) = (α : H → K) + β) : ℤ :=
  Classical.choose (hx.exists_int_structureConstant α β γ hγ hαβ)

/-- The cast of the integer structure constant is the structure constant. -/
@[simp]
theorem intStructureConstant_cast
    (α β γ : Weight K H L) (hγ : γ.IsNonZero)
    (hαβ : (γ : H → K) = (α : H → K) + β) :
    ((hx.intStructureConstant α β γ hγ hαβ : ℤ) : K) =
      hx.toIsSl2System.structureConstant α β γ hγ hαβ :=
  (Classical.choose_spec (hx.exists_int_structureConstant α β γ hγ hαβ)).symm

/-- **The defining equation of the integer structure constant.** The coefficient is an integer
acting by `ℤ`-scalar multiplication, which is what survives reduction to a base of arbitrary
characteristic. -/
theorem lie_eq_intStructureConstant_zsmul
    (α β γ : Weight K H L) (hγ : γ.IsNonZero)
    (hαβ : (γ : H → K) = (α : H → K) + β) :
    ⁅x α, x β⁆ = hx.intStructureConstant α β γ hγ hαβ • x γ := by
  rw [hx.toIsSl2System.lie_eq_structureConstant_smul α β γ hγ hαβ,
    ← hx.intStructureConstant_cast α β γ hγ hαβ, Int.cast_smul_eq_zsmul]

/-- An integer is the integer structure constant exactly when it gives the bracket of the
corresponding root vectors. -/
@[simp]
theorem eq_intStructureConstant_iff
    (α β γ : Weight K H L) (hγ : γ.IsNonZero)
    (hαβ : (γ : H → K) = (α : H → K) + β) (z : ℤ) :
    z = hx.intStructureConstant α β γ hγ hαβ ↔ ⁅x α, x β⁆ = z • x γ := by
  refine ⟨fun hz => hz ▸ hx.lie_eq_intStructureConstant_zsmul α β γ hγ hαβ, fun hz => ?_⟩
  refine Int.cast_injective (α := K) ?_
  rw [hx.intStructureConstant_cast α β γ hγ hαβ]
  exact (hx.toIsSl2System.eq_structureConstant_iff α β γ hγ hαβ (z : K)).2
    (by rw [Int.cast_smul_eq_zsmul]; exact hz)

/-- The integer structure constant of a genuine root-sum bracket is `±(p + 1)`, for `p` the
root-string coefficient `chainBotCoeff α β`. -/
theorem intStructureConstant_eq_natCast_or_eq_neg_natCast
    (α β γ : Weight K H L) (hα : α.IsNonZero) (hβ : β.IsNonZero) (hγ : γ.IsNonZero)
    (hαβ : (γ : H → K) = (α : H → K) + β) :
    hx.intStructureConstant α β γ hγ hαβ = (chainBotCoeff α β + 1 : ℕ) ∨
      hx.intStructureConstant α β γ hγ hαβ = -((chainBotCoeff α β + 1 : ℕ) : ℤ) := by
  rcases hx.structureConstant_eq_natCast_or_eq_neg_natCast α β γ hα hβ hγ hαβ with hN | hN
  · exact Or.inl (Int.cast_injective (α := K)
      (by rw [hx.intStructureConstant_cast α β γ hγ hαβ, hN]; push_cast; ring))
  · exact Or.inr (Int.cast_injective (α := K)
      (by rw [hx.intStructureConstant_cast α β γ hγ hαβ, hN]; push_cast; ring))

/-- The integer structure constant of a genuine root-sum bracket is nonzero. -/
theorem intStructureConstant_ne_zero
    (α β γ : Weight K H L) (hα : α.IsNonZero) (hβ : β.IsNonZero) (hγ : γ.IsNonZero)
    (hαβ : (γ : H → K) = (α : H → K) + β) :
    hx.intStructureConstant α β γ hγ hαβ ≠ 0 := by
  intro hzero
  refine hx.toIsSl2System.structureConstant_ne_zero α β γ hγ hαβ hα hβ ?_
  rw [← hx.intStructureConstant_cast α β γ hγ hαβ, hzero, Int.cast_zero]

/-- **Negating both roots negates the integer structure constant.** The Chevalley involution
sends the defining bracket equation `⁅x α, x β⁆ = N • x γ` to
`⁅x (-α), x (-β)⁆ = -N • x (-γ)`; uniqueness of the integer coefficient identifies the
constant at `(-α, -β)` as `-N`. -/
theorem intStructureConstant_neg_neg
    (α β γ : Weight K H L) (hγ : γ.IsNonZero)
    (hαβ : (γ : H → K) = (α : H → K) + β) :
    hx.intStructureConstant (-α) (-β) (-γ) hγ.neg (by
        rw [Weight.coe_neg, Weight.coe_neg, Weight.coe_neg, hαβ]
        abel) =
      -hx.intStructureConstant α β γ hγ hαβ := by
  refine Int.cast_injective (α := K) ?_
  rw [Int.cast_neg, hx.intStructureConstant_cast, hx.intStructureConstant_cast]
  exact hx.toIsSl2System.structureConstant_neg_neg_of_hom α β γ hγ hαβ ω.toLieHom
    (hx.map_root α) (hx.map_root β) (hx.map_root γ)

/-- **Cyclic symmetry of the integer structure constants.** For a root sum `γ = α + β`, the
Killing-weighted constants at `(α, β, γ)` and `(β, -γ, -α)` agree. This is the integral form
of the cyclic symmetry feeding the Chevalley commutator formula: with `α + β + γ' = 0`
(taking `γ' = -γ`), it relates `N(α, β)` to `N(β, γ')` up to the Killing pairings, which are
nonzero and explicitly known. -/
theorem intStructureConstant_cyclic_mul_killingForm
    (α β γ : Weight K H L) (hα : α.IsNonZero) (hγ : γ.IsNonZero)
    (hαβ : (γ : H → K) = (α : H → K) + β) :
    ((hx.intStructureConstant α β γ hγ hαβ : ℤ) : K) * killingForm K L (x γ) (x (-γ)) =
      ((hx.intStructureConstant β (-γ) (-α) hα.neg (by
        rw [Weight.coe_neg, Weight.coe_neg, hαβ]; abel) : ℤ) : K) *
        killingForm K L (x α) (x (-α)) := by
  rw [hx.intStructureConstant_cast α β γ hγ hαβ,
    hx.intStructureConstant_cast β (-γ) (-α) hα.neg _]
  exact hx.toIsSl2System.structureConstant_mul_killingForm_eq α β γ hγ hαβ hα

/-! ## Two-argument integer structure constants -/

omit hx in
/-- The two-argument integer structure constant of a Chevalley system. When `α + β` is a
nonzero root, this is the integer `N(α,β)` with `⁅x α, x β⁆ = N(α,β) • x(α+β)`; it is `0`
when `α + β` is not a root. The witness root is unique because the weight coercion is
injective, so the choice is well-defined. This form is consumed by the Chevalley
commutator formula. -/
noncomputable def intStructureConstant₂ {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L}
    (hx : IsChevalleySystem ω x) (α β : Weight K H L) : ℤ := by
  haveI := Classical.propDecidable
    (∃ γ : Weight K H L, γ.IsNonZero ∧ ((γ : H → K) = (α : H → K) + β))
  exact if h : ∃ γ : Weight K H L, γ.IsNonZero ∧ ((γ : H → K) = (α : H → K) + β) then
    hx.intStructureConstant α β (Classical.choose h) (Classical.choose_spec h).1
      (Classical.choose_spec h).2
  else
    0

omit hx in
/-- The two-argument constant agrees with the three-argument constant on a root sum. -/
theorem intStructureConstant₂_eq_intStructureConstant {ω : L ≃ₗ⁅K⁆ L}
    {x : Weight K H L → L} (hx : IsChevalleySystem ω x) (α β γ : Weight K H L)
    (hγ : γ.IsNonZero) (hαβ : (γ : H → K) = (α : H → K) + β) :
    hx.intStructureConstant₂ α β = hx.intStructureConstant α β γ hγ hαβ := by
  have hchoose : ∀ h : ∃ γ' : Weight K H L, γ'.IsNonZero ∧
      ((γ' : H → K) = (α : H → K) + β),
      hx.intStructureConstant α β (Classical.choose h) (Classical.choose_spec h).1
        (Classical.choose_spec h).2 = hx.intStructureConstant α β γ hγ hαβ := by
    intro h
    have hγ' : Classical.choose h = γ := by
      apply DFunLike.coe_injective
      calc ((Classical.choose h : Weight K H L) : H → K)
          = (α : H → K) + β := (Classical.choose_spec h).2
        _ = (γ : H → K) := hαβ.symm
    subst hγ'
    rfl
  unfold intStructureConstant₂
  split
  · exact hchoose _
  · rename_i hneg
    exact absurd ⟨γ, hγ, hαβ⟩ hneg

omit hx in
/-- The two-argument constant vanishes when `α + β` is not a root. -/
@[simp]
theorem intStructureConstant₂_eq_zero_of_not_isRootSum {ω : L ≃ₗ⁅K⁆ L}
    {x : Weight K H L → L} (hx : IsChevalleySystem ω x) (α β : Weight K H L)
    (h : ¬ ∃ γ : Weight K H L, γ.IsNonZero ∧ ((γ : H → K) = (α : H → K) + β)) :
    hx.intStructureConstant₂ α β = 0 := by
  unfold intStructureConstant₂
  split
  · rename_i hpos
    exact (h hpos).elim
  · rfl

omit hx in
/-- Swapping the two input weights negates the two-argument integer structure constant. -/
theorem intStructureConstant₂_skew {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L}
    (hx : IsChevalleySystem ω x) (α β : Weight K H L) :
    hx.intStructureConstant₂ β α = -hx.intStructureConstant₂ α β := by
  classical
  by_cases h : ∃ γ : Weight K H L, γ.IsNonZero ∧ ((γ : H → K) = (α : H → K) + β)
  · obtain ⟨γ, hγ, hαβ⟩ := h
    have hβα : (γ : H → K) = (β : H → K) + α := by rw [hαβ, add_comm]
    have e1 := hx.intStructureConstant₂_eq_intStructureConstant β α γ hγ hβα
    have e2 := hx.intStructureConstant₂_eq_intStructureConstant α β γ hγ hαβ
    rw [e1, e2]
    have hcast : ((hx.intStructureConstant β α γ hγ hβα : ℤ) : K)
        = (((-hx.intStructureConstant α β γ hγ hαβ : ℤ)) : K) := by
      rw [Int.cast_neg, hx.intStructureConstant_cast, hx.intStructureConstant_cast]
      exact hx.toIsSl2System.structureConstant_skew α β γ hγ hαβ
    exact Int.cast_injective hcast
  · have h' : ¬ ∃ γ : Weight K H L, γ.IsNonZero ∧
        ((γ : H → K) = (β : H → K) + α) := by
      rintro ⟨γ, hγ, hαβ⟩
      exact h ⟨γ, hγ, by rw [hαβ, add_comm]⟩
    rw [hx.intStructureConstant₂_eq_zero_of_not_isRootSum β α h',
      hx.intStructureConstant₂_eq_zero_of_not_isRootSum α β h, neg_zero]

omit hx in
/-- On a genuine root sum of nonzero roots, the two-argument constant is `±(p + 1)` for the
root-string coefficient `p = chainBotCoeff α β`. -/
theorem intStructureConstant₂_eq_natCast_or_eq_neg_natCast {ω : L ≃ₗ⁅K⁆ L}
    {x : Weight K H L → L} (hx : IsChevalleySystem ω x) (α β γ : Weight K H L)
    (hα : α.IsNonZero) (hβ : β.IsNonZero) (hγ : γ.IsNonZero)
    (hαβ : (γ : H → K) = (α : H → K) + β) :
    hx.intStructureConstant₂ α β = (chainBotCoeff α β + 1 : ℕ) ∨
      hx.intStructureConstant₂ α β = -((chainBotCoeff α β + 1 : ℕ) : ℤ) := by
  rw [hx.intStructureConstant₂_eq_intStructureConstant α β γ hγ hαβ]
  exact hx.intStructureConstant_eq_natCast_or_eq_neg_natCast α β γ hα hβ hγ hαβ

omit hx in
/-- The defining bracket equation for the two-argument constant on a root sum. -/
theorem lie_eq_intStructureConstant₂_zsmul {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L}
    (hx : IsChevalleySystem ω x) (α β γ : Weight K H L)
    (hγ : γ.IsNonZero) (hαβ : (γ : H → K) = (α : H → K) + β) :
    ⁅x α, x β⁆ = hx.intStructureConstant₂ α β • x γ := by
  have heq : hx.intStructureConstant₂ α β = hx.intStructureConstant α β γ hγ hαβ :=
    hx.intStructureConstant₂_eq_intStructureConstant α β γ hγ hαβ
  rw [heq]
  exact hx.lie_eq_intStructureConstant_zsmul α β γ hγ hαβ

omit hx in
/-- Negating both weights negates the two-argument integer structure constant. -/
theorem intStructureConstant₂_neg_neg {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L}
    (hx : IsChevalleySystem ω x) (α β : Weight K H L) :
    hx.intStructureConstant₂ (-α) (-β) = -hx.intStructureConstant₂ α β := by
  classical
  by_cases h : ∃ γ : Weight K H L, γ.IsNonZero ∧ ((γ : H → K) = (α : H → K) + β)
  · obtain ⟨γ, hγ, hαβ⟩ := h
    have hneg : ((-γ : Weight K H L) : H → K) =
        ((-α : Weight K H L) : H → K) + ((-β : Weight K H L) : H → K) := by
      rw [Weight.coe_neg, Weight.coe_neg, Weight.coe_neg]
      linear_combination -hαβ
    have e1 := hx.intStructureConstant₂_eq_intStructureConstant (-α) (-β) (-γ) hγ.neg hneg
    have e2 := hx.intStructureConstant₂_eq_intStructureConstant α β γ hγ hαβ
    rw [e1, e2]
    exact hx.intStructureConstant_neg_neg α β γ hγ hαβ
  · have h' : ¬ ∃ γ' : Weight K H L, γ'.IsNonZero ∧
        ((γ' : H → K) = ((-α : Weight K H L) : H → K) + ((-β : Weight K H L) : H → K)) := by
      rintro ⟨γ', hγ', hsum⟩
      apply h
      refine ⟨-γ', hγ'.neg, ?_⟩
      have hsum2 : (γ' : H → K) = -(α : H → K) + -(β : H → K) := by
        rw [hsum, Weight.coe_neg, Weight.coe_neg]
      have hgoal : ((-γ' : Weight K H L) : H → K) = -(γ' : H → K) := Weight.coe_neg
      rw [hgoal, hsum2]
      abel
    rw [hx.intStructureConstant₂_eq_zero_of_not_isRootSum (-α) (-β) h',
      hx.intStructureConstant₂_eq_zero_of_not_isRootSum α β h, neg_zero]

omit hx in
/-- Swapping and negating both weights preserves the two-argument constant. This combines
antisymmetry with negation: `N(-β, -α) = -N(-α, -β) = N(α, β)`. -/
theorem intStructureConstant₂_neg_swap {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L}
    (hx : IsChevalleySystem ω x) (α β : Weight K H L) :
    hx.intStructureConstant₂ (-β) (-α) = hx.intStructureConstant₂ α β := by
  rw [hx.intStructureConstant₂_skew (-α) (-β), hx.intStructureConstant₂_neg_neg α β, neg_neg]

omit hx in
/-- **Cyclic symmetry of the two-argument integer structure constants.** For a root sum
`γ = α + β`, the Killing-weighted constants at `(α, β)` and `(β, -γ)` agree. With
`α + β + γ' = 0` (taking `γ' = -γ`), this is the standard cyclic relation
`N(α, β) · B(x_γ, x_{-γ}) = N(β, γ') · B(x_α, x_{-α})` used by the Chevalley commutator
formula. -/
theorem intStructureConstant₂_cyclic_mul_killingForm {ω : L ≃ₗ⁅K⁆ L}
    {x : Weight K H L → L} (hx : IsChevalleySystem ω x) (α β γ : Weight K H L)
    (hα : α.IsNonZero) (hγ : γ.IsNonZero)
    (hαβ : (γ : H → K) = (α : H → K) + β) :
    ((hx.intStructureConstant₂ α β : ℤ) : K) * killingForm K L (x γ) (x (-γ)) =
      ((hx.intStructureConstant₂ β (-γ) : ℤ) : K) * killingForm K L (x α) (x (-α)) := by
  have hsum : ((-α : Weight K H L) : H → K) = (β : H → K) + ((-γ : Weight K H L) : H → K) := by
    rw [Weight.coe_neg, Weight.coe_neg, hαβ]
    abel
  rw [hx.intStructureConstant₂_eq_intStructureConstant α β γ hγ hαβ,
    hx.intStructureConstant₂_eq_intStructureConstant β (-γ) (-α) hα.neg hsum]
  exact hx.intStructureConstant_cyclic_mul_killingForm α β γ hα hγ hαβ

end IsChevalleySystem

end TauCeti
