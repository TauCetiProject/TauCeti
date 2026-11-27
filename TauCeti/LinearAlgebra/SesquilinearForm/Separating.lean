/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# Forms definite off the origin separate vectors

A semilinear map of two arguments `B` that is definite off the origin, `B x x ≠ 0` for `x ≠ 0`,
**separates** vectors: two vectors pairing identically against every vector are equal, because
their difference pairs to zero with itself. On a finite-dimensional space, a separating form
represents every pairing by a linear map, and a form definite off the origin identifies the space
semilinearly with its dual. In any dimension, the pairings of a vector with two linearly
independent vectors can be prescribed independently through a left-separating form. In general,
a sesquilinear map separates on the left exactly when it is injective in its left argument.

## Main results

* `LinearMap.separatingLeft_iff_injective`, `LinearMap.SeparatingLeft.injective`: a sesquilinear
  map is left-separating exactly when it is injective in its left argument.
* `LinearMap.eq_of_forall_sesq_eq`: a form definite off the origin separates vectors.
* `LinearMap.exists_linearMap_forall_apply_eq_apply`: every pairing factors through a separating
  form on a finite-dimensional space.
* `LinearMap.bijective_of_apply_self_ne_zero`: on a finite-dimensional space, a form definite off
  the origin is a bijection onto the dual.
* `LinearMap.SeparatingLeft.exists_apply_eq_and_apply_eq_of_linearIndependent`: through a
  left-separating form, the pairings with two linearly independent vectors can be prescribed
  independently.
-/

public section

namespace LinearMap

section Injective

variable {R R₁ R₂ M M₁ M₂ : Type*} [CommSemiring R] [Semiring R₁] [Semiring R₂]
  [AddCommMonoid M] [Module R M] [AddCommGroup M₁] [Module R₁ M₁] [AddCommMonoid M₂]
  [Module R₂ M₂] {I₁ : R₁ →+* R} {I₂ : R₂ →+* R} {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M}

/-- A sesquilinear map is left-separating exactly when it is injective as a map from its left
argument to the space of maps out of its right argument. -/
theorem separatingLeft_iff_injective : B.SeparatingLeft ↔ Function.Injective B :=
  separatingLeft_iff_linear_nontrivial.trans (injective_iff_map_eq_zero B).symm

/-- A left-separating sesquilinear map is injective in its left argument. -/
theorem SeparatingLeft.injective (hB : B.SeparatingLeft) : Function.Injective B :=
  separatingLeft_iff_injective.mp hB

end Injective

variable {R S M P : Type*} [Semiring R] [CommSemiring S] [AddCommGroup M] [Module R M]
  [AddCommGroup P] [Module S P] {I₁ I₂ : R →+* S}

/-- **A form definite off the origin separates vectors**: two vectors pairing identically against
every vector are equal, because their difference pairs to zero with itself.  Mathlib's
`LinearMap.SeparatingLeft` is the same separation stated as a property of the form; definiteness
off the origin is what supplies it here, and is the shape the callers carry it in. -/
theorem eq_of_forall_sesq_eq {B : M →ₛₗ[I₁] M →ₛₗ[I₂] P} (hdef : ∀ x : M, x ≠ 0 → B x x ≠ 0)
    {u v : M} (h : ∀ y : M, B u y = B v y) : u = v :=
  sub_eq_zero.1 <| not_not.1 fun hne ↦ hdef _ hne <| by simp [h]

/-- **Representing a pairing through a separating form.** Let `B` be a form on a finite-dimensional
space `V`, semilinear in the first variable and separating in the second, for instance a
nondegenerate sesquilinear form. Every pairing `S` of `V` with `W` of the same type has the form
`S x y = B x (T y)` for a linear map `T : W → V`. -/
theorem exists_linearMap_forall_apply_eq_apply {K V W : Type*} [Field K] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] [FiniteDimensional K V] {I : K →+* K}
    {B : V →ₛₗ[I] V →ₗ[K] K} (hB : B.SeparatingRight) (S : V →ₛₗ[I] W →ₗ[K] K) :
    ∃ T : W →ₗ[K] V, ∀ x y, S x y = B x (T y) := by
  let b := Module.finBasis K V
  -- The pairings of `v` with a basis determine `v`, so by dimension they take all values.
  let Φ : V →ₗ[K] Fin (Module.finrank K V) → K := LinearMap.pi fun i ↦ B (b i)
  have hΦ : Function.Injective Φ := (injective_iff_map_eq_zero Φ).mpr fun v hv ↦ by
    have h : B.flip v = 0 := b.ext fun i ↦ congrFun hv i
    exact hB v fun x ↦ LinearMap.congr_fun h x
  let e := Φ.linearEquivOfInjective hΦ (by simp)
  refine ⟨e.symm.toLinearMap ∘ₗ LinearMap.pi fun i ↦ S (b i), fun x y ↦ ?_⟩
  have h : S.flip y = B.flip (e.symm (fun i ↦ S (b i) y)) := b.ext fun i ↦
    (congrFun (e.apply_symm_apply fun i ↦ S (b i) y) i).symm
  exact LinearMap.congr_fun h x

/-- **Riesz representation for a form definite off the origin.** On a finite-dimensional space
`V`, a form `B`, semilinear in the first variable for a surjective `I` and with `B x x ≠ 0` for
`x ≠ 0`, identifies `V` semilinearly with its dual: every linear functional is `B u` for a unique
`u`. -/
theorem bijective_of_apply_self_ne_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {I : K →+* K} [RingHomSurjective I] {B : V →ₛₗ[I] V →ₗ[K] K}
    (hdef : ∀ x : V, x ≠ 0 → B x x ≠ 0) : Function.Bijective B := by
  have hdef' (u : V) (hu : B u u = 0) : u = 0 := not_not.1 fun hne ↦ hdef u hne hu
  refine ⟨(injective_iff_map_eq_zero B).2 fun u hu ↦ hdef' u (congrArg (· u) hu),
    LinearMap.range_eq_top.1 ?_⟩
  apply Submodule.eq_top_of_finrank_eq
  have hW := Subspace.finrank_add_finrank_dualCoannihilator_eq (LinearMap.range B)
  have hbot : (LinearMap.range B).dualCoannihilator = ⊥ :=
    (Submodule.eq_bot_iff _).2 fun u hu ↦
      hdef' u ((Submodule.mem_dualCoannihilator u).1 hu _ ⟨u, rfl⟩)
  rw [hbot, finrank_bot, add_zero] at hW
  rw [hW, Subspace.dual_finrank_eq]

/-- **Prescribing two pairings through a left-separating form.** Over a field, let `B` pair `V`
with `W` and separate the vectors of `V`. For linearly independent `u` and `v` and any `a` and `b`
there is `w` with `B u w = a` and `B v w = b`, that is, `x ↦ (B u x, B v x)` is onto `K × K`. No
finiteness of `V` or `W` is needed. -/
theorem SeparatingLeft.exists_apply_eq_and_apply_eq_of_linearIndependent {K V W : Type*}
    [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {B : V →ₗ[K] W →ₗ[K] K} (hB : B.SeparatingLeft) {u v : V}
    (hli : LinearIndependent K ![u, v]) (a b : K) : ∃ w, B u w = a ∧ B v w = b := by
  -- A linear form vanishing on the range of `φ` is `(s, t) ↦ a' * s + b' * t` with
  -- `B (a' • u + b' • v) = 0`, so `a' = b' = 0` and the range is everything.
  set φ := (B u).prod (B v)
  have hφ : LinearMap.range φ = ⊤ := by
    by_contra h
    obtain ⟨f, hf₀, hf⟩ := (LinearMap.range φ).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr h)
    have hfx (x : W) : B (f (1, 0) • u + f (0, 1) • v) x = 0 := by
      have hφx : φ x = B u x • ((1 : K), (0 : K)) + B v x • ((0 : K), (1 : K)) := by
        ext <;> simp [φ]
      have := LinearMap.mem_ker.mp (hf ⟨x, rfl⟩)
      simp only [hφx, map_add, map_smul, smul_eq_mul] at this
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      linear_combination this
    obtain ⟨ha, hb⟩ := LinearIndependent.pair_iff.mp hli _ _ (hB _ hfx)
    exact hf₀ (LinearMap.prod_ext (LinearMap.ext_ring ha) (LinearMap.ext_ring hb))
  obtain ⟨w, hw⟩ := LinearMap.range_eq_top.mp hφ (a, b)
  exact ⟨w, congrArg Prod.fst hw, congrArg Prod.snd hw⟩

end LinearMap
