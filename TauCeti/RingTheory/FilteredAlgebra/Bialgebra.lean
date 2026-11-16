/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.GroupLike
public import Mathlib.RingTheory.Bialgebra.Primitive
public import TauCeti.RingTheory.FilteredAlgebra.Exp.Basic
public import TauCeti.RingTheory.FilteredAlgebra.TensorProduct.Basic

/-!
# Completed counit, comultiplication, and primitive-exponential correspondence

Let `A` be a bialgebra over a commutative ring `R` equipped with a decreasing multiplicative
two-sided ideal filtration `F : AlgFiltration A`. Even when the finite quotients `A ⧸ F.ideal k`
are not quotient coalgebras, the bialgebra operations extend to the completion `F.completion`
whenever comultiplication preserves total filtration degree and the counit vanishes on the first
filtration ideal:

* `TauCeti.AlgFiltration.completedComul` extends comultiplication to an `R`-algebra homomorphism
  `F.completion →ₐ[R] (F.tensorProduct R F).completion`.
* `TauCeti.AlgFiltration.completedCounit` descends the counit through the order-zero quotient to an
  `R`-algebra homomorphism `F.completion →ₐ[R] R`.

Using the completed pure-tensor pairing `TauCeti.AlgFiltration.completedTensor`, this file defines
completed group-like elements (`TauCeti.AlgFiltration.IsCompletedGroupLike`) and completed
primitive elements (`TauCeti.AlgFiltration.IsCompletedPrimitive`). Completing the left counit law
shows that `Δ̂ x = x ⊗̂ 1 + 1 ⊗̂ x` already implies `ε̂ x = 0` over any commutative base ring, with
no separatedness, flatness, or torsion-freeness hypothesis.

When `A` is also a rational algebra whose rational and `R`-scalar actions commute, the completed
exponential and logarithm of `TauCeti.RingTheory.FilteredAlgebra.Exp.Basic` commute with
`completedComul` and exchange completed primitive elements of the first completion ideal with
completed group-like elements congruent to `1` modulo the first completion ideal
(`TauCeti.AlgFiltration.completedExpPrimitiveEquiv`). Because completed group-like elements are
closed under multiplication, `log (exp x * exp y)` is again a completed primitive element whenever
`x` and `y` are
(`TauCeti.AlgFiltration.isCompletedPrimitive_completedLog_completedExp_mul_completedExp`).

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter II, §6.
* D. Quillen, *Rational homotopy theory*, Ann. of Math. (2) **90** (1969), Appendix A.
* J.-P. Serre, *Lie Algebras and Lie Groups*, Part I, Chapter IV.
-/

public section

open scoped TensorProduct

namespace TauCeti.AlgFiltration

section Comul

variable (R : Type*) {A : Type*} [CommRing R] [Ring A] [Bialgebra R A] (F : AlgFiltration A)
  (hΔ : ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))

/-- The completed comultiplication `F.completion →ₐ[R] (F.tensorProduct R F).completion` induced by
a filtration-preserving bialgebra comultiplication. -/
noncomputable def completedComul : F.completion →ₐ[R] (F.tensorProduct R F).completion :=
  F.mapCompletionₐ (F.tensorProduct R F) (Bialgebra.comulAlgHom R A) id monotone_id
    fun k => hΔ (k + 1)

/-- Forgetting scalars on `completedComul` gives the ring completion map of comultiplication. -/
@[simp]
theorem coe_completedComul :
    (F.completedComul R hΔ : F.completion →+* (F.tensorProduct R F).completion) =
      F.mapCompletion (F.tensorProduct R F) (Bialgebra.comulAlgHom R A : A →+* A ⊗[R] A)
        id monotone_id (fun k => hΔ (k + 1)) :=
  F.coe_mapCompletionₐ (F.tensorProduct R F) (Bialgebra.comulAlgHom R A) id monotone_id _

/-- Completing a canonical element commutes with comultiplication. -/
@[simp]
theorem completedComul_toCompletion (a : A) :
    F.completedComul R hΔ (F.toCompletion a) =
      (F.tensorProduct R F).toCompletion (Coalgebra.comul (R := R) a) :=
  F.mapCompletionₐ_toCompletion _ _ _ monotone_id _ a

/-- The order-`k` component of `completedComul` is the quotient map induced by comultiplication. -/
@[simp]
theorem projection_completedComul (k : ℕ) (x : F.completion) :
    (F.tensorProduct R F).projection k (F.completedComul R hΔ x) =
      Ideal.quotientMapₐ ((F.tensorProduct R F).ideal (k + 1)) (Bialgebra.comulAlgHom R A)
        (hΔ (k + 1)) (F.projection k x) :=
  F.projection_mapCompletionₐ _ _ _ monotone_id _ k x

/-- Completed comultiplication preserves every completion filtration order. -/
theorem completedComul_mem_completionIdeal {k : ℕ} {x : F.completion}
    (hx : x ∈ F.completionIdeal k) :
    F.completedComul R hΔ x ∈ (F.tensorProduct R F).completionIdeal k := by
  cases k with
  | zero => simp
  | succ k => exact F.mapCompletionₐ_mem_completionIdeal _ _ id monotone_id _ k hx

end Comul

section Counit

variable (R : Type*) {A : Type*} [CommRing R] [Ring A] [Bialgebra R A] (F : AlgFiltration A)
  (hε : F.ideal 1 ≤ RingHom.ker (Bialgebra.counitAlgHom R A))

/-- The completed counit `F.completion →ₐ[R] R`, factoring the bialgebra counit through the
order-zero projection `F.projectionₐ 0 : F.completion →ₐ[R] A ⧸ F.ideal 1`. -/
noncomputable def completedCounit : F.completion →ₐ[R] R :=
  (Ideal.Quotient.liftₐ (F.ideal 1) (Bialgebra.counitAlgHom R A)
    fun _ ha => RingHom.mem_ker.mp (hε ha)).comp (F.projectionₐ (R := R) 0)

/-- The completed counit of a representative of the order-zero projection is its ordinary counit. -/
theorem completedCounit_eq_of_mk_eq_projection_zero {x : F.completion} {a : A}
    (ha : Ideal.Quotient.mk (F.ideal 1) a = F.projection 0 x) :
    F.completedCounit R hε x = Coalgebra.counit (R := R) a := by
  rw [completedCounit, AlgHom.comp_apply, projectionₐ_apply, ← ha]
  rfl

/-- Completing a canonical element preserves its counit. -/
@[simp]
theorem completedCounit_toCompletion (a : A) :
    F.completedCounit R hε (F.toCompletion a) = Coalgebra.counit (R := R) a :=
  F.completedCounit_eq_of_mk_eq_projection_zero R hε (F.projection_toCompletion 0 a).symm

/-- The first completion ideal lies in the kernel of the completed counit. -/
theorem completionIdeal_one_le_ker_completedCounit :
    F.completionIdeal 1 ≤ RingHom.ker (F.completedCounit R hε) := by
  intro x hx
  rw [completionIdeal_succ, RingHom.mem_ker] at hx
  rw [RingHom.mem_ker, completedCounit, AlgHom.comp_apply, projectionₐ_apply, hx, map_zero]

/-- Elements of the first completion ideal have completed counit zero. -/
theorem completedCounit_eq_zero_of_mem {x : F.completion} (hx : x ∈ F.completionIdeal 1) :
    F.completedCounit R hε x = 0 :=
  RingHom.mem_ker.mp (F.completionIdeal_one_le_ker_completedCounit R hε hx)

/-- Elements congruent to `1` modulo the first completion ideal have completed counit `1`. -/
theorem completedCounit_eq_one_of_sub_one_mem {u : F.completion}
    (hu : u - 1 ∈ F.completionIdeal 1) :
    F.completedCounit R hε u = 1 := by
  have h0 := F.completedCounit_eq_zero_of_mem R hε hu
  rwa [map_sub, map_one, sub_eq_zero] at h0

/-- When the first filtration ideal equals the augmentation kernel, the kernel of `completedCounit`
is exactly the first completion ideal. -/
theorem ker_completedCounit_eq_completionIdeal_one
    (hε' : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1) :
    RingHom.ker (F.completedCounit R hε) = F.completionIdeal 1 := by
  apply le_antisymm _ (F.completionIdeal_one_le_ker_completedCounit R hε)
  intro x hx
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection 0 x)
  have ha0 : a ∈ F.ideal 1 := hε' <| RingHom.mem_ker.mpr <| by
    rw [Bialgebra.counitAlgHom_apply,
      ← F.completedCounit_eq_of_mk_eq_projection_zero R hε ha]
    exact RingHom.mem_ker.mp hx
  rw [completionIdeal_succ, RingHom.mem_ker, ← ha, Ideal.Quotient.eq_zero_iff_mem]
  exact ha0

/-- When the first filtration ideal contains the counit kernel, membership in the first completion
ideal is equivalent to vanishing of the completed counit. -/
theorem mem_completionIdeal_one_iff_completedCounit_eq_zero
    (hε' : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1) {x : F.completion} :
    x ∈ F.completionIdeal 1 ↔ F.completedCounit R hε x = 0 := by
  rw [← F.ker_completedCounit_eq_completionIdeal_one R hε hε', RingHom.mem_ker]

/-- When the first filtration ideal contains the counit kernel, congruence to `1` modulo the first
completion ideal is equivalent to having completed counit `1`. -/
theorem sub_one_mem_completionIdeal_one_iff_completedCounit_eq_one
    (hε' : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1) {u : F.completion} :
    u - 1 ∈ F.completionIdeal 1 ↔ F.completedCounit R hε u = 1 := by
  rw [F.mem_completionIdeal_one_iff_completedCounit_eq_zero R hε hε', map_sub, map_one, sub_eq_zero]

end Counit

section GroupLikeAndPrimitive

variable (R : Type*) {A : Type*} [CommRing R] [Ring A] [Bialgebra R A] (F : AlgFiltration A)
  (hΔ : ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
  (hε : F.ideal 1 ≤ RingHom.ker (Bialgebra.counitAlgHom R A))

private noncomputable def counitLeftAlgHom : A ⊗[R] A →ₐ[R] A :=
  (Algebra.TensorProduct.lid R A).toAlgHom.comp
    (Algebra.TensorProduct.map (Bialgebra.counitAlgHom R A) (AlgHom.id R A))

private theorem counitLeftAlgHom_eq_lid_rTensor (t : A ⊗[R] A) :
    counitLeftAlgHom R t = TensorProduct.lid R A (Coalgebra.counit.rTensor A t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b => simp [counitLeftAlgHom]
  | add x y hx hy => simp [map_add, hx, hy]

private theorem counitLeftAlgHom_comp_comulAlgHom :
    (counitLeftAlgHom (R := R) (A := A)).comp (Bialgebra.comulAlgHom R A) = AlgHom.id R A := by
  apply AlgHom.ext
  intro a
  rw [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, counitLeftAlgHom_eq_lid_rTensor,
    Coalgebra.rTensor_counit_comul, TensorProduct.lid_tmul, one_smul, AlgHom.id_apply]

include hε in
private theorem tensorProduct_ideal_le_comap_counitLeftAlgHom (k : ℕ) :
    (F.tensorProduct R F).ideal k ≤ (F.ideal k).comap (counitLeftAlgHom (R := R) (A := A)) := by
  have bound : tensorFiltrationTail (fun n => (F.ideal n).restrictScalars R)
      (fun n => (F.ideal n).restrictScalars R) k ≤
      ((F.ideal k).restrictScalars R).comap
        (counitLeftAlgHom (R := R) (A := A)).toLinearMap := by
    refine (tensorFiltrationTail_le_iff _ _).mpr fun i j hij a ha b hb => ?_
    simp only [Submodule.mem_comap, AlgHom.toLinearMap_apply, Submodule.restrictScalars_mem,
      counitLeftAlgHom, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
      Bialgebra.counitAlgHom_apply, AlgHom.id_apply, AlgEquiv.toAlgHom_apply,
      Algebra.TensorProduct.lid_tmul]
    cases i with
    | zero =>
      rw [Algebra.smul_def]
      exact (F.ideal k).mul_mem_left _ (F.antitone (by omega : k ≤ j) hb)
    | succ i =>
      have ha1 : a ∈ F.ideal 1 := F.antitone (Nat.succ_le_succ (Nat.zero_le i)) ha
      have ha0 : Coalgebra.counit (R := R) a = 0 := by
        simpa only [Bialgebra.counitAlgHom_apply] using RingHom.mem_ker.mp (hε ha1)
      simp [ha0]
  intro t ht
  exact bound ((F.mem_tensorProduct_ideal_iff R F).mp ht)

private noncomputable def counitLeftCompletion :
    (F.tensorProduct R F).completion →ₐ[R] F.completion :=
  (F.tensorProduct R F).mapCompletionₐ F (counitLeftAlgHom (R := R) (A := A)) id monotone_id
    fun k => F.tensorProduct_ideal_le_comap_counitLeftAlgHom R hε (k + 1)

private theorem counitLeftCompletion_completedComul (x : F.completion) :
    F.counitLeftCompletion R hε (F.completedComul R hΔ x) = x := by
  apply F.completion_ext
  intro k
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection k x)
  have hx : (F.tensorProduct R F).projection k (F.completedComul R hΔ x) =
      Ideal.Quotient.mk ((F.tensorProduct R F).ideal (k + 1)) (Coalgebra.comul a) := by
    rw [projection_completedComul, ← ha]
    rfl
  have hc : F.projection k (F.counitLeftCompletion R hε (F.completedComul R hΔ x)) =
      Ideal.quotientMapₐ (F.ideal (k + 1)) (counitLeftAlgHom (R := R) (A := A))
        (F.tensorProduct_ideal_le_comap_counitLeftAlgHom R hε (k + 1))
        ((F.tensorProduct R F).projection k (F.completedComul R hΔ x)) :=
    (F.tensorProduct R F).projection_mapCompletionₐ F (counitLeftAlgHom (R := R) (A := A))
      id monotone_id _ k _
  rw [hc, hx]
  simpa only [Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk, ← Bialgebra.comulAlgHom_apply,
    ← AlgHom.comp_apply, counitLeftAlgHom_comp_comulAlgHom, AlgHom.id_apply] using ha

private theorem counitLeftCompletion_completedTensor (x y : F.completion) :
    F.counitLeftCompletion R hε (F.completedTensor R F x y) =
      F.completedCounit R hε x • y := by
  apply F.completion_ext
  intro k
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection k x)
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (F.projection k y)
  have ha0 : Ideal.Quotient.mk (F.ideal 1) a = F.projection 0 x := by
    simpa only [← ha, Ideal.Quotient.factor_mk] using F.factor_projection (Nat.zero_le k) x
  have hproj : F.projection k (F.counitLeftCompletion R hε (F.completedTensor R F x y)) =
      Ideal.quotientMapₐ (F.ideal (k + 1)) (counitLeftAlgHom (R := R) (A := A))
        (F.tensorProduct_ideal_le_comap_counitLeftAlgHom R hε (k + 1))
        ((F.tensorProduct R F).projection k (F.completedTensor R F x y)) :=
    (F.tensorProduct R F).projection_mapCompletionₐ F (counitLeftAlgHom (R := R) (A := A))
      id monotone_id _ k (F.completedTensor R F x y)
  have hrhs : F.projection k (F.completedCounit R hε x • y) =
      F.completedCounit R hε x • F.projection k y := by
    rw [← F.projectionₐ_apply (R := R), map_smul, F.projectionₐ_apply]
  rw [hproj, hrhs, F.projection_completedTensor_of_representatives R F k x y a b ha hb,
    F.completedCounit_eq_of_mk_eq_projection_zero R hε ha0, ← hb]
  simp [counitLeftAlgHom]

/-- The completed primitive comultiplication identity already forces the completed counit to
vanish, over any commutative base ring. -/
theorem completedCounit_eq_zero_of_completedComul_eq {x : F.completion}
    (hx : F.completedComul R hΔ x = F.completedTensor R F x 1 + F.completedTensor R F 1 x) :
    F.completedCounit R hε x = 0 := by
  have h := congrArg (F.counitLeftCompletion R hε) hx
  rw [F.counitLeftCompletion_completedComul R hΔ hε, map_add,
    F.counitLeftCompletion_completedTensor R hε, F.counitLeftCompletion_completedTensor R hε,
    map_one, one_smul] at h
  have hscalar : F.completedCounit R hε x • (1 : F.completion) = 0 := by
    simpa using sub_eq_zero.mpr h.symm
  have hc := congrArg (F.completedCounit R hε) hscalar
  simpa only [map_smul, map_one, smul_eq_mul, mul_one, map_zero] using hc

/-- An element `u` of a completed filtered bialgebra is group-like when `ε̂ u = 1` and
`Δ̂ u = u ⊗̂ u`. -/
@[mk_iff]
structure IsCompletedGroupLike (u : F.completion) : Prop where
  /-- A completed group-like element has completed counit `1`. -/
  completedCounit_eq_one : F.completedCounit R hε u = 1
  /-- A completed group-like element has completed comultiplication `u ⊗̂ u`. -/
  completedComul_eq : F.completedComul R hΔ u = F.completedTensor R F u u

attribute [simp] IsCompletedGroupLike.completedCounit_eq_one IsCompletedGroupLike.completedComul_eq

namespace IsCompletedGroupLike

variable {R F hΔ hε}

/-- `1` is group-like in the completion. -/
@[simp]
theorem one : F.IsCompletedGroupLike R hΔ hε 1 where
  completedCounit_eq_one := map_one _
  completedComul_eq := by simp

/-- Completed group-like elements are closed under multiplication. -/
theorem mul {u v : F.completion} (hu : F.IsCompletedGroupLike R hΔ hε u)
    (hv : F.IsCompletedGroupLike R hΔ hε v) :
    F.IsCompletedGroupLike R hΔ hε (u * v) where
  completedCounit_eq_one := by simp [hu.completedCounit_eq_one, hv.completedCounit_eq_one]
  completedComul_eq := by
    rw [map_mul, hu.completedComul_eq, hv.completedComul_eq, F.completedTensor_mul R F]

/-- Completed group-like elements are closed under natural powers. -/
theorem pow {u : F.completion} (hu : F.IsCompletedGroupLike R hΔ hε u) (n : ℕ) :
    F.IsCompletedGroupLike R hΔ hε (u ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => simpa [pow_succ] using ih.mul hu

/-- A two-sided multiplicative inverse of a completed group-like element is also completed
group-like. -/
theorem of_mul_eq_one {u v : F.completion} (huv : u * v = 1) (hvu : v * u = 1)
    (hu : F.IsCompletedGroupLike R hΔ hε u) :
    F.IsCompletedGroupLike R hΔ hε v where
  completedCounit_eq_one := left_inv_eq_right_inv
    (a := F.completedCounit R hε u)
    (by rw [← map_mul, hvu, map_one])
    (by rw [hu.completedCounit_eq_one, mul_one])
  completedComul_eq := left_inv_eq_right_inv
    (a := F.completedComul R hΔ u)
    (by rw [← map_mul, hvu, map_one])
    (by rw [hu.completedComul_eq, ← F.completedTensor_mul R F, huv,
      F.completedTensor_one_left R F, map_one])

/-- When the first filtration ideal contains the counit kernel, every completed group-like element
is congruent to `1` modulo the first completion ideal. -/
theorem sub_one_mem {u : F.completion}
    (hε' : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1)
    (hu : F.IsCompletedGroupLike R hΔ hε u) :
    u - 1 ∈ F.completionIdeal 1 :=
  (F.sub_one_mem_completionIdeal_one_iff_completedCounit_eq_one R hε hε').mpr
    hu.completedCounit_eq_one

end IsCompletedGroupLike

/-- The completed group-like elements form a submonoid of the completion. -/
def completedGroupLikeSubmonoid : Submonoid F.completion where
  carrier := {u | F.IsCompletedGroupLike R hΔ hε u}
  one_mem' := .one
  mul_mem' := .mul

@[simp]
theorem mem_completedGroupLikeSubmonoid {u : F.completion} :
    u ∈ F.completedGroupLikeSubmonoid R hΔ hε ↔ F.IsCompletedGroupLike R hΔ hε u := Iff.rfl

/-- An ordinary group-like element maps to a completed group-like element. -/
theorem isCompletedGroupLike_toCompletion {a : A} (ha : IsGroupLikeElem R a) :
    F.IsCompletedGroupLike R hΔ hε (F.toCompletion a) where
  completedCounit_eq_one := by simp [ha.counit_eq_one]
  completedComul_eq := by simp [ha.comul_eq_tmul_self]

/-- An element `x` of a completed filtered bialgebra is primitive when `ε̂ x = 0` and
`Δ̂ x = x ⊗̂ 1 + 1 ⊗̂ x`. -/
@[mk_iff]
structure IsCompletedPrimitive (x : F.completion) : Prop where
  /-- A completed primitive element has completed counit `0`. -/
  completedCounit_eq_zero : F.completedCounit R hε x = 0
  /-- A completed primitive element has completed comultiplication `x ⊗̂ 1 + 1 ⊗̂ x`. -/
  completedComul_eq :
    F.completedComul R hΔ x = F.completedTensor R F x 1 + F.completedTensor R F 1 x

attribute [simp] IsCompletedPrimitive.completedCounit_eq_zero IsCompletedPrimitive.completedComul_eq

/-- Because the counit condition follows automatically from the comultiplication equation, an
element is completed primitive if and only if `Δ̂ x = x ⊗̂ 1 + 1 ⊗̂ x`. -/
theorem isCompletedPrimitive_iff_completedComul_eq {x : F.completion} :
    F.IsCompletedPrimitive R hΔ hε x ↔
      F.completedComul R hΔ x = F.completedTensor R F x 1 + F.completedTensor R F 1 x :=
  ⟨IsCompletedPrimitive.completedComul_eq,
    fun hx => ⟨F.completedCounit_eq_zero_of_completedComul_eq R hΔ hε hx, hx⟩⟩

namespace IsCompletedPrimitive

variable {R F hΔ hε}

/-- `0` is completed primitive. -/
@[simp]
theorem zero : F.IsCompletedPrimitive R hΔ hε 0 where
  completedCounit_eq_zero := map_zero _
  completedComul_eq := by simp

/-- Completed primitive elements are closed under addition. -/
theorem add {x y : F.completion} (hx : F.IsCompletedPrimitive R hΔ hε x)
    (hy : F.IsCompletedPrimitive R hΔ hε y) :
    F.IsCompletedPrimitive R hΔ hε (x + y) := by
  refine (F.isCompletedPrimitive_iff_completedComul_eq R hΔ hε).mpr ?_
  simp only [map_add, hx.completedComul_eq, hy.completedComul_eq, LinearMap.add_apply]
  abel

/-- Completed primitive elements are closed under negation. -/
theorem neg {x : F.completion} (hx : F.IsCompletedPrimitive R hΔ hε x) :
    F.IsCompletedPrimitive R hΔ hε (-x) := by
  refine (F.isCompletedPrimitive_iff_completedComul_eq R hΔ hε).mpr ?_
  simp only [map_neg, hx.completedComul_eq, LinearMap.neg_apply]
  abel

/-- Completed primitive elements are closed under subtraction. -/
theorem sub {x y : F.completion} (hx : F.IsCompletedPrimitive R hΔ hε x)
    (hy : F.IsCompletedPrimitive R hΔ hε y) :
    F.IsCompletedPrimitive R hΔ hε (x - y) :=
  sub_eq_add_neg x y ▸ hx.add hy.neg

/-- Completed primitive elements are closed under `R`-scalar multiplication. -/
theorem smul {x : F.completion} (hx : F.IsCompletedPrimitive R hΔ hε x) (r : R) :
    F.IsCompletedPrimitive R hΔ hε (r • x) := by
  refine (F.isCompletedPrimitive_iff_completedComul_eq R hΔ hε).mpr ?_
  simp [hx.completedComul_eq, smul_add]

/-- Completed primitive elements are closed under the associative commutator `x * y - y * x`. -/
theorem commutator {x y : F.completion} (hx : F.IsCompletedPrimitive R hΔ hε x)
    (hy : F.IsCompletedPrimitive R hΔ hε y) :
    F.IsCompletedPrimitive R hΔ hε (x * y - y * x) := by
  refine (F.isCompletedPrimitive_iff_completedComul_eq R hΔ hε).mpr ?_
  have hxy := F.commute_includeLeftCompletion_includeRightCompletion R F x y
  have hyx := F.commute_includeLeftCompletion_includeRightCompletion R F y x
  rw [map_sub, map_mul, map_mul, hx.completedComul_eq, hy.completedComul_eq]
  simp only [completedTensor_one_right, completedTensor_one_left]
  simp only [add_mul, mul_add, map_sub, map_mul]
  rw [hxy.eq, hyx.eq]
  abel

/-- When the first filtration ideal contains the counit kernel, every completed primitive element
lies in the first completion ideal. -/
theorem mem_completionIdeal_one {x : F.completion}
    (hε' : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1)
    (hx : F.IsCompletedPrimitive R hΔ hε x) :
    x ∈ F.completionIdeal 1 :=
  (F.mem_completionIdeal_one_iff_completedCounit_eq_zero R hε hε').mpr hx.completedCounit_eq_zero

end IsCompletedPrimitive

/-- The `R`-submodule of completed primitive elements. -/
def completedPrimitiveSubmodule : Submodule R F.completion where
  carrier := {x | F.IsCompletedPrimitive R hΔ hε x}
  zero_mem' := .zero
  add_mem' := .add
  smul_mem' r _ hx := hx.smul r

@[simp]
theorem mem_completedPrimitiveSubmodule {x : F.completion} :
    x ∈ F.completedPrimitiveSubmodule R hΔ hε ↔ F.IsCompletedPrimitive R hΔ hε x := Iff.rfl

/-- An ordinary primitive element maps to a completed primitive element. -/
theorem isCompletedPrimitive_toCompletion {a : A} (ha : Bialgebra.IsPrimitiveElem R a) :
    F.IsCompletedPrimitive R hΔ hε (F.toCompletion a) := by
  refine (F.isCompletedPrimitive_iff_completedComul_eq R hΔ hε).mpr ?_
  rw [completedComul_toCompletion, ha.comul_eq_tmul_add_tmul, map_add,
    ← F.completedTensor_toCompletion R F, ← F.completedTensor_toCompletion R F, map_one, add_comm]

end GroupLikeAndPrimitive

section Exp

variable (R : Type*) {A : Type*} [CommRing R] [Ring A] [Bialgebra R A]
  [Algebra ℚ A] [SMulCommClass R ℚ A] (F : AlgFiltration A)
  (hΔ : ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
  (hε : F.ideal 1 ≤ RingHom.ker (Bialgebra.counitAlgHom R A))

/-- The completed left tensor inclusion commutes with `completedExp`. -/
@[simp]
theorem includeLeftCompletion_completedExp (x : F.completionIdeal 1) :
    F.includeLeftCompletion R F (F.completedExp x) =
      (F.tensorProduct R F).completedExp
        ⟨F.includeLeftCompletion R F x,
          F.includeLeftCompletion_mem_completionIdeal R F x.property⟩ := by
  apply (F.tensorProduct R F).completion_ext
  intro k
  rw [projection_includeLeftCompletion, projection_completedExp, projection_completedExp,
    projection_includeLeftCompletion]
  exact (F.isNilpotent_projection x.property k).map_exp _

/-- The completed right tensor inclusion commutes with `completedExp`. -/
@[simp]
theorem includeRightCompletion_completedExp (x : F.completionIdeal 1) :
    F.includeRightCompletion R F (F.completedExp x) =
      (F.tensorProduct R F).completedExp
        ⟨F.includeRightCompletion R F x,
          F.includeRightCompletion_mem_completionIdeal R F x.property⟩ := by
  apply (F.tensorProduct R F).completion_ext
  intro k
  rw [projection_includeRightCompletion, projection_completedExp, projection_completedExp,
    projection_includeRightCompletion]
  exact (F.isNilpotent_projection x.property k).map_exp _

/-- Completed comultiplication commutes with `completedExp`. -/
@[simp]
theorem completedComul_completedExp (x : F.completionIdeal 1) :
    F.completedComul R hΔ (F.completedExp x) =
      (F.tensorProduct R F).completedExp
        ⟨F.completedComul R hΔ x, F.completedComul_mem_completionIdeal R hΔ x.property⟩ := by
  apply (F.tensorProduct R F).completion_ext
  intro k
  rw [projection_completedComul, projection_completedExp, projection_completedExp,
    projection_completedComul]
  exact (F.isNilpotent_projection x.property k).map_exp _

/-- Completed comultiplication commutes with `completedLog`. -/
@[simp]
theorem completedComul_completedLog (u : {u : F.completion // u - 1 ∈ F.completionIdeal 1}) :
    F.completedComul R hΔ (F.completedLog u) =
      (F.tensorProduct R F).completedLog
        ⟨F.completedComul R hΔ u, by
          simpa only [map_sub, map_one] using
            F.completedComul_mem_completionIdeal R hΔ u.property⟩ := by
  apply (F.tensorProduct R F).completion_ext
  intro k
  rw [projection_completedComul, projection_completedLog, projection_completedLog,
    projection_completedComul]
  have hu : IsNilpotent (F.projection k u - 1) := by
    simpa only [map_sub, map_one] using F.isNilpotent_projection u.property k
  exact hu.map_log _

/-- The completed exponential of a completed primitive element in the first completion ideal is
completed group-like. -/
theorem IsCompletedPrimitive.completedExp {x : F.completionIdeal 1}
    (hx : F.IsCompletedPrimitive R hΔ hε x.val) :
    F.IsCompletedGroupLike R hΔ hε (F.completedExp x) where
  completedCounit_eq_one :=
    F.completedCounit_eq_one_of_sub_one_mem R hε (F.completedExp_sub_one_mem x)
  completedComul_eq := by
    let xl : (F.tensorProduct R F).completionIdeal 1 :=
      ⟨F.includeLeftCompletion R F x, F.includeLeftCompletion_mem_completionIdeal R F x.property⟩
    let xr : (F.tensorProduct R F).completionIdeal 1 :=
      ⟨F.includeRightCompletion R F x, F.includeRightCompletion_mem_completionIdeal R F x.property⟩
    have hsum : (⟨F.completedComul R hΔ x,
        F.completedComul_mem_completionIdeal R hΔ x.property⟩ :
          (F.tensorProduct R F).completionIdeal 1) = xl + xr := by
      apply Subtype.ext
      simpa [xl, xr] using hx.completedComul_eq
    rw [F.completedComul_completedExp R hΔ x, hsum,
      (F.tensorProduct R F).completedExp_add xl xr
        (F.commute_includeLeftCompletion_includeRightCompletion R F x x),
      ← F.includeLeftCompletion_completedExp R x,
      ← F.includeRightCompletion_completedExp R x, ← F.completedTensor_apply R F]

/-- The completed logarithm of a completed group-like element congruent to `1` modulo the first
completion ideal is completed primitive. -/
theorem IsCompletedGroupLike.completedLog
    {u : {u : F.completion // u - 1 ∈ F.completionIdeal 1}}
    (hu : F.IsCompletedGroupLike R hΔ hε u.val) :
    F.IsCompletedPrimitive R hΔ hε (F.completedLog u) := by
  refine (F.isCompletedPrimitive_iff_completedComul_eq R hΔ hε).mpr ?_
  let x : F.completionIdeal 1 := ⟨F.completedLog u, F.completedLog_mem u⟩
  have hxu : F.completedExp x = u.val := F.completedExp_completedLog u
  let xl : (F.tensorProduct R F).completionIdeal 1 :=
    ⟨F.includeLeftCompletion R F x, F.includeLeftCompletion_mem_completionIdeal R F x.property⟩
  let xr : (F.tensorProduct R F).completionIdeal 1 :=
    ⟨F.includeRightCompletion R F x, F.includeRightCompletion_mem_completionIdeal R F x.property⟩
  let dx : (F.tensorProduct R F).completionIdeal 1 :=
    ⟨F.completedComul R hΔ x, F.completedComul_mem_completionIdeal R hΔ x.property⟩
  have hexp : (F.tensorProduct R F).completedExp dx =
      (F.tensorProduct R F).completedExp (xl + xr) := by
    rw [← F.completedComul_completedExp R hΔ x, hxu, hu.completedComul_eq,
      (F.tensorProduct R F).completedExp_add xl xr
        (F.commute_includeLeftCompletion_includeRightCompletion R F x x),
      ← F.includeLeftCompletion_completedExp R x,
      ← F.includeRightCompletion_completedExp R x, hxu, ← F.completedTensor_apply R F]
  have hlog := congrArg (fun v => (F.tensorProduct R F).completedLog v)
    (Subtype.ext hexp :
      (⟨(F.tensorProduct R F).completedExp dx,
          (F.tensorProduct R F).completedExp_sub_one_mem dx⟩ :
        {v : (F.tensorProduct R F).completion //
          v - 1 ∈ (F.tensorProduct R F).completionIdeal 1}) =
      ⟨(F.tensorProduct R F).completedExp (xl + xr),
          (F.tensorProduct R F).completedExp_sub_one_mem (xl + xr)⟩)
  rw [(F.tensorProduct R F).completedLog_completedExp,
    (F.tensorProduct R F).completedLog_completedExp] at hlog
  simpa [dx, xl, xr, x] using hlog

/-- For `x` in the first completion ideal, `completedExp x` is completed group-like if and only if
`x` is completed primitive. -/
@[simp]
theorem isCompletedGroupLike_completedExp_iff (x : F.completionIdeal 1) :
    F.IsCompletedGroupLike R hΔ hε (F.completedExp x) ↔
      F.IsCompletedPrimitive R hΔ hε x.val :=
  ⟨fun h => by
      simpa using h.completedLog R F hΔ hε
        (u := ⟨F.completedExp x, F.completedExp_sub_one_mem x⟩),
    fun h => h.completedExp R F hΔ hε⟩

/-- For `u` congruent to `1` modulo the first completion ideal, `completedLog u` is completed
primitive if and only if `u` is completed group-like. -/
@[simp]
theorem isCompletedPrimitive_completedLog_iff
    (u : {u : F.completion // u - 1 ∈ F.completionIdeal 1}) :
    F.IsCompletedPrimitive R hΔ hε (F.completedLog u) ↔
      F.IsCompletedGroupLike R hΔ hε u.val :=
  ⟨fun h => by
      simpa using h.completedExp R F hΔ hε (x := ⟨F.completedLog u, F.completedLog_mem u⟩),
    fun h => h.completedLog R F hΔ hε⟩

/-- `completedExp` and `completedLog` exchange completed primitive elements of the first completion
ideal and completed group-like elements congruent to `1` modulo the first completion ideal. -/
noncomputable def completedExpPrimitiveEquiv :
    {x : F.completionIdeal 1 // F.IsCompletedPrimitive R hΔ hε x.val} ≃
      {u : {u : F.completion // u - 1 ∈ F.completionIdeal 1} //
        F.IsCompletedGroupLike R hΔ hε u.val} where
  toFun x := ⟨⟨F.completedExp x.1, F.completedExp_sub_one_mem x.1⟩, x.2.completedExp R F hΔ hε⟩
  invFun u := ⟨⟨F.completedLog u.1, F.completedLog_mem u.1⟩, u.2.completedLog R F hΔ hε⟩
  left_inv x := Subtype.ext (Subtype.ext (F.completedLog_completedExp x.1))
  right_inv u := Subtype.ext (Subtype.ext (F.completedExp_completedLog u.1))

@[simp]
theorem coe_completedExpPrimitiveEquiv
    (x : {x : F.completionIdeal 1 // F.IsCompletedPrimitive R hΔ hε x.val}) :
    ((F.completedExpPrimitiveEquiv R hΔ hε x).val : F.completion) = F.completedExp x.val := (rfl)

@[simp]
theorem coe_completedExpPrimitiveEquiv_symm
    (u : {u : {u : F.completion // u - 1 ∈ F.completionIdeal 1} //
      F.IsCompletedGroupLike R hΔ hε u.val}) :
    ((F.completedExpPrimitiveEquiv R hΔ hε).symm u).val.val = F.completedLog u.val := (rfl)

/-- When the first filtration ideal contains the counit kernel, `completedExp` and `completedLog`
exchange all completed primitive elements and all completed group-like elements. -/
noncomputable def completedExpPrimitiveEquivOfKerLe
    (hε' : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1) :
    {x : F.completion // F.IsCompletedPrimitive R hΔ hε x} ≃
      {u : F.completion // F.IsCompletedGroupLike R hΔ hε u} where
  toFun x :=
    ⟨F.completedExp ⟨x.1, x.2.mem_completionIdeal_one hε'⟩,
      x.2.completedExp R F hΔ hε (x := ⟨x.1, x.2.mem_completionIdeal_one hε'⟩)⟩
  invFun u :=
    ⟨F.completedLog ⟨u.1, u.2.sub_one_mem hε'⟩,
      u.2.completedLog R F hΔ hε (u := ⟨u.1, u.2.sub_one_mem hε'⟩)⟩
  left_inv x := Subtype.ext (F.completedLog_completedExp ⟨x.1, x.2.mem_completionIdeal_one hε'⟩)
  right_inv u := Subtype.ext (F.completedExp_completedLog ⟨u.1, u.2.sub_one_mem hε'⟩)

@[simp]
theorem coe_completedExpPrimitiveEquivOfKerLe
    (hε' : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1)
    (x : {x : F.completion // F.IsCompletedPrimitive R hΔ hε x}) :
    (F.completedExpPrimitiveEquivOfKerLe R hΔ hε hε' x : F.completion) =
      F.completedExp ⟨x.1, x.2.mem_completionIdeal_one hε'⟩ := (rfl)

@[simp]
theorem coe_completedExpPrimitiveEquivOfKerLe_symm
    (hε' : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1)
    (u : {u : F.completion // F.IsCompletedGroupLike R hΔ hε u}) :
    ((F.completedExpPrimitiveEquivOfKerLe R hΔ hε hε').symm u : F.completion) =
      F.completedLog ⟨u.1, u.2.sub_one_mem hε'⟩ := (rfl)

/-- The product of two completed exponentials is congruent to `1` modulo the first completion
ideal. -/
theorem completedExp_mul_completedExp_sub_one_mem (x y : F.completionIdeal 1) :
    F.completedExp x * F.completedExp y - 1 ∈ F.completionIdeal 1 := by
  have h : F.completedExp x * F.completedExp y - 1 =
      (F.completedExp x - 1) * F.completedExp y + (F.completedExp y - 1) := by
    rw [sub_mul, one_mul, sub_add_sub_cancel]
  rw [h]
  exact add_mem ((F.completionIdeal 1).mul_mem_right _ (F.completedExp_sub_one_mem x))
    (F.completedExp_sub_one_mem y)

/-- **Completed Baker–Campbell–Hausdorff primitivity**: the completed logarithm of the product of
the exponentials of two completed primitive elements in the first completion ideal is again
completed primitive. -/
theorem isCompletedPrimitive_completedLog_completedExp_mul_completedExp
    {x y : F.completionIdeal 1}
    (hx : F.IsCompletedPrimitive R hΔ hε x.val)
    (hy : F.IsCompletedPrimitive R hΔ hε y.val) :
    F.IsCompletedPrimitive R hΔ hε
      (F.completedLog ⟨F.completedExp x * F.completedExp y,
        F.completedExp_mul_completedExp_sub_one_mem x y⟩) :=
  ((hx.completedExp R F hΔ hε).mul (hy.completedExp R F hΔ hε)).completedLog R F hΔ hε

end Exp

end TauCeti.AlgFiltration
