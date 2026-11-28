/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Length
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import TauCeti.Algebra.Algebra.Subalgebra.Pi
import TauCeti.RingTheory.CongruenceModule.Basic
import TauCeti.RingTheory.Length.Endomorphism

/-!
# Length of a relative congruence module

For a point-separating subalgebra of a finite product of a discrete valuation ring, the
congruence quotient of a lattice along a subset of points has length bounded by the sum of the
colengths of the pointwise relative congruence ideals, weighted by the corresponding ranks.
The proof filters the quotient by successively imposing vanishing at each point of the subset.

## References

This bound specializes `GlobalTheory.EtaFromCut.congMod_le_of_family` from Levent Alpöge's
Riemann hypothesis formalization.
-/

public section

open scoped BigOperators
open Submodule TauCeti

namespace Subalgebra

variable {O X : Type*} [CommRing O] {A : Subalgebra O (X → O)}

private def evalAt (A : Subalgebra O (X → O)) (x : X) : A →ₐ[O] O :=
  (Pi.evalAlgHom O (fun _ : X ↦ O) x).comp A.val

private def supportIdeal (A : Subalgebra O (X → O)) (S : Finset X) : Ideal A :=
  ⨅ x : {x // x ∉ S}, RingHom.ker (evalAt A x)

private theorem mem_supportIdeal {S : Finset X} {f : A} :
    f ∈ supportIdeal A S ↔ ∀ x ∉ S, evalAt A x f = 0 := by
  simp [supportIdeal]

private theorem mul_eq_smul_of_supported_single {x : X} {b : A}
    (hb : ∀ y ≠ x, evalAt A y b = 0) (g : A) :
    b * g = evalAt A x g • b := by
  apply Subtype.ext
  funext y
  -- `A` is a subalgebra of functions, so multiplication evaluates pointwise.
  change evalAt A y b * evalAt A y g = evalAt A x g * evalAt A y b
  by_cases hy : y = x
  · subst y
    exact mul_comm _ _
  · rw [hb y hy, zero_mul, mul_zero]

variable {M : Type*} [AddCommGroup M] [Module A M]

private theorem smul_mem_torsionBySet_vanishingOn {Z : Finset X} {g : A}
    (hg : g ∈ supportIdeal A Z) (m : M) :
    g • m ∈ torsionBySet A M {f : A | ∀ y ∈ Z, (f : X → O) y = 0} := by
  apply (mem_torsionBySet_iff _ _).mpr
  intro k
  rw [← mul_smul]
  have hz : (k : A) * g = 0 := by
    apply Subtype.ext
    funext y
    -- Evaluation of the product in `A` is pointwise multiplication.
    change evalAt A y k * evalAt A y g = 0
    by_cases hy : y ∈ Z
    · have hky : evalAt A y k = 0 := by
        simpa [evalAt] using k.property y hy
      rw [hky, zero_mul]
    · rw [mem_supportIdeal.mp hg y hy, mul_zero]
  rw [hz, zero_smul]

variable [Module O M] [IsScalarTower O A M]

private theorem mem_torsionBySet_supportIdeal_insert [DecidableEq X] [IsDomain O]
    [Module.IsTorsionFree O M] {S : Finset X} {x : X} {b : A}
    (hb : ∀ y ≠ x, evalAt A y b = 0) (hbx : evalAt A x b ≠ 0)
    {m : M} (hm : m ∈ torsionBySet A M (supportIdeal A S)) (hbm : b • m = 0) :
    m ∈ torsionBySet A M (supportIdeal A (insert x S)) := by
  rw [mem_torsionBySet_iff] at hm ⊢
  rintro ⟨g, hg⟩
  let d : A := evalAt A x b • g - evalAt A x g • b
  have hd : d ∈ supportIdeal A S := by
    apply mem_supportIdeal.mpr
    intro y hy
    simp only [d, map_sub, map_smul, smul_eq_mul]
    by_cases hyx : y = x
    · subst y
      rw [mul_comm (evalAt A x b), sub_self]
    · rw [hb y hyx, mem_supportIdeal.mp hg y (by simp [hyx, hy]), mul_zero, mul_zero, sub_self]
  have h := hm ⟨d, hd⟩
  simp only [d] at h
  rw [sub_smul, smul_assoc, smul_assoc, hbm, smul_zero, sub_zero] at h
  exact (smul_eq_zero_iff_right hbx).mp h

variable [IsDomain O] [IsDiscreteValuationRing O] [Module.Finite O M]
  [Module.IsTorsionFree O M]

private theorem length_coordinate_step [DecidableEq X] {Z S : Finset X} {x : X} (hx : x ∈ Z)
    {b : A} (hb : ∀ y ≠ x, evalAt A y b = 0) (hbx : evalAt A x b ≠ 0)
    (P : Submodule O M)
    (hP : (torsionBySet A M {f : A | ∀ y ∈ Z, (f : X → O) y = 0}).restrictScalars O ≤ P) :
    Module.length O ((torsionBySet A M (supportIdeal A S)).restrictScalars O |>.map P.mkQ) ≤
      Module.length O ((torsionBySet A M (supportIdeal A (insert x S))).restrictScalars O
        |>.map P.mkQ) +
      (Module.finrank O ((torsionBySet A M (RingHom.ker (evalAt A x))).restrictScalars O) : ℕ∞) *
        Module.length O (O ⧸ (supportIdeal A Z).map (evalAt A x)) := by
  let N := (torsionBySet A M (supportIdeal A S)).restrictScalars O
  let N' := (torsionBySet A M (supportIdeal A (insert x S))).restrictScalars O
  let E := (torsionBySet A M (RingHom.ker (evalAt A x))).restrictScalars O
  have hN : N' ≤ N := restrictScalars_mono O <| torsionBySet_le_torsionBySet_of_subset <| by
    intro g hg
    exact mem_supportIdeal.mpr fun y hy ↦
      mem_supportIdeal.mp hg y (fun h ↦ hy (Finset.mem_insert_of_mem h))
  rw [length_map_mkQ_eq_add_length_quotient P hN]
  apply add_le_add_right
  let I := (supportIdeal A Z).map (evalAt A x)
  obtain ⟨g, hg, hga⟩ := (Ideal.mem_map_iff_of_surjective _ (evalAt A x).augmentation_surjective).mp
    (IsPrincipal.generator_mem I)
  have ha : IsPrincipal.generator I ≠ 0 := by
    intro ha
    have hbZ : b ∈ supportIdeal A Z := mem_supportIdeal.mpr fun y hy ↦ hb y (fun he ↦ hy (he ▸ hx))
    have h : evalAt A x b ∈ I := Ideal.mem_map_of_mem (evalAt A x).toRingHom hbZ
    rw [← IsPrincipal.span_singleton_generator I, ha, span_zero_singleton, mem_bot] at h
    exact hbx h
  -- Multiplication by the single-coordinate function detects the next filtration step.
  let f : N →ₗ[O] E := ((Algebra.lsmul O O M b).comp N.subtype).codRestrict E <| by
    intro n
    apply (mem_torsionBySet_iff _ _).mpr
    intro k
    -- The torsion predicate acts on the underlying `M` element of `n : N`.
    change (k : A) • (b • (n : M)) = 0
    rw [← mul_smul, mul_comm, mul_eq_smul_of_supported_single hb]
    have hk : evalAt A x k = 0 := k.property
    simp [hk]
  have hk : LinearMap.ker f ≤ N'.comap N.subtype := by
    intro n hn
    apply mem_torsionBySet_supportIdeal_insert hb hbx n.property
    exact congrArg Subtype.val (LinearMap.mem_ker.mp hn)
  let K := (N' ⊔ N ⊓ P).comap N.subtype
  -- These lets abbreviate the source quotient and the scalar ideal for the generic length bound.
  change Module.length O (N ⧸ K) ≤ (Module.finrank O E : ℕ∞) * Module.length O (O ⧸ I)
  rw [← IsPrincipal.span_singleton_generator I]
  refine f.length_quotient_le_of_scalar_mem K (hk.trans (comap_mono le_sup_left)) ha fun n ↦ ?_
  -- A lift of the ideal generator acts as a scalar modulo the next step and lands in P.
  have hgn : g • (n : M) ∈ N := (torsionBySet A M (supportIdeal A S)).smul_mem g n.property
  have hgP : g • (n : M) ∈ P := hP (smul_mem_torsionBySet_vanishingOn hg (n : M))
  let gn : N := ⟨g • (n : M), hgn⟩
  have hdiff : IsPrincipal.generator I • n - gn ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    -- `f` is scalar multiplication by `b` with codomain restricted to `E`; `gn` lifts `g • n`.
    change b • (IsPrincipal.generator I • (n : M) - g • (n : M)) = 0
    rw [smul_sub, smul_comm b, ← mul_smul, mul_eq_smul_of_supported_single hb, smul_assoc,
      hga, sub_self]
  exact mem_sup.mpr ⟨_, hk hdiff, _, ⟨hgn, hgP⟩, sub_add_cancel _ _⟩

/-- For a finite torsion-free module over a DVR with an action of a point-separating
subalgebra of functions, the relative congruence quotient has length at most the sum of the
pointwise relative congruence lengths weighted by the ranks of the point eigenspaces. -/
theorem length_quot_annihilators_le_sum_rank_mul_relCongruence
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {X : Type*} [Finite X]
    (A : Subalgebra O (X → O)) (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ A, f x ≠ f y)
    {M : Type*} [AddCommGroup M] [Module O M] [Module A M] [IsScalarTower O A M]
    [Module.Finite O M] [Module.IsTorsionFree O M]
    (Z : Finset X) :
    Module.length O (M ⧸
        (Submodule.torsionBySet A M {f : A | ∀ y ∈ Z, (f : X → O) y = 0} ⊔
          Submodule.torsionBySet A M {f : A | ∀ y ∉ Z, (f : X → O) y = 0}).restrictScalars O) ≤
      ∑ π ∈ Z,
        (Module.finrank O
            ((Submodule.torsionBySet A M {f : A | (f : X → O) π = 0}).restrictScalars O) : ℕ∞) *
          Module.length O (O ⧸ Ideal.span
            ((fun f : A => (f : X → O) π) '' {f : A | ∀ y ∉ Z, (f : X → O) y = 0})) := by
  classical
  have hsupport : (supportIdeal A Z : Set A) = {f : A | ∀ y ∉ Z, (f : X → O) y = 0} :=
    Set.ext fun _ ↦ mem_supportIdeal
  let T (S : Finset X) := (torsionBySet A M (supportIdeal A S)).restrictScalars O
  let P := (torsionBySet A M {f : A | ∀ y ∈ Z, (f : X → O) y = 0}).restrictScalars O ⊔ T Z
  let term (x : X) :=
    (Module.finrank O ((torsionBySet A M (RingHom.ker (evalAt A x))).restrictScalars O) : ℕ∞) *
      Module.length O (O ⧸ (supportIdeal A Z).map (evalAt A x))
  have h (S : Finset X) (hS : S ⊆ Z) :
      Module.length O ((T ∅).map P.mkQ) ≤ Module.length O ((T S).map P.mkQ) + ∑ x ∈ S, term x := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert x S hx ih =>
      obtain ⟨b, hbA, hb, hbx⟩ := Subalgebra.exists_supported_single (S := A)
        (fun _ _ hne ↦ hsep _ _ hne) x
      have hstep := length_coordinate_step (S := S) (b := ⟨b, hbA⟩)
        (hS (Finset.mem_insert_self x S)) hb hbx P le_sup_left
      rw [Finset.sum_insert hx, ← add_assoc]
      exact (ih (Finset.subset_insert x S |>.trans hS)).trans (add_le_add_left hstep _)
  have htop : T ∅ = ⊤ := by
    have he : (supportIdeal A ∅ : Set A) = {0} := by
      ext f
      -- Membership in the coerced set unfolds to submodule membership here.
      change f ∈ supportIdeal A ∅ ↔ f = 0
      rw [mem_supportIdeal]
      exact ⟨fun hf ↦ Subtype.ext (funext fun x ↦ hf x (Finset.notMem_empty x)),
        fun hf _ _ ↦ hf ▸ map_zero _⟩
    apply eq_top_iff.mpr
    intro m _
    -- `T` is the torsion submodule with scalars restricted from `A` to `O`.
    change m ∈ torsionBySet A M (supportIdeal A ∅)
    simp [he, mem_torsionBy_iff]
  have hz : (T Z).map P.mkQ = ⊥ := by
    exact bot_unique ((Submodule.map_mono (le_sup_right : T Z ≤ P)).trans_eq P.mkQ_map_self)
  specialize h Z (Finset.Subset.refl Z)
  rw [htop, Submodule.map_top, range_mkQ, Module.length_top, hz, Module.length_bot, zero_add] at h
  rw [restrictScalars_sup, ← hsupport]
  exact h

end Subalgebra
