/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Algebraic semilinear endomorphisms

A vector satisfies a monic relation for a semilinear endomorphism if some iterate belongs to
the span of its predecessors. Algebraicity is the condition that every vector has such a
relation. This condition passes to stable submodules and stable quotients and is closed under
extensions. In the extension argument, an equation in the quotient gives a residual vector in
the submodule, where a second monic equation yields a relation for the original vector.

## References

* B. Bhatt and J. Lurie, *A Riemann–Hilbert correspondence in positive characteristic*,
  Definition 2.4.1 and Proposition 9.5.1.
-/

public section

open Function Set

namespace LinearMap

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {σ : R →+* R}

/-- A monic relation for a vector under a semilinear endomorphism expresses an iterate as a
linear combination of the preceding iterates. -/
def HasMonicRelation (F : M →ₛₗ[σ] M) (x : M) : Prop :=
  ∃ n : ℕ, F^[n] x ∈ Submodule.span R (Set.range fun i : Fin n ↦ F^[i.val] x)

/-- A semilinear endomorphism is algebraic if every vector satisfies a monic relation. -/
def IsAlgebraic (F : M →ₛₗ[σ] M) : Prop :=
  ∀ x, F.HasMonicRelation x

variable {F : M →ₛₗ[σ] M} {G : N →ₛₗ[σ] N}

/-- Algebraicity is the pointwise monic relation condition. -/
theorem isAlgebraic_iff : F.IsAlgebraic ↔ ∀ x, F.HasMonicRelation x := Iff.rfl

/-- The span formulation of a monic relation is equivalent to an equation with coefficients
indexed by the lower degrees. -/
theorem hasMonicRelation_iff_exists_sum {x : M} :
    F.HasMonicRelation x ↔ ∃ (n : ℕ) (a : Fin n → R), F^[n] x = ∑ i, a i • F^[i.val] x := by
  simp only [HasMonicRelation, Submodule.mem_span_range_iff_exists_fun, eq_comm]

/-- A map intertwining the two endomorphisms sends monic relations to monic relations. -/
theorem HasMonicRelation.map {x : M} (hx : F.HasMonicRelation x) (f : M →ₗ[R] N)
    (hf : Semiconj f F G) : G.HasMonicRelation (f x) := by
  obtain ⟨n, a, ha⟩ := hasMonicRelation_iff_exists_sum.mp hx
  refine hasMonicRelation_iff_exists_sum.mpr ⟨n, a, ?_⟩
  simpa only [(hf.iterate_right _).eq, map_sum, map_smul] using congrArg f ha

/-- An injective intertwining map reflects monic relations. -/
theorem HasMonicRelation.of_map {x : M} (f : M →ₗ[R] N) (hf : Semiconj f F G)
    (hi : Injective f) (hx : G.HasMonicRelation (f x)) : F.HasMonicRelation x := by
  obtain ⟨n, a, ha⟩ := hasMonicRelation_iff_exists_sum.mp hx
  refine hasMonicRelation_iff_exists_sum.mpr ⟨n, a, hi ?_⟩
  simpa only [(hf.iterate_right _).eq, map_sum, map_smul] using ha

/-- A surjective intertwining map transfers algebraicity to the target endomorphism. -/
theorem IsAlgebraic.of_surjective (hF : F.IsAlgebraic) (f : M →ₗ[R] N)
    (hf : Semiconj f F G) (hs : Surjective f) : G.IsAlgebraic := by
  intro y
  obtain ⟨x, rfl⟩ := hs y
  exact (hF x).map f hf

/-- An injective intertwining map transfers algebraicity to the source endomorphism. -/
theorem IsAlgebraic.of_injective (hG : G.IsAlgebraic) (f : M →ₗ[R] N)
    (hf : Semiconj f F G) (hi : Injective f) : F.IsAlgebraic :=
  fun x ↦ HasMonicRelation.of_map f hf hi (hG (f x))

/-- Every endomorphism of the zero module is algebraic. -/
theorem isAlgebraic_of_subsingleton [Subsingleton M] (F : M →ₛₗ[σ] M) : F.IsAlgebraic :=
  fun _ ↦ hasMonicRelation_iff_exists_sum.mpr ⟨0, Fin.elim0, Subsingleton.elim _ _⟩

private theorem iterate_residual (x : M) {n : ℕ} (a : Fin n → R) (j : ℕ) :
    F^[j] (F^[n] x - ∑ i, a i • F^[i.val] x) =
      F^[j + n] x - ∑ i, σ^[j] (a i) • F^[j + i.val] x := by
  induction j with
  | zero => simp
  | succ j ih =>
    simp only [Function.iterate_succ_apply' _ j, ih, map_sub, map_sum, map_smulₛₗ,
      Nat.succ_add, Function.iterate_succ_apply']

/-- A monic relation for the residual of another monic expression gives a monic relation for
the original vector. -/
theorem HasMonicRelation.of_residual {x : M} {n : ℕ} (a : Fin n → R)
    (h : F.HasMonicRelation (F^[n] x - ∑ i, a i • F^[i.val] x)) : F.HasMonicRelation x := by
  obtain ⟨m, b, hb⟩ := hasMonicRelation_iff_exists_sum.mp h
  simp only [iterate_residual] at hb
  refine ⟨m + n, ?_⟩
  let P := Submodule.span R (Set.range fun i : Fin (m + n) ↦ F^[i.val] x)
  have hmem (k : ℕ) (hk : k < m + n) : F^[k] x ∈ P :=
    Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩
  have hsum (j : ℕ) (hj : j ≤ m) : (∑ i, σ^[j] (a i) • F^[j + i.val] x) ∈ P :=
    Submodule.sum_mem P fun i _ ↦ P.smul_mem _ (hmem _ (by omega))
  have hrhs : (∑ j, b j • (F^[j.val + n] x -
      ∑ i, σ^[j.val] (a i) • F^[j.val + i.val] x)) ∈ P :=
    Submodule.sum_mem P fun j _ ↦
      P.smul_mem _ (P.sub_mem (hmem _ (by omega)) (hsum _ j.isLt.le))
  exact (sub_add_cancel (F^[m + n] x) _ ▸ P.add_mem (hb.symm ▸ hrhs) (hsum m le_rfl))

/-- Algebraicity is preserved and reflected by passage to a stable submodule together with
its quotient. -/
theorem isAlgebraic_iff_restrict_and_mapQ (P : Submodule R M) (hP : MapsTo F P P) :
    F.IsAlgebraic ↔ (F.restrict hP).IsAlgebraic ∧ (P.mapQ P F (fun _ hx ↦ hP hx)).IsAlgebraic := by
  let F₁ := F.restrict hP
  let F₂ := P.mapQ P F (fun _ hx ↦ hP hx)
  have hi : Semiconj P.subtype F₁ F := fun _ ↦ rfl
  have hq : Semiconj P.mkQ F F₂ := fun x ↦ (Submodule.mapQ_apply P P F x).symm
  -- Name both induced maps so the iterate identity and the quotient relation use the same map.
  change F.IsAlgebraic ↔ F₁.IsAlgebraic ∧ F₂.IsAlgebraic
  refine ⟨fun h ↦ ⟨h.of_injective P.subtype hi P.subtype_injective,
    h.of_surjective P.mkQ hq P.mkQ_surjective⟩, ?_⟩
  rintro ⟨h₁, h₂⟩ x
  obtain ⟨n, a, ha⟩ := hasMonicRelation_iff_exists_sum.mp (h₂ (P.mkQ x))
  have hr : F^[n] x - ∑ i, a i • F^[i.val] x ∈ P := by
    rw [← Submodule.ker_mkQ P, LinearMap.mem_ker]
    simp only [map_sub, map_sum, map_smul, (hq.iterate_right _).eq, ha, sub_self]
  exact HasMonicRelation.of_residual a ((h₁ ⟨_, hr⟩).map P.subtype hi)

/-- The map induced by a semilinear endomorphism on the quotient of a stable submodule
`P` by its intersection with another stable submodule `Q`. -/
def subquotientMap (F : M →ₛₗ[σ] M) (P Q : Submodule R M)
    (hP : MapsTo F P P) (hQ : MapsTo F Q Q) :
    (P ⧸ Q.comap P.subtype) →ₛₗ[σ] (P ⧸ Q.comap P.subtype) :=
  (Q.comap P.subtype).mapQ _ (F.restrict hP) fun x hx ↦ hQ (x := x.val) hx

@[simp]
theorem subquotientMap_mk (P Q : Submodule R M)
    (hP : MapsTo F P P) (hQ : MapsTo F Q Q) (x : P) :
    F.subquotientMap P Q hP hQ (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (F.restrict hP x) :=
  (rfl)

/-- An algebraic endomorphism induces an algebraic endomorphism on each stable subquotient. -/
theorem IsAlgebraic.subquotientMap (h : F.IsAlgebraic) (P Q : Submodule R M)
    (hP : MapsTo F P P) (hQ : MapsTo F Q Q) : (F.subquotientMap P Q hP hQ).IsAlgebraic := by
  have h₁ := ((isAlgebraic_iff_restrict_and_mapQ P hP).mp h).1
  exact h₁.of_surjective (Q.comap P.subtype).mkQ
    (fun x ↦ (subquotientMap_mk P Q hP hQ x).symm) (Q.comap P.subtype).mkQ_surjective

/-- The induced map on a stable subquotient is bijective if the endomorphism is surjective
on the numerator and reflects membership in the denominator within the numerator. -/
theorem bijective_subquotientMap (P Q : Submodule R M)
    (hP : MapsTo F P P) (hQ : MapsTo F Q Q)
    (hs : SurjOn F P P) (hi : ∀ x ∈ P, F x ∈ Q → x ∈ Q) :
    Bijective (F.subquotientMap P Q hP hQ) := by
  refine ⟨?_, ?_⟩
  · have he : (Q.comap P.subtype).comap (F.restrict hP) = Q.comap P.subtype := by
      ext x
      simpa only [Submodule.mem_comap, Submodule.subtype_apply, coe_restrict_apply] using
        ⟨hi x x.property, fun h ↦ hQ h⟩
    apply ker_eq_bot.mp
    exact (Submodule.ker_mapQ _ _ _ _).trans
      ((congrArg (Submodule.map (Q.comap P.subtype).mkQ) he).trans (Submodule.mkQ_map_self _))
  · intro y
    obtain ⟨x, rfl⟩ := (Q.comap P.subtype).mkQ_surjective y
    obtain ⟨z, hz, hzF⟩ := hs x.property
    exact ⟨(Q.comap P.subtype).mkQ ⟨z, hz⟩, by
      rw [Submodule.mkQ_apply, subquotientMap_mk]
      exact congrArg (Q.comap P.subtype).mkQ (Subtype.ext hzF)⟩

/-- If the successive quotients of a finite descending stable filtration are algebraic,
then the restriction to its initial submodule is algebraic. -/
theorem isAlgebraic_restrict_of_filtration (P : ℕ → Submodule R M)
    (hP : ∀ i, MapsTo F (P i) (P i)) (hdesc : Antitone P) {n : ℕ} (hbot : P n = ⊥)
    (halg : ∀ i < n, (F.subquotientMap (P i) (P (i + 1)) (hP i) (hP (i + 1))).IsAlgebraic) :
    (F.restrict (hP 0)).IsAlgebraic := by
  let Fᵢ (i : ℕ) := F.restrict (hP i)
  have hbase : (Fᵢ n).IsAlgebraic := by
    have : Subsingleton (P n) := hbot ▸ inferInstance
    exact isAlgebraic_of_subsingleton _
  refine Nat.decreasingInduction (motive := fun i _ ↦ (Fᵢ i).IsAlgebraic)
    (fun i hi ih ↦ ?_) hbase (Nat.zero_le n)
  let Q := (P (i + 1)).comap (P i).subtype
  have hQ : MapsTo (Fᵢ i) Q Q := fun x hx ↦ hP (i + 1) (x := x.val) hx
  let e := Submodule.comapSubtypeEquivOfLe (hdesc (Nat.le_succ i))
  exact (isAlgebraic_iff_restrict_and_mapQ Q hQ).mpr
    ⟨ih.of_injective e.toLinearMap (fun _ ↦ rfl) e.injective, halg i hi⟩

section FixedScalar

open scoped Pointwise

variable {A V : Type*} [CommRing A] [AddCommGroup V] [Module A V] {τ : A →+* A}

/-- The image of multiplication by a fixed scalar is stable under a semilinear endomorphism. -/
theorem mapsTo_smul_top_of_fixed (f : V →ₛₗ[τ] V) {a : A} (ha : τ a = a) :
    MapsTo f (a • (⊤ : Submodule A V)) (a • (⊤ : Submodule A V)) := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
  rw [map_smulₛₗ, ha]
  exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

/-- A surjective semilinear endomorphism is surjective on the image of multiplication
by a fixed scalar. -/
theorem surjOn_smul_top_of_fixed (f : V →ₛₗ[τ] V) (hf : Surjective f) {a : A} (ha : τ a = a) :
    SurjOn f (a • (⊤ : Submodule A V)) (a • (⊤ : Submodule A V)) := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
  obtain ⟨z, rfl⟩ := hf y
  exact ⟨a • z, Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top, by rw [map_smulₛₗ, ha]⟩

/-- The submodule annihilated by a fixed scalar is stable under a semilinear endomorphism. -/
theorem mapsTo_ker_smul_of_fixed (f : V →ₛₗ[τ] V) {a : A} (ha : τ a = a) :
    MapsTo f (ker (DistribSMul.toLinearMap A V a)) (ker (DistribSMul.toLinearMap A V a)) := by
  intro x hx
  have hz : a • x = 0 := LinearMap.mem_ker.mp hx
  have hfz : f (a • x) = 0 := by rw [hz, map_zero]
  apply LinearMap.mem_ker.mpr
  simpa only [DistribSMul.toLinearMap_apply, map_smulₛₗ, ha] using hfz

/-- For a fixed nilpotent scalar, algebraicity can be checked on the submodule it annihilates. -/
theorem isAlgebraic_iff_restrict_ker_smul_of_isNilpotent (f : V →ₛₗ[τ] V)
    {a : A} (ha : τ a = a) (hnil : IsNilpotent a) :
    f.IsAlgebraic ↔ (f.restrict (f.mapsTo_ker_smul_of_fixed ha)).IsAlgebraic := by
  let K := ker (DistribSMul.toLinearMap A V a)
  let fK := f.restrict (f.mapsTo_ker_smul_of_fixed ha)
  have hKi : Semiconj K.subtype fK f := fun _ ↦ rfl
  refine ⟨fun h ↦ h.of_injective K.subtype hKi K.subtype_injective, ?_⟩
  intro h
  have hc : Function.Commute (a • · : V → V) f := fun x ↦ by
    simpa only [ha] using (f.map_smulₛₗ a x).symm
  -- Apply a relation for `a • x` to `x`. Its residual is killed by `a`.
  have hpow (k : ℕ) (x : V) (hx : a ^ k • x = 0) : f.HasMonicRelation x := by
    induction k generalizing x with
    | zero =>
      have hx0 : x = 0 := by simpa using hx
      exact hasMonicRelation_iff_exists_sum.mpr ⟨0, Fin.elim0, by simp [hx0]⟩
    | succ k ih =>
      have hax : a ^ k • (a • x) = 0 := by rw [← mul_smul, ← pow_succ, hx]
      obtain ⟨d, c, he⟩ := hasMonicRelation_iff_exists_sum.mp (ih _ hax)
      let r := f^[d] x - ∑ j, c j • f^[j.val] x
      have hr : r ∈ K := by
        rw [LinearMap.mem_ker, DistribSMul.toLinearMap_apply]
        calc
          a • r = f^[d] (a • x) - ∑ j, c j • f^[j.val] (a • x) := by
            dsimp only [r]
            rw [smul_sub, Finset.smul_sum, (hc.iterate_right d).eq]
            congr 1
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [smul_comm a, (hc.iterate_right j.val).eq]
          _ = 0 := sub_eq_zero.mpr he
      exact HasMonicRelation.of_residual c ((h ⟨r, hr⟩).map K.subtype hKi)
  obtain ⟨k, hk⟩ := hnil
  exact fun x ↦ hpow k x (by simp [hk])

end FixedScalar

end LinearMap
