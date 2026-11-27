/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.Basic
public import TauCeti.LinearAlgebra.Semilinear.Graded
import TauCeti.Algebra.Module.LinearMap.Iterate
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

section Semiring

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] {σ : R →+* R}

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

end Semiring

section Ring

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {σ : R →+* R}
  {F : M →ₛₗ[σ] M}

private theorem iterate_residual (x : M) {n : ℕ} (a : Fin n → R) (j : ℕ) :
    F^[j] (F^[n] x - ∑ i, a i • F^[i.val] x) =
      F^[j + n] x - ∑ i, σ^[j] (a i) • F^[j + i.val] x := by
  simp only [iterate_map_sub, F.iterate_map_sum_smulₛₗ, ← Function.iterate_add_apply]

private theorem map_iterate_sub_sum_smul {N : Type*} [AddCommGroup N] [Module R N]
    {G : N →ₛₗ[σ] N} (g : M →ₗ[R] N) (hg : Semiconj g F G) (x : M)
    {n : ℕ} (a : Fin n → R) :
    g (F^[n] x - ∑ i, a i • F^[i.val] x) = G^[n] (g x) - ∑ i, a i • G^[i.val] (g x) := by
  simp only [map_sub, map_sum, map_smul, (hg.iterate_right _).eq]

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
    rw [map_iterate_sub_sum_smul P.mkQ hq x a, ha, sub_self]
  exact HasMonicRelation.of_residual a ((h₁ ⟨_, hr⟩).map P.subtype hi)

/-- An algebraic endomorphism induces an algebraic endomorphism on each stable subquotient. -/
theorem IsAlgebraic.subquotientMap (h : F.IsAlgebraic) (P Q : Submodule R M)
    (hP : MapsTo F P P) (hQ : MapsTo F Q Q) : (F.subquotientMap P Q hP hQ).IsAlgebraic := by
  have h₁ := ((isAlgebraic_iff_restrict_and_mapQ P hP).mp h).1
  exact h₁.of_surjective (Q.comap P.subtype).mkQ
    (fun x ↦ (subquotientMap_mk P Q hP hQ x).symm) (Q.comap P.subtype).mkQ_surjective

/-- If the successive quotients of a finite descending stable filtration are algebraic,
then the restriction to its initial submodule is algebraic. -/
theorem isAlgebraic_restrict_of_filtration (P : ℕ → Submodule R M)
    (hP : ∀ i, MapsTo F (P i) (P i)) (hdesc : Antitone P) {n : ℕ} (hbot : P n = ⊥)
    (halg : ∀ i < n, (F.subquotientMap (P i) (P (i + 1)) (hP i) (hP (i + 1))).IsAlgebraic) :
    (F.restrict (hP 0)).IsAlgebraic :=
  F.restrict_of_filtration (fun g ↦ g.IsAlgebraic) (fun g ↦ isAlgebraic_of_subsingleton g)
    (fun e he hg ↦ hg.of_injective e.toLinearMap he e.injective)
    (fun Q hQ h₁ h₂ ↦ (isAlgebraic_iff_restrict_and_mapQ Q hQ).mpr ⟨h₁, h₂⟩)
    P hP hdesc hbot halg

end Ring

section FixedScalar

variable {A V : Type*} [CommRing A] [AddCommGroup V] [Module A V] {τ : A →+* A}

open scoped Pointwise

/-- Algebraicity passes to each graded piece for a fixed scalar. -/
theorem IsAlgebraic.smulPowGraded {f : V →ₛₗ[τ] V} (hf : f.IsAlgebraic)
    {a : A} (ha : τ a = a) (i : ℕ) : (f.smulPowGraded ha i).IsAlgebraic := by
  rw [smulPowGraded_eq_subquotientMap]
  exact hf.subquotientMap _ _ _ _

/-- For a fixed scalar with a finite power filtration, algebraicity can be checked on the
successive quotients. -/
theorem isAlgebraic_iff_smulPowGraded (f : V →ₛₗ[τ] V) {a : A} (ha : τ a = a) {n : ℕ}
    (hbot : a ^ n • (⊤ : Submodule A V) = ⊥) :
    f.IsAlgebraic ↔ ∀ i < n, (f.smulPowGraded ha i).IsAlgebraic := by
  let P (i : ℕ) := a ^ i • (⊤ : Submodule A V)
  refine ⟨fun h i _ ↦ h.smulPowGraded ha i, fun h ↦ ?_⟩
  have h₀ := isAlgebraic_restrict_of_filtration P (f.mapsTo_pow_smul_top_of_fixed ha)
    (Submodule.antitone_pow_smul_top a) hbot
    (fun i hi ↦ by simpa only [smulPowGraded_eq_subquotientMap] using h i hi)
  exact h₀.of_surjective (P 0).subtype (fun _ ↦ rfl) fun x ↦ ⟨⟨x, by simp [P]⟩, rfl⟩

/-- If the scalar-power filtration terminates, algebraicity is equivalent to algebraicity of
the induced map on `V / aV`. -/
theorem isAlgebraic_iff_mapQ_smul_top (f : V →ₛₗ[τ] V) {a : A} (ha : τ a = a) {n : ℕ}
    (hbot : a ^ n • (⊤ : Submodule A V) = ⊥) :
    f.IsAlgebraic ↔ (Submodule.mapQ (a • (⊤ : Submodule A V)) (a • ⊤) f
      (f.mapsTo_smul_top_of_fixed ha)).IsAlgebraic := by
  let Q : Submodule A V := a • ⊤
  refine ⟨fun h ↦ ((isAlgebraic_iff_restrict_and_mapQ Q (f.mapsTo_smul_top_of_fixed ha)).mp h).2,
    fun h ↦ (f.isAlgebraic_iff_smulPowGraded ha hbot).mpr fun i _ ↦ ?_⟩
  exact h.of_surjective (TauCeti.smulPowQuotientMap a i) (f.smulPowQuotientMap_semiconj ha i)
    (TauCeti.smulPowQuotientMap_surjective a i)

/-- If every vector is killed by a power of a fixed scalar, algebraicity can be checked on
the submodule killed by that scalar. -/
theorem isAlgebraic_iff_restrict_torsionBy (f : V →ₛₗ[τ] V)
    {a : A} (ha : τ a = a) (hnil : ∀ x : V, ∃ k : ℕ, a ^ k • x = 0) :
    f.IsAlgebraic ↔ (f.restrict (f.mapsTo_torsionBy_of_fixed ha)).IsAlgebraic := by
  let K := Submodule.torsionBy A V a
  let fK := f.restrict (f.mapsTo_torsionBy_of_fixed ha)
  have hKi : Semiconj K.subtype fK f := fun _ ↦ rfl
  refine ⟨fun h ↦ h.of_injective K.subtype hKi K.subtype_injective, ?_⟩
  intro h
  let g := DistribSMul.toLinearMap A V a
  have hc : Semiconj g f f := fun x ↦ by
    simpa only [g, DistribSMul.toLinearMap_apply, ha] using (f.map_smulₛₗ a x).symm
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
        apply (Submodule.mem_torsionBy_iff a r).mpr
        rw [← DistribSMul.toLinearMap_apply A V a r, map_iterate_sub_sum_smul g hc x c]
        simpa only [g, DistribSMul.toLinearMap_apply] using sub_eq_zero.mpr he
      exact HasMonicRelation.of_residual c ((h ⟨r, hr⟩).map K.subtype hKi)
  intro x
  obtain ⟨k, hk⟩ := hnil x
  exact hpow k x hk

end FixedScalar

end LinearMap
