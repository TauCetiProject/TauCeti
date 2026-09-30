/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Projection

/-!
# Orthogonal complements of bilinear forms

This file records facts about the orthogonal complement `LinearMap.BilinForm.orthogonal`
that Mathlib lacks. A vector lies in the orthogonal complement of the span of one or two vectors
exactly when it is orthogonal to each of them. Adjoining a vector `x` whose self-pairing is a
non-zero-divisor dividing all its pairings (over a field: a non-isotropic vector) to an orthogonal
basis of the orthogonal complement of `x` gives an orthogonal basis of the whole module, for a
reflexive form; this is the inductive step of every diagonalization argument, over a field as over
a valuation ring.
Adjoining an orthogonal vector whose self-pairing is a right non-zero-divisor to a left-separating
subspace of a reflexive bilinear space produces a nondegenerate restriction; this is the
structural step used when a Cartan--Dieudonne argument enlarges a fixed subspace.

## Main results

* `LinearMap.BilinForm.mem_orthogonal_span_singleton_iff`,
  `LinearMap.BilinForm.mem_orthogonal_span_pair_iff`: membership in the orthogonal complement of
  the span of one or two vectors.
* `LinearMap.BilinForm.IsRefl.exists_orthogonal_basis_of_orthogonal_span_singleton`: an
  orthogonal basis of `x^⊥` extends by `x` to an orthogonal basis of the whole space.
* `TauCeti.BilinForm.restrict_nondegenerate_sup_span_singleton`: adjoining an orthogonal vector
  to a left-separating subspace produces a nondegenerate restriction.
* `LinearMap.BilinForm.isCompl_orthogonal_of_flip_restrict_bijective`: a perfect flipped
  restriction splits a bilinear module over a commutative ring.
* `LinearMap.BilinForm.isCompl_orthogonal_of_restrict_bijective`: a perfect symmetric
  restriction splits a bilinear module over a commutative ring.
* `LinearMap.BilinForm.restrict_span_singleton_bijective_of_isUnit`: unit self-pairing makes
  the cyclic restriction perfect.
* `LinearMap.BilinForm.isCompl_span_singleton_orthogonal_of_dvd`: a vector whose self-pairing is
  a non-zero-divisor dividing all its pairings splits off.
* `LinearMap.BilinForm.isCompl_span_singleton_orthogonal_of_isUnit`: a vector with unit
  self-pairing splits off.
-/

public section

namespace LinearMap.BilinForm

variable {K V : Type*} [CommSemiring K] [AddCommMonoid V] [Module K V]

/-- A vector is orthogonal to the span of a vector `x` exactly when it is orthogonal to `x`. -/
theorem mem_orthogonal_span_singleton_iff (B : LinearMap.BilinForm K V) {x y : V} :
    y ∈ B.orthogonal (K ∙ x) ↔ B x y = 0 := by
  rw [orthogonal, Submodule.orthogonalBilin_span_singleton, LinearMap.mem_ker]

/-- A vector is orthogonal to the span of two vectors exactly when it is orthogonal to both. -/
theorem mem_orthogonal_span_pair_iff (B : LinearMap.BilinForm K V) {x y z : V} :
    z ∈ B.orthogonal (Submodule.span K {x, y}) ↔ B x z = 0 ∧ B y z = 0 := by
  constructor
  · intro hz
    exact ⟨hz x (Submodule.subset_span (by simp)), hz y (Submodule.subset_span (by simp))⟩
  · rintro ⟨hx, hy⟩ n hn
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hn
    simp [hx, hy]

end LinearMap.BilinForm

namespace TauCeti

open LinearMap (BilinForm)

namespace BilinForm

variable {K V : Type*} [CommSemiring K] [AddCommMonoid V] [Module K V]

/-- Adjoining a vector whose self-pairing is a right non-zero-divisor from the orthogonal complement
of a left-separating subspace preserves nondegeneracy. -/
theorem restrict_nondegenerate_sup_span_singleton
    (B : BilinForm K V) (hB : B.IsRefl) (W : Submodule K V)
    (hW : (B.restrict W).SeparatingLeft) (x : V) (hxx : B x x ∈ nonZeroDivisorsRight K)
    (hx : x ∈ B.orthogonal W) :
    (B.restrict (W ⊔ Submodule.span K {x})).Nondegenerate := by
  let S : Submodule K V := W ⊔ Submodule.span K {x}
  have hleft : (B.restrict S).SeparatingLeft := by
    intro y hy
    obtain ⟨w, hw, z, hz, hsum⟩ := Submodule.mem_sup.mp y.2
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have hwzero : ∀ w' : W, B w w' = 0 := by
      intro w'
      have hBxw' : B x w' = 0 := hB.eq_zero (hx w' w'.2)
      have hyw := hy ⟨w', Submodule.mem_sup_left w'.2⟩
      -- Expose the ambient bilinear form under its restriction to `S`.
      change B y w' = 0 at hyw
      rw [← hsum] at hyw
      simpa [hBxw'] using hyw
    have hw0 : w = 0 := congrArg Subtype.val (hW ⟨w, hw⟩ hwzero)
    have hxS : x ∈ S := Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
    have hyx := hy ⟨x, hxS⟩
    -- Expose the ambient bilinear form under its restriction to `S`.
    change B y x = 0 at hyx
    rw [← hsum, hw0, zero_add] at hyx
    have ha : a = 0 := by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul] at hyx
      exact hxx a (by simpa using hyx)
    apply Subtype.ext
    simp [← hsum, hw0, ha]
  refine ⟨hleft, fun y hy ↦ hleft y fun z ↦ ?_⟩
  exact (hB.domRestrict S).eq_zero (hy z)

end BilinForm

end TauCeti

namespace LinearMap.BilinForm

open Module

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- A submodule with perfect flipped restricted pairing is complementary to its right orthogonal
complement. -/
theorem isCompl_orthogonal_of_flip_restrict_bijective
    (B : LinearMap.BilinForm R M) (S : Submodule R M)
    (h : Function.Bijective (B.flip.restrict S)) :
    IsCompl S (B.orthogonal S) := by
  let e : S ≃ₗ[R] Module.Dual R S :=
    LinearEquiv.ofBijective (B.flip.restrict S) h
  let p : M →ₗ[R] S := e.symm.toLinearMap.comp (B.flip.domRestrict₂ S)
  have hp : ∀ y : S, p y = y := by
    intro y
    apply e.injective
    ext z
    simp [p, e, LinearMap.BilinForm.restrict_apply,
      LinearMap.domRestrict₂_apply, LinearMap.BilinForm.flip_apply]
  have hker : LinearMap.ker p = B.orthogonal S := by
    ext x
    rw [LinearMap.mem_ker, ← e.map_eq_zero_iff]
    have hpx : e (p x) = B.flip.domRestrict₂ S x := by simp [p]
    rw [hpx]
    constructor
    · intro hx
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro y hy
      have hy' := congrArg (fun f : Module.Dual R S ↦ f ⟨y, hy⟩) hx
      simpa [LinearMap.domRestrict₂_apply, LinearMap.BilinForm.flip_apply] using hy'
    · intro hx
      ext y
      exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) y y.property
  rw [← hker]
  exact LinearMap.isCompl_of_proj hp

/-- A submodule with perfect symmetric restricted pairing is complementary to its orthogonal
complement. -/
theorem isCompl_orthogonal_of_restrict_bijective
    (B : LinearMap.BilinForm R M) (S : Submodule R M) (hB : (B.restrict S).IsSymm)
    (h : Function.Bijective (B.restrict S)) :
    IsCompl S (B.orthogonal S) := by
  have hflip : B.flip.restrict S = B.restrict S := by
    ext x y
    simpa [LinearMap.BilinForm.restrict_apply, LinearMap.BilinForm.flip_apply] using
      (hB.eq y x)
  exact B.isCompl_orthogonal_of_flip_restrict_bijective S (hflip ▸ h)

/-- Unit self-pairing makes the restricted pairing on the cyclic span perfect. -/
theorem restrict_span_singleton_bijective_of_isUnit (B : LinearMap.BilinForm R M)
    (x : M) (hx : IsUnit (B x x)) : Function.Bijective (B.restrict (R ∙ x)) := by
  obtain ⟨a, ha⟩ := isUnit_iff_exists_inv.mp hx
  have ha' : a * B x x = 1 := by simpa [mul_comm] using ha
  let S : Submodule R M := R ∙ x
  have hxS : x ∈ S := Submodule.mem_span_singleton_self x
  constructor
  · intro y z hyz
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp y.property
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp z.property
    have hval : B (y : M) x = B (z : M) x := by
      simpa only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] using
        congrArg (fun f : Module.Dual R S ↦ f ⟨x, hxS⟩) hyz
    rw [← hb, ← hc, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply] at hval
    simp only [smul_eq_mul] at hval
    have hbc : b = c := by
      calc
        b = (a * B x x) * b := by rw [ha']; ring
        _ = a * (b * B x x) := by ring
        _ = a * (c * B x x) := by rw [hval]
        _ = c := by calc
          a * (c * B x x) = c * (a * B x x) := by ring
          _ = c := by rw [ha', mul_one]
    apply Subtype.ext
    rw [← hb, ← hc, hbc]
  · intro f
    refine ⟨⟨(a * f ⟨x, hxS⟩) • x, Submodule.smul_mem S _ hxS⟩, ?_⟩
    ext y
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp y.property
    have hy : y = b • (⟨x, hxS⟩ : S) := Subtype.ext hb.symm
    rw [hy]
    simp only [LinearMap.BilinForm.restrict_apply]
    rw [map_smul, map_smul, map_smul]
    simp only [smul_eq_mul]
    calc
      b * (a * f ⟨x, hxS⟩ * B x x) = b * (a * B x x) * f ⟨x, hxS⟩ := by ring
      _ = b * f ⟨x, hxS⟩ := by rw [ha']; ring

/-- A vector `x` whose self-pairing `B x x` is a non-zero-divisor dividing every pairing `B x y`
spans an orthogonal direct summand. Over a field this is the condition `B x x ≠ 0`; over a
valuation ring it says that `B x x` has minimal valuation among the pairings of `x`. -/
theorem isCompl_span_singleton_orthogonal_of_dvd (B : LinearMap.BilinForm R M) {x : M}
    (hx : B x x ∈ nonZeroDivisors R) (hdvd : ∀ y, B x x ∣ B x y) :
    IsCompl (R ∙ x) (B.orthogonal (R ∙ x)) := by
  refine ⟨Submodule.disjoint_def.mpr fun y hy hy' ↦ ?_, codisjoint_iff.mpr ?_⟩
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hc := (mem_orthogonal_iff.mp hy') x (Submodule.mem_span_singleton_self x)
    rw [map_smul, smul_eq_mul] at hc
    rw [(mem_nonZeroDivisors_iff_right.mp hx) c hc, zero_smul]
  · refine eq_top_iff.mpr fun z _ ↦ ?_
    obtain ⟨k, hk⟩ := hdvd z
    refine Submodule.mem_sup.mpr ⟨k • x, Submodule.smul_mem _ k
      (Submodule.mem_span_singleton_self x), z - k • x, mem_orthogonal_iff.mpr fun n hn ↦ ?_,
      add_sub_cancel _ _⟩
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hn
    simp only [map_smul, map_sub, LinearMap.smul_apply, smul_eq_mul, hk]
    ring

/-- Adjoining a vector `x` to an orthogonal basis of the orthogonal complement of `x` gives an
orthogonal basis of the whole module, for a reflexive form, provided the self-pairing `B x x` is a
non-zero-divisor dividing every pairing `B x y`. Over a field this says `B x x ≠ 0`. -/
theorem IsRefl.exists_orthogonal_basis_of_orthogonal_span_singleton {B : LinearMap.BilinForm R M}
    (hB : B.IsRefl) {x : M} (hx : B x x ∈ nonZeroDivisors R) (hdvd : ∀ y, B x x ∣ B x y)
    {d : ℕ} {v : Basis (Fin d) R (B.orthogonal (R ∙ x))}
    (hv : (B.restrict (B.orthogonal (R ∙ x))).iIsOrtho v) :
    ∃ b : Basis (Fin (d + 1)) R M, B.iIsOrtho b := by
  have hli : ∀ c : R, ∀ y ∈ B.orthogonal (R ∙ x), c • x + y = 0 → c = 0 := fun c y hy hcy ↦ by
    have h := congrArg (B x) hcy
    rw [map_add, map_smul, (mem_orthogonal_span_singleton_iff B).1 hy, smul_eq_mul, add_zero,
      map_zero] at h
    exact mem_nonZeroDivisors_iff_right.mp hx c h
  have hsp : ∀ z : M, ∃ c : R, z + c • x ∈ B.orthogonal (R ∙ x) := fun z ↦ by
    obtain ⟨k, hk⟩ := hdvd z
    refine ⟨-k, (mem_orthogonal_span_singleton_iff B).2 ?_⟩
    rw [map_add, map_smul, hk, smul_eq_mul]
    ring
  refine ⟨Basis.mkFinCons x v hli hsp, ?_⟩
  rw [iIsOrtho_def, Basis.coe_mkFinCons]
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> intro hij <;>
    simp only [Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
  · exact (hij rfl).elim
  · exact (mem_orthogonal_span_singleton_iff B).1 (v j).2
  · exact hB.eq_zero ((mem_orthogonal_span_singleton_iff B).1 (v i).2)
  · simpa using iIsOrtho_def.1 hv i j fun h => hij (congrArg Fin.succ h)

/-- A vector with unit self-pairing spans an orthogonal direct summand. -/
theorem isCompl_span_singleton_orthogonal_of_isUnit
    (B : LinearMap.BilinForm R M) (x : M) (hx : IsUnit (B x x)) :
    IsCompl (R ∙ x) (B.orthogonal (R ∙ x)) :=
  B.isCompl_span_singleton_orthogonal_of_dvd hx.mem_nonZeroDivisors fun _ ↦ hx.dvd

end LinearMap.BilinForm
