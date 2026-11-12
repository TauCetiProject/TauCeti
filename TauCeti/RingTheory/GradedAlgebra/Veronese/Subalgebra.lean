/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import TauCeti.Algebra.DirectSum.Internal

/-!
# The Veronese subalgebra of a graded algebra

Let `A = ⨁ₙ 𝒜 n` be an `ℕ`-graded `R`-algebra and `d : ℕ`. The *`d`-th Veronese
subalgebra* of `A` is

`A^{(d)} = ⨆ₖ 𝒜 (d k)`,

the `R`-subalgebra of `A` spanned by the homogeneous components whose degree is a multiple of `d`.
For `d ≠ 0` this sum is direct, `A^{(d)} = ⨁ₖ 𝒜 (d k)`, and `A^{(d)}` is again an
`ℕ`-graded `R`-algebra, whose degree-`k` part is `𝒜 (d k)`; in particular its degree-zero part is
`𝒜 0`, the degree-zero part of `A`.

For `d > 0` and `A` commutative, the Veronese subalgebra does not change the projective spectrum:
`Proj A^{(d)} ≅ Proj A`, with `𝒪(n)` corresponding to `𝒪(d n)` (Stacks, Tag 0B5J). This file
provides the graded algebra on which that comparison is stated, and its functoriality in graded
ring maps.

## Main definitions

* `TauCeti.GradedAlgebra.veronese 𝒜 d`: the Veronese subalgebra `⨆ₖ 𝒜 (d k)` of `A`.
* `TauCeti.GradedAlgebra.veroneseGrading 𝒜 d`: its grading, with degree-`k` part `𝒜 (d k)`.
* `TauCeti.GradedAlgebra.veroneseMap d f`: the graded ring map `A^{(d)} → B^{(d)}` induced by a
  graded ring map `f : A → B`.
* `TauCeti.GradedAlgebra.instGradedAlgebraVeroneseGrading`: for `d ≠ 0`, this grading makes the
  Veronese subalgebra an `ℕ`-graded `R`-algebra.
* `TauCeti.GradedAlgebra.veroneseGradingZeroEquiv`: its degree-zero part is `𝒜 0`, as rings.

## Main results

* `TauCeti.GradedAlgebra.isInternal_veroneseGrading`: for `d ≠ 0`, the Veronese subalgebra is the
  internal direct sum of the components `𝒜 (d k)`.
* `TauCeti.GradedAlgebra.map_veroneseGrading_zero`: the degree-zero part of the Veronese
  subalgebra is `𝒜 0`.

## Implementation notes

The subalgebra, its grading, its degree-zero part and its functoriality only use that the
components multiply like a grading (`SetLike.GradedMonoid 𝒜`); the direct-sum results and the
graded-algebra instance assume that `𝒜` decomposes `A` (`GradedAlgebra 𝒜`).

The definitions `veronese`, `veroneseGrading` and `veroneseMap` are exposed: statements about
homogeneous localizations of the Veronese subalgebra identify types such as
`HomogeneousLocalization.Away ℬ (φ f)` and `HomogeneousLocalization.Away ℬ (veroneseMap d φ f : B)`,
and membership `x ∈ veroneseGrading 𝒜 d k` with `(x : A) ∈ 𝒜 (d * k)` inside terms, which holds
only after unfolding these definitions.

## References

* [The Stacks Project, Section 27.11, Tag 0B5J](https://stacks.math.columbia.edu/tag/0B5J)
* A. Grothendieck, *Éléments de géométrie algébrique II*, Publ. Math. IHÉS 8 (1961), §2.4.7.
-/

public section

open DirectSum

namespace TauCeti.GradedAlgebra

section Semiring

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) (d : ℕ)

section GradedMonoid

variable [SetLike.GradedMonoid 𝒜]

/-- The `d`-th Veronese subalgebra `⨆ₖ 𝒜 (d k)` of a graded algebra `A = ⨁ₙ 𝒜 n`: the
`R`-subalgebra spanned by the homogeneous components whose degree is a multiple of `d`. For
`d ≠ 0` this sum is direct (`isInternal_veroneseGrading`). -/
@[expose] def veronese : Subalgebra R A :=
  Submodule.toSubalgebra (⨆ k, 𝒜 (d * k))
    (Submodule.mem_iSup_of_mem 0 (by simpa using SetLike.GradedOne.one_mem (A := 𝒜)))
    fun {x y} hx hy ↦ by
      induction hx using Submodule.iSup_induction' with
      | mem i x hx =>
        induction hy using Submodule.iSup_induction' with
        | mem j y hy =>
          exact Submodule.mem_iSup_of_mem (i + j) (mul_add d i j ▸ SetLike.mul_mem_graded hx hy)
        | zero => simp
        | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
      | zero => simp
      | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz

variable {𝒜 d} in
theorem mem_veronese {x : A} : x ∈ veronese 𝒜 d ↔ x ∈ ⨆ k, 𝒜 (d * k) :=
  Iff.rfl

variable {𝒜 d} in
theorem mem_veronese_of_mem {k : ℕ} {x : A} (hx : x ∈ 𝒜 (d * k)) : x ∈ veronese 𝒜 d :=
  Submodule.mem_iSup_of_mem k hx

variable {𝒜 d} in
/-- The Veronese subalgebra is the smallest subalgebra containing the components `𝒜 (d k)`. -/
theorem veronese_le_iff {S : Subalgebra R A} :
    veronese 𝒜 d ≤ S ↔ ∀ k, 𝒜 (d * k) ≤ Subalgebra.toSubmodule S :=
  iSup_le_iff (f := fun k ↦ 𝒜 (d * k)) (a := Subalgebra.toSubmodule S)

/-- The grading of the Veronese subalgebra `⨁ₖ 𝒜 (d k)`: its degree-`k` part is `𝒜 (d k)`. -/
@[expose] def veroneseGrading (k : ℕ) : Submodule R (veronese 𝒜 d) :=
  (𝒜 (d * k)).comap (veronese 𝒜 d).val.toLinearMap

variable {𝒜 d} in
@[simp]
theorem mem_veroneseGrading {k : ℕ} {x : veronese 𝒜 d} :
    x ∈ veroneseGrading 𝒜 d k ↔ (x : A) ∈ 𝒜 (d * k) :=
  Iff.rfl

/-- The degree-`k` part of the Veronese subalgebra, viewed in `A`, is `𝒜 (d k)`. -/
theorem map_veroneseGrading (k : ℕ) :
    (veroneseGrading 𝒜 d k).map (veronese 𝒜 d).val.toLinearMap = 𝒜 (d * k) := by
  refine le_antisymm (Submodule.map_comap_le _ _) fun x hx ↦ ?_
  exact ⟨⟨x, mem_veronese_of_mem hx⟩, hx, rfl⟩

/-- The degree-zero part of the Veronese subalgebra, viewed in `A`, is the degree-zero part `𝒜 0`
of `A`. -/
theorem map_veroneseGrading_zero :
    (veroneseGrading 𝒜 d 0).map (veronese 𝒜 d).val.toLinearMap = 𝒜 0 := by
  rw [map_veroneseGrading, mul_zero]

/-- The components `𝒜 (d k)` of the Veronese subalgebra multiply like a grading. -/
instance : SetLike.GradedMonoid (veroneseGrading 𝒜 d) where
  one_mem := by simpa using SetLike.GradedOne.one_mem (A := 𝒜)
  mul_mem i j x y hx hy := by
    rw [mem_veroneseGrading, mul_add]
    exact SetLike.mul_mem_graded hx hy

/-- The Veronese subalgebra is spanned by its components `𝒜 (d k)`. -/
theorem iSup_veroneseGrading_eq_top : ⨆ k, veroneseGrading 𝒜 d k = ⊤ := by
  apply Submodule.map_injective_of_injective (f := (veronese 𝒜 d).val.toLinearMap)
    Subtype.val_injective
  simp only [Submodule.map_iSup, map_veroneseGrading, Submodule.map_top]
  ext x
  simp [LinearMap.mem_range, mem_veronese]

/-- The degree-zero part of the Veronese subalgebra is the degree-zero part `𝒜 0` of `A`, as
rings. -/
def veroneseGradingZeroEquiv : veroneseGrading 𝒜 d 0 ≃+* 𝒜 0 where
  toFun a := ⟨a, by simpa only [mul_zero] using mem_veroneseGrading.1 a.2⟩
  invFun b := ⟨⟨b, mem_veronese_of_mem (k := 0) (by simpa only [mul_zero] using b.2)⟩,
    mem_veroneseGrading.2 (by simpa only [mul_zero] using b.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem coe_veroneseGradingZeroEquiv (a : veroneseGrading 𝒜 d 0) :
    (veroneseGradingZeroEquiv 𝒜 d a : A) = ((a : veronese 𝒜 d) : A) :=
  by rfl

@[simp]
theorem coe_veroneseGradingZeroEquiv_symm (b : 𝒜 0) :
    (((veroneseGradingZeroEquiv 𝒜 d).symm b : veronese 𝒜 d) : A) = b :=
  by rfl

section Map

variable {R' B : Type*} [CommSemiring R'] [Semiring B] [Algebra R' B] {ℬ : ℕ → Submodule R' B}
  [SetLike.GradedMonoid ℬ] {𝒜}

/-- A graded ring map `A → B` restricts to a graded ring map `A^{(d)} → B^{(d)}` between the
Veronese subalgebras. -/
@[expose] def veroneseMap (f : 𝒜 →+*ᵍ ℬ) : veroneseGrading 𝒜 d →+*ᵍ veroneseGrading ℬ d where
  toRingHom := (f.toRingHom.comp (veronese 𝒜 d).val.toRingHom).codRestrict (veronese ℬ d)
    fun ⟨x, hx⟩ ↦ by
      induction hx using Submodule.iSup_induction' with
      | mem k x hx => exact mem_veronese_of_mem (f.map_mem hx)
      | zero => simp
      | add x y _ _ hx hy => simpa using add_mem hx hy
  map_mem hx := mem_veroneseGrading.2 (f.map_mem (mem_veroneseGrading.1 hx))

@[simp]
theorem coe_veroneseMap_apply (f : 𝒜 →+*ᵍ ℬ) (x : veronese 𝒜 d) :
    (veroneseMap d f x : B) = f x :=
  rfl

@[simp]
theorem veroneseMap_id : veroneseMap d (GradedRingHom.id 𝒜) = GradedRingHom.id _ :=
  GradedRingHom.ext fun _ ↦ rfl

theorem veroneseMap_comp {R'' C : Type*} [CommSemiring R''] [Semiring C] [Algebra R'' C]
    {𝒞 : ℕ → Submodule R'' C} [SetLike.GradedMonoid 𝒞] (g : ℬ →+*ᵍ 𝒞) (f : 𝒜 →+*ᵍ ℬ) :
    veroneseMap d (g.comp f) = (veroneseMap d g).comp (veroneseMap d f) :=
  GradedRingHom.ext fun _ ↦ rfl

end Map

end GradedMonoid

section GradedAlgebra

variable [GradedAlgebra 𝒜]

/-- For `d ≠ 0`, the Veronese subalgebra is the internal direct sum of its components
`𝒜 (d k)`. -/
theorem isInternal_veroneseGrading (hd : d ≠ 0) : IsInternal (veroneseGrading 𝒜 d) := by
  -- The degree-`d k` component in `A` of a sum of elements of the `𝒜 (d j)` is its `k`-th term.
  have hcomp (y : ⨁ k, veroneseGrading 𝒜 d k) (k : ℕ) :
      (decompose 𝒜 ((DirectSum.coeAddMonoidHom (veroneseGrading 𝒜 d) y : veronese 𝒜 d) : A)
        (d * k) : A) = ((y k : veronese 𝒜 d) : A) := by
    induction y using DirectSum.induction_on with
    | zero => simp
    | of j x =>
      rw [DirectSum.coeAddMonoidHom_of]
      obtain rfl | hjk := eq_or_ne j k
      · rw [decompose_of_mem_same 𝒜 (mem_veroneseGrading.1 x.2), of_eq_same]
      · rw [decompose_of_mem_ne 𝒜 (mem_veroneseGrading.1 x.2) ((mul_right_injective₀ hd).ne hjk),
          of_eq_of_ne _ _ _ hjk.symm, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero]
    | add y z hy hz => simp [hy, hz]
  refine ⟨fun y z h ↦ DirectSum.ext fun k ↦ Subtype.ext <| Subtype.ext ?_, fun x ↦ ?_⟩
  · rw [← hcomp, ← hcomp, h]
  · -- The components span, so `coeLinearMap`, whose underlying map is `coeAddMonoidHom`, is onto.
    obtain ⟨y, hy⟩ := LinearMap.range_eq_top.1
      (range_coeLinearMap.trans (iSup_veroneseGrading_eq_top 𝒜 d)) x
    exact ⟨y, hy⟩

/-- For `d ≠ 0`, the components `𝒜 (d k)` of the Veronese subalgebra are independent. -/
theorem iSupIndep_veroneseGrading (hd : d ≠ 0) : iSupIndep (veroneseGrading 𝒜 d) :=
  (isInternal_veroneseGrading 𝒜 d hd).submodule_iSupIndep

/-- For `d ≠ 0`, the Veronese subalgebra `⨁ₖ 𝒜 (d k)` is an `ℕ`-graded `R`-algebra, with
degree-`k` part `𝒜 (d k)`. -/
noncomputable instance instGradedAlgebraVeroneseGrading [NeZero d] :
    GradedAlgebra (veroneseGrading 𝒜 d) where
  __ := (isInternal_veroneseGrading 𝒜 d (NeZero.ne d)).chooseDecomposition

variable {𝒜 d} in
/-- The degree-`k` component of an element of the Veronese subalgebra is its degree-`d k`
component in `A`. -/
@[simp]
theorem coe_decompose_veroneseGrading [NeZero d] (x : veronese 𝒜 d) (k : ℕ) :
    ((decompose (veroneseGrading 𝒜 d) x k : veronese 𝒜 d) : A) = decompose 𝒜 (x : A) (d * k) :=
  DirectSum.map_decompose_shift (veroneseGrading 𝒜 d) 𝒜
    (veronese 𝒜 d).val.toAddMonoidHom (fun k ↦ d * k) (mul_right_injective₀ (NeZero.ne d))
    (fun _ _ hx ↦ mem_veroneseGrading.mp hx) k x

end GradedAlgebra

end Semiring

end TauCeti.GradedAlgebra
