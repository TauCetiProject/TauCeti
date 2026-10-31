/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NoncommutativeGeometry.UniversalDifferential.Cycle
public import TauCeti.RingTheory.CyclicCohomology.TensorCycle

/-!
# The exterior product of cyclic cocycles

Every cyclic cocycle `φ` of degree `p` on an algebra `A` is the character of the universal-form
cycle `(⨁ m, Ωᵐ A, d, ∫_φ, ι)` (`TauCeti.UniversalForms.cycleCocycle_trace`). The exterior product
`φ # ψ` of `φ` with a cyclic cocycle `ψ` of degree `q` on an algebra `B` is the character of the
tensor product of their universal-form cycles: the differential graded algebra
`(⨁ m, Ωᵐ A) ᵍ⊗ (⨁ m, Ωᵐ B)` with the Koszul-signed product and differential, the trace
`∫_φ ⊗ ∫_ψ` on forms of bidegree `(p, q)`, and the homomorphism `a ⊗ b ↦ ι(a) ⊗ ι(b)`. It is a
cyclic cocycle of degree `p + q` on `A ⊗ B` with values in `M ⊗ N`.

Both algebras may be nonunital, and the universal forms are built on the forced unitizations, so
the construction applies to every pair of cyclic cocycles.

The exterior product is bilinear in the two cocycles.

When `ψ` has degree zero it is a trace, and the exterior product is computed explicitly:

`(φ # ψ)(a₀ ⊗ b₀, …, aₚ ⊗ bₚ) = φ(a₀, …, aₚ) ⊗ ψ(b₀ b₁ ⋯ bₚ)`.

In particular two traces multiply: `(φ # ψ)(a ⊗ b) = φ(a) ⊗ ψ(b)`.

## Main definitions

* `TauCeti.exteriorProductCocycle`: the exterior product `φ # ψ` of two cyclic cocycles.

## Main results

* `TauCeti.exteriorProductCocycle_add_left`, `TauCeti.exteriorProductCocycle_smul_left` and their
  right-hand counterparts: the exterior product is bilinear.
* `TauCeti.exteriorProductCocycle_apply_tmul_of_zero_foldl`: the exterior product with a trace;
  `TauCeti.exteriorProductCocycle_apply_tmul_of_zero` is its form for a unital algebra.
* `TauCeti.exteriorProductCocycle_zero_apply_tmul`: the exterior product of two traces.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1, for cycles and their tensor products.
* A. Connes, *Noncommutative differential geometry*, Publ. Math. IHÉS 62 (1985), Part II, §1.
-/

public section

open scoped DirectSum TensorProduct

namespace TauCeti

section

variable {k A B M N : Type*} [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
  [SMulCommClass k A A] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N] {p q : ℕ}

section NonUnital

variable [NonUnitalRing B] [Module k B] [IsScalarTower k B B] [SMulCommClass k B B]

/-- The **exterior product** `φ # ψ` of a cyclic cocycle `φ` of degree `p` on `A` and a cyclic
cocycle `ψ` of degree `q` on `B`: the character of the tensor product of the universal-form cycles
of `φ` and `ψ`, a cyclic cocycle of degree `p + q` on `A ⊗ B`. -/
noncomputable def exteriorProductCocycle (φ : cyclicCocycles k A M p)
    (ψ : cyclicCocycles k B N q) : cyclicCocycles k (A ⊗[k] B) (M ⊗[k] N) (p + q) :=
  cycleCocycle
    (isDGAlgebra_gradedTensorGrading (UniversalForms.isDGAlgebra k A)
      (UniversalForms.isDGAlgebra k B))
    (gradedTensorHomOfMemZero_mem UniversalForms.ι_mem_grading UniversalForms.ι_mem_grading)
    ((UniversalForms.isClosedGradedTrace_trace φ).gradedTensor (UniversalForms.isDGAlgebra k A)
      (UniversalForms.isDGAlgebra k B) (UniversalForms.isClosedGradedTrace_trace ψ))

/-- The exterior product is the character of the tensor product of the universal-form cycles. -/
theorem exteriorProductCocycle_apply (φ : cyclicCocycles k A M p) (ψ : cyclicCocycles k B N q)
    (x : Fin (p + q + 1) → A ⊗[k] B) :
    ((exteriorProductCocycle φ ψ : cyclicCochains k (A ⊗[k] B) (M ⊗[k] N) (p + q)) :
        MultilinearMap k (fun _ : Fin (p + q + 1) ↦ A ⊗[k] B) (M ⊗[k] N)) x =
      cycleCharacter (R := k) (A := A ⊗[k] B)
        (Ω := UniversalForms.grading k A ᵍ⊗[k] UniversalForms.grading k B) (M := M ⊗[k] N)
        (dgTensorDifferential (R := k) (A := ⨁ m, UniversalForms k A m)
          (B := ⨁ m, UniversalForms k B m) (UniversalForms.grading k A)
          (UniversalForms.grading k B) (UniversalForms.differential k A)
          (UniversalForms.differential k B))
        (gradedTensorTrace (R := k) (Ω₁ := ⨁ m, UniversalForms k A m)
          (Ω₂ := ⨁ m, UniversalForms k B m) (UniversalForms.grading k A)
          (UniversalForms.grading k B)
          (UniversalForms.trace ((φ : cyclicCochains k A M p) :
            MultilinearMap k (fun _ : Fin (p + 1) ↦ A) M))
          (UniversalForms.trace ((ψ : cyclicCochains k B N q) :
            MultilinearMap k (fun _ : Fin (q + 1) ↦ B) N)) p q)
        (gradedTensorHomOfMemZero (R := k) (A := ⨁ m, UniversalForms k A m)
          (B := ⨁ m, UniversalForms k B m) (UniversalForms.ι k A) (UniversalForms.ι k B)
          UniversalForms.ι_mem_grading UniversalForms.ι_mem_grading) (p + q) x := by
  rw [exteriorProductCocycle, coe_cycleCocycle]

/-- The exterior product is additive in the first cocycle. -/
@[simp]
theorem exteriorProductCocycle_add_left (φ φ' : cyclicCocycles k A M p)
    (ψ : cyclicCocycles k B N q) :
    exteriorProductCocycle (φ + φ') ψ =
      exteriorProductCocycle φ ψ + exteriorProductCocycle φ' ψ :=
  Subtype.ext <| Subtype.ext <| MultilinearMap.ext fun x ↦ by
    simp [exteriorProductCocycle_apply]

/-- The exterior product is additive in the second cocycle. -/
@[simp]
theorem exteriorProductCocycle_add_right (φ : cyclicCocycles k A M p)
    (ψ ψ' : cyclicCocycles k B N q) :
    exteriorProductCocycle φ (ψ + ψ') =
      exteriorProductCocycle φ ψ + exteriorProductCocycle φ ψ' :=
  Subtype.ext <| Subtype.ext <| MultilinearMap.ext fun x ↦ by
    simp [exteriorProductCocycle_apply]

/-- The exterior product is homogeneous in the first cocycle. -/
@[simp]
theorem exteriorProductCocycle_smul_left (c : k) (φ : cyclicCocycles k A M p)
    (ψ : cyclicCocycles k B N q) :
    exteriorProductCocycle (c • φ) ψ = c • exteriorProductCocycle φ ψ :=
  Subtype.ext <| Subtype.ext <| MultilinearMap.ext fun x ↦ by
    simp [exteriorProductCocycle_apply]

/-- The exterior product is homogeneous in the second cocycle. -/
@[simp]
theorem exteriorProductCocycle_smul_right (c : k) (φ : cyclicCocycles k A M p)
    (ψ : cyclicCocycles k B N q) :
    exteriorProductCocycle φ (c • ψ) = c • exteriorProductCocycle φ ψ :=
  Subtype.ext <| Subtype.ext <| MultilinearMap.ext fun x ↦ by
    simp [exteriorProductCocycle_apply]

/-- The exterior product vanishes when the first cocycle does. -/
@[simp]
theorem exteriorProductCocycle_zero_left (ψ : cyclicCocycles k B N q) :
    exteriorProductCocycle (0 : cyclicCocycles k A M p) ψ = 0 := by
  simpa using exteriorProductCocycle_smul_left (0 : k) (0 : cyclicCocycles k A M p) ψ

/-- The exterior product vanishes when the second cocycle does. -/
@[simp]
theorem exteriorProductCocycle_zero_right (φ : cyclicCocycles k A M p) :
    exteriorProductCocycle φ (0 : cyclicCocycles k B N q) = 0 := by
  simpa using exteriorProductCocycle_smul_right (0 : k) φ (0 : cyclicCocycles k B N q)

/-- **The exterior product with a trace**: if `ψ` is a cyclic cocycle of degree zero, then
`(φ # ψ)(a₀ ⊗ b₀, …, aₚ ⊗ bₚ) = φ(a₀, …, aₚ) ⊗ ψ(b₀ b₁ ⋯ bₚ)`. Since `B` need not be unital, the
nonempty product `b₀ b₁ ⋯ bₚ` is written as a left fold starting from `b₀`. -/
theorem exteriorProductCocycle_apply_tmul_of_zero_foldl (φ : cyclicCocycles k A M p)
    (ψ : cyclicCocycles k B N 0) (a : Fin (p + 1) → A) (b : Fin (p + 1) → B) :
    ((exteriorProductCocycle φ ψ : cyclicCochains k (A ⊗[k] B) (M ⊗[k] N) (p + 0)) :
        MultilinearMap k (fun _ : Fin (p + 0 + 1) ↦ A ⊗[k] B) (M ⊗[k] N))
        (fun i ↦ a i ⊗ₜ b i) =
      ((φ : cyclicCochains k A M p) : MultilinearMap k (fun _ : Fin (p + 1) ↦ A) M) a ⊗ₜ
        ((ψ : cyclicCochains k B N 0) : MultilinearMap k (fun _ : Fin 1 ↦ B) N)
          (fun _ ↦ (List.ofFn fun i : Fin p ↦ b i.succ).foldl (· * ·) (b 0)) := by
  rw [exteriorProductCocycle_apply]
  refine (cycleCharacter_gradedTensorHomOfMemZero_tmul_of_zero (UniversalForms.isDGAlgebra k A)
    (UniversalForms.isDGAlgebra k B) a b).trans ?_
  have hmap : (List.ofFn fun i : Fin p ↦ UniversalForms.ι k B (b i.succ)) =
      (List.ofFn fun i ↦ b i.succ).map (UniversalForms.ι k B) := by
    rw [List.map_ofFn]
    rfl
  rw [UniversalForms.cycleCharacter_trace, List.ofFn_succ, List.prod_cons, List.prod_eq_foldl,
    ← List.foldl_assoc (op := fun x y : ⨁ m, UniversalForms k B m ↦ x * y), mul_one, hmap,
    List.foldl_map, List.foldl_hom (UniversalForms.ι k B) fun x y ↦ (map_mul _ x y).symm,
    UniversalForms.trace_ι]

/-- **The exterior product of two traces** is their tensor product:
`(φ # ψ)(a ⊗ b) = φ(a) ⊗ ψ(b)`. -/
theorem exteriorProductCocycle_zero_apply_tmul (φ : cyclicCocycles k A M 0)
    (ψ : cyclicCocycles k B N 0) (a : A) (b : B) :
    ((exteriorProductCocycle φ ψ : cyclicCochains k (A ⊗[k] B) (M ⊗[k] N) (0 + 0)) :
        MultilinearMap k (fun _ : Fin (0 + 0 + 1) ↦ A ⊗[k] B) (M ⊗[k] N)) (fun _ ↦ a ⊗ₜ b) =
      ((φ : cyclicCochains k A M 0) : MultilinearMap k (fun _ : Fin 1 ↦ A) M) (fun _ ↦ a) ⊗ₜ
        ((ψ : cyclicCochains k B N 0) : MultilinearMap k (fun _ : Fin 1 ↦ B) N) (fun _ ↦ b) :=
  exteriorProductCocycle_apply_tmul_of_zero_foldl φ ψ (fun _ ↦ a) (fun _ ↦ b)

end NonUnital

/-- **The exterior product with a trace on a unital algebra**: if `ψ` is a cyclic cocycle of
degree zero on a unital algebra `B`, then
`(φ # ψ)(a₀ ⊗ b₀, …, aₚ ⊗ bₚ) = φ(a₀, …, aₚ) ⊗ ψ(b₀ b₁ ⋯ bₚ)`. -/
theorem exteriorProductCocycle_apply_tmul_of_zero [Ring B] [Algebra k B]
    (φ : cyclicCocycles k A M p) (ψ : cyclicCocycles k B N 0) (a : Fin (p + 1) → A)
    (b : Fin (p + 1) → B) :
    ((exteriorProductCocycle φ ψ : cyclicCochains k (A ⊗[k] B) (M ⊗[k] N) (p + 0)) :
        MultilinearMap k (fun _ : Fin (p + 0 + 1) ↦ A ⊗[k] B) (M ⊗[k] N))
        (fun i ↦ a i ⊗ₜ b i) =
      ((φ : cyclicCochains k A M p) : MultilinearMap k (fun _ : Fin (p + 1) ↦ A) M) a ⊗ₜ
        ((ψ : cyclicCochains k B N 0) : MultilinearMap k (fun _ : Fin 1 ↦ B) N)
          (fun _ ↦ (List.ofFn b).prod) := by
  rw [exteriorProductCocycle_apply_tmul_of_zero_foldl, List.ofFn_succ, List.prod_cons,
    List.prod_eq_foldl, ← List.foldl_assoc (op := fun x y : B ↦ x * y), mul_one]

end

end TauCeti
