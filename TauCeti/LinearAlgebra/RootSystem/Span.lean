/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.IsValuedIn

/-!
# Root-span restrictions of reflections

For any commutative ring `S` acting compatibly on `M`, the inclusion `P.rootSpanMem S` of roots into
the `S`-span `P.rootSpan S` is injective, and each reflection `P.reflection k` restricts to an
involution `P.reflectionRootSpan S k : P.rootSpan S ≃ₗ[S] P.rootSpan S` permuting `P.rootSpanMem S`
by `P.reflectionPerm k`.

## Main definitions and results

* `RootPairing.rootSpanMem_injective`: `P.rootSpanMem S` is injective.
* `RootPairing.reflectionRootSpan`: `P.reflection k` restricted to an `S`-linear equivalence of
  `P.rootSpan S`.
* `RootPairing.coe_reflectionRootSpan_apply`, `RootPairing.reflectionRootSpan_rootSpanMem`,
  `RootPairing.reflectionRootSpan_symm`, and `RootPairing.reflectionRootSpan_rootSpanMem_eq_sub`.
-/

public section

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R M N) (S : Type*) [CommRing S]

/-- Including root indices into `P.rootSpan S` via `P.rootSpanMem S` is injective. -/
theorem rootSpanMem_injective [Module S M] :
    Function.Injective (P.rootSpanMem S) := fun _ _ h =>
  P.root.injective (congrArg Subtype.val h)

section Tower

variable [SMul S R] [Module S M] [IsScalarTower S R M]

private theorem reflection_mem_rootSpan (k : ι) {x : M} (hx : x ∈ P.rootSpan S) :
    P.reflection k x ∈ P.rootSpan S := by
  refine Submodule.span_induction ?_ (by simp)
    (fun u v _ _ hu hv => by simpa only [map_add] using (P.rootSpan S).add_mem hu hv)
    (fun a u _ hu => by
      rw [← LinearEquiv.coe_toLinearMap, LinearMap.map_smul_of_tower]
      exact (P.rootSpan S).smul_mem a hu) hx
  rintro _ ⟨j, rfl⟩
  simpa only [← root_reflectionPerm] using (P.rootSpanMem S (P.reflectionPerm k j)).property

/-- **Restriction of `P.reflection k` to the `S`-span of the roots**, as an `S`-linear
equivalence. -/
noncomputable def reflectionRootSpan (k : ι) : P.rootSpan S ≃ₗ[S] P.rootSpan S :=
  let f : P.rootSpan S →ₗ[S] P.rootSpan S :=
    ((P.reflection k).toLinearMap.restrictScalars S).restrict
      fun _ hx => P.reflection_mem_rootSpan S k hx
  { f with
    invFun := f
    left_inv := fun x => Subtype.ext (P.reflection_same k x)
    right_inv := fun x => Subtype.ext (P.reflection_same k x) }

/-- Coercion of `P.reflectionRootSpan S k` to the ambient module agrees with `P.reflection k`. -/
@[simp]
theorem coe_reflectionRootSpan_apply (k : ι) (x : P.rootSpan S) :
    (P.reflectionRootSpan S k x : M) = P.reflection k x :=
  (rfl)

/-- `P.reflectionRootSpan S k` permutes `P.rootSpanMem S` via `P.reflectionPerm k`. -/
@[simp]
theorem reflectionRootSpan_rootSpanMem (k j : ι) :
    P.reflectionRootSpan S k (P.rootSpanMem S j) = P.rootSpanMem S (P.reflectionPerm k j) :=
  Subtype.ext (P.root_reflectionPerm k j).symm

/-- `P.reflectionRootSpan S k` is involutive, so its inverse is itself. -/
@[simp]
theorem reflectionRootSpan_symm (k : ι) :
    (P.reflectionRootSpan S k).symm = P.reflectionRootSpan S k :=
  (rfl)

end Tower

/-- When `P` is valued in `S`, `P.reflectionRootSpan S k` acts on `P.rootSpanMem S j` by subtracting
`P.pairingIn S j k • P.rootSpanMem S k`. -/
theorem reflectionRootSpan_rootSpanMem_eq_sub [Algebra S R] [Module S M]
    [IsScalarTower S R M] [P.IsValuedIn S] (k j : ι) :
    P.reflectionRootSpan S k (P.rootSpanMem S j) =
      P.rootSpanMem S j - P.pairingIn S j k • P.rootSpanMem S k :=
  Subtype.ext (P.reflection_apply_root' S)

end RootPairing

end
