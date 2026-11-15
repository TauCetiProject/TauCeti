/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IsTensorProduct
public import TauCeti.RingTheory.Invariant.Basic
public import TauCeti.RingTheory.IsTensorProduct.Pushout
public import TauCeti.RingTheory.Invariant.ModuleDescent

/-!
# Galois descent of algebras along a free action of a finite group

Let a finite group `G` act freely on a commutative `A`-algebra `B` by `A`-algebra automorphisms
with ring of invariants `A`, so that `B` is a finite étale `G`-torsor over `A` when `A → B` is
injective. A `B`-algebra `C` carries a *semilinear* action of `G` when `G` acts on `C` by ring
automorphisms with `g • (b • c) = (g • b) • (g • c)` (Mathlib's `SMulDistribClass G B C`). This
file shows that such a `C` descends to its subalgebra of fixed points `Cᴳ`:

* `C` is the base change of the `A`-algebra `Cᴳ` along `A → B`
  (`TauCeti.MulSemiringAction.isPushout_fixedPoints`), so `B ⊗[A] Cᴳ ≃ₐ[B] C`,
  `b ⊗ c ↦ b • c`, is `Algebra.IsPushout.equiv A B Cᴳ C`;
* a `B`-algebra map out of `C` is determined by its values on `Cᴳ`
  (`TauCeti.MulSemiringAction.algHom_ext_fixedPoints`);
* every `A`-algebra map `Cᴳ → C'ᴳ` between the fixed points of two such algebras extends uniquely
  to a `B`-algebra map `C → C'`, and the extension is `G`-equivariant
  (`TauCeti.MulSemiringAction.existsUnique_algHom_extend_fixedPoints`); conversely a
  `G`-equivariant `B`-algebra map restricts to the fixed points
  (`AlgHom.fixedPointsAlgHom`).

So passing to fixed points is effective on objects and fully faithful on `G`-equivariant maps:
an affine scheme over `Spec B` with a compatible action of `G` is the base change of an affine
scheme over `Spec A`, and every `G`-equivariant morphism between two such schemes is the base
change of a unique morphism between their descents. This is
the affine case of descent along a finite étale Galois cover, for instance the projection of an
affine scheme with a free action of a finite group to its invariant quotient.

The effectivity statement is the module form `TauCeti.MulSemiringAction.baseChangeInvariantsEquiv`
applied to `C`, whose invariant submodule is the fixed-point subalgebra.

## Main results

* `TauCeti.MulSemiringAction.isPushout_fixedPoints`: `C = B ⊗[A] Cᴳ`.
* `TauCeti.MulSemiringAction.algHom_ext_fixedPoints`: `B`-algebra maps out of `C` agreeing on
  `Cᴳ` are equal.
* `TauCeti.MulSemiringAction.existsUnique_algHom_extend_fixedPoints`: descent of morphisms.

## References

* S. U. Chase, D. K. Harrison and A. Rosenberg, *Galois theory and Galois cohomology of
  commutative rings*, Mem. Amer. Math. Soc. **52** (1965), 15–33, §1.
* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII, §1.
-/

public section

open TensorProduct

namespace TauCeti.MulSemiringAction

variable {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B] [Group G]
  [MulSemiringAction G B] [SMulCommClass G A B]

section Effective

variable (A B G) (C : Type*) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
  [MulSemiringAction G C] [SMulDistribClass G B C] [SMulCommClass G A C]

/-- **Galois descent of algebras.** For a free action of a finite group `G` on `B` with ring of
invariants `A`, every `B`-algebra `C` with a semilinear action of `G` by ring automorphisms is
the base change of its fixed points: `B ⊗[A] Cᴳ ≃ₐ[B] C`, `b ⊗ c ↦ b • c`. -/
theorem isPushout_fixedPoints [Finite G] [Algebra.IsInvariant A B G]
    (hG : ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun b : B ↦ g • b - b) = ⊤) :
    Algebra.IsPushout A B (FixedPoints.subalgebra A C G) C where
  out := .of_equiv
    (((FixedPoints.subalgebra A C G).toSubmoduleEquiv.symm.trans
        (LinearEquiv.ofEq _ _ (toSubmodule_fixedPoints_subalgebra A G C))).baseChange A B _ _ ≪≫ₗ
      baseChangeInvariantsEquiv A B G C hG)
    fun x ↦ by simp [Subalgebra.toSubmoduleEquiv]; rfl

end Effective

section Morphisms

variable {C C' : Type*} [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
  [MulSemiringAction G C] [SMulDistribClass G B C] [SMulCommClass G A C]
  [CommRing C'] [Algebra A C'] [Algebra B C'] [IsScalarTower A B C']
  [MulSemiringAction G C'] [SMulDistribClass G B C'] [SMulCommClass G A C']

variable [Finite G] [Algebra.IsInvariant A B G]

/-- **Descent of morphisms, uniqueness.** For a free action of a finite group `G` on `B` with ring
of invariants `A`, two `B`-algebra maps out of a `B`-algebra `C` with semilinear action are equal
once they agree on the fixed points `Cᴳ`. -/
theorem algHom_ext_fixedPoints
    (hG : ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun b : B ↦ g • b - b) = ⊤)
    {D : Type*} [Semiring D] [Algebra A D] [Algebra B D] [IsScalarTower A B D] {f f' : C →ₐ[B] D}
    (h : ∀ x : FixedPoints.subalgebra A C G, f x = f' x) : f = f' := by
  have := (isPushout_fixedPoints A B G C hG).symm
  exact Algebra.IsPushout.algHom_ext' (R := A) (S := FixedPoints.subalgebra A C G) (by
    ext x
    exact h x)

/-- **Descent of morphisms.** For a free action of a finite group `G` on `B` with ring of
invariants `A`, and `B`-algebras `C`, `C'` with semilinear actions of `G`, every `A`-algebra map
`φ : Cᴳ →ₐ[A] C'ᴳ` extends to a unique `B`-algebra map `f : C →ₐ[B] C'`, and this extension is
`G`-equivariant. Together with `AlgHom.fixedPointsAlgHom`, this identifies `G`-equivariant
`B`-algebra maps `C → C'` with `A`-algebra maps `Cᴳ → C'ᴳ`. -/
theorem existsUnique_algHom_extend_fixedPoints
    (hG : ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun b : B ↦ g • b - b) = ⊤)
    (φ : FixedPoints.subalgebra A C G →ₐ[A] FixedPoints.subalgebra A C' G) :
    ∃! f : C →ₐ[B] C', (∀ x : FixedPoints.subalgebra A C G, f x = φ x) ∧
      ∀ (g : G) (c : C), f (g • c) = g • f c := by
  have hC := isPushout_fixedPoints A B G C hG
  have := hC.symm
  let f : C →ₐ[B] C' := Algebra.IsPushout.lift B ((FixedPoints.subalgebra A C' G).val.comp φ)
  have hf (x : FixedPoints.subalgebra A C G) : f x = φ x :=
    Algebra.IsPushout.lift_algebraMap (R := A) _ x
  refine ⟨f, ⟨hf, fun g ↦ ?_⟩, fun f' hf' ↦ algHom_ext_fixedPoints hG fun x ↦ by rw [hf'.1, hf]⟩
  -- Both `c ↦ f (g • c)` and `c ↦ g • f c` are `A`-algebra maps; they agree on `B` and on `Cᴳ`.
  suffices ((f.restrictScalars A).comp (MulSemiringAction.toAlgHom A C g)) =
      (MulSemiringAction.toAlgHom A C' g).comp (f.restrictScalars A) from
    fun c ↦ congr($this c)
  refine Algebra.IsPushout.algHom_ext (R := A) (S := B) (R' := FixedPoints.subalgebra A C G)
    (S' := C) ?_ ?_
  · ext x
    simp [FixedPoints.mem_subalgebra.mp x.2 g, hf, FixedPoints.mem_subalgebra.mp (φ x).2 g]
  · ext b
    simp [Algebra.algebraMap_eq_smul_one, smul_distrib_smul]

end Morphisms

end TauCeti.MulSemiringAction
