/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.LinearAlgebra.TensorProduct.Decomposition
public import Mathlib.RingTheory.Flat.Basic
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic

/-!
# The fixed subcomodule

Let `C` be a coalgebra with a distinguished element `1`, and let `M` be a right `C`-comodule. The
vectors `v` with `coact v = v ⊗ 1` form a submodule, and it is a subcomodule because its own
coaction already lands in it. For the comodule attached to a representation of an affine group
this is the submodule of vectors the group fixes. Comodule morphisms induce linear maps on these
invariant vectors; these maps preserve identities, composition, and injectivity. An injective
morphism also reflects invariant vectors when the coalgebra is flat.

The consequences of complete reducibility for this subcomodule are proved in
`TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive`. They show that a linearly reductive
unipotent group acts trivially. Exactness on invariant vectors for arbitrary representations
is proved in `TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.Fixed`.

## Main declarations

* `TauCeti.Comodule.fixedSubcomodule`: the subcomodule of vectors with coaction `v ↦ v ⊗ 1`.
* `TauCeti.Comodule.mem_fixedSubcomodule` and `TauCeti.Comodule.fixedSubcomodule_eq_top_iff`: its
  membership and triviality characterizations.
* `TauCeti.Comodule.Hom.fixedMap`: the induced linear map on invariant vectors.
* `TauCeti.Comodule.Hom.mem_fixedSubcomodule_iff_of_injective`: reflection of invariance along
  injective comodule morphisms over a flat coalgebra.
* `TauCeti.Comodule.decompose_mem_fixedSubcomodule`: for a decomposition into pieces preserved by
  the coaction, the components of an invariant vector are invariant.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w

variable (R : Type u) (C : Type v) (M : Type w)
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C] [One C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- The subcomodule of vectors fixed by the coaction: those `v` with `coact v = v ⊗ 1`.

For the comodule of a representation of an affine group this is the submodule of invariants. -/
def fixedSubcomodule : Subcomodule R C M where
  carrier :=
    LinearMap.eqLocus (coact (R := R) (C := C) (M := M)) ((TensorProduct.mk R M C).flip 1)
  coact_mem' := by
    intro m hm
    have hm' : coact (R := R) (C := C) (M := M) m = m ⊗ₜ[R] (1 : C) := by
      simpa only [LinearMap.flip_apply, TensorProduct.mk_apply] using
        LinearMap.mem_eqLocus.mp hm
    exact ⟨(⟨m, hm⟩ : LinearMap.eqLocus (coact (R := R) (C := C) (M := M))
        ((TensorProduct.mk R M C).flip 1)) ⊗ₜ[R] (1 : C), by
          simpa only [TensorProduct.map_tmul, LinearMap.id_apply, Submodule.coe_subtype] using
            hm'.symm⟩

variable {R C M}

/-- Membership in the fixed subcomodule: `m` is fixed exactly when `coact m = m ⊗ 1`. -/
@[simp]
theorem mem_fixedSubcomodule {m : M} :
    m ∈ fixedSubcomodule R C M ↔ coact (R := R) (C := C) (M := M) m = m ⊗ₜ[R] (1 : C) :=
  Iff.rfl

/-- The fixed subcomodule is everything exactly when the coaction is trivial on every vector. -/
@[simp]
theorem fixedSubcomodule_eq_top_iff :
    fixedSubcomodule R C M = ⊤ ↔
      ∀ m : M, coact (R := R) (C := C) (M := M) m = m ⊗ₜ[R] (1 : C) :=
  ⟨fun h m ↦ mem_fixedSubcomodule.mp (h ▸ Subcomodule.mem_top m),
    fun h ↦ Subcomodule.ext fun m ↦ by simp [h m]⟩

namespace Hom

variable {N : Type*} [AddCommMonoid N] [Module R N] [Comodule R C N]

/-- A comodule morphism sends invariant vectors to invariant vectors. -/
theorem mem_fixedSubcomodule (f : Hom R C M N) {m : M}
    (hm : m ∈ fixedSubcomodule R C M) : f m ∈ fixedSubcomodule R C N := by
  rw [Comodule.mem_fixedSubcomodule] at hm ⊢
  rw [← f.map_coact_apply, hm]
  simp

/-- The restriction of a comodule morphism to invariant vectors. -/
def fixedMap (f : Hom R C M N) :
    fixedSubcomodule R C M →ₗ[R] fixedSubcomodule R C N :=
  f.toLinearMap.restrict fun _ hm ↦ f.mem_fixedSubcomodule hm

/-- On underlying vectors, the induced map on invariants is the original morphism. -/
@[simp]
theorem fixedMap_apply (f : Hom R C M N) (m : fixedSubcomodule R C M) :
    (f.fixedMap m : N) = f m :=
  (rfl)

/-- Restricting the identity morphism gives the identity on invariants. -/
-- Simplify before `ComoduleCat.ofHom_id` rewrites the identity in categorical form.
@[simp↓]
theorem fixedMap_id : (Hom.id R C M).fixedMap = LinearMap.id := by
  ext m
  rfl

/-- Restriction to invariants respects composition. -/
@[simp]
theorem fixedMap_comp {P : Type*} [AddCommMonoid P] [Module R P] [Comodule R C P]
    (g : Hom R C N P) (f : Hom R C M N) :
    (g.comp f).fixedMap = g.fixedMap.comp f.fixedMap := by
  ext m
  rfl

/-- An injective comodule morphism induces an injective map on invariants. -/
theorem fixedMap_injective (f : Hom R C M N) (hf : Function.Injective f) :
    Function.Injective f.fixedMap := by
  intro x y h
  apply Subtype.ext
  exact hf (congrArg Subtype.val h)

end Hom

/-- If a comodule is decomposed into submodules each of which the coaction maps into its tensor
product with `C`, then every homogeneous component of an invariant vector is invariant. For the
symmetric algebra of a comodule with its polynomial grading, the homogeneous components of an
invariant polynomial are invariant. -/
theorem decompose_mem_fixedSubcomodule {ι : Type*} [DecidableEq ι] (𝒜 : ι → Submodule R M)
    [DirectSum.Decomposition 𝒜]
    (h𝒜 : ∀ i, ∀ x ∈ 𝒜 i, coact (R := R) (C := C) x ∈ DirectSum.decomposeTensor 𝒜 C i)
    {x : M} (hx : x ∈ fixedSubcomodule R C M) (i : ι) :
    (DirectSum.decompose 𝒜 x i : M) ∈ fixedSubcomodule R C M := by
  -- The projection onto the `i`-th component commutes with the coaction.
  let p : M →ₗ[R] M := (𝒜 i).subtype ∘ₗ DirectSum.component R ι (fun j ↦ 𝒜 j) i ∘ₗ
    (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap
  have hp (y : M) : p y = DirectSum.decompose 𝒜 y i := (rfl)
  have hcomm (y : M) : coact (R := R) (C := C) (p y) = p.rTensor C (coact y) := by
    induction y using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | @homogeneous j y =>
      obtain ⟨z, hz⟩ := DirectSum.decomposeTensor_apply (ℳ := 𝒜) (N := C) ▸ h𝒜 j y y.2
      rw [← hz, ← LinearMap.rTensor_comp_apply]
      by_cases hji : j = i
      · subst hji
        have hpj : p ∘ₗ (𝒜 j).subtype = (𝒜 j).subtype :=
          LinearMap.ext fun y ↦ by
            rw [LinearMap.comp_apply, Submodule.subtype_apply, hp,
              DirectSum.decompose_of_mem_same 𝒜 y.2]
        rw [hpj, hz, hp, DirectSum.decompose_of_mem_same 𝒜 y.2]
      · have hpj : p ∘ₗ (𝒜 j).subtype = 0 :=
          LinearMap.ext fun y ↦ by
            rw [LinearMap.comp_apply, Submodule.subtype_apply, hp,
              DirectSum.decompose_of_mem_ne 𝒜 y.2 hji, LinearMap.zero_apply]
        rw [hpj, LinearMap.rTensor_zero, LinearMap.zero_apply, hp,
          DirectSum.decompose_of_mem_ne 𝒜 y.2 hji, map_zero]
  rw [mem_fixedSubcomodule, ← hp, hcomm, mem_fixedSubcomodule.1 hx, LinearMap.rTensor_tmul]

end TauCeti.Comodule

namespace TauCeti.Comodule.Hom

universe u v w x

variable {R : Type u} {C : Type v} {M : Type w} {N : Type x}
variable [CommRing R] [AddCommMonoid C] [Module R C] [Coalgebra R C] [One C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]
variable [AddCommMonoid N] [Module R N] [Comodule R C N] [Module.Flat R C]

/-- An injective comodule morphism reflects invariant vectors when the coalgebra is flat. -/
theorem mem_fixedSubcomodule_iff_of_injective (f : Hom R C M N)
    (hf : Function.Injective f) (m : M) :
    f m ∈ fixedSubcomodule R C N ↔ m ∈ fixedSubcomodule R C M := by
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  let : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
  refine ⟨fun hm ↦ ?_, f.mem_fixedSubcomodule⟩
  rw [Comodule.mem_fixedSubcomodule] at hm ⊢
  apply Module.Flat.rTensor_preserves_injective_linearMap f.toLinearMap hf
  simpa [LinearMap.rTensor_def] using hm

end TauCeti.Comodule.Hom
