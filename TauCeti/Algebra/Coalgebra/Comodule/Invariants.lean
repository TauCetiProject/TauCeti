/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Trivial

/-!
# Invariants of a comodule

For a bialgebra `C` over `R` and a right `C`-comodule `M`, the **invariants** `M^{coC}` are the
vectors fixed by the coaction: those `m : M` with `ρ(m) = m ⊗ 1`. Under the
representation ⇆ comodule dictionary of the reductive-groups roadmap, a right `C`-comodule is a
representation of the affine group scheme `Spec C`, and its invariants are exactly the fixed
vectors of that representation (the vectors on which the group acts trivially). They are also
the coinvariants `M^{coC}` of Hopf-algebra theory.

The invariants form an `R`-submodule, cut out as the kernel of `ρ - (· ⊗ 1)`. Two structural
facts pin the definition down: the trivial comodule (the coaction `m ↦ m ⊗ 1`) is all
invariants, and comodule morphisms carry invariants to invariants, so `M ↦ M^{coC}` is
functorial. On the regular comodule the unit `1 : C` is invariant, since `1` is group-like.

This is Layer 1 infrastructure for the reductive-groups roadmap
(`ReductiveGroups/README.md` in TauCetiRoadmap, "representations = comodules"): the invariants
functor `V ↦ V^{coC}` is the comodule-theoretic fixed-point functor, a prerequisite for the
complete-reducibility (linear reductivity) statements of Layer 6 and for the Hom-space
computations underlying Tannakian reconstruction. It is built on the existing comodule and
trivial-comodule API.

## Main definitions

* `TauCeti.Comodule.invariants`: the submodule of invariants of a right comodule.
* `TauCeti.Comodule.Hom.mapInvariants`: a comodule morphism restricted to invariants.

## Main results

* `TauCeti.Comodule.mem_invariants`: `m` is invariant iff `ρ(m) = m ⊗ 1`.
* `TauCeti.Comodule.invariants_trivial`: the trivial comodule is all invariants.
* `TauCeti.Comodule.one_mem_invariants_self`: `1` is invariant in the regular comodule.
* `TauCeti.Comodule.Hom.map_mem_invariants`, `mapInvariants_id`, `mapInvariants_comp`:
  functoriality of the invariants.

## References

The invariants (coinvariants) of a comodule are standard; see for example Sweedler,
*Hopf Algebras*, Chapter 3. This realizes the fixed-point functor of the
representation ⇆ comodule dictionary in Layer 1 of the Tau Ceti reductive-groups roadmap.
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace Comodule

universe u v w x y

variable {R : Type u} {C : Type v} {M : Type w} {N : Type x} {P : Type y}
variable [CommSemiring R]
variable [Semiring C] [Bialgebra R C]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

variable (R C M) in
/-- The invariants `M^{coC}` of a right `C`-comodule `M`: the `R`-submodule of vectors `m` with
`ρ(m) = m ⊗ 1`. These are the fixed vectors of the representation `M` of `Spec C`. -/
def invariants [Comodule R C M] : Submodule R M where
  carrier := {m | coact (R := R) (C := C) (M := M) m = m ⊗ₜ[R] (1 : C)}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [map_add, ha, hb, TensorProduct.add_tmul]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    rw [map_zero, TensorProduct.zero_tmul]
  smul_mem' r m hm := by
    simp only [Set.mem_setOf_eq] at *
    rw [map_smul, hm, TensorProduct.smul_tmul']

/-- A vector is invariant exactly when its coaction is `m ⊗ 1`. -/
@[simp]
theorem mem_invariants [Comodule R C M] {m : M} :
    m ∈ invariants R C M ↔ coact (R := R) (C := C) (M := M) m = m ⊗ₜ[R] (1 : C) :=
  Iff.rfl

/-- An invariant vector, unfolded: its coaction is `m ⊗ 1`. -/
theorem coact_eq_of_mem_invariants [Comodule R C M] {m : M} (hm : m ∈ invariants R C M) :
    coact (R := R) (C := C) (M := M) m = m ⊗ₜ[R] (1 : C) :=
  mem_invariants.1 hm

section Trivial

attribute [local instance] Comodule.trivial

/-- The trivial comodule (coaction `m ↦ m ⊗ 1`) is all invariants. -/
theorem invariants_trivial : invariants R C M = ⊤ := by
  ext m
  simp [mem_invariants]

end Trivial

/-- The regular comodule of a bialgebra has `1` among its invariants: `1` is group-like, so
`Δ 1 = 1 ⊗ 1`. -/
theorem one_mem_invariants_self : (1 : C) ∈ invariants R C C := by
  rw [mem_invariants, instSelf_coact, Bialgebra.comul_one, Algebra.TensorProduct.one_def]

namespace Hom

variable [Comodule R C M] [Comodule R C N] [Comodule R C P]

/-- Comodule morphisms carry invariants to invariants: if `ρ(m) = m ⊗ 1` then
`ρ(f m) = (f ⊗ id)(m ⊗ 1) = f m ⊗ 1`. -/
theorem map_mem_invariants (f : Hom R C M N) {m : M} (hm : m ∈ invariants R C M) :
    f m ∈ invariants R C N := by
  rw [mem_invariants] at hm ⊢
  rw [← map_coact_apply f m, hm, TensorProduct.map_tmul, LinearMap.id_apply, coe_toLinearMap]

/-- A comodule morphism restricted to invariants, as an `R`-linear map `M^{coC} → N^{coC}`. -/
@[expose] def mapInvariants (f : Hom R C M N) : invariants R C M →ₗ[R] invariants R C N :=
  f.toLinearMap.restrict fun _ hm => map_mem_invariants f hm

/-- `mapInvariants f` acts as the underlying map of `f` on invariant vectors. -/
@[simp]
theorem mapInvariants_coe_apply (f : Hom R C M N) (m : invariants R C M) :
    (mapInvariants f m : N) = f (m : M) :=
  LinearMap.coe_restrict_apply _ m

/-- The invariants functor sends the identity morphism to the identity. -/
@[simp]
theorem mapInvariants_id :
    mapInvariants (CategoryTheory.CategoryStruct.id (ComoduleCat.of R C M)) = LinearMap.id := by
  change mapInvariants (Hom.id R C (ComoduleCat.of R C M)) = LinearMap.id
  refine LinearMap.ext fun m => Subtype.ext ?_
  simp only [mapInvariants_coe_apply, Hom.id_apply, LinearMap.id_coe, id_eq]

/-- The invariants functor preserves composition. -/
@[simp]
theorem mapInvariants_comp (g : Hom R C N P) (f : Hom R C M N) :
    mapInvariants (g.comp f) = (mapInvariants g).comp (mapInvariants f) := by
  refine LinearMap.ext fun m => Subtype.ext ?_
  simp only [mapInvariants_coe_apply, Hom.comp_apply, LinearMap.comp_apply]

end Hom

section UniversalProperty

variable [Comodule R C M]

/-- The comodule morphism `R → M` from the trivial comodule `R` determined by an invariant
vector `m`, namely `r ↦ r • m`. -/
@[expose] noncomputable def Hom.ofInvariant (m : invariants R C M) :
    letI : Comodule R C R := Comodule.trivial
    Hom R C R M :=
  letI : Comodule R C R := Comodule.trivial
  { toLinearMap := LinearMap.toSpanSingleton R M (m : M)
    map_coact := by
      refine LinearMap.ext_ring ?_
      simp only [LinearMap.comp_apply, Comodule.trivial_coact_apply, TensorProduct.map_tmul,
        LinearMap.toSpanSingleton_apply, LinearMap.id_coe, id_eq, one_smul,
        coact_eq_of_mem_invariants m.2] }

/-- The value of `Hom.ofInvariant m` at `1` is `m`. -/
@[simp]
theorem Hom.ofInvariant_one (m : invariants R C M) :
    letI : Comodule R C R := Comodule.trivial
    (Hom.ofInvariant m) 1 = (m : M) := by
  change LinearMap.toSpanSingleton R M (m : M) 1 = (m : M)
  rw [LinearMap.toSpanSingleton_apply, one_smul]

/-- Evaluating a comodule morphism out of the trivial comodule `R` at `1` yields an invariant
vector: `ρ(f 1) = (f ⊗ id)(1 ⊗ 1) = f 1 ⊗ 1`. -/
theorem Hom.one_mem_invariants (f : letI : Comodule R C R := Comodule.trivial; Hom R C R M) :
    letI : Comodule R C R := Comodule.trivial
    f 1 ∈ invariants R C M := by
  letI : Comodule R C R := Comodule.trivial
  rw [mem_invariants, ← Hom.map_coact_apply f 1, Comodule.trivial_coact_apply,
    TensorProduct.map_tmul, LinearMap.id_apply, Hom.coe_toLinearMap]

/-- The invariants of a comodule `M` are exactly the comodule morphisms from the trivial
comodule `R`: `M^{coC} ≃ Hom(𝟙, M)`, the fixed vectors being the morphisms out of the unit
representation. The equivalence sends an invariant vector `m` to `r ↦ r • m` and a morphism `f`
to `f 1`. -/
@[expose] noncomputable def invariantsEquivHom :
    letI : Comodule R C R := Comodule.trivial
    invariants R C M ≃ Hom R C R M :=
  letI : Comodule R C R := Comodule.trivial
  { toFun := Hom.ofInvariant
    invFun := fun f => ⟨f 1, Hom.one_mem_invariants f⟩
    left_inv := fun m => Subtype.ext (Hom.ofInvariant_one m)
    right_inv := fun f => by
      apply Comodule.Hom.ext
      intro r
      change LinearMap.toSpanSingleton R M (f 1) r = f r
      rw [LinearMap.toSpanSingleton_apply]
      change r • f.toLinearMap 1 = f.toLinearMap r
      rw [← map_smul, smul_eq_mul, mul_one] }

/-- `invariantsEquivHom` sends an invariant vector `m` to the morphism `r ↦ r • m`. -/
@[simp]
theorem invariantsEquivHom_apply (m : invariants R C M) :
    letI : Comodule R C R := Comodule.trivial
    invariantsEquivHom m = Hom.ofInvariant m :=
  rfl

/-- The inverse of `invariantsEquivHom` sends a morphism `f` to the invariant vector `f 1`. -/
@[simp]
theorem invariantsEquivHom_symm_apply_coe
    (f : letI : Comodule R C R := Comodule.trivial; Hom R C R M) :
    letI : Comodule R C R := Comodule.trivial
    (invariantsEquivHom.symm f : M) = f 1 :=
  rfl

end UniversalProperty

end Comodule

end TauCeti
