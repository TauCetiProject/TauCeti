/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Trivial

/-!
# Invariants of a comodule

For a coalgebra `C` over `R`, a group-like element `g : GroupLike R C`, and a right
`C`-comodule `M`, the **invariants relative to `g`** are the vectors whose coaction is
`ρ(m) = m ⊗ g`. In a bialgebra, the usual invariants are the specialization `g = 1`. Under the
representation ⇆ comodule dictionary of the reductive-groups roadmap, these are the fixed
vectors for the corresponding affine monoid scheme representation; in the Hopf-algebra case,
this recovers the usual affine group scheme interpretation.

The invariants form an `R`-submodule, the equalizer of the two linear maps `ρ` and
`m ↦ m ⊗ g`. Two structural facts pin the definition down: the group-like comodule (the
coaction `m ↦ m ⊗ g`) is all invariants, and comodule morphisms carry invariants to
invariants, so `M ↦ M^{co g}` is functorial. On the regular comodule the element `g : C` is
invariant, since `g` is group-like.

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

* `TauCeti.Comodule.mem_invariants`: `m` is invariant iff `ρ(m) = m ⊗ g`.
* `TauCeti.Comodule.invariants_groupLike`: a group-like comodule is all invariants.
* `TauCeti.Comodule.groupLike_mem_invariants_self`: `g` is invariant in the regular comodule.
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
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

variable (R C M) in
/-- The invariants of a right `C`-comodule `M` relative to a group-like element
`g : GroupLike R C`: the `R`-submodule of vectors `m` with `ρ(m) = m ⊗ g`. In a bialgebra,
taking `g = 1` gives the usual invariant vectors. -/
def invariants (g : GroupLike R C) [Comodule R C M] : Submodule R M where
  carrier := {m | coact (R := R) (C := C) (M := M) m = m ⊗ₜ[R] (g : C)}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [map_add, ha, hb, TensorProduct.add_tmul]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    rw [map_zero, TensorProduct.zero_tmul]
  smul_mem' r m hm := by
    simp only [Set.mem_setOf_eq] at *
    rw [map_smul, hm, TensorProduct.smul_tmul']

/-- A vector is invariant exactly when its coaction is `m ⊗ g`. -/
@[simp]
theorem mem_invariants (g : GroupLike R C) [Comodule R C M] {m : M} :
    m ∈ invariants R C M g ↔ coact (R := R) (C := C) (M := M) m = m ⊗ₜ[R] (g : C) :=
  Iff.rfl

/-- An invariant vector, unfolded: its coaction is `m ⊗ g`. -/
theorem coact_eq_of_mem_invariants (g : GroupLike R C) [Comodule R C M] {m : M}
    (hm : m ∈ invariants R C M g) :
    coact (R := R) (C := C) (M := M) m = m ⊗ₜ[R] (g : C) :=
  (mem_invariants g).1 hm

section GroupLike

variable (g : GroupLike R C)

/-- The group-like comodule (coaction `m ↦ m ⊗ g`) is all invariants. -/
theorem invariants_groupLike :
    letI : Comodule R C M := Comodule.groupLike (R := R) (C := C) (M := M) g
    invariants R C M g = ⊤ := by
  letI : Comodule R C M := Comodule.groupLike (R := R) (C := C) (M := M) g
  ext m
  simp

/-- The regular comodule has `g` among its invariants: `g` is group-like, so
`Δ g = g ⊗ g`. -/
theorem groupLike_mem_invariants_self : (g : C) ∈ invariants R C C g := by
  rw [mem_invariants, instSelf_coact, g.isGroupLikeElem_val.comul_eq_tmul_self]

end GroupLike

namespace Hom

variable [Comodule R C M] [Comodule R C N] [Comodule R C P]

/-- Comodule morphisms carry invariants to invariants: if `ρ(m) = m ⊗ g` then
`ρ(f m) = (f ⊗ id)(m ⊗ g) = f m ⊗ g`. -/
theorem map_mem_invariants (g : GroupLike R C) (f : Hom R C M N) {m : M}
    (hm : m ∈ invariants R C M g) :
    f m ∈ invariants R C N g := by
  rw [mem_invariants] at hm ⊢
  rw [← map_coact_apply f m, hm, TensorProduct.map_tmul, LinearMap.id_apply, coe_toLinearMap]

/-- A comodule morphism restricted to invariants, as an `R`-linear map `M^{coC} → N^{coC}`. -/
def mapInvariants (g : GroupLike R C) (f : Hom R C M N) :
    invariants R C M g →ₗ[R] invariants R C N g :=
  f.toLinearMap.restrict fun _ hm => map_mem_invariants g f hm

/-- `mapInvariants f` acts as the underlying map of `f` on invariant vectors. -/
@[simp]
theorem mapInvariants_coe_apply (g : GroupLike R C) (f : Hom R C M N)
    (m : invariants R C M g) :
    (mapInvariants g f m : N) = f (m : M) :=
  LinearMap.coe_restrict_apply _ m

/-- The invariants functor sends the identity morphism to the identity. -/
@[simp]
theorem mapInvariants_id (g : GroupLike R C) :
    mapInvariants g (Hom.id R C M) = LinearMap.id := by
  refine LinearMap.ext fun m => Subtype.ext ?_
  simp only [mapInvariants_coe_apply, Hom.id_apply, LinearMap.id_coe, id_eq]

/-- The invariants functor preserves composition. -/
@[simp]
theorem mapInvariants_comp (g : GroupLike R C) (h : Hom R C N P) (f : Hom R C M N) :
    mapInvariants g (h.comp f) = (mapInvariants g h).comp (mapInvariants g f) := by
  refine LinearMap.ext fun m => Subtype.ext ?_
  simp only [mapInvariants_coe_apply, Hom.comp_apply, LinearMap.comp_apply]

end Hom

section UniversalProperty

variable [Comodule R C M]

/-- The comodule morphism `R → M` from the trivial comodule `R` determined by an invariant
vector `m`, namely `r ↦ r • m`. -/
noncomputable def Hom.ofInvariant (g : GroupLike R C) (m : invariants R C M g) :
    letI : Comodule R C R := Comodule.groupLike (R := R) (C := C) (M := R) g
    Hom R C R M :=
  letI : Comodule R C R := Comodule.groupLike (R := R) (C := C) (M := R) g
  { toLinearMap := LinearMap.toSpanSingleton R M (m : M)
    map_coact := by
      refine LinearMap.ext_ring ?_
      simp only [LinearMap.comp_apply, Comodule.groupLike_coact_apply, TensorProduct.map_tmul,
        LinearMap.toSpanSingleton_apply, LinearMap.id_coe, id_eq, one_smul,
        coact_eq_of_mem_invariants g m.2] }

/-- The morphism `Hom.ofInvariant g m` sends `r` to `r • m`. -/
@[simp]
theorem Hom.ofInvariant_apply (g : GroupLike R C) (m : invariants R C M g) (r : R) :
    letI : Comodule R C R := Comodule.groupLike (R := R) (C := C) (M := R) g
    (Hom.ofInvariant g m) r = r • (m : M) := by
  letI : Comodule R C R := Comodule.groupLike (R := R) (C := C) (M := R) g
  exact LinearMap.toSpanSingleton_apply R M (m : M) r

/-- The value of `Hom.ofInvariant m` at `1` is `m`. -/
@[simp]
theorem Hom.ofInvariant_one (g : GroupLike R C) (m : invariants R C M g) :
    letI : Comodule R C R := Comodule.groupLike (R := R) (C := C) (M := R) g
    (Hom.ofInvariant g m) 1 = (m : M) := by
  simp

/-- Evaluating a comodule morphism out of the trivial comodule `R` at `1` yields an invariant
vector: `ρ(f 1) = (f ⊗ id)(1 ⊗ g) = f 1 ⊗ g`. -/
theorem Hom.map_one_mem_invariants (g : GroupLike R C)
    (f : letI : Comodule R C R := Comodule.groupLike (R := R) (C := C) (M := R) g;
      Hom R C R M) :
    letI : Comodule R C R := Comodule.groupLike (R := R) (C := C) (M := R) g
    f 1 ∈ invariants R C M g := by
  letI : Comodule R C R := Comodule.groupLike (R := R) (C := C) (M := R) g
  rw [mem_invariants, ← Hom.map_coact_apply f 1, Comodule.groupLike_coact_apply,
    TensorProduct.map_tmul, LinearMap.id_apply, Hom.coe_toLinearMap]

/-- The invariants of a comodule `M` are exactly the comodule morphisms from the trivial
comodule `R`: `M^{coC} ≃ Hom(𝟙, M)`, the fixed vectors being the morphisms out of the unit
representation. The equivalence sends an invariant vector `m` to `r ↦ r • m` and a morphism `f`
to `f 1`. -/
@[expose] noncomputable def invariantsEquivHom (g : GroupLike R C) :
    letI : Comodule R C R := Comodule.groupLike (R := R) (C := C) (M := R) g
    invariants R C M g ≃ Hom R C R M :=
  letI : Comodule R C R := Comodule.groupLike (R := R) (C := C) (M := R) g
  { toFun := Hom.ofInvariant g
    invFun := fun f => ⟨f 1, Hom.map_one_mem_invariants g f⟩
    left_inv := fun m => Subtype.ext (Hom.ofInvariant_one g m)
    right_inv := fun f => by
      apply Comodule.Hom.ext
      intro r
      rw [Hom.ofInvariant_apply]
      calc
        r • f 1 = f.toLinearMap (r • 1) := (map_smul f.toLinearMap r 1).symm
        _ = f r := by
          rw [smul_eq_mul, mul_one]
          rfl }

/-- `invariantsEquivHom` sends an invariant vector `m` to the morphism `r ↦ r • m`. -/
@[simp]
theorem invariantsEquivHom_apply (g : GroupLike R C) (m : invariants R C M g) :
    letI : Comodule R C R := Comodule.groupLike (R := R) (C := C) (M := R) g
    invariantsEquivHom g m = Hom.ofInvariant g m :=
  rfl

/-- The inverse of `invariantsEquivHom` sends a morphism `f` to the invariant vector `f 1`. -/
@[simp]
theorem invariantsEquivHom_symm_apply_coe (g : GroupLike R C)
    (f : letI : Comodule R C R := Comodule.groupLike (R := R) (C := C) (M := R) g;
      Hom R C R M) :
    letI : Comodule R C R := Comodule.groupLike (R := R) (C := C) (M := R) g
    (invariantsEquivHom g).symm f = f 1 :=
  rfl

end UniversalProperty

end Comodule

end TauCeti
