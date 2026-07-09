/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Module.Submodule.EqLocus
public import TauCeti.Algebra.Coalgebra.Comodule.Trivial

/-!
# Coinvariants of a comodule

For a coalgebra `C` over `R`, a group-like element `g : GroupLike R C`, and a right
`C`-comodule `M`, the **coinvariants relative to `g`** are the vectors whose coaction is
`ρ(m) = m ⊗ g`. In a bialgebra, the specialization `g = 1` is the comodule-theoretic form of
the usual fixed-vector construction. Under the representation ⇆ comodule dictionary in the
commutative bialgebra or Hopf-algebra setting of the reductive-groups roadmap, this
specialization is the affine monoid or affine group scheme fixed-point functor.

The coinvariants form an `R`-submodule, the equalizer of the two linear maps `ρ` and
`m ↦ m ⊗ g`. Two structural facts pin the definition down: the group-like comodule attached
to `g` is all coinvariants, and comodule morphisms carry coinvariants relative to `g` to
coinvariants relative to `g`, so `M ↦ M^{co g}` is functorial. On the regular comodule the
element `g : C` is coinvariant, since `g` is group-like.

This is Layer 1 infrastructure for the reductive-groups roadmap
(`ReductiveGroups/README.md` in TauCetiRoadmap, "representations = comodules"): the `g = 1`
specialization gives the comodule-theoretic fixed-vector/invariants functor needed for the
complete-reducibility (linear reductivity) statements of Layer 6, while the relative
`g`-coinvariants developed here support the same Hom-space calculation for any group-like
source comodule. It is built on the existing comodule and trivial-comodule API.

## Main definitions

* `TauCeti.Comodule.coinvariants`: the submodule of coinvariants of a right comodule.
* `TauCeti.Comodule.invariants`: the bialgebraic fixed-vector specialization at `g = 1`.
* `TauCeti.Comodule.Hom.mapCoinvariants`: a comodule morphism restricted to coinvariants.

## Main results

* `TauCeti.Comodule.mem_coinvariants`: `m` is coinvariant iff `ρ(m) = m ⊗ g`.
* `TauCeti.Comodule.coinvariants_groupLike_eq_top`: a group-like comodule has all vectors
  coinvariant.
* `TauCeti.Comodule.groupLike_mem_coinvariants_self`: `g` is coinvariant in the regular
  comodule.
* `TauCeti.Comodule.Hom.map_mem_coinvariants`, `mapCoinvariants_id`, `mapCoinvariants_comp`:
  functoriality of coinvariants.

## References

The coinvariants of a comodule are standard; see for example Sweedler,
*Hopf Algebras*, Chapter 3. The `g = 1` specialization realizes the fixed-point functor of
the representation ⇆ comodule dictionary in Layer 1 of the Tau Ceti reductive-groups roadmap.
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
/-- The coinvariants of a right `C`-comodule `M` relative to a group-like element
`g : GroupLike R C`: the equalizer of the coaction and the group-like coaction
`m ↦ m ⊗ g`. -/
def coinvariants (g : GroupLike R C) [Comodule R C M] : Submodule R M :=
  LinearMap.eqLocus (coact (R := R) (C := C) (M := M))
    (Comodule.groupLikeCoact (R := R) (C := C) (M := M) g)

/-- A vector is coinvariant exactly when its coaction is `m ⊗ g`. -/
@[simp]
theorem mem_coinvariants (g : GroupLike R C) [Comodule R C M] {m : M} :
    m ∈ coinvariants R C M g ↔ coact (R := R) (C := C) (M := M) m = m ⊗ₜ[R] (g : C) := by
  rw [coinvariants, LinearMap.mem_eqLocus]
  rfl

/-- A coinvariant vector, unfolded: its coaction is `m ⊗ g`. -/
theorem coact_eq_of_mem_coinvariants (g : GroupLike R C) [Comodule R C M] {m : M}
    (hm : m ∈ coinvariants R C M g) :
    coact (R := R) (C := C) (M := M) m = m ⊗ₜ[R] (g : C) :=
  (mem_coinvariants g).1 hm

section GroupLike

variable (g : GroupLike R C)

/-- The group-like comodule attached to `g` has all vectors coinvariant. -/
theorem coinvariants_groupLike_eq_top :
    letI : Comodule R C M := Comodule.groupLike (R := R) (C := C) (M := M) g
    coinvariants R C M g = ⊤ := by
  letI : Comodule R C M := Comodule.groupLike (R := R) (C := C) (M := M) g
  ext m
  simp [mem_coinvariants]

/-- The regular comodule has `g` among its coinvariants: `g` is group-like, so
`Δ g = g ⊗ g`. -/
theorem groupLike_mem_coinvariants_self : (g : C) ∈ coinvariants R C C g := by
  rw [mem_coinvariants, instSelf_coact, g.isGroupLikeElem_val.comul_eq_tmul_self]

end GroupLike

namespace Hom

variable [Comodule R C M] [Comodule R C N] [Comodule R C P]

/-- Comodule morphisms carry coinvariants to coinvariants: if `ρ(m) = m ⊗ g` then
`ρ(f m) = (f ⊗ id)(m ⊗ g) = f m ⊗ g`. -/
theorem map_mem_coinvariants (g : GroupLike R C) (f : Hom R C M N) {m : M}
    (hm : m ∈ coinvariants R C M g) :
    f m ∈ coinvariants R C N g := by
  rw [mem_coinvariants] at hm ⊢
  rw [← map_coact_apply f m, hm, TensorProduct.map_tmul, LinearMap.id_apply, coe_toLinearMap]

/-- A comodule morphism restricted to coinvariants relative to the same group-like element
`g`, as an `R`-linear map `M^{co g} → N^{co g}`. -/
def mapCoinvariants (g : GroupLike R C) (f : Hom R C M N) :
    coinvariants R C M g →ₗ[R] coinvariants R C N g :=
  f.toLinearMap.restrict fun _ hm => map_mem_coinvariants g f hm

/-- `mapCoinvariants f` acts as the underlying map of `f` on coinvariant vectors. -/
@[simp]
theorem mapCoinvariants_coe_apply (g : GroupLike R C) (f : Hom R C M N)
    (m : coinvariants R C M g) :
    (mapCoinvariants g f m : N) = f (m : M) :=
  LinearMap.coe_restrict_apply _ m

/-- The coinvariants functor sends the identity morphism to the identity. -/
@[simp]
theorem mapCoinvariants_id (g : GroupLike R C) :
    mapCoinvariants g (CategoryTheory.CategoryStruct.id (ComoduleCat.of R C M)) = LinearMap.id := by
  refine LinearMap.ext fun m => Subtype.ext ?_
  rfl

/-- The coinvariants functor preserves composition. -/
@[simp]
theorem mapCoinvariants_comp (g : GroupLike R C) (h : Hom R C N P) (f : Hom R C M N) :
    mapCoinvariants g (h.comp f) = (mapCoinvariants g h).comp (mapCoinvariants g f) := by
  refine LinearMap.ext fun m => Subtype.ext ?_
  simp only [mapCoinvariants_coe_apply, Hom.comp_apply, LinearMap.comp_apply]

end Hom

section UniversalProperty

variable [Comodule R C M]

/-- The comodule morphism from the group-like comodule on `R` attached to `g`, determined by
a coinvariant vector `m`, namely `r ↦ r • m`. -/
noncomputable def Hom.ofCoinvariant (g : GroupLike R C) (m : coinvariants R C M g) :
    letI : Comodule R C R := Comodule.groupLike (R := R) (C := C) (M := R) g
    Hom R C R M :=
  letI : Comodule R C R := Comodule.groupLike (R := R) (C := C) (M := R) g
  { toLinearMap := LinearMap.toSpanSingleton R M (m : M)
    map_coact := by
      refine LinearMap.ext_ring ?_
      simp only [LinearMap.comp_apply, Comodule.groupLike_coact_apply, TensorProduct.map_tmul,
        LinearMap.toSpanSingleton_apply, LinearMap.id_coe, id_eq, one_smul,
        coact_eq_of_mem_coinvariants g m.2] }

/-- The morphism `Hom.ofCoinvariant g m` sends `r` to `r • m`. -/
@[simp]
theorem Hom.ofCoinvariant_apply (g : GroupLike R C) (m : coinvariants R C M g) (r : R) :
    letI : Comodule R C R := Comodule.groupLike (R := R) (C := C) (M := R) g
    (Hom.ofCoinvariant g m) r = r • (m : M) := by
  letI : Comodule R C R := Comodule.groupLike (R := R) (C := C) (M := R) g
  exact LinearMap.toSpanSingleton_apply R M (m : M) r

/-- The value of `Hom.ofCoinvariant m` at `1` is `m`. -/
theorem Hom.ofCoinvariant_one (g : GroupLike R C) (m : coinvariants R C M g) :
    letI : Comodule R C R := Comodule.groupLike (R := R) (C := C) (M := R) g
    (Hom.ofCoinvariant g m) 1 = (m : M) := by
  simp

/-- Evaluating a comodule morphism out of the group-like comodule on `R` attached to `g` at
`1` yields a coinvariant vector: `ρ(f 1) = (f ⊗ id)(1 ⊗ g) = f 1 ⊗ g`. -/
theorem Hom.map_one_mem_coinvariants (g : GroupLike R C)
    (f : letI : Comodule R C R := Comodule.groupLike (R := R) (C := C) (M := R) g;
      Hom R C R M) :
    letI : Comodule R C R := Comodule.groupLike (R := R) (C := C) (M := R) g
    f 1 ∈ coinvariants R C M g := by
  letI : Comodule R C R := Comodule.groupLike (R := R) (C := C) (M := R) g
  rw [mem_coinvariants, ← Hom.map_coact_apply f 1, Comodule.groupLike_coact_apply,
    TensorProduct.map_tmul, LinearMap.id_apply, Hom.coe_toLinearMap]

/-- The coinvariants of a comodule `M` relative to `g` are linearly equivalent to the
comodule morphisms from the group-like comodule on `R` attached to `g`. The equivalence sends
a coinvariant vector `m` to `r ↦ r • m` and a morphism `f` to `f 1`. -/
@[expose] noncomputable def coinvariantsEquivHom (g : GroupLike R C) :
    letI : Comodule R C R := Comodule.groupLike (R := R) (C := C) (M := R) g
    coinvariants R C M g ≃ₗ[R] Hom R C R M :=
  letI : Comodule R C R := Comodule.groupLike (R := R) (C := C) (M := R) g
  { toFun := Hom.ofCoinvariant g
    invFun := fun f => ⟨f 1, Hom.map_one_mem_coinvariants g f⟩
    left_inv := fun m => Subtype.ext (Hom.ofCoinvariant_one g m)
    right_inv := fun f => by
      apply Comodule.Hom.ext
      intro r
      rw [Hom.ofCoinvariant_apply]
      calc
        r • f 1 = f.toLinearMap (r • 1) := (map_smul f.toLinearMap r 1).symm
        _ = f r := by
          rw [smul_eq_mul, mul_one]
          rfl
    map_add' := fun m n => by
      apply Comodule.Hom.ext
      intro r
      simp [smul_add]
    map_smul' := fun r m => by
      apply Comodule.Hom.ext
      intro s
      simp [smul_comm r s (m : M)] }

/-- `coinvariantsEquivHom` sends a coinvariant vector `m` to the morphism `r ↦ r • m`. -/
@[simp]
theorem coinvariantsEquivHom_apply (g : GroupLike R C) (m : coinvariants R C M g) :
    letI : Comodule R C R := Comodule.groupLike (R := R) (C := C) (M := R) g
    coinvariantsEquivHom g m = Hom.ofCoinvariant g m :=
  rfl

/-- The inverse of `coinvariantsEquivHom` sends a morphism `f` to the coinvariant vector
`f 1`. -/
@[simp]
theorem coinvariantsEquivHom_symm_apply_coe (g : GroupLike R C)
    (f : letI : Comodule R C R := Comodule.groupLike (R := R) (C := C) (M := R) g;
      Hom R C R M) :
    letI : Comodule R C R := Comodule.groupLike (R := R) (C := C) (M := R) g
    (coinvariantsEquivHom g).symm f = f 1 :=
  rfl

end UniversalProperty

end Comodule

namespace Comodule

universe u v w x y

variable {R : Type u} {C : Type v} {M : Type w} {N : Type x} {P : Type y}
variable [CommSemiring R] [Semiring C] [Bialgebra R C]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

section Invariants

variable (R C M) in
/-- The invariants, or fixed vectors, of a right comodule over a bialgebra: the specialization
of `coinvariants` to the unit group-like element. -/
abbrev invariants [Comodule R C M] : Submodule R M :=
  coinvariants R C M (1 : GroupLike R C)

/-- A vector is invariant exactly when its coaction is `m ⊗ 1`. -/
theorem mem_invariants [Comodule R C M] {m : M} :
    m ∈ invariants R C M ↔ coact (R := R) (C := C) (M := M) m = m ⊗ₜ[R] (1 : C) :=
  mem_coinvariants (R := R) (C := C) (M := M) (1 : GroupLike R C)

/-- An invariant vector, unfolded: its coaction is `m ⊗ 1`. -/
theorem coact_eq_of_mem_invariants [Comodule R C M] {m : M}
    (hm : m ∈ invariants R C M) :
    coact (R := R) (C := C) (M := M) m = m ⊗ₜ[R] (1 : C) :=
  (mem_invariants (R := R) (C := C) (M := M)).1 hm

namespace Hom

variable [Comodule R C M] [Comodule R C N]

/-- Comodule morphisms carry invariants to invariants. -/
theorem map_mem_invariants (f : Hom R C M N) {m : M} (hm : m ∈ invariants R C M) :
    f m ∈ invariants R C N :=
  map_mem_coinvariants (R := R) (C := C) (M := M) (N := N) (1 : GroupLike R C) f hm

/-- A comodule morphism restricted to invariants, as an `R`-linear map
`M^{co 1} → N^{co 1}`. -/
abbrev mapInvariants (f : Hom R C M N) : invariants R C M →ₗ[R] invariants R C N :=
  mapCoinvariants (R := R) (C := C) (M := M) (N := N) (1 : GroupLike R C) f

/-- `mapInvariants f` acts as the underlying map of `f` on invariant vectors. -/
theorem mapInvariants_coe_apply (f : Hom R C M N) (m : invariants R C M) :
    (mapInvariants (R := R) (C := C) f m : N) = f (m : M) :=
  mapCoinvariants_coe_apply (R := R) (C := C) (M := M) (N := N)
    (1 : GroupLike R C) f m

/-- The invariants functor sends the identity morphism to the identity. -/
@[simp]
theorem mapInvariants_id :
    mapInvariants (R := R) (C := C)
      (CategoryTheory.CategoryStruct.id (ComoduleCat.of R C M)) = LinearMap.id :=
  mapCoinvariants_id (R := R) (C := C) (M := M) (1 : GroupLike R C)

variable [Comodule R C P]

/-- The invariants functor preserves composition. -/
theorem mapInvariants_comp (h : Hom R C N P) (f : Hom R C M N) :
    mapInvariants (R := R) (C := C) (M := M) (N := P) (h.comp f) =
      (mapInvariants (R := R) (C := C) (M := N) (N := P) h).comp
        (mapInvariants (R := R) (C := C) (M := M) (N := N) f) :=
  mapCoinvariants_comp (R := R) (C := C) (M := M) (N := N) (P := P)
    (1 : GroupLike R C) h f

end Hom

variable [Comodule R C M]

/-- The invariant vectors of a comodule `M` are linearly equivalent to the comodule morphisms
from the trivial comodule on `R`. The equivalence sends an invariant vector `m` to `r ↦ r • m`
and a morphism `f` to `f 1`. -/
noncomputable abbrev invariantsEquivHom :
    letI : Comodule R C R := Comodule.trivial (R := R) (C := C) (M := R)
    invariants R C M ≃ₗ[R] Hom R C R M :=
  by
    simpa [Comodule.trivial_eq_groupLike_one] using
      (coinvariantsEquivHom (R := R) (C := C) (M := M) (1 : GroupLike R C))

/-- `invariantsEquivHom` sends an invariant vector `m` to the morphism `r ↦ r • m`. -/
@[simp]
theorem invariantsEquivHom_apply (m : invariants R C M) :
    letI : Comodule R C R := Comodule.trivial (R := R) (C := C) (M := R)
    invariantsEquivHom (R := R) (C := C) (M := M) m =
      Hom.ofCoinvariant (R := R) (C := C) (M := M) (1 : GroupLike R C) m :=
  rfl

/-- The inverse of `invariantsEquivHom` sends a morphism `f` to the invariant vector `f 1`. -/
@[simp]
theorem invariantsEquivHom_symm_apply_coe
    (f : letI : Comodule R C R := Comodule.trivial (R := R) (C := C) (M := R);
      Hom R C R M) :
    letI : Comodule R C R := Comodule.trivial (R := R) (C := C) (M := R)
    (invariantsEquivHom (R := R) (C := C) (M := M)).symm f = f 1 :=
  rfl

end Invariants

end Comodule

end TauCeti
