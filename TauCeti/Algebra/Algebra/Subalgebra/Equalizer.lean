/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Operations

import Mathlib.Algebra.Group.Submonoid.Units
import TauCeti.GroupTheory.GroupAction.Closure

/-!
# Transporting equalizers along isomorphisms, and invariants as an equalizer

Mathlib's `AlgHom.equalizer f g` is the subalgebra of `A` on which two algebra maps
`f g : A →ₐ[R] B` agree. Isomorphisms `eA : A ≃ₐ[R] A'` and `eB : B ≃ₐ[R] B'` transport `f` and
`g` to maps `A' →ₐ[R] B'`, and `eA` restricts to an isomorphism between the two equalizers
(`AlgEquiv.equalizerCongr`). This lets an equalizer be computed after replacing the source
and the target by isomorphic models.

The invariant subalgebra `FixedPoints.subalgebra R S G` of a monoid `G` acting on `S` by
`R`-algebra endomorphisms is the equalizer of the diagonal map `S → (ι → S)` and
`s ↦ (σ i • s)ᵢ`, for any family `σ : ι → G` whose maps `s ↦ σ i • s` generate the monoid of the
maps `s ↦ g • s` with `g : G`, for instance a family generating `G` as a monoid
(`TauCeti.FixedPoints.subalgebra_eq_equalizer`, from the fixed-point criterion
`TauCeti.forall_smul_eq_self_iff_of_closure_toEndHom_eq_top`). Properties of equalizers therefore
pass to invariant subalgebras.

For algebra maps `f g : A →ₐ[R] B` and an element `P : B`, the elements `x` of `A` with
`P * g x = f x * P` form a subalgebra (`TauCeti.intertwiningSubalgebra`): `P` intertwines `g`
with `f` on it. For `P = 1` this is the equalizer of `g` and `f`
(`AlgHom.intertwiningSubalgebra_one`). To show that `P` intertwines `g` with `f` on a subalgebra,
it therefore suffices to check it on generators (`Algebra.adjoin_le`).

An element of the equalizer is a unit of the equalizer exactly when it is a unit of `A`
(`AlgHom.isUnit_equalizer_mk_iff`), so the inclusion of an equalizer is a local homomorphism.
-/

public section

namespace AlgEquiv

open AlgHom

variable {R A B A' B' : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Semiring A']
  [Semiring B'] [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra R B']

/-- Transport of an equalizer along isomorphisms of the source and the target: `eA` restricts to
an isomorphism from `equalizer f g` to the equalizer of the transported maps. -/
def equalizerCongr (eA : A ≃ₐ[R] A') (eB : B ≃ₐ[R] B') (f g : A →ₐ[R] B) :
    equalizer f g ≃ₐ[R]
      equalizer ((eB : B →ₐ[R] B').comp (f.comp (eA.symm : A' →ₐ[R] A)))
        ((eB : B →ₐ[R] B').comp (g.comp (eA.symm : A' →ₐ[R] A))) :=
  (eA.subalgebraMap (equalizer f g)).trans <| Subalgebra.equivOfEq _ _ <| by
    ext x
    simp only [Subalgebra.mem_map, mem_equalizer, coe_comp, Function.comp_apply,
      AlgEquiv.coe_toAlgHom, EmbeddingLike.apply_eq_iff_eq]
    exact ⟨fun ⟨y, hy, hyx⟩ ↦ hyx ▸ by simpa using hy, fun h ↦ ⟨_, h, by simp⟩⟩

/-- The transport of an equalizer is `eA` on underlying elements. -/
@[simp]
theorem coe_equalizerCongr_apply (eA : A ≃ₐ[R] A') (eB : B ≃ₐ[R] B') (f g : A →ₐ[R] B)
    (x : equalizer f g) : (equalizerCongr eA eB f g x : A') = eA x := by
  simp [equalizerCongr]

/-- The inverse transport of an equalizer is `eA.symm` on underlying elements. -/
@[simp]
theorem coe_equalizerCongr_symm_apply (eA : A ≃ₐ[R] A') (eB : B ≃ₐ[R] B') (f g : A →ₐ[R] B)
    (y : equalizer ((eB : B →ₐ[R] B').comp (f.comp (eA.symm : A' →ₐ[R] A)))
      ((eB : B →ₐ[R] B').comp (g.comp (eA.symm : A' →ₐ[R] A)))) :
    ((equalizerCongr eA eB f g).symm y : A) = eA.symm y :=
  eA.injective <| by rw [← coe_equalizerCongr_apply eA eB f g, apply_symm_apply, apply_symm_apply]

end AlgEquiv

namespace AlgHom

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/-- An element of the equalizer of two algebra maps is a unit of the equalizer exactly when it is
a unit of `A`: the inverse of an element on which `f` and `g` agree is again such an element. -/
theorem isUnit_equalizer_mk_iff (f g : A →ₐ[R] B) {a : A} (ha : f a = g a) :
    IsUnit (⟨a, ha⟩ : equalizer f g) ↔ IsUnit a :=
  -- The submonoid underlying `equalizer f g` is by definition Mathlib's equalizer `eqLocusM` of
  -- the underlying monoid maps: both have carrier `{a | f a = g a}` and the induced monoid
  -- structure, so the statement is the monoid case.
  MonoidHom.isUnit_eqLocusM_mk_iff (f : A →* B) g ha

instance (f g : A →ₐ[R] B) : IsLocalHom (equalizer f g).val where
  map_nonunit a := (isUnit_equalizer_mk_iff f g a.prop).2

end AlgHom

namespace TauCeti.FixedPoints

/-- Let a monoid `G` act on `S` by `R`-algebra endomorphisms, and let `σ : ι → G` be a family whose
maps `s ↦ σ i • s` generate the monoid of the maps `s ↦ g • s` with `g : G` (for instance, a family
generating `G` as a monoid). Then the invariant subalgebra is the equalizer of the diagonal map
`S → (ι → S)` and the `R`-algebra map `s ↦ (σ i • s)ᵢ`. -/
theorem subalgebra_eq_equalizer {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    (G : Type*) [Monoid G] [MulSemiringAction G S] [SMulCommClass G R S] {ι : Type*} {σ : ι → G}
    (hσ : Submonoid.closure
      (Set.range ((MulAction.toEndHom (M := G) (α := S)).mrangeRestrict ∘ σ)) = ⊤) :
    FixedPoints.subalgebra R S G = AlgHom.equalizer (AlgHom.pi fun _ ↦ AlgHom.id R S)
      (AlgHom.pi fun i ↦ MulSemiringAction.toAlgHom R S (σ i)) := by
  ext s
  simp only [FixedPoints.mem_subalgebra, AlgHom.mem_equalizer, funext_iff, AlgHom.pi_apply,
    AlgHom.id_apply, MulSemiringAction.toAlgHom_apply]
  exact (forall_smul_eq_self_iff_of_closure_toEndHom_eq_top hσ).trans
    (forall_congr' fun _ ↦ eq_comm)

end TauCeti.FixedPoints

namespace TauCeti

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/-- The subalgebra of the elements `x` with `P * g x = f x * P`, on which `P` intertwines the
algebra maps `g` and `f`. -/
def intertwiningSubalgebra (P : B) (f g : A →ₐ[R] B) : Subalgebra R A where
  carrier := {x | P * g x = f x * P}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, map_mul] at hx hy ⊢
    rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, map_add] at hx hy ⊢
    rw [mul_add, add_mul, hx, hy]
  algebraMap_mem' r := by
    simp only [Set.mem_ofPred_eq, AlgHom.commutes]
    exact (Algebra.commutes r P).symm

/-- Membership in the intertwining subalgebra is the intertwining identity. -/
@[simp]
theorem mem_intertwiningSubalgebra {P : B} {f g : A →ₐ[R] B} {x : A} :
    x ∈ intertwiningSubalgebra P f g ↔ P * g x = f x * P :=
  Iff.rfl

/-- For `P = 1`, the intertwining subalgebra is the equalizer of `g` and `f`. -/
@[simp]
theorem _root_.AlgHom.intertwiningSubalgebra_one (f g : A →ₐ[R] B) :
    intertwiningSubalgebra 1 f g = AlgHom.equalizer g f := by
  ext x
  simp [AlgHom.mem_equalizer]

end TauCeti
