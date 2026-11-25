/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.BaseChange.Radical
public import TauCeti.Algebra.TensorProduct.Galois
import TauCeti.Algebra.TensorProduct.BaseChange

/-!
# Galois descent of Lie submodules and the nilradical under extension of scalars

Let `E / K` be a Galois extension, possibly infinite, and let `L` be a Lie algebra over `K`. An
automorphism `σ` of `E` over `K` acts on `E ⊗[K] L` through the scalar factor, by `σ ⊗ id`. This
map is `σ`-semilinear and preserves brackets, so it carries ideals of `E ⊗[K] L` to ideals and
nilpotent ideals to nilpotent ideals. Hence the nilradical of `E ⊗[K] L` is stable under the
scalar-factor Galois action, and so is the extension of scalars of every Lie submodule.

Conversely, Galois descent of subspaces (`Submodule.baseChange_comap_eq_of_forall_map_mem`) says
that a Galois-stable subspace of `E ⊗[K] M` is the extension of scalars of the vectors `m` with
`1 ⊗ m` in it. For a Lie submodule of `E ⊗[K] M` that subspace of `M` is again a Lie submodule.
So the Lie submodules arising by extension of scalars are exactly the Galois-stable ones.

Applied to the nilradical, this gives the nilradical counterpart of
`LieAlgebra.radical_baseChange`: for a finite-dimensional `L`, the nilradical of `E ⊗[K] L` is
extended from an ideal of `L`, that ideal is nilpotent because nilpotency descends along a field
extension (`LieIdeal.isNilpotent_baseChange_iff`), hence it lies in the nilradical of `L`. With
`LieAlgebra.baseChange_nilradical_le` this gives

```text
nilradical E (E ⊗[K] L) = (nilradical K L).baseChange E.
```

No characteristic hypothesis is needed. In characteristic zero an algebraic closure of `K` is
Galois over `K` (Mathlib's `IsAlgClosure.isGalois`), so the nilradical commutes with extension of
scalars to an algebraic closure, where Lie's theorem becomes available. Unlike the radical, the
nilradical cannot be handled through the quotient `L ⧸ nilradical K L`, whose nilradical need not
be trivial: for the two-dimensional nonabelian Lie algebra the nilradical is a line and the
quotient is abelian.

## Main results

* `LieSubmodule.existsUnique_baseChange_eq_iff_forall_map_mem`: along a Galois extension, the Lie
  submodules of `E ⊗[K] M` that are extended from `M` are exactly those stable under the
  scalar-factor Galois action, and each is extended from a unique Lie submodule of `M`.
* `LieAlgebra.map_mem_nilradical`: the nilradical of `A ⊗[R] L` is stable under `σ ⊗ id` for every
  algebra automorphism `σ` of `A`.
* `LieAlgebra.nilradical_baseChange`: **the nilradical of a finite-dimensional Lie algebra commutes
  with extension of scalars along a Galois extension**, with
  `LieAlgebra.one_tmul_mem_nilradical_baseChange_iff` reading it as a membership criterion.

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*][bourbaki1975], Chapter I, §5.
* J. S. Milne, *Algebraic Groups* (2017), Appendix A.64, for Galois descent of subspaces.
-/

public section

open TensorProduct

namespace LieSubmodule

variable {K E L M : Type*} [Field K] [Field E] [Algebra K E] [IsGalois K E]
  [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

/-- The Lie submodule of `M` of the vectors `m` such that `1 ⊗ m` lies in a given Lie submodule of
`E ⊗[K] M`. -/
private def descend (N : LieSubmodule E (E ⊗[K] L) (E ⊗[K] M)) : LieSubmodule K L M where
  toSubmodule := ((N : Submodule E (E ⊗[K] M)).restrictScalars K).comap (TensorProduct.mk K E M 1)
  lie_mem {x m} hm := by
    have h : (1 : E) ⊗ₜ[K] ⁅x, m⁆ = ⁅(1 : E) ⊗ₜ[K] x, (1 : E) ⊗ₜ[K] m⁆ := by
      rw [LieAlgebra.ExtendScalars.bracket_tmul, one_mul]
    exact (congrArg (· ∈ N) h).mpr (N.lie_mem hm)

/-- **Galois descent of Lie submodules.** Along a Galois extension `E / K`, a Lie submodule of
`E ⊗[K] M` is the extension of scalars of a Lie submodule of `M` exactly when it is stable under
the scalar-factor Galois action, and that Lie submodule of `M` is then unique. -/
theorem existsUnique_baseChange_eq_iff_forall_map_mem
    (N : LieSubmodule E (E ⊗[K] L) (E ⊗[K] M)) :
    (∃! N₀ : LieSubmodule K L M, N₀.baseChange E = N) ↔
      ∀ σ : E ≃ₐ[K] E, ∀ x ∈ N, TensorProduct.map σ.toLinearMap LinearMap.id x ∈ N := by
  constructor
  · rintro ⟨N₀, rfl, -⟩ σ x hx
    exact (N₀ : Submodule K M).map_mem_baseChange σ.toLinearMap hx
  · intro hN
    have hdesc : (descend N).baseChange E = N := by
      rw [← toSubmodule_inj, coe_baseChange]
      exact Submodule.baseChange_comap_eq_of_forall_map_mem _ hN
    exact ⟨descend N, hdesc, fun N₀ h ↦ (baseChange_inj N₀ (descend N)).mp (h.trans hdesc.symm)⟩

end LieSubmodule

namespace LieAlgebra

open TauCeti.LieAlgebra

section CommRing

variable {R A L : Type*} [CommRing R] [CommRing A] [Algebra R A] [LieRing L] [LieAlgebra R L]

/-- The scalar-factor action of an automorphism preserves brackets. -/
private theorem tensorMap_lie (σ : A ≃ₐ[R] A) (x y : A ⊗[R] L) :
    TensorProduct.map σ.toLinearMap LinearMap.id ⁅x, y⁆ =
      ⁅TensorProduct.map σ.toLinearMap LinearMap.id x,
        TensorProduct.map σ.toLinearMap LinearMap.id y⁆ :=
  -- Mathlib's `ExtendScalars.map σ id` is `σ ⊗ id` by definition.
  (ExtendScalars.map σ.toAlgHom (LieHom.id : L →ₗ⁅R⁆ L)).map_lie x y

/-- The image `(σ ⊗ id) I` of an ideal `I` of `A ⊗[R] L`, described as the preimage of `I` under
`σ⁻¹ ⊗ id`. -/
private def galoisTranslate (σ : A ≃ₐ[R] A) (I : LieIdeal A (A ⊗[R] L)) :
    LieIdeal A (A ⊗[R] L) where
  carrier := {y | TensorProduct.map σ.symm.toLinearMap LinearMap.id y ∈ I}
  add_mem' {x y} hx hy := by
    rw [Set.mem_ofPred_eq, map_add]
    exact add_mem hx hy
  zero_mem' := by simp
  smul_mem' a y hy := by
    rw [Set.mem_ofPred_eq, TauCeti.ScalarAut.tensorProductMap_eq_smul,
      TauCeti.ScalarAut.smul_smulₛₗ, ← TauCeti.ScalarAut.tensorProductMap_eq_smul]
    exact I.smul_mem (σ.symm a) hy
  lie_mem {x y} hy := by
    rw [Set.mem_ofPred_eq, tensorMap_lie]
    exact I.lie_mem hy

private theorem mem_galoisTranslate {σ : A ≃ₐ[R] A} {I : LieIdeal A (A ⊗[R] L)}
    {y : A ⊗[R] L} :
    y ∈ galoisTranslate σ I ↔ TensorProduct.map σ.symm.toLinearMap LinearMap.id y ∈ I :=
  Iff.rfl

/-- A translate of a nilpotent ideal under the scalar-factor action is nilpotent. -/
private theorem isNilpotent_galoisTranslate (σ : A ≃ₐ[R] A) (I : LieIdeal A (A ⊗[R] L))
    [LieRing.IsNilpotent I] : LieRing.IsNilpotent (galoisTranslate σ I) := by
  let g : galoisTranslate σ I →+ I :=
    { toFun y := ⟨TensorProduct.map σ.symm.toLinearMap LinearMap.id y,
        mem_galoisTranslate.mp y.property⟩
      map_zero' := by ext; simp
      map_add' y z := by ext; simp }
  let f : galoisTranslate σ I →ₗ⁅ℤ⁆ I :=
    { g.toIntLinearMap with
      map_lie' {y z} := Subtype.ext (tensorMap_lie σ.symm (y : A ⊗[R] L) z) }
  refine Function.Injective.lieAlgebra_isNilpotent (f := f) fun y z h ↦ Subtype.ext ?_
  have h' : TensorProduct.map σ.symm.toLinearMap LinearMap.id (y : A ⊗[R] L) =
      TensorProduct.map σ.symm.toLinearMap LinearMap.id z := congrArg Subtype.val h
  rwa [TauCeti.ScalarAut.tensorProductMap_eq_smul, TauCeti.ScalarAut.tensorProductMap_eq_smul,
    smul_left_cancel_iff] at h'

/-- **The nilradical of an extension of scalars is stable under the scalar-factor action.** For
every algebra automorphism `σ` of `A`, the map `σ ⊗ id` carries the nilradical of `A ⊗[R] L` into
itself. No finiteness hypothesis is needed. -/
theorem map_mem_nilradical (σ : A ≃ₐ[R] A) {x : A ⊗[R] L}
    (hx : x ∈ nilradical A (A ⊗[R] L)) :
    TensorProduct.map σ.toLinearMap LinearMap.id x ∈ nilradical A (A ⊗[R] L) := by
  obtain ⟨I, hI, hxI⟩ := exists_isNilpotent_ideal_of_mem_nilradical hx
  refine LieIdeal.le_nilradical A _ (galoisTranslate σ I) (isNilpotent_galoisTranslate σ I) ?_
  rwa [mem_galoisTranslate, TauCeti.ScalarAut.tensorProductMap_eq_smul,
    TauCeti.ScalarAut.tensorProductMap_eq_smul, ← AlgEquiv.aut_inv, inv_smul_smul]

end CommRing

section Galois

variable (K L E : Type*) [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  [Field E] [Algebra K E] [IsGalois K E]

/-- **The nilradical commutes with extension of scalars along a Galois extension.** For a
finite-dimensional Lie algebra `L` over `K` and a Galois extension `E / K`, possibly infinite, the
nilradical of `E ⊗[K] L` is the extension of scalars of the nilradical of `L`. In characteristic
zero this applies to an algebraic closure of `K`. The containment `⊇` is
`LieAlgebra.baseChange_nilradical_le`, which holds for every coefficient algebra. -/
@[simp]
theorem nilradical_baseChange :
    nilradical E (E ⊗[K] L) = (nilradical K L).baseChange E := by
  refine le_antisymm ?_ (baseChange_nilradical_le K L E)
  -- The nilradical of `E ⊗[K] L` is Galois-stable, hence extended from an ideal `N` of `L`, which
  -- is nilpotent because nilpotency descends along the field extension.
  obtain ⟨N, hN, -⟩ := (LieSubmodule.existsUnique_baseChange_eq_iff_forall_map_mem
    (nilradical E (E ⊗[K] L))).mpr fun σ _ hx ↦ map_mem_nilradical σ hx
  have : LieRing.IsNilpotent N := by
    rw [← LieIdeal.isNilpotent_baseChange_iff E, hN]
    infer_instance
  rw [← hN, ← LieSubmodule.toSubmodule_le_toSubmodule, LieSubmodule.coe_baseChange,
    LieSubmodule.coe_baseChange]
  exact Submodule.baseChange_mono E
    ((LieSubmodule.toSubmodule_le_toSubmodule _ _).2 (LieIdeal.le_nilradical K L N this))

/-- **Membership in the nilradical may be checked after extending scalars along a Galois
extension.** A vector of a finite-dimensional Lie algebra lies in the nilradical exactly when its
canonical image in the extension of scalars does. -/
theorem one_tmul_mem_nilradical_baseChange_iff (x : L) :
    (1 : E) ⊗ₜ[K] x ∈ nilradical E (E ⊗[K] L) ↔ x ∈ nilradical K L := by
  rw [nilradical_baseChange, LieSubmodule.one_tmul_mem_baseChange_iff]

end Galois

end LieAlgebra
