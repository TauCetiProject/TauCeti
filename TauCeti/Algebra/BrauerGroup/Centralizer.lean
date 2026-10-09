/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BrauerGroup.BaseChange
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.Algebra.CentralSimple.Centralizer.Basic
import TauCeti.Algebra.CentralSimple.Subfield
import TauCeti.RingTheory.Semisimple.EndAlgebra

/-!
# The centralizer of a subfield represents the base change

Let `A` be a finite-dimensional central simple algebra over a field `K`, and let `L ⊆ A` be a
subfield containing `K`. Its centralizer `C_A(L)` is an `L`-algebra, central simple over `L`, and it
represents the base change of `A` to `L`:

  `[L ⊗[K] A] = [C_A(L)]`  in `Br(L)`.

The centralizer is presented here by a central simple `L`-algebra `B` together with a `K`-algebra
homomorphism `g : B →ₐ[K] A` mapping `B` onto it, the subfield being the image of `L` under `g`.
This is the form in which the statement is applied: when `A` is the crossed product of a cocycle of
a finite Galois extension `E/K` and `K ⊆ L ⊆ E`, the crossed product of the restricted cocycle of
`E/L` maps onto `C_A(L)`, so its Brauer class is the base change of `[A]`. That is how base change
of Brauer classes corresponds to restriction in Galois cohomology.

Whether `g` maps `B` onto `C_A(L)` is a dimension count
(`AlgHom.range_eq_centralizer_iff_finrank_mul_finrank_eq`): the image of `g` always lies in the
centralizer, because `L` is central in `B`, and the centralizer theorem
`[L : K] · dim_K C_A(L) = dim_K A` (`TauCeti.finrank_mul_finrank_centralizer_of_isField`) gives the
dimension of the centralizer.

## The argument

Let `T = L ⊗[K] A`, a central simple `L`-algebra, and let `V` be `A` regarded as a `T`-module, with
`l ⊗ a` acting by `x ↦ a x l` (`TauCeti.BaseChangeModule`). Right multiplication through `g` is an
`L`-algebra homomorphism `Bᵐᵒᵖ → End_T V`, because `L` is central in `B`. It is injective because
`Bᵐᵒᵖ` is simple, and onto by the dimension count
`TauCeti.IsSimpleRing.finrank_end_mul_finrank_eq_sq`. Finally `Mₐ(T) ≃ₐ[L] M_b((End_T V)ᵐᵒᵖ)` for
nonzero sizes `a`, `b` (`TauCeti.IsSimpleRing.nonempty_algEquiv_matrix_mulOpposite_end`), and
`(End_T V)ᵐᵒᵖ ≃ₐ[L] B`, so `T` and `B` have the same Brauer class.

## Main results

* `AlgHom.range_eq_centralizer_iff_finrank_mul_finrank_eq`: `g` maps `B` onto the centralizer of
  the image of `L` exactly when `[L : K] · dim_K B = dim_K A`.
* `TauCeti.BrauerGroup.baseChange_mk_eq_mk_of_range_eq_centralizer`: if `g` maps `B` onto the
  centralizer of the image of `L`, then `[L ⊗[K] A] = [B]` in `Br(L)`.

## References

* J.-P. Serre, *Local Fields*, GTM 67 (1979), Chapter X, §5.
* R. S. Pierce, *Associative Algebras*, GTM 88 (1982), Chapters 12 and 13.
-/

public section

namespace TauCeti

open Module
open scoped TensorProduct

section Centralizer

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A] (L : Type*) [Field L]
  [Algebra K L] {B : Type*} [Ring B] [Algebra L B] [Algebra K B] [IsScalarTower K L B]

omit [Algebra K L] [IsScalarTower K L B] in
variable {L} in
/-- The image of `l` in `A` commutes with the image of every element of `B`, because `l` is central
in `B`. -/
private theorem commute_apply_algebraMap (g : B →ₐ[K] A) (b : B) (l : L) :
    g b * g (algebraMap L B l) = g (algebraMap L B l) * g b := by
  rw [← map_mul, ← map_mul, Algebra.commutes]

/-! ### Right multiplication through `g` -/

namespace BaseChangeModule

variable (g : B →ₐ[K] A)

/-- The action of `L ⊗[K] A` on `A` through the subfield `g ∘ algebraMap L B` commutes with right
multiplication by the image of `g`. -/
private theorem toEnd_mul_apply (r : L ⊗[K] A) (x : A) (b : B) :
    toEnd (g.comp (IsScalarTower.toAlgHom K L B)) r (x * g b) =
      toEnd (g.comp (IsScalarTower.toAlgHom K L B)) r x * g b := by
  induction r using TensorProduct.inductionOn with
  | tmul l a =>
    simp only [toEnd_tmul_apply, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', mul_assoc,
      commute_apply_algebraMap]
  | add r s hr hs => simp only [map_add, LinearMap.add_apply, hr, hs, add_mul]

/-- Right multiplication by `g b`, as an endomorphism of the `L ⊗[K] A`-module `A`. -/
private noncomputable def mulRight (b : B) :
    Module.End (L ⊗[K] A) (BaseChangeModule (g.comp (IsScalarTower.toAlgHom K L B))) where
  toFun x := of _ ((of _).symm x * g b)
  map_add' x y := by simp only [map_add, add_mul]
  map_smul' r x := by
    obtain ⟨x, rfl⟩ := (of (g.comp (IsScalarTower.toAlgHom K L B))).surjective x
    simp only [smul_def, LinearEquiv.symm_apply_apply, toEnd_mul_apply L, RingHom.id_apply]

private theorem mulRight_of (b : B) (x : A) :
    mulRight L g b (of _ x) = of _ (x * g b) := by
  simp only [mulRight, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.symm_apply_apply]

/-- Right multiplication through `g`, as an `L`-algebra homomorphism out of `Bᵐᵒᵖ`. -/
private noncomputable def mulRightAlgHom :
    Bᵐᵒᵖ →ₐ[L]
      Module.End (L ⊗[K] A) (BaseChangeModule (g.comp (IsScalarTower.toAlgHom K L B))) where
  toFun b := mulRight L g b.unop
  map_one' := by
    ext x
    obtain ⟨x, rfl⟩ := (of (g.comp (IsScalarTower.toAlgHom K L B))).surjective x
    rw [MulOpposite.unop_one, mulRight_of, map_one g, mul_one, Module.End.one_apply]
  map_mul' b c := by
    ext x
    obtain ⟨x, rfl⟩ := (of (g.comp (IsScalarTower.toAlgHom K L B))).surjective x
    rw [MulOpposite.unop_mul, Module.End.mul_apply, mulRight_of, mulRight_of, mulRight_of,
      map_mul g, mul_assoc]
  map_zero' := by
    ext x
    obtain ⟨x, rfl⟩ := (of (g.comp (IsScalarTower.toAlgHom K L B))).surjective x
    rw [MulOpposite.unop_zero, mulRight_of, map_zero g, mul_zero, map_zero, LinearMap.zero_apply]
  map_add' b c := by
    ext x
    obtain ⟨x, rfl⟩ := (of (g.comp (IsScalarTower.toAlgHom K L B))).surjective x
    rw [MulOpposite.unop_add, LinearMap.add_apply, mulRight_of, mulRight_of, mulRight_of, map_add g,
      mul_add, map_add]
  commutes' l := by
    ext x
    obtain ⟨x, rfl⟩ := (of (g.comp (IsScalarTower.toAlgHom K L B))).surjective x
    simp only [MulOpposite.algebraMap_apply, MulOpposite.unop_op, mulRight_of,
      Module.algebraMap_end_apply, lsmul_of, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']

end BaseChangeModule

/-! ### The centralizer of the subfield -/

variable [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A] [IsSimpleRing B]

/-- **The centralizer of a subfield, through a model.** A `K`-algebra homomorphism `g : B →ₐ[K] A`
out of a simple `L`-algebra maps `B` onto the centralizer of the image of `L` exactly when
`[L : K] · dim_K B = dim_K A`, which is the dimension of that centralizer given by the centralizer
theorem. -/
theorem _root_.AlgHom.range_eq_centralizer_iff_finrank_mul_finrank_eq (g : B →ₐ[K] A) :
    g.range = Subalgebra.centralizer K ((g.comp (IsScalarTower.toAlgHom K L B)).range : Set A) ↔
      finrank K L * finrank K B = finrank K A := by
  set f := g.comp (IsScalarTower.toAlgHom K L B)
  have hf : Function.Injective f := f.toRingHom.injective
  have hg : Function.Injective g := g.toRingHom.injective
  have : FiniteDimensional K L := FiniteDimensional.of_injective f.toLinearMap hf
  have : FiniteDimensional K B := FiniteDimensional.of_injective g.toLinearMap hg
  have hL : finrank K f.range = finrank K L :=
    (AlgEquiv.ofInjective f hf).toLinearEquiv.finrank_eq.symm
  have hB : finrank K g.range = finrank K B :=
    (AlgEquiv.ofInjective g hg).toLinearEquiv.finrank_eq.symm
  have hC := finrank_mul_finrank_centralizer_of_isField f.range
    ((AlgEquiv.ofInjective f hf).symm.toMulEquiv.isField (Field.toIsField L))
  rw [hL] at hC
  constructor
  · intro h
    rw [← hB, h, hC]
  · intro h
    refine Subalgebra.eq_of_le_of_finrank_eq ?_ ?_
    · rintro _ ⟨b, rfl⟩
      rw [Subalgebra.mem_centralizer_iff]
      rintro _ ⟨l, rfl⟩
      exact (commute_apply_algebraMap g b l).symm
    · rw [hB]
      exact Nat.eq_of_mul_eq_mul_left finrank_pos (h.trans hC.symm)

namespace BaseChangeModule

variable (g : B →ₐ[K] A) [FiniteDimensional L B]

/-- When `[L : K] · dim_K B = dim_K A`, that is when `g` maps `B` onto the centralizer of the image
of `L`, right multiplication through `g` is an isomorphism `Bᵐᵒᵖ ≃ End_{L ⊗[K] A} A`. -/
private theorem mulRightAlgHom_bijective
    (hdim : finrank K L * finrank K B = finrank K A) : Function.Bijective (mulRightAlgHom L g) := by
  have hinj : Function.Injective (mulRightAlgHom L g) := (mulRightAlgHom L g).toRingHom.injective
  refine ⟨hinj, ?_⟩
  set f := g.comp (IsScalarTower.toAlgHom K L B)
  -- With `d = [L : K]`, `e = dim_L B` and `n = dim_K A`, the dimension hypothesis reads
  -- `d * d * e = n`, the tower law gives `dim_L A = d * e`, and the dimension of the
  -- endomorphism algebra `X` satisfies `X * n = (d * e)²`; so `X = e`.
  have : FiniteDimensional K L := FiniteDimensional.of_injective f.toLinearMap f.toRingHom.injective
  have hn := hdim
  rw [← Module.finrank_mul_finrank K L B, ← mul_assoc] at hn
  have hV : finrank L (BaseChangeModule f) = finrank K L * finrank L B :=
    Nat.eq_of_mul_eq_mul_left finrank_pos ((finrank_mul_finrank f).trans (by rw [← hn, mul_assoc]))
  have hE := IsSimpleRing.finrank_end_mul_finrank_eq_sq L (R := L ⊗[K] A) (M := BaseChangeModule f)
  rw [Module.finrank_baseChange, hV, ← hn] at hE
  have hX : finrank L (Module.End (L ⊗[K] A) (BaseChangeModule f)) = finrank L Bᵐᵒᵖ := by
    rw [← (MulOpposite.opLinearEquiv L).finrank_eq]
    refine Nat.eq_of_mul_eq_mul_right (m := finrank K L * finrank K L * finrank L B) ?_ ?_
    · rw [hn]
      exact finrank_pos
    · rw [hE]
      ring
  have : FiniteDimensional L (Module.End (L ⊗[K] A) (BaseChangeModule f)) :=
    Module.finite_of_finrank_pos (hX ▸ finrank_pos)
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (mulRightAlgHom L g).toLinearMap) hX.symm).1 hinj

end BaseChangeModule

end Centralizer

/-! ### The Brauer class of the centralizer -/

namespace BrauerGroup

universe u

variable {K : Type u} [Field K] {A : Type u} [Ring A] [Algebra K A] [Algebra.IsCentral K A]
  [IsSimpleRing A] [FiniteDimensional K A] {L : Type u} [Field L] [Algebra K L] {B : Type u}
  [Ring B] [Algebra L B] [Algebra K B] [IsScalarTower K L B] [Algebra.IsCentral L B]
  [IsSimpleRing B] [FiniteDimensional L B]

/-- **The centralizer of a subfield represents the base change** (Serre, *Local Fields*, Chapter X,
§5). Let `A` be a finite-dimensional central simple `K`-algebra and `B` a finite-dimensional
central simple `L`-algebra, and let `g : B →ₐ[K] A` map `B` onto the centralizer of the image of
`L`. Then `B` represents the base change of `A` to `L`: `[L ⊗[K] A] = [B]` in `Br(L)`.

Whether `g` maps onto the centralizer is the dimension count
`AlgHom.range_eq_centralizer_iff_finrank_mul_finrank_eq`. -/
theorem baseChange_mk_eq_mk_of_range_eq_centralizer (g : B →ₐ[K] A)
    (hg : g.range =
      Subalgebra.centralizer K ((g.comp (IsScalarTower.toAlgHom K L B)).range : Set A)) :
    baseChange K L (mk (CSA.of K A)) = mk (CSA.of L B) := by
  have hdim := (g.range_eq_centralizer_iff_finrank_mul_finrank_eq L).1 hg
  set f := g.comp (IsScalarTower.toAlgHom K L B)
  -- `Bᵐᵒᵖ ≃ End_{L ⊗ A} A`, so `(End_{L ⊗ A} A)ᵐᵒᵖ ≃ B`.
  let e : (Module.End (L ⊗[K] A) (BaseChangeModule f))ᵐᵒᵖ ≃ₐ[L] B :=
    AlgEquiv.opComm
      (AlgEquiv.ofBijective _ (BaseChangeModule.mulRightAlgHom_bijective L g hdim)).symm
  obtain ⟨E⟩ :=
    IsSimpleRing.nonempty_algEquiv_matrix_mulOpposite_end L (R := L ⊗[K] A)
      (M := BaseChangeModule f)
  rw [baseChange_mk, mk_eq_mk_iff]
  exact ⟨_, _, finrank_pos.ne', finrank_pos.ne', ⟨E.trans e.mapMatrix⟩⟩

end BrauerGroup

end TauCeti
