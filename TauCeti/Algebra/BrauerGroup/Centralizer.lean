/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BrauerGroup.BaseChange
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
(`AlgHom.range_eq_centralizer_iff_finrank_mul_finrank_eq`, in
`TauCeti/Algebra/CentralSimple/Centralizer/Basic.lean`): the image of `g` always lies in the
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
