/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Projective.RadicalExt
public import TauCeti.RingTheory.Idempotents.Corner.RadicalLayer
public import TauCeti.RingTheory.Idempotents.Projective
public import TauCeti.RingTheory.Idempotents.Simple.Top
import TauCeti.RingTheory.Idempotents.Jacobson
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Extensions between simple tops and corners of the first radical layer

Let `A` be an algebra over a field `k`, with Jacobson radical `J`, and let `e : ι → A` be a
complete family of orthogonal idempotents whose classes span `A ⧸ J` over `k`. This is the
situation of a basic algebra over an algebraically closed field
(`TauCeti.IsBasic.exists_completeOrthogonalIdempotents`), and of a bound quiver algebra with its
vertex idempotents. When moreover every `eᵢ` is nonzero, `A ⧸ J` is one copy of `k` for each
index. Write `Sᵢ = Aeᵢ / J(Aeᵢ)` for the top of the projective left ideal `Aeᵢ`. This file
proves that, whenever `eⱼ ≠ 0`,

`Ext¹_A(Sᵢ, Sⱼ) ≃ Homₖ(eⱼ (J / J²) eᵢ, k)`,

so that `dimₖ Ext¹_A(Sᵢ, Sⱼ)` is the dimension of the `(j, i)`-corner of the first radical
layer `J / J²`. A basis of that corner is the set of arrows `i → j` of the quiver of a basic
algebra, as in its bound-quiver presentation
(`TauCeti.IsBasic.exists_surjective_pathAlgebra_isAdmissibleIdeal_ker`), so the arrow counts of
that quiver are those of the Ext-quiver.

The proof has three steps.

* A module `M` killed by `J` is a module over `A ⧸ J`, a product of copies of `k`, so an
  `A`-linear map from `M` to a module on which `eⱼ` acts as the identity is the same as a
  `k`-linear map out of the piece `eⱼ M`
  (`CompleteOrthogonalIdempotents.linearMapEquivSMulTopLinearMap`). The top `Sⱼ` is such a
  module, and for `eⱼ ≠ 0` it is the line spanned by the class of `eⱼ`
  (`CompleteOrthogonalIdempotents.equivQuotientSMulTop`).
  Composing with the inverse of that line identifies the maps `M → Sⱼ` with the dual of `eⱼ M`
  (`CompleteOrthogonalIdempotents.linearMapEquivDual`).
* For idempotents `f` and `g` and any two-sided ideal `J`, the piece `f M` of the first radical
  layer `M = J(Ag) / J²(Ag)` of `Ag` is the corner `f (J / J²) g`
  (`IsIdempotentElem.smulTopRadicalLayerEquiv`).
* The extensions of `Sᵢ` are computed from the first radical layer of `Aeᵢ` by
  `Submodule.radicalLayerHomEquivExt`.

The first two steps live in `TauCeti.RingTheory.Idempotents.Simple.Top` and
`TauCeti.RingTheory.Idempotents.Corner.RadicalLayer`.

## Main definitions

* `CompleteOrthogonalIdempotents.extQuotientSMulTopEquivDual`: the linear equivalence
  `Ext¹_A(Sᵢ, Sⱼ) ≃ₗ[k] Dual k (eⱼ (J / J²) eᵢ)`.

## Main results

* `CompleteOrthogonalIdempotents.finrank_ext_quotient_smul_top`: `dimₖ Ext¹_A(Sᵢ, Sⱼ)` is the
  dimension of the corner `eⱼ (J / J²) eᵢ`.

## Implementation notes

The Ext comparison takes `k` and `A` in one universe: `Ext` is computed in `ModuleCat A` by
`Submodule.radicalLayerHomEquivExt`, whose module universe must contain both the base field and
the left ideals `Aeᵢ`. The `k`-module structure on `Ext` is the one `ModuleCat` puts on its
objects (`ModuleCat.Algebra`), which is not definitionally the quotient-module structure on
`Sⱼ`; the general statements are therefore stated for arbitrary compatible `k`-module
structures.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, Lemma III.2.12, and Section II.3 for the quiver of a basic algebra.
-/

public section

open CategoryTheory CategoryTheory.Abelian
open scoped Pointwise

namespace CompleteOrthogonalIdempotents

open TauCeti

section Ext

open scoped ModuleCat.Algebra

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
  {ι : Type*} [Fintype ι] {e : ι → A}

/-- **Extensions between simple tops are the duals of the radical-layer corners.** Let `e` be
a complete family of orthogonal idempotents of a `k`-algebra `A` whose classes span `A ⧸ J`,
where `J` is the Jacobson radical, and write `Sᵢ = A eᵢ / J (A eᵢ)`. For `e j ≠ 0`,

`Ext¹_A(Sᵢ, Sⱼ) ≃ₗ[k] Homₖ(eⱼ (J / J²) eᵢ, k)`.

This is the linear algebra behind reading the arrows `i → j` of the quiver of a basic algebra
as `dimₖ Ext¹_A(Sᵢ, Sⱼ)`. -/
noncomputable def extQuotientSMulTopEquivDual (he : CompleteOrthogonalIdempotents e)
    (hquot : Submodule.span k
      (Set.range fun i ↦ Ideal.Quotient.mk (Ring.jacobson A) (e i)) = ⊤)
    (i j : ι) (hj : e j ≠ 0) :
    Ext (ModuleCat.of A ((Ideal.span {e i} : Ideal A) ⧸
        Ring.jacobson A • (⊤ : Submodule A (Ideal.span {e i} : Ideal A))))
      (ModuleCat.of A ((Ideal.span {e j} : Ideal A) ⧸
        Ring.jacobson A • (⊤ : Submodule A (Ideal.span {e j} : Ideal A)))) 1 ≃ₗ[k]
      Module.Dual k (radicalLayerCorner k (Ring.jacobson A) (e j) (e i)) := by
  have hjJ : e j ∉ Ring.jacobson A := fun h ↦
    hj ((he.idem j).eq_zero_of_mem_jacobson_bot (Ideal.jacobson_bot (R := A) ▸ h))
  have := (he.idem i).projective_span_singleton
  have := he.isSimpleModule_quotient_smul_top hquot j hjJ
  let P := ModuleCat.of A (Ideal.span {e i} : Ideal A)
  let S := ModuleCat.of A ((Ideal.span {e j} : Ideal A) ⧸
    Ring.jacobson A • (⊤ : Submodule A (Ideal.span {e j} : Ideal A)))
  -- `Ext` is a `k`-module through the `k`-module structure that `ModuleCat` puts on `S`, which
  -- is not definitionally the quotient-module structure; make the former the local instance.
  letI : Module k S := ModuleCat.Algebra.instModuleCarrier
  haveI := ModuleCat.Algebra.instIsScalarTowerCarrier (S₀ := k) (M := S)
  exact (Submodule.radicalLayerHomEquivExt.{u, u, u} (k := k) (P := P)
      (Ring.jacobson A • (⊤ : Submodule A P)) (Ring.jacobson_smul_top_le A P) S).symm ≪≫ₗ
    he.linearMapEquivDual (N := S) hquot
      (Module.isTorsionBySet_quotient_ideal_smul _ _)
      (Module.isTorsionBySet_quotient_ideal_smul _ _) j (he.smul_quotient_smul_top_eq_self hquot j)
      _ (mk_spanSingletonGenerator_ne_zero hjJ) exists_smul_mk_spanSingletonGenerator_eq ≪≫ₗ
    ((he.idem j).smulTopRadicalLayerEquiv (he.idem i)).symm.dualMap

/-- **The arrow count of the Ext-quiver.** Under the hypotheses of
`CompleteOrthogonalIdempotents.extQuotientSMulTopEquivDual`, `dimₖ Ext¹_A(Sᵢ, Sⱼ)` is the
dimension of the corner `eⱼ (J / J²) eᵢ` of the first radical layer. -/
theorem finrank_ext_quotient_smul_top (he : CompleteOrthogonalIdempotents e)
    (hquot : Submodule.span k
      (Set.range fun i ↦ Ideal.Quotient.mk (Ring.jacobson A) (e i)) = ⊤)
    (i j : ι) (hj : e j ≠ 0) :
    Module.finrank k (Ext (ModuleCat.of A ((Ideal.span {e i} : Ideal A) ⧸
        Ring.jacobson A • (⊤ : Submodule A (Ideal.span {e i} : Ideal A))))
      (ModuleCat.of A ((Ideal.span {e j} : Ideal A) ⧸
        Ring.jacobson A • (⊤ : Submodule A (Ideal.span {e j} : Ideal A)))) 1) =
      Module.finrank k (radicalLayerCorner k (Ring.jacobson A) (e j) (e i)) := by
  rw [(he.extQuotientSMulTopEquivDual hquot i j hj).finrank_eq, Subspace.dual_finrank_eq]

end Ext

end CompleteOrthogonalIdempotents
