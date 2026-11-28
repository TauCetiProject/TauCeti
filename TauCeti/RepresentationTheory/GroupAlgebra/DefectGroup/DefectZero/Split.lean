/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GroupAlgebra.DefectGroup.DefectZero.Matrix
public import TauCeti.RepresentationTheory.GroupAlgebra.DefectGroup.DefectZero.Simple
public import TauCeti.RepresentationTheory.GroupAlgebra.Split

/-!
# Blocks of defect zero over a splitting field

A field `k` **splits** a finite group `G` when every simple `k[G]`-module has endomorphism ring
`k`; Tau Ceti states this as scalar Schur for finite-dimensional representations,
`∀ V : FDRep k G, Simple V → Module.finrank k (V ⟶ V) = 1`. Over such a field, a block of `k[G]`
has defect group `1` exactly when its block algebra is a matrix algebra `M_n(k)` (Webb,
Corollary 12.4.8, p. 242, with Theorem 9.6.1, p. 161), extending
`TauCeti.IsBlockIdempotent.isDefectGroup_bot_iff_exists_algEquiv_matrix` from algebraically closed
fields.

The route: a block `e` of defect group `1` has a simple block algebra `e k[G]`
(`TauCeti.IsBlockIdempotent.isSimpleRing_blockAlgebra_of_isDefectGroup_bot`), which by
Wedderburn–Artin is `M_n(D^op)` for `D` the endomorphism ring of a simple left ideal `I`. Along
the surjection `k[G] → e k[G]`, `I` is a simple `k[G]`-module with the same endomorphisms, so
`D = k` because `k` splits `G` (`TauCeti.finrank_end_eq_one_of_scalarSchur_of_surjective`). The
converse holds over any field (`TauCeti.IsBlockIdempotent.isDefectGroup_bot_of_algEquiv_matrix`).

The splitting hypothesis is needed: over `𝔽₂`, which does not split `C₃`, the block `r + r²` of
`𝔽₂[C₃]` has defect group `1` and block algebra `𝔽₄`, which is not a matrix algebra over `𝔽₂`.

## Main results

* `TauCeti.IsBlockIdempotent.exists_algEquiv_matrix_of_isDefectGroup_bot_of_scalarSchur`: over a
  field splitting `G`, a block of defect group `1` is a matrix algebra `M_n(k)`.
* `TauCeti.IsBlockIdempotent.isDefectGroup_bot_iff_exists_algEquiv_matrix_of_scalarSchur`: over
  a field splitting `G`, a block has defect group `1` exactly when it is a matrix algebra over `k`.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Theorem 9.6.1, p. 161, and
  Corollary 12.4.8, p. 242.
-/

public section

open CategoryTheory

universe u v

namespace TauCeti

variable {k : Type u} {G : Type v} [Field k] [Group G] [Finite G]

namespace IsBlockIdempotent

variable {p : ℕ} [CharP k p] {b : Subalgebra.center k (MonoidAlgebra k G)}

/-- **A block of defect zero over a splitting field is a matrix algebra.** If every simple
finite-dimensional representation of `G` over `k` has a one-dimensional endomorphism space and `1`
is a defect group of a block idempotent `e` of `k[G]`, `k` of characteristic `p`, then the block
algebra `e k[G]` is isomorphic to `M_n(k)` for some `n > 0` (Webb, Corollary 12.4.8, p. 242, with
Theorem 9.6.1, p. 161). -/
theorem exists_algEquiv_matrix_of_isDefectGroup_bot_of_scalarSchur
    (hk : ∀ V : FDRep k G, Simple V → Module.finrank k (V ⟶ V) = 1) (hb : IsBlockIdempotent b)
    (hD : IsDefectGroup k p (b : MonoidAlgebra k G) ⊥) :
    ∃ (n : ℕ) (_ : NeZero n), Nonempty (hb.BlockAlgebra ≃ₐ[k] Matrix (Fin n) (Fin n) k) := by
  have := hb.isSemisimpleRing_blockAlgebra_of_isDefectGroup_bot hD
  have := hb.isSimpleRing_blockAlgebra_of_isDefectGroup_bot hD
  have : IsScalarTower k hb.BlockAlgebra hb.BlockAlgebra :=
    ⟨fun c x y ↦ Subtype.ext (smul_mul_assoc c x.val y.val)⟩
  have := IsArtinianRing.of_finite k hb.BlockAlgebra
  obtain ⟨n, hn, I, hI, ⟨ψ⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_end_mulOpposite k
    hb.BlockAlgebra
  -- The endomorphism ring of the simple left ideal `I` is `k`.
  let φ := hb.isIdempotentElem_val.compressAlgHom k (Set.mem_center_iff.mp b.property)
  have hfin := finrank_end_eq_one_of_scalarSchur_of_surjective hk φ
    (IsIdempotentElem.compressAlgHom_surjective _ _ _) I
  have := Module.Free.of_divisionRing k (Module.End hb.BlockAlgebra I)
  let χ : (Module.End hb.BlockAlgebra I)ᵐᵒᵖ ≃ₐ[k] k :=
    (AlgEquiv.op (Module.nonempty_algEquiv_iff_finrank_eq_one.mpr hfin).some.symm).trans
      (AlgEquiv.toOpposite k k).symm
  exact ⟨n, hn, ⟨ψ.trans χ.mapMatrix⟩⟩

variable [Fact p.Prime]

/-- **Defect zero over a splitting field.** If every simple finite-dimensional representation of
`G` over `k` has a one-dimensional endomorphism space, a block idempotent `e` of `k[G]`, `k` a
field of characteristic `p`, has defect group `1` exactly when its block algebra `e k[G]` is a
matrix algebra `M_n(k)` (Webb, Corollary 12.4.8, p. 242, with Theorem 9.6.1, p. 161). -/
theorem isDefectGroup_bot_iff_exists_algEquiv_matrix_of_scalarSchur
    (hk : ∀ V : FDRep k G, Simple V → Module.finrank k (V ⟶ V) = 1) (hb : IsBlockIdempotent b) :
    IsDefectGroup k p (b : MonoidAlgebra k G) ⊥ ↔
      ∃ n : ℕ, Nonempty (hb.BlockAlgebra ≃ₐ[k] Matrix (Fin n) (Fin n) k) := by
  refine ⟨fun hD ↦ ?_, fun ⟨n, ⟨ψ⟩⟩ ↦ hb.isDefectGroup_bot_of_algEquiv_matrix ψ⟩
  obtain ⟨n, -, hψ⟩ := hb.exists_algEquiv_matrix_of_isDefectGroup_bot_of_scalarSchur hk hD
  exact ⟨n, hψ⟩

end IsBlockIdempotent

end TauCeti
