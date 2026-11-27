/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GroupAlgebra.Block.CentralCharacter.ScalarExtension
public import TauCeti.RepresentationTheory.GroupAlgebra.Split
public import TauCeti.RingTheory.Idempotents.Jacobson
import TauCeti.RingTheory.Semisimple.CentralCharacter

/-!
# Central characters of blocks over a splitting field

A field `k` **splits** a group `G` when every simple `k[G]`-module has endomorphism ring `k`.
Tau Ceti states this, for a finite group, as scalar Schur for finite-dimensional
representations: `∀ V : FDRep k G, Simple V → Module.finrank k (V ⟶ V) = 1` (as in
`TauCeti.nonempty_splitWedderburnAlgebraPresentation_iff_scalarSchur`). Algebraically closed
fields split every finite group (`FDRep.finrank_hom_simple_simple`), and `𝔽₂` splits `S₃` but
not `C₃`.

Over a splitting field every block `B` of `k[G]` has a central character `λ_B : Z(k[G]) → k`.
The block idempotent `e_B` is a nonzero idempotent, so it is not in the Jacobson radical and
some maximal left ideal `I` misses it. The simple module `k[G]/I` has endomorphism ring `k`
because `k` splits `G` (`TauCeti.finrank_end_eq_one_of_scalarSchur`), so its central character
(`TauCeti.centralCharacterOfBijectiveAlgebraMap`) is defined; this gives `λ_B`, and
`λ_B(e_B) = 1` since `e_B` acts by a nonzero idempotent scalar.

With central characters, scalar extension along a field homomorphism `k → k'` keeps blocks
(`TauCeti.IsBlockIdempotent.centerMapRingHom`), and so the blocks of `k'[G]` are exactly the
images of the blocks of `k[G]`; the central character over `k'` of the image of `B` extends
`λ_B`.

## Main results

* `IsIdempotentElem.exists_algHom_apply_eq_one_of_scalarSchur`,
  `TauCeti.IsBlockIdempotent.exists_algHom_apply_eq_one_of_scalarSchur`: over a splitting field
  every nonzero central idempotent, in particular every block idempotent, has a character of
  `Z(k[G])` with value `1` at it.
* `TauCeti.IsBlockIdempotent.apply_centerMapRingHom`: the central character over `k'` of the
  image of a block extends its central character over `k`.
* `TauCeti.IsBlockIdempotent.centerMapRingHom_of_scalarSchur`,
  `TauCeti.exists_isBlockIdempotent_centerMapRingHom_eq_of_scalarSchur`: over a splitting field
  `k`, the blocks of `k'[G]` are exactly the images of the blocks of `k[G]`.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, §9.2 and Proposition 9.2.5,
  pp. 142–143, for splitting fields.
-/

public section

open CategoryTheory
open scoped _root_.MonoidAlgebra

namespace TauCeti

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G] [Finite G]

/-- **Central idempotents have characters over a splitting field.** Let `k` split `G`: every
simple finite-dimensional representation has a one-dimensional endomorphism space. Then every
nonzero central idempotent `e` of `k[G]` has a `k`-algebra homomorphism `φ : Z(k[G]) → k` with
`φ(e) = 1`. -/
theorem _root_.IsIdempotentElem.exists_algHom_apply_eq_one_of_scalarSchur
    (hk : ∀ V : FDRep k G, Simple V → Module.finrank k (V ⟶ V) = 1)
    {e : Subalgebra.center k k[G]} (he : IsIdempotentElem e) (h0 : e ≠ 0) :
    ∃ φ : Subalgebra.center k k[G] →ₐ[k] k, φ e = 1 := by
  have he' : IsIdempotentElem (e : k[G]) := he.map (Subalgebra.center k k[G]).val
  -- A maximal left ideal `I` with `e ∉ I`.
  obtain ⟨I, hI, heI⟩ : ∃ I : Submodule k[G] k[G], IsCoatom I ∧ (e : k[G]) ∉ I := by
    by_contra! h
    have hJ : (e : k[G]) ∈ Ring.jacobson k[G] := Submodule.mem_sInf.2 fun I hI => h I hI
    exact h0 (Subtype.ext (he'.eq_zero_of_mem_jacobson hJ))
  let M := k[G] ⧸ I
  have : IsSimpleModule k[G] M := (isSimpleModule_iff_isCoatom).2 hI
  have hbij := Algebra.finrank_eq_one_iff_bijective_algebraMap.1
    (finrank_end_eq_one_of_scalarSchur hk M)
  have hc := bijective_algebraMap_center_of_bijective hbij
  refine ⟨centralCharacterOfBijectiveAlgebraMap k k[G] M hc, ?_⟩
  rcases (he.map (centralCharacterOfBijectiveAlgebraMap k k[G] M hc)).eq_zero_or_one with h | h
  · -- `e` acts on `k[G]/I` by `0`, so `e = e • 1 ∈ I`.
    refine absurd ?_ heI
    have := smul_eq_centralCharacterOfBijectiveAlgebraMap_smul k k[G] M hc e
      (Submodule.Quotient.mk 1)
    rw [h, zero_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one] at this
    exact (Submodule.Quotient.mk_eq_zero I).1 this
  · exact h

/-- **Blocks have central characters over a splitting field.** If every simple
finite-dimensional representation of `G` over `k` has a one-dimensional endomorphism space, every
block idempotent `e_B` of `k[G]` has a central character `λ_B : Z(k[G]) → k`, `λ_B(e_B) = 1`. -/
theorem IsBlockIdempotent.exists_algHom_apply_eq_one_of_scalarSchur
    (hk : ∀ V : FDRep k G, Simple V → Module.finrank k (V ⟶ V) = 1)
    {b : Subalgebra.center k k[G]} (hb : IsBlockIdempotent b) :
    ∃ φ : Subalgebra.center k k[G] →ₐ[k] k, φ b = 1 :=
  hb.isIdempotentElem.exists_algHom_apply_eq_one_of_scalarSchur hk hb.ne_zero

section ScalarExtension

variable {k' : Type*} [Field k']

/-- **The central character over a larger field extends the central character over `k`.** Let
`f : k →+* k'` be a homomorphism of fields and `e_B` a block idempotent of `k[G]` with a central
character `φ`, `φ(e_B) = 1`. Every `k'`-algebra homomorphism `φ' : Z(k'[G]) → k'` with value `1`
at the image of `e_B` satisfies `φ'(f(z)) = f(φ(z))`. -/
theorem IsBlockIdempotent.apply_centerMapRingHom (f : k →+* k') {b : Subalgebra.center k k[G]}
    (hb : IsBlockIdempotent b) {φ : Subalgebra.center k k[G] →ₐ[k] k} (hφ : φ b = 1)
    {φ' : Subalgebra.center k' k'[G] →ₐ[k'] k'}
    (hφ' : φ' (MonoidAlgebra.centerMapRingHom G f b) = 1)
    (z : Subalgebra.center k k[G]) :
    φ' (MonoidAlgebra.centerMapRingHom G f z) = f (φ z) := by
  set x := z - algebraMap k (Subalgebra.center k k[G]) (φ z) with hx
  have hφx : φ x = 0 := by simp [hx]
  have hnil := (hb.isNilpotent_mul_of_apply_eq_zero hφ hφx).map
    (MonoidAlgebra.centerMapRingHom G f)
  simpa [hφ', hx, sub_eq_zero, MonoidAlgebra.centerMapRingHom_algebraMap] using
    (hnil.map φ').eq_zero

/-- **Blocks stay blocks over an extension of a splitting field.** If every simple
finite-dimensional representation of `G` over `k` has a one-dimensional endomorphism space, the
image of a block idempotent of `k[G]` along a field homomorphism `k → k'` is a block idempotent
of `k'[G]`. -/
theorem IsBlockIdempotent.centerMapRingHom_of_scalarSchur
    (hk : ∀ V : FDRep k G, Simple V → Module.finrank k (V ⟶ V) = 1) (f : k →+* k')
    {b : Subalgebra.center k k[G]} (hb : IsBlockIdempotent b) :
    IsBlockIdempotent (MonoidAlgebra.centerMapRingHom G f b) :=
  hb.centerMapRingHom f (hb.exists_algHom_apply_eq_one_of_scalarSchur hk).choose_spec

/-- **Every block over an extension of a splitting field comes from `k`.** If every simple
finite-dimensional representation of `G` over `k` has a one-dimensional endomorphism space and
`f : k →+* k'` is a homomorphism of fields, every block idempotent of `k'[G]` is the image of a
block idempotent of `k[G]`. -/
theorem exists_isBlockIdempotent_centerMapRingHom_eq_of_scalarSchur
    (hk : ∀ V : FDRep k G, Simple V → Module.finrank k (V ⟶ V) = 1) (f : k →+* k')
    {b' : Subalgebra.center k' k'[G]} (hb' : IsBlockIdempotent b') :
    ∃ b, IsBlockIdempotent b ∧ MonoidAlgebra.centerMapRingHom G f b = b' := by
  obtain ⟨n, e, he, hep⟩ := exists_completeOrthogonalIdempotents_isBlockIdempotent k G
  obtain ⟨i, hi⟩ : ∃ i, b' * MonoidAlgebra.centerMapRingHom G f (e i) ≠ 0 := by
    by_contra! h
    refine hb'.ne_zero ?_
    rw [← mul_one b', ← map_one (MonoidAlgebra.centerMapRingHom G f), ← he.complete, map_sum,
      Finset.mul_sum]
    exact Finset.sum_eq_zero fun i _ => h i
  exact ⟨e i, hep i, (((hep i).centerMapRingHom_of_scalarSchur hk f).eq_of_commute_of_mul_ne_zero
    hb' (Commute.all _ _) (by rwa [mul_comm]))⟩

end ScalarExtension

end TauCeti
