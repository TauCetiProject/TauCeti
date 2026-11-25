/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.Reductive.CompleteReducibility
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Faithful

/-!
# Reductivity of closed subgroups of `GL_n` through the standard representation

Let `k` be a field of characteristic zero and `H` the coordinate Hopf algebra of an affine group
of finite type over `k`, given with a surjective Hopf algebra morphism
`f : O(GL_n) → H`, that is, as a closed subgroup of `GL_n`. Its standard representation
`TauCeti.GeneralLinear.corestrictStandardComodule k n f` on `kⁿ` is faithful. When `H` is
geometrically connected, `H` is reductive exactly when this representation is completely
reducible (`TauCeti.reductiveCommHopfAlgProperty_iff_isCompletelyReducible_corestrict`):
reductive groups in characteristic zero have completely reducible representations
(`TauCeti.Comodule.isCompletelyReducible_of_reductive`), and conversely a faithful completely
reducible representation makes a connected group reductive
(`TauCeti.reductiveCommHopfAlgProperty_of_isFaithful_of_isCompletelyReducible`).

This is the form in which reductivity of a Mumford–Tate group is proved: `MT(V) ⊆ GL(V)` is
geometrically connected, and `V` is completely reducible under it when `V` is polarizable.

## References

* J. S. Milne, *Algebraic Groups* (2017), §22.
* J. S. Milne, *Shimura varieties and moduli*, proof of Corollary 6.5.
-/

public section

namespace TauCeti

universe u

/-- **A connected closed subgroup of `GL_n` in characteristic zero is reductive exactly when its
standard representation is completely reducible.** -/
theorem reductiveCommHopfAlgProperty_iff_isCompletelyReducible_corestrict
    {k : Type u} [Field k] [CharZero k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hconnected : geometricallyConnectedCommHopfAlgProperty k H.obj) {n : ℕ}
    (f : GeneralLinear.coordinateHopfAlgebra k n →ₐc[k] H) (hf : Function.Surjective f) :
    reductiveCommHopfAlgProperty k H ↔
      letI := GeneralLinear.corestrictStandardComodule k n f
      Comodule.IsCompletelyReducible k H (Fin n → k) := by
  let _ := GeneralLinear.corestrictStandardComodule k n f
  exact ⟨fun hH ↦ Comodule.isCompletelyReducible_of_reductive hH, fun hcr ↦
    reductiveCommHopfAlgProperty_of_isFaithful_of_isCompletelyReducible H hconnected
      (GeneralLinear.isFaithful_corestrictStandardComodule k n f hf) hcr⟩

end TauCeti
