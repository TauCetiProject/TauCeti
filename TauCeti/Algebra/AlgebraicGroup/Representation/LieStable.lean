/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Smooth.LieAlgebra
public import TauCeti.Algebra.AlgebraicGroup.Representation.Stabilizer
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero

/-!
# Lie-stable subspaces in characteristic zero

Let `G` be a connected affine group of finite type over an algebraically closed field `k` of
characteristic zero, and `M` a representation of `G`, that is, a comodule over its coordinate
Hopf algebra `H`. A subspace `W ≤ M` is a subrepresentation exactly when it is stable under the
differentiated action of the Lie algebra `Lie(G)`.

One direction holds over any base ring: subcomodules are stable under the differentiated action.
For the converse, the Lie algebra of the stabilizer `G_W` of `W` consists of the tangent vectors
preserving `W`, so `Lie(G_W) = Lie(G)`. In characteristic zero both groups are smooth, by
Cartier's theorem, so `G_W = G` because `G` is connected.

Both hypotheses are needed. In characteristic `p` the line spanned by `xᵖ` in the regular
representation of `𝔾ₐ` is killed by `Lie(𝔾ₐ)`, but its coaction `xᵖ ⊗ 1 + 1 ⊗ xᵖ` does not lie
in it. A nontrivial finite constant group has zero Lie algebra, so every subspace of its regular
representation is `Lie`-stable.

This is the bridge that lets complete reducibility of `Lie(G)`-representations be transported to
representations of `G` in characteristic zero.

## Main declarations

* `Submodule.coact_mem_range_of_forall_differential_mem`: in characteristic zero, the coaction of
  a vector of a `Lie(G)`-stable subspace `W` lies in `W ⊗ H`.
* `Submodule.exists_subcomodule_iff_forall_differential_mem`: in characteristic zero, a subspace
  is a subcomodule exactly when it is `Lie(G)`-stable.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 10.
* J. E. Humphreys, *Linear Algebraic Groups*, §13 (characteristic zero theory).
-/

public section

open TauCeti

universe u w

namespace Submodule

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} [ConnectedSpace (PrimeSpectrum H)]
variable {M : Type w} [AddCommGroup M] [Module k M] [Comodule k H M]

/-- In characteristic zero, the coaction of a vector of a subspace stable under the
differentiated action of the Lie algebra of a connected group lies in the tensor product of the
subspace with the coordinate algebra. -/
theorem coact_mem_range_of_forall_differential_mem (W : Submodule k M)
    (hW : ∀ d : Derivation k H (Bialgebra.CounitAlgebra k H k), ∀ w ∈ W,
      Comodule.differential (R := k) (H := H) (M := M) d w ∈ W)
    {w : M} (hw : w ∈ W) :
    Comodule.coact (R := k) (C := H) (M := M) w ∈
      LinearMap.range (TensorProduct.map W.subtype (LinearMap.id : H →ₗ[k] H)) := by
  let _ : Algebra.Smooth k H :=
    (smoothCommHopfAlgProperty_iff _).mp (smoothCommHopfAlgProperty_of_charZero k H.obj)
  let _ : Algebra.Smooth k (H ⧸ (W.stabilizerHopfIdeal H).toIdeal) :=
    (smoothCommHopfAlgProperty_iff _).mp (smoothCommHopfAlgProperty_of_charZero k
      (_root_.CommHopfAlgCat.of k (H ⧸ (W.stabilizerHopfIdeal H).toIdeal)))
  have hlie : (W.stabilizerHopfIdeal H).lieSubalgebra (B := k) = ⊤ :=
    eq_top_iff.mpr fun d _ ↦ (mem_lieSubalgebra_stabilizerHopfIdeal_iff W d).mpr (hW d)
  exact (stabilizerHopfIdeal_eq_bot_iff W).mp (HopfIdeal.eq_bot_of_lieSubalgebra_eq_top _ hlie)
    w hw

/-- In characteristic zero, a subspace of a representation of a connected group over an
algebraically closed field is a subrepresentation exactly when it is stable under the
differentiated action of the Lie algebra. -/
theorem exists_subcomodule_iff_forall_differential_mem (W : Submodule k M) :
    (∃ N : Subcomodule k H M, N.toSubmodule = W) ↔
      ∀ d : Derivation k H (Bialgebra.CounitAlgebra k H k), ∀ w ∈ W,
        Comodule.differential (R := k) (H := H) (M := M) d w ∈ W := by
  constructor
  · rintro ⟨N, rfl⟩ d w hw
    exact N.differential_mem d hw
  · intro hW
    exact ⟨⟨W, fun _ hw ↦ coact_mem_range_of_forall_differential_mem W hW hw⟩, rfl⟩

end Submodule
