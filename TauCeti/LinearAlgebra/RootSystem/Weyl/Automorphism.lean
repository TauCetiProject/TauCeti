/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Bases
import TauCeti.LinearAlgebra.RootSystem.HomInvariance

/-!
# Root systems whose automorphisms are all Weyl

An automorphism `u` of a finite reduced crystallographic root system carries a base `b` to a base,
and the Weyl group acts simply transitively on the bases
(`RootPairing.Base.existsUnique_map_eq`). So `u = w v` with `w` in the Weyl group and `v` carrying
`b` onto itself. Such a `v` permutes the simple roots of `b` by a symmetry of the Cartan matrix,
and, when the roots span the weight space, `v` is determined by that permutation. Hence, when the
Cartan matrix of `b` has no nontrivial symmetry, every automorphism lies in the Weyl group.

This is the half of the decomposition `Aut(Φ) = W(Φ) ⋊ Aut(Dynkin diagram)` needed to identify
the full automorphism group of a root system of rigid type, such as `E₈`, with its Weyl group.

## Main results

* `RootPairing.Base.eq_one_of_forall_indexEquiv_eq`: an automorphism of a root system fixing every
  simple root of a base is the identity.
* `RootPairing.Base.mem_support_map_iff`: the simple roots of a transported base.
* `RootPairing.Base.weylGroup_eq_top_of_matrixSymmetryGroup_eq_bot`: **if the Cartan matrix of a
  base has no nontrivial symmetry, every automorphism lies in the Weyl group.**
* `TauCeti.HasCartanType.weylGroup_eq_top`: the same for a base of a Dynkin type whose diagram has
  no nontrivial symmetry, and `TauCeti.weylGroup_eq_top_of_hasCartanType_E8` its instance for
  `E₈`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.5, Proposition 16 and §4,
  Plate VII.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §12.2.
-/

public section

namespace TauCeti

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

/-- **An automorphism of a root system fixing every simple root of a base is the identity.** The
simple roots span the root span, which is everything for a root system. -/
theorem _root_.RootPairing.Base.eq_one_of_forall_indexEquiv_eq [P.IsRootSystem] (b : P.Base)
    {u : P.Aut} (hu : ∀ i ∈ b.support, u.indexEquiv i = i) : u = 1 := by
  apply RootPairing.Equiv.weightHom_injective P
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.ext_on (s := P.root '' b.support) ?_ ?_
  · rw [b.span_root_support, RootPairing.rootSpan, RootPairing.IsRootSystem.span_root_eq_top]
  · rintro _ ⟨i, hi, rfl⟩
    simp [RootPairing.Hom.root_weightMap_apply, hu i hi]

/-- A root index is simple for the transported base `b.map e` exactly when its preimage under `e`
is simple for `b`. -/
theorem _root_.RootPairing.Base.mem_support_map_iff (b : P.Base) (e : P.Aut) (j : ι) :
    j ∈ (b.map e).support ↔ e.indexEquiv.symm j ∈ b.support := by
  classical
  rw [RootPairing.Base.support_map_eq, Finset.mem_image]
  exact ⟨by rintro ⟨i, hi, rfl⟩; simpa using hi, fun h ↦ ⟨_, h, by simp⟩⟩

variable [Finite ι] [IsDomain R] [CharZero R] [P.IsCrystallographic] [P.IsReduced]

/-- **If the Cartan matrix of a base has no nontrivial symmetry, every automorphism of the root
system lies in the Weyl group.** -/
theorem _root_.RootPairing.Base.weylGroup_eq_top_of_matrixSymmetryGroup_eq_bot [P.IsRootSystem]
    (b : P.Base) (hb : matrixSymmetryGroup b.cartanMatrix = ⊥) : P.weylGroup = ⊤ := by
  classical
  refine eq_top_iff.mpr fun u _ ↦ ?_
  obtain ⟨w, hw, -⟩ := b.existsUnique_map_eq (b.map u)
  -- The automorphism `w⁻¹ u` carries the simple roots of `b` onto themselves.
  have hsupp (i : ι) : ((w : P.Aut)⁻¹ * u).indexEquiv i ∈ b.support ↔ i ∈ b.support := by
    have hidx :
        ((w : P.Aut)⁻¹ * u).indexEquiv i = (w : P.Aut).indexEquiv.symm (u.indexEquiv i) := by
      simp
    rw [hidx, ← b.mem_support_map_iff, hw, b.mem_support_map_iff, Equiv.symm_apply_apply]
  -- The permutation it induces on the simple roots preserves the Cartan matrix, so is trivial.
  have hσ := hb.le (show Equiv.Perm.subtypePerm _ hsupp ∈ matrixSymmetryGroup b.cartanMatrix by
    refine mem_matrixSymmetryGroup_iff.mpr (Matrix.ext fun i j ↦ ?_)
    simp only [Matrix.submatrix_apply, Equiv.Perm.subtypePerm_apply, RootPairing.Base.cartanMatrix,
      RootPairing.Base.cartanMatrixIn_def]
    exact RootPairing.Hom.pairingIn_indexEquiv _ ℤ (i : ι) j)
  have hv : (w : P.Aut)⁻¹ * u = 1 := b.eq_one_of_forall_indexEquiv_eq fun i hi ↦ by
    simpa using congrArg Subtype.val (Equiv.ext_iff.mp (Subgroup.mem_bot.mp hσ) ⟨i, hi⟩)
  rw [inv_mul_eq_one] at hv
  exact hv ▸ w.2

/-- **A root system with a base of a Dynkin type whose diagram has no nontrivial symmetry has
every automorphism in its Weyl group.** -/
theorem HasCartanType.weylGroup_eq_top [P.IsRootSystem] {b : P.Base} {t : DynkinType}
    (h : HasCartanType P b t) (ht : t.diagramSymmetry = ⊥) : P.weylGroup = ⊤ := by
  obtain ⟨e, he⟩ := (hasCartanType_iff b t).mp h
  refine b.weylGroup_eq_top_of_matrixSymmetryGroup_eq_bot
    ((Subgroup.eq_bot_iff_forall _).mpr fun σ hσ ↦ ?_)
  -- Transport `σ` along the labelling of the simple roots by the nodes of `t`.
  have hτ : e.symm.trans (σ.trans e) ∈ t.diagramSymmetry :=
    DynkinType.mem_diagramSymmetry_iff.mpr fun i j ↦ by
      have hij := congrFun₂ (mem_matrixSymmetryGroup_iff.mp hσ) (e.symm i) (e.symm j)
      rw [Matrix.submatrix_apply, he, he, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hij
      simpa only [Equiv.trans_apply] using hij
  ext i
  have hi := Equiv.ext_iff.mp (Subgroup.mem_bot.mp (ht.le hτ)) (e i)
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.Perm.coe_one, id_eq] at hi
  simp [e.injective hi]

/-- **Every automorphism of a root system of type `E₈` lies in its Weyl group.** -/
theorem weylGroup_eq_top_of_hasCartanType_E8 [P.IsRootSystem] {b : P.Base}
    (h : HasCartanType P b .E8) : P.weylGroup = ⊤ :=
  h.weylGroup_eq_top DynkinType.diagramSymmetry_E8_eq_bot

end TauCeti
