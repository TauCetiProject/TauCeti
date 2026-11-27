/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.ChevalleyRestriction
import TauCeti.Algebra.DirectSum.Internal
import TauCeti.LinearAlgebra.SymmetricAlgebra.DegreeFiltration

/-!
# Chevalley's restriction isomorphism preserves the degree filtration

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over an algebraically
closed field of characteristic zero and `H` a Cartan subalgebra. Chevalley's restriction
isomorphism `S(L)^L ≃ₐ S(H)^W` (`LieSubalgebra.lieChevalleyRestrictionIso H`) preserves degrees in
both directions: an invariant has degree at most `n` exactly when its restriction to `H` does
(`LieSubalgebra.lieChevalleyRestrictionIso_mem_wordFiltration_iff`). Main has the homogeneous form
(`LieSubalgebra.lieChevalleyRestrictionIso_mem_homogeneousSubmodule_iff`).

The restriction is graded, so it maps the homogeneous component of degree `m` of `p` to the
component of degree `m` of the restriction (`TauCeti.lieCartanRestriction_decompose`). If the
restriction has degree at most `n`, its components above `n` vanish; the corresponding components
of `p` are invariant (the invariants are graded) and restrict to zero, so they vanish by
injectivity of the restriction on invariants. Hence `p` is the sum of its components of degree at
most `n`.

## Main results

* `TauCeti.lieCartanRestriction_decompose`: restriction commutes with the homogeneous components.
* `LieSubalgebra.lieChevalleyRestrictionIso_mem_wordFiltration_iff`: Chevalley's isomorphism
  preserves the degree filtration in both directions.
-/

public section

open LieAlgebra LieAlgebra.IsKilling _root_.LieModule Module TauCeti TauCeti.SymmetricAlgebra
  TauCeti.Algebra

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [IsKilling K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

namespace TauCeti

omit [CharZero K] [FiniteDimensional K L] in
/-- **Restriction to `H` commutes with the homogeneous components**: it maps the component of
degree `m` of `p` to the component of degree `m` of the restriction of `p`. -/
theorem lieCartanRestriction_decompose (p : _root_.SymmetricAlgebra K L) (m : ℕ) :
    lieCartanRestriction H (DirectSum.decompose (homogeneousSubmodule K L) p m :
        _root_.SymmetricAlgebra K L) =
      (DirectSum.decompose (homogeneousSubmodule K H) (lieCartanRestriction H p) m :
        _root_.SymmetricAlgebra K H) :=
  DirectSum.map_decompose_shift (homogeneousSubmodule K L) (homogeneousSubmodule K H)
    (lieCartanRestriction H).toLinearMap.toAddMonoidHom id Function.injective_id
    (fun _ _ hq ↦ lieCartanRestriction_mem_homogeneousSubmodule H hq) m p

end TauCeti

namespace LieSubalgebra

variable [IsAlgClosed K] [IsTriangularizable K H L]

/-- **Chevalley's restriction isomorphism preserves degrees**: an invariant has degree at most `n`
exactly when its restriction to `H` has. -/
theorem lieChevalleyRestrictionIso_mem_wordFiltration_iff {p : lieInvariants K L L} {n : ℕ} :
    (H.lieChevalleyRestrictionIso p : _root_.SymmetricAlgebra K H) ∈
        wordFiltration (_root_.SymmetricAlgebra.ι K H) n ↔
      (p : _root_.SymmetricAlgebra K L) ∈ wordFiltration (_root_.SymmetricAlgebra.ι K L) n := by
  classical
  rw [coe_lieChevalleyRestrictionIso_apply]
  refine ⟨fun hq ↦ ?_, fun hp ↦ map_mem_wordFiltration _ _ _ (fun x ↦ ?_) hp⟩
  · -- the components of `p` above `n` restrict to zero, so vanish
    have hzero (m : ℕ) (hm : n < m) :
        (DirectSum.decompose (homogeneousSubmodule K L) (p : _root_.SymmetricAlgebra K L) m :
          _root_.SymmetricAlgebra K L) = 0 := by
      refine lieCartanRestriction_injOn_lieInvariants H
        (decompose_mem_lieInvariants p.property m) (zero_mem _) ?_
      rw [lieCartanRestriction_decompose, map_zero]
      exact coe_decompose_eq_zero_of_mem_wordFiltration hm hq
    rw [← DirectSum.sum_support_decompose (homogeneousSubmodule K L)
      (p : _root_.SymmetricAlgebra K L)]
    refine Submodule.sum_mem _ fun m _ ↦ ?_
    rcases le_or_gt m n with hmn | hmn
    · exact wordFiltration_mono _ hmn
        (range_pow_le_wordFiltration _ m (SetLike.coe_mem _))
    · rw [hzero m hmn]
      exact zero_mem _
  · rw [lieCartanRestriction_ι]
    exact apply_mem_wordFiltration_one _ _

end LieSubalgebra
