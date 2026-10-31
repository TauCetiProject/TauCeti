/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.RingTheory.AdicCompletion.RingHom

/-!
# An adically complete ring as a limit of commutative rings

Let `I` be an ideal of a commutative ring `R`. The quotients `R ⧸ I ^ (n + 1)` and the quotient
maps `R ⧸ I ^ (n + 1) → R ⧸ I ^ (m + 1)` for `m ≤ n` form a diagram `ℕᵒᵖ ⥤ CommRingCat`, and the
quotient maps `R → R ⧸ I ^ (n + 1)` form a cone over it with apex `R`. If `R` is `I`-adically
complete, this cone is a limit cone: this is the universal property of `R` among commutative
rings, Mathlib's `IsAdicComplete.liftRingHom`, restated in `CommRingCat`.

The diagram starts at `R ⧸ I`, not at the zero ring `R ⧸ I ^ 0`. These are the rings of the
thickenings `Spec (R ⧸ I ^ (n + 1))` of `Spec (R ⧸ I)` whose structure sheaves define the formal
spectrum, and the form used to identify its global sections with `R`.

## Main definitions

* `Ideal.quotientPowSuccDiagram I`: the diagram `n ↦ R ⧸ I ^ (n + 1)` of commutative rings.
* `Ideal.quotientPowSuccCone I`: the cone over it with apex `R` given by the quotient maps.

## Main results

* `IsAdicComplete.isLimitQuotientPowSuccCone`: if `R` is `I`-adically complete, the cone of
  quotient maps is a limit cone.
-/

universe u

open CategoryTheory Limits Opposite

@[expose] public section

namespace Ideal

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The diagram `R ⧸ I ← R ⧸ I ^ 2 ← R ⧸ I ^ 3 ← ⋯` of commutative rings, with the quotient
maps as transitions. -/
@[simps]
noncomputable def quotientPowSuccDiagram : ℕᵒᵖ ⥤ CommRingCat.{u} where
  obj n := CommRingCat.of (R ⧸ I ^ (n.unop + 1))
  map f := CommRingCat.ofHom (Quotient.factor
    (pow_le_pow_right (Nat.succ_le_succ (leOfHom f.unop))))
  map_id _ := by
    ext x
    rfl
  map_comp _ _ := by
    ext x
    rfl

/-- The cone of quotient maps `R → R ⧸ I ^ (n + 1)` over `Ideal.quotientPowSuccDiagram I`. -/
@[simps]
noncomputable def quotientPowSuccCone : Cone (quotientPowSuccDiagram I) where
  pt := CommRingCat.of R
  π.app n := CommRingCat.ofHom (Quotient.mk _)
  π.naturality _ _ _ := by
    ext x
    rfl

end Ideal

end

public section

namespace IsAdicComplete

variable {R : Type u} [CommRing R] (I : Ideal R) [IsAdicComplete I R]

/-- If `R` is `I`-adically complete, then `R` is the limit of the rings `R ⧸ I ^ (n + 1)` in
`CommRingCat`, with the quotient maps as projections. -/
noncomputable def isLimitQuotientPowSuccCone : IsLimit (Ideal.quotientPowSuccCone I) where
  lift s := CommRingCat.ofHom <| StrictMono.liftRingHom I (strictMono_id.add_const 1)
    (fun n ↦ (s.π.app (op n)).hom)
    (CommRingCat.hom_ext_iff.mp (s.w (homOfLE (Nat.le_succ _)).op))
  fac s n := by
    ext1
    exact StrictMono.mk_comp_liftRingHom (n := n.unop) I (strictMono_id.add_const 1) _
      (CommRingCat.hom_ext_iff.mp (s.w (homOfLE (Nat.le_succ _)).op))
  uniq s m hm := by
    ext1
    refine StrictMono.eq_liftRingHom (F := m.hom) I (strictMono_id.add_const 1) _
      (CommRingCat.hom_ext_iff.mp (s.w (homOfLE (Nat.le_succ _)).op)) fun n ↦ ?_
    exact CommRingCat.hom_ext_iff.mp (hm (op n))

end IsAdicComplete
