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
public import TauCeti.RingTheory.AdicCompletion.AlgHom

/-!
# Adic completions as limits of commutative rings

Let `I` be an ideal of a commutative ring `R`. The quotients `R ⧸ I ^ (n + 1)` and the quotient
maps `R ⧸ I ^ (n + 1) → R ⧸ I ^ (m + 1)` for `m ≤ n` form a diagram `ℕᵒᵖ ⥤ CommRingCat`, and the
quotient maps `R → R ⧸ I ^ (n + 1)` form a cone over it with apex `R`. If `R` is `I`-adically
complete, this cone is a limit cone: this is the universal property of `R` among commutative
rings, Mathlib's `IsAdicComplete.liftRingHom`, restated in `CommRingCat`. For an arbitrary ring
`R`, the adic completion `AdicCompletion I R` with its projections `R ⧸ I ^ (n + 1)` is a limit
cone over the same diagram, by the universal property `AdicCompletion.liftRingHom`.

The diagram starts at `R ⧸ I`, not at the zero ring `R ⧸ I ^ 0`. These are the rings of the
thickenings `Spec (R ⧸ I ^ (n + 1))` of `Spec (R ⧸ I)` whose structure sheaves define the formal
spectrum, and the form used to identify its global sections with `R`.

## Main definitions

* `Ideal.quotientPowSuccDiagram I`: the diagram `n ↦ R ⧸ I ^ (n + 1)` of commutative rings.
* `Ideal.quotientPowSuccCone I`: the cone over it with apex `R` given by the quotient maps.
* `AdicCompletion.quotientPowSuccCone I`: the cone over it with apex `AdicCompletion I R` given by
  the projections `AdicCompletion.evalₐ I (n + 1)`.

## Main results

* `IsAdicComplete.isLimitQuotientPowSuccCone`: if `R` is `I`-adically complete, the cone of
  quotient maps is a limit cone.
* `AdicCompletion.isLimitQuotientPowSuccCone`: the adic completion is the limit of the rings
  `R ⧸ I ^ (n + 1)`.
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

namespace AdicCompletion

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The cone of projections `AdicCompletion I R → R ⧸ I ^ (n + 1)` over
`Ideal.quotientPowSuccDiagram I`. -/
@[simps]
noncomputable def quotientPowSuccCone : Cone (Ideal.quotientPowSuccDiagram I) where
  pt := CommRingCat.of (AdicCompletion I R)
  π.app n := CommRingCat.ofHom (evalₐ I (n.unop + 1)).toRingHom
  π.naturality _ _ f := by
    ext x
    exact (factor_evalₐ (Nat.succ_le_succ (leOfHom f.unop)) x).symm

end AdicCompletion

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

namespace AdicCompletion

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The leg `s.pt → R ⧸ I ^ (n + 1)` of a cone over `Ideal.quotientPowSuccDiagram I`, typed as a
ring homomorphism into the quotient. The objects of the diagram are these quotients only after
unfolding `Ideal.quotientPowSuccDiagram`, so the proofs below state the legs with this type in order
to compose and rewrite them with the quotient maps. -/
private noncomputable def leg (s : Cone (Ideal.quotientPowSuccDiagram I)) (n : ℕ) :
    s.pt →+* R ⧸ I ^ (n + 1) :=
  (s.π.app (op n)).hom

private theorem factor_comp_leg (s : Cone (Ideal.quotientPowSuccDiagram I)) {m n : ℕ}
    (hle : m ≤ n) :
    (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right hle 1))).comp
      (leg I s n) = leg I s m :=
  CommRingCat.hom_ext_iff.mp (s.w (homOfLE hle).op)

/-- A cone over `Ideal.quotientPowSuccDiagram I` gives a compatible family of ring homomorphisms
to all the quotients `R ⧸ I ^ n`, starting at the zero ring `R ⧸ I ^ 0`. -/
private theorem factorPow_comp_factor_comp_leg (s : Cone (Ideal.quotientPowSuccDiagram I))
    {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow I hle).comp
        ((Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_add_right n 1))).comp
          (leg I s n)) =
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_add_right m 1))).comp
        (leg I s m) := by
  rw [← factor_comp_leg I s hle]
  simp only [Ideal.Quotient.factorPow, ← RingHom.comp_assoc, Ideal.Quotient.factor_comp]

/-- The adic completion `AdicCompletion I R` is the limit of the rings `R ⧸ I ^ (n + 1)` in
`CommRingCat`, with the projections `evalₐ I (n + 1)`. -/
noncomputable def isLimitQuotientPowSuccCone : IsLimit (quotientPowSuccCone I) where
  lift s := CommRingCat.ofHom <| liftRingHom I
    (fun n ↦ (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_add_right n 1))).comp
      (leg I s n))
    (factorPow_comp_factor_comp_leg I s)
  fac s n := by
    ext x
    exact (evalₐ_liftRingHom I _ (factorPow_comp_factor_comp_leg I s) _ x).trans
      congr($(factor_comp_leg I s (Nat.le_add_right n.unop 1)) x)
  uniq s m hm := by
    ext x
    refine ext_evalₐ fun n ↦ ?_
    cases n with
    | zero =>
      have : Subsingleton (R ⧸ I ^ 0) :=
        Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.one_eq_top])
      exact Subsingleton.elim _ _
    | succ n =>
      have hm' : evalₐ I (n + 1) (m x) = leg I s n x := congr($(hm (op n)) x)
      exact hm'.trans ((evalₐ_liftRingHom I _ (factorPow_comp_factor_comp_leg I s) _ x).trans
        congr($(factor_comp_leg I s (Nat.le_add_right n 1)) x)).symm

end AdicCompletion
