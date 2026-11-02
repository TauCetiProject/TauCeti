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

import TauCeti.RingTheory.AdicCompletion.AlgHom

/-!
# Adic completions as limits of commutative rings

Let `I` be an ideal of a commutative ring `R`. The quotients `R ⧸ I ^ (n + 1)` and the quotient
maps `R ⧸ I ^ (n + 1) → R ⧸ I ^ (m + 1)` for `m ≤ n` form a diagram `ℕᵒᵖ ⥤ CommRingCat`, and the
quotient maps `R → R ⧸ I ^ (n + 1)` form a cone over it with apex `R`. If `R` is `I`-adically
complete, this cone is a limit cone: this is the universal property of `R` among commutative
rings, Mathlib's `IsAdicComplete.liftRingHom`, restated in `CommRingCat`.

Without any completeness assumption, the adic completion `AdicCompletion I R` with its
evaluation maps `AdicCompletion I R → R ⧸ I ^ (n + 1)` is a limit cone over the same diagram:
this is Mathlib's universal property `AdicCompletion.liftRingHom`, restated in `CommRingCat`.
It identifies the rings of sections of the formal spectrum over basic open sets, limits of the
sections of the thickenings, with adic completions.

The diagram starts at `R ⧸ I`, not at the zero ring `R ⧸ I ^ 0`. These are the rings of the
thickenings `Spec (R ⧸ I ^ (n + 1))` of `Spec (R ⧸ I)` whose structure sheaves define the formal
spectrum, and the form used to identify its global sections with `R`.

## Main definitions

* `Ideal.quotientPowSuccDiagram I`: the diagram `n ↦ R ⧸ I ^ (n + 1)` of commutative rings.
* `Ideal.quotientPowSuccCone I`: the cone over it with apex `R` given by the quotient maps.
* `AdicCompletion.quotientPowSuccCone I`: the cone over it with apex `AdicCompletion I R` given by
  the evaluation maps.

## Main results

* `IsAdicComplete.isLimitQuotientPowSuccCone`: if `R` is `I`-adically complete, the cone of
  quotient maps is a limit cone.
* `AdicCompletion.isLimitQuotientPowSuccCone`: the cone of evaluation maps is a limit cone.
* `Ideal.factor_comp_quotEquivOfEq_map_pow`: along a ring homomorphism `f : R →+* S`, the
  quotient maps of `S` by the extended ideals `I ^ (n + 1) S` are, through `Ideal.map_pow`, the
  transition maps of `Ideal.quotientPowSuccDiagram (I.map f)`.
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

/-- Read through `Ideal.map_pow`, the quotient map `S ⧸ I ^ (m + 1) S → S ⧸ I ^ (n + 1) S` along
a ring homomorphism `f : R →+* S` is the transition map of the diagram of the quotients of `S` by
the powers of `I S`. -/
theorem factor_comp_quotEquivOfEq_map_pow {S : Type u} [CommRing S] (f : R →+* S) {m n : ℕ}
    (h : n ≤ m) :
    CommRingCat.ofHom (Quotient.factor (map_mono (pow_le_pow_right (I := I)
        (Nat.succ_le_succ h)))) ≫
      CommRingCat.ofHom (quotEquivOfEq (I.map_pow f (n + 1))).toRingHom =
    CommRingCat.ofHom (quotEquivOfEq (I.map_pow f (m + 1))).toRingHom ≫
      (quotientPowSuccDiagram (I.map f)).map (homOfLE h).op := by
  -- both sides send the class of `x ∈ S` to its class. `simp` rewrites the transition map by
  -- `Ideal.quotientPowSuccDiagram_map` but cannot evaluate the resulting composite, whose objects
  -- are the diagram's objects rather than `CommRingCat.of`, so the step is closed by `rfl`
  ext x
  rfl

end Ideal

namespace AdicCompletion

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The cone of evaluation maps `AdicCompletion I R → R ⧸ I ^ (n + 1)` over
`Ideal.quotientPowSuccDiagram I`. -/
@[simps]
noncomputable def quotientPowSuccCone : Cone (Ideal.quotientPowSuccDiagram I) where
  pt := CommRingCat.of (AdicCompletion I R)
  π.app n := CommRingCat.ofHom (evalₐ I (n.unop + 1) : AdicCompletion I R →+* R ⧸ I ^ (n.unop + 1))
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

variable {R : Type u} [CommRing R] {I : Ideal R}

/-- The compatible family of ring homomorphisms `X → R ⧸ I ^ n` underlying a cone with apex `X`
over the diagram of the quotients `R ⧸ I ^ (n + 1)`. -/
private noncomputable def coneFamily (s : Cone (Ideal.quotientPowSuccDiagram I)) (n : ℕ) :
    s.pt →+* R ⧸ I ^ n :=
  (Ideal.Quotient.factorPow I n.le_succ).comp (s.π.app (op n)).hom

private theorem factorPow_comp_coneFamily (s : Cone (Ideal.quotientPowSuccDiagram I)) {m n : ℕ}
    (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow I hmn).comp (coneFamily s n) = coneFamily s m := by
  ext x
  have key (z : R ⧸ I ^ (n + 1)) : Ideal.Quotient.factorPow I hmn
      (Ideal.Quotient.factorPow I n.le_succ z) = Ideal.Quotient.factorPow I m.le_succ
        ((Ideal.quotientPowSuccDiagram I).map (homOfLE hmn).op z) := by
    -- both sides are the class of `y` modulo `I ^ m`. `simp` rewrites the transition map by
    -- `Ideal.quotientPowSuccDiagram_map` but cannot evaluate it on the diagram's objects, which
    -- are not reducibly `CommRingCat.of`, so the step is closed by `rfl`
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    rfl
  exact (key _).trans (congrArg _ congr($(s.w (homOfLE hmn).op).hom x))

variable (I)

/-- The adic completion `AdicCompletion I R` is the limit of the rings `R ⧸ I ^ (n + 1)` in
`CommRingCat`, with the evaluation maps as projections. -/
noncomputable def isLimitQuotientPowSuccCone : IsLimit (quotientPowSuccCone I) where
  lift s := CommRingCat.ofHom <| liftRingHom I (coneFamily s) (factorPow_comp_coneFamily s)
  fac s n := by
    ext x
    exact (evalₐ_liftRingHom I _ (factorPow_comp_coneFamily s) _ x).trans
      congr($(s.w (homOfLE n.unop.le_succ).op).hom x)
  uniq s m hm := by
    ext x
    refine ext_evalₐ fun n ↦ (factor_evalₐ n.le_succ _).symm.trans ?_
    exact (congrArg _ congr($(hm (op n)).hom x)).trans
      (evalₐ_liftRingHom I _ (factorPow_comp_coneFamily s) _ x).symm

end AdicCompletion
