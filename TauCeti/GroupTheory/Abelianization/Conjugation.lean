/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.End
public import Mathlib.GroupTheory.Abelianization.Defs
public import TauCeti.GroupTheory.GroupAction.ConjAct

/-!
# Conjugation on the abelianization of a normal subgroup

Let `N` be a normal subgroup of a group `G`. Conjugation by `g ∈ G` is an automorphism of `N`, so
it induces an automorphism of the abelianization `N^{ab}`. Conjugation by an element of `N` itself
is inner, hence invisible in `N^{ab}`, so the action factors through `G ⧸ N`: this file makes
`N^{ab}` a `G ⧸ N`-module, with `(g : G ⧸ N) • [n] = [g n g⁻¹]` (`Abelianization.mk_smul_of`).

For `N = G'` the commutator subgroup, the acting group is `G ⧸ G' = G^{ab}`, and `G' ⧸ G''` is the
`G^{ab}`-module whose extension class is that of `G ⧸ G''`; this is the coefficient module in
which the transfer `G → G' ⧸ G''` takes its values. The instance for `Abelianization G` is
recorded separately, because `Abelianization G` is not reducibly `G ⧸ commutator G`.

## Main definitions

* `Abelianization.conjAut N`: conjugation by `G ⧸ N` on `N^{ab}`, as a homomorphism to the
  automorphism group.
* The instance `MulDistribMulAction (G ⧸ N) (Abelianization N)`, and its specialization
  `MulDistribMulAction (Abelianization G) (Abelianization (commutator G))`.

## Main results

* `Abelianization.mk_smul_of`: the class of `g` sends the class of `n` to the class of
  `g * n * g⁻¹`.
* `Abelianization.of_smul_of`: the same for the action of `G^{ab}` on `G' ⧸ G''`.
-/

public section

namespace Abelianization

variable {G : Type*} [Group G]

/-- Two isomorphisms out of an abelianization agree if they agree on the classes of elements. -/
theorem mulEquiv_ext {H M : Type*} [Group H] [Monoid M] {e e' : Abelianization H ≃* M}
    (h : ∀ x : H, e (of x) = e' (of x)) : e = e' :=
  MulEquiv.toMonoidHom_injective (hom_ext _ _ (MonoidHom.ext h))

variable (N : Subgroup G) [N.Normal]

/-- **Conjugation by `G ⧸ N` on `N^{ab}`**: conjugation by `g ∈ G` on `N`, carried to `N^{ab}`,
which depends only on the class of `g` because elements of `N` act by inner automorphisms. -/
noncomputable def conjAut : G ⧸ N →* MulAut (Abelianization N) :=
  QuotientGroup.lift N
    { toFun g := (MulAut.conjNormal g).abelianizationCongr
      map_one' := mulEquiv_ext fun x ↦ by simp
      map_mul' g h := mulEquiv_ext fun x ↦ by simp }
    fun g hg ↦ MonoidHom.mem_ker.2 <| mulEquiv_ext fun x ↦ by
      simpa using MonoidHom.map_conjNormal_val (of : N →* _) ⟨g, hg⟩ x

/-- `conjAut N` sends the class of `g` to conjugation by `g` on classes. -/
theorem conjAut_mk_of (g : G) (n : N) :
    conjAut N g (of n) = of (MulAut.conjNormal g n) := by
  rw [conjAut, QuotientGroup.lift_mk]
  simp

/-- **The conjugation action of `G ⧸ N` on `N^{ab}`**, given by `conjAut N`. -/
noncomputable instance instMulDistribMulActionQuotient :
    MulDistribMulAction (G ⧸ N) (Abelianization N) :=
  MulDistribMulAction.compHom _ (conjAut N)

/-- Applying the automorphism `conjAut N q` is the action of `q`. -/
theorem conjAut_apply (q : G ⧸ N) (x : Abelianization N) : conjAut N q x = q • x := (rfl)

/-- **The defining equation of the action of `G ⧸ N` on `N^{ab}`**: the class of `g` sends the
class of `n` to the class of `g * n * g⁻¹`. -/
@[simp]
theorem mk_smul_of (g : G) (n : N) :
    (g : G ⧸ N) • of n = of (MulAut.conjNormal g n) := by
  rw [← conjAut_apply, conjAut_mk_of]

/-- The conjugation action of `G^{ab}` on `G' ⧸ G''`. -/
noncomputable instance instMulDistribMulActionCommutator :
    MulDistribMulAction (Abelianization G) (Abelianization (commutator G)) :=
  inferInstanceAs (MulDistribMulAction (G ⧸ commutator G) _)

/-- The class of `g` in `G^{ab}` acts on `G' ⧸ G''` as conjugation by `g`. -/
@[simp]
theorem of_smul_of (g : G) (n : commutator G) : of g • of n = of (MulAut.conjNormal g n) :=
  mk_smul_of _ g n

end Abelianization
