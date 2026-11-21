/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.GroupTheory.GroupAction.Quotient
public import TauCeti.CategoryTheory.Groupoid.ActionCategory.Map
import Mathlib.Algebra.Group.Action.Prod
import Mathlib.Algebra.Group.Equiv.Opposite

/-!
# The double-coset action groupoid

For subgroups `H, K ≤ G`, retain both changes of representative in the quotient of `G` by
`(h, k) • g = h * g * k⁻¹`. The resulting action groupoid, unlike the set of double cosets,
remembers stabilizers. Quotienting by the free right action first gives an equivalent groupoid:
`H` acting on `G ⧸ K`. The right component of an arrow between `x` and `y` is forced by its
left component `h`, since `h * x = y * k`.

In particular, for `H = K` the identity representative has automorphism group `H`, embedded
by the diagonal labels. This is the group-level calculation for two trivializations in the
local Hecke stack of Fargues and Scholze, *Geometrization of the local Langlands correspondence*,
VI.1.6–VI.1.7; no assertion about torsor descent or stackification is made here.
-/

public section

open CategoryTheory

namespace DoubleCoset

variable {G : Type*} [Group G] (H K : Subgroup G)

/-- The action by left multiplication in `H` and inverse right multiplication in `K`.
The instance is scoped since an action by a product is not canonical in general. -/
scoped instance instMulAction : MulAction (H × K) G :=
  let φ := (MulEquiv.inv' G).toMonoidHom.comp K.subtype
  letI := MulAction.compHom G φ
  letI : SMulCommClass H K G := ⟨fun h k x ↦ (mul_assoc (h : G) x (k : G)⁻¹).symm⟩
  MulAction.prodOfSMulCommClass H K G

/-- The right component acts by its inverse, so the two components compose in the same order. -/
@[simp]
theorem smul_eq_mul_mul_inv (p : H × K) (x : G) :
    p • x = (p.1 : G) * x * (p.2 : G)⁻¹ :=
  (mul_assoc _ _ _).symm

/-- The double-coset action groupoid, with objects `g : G` and arrows labelled by pairs in
`H × K`. -/
abbrev ActionGroupoid := ActionCategory (H × K) G

/-- Taking the coset `xK` forgets the right label of an arrow, keeping its left label. -/
def toLeftCosets : ActionGroupoid H K ⥤ ActionCategory H (G ⧸ K) :=
  ActionCategory.map (MonoidHom.fst H K) {
    toFun := QuotientGroup.mk
    map_smul' := fun p x ↦ by
      rw [smul_eq_mul_mul_inv, MonoidHom.coe_fst, Subgroup.smul_def,
        MulAction.Quotient.smul_mk, smul_eq_mul]
      exact QuotientGroup.mk_mul_of_mem _ (K.inv_mem p.2.property) }

/-- The point underlying the image object is the coset of the representative. -/
@[simp]
theorem back_toLeftCosets_obj (x : ActionGroupoid H K) :
    ((toLeftCosets H K).obj x).back = (x.back : G ⧸ K) :=
  ActionCategory.back_map_obj ..

/-- Its arrow label is the first component of the original label. -/
@[simp]
theorem toLeftCosets_map_hom {x y : ActionGroupoid H K} (f : x ⟶ y) :
    ((toLeftCosets H K).map f).hom = (f.hom : H × K).1 :=
  ActionCategory.map_map_hom ..

/-- An arrow's right label is determined by its left label and by the two endpoints. -/
theorem coe_hom_snd_eq {x y : ActionGroupoid H K} (f : x ⟶ y) :
    ((f.hom : H × K).2 : G) = y.back⁻¹ * ((f.hom.1 : G) * x.back) := by
  have hf := (smul_eq_mul_mul_inv H K _ _).symm.trans f.map_val
  exact eq_inv_mul_iff_mul_eq.mpr (mul_inv_eq_iff_eq_mul.mp hf).symm

/-- For fixed endpoints, a left label between the cosets determines a unique arrow between
representatives. -/
def fullyFaithfulToLeftCosets : (toLeftCosets H K).FullyFaithful where
  preimage {x y} f := by
    let h : H := f.hom
    have hf : h • ((toLeftCosets H K).obj x).back = ((toLeftCosets H K).obj y).back := f.map_val
    have hk : y.back⁻¹ * ((h : G) * x.back) ∈ K := by
      rw [back_toLeftCosets_obj, back_toLeftCosets_obj, Subgroup.smul_def,
        MulAction.Quotient.smul_coe, smul_eq_mul] at hf
      exact QuotientGroup.eq.mp hf.symm
    exact Functor.Elements.homMk (h, ⟨_, hk⟩)
      (by
        -- The carrier of the action functor is `G`; use `back` to expose its group operations.
        change (h, (⟨_, hk⟩ : K)) • x.back = y.back
        rw [smul_eq_mul_mul_inv, mul_inv_eq_iff_eq_mul]
        simp)
  map_preimage f := Functor.Elements.hom_ext (toLeftCosets_map_hom H K _)
  preimage_map f := by
    apply Functor.Elements.hom_ext
    simp only [toLeftCosets_map_hom]
    exact Prod.ext rfl (Subtype.ext (coe_hom_snd_eq H K f).symm)

/-- Quotienting the free right action first gives an equivalent groupoid. -/
instance : (toLeftCosets H K).IsEquivalence where
  full := (fullyFaithfulToLeftCosets H K).full
  faithful := (fullyFaithfulToLeftCosets H K).faithful
  essSurj := ⟨fun y ↦ by
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective y.back
    refine ⟨(x : ActionGroupoid H K), ⟨eqToIso (ActionCategory.back_injective ?_)⟩⟩
    simpa only [back_toLeftCosets_obj, ActionCategory.coe_back] using hx⟩

/-- At the identity representative with equal subgroups, the automorphisms are precisely
pairs of equal labels, with their original group law. -/
def diagonalAutEquiv : H ≃* Aut (ActionCategory.objEquiv (H × H) G (1 : G)) :=
  let e : H ≃* MulAction.stabilizer (H × H) (1 : G) :=
    { toFun h := ⟨(h, h), MulAction.mem_stabilizer_iff.mpr (by simp)⟩
      invFun p := p.val.1
      left_inv _ := rfl
      right_inv p := by
        have hp := MulAction.mem_stabilizer_iff.mp p.property
        have hp' : (p.val.1 : G) = (p.val.2 : G) := by simpa [mul_inv_eq_one] using hp
        exact Subtype.ext (Prod.ext rfl (Subtype.ext hp'))
      map_mul' _ _ := rfl }
  e.trans (ActionCategory.stabilizerMulEquivAut (H × H) (1 : G))

/-- The automorphism corresponding to `h` has label `(h, h)`. -/
@[simp]
theorem diagonalAutEquiv_apply_hom_hom (h : H) :
    (diagonalAutEquiv H h).asIso.hom.hom = (h, h) := by
  simp [diagonalAutEquiv]

/-- The inverse equivalence reads the left label of the automorphism. -/
@[simp]
theorem diagonalAutEquiv_symm_apply (e : Aut (ActionCategory.objEquiv (H × H) G (1 : G))) :
    (diagonalAutEquiv H).symm e = (e.asIso.hom.hom : H × H).1 :=
  congrArg Prod.fst (ActionCategory.coe_stabilizerMulEquivAut_symm_apply _ e)

end DoubleCoset
