/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.MulSign
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Extension.FiberProd
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Twist
public import TauCeti.Topology.VectorBundle.SpinStructure.Orientation

/-!
# Twisting a Spin structure by a principal `ℤ/2`-bundle

Let `s` be a Spin structure of rank `n ≥ 1` on a real vector bundle `V` with fibre inner products,
with principal `Spin(n)`-bundle `P`, and let `L` be a principal `ℤ/2`-bundle (a double cover) over
the same base, where `ℤ/2 = Multiplicative (ZMod 2)` is the kernel `{1, -1}` of
`Spin(n) → SO(n)`. The **twist** `s.twist L` (`TauCeti.SpinStructure.twist`) is the Spin structure
with principal bundle

`P ⊗ L = (P ×_X L) ×_μ Spin(n)`,

the twist of lifts of the orthonormal frame bundle (`TauCeti.OrthonormalFrameLift.twist`) along
the multiplication by the central signs `μ : Spin(n) × ℤ/2 → Spin(n)`, `(g, ε) ↦ g ε`
(`CliffordAlgebra.realCliffordSpinMulSign`): the extension of structure group of the fibre product
`P ×_X L` along `μ`. Equivalently, `P ⊗ L` is the quotient of `P ×_X L` by `ℤ/2` acting by
`(p, l) • ε = (p ε, l ε)`; in terms of transition functions, it multiplies the transition functions
of `P` by the `±1`-valued transition functions of `L` (this description is not formalized here).
The construction follows the twist of `Spinᶜ` structures by principal `U(1)`-bundles
(`TauCeti.SpinCStructure.twist`), with the central circle replaced by the central signs; both are
instances of the general twist.

Since the signs act trivially on frames, the frame of `[(p, l), a]` is the frame of `p` composed
with the rotation of `a` (`TauCeti.OrthonormalFrameLift.toFrame_twist_mk`). In particular the
twist induces the same orientation of `V` as `s` (`TauCeti.SpinStructure.orientation_twist`).
Twisting is functorial in `s` and `L` (`TauCeti.OrthonormalFrameLift.twistEquiv`) and commutes
with pullback (`TauCeti.OrthonormalFrameLift.twistPullbackEquiv`); twisting by the trivial double
cover does nothing (`TauCeti.SpinStructure.twistTrivialEquiv`). Twisting is an involution:
twisting twice by the same double cover gives back `s` (`TauCeti.SpinStructure.twistTwistEquiv`),
by `[([(p, l), a], l'), b] ↦ p • a ε b`, where `ε` is the sign with `l' = l • ε`. This last fact
uses that every sign squares to one.

This is the action of the double covers of the base on the Spin structures inducing a fixed
orientation of `V`. On paracompact Hausdorff bases the double covers are classified by
`H¹(X; ℤ/2)`, and the action on equivalence classes of Spin structures is free and transitive;
none of these statements is proved here.

## Main definitions

* `TauCeti.SpinStructure.twist`: the twist of a Spin structure by a principal `ℤ/2`-bundle.
* `TauCeti.SpinStructure.twistTrivialEquiv`: the twist by the trivial double cover is equivalent to
  the Spin structure.
* `TauCeti.SpinStructure.twistTwistEquiv`: twisting twice by the same double cover is equivalent
  to the Spin structure.

## Main results

* `TauCeti.SpinStructure.fiberOrientation_twist`, `TauCeti.SpinStructure.orientation_twist`: the
  twist induces the orientation induced by `s`.
* `TauCeti.SpinStructure.twistTwistEquiv_toEquiv_inl`: the formula of the untwisting equivalence.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Chapter II,
  §1, Theorem 1.7.
* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 3rd ed., World Scientific, 2020,
  Remark 12.2.28.
-/

public section

open Bundle MulOpposite CliffordAlgebra TauCeti.PrincipalBundle

namespace TauCeti

namespace SpinStructure

open OrthonormalFrameLift

variable {X : Type*} [TopologicalSpace X] {F : Type*} {V : X → Type}
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F V]
  [VectorBundle ℝ F V] {n : ℕ} [NeZero n]
  (L : X → Type) [TopologicalSpace (TotalSpace (Multiplicative (ZMod 2)) L)]
  [∀ x, TopologicalSpace (L x)] [FiberBundle (Multiplicative (ZMod 2)) L]
  [∀ x, MulAction (Multiplicative (ZMod 2))ᵐᵒᵖ (L x)] [PrincipalBundle (Multiplicative (ZMod 2)) L]

/-- The cyclic group of order two, the kernel `{1, -1}` of `Spin(n) → SO(n)`. -/
local notation "C₂" => Multiplicative (ZMod 2)

/-- The vector action `Spin(n) → SO(n) ⊆ GL(ℝⁿ)` along which Spin structures lift the
orthonormal frame bundle. -/
local notation "ρS" => MonoidHom.comp
  (Subgroup.subtype (QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)))
  (spinToSpecialOrthogonal (realCliffordForm n 0))

/-- The vector action of `Spin(n)` preserves the Euclidean norm of `ℝⁿ`. -/
local notation "hn" => fun g v ↦
  CliffordAlgebra.norm_toLp_specialOrthogonalGroup_realCliffordForm_apply n
    (spinToSpecialOrthogonal (realCliffordForm n 0) g) v

/-- The vector action of `Spin(n)` on a fixed vector is continuous in the group element. -/
local notation "hc" => fun v ↦ Continuous.comp
  (CliffordAlgebra.continuous_specialOrthogonalGroup_realCliffordForm_apply n v)
  (continuous_spinToSpecialOrthogonal_pi (realCliffordForm n 0))

/-- The **twist of a Spin structure by a principal `ℤ/2`-bundle** `L`: the Spin structure with
principal bundle `(P ×_X L) ×_μ Spin(n)`, the twist of lifts (`TauCeti.OrthonormalFrameLift.twist`)
along multiplication by the central signs `μ : (g, ε) ↦ g ε`. The frame of `[(p, l), a]` is the
frame of `p` composed with the rotation of `a` (`TauCeti.OrthonormalFrameLift.toFrame_twist_mk`).
It is reducible, so that the general API of `TauCeti.OrthonormalFrameLift.twist` applies to it. -/
noncomputable abbrev twist (s : SpinStructure F V n) : SpinStructure F V n :=
  OrthonormalFrameLift.twist s L (realCliffordSpinMulSign n) (continuous_realCliffordSpinMulSign n)
    (subtype_comp_spinToSpecialOrthogonal_comp_realCliffordSpinMulSign n) hn hc

variable {L} (s : SpinStructure F V n)

/-- **Twisting preserves the orientation of the fibres**: the twist of `s` by `L` induces on each
fibre the orientation induced by `s`. -/
@[simp]
theorem fiberOrientation_twist (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) (x : X) :
    (s.twist L).fiberOrientation o x = s.fiberOrientation o x := by
  obtain ⟨z⟩ := (s.fiberProd C₂ L).nonempty_P x
  set p := FiberProd.fst (P := s.P) (Q := L) z
  have hf : (s.twist L).toFrame
      ⟨x, Extend.inl (realCliffordSpinMulSign n) (continuous_realCliffordSpinMulSign n)
        (P := (s.fiberProd C₂ L).P) (FiberProd.mk p (FiberProd.snd (P := s.P) (Q := L) z))⟩ =
      s.toFrame ⟨x, p⟩ :=
    toFrame_twist_inl s _ _ _ _ _ x p _
  have h := (s.twist L).toOrientationCover_toFrame o
    ⟨x, Extend.inl (realCliffordSpinMulSign n) (continuous_realCliffordSpinMulSign n)
      (P := (s.fiberProd C₂ L).P) (FiberProd.mk p (FiberProd.snd (P := s.P) (Q := L) z))⟩
  rw [hf, s.toOrientationCover_toFrame, VectorBundleOrientationCover.mk_eq_mk_iff] at h
  exact h.symm

/-- **Twisting preserves the orientation**: the twist of `s` by `L` induces the orientation of `V`
induced by `s`. -/
@[simp]
theorem orientation_twist (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) :
    (s.twist L).orientation o = s.orientation o := by
  ext x
  rw [orientation_apply, orientation_apply, fiberOrientation_twist]

/-- **Twisting by the trivial double cover changes nothing**: the twist of a Spin structure `s` by
the trivial principal `ℤ/2`-bundle is equivalent to `s`, by `[(p, ε), a] ↦ p • ε a`
(`TauCeti.OrthonormalFrameLift.twistTrivialEquiv_toEquiv_mk`). -/
noncomputable abbrev twistTrivialEquiv : (s.twist (Bundle.Trivial X C₂)).Equiv s :=
  OrthonormalFrameLift.twistTrivialEquiv s (realCliffordSpinMulSign n)
    (continuous_realCliffordSpinMulSign n)
    (subtype_comp_spinToSpecialOrthogonal_comp_realCliffordSpinMulSign n) hn hc
    (realCliffordSpinMulSign_comp_inl n)

/-! ### Twisting twice -/

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F V] [VectorBundle ℝ F V] in
/-- The point `p • ε` of `P`, for `((p, l), l')` in `(P ×_X L) ×_X L` and `ε` the sign with
`l' = l • ε`. It is the untwisting map of `TauCeti.SpinStructure.twistTwistEquiv` on
representatives. -/
private noncomputable def untwist (x : X)
    (z : ((s.fiberProd C₂ L).fiberProd C₂ L).P x) : s.P x :=
  op ((realCliffordSpinDoubleCoverZero n).inl (division C₂ z.fst.snd z.snd)) • z.fst.fst

/-- Multiplication by the central signs on the first factor lifts the double first projection
along the vector action. -/
private theorem comp_fst_comp_prodMap_eq :
    (MonoidHom.comp ρS (MonoidHom.fst _ C₂)).comp
        ((realCliffordSpinMulSign n).prodMap (MonoidHom.id C₂)) =
      (MonoidHom.comp ρS (MonoidHom.fst _ C₂)).comp (MonoidHom.fst _ C₂) :=
  MonoidHom.ext fun g ↦ DFunLike.congr_fun
    (subtype_comp_spinToSpecialOrthogonal_comp_realCliffordSpinMulSign n) g.1

/-- Multiplication by the central signs, applied twice, lifts the double first projection along
the vector action. -/
private theorem comp_comp_prodMap_eq :
    MonoidHom.comp ρS ((realCliffordSpinMulSign n).comp
        ((realCliffordSpinMulSign n).prodMap (MonoidHom.id C₂))) =
      (MonoidHom.comp ρS (MonoidHom.fst _ C₂)).comp (MonoidHom.fst _ C₂) :=
  MonoidHom.ext fun g ↦
    (DFunLike.congr_fun (subtype_comp_spinToSpecialOrthogonal_comp_realCliffordSpinMulSign n)
      ((realCliffordSpinMulSign n).prodMap (MonoidHom.id C₂) g)).trans
    (DFunLike.congr_fun (subtype_comp_spinToSpecialOrthogonal_comp_realCliffordSpinMulSign n) g.1)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F V] [VectorBundle ℝ F V] in
private theorem untwist_smul (x : X) (z : ((s.fiberProd C₂ L).fiberProd C₂ L).P x)
    (g : (realCliffordSpinGroupZero n × C₂) × C₂) :
    untwist s x (op g • z) =
      op ((realCliffordSpinMulSign n).comp ((realCliffordSpinMulSign n).prodMap
        (MonoidHom.id C₂)) g) • untwist s x z := by
  obtain ⟨⟨a, ε⟩, ε'⟩ := g
  -- In `ℤ/2` every element is its own inverse.
  have inv_mul_mul_eq : ∀ ε d ε' : C₂, ε⁻¹ * d * ε' = d * (ε * ε') := by decide
  have key (d : C₂) : a * (realCliffordSpinDoubleCoverZero n).inl (ε⁻¹ * d * ε') =
      (realCliffordSpinDoubleCoverZero n).inl d *
        realCliffordSpinMulSign n (realCliffordSpinMulSign n (a, ε), ε') := by
    -- Both sides are `a d ε ε'`, since the sign `d` commutes with `a`.
    rw [inv_mul_mul_eq]
    simp only [realCliffordSpinMulSign_apply, map_mul, ← mul_assoc,
      (realCliffordSpinDoubleCoverZero_inl_commute n d a).eq]
  simp only [untwist, OrthonormalFrameLift.fiberProd_fst_smul,
    OrthonormalFrameLift.fiberProd_snd_smul, unop_op, division_smul_left, division_smul_right,
    smul_smul, ← op_mul]
  exact congrArg (fun g ↦ op g • _) (key _)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F V] [VectorBundle ℝ F V] in
private theorem continuous_untwist :
    Continuous fun z : TotalSpace ((realCliffordSpinGroupZero n × C₂) × C₂)
        ((s.fiberProd C₂ L).fiberProd C₂ L).P ↦
      (⟨z.proj, untwist s z.proj z.snd⟩ : TotalSpace (realCliffordSpinGroupZero n) s.P) := by
  refine Continuous.totalSpaceMk_smul (G := realCliffordSpinGroupZero n)
    (f := fun z : TotalSpace ((realCliffordSpinGroupZero n × C₂) × C₂)
      ((s.fiberProd C₂ L).fiberProd C₂ L).P ↦ z.proj)
    (p := fun z ↦ z.snd.fst.fst)
    (FiberProd.continuous_totalSpaceMk_fst.comp FiberProd.continuous_totalSpaceMk_fst) ?_
  exact (continuous_of_discreteTopology (f := ⇑(realCliffordSpinDoubleCoverZero n).inl)).comp
    (Continuous.division
      (FiberProd.continuous_totalSpaceMk_snd.comp FiberProd.continuous_totalSpaceMk_fst)
      FiberProd.continuous_totalSpaceMk_snd)

/-- **Twisting twice by the same double cover gives back the Spin structure**:
`(s.twist L).twist L ≃ s`, by `[([(p, l), a], l'), b] ↦ p • a ε b`, where `ε` is the sign with
`l' = l • ε` (`TauCeti.SpinStructure.twistTwistEquiv_toEquiv_inl`). It holds because every sign
squares to one. -/
noncomputable def twistTwistEquiv : ((s.twist L).twist L).Equiv s :=
  (((s.fiberProd C₂ L).extendFiberProdEquiv L (realCliffordSpinMulSign n)
      (continuous_realCliffordSpinMulSign n)
      (subtype_comp_spinToSpecialOrthogonal_comp_realCliffordSpinMulSign n) hn hc).symm.extend
    (realCliffordSpinMulSign n) (continuous_realCliffordSpinMulSign n)
    (subtype_comp_spinToSpecialOrthogonal_comp_realCliffordSpinMulSign n) hn hc).trans <|
  (((s.fiberProd C₂ L).fiberProd C₂ L).extendCompEquiv
    (ρ' := MonoidHom.comp ρS (MonoidHom.fst _ C₂))
    ((realCliffordSpinMulSign n).prodMap (MonoidHom.id C₂))
    ((continuous_realCliffordSpinMulSign n).prodMap continuous_id)
    comp_fst_comp_prodMap_eq (fun k v ↦ hn k.1 v) (fun v ↦ (hc v).comp continuous_fst)
    (realCliffordSpinMulSign n) (continuous_realCliffordSpinMulSign n)
    (subtype_comp_spinToSpecialOrthogonal_comp_realCliffordSpinMulSign n) hn hc).symm.trans <|
  ((s.fiberProd C₂ L).fiberProd C₂ L).extendEquivOfEquivariant
    ((realCliffordSpinMulSign n).comp ((realCliffordSpinMulSign n).prodMap (MonoidHom.id C₂)))
    ((continuous_realCliffordSpinMulSign n).comp
      ((continuous_realCliffordSpinMulSign n).prodMap continuous_id))
    comp_comp_prodMap_eq hn hc s (untwist s) (untwist_smul s) (continuous_untwist s)
    (fun x _ ↦ s.toFrame_smul_of_map_eq_one (by simp) x _)

/-- The untwisting equivalence `(s.twist L).twist L ≃ s` sends `[([(p, l), 1], l'), 1]` to
`p • ε`, where `ε` is the sign with `l' = l • ε`. -/
@[simp]
theorem twistTwistEquiv_toEquiv_inl (x : X) (p : s.P x) (l l' : L x) :
    (s.twistTwistEquiv (L := L)).toEquiv x
        (Extend.inl (realCliffordSpinMulSign n) (continuous_realCliffordSpinMulSign n)
          (P := ((s.twist L).fiberProd C₂ L).P)
          (FiberProd.mk (Extend.inl (realCliffordSpinMulSign n)
            (continuous_realCliffordSpinMulSign n) (P := (s.fiberProd C₂ L).P)
            (FiberProd.mk p l)) l')) =
      op ((realCliffordSpinDoubleCoverZero n).inl (division C₂ l l')) • p := by
  -- `rw` and `simp` cannot see through the fibres of the iterated twist, so the values of the
  -- three equivalences composed in `twistTwistEquiv` are computed one at a time and chained by
  -- `TauCeti.OrthonormalFrameLift.Equiv.trans_toEquiv_apply_of_eq` and
  -- `TauCeti.OrthonormalFrameLift.Equiv.symm_toEquiv_apply_of_eq`.
  unfold twistTwistEquiv
  apply Equiv.trans_toEquiv_apply_of_eq
  · exact (Equiv.extend_toEquiv_inl _ _ _ _ _ _ x _).trans
      (congrArg _ (Equiv.symm_toEquiv_apply_of_eq _
        ((s.fiberProd C₂ L).extendFiberProdEquiv_toEquiv_inl L (realCliffordSpinMulSign n)
          (continuous_realCliffordSpinMulSign n)
          (subtype_comp_spinToSpecialOrthogonal_comp_realCliffordSpinMulSign n) hn hc x
          (FiberProd.mk p l) l')))
  apply Equiv.trans_toEquiv_apply_of_eq
  · exact Equiv.symm_toEquiv_apply_of_eq _ (extendCompEquiv_toEquiv_inl ..)
  · exact extendEquivOfEquivariant_toEquiv_inl ..

end SpinStructure

end TauCeti
